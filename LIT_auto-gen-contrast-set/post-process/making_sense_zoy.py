# from https://github.com/XuhuiZhou/CATS/blob/master/making_sense.py
# from https://github.com/leo-liuzy/LIT_auto-gen-contrast-set/blob/main/post-process/making_sense.py

import torch
from torch.nn import CrossEntropyLoss
import numpy as np
import math
import logging
import os
import sys

# Enable only certain GPUs
#os.environ["CUDA_VISIBLE_DEVICES"]="0"
#os.environ["HIP_VISIBLE_DEVICES="]="1"

logging.basicConfig(level=logging.INFO)
logger = logging.getLogger(__name__)

def get_device():
    return 'cuda' if torch.cuda.is_available() else 'cpu'

def score_causal_lm(text, model, tokenizer):
    """
    Scoring for Standard PyTorch Causal LMs (Mistral, Llama, GPT-2).
    """
    device = get_device()
    inputs = tokenizer(text, return_tensors="pt")
    input_ids = inputs["input_ids"].to(device)
    if input_ids.size(1) == 0:
        return -math.inf
    with torch.no_grad():
        outputs = model(input_ids, labels=input_ids)
        loss = outputs.loss
    return -loss.item()

def score_masked_lm(text, model, tokenizer):
    """
    Scoring for Masked LMs (BERT, RoBERTa).
    """
    device = get_device()
    inputs = tokenizer(text, return_tensors="pt", add_special_tokens=True)
    input_ids = inputs["input_ids"].to(device)
    seq_len = input_ids.size(1)
    if seq_len <= 2:
        return -math.inf
    total_score = 0
    masked_indices = range(1, seq_len - 1)
    with torch.no_grad():
        for i in masked_indices:
            original_token_id = input_ids[0, i].clone()
            input_ids[0, i] = tokenizer.mask_token_id
            outputs = model(input_ids)
            logits = outputs.logits
            token_logits = logits[0, i]
            log_probs = torch.nn.functional.log_softmax(token_logits, dim=0)
            score = log_probs[original_token_id].item()
            total_score += score
            input_ids[0, i] = original_token_id
    return total_score / len(masked_indices)

def score_gguf(text, llm, tokenizer=None):
    """
    Optimized scoring for GGUF models using low-level eval().
    Bypasses the expensive sorting of 200k vocab logits.
    """
    if not text.strip():
        return -math.inf

    try:
        # 1. Tokenize
        # add_bos=True is important for the start of the sentence
        tokens = llm.tokenize(text.encode("utf-8"), add_bos=True)
        if len(tokens) <= 1:
            return -math.inf

        # 2. Reset and Evaluate
        # We clear the KV cache to ensure no contamination from previous sentences
        llm.reset()
        llm.eval(tokens)

        # 3. Extract Logits
        # llm._scores contains raw logits [n_tokens, vocab_size]
        # We convert to numpy to do fast math
        logits = np.array(llm._scores[:len(tokens)])

        # 4. Calculate Perplexity (Shifted)
        # We predict token[i+1] given context[0...i]
        # Logits for pos 0 predict token 1, etc.
        preds = logits[:-1]      # Predictions at step 0..N-1
        targets = tokens[1:]     # Actual tokens at step 1..N
        log_likelihood = 0.0

        for i, target_id in enumerate(targets):
            token_logits = preds[i]
            # Optimized Log-Softmax (Stable)
            # This avoids sorting the whole vocab!
            max_logit = np.max(token_logits)
            norm_logits = token_logits - max_logit
            log_sum_exp = np.log(np.sum(np.exp(norm_logits)))
            # Log Prob = (Logit - Max) - LogSumExp
            token_log_prob = norm_logits[target_id] - log_sum_exp
            log_likelihood += token_log_prob
        return log_likelihood / len(targets)

    except Exception as e:
        print(f"GGUF Scoring Error: {e}")
        # Reset on error to be safe
        try: llm.reset()
        except: pass
        return -math.inf

def uni_predict(text, model, tokenizer):
    # Tokenized input
    # text = "[CLS] I got restricted because Tom reported my reply [SEP]"
    text = text
    tokenized_text = tokenizer.tokenize(text)
    sentence_score = 0
    indexed_tokens = tokenizer.convert_tokens_to_ids(tokenized_text)
    length = len(tokenized_text)
    tokens_tensor = torch.tensor([indexed_tokens])
    tokens_tensor = tokens_tensor.to('cuda')
    #masked_tensor = torch.tensor([masked_index])
    with torch.no_grad():
        outputs = model(tokens_tensor, labels= tokens_tensor)
    loss = outputs[0]
    sentence_score = -loss
    return sentence_score

def bert_predict(text, model, tokenizer):
    # Tokenized input
    # text = "[CLS] I got restricted because Tom reported my reply [SEP]"
    text = "[CLS] " + text + " [SEP]" #special token for BERT, RoBERTa
    tokenized_text = tokenizer.tokenize(text)
    sentence_score = 0
    length = len(tokenized_text)-2
    if length == 0:
        print(text, tokenized_text)
    for masked_index in range(1,len(tokenized_text)-1):
        # Mask a token that we will try to predict back with `BertForMaskedLM`
        masked_word = tokenized_text[masked_index]
        #tokenized_text[masked_index] = '<mask>' #special token for XLNet
        tokenized_text[masked_index] = '[MASK]' #special token for BERT, RoBerta
        # Convert token to vocabulary indices
        indexed_tokens = tokenizer.convert_tokens_to_ids(tokenized_text)
        index = torch.tensor(tokenizer.convert_tokens_to_ids(masked_word))
        tokens_tensor = torch.tensor([indexed_tokens])
        tokens_tensor = tokens_tensor.to('cuda')
        index = index.to('cuda')
        #masked_tensor = torch.tensor([masked_index])
        with torch.no_grad():
            outputs = model(tokens_tensor)
        prediction_scores = outputs[0]
        prediction_scores = prediction_scores.view(-1, model.config.vocab_size)
        prediction_scores = prediction_scores[masked_index].unsqueeze(0)
        loss_fct = CrossEntropyLoss(ignore_index=-1)  # -1 index = padding token
        masked_lm_loss = loss_fct(prediction_scores, index.view(-1))
        tokenized_text[masked_index] = masked_word
        sentence_score -= masked_lm_loss.item()
        tokenized_text[masked_index] = masked_word
    sentence_score = sentence_score/length
    return sentence_score

def ro_predict(text, model, tokenizer):
    # Tokenized input
    # text = "[CLS] I got restricted because Tom reported my reply [SEP]"
    text = '<s> '+text+ ' </s>' #special token for RoBERTa
    tokenized_text = tokenizer.tokenize(text)
    sentence_score = 0
    length = len(tokenized_text)-2
    for masked_index in range(1,len(tokenized_text)-1):
        # Mask a token that we will try to predict back with `BertForMaskedLM`
        masked_word = tokenized_text[masked_index]
        #tokenized_text[masked_index] = '<mask>' #special token for XLNet
        tokenized_text[masked_index] = '<mask>' #special token for BERT, RoBerta
        # Convert token to vocabulary indices
        indexed_tokens = tokenizer.convert_tokens_to_ids(tokenized_text)
        index = torch.tensor(tokenizer.convert_tokens_to_ids(masked_word))
        tokens_tensor = torch.tensor([indexed_tokens])
        tokens_tensor = tokens_tensor.to('cuda')
        index = index.to('cuda')
        #masked_tensor = torch.tensor([masked_index])
        with torch.no_grad():
            outputs = model(tokens_tensor)
        prediction_scores = outputs[0]
        prediction_scores = prediction_scores.view(-1, model.config.vocab_size)
        prediction_scores = prediction_scores[masked_index].unsqueeze(0)
        loss_fct = CrossEntropyLoss(ignore_index=-1)  # -1 index = padding token
        masked_lm_loss = loss_fct(prediction_scores, index.view(-1))
        tokenized_text[masked_index] = masked_word
        sentence_score -= masked_lm_loss.item()
        tokenized_text[masked_index] = masked_word
    sentence_score = sentence_score/length
    return sentence_score

def xlnet_predict(text, model, tokenizer):
    tokenized_text = tokenizer.tokenize(text)
    sentence_score = 0
    #Sprint(len(tokenized_text))
    for masked_index in range(0,len(tokenized_text)):
        masked_word = tokenized_text[masked_index]
        masked_word = tokenized_text[masked_index]
        tokenized_text[masked_index] = '<mask>'
        input_ids = torch.tensor(tokenizer.convert_tokens_to_ids(tokenized_text)).unsqueeze(0)
        index = torch.tensor(tokenizer.convert_tokens_to_ids(masked_word))
        perm_mask = torch.zeros((1, input_ids.shape[1], input_ids.shape[1]), dtype=torch.float)
        perm_mask[:, :, masked_index] = 1.0  # Previous tokens don't see last token
        target_mapping = torch.zeros((1, 1, input_ids.shape[1]), dtype=torch.float)  # Shape [1, 1, seq_length] => let's predict one token
        target_mapping[0, 0, masked_index] = 1.0  # Our first (and only) prediction will be the last token of the sequence (the masked token)
        input_ids = input_ids.to('cuda')
        perm_mask = perm_mask.to('cuda')
        target_mapping = target_mapping.to('cuda')
        index = index.to('cuda')
        with torch.no_grad():
            outputs = model(input_ids, perm_mask=perm_mask, target_mapping=target_mapping, labels = index)
        next_token_logits = outputs[0]
        length = len(tokenized_text)
        # predict_list = predictions[0, masked_index]
        sentence_score -= next_token_logits.item()
        tokenized_text[masked_index] = masked_word
    return sentence_score/(length)

#ifndef	QC_H
#define QC_H

struct qc	*extract_qc(struct dg	*d);
struct qc	*extract_qc_arg(struct dg	*d, int	arg);
int			quickcheck(struct qc	*a, struct qc	*b);
int	equiv_quickcheck(struct qc	*a, struct qc	*b, int *Fw, int *Bk, int	*Gz);
struct qc	*copy_qc(struct qc	*in);
struct type	*qc_type_n(struct qc	*in, int	n);

#ifdef	CONF_H
void	gqc_count_failure(struct path	path);
void	gqc_result();
void	write_qccode_from_pet_instance(struct dg	*petqc, FILE	*f);
#endif

extern int __qc_use_heap;

// qc extractor compiler
typedef	void	(*qc_extractor_function)(struct type**, struct dg*);
qc_extractor_function	dynamically_link_qc_extractor();
int	compile_qc(char	*qccode_path);

// internal properties to be used only by the freezer
void	*freeze_qc();
void	recover_qc(void	*qcf);

#endif

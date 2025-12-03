#include	"mrs.h"
#define		REGEX_FLAGS	REG_PERL
#define		UNICODE
#include	<boost/regex.h>

#define	ALLOW_SEMI_MODE	0

//#define	COPIED_VARIABLES_NEED_REENTRANCIES
#undef	COPIED_VARIABLES_NEED_REENTRANCIES

#define	FIXUP_FIRST_ROUTE_ONLY		1
#define	CLEANUP_FIRST_ROUTE_ONLY	1

//#define	EQUATE_QEQS_FOR_TRANSFER	0	// had thought this was right for some reason, perhaps related to the fixup test I did when Dan was here
#define	EQUATE_QEQS_FOR_TRANSFER	1	// using this setting for the paper with Berthold

#undef	NO_FIXUP
//#define	NO_FIXUP


struct mrs_ep_desc
{
	wchar_t	*pred_re;
	regex_t	re;
	struct dg	*dg;
};

struct mrs_desc
{
	int	neps;
	int	nhcons;
	struct mrs_ep_desc	*eps;
	struct mrs	*mrs;
	struct dg	*dg;
};

struct transfer_rule
{
	char	*name;
	struct mrs_desc	input, context, filter, output;
	struct dg	*dg;	// in this dg, all types under OUTPUT are washed out to *top* (but features remain)
	struct dg	*output_override;	// another version of the part of dg under OUTPUT where the types are not washed out (but missing reentrancies with the rest of 'dg')

	int	neq, nss;
	struct dg	**eq, **ss;

	int	optional;
	/*int	ncopy;
	int	*copy;
	char	*output_copy_map;*/
	int	disabled;
};

extern int g_transfer;
extern int	ntransfer_rules;
extern struct transfer_rule	**transfer_rules;
int	load_transfer_rules();

/*
// for use when loading rules with ugly +copy+ specifications
struct tcopy
{
	int	*frompath;
	int	*topath;
	int	frompathlen;
	int	topathlen;
};
extern int saved_ntcopies;
extern struct tcopy	*saved_tcopies;
*/

int	align_transfer_rule(struct transfer_rule	*tr, struct mrs	*mrs, int	(*callback)(int	*alignment, int	*hcalignment));
struct transfer_rule	*dg_to_transfer_rule(char	*name, struct dg	*dg, struct dg	*output_override);

int	study_trigger_rule(char	*name, struct dg	*main_dg, struct dg	*output_override);
void	activate_trigger_rules(struct mrs	*mrsin, void	trigger(char	*lexid, struct dg	*cons));

extern char	*non_idiom_root;
int	study_idiom_rule(char	*name, struct dg	*main_dg, struct dg	*output_override);
int	check_idioms(struct dg	*dg, struct mrs	*m);

int	study_fixup_rule(char	*name, struct dg	*main_dg, struct dg	*output_override);
int	study_cleanup_rule(char	*name, struct dg	*main_dg, struct dg	*output_override);
struct mrs	*fixup_mrs(struct mrs	*m);
struct mrs	*cleanup_mrs(struct mrs	*m);

struct type	*transfer_next_skolem_constant();

int	transfer_mrs(int	nrules, struct transfer_rule	**rules, struct mrs	*m, struct mrs	***Results, int first_route_only);
struct mrs	*transfer_mrs_result(struct transfer_rule	*tr, int	*alignment, int	*hcalignment, struct mrs	*min);

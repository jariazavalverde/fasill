<div class="container py-2 px-0"><h4 id="fasill_max_inferences/1"><a href="/fasill/documentation/src/environment#fasill_max_inferences/1">fasill_max_inferences/1</a></h4><?php echo show_template("fasill_max_inferences(?Limit)"); ?><p><?php echo show_description("This predicate succeeds when ?Limit is the current limit of inferences that can be performed when a goal is executed."); ?></p></div>
<div class="container py-2 px-0"><h4 id="set_max_inferences/1"><a href="/fasill/documentation/src/environment#set_max_inferences/1">set_max_inferences/1</a></h4><?php echo show_template("set_max_inferences(+Limit)"); ?><p><?php echo show_description("This predicate succeeds, and chages the current limit of inferences that can be performed when a goal is executed."); ?></p></div>
<div class="container py-2 px-0"><h4 id="to_prolog/2"><a href="/fasill/documentation/src/environment#to_prolog/2">to_prolog/2</a></h4><?php echo show_template("to_prolog(+FASILL, ?Prolog)"); ?><p><?php echo show_description("This predicate takes the FASILL object +FASILL and returns the object ?Prolog in Prolog notation."); ?></p></div>
<div class="container py-2 px-0"><h4 id="from_prolog/2"><a href="/fasill/documentation/src/environment#from_prolog/2">from_prolog/2</a></h4><?php echo show_template("from_prolog(+Prolog, ?FASILL)"); ?><p><?php echo show_description("This predicate takes the Prolog object +Prolog and returns the object ?FASILL in FASILL notation."); ?></p></div>
<div class="container py-2 px-0"><h4 id="fasill_number/1"><a href="/fasill/documentation/src/environment#fasill_number/1">fasill_number/1</a></h4><?php echo show_template("fasill_number(+Term)"); ?><p><?php echo show_description("This predicate succeeds when +Term is a FASILL number."); ?></p></div>
<div class="container py-2 px-0"><h4 id="fasill_integer/1"><a href="/fasill/documentation/src/environment#fasill_integer/1">fasill_integer/1</a></h4><?php echo show_template("fasill_integer(+Term)"); ?><p><?php echo show_description("This predicate succeeds when +Term is a FASILL integer."); ?></p></div>
<div class="container py-2 px-0"><h4 id="fasill_float/1"><a href="/fasill/documentation/src/environment#fasill_float/1">fasill_float/1</a></h4><?php echo show_template("fasill_float(+Term)"); ?><p><?php echo show_description("This predicate succeeds when +Term is a FASILL float."); ?></p></div>
<div class="container py-2 px-0"><h4 id="fasill_atom/1"><a href="/fasill/documentation/src/environment#fasill_atom/1">fasill_atom/1</a></h4><?php echo show_template("fasill_atom(+Term)"); ?><p><?php echo show_description("This predicate succeeds when +Term is a FASILL atom."); ?></p></div>
<div class="container py-2 px-0"><h4 id="fasill_term/1"><a href="/fasill/documentation/src/environment#fasill_term/1">fasill_term/1</a></h4><?php echo show_template("fasill_term(+Term)"); ?><p><?php echo show_description("This predicate succeeds when +Term is a FASILL term."); ?></p></div>
<div class="container py-2 px-0"><h4 id="fasill_var/1"><a href="/fasill/documentation/src/environment#fasill_var/1">fasill_var/1</a></h4><?php echo show_template("fasill_var(+Term)"); ?><p><?php echo show_description("This predicate succeeds when +Term is a FASILL variable."); ?></p></div>
<div class="container py-2 px-0"><h4 id="program_clause/2"><a href="/fasill/documentation/src/environment#program_clause/2">program_clause/2</a></h4><?php echo show_template("program_clause(?Indicator, ?Rule)"); ?><p><?php echo show_description(""); ?></p></div>
<div class="container py-2 px-0"><h4 id="program_rule_id/2"><a href="/fasill/documentation/src/environment#program_rule_id/2">program_rule_id/2</a></h4><?php echo show_template("program_rule_id(+Rule, ?Id)"); ?><p><?php echo show_description("This predicate succeeds when ?Id is the identifier of the rule +Rule."); ?></p></div>
<div class="container py-2 px-0"><h4 id="program_consult/1"><a href="/fasill/documentation/src/environment#program_consult/1">program_consult/1</a></h4><?php echo show_template("program_consult(+Path)"); ?><p><?php echo show_description("This predicate loads the FASILL program from the file +Path into the environment. This predicate cleans the previous rules."); ?></p></div>
<div class="container py-2 px-0"><h4 id="program_has_predicate/1"><a href="/fasill/documentation/src/environment#program_has_predicate/1">program_has_predicate/1</a></h4><?php echo show_template("program_has_predicate(?Indicator)"); ?><p><?php echo show_description("This predicate succeeds when ?Indicator is the indicator of a predicate asserted in the program loaded in the current environment."); ?></p></div>
<div class="container py-2 px-0"><h4 id="lattice_tnorm/1"><a href="/fasill/documentation/src/environment#lattice_tnorm/1">lattice_tnorm/1</a></h4><?php echo show_template("lattice_tnorm(?Tnorm)"); ?><p><?php echo show_description("This predicate succeeds when ?Tnorm is the current t-norm asserted in the environment."); ?></p></div>
<div class="container py-2 px-0"><h4 id="lattice_tconorm/1"><a href="/fasill/documentation/src/environment#lattice_tconorm/1">lattice_tconorm/1</a></h4><?php echo show_template("lattice_tconorm(?Tconorm)"); ?><p><?php echo show_description("This predicate succeeds when ?Tconorm is the current t-conorm asserted in the environment."); ?></p></div>
<div class="container py-2 px-0"><h4 id="lattice_call_bot/1"><a href="/fasill/documentation/src/environment#lattice_call_bot/1">lattice_call_bot/1</a></h4><?php echo show_template("lattice_call_bot(-Bot)"); ?><p><?php echo show_description("This predicate succeeds when -Bot is the bottom member of the lattice loaded into the environment."); ?></p></div>
<div class="container py-2 px-0"><h4 id="lattice_call_top/1"><a href="/fasill/documentation/src/environment#lattice_call_top/1">lattice_call_top/1</a></h4><?php echo show_template("lattice_call_top(-Bot)"); ?><p><?php echo show_description("This predicate succeeds when -Bot is the bottom member of the lattice loaded into the environment."); ?></p></div>
<div class="container py-2 px-0"><h4 id="lattice_call_member/1"><a href="/fasill/documentation/src/environment#lattice_call_member/1">lattice_call_member/1</a></h4><?php echo show_template("lattice_call_member(+Memeber)"); ?><p><?php echo show_description("This predicate succeeds when +Member is a member of the lattice loaded into the environment."); ?></p></div>
<div class="container py-2 px-0"><h4 id="lattice_call_connective/3"><a href="/fasill/documentation/src/environment#lattice_call_connective/3">lattice_call_connective/3</a></h4><?php echo show_template("lattice_call_connective(+Name, +Arguments, ?Result)"); ?><p><?php echo show_description("This predicate succeeds when ?Result is the result of evaluate the connective ?Name with the arguments +Arguments of the lattice loaded into the environment."); ?></p></div>
<div class="container py-2 px-0"><h4 id="lattice_consult/1"><a href="/fasill/documentation/src/environment#lattice_consult/1">lattice_consult/1</a></h4><?php echo show_template("lattice_consult(+Path)"); ?><p><?php echo show_description("This predicate loads the lattice of the file +Path into the environment. This predicate cleans the previous lattice."); ?></p></div>
<div class="container py-2 px-0"><h4 id="~/1"><a href="/fasill/documentation/src/environment#~/1">~/1</a></h4><?php echo show_template("~(+Assignment)"); ?><p><?php echo show_description("This predicate succeeds when +Assignment is a valid  assignment of a t-norm. A valid assignment is of the  form ~tnorm = Atom, where Atom is an atom. This predicate asserts Atom in the current environment as the current t-norm for similarities. This predicate retracts the current t-norm, if exists."); ?></p></div>
<div class="container py-2 px-0"><h4 id="~/2"><a href="/fasill/documentation/src/environment#~/2">~/2</a></h4><?php echo show_template("~(+SimilarityEquation)"); ?><p><?php echo show_description("This predicate succeeds when +SimilarityEquation is a valid similarity equation and asserts it in the current environment. A valid similarity equation is of the form AtomA/Length ~ AtomB/Length = TD, where AtomA and AtomB are atoms and Length is a non-negative integer. Note that this equation is parsed with the default table operator as '~'('/'(AtomA,Length), '='('/'(AtomB,Length),TD))."); ?></p></div>
<div class="container py-2 px-0"><h4 id="similarity_tnorm/1"><a href="/fasill/documentation/src/environment#similarity_tnorm/1">similarity_tnorm/1</a></h4><?php echo show_template("similarity_tnorm(?Tnorm)"); ?><p><?php echo show_description("This predicate succeeds when ?Tnorm is the current t-norm asserted in the environment."); ?></p></div>
<div class="container py-2 px-0"><h4 id="similarity_between/4"><a href="/fasill/documentation/src/environment#similarity_between/4">similarity_between/4</a></h4><?php echo show_template("similarity_between(?AtomA, ?AtomB, ?Length, ?TD)"); ?><p><?php echo show_description("This predicate succeeds when ?AtomA/?Length is similar to ?AtomB/?Length with truth degree ?TD, using the current similarity relation in the environment."); ?></p></div>
<div class="container py-2 px-0"><h4 id="similarity_retract/0"><a href="/fasill/documentation/src/environment#similarity_retract/0">similarity_retract/0</a></h4><?php echo show_template("similarity_retract"); ?><p><?php echo show_description("This predicate succeeds and retracts all the clauses of similarity from the current environment."); ?></p></div>
<div class="container py-2 px-0"><h4 id="similarity_consult/1"><a href="/fasill/documentation/src/environment#similarity_consult/1">similarity_consult/1</a></h4><?php echo show_template("similarity_consult(+Path)"); ?><p><?php echo show_description("This predicate loads the similarities equations of the file +Path into the environment. This predicate cleans the previous similarity relations."); ?></p></div>
<div class="container py-2 px-0"><h4 id="similarity_closure/0"><a href="/fasill/documentation/src/environment#similarity_closure/0">similarity_closure/0</a></h4><?php echo show_template("similarity_closure"); ?><p><?php echo show_description("This predicate computes the reflexive, symmetric and  transitive closure of the similarity scheme asserted into the current environment."); ?></p></div>
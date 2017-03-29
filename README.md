# HMLSL
Proof of motorway safety with an extension of Multi-Lane Spatial Logic as an semantic embedding in Isabelle/HOL 


# Abbreviations
The operators for HMLSL can be written using
the abbreviations defind in the file "abbrev". Following
the implementation of Benzm"uller, we whoose to prefix each
abbreviation with "m". The first-order operators mostly 
follow the conventions in Isabelle, while the HMLSL specific
operators also carry semantically sensible names.

*mand	  : conjunction
*mor	  : disjunction
*mneg	  : negation
*mimpl	  : implication
*mequiv	  : biimplication
*mtop	  : true
*mbot	  : false
**mforall	  : universal quantifier
*mexists	  : existential quantifier
*mequals	  : equality
*mgeq	  : greater or equal than
*mge	  : greater than

*mhchop	  : horizontal chop
*mvchop	  : vertical chop
*mbox	  : box modality
*mdia	  : diamond modality
*msomel	  : left somewhere bracket
*msomer	  : right somewhere bracket
*meveryl	  : left everywhere bracket
*meveryr	  : right everywhere bracket
*mglobally : globally
*mat	  : switch modality

*mwidth	  : width (thick omega)
*mlength	  : length (thick l)

*mtransl	  : left part of transition arrow (thick bar)
*mtransr	  : right part of transition arrow (thick rightarrow)
*mevolve	  : evolution transition
*mabstrans : abstract transition



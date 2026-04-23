---
title: "Introduction"
link-citations: true
bibliography: bibliography.bib
csl: chicago.csl
notes-after-punctuation: false
---

This website presents the Agda formalisation for the paper "Commutative algebras of series" [@Clemente:arXiv:2026],
however it is meant to be accessible without referring to the paper.
The paper contains clickable links to the relevant parts of this website.

We develop a fragment of the theory of *formal series in noncommuting variables* and their algebraic properties.
Our approach is *coinductive*, using Agda's sized types and guardedness features.
This website can be used as a tutorial on the use of these features in Agda.

# Organisation

The rest of the document is structured as follows.

- In the [Preliminaries](Preliminaries/index/) part,
we introduce some basic notions extending Agda's standard library.

- Then in the [General](General/index/) part,
we develop some aspects of the theory of formal series which are valid for every product rule.

- Finally, in the [Special](Special/index/) part,
we develop the aspects of the theory of formal series which holds only for special product rules.

# Acknowledgements

The following two projects have been inspiring for this document.

* [@Kirst_2025] shows an example of a mathematical paper containing hyperlinks to a supporting Coq formalisation.
* [@plfa20.07] shows that beautiful books can be written in Agda. A lot of the layout in this document is inspired from this project.

We have learned a lot from several Agda resources [@BoveDybjer:LerNet:2008] [@Norell:AFP:2008] [@McBride:2013] [@Stump:ACM:2016] [@agda-dybjer:2018].

::: {#refs}
# References
:::

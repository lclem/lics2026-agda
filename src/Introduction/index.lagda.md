---
title: "Introduction"
---

```
{-# OPTIONS --guardedness --sized-types #-}
module Introduction.index where
```

This document is a support Agda formalisation for the paper [@Clemente:arXiv:2026].
We develop a fragment of the theory of formal series in noncommuting variables and their algebraic properties.
Our approach is coinductive, using Agda's sized types and guardedness features.

# Organisation

The rest of the document is structured as follows.
In the [Preliminaries](../../Preliminaries/index/) part, we introduce some basic notions extending Agda's standard library.
Then in the [General](../../General/index/) part, we develop some aspects of the theory of formal series which are valid for every product rule.
Finally,  in the [Special](../../Special/index/) part, we develop the aspects of the theory of formal series which holds only for special product rules.

```
import Preliminaries.index
import General.index
import Special.index
```

# Acknowledgements

The following two projects have been inspiring for this document.

* [@Kirst_2025] shows an example of a mathematical paper containing hyperlinks to a supporting Coq formalisation.
* [@plfa20.07] shows that beautiful books can be written in Agda. A lot of the layout in this document is inspired from this project.

The following are some basic Agda resources:

* [@BoveDybjer:LerNet:2008]
* [@Norell:AFP:2008]
* [@McBride:2013]
* [@Stump:ACM:2016]
* [@agda-dybjer:2018]

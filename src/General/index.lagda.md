---
title: "General results 🚧"
---

```
{-# OPTIONS --guardedness --sized-types #-}
-- --allow-unsolved-metas

module General.index where
```

In this part we present our results on formal series that are valid for every product rule.
The rest of the section is structured as follows.
In [Series](../Series) we define formal series and their vector space structure.
In [Terms](../Terms) we define the notion of terms and develop their basic properties.
In [ProductRules](../ProductRules) we define the notion of a *product rule* `P`,
which is then used in [Products](../Products) to define the *`P`-product* operation on formal series.
In [FinitelyGenerated](../FinitelyGenerated) we study the resulting notion of *`P`-finite* series
and in [Automata](../Automata) we study *`P`-automata*.
This culminates with a proof of the [coincidence](../Automata#sec:coincidence) of `P`-finite series and series recognized by `P`-automata.
Finally, in [Reversal](../Reversal) we study right derivatives and reversals of formal series.

```

import General.Series
import General.Terms
import General.ProductRules
import General.Products
import General.FinitelyGenerated
import General.Automata
import General.Reversal
```

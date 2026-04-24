---
title: "Introduction"
link-citations: true
bibliography: bibliography.bib
csl: chicago.csl
notes-after-punctuation: false
---

This website contains the Agda formalisation for the paper [@Clemente:arXiv:2026],
<p style="text-align: center;">
    Lorenzo Clemente, *Commutative algebras of series* (LICS'26).
</p>
The source code is publicly available on [github](https://github.com/lclem/lics2026-agda)
in the form of [literate Agda](https://agda.readthedocs.io/en/latest/tools/literate-programming.html).
Background, motivation, and examples are given in the paper,
which contains clickable links to the relevant parts of this website.

We develop a fragment of the theory of *formal series in noncommuting variables* and their algebraic properties.
Our approach is *coinductive*, using Agda's sized types and guardedness features.

This website is meant to be accessible without referring to the paper.
In particular, it can be used as a tutorial on the formalisation of power series in Agda.
Clicking on a keyword will take you to its definition.

# Abstract

We quote below the abstract from [@Clemente:arXiv:2026].

> We consider a large family of product operations of formal power series in noncommuting indeterminates,
the classes of automata they define, and the respective equivalence problems.
A P-product of series is defined coinductively by a polynomial product rule P,
which gives a recursive recipe to build the product of two series as a function of the series themselves and their derivatives.
>
> The first main result of the paper is a complete and decidable characterisation of all product rules P
giving rise to P-products which are bilinear, associative, and commutative (BAC).
The characterisation shows that there are infinitely many such products,
and in particular it applies to the notable Hadamard, shuffle, and infiltration products from the literature.
>
> Every P-product gives rise to the class of P-automata,
an infinite-state model where states are terms.
The second main result of the paper is that the equivalence problem for P-automata is decidable for P-products satisfying our characterisation.
This explains, subsumes, and extends known results from the literature on the Hadamard, shuffle, and infiltration automata.

{::comment}
Removed the last sentence of the abstract.
{:/comment}

# Organisation

The rest of the document is structured in three parts, as follows.

- [Preliminaries](Preliminaries/index/): We introduce some basic notions extending Agda's standard library.

- [General](General/index/): We develop the theory of formal series and product rules.

    - [Series](General/Series): Formal series and vector space structure.
    - [Terms](General/Terms): Terms and their basic properties.
    - [Product rules](General/ProductRules): Product rules.
    - [Products](General/Products): Product operations obeying a product rule.
    - [P-finite series](General/FinitelyGenerated): P-finite series.
    - [Automata](General/Automata): P-automata and equivalence with P-finite series.
    - [Reversal](General/Reversal): Right derivatives and reversals of formal series.
    - [Reversal endomorphisms](General/ReversalEnd): Reversal endomorphisms.


- [Special](Special/index/): We focus on the *special product rules*,
which are those rules giving rise to products which are bilinear, associative, and commutative.

    - [Special product rules](Special/ProductRules): Special product rules.
    - [Special products](Special/Products): Special products.
    - [Automata](Special/Automata): Special automata and equivalence with special finite series.
    - [Reversal endomorphisms](Special/Reversal): Special reversal endomorphisms.

# Acknowledgements

The following two projects have been inspiring for this document.

* [@Kirst_2025] shows an example of a mathematical paper containing hyperlinks to a supporting Coq formalisation.
* [@plfa20.07] shows that beautiful books can be written in Agda. A lot of the layout in this document is inspired from this project.

We have learned a lot from several Agda resources [@BoveDybjer:LerNet:2008] [@Norell:AFP:2008] [@McBride:2013] [@Stump:ACM:2016] [@agda-dybjer:2018].

# Citing this document

```bibtex
@Book{Clemente:Agda:LICS:2026,
    author = {Lorenzo Clemente},
    title  = {Commutative algebras of series (in Agda)},
    year   = {2026},
    month  = {May},
    url    = {https://lclem.github.io/lics2026-agda},
}
```

::: {#refs}
# References
:::

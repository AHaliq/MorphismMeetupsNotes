#import "@preview/lemmify:0.1.8": *
#import "@preview/fletcher:0.5.8" as fletcher: diagram, node, edge

// lemmify ---------------------------------
#let (
  definition, theorem, lemma, corollary,
  remark, proposition, example,
  proof, rules: thm-rules
) = default-theorems("thm-group", lang: "en")
#show: thm-rules

// end of preamble -------------------------

= Meeting 1: @riehl2017category Chapter 2 (#datetime(year: 2025, month: 10, day:10).display())

1. Universal Properties
2. Representable Functors
3. Yoneda Lemma
4. Universal Property as Representable Functor
5. All presheaves are colimits of representable functors (Towards the future)

object that uniquely determines the natural isomorphism are the "legs" that define the universal property
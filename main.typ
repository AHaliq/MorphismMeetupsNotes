#import "@preview/arkheion:0.1.1": arkheion, arkheion-appendices
#import "@preview/lemmify:0.1.8": *
#import "@preview/fletcher:0.5.8" as fletcher: diagram, node, edge

// template --------------------------------
#show: arkheion.with(
  title: "Morphism Meetups Notes",
  // authors: (
  //   (name: "Haliq", email: "haliq12@gmail.com", affiliation: "-", orcid: "0009-0006-1276-363X"),
  // ),
  abstract: [Notes from Morphism Meetups; reading group on higher category theory. The notes attempt to be rigorous in defining concepts as logical predicates and will use them as composable blocks for proofs. They will be accompanied with commutative diagrams when relevant to provide visual intuition.],
  keywords: ("Category Theory", ""),
  date: datetime.today().display(),
)
#set cite(style: "chicago-author-date")
#show link: underline

// lemmify ---------------------------------
#let (
  definition, theorem, lemma, corollary,
  remark, proposition, example,
  proof, rules: thm-rules
) = default-theorems("thm-group", lang: "en")
#show: thm-rules

// end of preamble -------------------------

#include "1-prereq.typ"
#include "2-yoneda.typ"

// Add bibliography and create Bibiliography section
#bibliography("bibliography.bib")

// Create appendix section
// #show: arkheion-appendices
// =

// == Appendix section

// #lorem(100)


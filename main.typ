#import "@preview/arkheion:0.1.1": arkheion, arkheion-appendices
#import "@preview/ez-today:1.1.0"

// template --------------------------------
#show: arkheion.with(
  title: "Morphism Meetups Notes",
  authors: (
    (name: "Haliq", email: "haliq12@gmail.com", affiliation: "", orcid: "0009-0006-1276-363X"),
  ),
  abstract: [Notes from Morphism Meetups; a reading group on learning higher category theory starting from 1-category.],
  keywords: ("Category Theory", ""),
  date: ez-today.today(lang: "en"),
)
#set cite(style: "chicago-author-date")
#show link: underline

// end of preamble -------------------------

#include "1-pre-req.typ"
#include "2-yoneda.typ"

#bibliography("bibliography.bib")

// Create appendix section
// #show: arkheion-appendices
// =

// == Appendix section

// #lorem(100)


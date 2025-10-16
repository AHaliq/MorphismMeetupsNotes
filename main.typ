#import "@preview/arkheion:0.1.1": arkheion, arkheion-appendices
#import "@preview/ez-today:1.1.0"

// template --------------------------------
#show: arkheion.with(
  title: "Notes on Abstract Categories",
  authors: (
    (name: "Haliq", email: "haliq12@gmail.com", affiliation: "", orcid: "0009-0006-1276-363X"),
  ),
  abstract: [We build up to the definition of an abstract n-category starting from 1-category. Here, we follow @riehl2017category, to define the taxonomy of abstract categories and their properties.],
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


#import "@preview/lemmify:0.1.8": *
#import "@preview/showybox:2.0.4": *
#import "@preview/equate:0.3.2": equate

// custom functions -----------------------------

#let dim(x) = text(fill: gray, $#x$)

#let summary(it) = [
  #line(length: 100%)

  #align(center)[#smallcaps[
      $-$ Summary $-$
    ]

    #it
  ]

  #line(length: 100%)
]

// lemmify --------------------------------------

#let notation-style(
  thm-type,
  name,
  number,
  body,
) = showybox(breakable: true, frame: (
  thickness: 0pt,
  body-color: blue.lighten(95%),
))[
  *#thm-type* #if name == none [] else [_(#name)_] #body
]

#let proof-col = black.lighten(90%)
#let proof-style(it) = showybox(breakable: true, frame: (
  thickness: 0pt,
  body-color: proof-col,
))[#it]

#let (
  definition,
  theorem,
  lemma,
  corollary,
  remark,
  proposition,
  example,
  proof,
  rules: thm-rules,
) = default-theorems("thm-group", lang: "en")

#let (
  notation,
  rules: thm-rules-2,
) = new-theorems("thm-group", ("notation": [Notation]), thm-styling: notation-style)

// top level preamble ---------------------------
// call via `#show: init`

#let init(it) = {
  set table(stroke: (thickness: 0.5pt, paint: black.lighten(67%)), align: center + horizon)
  set grid(align: center + horizon, gutter: 1em)
  show: thm-rules
  show: thm-rules-2
  // show thm-selector("thm-group", subgroup: "definition"): it => showybox(breakable: true)[#it]
  show thm-selector("thm-group", subgroup: "proof"): proof-style

  show: equate.with(breakable: true, sub-numbering: true)
  set math.equation(numbering: "(1.1)")
  it
}

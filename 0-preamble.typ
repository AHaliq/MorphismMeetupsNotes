#import "@preview/lemmify:0.1.8": *
#import "@preview/showybox:2.0.4": *

// lemmify ---------------------------------

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

#let my-thm-style(
  thm-type,
  name,
  number,
  body,
) = showybox(breakable: true, frame: (
  thickness: 0pt,
  body-color: blue.lighten(90%),
))[
  *#thm-type* #if name == none [] else [_(#name)_] #body
]

#let my-styling = (
  thm-styling: my-thm-style,
)

#let (
  notation,
  rules: thm-rules-2,
) = new-theorems("thm-group", ("notation": [Notation]), ..my-styling)

#let init(it) = {
  set table(stroke: 0.5pt + gray, align: center + horizon)
  set grid(align: center + horizon, gutter: 1em)
  show: thm-rules
  show: thm-rules-2
  show thm-selector("thm-group", subgroup: "definition"): it => showybox(breakable: true)[#it]
  show thm-selector("thm-group", subgroup: "proof"): it => showybox(breakable: true, frame: (
    thickness: 0pt,
    body-color: black.lighten(90%),
  ))[#it]
  it
}

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

#let style(it) = {
  show thm-selector("thm-group", subgroup: "definition"): it => showybox(breakable: true)[#it]
  show thm-selector("thm-group", subgroup: "proof"): it => showybox(breakable: true, frame: (
    thickness: 0pt,
    title-color: red.lighten(60%),
    body-color: black.lighten(90%)
  ))[#it]
  it
}

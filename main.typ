#import "@preview/arkheion:0.1.1": arkheion, arkheion-appendices
#import "@preview/lemmify:0.1.8": *
#import "@preview/fletcher:0.5.8" as fletcher: diagram, node, edge

// template --------------------------------
#show: arkheion.with(
  title: "Morphism Meetups Notes",
  // authors: (
  //   (name: "Haliq", email: "haliq12@gmail.com", affiliation: "-", orcid: "0009-0006-1276-363X"),
  // ),
  abstract: [Notes from Morphism Meetups; reading group on higher category theory.],
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

= Pre-Requisite: @riehl2017category Chapter 1

#definition(name: "Category")[A #emph("category") $cal(C)$ consists of #emph("objects") $X, Y, Z, ... in cal(C)$ and #emph("morphisms") $f, g, h, ... in cal(C)(X,Y)$ where $X in cal(C)$ is its #emph("domain") and $Y in cal(C)$ is its #emph("codomain").

#figure(
table(
  align: center,
  columns: (auto, auto, auto),
  row-gutter: (2pt, auto),
  stroke: 0.5pt,
  inset: 7pt,
  [hom], [type], [diagram],
  $f in cal(C)(X,Y)$,
  $f: X -> Y$,
  $X attach(->, t: f) Y$,
),
caption: [Different notations for morphisms]
)

$
text("IsCat")(cal(C))
&= forall X in cal(C). 1_X in cal(C)(X,X)
& text("identity") \
&and forall f in cal(C)(X,Y), g in cal(C)(Y,Z). g f in cal(C)(X,Z)
& text("composition") \
&and forall f in cal(C)(X,Y). 1_Y f = f = f 1_X
& text("unital") \
&and forall f in cal(C)(X,Y), g in cal(C)(Y,Z), h in cal(C)(Z,W). h (g f) = (h g) f
& text("associative")
$

#figure(
table(
  align: horizon+center,
  columns: (auto, auto, auto, auto),
  row-gutter: (2pt, auto),
  stroke: 0.5pt,
  inset: 7pt,
  [identity], [composition], [unital], [associative],
  diagram({
    let X = (0,0)
    node(X, $X$)
    edge(X, "->", X, bend: -130deg, loop-angle: 120deg)[$1_X$]
  }),
  diagram({
    let X = (0,1)
    let Y = (0,0)
    let Z = (1,0)
    node(X, $X$)
    node(Y, $Y$)
    node(Z, $Z$)
    edge(X, "->", Y)[$f$]
    edge(Y, "->", Z)[$g$]
    edge(X, "->", Z, label-side: right)[$g f$]
  }),
  diagram({
    let X1 = (0,0)
    let X2 = (0,1)
    let Y1 = (1,0)
    let Y2 = (1,1)
    node(X1, $X$)
    node(X2, $X$)
    node(Y1, $Y$)
    node(Y2, $Y$)
    edge(X1, "->", Y1)[$f$]
    edge(X2, "->", Y2)[$f$]
    edge(X2, "->", X1, label-side: left)[$1_X$]
    edge(Y2, "->", Y1, label-side: right)[$1_Y$]
    edge(X2, "->", Y1)[$f$]
  }),
  diagram({
    let X = (0,0)
    let Y = (1,0)
    let Z = (2,0)
    let W = (3,0)
    node(X, $X$)
    node(Y, $Y$)
    node(Z, $Z$)
    node(W, $W$)
    edge(X, "->", Y)[$f$]
    edge(Y, "->", Z)[$g$]
    edge(Z, "->", W)[$h$]
    edge(X, "->", Z, bend: -20deg)[$g f$]
    edge(Y, "->", W, bend: 40deg)[$h g$]
    edge(X, "->", W, bend: -40deg)[$h g f$]
  })
),
caption: [Commutative Diagram for each property of a category]
)
]

#let Mor = $text("Mor")$;
#let Set = $text("Set")$;

#definition(name: "Small Category")[A category is where it has only a set's worth of morphisms
  $
    Mor cal(C) in Set
  $
]

#definition(name: "Locally Small Category")[A category where its homs are a set's worth
  $
    cal(C)(X,Y) in Set
  $
]

#let iso = math.tilde.equiv;

#definition(name: "Isomorphism")[A morphism in a category that has an inverse
  $
    text("IsIso")(f: cal(C)(X,Y)) &= exists g: cal(C)(Y,X). g f = 1_X and f g = 1_Y \
    X iso Y &= exists f in cal(C)(X,Y). text("IsIso")(f)
  $

  #figure(
    table(stroke: 0.5pt,
    diagram({
      let X = (0,0)
      let Y = (1,0)
      node(X, $X$)
      node(Y, $Y$)
      edge(X, "->", Y, bend: 30deg)[$f$]
      edge(Y, "->", X, bend: 30deg)[$g$]
      edge(X, "->", X, bend: -130deg, loop-angle: 0deg)[$1_X=g f$]
      edge(Y, "->", Y, bend: -130deg, loop-angle: 180deg)[$1_Y=f g$]
    })
    )
  )
]

#definition(name: "Endomorphism")[A morphism whose domain and codomain are the same
  $
    text("IsEndo")(f: cal(C)(X,Y)) &= (X attach(=, t:?) Y) \
  $

  #figure(
    table(stroke: 0.5pt,
    diagram({
      let X = (0,0)
      node(X, $X$)
      edge(X, "->", X, bend: -130deg, loop-angle: 120deg)[$f$]
    })
    )
  )
]

#definition(name: "Automorphism")[An isomorphism thats also an endomorphism
  $
    text("IsAuto")(f: cal(C)(X,Y)) &= text("IsIso")(f) and text("IsEndo")(f)
  $

  #figure(
    table(stroke: 0.5pt,
    diagram({
      let X = (0,0)
      node(X, $X$)
      edge(X, "->", X, bend: -130deg, loop-angle: 120deg)[$f$]
      edge(X, "->", X, bend: -130deg, loop-angle: 20deg)[$g$]
      edge(X, "->", X, bend: -130deg, loop-angle: 230deg)[$1_X=f g= g f$]
    })
    )
  )
]

#definition(name: "Subcategory")[A subset of objects and morphisms of a category that is also a category
  $
    cal(D) subset.eq cal(C) &=> text("IsCat")(cal(D))
  $
]

#definition(name: "Opposite Category")[The category with all morphisms domain and codomain swapped
  $
    cal(C)^op &=> forall X in cal(C). X in cal(C)^op 
    & text("same objects") \
    &and forall f in cal(C)(X,Y). f^op in cal(C)^op (Y,X)
    & text("reversed morphisms")
  $
]

#theorem(name: "Dual Theorem")[If a statement applies to all categories, then it also applies to opposite categories. The theorem $P$ on the opposite category is called the dual theorem.
  $
    forall cal(C). P(cal(C)) => P(cal(C)^op)
  $
]

#definition(name: "Monomorphism")[A morphism when composed with any pair of parallel morphism are equal.
  $
    text("IsMono")(f) = forall h,k. h != k => f h = f k
  $
  #figure(
    table(stroke: 0.5pt,
    diagram({
      let X = (1,0)
      let Y = (2,0)
      let Z = (0,0)
      node(X, $X$)
      node(Y, $Y$)
      node(Z, $Z$)
      edge(X, ">->", Y)[$f$]
      edge(Z, "->", X, shift: 5pt)[$h$]
      edge(Z, "->", X, shift: -5pt, label-sep: -1pt)[$k$]
      edge(Z, "->", Y, bend: -30deg)[$f h = f k$]
    })
    )
  )
]

#definition(name: "Epimorphism")[A morphism when pre-composed with any pair of parallel morphism are equal.
  $
    text("IsEpi")(f) = forall h,k. h != k => h f = k f
  $

  #figure(
    table(stroke: 0.5pt,
    diagram({
      let X = (1,0)
      let Y = (2,0)
      let Z = (0,0)
      node(X, $X$)
      node(Y, $Y$)
      node(Z, $Z$)
      edge(Y, "->>", X)[$f$]
      edge(X, "->", Z, shift: 5pt, label-sep: -1pt)[$k$]
      edge(X, "->", Z, shift: -5pt)[$h$]
      edge(Y, "->", Z, bend: 30deg)[$h f = k f$]
    })
    )
  )
]

#theorem(name: "Mono-Epi Dual Theorem")[A monomorphism is an epimorphism in its opposite category and vice versa.
  $
    forall cal(C). text("IsMono")(f: cal(C)(X,Y)) => text("IsEpi")(f^op: cal(C)^op (Y,X)) \
    forall cal(C). text("IsEpi")(f: cal(C)(X,Y)) => text("IsMono")(f^op: cal(C)^op (Y,X))
  $
]

TODO

- section
- retraction
- functor
- forgetful functor
- contravariant functor
- naturality... onwards

= Meeting 1: @riehl2017category Chapter 2 (#datetime(year: 2025, month: 10, day:10).display())

1. Universal Properties
2. Representable Functors
3. Yoneda Lemma
4. Universal Property as Representable Functor
5. All presheaves are colimits of representable functors (Towards the future)

object that uniquely determines the natural isomorphism are the "legs" that define the universal property

// Add bibliography and create Bibiliography section
#bibliography("bibliography.bib")

// Create appendix section
// #show: arkheion-appendices
// =

// == Appendix section

// #lorem(100)


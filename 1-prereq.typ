#import "@preview/lemmify:0.1.8": *
#import "@preview/fletcher:0.5.8" as fletcher: diagram, edge, node

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
#show: thm-rules

#let grayed(x) = text(fill: gray, $#x$)

// end of preamble -------------------------

= Pre-Requisite: @riehl2017category Chapter 1

#definition(
  name: "Category",
)[A #emph("category") $cal(C)$ consists of #emph("objects") $X, Y, Z, ... in cal(C)$ and #emph("morphisms") $f, g, h, ... in cal(C)(X,Y)$ where $X in cal(C)$ is its #emph("domain") and $Y in cal(C)$ is its #emph("codomain").

  #figure(
    table(
      align: center,
      columns: (auto, auto, auto),
      row-gutter: (2pt, auto),
      stroke: 0.5pt,
      inset: 7pt,
      [hom], [type], [diagram],
      $f in cal(C)(X,Y)$, $f: X -> Y$, $X attach(->, t: f) Y$,
    ),
    caption: [Different notations for morphisms],
  )

  $
    text("IsCat")(cal(C))
    &= forall X grayed(in cal(C)). 1_X grayed(in cal(C)(X,X))
    & text("identity") \
    &and forall f grayed(in cal(C)(X,Y)), g grayed(in cal(C)(Y,Z)). g f grayed(in cal(C)(X,Z))
    & text("composition") \
    &and forall f grayed(in cal(C)(X,Y)). 1_Y f = f = f 1_X
    & text("unital") \
    &and forall f grayed(in cal(C)(X,Y)), g grayed(in cal(C)(Y,Z)), h grayed(in cal(C)(Z,W)). h (g f) = (h g) f
    & text("associative")
  $

  #figure(
    table(
      align: horizon + center,
      columns: (auto, auto, auto, auto),
      row-gutter: (2pt, auto),
      stroke: 0.5pt,
      inset: 7pt,
      [identity], [composition], [unital], [associative],
      diagram({
        let X = (0, 0)
        node(X, $X$)
        edge(X, "->", X, bend: -130deg, loop-angle: 120deg)[$1_X$]
      }),
      diagram({
        let X = (0, 1)
        let Y = (0, 0)
        let Z = (1, 0)
        node(X, $X$)
        node(Y, $Y$)
        node(Z, $Z$)
        edge(X, "->", Y)[$f$]
        edge(Y, "->", Z)[$g$]
        edge(X, "->", Z, label-side: right)[$g f$]
      }),
      diagram({
        let X1 = (0, 0)
        let X2 = (0, 1)
        let Y1 = (1, 0)
        let Y2 = (1, 1)
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
        let X = (0, 0)
        let Y = (1, 0)
        let Z = (2, 0)
        let W = (3, 0)
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
      }),
    ),
    caption: [Commutative Diagram for each property of a category],
  )
]

#let Mor = $text("Mor")$;
#let Set = $text("Set")$;

#definition(name: "Small Category")[A category where it has only a set's worth of morphisms
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

#definition(name: "Isomorphism")[A morphism in a category that has an #emph("inverse")
  $
    text("IsIso")(f grayed(in cal(C)(X,Y))) & = exists g grayed(in cal(C)(Y,X)). g f = 1_X and f g = 1_Y \
                            X iso Y & = exists f grayed(in cal(C)(X,Y)). text("IsIso")(f)
  $

  #figure(
    table(
      stroke: 0.5pt,
      diagram({
        let X = (0, 0)
        let Y = (1, 0)
        node(X, $X$)
        node(Y, $Y$)
        edge(X, "->", Y, bend: 30deg)[$f$]
        edge(Y, "->", X, bend: 30deg)[$g$]
        edge(X, "->", X, bend: -130deg, loop-angle: 0deg)[$1_X=g f$]
        edge(Y, "->", Y, bend: -130deg, loop-angle: 180deg)[$1_Y=f g$]
      }),
    ),
  )
]

#definition(name: "Endomorphism")[A morphism whose domain and codomain are the same
  $
    text("IsEndo")(f grayed(in cal(C)(X,Y))) & = (X attach(=, t: ?) Y) \
  $

  #figure(
    table(
      stroke: 0.5pt,
      diagram({
        let X = (0, 0)
        node(X, $X$)
        edge(X, "->", X, bend: -130deg, loop-angle: 120deg)[$f$]
      }),
    ),
  )
]

#definition(name: "Automorphism")[An isomorphism thats also an endomorphism
  $
    text("IsAuto")(f grayed(in cal(C)(X,Y))) & = text("IsIso")(f) and text("IsEndo")(f)
  $

  #figure(
    table(
      stroke: 0.5pt,
      diagram({
        let X = (0, 0)
        node(X, $X$)
        edge(X, "->", X, bend: -130deg, loop-angle: 120deg)[$f$]
        edge(X, "->", X, bend: -130deg, loop-angle: 20deg)[$g$]
        edge(X, "->", X, bend: -130deg, loop-angle: 230deg)[$1_X=f g= g f$]
      }),
    ),
  )
]

#definition(name: "Subcategory")[A subset of objects and morphisms of a category that is also a category
  $
    cal(D) subset.eq cal(C) & => text("IsCat")(cal(D))
  $
]

#definition(name: "Opposite Category")[The category with all morphisms domain and codomain swapped
  $
    cal(C)^op & => forall X in cal(C). X in cal(C)^op                &       text("same objects") \
              & and forall f grayed(in cal(C)(X,Y)). f^op grayed(in cal(C)^op (Y,X)) & text("reversed morphisms")
  $
]

#theorem(
  name: "Dual Theorem",
)[If a statement applies to all categories, then it also applies to opposite categories. The theorem $P'$ on the opposite category is called the dual theorem of $P$.
  $
    forall cal(C). P(cal(C)) => P'(cal(C)^op)
  $
]

#definition(name: "Monomorphism")[A morphism when composed with any pair of parallel morphism are equal.
  $
    text("Monic")(f grayed(in cal(C)(X,Y))) = forall h,k grayed(in cal(C)(Z,X)). f h = f k => h = k
  $
  #figure(
    table(
      stroke: 0.5pt,
      diagram({
        let X = (1, 0)
        let Y = (2, 0)
        let Z = (0, 0)
        node(X, $X$)
        node(Y, $Y$)
        node(Z, $Z$)
        edge(X, ">->", Y)[$f$]
        edge(Z, "->", X, shift: 5pt)[$h$]
        edge(Z, "->", X, shift: -5pt, label-sep: -1pt)[$k$]
        edge(Z, "->", Y, bend: -30deg)[$f h = f k$]
      }),
    ),
  )
  $
    text("Monic")(f grayed(in cal(C)(X,Y))) => exists f_* : cal(C)(Z,X) arrow.hook cal(C)(Z,Y).
  $
  #align(center)[If $X attach(>->, t: f) Y$ is monic, there is an injective map $f_*$ of morphisms from any $Z$ to $X$ to morphisms from $Z$ to $Y$ i.e. if $f_*(h) = g$ and $f_*(k) = g$ then $h = k$ e.g. $g = f h = f k$]
]

#definition(name: "Epimorphism")[A morphism when pre-composed with any pair of parallel morphism are equal.
  $
    text("Epic")(f grayed(in cal(C)(Y,X))) = forall h,k grayed(in cal(C)(X,Z)). h f = k f => h = k
  $

  #figure(
    table(
      stroke: 0.5pt,
      diagram({
        let X = (1, 0)
        let Y = (2, 0)
        let Z = (0, 0)
        node(X, $X$)
        node(Y, $Y$)
        node(Z, $Z$)
        edge(Y, "->>", X)[$f$]
        edge(X, "->", Z, shift: 5pt, label-sep: -1pt)[$k$]
        edge(X, "->", Z, shift: -5pt)[$h$]
        edge(Y, "->", Z, bend: 30deg)[$h f = k f$]
      }),
    ),
  )
  $
    text("Epic")(f grayed(in cal(C)(Y,X))) => exists f^* : cal(C)(X,Z) arrow.hook cal(C)(Y,Z).
  $
  #align(center)[If $Y attach(->>, t: f) X$ is epic, there is an injective map $f^*$ of morphisms from $X$ to any $Z$ to morphisms from $Y$ to $Z$ i.e. if $f^*(h) = g$ and $f^*(k) = g$ then $h = k$ e.g. $g = h f = k f$]
]

#theorem(name: "Mono-Epi Dual Theorem")[A monomorphism is an epimorphism in its opposite category and vice versa.
  $
    forall cal(C). text("Monic")(f grayed(in cal(C)(X,Y))) => text("Epic")(f^op grayed(in cal(C)^op (Y,X))) \
    forall cal(C). text("Epic")(f grayed(in cal(C)(X,Y))) => text("Monic")(f^op grayed(in cal(C)^op (Y,X)))
  $
]

#definition(
  name: "Sections and Retractions",
)[A #emph("section") is a right inverse to the #emph("retraction") that is a left inverse. The object defining the identity is called the #emph("retract").
  $
    #text("IsSec") (s,r) = #text("IsRet") (r,s) = (r s attach(=, t: ?) 1_X) \
    #text("Retract") (X grayed(in cal(C)),Y grayed(in cal(C))) = exists s grayed(in cal(C) (X,Y)), r grayed(in cal(C)(Y,X)). #text("IsSec") (s,r) 
  $

  #figure(
    table(
      stroke: 0.5pt,
      diagram({
        let X = (0, 0)
        let Y = (1, 0)
        node(X, $X$)
        node(Y, $Y$)
        edge(X, "->", Y, bend: 30deg)[$s$]
        edge(Y, "->", X, bend: 30deg)[$r$]
        edge(X, "->", X, bend: -130deg, loop-angle: 0deg)[$1_X=r s$]
      }),
    ),
  )
]

#theorem(name: "Sections are Monic, Retractions are Epic")[Sections are monomorphisms and retractions are epimorphisms. We call them #emph("split monomorphisms") and #emph("split epimorphisms") respectively to emphasize this property.
  $
    forall cal(C). text("IsSec")(s,r) => text("Monic")(s) and text("Epic")(r)
  $

  #figure(
    table(
      stroke: 0.5pt,
      diagram({
        let X = (1, 0)
        let Y = (2, 0)
        let ZM = (0, -1)
        let ZE = (0, 1)
        node(X, $X$)
        node(Y, $Y$)
        node(ZM, $Z_M$)
        node(ZE, $Z_E$)
        edge(X, ">->", Y, bend: 30deg)[$s$]
        edge(Y, "->>", X, bend: 30deg)[$r$]
        edge(X, "->", X, bend: -130deg, loop-angle: 90deg)[$1_X=r s$]
        edge(ZM, "->", X, bend: 0deg, label-side: center)[$h_m$]
        edge(ZM, "->", X, bend: -30deg, label-side: center)[$k_m$]
        edge(X, "->", ZE, bend: -30deg, label-side: center)[$h_e$]
        edge(X, "->", ZE, bend: 0deg, label-side: center)[$k_e$]
      }),
    ),
  )
]
#proof(name: "Sections are Monic")[
  $
    &forall cal(C). text("IsSec")(s,r) => text("Monic")(s) \
    =&forall cal(C). (r s = 1_X) => (forall h_m, k_m. s h_m = s k_m => h_m = k_m) & text("by definition") \
    =&forall cal(C). r s = 1_X => forall h_m, k_m. s h_m = s k_m => 1_X h_m = 1_X k_m & text("by unital") \
    =&forall cal(C). r s = 1_X => forall h_m, k_m. s h_m = s k_m => r s h_m = r s k_m & text("by section") \
    =&forall cal(C). r s = 1_X => forall h_m, k_m. top \
    =&forall cal(C). r s = 1_X => top \
    =&forall cal(C). top \
    =&top
  $
]

#theorem(name: "Isomorphisms are Monic and Epic")[
  $
    text("IsIso")(f) => text("Monic")(f) and text("Epic")(f) 
  $
  #align(center)[If $f in cal(C)(X,Y)$ has an inverse $g$, then $f$ is a section to $g$ when $X$ is the retract, and is a retraction to $g$ when $Y$ is the retract. i.e. $text("IsSec")(f,g) and text("IsRet")(g,f)$]
]


TODO

- functor
- forgetful functor
- contravariant functor
- naturality... onwards

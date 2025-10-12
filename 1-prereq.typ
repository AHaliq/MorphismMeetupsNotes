#import "@preview/equate:0.3.2": equate
#import "@preview/lemmify:0.1.8": *
#import "@preview/fletcher:0.5.8" as fletcher: diagram, edge, node

// equate ----------------------------------

#show: equate.with(breakable: true, sub-numbering: true)
#set math.equation(numbering: "(1.1)")

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
)[A #emph("category") $cal(C)$ consists of #emph("objects") $X, Y, Z, ... in cal(C)$ and #emph("morphisms") $f, g, h, ... in cal(C)(X,Y)$ where $X in cal(C)$ is its #emph("domain") and $Y in cal(C)$ is its #emph("codomain"). Every object has an #emph("identity") morphism that is #emph("unital") with respect to #emph("composition") of morphisms that is #emph("associative").

  $
    text("IsCat")(cal(C))
    &= forall X grayed(in cal(C)). 1_X grayed(in cal(C)(X,X)) & text("Identity") #<identity> \
    &and forall f grayed(in cal(C)(X,Y)), g grayed(in cal(C)(Y,Z)). g f grayed(in cal(C)(X,Z)) & text("Composition") #<composition> \
    &and forall f grayed(in cal(C)(X,Y)). 1_Y f = f = f 1_X & text("Unital") #<unital> \
    &and forall f grayed(in cal(C)(X,Y)), g grayed(in cal(C)(Y,Z)), h grayed(in cal(C)(Z,W)). h (g f) = (h g) f & text("Associative") #<associative>
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
  )
  Morphisms can be notated as follows:
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
  )
  The hom-set notation is explicit about the underlying category whereas the type notation leaves it implicit. The commutative diagram notation notates the morphism as labels on arrows between objects.
] <category>

#let Mor = $text("Mor")$;
#let Set = $text("Set")$;

#definition(name: "Small Category")[A category where it has only a set's worth of morphisms
  $
    Mor cal(C) in Set
  $
] <small>

#definition(name: "Locally Small Category")[A category where its homs are a set's worth
  $
    cal(C)(X,Y) in Set
  $
] <locallysmall>

#let iso = math.tilde.equiv;

#definition(name: "Isomorphism")[A morphism in a category that has an #emph("inverse")
  $
    text("Iso")(f grayed(in cal(C)(X,Y))) & = exists g grayed(in cal(C)(Y,X)). g f = 1_X and f g = 1_Y \
                                  X iso Y & = exists f grayed(in cal(C)(X,Y)). text("Iso")(f)
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
] <isomorphism>

#definition(name: "Endomorphism")[A morphism whose domain and codomain are the same
  $
    text("Endo")(f grayed(in cal(C)(X,Y))) & = (X attach(=, t: ?) Y) \
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
] <endomorphism>

#definition(name: "Automorphism")[An isomorphism thats also an endomorphism
  $
    text("Auto")(f grayed(in cal(C)(X,Y))) & = text("Iso")(f) and text("Endo")(f)
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
] <automorphism>

#definition(name: "Subcategory")[A subset of objects and morphisms of a category that is also a category
  $
    cal(D) subset.eq cal(C) & => text("IsCat")(cal(D))
  $
] <subcategory>

#definition(name: "Opposite Category")[The category with all morphisms domain and codomain swapped
  $
    cal(C)^op & => forall X in cal(C). X in cal(C)^op                                &       text("same objects") \
              & and forall f grayed(in cal(C)(X,Y)). f^op grayed(in cal(C)^op (Y,X)) & text("reversed morphisms")
  $
] <oppositecategory>

#theorem(
  name: "Dual Theorem",
)[If a statement $P$ applies to all categories, then it also applies to opposite categories.
  $
    (grayed(forall cal(C).) P(cal(C))) <=> (grayed(forall cal(C).) P(cal(C)^op))
  $
] <dualtheorem>

#definition(
  name: "Monomorphism",
)[A morphism when composed with any pair of parallel morphism are equal implies that the pair of parallel morphism are equal.
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
] <monomorphism>

#theorem(
  name: "Mono Injective Hom",
)[If $X attach(>->, t: f) Y$ is monic, there is an injective map $f_*$ of morphisms from any $Z$ to $X$ to morphisms from $Z$ to $Y$ i.e. if $f_*(h) = g$ and $f_*(k) = g$ then $h = k$ where $f h$ and $f k$ is a candidate for $g$.

  $
    text("Monic")(f grayed(in cal(C)(X,Y))) => exists f_* : cal(C)(Z,X) arrow.hook cal(C)(Z,Y).
  $
]

#definition(
  name: "Epimorphism",
)[A morphism when pre-composed with any pair of parallel morphism are equal implies that the pair of parallel morphism are equal.
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
] <epimorphism>

#theorem(
  name: "Epi Injective Hom",
)[If $Y attach(->>, t: f) X$ is epic, there is an injective map $f^*$ of morphisms from $X$ to any $Z$ to morphisms from $Y$ to $Z$ i.e. if $f^*(h) = g$ and $f^*(k) = g$ then $h = k$ where $h f$ and $k f$ is a candidate for $g$.

  $
    text("Epic")(f grayed(in cal(C)(Y,X))) => exists f^* : cal(C)(X,Z) arrow.hook cal(C)(Y,Z).
  $
]

#theorem(name: "Mono-Epi Dual Theorem")[A monomorphism is an epimorphism in its opposite category and vice versa.
  $
    forall cal(C). text("Monic")(f grayed(in cal(C)(X,Y))) <=> text("Epic")(f^op grayed(in cal(C)^op (Y,X)))
  $
]

#definition(
  name: "Sections and Retractions",
)[A #emph("section") is a right inverse to the #emph("retraction") that is a left inverse. The object defining the identity is called the #emph("retract").
  $
    #text("Section") (s,r) = #text("Retraction") (r,s) = (r s attach(=, t: ?) 1_X) \
    #text("Retract") (X grayed(in cal(C)),Y grayed(in cal(C))) = exists s grayed(in cal(C) (X,Y)), r grayed(in cal(C)(Y,X)). #text("Section") (s,r)
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
] <section>

#theorem(
  name: "Sections are Monic, Retractions are Epic",
)[Sections are monomorphisms and retractions are epimorphisms. We call them #emph("split monomorphisms") and #emph("split epimorphisms") respectively to emphasize this property.
  $
    text("Section")(s,r) => text("Monic")(s) and text("Epic")(r)
  $
  #figure(
    table(
      stroke: 0.5pt,
      diagram({
        let X = (1, 0)
        let Y = (2, 0)
        let W = (0, -1)
        let Z = (0, 1)
        node(X, $X$)
        node(Y, $Y$)
        node(W, $W$)
        node(Z, $Z$)
        edge(X, ">->", Y, bend: 30deg)[$s$]
        edge(Y, "->>", X, bend: 30deg)[$r$]
        edge(X, "->", X, bend: -130deg, loop-angle: 90deg)[$1_X=r s$]
        edge(W, "->", X, bend: 0deg, label-side: center)[$h$]
        edge(W, "->", X, bend: -30deg, label-side: center)[$k$]
        edge(X, "->", Z, bend: -30deg, label-side: center)[$i$]
        edge(X, "->", Z, bend: 0deg, label-side: center)[$j$]
        edge(W, "->", Y, bend: 40deg)[$s h = s k$]
        edge(Y, "->", Z, bend: 40deg)[$i r = j r$]
      }),
    ),
  )
]

#proof(
  name: "Sections are Monic",
)[
  $
    text("Section")(s,r) => text("Monic")(s)
  $
  Let $s in cal(C)(X,Y)$ be a section to $r in cal(C)(Y,X)$ such that $r s = 1_X$. We show that $s$ is monic. Suppose that $s h = s k$ we show that $h = k$. Composing with $r$ we get that $r s h = r s k$ and so $1_X h = 1_X k$. By the unital property of identity morphisms, $1_X h = h$ and likewise $1_X k = k$. Thus, $h = k$ concluding that $s$ is monic.
  $
    text("Section")(s,r) = & (r s = 1_X)                             &      #ref(<section>) \
        text("Monic")(s) = & (forall h, k. s h = s k => h = k)       & #ref(<monomorphism>) \
                         = & forall h, k. s h = s k => 1_X h = 1_X k &       #ref(<unital>) \
                         = & forall h, k. s h = s k => r s h = r s k &                      \
                         = & forall h, k. top                        &  #ref(<composition>) \
                         = & top
  $
] <sections-are-monic>

#proof(
  name: "Retractions are Epic",
)[
  $
    text("Section")(s,r) => text("Epic")(r)
  $
  Let $r in cal(C)(Y,X)$ be a retraction to $s in cal(C)(X,Y)$ such that $r s = 1_X$. We show that $r$ is epic. Suppose that $i r = j r$ we show that $i = j$. Composing with $s$ we get that $i r s = j r s$ and so $i 1_X = j 1_X$. By the unital property of identity morphisms, $i 1_X = i$ and likewise $j 1_X = j$. Thus, $i = j$ concluding $r$ is epic.
  $
    text("Section")(s,r) = & (r s = 1_X)                             &     #ref(<section>) \
         text("Epic")(r) = & (forall i, j. i r = j r => i = j)       & #ref(<epimorphism>) \
                         = & forall i, j. i r = j r => i 1_X = j 1_X &      #ref(<unital>) \
                         = & forall i, j. i r = j r => i r s = j r s &                     \
                         = & forall i, j. top                        & #ref(<composition>) \
                         = & top
  $
] <retractions-are-epic>

#theorem(name: "Isomorphisms are Monic and Epic")[
  $
    text("Iso")(f) => text("Monic")(f) and text("Epic")(f)
  $
  #figure(
    table(
      stroke: 0.5pt,
      diagram({
        let X = (1, 0)
        let Y = (2, 0)
        let W = (0, 0)
        let Z = (3, 0)
        node(X, $X$)
        node(Y, $Y$)
        node(W, $W$)
        node(Z, $Z$)
        edge(X, ">->>", Y, bend: 30deg)[$f$]
        edge(Y, ">->>", X, bend: 30deg)[$g$]
        edge(X, "->", X, bend: -130deg, loop-angle: -90deg)[$1_X=g f$]
        edge(Y, "->", Y, bend: -130deg, loop-angle: 90deg)[$1_Y=f g$]
        edge(W, "->", X, bend: 20deg, label-side: center)[$h$]
        edge(W, "->", X, bend: -20deg, label-side: center)[$k$]
        edge(Y, "->", Z, bend: 20deg, label-side: center)[$i$]
        edge(Y, "->", Z, bend: -20deg, label-side: center)[$j$]
        edge(W, "->", Y, bend: 80deg)[$f h = f k$]
        edge(X, "->", Z, bend: -80deg)[$i f = j f$]
      }),
    ),
  )
]

#proof(name: "Isomorphisms are Monic and Epic")[
  $
    text("Iso")(f) => text("Monic")(f) and text("Epic")(f)
  $
  Let $f in cal(C)(X,Y)$ be an isomorphism with the inverse $g in cal(C)(Y,X)$. Thus, $f$ is a section to $g$ when $X$ is the retract since $g f = 1_X$. Moreover, $f$ is a retraction to $g$ when $Y$ is the retract since $f g = 1_Y$. Since sections are monic and retractions are epic, $f$ is both monic and epic.
  $
      text("Iso")(f) = & (exists g. g f = 1_X and f g = 1_Y)       &  #ref(<isomorphism>) \
      =& exists g. text("Section")(f,g) and text("Section")(g, f) & #ref(<section>) \
      =& exists g. text("Monic")(f) and text("Epic")(f)         & #ref(<retractions-are-epic>) \
  $
]


TODO

- functor
- forgetful functor
- contravariant functor
- naturality... onwards

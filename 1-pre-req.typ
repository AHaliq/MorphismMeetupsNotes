#import "@preview/equate:0.3.2": equate
#import "@preview/fletcher:0.5.8" as fletcher: diagram, edge, node
#import "0-preamble.typ": definition, proof, style, theorem, thm-rules

#show: thm-rules
#show: style

// equate ----------------------------------

#show: equate.with(breakable: true, sub-numbering: true)
#set math.equation(numbering: "(1.1)")

// lemmify ---------------------------------


#let dim(x) = text(fill: gray, $#x$)

// end of preamble -------------------------

= Categories, Functors and Naturality

#let Category(x) = $text("Category")(#x)$
#let Identity(x) = $text("Identity")(#x)$

#let dom(x) = $text("dom")(#x)$
#let cod(x) = $text("cod")(#x)$
#definition(name: "Morphisms")[
  A morphism (or _arrow_) $f$ is a directed edge from a _domain_ object $X$ to a _codomain_ object $Y$. We can notate them as follows:
  #figure(
    table(
      align: center + horizon,
      columns: (auto, auto, auto, auto),
      row-gutter: (2pt, auto),
      stroke: 0.5pt,
      inset: 7pt,
      [hom], [type], [diagram], [algebra],
      $f in cal(C)(X,Y)$, $f: X -> Y$, $X attach(->, t: f) Y$, $dom(f) = X, cod(f) = Y$,
    ),
  )
]

#definition(
  name: "Category",
)[A _category_ $cal(C)$ consists of _objects_ $X, Y, Z, ... in cal(C)$ and _morphisms_ $f, g, h, ... in cal(C)(X,Y)$. Every object has an _identity_ morphism that is _unital_ with respect to _composition_ of morphisms that is _associative_.
  $
    Category(cal(C))
    &:= forall X dim(in cal(C)). 1_X dim(in cal(C)(X,X)) & text("Id") #<identity> \
    &and forall f dim(in cal(C)(X,Y)), g dim(in cal(C)(Y,Z)). g f dim(in cal(C)(X,Z)) & text("Comp") #<composition> \
    &and forall f dim(in cal(C)(X,Y)). 1_Y f = f = f 1_X & text("Unital") #<unital> \
    &and forall f dim(in cal(C)(X,Y)), g dim(in cal(C)(Y,Z)), h dim(in cal(C)(Z,W)). h (g f) = (h g) f & text("Assoc") #<associative>
  $
  When $cal(C)(X,Y)$ has $X$ and $Y$ unquantified, it notates them implicitly; $forall X,Y in cal(C). cal(C)(X,Y)$.
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
        edge(X, "->", W, bend: -40deg)[$h g f = h (g f) = (h g) f$]
      }),
    ),
  )
] <category>

#definition(name: "Composition is unique")[
  $
    forall f dim(in cal(C)(X,Y)), g dim(in cal(C)(Y,Z)). exists! h dim(in cal(C)(X,Z)). h = g f
  $
  $g f$ is notational shorthand for $g compose f$ where $compose : cal(C)(Y,Z) -> cal(C)(X,Y) -> cal(C)(X,Z)$, thus if the arguments are the same, then the resulting composition is unique. i.e. the composition operation returns a morphism, not a set of morphisms.
] <composition-unique>

#theorem(name: "Identity is unique")[
  $
    dim(forall X.) exists! 1_X dim(in cal(C)(X,X)) => forall f dim(in cal(C)(X,Y).) 1_Y f = f = f 1_X
  $
] <identity-unique>

#proof[
  Assuming there are two identity morphisms $1_X$ and $1'_X$ for every object $X$, then for any morphism $f: X -> Y$ by the unital property we know that $1_Y f = f = f 1_X$ and $1'_Y f = f = f 1'_X$. If we let $f= 1_X$ and $f = 1'_X$ we can see that $1_X 1'_X = 1'_X = 1'_X 1_X = 1_X = 1_X 1'_X$ which quotients $1_X = 1'_X$ making the identity unique.
  $
        & dim(forall X in cal(C).) 1_X dim(in cal(C)(X,X))         &                   #ref(<identity>) \
    and & forall f dim(in cal(C)(X,Y)). 1_Y f = f = f 1_X          &                     #ref(<unital>) \
     => & dim(forall X in cal(C).) 1'_X dim(in cal(C)(X,X))        &                text("premise; id") \
    and & forall f' dim(in cal(C)(X,Y)). 1'_Y f' = f' = f' 1'_X    & text("premise; unital") #<iduniq1> \
     => & dim(forall X in cal(C).) (1_X 1'_X = 1'_X = 1'_X 1_X     &               text("Let") f = 1'_X \
    and & 1'_X 1_X = 1_X = 1_X 1'_X)                               &               text("Let") f' = 1_X \
     => & dim(forall X in cal(C).) 1_X = 1'_X                      &                text("transitive")= \
     => & dim(forall X in cal(C).) exists! 1_X dim(in cal(C)(X,X)) &              text("intro") exists! \
     => & forall f. 1_Y f = f = f 1_X                              &                    #ref(<iduniq1>)
  $
]

#let Thin(x) = $text("Thin")(#x)$;
#definition(
  name: "Thin Category",
)[Alternatively called a _posetal_ category, is a category where there is at most one morphism between any two objects. The name posetal comes from the category modelling a partially ordered set where there is at most one morphism between any two objects modelling the $<=$ relation.
  $
    Thin(cal(C)) & := |cal(C)(X,Y)| <= 1
  $
] <thin-category>

#let Mor = $text("Mor")$;
#let Set = $text("Set")$;

#let Small(x) = $text("Small")(#x)$;

#definition(name: "Small Category")[A category where it has only a set's worth of morphisms
  $
    Small(cal(C)) & := Mor cal(C) in Set
  $
] <small>

#let LocallySmall(x) = $text("LocallySmall")(#x)$;

#definition(name: "Locally Small Category")[A category where its homs are a set's worth
  $
    LocallySmall(cal(C)) & := cal(C)(X,Y) in Set
  $
] <locally-small>

#theorem(name: "Thin Categories are locally small")[
  $
    dim(forall cal(C).) Thin(cal(C)) => LocallySmall(cal(C))
  $
]

#proof[Trivially if all hom sets are of cardinality at most one, it as a set's worth.
  $
    Thin(cal(C)) = & |cal(C)(X,Y)| <= 1   & #ref(<thin-category>) \
                => & cal(C)(X,Y) in Set \
                 = & LocallySmall(cal(C)) & #ref(<locally-small>) \
  $
]

#let iso = math.tilde.equiv;
#let Iso(x) = $text("Iso")(#x)$;

#definition(name: "Isomorphism")[A morphism in a category that has an _inverse_
  $
    Iso(f dim(in cal(C)(X,Y))) & := exists g dim(in cal(C)(Y,X)). g f = 1_X and f g = 1_Y
  $
  $
    X iso Y & := exists f dim(in cal(C)(X,Y)). Iso(f)
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

#let Endo(x) = $text("Endo")(#x)$;

#definition(name: "Endomorphism")[A morphism whose domain and codomain are the same
  $
    Endo(f dim(in cal(C)(X,Y))) & := (X = Y) \
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
  Note that what distinguishes an arbitrary endomorphism from the identity is that the identity is guaranteed unital; #ref(<unital>), under composition.
] <endomorphism>

#let Auto(x) = $text("Auto")(#x)$;

#definition(name: "Automorphism")[An isomorphism thats also an endomorphism
  $
    Auto(f dim(in cal(C)(X,Y))) & := Iso(f) and Endo(f)
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

#theorem(
  name: "Identity Morphisms are Automorphisms",
)[
  $
    dim(forall X in cal(C).) Auto(1_X)
  $
]

#let Let = $text("Let")$

#proof[Identity morphisms are an endomorphism since their domain and codomain are the same object. They are also isomorphisms since they are their own inverse.
  $
       & dim(forall X in cal(C).) 1_X in cal(C)(X,X) &      #ref(<identity>) \
    => & dim(forall X in cal(C)). (1_X = 1_X)        &   text("reflexivity") \
     = & (1_X 1_X = 1_X)                             &        #ref(<unital>) \
     = & (1_X 1_X = 1_X and 1_X 1_X = 1_X)           & text("idempotent")and \
     = & exists g. g 1_X = 1_X and 1_Y g = 1_Y       &  text("intro") exists \
     = & Iso(1_X)                                    &   #ref(<isomorphism>) \
     = & Iso(1_X) and (X = X)                        &   text("reflexivity") \
     = & Iso(1_X) and Endo(1_X)                      &  #ref(<endomorphism>) \
     = & Auto(1_X)                                   &  #ref(<automorphism>) \
  $
  #figure(
    table(
      align: center + horizon,
      columns: (auto, auto),
      stroke: 0.5pt,
      diagram({
        let X = (0, 0)
        let Y = (1, 0)
        node(X, $X$)
        node(Y, $X$)
        edge(X, "->", Y, bend: 30deg)[$1_X$]
        edge(Y, "->", X, bend: 30deg)[$1_X$]
        edge(X, "->", X, bend: -130deg, loop-angle: 0deg)[$1_X = 1_X 1_X$]
        edge(Y, "->", Y, bend: -130deg, loop-angle: 180deg)[$1_X = 1_X 1_X$]
      }),
      diagram({
        let X = (0, 0)
        node(X, $X$)
        edge(X, "->", X, bend: -130deg, loop-angle: 120deg)[$1_X$]
        edge(X, "->", X, bend: -130deg, loop-angle: 20deg)[$1_X$]
        edge(X, "->", X, bend: -130deg, loop-angle: 230deg)[$1_X=1_X 1_X$]
      }),
    ),
  )
  Note that we can duplicate objects in the diagram for clarity; there is only one $X$.
]

#definition(name: "Subcategory")[A subset of objects and morphisms of a category that is also a category
  $
    dim(forall cal(C)\, cal(D).) cal(D) subset.eq cal(C) & => Category(cal(D))
  $
] <subcategory>

#let SliceU(x, y) = $#x#h(-0.1em)slash#y$;
#let SliceO(x, y) = $#x#h(-0em)backslash#h(-0.1em)#y$;
#definition(
  name: "Slice Categories",
)[A slice category of the underlying category $cal(C)$ fixes some object $C in cal(C)$. The slice category under $C$ has objects as morphisms from $C$. Similarly the slice category over $C$ has objects as morphisms to $C$.

  #smallcaps[$SliceU(C, cal(C))$ slice category of $cal(C)$ under $C$:]
  $
    dim(C in cal(C)). & SliceU(C, cal(C)) &= limits(union)_(X in cal(C)) cal(C)(C,X) \
    and & SliceU(C, cal(C))(f dim(in cal(C)(C,X)),g dim(in cal(C)(C,Y))) &= { h | h f = g }
  $
  #figure(
    table(
      align: center + horizon,
      columns: (auto, auto),
      stroke: 0.5pt,
      $cal(C)$, $SliceU(C, cal(C))$,
      diagram({
        let C = (0, 0)
        let X = (1, 0)
        let Y = (1, 1)
        node(C, $C$)
        node(X, $X$)
        node(Y, $Y$)
        edge(C, "->", X)[$f$]
        edge(C, "->", Y)[$g$]
        edge(X, "->", Y)[$h$]
      }),
      diagram({
        let f = (2, 0)
        let g = (2, 1)
        node(f, $f$)
        node(g, $g$)
        edge(f, "->", g)[$h$]
      }),
    ),
  )

  #smallcaps[$SliceO(C, cal(C))$ slice category of $cal(C)$ over $C$]:
  $
    dim(C in cal(C)). & SliceO(C, cal(C))(C) &= limits(union)_(X in cal(C)) cal(C)(X,C) \
    and & SliceO(C, cal(C))(C))(f dim(in cal(C)(X,C)),g dim(in cal(C)(Y,C))) &= { h | g h = f}
  $
  #figure(
    table(
      align: center + horizon,
      columns: (auto, auto),
      stroke: 0.5pt,
      $cal(C)$, $SliceO(C, cal(C))$,
      diagram({
        let C = (0, 0)
        let X = (1, 0)
        let Y = (1, 1)
        node(C, $C$)
        node(X, $X$)
        node(Y, $Y$)
        edge(X, "->", C)[$f$]
        edge(Y, "->", C)[$g$]
        edge(X, "->", Y)[$h$]
      }),
      diagram({
        let f = (2, 0)
        let g = (2, 1)
        node(f, $f$)
        node(g, $g$)
        edge(f, "->", g)[$h$]
        node(enclose: (f, g))
      }),
    ),
  )
] <slice-category>

#proof[The slice category under $C$ is a category because for every object $f: C -> X$ the identity is $1_f = 1_X$. Composition exists by virtue that the objects are morphisms that are composable (and associative) in the underlying category. The unital property holds similarly.
  $
    Category(SliceU(C, cal(C))) =& forall f mat(delim: #none, in, cal(C)(C,X); in, SliceU(C, cal(C))). 1_f dim(in SliceU(C, cal(C))(f,f)) = 1_X dim(in cal(C)(X,X)) \
    and& forall h mat(delim: #none, in, cal(C)(X,Y); in, SliceU(C, cal(C))(f,g)), j mat(delim: #none, in, cal(C)(Y,Z); in, SliceU(C, cal(C))(g,i)). j h in mat(delim: #none, in, cal(C)(X,Z); in, SliceU(C, cal(C))(f,i)) \
    and& forall h dim(in SliceU(C, cal(C))(f,g)). 1_g h = 1_Y h = h = h 1_X = h 1_f \
    and& forall h, j, l. l (j h) = (l j) h
  $

  #figure(
    table(
      stroke: 0.5pt,
      diagram({
        let C = (2, 0)
        let X2 = (0, 1)
        let X = (1, 1)
        let Y = (2, 1)
        let Z = (3, 1)
        let W = (4, 1)
        node(C, $C$)
        node(X, $X$)
        node(X2, $X$)
        node(Y, $Y$)
        node(Z, $Z$)
        node(W, $W$)
        edge(C, "->", X2, bend: -20deg)[$f$]
        edge(C, "->", X, bend: -5deg)[$f$]
        edge(X2, "->", X, label-side: right)[$1_X = 1_f$]
        edge(C, "->", Y)[$g$]
        edge(C, "->", Z, bend: 5deg)[$i$]
        edge(C, "->", W, bend: 20deg)[$k$]
        edge(X, "->", Y)[$h$]
        edge(Y, "->", Z)[$j$]
        edge(Z, "->", W)[$l$]

        let f = (1, 1.6)
        let g = (2, 1.6)
        let i = (3, 1.6)
        let k = (4, 1.6)
        node(f, $f$)
        node(g, $g$)
        node(i, $i$)
        node(k, $k$)
        edge(f, "->", g)[$h$]
        edge(g, "->", i)[$j$]
        edge(i, "->", k)[$l$]
      }),
    ),
  )
]

#proof[Likewise for the slice category over $C$, for every object $f: X -> C$ the identity is $1_f = 1_X$. Associative composition and unital properties hold by the same argument.
  $
    Category(SliceO(C, cal(C))) =& forall f mat(delim: #none, in, cal(C)(X,C); in, SliceO(C, cal(C))). 1_f dim(in SliceO(C, cal(C))(f,f)) = 1_X in cal(C)(X,X) \
    and& forall h mat(delim: #none, in, cal(C)(X,Y); in, SliceO(C, cal(C))(f,g)), j mat(delim: #none, in, cal(C)(Y,Z); in, SliceO(C, cal(C))(g,i)). j h in mat(delim: #none, in, cal(C)(X,Z); in, SliceO(C, cal(C))(f,i)) \
    and& forall h dim(in SliceO(C, cal(C))(f,g)). 1_g h = 1_Y h = h = h 1_X = h 1_f \
    and& forall h, j, l. l (j h) = (l j) h
  $

  #figure(
    table(
      stroke: 0.5pt,
      diagram({
        let C = (2, 0)
        let X2 = (0, 1)
        let X = (1, 1)
        let Y = (2, 1)
        let Z = (3, 1)
        let W = (4, 1)
        node(C, $C$)
        node(X, $X$)
        node(X2, $X$)
        node(Y, $Y$)
        node(Z, $Z$)
        node(W, $W$)
        edge(C, "<-", X2, bend: -20deg)[$f$]
        edge(C, "<-", X, bend: -5deg)[$f$]
        edge(X2, "->", X, label-side: right)[$1_X = 1_f$]
        edge(C, "<-", Y)[$g$]
        edge(C, "<-", Z, bend: 5deg)[$i$]
        edge(C, "<-", W, bend: 20deg)[$k$]
        edge(X, "->", Y)[$h$]
        edge(Y, "->", Z)[$j$]
        edge(Z, "->", W)[$l$]

        let f = (1, 1.6)
        let g = (2, 1.6)
        let i = (3, 1.6)
        let k = (4, 1.6)
        node(f, $f$)
        node(g, $g$)
        node(i, $i$)
        node(k, $k$)
        edge(f, "->", g)[$h$]
        edge(g, "->", i)[$j$]
        edge(i, "->", k)[$l$]
      }),
    ),
  )
]

#theorem(
  name: "Slice Categories are not necessarily Posetal",
)[Let $h, h' in SliceO(C, cal(C))(f,g)$. Although composition is unique, it is unique for both operands. i.e. $forall f, g. exists! g f$. However, here it varies: $g h = f$, $g h' = f$ where $h != h'$. Compositions are unique, but "decompositions" (of $f$) are not necessarily. Thus, slice categories are not necessarily posetal, since theres more than one unique morphism.
  $
    exists cal(C)dim(\, C in cal(C).) not Thin(SliceU(C, cal(C))) \
    exists cal(C)dim(\, C in cal(C).) not Thin(SliceO(C, cal(C))) \
  $
]

#proof[
  For $SliceU(C, cal(C))$, we let $C = X = Y = { star , star'} = 2$ and $f = g = h' = hat(star)$ where $hat(star)$ is a constant function returning $star$. Let $h = id$ the identity morphism. We can see that $h f = g$ and $h' f = g$. Since $h != h'$, there is more than one morphism from $X$ to $Y$. Thus $SliceU(C, cal(C))$ is not posetal.

  Let $2 = { star, star' }, 
    dim(forall x in 2.) id(x) = x,
    dim(forall x in 2.) hat(star)(x) = star$
  #figure(
    table(
      stroke: none,
      columns: (auto, auto, auto),
      align: center + horizon,
      [
        $
             & SliceU(C, cal(C))(f,g) = { h, h' } \
          => & not Thin(SliceU(C, cal(C)))        & #ref(<thin-category>)
        $
      ],
      diagram({
        let C = (0, 0)
        let X = (1, 0)
        let Y = (1, 1)
        node(C, $2$)
        node(X, $2$)
        node(Y, $2$)
        edge(C, "->", X)[$hat(star)$]
        edge(C, "->", Y, label-side: right)[$hat(star)$]
        edge(X, "->", Y, bend: 10deg)[$hat(star)$]
        edge(X, "->", Y, bend: -10deg)[$id$]
      }),
      diagram({
        let f = (0, 0)
        let g = (1, 0)
        node(f, $hat(star)$)
        node(g, $hat(star)$)
        edge(f, "->", g, bend: 10deg)[$hat(star)$]
        edge(f, "->", g, bend: -10deg)[$id$]
      }),
    ),
  )
  Similarly for $SliceO(C, cal(C))$.
  #figure(
    table(
      stroke: none,
      columns: (auto, auto, auto),
      align: center + horizon,
      [
        $
             & SliceO(C, cal(C))(f,g) = { h, h' } \
          => & not Thin(SliceU(C, cal(C)))        & #ref(<thin-category>)
        $
      ],
      diagram({
        let C = (0, 0)
        let X = (1, 0)
        let Y = (1, 1)
        node(C, $2$)
        node(X, $2$)
        node(Y, $2$)
        edge(C, "<-", X)[$hat(star)$]
        edge(C, "<-", Y, label-side: right)[$hat(star)$]
        edge(X, "->", Y, bend: 10deg)[$hat(star)$]
        edge(X, "->", Y, bend: -10deg)[$id$]
      }),
      diagram({
        let f = (0, 0)
        let g = (1, 0)
        node(f, $hat(star)$)
        node(g, $hat(star)$)
        edge(f, "->", g, bend: 10deg)[$hat(star)$]
        edge(f, "->", g, bend: -10deg)[$id$]
      }),
    ),
  )
] <slice-not-thin>

#definition(name: "Opposite Category")[The category with all morphisms domain and codomain swapped
  $
    dim(forall cal(C).) cal(C)^op => & forall X in cal(C). X in cal(C)^op               &       text("same objects") \
                                 and & forall f in cal(C)(X,Y). f^op in cal(C)^op (Y,X) & text("reversed morphisms")
  $
] <opposite-category>

#theorem(
  name: "Dual Theorem",
)[If a statement $P$ applies to all categories, then it also applies to opposite categories.
  $
    (dim(forall cal(C).) P(cal(C))) <=> (dim(forall cal(C).) P(cal(C)^op))
  $
] <dual-theorem>

#let Monic(x) = $text("Monic")(#x)$;

#definition(
  name: "Monomorphism",
)[A morphism when composed with any pair of parallel morphisms resulting in equal morphisms implies that the pair of parallel morphism are equal.
  $
    Monic(f dim(in cal(C)(X,Y))) & := forall h,k dim(in cal(C)(Z,X)). f h = f k => h = k
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
        edge(Z, "->", X, bend: 15deg, label-side: center)[$h$]
        edge(Z, "->", X, bend: -15deg, label-side: center)[$k$]
        edge(Z, "->", Y, bend: -30deg)[$f h = f k$]
      }),
    ),
  )
] <monomorphism>

#definition(
  name: "Post-composition Function",
)[A map indexed by the morphism $f$ from morphisms $h$ to $g$ such that $g = f h$.
  $
    f_* : cal(C)(Z,X) -> cal(C)(Z,Y) & := [h mapsto g] text("such that") g = f h
  $
]

#theorem(
  name: "Monic Injective Hom",
)[If $X attach(>->, t: f) Y$ is monic, there is an injective map $f_*$ of morphisms from any $Z$ to $X$ to morphisms from $Z$ to $Y$ i.e. if $f_*(h) = g$ and $f_*(k) = g$ then $h = k$ where $f h = f k = g$.

  $
    dim(forall cal(C).) Monic(f dim(in cal(C)(X,Y))) => exists f_* : cal(C)(Z,X) arrow.hook cal(C)(Z,Y).
  $
]

#let Epic(x) = $text("Epic")(#x)$;

#definition(
  name: "Epimorphism",
)[A morphism when pre-composed with any pair of parallel morphisms resulting in equal morphisms implies that the pair of parallel morphism are equal.
  $
    Epic(f dim(in cal(C)(Y,X))) & := forall h,k dim(in cal(C)(X,Z)). h f = k f => h = k
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
        edge(X, "->", Z, bend: 15deg, label-side: center)[$k$]
        edge(X, "->", Z, bend: -15deg, label-side: center)[$h$]
        edge(Y, "->", Z, bend: 30deg)[$h f = k f$]
      }),
    ),
  )
] <epimorphism>

#definition(
  name: "Pre-Composition Function",
)[A map indexed by the morphism $f$ from morphisms $h$ to $g$ such that $g = h f$.
  $
    f^* : cal(C)(X,Z) -> cal(C)(Y,Z) & := [h mapsto g] text("such that") g = h f
  $
]

#theorem(
  name: "Epic Injective Hom",
)[If $Y attach(->>, t: f) X$ is epic, there is an injective map $f^*$ of morphisms from $X$ to any $Z$ to morphisms from $Y$ to $Z$ i.e. if $f^*(h) = g$ and $f^*(k) = g$ then $h = k$ where $h f = k f = g$.

  $
    dim(forall cal(C).) Epic(f dim(in cal(C)(Y,X))) => exists f^* : cal(C)(X,Z) arrow.hook cal(C)(Y,Z).
  $
]

#theorem(name: "Monic-Epic Dual Theorem")[A monomorphism is an epimorphism in its opposite category and vice versa.
  $
    dim(forall cal(C).) Monic(f dim(in cal(C)(X,Y))) <=> Epic(f^op dim(in cal(C)^op (Y,X)))
  $
]

#let Section(x, y) = $text("Section")(#x,#y)$;
#let Retraction(x, y) = $text("Retraction")(#x,#y)$;
#let Retract(x, y) = $text("Retract")(#x,#y)$;

#definition(
  name: "Sections and Retractions",
)[A _section_ is a right inverse to the _retraction_ that is a left inverse. The object defining the identity is called the _retract_.
  $
               Section(s, r) = Retraction(r, s) & := (r s = 1_X) \
    Retract(X dim(in cal(C)), Y dim(in cal(C))) & := exists s dim(in cal(C) (X,Y)), r dim(in cal(C)(Y,X)). Section(s, r)
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
)[Sections are monomorphisms and retractions are epimorphisms. We call them _split monomorphisms_ and _split epimorphisms_ respectively to emphasize this property.
  $
    dim(forall cal(C).) Section(s dim(in cal(C)(X,Y)), r dim(in cal(C)(Y,X))) => Monic(s) and Epic(r)
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
    dim(forall cal(C).) Section(s dim(in cal(C)(X,Y)), r dim(in cal(C)(Y,X))) => Monic(s)
  $
  Let $s in cal(C)(X,Y)$ be a section to $r in cal(C)(Y,X)$ such that $r s = 1_X$. We show that $s$ is monic. Suppose that $s h = s k$ we show that $h = k$. Composing with $r$ we get that $r s h = r s k$ and so $1_X h = 1_X k$. By the unital property of identity morphisms, $1_X h = h$ and likewise $1_X k = k$. Thus, $h = k$ concluding that $s$ is monic.
  $
    Section(s, r) = & (r s = 1_X)                             & #ref(<section>) #<secmonic> \
                 => & forall h, k. s h = s k                  &             text("premise") \
                  = & forall h, k. s h = s k => s h = s k     &       text("idempotent") => \
                  = & forall h, k. s h = s k => r s h = r s k &         #ref(<composition>) \
                  = & forall h, k. s h = s k => 1_X h = 1_X k &            #ref(<secmonic>) \
                  = & forall h, k. s h = s k => h = k         &              #ref(<unital>) \
                  = & Monic(s)                                &        #ref(<monomorphism>)
  $
] <sections-are-monic>

#proof(
  name: "Retractions are Epic",
)[
  $
    dim(forall cal(C).) Section(s dim(in cal(C)(X,Y)), r dim(in cal(C)(Y,X))) => Epic(r)
  $
  Let $r in cal(C)(Y,X)$ be a retraction to $s in cal(C)(X,Y)$ such that $r s = 1_X$. We show that $r$ is epic. Suppose that $i r = j r$ we show that $i = j$. Pre-composing with $s$ we get that $i r s = j r s$ and so $i 1_X = j 1_X$. By the unital property of identity morphisms, $i 1_X = i$ and likewise $j 1_X = j$. Thus, $i = j$ concluding $r$ is epic.
  $
    Section(s, r) = & (r s = 1_X)                            & #ref(<section>) #<retepic1> \
                 => & forall i, j. i r = j r                 &             text("premise") \
                  = & forall i,j. i r = j r => i r = j r     &       text("idempotent") => \
                  = & forall i,j. i r = j r => i r s = j r s &         #ref(<composition>) \
                  = & forall i,j. i r = j r => i 1_X = j 1_X &            #ref(<retepic1>) \
                  = & forall i,j. i r = j r => i = j         &              #ref(<unital>) \
                  = & Epic(r)                                &         #ref(<epimorphism>)
  $
] <retractions-are-epic>

#theorem(name: "Isomorphisms are Monic and Epic")[
  $
    dim(forall cal(C).) Iso(f dim(in cal(C)(X,Y))) => Monic(f) and Epic(f)
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
        edge(Y, "->", X, bend: 30deg)[$g$]
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

#proof[
  $
    dim(forall cal(C).) Iso(f dim(in cal(C)(X,Y))) => Monic(f) and Epic(f)
  $
  Let $f in cal(C)(X,Y)$ be an isomorphism with the inverse $g in cal(C)(Y,X)$. Thus, $f$ is a section to $g$ when $X$ is the retract since $g f = 1_X$. Moreover, $f$ is a retraction to $g$ when $Y$ is the retract since $f g = 1_Y$. Since sections are monic and retractions are epic, $f$ is both monic and epic.
  $
    Iso(f) = & (exists g. g f = 1_X and f g = 1_Y)       &          #ref(<isomorphism>) \
           = & exists g. Section(f, g) and Section(g, f) &              #ref(<section>) \
          => & Monic(f) and Epic(f)                      & #ref(<retractions-are-epic>)
  $
] <isomorphisms-are-monic-and-epic>

#theorem(name: "Isomorphism Inverse are unique")[
  $
    Iso(f) => & exists! g. g f = 1_X and f g = 1_Y
  $
]

#proof[Let $f$ be an isomorphism with two inverses $g, h$. It must be that $g = h$ since $f$ is monic / epic.
  $
    Iso(f) => & Monic(f)                                         & #ref(<isomorphisms-are-monic-and-epic>) \
            = & forall a, b. f a = f b => a = b                  &         #ref(<monomorphism>) #<isoinv1> \
           => & exists g. g f = 1_X and f g = 1_Y                &                     #ref(<isomorphism>) \
            = & exists g, h. g f = h f = 1_X and f g = f h = 1_Y &                         text("premise") \
           => & exists g, h. f g = f h => g = h                  &                         #ref(<isoinv1>) \
           => & exists! g. g f = 1_X and f g = 1_Y               &                   text("intro") exists!
  $
] <iso-inv-unique>

#let Functor(x) = $text("Functor")(#x)$;
#let Cat = $text("Cat")$;
#definition(name: "Functor")[
  Maps between categories that are _left total_ and _preserves_ composition and identity.
  $
    F : & cal(C) -> cal(D) \
    Functor(F) := & forall X in cal(C). F X in cal(D) #<functor-obj-left-total> \
    and & forall f in cal(C)(X,Y). F(f) in cal(D)(F X,F Y) & text("Left Total") #<functor-mor-left-total> \
    and & forall f in cal(C)(X,Y), g in cal(C)(Y,Z). F(g f) = F(g) F(f) & text("Composition") #<functor-preserves-composition> \
    and & forall X in cal(C). F(1_X) = 1_(F X) & text("Identity") #<functor-preserves-identity> \
  $
  We notationally omit the parentheses when applied to objects i.e. $F X = F(X)$ and use $attach(=>, t: F)$ to notate functor arrows in commutative diagrams.

  #figure(
    table(
      stroke: 0.5pt,
      diagram({
        let X = (0, 0)
        let Y = (0, 1)
        node(X, $X$)
        node(Y, $Y$)
        edge(X, "->", Y)[$f$]

        let FX = (1, 0)
        let FY = (1, 1)
        node(FX, $F X$)
        node(FY, $F Y$)
        edge(FX, "->", FY, label-side: left)[$F(f)$]

        edge((0.25, 0.5), "=>", (0.75, 0.5))[$F$]
      }),
    ),
  )
  Notice how $-^op : cal(C) -> cal(C)^op$ is a functor. Likewise if $C in cal(C)$ then $SliceU(C, -) : cal(C) -> SliceU(C, cal(C))$ and $SliceO(C, -) : cal(C) -> SliceO(C, cal(C))$ are functors too. We just have to show that it preserves composition and identity.
] <functor>

#definition(
  name: "Forgetful Functor",
)[A general term that is used for any functor that forgets structure. e.g. mapping from the category of groups to set where the group structure is forgotten; group homomorphisms are forgotten to arbitrary functions.] <forgetful-functor>

#let Contravariant(x) = $text("Contravariant")(#x)$;
#let Covariant(x) = $text("Covariant")(#x)$;
#definition(
  name: "Contravariant Functors",
)[Given a functor $F$ when we dualize the domain category we get a contravariant functor. The original non-dualized functor is called a _covariant_ functor.
  $
                    Covariant(F) & := Functor(F : cal(C) -> cal(D)) \
       Contravariant(F\, cal(C)) & := Functor(F : cal(C)^op -> cal(D)) \
    Contravariant(F\, cal(C)^op) & = Covariant(F)
  $
]

#let Presheaf(x) = $text("Presheaf")(#x)$;
#definition(name: "Presheaf")[A contravariant functor to the category of sets.
  $
    Presheaf(F\, cal(C)) & := Contravariant(F\, cal(C)) and cod(F) = Set
  $
] <presheaf>

#theorem(
  name: "Presheaf over hom set",
)[If $C in cal(C)$ and $f in cal(C)(X,Y)$ then $cal(C)(-, C)$ where $cal(C)(f^op, C)$ is the pre-composition function $f^*$ where $f^*(k) = h$ is a presheaf when $cal(C)$ is locally small.

  $
    LocallySmall(cal(C)) => Presheaf(cal(C)(-, C)\, cal(C))
  $

  #figure(
    table(
      stroke: 0.5pt,
      diagram({
        let C = (-1, 1)
        let X = (0, 0)
        let Y = (0, 1)
        node(X, $X$)
        node(Y, $Y$)
        node(C, $C$)
        edge(X, "->", Y)[$f$]
        edge(X, "->", C)[$h$]
        edge(Y, "->", C)[$k$]

        let FX = (1, 0)
        let FY = (1, 1)
        node(FX, $cal(C)(X,C)$)
        node(FY, $cal(C)(Y,C)$)
        edge(FY, "->", FX, label-side: right)[$f^*$]
      }),
    ),
  )
]

#theorem(name: "Functors preserve split monomorphisms and split epimorphisms")[
  $
    Section(s, r) => Monic(F(s)) and Epic(F(r))
  $
  Note that if $s,r$ are monic and epic respectively but $r s = 1_X$ does not hold, $F$ does not necessarily preserves $F(s)$ to be monic and $F(r)$ to be epic.
]

#proof[Since functors preserve composition and identity, $F(r) F(s) = 1_(F X)$ holds when $r s = 1_X$. This makes $F(r)$ a retraction to $F(s)$ over the retract $F X$. Since sections are split monomorphisms and retractions are split epimorphisms, so are $F(s)$ and $F(r)$ respectively.
  $
    Section(s, r) = & (r s = 1_X)                &                       #ref(<section>) \
                 => & F(r) F(s) = F(1_X)         & #ref(<functor-preserves-composition>) \
                  = & (F(r) F(s) = 1_(F X))      &    #ref(<functor-preserves-identity>) \
                  = & Section(F(s), F(r))        &                       #ref(<section>) \
                 => & Monic(F(s)) and Epic(F(r)) &            #ref(<sections-are-monic>)
  $
]

- product category
- bifunctor
- data of covariant and contravariant as bifunctor
- isomorphism of categories
- comma category
- naturality... onwards

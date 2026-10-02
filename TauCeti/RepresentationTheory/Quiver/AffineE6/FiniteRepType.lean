/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Quiver.AffineE6.Basic
public import TauCeti.RepresentationTheory.Quiver.OneLoop.FiniteRepType

/-!
# The extended Dynkin quiver `E₆~` has infinite representation type

The quiver `TauCeti.Quiver.AffineE6`, whose underlying graph is the extended Dynkin diagram `E₆~`,
has infinitely many finite-dimensional indecomposable representations over every field
(`TauCeti.not_isFiniteRepType_affineE6`).

The proof reduces to the loop quiver `•↺`, which is already known to have infinite representation
type (`TauCeti.not_isFiniteRepType_oneLoop`). A representation of `•↺` is a vector space `V` with
an endomorphism `f`, and `TauCeti.affineE6LoopRep` turns it into the representation of `E₆~` with
`V × V × V` at the centre, `V × V` at each inner vertex and `V` at each outer vertex. All its
arrows are injective, so it is a configuration of three flags `Lᵢ ⊆ Pᵢ` of `V × V × V`:

* `L₀ = V × 0 × 0` inside `P₀ = V × V × 0`;
* `L₁ = 0 × 0 × V` inside `P₁ = 0 × V × V`;
* `L₂ = {(x, x + f x, f x)}` inside `P₂ = {(a, a + c, c)}`.

This construction is fully faithful (`TauCeti.fullyFaithfulAffineE6LoopFunctor`). A morphism
between two such configurations preserves the first two flags, so its centre component acts on
the three coordinates separately; preserving `P₂` forces the three coordinate actions to agree,
and preserving `L₂` forces the common one to commute with the endomorphisms. The construction
therefore preserves indecomposability and reflects isomorphism, and it preserves
finite-dimensionality, so it embeds the finite-dimensional indecomposables of `•↺`, up to
isomorphism, in those of `E₆~`. No algebraic closedness and no infinitude of the field is needed:
the nilpotent Jordan blocks already give infinitely many indecomposables of `•↺` over every field.

## Main definitions

* `TauCeti.affineE6LoopRep`: the representation of `E₆~` attached to a representation of `•↺`.
* `TauCeti.affineE6LoopFunctor`: the same construction, as a functor.

## Main results

* `TauCeti.fullyFaithfulAffineE6LoopFunctor`: the functor is fully faithful.
* `TauCeti.IsFiniteRepType.oneLoop_of_affineE6`: finite representation type of `E₆~` would force
  it on `•↺`.
* `TauCeti.not_isFiniteRepType_affineE6`: `E₆~` has infinite representation type over every field.

## Implementation notes

`TauCeti.affineE6LoopRep` carries `@[expose]` for the reason recorded in
`TauCeti.RepresentationTheory.Quiver.OneLoop.FiniteRepType`: a functor built by
`CategoryTheory.Paths.lift` reveals its vertex spaces only through its definition, and the
components of the functor on morphisms are typed by them.

In the proof of fullness the components of a morphism are recorded as linear maps between
products of the vertex spaces, so that its six naturality squares, read on elements through
`CategoryTheory.NatTrans.naturality_apply`, are equations between pairs and triples which `rw`
and `simp` can take apart coordinatewise.

## References

* I. Assem, D. Simson, A. Skowroński, *Elements of the Representation Theory of Associative
  Algebras*, Volume I, Chapter VII.
* H. Derksen, J. Weyman, *An Introduction to Quiver Representations*, Chapter 4.
-/

public section

namespace TauCeti

open CategoryTheory

universe u w t

variable {k : Type u} [Field k]

/-- **A vector space with an endomorphism, as a representation of `E₆~`.** For a representation
`M` of `•↺`, with vertex space `V` on which the loop acts by `f`, this is the representation of
`TauCeti.Quiver.AffineE6` with `V × V × V` at the centre, `V × V` at each inner vertex and `V` at
each outer vertex. The outer arrows are `x ↦ (x, 0)`, `x ↦ (0, x)` and `x ↦ (x, f x)`, and the
inner arrows are `(a, b) ↦ (a, b, 0)`, `(b, c) ↦ (0, b, c)` and `(a, c) ↦ (a, a + c, c)`. -/
@[expose]
noncomputable def affineE6LoopRep (M : QuiverRep.{u, 0, w, t} k Quiver.OneLoop) :
    QuiverRep.{u, 0, 0, t} k Quiver.AffineE6 :=
  let V := M.obj (Quiver.OneLoop.vertex : Paths Quiver.OneLoop)
  let f := (M.map (Quiver.Hom.toPath Quiver.OneLoop.loop)).hom
  Paths.lift
    { obj := fun v ↦ match v with
        | .center => ModuleCat.of k (V × V × V)
        | .inner _ => ModuleCat.of k (V × V)
        | .outer _ => V
      map := fun {a b} e ↦ match a, b, e with
        | .outer i, .inner _, _ => ModuleCat.ofHom
            (![LinearMap.inl k V V, LinearMap.inr k V V, LinearMap.id.prod f] i)
        | .inner i, .center, _ => ModuleCat.ofHom
            (![LinearMap.id.prodMap (LinearMap.inl k V V), LinearMap.inr k V (V × V),
              (LinearMap.fst k V V).prod
                ((LinearMap.fst k V V + LinearMap.snd k V V).prod (LinearMap.snd k V V))] i)
        | .center, _, e => isEmptyElim e
        | .inner _, .inner _, e => isEmptyElim e
        | .inner _, .outer _, e => isEmptyElim e
        | .outer _, .center, e => isEmptyElim e
        | .outer _, .outer _, e => isEmptyElim e }

variable {M N : QuiverRep.{u, 0, w, t} k Quiver.OneLoop}

/-- The centre of `TauCeti.affineE6LoopRep M` carries the cube of the vertex space of `M`. -/
@[simp]
theorem affineE6LoopRep_obj_center :
    (affineE6LoopRep M).obj (Quiver.AffineE6.center : Paths Quiver.AffineE6) =
      ModuleCat.of k (M.obj (Quiver.OneLoop.vertex : Paths Quiver.OneLoop) ×
        M.obj (Quiver.OneLoop.vertex : Paths Quiver.OneLoop) ×
        M.obj (Quiver.OneLoop.vertex : Paths Quiver.OneLoop)) :=
  (rfl)

/-- Each inner vertex of `TauCeti.affineE6LoopRep M` carries the square of the vertex space of
`M`. -/
@[simp]
theorem affineE6LoopRep_obj_inner (i : Fin 3) :
    (affineE6LoopRep M).obj (Quiver.AffineE6.inner i : Paths Quiver.AffineE6) =
      ModuleCat.of k (M.obj (Quiver.OneLoop.vertex : Paths Quiver.OneLoop) ×
        M.obj (Quiver.OneLoop.vertex : Paths Quiver.OneLoop)) :=
  (rfl)

/-- Each outer vertex of `TauCeti.affineE6LoopRep M` carries the vertex space of `M`. -/
@[simp]
theorem affineE6LoopRep_obj_outer (i : Fin 3) :
    (affineE6LoopRep M).obj (Quiver.AffineE6.outer i : Paths Quiver.AffineE6) =
      M.obj (Quiver.OneLoop.vertex : Paths Quiver.OneLoop) :=
  (rfl)

/-- The first outer arrow is the inclusion of the first coordinate axis. -/
@[simp]
theorem affineE6LoopRep_map_outerArrow_zero :
    (affineE6LoopRep M).map (Quiver.AffineE6.outerArrow 0).toPath =
      ModuleCat.ofHom (LinearMap.inl k (M.obj (Quiver.OneLoop.vertex : Paths Quiver.OneLoop))
        (M.obj (Quiver.OneLoop.vertex : Paths Quiver.OneLoop))) :=
  Paths.lift_toPath _ _

/-- The second outer arrow is the inclusion of the second coordinate axis. -/
@[simp]
theorem affineE6LoopRep_map_outerArrow_one :
    (affineE6LoopRep M).map (Quiver.AffineE6.outerArrow 1).toPath =
      ModuleCat.ofHom (LinearMap.inr k (M.obj (Quiver.OneLoop.vertex : Paths Quiver.OneLoop))
        (M.obj (Quiver.OneLoop.vertex : Paths Quiver.OneLoop))) :=
  Paths.lift_toPath _ _

/-- The third outer arrow is the graph of the endomorphism by which the loop acts on `M`. -/
@[simp]
theorem affineE6LoopRep_map_outerArrow_two :
    (affineE6LoopRep M).map (Quiver.AffineE6.outerArrow 2).toPath =
      ModuleCat.ofHom (LinearMap.id.prod (M.map (Quiver.Hom.toPath Quiver.OneLoop.loop)).hom) :=
  Paths.lift_toPath _ _

/-- The first inner arrow is `(a, b) ↦ (a, b, 0)`. -/
@[simp]
theorem affineE6LoopRep_map_innerArrow_zero :
    (affineE6LoopRep M).map (Quiver.AffineE6.innerArrow 0).toPath =
      ModuleCat.ofHom (LinearMap.id.prodMap
        (LinearMap.inl k (M.obj (Quiver.OneLoop.vertex : Paths Quiver.OneLoop))
          (M.obj (Quiver.OneLoop.vertex : Paths Quiver.OneLoop)))) :=
  Paths.lift_toPath _ _

/-- The second inner arrow is `(b, c) ↦ (0, b, c)`. -/
@[simp]
theorem affineE6LoopRep_map_innerArrow_one :
    (affineE6LoopRep M).map (Quiver.AffineE6.innerArrow 1).toPath =
      ModuleCat.ofHom (LinearMap.inr k (M.obj (Quiver.OneLoop.vertex : Paths Quiver.OneLoop))
        (M.obj (Quiver.OneLoop.vertex : Paths Quiver.OneLoop) ×
          M.obj (Quiver.OneLoop.vertex : Paths Quiver.OneLoop))) :=
  Paths.lift_toPath _ _

/-- The third inner arrow is `(a, c) ↦ (a, a + c, c)`. -/
@[simp]
theorem affineE6LoopRep_map_innerArrow_two :
    (affineE6LoopRep M).map (Quiver.AffineE6.innerArrow 2).toPath =
      ModuleCat.ofHom
        ((LinearMap.fst k (M.obj (Quiver.OneLoop.vertex : Paths Quiver.OneLoop))
          (M.obj (Quiver.OneLoop.vertex : Paths Quiver.OneLoop))).prod
        ((LinearMap.fst k _ _ + LinearMap.snd k _ _).prod (LinearMap.snd k _ _))) :=
  Paths.lift_toPath _ _

/-- **A finite-dimensional representation of `•↺` gives a finite-dimensional representation of
`E₆~`**: the vertex spaces of `TauCeti.affineE6LoopRep M` are powers of the vertex space of `M`. -/
theorem isFinDim_affineE6LoopRep (hM : IsFinDim k Quiver.OneLoop M) :
    IsFinDim k Quiver.AffineE6 (affineE6LoopRep M) := by
  have : FiniteDimensional k (M.obj (Quiver.OneLoop.vertex : Paths Quiver.OneLoop)) :=
    isFinDim_iff.mp hM _
  refine isFinDim_iff.mpr fun v ↦ ?_
  cases v with
  | center => exact inferInstanceAs (FiniteDimensional k
      (M.obj (Quiver.OneLoop.vertex : Paths Quiver.OneLoop) ×
        M.obj (Quiver.OneLoop.vertex : Paths Quiver.OneLoop) ×
        M.obj (Quiver.OneLoop.vertex : Paths Quiver.OneLoop)))
  | inner i => exact inferInstanceAs (FiniteDimensional k
      (M.obj (Quiver.OneLoop.vertex : Paths Quiver.OneLoop) ×
        M.obj (Quiver.OneLoop.vertex : Paths Quiver.OneLoop)))
  | outer i => exact this

/-! ### The functor -/

/-- The components of the image of a morphism `φ` of representations of `•↺`: the component `ψ`
of `φ` at every outer vertex, `ψ × ψ` at the inner vertices and `ψ × ψ × ψ` at the centre. -/
private noncomputable def loopApp (φ : M ⟶ N) :
    ∀ v : Quiver.AffineE6, (affineE6LoopRep M).obj v ⟶ (affineE6LoopRep N).obj v
  | .center => ModuleCat.ofHom ((φ.app (Quiver.OneLoop.vertex : Paths Quiver.OneLoop)).hom.prodMap
      ((φ.app (Quiver.OneLoop.vertex : Paths Quiver.OneLoop)).hom.prodMap
        (φ.app (Quiver.OneLoop.vertex : Paths Quiver.OneLoop)).hom))
  | .inner _ => ModuleCat.ofHom ((φ.app (Quiver.OneLoop.vertex : Paths Quiver.OneLoop)).hom.prodMap
      (φ.app (Quiver.OneLoop.vertex : Paths Quiver.OneLoop)).hom)
  | .outer _ => φ.app (Quiver.OneLoop.vertex : Paths Quiver.OneLoop)

/-- The components `loopApp` commute with the arrows of `E₆~`. Both sides of each square are
computed coordinatewise by the definitions of `TauCeti.affineE6LoopRep` and `loopApp`, so each
square reduces to linearity of the component of `φ`, except along the third outer arrow, where it
is naturality of `φ` along the loop. -/
private theorem loopApp_naturality (φ : M ⟶ N) {a b : Quiver.AffineE6} (e : a ⟶ b) :
    (affineE6LoopRep M).map e.toPath ≫ loopApp φ b =
      loopApp φ a ≫ (affineE6LoopRep N).map e.toPath := by
  let ψ := (φ.app (Quiver.OneLoop.vertex : Paths Quiver.OneLoop)).hom
  match a, b, e with
  | .outer i, .inner j, e =>
    obtain rfl : i = j := e.down
    obtain rfl : e = Quiver.AffineE6.outerArrow i := Subsingleton.elim _ _
    refine ModuleCat.hom_ext (LinearMap.ext fun x ↦ ?_)
    match i with
    | 0 => exact Prod.ext rfl (map_zero ψ)
    | 1 => exact Prod.ext (map_zero ψ) rfl
    | 2 => exact Prod.ext rfl (NatTrans.naturality_apply φ Quiver.OneLoop.loop.toPath x)
  | .inner i, .center, e =>
    obtain rfl : e = Quiver.AffineE6.innerArrow i := Subsingleton.elim _ _
    refine ModuleCat.hom_ext (LinearMap.ext fun x ↦ ?_)
    match i with
    | 0 => exact Prod.ext rfl (Prod.ext rfl (map_zero ψ))
    | 1 => exact Prod.ext (map_zero ψ) rfl
    | 2 => exact Prod.ext rfl (Prod.ext (map_add ψ _ _) rfl)
  | .center, _, e => exact isEmptyElim e
  | .inner _, .inner _, e => exact isEmptyElim e
  | .inner _, .outer _, e => exact isEmptyElim e
  | .outer _, .center, e => exact isEmptyElim e
  | .outer _, .outer _, e => exact isEmptyElim e

variable (k) in
/-- **A vector space with an endomorphism, as a representation of `E₆~`, as a functor**: a
morphism with component `ψ` acts by `ψ` at every outer vertex, by `ψ × ψ` at the inner vertices
and by `ψ × ψ × ψ` at the centre. -/
noncomputable def affineE6LoopFunctor :
    QuiverRep.{u, 0, w, t} k Quiver.OneLoop ⥤ QuiverRep.{u, 0, 0, t} k Quiver.AffineE6 where
  obj M := affineE6LoopRep M
  map φ := Paths.liftNatTrans (loopApp φ) (loopApp_naturality φ)
  map_id M := by
    refine NatTrans.ext (funext fun v ↦ ?_)
    cases v <;> rfl
  map_comp φ ψ := by
    refine NatTrans.ext (funext fun v ↦ ?_)
    cases v <;> rfl

/-- The functor `TauCeti.affineE6LoopFunctor` sends a representation to its `E₆~` representation. -/
@[simp]
theorem affineE6LoopFunctor_obj : (affineE6LoopFunctor k).obj M = affineE6LoopRep M :=
  (rfl)

/-! ### Full faithfulness -/

section Full

variable (g : affineE6LoopRep M ⟶ affineE6LoopRep N)

/-- The component of `g` at the centre, as a linear map between cubes. -/
private noncomputable def centerHom :
    M.obj (Quiver.OneLoop.vertex : Paths Quiver.OneLoop) ×
        M.obj (Quiver.OneLoop.vertex : Paths Quiver.OneLoop) ×
        M.obj (Quiver.OneLoop.vertex : Paths Quiver.OneLoop) →ₗ[k]
      N.obj (Quiver.OneLoop.vertex : Paths Quiver.OneLoop) ×
        N.obj (Quiver.OneLoop.vertex : Paths Quiver.OneLoop) ×
        N.obj (Quiver.OneLoop.vertex : Paths Quiver.OneLoop) :=
  (g.app (Quiver.AffineE6.center : Paths Quiver.AffineE6)).hom

/-- The component of `g` at an inner vertex, as a linear map between squares. -/
private noncomputable def innerHom (i : Fin 3) :
    M.obj (Quiver.OneLoop.vertex : Paths Quiver.OneLoop) ×
        M.obj (Quiver.OneLoop.vertex : Paths Quiver.OneLoop) →ₗ[k]
      N.obj (Quiver.OneLoop.vertex : Paths Quiver.OneLoop) ×
        N.obj (Quiver.OneLoop.vertex : Paths Quiver.OneLoop) :=
  (g.app (Quiver.AffineE6.inner i : Paths Quiver.AffineE6)).hom

/-- The component of `g` at an outer vertex, as a linear map between the vertex spaces. -/
private noncomputable def outerHom (i : Fin 3) :
    M.obj (Quiver.OneLoop.vertex : Paths Quiver.OneLoop) →ₗ[k]
      N.obj (Quiver.OneLoop.vertex : Paths Quiver.OneLoop) :=
  (g.app (Quiver.AffineE6.outer i : Paths Quiver.AffineE6)).hom

/-! The six naturality squares of `g`, read on elements. Each is
`CategoryTheory.NatTrans.naturality_apply` along one arrow, whose action is the one recorded in
the docstring of `TauCeti.affineE6LoopRep`. -/

private theorem innerHom_zero_inl (x : M.obj (Quiver.OneLoop.vertex : Paths Quiver.OneLoop)) :
    innerHom g 0 (x, 0) = (outerHom g 0 x, 0) :=
  NatTrans.naturality_apply g (Quiver.AffineE6.outerArrow 0).toPath x

private theorem innerHom_one_inr (x : M.obj (Quiver.OneLoop.vertex : Paths Quiver.OneLoop)) :
    innerHom g 1 (0, x) = (0, outerHom g 1 x) :=
  NatTrans.naturality_apply g (Quiver.AffineE6.outerArrow 1).toPath x

private theorem innerHom_two_graph (x : M.obj (Quiver.OneLoop.vertex : Paths Quiver.OneLoop)) :
    innerHom g 2 (x, (M.map (Quiver.Hom.toPath Quiver.OneLoop.loop)).hom x) =
      (outerHom g 2 x, (N.map (Quiver.Hom.toPath Quiver.OneLoop.loop)).hom (outerHom g 2 x)) :=
  NatTrans.naturality_apply g (Quiver.AffineE6.outerArrow 2).toPath x

private theorem centerHom_innerArrow_zero
    (a b : M.obj (Quiver.OneLoop.vertex : Paths Quiver.OneLoop)) :
    centerHom g (a, b, 0) = ((innerHom g 0 (a, b)).1, (innerHom g 0 (a, b)).2, 0) :=
  NatTrans.naturality_apply g (Quiver.AffineE6.innerArrow 0).toPath (a, b)

private theorem centerHom_innerArrow_one
    (b c : M.obj (Quiver.OneLoop.vertex : Paths Quiver.OneLoop)) :
    centerHom g (0, b, c) = (0, innerHom g 1 (b, c)) :=
  NatTrans.naturality_apply g (Quiver.AffineE6.innerArrow 1).toPath (b, c)

private theorem centerHom_innerArrow_two
    (a c : M.obj (Quiver.OneLoop.vertex : Paths Quiver.OneLoop)) :
    centerHom g (a, a + c, c) = ((innerHom g 2 (a, c)).1,
      (innerHom g 2 (a, c)).1 + (innerHom g 2 (a, c)).2, (innerHom g 2 (a, c)).2) :=
  NatTrans.naturality_apply g (Quiver.AffineE6.innerArrow 2).toPath (a, c)

/-- The centre component of `g` sends the first axis by the first outer component. -/
private theorem centerHom_fst_axis
    (a : M.obj (Quiver.OneLoop.vertex : Paths Quiver.OneLoop)) :
    centerHom g (a, 0, 0) = (outerHom g 0 a, 0, 0) := by
  rw [centerHom_innerArrow_zero, innerHom_zero_inl]

/-- The centre component of `g` sends the third axis by the second outer component. -/
private theorem centerHom_third_axis
    (c : M.obj (Quiver.OneLoop.vertex : Paths Quiver.OneLoop)) :
    centerHom g (0, 0, c) = (0, 0, outerHom g 1 c) := by
  rw [centerHom_innerArrow_one, innerHom_one_inr]

/-- The centre component of `g` is the sum of its values on the three axes. -/
private theorem centerHom_eq_add (a b c : M.obj (Quiver.OneLoop.vertex : Paths Quiver.OneLoop)) :
    centerHom g (a, b, c) =
      centerHom g (a, 0, 0) + centerHom g (0, b, 0) + centerHom g (0, 0, c) := by
  rw [← map_add, ← map_add]
  simp

/-- The centre component of `g` sends the second axis into the second axis: the inner arrows of
the first two arms see the second axis, and their images miss the third, resp. the first,
coordinate. -/
private theorem centerHom_snd_axis_fst
    (b : M.obj (Quiver.OneLoop.vertex : Paths Quiver.OneLoop)) :
    (centerHom g (0, b, 0)).1 = 0 := by
  rw [centerHom_innerArrow_one]

private theorem centerHom_snd_axis_third
    (b : M.obj (Quiver.OneLoop.vertex : Paths Quiver.OneLoop)) :
    (centerHom g (0, b, 0)).2.2 = 0 := by
  rw [centerHom_innerArrow_zero]

/-- On the second axis the centre component of `g` acts by the first outer component: the third
arm sees the diagonal `{(a, a, 0)}` of the first two axes. -/
private theorem centerHom_snd_axis_snd
    (b : M.obj (Quiver.OneLoop.vertex : Paths Quiver.OneLoop)) :
    (centerHom g (0, b, 0)).2.1 = outerHom g 0 b := by
  have h := centerHom_innerArrow_two g b 0
  rw [add_zero, centerHom_eq_add, centerHom_fst_axis, centerHom_third_axis, map_zero] at h
  have h1 := congrArg Prod.fst h
  have h2 := congrArg (fun p ↦ p.2.1) h
  have h3 := congrArg (fun p ↦ p.2.2) h
  simp only [Prod.fst_add, Prod.snd_add, centerHom_snd_axis_fst, centerHom_snd_axis_third,
    add_zero, zero_add] at h1 h2 h3
  rw [h2, ← h1, ← h3, add_zero]

/-- The first two outer components of `g` agree: the third arm sees the diagonal `{(0, c, c)}` of
the last two axes. -/
private theorem outerHom_one (c : M.obj (Quiver.OneLoop.vertex : Paths Quiver.OneLoop)) :
    outerHom g 1 c = outerHom g 0 c := by
  have h := centerHom_innerArrow_two g 0 c
  rw [zero_add, centerHom_eq_add, centerHom_fst_axis, centerHom_third_axis, map_zero] at h
  have h1 := congrArg Prod.fst h
  have h2 := congrArg (fun p ↦ p.2.1) h
  have h3 := congrArg (fun p ↦ p.2.2) h
  simp only [Prod.fst_add, Prod.snd_add, centerHom_snd_axis_fst, centerHom_snd_axis_third,
    centerHom_snd_axis_snd, add_zero, zero_add] at h1 h2 h3
  rw [h3, ← zero_add (innerHom g 2 (0, c)).2, h1, ← h2]

/-- **The centre component of `g` is `ψ × ψ × ψ` for its first outer component `ψ`.** -/
private theorem centerHom_apply
    (a b c : M.obj (Quiver.OneLoop.vertex : Paths Quiver.OneLoop)) :
    centerHom g (a, b, c) = (outerHom g 0 a, outerHom g 0 b, outerHom g 0 c) := by
  rw [centerHom_eq_add, centerHom_fst_axis, centerHom_third_axis, outerHom_one]
  refine Prod.ext ?_ (Prod.ext ?_ ?_) <;>
    simp [centerHom_snd_axis_fst, centerHom_snd_axis_snd, centerHom_snd_axis_third]

/-- **Every inner component of `g` is `ψ × ψ` for its first outer component `ψ`.** -/
private theorem innerHom_apply (i : Fin 3)
    (a b : M.obj (Quiver.OneLoop.vertex : Paths Quiver.OneLoop)) :
    innerHom g i (a, b) = (outerHom g 0 a, outerHom g 0 b) := by
  match i with
  | 0 =>
    have h := centerHom_innerArrow_zero g a b
    rw [centerHom_apply] at h
    exact Prod.ext (congrArg Prod.fst h).symm (congrArg (fun p ↦ p.2.1) h).symm
  | 1 =>
    have h := centerHom_innerArrow_one g a b
    rw [centerHom_apply] at h
    exact (congrArg Prod.snd h).symm
  | 2 =>
    have h := centerHom_innerArrow_two g a b
    rw [centerHom_apply] at h
    exact Prod.ext (congrArg Prod.fst h).symm (congrArg (fun p ↦ p.2.2) h).symm

/-- The third outer component of `g` agrees with the first one, and the first one intertwines the
two loop actions: the third outer arrow is the graph of the loop action. -/
private theorem outerHom_two_and_intertwine
    (x : M.obj (Quiver.OneLoop.vertex : Paths Quiver.OneLoop)) :
    outerHom g 2 x = outerHom g 0 x ∧
      outerHom g 0 ((M.map (Quiver.Hom.toPath Quiver.OneLoop.loop)).hom x) =
        (N.map (Quiver.Hom.toPath Quiver.OneLoop.loop)).hom (outerHom g 0 x) := by
  have h := innerHom_two_graph g x
  rw [innerHom_apply] at h
  have h1 := congrArg Prod.fst h
  have h2 := congrArg Prod.snd h
  dsimp only at h1 h2
  rw [← h1] at h2
  exact ⟨h1.symm, h2⟩

/-- **Every outer component of `g` is the first one.** -/
private theorem outerHom_eq (i : Fin 3) : outerHom g i = outerHom g 0 := by
  ext x
  match i with
  | 0 => rfl
  | 1 => exact outerHom_one g x
  | 2 => exact (outerHom_two_and_intertwine g x).1

/-- The morphism of representations of `•↺` underlying `g`: its component at the first outer
vertex, which commutes with the loop by `outerHom_two_and_intertwine`. -/
private noncomputable def unloop : M ⟶ N :=
  Paths.liftNatTrans (fun _ ↦ g.app (Quiver.AffineE6.outer 0 : Paths Quiver.AffineE6))
    fun {a b} e ↦ by
      cases a
      cases b
      rw [Subsingleton.elim e Quiver.OneLoop.loop]
      exact ModuleCat.hom_ext (LinearMap.ext fun x ↦ (outerHom_two_and_intertwine g x).2)

end Full

variable (k) in
/-- **The functor `TauCeti.affineE6LoopFunctor` is fully faithful.** A morphism between images is
determined by its component `ψ` at the first outer vertex: by naturality along the six arrows,
every other component is `ψ`, `ψ × ψ` or `ψ × ψ × ψ`, and `ψ` commutes with the loop. -/
noncomputable def fullyFaithfulAffineE6LoopFunctor :
    (affineE6LoopFunctor.{u, w, t} k).FullyFaithful where
  preimage {M N} g := unloop g
  map_preimage {M N} g := by
    refine NatTrans.ext (funext fun v ↦ ?_)
    refine ModuleCat.hom_ext (LinearMap.ext fun x ↦ ?_)
    cases v with
    | center =>
      obtain ⟨a, b, c⟩ := x
      exact (centerHom_apply g a b c).symm
    | inner i =>
      obtain ⟨a, b⟩ := x
      exact (innerHom_apply g i a b).symm
    | outer i => exact (LinearMap.congr_fun (outerHom_eq g i) x).symm
  preimage_map {M N} φ := by
    refine NatTrans.ext (funext fun v ↦ ?_)
    cases v
    rfl

/-- **The functor `TauCeti.affineE6LoopFunctor` reflects and preserves isomorphism.** -/
@[simp]
theorem nonempty_affineE6LoopRep_iso_iff :
    Nonempty (affineE6LoopRep M ≅ affineE6LoopRep N) ↔ Nonempty (M ≅ N) :=
  ⟨fun ⟨e⟩ ↦ ⟨(fullyFaithfulAffineE6LoopFunctor k).preimageIso e⟩,
    fun ⟨e⟩ ↦ ⟨(affineE6LoopFunctor k).mapIso e⟩⟩

/-- **The image of an indecomposable representation of `•↺` is indecomposable**: the functor is
fully faithful, so it matches the idempotent endomorphisms of `M` with those of its image. -/
theorem indecomposable_affineE6LoopRep (hM : Indecomposable M) :
    Indecomposable (affineE6LoopRep M) :=
  (affineE6LoopFunctor k).indecomposable_obj_of_map_bijective hM
    ((fullyFaithfulAffineE6LoopFunctor k).map_bijective M M)

/-! ### Infinite representation type -/

/-- **Finite representation type of `E₆~` would force it on the loop quiver**: the functor
`TauCeti.affineE6LoopFunctor` carries the finite-dimensional indecomposables of `•↺` to
finite-dimensional indecomposables of `TauCeti.Quiver.AffineE6` and reflects isomorphism among
them. -/
theorem IsFiniteRepType.oneLoop_of_affineE6
    (h : IsFiniteRepType.{u, 0, 0, t} k Quiver.AffineE6) :
    IsFiniteRepType.{u, 0, w, t} k Quiver.OneLoop :=
  isFiniteRepType_of_map (fun _ ↦ False) affineE6LoopRep
    (fun _ hM hM' _ ↦ ⟨isFinDim_affineE6LoopRep hM, indecomposable_affineE6LoopRep hM'⟩)
    (fun _ _ _ _ _ _ ↦ nonempty_affineE6LoopRep_iso_iff.mp) (fun _ _ _ _ h _ ↦ h.elim) h

/-- **The extended Dynkin quiver `E₆~` has infinite representation type over every field.** The
images of the nilpotent Jordan blocks (`TauCeti.oneLoopNilpotentRep`) are infinitely many pairwise
non-isomorphic finite-dimensional indecomposables. -/
theorem not_isFiniteRepType_affineE6 (k : Type u) [Field k] :
    ¬ IsFiniteRepType.{u, 0, 0, u} k Quiver.AffineE6 :=
  fun h ↦ not_isFiniteRepType_oneLoop.{u, 0} k h.oneLoop_of_affineE6

end TauCeti

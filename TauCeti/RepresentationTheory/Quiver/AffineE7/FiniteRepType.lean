/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Quiver.AffineE7.Basic
public import TauCeti.RepresentationTheory.Quiver.OneLoop.FiniteRepType

/-!
# The extended Dynkin quiver `E₇~` has infinite representation type

The quiver `TauCeti.Quiver.AffineE7`, whose underlying graph is the extended Dynkin diagram `E₇~`,
has infinitely many finite-dimensional indecomposable representations over every field
(`TauCeti.not_isFiniteRepType_affineE7`).

The proof reduces to the loop quiver `•↺`, which is already known to have infinite representation
type (`TauCeti.not_isFiniteRepType_oneLoop`). A representation of `•↺` is a vector space `V` with
an endomorphism `f`, and `TauCeti.affineE7LoopRep` turns it into the representation of `E₇~` with
`V⁴` at the centre, `V³`, `V²` and `V` along each long arm, and `V²` at the short vertex. All its
arrows are injective, so it is a configuration in `V⁴` of two flags and one subspace:

* the flag `V × 0 × 0 × 0 ⊆ V × V × 0 × 0 ⊆ V × V × V × 0` along the first long arm;
* the flag `0 × 0 × 0 × V ⊆ 0 × 0 × V × V ⊆ 0 × V × V × V` along the second long arm;
* the subspace `{(a, b, a + b, a + f b)}` at the short vertex.

This construction is fully faithful (`TauCeti.fullyFaithfulAffineE7LoopFunctor`). A morphism
between two such configurations preserves both flags, so its centre component preserves the four
coordinate axes and acts on them separately; preserving the subspace at the short vertex forces
the four coordinate actions to agree, and the common one to commute with the endomorphisms. The
construction therefore preserves indecomposability and reflects isomorphism, and it preserves
finite-dimensionality, so it embeds the finite-dimensional indecomposables of `•↺`, up to
isomorphism, in those of `E₇~`. No algebraic closedness and no infinitude of the field is needed:
the nilpotent Jordan blocks already give infinitely many indecomposables of `•↺` over every field.

## Main definitions

* `TauCeti.affineE7LoopRep`: the representation of `E₇~` attached to a representation of `•↺`.
* `TauCeti.affineE7LoopFunctor`: the same construction, as a functor.

## Main results

* `TauCeti.fullyFaithfulAffineE7LoopFunctor`: the functor is fully faithful.
* `TauCeti.IsFiniteRepType.oneLoop_of_affineE7`: finite representation type of `E₇~` would force
  it on `•↺`.
* `TauCeti.not_isFiniteRepType_affineE7`: `E₇~` has infinite representation type over every field.

## References

* I. Assem, D. Simson, A. Skowroński, *Elements of the Representation Theory of Associative
  Algebras*, Volume I, Chapter VII.
* H. Derksen, J. Weyman, *An Introduction to Quiver Representations*, Chapter 4.
-/

-- The file layout and the shape of the API are adapted from the parallel treatment of `E₆~`
-- (TauCeti PR #10945); the two files share no code.

public section

namespace TauCeti

open CategoryTheory
open Quiver.OneLoop (vertex loop)

universe u w t

variable {k : Type u} [Field k]

/-- **A vector space with an endomorphism, as a representation of `E₇~`.** For a representation
`M` of `•↺`, with vertex space `V` on which the loop acts by `f`, this is the representation of
`TauCeti.Quiver.AffineE7` with `V⁴` at the centre, `V³`, `V²` and `V` at the inner, middle and
outer vertex of each long arm, and `V²` at the short vertex. Along the first long arm the arrows
are `x ↦ (x, 0)`, `(a, b) ↦ (a, b, 0)` and `(a, b, c) ↦ (a, b, c, 0)`; along the second they are
`x ↦ (0, x)`, `(c, d) ↦ (0, c, d)` and `(b, c, d) ↦ (0, b, c, d)`; the short arrow is
`(a, b) ↦ (a, b, a + b, a + f b)`. -/
-- `@[expose]`: a functor built by `CategoryTheory.Paths.lift` reveals its vertex spaces only
-- through its definition, and the components of the functor on morphisms are typed by them.
@[expose]
noncomputable def affineE7LoopRep (M : QuiverRep.{u, 0, w, t} k Quiver.OneLoop) :
    QuiverRep.{u, 0, 0, t} k Quiver.AffineE7 :=
  let V := M.obj vertex
  let f := (M.map loop.toPath).hom
  Paths.lift
    { obj := fun v ↦ match v with
        | .center => ModuleCat.of k (V × V × V × V)
        | .short => ModuleCat.of k (V × V)
        | .inner _ => ModuleCat.of k (V × V × V)
        | .middle _ => ModuleCat.of k (V × V)
        | .outer _ => V
      map := fun e ↦ match e with
        | .outerMiddle i => ModuleCat.ofHom (![LinearMap.inl k V V, LinearMap.inr k V V] i)
        | .middleInner i => ModuleCat.ofHom
            (![LinearMap.id.prodMap (LinearMap.inl k V V), LinearMap.inr k V (V × V)] i)
        | .innerCenter i => ModuleCat.ofHom
            (![LinearMap.id.prodMap (LinearMap.id.prodMap (LinearMap.inl k V V)),
              LinearMap.inr k V (V × V × V)] i)
        | .shortCenter => ModuleCat.ofHom
            ((LinearMap.fst k V V).prod ((LinearMap.snd k V V).prod
              ((LinearMap.fst k V V + LinearMap.snd k V V).prod
                (LinearMap.fst k V V + f ∘ₗ LinearMap.snd k V V)))) }

variable {M N : QuiverRep.{u, 0, w, t} k Quiver.OneLoop}

/-- The centre of `TauCeti.affineE7LoopRep M` carries the fourth power of the vertex space of
`M`. -/
@[simp]
theorem affineE7LoopRep_obj_center :
    (affineE7LoopRep M).obj Quiver.AffineE7.center =
      ModuleCat.of k (M.obj vertex × M.obj vertex × M.obj vertex × M.obj vertex) :=
  (rfl)

/-- The short vertex of `TauCeti.affineE7LoopRep M` carries the square of the vertex space of
`M`. -/
@[simp]
theorem affineE7LoopRep_obj_short :
    (affineE7LoopRep M).obj Quiver.AffineE7.short = ModuleCat.of k (M.obj vertex × M.obj vertex) :=
  (rfl)

/-- Each inner vertex of `TauCeti.affineE7LoopRep M` carries the cube of the vertex space of
`M`. -/
@[simp]
theorem affineE7LoopRep_obj_inner (i : Fin 2) :
    (affineE7LoopRep M).obj (Quiver.AffineE7.inner i) =
      ModuleCat.of k (M.obj vertex × M.obj vertex × M.obj vertex) :=
  (rfl)

/-- Each middle vertex of `TauCeti.affineE7LoopRep M` carries the square of the vertex space of
`M`. -/
@[simp]
theorem affineE7LoopRep_obj_middle (i : Fin 2) :
    (affineE7LoopRep M).obj (Quiver.AffineE7.middle i) =
      ModuleCat.of k (M.obj vertex × M.obj vertex) :=
  (rfl)

/-- Each outer vertex of `TauCeti.affineE7LoopRep M` carries the vertex space of `M`. -/
@[simp]
theorem affineE7LoopRep_obj_outer (i : Fin 2) :
    (affineE7LoopRep M).obj (Quiver.AffineE7.outer i) = M.obj vertex :=
  (rfl)

/-- The outer arrow of the long arm `i` is `x ↦ (x, 0)` for `i = 0` and `x ↦ (0, x)` for
`i = 1`. -/
private theorem affineE7LoopRep_map_outerMiddle (i : Fin 2) :
    (affineE7LoopRep M).map (Quiver.Hom.toPath (.outerMiddle i)) =
      ModuleCat.ofHom (![LinearMap.inl k (M.obj vertex) (M.obj vertex),
        LinearMap.inr k (M.obj vertex) (M.obj vertex)] i) :=
  Paths.lift_toPath _ _

/-- The middle arrow of the long arm `i` is `(a, b) ↦ (a, b, 0)` for `i = 0` and
`(c, d) ↦ (0, c, d)` for `i = 1`. -/
private theorem affineE7LoopRep_map_middleInner (i : Fin 2) :
    (affineE7LoopRep M).map (Quiver.Hom.toPath (.middleInner i)) =
      ModuleCat.ofHom (![LinearMap.id.prodMap (LinearMap.inl k (M.obj vertex) (M.obj vertex)),
        LinearMap.inr k (M.obj vertex) (M.obj vertex × M.obj vertex)] i) :=
  Paths.lift_toPath _ _

/-- The inner arrow of the long arm `i` is `(a, b, c) ↦ (a, b, c, 0)` for `i = 0` and
`(b, c, d) ↦ (0, b, c, d)` for `i = 1`. -/
private theorem affineE7LoopRep_map_innerCenter (i : Fin 2) :
    (affineE7LoopRep M).map (Quiver.Hom.toPath (.innerCenter i)) =
      ModuleCat.ofHom (![LinearMap.id.prodMap
          (LinearMap.id.prodMap (LinearMap.inl k (M.obj vertex) (M.obj vertex))),
        LinearMap.inr k (M.obj vertex) (M.obj vertex × M.obj vertex × M.obj vertex)] i) :=
  Paths.lift_toPath _ _

/-- The short arrow is `(a, b) ↦ (a, b, a + b, a + f b)`, for the endomorphism `f` by which the
loop acts on `M`. -/
private theorem affineE7LoopRep_map_shortCenter :
    (affineE7LoopRep M).map (Quiver.Hom.toPath .shortCenter) =
      ModuleCat.ofHom ((LinearMap.fst k (M.obj vertex) (M.obj vertex)).prod
        ((LinearMap.snd k (M.obj vertex) (M.obj vertex)).prod
          ((LinearMap.fst k _ _ + LinearMap.snd k _ _).prod
            (LinearMap.fst k _ _ + (M.map loop.toPath).hom ∘ₗ LinearMap.snd k _ _)))) :=
  Paths.lift_toPath _ _

-- Specify the source and target of `Hom.hom` in simp-normal form: otherwise the object
-- lemmas above simplify its implicit arguments before the arrow application lemmas can fire.
/-- The outer arrow of the first long arm sends `x` to `(x, 0)`. -/
@[simp]
theorem affineE7LoopRep_map_outerMiddle_zero_apply (x : M.obj vertex) :
    ModuleCat.Hom.hom (A := M.obj vertex) (B := ModuleCat.of k (M.obj vertex × M.obj vertex))
      ((affineE7LoopRep M).map (Quiver.Hom.toPath (.outerMiddle 0))) x = (x, 0) := by
  rw [affineE7LoopRep_map_outerMiddle]
  rfl

/-- The outer arrow of the second long arm sends `x` to `(0, x)`. -/
@[simp]
theorem affineE7LoopRep_map_outerMiddle_one_apply (x : M.obj vertex) :
    ModuleCat.Hom.hom (A := M.obj vertex) (B := ModuleCat.of k (M.obj vertex × M.obj vertex))
      ((affineE7LoopRep M).map (Quiver.Hom.toPath (.outerMiddle 1))) x = (0, x) := by
  rw [affineE7LoopRep_map_outerMiddle]
  rfl

/-- The middle arrow of the first long arm sends `(a, b)` to `(a, b, 0)`. -/
@[simp]
theorem affineE7LoopRep_map_middleInner_zero_apply (x : M.obj vertex × M.obj vertex) :
    ModuleCat.Hom.hom (A := ModuleCat.of k (M.obj vertex × M.obj vertex))
      (B := ModuleCat.of k (M.obj vertex × M.obj vertex × M.obj vertex))
      ((affineE7LoopRep M).map (Quiver.Hom.toPath (.middleInner 0))) x = (x.1, x.2, 0) := by
  rw [affineE7LoopRep_map_middleInner]
  rfl

/-- The middle arrow of the second long arm sends `(c, d)` to `(0, c, d)`. -/
@[simp]
theorem affineE7LoopRep_map_middleInner_one_apply (x : M.obj vertex × M.obj vertex) :
    ModuleCat.Hom.hom (A := ModuleCat.of k (M.obj vertex × M.obj vertex))
      (B := ModuleCat.of k (M.obj vertex × M.obj vertex × M.obj vertex))
      ((affineE7LoopRep M).map (Quiver.Hom.toPath (.middleInner 1))) x = (0, x) := by
  rw [affineE7LoopRep_map_middleInner]
  rfl

/-- The inner arrow of the first long arm sends `(a, b, c)` to `(a, b, c, 0)`. -/
@[simp]
theorem affineE7LoopRep_map_innerCenter_zero_apply
    (x : M.obj vertex × M.obj vertex × M.obj vertex) :
    ModuleCat.Hom.hom (A := ModuleCat.of k (M.obj vertex × M.obj vertex × M.obj vertex))
      (B := ModuleCat.of k (M.obj vertex × M.obj vertex × M.obj vertex × M.obj vertex))
      ((affineE7LoopRep M).map (Quiver.Hom.toPath (.innerCenter 0))) x =
      (x.1, x.2.1, x.2.2, 0) := by
  rw [affineE7LoopRep_map_innerCenter]
  rfl

/-- The inner arrow of the second long arm sends `(b, c, d)` to `(0, b, c, d)`. -/
@[simp]
theorem affineE7LoopRep_map_innerCenter_one_apply
    (x : M.obj vertex × M.obj vertex × M.obj vertex) :
    ModuleCat.Hom.hom (A := ModuleCat.of k (M.obj vertex × M.obj vertex × M.obj vertex))
      (B := ModuleCat.of k (M.obj vertex × M.obj vertex × M.obj vertex × M.obj vertex))
      ((affineE7LoopRep M).map (Quiver.Hom.toPath (.innerCenter 1))) x = (0, x) := by
  rw [affineE7LoopRep_map_innerCenter]
  rfl

/-- The short arrow sends `(a, b)` to `(a, b, a + b, a + f b)`, for the endomorphism `f` by which
the loop acts on `M`. -/
@[simp]
theorem affineE7LoopRep_map_shortCenter_apply (x : M.obj vertex × M.obj vertex) :
    ModuleCat.Hom.hom (A := ModuleCat.of k (M.obj vertex × M.obj vertex))
      (B := ModuleCat.of k (M.obj vertex × M.obj vertex × M.obj vertex × M.obj vertex))
      ((affineE7LoopRep M).map (Quiver.Hom.toPath .shortCenter)) x =
      (x.1, x.2, x.1 + x.2, x.1 + (M.map loop.toPath).hom x.2) := by
  rw [affineE7LoopRep_map_shortCenter]
  rfl

/-- **A finite-dimensional representation of `•↺` gives a finite-dimensional representation of
`E₇~`**: the vertex spaces of `TauCeti.affineE7LoopRep M` are powers of the vertex space of `M`. -/
theorem isFinDim_affineE7LoopRep (hM : IsFinDim k Quiver.OneLoop M) :
    IsFinDim k Quiver.AffineE7 (affineE7LoopRep M) := by
  have : FiniteDimensional k (M.obj vertex) := isFinDim_iff.mp hM _
  refine isFinDim_iff.mpr fun v ↦ ?_
  cases v with
  | center => exact inferInstanceAs
      (FiniteDimensional k (M.obj vertex × M.obj vertex × M.obj vertex × M.obj vertex))
  | short => exact inferInstanceAs (FiniteDimensional k (M.obj vertex × M.obj vertex))
  | inner i => exact inferInstanceAs
      (FiniteDimensional k (M.obj vertex × M.obj vertex × M.obj vertex))
  | middle i => exact inferInstanceAs (FiniteDimensional k (M.obj vertex × M.obj vertex))
  | outer i => exact this

/-! ### The functor -/

/-- The components of the image of a morphism `φ` of representations of `•↺`: the powers of the
component `ψ` of `φ`, namely `ψ` at the outer vertices, `ψ × ψ` at the middle and short vertices,
`ψ × ψ × ψ` at the inner vertices and `ψ × ψ × ψ × ψ` at the centre. -/
private noncomputable def loopApp (φ : M ⟶ N) :
    ∀ v : Quiver.AffineE7, (affineE7LoopRep M).obj v ⟶ (affineE7LoopRep N).obj v
  | .center => ModuleCat.ofHom ((φ.app vertex).hom.prodMap
      ((φ.app vertex).hom.prodMap ((φ.app vertex).hom.prodMap (φ.app vertex).hom)))
  | .short => ModuleCat.ofHom ((φ.app vertex).hom.prodMap (φ.app vertex).hom)
  | .inner _ => ModuleCat.ofHom ((φ.app vertex).hom.prodMap
      ((φ.app vertex).hom.prodMap (φ.app vertex).hom))
  | .middle _ => ModuleCat.ofHom ((φ.app vertex).hom.prodMap (φ.app vertex).hom)
  | .outer _ => φ.app vertex

/-- The components `loopApp` commute with the arrows of `E₇~`. Both sides of each square are
computed coordinatewise by the definitions of `TauCeti.affineE7LoopRep` and `loopApp`, so each
square reduces to linearity of the component of `φ`, except along the short arrow, where it also
uses naturality of `φ` along the loop. -/
private theorem loopApp_naturality (φ : M ⟶ N) {a b : Quiver.AffineE7} (e : a ⟶ b) :
    (affineE7LoopRep M).map e.toPath ≫ loopApp φ b =
      loopApp φ a ≫ (affineE7LoopRep N).map e.toPath := by
  let ψ := (φ.app vertex).hom
  refine ModuleCat.hom_ext (LinearMap.ext fun x ↦ ?_)
  cases e with
  | outerMiddle i =>
    match i with
    | 0 => exact Prod.ext rfl (map_zero ψ)
    | 1 => exact Prod.ext (map_zero ψ) rfl
  | middleInner i =>
    match i with
    | 0 => exact Prod.ext rfl (Prod.ext rfl (map_zero ψ))
    | 1 => exact Prod.ext (map_zero ψ) rfl
  | innerCenter i =>
    match i with
    | 0 => exact Prod.ext rfl (Prod.ext rfl (Prod.ext rfl (map_zero ψ)))
    | 1 => exact Prod.ext (map_zero ψ) rfl
  | shortCenter =>
    exact Prod.ext rfl (Prod.ext rfl (Prod.ext (map_add ψ _ _)
      ((map_add ψ _ _).trans (congrArg (ψ x.1 + ·)
        (NatTrans.naturality_apply φ loop.toPath x.2)))))

variable (k) in
/-- **A vector space with an endomorphism, as a representation of `E₇~`, as a functor**: a
morphism with component `ψ` acts by `ψ` at the outer vertices, by `ψ × ψ` at the middle and short
vertices, by `ψ × ψ × ψ` at the inner vertices and by `ψ × ψ × ψ × ψ` at the centre. -/
noncomputable def affineE7LoopFunctor :
    QuiverRep.{u, 0, w, t} k Quiver.OneLoop ⥤ QuiverRep.{u, 0, 0, t} k Quiver.AffineE7 where
  obj M := affineE7LoopRep M
  map φ := Paths.liftNatTrans (loopApp φ) (loopApp_naturality φ)
  map_id M := by
    refine NatTrans.ext (funext fun v ↦ ?_)
    cases v <;> rfl
  map_comp φ ψ := by
    refine NatTrans.ext (funext fun v ↦ ?_)
    cases v <;> rfl

/-- The functor `TauCeti.affineE7LoopFunctor` sends a representation to its `E₇~` representation. -/
@[simp]
theorem affineE7LoopFunctor_obj : (affineE7LoopFunctor k).obj M = affineE7LoopRep M :=
  (rfl)

/-- At the centre, `TauCeti.affineE7LoopFunctor` maps a morphism by the fourfold product of its
component at the loop vertex, transported to the functor's vertex spaces. -/
@[simp]
theorem affineE7LoopFunctor_map_app_center (φ : M ⟶ N) :
    ((affineE7LoopFunctor k).map φ).app Quiver.AffineE7.center =
      eqToHom ((Functor.congr_obj (affineE7LoopFunctor_obj (M := M)) _).trans
        affineE7LoopRep_obj_center) ≫
      ModuleCat.ofHom ((φ.app vertex).hom.prodMap ((φ.app vertex).hom.prodMap
        ((φ.app vertex).hom.prodMap (φ.app vertex).hom))) ≫
      eqToHom ((Functor.congr_obj (affineE7LoopFunctor_obj (M := N)) _).trans
        affineE7LoopRep_obj_center).symm :=
  (rfl)

/-- At the short vertex, `TauCeti.affineE7LoopFunctor` maps a morphism by the twofold product of
its component at the loop vertex, transported to the functor's vertex spaces. -/
@[simp]
theorem affineE7LoopFunctor_map_app_short (φ : M ⟶ N) :
    ((affineE7LoopFunctor k).map φ).app Quiver.AffineE7.short =
      eqToHom ((Functor.congr_obj (affineE7LoopFunctor_obj (M := M)) _).trans
        affineE7LoopRep_obj_short) ≫
      ModuleCat.ofHom ((φ.app vertex).hom.prodMap (φ.app vertex).hom) ≫
      eqToHom ((Functor.congr_obj (affineE7LoopFunctor_obj (M := N)) _).trans
        affineE7LoopRep_obj_short).symm :=
  (rfl)

/-- At each inner vertex, `TauCeti.affineE7LoopFunctor` maps a morphism by the threefold product
of its component at the loop vertex, transported to the functor's vertex spaces. -/
@[simp]
theorem affineE7LoopFunctor_map_app_inner (φ : M ⟶ N) (i : Fin 2) :
    ((affineE7LoopFunctor k).map φ).app (Quiver.AffineE7.inner i) =
      eqToHom ((Functor.congr_obj (affineE7LoopFunctor_obj (M := M)) _).trans
        (affineE7LoopRep_obj_inner i)) ≫
      ModuleCat.ofHom ((φ.app vertex).hom.prodMap ((φ.app vertex).hom.prodMap (φ.app vertex).hom)) ≫
      eqToHom ((Functor.congr_obj (affineE7LoopFunctor_obj (M := N)) _).trans
        (affineE7LoopRep_obj_inner i)).symm :=
  (rfl)

/-- At each middle vertex, `TauCeti.affineE7LoopFunctor` maps a morphism by the twofold product
of its component at the loop vertex, transported to the functor's vertex spaces. -/
@[simp]
theorem affineE7LoopFunctor_map_app_middle (φ : M ⟶ N) (i : Fin 2) :
    ((affineE7LoopFunctor k).map φ).app (Quiver.AffineE7.middle i) =
      eqToHom ((Functor.congr_obj (affineE7LoopFunctor_obj (M := M)) _).trans
        (affineE7LoopRep_obj_middle i)) ≫
      ModuleCat.ofHom ((φ.app vertex).hom.prodMap (φ.app vertex).hom) ≫
      eqToHom ((Functor.congr_obj (affineE7LoopFunctor_obj (M := N)) _).trans
        (affineE7LoopRep_obj_middle i)).symm :=
  (rfl)

/-- At each outer vertex, `TauCeti.affineE7LoopFunctor` maps a morphism by its component at the
loop vertex, transported to the functor's vertex spaces. -/
@[simp]
theorem affineE7LoopFunctor_map_app_outer (φ : M ⟶ N) (i : Fin 2) :
    ((affineE7LoopFunctor k).map φ).app (Quiver.AffineE7.outer i) =
      eqToHom ((Functor.congr_obj (affineE7LoopFunctor_obj (M := M)) _).trans
        (affineE7LoopRep_obj_outer i)) ≫
      φ.app vertex ≫
      eqToHom ((Functor.congr_obj (affineE7LoopFunctor_obj (M := N)) _).trans
        (affineE7LoopRep_obj_outer i)).symm :=
  (rfl)

/-! ### Full faithfulness -/

section Full

variable (g : affineE7LoopRep M ⟶ affineE7LoopRep N)

-- The components of `g` are recorded as linear maps between products of the vertex spaces, so
-- that its naturality squares, read on elements, are equations between tuples which `simp` can
-- take apart coordinatewise.

/-- The component of `g` at the centre, as a linear map between fourth powers. -/
private noncomputable def centerHom :
    M.obj vertex × M.obj vertex × M.obj vertex × M.obj vertex →ₗ[k]
      N.obj vertex × N.obj vertex × N.obj vertex × N.obj vertex :=
  (g.app Quiver.AffineE7.center).hom

/-- The component of `g` at the short vertex, as a linear map between squares. -/
private noncomputable def shortHom :
    M.obj vertex × M.obj vertex →ₗ[k] N.obj vertex × N.obj vertex :=
  (g.app Quiver.AffineE7.short).hom

/-- The component of `g` at an inner vertex, as a linear map between cubes. -/
private noncomputable def innerHom (i : Fin 2) :
    M.obj vertex × M.obj vertex × M.obj vertex →ₗ[k] N.obj vertex × N.obj vertex × N.obj vertex :=
  (g.app (Quiver.AffineE7.inner i)).hom

/-- The component of `g` at a middle vertex, as a linear map between squares. -/
private noncomputable def middleHom (i : Fin 2) :
    M.obj vertex × M.obj vertex →ₗ[k] N.obj vertex × N.obj vertex :=
  (g.app (Quiver.AffineE7.middle i)).hom

/-- The component of `g` at an outer vertex, as a linear map between the vertex spaces. -/
private noncomputable def outerHom (i : Fin 2) : M.obj vertex →ₗ[k] N.obj vertex :=
  (g.app (Quiver.AffineE7.outer i)).hom

/-! The seven naturality squares of `g`, read on elements. Each is
`CategoryTheory.NatTrans.naturality_apply` along one arrow, whose action on elements is given by
the corresponding `TauCeti.affineE7LoopRep_map_*_apply` lemma. -/

private theorem middleHom_zero_inl (x : M.obj vertex) :
    middleHom g 0 (x, 0) = (outerHom g 0 x, 0) := by
  rw [← affineE7LoopRep_map_outerMiddle_zero_apply x,
    ← affineE7LoopRep_map_outerMiddle_zero_apply (outerHom g 0 x)]
  exact NatTrans.naturality_apply g (Quiver.Hom.toPath (.outerMiddle 0)) x

private theorem innerHom_zero_mk (a b : M.obj vertex) :
    innerHom g 0 (a, b, 0) = ((middleHom g 0 (a, b)).1, (middleHom g 0 (a, b)).2, 0) := by
  rw [← affineE7LoopRep_map_middleInner_zero_apply (a, b),
    ← affineE7LoopRep_map_middleInner_zero_apply (middleHom g 0 (a, b))]
  exact NatTrans.naturality_apply g (Quiver.Hom.toPath (.middleInner 0)) (a, b)

private theorem centerHom_innerCenter_zero (a b c : M.obj vertex) :
    centerHom g (a, b, c, 0) = ((innerHom g 0 (a, b, c)).1, (innerHom g 0 (a, b, c)).2.1,
      (innerHom g 0 (a, b, c)).2.2, 0) := by
  rw [← affineE7LoopRep_map_innerCenter_zero_apply (a, b, c),
    ← affineE7LoopRep_map_innerCenter_zero_apply (innerHom g 0 (a, b, c))]
  exact NatTrans.naturality_apply g (Quiver.Hom.toPath (.innerCenter 0)) (a, b, c)

private theorem middleHom_one_inr (x : M.obj vertex) :
    middleHom g 1 (0, x) = (0, outerHom g 1 x) := by
  rw [← affineE7LoopRep_map_outerMiddle_one_apply x,
    ← affineE7LoopRep_map_outerMiddle_one_apply (outerHom g 1 x)]
  exact NatTrans.naturality_apply g (Quiver.Hom.toPath (.outerMiddle 1)) x

private theorem innerHom_one_mk (c d : M.obj vertex) :
    innerHom g 1 (0, c, d) = (0, middleHom g 1 (c, d)) := by
  rw [← affineE7LoopRep_map_middleInner_one_apply (c, d),
    ← affineE7LoopRep_map_middleInner_one_apply (middleHom g 1 (c, d))]
  exact NatTrans.naturality_apply g (Quiver.Hom.toPath (.middleInner 1)) (c, d)

private theorem centerHom_innerCenter_one (b c d : M.obj vertex) :
    centerHom g (0, b, c, d) = (0, innerHom g 1 (b, c, d)) := by
  rw [← affineE7LoopRep_map_innerCenter_one_apply (b, c, d),
    ← affineE7LoopRep_map_innerCenter_one_apply (innerHom g 1 (b, c, d))]
  exact NatTrans.naturality_apply g (Quiver.Hom.toPath (.innerCenter 1)) (b, c, d)

private theorem centerHom_shortCenter (a b : M.obj vertex) :
    centerHom g (a, b, a + b, a + (M.map loop.toPath).hom b) =
      ((shortHom g (a, b)).1, (shortHom g (a, b)).2,
        (shortHom g (a, b)).1 + (shortHom g (a, b)).2,
        (shortHom g (a, b)).1 + (N.map loop.toPath).hom (shortHom g (a, b)).2) := by
  rw [← affineE7LoopRep_map_shortCenter_apply (a, b),
    ← affineE7LoopRep_map_shortCenter_apply (shortHom g (a, b))]
  exact NatTrans.naturality_apply g (Quiver.Hom.toPath .shortCenter) (a, b)

/-- The centre component of `g` sends the first axis by the first outer component. -/
private theorem centerHom_first_axis (a : M.obj vertex) :
    centerHom g (a, 0, 0, 0) = (outerHom g 0 a, 0, 0, 0) := by
  rw [centerHom_innerCenter_zero, innerHom_zero_mk, middleHom_zero_inl]

/-- The centre component of `g` sends the fourth axis by the second outer component. -/
private theorem centerHom_fourth_axis (d : M.obj vertex) :
    centerHom g (0, 0, 0, d) = (0, 0, 0, outerHom g 1 d) := by
  rw [centerHom_innerCenter_one, innerHom_one_mk, middleHom_one_inr]

/-- The centre component of `g` sends the second axis into itself: the inner arrow of the first
long arm sees the second axis inside the image of its middle arrow, which misses the last two
coordinates, and the inner arrow of the second long arm misses the first coordinate. -/
private theorem centerHom_second_axis (b : M.obj vertex) :
    centerHom g (0, b, 0, 0) = (0, (middleHom g 0 (0, b)).2, 0, 0) := by
  have h := centerHom_innerCenter_zero g 0 b 0
  rw [innerHom_zero_mk] at h
  have h' := congrArg Prod.fst (centerHom_innerCenter_one g b 0 0)
  rw [h] at h' ⊢
  exact Prod.ext h' rfl

/-- The centre component of `g` sends the third axis into itself, symmetrically. -/
private theorem centerHom_third_axis (c : M.obj vertex) :
    centerHom g (0, 0, c, 0) = (0, 0, (middleHom g 1 (c, 0)).1, 0) := by
  have h := centerHom_innerCenter_one g 0 c 0
  rw [innerHom_one_mk] at h
  have h' := congrArg (fun p ↦ p.2.2.2) (centerHom_innerCenter_zero g 0 0 c)
  rw [h] at h' ⊢
  exact Prod.ext rfl (Prod.ext rfl (Prod.ext rfl h'))

/-- **The centre component of `g` acts on the four coordinates separately.** -/
private theorem centerHom_apply_of_axes (a b c d : M.obj vertex) :
    centerHom g (a, b, c, d) =
      (outerHom g 0 a, (middleHom g 0 (0, b)).2, (middleHom g 1 (c, 0)).1, outerHom g 1 d) := by
  have h : ((a, b, c, d) : M.obj vertex × M.obj vertex × M.obj vertex × M.obj vertex) =
      (a, 0, 0, 0) + (0, b, 0, 0) + (0, 0, c, 0) + (0, 0, 0, d) := by
    simp
  rw [h, map_add, map_add, map_add, centerHom_first_axis, centerHom_second_axis,
    centerHom_third_axis, centerHom_fourth_axis]
  simp

/-- Along the short arrow at `(a, 0)`, the third and fourth coordinate actions of the centre
component of `g` agree with the first one. -/
private theorem middleHom_one_fst_and_outerHom_one (a : M.obj vertex) :
    (middleHom g 1 (a, 0)).1 = outerHom g 0 a ∧ outerHom g 1 a = outerHom g 0 a := by
  have h := centerHom_shortCenter g a 0
  simp only [add_zero, map_zero, centerHom_apply_of_axes, Prod.mk_zero_zero, Prod.snd_zero,
    Prod.mk.injEq] at h
  obtain ⟨h1, h2, h3, h4⟩ := h
  rw [← h2, add_zero, ← h1] at h3
  rw [← h2, map_zero, add_zero, ← h1] at h4
  exact ⟨h3, h4⟩

/-- Along the short arrow at `(0, b)`, the second coordinate action of the centre component of
`g` agrees with the third one, and the fourth one intertwines the loop actions. -/
private theorem middleHom_zero_snd_and_intertwine (b : M.obj vertex) :
    (middleHom g 0 (0, b)).2 = outerHom g 0 b ∧
      outerHom g 0 ((M.map loop.toPath).hom b) =
        (N.map loop.toPath).hom (outerHom g 0 b) := by
  have h := centerHom_shortCenter g 0 b
  simp only [zero_add, map_zero, centerHom_apply_of_axes, Prod.mk.injEq] at h
  obtain ⟨h1, h2, h3, h4⟩ := h
  rw [← h1, zero_add, ← h2, (middleHom_one_fst_and_outerHom_one g b).1] at h3
  rw [← h1, zero_add, ← h2, ← h3, (middleHom_one_fst_and_outerHom_one g _).2] at h4
  exact ⟨h3.symm, h4⟩

/-- **The centre component of `g` is `ψ × ψ × ψ × ψ` for its first outer component `ψ`.** -/
private theorem centerHom_apply (a b c d : M.obj vertex) :
    centerHom g (a, b, c, d) =
      (outerHom g 0 a, outerHom g 0 b, outerHom g 0 c, outerHom g 0 d) := by
  rw [centerHom_apply_of_axes, (middleHom_zero_snd_and_intertwine g b).1,
    (middleHom_one_fst_and_outerHom_one g c).1, (middleHom_one_fst_and_outerHom_one g d).2]

/-- **Every inner component of `g` is `ψ × ψ × ψ` for its first outer component `ψ`.** -/
private theorem innerHom_apply (i : Fin 2) (a b c : M.obj vertex) :
    innerHom g i (a, b, c) = (outerHom g 0 a, outerHom g 0 b, outerHom g 0 c) := by
  match i with
  | 0 =>
    have h := centerHom_innerCenter_zero g a b c
    rw [centerHom_apply] at h
    exact Prod.ext (congrArg Prod.fst h).symm
      (Prod.ext (congrArg (fun p ↦ p.2.1) h).symm (congrArg (fun p ↦ p.2.2.1) h).symm)
  | 1 =>
    have h := centerHom_innerCenter_one g a b c
    rw [centerHom_apply] at h
    exact (congrArg Prod.snd h).symm

/-- **Every middle component of `g` is `ψ × ψ` for its first outer component `ψ`.** -/
private theorem middleHom_apply (i : Fin 2) (a b : M.obj vertex) :
    middleHom g i (a, b) = (outerHom g 0 a, outerHom g 0 b) := by
  match i with
  | 0 =>
    have h := innerHom_zero_mk g a b
    rw [innerHom_apply] at h
    exact Prod.ext (congrArg Prod.fst h).symm (congrArg (fun p ↦ p.2.1) h).symm
  | 1 =>
    have h := innerHom_one_mk g a b
    rw [innerHom_apply] at h
    exact (congrArg Prod.snd h).symm

/-- **The short component of `g` is `ψ × ψ` for its first outer component `ψ`.** -/
private theorem shortHom_apply (a b : M.obj vertex) :
    shortHom g (a, b) = (outerHom g 0 a, outerHom g 0 b) := by
  have h := centerHom_shortCenter g a b
  rw [centerHom_apply] at h
  exact Prod.ext (congrArg Prod.fst h).symm (congrArg (fun p ↦ p.2.1) h).symm

/-- **Every outer component of `g` is the first one.** -/
private theorem outerHom_eq (i : Fin 2) : outerHom g i = outerHom g 0 := by
  ext x
  match i with
  | 0 => rfl
  | 1 => exact (middleHom_one_fst_and_outerHom_one g x).2

/-- The morphism of representations of `•↺` underlying `g`: its component at the first outer
vertex, which commutes with the loop by `middleHom_zero_snd_and_intertwine`. -/
private noncomputable def unloop : M ⟶ N :=
  Paths.liftNatTrans (fun _ ↦ g.app (Quiver.AffineE7.outer 0))
    fun {a b} e ↦ by
      cases a
      cases b
      rw [Subsingleton.elim e loop]
      exact ModuleCat.hom_ext
        (LinearMap.ext fun x ↦ (middleHom_zero_snd_and_intertwine g x).2)

end Full

variable (k) in
/-- **The functor `TauCeti.affineE7LoopFunctor` is fully faithful.** A morphism between images is
determined by its component `ψ` at the first outer vertex: by naturality along the seven arrows,
every other component is a power of `ψ`, and `ψ` commutes with the loop. -/
noncomputable def fullyFaithfulAffineE7LoopFunctor :
    (affineE7LoopFunctor.{u, w, t} k).FullyFaithful where
  preimage {M N} g := unloop g
  map_preimage {M N} g := by
    refine NatTrans.ext (funext fun v ↦ ?_)
    refine ModuleCat.hom_ext (LinearMap.ext fun x ↦ ?_)
    cases v with
    | center =>
      obtain ⟨a, b, c, d⟩ := x
      exact (centerHom_apply g a b c d).symm
    | short =>
      obtain ⟨a, b⟩ := x
      exact (shortHom_apply g a b).symm
    | inner i =>
      obtain ⟨a, b, c⟩ := x
      exact (innerHom_apply g i a b c).symm
    | middle i =>
      obtain ⟨a, b⟩ := x
      exact (middleHom_apply g i a b).symm
    | outer i => exact (LinearMap.congr_fun (outerHom_eq g i) x).symm
  preimage_map {M N} φ := by
    refine NatTrans.ext (funext fun v ↦ ?_)
    cases v
    rfl

/-- **The functor `TauCeti.affineE7LoopFunctor` reflects and preserves isomorphism.** -/
@[simp]
theorem nonempty_affineE7LoopRep_iso_iff :
    Nonempty (affineE7LoopRep M ≅ affineE7LoopRep N) ↔ Nonempty (M ≅ N) :=
  ⟨fun ⟨e⟩ ↦ ⟨(fullyFaithfulAffineE7LoopFunctor k).preimageIso e⟩,
    fun ⟨e⟩ ↦ ⟨(affineE7LoopFunctor k).mapIso e⟩⟩

/-- **The image of an indecomposable representation of `•↺` is indecomposable**: the functor is
fully faithful, so it matches the idempotent endomorphisms of `M` with those of its image. -/
theorem indecomposable_affineE7LoopRep (hM : Indecomposable M) :
    Indecomposable (affineE7LoopRep M) :=
  (affineE7LoopFunctor k).indecomposable_obj_of_map_bijective hM
    ((fullyFaithfulAffineE7LoopFunctor k).map_bijective M M)

/-! ### Infinite representation type -/

/-- **Finite representation type of `E₇~` would force it on the loop quiver**: the functor
`TauCeti.affineE7LoopFunctor` carries the finite-dimensional indecomposables of `•↺` to
finite-dimensional indecomposables of `TauCeti.Quiver.AffineE7` and reflects isomorphism among
them. -/
theorem IsFiniteRepType.oneLoop_of_affineE7
    (h : IsFiniteRepType.{u, 0, 0, t} k Quiver.AffineE7) :
    IsFiniteRepType.{u, 0, w, t} k Quiver.OneLoop :=
  isFiniteRepType_of_map (fun _ ↦ False) affineE7LoopRep
    (fun _ hM hM' _ ↦ ⟨isFinDim_affineE7LoopRep hM, indecomposable_affineE7LoopRep hM'⟩)
    (fun _ _ _ _ _ _ ↦ nonempty_affineE7LoopRep_iso_iff.mp) (fun _ _ _ _ h _ ↦ h.elim) h

/-- **The extended Dynkin quiver `E₇~` has infinite representation type over every field.** The
images of the nilpotent Jordan blocks (`TauCeti.oneLoopNilpotentRep`) are infinitely many pairwise
non-isomorphic finite-dimensional indecomposables. -/
theorem not_isFiniteRepType_affineE7 (k : Type u) [Field k] :
    ¬ IsFiniteRepType.{u, 0, 0, u} k Quiver.AffineE7 :=
  fun h ↦ not_isFiniteRepType_oneLoop.{u, 0} k h.oneLoop_of_affineE7

end TauCeti

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.Category.CommAlgCat.Fpqc
public import TauCeti.Algebra.AlgebraicGroup.LoopGroup.Basic
public import Mathlib.GroupTheory.GroupAction.Quotient
public import Mathlib.CategoryTheory.Sites.LocallyBijective
public import Mathlib.CategoryTheory.Sites.Monoidal
import Mathlib.CategoryTheory.Monoidal.Closed.Types
import TauCeti.Algebra.AlgebraicGroup.Trivial

/-!
# The fpqc quotient of the loop group by positive loops

For an affine group with coordinate Hopf algebra `H` over a commutative ring `k`, the
loop Grassmannian is the fpqc sheafification of the left cosets `LG(R)/L⁺G(R)`. The site is
the affine site over `Spec k` with the topology induced by the big fpqc topology, and its
objects include every commutative `k`-algebra. No smoothness, reductivity, or reducedness
assumption is needed for this quotient sheaf.

Invariant natural maps from loops to fpqc sheaves factor uniquely through the loop Grassmannian.
For arbitrary presheaf targets, `loopCosetHomEquiv` gives the corresponding universal property
of the coset presheaf. The quotient projection is locally surjective. Left multiplication extends
from cosets to an action of loops on the quotient, naturally in the value algebra.

This construction uses the coefficientwise `k`-algebra structure on Laurent series, as does
`TauCeti.HopfAlgebra.loopGroup`. It does not assert representability or a torsor description.
The sheafification argument follows `CommHopfAlgCat.fppfHomogeneousQuotientHomEquiv` and
`CommHopfAlgCat.fppfHomogeneousQuotientAction`, applied here to the image of positive loops
rather than a closed subgroup cut out by a Hopf ideal (and the fppf topology).

## References

* X. Zhu, *An introduction to affine Grassmannians and the geometric Satake equivalence*,
  §1.1, especially Theorem 1.1.3.
-/

public section

open CategoryTheory Opposite MonoidalCategory

-- Select the same coefficientwise algebra structure as `loopGroup`.
attribute [local instance 1100] HahnSeries.instAlgebra

namespace TauCeti.HopfAlgebra

universe u

noncomputable section

variable (k : Type u) [CommRing k] (H : Type u) [Semiring H] [_root_.HopfAlgebra k H]

/-- Loops as a universe-lifted type-valued presheaf on the affine site. -/
abbrev loopPresheaf : ((CommAlgCat.{u} k)ᵒᵖ)ᵒᵖ ⥤ Type (u + 1) :=
  unopUnop (CommAlgCat.{u} k) ⋙ loopGroup k H ⋙ forget GrpCat ⋙ uliftFunctor.{u + 1, u}

/-- The presheaf of left cosets `LG(R)/L⁺G(R)`, before fpqc sheafification. -/
def loopCosetPresheaf : ((CommAlgCat.{u} k)ᵒᵖ)ᵒᵖ ⥤ Type (u + 1) where
  obj A := ULift.{u + 1, u} ((loopGroup k H).obj A.unop.unop ⧸
    ((positiveLoopToLoop k H).app A.unop.unop).hom.range)
  map {A B} f := ↾fun q ↦ ULift.up <| Quotient.map'
    ((loopGroup k H).map f.unop.unop) (fun x y hxy ↦ by
      apply QuotientGroup.leftRel_apply.mpr
      obtain ⟨n, hn⟩ := QuotientGroup.leftRel_apply.mp hxy
      refine ⟨(positiveLoopGroup k H).map f.unop.unop n, ?_⟩
      have h := congrArg (fun t ↦ t n) ((positiveLoopToLoop k H).naturality f.unop.unop)
      simpa only [ConcreteCategory.comp_apply, hn, map_mul, map_inv] using h) q.down
  map_id A := by
    ext q
    obtain ⟨q⟩ := q
    induction q using Quotient.inductionOn' with | _ g =>
      simp
  map_comp f g := by
    ext q
    obtain ⟨q⟩ := q
    induction q using Quotient.inductionOn' with | _ x =>
      exact congrArg (fun z ↦ QuotientGroup.mk z)
        (congrArg (fun t ↦ t x) ((loopGroup k H).map_comp f.unop.unop g.unop.unop))

/-- The coset of a loop. -/
def loopCosetMk (A : ((CommAlgCat.{u} k)ᵒᵖ)ᵒᵖ)
    (g : (loopGroup k H).obj A.unop.unop) : (loopCosetPresheaf k H).obj A :=
  ULift.up (QuotientGroup.mk g)

/-- Every coset has a representative. -/
@[elab_as_elim]
theorem loopCoset_induction_on {A : ((CommAlgCat.{u} k)ᵒᵖ)ᵒᵖ}
    (q : (loopCosetPresheaf k H).obj A) {P : (loopCosetPresheaf k H).obj A → Prop}
    (h : ∀ g, P (loopCosetMk k H A g)) : P q := by
  obtain ⟨q⟩ := q
  induction q using Quotient.inductionOn' with | _ g => exact h g

/-- Restricting a coset restricts its representative. -/
@[simp]
theorem loopCosetPresheaf_map_mk {A B : ((CommAlgCat.{u} k)ᵒᵖ)ᵒᵖ} (f : A ⟶ B)
    (g : (loopGroup k H).obj A.unop.unop) :
    (loopCosetPresheaf k H).map f (loopCosetMk k H A g) =
      loopCosetMk k H B ((loopGroup k H).map f.unop.unop g) := (rfl)

/-- Two loops give the same coset exactly when their right difference is a positive loop. -/
theorem loopCosetMk_eq_iff (A : ((CommAlgCat.{u} k)ᵒᵖ)ᵒᵖ)
    (g g' : (loopGroup k H).obj A.unop.unop) :
    loopCosetMk k H A g = loopCosetMk k H A g' ↔
      ∃ n : (positiveLoopGroup k H).obj A.unop.unop,
        (positiveLoopToLoop k H).app A.unop.unop n = g⁻¹ * g' :=
  ULift.up_inj.trans QuotientGroup.eq

/-- The pointwise surjective projection from loops onto cosets. -/
def loopCosetProjection : loopPresheaf k H ⟶ loopCosetPresheaf k H where
  app A := ↾fun g ↦ loopCosetMk k H A g.down
  naturality _ _ _ := rfl

/-- The coset projection on representatives. -/
@[simp]
theorem loopCosetProjection_app (A : ((CommAlgCat.{u} k)ᵒᵖ)ᵒᵖ)
    (g : (loopGroup k H).obj A.unop.unop) :
    dsimp% (loopCosetProjection k H).app A (ULift.up g) = loopCosetMk k H A g := (rfl)

/-- Every coset lifts to a loop over the same value algebra. -/
theorem loopCosetProjection_surjective (A : ((CommAlgCat.{u} k)ᵒᵖ)ᵒᵖ) :
    Function.Surjective ((loopCosetProjection k H).app A) := by
  intro q
  induction q using loopCoset_induction_on k H with
  | h g => exact ⟨ULift.up g, rfl⟩

/-- Right multiplication by a positive loop does not change a coset. -/
@[simp]
theorem loopCosetMk_mul_positive (A : ((CommAlgCat.{u} k)ᵒᵖ)ᵒᵖ)
    (g : (loopGroup k H).obj A.unop.unop)
    (n : (positiveLoopGroup k H).obj A.unop.unop) :
    dsimp% loopCosetMk k H A (g * (positiveLoopToLoop k H).app A.unop.unop n) =
      loopCosetMk k H A g := by
  exact congrArg ULift.up (QuotientGroup.mk_mul_of_mem g ⟨n, rfl⟩)

/-- Natural maps invariant under right multiplication by positive loops. -/
def IsPositiveLoopInvariant {F : ((CommAlgCat.{u} k)ᵒᵖ)ᵒᵖ ⥤ Type (u + 1)}
    (f : loopPresheaf k H ⟶ F) : Prop :=
  ∀ (A : ((CommAlgCat.{u} k)ᵒᵖ)ᵒᵖ) (g : (loopGroup k H).obj A.unop.unop)
    (n : (positiveLoopGroup k H).obj A.unop.unop),
    f.app A (ULift.up (g * (positiveLoopToLoop k H).app A.unop.unop n)) =
      f.app A (ULift.up g)

/-- Invariance means componentwise invariance under right multiplication by positive loops. -/
theorem isPositiveLoopInvariant_iff {F : ((CommAlgCat.{u} k)ᵒᵖ)ᵒᵖ ⥤ Type (u + 1)}
    (f : loopPresheaf k H ⟶ F) :
    IsPositiveLoopInvariant k H f ↔
      ∀ (A : ((CommAlgCat.{u} k)ᵒᵖ)ᵒᵖ) (g : (loopGroup k H).obj A.unop.unop)
        (n : (positiveLoopGroup k H).obj A.unop.unop),
        f.app A (ULift.up (g * (positiveLoopToLoop k H).app A.unop.unop n)) =
          f.app A (ULift.up g) := Iff.rfl

/-- The coset projection is invariant under right multiplication by positive loops. -/
theorem isPositiveLoopInvariant_loopCosetProjection :
    IsPositiveLoopInvariant k H (loopCosetProjection k H) :=
  loopCosetMk_mul_positive k H

/-- Descending an invariant natural map to the coset presheaf. -/
def loopCosetLift {F : ((CommAlgCat.{u} k)ᵒᵖ)ᵒᵖ ⥤ Type (u + 1)}
    (f : loopPresheaf k H ⟶ F) (hf : IsPositiveLoopInvariant k H f) :
    loopCosetPresheaf k H ⟶ F where
  app A := ↾fun q ↦ Quotient.liftOn' q.down (fun g ↦ f.app A (ULift.up g))
    (fun g g' hgg' ↦ by
      obtain ⟨n, hn⟩ := QuotientGroup.leftRel_apply.mp hgg'
      have h := hf A g n
      simpa only [hn, mul_inv_cancel_left] using h.symm)
  naturality {A B} χ := by
    ext q
    induction q using loopCoset_induction_on k H with | h g =>
      exact congrArg (fun t ↦ t (ULift.up g)) (f.naturality χ)

/-- The descended map has the prescribed value on a coset representative. -/
@[simp]
theorem loopCosetLift_app_mk {F : ((CommAlgCat.{u} k)ᵒᵖ)ᵒᵖ ⥤ Type (u + 1)}
    (f : loopPresheaf k H ⟶ F) (hf : IsPositiveLoopInvariant k H f)
    (A : ((CommAlgCat.{u} k)ᵒᵖ)ᵒᵖ) (g : (loopGroup k H).obj A.unop.unop) :
    (loopCosetLift k H f hf).app A (loopCosetMk k H A g) = f.app A (ULift.up g) := (rfl)

/-- Restricting the descended map along the projection recovers the original map. -/
@[reassoc (attr := simp)]
theorem loopCosetProjection_comp_lift {F : ((CommAlgCat.{u} k)ᵒᵖ)ᵒᵖ ⥤ Type (u + 1)}
    (f : loopPresheaf k H ⟶ F) (hf : IsPositiveLoopInvariant k H f) :
    loopCosetProjection k H ≫ loopCosetLift k H f hf = f := by
  ext A g
  rfl

/-- Maps out of the coset presheaf are determined on loops. -/
theorem loopCoset_hom_ext {F : ((CommAlgCat.{u} k)ᵒᵖ)ᵒᵖ ⥤ Type (u + 1)}
    {f g : loopCosetPresheaf k H ⟶ F}
    (h : loopCosetProjection k H ≫ f = loopCosetProjection k H ≫ g) : f = g := by
  ext A q
  induction q using loopCoset_induction_on k H with | h x =>
    exact congrArg (fun t ↦ t.app A (ULift.up x)) h

/-- Maps out of cosets are exactly invariant natural maps out of loops. -/
def loopCosetHomEquiv (F : ((CommAlgCat.{u} k)ᵒᵖ)ᵒᵖ ⥤ Type (u + 1)) :
    (loopCosetPresheaf k H ⟶ F) ≃
      {f : loopPresheaf k H ⟶ F // IsPositiveLoopInvariant k H f} where
  toFun f := ⟨loopCosetProjection k H ≫ f, fun A g n ↦
    congrArg (fun q ↦ f.app A q) (loopCosetMk_mul_positive k H A g n)⟩
  invFun f := loopCosetLift k H f.val f.property
  left_inv _ := loopCoset_hom_ext k H (loopCosetProjection_comp_lift k H _ _)
  right_inv _ := Subtype.ext (loopCosetProjection_comp_lift k H _ _)

/-- The loop Grassmannian as an fpqc quotient sheaf on all commutative `k`-algebras. -/
def loopGrassmannian : Sheaf (CommAlgCat.fpqcTopology k) (Type (u + 1)) :=
  (presheafToSheaf (CommAlgCat.fpqcTopology k) (Type (u + 1))).obj (loopCosetPresheaf k H)

/-- The underlying presheaf of the loop Grassmannian is the sheafification of cosets. -/
theorem loopGrassmannian_obj :
    (loopGrassmannian k H).obj = sheafify (CommAlgCat.fpqcTopology k) (loopCosetPresheaf k H) :=
  (rfl)

/-- The natural quotient projection `LG → Gr_G`. -/
def loopGrassmannianProjection : loopPresheaf k H ⟶ (loopGrassmannian k H).obj :=
  loopCosetProjection k H ≫ toSheafify (CommAlgCat.fpqcTopology k) (loopCosetPresheaf k H)

/-- The quotient projection is the coset projection followed by the sheafification unit. -/
theorem loopGrassmannianProjection_def :
    loopGrassmannianProjection k H = loopCosetProjection k H ≫
      toSheafify (CommAlgCat.fpqcTopology k) (loopCosetPresheaf k H) ≫
        eqToHom (loopGrassmannian_obj k H).symm := (rfl)

/-- The image of a loop in the fpqc quotient. -/
def loopGrassmannianMk (A : ((CommAlgCat.{u} k)ᵒᵖ)ᵒᵖ)
    (g : (loopGroup k H).obj A.unop.unop) : (loopGrassmannian k H).obj.obj A :=
  (loopGrassmannianProjection k H).app A (ULift.up g)

/-- Evaluating the projection on a loop gives its quotient class. -/
@[simp]
theorem loopGrassmannianProjection_app (A : ((CommAlgCat.{u} k)ᵒᵖ)ᵒᵖ)
    (g : (loopGroup k H).obj A.unop.unop) :
    dsimp% (loopGrassmannianProjection k H).app A (ULift.up g) =
      loopGrassmannianMk k H A g := (rfl)

/-- The coset equality sieve consists of restrictions whose right difference is positive. -/
theorem equalizerSieve_loopCosetMk_apply {A B : ((CommAlgCat.{u} k)ᵒᵖ)ᵒᵖ}
    (f : A ⟶ B) (g g' : (loopGroup k H).obj A.unop.unop) :
    Presheaf.equalizerSieve (F := loopCosetPresheaf k H)
      (loopCosetMk k H A g) (loopCosetMk k H A g') f.unop ↔
      ∃ n : (positiveLoopGroup k H).obj B.unop.unop,
        (positiveLoopToLoop k H).app B.unop.unop n =
          ((loopGroup k H).map f.unop.unop g)⁻¹ * (loopGroup k H).map f.unop.unop g' := by
  simpa only [Presheaf.equalizerSieve_apply, Quiver.Hom.op_unop,
    loopCosetPresheaf_map_mk] using
    loopCosetMk_eq_iff k H B ((loopGroup k H).map f.unop.unop g)
      ((loopGroup k H).map f.unop.unop g')

/-- Two loop classes agree exactly when their cosets agree fpqc locally.
By `equalizerSieve_loopCosetMk_apply`, this is the covering sieve of restrictions on which
the right difference of the two loops lies in the image of positive loops. -/
theorem loopGrassmannianMk_eq_iff (A : ((CommAlgCat.{u} k)ᵒᵖ)ᵒᵖ)
    (g g' : (loopGroup k H).obj A.unop.unop) :
    loopGrassmannianMk k H A g = loopGrassmannianMk k H A g' ↔
      Presheaf.equalizerSieve (F := loopCosetPresheaf k H)
        (loopCosetMk k H A g) (loopCosetMk k H A g') ∈
        CommAlgCat.fpqcTopology k A.unop := by
  constructor
  · exact Presheaf.equalizerSieve_mem (CommAlgCat.fpqcTopology k)
      (toSheafify (CommAlgCat.fpqcTopology k) (loopCosetPresheaf k H)) _ _
  · intro hS
    refine (((isSheaf_iff_isSheaf_of_type _ _).mp
      (loopGrassmannian k H).property).isSeparated _ hS).ext ?_
    intro B f hf
    -- Identify sections with their sheafification-unit values to use the unit's naturality.
    change (sheafify (CommAlgCat.fpqcTopology k) (loopCosetPresheaf k H)).map f.op
      ((toSheafify (CommAlgCat.fpqcTopology k) (loopCosetPresheaf k H)).app A
        (loopCosetMk k H A g)) =
      (sheafify (CommAlgCat.fpqcTopology k) (loopCosetPresheaf k H)).map f.op
        ((toSheafify (CommAlgCat.fpqcTopology k) (loopCosetPresheaf k H)).app A
          (loopCosetMk k H A g'))
    rw [← NatTrans.naturality_apply, ← NatTrans.naturality_apply]
    exact congrArg ((toSheafify (CommAlgCat.fpqcTopology k)
      (loopCosetPresheaf k H)).app (op B)) hf

/-- Changing the value algebra maps a representative by the loop-group functor. -/
@[simp]
theorem loopGrassmannian_map_mk {A B : ((CommAlgCat.{u} k)ᵒᵖ)ᵒᵖ} (f : A ⟶ B)
    (g : (loopGroup k H).obj A.unop.unop) :
    (loopGrassmannian k H).obj.map f (loopGrassmannianMk k H A g) =
      loopGrassmannianMk k H B ((loopGroup k H).map f.unop.unop g) :=
  (congrArg (fun t ↦ t (ULift.up g)) ((loopGrassmannianProjection k H).naturality f)).symm

/-- Right multiplication by a positive loop does not change the quotient point. -/
@[simp]
theorem loopGrassmannianMk_mul_positive (A : ((CommAlgCat.{u} k)ᵒᵖ)ᵒᵖ)
    (g : (loopGroup k H).obj A.unop.unop)
    (n : (positiveLoopGroup k H).obj A.unop.unop) :
    dsimp% loopGrassmannianMk k H A (g * (positiveLoopToLoop k H).app A.unop.unop n) =
      loopGrassmannianMk k H A g :=
  congrArg ((toSheafify (CommAlgCat.fpqcTopology k) (loopCosetPresheaf k H)).app A)
    (loopCosetMk_mul_positive k H A g n)

/-- The quotient's base point, represented by the identity loop. -/
def loopGrassmannianBasePoint (A : ((CommAlgCat.{u} k)ᵒᵖ)ᵒᵖ) :
    (loopGrassmannian k H).obj.obj A := loopGrassmannianMk k H A 1

/-- The class of the identity loop is the base point. -/
@[simp]
theorem loopGrassmannianMk_one (A : ((CommAlgCat.{u} k)ᵒᵖ)ᵒᵖ) :
    loopGrassmannianMk k H A 1 = loopGrassmannianBasePoint k H A := (rfl)

/-- The base point is natural in the value algebra. -/
@[simp]
theorem loopGrassmannian_map_basePoint {A B : ((CommAlgCat.{u} k)ᵒᵖ)ᵒᵖ} (f : A ⟶ B) :
    (loopGrassmannian k H).obj.map f (loopGrassmannianBasePoint k H A) =
      loopGrassmannianBasePoint k H B := by
  exact (loopGrassmannian_map_mk k H f 1).trans
    (congrArg (loopGrassmannianMk k H B) ((loopGroup k H).map f.unop.unop).hom.map_one)

/-- The quotient projection is fpqc locally surjective. -/
instance loopGrassmannianProjection_isLocallySurjective :
    Presheaf.IsLocallySurjective (CommAlgCat.fpqcTopology k) (loopGrassmannianProjection k H) := by
  have : Presheaf.IsLocallySurjective (CommAlgCat.fpqcTopology k) (loopCosetProjection k H) :=
    Presheaf.isLocallySurjective_of_surjective _ _ (loopCosetProjection_surjective k H)
  have := Presheaf.isLocallySurjective_toSheafify'
    (CommAlgCat.fpqcTopology k) (loopCosetPresheaf k H)
  exact Presheaf.isLocallySurjective_comp (CommAlgCat.fpqcTopology k)
    (loopCosetProjection k H)
    (toSheafify (CommAlgCat.fpqcTopology k) (loopCosetPresheaf k H))

/-- Maps from the fpqc quotient to a sheaf are exactly invariant natural maps from loops. -/
def loopGrassmannianHomEquiv (F : Sheaf (CommAlgCat.fpqcTopology k) (Type (u + 1))) :
    (loopGrassmannian k H ⟶ F) ≃
      {f : loopPresheaf k H ⟶ F.obj // IsPositiveLoopInvariant k H f} :=
  ((sheafificationAdjunction (CommAlgCat.fpqcTopology k) (Type (u + 1))).homEquiv
    (loopCosetPresheaf k H) F).trans (loopCosetHomEquiv k H F.obj)

/-- The universal property restricts a map along the quotient projection. -/
@[simp]
theorem loopGrassmannianHomEquiv_apply
    (F : Sheaf (CommAlgCat.fpqcTopology k) (Type (u + 1))) (f : loopGrassmannian k H ⟶ F) :
    (loopGrassmannianHomEquiv k H F f).val = loopGrassmannianProjection k H ≫ f.hom := by
  dsimp [loopGrassmannianHomEquiv, loopCosetHomEquiv, loopGrassmannianProjection]
  exact (Category.assoc _ _ _).symm

/-- Maps out of the loop Grassmannian are determined by their values on loop representatives. -/
theorem loopGrassmannian_hom_ext
    {F : Sheaf (CommAlgCat.fpqcTopology k) (Type (u + 1))} {f g : loopGrassmannian k H ⟶ F}
    (h : loopGrassmannianProjection k H ≫ f.hom = loopGrassmannianProjection k H ≫ g.hom) :
    f = g := by
  apply (loopGrassmannianHomEquiv k H F).injective
  apply Subtype.ext
  simpa only [loopGrassmannianHomEquiv_apply] using h

/-- Sheaf morphisms out of the quotient are determined on loop classes. -/
@[ext]
theorem loopGrassmannian_hom_ext_mk
    {F : Sheaf (CommAlgCat.fpqcTopology k) (Type (u + 1))} {f g : loopGrassmannian k H ⟶ F}
    (h : ∀ (A : ((CommAlgCat.{u} k)ᵒᵖ)ᵒᵖ) (x : (loopGroup k H).obj A.unop.unop),
      f.hom.app A (loopGrassmannianMk k H A x) =
        g.hom.app A (loopGrassmannianMk k H A x)) : f = g := by
  apply loopGrassmannian_hom_ext
  ext A ⟨x⟩
  exact h A x

/-- The inverse universal property recovers the invariant map on representatives. -/
@[reassoc (attr := simp)]
theorem loopGrassmannianHomEquiv_symm_apply
    (F : Sheaf (CommAlgCat.fpqcTopology k) (Type (u + 1)))
    (f : loopPresheaf k H ⟶ F.obj) (hf : IsPositiveLoopInvariant k H f) :
    loopGrassmannianProjection k H ≫
      ((loopGrassmannianHomEquiv k H F).symm ⟨f, hf⟩).hom = f := by
  exact (loopGrassmannianHomEquiv_apply k H F _).symm.trans
    (congrArg Subtype.val ((loopGrassmannianHomEquiv k H F).apply_symm_apply ⟨f, hf⟩))

/-- Equality of sheaf sections can be checked after changes of algebra on which a fixed
quotient section has a loop representative. -/
theorem eq_of_forall_loopGrassmannian_map_eq_mk
    (F : Sheaf (CommAlgCat.fpqcTopology k) (Type (u + 1)))
    {A : ((CommAlgCat.{u} k)ᵒᵖ)ᵒᵖ} (z : (loopGrassmannian k H).obj.obj A)
    {x y : F.obj.obj A}
    (h : ∀ (B : ((CommAlgCat.{u} k)ᵒᵖ)ᵒᵖ) (f : A ⟶ B)
      (g : (loopGroup k H).obj B.unop.unop),
      (loopGrassmannian k H).obj.map f z = loopGrassmannianMk k H B g →
        F.obj.map f x = F.obj.map f y) : x = y := by
  have hS := Presheaf.imageSieve_mem (CommAlgCat.fpqcTopology k)
    (loopGrassmannianProjection k H) z
  refine (((isSheaf_iff_isSheaf_of_type _ _).mp F.property).isSeparated _ hS).ext ?_
  rintro B f ⟨⟨g⟩, hg⟩
  exact h _ f.op g hg.symm

/-- Left multiplication of a loop and a coset. -/
private def loopCosetAction :
    loopPresheaf k H ⊗ loopCosetPresheaf k H ⟶ loopCosetPresheaf k H where
  app A := ↾fun p ↦ ULift.up
    (HSMul.hSMul (α := (loopGroup k H).obj A.unop.unop) p.1.down p.2.down)
  naturality {A B} f := by
    ext ⟨⟨x⟩, q⟩
    induction q using loopCoset_induction_on k H with | h g =>
      exact congrArg (loopCosetMk k H B)
        (((loopGroup k H).map f.unop.unop).hom.map_mul x g).symm

/-- Left multiplication of loops on the fpqc quotient. The acting loops may be over any
value algebra; they need not be extended from the base ring. -/
def loopGrassmannianAction :
    loopPresheaf k H ⊗ (loopGrassmannian k H).obj ⟶ (loopGrassmannian k H).obj :=
  (((GrothendieckTopology.W_toSheafify (CommAlgCat.fpqcTopology k)
    (loopCosetPresheaf k H)).whiskerLeft (loopPresheaf k H)).homEquiv _
      (loopGrassmannian k H).property).symm
    (loopCosetAction k H ≫ toSheafify (CommAlgCat.fpqcTopology k) (loopCosetPresheaf k H))

private theorem whiskerLeft_toSheafify_comp_loopGrassmannianAction :
    loopPresheaf k H ◁ toSheafify (CommAlgCat.fpqcTopology k) (loopCosetPresheaf k H) ≫
      loopGrassmannianAction k H =
    loopCosetAction k H ≫ toSheafify (CommAlgCat.fpqcTopology k) (loopCosetPresheaf k H) :=
  (((GrothendieckTopology.W_toSheafify (CommAlgCat.fpqcTopology k)
    (loopCosetPresheaf k H)).whiskerLeft (loopPresheaf k H)).homEquiv _
      (loopGrassmannian k H).property).apply_symm_apply _

/-- The action of loops on quotient points over a value algebra. -/
instance instSMulLoopGrassmannian (A : ((CommAlgCat.{u} k)ᵒᵖ)ᵒᵖ) :
    SMul ((loopGroup k H).obj A.unop.unop) ((loopGrassmannian k H).obj.obj A) where
  smul x z := (loopGrassmannianAction k H).app A (ULift.up x, z)

/-- Evaluating the action morphism gives the scalar action on sections. -/
@[simp]
theorem loopGrassmannianAction_app (A : ((CommAlgCat.{u} k)ᵒᵖ)ᵒᵖ)
    (x : (loopGroup k H).obj A.unop.unop) (z : (loopGrassmannian k H).obj.obj A) :
    dsimp% (loopGrassmannianAction k H).app A (ULift.up x, z) = x • z := (rfl)

/-- Acting on the class of a loop multiplies its representative on the left. -/
@[simp]
theorem smul_loopGrassmannianMk (A : ((CommAlgCat.{u} k)ᵒᵖ)ᵒᵖ)
    (x g : (loopGroup k H).obj A.unop.unop) :
    dsimp% x • loopGrassmannianMk k H A g = loopGrassmannianMk k H A (x * g) :=
  congrArg (fun α ↦ α.app A (ULift.up x, loopCosetMk k H A g))
    (whiskerLeft_toSheafify_comp_loopGrassmannianAction k H)

/-- Changing the value algebra commutes with the loop-group action. -/
@[simp]
theorem loopGrassmannian_map_smul {A B : ((CommAlgCat.{u} k)ᵒᵖ)ᵒᵖ} (f : A ⟶ B)
    (x : (loopGroup k H).obj A.unop.unop) (z : (loopGrassmannian k H).obj.obj A) :
    dsimp% (loopGrassmannian k H).obj.map f (x • z) =
      (loopGroup k H).map f.unop.unop x • (loopGrassmannian k H).obj.map f z :=
  (congrArg (fun t ↦ t (ULift.up x, z)) ((loopGrassmannianAction k H).naturality f)).symm

/-- Left multiplication defines an action of loops on quotient points. -/
instance instMulActionLoopGrassmannian (A : ((CommAlgCat.{u} k)ᵒᵖ)ᵒᵖ) :
    MulAction ((loopGroup k H).obj A.unop.unop) ((loopGrassmannian k H).obj.obj A) where
  one_smul z := by
    refine eq_of_forall_loopGrassmannian_map_eq_mk k H _ z fun B f g hg ↦ ?_
    simp [hg]
  mul_smul x y z := by
    refine eq_of_forall_loopGrassmannian_map_eq_mk k H _ z fun B f g hg ↦ ?_
    simp [hg, mul_assoc]

/-- The class of a loop is its translate of the base point. -/
@[simp]
theorem smul_loopGrassmannianBasePoint (A : ((CommAlgCat.{u} k)ᵒᵖ)ᵒᵖ)
    (g : (loopGroup k H).obj A.unop.unop) :
    g • loopGrassmannianBasePoint k H A = loopGrassmannianMk k H A g := by
  rw [loopGrassmannianBasePoint, smul_loopGrassmannianMk, mul_one]

/-- For the trivial affine group, every quotient section is the base point. -/
theorem loopGrassmannian_self_eq_basePoint (A : ((CommAlgCat.{u} k)ᵒᵖ)ᵒᵖ)
    (z : (loopGrassmannian k k).obj.obj A) : z = loopGrassmannianBasePoint k k A := by
  refine eq_of_forall_loopGrassmannian_map_eq_mk k k _ z fun B f g hg ↦ ?_
  rw [hg, loopGrassmannian_map_basePoint]
  exact congrArg (loopGrassmannianMk k k B) (WithConv.convPoint_eq_one g)

/-- The loop Grassmannian of the trivial group has one section over each value algebra. -/
instance instUniqueLoopGrassmannianSelf (A : ((CommAlgCat.{u} k)ᵒᵖ)ᵒᵖ) :
    Unique ((loopGrassmannian k k).obj.obj A) where
  default := loopGrassmannianBasePoint k k A
  uniq := loopGrassmannian_self_eq_basePoint k A

/-- The fpqc quotient for the trivial group is the terminal sheaf. -/
def isTerminalLoopGrassmannianSelf : Limits.IsTerminal (loopGrassmannian k k) :=
  Limits.IsTerminal.isTerminalOfObj (sheafToPresheaf _ _) _
    (Functor.isTerminal fun A ↦ (Limits.Types.isTerminalEquivUnique _).symm
      (instUniqueLoopGrassmannianSelf k A))

end

end TauCeti.HopfAlgebra

namespace CommHopfAlgCat.Hom

open TauCeti HopfAlgebra

universe u

noncomputable section

variable {k : Type u} [CommRing k] {H K L : _root_.CommHopfAlgCat.{u} k}

private def loopPresheafMap (φ : H ⟶ K) : loopPresheaf k K ⟶ loopPresheaf k H :=
  Functor.whiskerRight
    (Functor.whiskerLeft (unopUnop (CommAlgCat.{u} k))
      ((TauCeti.CommHopfAlgCat.loopGroupFunctor k).map φ.op))
    (forget GrpCat ⋙ uliftFunctor.{u + 1, u})

private theorem loopPresheafMap_app (φ : H ⟶ K) (A : ((CommAlgCat.{u} k)ᵒᵖ)ᵒᵖ)
    (g : (loopGroup k K).obj A.unop.unop) :
    (loopPresheafMap φ).app A (ULift.up g) = ULift.up
      (((TauCeti.CommHopfAlgCat.loopGroupFunctor k).map φ.op :
        loopGroup k K ⟶ loopGroup k H).app A.unop.unop g) := (rfl)

private theorem loopPresheafMap_invariant (φ : H ⟶ K) :
    IsPositiveLoopInvariant k K (loopPresheafMap φ ≫ loopGrassmannianProjection k H) := by
  intro A g n
  let α : loopGroup k K ⟶ loopGroup k H :=
    (TauCeti.CommHopfAlgCat.loopGroupFunctor k).map φ.op
  have hpos : α.app A.unop.unop ((positiveLoopToLoop k K).app A.unop.unop n) =
      (positiveLoopToLoop k H).app A.unop.unop
        (((TauCeti.CommHopfAlgCat.positiveLoopGroupFunctor k).map φ.op).app A.unop.unop n) :=
    by
      have h := congrArg (fun t ↦ t.app A.unop.unop n)
        ((TauCeti.CommHopfAlgCat.positiveLoopToLoop k).naturality φ.op)
      simp only [TauCeti.CommHopfAlgCat.positiveLoopToLoop_app] at h
      -- Evaluate the two composites after removing the inclusion's functor wrappers.
      convert h.symm using 1 <;> rfl
  have heval (x : (loopGroup k K).obj A.unop.unop) :
      (loopPresheafMap φ ≫ loopGrassmannianProjection k H).app A (ULift.up x) =
        loopGrassmannianMk k H A (α.app A.unop.unop x) :=
    congrArg ((loopGrassmannianProjection k H).app A) (loopPresheafMap_app φ A x)
  rw [heval, heval, (α.app A.unop.unop).hom.map_mul, hpos]
  exact loopGrassmannianMk_mul_positive k H A _ _

/-- A homomorphism of affine groups induces a map of loop Grassmannians.
The coordinate Hopf-algebra morphism goes in the opposite direction. -/
def loopGrassmannianMap (φ : H ⟶ K) : loopGrassmannian k K ⟶ loopGrassmannian k H :=
  (loopGrassmannianHomEquiv k K (loopGrassmannian k H)).symm
    ⟨loopPresheafMap φ ≫ loopGrassmannianProjection k H, loopPresheafMap_invariant φ⟩

/-- The induced map applies the group homomorphism to a loop representative. -/
@[simp]
theorem loopGrassmannianMap_mk (φ : H ⟶ K) (A : ((CommAlgCat.{u} k)ᵒᵖ)ᵒᵖ)
    (g : (loopGroup k K).obj A.unop.unop) :
    φ.loopGrassmannianMap.hom.app A (loopGrassmannianMk k K A g) =
      loopGrassmannianMk k H A
        (((TauCeti.CommHopfAlgCat.loopGroupFunctor k).map φ.op :
          loopGroup k K ⟶ loopGroup k H).app A.unop.unop g) := by
  exact (congrArg (fun t ↦ t.app A (ULift.up g))
    (loopGrassmannianHomEquiv_symm_apply k K (loopGrassmannian k H)
      (loopPresheafMap φ ≫ loopGrassmannianProjection k H)
      (loopPresheafMap_invariant φ))).trans
    (congrArg ((loopGrassmannianProjection k H).app A) (loopPresheafMap_app φ A g))

/-- Group homomorphisms intertwine the left actions on loop Grassmannians. -/
@[simp]
theorem loopGrassmannianMap_smul (φ : H ⟶ K) (A : ((CommAlgCat.{u} k)ᵒᵖ)ᵒᵖ)
    (x : (loopGroup k K).obj A.unop.unop) (z : (loopGrassmannian k K).obj.obj A) :
    dsimp% φ.loopGrassmannianMap.hom.app A (x • z) =
      HSMul.hSMul (α := (loopGroup k H).obj A.unop.unop) (BialgHom.mapDomain φ.hom x)
        (φ.loopGrassmannianMap.hom.app A z) := by
  let α : loopGroup k K ⟶ loopGroup k H :=
    (TauCeti.CommHopfAlgCat.loopGroupFunctor k).map φ.op
  suffices h : φ.loopGrassmannianMap.hom.app A (x • z) =
      α.app A.unop.unop x • φ.loopGrassmannianMap.hom.app A z by
    exact h.trans (congrArg (fun y : (loopGroup k H).obj A.unop.unop ↦
      y • φ.loopGrassmannianMap.hom.app A z)
      (TauCeti.CommHopfAlgCat.loopGroupFunctor_map_app_apply k φ.op A.unop.unop x))
  refine eq_of_forall_loopGrassmannian_map_eq_mk k K (loopGrassmannian k H) z
    fun B f g hg ↦ ?_
  have hnat := congrArg (fun t ↦ t x) (α.naturality f.unop.unop)
  simp only [ConcreteCategory.comp_apply] at hnat
  rw [loopGrassmannian_map_smul k H f (α.app A.unop.unop x)]
  rw [← NatTrans.naturality_apply, loopGrassmannian_map_smul k K f x, hg,
    smul_loopGrassmannianMk, loopGrassmannianMap_mk]
  rw [← NatTrans.naturality_apply, hg, loopGrassmannianMap_mk]
  exact (congrArg (loopGrassmannianMk k H B)
    (((α.app B.unop.unop).hom.map_mul _ _).trans
      (congrArg (fun y ↦ y * α.app B.unop.unop g) hnat))).trans
    (smul_loopGrassmannianMk k H B _ _).symm

/-- Group homomorphisms preserve the base point of the loop Grassmannian. -/
@[simp]
theorem loopGrassmannianMap_basePoint (φ : H ⟶ K) (A : ((CommAlgCat.{u} k)ᵒᵖ)ᵒᵖ) :
    φ.loopGrassmannianMap.hom.app A (loopGrassmannianBasePoint k K A) =
      loopGrassmannianBasePoint k H A := by
  exact (loopGrassmannianMap_mk φ A 1).trans
    (congrArg (loopGrassmannianMk k H A)
      ((((TauCeti.CommHopfAlgCat.loopGroupFunctor k).map φ.op).app A.unop.unop).hom.map_one))

/-- Maps of loop Grassmannians compose contravariantly in coordinate Hopf algebras. -/
@[simp]
theorem loopGrassmannianMap_comp (φ : H ⟶ K) (ψ : K ⟶ L) :
    loopGrassmannianMap (φ ≫ ψ) = ψ.loopGrassmannianMap ≫ φ.loopGrassmannianMap := by
  apply loopGrassmannian_hom_ext_mk
  intro A g
  let α : loopGroup k L ⟶ loopGroup k K :=
    (TauCeti.CommHopfAlgCat.loopGroupFunctor k).map ψ.op
  calc
    _ = loopGrassmannianMk k H A
        (((TauCeti.CommHopfAlgCat.loopGroupFunctor k).map (φ ≫ ψ).op).app A.unop.unop g) :=
      loopGrassmannianMap_mk (φ ≫ ψ) A g
    _ = loopGrassmannianMk k H A
        (((TauCeti.CommHopfAlgCat.loopGroupFunctor k).map φ.op).app A.unop.unop
          (α.app A.unop.unop g)) :=
      congrArg (fun β : loopGroup k L ⟶ loopGroup k H ↦
        loopGrassmannianMk k H A (β.app A.unop.unop g))
        ((TauCeti.CommHopfAlgCat.loopGroupFunctor k).map_comp ψ.op φ.op)
    _ = φ.loopGrassmannianMap.hom.app A
        (loopGrassmannianMk k K A (α.app A.unop.unop g)) :=
      (loopGrassmannianMap_mk φ A _).symm
    _ = _ := congrArg (φ.loopGrassmannianMap.hom.app A)
      (loopGrassmannianMap_mk ψ A g).symm

end

end CommHopfAlgCat.Hom

namespace CommHopfAlgCat

open TauCeti HopfAlgebra

universe u

/-- The map induced by the identity homomorphism is the identity. -/
@[simp]
theorem loopGrassmannianMap_id {k : Type u} [CommRing k] (H : CommHopfAlgCat.{u} k) :
    Hom.loopGrassmannianMap (𝟙 H) = 𝟙 (loopGrassmannian k H) := by
  apply loopGrassmannian_hom_ext_mk
  intro A g
  simp only [Hom.loopGrassmannianMap_mk, ObjectProperty.FullSubcategory.id_hom,
    NatTrans.id_app, ConcreteCategory.id_apply]
  exact congrArg (fun α : loopGroup k H ⟶ loopGroup k H ↦
    loopGrassmannianMk k H A (α.app A.unop.unop g))
    ((TauCeti.CommHopfAlgCat.loopGroupFunctor k).map_id (op H))

end CommHopfAlgCat

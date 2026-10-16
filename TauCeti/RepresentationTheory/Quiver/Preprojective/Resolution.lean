/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.ModuleCat.LengthTwo
public import TauCeti.RepresentationTheory.Quiver.Preprojective.Koszul.Complex
public import TauCeti.RepresentationTheory.Quiver.Preprojective.Sinkless
import Mathlib.Algebra.DirectSum.Module

/-!
# Projective resolutions of preprojective vertex modules

For a finite quiver `Q`, write `Π = Π_k(Q)`. The right vertex projective `e_v Π` consists of
path classes ending at `v`. Right modules are represented as left modules over `Πᵐᵒᵖ`.
This file bundles the two maps of the preprojective Koszul complex as right-module maps:

`e_v Π → ⨁_{b : i → v} e_i Π → e_v Π`,

with formulas `y ↦ (ε_b b* y)_b` and `(z_b) ↦ ∑_b b z_b`. Multiplication is
later-factor-first. The finite direct sum is implemented as a dependent function space.
The cokernel is the vertex augmentation module: the kernel of its quotient map is precisely
the positive path-degree part of `e_v Π`.

The middle exactness is valid over every commutative ring and for every finite quiver.
When every vertex of `Q` has an outgoing arrow, the first map is injective and the augmented
complex is a length-two projective resolution. The construction uses the exactness theorems in
`TauCeti.RepresentationTheory.Quiver.Preprojective.Koszul.Complex` and the injectivity theorem in
`TauCeti.RepresentationTheory.Quiver.Preprojective.Sinkless`. This is an ungraded resolution;
internal shifts and linearity are not asserted here.

## References

* P. Etingof and C.-H. Eu, *Koszulity and the Hilbert series of preprojective algebras*,
  Math. Res. Lett. 14 (2007), Sections 2 and 3.
-/

public section

namespace TauCeti

open _root_.Quiver PathAlgebra MulOpposite CategoryTheory

universe u v w

variable (k : Type w) {Q : Type u} [CommRing k] [Quiver.{v} Q] [Fintype Q]
  [∀ i j : Q, Fintype (i ⟶ j)]

local notation "Π" => preprojectiveAlgebra k Q
local notation "π" => preprojectiveMk k Q
local notation "e" => fun i : Symmetrify Q => π (vertexIdempotent k i)

/-- The right vertex projective `e_i Π`, realized inside `Π` with opposite scalars. -/
noncomputable def preprojectiveRightProjective (i : Symmetrify Q) : Submodule Πᵐᵒᵖ Π :=
  LinearMap.range (LinearMap.mulLeft Πᵐᵒᵖ (e i))

/-- A path class belongs to `e_i Π` exactly when left multiplication by `e_i` fixes it. -/
@[simp]
theorem mem_preprojectiveRightProjective_iff (i : Symmetrify Q) (x : Π) :
    x ∈ preprojectiveRightProjective k i ↔ e i * x = x := by
  have he : e i * e i = e i := by rw [← map_mul, vertexIdempotent_mul_self]
  constructor
  · rintro ⟨y, rfl⟩
    simp only [LinearMap.mulLeft_apply, ← mul_assoc, he]
  · intro hx
    exact ⟨x, hx⟩

/-- Each right vertex ideal is projective, since multiplication by its idempotent splits its
inclusion in the regular right module. -/
instance (i : Symmetrify Q) : Module.Projective Πᵐᵒᵖ (preprojectiveRightProjective k i) := by
  let : Module.Projective Πᵐᵒᵖ Π :=
    Module.Projective.of_equiv (MulOpposite.opLinearEquiv Πᵐᵒᵖ (M := Π)).symm
  refine Module.Projective.of_split (preprojectiveRightProjective k i).subtype
    (LinearMap.mulLeft Πᵐᵒᵖ (e i)).rangeRestrict ?_
  ext x
  exact (mem_preprojectiveRightProjective_iff k i x).1 x.property

/-- The middle projective of the Koszul complex at `v`, indexed by doubled arrows into `v`. -/
abbrev preprojectiveKoszulMiddle (v : Q) :=
  (i : Symmetrify Q) → (i ⟶ Symmetrify.of.obj v) → preprojectiveRightProjective k i

/-- The middle Koszul term is projective as a finite direct sum of right vertex projectives,
represented by a dependent function space. -/
instance (v : Q) : Module.Projective Πᵐᵒᵖ (preprojectiveKoszulMiddle k v) := by
  let (i : Symmetrify Q) :
      Module.Projective Πᵐᵒᵖ ((i ⟶ Symmetrify.of.obj v) → preprojectiveRightProjective k i) :=
    Module.Projective.of_equiv (DirectSum.linearEquivFunOnFintype Πᵐᵒᵖ _ _)
  exact Module.Projective.of_equiv (DirectSum.linearEquivFunOnFintype Πᵐᵒᵖ _ _)

private theorem arrow_mul_mem_rightProjective {i j : Symmetrify Q} (b : i ⟶ j) (x : Π) :
    π (ofArrow b) * x ∈ preprojectiveRightProjective k j := by
  classical
  rw [mem_preprojectiveRightProjective_iff, ← mul_assoc, ← map_mul,
    vertexIdempotent_mul_ofArrow, ite_eq_left rfl]

/-- The first Koszul differential, `y ↦ (ε_b b* y)_b`. -/
noncomputable def preprojectiveKoszulLeft (v : Q) :
    preprojectiveRightProjective k (Symmetrify.of.obj v) →ₗ[Πᵐᵒᵖ]
      preprojectiveKoszulMiddle k v where
  toFun y i b := ⟨doubledArrowSign k b • (π (ofArrow (Quiver.reverse b)) * y), by
    rw [mem_preprojectiveRightProjective_iff, mul_smul_comm]
    exact congrArg (doubledArrowSign k b • ·)
      ((mem_preprojectiveRightProjective_iff k i _).1
        (arrow_mul_mem_rightProjective k (Quiver.reverse b) y))⟩
  map_add' x y := by ext i b; simp [mul_add, smul_add]
  map_smul' a y := by
    ext i b
    simp [MulOpposite.smul_eq_mul_unop, mul_assoc]

/-- The second Koszul differential, `(z_b) ↦ ∑_b b z_b`. -/
noncomputable def preprojectiveKoszulRight (v : Q) :
    preprojectiveKoszulMiddle k v →ₗ[Πᵐᵒᵖ]
      preprojectiveRightProjective k (Symmetrify.of.obj v) where
  toFun z := ⟨∑ i, ∑ b : i ⟶ Symmetrify.of.obj v, π (ofArrow b) * z i b,
    Submodule.sum_mem _ fun i _ => Submodule.sum_mem _ fun b _ =>
      arrow_mul_mem_rightProjective k b (z i b)⟩
  map_add' x y := by ext; simp [mul_add, Finset.sum_add_distrib]
  map_smul' a y := by
    ext
    simp [MulOpposite.smul_eq_mul_unop, mul_assoc, Finset.sum_mul]

@[simp]
theorem coe_preprojectiveKoszulLeft_apply (v : Q)
    (y : preprojectiveRightProjective k (Symmetrify.of.obj v)) (i : Symmetrify Q)
    (b : i ⟶ Symmetrify.of.obj v) :
    (preprojectiveKoszulLeft k v y i b : Π) =
      doubledArrowSign k b • (π (ofArrow (Quiver.reverse b)) * y) := (rfl)

@[simp]
theorem coe_preprojectiveKoszulRight_apply (v : Q) (z : preprojectiveKoszulMiddle k v) :
    (preprojectiveKoszulRight k v z : Π) =
      ∑ i, ∑ b : i ⟶ Symmetrify.of.obj v, π (ofArrow b) * z i b := (rfl)

/-- The Koszul differentials compose to zero by the local preprojective relation. -/
@[simp]
theorem preprojectiveKoszulRight_comp_left (v : Q) :
    (preprojectiveKoszulRight k v).comp (preprojectiveKoszulLeft k v) = 0 := by
  ext y
  exact sum_preprojectiveMk_ofArrow_mul_doubledArrowSign_smul_eq_zero k v y

/-- Exactness at the middle projective, with no restriction on the quiver. -/
theorem range_preprojectiveKoszulLeft_eq_ker_right (v : Q) :
    LinearMap.range (preprojectiveKoszulLeft k v) =
      LinearMap.ker (preprojectiveKoszulRight k v) := by
  ext z
  rw [LinearMap.mem_range, LinearMap.mem_ker]
  constructor
  · rintro ⟨y, rfl⟩
    exact LinearMap.congr_fun (preprojectiveKoszulRight_comp_left k v) y
  · intro hz
    have hz' : ∑ i, ∑ b : i ⟶ Symmetrify.of.obj v, π (ofArrow b) * (z i b : Π) = 0 :=
      congrArg Subtype.val hz
    obtain ⟨y, hy, hzy⟩ := (sum_preprojectiveMk_ofArrow_mul_eq_zero_iff k v
      (fun i b => (mem_preprojectiveRightProjective_iff k i _).1 (z i b).property)).1 hz'
    rw [doubledVertexIdempotent_def] at hy
    exact ⟨⟨y, (mem_preprojectiveRightProjective_iff k _ _).2 hy⟩,
      funext fun i => funext fun b => Subtype.ext (hzy i b).symm⟩

/-- The vertex augmentation module, the cokernel of the incoming-arrow map on `e_v Π`.
Its quotient kernel is precisely the positive path-degree part. -/
abbrev preprojectiveVertexModule (v : Q) :=
  preprojectiveRightProjective k (Symmetrify.of.obj v) ⧸
    LinearMap.range (preprojectiveKoszulRight k v)

/-- The augmentation from the vertex projective to its vertex module. -/
noncomputable def preprojectiveVertexAugmentation (v : Q) :
    preprojectiveRightProjective k (Symmetrify.of.obj v) →ₗ[Πᵐᵒᵖ]
      preprojectiveVertexModule k v :=
  (LinearMap.range (preprojectiveKoszulRight k v)).mkQ

/-- The vertex augmentation sends each element to its quotient class. -/
theorem preprojectiveVertexAugmentation_apply (v : Q)
    (x : preprojectiveRightProjective k (Symmetrify.of.obj v)) :
    preprojectiveVertexAugmentation k v x = Submodule.Quotient.mk x := (rfl)

/-- The augmentation kills exactly the elements of positive path degree. -/
@[simp]
theorem preprojectiveVertexAugmentation_eq_zero_iff (v : Q)
    (x : preprojectiveRightProjective k (Symmetrify.of.obj v)) :
    preprojectiveVertexAugmentation k v x = 0 ↔ (x : Π) ∈ ⨆ n, preprojectiveGrade k Q (n + 1) := by
  rw [preprojectiveVertexAugmentation, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero,
    LinearMap.mem_range]
  have hx : π (doubledVertexIdempotent k v) * (x : Π) = x := by
    simpa only [doubledVertexIdempotent_def] using
      (mem_preprojectiveRightProjective_iff k _ _).1 x.property
  rw [mem_iSup_preprojectiveGrade_add_one_iff_exists_eq_sum k v hx]
  constructor
  · rintro ⟨z, rfl⟩
    exact ⟨fun i b => z i b, fun i b =>
      (mem_preprojectiveRightProjective_iff k i _).1 (z i b).property, rfl⟩
  · rintro ⟨z, hz, hxz⟩
    exact ⟨fun i b => ⟨z i b, (mem_preprojectiveRightProjective_iff k i _).2 (hz i b)⟩,
      Subtype.ext hxz.symm⟩

/-- The vertex augmentation kernel is the range of the incoming-arrow differential. -/
@[simp]
theorem ker_preprojectiveVertexAugmentation (v : Q) :
    LinearMap.ker (preprojectiveVertexAugmentation k v) =
      LinearMap.range (preprojectiveKoszulRight k v) :=
  Submodule.ker_mkQ _

/-- The vertex augmentation is surjective. -/
theorem preprojectiveVertexAugmentation_surjective (v : Q) :
    Function.Surjective (preprojectiveVertexAugmentation k v) :=
  Submodule.mkQ_surjective _

/-- The left Koszul differential is injective exactly when no nonzero element of `e_v Π`
is annihilated by every doubled arrow leaving `v`. The signs in the differential are units,
including in characteristic two. -/
theorem preprojectiveKoszulLeft_injective_iff (v : Q) :
    Function.Injective (preprojectiveKoszulLeft k v) ↔
      ∀ y : Π, π (doubledVertexIdempotent k v) * y = y →
        (∀ (i : Symmetrify Q) (b : i ⟶ Symmetrify.of.obj v),
          π (ofArrow (Quiver.reverse b)) * y = 0) → y = 0 := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  constructor
  · intro h y hy hb
    have hy' : y ∈ preprojectiveRightProjective k (Symmetrify.of.obj v) := by
      rw [doubledVertexIdempotent_def] at hy
      exact (mem_preprojectiveRightProjective_iff k _ y).2 hy
    have hz : preprojectiveKoszulLeft k v ⟨y, hy'⟩ = 0 := by
      ext i b
      simp only [coe_preprojectiveKoszulLeft_apply, hb, smul_zero,
        Pi.zero_apply, Submodule.coe_zero]
    exact congrArg Subtype.val (h ⟨y, hy'⟩ hz)
  · intro h y hy
    apply Subtype.ext
    have hv : π (doubledVertexIdempotent k v) * (y : Π) = y := by
      simpa only [doubledVertexIdempotent_def] using
        (mem_preprojectiveRightProjective_iff k _ _).1 y.property
    apply h y hv
    intro i b
    have hb : doubledArrowSign k b • (π (ofArrow (Quiver.reverse b)) * (y : Π)) = 0 :=
      congrArg (fun z => (z i b : Π)) hy
    have hh := congrArg (doubledArrowSign k b • ·) hb
    simpa only [smul_smul, doubledArrowSign_mul_self, one_smul, smul_zero] using hh

/-- For a quiver without sinks, the left Koszul differential is injective. -/
theorem preprojectiveKoszulLeft_injective (hQ : ∀ u : Q, ∃ w, Nonempty (u ⟶ w)) (v : Q) :
    Function.Injective (preprojectiveKoszulLeft k v) :=
  (preprojectiveKoszulLeft_injective_iff k v).2 fun _ hy =>
    (forall_preprojectiveMk_ofArrow_reverse_mul_eq_zero_iff k hQ v hy).1

/-! ### The augmented chain complex -/

/-- The right-module Koszul chain complex, supported in degrees zero, one and two.
Its term identifications and differential formulas are those of `ModuleCatLengthTwo.complex`. -/
noncomputable def preprojectiveKoszulComplex (v : Q) :
    ChainComplex (ModuleCat.{max u v w} Πᵐᵒᵖ) ℕ :=
  ModuleCatLengthTwo.complex (preprojectiveKoszulLeft k v) (preprojectiveKoszulRight k v)
    (preprojectiveKoszulRight_comp_left k v)

/-- The Koszul complex is the common three-term construction on the Koszul maps. -/
@[simp]
theorem preprojectiveKoszulComplex_def (v : Q) :
    preprojectiveKoszulComplex k v =
      ModuleCatLengthTwo.complex (preprojectiveKoszulLeft k v)
        (preprojectiveKoszulRight k v) (preprojectiveKoszulRight_comp_left k v) := (rfl)

/-- The vertex module of a quiver without sinks has a projective resolution supported in
homological degrees zero, one and two, with the Koszul maps as differentials. This is a
resolution over the opposite algebra, hence of right preprojective modules.
The term identifications and augmentation formula are supplied by
`ModuleCatLengthTwo.projectiveResolutionXIso` and
`ModuleCatLengthTwo.projectiveResolution_π_f_zero`. -/
noncomputable def preprojectiveKoszulProjectiveResolution
    (hQ : ∀ u : Q, ∃ w, Nonempty (u ⟶ w)) (v : Q) :
    ProjectiveResolution (ModuleCat.of Πᵐᵒᵖ (preprojectiveVertexModule k v)) :=
  ModuleCatLengthTwo.projectiveResolution (preprojectiveKoszulLeft k v)
    (preprojectiveKoszulRight k v)
    (range_preprojectiveKoszulLeft_eq_ker_right k v)
    (preprojectiveKoszulLeft_injective k hQ v)

/-- The vertex resolution is the common length-two construction on the Koszul maps. -/
@[simp]
theorem preprojectiveKoszulProjectiveResolution_def
    (hQ : ∀ u : Q, ∃ w, Nonempty (u ⟶ w)) (v : Q) :
    preprojectiveKoszulProjectiveResolution k hQ v =
      ModuleCatLengthTwo.projectiveResolution (preprojectiveKoszulLeft k v)
        (preprojectiveKoszulRight k v) (range_preprojectiveKoszulLeft_eq_ker_right k v)
        (preprojectiveKoszulLeft_injective k hQ v) := (rfl)

end TauCeti

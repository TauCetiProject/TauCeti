/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.CategoryTheory.Monoidal.Rigid.Basic
public import Mathlib.Data.Int.Order.Units
public import TauCeti.CategoryTheory.Dagger.Monoidal
public import TauCeti.CategoryTheory.Monoidal.Preadditive
public import TauCeti.CategoryTheory.Preadditive.Schur
import TauCeti.CategoryTheory.Monoidal.Rigid.Simple

/-!
# Signed self-dual cups

A cup `R : 𝟙_ C ⟶ X ⊗ X` has zigzag sign `s : ℤˣ` if inserting it to the right of `X`
and contracting the first two factors against its adjoint acts as `s` on `X`. Taking daggers
gives the other zigzag. Thus `R` and `s • dagger R` are the coevaluation and evaluation of
a native `ExactPairing X X`. Its closed loop is the signed multiple of `R ≫ dagger R`.

The sign is preserved by unitary changes of object and by additive dagger functors
with unitary monoidal constraints. The functor transport applies the unit and tensor
comparisons to the signed zigzag, as in `Functor.mapExactPairing` for an exact pairing.

Given one signed cup on a nonzero object with scalar endomorphisms, every other
signed cup has its sign and differs from it by a norm-one scalar. In particular,
over ℂ the sign is an invariant of a simple self-dual object with finite-dimensional
endomorphisms in a category with kernels.

## References

* S. Neshveyev and L. Tuset, *Compact Quantum Groups and Their Representation Categories*,
  §2.5. Our sign is the scalar in the zigzag equation, the negative of their sign parameter.
-/

public section

open CategoryTheory MonoidalCategory Functor.LaxMonoidal Functor.OplaxMonoidal

universe v w u u'

namespace TauCeti

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [Preadditive C] [DaggerCategory C]

/-- The cup `R` has zigzag sign `s` when `(R† ⊗ 1)(1 ⊗ R) = s 1`, with the
associator and unitors inserted. The two signs are the units of the integers. -/
def IsSignedCup {X : C} (s : ℤˣ) (R : 𝟙_ C ⟶ X ⊗ X) : Prop :=
  X ◁ R ≫ (α_ X X X).inv ≫ dagger R ▷ X = (s : ℤ) • ((ρ_ X).hom ≫ (λ_ X).inv)

variable {X Y : C} {s : ℤˣ} {R : 𝟙_ C ⟶ X ⊗ X}

/-- A cup has sign `s` exactly when its contraction on the right is the signed unitor composite. -/
theorem isSignedCup_iff :
    IsSignedCup s R ↔
      X ◁ R ≫ (α_ X X X).inv ≫ dagger R ▷ X = (s : ℤ) • ((ρ_ X).hom ≫ (λ_ X).inv) :=
  Iff.rfl

namespace IsSignedCup

/-- The signed contraction with the cup on the right. -/
@[reassoc] theorem whiskerLeft_comp (h : IsSignedCup s R) :
    X ◁ R ≫ (α_ X X X).inv ≫ dagger R ▷ X = (s : ℤ) • ((ρ_ X).hom ≫ (λ_ X).inv) :=
  isSignedCup_iff.mp h

variable [DaggerMonoidalCategory C]

/-- The canonical self-duality of the tensor unit has positive sign. -/
@[simp] theorem rightUnitor_inv_tensorUnit : IsSignedCup (1 : ℤˣ) (ρ_ (𝟙_ C)).inv := by
  simpa [isSignedCup_iff] using ExactPairing.coevaluation_evaluation (𝟙_ C) (𝟙_ C)

variable [DaggerPreadditive C]

/-- The contraction with the cup on the left has the same sign. -/
@[reassoc] theorem whiskerRight_comp (h : IsSignedCup s R) :
    R ▷ X ≫ (α_ X X X).hom ≫ X ◁ dagger R = (s : ℤ) • ((λ_ X).hom ≫ (ρ_ X).inv) := by
  simpa [Category.assoc] using congrArg dagger h.whiskerLeft_comp

variable [MonoidalPreadditive C]

/-- A signed self-duality with coevaluation `R` and evaluation `s • dagger R`. -/
@[instance_reducible]
def exactPairing (h : IsSignedCup s R) : ExactPairing X X where
  coevaluation' := R
  evaluation' := (s : ℤ) • dagger R
  coevaluation_evaluation' := by
    simp [h.whiskerLeft_comp, smul_smul, Int.units_coe_mul_self]
  evaluation_coevaluation' := by
    simp [h.whiskerRight_comp, smul_smul, Int.units_coe_mul_self]

/-- The coevaluation of the pairing from a signed cup is the cup itself. -/
@[simp] theorem exactPairing_coevaluation (h : IsSignedCup s R) :
    @ExactPairing.coevaluation C _ _ X X h.exactPairing = R := (rfl)

/-- The evaluation of the pairing from a signed cup is its signed adjoint. -/
@[simp] theorem exactPairing_evaluation (h : IsSignedCup s R) :
    @ExactPairing.evaluation C _ _ X X h.exactPairing = (s : ℤ) • dagger R := (rfl)

omit [DaggerMonoidalCategory C] [DaggerPreadditive C] in
/-- For an existing self-pairing with cup `R`, the sign is `s` exactly when its evaluation
is the signed adjoint of `R`. -/
theorem iff_evaluation_eq [P : ExactPairing X X] (hη : η_ X X = R) :
    IsSignedCup s R ↔ ε_ X X = (s : ℤ) • dagger R := by
  subst R
  constructor
  · intro h
    apply (tensorRightHomEquiv X X X (𝟙_ C)).injective
    simp [tensorRightHomEquiv, h.whiskerLeft_comp, smul_smul]
  · intro hε
    have h := ExactPairing.coevaluation_evaluation X X
    rw [hε, zsmul_whiskerRight, Preadditive.comp_zsmul, Preadditive.comp_zsmul] at h
    simpa only [isSignedCup_iff, smul_smul, Int.units_coe_mul_self, one_smul] using
      congrArg ((s : ℤ) • ·) h

omit [DaggerPreadditive C] [MonoidalPreadditive C] in
/-- Transporting both legs along a unitary isomorphism preserves the signed cup equation. -/
theorem unitary_congr (h : IsSignedCup s R) (e : X ≅ Y) (he : IsUnitary e.hom) :
    IsSignedCup s (R ≫ (e.hom ⊗ₘ e.hom)) := by
  have cup : e.hom ▷ (𝟙_ C) ≫ Y ◁ (R ≫ (e.hom ⊗ₘ e.hom)) =
      X ◁ R ≫ (e.hom ⊗ₘ (e.hom ⊗ₘ e.hom)) := by
    rw [← tensorHom_def, whiskerLeft_comp_tensorHom]
  have cap : ((e.hom ⊗ₘ e.hom) ⊗ₘ e.hom) ≫ dagger (R ≫ (e.hom ⊗ₘ e.hom)) ▷ Y =
      dagger R ▷ X ≫ (𝟙_ C) ◁ e.hom := by
    rw [tensorHom_comp_whiskerRight, ← tensorHom_def, dagger_comp, dagger_tensorHom,
      e.dagger_hom_eq_inv_of_isUnitary he]
    simp
  rw [isSignedCup_iff, ← cancel_epi (e.hom ▷ (𝟙_ C)), reassoc_of% cup,
    associator_inv_naturality_assoc, cap, h.whiskerLeft_comp_assoc]
  simp

variable {D : Type u'} [Category.{w} D] [MonoidalCategory D] [Preadditive D] [DaggerCategory D]

open Functor.Monoidal in
omit [DaggerMonoidalCategory C] [DaggerPreadditive C] [MonoidalPreadditive C] in
/-- An additive dagger functor with unitary monoidal constraints preserves the sign of a
self-dual cup. The unit and tensor comparisons identify its source and target. -/
theorem map (h : IsSignedCup s R) (F : C ⥤ D) [F.Monoidal] [F.Additive]
    [F.PreservesDagger] [F.IsUnitaryMonoidal] :
    IsSignedCup s (ε F ≫ F.map R ≫ δ F X X) := by
  apply isSignedCup_iff.mpr
  let transport (f : X ⊗ 𝟙_ C ⟶ (𝟙_ C) ⊗ X) :=
    F.obj X ◁ ε F ≫ μ F X (𝟙_ C) ≫ F.map f ≫ δ F (𝟙_ C) X ≫ η F ▷ F.obj X
  have hm := congrArg transport h.whiskerLeft_comp
  simp only [transport, Functor.map_zsmul, Functor.map_comp, map_whiskerLeft, map_associator_inv,
    map_whiskerRight, map_rightUnitor, map_leftUnitor_inv, Preadditive.zsmul_comp,
    Preadditive.comp_zsmul, Category.assoc, μ_δ_assoc] at hm
  simpa [Category.assoc] using hm

section Scalar

variable {𝕜 : Type*} [RCLike 𝕜] [Linear 𝕜 C] [MonoidalLinear 𝕜 C] [DaggerLinear 𝕜 C]
  {t : ℤˣ}

omit [DaggerMonoidalCategory C] [DaggerPreadditive C] in
/-- On a nonzero object, rescaling a signed cup gives a signed cup exactly for scalars
of norm one, and the sign is unchanged. -/
theorem smul_iff (h : IsSignedCup s R) (hX : ¬ Limits.IsZero X) (c : 𝕜) :
    IsSignedCup t (c • R) ↔ ‖c‖ = 1 ∧ s = t := by
  let u := (ρ_ X).hom ≫ (λ_ X).inv
  have hu : u ≠ 0 := by
    intro hz
    exact hX ((Limits.IsZero.iff_id_eq_zero X).2
      (by simpa [u] using (ρ_ X).inv ≫= hz =≫ (λ_ X).hom))
  have hst : IsSignedCup t (c • R) ↔
      star c * c * ((s : ℤ) : 𝕜) = ((t : ℤ) : 𝕜) := by
    rw [isSignedCup_iff, dagger_smul]
    simp only [MonoidalLinear.whiskerLeft_smul, MonoidalLinear.smul_whiskerRight,
      Linear.comp_smul, Linear.smul_comp, h.whiskerLeft_comp, ← Int.cast_smul_eq_zsmul 𝕜,
      smul_smul, ← mul_assoc]
    exact (smul_left_injective 𝕜 hu).eq_iff
  rw [hst]
  constructor
  · intro heq
    have hn (v : ℤˣ) : ‖((v : ℤ) : 𝕜)‖ = 1 := by
      rcases Int.units_eq_one_or v with hv | hv <;> simp [hv]
    have hnorm : ‖c‖ * ‖c‖ = 1 := by
      simpa only [norm_mul, norm_star, hn, mul_one] using congrArg norm heq
    have hc : ‖c‖ = 1 := by nlinarith [norm_nonneg c]
    have he : ((s : ℤ) : 𝕜) = ((t : ℤ) : 𝕜) := by
      simpa [RCLike.star_def, RCLike.conj_mul, hc] using heq
    exact ⟨hc, Units.ext (Int.cast_injective he)⟩
  · rintro ⟨hc, rfl⟩
    simp [RCLike.star_def, RCLike.conj_mul, hc]

/-- On a nonzero object with scalar endomorphisms, the signed cups are exactly the norm-one
scalar multiples of any one signed cup, all with its sign. -/
theorem iff_of_surjective_algebraMap (hR : IsSignedCup s R) {S : 𝟙_ C ⟶ X ⊗ X}
    (hX : ¬ Limits.IsZero X)
    (hEnd : Function.Surjective (algebraMap 𝕜 (End X))) :
    IsSignedCup t S ↔ s = t ∧ ∃ c : 𝕜, ‖c‖ = 1 ∧ S = c • R := by
  refine ⟨fun hS ↦ ?_, ?_⟩
  · let := hR.exactPairing
    obtain ⟨b, hb⟩ := hom_tensorUnit_eq_smul_evaluation_of_surjective_right hEnd (dagger S)
    have hSR : S = star (b * ((s : ℤ) : 𝕜)) • R := by
      simpa only [exactPairing_evaluation, dagger_smul, dagger_zsmul, dagger_dagger,
        ← Int.cast_smul_eq_zsmul 𝕜, smul_smul] using congrArg dagger hb
    rw [hSR] at hS
    obtain ⟨hc, hst⟩ := (hR.smul_iff hX _).mp hS
    exact ⟨hst, _, hc, hSR⟩
  · rintro ⟨rfl, c, hc, rfl⟩
    exact (hR.smul_iff hX c).2 ⟨hc, rfl⟩

end Scalar

/-- The zigzag sign of a simple self-dual object with finite-dimensional endomorphisms over an
algebraically closed scalar field is independent of the choice of cup. -/
theorem sign_eq_of_simple (𝕜 : Type*) [RCLike 𝕜] [IsAlgClosed 𝕜] [Linear 𝕜 C]
    [MonoidalLinear 𝕜 C] [DaggerLinear 𝕜 C] [Limits.HasKernels C] [Simple X]
    [FiniteDimensional 𝕜 (X ⟶ X)] (hR : IsSignedCup s R) {t : ℤˣ} {S : 𝟙_ C ⟶ X ⊗ X}
    (hS : IsSignedCup t S) : s = t :=
  ((hR.iff_of_surjective_algebraMap (Simple.not_isZero X)
    (bijective_algebraMap_end_of_simple 𝕜 X).surjective).1 hS).1

end IsSignedCup

end TauCeti

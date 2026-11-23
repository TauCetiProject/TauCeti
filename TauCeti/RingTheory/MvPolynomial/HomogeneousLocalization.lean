/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Jie Xu, Shitan Xu
-/
module

public import TauCeti.RingTheory.GradedAlgebra.HomogeneousLocalization.Basic
public import TauCeti.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.RingTheory.MvPolynomial.Ideal

/-!
# Normalized coordinates on polynomial projective charts

The degree-zero localization of `R[Xᵢ]` at a variable is generated over `R` by the fractions
`Xⱼ / Xᵢ`. This description holds for arbitrary coordinate sets. For a singleton coordinate
set the chart is the coefficient ring itself. These computations describe the affine
charts used by the Segre embedding.
-/

public section

open HomogeneousLocalization

namespace TauCeti.MvPolynomial

open _root_.MvPolynomial

attribute [local instance] _root_.MvPolynomial.gradedAlgebra

variable {R σ : Type*} [CommRing R]

/-- The normalized coordinate `Xⱼ / Xᵢ` on the standard projective chart `D₊(Xᵢ)`. -/
noncomputable def awayXRatio (i j : σ) :
    Away (homogeneousSubmodule σ R) (X i) :=
  Away.mk _ ((mem_homogeneousSubmodule _ _).mpr (isHomogeneous_X R i)) 1 (X j)
    ((mem_homogeneousSubmodule _ _).mpr (by simpa using isHomogeneous_X R j))

/-- The normalized coordinate is the homogeneous fraction with numerator `Xⱼ`
and denominator `Xᵢ`. -/
theorem awayXRatio_def (i j : σ) :
    awayXRatio (R := R) i j =
      Away.mk _ ((mem_homogeneousSubmodule _ _).mpr (isHomogeneous_X R i)) 1 (X j)
        ((mem_homogeneousSubmodule _ _).mpr (by simpa using isHomogeneous_X R j)) := by rfl

/-- Localization of a degree-one coordinate is the corresponding normalized coordinate. -/
@[simp]
theorem isLocalizationElem_X (i k : σ) :
    Away.isLocalizationElem ((mem_homogeneousSubmodule _ _).mpr (isHomogeneous_X R i))
      ((mem_homogeneousSubmodule _ _).mpr (isHomogeneous_X R k)) =
      awayXRatio (R := R) i k := by
  apply val_injective
  simp only [Away.isLocalizationElem, awayXRatio_def, Away.val_mk, pow_one]

/-- The denominator coordinate is one on its standard chart. -/
@[simp]
theorem awayXRatio_self (i : σ) : awayXRatio (R := R) i i = 1 :=
  by
    rw [awayXRatio_def]
    apply HomogeneousLocalization.val_injective
    rw [HomogeneousLocalization.val_one]
    -- Compare fractions in the full localization; the degree-zero inclusion is injective.
    change Localization.mk (X i)
      (⟨(X i) ^ 1, by use 1⟩ : Submonoid.powers (X i : MvPolynomial σ R)) = 1
    simp only [pow_one, Localization.mk_self_mk]

/-- The normalized coordinate maps to `Xᵢ⁻¹ Xⱼ` in the full localization. -/
theorem val_awayXRatio (i j : σ) :
    algebraMap (Away (homogeneousSubmodule σ R) (X i))
        (Localization.Away (X i : MvPolynomial σ R)) (awayXRatio i j) =
      IsLocalization.Away.invSelf (X i : MvPolynomial σ R) *
        algebraMap (MvPolynomial σ R) (Localization.Away (X i : MvPolynomial σ R)) (X j) := by
  rw [awayXRatio_def, HomogeneousLocalization.algebraMap_apply]
  -- The inclusion sends a homogeneous fraction to the same fraction in the full localization.
  change Localization.mk (X j)
    (⟨(X i) ^ 1, by use 1⟩ : Submonoid.powers (X i : MvPolynomial σ R)) = _
  simp [IsLocalization.Away.invSelf, ← Localization.mk_eq_mk',
    ← Localization.mk_one_eq_algebraMap, Localization.mk_mul]

end TauCeti.MvPolynomial

namespace MvPolynomial.IsHomogeneous

open TauCeti.MvPolynomial

attribute [local instance] MvPolynomial.gradedAlgebra

variable {R σ : Type*} [CommRing R]

/-- A homogeneous polynomial evaluated at normalized coordinates is its
homogeneous fraction with the corresponding power of `Xᵢ` as denominator. -/
theorem aeval_awayXRatio {n : ℕ} {p : MvPolynomial σ R}
    (hp : p.IsHomogeneous n) (i : σ) :
    MvPolynomial.aeval (awayXRatio (R := R) i) p =
      Away.mk _ ((mem_homogeneousSubmodule _ _).mpr (isHomogeneous_X R i)) n p (by simpa using
        hp) := by
  apply HomogeneousLocalization.val_injective
  let L := Localization.Away (X i : MvPolynomial σ R)
  let φ : MvPolynomial σ R →+* L := algebraMap _ _
  let c : L := IsLocalization.Away.invSelf (X i : MvPolynomial σ R)
  have hcomp :
      (algebraMap (Away (homogeneousSubmodule σ R) (X i)) L).comp
          (MvPolynomial.aeval (awayXRatio (R := R) i)).toRingHom =
        MvPolynomial.eval₂Hom (φ.comp (C : R →+* MvPolynomial σ R)) (fun j ↦ c * φ (X j)) := by
    apply ringHom_ext
    · intro r
      simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
        aeval_C, eval₂Hom_C]
      rw [HomogeneousLocalization.algebraMap_apply]
      exact (HomogeneousLocalization.val_algebraMap (homogeneousSubmodule σ R)
        (Submonoid.powers (X i)) r).trans
          (IsScalarTower.algebraMap_apply R (MvPolynomial σ R) L r)
    · intro j
      simpa only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
        aeval_X, eval₂Hom_X'] using val_awayXRatio (R := R) i j
  have heval : MvPolynomial.eval₂Hom (φ.comp (C : R →+* MvPolynomial σ R))
      (fun j : σ ↦ φ (X j)) = φ := by
    apply ringHom_ext <;> simp
  -- Express evaluation as composition before applying the polynomial homomorphism identity.
  change ((algebraMap (Away (homogeneousSubmodule σ R) (X i)) L).comp
    (MvPolynomial.aeval (awayXRatio (R := R) i)).toRingHom) p = _
  rw [hcomp]
  -- The homogeneous scaling law is stated for eval₂ rather than its bundled homomorphism.
  change MvPolynomial.eval₂ (φ.comp C) (fun j ↦ c * φ (X j)) p = _
  rw [hp.eval₂_const_mul]
  -- Bundle the remaining evaluation so that the homomorphism identity heval applies.
  change c ^ n * MvPolynomial.eval₂Hom (φ.comp C) (fun j ↦ φ (X j)) p = _
  rw [heval]
  dsimp only [c, φ, L]
  rw [IsLocalization.Away.invSelf, ← Localization.mk_eq_mk',
    ← Localization.mk_one_eq_algebraMap, Localization.mk_pow, Localization.mk_mul]
  simp only [one_pow, one_mul]
  -- Both denominators have the same value; only their subtype membership proofs differ.
  change Localization.mk p _ = Localization.mk p _
  congr 1
  exact Subtype.ext (by simp)

end MvPolynomial.IsHomogeneous

namespace TauCeti.MvPolynomial

open _root_.MvPolynomial

attribute [local instance] _root_.MvPolynomial.gradedAlgebra

variable {R σ : Type*} [CommRing R]

/-- Normalized coordinates generate the standard chart over the coefficient ring. -/
theorem adjoin_range_awayXRatio (i : σ) :
    Algebra.adjoin R (Set.range (awayXRatio (R := R) i)) = ⊤ := by
  apply top_unique
  intro z _
  obtain ⟨n, p, hp, rfl⟩ := Away.mk_surjective _ ((mem_homogeneousSubmodule _ _).mpr
    (isHomogeneous_X R i)) z
  have hpn : p.IsHomogeneous n := by simpa using hp
  rw [← hpn.aeval_awayXRatio i]
  rw [Algebra.adjoin_range_eq_range_aeval]
  exact ⟨p, rfl⟩

end TauCeti.MvPolynomial

namespace MvPolynomial

attribute [local instance] gradedAlgebra

/-- The variables generate the irrelevant ideal for total-degree grading. -/
theorem irrelevant_eq_span_X (σ R : Type*) [CommRing R] :
    (HomogeneousIdeal.irrelevant (homogeneousSubmodule σ R)).toIdeal =
      Ideal.span (Set.range (X : σ → MvPolynomial σ R)) := by
  have h1 : Ideal.span (Set.range (X : σ → MvPolynomial σ R)) = idealOfVars σ R ^ 1 :=
    (pow_one _).symm
  ext p
  rw [h1, mem_pow_idealOfVars_iff']
  simp only [HomogeneousIdeal.toIdeal_irrelevant, RingHom.mem_ker,
    GradedRing.projZeroRingHom_apply]
  -- Identify the graded decomposition projection with the polynomial homogeneous component.
  rw [show ((DirectSum.decompose (homogeneousSubmodule σ R) p 0 :
      homogeneousSubmodule σ R 0) : MvPolynomial σ R) = homogeneousComponent 0 p from
      decomposition.decompose'_apply p 0, homogeneousComponent_zero, C_eq_zero]
  refine ⟨fun h d hd ↦ ?_, fun h ↦ h 0 (by simp)⟩
  obtain rfl : d = 0 := by
    simpa [Nat.lt_one_iff, Finsupp.degree_eq_zero_iff] using hd
  exact h

end MvPolynomial

namespace RingHom

open MvPolynomial TauCeti.MvPolynomial

attribute [local instance] _root_.MvPolynomial.gradedAlgebra

variable {R B σ : Type*} [CommRing R] [CommRing B]

/-- When `Xᵢ` maps to one, evaluation at normalized coordinates followed
by the degree-zero localization map recovers the original polynomial homomorphism. -/
theorem lift_comp_aeval_awayXRatio (φ : MvPolynomial σ R →+* B) (i : σ)
    (h : φ (X i) = 1) :
    (Away.lift (homogeneousSubmodule σ R) φ (h ▸ isUnit_one)).comp
      (aeval (awayXRatio (R := R) i)).toRingHom = φ := by
  have hu : (h ▸ isUnit_one : IsUnit (φ (X i))).unit = 1 :=
    Units.ext (((h ▸ isUnit_one : IsUnit (φ (X i))).unit_spec).trans h)
  apply ringHom_ext
  · intro r
    simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, aeval_C]
    -- The localization scalar law uses degree-zero coefficients, before scalar-tower transport.
    change Away.lift _ φ _ (algebraMap (homogeneousSubmodule σ R 0)
      (Away (homogeneousSubmodule σ R) (X i))
      (algebraMap R (homogeneousSubmodule σ R 0) r)) = _
    rw [Away.lift_algebraMap]
    rfl
  · intro j
    simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
      aeval_X, awayXRatio_def]
    rw [Away.lift_mk]
    simp only [hu, one_pow, inv_one, Units.val_one, mul_one]

/-- A surjective polynomial homomorphism sending `Xᵢ` to one
induces a surjective map from the standard projective chart. -/
theorem lift_surjective_of_eval_surjective (φ : MvPolynomial σ R →+* B) (i : σ)
    (h : φ (X i) = 1) (hφ : Function.Surjective φ) :
    Function.Surjective (Away.lift (homogeneousSubmodule σ R) φ (h ▸ isUnit_one)) := by
  intro b
  obtain ⟨p, rfl⟩ := hφ b
  refine ⟨aeval (awayXRatio (R := R) i) p, ?_⟩
  exact DFunLike.congr_fun (φ.lift_comp_aeval_awayXRatio i h) p

end RingHom


namespace TauCeti.MvPolynomial

attribute [local instance] _root_.MvPolynomial.gradedAlgebra

/-- For one homogeneous coordinate, the degree-zero chart is exactly
the coefficient ring. -/
theorem bijective_algebraMap_awayX (R σ : Type*) [CommRing R] [Unique σ] :
    Function.Bijective (algebraMap R
      (Away (MvPolynomial.homogeneousSubmodule σ R) (MvPolynomial.X (default : σ)))) := by
  constructor
  · intro x y hxy
    have hloc := congrArg val hxy
    simp only [val_algebraMap] at hloc
    have hreg : Submonoid.powers (MvPolynomial.X (default : σ) : MvPolynomial σ R) ≤
        nonZeroDivisors (MvPolynomial σ R) :=
      Submonoid.powers_le.mpr (isRegular_iff_mem_nonZeroDivisors.mp MvPolynomial.isRegular_X)
    have hinj := IsLocalization.injective
      (S := Localization.Away (MvPolynomial.X (default : σ) : MvPolynomial σ R)) hreg
    exact MvPolynomial.C_injective σ R (by simpa using hinj hloc)
  · intro z
    have hz : z ∈ Algebra.adjoin R
        (Set.range (TauCeti.MvPolynomial.awayXRatio (R := R) (default : σ))) := by
      rw [TauCeti.MvPolynomial.adjoin_range_awayXRatio]
      trivial
    have hb : Algebra.adjoin R
        (Set.range (TauCeti.MvPolynomial.awayXRatio (R := R) (default : σ))) ≤ ⊥ := by
      apply Algebra.adjoin_le
      rintro _ ⟨i, rfl⟩
      rw [Unique.eq_default i, TauCeti.MvPolynomial.awayXRatio_self]
      exact one_mem _
    exact Algebra.mem_bot.mp (hb hz)


end TauCeti.MvPolynomial

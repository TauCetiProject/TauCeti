/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Padics.Measure.ExtendCoefficients.Algebra
public import TauCeti.NumberTheory.Padics.Measure.Units.Pseudomeasure
public import TauCeti.NumberTheory.Padics.Basic

/-!
# Scalar-valued character evaluations of integral pseudomeasures

Let `G` be a commutative profinite monoid, `O` a Hausdorff topological commutative ring, and
`j : O →+* K` a coefficient homomorphism into the closed unit ball of a complete ultrametric
field. A continuous character `χ : G →ₜ* K` integrates against `O`-valued measures through
`χ.extendedCharacterRingHom j hj`. If `χ ≠ 1`, this scalar map extends uniquely to
pseudomeasures: clear a denominator `δ g - 1` with `χ g ≠ 1`, and divide in `K`.

The resulting additive map `ContinuousMonoidHom.extendedPseudoCharacterEval` satisfies the
cleared-numerator identity at every `g`, including those with `χ g = 1`. Its ratio formula
therefore uses any admissible clearing element. It agrees with character integration on
integral measures, respects the action of measures, and varies continuously with the character
away from the trivial character. For `G = ℤ_pˣ` and the inclusion `ℤ_p → ℚ_p`, it recovers
`ContinuousMonoidHom.unitCharacterEval` on integral-valued characters.

Only the scalar denominator `χ g - 1` is inverted. No regularity of `δ g - 1` and no map on an
entire total quotient ring is required. The construction works in any faithful commutative
algebra of measures, in particular their total quotient ring. It combines the existing
`AbstractMeasure.extendCoefficients` and `TauCeti.Iwasawa.evalAt` APIs.

## References

J. Rodrigues Jacinto and C. Williams, *An introduction to p-adic L-functions*, §3.6,
Definition 3.34, equation (3-11) and Remark 3.35; Remark 3.28 for extension of coefficients.
-/

public noncomputable section

open AbstractMeasure TauCeti.Iwasawa

namespace ContinuousMonoidHom

variable {G O K : Type*} [TopologicalSpace G] [CompactSpace G] [T2Space G]
  [TotallyDisconnectedSpace G] [CommMonoid G] [ContinuousMul G]
  [CommRing O] [TopologicalSpace O] [IsTopologicalRing O] [T0Space O]
  [NormedField K] [CompleteSpace K] [IsUltrametricDist K]
  (χ : G →ₜ* K) (j : O →+* K) (hj : ∀ a, ‖j a‖ ≤ 1)
  (Q : Type*) [CommRing Q] [Algebra D(G, O) Q] [FaithfulSMul D(G, O) Q]

private theorem isUnit_extended_clearing {g : G} (hg : χ g ≠ 1) :
    let := (χ.extendedCharacterRingHom j hj).toAlgebra
    IsUnit (algebraMap D(G, O) K (diracHom g - 1)) := by
  simpa only [RingHom.algebraMap_toAlgebra, map_sub, map_one, diracHom_apply,
    extendedCharacterRingHom_dirac] using (sub_ne_zero.mpr hg).isUnit

/-- Evaluation of an integral pseudomeasure at a nontrivial scalar-valued character, by
extending coefficients of a cleared numerator and dividing by the scalar clearing factor. -/
def extendedPseudoCharacterEval (hχ : χ ≠ 1) :
    pseudomeasures (diracHom (G := G) (R := O)) Q →+ K :=
  letI := (χ.extendedCharacterRingHom j hj).toAlgebra
  (evalAt (diracHom (G := G) (R := O)) Q K (DFunLike.ne_iff.mp hχ).choose
    (isUnit_extended_clearing χ j hj (DFunLike.ne_iff.mp hχ).choose_spec)).toAddMonoidHom

/-- Scalar character evaluation is the generic admissible evaluation at any `g` with
`χ g ≠ 1`, for the algebra structure supplied by extended character integration. -/
theorem extendedPseudoCharacterEval_eq_evalAt (hχ : χ ≠ 1) (g : G) :
    let := (χ.extendedCharacterRingHom j hj).toAlgebra
    ∀ hg' : IsUnit (algebraMap D(G, O) K (diracHom g - 1)),
      χ.extendedPseudoCharacterEval j hj Q hχ =
        (evalAt (diracHom (G := G) (R := O)) Q K g hg').toAddMonoidHom := by
  let := (χ.extendedCharacterRingHom j hj).toAlgebra
  dsimp only
  intro hg'
  unfold extendedPseudoCharacterEval
  exact congrArg (fun L : pseudomeasures (diracHom (G := G) (R := O)) Q →ₗ[D(G, O)] K ↦
    L.toAddMonoidHom) (evalAt_independent _ _ _ _)

/-- The cleared scalar identity holds at every monoid element, even when its character value
is one. -/
theorem extendedPseudoCharacterEval_spec (hχ : χ ≠ 1) (g : G)
    (z : pseudomeasures (diracHom (G := G) (R := O)) Q) :
    (χ g - 1) * χ.extendedPseudoCharacterEval j hj Q hχ z =
      χ.extendedCharacterRingHom j hj (numerator (diracHom (G := G) (R := O)) Q g z) := by
  let := (χ.extendedCharacterRingHom j hj).toAlgebra
  simpa only [extendedPseudoCharacterEval, LinearMap.toAddMonoidHom_coe,
    RingHom.algebraMap_toAlgebra, map_sub, map_one,
    diracHom_apply, extendedCharacterRingHom_dirac] using
    evalAt_cross (δ := diracHom (G := G) (R := O)) (Q := Q) (A := K)
      (DFunLike.ne_iff.mp hχ).choose g
      (isUnit_extended_clearing χ j hj (DFunLike.ne_iff.mp hχ).choose_spec) z

/-- The ratio formula for scalar character evaluation, independent of the choice of an
admissible clearing element. -/
theorem extendedPseudoCharacterEval_eq_div (hχ : χ ≠ 1) {g : G} (hg : χ g ≠ 1)
    (z : pseudomeasures (diracHom (G := G) (R := O)) Q) :
    χ.extendedPseudoCharacterEval j hj Q hχ z =
      χ.extendedCharacterRingHom j hj (numerator (diracHom (G := G) (R := O)) Q g z) /
        (χ g - 1) := by
  rw [eq_div_iff (sub_ne_zero.mpr hg), mul_comm, extendedPseudoCharacterEval_spec]

/-- On integral measures, scalar pseudomeasure evaluation is extended character integration. -/
@[simp]
theorem extendedPseudoCharacterEval_integral (hχ : χ ≠ 1) (μ : D(G, O)) :
    χ.extendedPseudoCharacterEval j hj Q hχ (integral (diracHom (G := G) (R := O)) Q μ) =
      χ.extendedCharacterRingHom j hj μ := by
  let := (χ.extendedCharacterRingHom j hj).toAlgebra
  simp [extendedPseudoCharacterEval, RingHom.algebraMap_toAlgebra]

/-- Multiplication by an integral measure becomes multiplication by its scalar character
integral. -/
theorem extendedPseudoCharacterEval_smul (hχ : χ ≠ 1) (μ : D(G, O))
    (z : pseudomeasures (diracHom (G := G) (R := O)) Q) :
    χ.extendedPseudoCharacterEval j hj Q hχ (μ • z) =
      χ.extendedCharacterRingHom j hj μ * χ.extendedPseudoCharacterEval j hj Q hχ z := by
  let := (χ.extendedCharacterRingHom j hj).toAlgebra
  exact map_smul (evalAt (diracHom (G := G) (R := O)) Q K (DFunLike.ne_iff.mp hχ).choose
    (isUnit_extended_clearing χ j hj (DFunLike.ne_iff.mp hχ).choose_spec)) μ z

/-- Scalar pseudomeasure evaluation is the unique additive extension of character integration
that respects the action of integral measures. -/
theorem extendedPseudoCharacterEval_unique (hχ : χ ≠ 1)
    (L : pseudomeasures (diracHom (G := G) (R := O)) Q →+ K)
    (hsmul : ∀ μ z, L (μ • z) = χ.extendedCharacterRingHom j hj μ * L z)
    (hint : ∀ μ, L (integral (diracHom (G := G) (R := O)) Q μ) =
      χ.extendedCharacterRingHom j hj μ) :
    L = χ.extendedPseudoCharacterEval j hj Q hχ := by
  let := (χ.extendedCharacterRingHom j hj).toAlgebra
  let L' : pseudomeasures (diracHom (G := G) (R := O)) Q →ₗ[D(G, O)] K :=
    { toFun := L
      map_add' := L.map_add
      map_smul' := fun μ z ↦ by
        simpa only [RingHom.id_apply, Algebra.smul_def, RingHom.algebraMap_toAlgebra] using
          hsmul μ z }
  ext z
  unfold extendedPseudoCharacterEval
  exact LinearMap.congr_fun (evalAt_unique _ _ L' fun μ ↦ hint μ) z

/-- For a continuous family of scalar characters, the evaluation of a fixed integral
pseudomeasure is continuous away from the trivial character. -/
theorem continuous_extendedPseudoCharacterEval {S : Type*} [TopologicalSpace S]
    {κ : S → G →ₜ* K} (hκ : Continuous κ)
    (z : pseudomeasures (diracHom (G := G) (R := O)) Q) :
    Continuous fun s : {s // κ s ≠ 1} ↦ (κ s).extendedPseudoCharacterEval j hj Q s.2 z := by
  have hκ' : Continuous fun s ↦ (κ s : C(G, K)) :=
    (ContinuousMonoidHom.isInducing_toContinuousMap _ _).continuous.comp hκ
  rw [continuous_iff_continuousAt]
  rintro ⟨s₀, hs₀⟩
  obtain ⟨g, hg⟩ : ∃ g, κ s₀ g ≠ 1 := by simpa using DFunLike.ne_iff.mp hs₀
  have hval : Continuous fun s ↦ κ s g := (continuous_eval_const g).comp hκ
  have hV : IsOpen {s : {s // κ s ≠ 1} | κ s g ≠ 1} :=
    isOpen_ne_fun (hval.comp continuous_subtype_val) continuous_const
  refine ContinuousAt.congr (f := fun s : {s // κ s ≠ 1} ↦
    (κ s).extendedCharacterRingHom j hj (numerator (diracHom (G := G) (R := O)) Q g z) /
      (κ s g - 1)) ?_ ?_
  · refine ContinuousAt.div ?_ ?_ (sub_ne_zero.mpr hg)
    · simpa only [extendedCharacterRingHom_apply, Function.comp_def] using
        ((map_continuous
          (extendCoefficients j hj (numerator (diracHom (G := G) (R := O)) Q g z))).comp
          (hκ'.comp continuous_subtype_val)).continuousAt
    · exact ((hval.comp continuous_subtype_val).sub continuous_const).continuousAt
  · filter_upwards [hV.mem_nhds hg] with s hs
    exact ((κ s).extendedPseudoCharacterEval_eq_div j hj Q s.2 hs z).symm

end ContinuousMonoidHom

namespace ContinuousMonoidHom

variable {p : ℕ} [Fact p.Prime]

/-- On `ℤ_p`-valued unit characters followed by the inclusion in `ℚ_p`, scalar evaluation
agrees with the intrinsic integral-character evaluation. -/
theorem extendedPseudoCharacterEval_eq_unitCharacterEval
    (χ : ℤ_[p]ˣ →ₜ* ℚ_[p]) (κ : ℤ_[p]ˣ →ₜ* ℤ_[p]) (hχ : χ ≠ 1) (hκ : κ ≠ 1)
    (hχκ : ∀ u, χ u = (κ u : ℚ_[p])) :
    χ.extendedPseudoCharacterEval PadicInt.Coe.ringHom PadicInt.norm_coe_ringHom_le_one
        (FractionRing D(ℤ_[p]ˣ, ℤ_[p])) hχ = κ.unitCharacterEval hκ := by
  obtain ⟨g, hg⟩ : ∃ g, κ g ≠ 1 := by simpa using DFunLike.ne_iff.mp hκ
  have hg' : χ g ≠ 1 := by
    rw [hχκ]
    exact fun h ↦ hg (PadicInt.coe_inj.mp (h.trans PadicInt.coe_one.symm))
  ext z
  rw [extendedPseudoCharacterEval_eq_div _ _ _ _ hχ hg', unitCharacterEval_eq_div _ hκ hg,
    hχκ]
  congr 1
  simpa only [characterIntegralAlgHom_apply, PadicInt.Coe.ringHom_apply] using
    χ.extendedCharacterRingHom_apply_eq_characterIntegralAlgHom
      (PadicInt.Coe.ringHom (p := p)) PadicInt.norm_coe_ringHom_le_one
      PadicInt.isEmbedding_coe_ringHom.continuous κ hχκ
      (numerator (diracHom (R := ℤ_[p])) _ g z)

end ContinuousMonoidHom

open ContinuousMonoidHom

/-! The following checks retain the coefficient, the atom, and the scalar clearing factor. -/

example {p : ℕ} [Fact p.Prime] (χ : ℤ_[p]ˣ →ₜ* ℚ_[p]) (hχ : χ ≠ 1)
    (a : ℤ_[p]) (u : ℤ_[p]ˣ) :
    χ.extendedPseudoCharacterEval PadicInt.Coe.ringHom PadicInt.norm_coe_ringHom_le_one
      (FractionRing D(ℤ_[p]ˣ, ℤ_[p])) hχ
      (integral (diracHom (R := ℤ_[p])) _ (a • dirac ℤ_[p] u)) = (a : ℚ_[p]) * χ u := by
  rw [extendedPseudoCharacterEval_integral, extendedCharacterRingHom_apply]
  simp

example {p : ℕ} [Fact p.Prime] (χ : ℤ_[p]ˣ →ₜ* ℚ_[p]) (hχ : χ ≠ 1) :
    χ.extendedPseudoCharacterEval PadicInt.Coe.ringHom PadicInt.norm_coe_ringHom_le_one
      (FractionRing D(ℤ_[p]ˣ, ℤ_[p])) hχ
      (integral (diracHom (G := ℤ_[p]ˣ) (R := ℤ_[p])) _ (1 : D(ℤ_[p]ˣ, ℤ_[p]))) = 1 := by
  simp

-- In particular the sign character at 2 uses the scalar -2 at -1. Its Dirac difference
-- need not be regular in the measure ring for this evaluation to make sense.
example (χ : ℤ_[2]ˣ →ₜ* ℚ_[2]) (hχ : χ ≠ 1) (hneg : χ (-1) = -1)
    (z : unitsPseudomeasures 2) :
    (-2 : ℚ_[2]) * χ.extendedPseudoCharacterEval PadicInt.Coe.ringHom
      PadicInt.norm_coe_ringHom_le_one (FractionRing D(ℤ_[2]ˣ, ℤ_[2])) hχ z =
      χ.extendedCharacterRingHom PadicInt.Coe.ringHom PadicInt.norm_coe_ringHom_le_one
        (numerator (diracHom (R := ℤ_[2])) _ (-1) z) := by
  convert χ.extendedPseudoCharacterEval_spec PadicInt.Coe.ringHom
    PadicInt.norm_coe_ringHom_le_one (FractionRing D(ℤ_[2]ˣ, ℤ_[2])) hχ (-1) z using 1
  norm_num [hneg]

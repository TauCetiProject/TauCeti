/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Padics.Measure.Units.Moments
public import TauCeti.RingTheory.Iwasawa.Pseudomeasure
public import Mathlib.Topology.Algebra.Group.CompactOpen

/-!
# Evaluation of pseudo-measures on `ℤ_pˣ` at characters

Let `M = D(ℤ_pˣ, ℤ_p)` be the convolution algebra of measures on the unit group and `Q` its total
quotient ring. A pseudo-measure is an element `z : Q` such that `(δ_a - 1) z` is a measure for
every unit `a`; the `p`-adic zeta function of Kubota–Leopoldt is the basic example. Since the
character integral `μ ↦ μ κ` of a nontrivial continuous character `κ` does not extend to `Q`, a
pseudo-measure is evaluated at `κ` by clearing a denominator: for any `g` with `κ g ≠ 1`,

  `E_κ(z) = (n_g(z))(κ) / (κ g - 1)`,

where `n_g(z) = (δ_g - 1) z ∈ M` is the cleared numerator. This value lies in `ℚ_p` and does not
depend on `g`. It is the unique additive extension of `μ ↦ μ κ` to pseudo-measures that is
compatible with the action of measures.

The positive moments of a pseudo-measure are its evaluations at the power characters
`u ↦ u ^ k`, `k > 0`. Clearing denominators with the regular element `δ_{1+p} - 1` reduces the
statement that these moments determine a pseudo-measure to the corresponding statement for
measures, `AbstractMeasure.units_eq_zero_of_positive_moments`. Hence the nontrivial characters
separate pseudo-measures.

Near a parameter at which `κ g ≠ 1`, the ratio formula at the fixed clearing element `g` shows
that the evaluation varies continuously with the character.

## Main definitions

* `AbstractMeasure.unitsPseudomeasures p`: the pseudo-measures on `ℤ_pˣ`, an `M`-submodule of the
  total quotient ring of `M`.
* `ContinuousMonoidHom.unitCharacterEval κ hκ`: evaluation of pseudo-measures at a nontrivial
  continuous character `κ : ℤ_pˣ →ₜ* ℤ_p`, with values in `ℚ_p`.

## Main results

* `ContinuousMonoidHom.unitCharacterEval_spec`: the cleared identity
  `(κ g - 1) E_κ(z) = n_g(z)(κ)`, for every `g`.
* `ContinuousMonoidHom.unitCharacterEval_eq_div`: the ratio formula at any `g` with `κ g ≠ 1`.
* `ContinuousMonoidHom.unitCharacterEval_integral` and `ContinuousMonoidHom.unitCharacterEval_smul`:
  `E_κ` extends `μ ↦ μ κ` and is compatible with the action of measures.
* `ContinuousMonoidHom.unitCharacterEval_unique`: these two properties characterise `E_κ`.
* `ContinuousMonoidHom.continuous_unitCharacterEval`: for a continuous family of characters
  `κ_s`, the value `E_{κ_s}(z)` is continuous in `s` away from the trivial character.
* `AbstractMeasure.unitsPseudomeasure_eq_zero_of_positive_moments`: a pseudo-measure with vanishing
  positive moments is zero.
* `AbstractMeasure.unitCharacterEval_ext`: pseudo-measures with the same evaluation at every
  nontrivial character are equal.

## References

* J. Rodrigues Jacinto and C. Williams, *An introduction to p-adic L-functions*, §3.6,
  Definition 3.34, equation (3-11), Remark 3.35 and Lemma 3.36.
-/

public noncomputable section

open scoped AbstractMeasure nonZeroDivisors

open TauCeti.Iwasawa PadicInt

variable {p : ℕ} [Fact p.Prime]

namespace AbstractMeasure

variable (p) in
/-- The pseudo-measures on `ℤ_pˣ`: the elements `z` of the total quotient ring of
`D(ℤ_pˣ, ℤ_p)` such that `(δ_a - 1) z` is a measure for every unit `a`. -/
abbrev unitsPseudomeasures : Submodule D(ℤ_[p]ˣ, ℤ_[p]) (FractionRing D(ℤ_[p]ˣ, ℤ_[p])) :=
  pseudomeasures (diracHom (R := ℤ_[p])) (FractionRing D(ℤ_[p]ˣ, ℤ_[p]))

end AbstractMeasure

namespace ContinuousMonoidHom

open AbstractMeasure

variable (κ : ℤ_[p]ˣ →ₜ* ℤ_[p])

/-- The character integral `μ ↦ μ κ` on `D(ℤ_pˣ, ℤ_p)`, followed by the inclusion `ℤ_p → ℚ_p`. -/
private def toPadicRingHom : D(ℤ_[p]ˣ, ℤ_[p]) →+* ℚ_[p] :=
  (algebraMap ℤ_[p] ℚ_[p]).comp (characterIntegralAlgHom κ).toRingHom

/-- For the algebra structure on `ℚ_p` given by `toPadicRingHom κ`, `algebraMap` is `μ ↦ μ κ`. -/
private theorem algebraMap_toAlgebra_apply (μ : D(ℤ_[p]ˣ, ℤ_[p])) :
    letI := (toPadicRingHom κ).toAlgebra
    algebraMap D(ℤ_[p]ˣ, ℤ_[p]) ℚ_[p] μ = (μ κ : ℚ_[p]) := by
  let := (toPadicRingHom κ).toAlgebra
  rw [RingHom.algebraMap_toAlgebra]
  simp [toPadicRingHom]

private theorem algebraMap_toAlgebra_dirac_sub_one (g : ℤ_[p]ˣ) :
    letI := (toPadicRingHom κ).toAlgebra
    algebraMap D(ℤ_[p]ˣ, ℤ_[p]) ℚ_[p] (diracHom g - 1) = (κ g : ℚ_[p]) - 1 := by
  let := (toPadicRingHom κ).toAlgebra
  rw [map_sub, map_one, algebraMap_toAlgebra_apply]
  simp

private theorem exists_apply_ne_one {κ : ℤ_[p]ˣ →ₜ* ℤ_[p]} (hκ : κ ≠ 1) : ∃ g, κ g ≠ 1 := by
  simpa using DFunLike.ne_iff.1 hκ

private theorem coe_apply_sub_one_ne_zero {g : ℤ_[p]ˣ} (hg : κ g ≠ 1) :
    (κ g : ℚ_[p]) - 1 ≠ 0 := by
  exact_mod_cast PadicInt.coe_ne_zero.2 (sub_ne_zero.2 hg)

/-- For the algebra structure given by `μ ↦ μ κ`, the clearing factor `δ_g - 1` of a unit `g` with
`κ g ≠ 1` maps to a unit of `ℚ_p`. -/
private theorem isUnit_algebraMap_dirac_sub_one {g : ℤ_[p]ˣ} (hg : κ g ≠ 1) :
    letI := (toPadicRingHom κ).toAlgebra
    IsUnit (algebraMap D(ℤ_[p]ˣ, ℤ_[p]) ℚ_[p] (diracHom g - 1)) := by
  rw [algebraMap_toAlgebra_dirac_sub_one]
  exact Ne.isUnit (coe_apply_sub_one_ne_zero κ hg)

/-- Evaluation of pseudo-measures on `ℤ_pˣ` at a nontrivial continuous character `κ`: the
pseudo-measure `z` is sent to `n_g(z)(κ) / (κ g - 1)` in `ℚ_p`, for any `g` with `κ g ≠ 1`, where
`n_g(z) = (δ_g - 1) z` is the cleared numerator. The value does not depend on `g`
(`unitCharacterEval_eq_div`). -/
def unitCharacterEval (hκ : κ ≠ 1) : unitsPseudomeasures p →+ ℚ_[p] :=
  letI := (toPadicRingHom κ).toAlgebra
  (evalAt (diracHom (R := ℤ_[p])) (FractionRing D(ℤ_[p]ˣ, ℤ_[p])) ℚ_[p]
    (exists_apply_ne_one hκ).choose
    (isUnit_algebraMap_dirac_sub_one κ (exists_apply_ne_one hκ).choose_spec)).toAddMonoidHom

/-- `unitCharacterEval` is `evalAt` at the chosen clearing element, for the algebra structure on
`ℚ_p` given by `μ ↦ μ κ`. All of its properties are derived from the `evalAt` API through this
unfolding. -/
private theorem unitCharacterEval_apply (hκ : κ ≠ 1) (z : unitsPseudomeasures p) :
    letI := (toPadicRingHom κ).toAlgebra
    κ.unitCharacterEval hκ z =
      evalAt (diracHom (R := ℤ_[p])) _ ℚ_[p] (exists_apply_ne_one hκ).choose
        (isUnit_algebraMap_dirac_sub_one κ (exists_apply_ne_one hκ).choose_spec) z :=
  rfl

/-- The cleared identity for the evaluation at a nontrivial character: for every unit `g`,
`(κ g - 1) E_κ(z) = n_g(z)(κ)`, where `n_g(z) = (δ_g - 1) z` is the cleared numerator. -/
theorem unitCharacterEval_spec (hκ : κ ≠ 1) (g : ℤ_[p]ˣ) (z : unitsPseudomeasures p) :
    ((κ g : ℚ_[p]) - 1) * κ.unitCharacterEval hκ z =
      (numerator (diracHom (R := ℤ_[p])) _ g z κ : ℚ_[p]) := by
  let := (toPadicRingHom κ).toAlgebra
  rw [unitCharacterEval_apply, ← algebraMap_toAlgebra_dirac_sub_one,
    ← algebraMap_toAlgebra_apply]
  exact evalAt_cross _ g _ z

/-- The ratio formula: for any unit `g` with `κ g ≠ 1`, the evaluation of a pseudo-measure `z` at
`κ` is `n_g(z)(κ) / (κ g - 1)`. -/
theorem unitCharacterEval_eq_div (hκ : κ ≠ 1) {g : ℤ_[p]ˣ} (hg : κ g ≠ 1)
    (z : unitsPseudomeasures p) :
    κ.unitCharacterEval hκ z =
      (numerator (diracHom (R := ℤ_[p])) _ g z κ : ℚ_[p]) / ((κ g : ℚ_[p]) - 1) := by
  rw [eq_div_iff (coe_apply_sub_one_ne_zero κ hg), mul_comm, unitCharacterEval_spec]

/-- The evaluation at `κ` extends the character integral `μ ↦ μ κ` from measures to
pseudo-measures. -/
@[simp]
theorem unitCharacterEval_integral (hκ : κ ≠ 1) (μ : D(ℤ_[p]ˣ, ℤ_[p])) :
    κ.unitCharacterEval hκ (integral (diracHom (R := ℤ_[p])) _ μ) = (μ κ : ℚ_[p]) := by
  let := (toPadicRingHom κ).toAlgebra
  rw [unitCharacterEval_apply, ← algebraMap_toAlgebra_apply]
  exact evalAt_integral _ _ μ

/-- The evaluation at `κ` is compatible with the action of measures on pseudo-measures:
`E_κ(μ z) = μ(κ) E_κ(z)`. -/
theorem unitCharacterEval_smul (hκ : κ ≠ 1) (μ : D(ℤ_[p]ˣ, ℤ_[p])) (z : unitsPseudomeasures p) :
    κ.unitCharacterEval hκ (μ • z) = (μ κ : ℚ_[p]) * κ.unitCharacterEval hκ z := by
  let := (toPadicRingHom κ).toAlgebra
  rw [unitCharacterEval_apply, unitCharacterEval_apply, ← algebraMap_toAlgebra_apply,
    ← Algebra.smul_def]
  exact map_smul (evalAt (diracHom (R := ℤ_[p])) _ ℚ_[p] _ _) μ z

/-- Uniqueness of the evaluation at `κ`: an additive map on pseudo-measures which extends the
character integral `μ ↦ μ κ` and is compatible with the action of measures is `E_κ`. -/
theorem unitCharacterEval_unique (hκ : κ ≠ 1) (L : unitsPseudomeasures p →+ ℚ_[p])
    (hsmul : ∀ (μ : D(ℤ_[p]ˣ, ℤ_[p])) z, L (μ • z) = (μ κ : ℚ_[p]) * L z)
    (hint : ∀ μ : D(ℤ_[p]ˣ, ℤ_[p]), L (integral (diracHom (R := ℤ_[p])) _ μ) = (μ κ : ℚ_[p])) :
    L = κ.unitCharacterEval hκ := by
  let := (toPadicRingHom κ).toAlgebra
  -- `L` is `D(ℤ_pˣ, ℤ_p)`-linear for the algebra structure given by `μ ↦ μ κ`.
  let L' : unitsPseudomeasures p →ₗ[D(ℤ_[p]ˣ, ℤ_[p])] ℚ_[p] :=
    { L with
      map_smul' := fun μ z => by
        -- The coercion of `{ L with .. }` is `L` and `RingHom.id` is the identity, by definition;
        -- the scalar action of `μ` on `ℚ_p` is the one given by `toPadicRingHom κ`.
        change L (μ • z) = μ • L z
        rw [hsmul, Algebra.smul_def, algebraMap_toAlgebra_apply] }
  ext z
  rw [unitCharacterEval_apply]
  -- `L' z` is `L z` by definition.
  exact LinearMap.congr_fun (evalAt_unique _ _ L' fun μ => (hint μ).trans
    (algebraMap_toAlgebra_apply κ μ).symm) z

/-- Continuity of the evaluation away from the trivial character: for a continuous family of
characters `κ : S → (ℤ_pˣ →ₜ* ℤ_p)` (for the compact-open topology, which is the topology of uniform
convergence since `ℤ_pˣ` is compact) and a fixed pseudo-measure `z`, the value `E_{κ s}(z)` depends
continuously on the parameter `s` ranging over `{s | κ s ≠ 1}`. -/
theorem continuous_unitCharacterEval {S : Type*} [TopologicalSpace S]
    {κ : S → ℤ_[p]ˣ →ₜ* ℤ_[p]} (hκ : Continuous κ) (z : unitsPseudomeasures p) :
    Continuous fun s : {s // κ s ≠ 1} => (κ s).unitCharacterEval s.2 z := by
  have hκ' : Continuous fun s => (κ s : C(ℤ_[p]ˣ, ℤ_[p])) :=
    (ContinuousMonoidHom.isInducing_toContinuousMap _ _).continuous.comp hκ
  rw [continuous_iff_continuousAt]
  rintro ⟨s₀, hs₀⟩
  obtain ⟨g, hg⟩ := exists_apply_ne_one hs₀
  -- Near `s₀` the clearing element `g` stays admissible, and the ratio formula at `g` is
  -- continuous.
  have hval : Continuous fun s => κ s g := (continuous_eval_const g).comp hκ
  have hV : IsOpen {s : {s // κ s ≠ 1} | κ s g ≠ 1} :=
    isOpen_ne_fun (hval.comp continuous_subtype_val) continuous_const
  refine ContinuousAt.congr (f := fun s : {s // κ s ≠ 1} =>
      (numerator (diracHom (R := ℤ_[p])) _ g z (κ s) : ℚ_[p]) / ((κ s g : ℚ_[p]) - 1)) ?_ ?_
  · refine ContinuousAt.div ?_ ?_ (coe_apply_sub_one_ne_zero _ hg)
    · exact (continuous_subtype_val.comp ((map_continuous _).comp
        (hκ'.comp continuous_subtype_val))).continuousAt
    · exact ((continuous_subtype_val.comp (hval.comp continuous_subtype_val)).sub
        continuous_const).continuousAt
  · filter_upwards [hV.mem_nhds hg] with s hs
    exact (unitCharacterEval_eq_div _ _ hs z).symm

end ContinuousMonoidHom

namespace AbstractMeasure

open ContinuousMonoidHom

/-- A pseudo-measure on `ℤ_pˣ` whose positive moments, its evaluations at the power characters
`u ↦ u ^ k` for `k > 0`, all vanish is zero. -/
theorem unitsPseudomeasure_eq_zero_of_positive_moments (z : unitsPseudomeasures p)
    (hz : ∀ k (hk : 0 < k),
      (unitsPowCharacter p k).unitCharacterEval (unitsPowCharacter_ne_one hk) z = 0) :
    z = 0 := by
  obtain ⟨a, -, hreg⟩ := exists_val_eq_one_add_dirac_sub_one_mem_nonZeroDivisors (p := p)
  -- The cleared numerator `(δ_a - 1) z` is a measure with vanishing positive moments.
  have hn : numerator (diracHom (R := ℤ_[p])) _ a z = 0 := by
    refine units_eq_zero_of_positive_moments _ fun k hk => ?_
    have h := unitCharacterEval_spec _ (unitsPowCharacter_ne_one hk) a z
    rwa [hz k hk, mul_zero, eq_comm, PadicInt.coe_eq_zero] at h
  -- Since `δ_a - 1` is regular, it becomes a unit in the total quotient ring.
  have hz' := algebraMap_numerator a z
  rw [hn, map_zero, eq_comm, diracHom_apply,
    (IsLocalization.map_units (FractionRing D(ℤ_[p]ˣ, ℤ_[p])) ⟨_, hreg⟩).mul_right_eq_zero] at hz'
  exact Subtype.ext hz'

/-- Pseudo-measures on `ℤ_pˣ` are determined by their evaluations at the nontrivial continuous
characters. -/
theorem unitCharacterEval_ext {z η : unitsPseudomeasures p}
    (h : ∀ (κ : ℤ_[p]ˣ →ₜ* ℤ_[p]) (hκ : κ ≠ 1),
      κ.unitCharacterEval hκ z = κ.unitCharacterEval hκ η) :
    z = η :=
  sub_eq_zero.1 <| unitsPseudomeasure_eq_zero_of_positive_moments _ fun k hk => by
    rw [map_sub, h, sub_self]

end AbstractMeasure

/-! ### Examples -/

open AbstractMeasure ContinuousMonoidHom

-- The evaluation at a nontrivial character of the integral Dirac measure at `a` is `κ a`.
example (κ : ℤ_[p]ˣ →ₜ* ℤ_[p]) (hκ : κ ≠ 1) (a : ℤ_[p]ˣ) :
    κ.unitCharacterEval hκ (integral (diracHom (R := ℤ_[p])) _ (dirac ℤ_[p] a)) =
      (κ a : ℚ_[p]) := by
  simp

-- At `p = 3`, the positive moments of the integral Dirac measure at the unit `2` are `2 ^ k`.
-- Computed through the clearing element `a = 4`, the numerator moment `2 ^ k * (4 ^ k - 1)` must be
-- divided by `4 ^ k - 1`.
example (k : ℕ) (hk : 0 < k) (a b : ℤ_[3]ˣ) (ha : (a : ℤ_[3]) = 4) (hb : (b : ℤ_[3]) = 2) :
    numerator (diracHom (R := ℤ_[3])) _ a (integral (diracHom (R := ℤ_[3]))
        (FractionRing D(ℤ_[3]ˣ, ℤ_[3])) (dirac ℤ_[3] b)) (unitsPowCharacter 3 k) =
        2 ^ k * (4 ^ k - 1) ∧
      (unitsPowCharacter 3 k).unitCharacterEval (unitsPowCharacter_ne_one hk)
        (integral (diracHom (R := ℤ_[3])) _ (dirac ℤ_[3] b)) = ((2 ^ k : ℤ_[3]) : ℚ_[3]) := by
  rw [numerator_integral, unitCharacterEval_integral, ← characterIntegralAlgHom_apply,
    ← characterIntegralAlgHom_apply]
  simp only [map_mul, map_sub, map_one, diracHom_apply, characterIntegralAlgHom_dirac,
    unitsPowCharacter_apply, ha, hb, and_true]
  exact mul_comm _ _

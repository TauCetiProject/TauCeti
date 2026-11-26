/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Padics.Distribution.LocallyAnalytic
import TauCeti.Data.ZMod.Cast

/-!
# Restricting locally analytic functions to residue classes

For `n : ℕ` and `a ∈ ZMod (pⁿ)`, multiplying a locally analytic function `f` on `ℤ_p` by the
indicator of the residue class `a + pⁿℤ_p` gives a locally analytic function `1_{a + pⁿℤ_p} f`.
This file constructs this restriction on coefficient vectors and on locally analytic functions.

On the analytic stage `LA_h(E)` of a level `h ≥ n`, every disc `b + pʰℤ_p` lies in a single
residue class modulo `pⁿ`, the class of `b.val`. Multiplying by the indicator of `a + pⁿℤ_p`
keeps the coefficients on the discs of the classes `b` with `b.val ≡ a` and replaces the others
by zero; this is the coordinate projection `ZeroAtInftyContinuousMap.indicatorCLM`. On a stage of
level `h < n`, a vector is first re-expanded to the level `max h n`. Re-expansion only reads the
coefficients on the disc containing a smaller disc
(`TauCeti.AnalyticStage.transitionLE_indicatorCLM`), so the restrictions are compatible with the
transitions between levels and induce the restriction `TauCeti.LocallyAnalytic.restrictResidue`
on the algebraic direct limit `LA(ℤ_p, E)`. The identities between restrictions of locally
analytic functions are proved on coefficients, not on evaluated functions, so they hold without
torsion-freeness of `E`.

The transpose, restriction of locally analytic distributions, is in
`TauCeti.NumberTheory.Padics.Distribution.Residue`.

## Main definitions

* `TauCeti.AnalyticStage.restrictResidue S n a`: restriction to `a + pⁿℤ_p`,
  `LA_h(E) →L[S] LA_{max h n}(E)`.
* `TauCeti.LocallyAnalytic.restrictResidue S n a`: restriction of locally analytic functions.

## Main results

* `TauCeti.AnalyticStage.restrictResidue_of_le`: on a stage of level `h ≥ n`, restriction is the
  coordinate projection.
* `TauCeti.AnalyticStage.norm_restrictResidue_le`,
  `TauCeti.AnalyticStage.opNorm_restrictResidue_le_one`: restriction does not increase norms.
* `TauCeti.LocallyAnalytic.eval_restrictResidue`: restriction evaluates to `1_{a + pⁿℤ_p} f`.
* `TauCeti.LocallyAnalytic.restrictResidue_comp`, `TauCeti.LocallyAnalytic.sum_restrictResidue`:
  the restrictions at depth `n` are orthogonal idempotents with sum the identity.

## References

* P. Colmez, *Fonctions d'une variable p-adique*, Astérisque 330 (2010), §II.4.
-/

public section

open scoped ZeroAtInfty
open ZeroAtInftyContinuousMap

namespace TauCeti

variable {p : ℕ} [Fact p.Prime]

namespace AnalyticStage

variable {h : ℕ} {E : Type*} [NormedAddCommGroup E] [Module ℤ_[p] E] [IsBoundedSMul ℤ_[p] E]
  [IsUltrametricDist E] [CompleteSpace E]
  (S : Type*) [Semiring S] [Module S E] [ContinuousConstSMul S E] [SMulCommClass ℤ_[p] S E]
  (n : ℕ) (a : ZMod (p ^ n))

/-- Restriction of a coefficient vector of `LA_h(E)` to the residue class `a + pⁿℤ_p`: the vector
is re-expanded to the level `max h n`, where it is projected onto the discs of the classes `b`
with `b.val ≡ a` modulo `pⁿ`. -/
noncomputable def restrictResidue : AnalyticStage p h E →L[S] AnalyticStage p (max h n) E :=
  indicatorCLM S (Prod.fst ⁻¹' {b : ZMod (p ^ max h n) | (ZMod.cast b : ZMod (p ^ n)) = a}) ∘L
    transitionLE S (le_max_left h n)

/-- The restriction to a residue class re-expands to the level `max h n`, then projects. -/
theorem restrictResidue_apply (c : AnalyticStage p h E) :
    restrictResidue S n a c =
      indicatorCLM S (Prod.fst ⁻¹' {b : ZMod (p ^ max h n) | (ZMod.cast b : ZMod (p ^ n)) = a})
        (transitionLE S (le_max_left h n) c) :=
  (rfl)

/-- The restriction to a residue class does not increase the norm. -/
theorem norm_restrictResidue_le (c : AnalyticStage p h E) : ‖restrictResidue S n a c‖ ≤ ‖c‖ :=
  (norm_indicatorCLM_apply_le _ _).trans (norm_transitionLE_le S _ c)

/-- The restriction to a residue class has operator norm at most `1`. -/
theorem opNorm_restrictResidue_le_one {𝕜 : Type*} [NontriviallyNormedField 𝕜] [NormedSpace 𝕜 E]
    [SMulCommClass ℤ_[p] 𝕜 E] : ‖restrictResidue (p := p) (h := h) (E := E) 𝕜 n a‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun c ↦ by
    simpa using norm_restrictResidue_le 𝕜 n a c

/-- On a stage of level `h ≥ n`, the restriction to a residue class is the projection onto the
discs of the classes in it, followed by re-expansion to the level `max h n`. -/
theorem restrictResidue_of_le (hnh : n ≤ h) (c : AnalyticStage p h E) :
    restrictResidue S n a c =
      transitionLE S (le_max_left h n)
        (indicatorCLM S (Prod.fst ⁻¹' {b : ZMod (p ^ h) | (ZMod.cast b : ZMod (p ^ n)) = a})
          c) := by
  rw [restrictResidue_apply, transitionLE_indicatorCLM S (le_max_left h n),
    ZMod.preimage_cast_setOf_cast_eq (pow_dvd_pow p hnh) (pow_dvd_pow p (le_max_left h n))]

/-- The restriction to a residue class commutes with re-expansion. -/
theorem transitionLE_restrictResidue {k : ℕ} (hhk : h ≤ k) (c : AnalyticStage p h E) :
    transitionLE S (max_le_max_right n hhk) (restrictResidue S n a c) =
      restrictResidue S n a (transitionLE S hhk c) := by
  rw [restrictResidue_apply, restrictResidue_apply,
    transitionLE_indicatorCLM S (max_le_max_right n hhk),
    ZMod.preimage_cast_setOf_cast_eq (pow_dvd_pow p (le_max_right h n))
      (pow_dvd_pow p (max_le_max_right n hhk)),
    transitionLE_transitionLE, transitionLE_transitionLE]

end AnalyticStage

namespace LocallyAnalytic

open AnalyticStage

variable {E : Type*} [NormedAddCommGroup E] [Module ℤ_[p] E] [IsBoundedSMul ℤ_[p] E]
  [IsUltrametricDist E] [CompleteSpace E]
  (S : Type*) [Semiring S] [Module S E] [ContinuousConstSMul S E] [SMulCommClass ℤ_[p] S E]
  (n : ℕ) (a : ZMod (p ^ n))

/-- Restriction of locally analytic functions to the residue class `a + pⁿℤ_p`, that is,
multiplication by its indicator, induced by `AnalyticStage.restrictResidue` on each stage. -/
noncomputable def restrictResidue : LocallyAnalytic p S E →ₗ[S] LocallyAnalytic p S E :=
  Module.DirectLimit.lift S ℕ _ _
    (fun h ↦ ofStage S (max h n) ∘ₗ (AnalyticStage.restrictResidue S n a).toLinearMap)
    fun h k hhk c ↦ by
      simp only [LinearMap.coe_comp, ContinuousLinearMap.coe_coe, Function.comp_apply]
      rw [← transitionLE_restrictResidue, ofStage_transitionLE]

/-- The restriction to a residue class is computed on any stage after re-expansion to the level
`max h n`. -/
@[simp]
theorem restrictResidue_ofStage (h : ℕ) (c : AnalyticStage p h E) :
    restrictResidue S n a (ofStage S h c) =
      ofStage S (max h n) (AnalyticStage.restrictResidue S n a c) :=
  lift_ofStage S _ _ h c

/-- On a stage of level `h ≥ n`, the restriction to a residue class is the projection onto the
discs of the classes in it. -/
theorem restrictResidue_ofStage_of_le {h : ℕ} (hnh : n ≤ h) (c : AnalyticStage p h E) :
    restrictResidue S n a (ofStage S h c) =
      ofStage S h
        (indicatorCLM S (Prod.fst ⁻¹' {b : ZMod (p ^ h) | (ZMod.cast b : ZMod (p ^ n)) = a})
          c) := by
  rw [restrictResidue_ofStage, restrictResidue_of_le S n a hnh, ofStage_transitionLE]

/-- The restriction to `a + pⁿℤ_p` evaluates to the product with the indicator of the class. -/
@[simp]
theorem eval_restrictResidue (f : LocallyAnalytic p S E) (x : ℤ_[p]) :
    eval S (restrictResidue S n a f) x =
      if PadicInt.toZModPow n x = a then eval S f x else 0 := by
  obtain ⟨h, hnh, c, rfl⟩ := exists_ofStage_ge S n f
  rw [restrictResidue_ofStage_of_le S n a hnh, eval_ofStage, eval_ofStage, eval_indicatorCLM]
  simp [Set.indicator_apply, PadicInt.cast_toZModPow n h hnh]

/-- The restrictions to the residue classes modulo `pⁿ` are orthogonal idempotents. -/
theorem restrictResidue_comp (b : ZMod (p ^ n)) (f : LocallyAnalytic p S E) :
    restrictResidue S n a (restrictResidue S n b f) =
      if a = b then restrictResidue S n a f else 0 := by
  obtain ⟨h, hnh, c, rfl⟩ := exists_ofStage_ge S n f
  simp only [restrictResidue_ofStage_of_le S n _ hnh]
  split_ifs with hab
  · subst hab
    congr 1
    ext i
    simp [Set.indicator_indicator]
  · rw [← map_zero (ofStage S h)]
    congr 1
    ext ⟨b', j⟩
    by_cases hb' : (ZMod.cast b' : ZMod (p ^ n)) = a <;> simp [hb', hab]

/-- Restricting twice to the same residue class is restricting once. -/
@[simp]
theorem restrictResidue_idem (f : LocallyAnalytic p S E) :
    restrictResidue S n a (restrictResidue S n a f) = restrictResidue S n a f := by
  simp [restrictResidue_comp]

/-- A locally analytic function is the sum of its restrictions to the residue classes modulo
`pⁿ`. -/
@[simp]
theorem sum_restrictResidue (f : LocallyAnalytic p S E) :
    ∑ a : ZMod (p ^ n), restrictResidue S n a f = f := by
  obtain ⟨h, hnh, c, rfl⟩ := exists_ofStage_ge S n f
  simp only [restrictResidue_ofStage_of_le S n _ hnh, ← map_sum]
  congr 1
  ext i
  simp [Set.indicator_apply]

/-- Modulo `p ^ 0 = 1` there is a single residue class, so restriction is the identity. -/
@[simp]
theorem restrictResidue_zero_depth (a : ZMod (p ^ 0)) (f : LocallyAnalytic p S E) :
    restrictResidue S 0 a f = f := by
  have : Subsingleton (ZMod (p ^ 0)) := by
    rw [pow_zero]
    infer_instance
  simpa only [Fintype.sum_subsingleton _ a] using sum_restrictResidue S 0 f

end LocallyAnalytic

end TauCeti

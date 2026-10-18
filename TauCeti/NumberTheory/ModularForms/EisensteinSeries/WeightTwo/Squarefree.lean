/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ModularForms.EisensteinSeries.WeightTwo.Boundary
public import TauCeti.NumberTheory.ModularForms.Cusps.Squarefree
import TauCeti.NumberTheory.ModularForms.SturmBound
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# The weight-two cusp–Eisenstein decomposition at squarefree level

For squarefree `N`, the corrected series `E₂(z) - d E₂(dz)`, indexed by divisors `d > 1`
of `N`, span a complement to `S₂(Γ₀(N))` in `M₂(Γ₀(N))`. Thus every weight-two form is a
unique sum of a cusp form and a linear combination of these corrected series, and the
codimension of the cusp space is the number of divisors of `N` minus one.

The boundary vectors of the corrected series are already known to be independent.
At squarefree level there is one cusp per divisor, and the residue relation cuts the
boundary image down by at least one dimension. Independence therefore gives spanning.
No dimension formula for the compactified modular curve is used.

## References

* F. Diamond and J. Shurman, *A First Course in Modular Forms*, §4.6.

The construction uses `correctedE2AtLevel`, its boundary independence theorem, and the
width-weighted weight-two residue relation.
-/

public noncomputable section

open Matrix.SpecialLinearGroup CongruenceSubgroup ModularForm
open scoped MatrixGroups

namespace TauCeti.EisensteinSeries

variable {N : ℕ} [NeZero N]

private def nontrivialDivisorEquiv :
    {d : ℕ // 1 < d ∧ d ∣ N} ≃
      {d : N.divisors // d ≠ ⟨1, Nat.one_mem_divisors.mpr (NeZero.ne N)⟩} where
  toFun d := ⟨⟨d.val, Nat.mem_divisors.mpr ⟨d.property.2, NeZero.ne N⟩⟩,
    fun h ↦ by have := congrArg Subtype.val h; simp at this; omega⟩
  invFun d := ⟨d.val.val, by
    have hdpos := Nat.pos_of_mem_divisors d.val.property
    have hdne : d.val.val ≠ 1 := fun h ↦ d.property (Subtype.ext h)
    exact ⟨by omega, Nat.dvd_of_mem_divisors d.val.property⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The corrected weight-two Eisenstein span has dimension `τ(N) - 1`, at any nonzero level. -/
theorem finrank_span_correctedE2AtLevel :
    Module.finrank ℂ (Submodule.span ℂ (Set.range (correctedE2AtLevel N))) =
      N.divisors.card - 1 := by
  classical
  let _ := Fintype.ofEquiv _ (nontrivialDivisorEquiv (N := N)).symm
  rw [finrank_span_eq_card (linearIndependent_correctedE2AtLevel N),
    Fintype.card_congr (nontrivialDivisorEquiv (N := N))]
  simp

/-- At squarefree level, the corrected weight-two Eisenstein series and the cusp forms are
complementary in the full modular-form space. This includes `N = 1`, when the Eisenstein span
and the entire weight-two space are both zero. -/
theorem isCompl_span_correctedE2AtLevel_cuspFormSubmodule_of_squarefree (hN : Squarefree N) :
    IsCompl (Submodule.span ℂ (Set.range (correctedE2AtLevel N)))
      (cuspFormSubmodule ((Gamma0 N).map (mapGL ℝ)) 2) := by
  classical
  let E := Submodule.span ℂ (Set.range (correctedE2AtLevel N))
  let Q := constantTermsAtDivisors (N := N) (k := 2)
  have hker : LinearMap.ker Q = cuspFormSubmodule ((Gamma0 N).map (mapGL ℝ)) 2 :=
    ker_constantTermsAtDivisors_of_squarefree hN
  have hdis : Disjoint E (LinearMap.ker Q) := by
    rw [hker]
    exact disjoint_span_correctedE2AtLevel_cuspFormSubmodule
  have hinj : Function.Injective (Q.domRestrict E) :=
    LinearMap.injective_domRestrict_iff.mpr hdis
  have hdim : Module.finrank ℂ (E.map Q) = N.divisors.card - 1 := by
    rw [← LinearMap.range_domRestrict, LinearMap.finrank_range_of_inj hinj]
    exact finrank_span_correctedE2AtLevel
  have hlt : Module.finrank ℂ (LinearMap.range Q) < N.divisors.card := by
    have h := Submodule.finrank_lt_finrank_of_lt
      (lt_top_iff_ne_top.mpr (range_constantTermsAtDivisors_ne_top_of_squarefree hN))
    simpa using h
  have heq : E.map Q = LinearMap.range Q :=
    Submodule.eq_of_le_of_finrank_le LinearMap.map_le_range
      (by rw [hdim]; omega)
  rw [← hker]
  exact ⟨hdis, Submodule.map_eq_range_iff.mp heq⟩

end TauCeti.EisensteinSeries

namespace TauCeti

/-- At squarefree level, weight-two modular forms have dimension `τ(N) - 1` more than cusp
forms, where `τ(N)` is the number of positive divisors of `N`. -/
theorem finrank_weight_two_Gamma0_of_squarefree {N : ℕ} [NeZero N] (hN : Squarefree N) :
    Module.finrank ℂ (ModularForm ((Gamma0 N).map (mapGL ℝ)) 2) =
      Module.finrank ℂ (CuspForm ((Gamma0 N).map (mapGL ℝ)) 2) +
        (N.divisors.card - 1) := by
  have hdim := Submodule.finrank_add_eq_of_isCompl
    (TauCeti.EisensteinSeries.isCompl_span_correctedE2AtLevel_cuspFormSubmodule_of_squarefree
      hN).symm
  rw [TauCeti.EisensteinSeries.finrank_span_correctedE2AtLevel,
    ← (CuspForm.equivCuspFormSubmodule ((Gamma0 N).map (mapGL ℝ)) 2).finrank_eq] at hdim
  exact hdim.symm

end TauCeti

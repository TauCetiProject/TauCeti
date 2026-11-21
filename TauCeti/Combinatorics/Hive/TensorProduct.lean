/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Dimension.Finrank
public import TauCeti.Combinatorics.Hive.LittlewoodRichardson
public import TauCeti.RepresentationTheory.ClassicalGroups.WeylModule.Rational
import TauCeti.Combinatorics.Hive.GelfandTsetlin
import TauCeti.RepresentationTheory.ClassicalGroups.WeylModule.LittlewoodRichardson

/-!
# Hive multiplicities for `GLₙ(ℂ)` rational Weyl-module tensor products

Combining the signed hive–Littlewood–Richardson count
(`TauCeti.Hive.hiveCount_productBoundary_eq_ite_natCard_lrTableau`) with the rational Weyl-module
tensor-product rule (`TauCeti.finrank_hom_tprod_rationalWeylFDRep`), the multiplicity of `V_γ` in
`V_λ ⊗ V_μ` equals `hiveCount (productBoundary λ μ γ)`.

## Main results

* `TauCeti.Hive.finrank_hom_eq_hiveCount`: `GLₙ(ℂ)` tensor-product multiplicity equals
  `hiveCount (productBoundary λ μ γ)` for arbitrary dominant weights `λ, μ, γ`.
* `TauCeti.Hive.hiveCount_comm`: commutativity `c(λ, μ; γ) = c(μ, λ; γ)` deduced from symmetry of
  tensor products in `FDRep`.
* `TauCeti.Hive.finrank_hom_zero_eq_one`, `TauCeti.Hive.finrank_hom_one_eq_ite`,
  `TauCeti.Hive.finrank_hom_three_two_one_two_one_three_two_one`: concrete rank-`0`, rank-`1`,
  and multiplicity-`2` rank-`3` representation-theoretic checks.

## References

* A. Knutson and T. Tao, *The honeycomb model of $\mathrm{GL}_n(\mathbb{C})$ tensor products I:
  proof of the saturation conjecture*, J. Amer. Math. Soc. **12** (1999), 1055–1090.
-/

public section

open CategoryTheory MonoidalCategory

namespace TauCeti.Hive

/-! ### `GLₙ(ℂ)` tensor-product multiplicities and commutativity -/

section TensorMultiplicities

/-- **Hive tensor-product multiplicity theorem for `GLₙ(ℂ)`**: for arbitrary dominant weights
`λ, μ, γ` of `GLₙ(ℂ)`, the multiplicity of the irreducible rational Weyl module `V_γ` in
`V_λ ⊗ V_μ` equals `hiveCount (productBoundary λ μ γ)`. -/
theorem finrank_hom_eq_hiveCount {n : ℕ} (lam μ γ : DominantWeight n) :
    Module.finrank ℂ
        (rationalWeylFDRep ℂ n γ ⟶ rationalWeylFDRep ℂ n lam ⊗ rationalWeylFDRep ℂ n μ) =
      hiveCount (productBoundary lam μ γ) := by
  rw [finrank_hom_tprod_rationalWeylFDRep, hiveCount_productBoundary_eq_ite_natCard_lrTableau]

/-- **Commutativity of Littlewood–Richardson hive counts**:
`hiveCount (productBoundary λ μ γ) = hiveCount (productBoundary μ λ γ)`. -/
theorem hiveCount_comm {n : ℕ} (lam μ γ : DominantWeight n) :
    hiveCount (productBoundary lam μ γ) = hiveCount (productBoundary μ lam γ) := by
  rw [← finrank_hom_eq_hiveCount, ← finrank_hom_eq_hiveCount]
  let e₁ := FDRep.homLinearEquiv (rationalWeylFDRep ℂ n γ)
    (rationalWeylFDRep ℂ n lam ⊗ rationalWeylFDRep ℂ n μ)
  let e₂ := Representation.Equiv.intertwiningMapCongr
    (Representation.Equiv.refl (rationalWeylRep ℂ n γ))
    (Representation.TensorProduct.comm (rationalWeylRep ℂ n lam) (rationalWeylRep ℂ n μ))
  let e₃ := (FDRep.homLinearEquiv (rationalWeylFDRep ℂ n γ)
    (rationalWeylFDRep ℂ n μ ⊗ rationalWeylFDRep ℂ n lam)).symm
  exact (e₁ ≪≫ₗ e₂ ≪≫ₗ e₃).finrank_eq

end TensorMultiplicities

/-! ### Concrete `GLₙ(ℂ)` multiplicity checks at ranks `0`, `1`, and `3` -/

section ConcreteChecks

/-- Rank-`0` check: the unique trivial representation has tensor multiplicity `1`. -/
theorem finrank_hom_zero_eq_one (lam μ γ : DominantWeight 0) :
    Module.finrank ℂ
        (rationalWeylFDRep ℂ 0 γ ⟶ rationalWeylFDRep ℂ 0 lam ⊗ rationalWeylFDRep ℂ 0 μ) = 1 := by
  rw [finrank_hom_eq_hiveCount, hiveCount_rank_zero]

/-- Rank-`1` `GL₁(ℂ)` tensor-product check via `finrank_hom_eq_hiveCount`. -/
theorem finrank_hom_one_eq_ite (lam μ γ : DominantWeight 1) :
    Module.finrank ℂ
        (rationalWeylFDRep ℂ 1 γ ⟶ rationalWeylFDRep ℂ 1 lam ⊗ rationalWeylFDRep ℂ 1 μ) =
      if lam.val 0 + μ.val 0 = γ.val 0 then 1 else 0 := by
  rw [finrank_hom_eq_hiveCount, hiveCount_one_productBoundary]

/-- `GL₃(ℂ)` multiplicity-`2` check: `V_{(2, 1, 0)} ⊗ V_{(2, 1, 0)}` contains two copies of
`V_{(3, 2, 1)}`. -/
theorem finrank_hom_three_two_one_two_one_three_two_one :
    Module.finrank ℂ
        (rationalWeylFDRep ℂ 3 ⟨![3, 2, 1], by decide⟩ ⟶
          rationalWeylFDRep ℂ 3 ⟨![2, 1, 0], by decide⟩ ⊗
            rationalWeylFDRep ℂ 3 ⟨![2, 1, 0], by decide⟩) = 2 := by
  rw [finrank_hom_eq_hiveCount, hiveCount_three_two_one_two_one_three_two_one]

end ConcreteChecks

end TauCeti.Hive

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Height.Twisted.Weight.Supermodular
public import Mathlib.Algebra.BigOperators.Finprod

/-!
# Global weights of subspaces

The weight of a subspace is the finite sum of its local weights over an arbitrary
index type of places. Finite support of the form weights guarantees finite support
of the local contributions. The index type need not carry arithmetic structure:
these constructions depend only on finite families of linear forms.
For spanning local systems with finitely supported weights, the global weight is
supermodular on the lattice of subspaces.

## References

* J.-H. Evertse and R. G. Ferretti, *A further improvement of the Quantitative
  Subspace Theorem*, §15, (15.3) and Lemma 15.1.
-/

public noncomputable section

open Function Module Submodule Set

namespace TauCeti

variable {K V ι Ω : Type*} [Field K] [AddCommGroup V] [Module K V] [Fintype ι]

/-- The sum over places of the minimum weights of restricted dual bases.
As for `finsum`, the value is zero when the local contributions have infinite support. -/
def weight (L : Ω → ι → Module.Dual K V) (c : Ω → ι → ℝ)
    (U : Submodule K V) : ℝ :=
  ∑ᶠ v, localWeight (L v) (c v) U

/-- The global weight is the finite sum of its local contributions. -/
theorem weight_def (L : Ω → ι → Module.Dual K V) (c : Ω → ι → ℝ)
    (U : Submodule K V) : weight L c U = ∑ᶠ v, localWeight (L v) (c v) U :=
  (rfl)

/-- A local contribution can be nonzero only at a place with nonzero form weights. -/
theorem support_localWeight_subset (L : Ω → ι → Module.Dual K V) (c : Ω → ι → ℝ)
    (U : Submodule K V) :
    support (fun v ↦ localWeight (L v) (c v) U) ⊆ support c := by
  intro v hv hc
  exact hv (by simpa only [hc] using localWeight_zero (L v) U)

/-- Finite support of the form weights gives finite support of the local contributions. -/
theorem hasFiniteSupport_localWeight (L : Ω → ι → Module.Dual K V)
    {c : Ω → ι → ℝ} (hc : HasFiniteSupport c) (U : Submodule K V) :
    HasFiniteSupport (fun v ↦ localWeight (L v) (c v) U) :=
  hc.subset (support_localWeight_subset L c U)

/-- The global weight can be computed on any finite set containing the form-weight support. -/
theorem weight_eq_sum_of_support_subset (L : Ω → ι → Module.Dual K V)
    (c : Ω → ι → ℝ) (U : Submodule K V) {s : Finset Ω}
    (hc : support c ⊆ (s : Set Ω)) :
    weight L c U = ∑ v ∈ s, localWeight (L v) (c v) U := by
  rw [weight_def]
  exact finsum_eq_sum_of_support_subset _ ((support_localWeight_subset L c U).trans hc)

/-- Zero form weights give zero global weight. -/
@[simp]
theorem weight_zero (L : Ω → ι → Module.Dual K V) (U : Submodule K V) :
    weight L 0 U = 0 := by
  simp [weight_def]

/-- The zero subspace has global weight zero. -/
@[simp]
theorem weight_bot (L : Ω → ι → Module.Dual K V) (c : Ω → ι → ℝ) :
    weight L c (⊥ : Submodule K V) = 0 := by
  simp [weight_def]

/-- For independent spanning local forms, the whole space has the sum of all form weights. -/
@[simp]
theorem weight_top {L : Ω → ι → Module.Dual K V}
    (hLi : ∀ v, LinearIndependent K (L v)) (hL : ∀ v, span K (range (L v)) = ⊤)
    (c : Ω → ι → ℝ) :
    weight L c (⊤ : Submodule K V) = ∑ᶠ v, ∑ i, c v i := by
  simp [weight_def, localWeight_top, hLi, hL]

/-- The global weight is supermodular for spanning local systems with finitely supported weights. -/
theorem weight_inf_add_weight_sup {L : Ω → ι → Module.Dual K V}
    (hL : ∀ v, span K (range (L v)) = ⊤) {c : Ω → ι → ℝ}
    (hc : HasFiniteSupport c) (U W : Submodule K V) :
    weight L c U + weight L c W ≤ weight L c (U ⊓ W) + weight L c (U ⊔ W) := by
  classical
  have hsum (A : Submodule K V) :=
    weight_eq_sum_of_support_subset L c A hc.coe_toFinset.ge
  simp only [hsum, ← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun v _ ↦ localWeight_inf_add_localWeight_sup (hL v) (c v) U W

end TauCeti

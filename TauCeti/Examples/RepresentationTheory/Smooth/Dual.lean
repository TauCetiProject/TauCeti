/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Smooth.Dual
public import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.LinearAlgebra.Dimension.Finite

/-!
# Examples of smooth duals

The smooth dual of the zero representation is zero, and the smooth dual of a trivial
representation, or of a smooth representation on a finitely generated module such as `A[G ⧸ U]`
for an open subgroup `U` of finite index, is the whole algebraic dual.

For `G = ℚ_[p]` and `V = ℚ[ℚ_[p] ⧸ ℤ_[p]]`, the open subgroup `ℤ_[p]` acts trivially, so every
linear form on `V` and on its smooth dual is smooth. Since `ℚ_[p] ⧸ ℤ_[p]` is infinite, `V` is
infinite-dimensional and the evaluation map `V → V^∨∨` is not surjective.
-/

public section

open Module Representation

namespace TauCeti

variable {A G V : Type*} [CommRing A] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [AddCommGroup V] [Module A V]

/-- The smooth dual of the zero representation is zero. -/
example (ρ : Representation A G PUnit) : Subsingleton ρ.dual.smoothVectors.toSubmodule :=
  inferInstance

/-- The smooth dual of a trivial representation is the whole dual. -/
example : (trivial A G V).dual.smoothVectors = ⊤ :=
  smoothVectors_dual_eq_top_of_isTrivial

/-- The smooth dual of `A[G ⧸ U]` for an open subgroup `U` of finite index is the whole dual. -/
example (U : OpenSubgroup G) [Finite (G ⧸ (U : Subgroup G))] :
    (ofMulAction A G (G ⧸ (U : Subgroup G))).dual.smoothVectors = ⊤ :=
  smoothVectors_dual_eq_top

/-- Evaluation into the double smooth dual is `v ↦ (λ ↦ λ v)`. -/
example (ρ : Representation A G V) [IsSmooth ρ] (v : V) (f : ρ.dual.smoothVectors.toSubmodule) :
    (ρ.smoothDualEval v : Dual A _) f = (f : Dual A V) v := by
  simp

/-! ### The representation `ℚ[ℚ_[p] ⧸ ℤ_[p]]` -/

section Padic

variable (p : ℕ) [Fact p.Prime]

/-- The `p`-adic integers `ℤ_[p]` as an open subgroup of the additive group of `ℚ_[p]`, written
multiplicatively. -/
noncomputable def padicIntOpenSubgroup : OpenSubgroup (Multiplicative ℚ_[p]) where
  toSubgroup := AddSubgroup.toSubgroup (PadicInt.subring p).toAddSubgroup
  isOpen' := by
    have := IsUltrametricDist.isOpen_closedBall (0 : ℚ_[p]) one_ne_zero
    exact (by simpa [Metric.closedBall, dist_eq_norm_sub] using this :
      IsOpen {y : ℚ_[p] | ‖y‖ ≤ 1})

/-- The quotient `ℚ_[p] ⧸ ℤ_[p]`, written multiplicatively. -/
abbrev PadicQuotient : Type :=
  Multiplicative ℚ_[p] ⧸ (padicIntOpenSubgroup p : Subgroup (Multiplicative ℚ_[p]))

theorem mem_padicIntOpenSubgroup_iff {x : Multiplicative ℚ_[p]} :
    x ∈ padicIntOpenSubgroup p ↔ ‖x.toAdd‖ ≤ 1 :=
  Iff.rfl

/-- The open subgroup `ℤ_[p]` fixes every point of `ℚ_[p] ⧸ ℤ_[p]`. -/
theorem smul_eq_of_mem_padicIntOpenSubgroup {g : Multiplicative ℚ_[p]}
    (hg : g ∈ padicIntOpenSubgroup p)
    (x : PadicQuotient p) :
    g • x = x := by
  induction x using QuotientGroup.induction_on with | H y =>
  change ((g * y : Multiplicative ℚ_[p]) : PadicQuotient p) = (y : PadicQuotient p)
  rw [QuotientGroup.eq, mul_inv_rev, mul_comm, ← mul_assoc, mul_inv_cancel, one_mul]
  exact inv_mem hg

/-- The quotient `ℚ_[p] ⧸ ℤ_[p]` is infinite: the classes of `p⁻ⁿ` are pairwise distinct. -/
theorem infinite_quotient_padicIntOpenSubgroup :
    Infinite (PadicQuotient p) := by
  have hp : (1 : ℝ) < p := mod_cast (Fact.out : p.Prime).one_lt
  refine Infinite.of_injective
    (fun n : ℕ ↦ ((Multiplicative.ofAdd ((p : ℚ_[p]) ^ (-(n : ℤ))) : Multiplicative ℚ_[p]) :
      PadicQuotient p)) fun n m h ↦ ?_
  by_contra hnm
  rw [QuotientGroup.eq] at h
  have h' : ‖-(p : ℚ_[p]) ^ (-(n : ℤ)) + (p : ℚ_[p]) ^ (-(m : ℤ))‖ ≤ 1 := h
  have hne : (p : ℝ) ^ (n : ℤ) ≠ (p : ℝ) ^ (m : ℤ) := fun he ↦
    hnm (by exact_mod_cast zpow_right_injective₀ (by positivity) hp.ne' he)
  rw [Padic.add_eq_max_of_ne (by simpa [Padic.norm_p_zpow] using hne), norm_neg,
    Padic.norm_p_zpow, Padic.norm_p_zpow, neg_neg, neg_neg] at h'
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact (one_lt_zpow₀ hp (by omega : (0 : ℤ) < m)).not_ge
      ((le_max_right _ _).trans h')
  · exact (one_lt_zpow₀ hp (by omega : (0 : ℤ) < n)).not_ge ((le_max_left _ _).trans h')

/-- **The evaluation map to the double smooth dual need not be surjective.** For `G = ℚ_[p]` and
`V = ℚ[ℚ_[p] ⧸ ℤ_[p]]`, the evaluation map `V → V^∨∨` is not surjective. -/
theorem not_surjective_smoothDualEval_padic :
    ¬Function.Surjective
      (smoothDualEval (ofMulAction ℚ (Multiplicative ℚ_[p]) (PadicQuotient p))) := by
  have hfix (v) : (padicIntOpenSubgroup p : Subgroup (Multiplicative ℚ_[p])) ≤
      (ofMulAction ℚ (Multiplicative ℚ_[p]) (PadicQuotient p)).stabilizer v := by
    intro g hg
    induction v using MonoidAlgebra.induction_linear with
    | zero => exact mem_stabilizer.2 (map_zero _)
    | add f₁ f₂ h₁ h₂ =>
      exact mem_stabilizer.2 (by rw [map_add, mem_stabilizer.1 h₁, mem_stabilizer.1 h₂])
    | single x r =>
      exact mem_stabilizer.2 (by rw [ofMulAction_single, smul_eq_of_mem_padicIntOpenSubgroup p hg])
  rw [smoothDualEval_surjective_iff (padicIntOpenSubgroup p).isOpen hfix]
  intro h
  have hfin : Module.Finite ℚ (PadicQuotient p →₀ ℚ) :=
    Module.Finite.equiv (MonoidAlgebra.coeffLinearEquiv ℚ)
  have := infinite_quotient_padicIntOpenSubgroup p
  rcases Module.finite_finsupp_self_iff.1 hfin with h | h
  · exact (not_subsingleton ℚ) h
  · exact not_finite (PadicQuotient p)

end Padic

end TauCeti

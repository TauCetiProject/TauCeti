/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.NovikovModule.Basic
public import TauCeti.Topology.Algebra.Torsor.DiscretePeriod

/-!
# Completed combinations of fixed degree and discrete degree-zero periods

Let the generators be a finite union `Σ k, P k` of torsors under an additive group `H`, with a
potential `F` and a degree `d` shifted by translations through homomorphisms `N : H →+ ℝ` and
`δ : H →+ D`:

`F (h +ᵥ p) = N h + F p`,  `d (h +ᵥ p) = δ h + d p`.

Assume that `N` and `δ` are jointly injective, `Disjoint N.ker δ.ker`. When is a coefficient
function supported in a single degree, with potential bounded above on its support, a completed
combination (an element of `TauCeti.NovikovModule`)? The answer depends only on the subgroup
`N (ker δ)` of `ℝ`, the *degree-zero periods*, and every subgroup of `ℝ` is either discrete or
dense (`AddSubgroup.dense_or_isCyclic`, `AddSubgroup.isAddCyclic_iff_discreteTopology`).

* If the degree-zero periods are discrete, only finitely many generators of a given degree have
  potential in a bounded window (`TauCeti.AddTorsor.finite_setOf_sigma_eq_and_mem_Icc`, in
  `TauCeti.Topology.Algebra.Torsor.DiscretePeriod`). Hence
  every coefficient function of fixed degree with potential bounded above is a completed
  combination (`TauCeti.NovikovModule.mem_of_forall_eq_and_le`). In particular a kernel obeying a
  potential bound and a fixed degree shift has completed rows
  (`TauCeti.NovikovModule.mem_of_le_add_of_eq_add`,
  `TauCeti.NovikovModule.mem_of_le_add_add_of_eq_add_add`): these are the hypotheses `hmfin` of
  `TauCeti.NovikovModule.kernelMap` and `hfin` of `TauCeti.NovikovModule.kernelProduct`.
* If the degree-zero periods are dense, every generator `p` has infinitely many translates of the
  same degree with potential in `(F p - 1, F p)`, and their indicator is a coefficient function of
  fixed degree with potential bounded above that is not a completed combination
  (`TauCeti.NovikovModule.exists_notMem_of_dense`).

`TauCeti.NovikovModule.forall_mem_iff_discreteTopology` combines the two. The case of an injective
`δ`, where the degree-zero periods are trivial, is treated with finite supports in
`TauCeti.RingTheory.NovikovModule.InjectiveGrading`.

In capped Hamiltonian Floer theory `H` is the period group, `F` is the action, `δ` is twice the
first Chern number and `N` is the symplectic area. The energy bound and the fixed index of a
kernel alone guarantee completed rows, for every choice of counts, exactly when the areas of the
Chern-zero spherical classes form a discrete subgroup of `ℝ`. When they are dense, some kernels
obeying the energy bound and the index fail to have completed rows, so for a geometric kernel the
finiteness of the counts below each energy level must come from compactness.

## References

* H. Hofer and D. A. Salamon, *Floer homology and Novikov rings*, in *The Floer memorial
  volume*, Progr. Math. 133 (1995), 483–524.
-/

public section

namespace TauCeti

open Function Set

variable {H D : Type*} [AddGroup H] [AddGroup D] {N : H →+ ℝ} {δ : H →+ D}

namespace NovikovModule

variable {R : Type*} [Semiring R] {ι₀ : Type*} {P₀ : ι₀ → Type*} [∀ k, AddTorsor H (P₀ k)]
  {F₀ : (Σ k, P₀ k) → ℝ} {d₀ : (Σ k, P₀ k) → D}

section Discrete

variable [Finite ι₀] (hF₀ : ∀ k (h : H) (p : P₀ k), F₀ ⟨k, h +ᵥ p⟩ = N h + F₀ ⟨k, p⟩)
  (hd₀ : ∀ k (h : H) (p : P₀ k), d₀ ⟨k, h +ᵥ p⟩ = δ h + d₀ ⟨k, p⟩) (hNδ : Disjoint N.ker δ.ker)
  (hdisc : DiscreteTopology (δ.ker.map N))
include hF₀ hd₀ hNδ hdisc

/-- With discrete degree-zero periods, a coefficient function supported in a single degree `e`,
with potential at most `U` on its support, is a completed combination. -/
theorem mem_of_forall_eq_and_le {a : (Σ k, P₀ k) → R} {e : D} {U : ℝ}
    (ha : ∀ p, a p ≠ 0 → d₀ p = e ∧ F₀ p ≤ U) : a ∈ NovikovModule R F₀ :=
  mem_iff.2 fun C => (AddTorsor.finite_setOf_sigma_eq_and_mem_Icc hF₀ hd₀ hNδ hdisc e C U).subset
    fun p hp => ⟨(ha p hp.1).1, hp.2.le, (ha p hp.1).2⟩

/-- With discrete degree-zero periods, a kernel with a potential bound `F₀ p₀ ≤ F₁ p₁ + C` and a
fixed degree shift `ε` has completed rows. This is the hypothesis `hmfin` of
`TauCeti.NovikovModule.kernelMap`. -/
theorem mem_of_le_add_of_eq_add {S₁ : Type*} {F₁ : S₁ → ℝ} {d₁ : S₁ → D} {C : ℝ} {ε : D}
    {m : S₁ → (Σ k, P₀ k) → R} (hm : ∀ p₁ p₀, m p₁ p₀ ≠ 0 → F₀ p₀ ≤ F₁ p₁ + C)
    (hmd : ∀ p₁ p₀, m p₁ p₀ ≠ 0 → d₀ p₀ = d₁ p₁ + ε) (p₁ : S₁) : m p₁ ∈ NovikovModule R F₀ :=
  mem_of_forall_eq_and_le hF₀ hd₀ hNδ hdisc fun p₀ h => ⟨hmd p₁ p₀ h, hm p₁ p₀ h⟩

/-- With discrete degree-zero periods, a product kernel with a potential bound
`F₀ p₀ ≤ F₁ p₁ + F₂ p₂ + C` and a fixed degree shift `ε` has completed rows. This is the
hypothesis `hfin` of `TauCeti.NovikovModule.kernelProduct`. -/
theorem mem_of_le_add_add_of_eq_add_add {S₁ S₂ : Type*} {F₁ : S₁ → ℝ} {F₂ : S₂ → ℝ}
    {d₁ : S₁ → D} {d₂ : S₂ → D} {C : ℝ} {ε : D} {n : S₁ → S₂ → (Σ k, P₀ k) → R}
    (hn : ∀ p₁ p₂ p₀, n p₁ p₂ p₀ ≠ 0 → F₀ p₀ ≤ F₁ p₁ + F₂ p₂ + C)
    (hnd : ∀ p₁ p₂ p₀, n p₁ p₂ p₀ ≠ 0 → d₀ p₀ = d₁ p₁ + d₂ p₂ + ε) (p₁ : S₁) (p₂ : S₂) :
    n p₁ p₂ ∈ NovikovModule R F₀ :=
  mem_of_forall_eq_and_le hF₀ hd₀ hNδ hdisc fun p₀ h => ⟨hnd p₁ p₂ p₀ h, hn p₁ p₂ p₀ h⟩

end Discrete

/-- With dense degree-zero periods, every generator `p` carries a coefficient function supported
in the degree of `p`, with potential at most that of `p`, which is not a completed combination:
the indicator of the infinitely many translates of `p` of the same degree with potential in
`(F₀ p - 1, F₀ p)`. -/
theorem exists_notMem_of_dense [Nontrivial R]
    (hF₀ : ∀ k (h : H) (p : P₀ k), F₀ ⟨k, h +ᵥ p⟩ = N h + F₀ ⟨k, p⟩)
    (hd₀ : ∀ k (h : H) (p : P₀ k), d₀ ⟨k, h +ᵥ p⟩ = δ h + d₀ ⟨k, p⟩)
    (hdense : Dense ((δ.ker.map N : AddSubgroup ℝ) : Set ℝ)) (p : Σ k, P₀ k) :
    ∃ a : (Σ k, P₀ k) → R, (∀ q, a q ≠ 0 → d₀ q = d₀ p ∧ F₀ q ≤ F₀ p) ∧
      a ∉ NovikovModule R F₀ := by
  let T : Set (Σ k, P₀ k) :=
    (fun h => (⟨p.1, h +ᵥ p.2⟩ : Σ k, P₀ k)) '' {h : H | δ h = 0 ∧ N h ∈ Ioo (-1) 0}
  have hT : ∀ q ∈ T, d₀ q = d₀ p ∧ F₀ p - 1 < F₀ q ∧ F₀ q ≤ F₀ p := by
    rintro _ ⟨h, ⟨hδ, hN⟩, rfl⟩
    refine ⟨by rw [hd₀, hδ, zero_add], ?_, ?_⟩ <;> rw [hF₀] <;> linarith [hN.1, hN.2]
  refine ⟨T.indicator 1, fun q hq => ?_, fun hmem => ?_⟩
  · obtain ⟨hdq, -, hFq⟩ := hT q (mem_of_indicator_ne_zero hq)
    exact ⟨hdq, hFq⟩
  · refine ((AddTorsor.infinite_setOf_eq_zero_and_mem_Ioo hdense (neg_one_lt_zero)).image
      fun h _ h' _ hh => vadd_right_cancel p.2 (eq_of_heq (Sigma.mk.inj hh).2)).mono ?_
      (mem_iff.1 hmem (F₀ p - 1))
    intro q hq
    have hqT : q ∈ T := hq
    exact ⟨by rw [indicator_of_mem hqT]; exact one_ne_zero, (hT q hqT).2.1⟩

/-- On a nonempty finite union of torsors with jointly injective period and degree shifts, every
coefficient function of fixed degree with potential bounded above on its support is a completed
combination exactly when the degree-zero periods `N (ker δ)` form a discrete subgroup of `ℝ`. -/
theorem forall_mem_iff_discreteTopology [Nontrivial R] [Finite ι₀] [Nonempty ι₀]
    (hF₀ : ∀ k (h : H) (p : P₀ k), F₀ ⟨k, h +ᵥ p⟩ = N h + F₀ ⟨k, p⟩)
    (hd₀ : ∀ k (h : H) (p : P₀ k), d₀ ⟨k, h +ᵥ p⟩ = δ h + d₀ ⟨k, p⟩)
    (hNδ : Disjoint N.ker δ.ker) :
    (∀ (a : (Σ k, P₀ k) → R) (e : D) (U : ℝ), (∀ p, a p ≠ 0 → d₀ p = e ∧ F₀ p ≤ U) →
      a ∈ NovikovModule R F₀) ↔ DiscreteTopology (δ.ker.map N) := by
  refine ⟨fun h => ?_, fun hdisc a e U ha => mem_of_forall_eq_and_le hF₀ hd₀ hNδ hdisc ha⟩
  rw [← AddSubgroup.isAddCyclic_iff_discreteTopology]
  refine (AddSubgroup.dense_or_isCyclic _).resolve_left fun hdense => ?_
  let k := Classical.arbitrary ι₀
  obtain ⟨a, ha, hna⟩ := exists_notMem_of_dense (R := R) hF₀ hd₀ hdense
    ⟨k, Classical.arbitrary (P₀ k)⟩
  exact hna (h a _ _ ha)

end NovikovModule

end TauCeti

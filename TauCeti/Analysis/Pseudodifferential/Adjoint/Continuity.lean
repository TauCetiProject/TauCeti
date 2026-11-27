/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Pseudodifferential.Adjoint.Expansion

/-!
# Continuity of the adjoint symbol and of the remainders of its expansion

Let `a` be a symbol of order `m` that vanishes at positions outside a fixed compact set `K`, with
values in operators between complex Hilbert spaces. This file proves that the adjoint symbol `a*`
(`TauCeti.Symbol.adjoint`), whose quantization is the formal adjoint of the quantization of `a`,
depends continuously on `a` in the seminorm topologies of the symbol classes
(`TauCeti.Symbol.instTopologicalSpace`), and so do the remainders
`R_N(a) = a* - ∑_{k < N} adjointTerm a k` of its asymptotic expansion
(`TauCeti.Symbol.adjointRemainder`), in the class of order `m - N`:

* `Continuous.symbol_adjoint`: a continuous family `t ↦ a t` of symbols, all vanishing outside one
  compact set, has a continuous family `t ↦ (a t)*` of adjoint symbols;
* `Continuous.symbol_adjointRemainder`: for every `N`, the remainders `t ↦ R_N(a t)` form a
  continuous family of symbols of order `m - N`.

Continuity of the remainders in the class of order `m - N` does not follow from that of `a*` and of
the finitely many terms, which only gives continuity in the class of order `m`. It rests on the
seminorm estimate `p_{L,α,β}(R_N(a)) ≤ C ∑ᵢ p_{K,αᵢ,βᵢ}(a)` of
`TauCeti.Symbol.exists_seminorm_adjointRemainder_le`, whose case `N = 0` is the estimate
`TauCeti.Symbol.exists_seminorm_adjoint_le` for `a*`, together with the additivity of the adjoint
symbol and of the remainders (`TauCeti.Symbol.adjoint_sub`, `TauCeti.Symbol.adjointRemainder_sub`).
Continuous families of symbols arise as homotopies of symbols and as parameter-dependent symbols;
these statements let them pass to the formal adjoints of the corresponding pseudodifferential
operators, with every truncation of the adjoint expansion.

## References

* L. Hörmander, *The Analysis of Linear Partial Differential Operators III*, Theorem 18.1.7.
* M. Taylor, *Pseudodifferential Operators: Four Lectures at MSRI* (2008), Lecture I, (2.3).
-/

public section

noncomputable section

open Filter Topology
open TopologicalSpace (Compacts)

namespace TauCeti

namespace Symbol

variable {n : ℕ} {m m' : ℝ} {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  [CompleteSpace V] [NormedAddCommGroup W] [InnerProductSpace ℂ W] [CompleteSpace W]

omit [CompleteSpace V] [CompleteSpace W] in
/-- A family `t ↦ F t` of symbols is continuous if every seminorm of `F t - F t₀` is at most a
constant times finitely many seminorms on `K` of `a t - a t₀`, for a continuous family `a`. -/
private theorem continuous_of_seminorm_sub_le {X : Type*} [TopologicalSpace X]
    {a : X → Symbol n V W m} (ha : Continuous a) (K : Compacts (CoordinateSpace n))
    {F : X → Symbol n W V m'}
    (hF : ∀ (L : Compacts (CoordinateSpace n)) (α β : List (Fin n)),
      ∃ (s : Finset (List (Fin n) × List (Fin n))) (C : ℝ), ∀ t t₀,
        Symbol.seminorm L α β (F t - F t₀) ≤ C * ∑ i ∈ s, Symbol.seminorm K i.1 i.2 (a t - a t₀)) :
    Continuous F := by
  refine continuous_iff_continuousAt.2 fun t₀ ↦ ?_
  rw [ContinuousAt, withSeminorms.tendsto_nhds]
  rintro ⟨L, α, β⟩ ε hε
  obtain ⟨s, C, hC⟩ := hF L α β
  have ha' (i : List (Fin n) × List (Fin n)) :
      Tendsto (fun t ↦ Symbol.seminorm K i.1 i.2 (a t - a t₀)) (𝓝 t₀) (𝓝 0) := by
    simpa only [Function.comp_def, seminormFamily_apply] using
      ((withSeminorms.continuous_seminorm (K, i.1, i.2)).comp
        (show Continuous fun t ↦ a t - a t₀ from ha.sub continuous_const)).tendsto' t₀ 0
        (by simp)
  have hP : Tendsto (fun t ↦ C * ∑ i ∈ s, Symbol.seminorm K i.1 i.2 (a t - a t₀)) (𝓝 t₀)
      (𝓝 0) := by
    simpa using (tendsto_finsetSum s fun i _ ↦ ha' i).const_mul C
  have key : Tendsto (fun t ↦ Symbol.seminorm L α β (F t - F t₀)) (𝓝 t₀) (𝓝 0) :=
    squeeze_zero (fun _ ↦ apply_nonneg _ _) (fun t ↦ hC t t₀) hP
  simpa only [seminormFamily_apply] using (tendsto_order.1 key).2 ε hε

/-- **Continuity of the adjoint symbol.** If `t ↦ a t` is a continuous family of symbols of order
`m`, all vanishing at positions outside one compact set `K`, then `t ↦ (a t)*` is a continuous
family of symbols of order `m`. -/
theorem _root_.Continuous.symbol_adjoint {X : Type*} [TopologicalSpace X]
    {a : X → Symbol n V W m} (ha : Continuous a) {K : Set (CoordinateSpace n)} (hK : IsCompact K)
    (haK : ∀ t, ∀ x ∉ K, ∀ ξ, (a t).coefficient (x, ξ) = 0) :
    Continuous fun t ↦ adjoint (a t) (hasCompactSpatialSupport_iff.2 ⟨K, hK, haK t⟩) := by
  refine continuous_of_seminorm_sub_le ha ⟨K, hK⟩ fun L α β ↦ ?_
  obtain ⟨s, C, -, hC⟩ := exists_seminorm_adjoint_le (V := V) (W := W) (m := m) ⟨K, hK⟩ L α β
  refine ⟨s, C, fun t t₀ ↦ ?_⟩
  rw [← adjoint_sub]
  exact hC _ _ fun x hx ξ ↦ by simp [haK t x hx ξ, haK t₀ x hx ξ]

/-- **Continuity of the remainders of the adjoint expansion.** If `t ↦ a t` is a continuous family
of symbols of order `m`, all vanishing at positions outside one compact set `K`, then for every `N`
the remainders `t ↦ (a t)* - ∑_{k < N} adjointTerm (a t) k` form a continuous family of symbols of
order `m - N`. -/
theorem _root_.Continuous.symbol_adjointRemainder {X : Type*} [TopologicalSpace X]
    {a : X → Symbol n V W m} (ha : Continuous a) {K : Set (CoordinateSpace n)} (hK : IsCompact K)
    (haK : ∀ t, ∀ x ∉ K, ∀ ξ, (a t).coefficient (x, ξ) = 0) (N : ℕ) :
    Continuous fun t ↦
      (a t).adjointRemainder (hasCompactSpatialSupport_iff.2 ⟨K, hK, haK t⟩) N := by
  refine continuous_of_seminorm_sub_le ha ⟨K, hK⟩ fun L α β ↦ ?_
  obtain ⟨s, C, -, hC⟩ :=
    exists_seminorm_adjointRemainder_le (V := V) (W := W) (m := m) ⟨K, hK⟩ L N α β
  refine ⟨s, C, fun t t₀ ↦ ?_⟩
  rw [← adjointRemainder_sub]
  exact hC _ _ fun x hx ξ ↦ by simp [haK t x hx ξ, haK t₀ x hx ξ]

end Symbol

end TauCeti

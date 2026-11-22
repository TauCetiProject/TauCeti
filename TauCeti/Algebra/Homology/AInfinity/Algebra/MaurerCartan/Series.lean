/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.InfiniteSum.NatInt
public import TauCeti.Algebra.Homology.AInfinity.Algebra.MaurerCartan
public import TauCeti.Topology.Algebra.Nonarchimedean.EnergyFiltration
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Order.Filter.AtTopBot.Archimedean
import Mathlib.Order.Filter.AtTopBot.Field

/-!
# The convergent Maurer–Cartan series of a filtered `A∞` algebra

For an `A∞` algebra with operations `mₙ`, the **Maurer–Cartan series** of an element `α` is

`∑_{n ≥ 0} (-1)^{n(n-1)/2} mₙ(α, …, α)`

(`TauCeti.AInfinityAlgebra.maurerCartanSeries`), whose partial sums are the truncated sums
`TauCeti.AInfinityAlgebra.maurerCartanSum`. Two regimes give it a meaning.

* In the arity-nilpotent regime of `TauCeti.AInfinityAlgebra.IsMaurerCartan`, only finitely many
  terms are nonzero and the series is the truncated sum at any arity bound
  (`TauCeti.AInfinityAlgebra.maurerCartanSeries_eq_maurerCartanSum`). The Maurer–Cartan equation
  is then the vanishing of the series
  (`TauCeti.AInfinityAlgebra.isMaurerCartan_iff_maurerCartanSeries_eq_zero`).
* In the complete filtered regime, the carrier is complete for an energy filtration `F`
  (`TauCeti.IsEnergyFiltration`), every operation satisfies the nonnegative energy bound
  `ν(mₙ(a₁, …, aₙ)) ≥ ν(a₁) + ⋯ + ν(aₙ)`, and `α` has positive energy. Then the `n`-th term has
  energy at least `n ν(α)`, so the series converges
  (`TauCeti.AInfinityAlgebra.hasSum_maurerCartanSeries`), its truncated sums converge to it
  (`TauCeti.AInfinityAlgebra.tendsto_maurerCartanSum`), and it has energy at least that of `α`
  (`TauCeti.AInfinityAlgebra.maurerCartanSeries_mem`). This is the setting of bounding cochains in
  Lagrangian Floer theory, where the series is infinite.

For `α` of degree one, the sign `(-1)^{n(n-1)/2}` is the Koszul sign of the suspension, so the
series is the sign-free sum `∑_{n ≥ 1} b((sα)^{⊗n})` of the suspended Taylor map
(`TauCeti.AInfinityAlgebra.hasSum_taylor_of_tprod_const`). Informally, this is the nullary term
of inserting `sα` into the suspended operations, cf. `TauCeti.deformedOperation`.

## Main definitions

* `TauCeti.AInfinityAlgebra.maurerCartanSeries`: the Maurer–Cartan series of an element.

## Main results

* `TauCeti.AInfinityAlgebra.maurerCartanSeries_eq_maurerCartanSum` and
  `TauCeti.AInfinityAlgebra.isMaurerCartan_iff_maurerCartanSeries_eq_zero`: comparison with the
  arity-nilpotent theory.
* `TauCeti.AInfinityAlgebra.hasSum_maurerCartanSeries` and
  `TauCeti.AInfinityAlgebra.tendsto_maurerCartanSum`: convergence in the complete filtered regime.
* `TauCeti.AInfinityAlgebra.maurerCartanSeries_mem`: the series has energy at least that of `α`.
* `TauCeti.AInfinityAlgebra.hasSum_taylor_of_tprod_const`: the sign-free suspended form of the
  series.

## References

* K. Fukaya, Y.-G. Oh, H. Ohta and K. Ono, *Lagrangian intersection Floer theory: anomaly and
  obstruction, Part I*, AMS/IP Studies in Advanced Mathematics 46.1, 2009, Chapter 3.
* B. Keller, *Introduction to A-infinity algebras and modules*, Section 7.6, equation (7.1).
-/

public section

open Filter Finset Topology

namespace TauCeti

namespace AInfinityAlgebra

variable {R A : Type*} [CommRing R] [AddCommGroup A] [Module R A] (𝒜 : AInfinityAlgebra R A)

section TopologicalSpace

variable [TopologicalSpace A]

/-- The **Maurer–Cartan series** `∑_{n ≥ 0} (-1)^{n(n-1)/2} mₙ(α, …, α)` of `α`, whose partial
sums are the truncated sums `maurerCartanSum α N`. The arity-zero term vanishes since
`m 0 = 0`. -/
noncomputable def maurerCartanSeries (α : A) : A :=
  ∑' n, negOnePowCast R (n.choose 2) • 𝒜.m n fun _ ↦ α

theorem maurerCartanSeries_def (α : A) :
    𝒜.maurerCartanSeries α = ∑' n, negOnePowCast R (n.choose 2) • 𝒜.m n fun _ ↦ α :=
  (rfl)

variable {𝒜}

/-! ### The arity-nilpotent regime -/

/-- **The series is the truncated sum** at any arity bound beyond which `mₙ(α, …, α)` vanishes. -/
theorem maurerCartanSeries_eq_maurerCartanSum {α : A} {N : ℕ}
    (hN : ∀ n, N ≤ n → 𝒜.m n (fun _ ↦ α) = 0) :
    𝒜.maurerCartanSeries α = 𝒜.maurerCartanSum α N := by
  rw [maurerCartanSeries_def, maurerCartanSum_def]
  exact tsum_eq_sum fun n hn ↦ by rw [hN n (by simpa using hn), smul_zero]

/-- Given an arity bound for `α`, the element `α` is Maurer–Cartan exactly when it has degree one
and its Maurer–Cartan series vanishes. -/
theorem isMaurerCartan_iff_maurerCartanSeries_eq_zero {α : A} {N : ℕ}
    (hN : ∀ n, N ≤ n → 𝒜.m n (fun _ ↦ α) = 0) :
    𝒜.IsMaurerCartan α ↔ α ∈ 𝒜.grading.piece 1 ∧ 𝒜.maurerCartanSeries α = 0 := by
  rw [isMaurerCartan_iff hN, maurerCartanSeries_eq_maurerCartanSum hN]

end TopologicalSpace

/-! ### The complete filtered regime -/

variable {𝒜} {F : ℝ → AddSubgroup A}
  (hm : ∀ n, MultilinearMap.IsHomogeneous (𝒜.m n) (fun _ ↦ F) F 0) {δ : ℝ} {α : A}
  (hα : α ∈ F δ)
include hm hα

/-- The `n`-th term of the Maurer–Cartan series has energy at least `n` times the energy of
`α`. -/
private theorem maurerCartanTerm_mem (n : ℕ) :
    negOnePowCast R (n.choose 2) • 𝒜.m n (fun _ ↦ α) ∈ F (n * δ) :=
  negOnePowCast_smul_mem _ (by simpa using (hm n).map_mem (fun _ ↦ δ) (fun _ ↦ α) fun _ ↦ hα)

/-- **The Maurer–Cartan series has energy at least that of `α`** when `α` has nonnegative energy.
The series need not converge for this: a divergent series has sum `0`. -/
theorem maurerCartanSeries_mem [TopologicalSpace A] [IsTopologicalAddGroup A]
    (hF : IsEnergyFiltration F) (hδ : 0 ≤ δ) : 𝒜.maurerCartanSeries α ∈ F δ := by
  refine hF.tsum_mem fun n ↦ ?_
  rcases n with _ | n
  · simp [𝒜.m_zero]
  · refine hF.antitone ?_ (maurerCartanTerm_mem hm hα (n + 1))
    push_cast
    nlinarith

variable [UniformSpace A] [IsUniformAddGroup A] [CompleteSpace A] (hF : IsEnergyFiltration F)
  (hδ : 0 < δ)
include hF hδ

/-- **The Maurer–Cartan series converges** on a complete filtered `A∞` algebra whose operations
satisfy the nonnegative energy bound, for `α` of positive energy. -/
theorem hasSum_maurerCartanSeries :
    HasSum (fun n ↦ negOnePowCast R (n.choose 2) • 𝒜.m n fun _ ↦ α)
      (𝒜.maurerCartanSeries α) := by
  refine (hF.summable_of_mem (maurerCartanTerm_mem hm hα) ?_).hasSum
  rw [Nat.cofinite_eq_atTop]
  exact Tendsto.atTop_mul_const hδ tendsto_natCast_atTop_atTop

/-- **The truncated Maurer–Cartan sums converge to the series** on a complete filtered `A∞`
algebra, for `α` of positive energy. -/
theorem tendsto_maurerCartanSum :
    Tendsto (𝒜.maurerCartanSum α) atTop (𝓝 (𝒜.maurerCartanSeries α)) := by
  have h := (hasSum_maurerCartanSeries hm hα hF hδ).tendsto_sum_nat
  simp_rw [← maurerCartanSum_def] at h
  exact h

/-- **The suspended form of the series.** For `α` of degree one, the sign-free sum
`∑_{n ≥ 1} b((sα)^{⊗n})` of the suspended Taylor map converges to the Maurer–Cartan series, on a
complete filtered `A∞` algebra and for `α` of positive energy. -/
theorem hasSum_taylor_of_tprod_const (hα₁ : α ∈ 𝒜.grading.piece 1) :
    HasSum (fun n : ℕ ↦ 𝒜.taylor
        (ReducedTensorWords.of R A ⟨n + 1, n.succ_pos⟩ (PiTensorProduct.tprod R fun _ ↦ α)))
      (𝒜.maurerCartanSeries α) := by
  have h := (hasSum_nat_add_iff' 1).2 (hasSum_maurerCartanSeries hm hα hF hδ)
  simp only [range_one, sum_singleton, 𝒜.m_zero, zero_apply, smul_zero,
    sub_zero] at h
  simpa only [𝒜.taylor_of_tprod_const hα₁] using h

end AInfinityAlgebra

end TauCeti

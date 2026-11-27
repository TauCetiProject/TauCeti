/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.Torsion.Basic
public import TauCeti.RingTheory.AdicCompletion.DerivedComplete.Module
import Mathlib.Topology.Baire.CompleteMetrizable
import Mathlib.Topology.MetricSpace.PiNat

/-!
# Torsion derived complete modules are bounded

Let `f` be an element of an ideal `I` of a commutative ring `R`, and `M` a derived `I`-complete
module in which every element is killed by some power of `f`. Then a single power of `f` kills
all of `M` (`TauCeti.IsDerivedComplete.exists_isTorsionBy_pow`). This is the principal case of
Bhatt's theorem that torsion derived complete modules are bounded. Without derived completeness it
fails: `⊕ₙ ℤ/pⁿℤ` is `p`-power torsion and is not killed by any power of `p`.

The proof is a Baire category argument on the space of sequences `ℕ → M`, with `M` discrete. The
telescope map `(xₙ) ↦ (xₙ - f • xₙ₊₁)` is bijective, and its inverse followed by the evaluation at
`0` sums the series `∑ₙ fⁿ • cₙ`. Let `D = ⋂ₙ fⁿ M`. For each `k`, the sequences whose sum is sent
into `D` by `fᵏ` form a closed set, since changing a sequence from the index `n` on changes its
sum by an element of `fⁿ M`; and these sets cover all sequences, since every sum is torsion. By
Baire's theorem one of them contains a cylinder, which gives `fᴷ M ⊆ D` for some `K`. Then
`D = fᴷ M = f D`, and Nakayama's lemma for derived complete modules
(`TauCeti.IsDerivedComplete.eq_bot_of_le_pointwise_smul`) gives `D = 0`.

## Main results

* `TauCeti.IsDerivedComplete.exists_isTorsionBy_pow`: a derived `I`-complete module that is
  `f`-power torsion for some `f ∈ I` is killed by a power of `f`.

## References

* B. Bhatt, *Torsion completions are bounded*, J. Pure Appl. Algebra 223 (2019), 1940–1945.
* [Stacks Project, Section 15.93, Tag 091N](https://stacks.math.columbia.edu/tag/091N).
-/

public section

open Finset Function
open scoped Pointwise

namespace TauCeti

variable {R : Type*} [CommRing R] {I : Ideal R} {M : Type*} [AddCommGroup M] [Module R M]

/-- Let `e` be a linear equivalence whose underlying map is the telescope map of `f`. The sums
`(e.symm c) 0` of two sequences which agree below the index `n` differ by an element of `fⁿ M`. -/
private lemma sub_mem_pow_smul_top_of_eq {f : R} {e : (ℕ → M) ≃ₗ[R] (ℕ → M)}
    (he : ⇑e = telescope M f) {c c' : ℕ → M} {n : ℕ} (h : ∀ j < n, c j = c' j) :
    e.symm c 0 - e.symm c' 0 ∈ (f ^ n • ⊤ : Submodule R M) := by
  have hz : telescope M f (e.symm (c - c')) = c - c' := by rw [← he]; exact e.apply_symm_apply _
  rw [← Pi.sub_apply, ← map_sub, eq_sum_range_add_pow_smul_of_telescope_eq hz 0 n,
    sum_eq_zero fun j hj ↦ by simp [h j (mem_range.1 hj)], zero_add]
  exact Submodule.smul_mem_pointwise_smul _ _ _ Submodule.mem_top

/-- Let `e` be a linear equivalence whose underlying map is the telescope map of `f`. The sum
`(e.symm c) 0` of the sequence `c` with the single nonzero term `m` at the index `n` is
`fⁿ • m`. -/
private lemma symm_single_zero {f : R} {e : (ℕ → M) ≃ₗ[R] (ℕ → M)}
    (he : ⇑e = telescope M f) (n : ℕ) (m : M) : e.symm (Pi.single n m) 0 = f ^ n • m := by
  set z := e.symm (Pi.single n m)
  have hz : telescope M f z = Pi.single n m := by rw [← he]; exact e.apply_symm_apply _
  -- The terms of `z` beyond `n` form a sequence killed by the telescope map.
  have htail : (fun k ↦ z (k + (n + 1))) = 0 := (map_eq_zero_iff (telescope M f)
      (he ▸ e.injective : Injective (telescope M f))).1 <|
    funext fun k ↦ by
      have hk := congrFun hz (k + (n + 1))
      rw [telescope_apply, Pi.single_eq_of_ne (by omega)] at hk
      simpa [add_right_comm k 1 (n + 1)] using hk
  rw [eq_sum_range_add_pow_smul_of_telescope_eq hz 0 (n + 1), sum_range_succ,
    sum_eq_zero fun j hj ↦ by simp [Pi.single_eq_of_ne (mem_range.1 hj).ne],
    show z (0 + (n + 1)) = 0 by simpa using congrFun htail 0]
  simp

namespace IsDerivedComplete

/-- **Torsion derived complete modules are bounded.** If `M` is derived `I`-complete and every
element of `M` is killed by a power of some `f ∈ I`, then a single power of `f` kills `M`. This is
the principal case of Bhatt's theorem. -/
theorem exists_isTorsionBy_pow (hM : IsDerivedComplete I M) {f : R} (hf : f ∈ I)
    (htors : Module.IsTorsion' M (Submonoid.powers f)) :
    ∃ n, Module.IsTorsionBy R M (f ^ n) := by
  rw [Submodule.isTorsion'_powers_iff] at htors
  obtain ⟨e, he⟩ : ∃ e : (ℕ → M) ≃ₗ[R] (ℕ → M), ⇑e = telescope M f :=
    ⟨LinearEquiv.ofBijective _ (hM.bijective hf), rfl⟩
  -- `D = ⋂ₙ fⁿ M`, and the sets `B k` of sequences whose sum is sent into `D` by `fᵏ`.
  set D : Submodule R M := ⨅ n : ℕ, f ^ n • ⊤
  let B (k : ℕ) : Set (ℕ → M) := {c | f ^ k • e.symm c 0 ∈ D}
  -- Baire's theorem on `ℕ → M`, with `M` discrete, a complete metric space.
  let _ : TopologicalSpace M := ⊥
  have _ : DiscreteTopology M := ⟨rfl⟩
  let _ : MetricSpace (ℕ → M) := PiNat.metricSpace
  have _ : CompleteSpace (ℕ → M) := PiNat.completeSpace
  have hclosed (k : ℕ) : IsClosed (B k) := by
    refine isOpen_compl_iff.1 (isOpen_iff_forall_mem_open.2 fun c hc ↦ ?_)
    obtain ⟨n, hn⟩ : ∃ n, f ^ k • e.symm c 0 ∉ (f ^ n • ⊤ : Submodule R M) := by
      simpa [B, D, Submodule.mem_iInf] using hc
    refine ⟨(range n : Set ℕ).pi fun j ↦ {c j}, fun c' hc' hc'B ↦ hn ?_,
      isOpen_set_pi (finite_toSet _) fun _ _ ↦ isOpen_discrete _, fun _ _ ↦ rfl⟩
    have h := Submodule.smul_mem _ (f ^ k) (sub_mem_pow_smul_top_of_eq he (c := c') (c' := c)
      (n := n) fun j hj ↦ hc' j (mem_range.2 hj))
    rw [smul_sub] at h
    simpa using sub_mem (Submodule.mem_iInf _ |>.1 hc'B n) h
  have hcover : ⋃ k, B k = Set.univ := Set.eq_univ_of_forall fun c ↦ by
    obtain ⟨k, hk⟩ := htors (e.symm c 0)
    exact Set.mem_iUnion.2 ⟨k, by simp [B, hk, D.zero_mem]⟩
  obtain ⟨k, c₀, hc₀⟩ := nonempty_interior_of_iUnion_of_closed hclosed hcover
  -- The open set `interior (B k)` contains a cylinder around `c₀`, of length `n`.
  obtain ⟨J, u, hu, hJ⟩ := isOpen_pi_iff.1 isOpen_interior c₀ hc₀
  set n := J.sup id + 1
  have hD (m : M) : f ^ (k + n) • m ∈ D := by
    have h₁ : c₀ + Pi.single n m ∈ B k := interior_subset <| hJ fun a ha ↦ by
      have han : a ≠ n := (Nat.lt_succ_of_le (le_sup (f := id) ha)).ne
      simpa [Pi.single_eq_of_ne han] using (hu a ha).2
    have h₂ : c₀ ∈ B k := interior_subset hc₀
    simp only [B, Set.mem_ofPred_eq] at h₁ h₂
    have h := sub_mem h₁ h₂
    rwa [map_add, Pi.add_apply, smul_add, add_sub_cancel_left, symm_single_zero he, smul_smul,
      ← pow_add] at h
  -- Hence `D = fᵏ⁺ⁿ M`, so `D = f D`, and `D = 0` by Nakayama's lemma.
  have hle : D ≤ f • D := fun x hx ↦ by
    obtain ⟨m, -, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1
      (Submodule.mem_iInf _ |>.1 hx (k + n + 1))
    rw [pow_succ', mul_smul]
    exact Submodule.smul_mem_pointwise_smul _ _ _ (hD m)
  refine ⟨k + n, fun m ↦ ?_⟩
  simpa [hM.eq_bot_of_le_pointwise_smul hf hle] using hD m

end IsDerivedComplete

end TauCeti

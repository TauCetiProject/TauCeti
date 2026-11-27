/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Dynamics.TopologicalEntropy.NetEntropy
public import TauCeti.Analysis.Asymptotics.ExpGrowth

/-!
# Comparing scales of topological entropy through a time window

If closeness at a coarse scale `V` during a window of times forces closeness at a fine scale `U`,
then dynamical nets at the fine scale give dynamical nets at the coarse scale for a slightly
longer time. Since a shift of the time does not change the exponential growth rate
(`Monotone.expGrowthSup_comp_add`), the topological entropy is then computed at the single
scale `V`.

## Main results

* `TauCeti.netMaxcard_le_netMaxcard_add_of_window`: for a permutation `T`, if pairs `V`-close at
  all times `|i| ≤ N` are `U`-close, then `T ^ (-N)` carries `(U, n)`-nets of the space to
  `(V, n + 2 N)`-nets.
* `TauCeti.netMaxcard_le_netMaxcard_add_of_forward_window`: the forward version for a map `T`
  and times `i ≤ N`, where `(U, n)`-nets are themselves `(V, n + N)`-nets.
* `TauCeti.coverEntropy_eq_netEntropyEntourage_of_window`: if every scale of a basis of the
  uniformity compares in this way with `V ∈ 𝓤 X`, then
  `coverEntropy T F = netEntropyEntourage T F V`.
* `TauCeti.coverEntropy_lt_top_of_window`: under the same hypothesis, the entropy of `T` on a
  compact invariant set is finite.

These are the comparisons in the proof that the entropy of an expansive homeomorphism is computed
at one scale.

## References

* P. Walters, *An Introduction to Ergodic Theory*, Graduate Texts in Mathematics 79, Springer,
  1982, proof of Theorem 7.11.
-/

public section

namespace TauCeti

open Dynamics ExpGrowth Filter Set
open scoped ENNReal Uniformity

variable {X : Type*}

/-- **Comparison of scales through a two-sided window.** Let `T` be a permutation and `U`, `V`
relations such that a pair is `U`-related as soon as its images under `T ^ i` are `V`-related for
all `|i| ≤ N`. Then a `(U, n)`-dynamical net of the whole space is carried by `T ^ (-N)` to a
`(V, n + 2 N)`-dynamical net, so `netMaxcard T univ U n ≤ netMaxcard T univ V (n + 2 N)`. -/
theorem netMaxcard_le_netMaxcard_add_of_window (T : Equiv.Perm X) {U V : SetRel X X} {N : ℕ}
    (hwin : ∀ x y, (∀ i : ℤ, |i| ≤ N → ((T ^ i) x, (T ^ i) y) ∈ V) → (x, y) ∈ U) (n : ℕ) :
    netMaxcard T univ U n ≤ netMaxcard T univ V (n + 2 * N) := by
  classical
  refine iSup₂_le fun s hs ↦ ?_
  have hinj : Function.Injective (T ^ (-(N : ℤ))) := Equiv.injective _
  rw [← Finset.card_image_of_injective s hinj]
  refine IsDynNetIn.card_le_netMaxcard ⟨subset_univ _, ?_⟩
  -- iterates of `T` are powers of `T`
  have hit (k : ℕ) (x : X) : T^[k] x = (T ^ (k : ℤ)) x := by
    rw [zpow_natCast, Equiv.Perm.iterate_eq_pow]
  intro a ha b hb hab
  simp only [Finset.coe_image, mem_image, Finset.mem_coe] at ha hb
  obtain ⟨x, hx, rfl⟩ := ha
  obtain ⟨y, hy, rfl⟩ := hb
  have hxy : x ≠ y := fun h ↦ hab (h ▸ rfl)
  refine Set.disjoint_left.2 fun z hzx hzy ↦ ?_
  -- the point `w = T ^ N z` lies in the `(U, n)`-balls of both `x` and `y`
  have key : ∀ x, z ∈ (dynEntourage T V (n + 2 * N)).inv.ball ((T ^ (-(N : ℤ))) x) →
      (T ^ (N : ℤ)) z ∈ (dynEntourage T U n).inv.ball x := by
    intro x hz
    simp only [SetRel.mem_ball, SetRel.mem_inv, mem_dynEntourage] at hz ⊢
    intro j hj
    refine hwin _ _ fun i hi ↦ ?_
    have hk : 0 ≤ i + j + N := by
      have := neg_abs_le i
      omega
    obtain ⟨k, hk'⟩ := Int.eq_ofNat_of_zero_le hk
    have hkn : k < n + 2 * N := by
      have := le_abs_self i
      omega
    have h := hz k hkn
    rw [hit, hit] at h
    rw [hit, hit]
    have e₁ : (T ^ i) ((T ^ (j : ℤ)) x) = (T ^ (k : ℤ)) ((T ^ (-(N : ℤ))) x) := by
      simp only [← Equiv.Perm.mul_apply, ← zpow_add]
      congr 2
      omega
    have e₂ : (T ^ i) ((T ^ (j : ℤ)) ((T ^ (N : ℤ)) z)) = (T ^ (k : ℤ)) z := by
      simp only [← Equiv.Perm.mul_apply, ← zpow_add]
      congr 2
      omega
    rwa [e₁, e₂]
  exact hs.2 hx hy hxy |>.ne_of_mem (key x hzx) (key y hzy) rfl

/-- **Comparison of scales through a forward window.** Let `T` be a map and `U`, `V` relations
such that a pair is `U`-related as soon as its images under `T^[i]` are `V`-related for all
`i ≤ N`. Then every `(U, n)`-dynamical net is a `(V, n + N)`-dynamical net, so
`netMaxcard T F U n ≤ netMaxcard T F V (n + N)`. -/
theorem netMaxcard_le_netMaxcard_add_of_forward_window (T : X → X) (F : Set X)
    {U V : SetRel X X} {N : ℕ}
    (hwin : ∀ x y, (∀ i ≤ N, (T^[i] x, T^[i] y) ∈ V) → (x, y) ∈ U) (n : ℕ) :
    netMaxcard T F U n ≤ netMaxcard T F V (n + N) := by
  refine iSup₂_le fun s hs ↦ IsDynNetIn.card_le_netMaxcard ⟨hs.1, fun x hx y hy hxy ↦ ?_⟩
  refine Set.disjoint_left.2 fun z hzx hzy ↦ ?_
  have key : ∀ x, z ∈ (dynEntourage T V (n + N)).inv.ball x →
      z ∈ (dynEntourage T U n).inv.ball x := by
    intro x hz
    simp only [SetRel.mem_ball, SetRel.mem_inv, mem_dynEntourage] at hz ⊢
    intro j hj
    refine hwin _ _ fun i hi ↦ ?_
    rw [← Function.iterate_add_apply, ← Function.iterate_add_apply]
    exact hz _ (by omega)
  exact (hs.2 hx hy hxy).ne_of_mem (key x hzx) (key y hzy) rfl

variable [UniformSpace X]

/-- **Entropy at a single scale.** Let `V ∈ 𝓤 X` and let `s` be a basis of the uniformity such
that for each `s i` some time shift `N` gives `netMaxcard T F (s i) n ≤ netMaxcard T F V (n + N)`
for all `n`. Then the topological entropy of `T` on `F` is the growth rate of the largest
dynamical nets for `V`. -/
theorem coverEntropy_eq_netEntropyEntourage_of_window {ι : Sort*} {p : ι → Prop}
    {s : ι → SetRel X X} (hb : (𝓤 X).HasBasis p s) {T : X → X} {F : Set X} {V : SetRel X X}
    (hV : V ∈ 𝓤 X)
    (hwin : ∀ i, p i → ∃ N : ℕ, ∀ n, netMaxcard T F (s i) n ≤ netMaxcard T F V (n + N)) :
    coverEntropy T F = netEntropyEntourage T F V := by
  refine le_antisymm ?_ (netEntropyEntourage_le_coverEntropy T F hV)
  rw [coverEntropy_eq_iSup_basis_netEntropyEntourage hb T F]
  refine iSup₂_le fun i hi ↦ ?_
  obtain ⟨N, hN⟩ := hwin i hi
  calc netEntropyEntourage T F (s i)
      ≤ expGrowthSup fun n ↦ (netMaxcard T F V (n + N) : ℝ≥0∞) :=
        expGrowthSup_monotone fun n ↦ ENat.toENNReal_mono (hN n)
    _ = netEntropyEntourage T F V :=
        (ENat.toENNReal_mono.comp (netMaxcard_monotone_time T F V)).expGrowthSup_comp_add N

/-- **Finite entropy from a window.** Under the hypotheses of
`TauCeti.coverEntropy_eq_netEntropyEntourage_of_window`, the topological entropy of `T` on a
compact invariant set `F` is finite. -/
theorem coverEntropy_lt_top_of_window {ι : Sort*} {p : ι → Prop} {s : ι → SetRel X X}
    (hb : (𝓤 X).HasBasis p s) {T : X → X} {F : Set X} {V : SetRel X X} (hV : V ∈ 𝓤 X)
    (hwin : ∀ i, p i → ∃ N : ℕ, ∀ n, netMaxcard T F (s i) n ≤ netMaxcard T F V (n + N))
    (hF : IsCompact F) (hTF : MapsTo T F F) :
    coverEntropy T F < ⊤ := by
  rw [coverEntropy_eq_netEntropyEntourage_of_window hb hV hwin]
  exact (netEntropyEntourage_le_coverEntropyEntourage T F).trans_lt
    (coverEntropyEntourage_finite_of_isCompact_invariant hF hTF hV)

end TauCeti

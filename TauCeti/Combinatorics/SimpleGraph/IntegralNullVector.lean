/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.SimpleGraph.AdditiveFunction
public import Mathlib.Algebra.GCDMonoid.Finset

/-!
# Primitive integral additive functions

A nonzero natural-valued additive function on a finite preconnected graph is positive.
Dividing its coordinates by their gcd gives the unique positive additive function with
coordinate gcd one. Every natural-valued additive function, including zero, is a natural
multiple of this primitive vector; the multiplier is its coordinate gcd.

The rational kernel theorem for the graph Cartan matrix gives proportionality. Taking the
gcd of the cross-multiplication identities then proves integrality of the multiplier, rather
than merely asserting that two integral vectors on the same rational line are integral multiples.

The positive-additive-function viewpoint follows Kac, *Infinite dimensional Lie algebras*,
3rd edition, Chapter 4.
-/

public section

namespace SimpleGraph

open Finset Matrix

variable {V : Type*} [Fintype V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

/-- A nonzero natural-valued additive function on a preconnected graph is positive everywhere. -/
theorem Preconnected.pos_of_sum_eq_two_mul (hG : G.Preconnected) {a : V → ℕ}
    (ha : ∀ i, ∑ j ∈ G.neighborFinset i, a j = 2 * a i) (hne : a ≠ 0) (i : V) :
    0 < a i := by
  classical
  have hnull : G.graphCartanMatrix ℤ *ᵥ (fun j ↦ (a j : ℤ)) = 0 :=
    G.graphCartanMatrix_mulVec_eq_zero fun j ↦ by exact_mod_cast ha j
  have hne' : (fun j ↦ (a j : ℤ)) ≠ 0 := by
    intro h
    apply hne
    ext j
    have hj : (a j : ℤ) = 0 := congrFun h j
    exact_mod_cast hj
  exact_mod_cast hG.pos_of_graphCartanMatrix_mulVec_nonneg
    (fun j ↦ Int.natCast_nonneg (a j)) hnull.ge hne' i

/-- Every natural-valued additive function is its coordinate gcd times any primitive
additive function. -/
theorem Preconnected.eq_gcd_smul_of_sum_eq_two_mul (hG : G.Preconnected) {δ a : V → ℕ}
    (hδ : ∀ i, ∑ j ∈ G.neighborFinset i, δ j = 2 * δ i)
    (hprim : univ.gcd δ = 1)
    (ha : ∀ i, ∑ j ∈ G.neighborFinset i, a j = 2 * a i) :
    a = univ.gcd a • δ := by
  classical
  have hpos := hG.pos_of_sum_eq_two_mul hδ (by
    intro hz
    have hg : univ.gcd δ = 0 := Finset.gcd_eq_zero_iff.mpr (by simp [hz])
    exact Nat.one_ne_zero (hprim.symm.trans hg))
  have hδQ : ∀ i, ∑ j ∈ G.neighborFinset i, (δ j : ℚ) = 2 * (δ i : ℚ) :=
    fun i ↦ by exact_mod_cast hδ i
  have haQ : G.graphCartanMatrix ℚ *ᵥ (fun i ↦ (a i : ℚ)) = 0 :=
    G.graphCartanMatrix_mulVec_eq_zero fun i ↦ by exact_mod_cast ha i
  have hmem : (fun i ↦ (a i : ℚ)) ∈
      Submodule.span ℚ {fun i ↦ (δ i : ℚ)} := by
    rw [← G.ker_mulVecLin_graphCartanMatrix hG
      (fun i ↦ by exact_mod_cast hpos i) hδQ]
    exact haQ
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hmem
  have hcross (i j : V) : a i * δ j = δ i * a j := by
    have hi := congrFun hc i
    have hj := congrFun hc j
    simp only [Pi.smul_apply, smul_eq_mul] at hi hj
    exact_mod_cast (by nlinarith : (a i : ℚ) * δ j = (δ i : ℚ) * a j)
  ext i
  have hg := congrArg (fun f : V → ℕ ↦ univ.gcd f) (funext (hcross i))
  simp only [Finset.gcd_mul_left, normalize_eq, hprim, mul_one] at hg
  simpa only [Pi.smul_apply, smul_eq_mul, mul_comm] using hg

/-- The natural null cone of the graph Cartan matrix is precisely the natural multiples of a
primitive additive function. This includes the zero multiple. -/
theorem Preconnected.sum_eq_two_mul_iff_exists_smul (hG : G.Preconnected) {δ : V → ℕ}
    (hδ : ∀ i, ∑ j ∈ G.neighborFinset i, δ j = 2 * δ i)
    (hprim : univ.gcd δ = 1) (a : V → ℕ) :
    (∀ i, ∑ j ∈ G.neighborFinset i, a j = 2 * a i) ↔ ∃ m : ℕ, a = m • δ := by
  constructor
  · intro ha
    exact ⟨univ.gcd a, hG.eq_gcd_smul_of_sum_eq_two_mul hδ hprim ha⟩
  · rintro ⟨m, rfl⟩ i
    simp only [Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum, hδ i]
    ring

/-- A nonzero natural-valued additive function determines a unique primitive integral null vector.
It is positive by `Preconnected.pos_of_sum_eq_two_mul`; no vertex is assumed to have coefficient
one. -/
theorem Preconnected.existsUnique_sum_eq_two_mul_gcd_eq_one (hG : G.Preconnected)
    {a : V → ℕ} (ha : ∀ i, ∑ j ∈ G.neighborFinset i, a j = 2 * a i) (hne : a ≠ 0) :
    ∃! δ : V → ℕ,
      (∀ i, ∑ j ∈ G.neighborFinset i, δ j = 2 * δ i) ∧ univ.gcd δ = 1 := by
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hne
  obtain ⟨δ, hfactor, hprim⟩ := univ.extract_gcd a ⟨i, mem_univ i⟩
  have hg : univ.gcd a ≠ 0 := by
    intro hg
    exact hi (by simpa [hg] using hfactor i (mem_univ i))
  have hfactor' (j : V) : a j = univ.gcd a * δ j := hfactor j (mem_univ j)
  have hδ (j : V) : ∑ l ∈ G.neighborFinset j, δ l = 2 * δ j := by
    apply Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hg)
    calc
      univ.gcd a * ∑ l ∈ G.neighborFinset j, δ l =
          ∑ l ∈ G.neighborFinset j, a l := by simp_rw [hfactor', mul_sum]
      _ = 2 * a j := ha j
      _ = univ.gcd a * (2 * δ j) := by rw [hfactor']; ring
  refine ⟨δ, ⟨hδ, hprim⟩, ?_⟩
  rintro η ⟨hη, hηprim⟩
  simpa [hηprim] using hG.eq_gcd_smul_of_sum_eq_two_mul hδ hprim hη

end SimpleGraph

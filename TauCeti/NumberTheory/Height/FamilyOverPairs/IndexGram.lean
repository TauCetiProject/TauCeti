/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Height.GramOverPairs
public import TauCeti.NumberTheory.Height.IndexOverPairs

/-!
# Scaled Gram heights from index bounds

`PrimePadicIso.IndexLe.heightLe_scaled_det_gram` bounds the height of a family of Gram
determinants completed by auxiliary vectors. It uses the same index budget for the two
opposite prime-adic embeddings and the pairing bound
`PrimePadicIso.heightLe_scaled_det_gram`.

The estimate adapts `New.TwistedLattice.heightLe_pow_mul_det_gram` from
[TwistedLattice.lean in lsernau/grh-lean][short-proof] (Apache 2.0), the finite-place step of
`New.TwistedLattice.covolume_add_index_nonneg`.

[short-proof]:
https://github.com/lsernau/grh-lean/blob/72fead1/grh/src/New/Reduction/Lattices/TwistedLattice.lean
-/

public section

open Matrix
open scoped InnerProductSpace

namespace TauCeti.PrimePadicIso

/-- Suppose `y` has index at most `δ` relative to the submodules `L`. For each embedding `ι`,
let `L₁ ι` contain the index submodule at the embedding obtained by precomposing `ι` with
complex conjugation, and let `L₂ ι` contain `L ι`. Suppose both sets contain every scaled
auxiliary vector `γ ι • z j`, and the pairing of `f ι u` with `f ι v` is integral at `ι` for
every `u ∈ L₁ ι` and `v ∈ L₂ ι`. Then the scaled Gram determinants of the lifted family
completed by `z` have height at most `2 * δ`. -/
theorem IndexLe.heightLe_scaled_det_gram {V I J : Type*} [AddCommMonoid V] [Module ℂ V]
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    {E : PrimePadicIso → Type*} [∀ ι, SeminormedAddCommGroup (E ι)]
    [∀ ι, InnerProductSpace ℂ (E ι)]
    {L : (ι : PrimePadicIso) → Submodule ι.integers V} {y : I → V} {δ : ℝ}
    (hy : IndexLe L y δ) (z : J → V) (f : ∀ ι, V →ₗ[ℂ] E ι) (γ : PrimePadicIso → ℂ)
    {L₁ L₂ : PrimePadicIso → Set V}
    (h₁ : ∀ ι, (L { ι with iso := Complex.conjAe.toRingEquiv.trans ι.iso } : Set V) ⊆ L₁ ι)
    (h₂ : ∀ ι, (L ι : Set V) ⊆ L₂ ι)
    (hz₁ : ∀ ι j, γ ι • z j ∈ L₁ ι) (hz₂ : ∀ ι j, γ ι • z j ∈ L₂ ι)
    (hpair : ∀ ι ⦃u v⦄, u ∈ L₁ ι → v ∈ L₂ ι → ‖ι.iso ⟪f ι u, f ι v⟫_ℂ‖ ≤ 1) :
    HeightLe (fun ι ↦ (↑(‖γ ι‖ ^ (2 * Fintype.card J)) : ℂ) *
      (gram ℂ (Sum.elim (fun i ↦ f ι (y i)) (fun j ↦ f ι (z j)))).det) (2 * δ) := by
  obtain ⟨d, _, hbudget, hmat⟩ := indexLe_iff.mp hy
  refine PrimePadicIso.heightLe_scaled_det_gram
    (fun ι i ↦ f ι (y i)) (fun ι j ↦ f ι (z j)) γ hbudget ?_
  intro ι
  let κ : PrimePadicIso := { ι with iso := Complex.conjAe.toRingEquiv.trans ι.iso }
  obtain ⟨A, hA, hrowsA⟩ := hmat κ
  obtain ⟨B, hB, hrowsB⟩ := hmat ι
  have hdet (η : PrimePadicIso) (D : Matrix I I η.integers) :
      (D.map η.integers.subtype).det = (D.det : ℂ) :=
    (RingHom.map_det η.integers.subtype D).symm
  refine ⟨A.map κ.integers.subtype, B.map ι.integers.subtype, ?_, ?_, ?_⟩
  · have hκ (w : ℂ) : ‖κ.iso w‖ = ‖ι.iso (star w)‖ := by
      simp only [κ, RingEquiv.trans_apply, AlgEquiv.coe_toRingEquiv, Complex.conjAe_coe,
        Complex.star_def]
    have hprime : κ.prime = ι.prime := (rfl)
    simpa only [hdet κ A, hκ, hprime] using hA
  · simpa only [hdet ι B] using hB
  have hmem (η : PrimePadicIso) (D : Matrix I I η.integers) (S : Set V)
      (hrows : ∀ i, (∑ k, D i k • y k) ∈ S) (hz : ∀ j, γ ι • z j ∈ S) (i : I ⊕ J) :
      ∃ u ∈ S, f ι u = Sum.elim (fun i ↦ ∑ k, (D.map η.integers.subtype) i k • f ι (y k))
        (fun j ↦ γ ι • f ι (z j)) i := by
    cases i with
    | inl i =>
      refine ⟨∑ k, D i k • y k, hrows i, ?_⟩
      simp only [Subring.smul_def, map_sum, map_smul, Matrix.map_apply, Subring.coe_subtype,
        Sum.elim_inl]
    | inr j => exact ⟨γ ι • z j, hz j, (f ι).map_smul _ _⟩
  have hsub : (L κ : Set V) ⊆ L₁ ι := h₁ ι
  intro i j
  obtain ⟨u, hu, hu'⟩ := hmem κ A (L₁ ι) (fun i ↦ hsub (hrowsA i)) (hz₁ ι) i
  obtain ⟨v, hv, hv'⟩ := hmem ι B (L₂ ι) (fun j ↦ h₂ ι (hrowsB j)) (hz₂ ι) j
  rw [← hu', ← hv']
  exact hpair ι hu hv

end TauCeti.PrimePadicIso

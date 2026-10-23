/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.SpecificGroups.Braid.HeckeSkein
public import TauCeti.KnotTheory.Markov.Basic
import Mathlib.Tactic.LinearCombination

/-!
# Skein relations determine Markov invariants

A function `F` on braids of any width is a skein invariant with parameters `x`, `z` and `d` when it
is constant along Markov equivalence, satisfies the skein relation
`x F(σᵢ c) - x⁻¹ F(σᵢ⁻¹ c) = z F(c)` and is multiplied by `d` when an uncrossed strand is added.
The HOMFLY polynomial (`x = a`) and the writhe-normalized Kauffman bracket (`x = A⁴`) are of this
kind. This file proves that such a function is determined by its value on the trivial braid on one
strand (`TauCeti.MarkovBraid.eq_of_skein`), the closed-braid form of the uniqueness half of the
skein-theoretic characterization of these polynomials. No hypothesis on `x`, `z` or `d` beyond
`x` being a unit is needed.

The proof weights `F` by `x ^ e`, for `e` the exponent sum of the braid, which turns the skein
relation into the Hecke skein relation `f(b σᵢ c) - f(b σᵢ⁻¹ c) = z f(b c)` in every braid context.
Modulo the Hecke skein relation every braid on `n + 2` strands is a combination of the braids `ι b`
and `ι b * σ * ι c` (`TauCeti.BraidGroup.strandSpan_sup_heckeSkein_eq_top`); the first kind is
handled by the strand factor `d` and the second, conjugate to a stabilization of `c * b`, by Markov
invariance. Induction on the number of strands then concludes.

## Main results

* `TauCeti.MarkovBraid.eq_of_skein`: two skein invariants with the same parameters agreeing on the
  one-strand trivial braid are equal.

## References

* V. F. R. Jones, *Hecke algebra representations of braid groups and link polynomials*,
  Ann. of Math. 126 (1987), 335–388, Sections 4–6.
* C. Kassel, V. Turaev, *Braid Groups*, Graduate Texts in Mathematics 247, Springer (2008),
  Section 4.2.
-/

public section

namespace TauCeti.MarkovBraid

open BraidGroup MonoidAlgebra

variable {R : Type*} [CommRing R]

/-- The weight `x ^ e` of a braid with exponent sum `e`, as a homomorphism to the units. -/
private noncomputable def weight (x : Rˣ) (n : ℕ) : BraidGroup n →* Rˣ :=
  (zpowersHom Rˣ x).comp (ArtinGroup.exponentSum _)

private theorem weight_sigma (x : Rˣ) {n : ℕ} (i : Fin (n - 1)) : weight x n (sigma i) = x := by
  simp [weight]

/-- A Markov invariant satisfying the skein relation, weighted by `x ^ e` for the exponent sum `e`,
satisfies the Hecke skein relation in every braid context. -/
private theorem weight_skein (x : Rˣ) (z : R) {F : MarkovBraid → R}
    (hF : ∀ β γ, MarkovEquiv β γ → F β = F γ)
    (hs : ∀ n (c : BraidGroup (n + 1)) (i : Fin n),
      x * F ⟨n, sigma (n := n + 1) i * c⟩ - (↑x⁻¹ : R) * F ⟨n, (sigma (n := n + 1) i)⁻¹ * c⟩ =
        z * F ⟨n, c⟩)
    {n : ℕ} (b c : BraidGroup (n + 1)) (i : Fin n) :
    weight x _ (b * sigma (n := n + 1) i * c) * F ⟨n, b * sigma (n := n + 1) i * c⟩ -
        weight x _ (b * (sigma (n := n + 1) i)⁻¹ * c) *
          F ⟨n, b * (sigma (n := n + 1) i)⁻¹ * c⟩ =
      z * (weight x _ (b * c) * F ⟨n, b * c⟩) := by
  -- Conjugating by `b` moves the crossing to the front, `b * g * c ~ g * (c * b)`.
  have hconj (g : BraidGroup (n + 1)) : F ⟨n, b * g * c⟩ = F ⟨n, g * (c * b)⟩ :=
    hF _ _ (by simpa [mul_assoc] using (IsMarkovMove.conj (g * (c * b)) b).markovEquiv)
  have hcb : F ⟨n, b * c⟩ = F ⟨n, c * b⟩ := by simpa using hconj 1
  have hw (g : BraidGroup (n + 1)) :
      weight x _ (b * g * c) = weight x _ g * weight x _ (c * b) := by
    simp only [map_mul]
    ac_rfl
  have hwbc : weight x _ (b * c) = weight x _ (c * b) := by simpa using hw 1
  rw [hconj, hconj, hcb, hw, hw, hwbc, map_inv, weight_sigma]
  simp only [Units.val_mul]
  linear_combination ((weight x _ (c * b) : Rˣ) : R) * hs n (c * b) i

/-- **Skein invariants are determined by the unknot.** Let `F` and `G` be functions on braids of
any width which are constant along Markov equivalence, satisfy the skein relation
`x F(σᵢ c) - x⁻¹ F(σᵢ⁻¹ c) = z F(c)` for the same unit `x` and the same `z`, and are multiplied by
the same `d` when an uncrossed strand is added. If they agree on the trivial braid on one strand,
they are equal. -/
theorem eq_of_skein (x : Rˣ) (z d : R) {F G : MarkovBraid → R}
    (hF : ∀ β γ, MarkovEquiv β γ → F β = F γ) (hG : ∀ β γ, MarkovEquiv β γ → G β = G γ)
    (hFs : ∀ n (c : BraidGroup (n + 1)) (i : Fin n),
      x * F ⟨n, sigma (n := n + 1) i * c⟩ - (↑x⁻¹ : R) * F ⟨n, (sigma (n := n + 1) i)⁻¹ * c⟩ =
        z * F ⟨n, c⟩)
    (hGs : ∀ n (c : BraidGroup (n + 1)) (i : Fin n),
      x * G ⟨n, sigma (n := n + 1) i * c⟩ - (↑x⁻¹ : R) * G ⟨n, (sigma (n := n + 1) i)⁻¹ * c⟩ =
        z * G ⟨n, c⟩)
    (hFι : ∀ n (b : BraidGroup (n + 1)), F ⟨n + 1, strandIncl b⟩ = d * F ⟨n, b⟩)
    (hGι : ∀ n (b : BraidGroup (n + 1)), G ⟨n + 1, strandIncl b⟩ = d * G ⟨n, b⟩)
    (h₁ : F ⟨0, 1⟩ = G ⟨0, 1⟩) : F = G := by
  suffices h : ∀ n (b : BraidGroup (n + 1)), F ⟨n, b⟩ = G ⟨n, b⟩ by
    funext ⟨n, b⟩
    exact h n b
  intro n
  induction n with
  | zero =>
    intro b
    have hb : b = 1 := by
      have h : MonoidHom.id (BraidGroup 1) = 1 := hom_ext fun i ↦ i.elim0
      exact DFunLike.congr_fun h b
    rw [hb, h₁]
  | succ n ih =>
    -- The weighted difference, extended linearly to the group algebra, kills the Hecke skein
    -- relators and the spanning braids, hence everything.
    let f (g : BraidGroup (n + 2)) : R := weight x _ g * (F ⟨n + 1, g⟩ - G ⟨n + 1, g⟩)
    let φ : R[BraidGroup (n + 2)] →ₗ[R] R :=
      Finsupp.linearCombination R f ∘ₗ (coeffLinearEquiv R).toLinearMap
    have hφ (g : BraidGroup (n + 2)) (r : R) : φ (single g r) = r * f g := by
      simp [φ, coeffLinearEquiv_apply, coeff_single]
    -- A braid crossing the new strand once is Markov equivalent to a braid on one strand fewer.
    have hstab {H : MarkovBraid → R} (hH : ∀ β γ, MarkovEquiv β γ → H β = H γ)
        (b c : BraidGroup (n + 1)) :
        H ⟨n + 1, strandIncl b * sigma (n := n + 2) (Fin.last n) * strandIncl c⟩ = H ⟨n, c * b⟩ :=
      by
      refine hH _ _ (MarkovEquiv.trans ?_ (IsMarkovMove.stabilize (c * b)).markovEquiv)
      simpa [mul_assoc] using
        (IsMarkovMove.conj (strandIncl (c * b) * sigma (n := n + 2) (Fin.last n))
          (strandIncl c)⁻¹).markovEquiv
    have hle : strandSpan R n ⊔ heckeSkein R z (n + 2) ≤ LinearMap.ker φ := by
      refine sup_le ((strandSpan_le_iff R).mpr ⟨fun b ↦ ?_, fun b c ↦ ?_⟩)
        ((heckeSkein_le_iff R z).mpr fun b c i ↦ ?_) <;> rw [LinearMap.mem_ker]
      · rw [hφ, one_mul]
        simp only [f, hFι, hGι, ih, sub_self, mul_zero]
      · rw [hφ, one_mul]
        simp only [f, hstab hF, hstab hG, ih, sub_self, mul_zero]
      · have hFw := weight_skein x z hF hFs b c i
        have hGw := weight_skein x z hG hGs b c i
        rw [heckeRelator_def, map_sub, map_sub, hφ, hφ, hφ]
        simp only [f]
        linear_combination hFw - hGw
    rw [strandSpan_sup_heckeSkein_eq_top, top_le_iff] at hle
    intro g
    have hg : φ (single g 1) = 0 := LinearMap.mem_ker.mp (hle ▸ Submodule.mem_top)
    rw [hφ, one_mul] at hg
    simpa [f, sub_eq_zero] using hg

end TauCeti.MarkovBraid

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Module.Filtration.Basic
public import TauCeti.NumberTheory.WeilNumber.Pure

/-!
# Endomorphisms pure on the graded pieces of a filtration

Let `F` be a `ℤ`-indexed family of submodules of a finite-dimensional vector space `V` over a
field `K` of characteristic zero, and `φ` an endomorphism of `V` preserving every step `F a`. Then
`φ` induces an endomorphism `TauCeti.GradedPiece.map φ _ a` of each graded piece
`gr_a = F a ⧸ F (a - 1)` (`TauCeti.GradedPiece F a`). Following Deligne, `φ`
is *pure of weight `w` on the graded pieces of `F`*, relative to `q`, if for every `a` the
endomorphism induced on `gr_a` is pure of weight `w + a` in the sense of `TauCeti.IsPure`: its
characteristic roots are Weil `q`-numbers of weight `w + a`.

For the monodromy filtration `M(N)` of a nilpotent monodromy operator `N` and a geometric Frobenius
`φ`, this is the weight condition of the weight–monodromy conjecture: the eigenvalues of Frobenius
on `gr_a^{M(N)}` have weight `w + a`. When `N = 0` the monodromy filtration jumps from `0` to `V`
at the step `0`, and purity on the graded pieces is ordinary purity of weight `w`
(`TauCeti.isGradedPure_iff_isPure_of_eq_bot_of_eq_top`).

## Main definitions

* `TauCeti.IsGradedPure q w F φ`: `φ` preserves every step of `F` and is pure of weight `w + a`
  on `F a ⧸ F (a - 1)` for every `a`.

## Main results

* `TauCeti.isGradedPure_of_subsingleton`: every endomorphism of the zero space is pure of every
  weight on the graded pieces of every filtration.
* `TauCeti.isGradedPure_iff_isPure_of_eq_bot_of_eq_top`: for a filtration concentrated in
  degree `0`, purity on the graded pieces is purity.

## References

* P. Deligne, *La conjecture de Weil. II*, Publ. Math. IHÉS 52 (1980), §1.6, (1.6.1) and §1.8.
* P. Scholze, *Perfectoid spaces*, Publ. Math. IHÉS 116 (2012), §9, Conjecture 9.3.
-/

public section

open Module

namespace TauCeti

variable {K V : Type*} [Field K] [Algebra ℚ K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {q : ℝ} {w : ℤ} {F : ℤ → Submodule K V} {φ : End K V}

/-- An endomorphism `φ` is *pure of weight `w` on the graded pieces of `F`*, relative to `q`, if
it preserves every step `F a` and the endomorphism it induces on `F a ⧸ F (a - 1)` is pure of
weight `w + a` relative to `q`: every characteristic root there is a Weil `q`-number of weight
`w + a`. For the monodromy filtration of a nilpotent `N` and a geometric Frobenius `φ`, this is
the weight condition of the weight–monodromy conjecture. -/
structure IsGradedPure (q : ℝ) (w : ℤ) (F : ℤ → Submodule K V) (φ : End K V) : Prop where
  /-- `φ` preserves every step of the filtration. -/
  le_comap : ∀ a, F a ≤ (F a).comap φ
  /-- The endomorphism induced on `F a ⧸ F (a - 1)` is pure of weight `w + a`. -/
  isPure (a : ℤ) : IsPure q (w + a) (GradedPiece.map φ le_comap a)

/-- Every endomorphism of the zero space is pure of every weight on the graded pieces of every
filtration. -/
@[simp]
theorem isGradedPure_of_subsingleton [Subsingleton V] : IsGradedPure q w F φ where
  le_comap a x _ := by rw [Submodule.mem_comap, Subsingleton.elim x 0, map_zero]; exact zero_mem _
  isPure _ := isPure_of_subsingleton

/-- For a filtration that vanishes in negative degrees and is everything in nonnegative degrees,
such as the monodromy filtration of `N = 0`, purity of weight `w` on the graded pieces is purity
of weight `w`: the only nonzero graded piece is `F 0 ⧸ F (-1) ≅ V`. -/
theorem isGradedPure_iff_isPure_of_eq_bot_of_eq_top (hneg : ∀ a < 0, F a = ⊥)
    (hnonneg : ∀ a, 0 ≤ a → F a = ⊤) : IsGradedPure q w F φ ↔ IsPure q w φ := by
  have hF : ∀ a, F a ≤ (F a).comap φ := fun a x hx ↦ by
    rcases lt_or_ge a 0 with ha | ha
    · rw [hneg a ha, Submodule.mem_bot] at hx
      rw [hneg a ha, Submodule.mem_comap, hx, map_zero, Submodule.mem_bot]
    · rw [hnonneg a ha, Submodule.comap_top]
      exact Submodule.mem_top
  -- The graded piece of degree `0` is identified with `V`, compatibly with `φ`.
  have hbot : (F (0 - 1)).comap (F 0).subtype = ⊥ := by
    rw [hneg (0 - 1) (by norm_num), Submodule.comap_bot, Submodule.ker_subtype]
  let e := (Submodule.quotEquivOfEqBot _ hbot).trans (LinearEquiv.ofTop _ (hnonneg 0 le_rfl))
  have hconj : e.conj (GradedPiece.map φ hF 0) = φ := by
    ext v
    obtain ⟨x, rfl⟩ := e.surjective v
    simp [LinearEquiv.conj_apply, e]
  refine ⟨fun h ↦ ?_, fun h ↦ ⟨hF, fun a ↦ ?_⟩⟩
  · have h0 := h.isPure 0
    rwa [add_zero, ← isPure_conj_iff e, hconj] at h0
  · rcases lt_trichotomy a 0 with ha | rfl | ha
    · -- In negative degrees the graded piece is a quotient of `F a = 0`.
      have : Subsingleton (F a) := by
        rw [hneg a ha]
        infer_instance
      exact isPure_of_subsingleton
    · rwa [add_zero, ← isPure_conj_iff e, hconj]
    · -- In positive degrees `F (a - 1) = F a = V`, so the graded piece is zero.
      have htop : (F (a - 1)).comap (F a).subtype = ⊤ := by
        rw [hnonneg (a - 1) (by omega), Submodule.comap_top]
      have : Subsingleton (GradedPiece F a) := Submodule.Quotient.subsingleton_iff.2 htop
      exact isPure_of_subsingleton

end TauCeti

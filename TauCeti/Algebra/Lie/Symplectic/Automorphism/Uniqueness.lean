/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.SkewAdjoint
public import Mathlib.LinearAlgebra.BilinearForm.IsometryEquiv
import Mathlib.LinearAlgebra.Center
import TauCeti.Algebra.Lie.Symplectic.Transvection

/-!
# Uniqueness of a symplectic conjugating isometry

Two isometries of a nonzero alternating form induce the same conjugation on skew-adjoint
endomorphisms exactly when they agree up to a single sign. The form may have a radical and the
spaces may be infinite-dimensional.

The rank-one skew-adjoint endomorphisms force the ratio of the two isometries to preserve
each line. Preservation of a nonzero value of the form forces the resulting scalar to square
to one.
-/

public section

namespace LinearMap.BilinForm.IsometryEquiv

open LinearMap (BilinForm)

variable {K V W : Type*} [Field K] [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
variable {B : BilinForm K V} {C : BilinForm K W}

private theorem exists_smul_of_commute_rank_one (G : Module.End K V) {p q : V} (hpq : B p q = 1)
    (h : ∀ z v, B z v • G v = B (G z) v • v) : ∃ c : K, G = c • 1 := by
  apply LinearMap.exists_eq_smul_id_of_forall_notLinearIndependent
  intro v
  suffices ∃ a : K, G v = a • v by
    obtain ⟨a, ha⟩ := this
    rw [LinearIndependent.pair_iff]
    push Not
    exact ⟨a, -1, by rw [ha, neg_one_smul, add_neg_cancel], by simp⟩
  by_cases hv : ∃ z, B z v ≠ 0
  · obtain ⟨z, hz⟩ := hv
    refine ⟨B (G ((B z v)⁻¹ • z)) v, ?_⟩
    have he := h ((B z v)⁻¹ • z) v
    simpa only [map_smul, LinearMap.smul_apply, smul_eq_mul, inv_mul_cancel₀ hz, one_smul]
      using he
  · push Not at hv
    refine ⟨B (G p) q, ?_⟩
    have hq : G q = B (G p) q • q := by simpa only [hpq, one_smul] using h p q
    simpa only [map_add, hv, zero_add, hpq, one_smul, smul_add, hq, add_left_inj]
      using h p (v + q)

/-- Isometries of a nonzero alternating form give identical conjugations on its skew-adjoint
endomorphisms exactly when the two isometries agree everywhere or are negatives everywhere. -/
theorem conj_eq_on_skewAdjoint_iff (f g : B.IsometryEquiv C) (hB : B.IsAlt) (hB₀ : B ≠ 0) :
    (∀ X : skewAdjointLieSubalgebra B, f.toLinearEquiv.conj X.val = g.toLinearEquiv.conj X.val) ↔
      f = g ∨ ∀ v, f v = -(g v) := by
  obtain ⟨p, q, hpq⟩ : ∃ p q, B p q = 1 := by
    obtain ⟨x, y, hxy⟩ : ∃ x y, B x y ≠ 0 := by
      by_contra! hall
      exact hB₀ (LinearMap.ext₂ hall)
    exact ⟨x, (B x y)⁻¹ • y, by rw [map_smul, smul_eq_mul, inv_mul_cancel₀ hxy]⟩
  constructor
  · intro h
    let G := g.toLinearEquiv.symm.toLinearMap.comp f.toLinearEquiv.toLinearMap
    obtain ⟨c, hc⟩ := exists_smul_of_commute_rank_one G hpq fun z v ↦ by
      let X : skewAdjointLieSubalgebra B :=
        ⟨(B.flip v).smulRight v, smulRight_flip_mem_skewAdjointSubmodule hB v⟩
      rw [← map_smul]
      apply g.injective
      change g.toLinearEquiv (g.toLinearEquiv.symm (f (X.val z))) =
        g.toLinearEquiv (X.val (g.toLinearEquiv.symm (f z)))
      have he := LinearMap.congr_fun (h X) (f.toLinearEquiv z)
      simp only [LinearEquiv.conj_apply_apply, LinearEquiv.symm_apply_apply] at he
      simpa only [LinearEquiv.apply_symm_apply, coe_toLinearEquiv] using he
    have hs (v : V) : f v = c • g v := by
      have hv : G v = c • v := DFunLike.congr_fun hc v
      calc f v = g.toLinearEquiv (G v) := (g.toLinearEquiv.apply_symm_apply _).symm
           _ = c • g v := by rw [hv, map_smul]; rfl
    have hc2 : c ^ 2 = 1 := by
      simpa only [hs, map_smul, LinearMap.smul_apply, smul_eq_mul, g.map_app, hpq, mul_one, sq]
        using f.map_app q p
    rcases sq_eq_one_iff.mp hc2 with h1 | h1
    · exact Or.inl (DFunLike.ext _ _ fun v ↦ by simpa only [h1, one_smul] using hs v)
    · exact Or.inr fun v ↦ by simpa only [h1, neg_one_smul] using hs v
  · rintro (rfl | h)
    · exact fun _ ↦ rfl
    · intro X
      ext w
      obtain ⟨v, rfl⟩ := g.surjective w
      have hv : f.toLinearEquiv.symm (g v) = -v := by
        apply f.toLinearEquiv.injective
        rw [LinearEquiv.apply_symm_apply, map_neg, IsometryEquiv.coe_toLinearEquiv, h, neg_neg]
      have hg : g.toLinearEquiv.symm (g v) = v := g.toLinearEquiv.symm_apply_apply v
      simp only [LinearEquiv.conj_apply_apply, hv, hg, map_neg, IsometryEquiv.coe_toLinearEquiv,
        h, neg_neg]

end LinearMap.BilinForm.IsometryEquiv

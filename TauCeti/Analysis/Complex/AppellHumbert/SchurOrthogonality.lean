/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.AppellHumbert.Frobenius
import Mathlib.LinearAlgebra.Trace

/-!
# Schur orthogonality for translates of theta functions

Let D = (B, χ) be an Appell–Humbert datum for a full lattice L in a finite-dimensional complex
normed space V, with positive Riemann form E (TauCeti.AppellHumbertData.IsPositive).
If  : T → L^⊥ is a finite family in the dual lattice whose classes modulo L are permuted by
translation by every element of L^⊥, then for all , g ∈ D.thetaSpace and z, w ∈ V,

√[L^⊥ : L] * ∑ s : T, U_{-a s} g z * U_{a s} f w = |T| * f z * g w

(TauCeti.AppellHumbertData.IsPositive.sum_twistedTranslate_mul_twistedTranslate).
The proof forms the endomorphism Q x = ∑ s, (U_{-a s} x z) • U_{a s} f of D.thetaSpace,
shows Q commutes with every U_t, 	 ∈ L^⊥, hence is a scalar c • 1 by Schur's lemma
(TauCeti.AppellHumbertData.IsPositive.exists_eq_smul_one_of_commute), and evaluates c by
taking the trace of Q together with Frobenius' dimension formula
(TauCeti.AppellHumbertData.IsPositive.finrank_thetaSpace_sq).

## Main results

* TauCeti.AppellHumbertData.twistedTranslate_neg_twistedTranslate: U_{-u} (U_u f) = f.
* TauCeti.AppellHumbertData.IsPositive.sum_twistedTranslate_mul_twistedTranslate: Schur
  orthogonality for theta translates over a dual-lattice orbit modulo L.
* TauCeti.AppellHumbertData.IsPositive.sum_dualQuotient_twistedTranslate_mul: specialization
  to a full system of representatives of L^⊥ / L.

## Provenance

Adapted from New.IsAppellHumbert.sum_shift_mul_shift (file
src/Lib/Shimura/ThetaNormality/NormalGeneration.lean) in grh-lean
(https://github.com/lsernau/grh-lean, commit 72fead102f663d5c7a407964a13dc0cf9d977207,
Apache 2.0, Copyright 2026 Anthropic, PBC).
-/

public section

open Complex Finset Module
open scoped Real

namespace TauCeti.AppellHumbertData

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] {L : Submodule ℤ V}
  {D : AppellHumbertData L}

/-- The twisted translations by -u and u are mutual inverses: U_{-u} (U_u f) = f. -/
@[simp]
theorem twistedTranslate_neg_twistedTranslate (u : V) (f : V → ℂ) :
    D.twistedTranslate (-u) (D.twistedTranslate u f) = f := by
  rw [D.twistedTranslate_twistedTranslate, map_neg, LinearMap.neg_apply,
    D.riemannForm_self, neg_zero, Complex.ofReal_zero, mul_zero, neg_zero, exp_zero, one_smul,
    neg_add_cancel, D.twistedTranslate_zero]

variable [FiniteDimensional ℂ V] [DiscreteTopology L] [IsZLattice ℝ L]

/-- **Schur orthogonality for theta translates.** Let  : T → L^⊥ be a finite family in the dual
lattice such that translation by every 	 ∈ L^⊥ permutes the classes of  s modulo L. Then
for all , g ∈ D.thetaSpace and z, w ∈ V,
√[L^⊥ : L] * ∑ s : T, U_{-a s} g z * U_{a s} f w = |T| * f z * g w. -/
theorem IsPositive.sum_twistedTranslate_mul_twistedTranslate (hD : D.IsPositive)
    {T : Type*} [Fintype T] (a : T → D.riemannForm.dualSubmodule L)
    (ha : ∀ t : D.riemannForm.dualSubmodule L, ∃ e : T ≃ T,
      ∀ s : T, ((t + a s - a (e s) : D.riemannForm.dualSubmodule L) : V) ∈ L)
    (f g : D.thetaSpace) (z w : V) :
    ((L.toAddSubgroup.relIndex (D.riemannForm.dualSubmodule L).toAddSubgroup).sqrt : ℂ) *
        ∑ s : T, D.twistedTranslate (-(a s : V)) g z * D.twistedTranslate (a s : V) f w =
      Fintype.card T * f.val z * g.val w := by
  let Q : Module.End ℂ D.thetaSpace :=
    ∑ s : T, ((LinearMap.proj z ∘ₗ D.twistedTranslate (-(a s : V))).domRestrict _).smulRight
      (D.twistedTranslateEnd (a s) f)
  obtain ⟨c, hQ⟩ : ∃ c : ℂ, Q = c • 1 := by
    refine hD.exists_eq_smul_one_of_commute fun t ↦ LinearMap.ext fun x ↦ Subtype.ext ?_
    obtain ⟨e, he_mem⟩ := ha t
    have term_eq (s : T) :
        D.twistedTranslate (-(a s : V)) x z •
          D.twistedTranslate t (D.twistedTranslate (a s : V) f) =
        D.twistedTranslate (-(a (e s) : V)) (D.twistedTranslate t x) z •
          D.twistedTranslate (a (e s) : V) f := by
      let l : L := ⟨((t + a s - a (e s) : D.riemannForm.dualSubmodule L) : V), he_mem s⟩
      have hκ (y : V → ℂ) (hy : y ∈ D.thetaSpace) :
          D.twistedTranslate t (D.twistedTranslate (a s : V) y) =
            (exp (-(π * I * D.riemannForm t (a s))) *
              (exp (π * I * D.riemannForm (a (e s)) l) * D.semichar l)) •
              D.twistedTranslate (a (e s) : V) y := by
        rw [D.twistedTranslate_twistedTranslate,
          show (t : V) + (a s : V) = (a (e s) : V) + (l : V) by simp [l],
          twistedTranslate_add_eq_smul_of_mem_thetaSpace hy _ l, smul_smul]
      have hx := hκ _ (twistedTranslate_mem_thetaSpace_of_mem_dualSubmodule
        (neg_mem (a s).property) x.property)
      rw [show D.twistedTranslate (a s : V) (D.twistedTranslate (-(a s : V)) x) = x by
        simpa using twistedTranslate_neg_twistedTranslate (D := D) (-(a s : V)) x] at hx
      rw [hκ f f.property, hx, map_smul, twistedTranslate_neg_twistedTranslate,
        Pi.smul_apply, smul_eq_mul, smul_smul, mul_comm]
    simp only [mul_apply_eq_comp, coe_twistedTranslateEnd_apply, Q, LinearMap.sum_apply,
      Submodule.coe_sum, map_sum, LinearMap.smulRight_apply, LinearMap.domRestrict_apply,
      LinearMap.comp_apply, LinearMap.proj_apply, SetLike.val_smul, map_smul]
    exact Fintype.sum_equiv e _ _ term_eq
  have := hD.finiteDimensional_thetaSpace
  have hsum : ∑ s : T, D.twistedTranslate (-(a s : V)) g z * D.twistedTranslate (a s : V) f w =
      c * g.val w := by
    simpa [Q] using congrArg (fun S : Module.End ℂ D.thetaSpace ↦ (S g).val w) hQ
  have htr : (Fintype.card T : ℂ) * f.val z = c * Module.finrank ℂ D.thetaSpace := by
    simpa only [Q, map_sum, LinearMap.trace_smulRight, LinearMap.domRestrict_apply,
      LinearMap.comp_apply, LinearMap.proj_apply, coe_twistedTranslateEnd_apply,
      twistedTranslate_neg_twistedTranslate, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul, map_smul,
      LinearMap.trace_one, smul_eq_mul] using congrArg (LinearMap.trace ℂ D.thetaSpace) hQ
  rw [← hD.finrank_thetaSpace_sq, Nat.sqrt_eq', hsum, ← mul_assoc, mul_comm _ c, ← htr, mul_assoc]

/-- Specialization of Schur orthogonality to a full system of representatives of L^⊥ / L. -/
theorem IsPositive.sum_dualQuotient_twistedTranslate_mul (hD : D.IsPositive)
    [Fintype D.DualQuotient] (f g : D.thetaSpace) (z w : V) :
    ∑ q : D.DualQuotient,
        D.twistedTranslate (-(q.out : V)) g z * D.twistedTranslate (q.out : V) f w =
      (Module.finrank ℂ D.thetaSpace : ℂ) * f.val z * g.val w := by
  have := hD.finiteDimensional_thetaSpace
  have h_pos : (Module.finrank ℂ D.thetaSpace : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr hD.finrank_thetaSpace_pos.ne'
  have h_card : Fintype.card D.DualQuotient = Module.finrank ℂ D.thetaSpace ^ 2 := by
    rw [← Nat.card_eq_fintype_card, hD.finrank_thetaSpace_sq]
    rfl
  have h_schur := hD.sum_twistedTranslate_mul_twistedTranslate (T := D.DualQuotient)
    (fun q ↦ q.out) (fun t ↦ ⟨Equiv.addLeft (QuotientAddGroup.mk t), fun q ↦ by
      have h : QuotientAddGroup.mk
          ((t + q.out - ((QuotientAddGroup.mk t + q : D.DualQuotient).out) :
            D.riemannForm.dualSubmodule L)) = (0 : D.DualQuotient) := by simp
      exact (QuotientAddGroup.eq_zero_iff _).mp h⟩) f g z w
  rw [← hD.finrank_thetaSpace_sq, Nat.sqrt_eq', h_card, Nat.cast_pow, sq] at h_schur
  exact mul_left_cancel₀ h_pos (by linear_combination h_schur)

end TauCeti.AppellHumbertData

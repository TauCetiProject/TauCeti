/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.DeRham.Presentation
import TauCeti.LinearAlgebra.Alternating.ConsCons
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Module

/-!
# The de Rham differential

For an `A`-algebra `B`, this file constructs the de Rham differential
`d : Ωⁿ →ₗ[A] Ωⁿ⁺¹` on the differential forms `Ωⁿ = ⋀[B]^n Ω[B⁄A]`. It is characterised by
`d (c • dv₀ ∧ ⋯ ∧ dvₙ₋₁) = dc ∧ dv₀ ∧ ⋯ ∧ dvₙ₋₁`, the coefficient being differentiated into the
first slot. The differential is `A`-linear but in general not `B`-linear.

The construction differentiates the free differential symbols,
`[c; v] ↦ dc ∧ dv₀ ∧ ⋯ ∧ dvₙ₋₁`, checks that this kills the relations among symbols, and descends
along the differential-symbol presentation `Sₙ ⧸ Rₙ ≃ₗ[A] Ωⁿ`
(`TauCeti.DeRham.symbolQuotientEquiv`).

## Main definitions

* `TauCeti.DeRham.freeDifferential A B n`: the `A`-linear map `Sₙ → Ωⁿ⁺¹` on free symbols.
* `TauCeti.DeRham.d A B n`: the de Rham differential `Ωⁿ →ₗ[A] Ωⁿ⁺¹`.

## Main results

* `TauCeti.DeRham.freeDifferential_relations`: the free differential kills every relation.
* `TauCeti.DeRham.d_elementary`: the value of `d` on elementary forms.
* `TauCeti.DeRham.d_unique`: the elementary-form rule determines `d`.
* `TauCeti.DeRham.d_comp_d`: `d ∘ d = 0`.
* `TauCeti.DeRham.oneEquiv_d_zeroEquiv_symm`: in degree zero, `d` is the universal derivation.

## References

* The Stacks Project, Section 10.132 (Tag 0FKF), the construction of the de Rham complex.
-/

namespace TauCeti.DeRham

open KaehlerDifferential exteriorPower Function

variable (A B : Type*) [CommRing A] [CommRing B] [Algebra A B] (n : ℕ)

public section

/-- The free de Rham differential `[c; v] ↦ dc ∧ dv₀ ∧ ⋯ ∧ dvₙ₋₁` on differential symbols, an
`A`-linear map `Symbols A B n →ₗ[A] Forms A B (n + 1)`. -/
noncomputable def freeDifferential : Symbols A B n →ₗ[A] Forms A B (n + 1) :=
  Finsupp.linearCombination A fun p : B × (Fin n → B) =>
    ιMulti B (n + 1) (Fin.cons (D A B p.1) fun i => D A B (p.2 i))

variable {A B n}

/-- The free differential sends `[c; v]` to `dc ∧ dv₀ ∧ ⋯ ∧ dvₙ₋₁`. -/
@[simp]
theorem freeDifferential_sym (c : B) (v : Fin n → B) :
    freeDifferential A B n (sym A c v) =
      ιMulti B (n + 1) (Fin.cons (D A B c) fun i => D A B (v i)) := by
  rw [← single_eq_sym]
  simp [freeDifferential]

/-- The free differential kills every relation among differential symbols, so it depends only on
the represented form. -/
theorem freeDifferential_relations :
    symbolRelations A B n ≤ LinearMap.ker (freeDifferential A B n) := by
  -- `Fin.cons` forms of `AlternatingMap.map_vecCons_add` and `AlternatingMap.map_vecCons_smul`,
  -- and their analogues in the slot `i + 1`.
  have cons_add (p q : Ω[B⁄A]) (u : Fin n → Ω[B⁄A]) :
      ιMulti B (n + 1) (Fin.cons (p + q) u) =
        ιMulti B (n + 1) (Fin.cons p u) + ιMulti B (n + 1) (Fin.cons q u) :=
    (ιMulti B (n + 1)).map_vecCons_add u p q
  have cons_smul (b : B) (p : Ω[B⁄A]) (u : Fin n → Ω[B⁄A]) :
      ιMulti B (n + 1) (Fin.cons (b • p) u) = b • ιMulti B (n + 1) (Fin.cons p u) :=
    (ιMulti B (n + 1)).map_vecCons_smul u b p
  have slot_add (z p q : Ω[B⁄A]) (u : Fin n → Ω[B⁄A]) (i : Fin n) :
      ιMulti B (n + 1) (Fin.cons z (update u i (p + q))) =
        ιMulti B (n + 1) (Fin.cons z (update u i p)) +
          ιMulti B (n + 1) (Fin.cons z (update u i q)) := by
    simp only [Fin.cons_update, AlternatingMap.map_update_add]
  have slot_smul (z p : Ω[B⁄A]) (b : B) (u : Fin n → Ω[B⁄A]) (i : Fin n) :
      ιMulti B (n + 1) (Fin.cons z (update u i (b • p))) =
        b • ιMulti B (n + 1) (Fin.cons z (update u i p)) := by
    simp only [Fin.cons_update, AlternatingMap.map_update_smul]
  refine symbolRelations_le (fun c e v => ?_) (fun a c v => ?_) (fun c v i x y => ?_)
    (fun c v i x y => ?_) (fun c v i a => ?_) (fun c v i j hv hij => ?_) <;>
    simp only [LinearMap.mem_ker, map_sub, map_smul, freeDifferential_sym,
      apply_update (fun _ => D A B), map_add, Derivation.leibniz]
  · rw [cons_add, sub_sub, sub_self]
  · rw [Derivation.map_smul, ← algebraMap_smul B a (D A B c), cons_smul, algebraMap_smul,
      sub_self]
  · rw [slot_add, sub_sub, sub_self]
  · have h :=
      (ιMulti B (n + 1)).map_cons_update_add (fun k => D A B (v k)) i (D A B x) (D A B y)
    simp only [slot_add, slot_smul, cons_add, cons_smul]
    linear_combination (norm := module) (-c) • h
  · rw [Derivation.map_algebraMap, Fin.cons_update, AlternatingMap.map_update_zero]
  · exact AlternatingMap.map_eq_zero_of_eq _ _ (i := i.succ) (j := j.succ)
      (by simpa using congrArg (D A B) hv) ((Fin.succ_injective _).ne hij)

variable (A B n)

/-- **The de Rham differential** `d : Ωⁿ →ₗ[A] Ωⁿ⁺¹`, the descent of the free differential
along the differential-symbol presentation. It sends `c • dv₀ ∧ ⋯ ∧ dvₙ₋₁` to
`dc ∧ dv₀ ∧ ⋯ ∧ dvₙ₋₁` (`d_elementary`); it is `A`-linear, but not `B`-linear in general. -/
noncomputable def d : Forms A B n →ₗ[A] Forms A B (n + 1) :=
  (symbolRelations A B n).liftQ (freeDifferential A B n) freeDifferential_relations ∘ₗ
    (symbolQuotientEquiv A B n).symm.toLinearMap

variable {A B n}

/-- `d` differentiates the coefficient of an elementary form into the first slot:
`d (c • dv₀ ∧ ⋯ ∧ dvₙ₋₁) = dc ∧ dv₀ ∧ ⋯ ∧ dvₙ₋₁`. -/
@[simp]
theorem d_elementary (c : B) (v : Fin n → B) :
    d A B n (elementary A c v) =
      ιMulti B (n + 1) (Fin.cons (D A B c) fun i => D A B (v i)) := by
  rw [← symbolMap_sym, ← symbolQuotientEquiv_mk]
  simp only [d, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply,
    Submodule.liftQ_apply, freeDifferential_sym]

/-- `d` composed with the evaluation of symbols is the free differential. -/
theorem d_comp_symbolMap : d A B n ∘ₗ symbolMap A B n = freeDifferential A B n :=
  symbols_hom_ext fun c v => by simp

/-- **Uniqueness of the de Rham differential.** An `A`-linear map `Ωⁿ → Ωⁿ⁺¹` that sends every
elementary form `c • dv₀ ∧ ⋯ ∧ dvₙ₋₁` to `dc ∧ dv₀ ∧ ⋯ ∧ dvₙ₋₁` is `d`. -/
theorem d_unique (f : Forms A B n →ₗ[A] Forms A B (n + 1))
    (hf : ∀ (c : B) (v : Fin n → B),
      f (elementary A c v) =
        ιMulti B (n + 1) (Fin.cons (D A B c) fun i => D A B (v i))) :
    f = d A B n :=
  forms_hom_ext fun c v => by rw [hf, d_elementary]

/-- **The de Rham differential squares to zero.** -/
@[simp]
theorem d_comp_d : d A B (n + 1) ∘ₗ d A B n = 0 := by
  refine forms_hom_ext fun c v => ?_
  have h : (ιMulti B (n + 1) (Fin.cons (D A B c) fun i => D A B (v i)) :
      Forms A B (n + 1)) = elementary A 1 (Fin.cons c v) := by
    rw [elementary_def, one_smul]
    exact congrArg _ (Fin.comp_cons (D A B) c v).symm
  simp only [LinearMap.comp_apply, LinearMap.zero_apply, d_elementary, h,
    Derivation.map_one_eq_zero]
  exact AlternatingMap.map_coord_zero _ 0 (Fin.cons_zero _ _)

/-- `d (d ω) = 0`. -/
@[simp]
theorem d_d (ω : Forms A B n) : d A B (n + 1) (d A B n ω) = 0 :=
  LinearMap.congr_fun d_comp_d ω

/-- In degree zero, `d` is the universal derivation: under `Ω⁰ ≃ B` and `Ω¹ ≃ Ω[B⁄A]`, it sends
`b` to `D A B b`. -/
theorem oneEquiv_d_zeroEquiv_symm (b : B) :
    exteriorPower.oneEquiv B Ω[B⁄A] (d A B 0 ((exteriorPower.zeroEquiv B Ω[B⁄A]).symm b)) =
      D A B b := by
  have h : (exteriorPower.zeroEquiv B Ω[B⁄A]).symm b = elementary A b ![] := by
    rw [LinearEquiv.symm_apply_eq, elementary_def, map_smul, exteriorPower.zeroEquiv_ιMulti,
      smul_eq_mul, mul_one]
  rw [h, d_elementary, exteriorPower.oneEquiv_ιMulti, Fin.cons_zero]

end

end TauCeti.DeRham

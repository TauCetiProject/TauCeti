/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Henselian.Radical
public import TauCeti.RingTheory.Henselian.Quotient
import Mathlib.Tactic.LinearCombination

/-!
# Henselian pairs and nested ideals

For ideals `J ≤ I`, the pair `(R, I)` is henselian if and only if `(R, J)` and
`(R ⧸ J, I/J)` are henselian. In particular, henselianity passes to smaller ideals
and to quotients by ideals contained in the henselian ideal. These results allow
simple-root lifting to be performed in two stages, first modulo `J` and then in `R`.

Combined with henselianity along radicals, the smaller-ideal theorem also shows that
henselianity depends only on the radical of the ideal. No Noetherian, completeness,
locality or finite-generation hypotheses are needed.

## References

* [Stacks Project, Lemma 15.11.9](https://stacks.math.columbia.edu/tag/0DYD),
  henselian pairs and nested ideals.
* [Stacks Project, Lemma 15.11.7](https://stacks.math.columbia.edu/tag/09XJ),
  henselian pairs and radicals.
-/

public section

open Polynomial

namespace Ideal

variable {R : Type*} [CommRing R] {I J : Ideal R}

/-- Every ideal contained in a henselian ideal is henselian. -/
theorem henselianRing_of_le (hJI : J ≤ I) [HenselianRing R I] : HenselianRing R J where
  jac := hJI.trans HenselianRing.jac
  is_henselian f hf a₀ ha hu := by
    have := isLocalHom_of_le_jacobson_bot J (hJI.trans HenselianRing.jac)
    have hder : IsUnit (f.derivative.eval a₀) := isUnit_of_map_unit _ _ hu
    obtain ⟨a, hfa, haa⟩ := HenselianRing.is_henselian f hf a₀ (hJI ha)
      (hder.map (Quotient.mk I))
    obtain ⟨c, hc⟩ := f.exists_mul_sq_add_linear_part_eq_eval_add a₀ (a - a₀)
    have hunit : IsUnit (c * (a - a₀) + f.derivative.eval a₀) := by
      have := isLocalHom_of_le_jacobson_bot I HenselianRing.jac
      apply isUnit_of_map_unit (Quotient.mk I)
      simpa [map_add, map_mul, Quotient.eq_zero_iff_mem.2 haa] using
        hder.map (Quotient.mk I)
    refine ⟨a, hfa, (J.unit_mul_mem_iff_mem hunit).1 ?_⟩
    have heq : (c * (a - a₀) + f.derivative.eval a₀) * (a - a₀) = -f.eval a₀ := by
      have hsum : a₀ + (a - a₀) = a := by ring
      rw [hsum, hfa.eq_zero] at hc
      linear_combination hc
    rw [heq]
    exact J.neg_mem ha

/-- Simple-root lifting can be performed first in `R/J` and then in `R`: henselianity
along `J` and along `I/J` implies henselianity along `I`. -/
theorem henselianRing_of_quotient (hJI : J ≤ I) [HenselianRing R J]
    [HenselianRing (R ⧸ J) (I.map (Quotient.mk J))] : HenselianRing R I := by
  have hjac : I ≤ jacobson ⊥ := by
    have h : I ≤ (I.map (Quotient.mk J)).comap (Quotient.mk J) := le_comap_map
    refine h.trans ((comap_mono HenselianRing.jac).trans ?_)
    rw [comap_jacobson_of_surjective Quotient.mk_surjective,
      ← RingHom.ker_eq_comap_bot, mk_ker]
    exact (jacobson_mono HenselianRing.jac).trans_eq jacobson_idem
  have := isLocalHom_of_le_jacobson_bot I hjac
  refine ⟨hjac, fun f hf a₀ ha hu ↦ ?_⟩
  have hunit : IsUnit (f.derivative.eval a₀) := isUnit_of_map_unit _ _ hu
  obtain ⟨b, hb, hba⟩ := HenselianRing.is_henselian
    (I := I.map (Quotient.mk J)) (f.map (Quotient.mk J)) (hf.map _) (Quotient.mk J a₀)
    (by simpa [eval_map_apply] using mem_map_of_mem (Quotient.mk J) ha)
    (by simpa [derivative_map, eval_map_apply] using
      (hunit.map (Quotient.mk J)).map (Quotient.mk (I.map (Quotient.mk J))))
  obtain ⟨b, rfl⟩ := Quotient.mk_surjective b
  have hfb : f.eval b ∈ J := by
    apply Quotient.eq_zero_iff_mem.1
    simpa [eval_map_apply] using hb.eq_zero
  have hbaI : b - a₀ ∈ I := by
    rw [← comap_map_mk hJI, mem_comap, map_sub]
    exact hba
  have hder : IsUnit (Quotient.mk J (f.derivative.eval b)) := by
    have heq : Quotient.mk I b = Quotient.mk I a₀ := Quotient.eq.2 hbaI
    have hderI : IsUnit (Quotient.mk I (f.derivative.eval b)) := by
      rw [← eval_map_apply, heq, eval_map_apply]
      exact hunit.map (Quotient.mk I)
    exact (isUnit_of_map_unit (Quotient.mk I) _ hderI).map (Quotient.mk J)
  obtain ⟨a, hfa, hab⟩ := HenselianRing.is_henselian f hf b hfb hder
  exact ⟨a, hfa, by simpa using I.add_mem (hJI hab) hbaI⟩

/-- For `J ≤ I`, a pair is henselian exactly when its two successive pairs are henselian. -/
@[stacks 0DYD]
theorem henselianRing_iff_quotient (hJI : J ≤ I) :
    HenselianRing R I ↔ HenselianRing R J ∧ HenselianRing (R ⧸ J) (I.map (Quotient.mk J)) := by
  constructor
  · intro h
    exact ⟨henselianRing_of_le hJI, inferInstance⟩
  · rintro ⟨hJ, hquot⟩
    exact henselianRing_of_quotient hJI

/-- Passing to the radical of an ideal preserves and reflects henselianity. -/
@[simp]
theorem henselianRing_radical_iff : HenselianRing R I.radical ↔ HenselianRing R I :=
  ⟨fun _ ↦ henselianRing_of_le le_radical, fun _ ↦ inferInstance⟩

end Ideal

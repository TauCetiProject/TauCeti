/-
Copyright (c) 2026 Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
public import Mathlib.RingTheory.AlgebraicIndependent.Transcendental
import Mathlib.RingTheory.Algebraic.Cardinality
import Mathlib.RingTheory.AlgebraicIndependent.AlgebraicClosure
import Mathlib.RingTheory.AlgebraicIndependent.RankAndCardinality

/-!
# Transcendence bases and transcendence degree in towers

This file records consequences of algebraic independence and Mathlib's transcendence-degree
tower inequality `lift_trdeg_add_le` for towers of commutative rings, and compares transcendence
bases of two domains with comparable transcendence degrees.

## Main results

* `TauCeti.trdeg_eq_of_isAlgebraic_base`: an injective algebraic extension of the base ring
  preserves transcendence degree in any commutative algebra over the larger base.
* `TauCeti.isAlgebraic_of_trdeg_le`: if the top ring has finite transcendence degree over the
  middle ring, at least its transcendence degree over the bottom ring, then the middle ring is
  algebraic over the bottom ring; `TauCeti.isAlgebraic_of_trdeg_eq_one` is the case of
  transcendence degree one.
* `Transcendental.exists_isTranscendenceBasis_mem`: a transcendental element lies in a
  transcendence basis.
* `IsTranscendenceBasis.nonempty_embedding_of_lift_trdeg_le`,
  `IsTranscendenceBasis.nonempty_equiv_of_lift_trdeg_eq`: comparing transcendence degrees of two
  domains compares the index types of their transcendence bases.
* `IsTranscendenceBasis.cardinalMk_eq_of_aleph0_lt`: a transcendence basis of an uncountable
  integral domain over a countable commutative ring has the domain's cardinality.
* `TauCeti.trdeg_eq_cardinalMk`: the transcendence degree of an uncountable integral domain over a
  countable field is its cardinality.
-/

public section

namespace TauCeti

universe u v w

variable {R : Type u} {S : Type v} {A : Type w}
variable [CommRing R] [CommRing S] [CommRing A]
variable [Algebra R S] [Algebra S A] [Algebra R A] [IsScalarTower R S A]

/-- An injective algebraic extension of the base ring preserves transcendence degree, provided
the larger base has no zero divisors. The top algebra may have zero divisors, and its structure
map need not be injective. -/
theorem trdeg_eq_of_isAlgebraic_base
    [NoZeroDivisors S] [FaithfulSMul R S] [Algebra.IsAlgebraic R S] :
    Algebra.trdeg S A = Algebra.trdeg R A := by
  -- Mathlib's algebraic-independence transfer identifies the sets in the defining supremum.
  rw [Algebra.trdeg, Algebra.trdeg,
    funext fun _ ↦ propext (Algebra.IsAlgebraic.algebraicIndependent_iff R S (A := A)).symm]

variable [Nontrivial R] [FaithfulSMul R S] [FaithfulSMul S A]

/-- In an injective tower `R → S → A`, if `A` has finite transcendence degree over `S` that is
at least its transcendence degree over `R`, then `S` is algebraic over `R`. Finiteness allows
cancellation in the transcendence-degree tower inequality `lift_trdeg_add_le`. -/
theorem isAlgebraic_of_trdeg_le (h : Algebra.trdeg R A ≤ Algebra.trdeg S A)
    (hfin : Algebra.trdeg S A < Cardinal.aleph0) : Algebra.IsAlgebraic R S := by
  rw [← trdeg_eq_zero_iff, ← Cardinal.lift_eq_zero.{w}, ← nonpos_iff_eq_zero,
    ← Cardinal.add_le_add_iff_of_lt_aleph0 (Cardinal.lift_lt_aleph0.mpr hfin), zero_add]
  exact lift_trdeg_add_le.trans (Cardinal.lift_le.mpr h)

omit [FaithfulSMul R S] [FaithfulSMul S A] in
/-- In a tower `R → S → A`, if `A` has transcendence degree one over both `R` and `S`, then `S` is
algebraic over `R`. The structure maps are injective because the transcendence degrees are
nonzero. -/
theorem isAlgebraic_of_trdeg_eq_one (h : Algebra.trdeg R A = 1) (h' : Algebra.trdeg S A = 1) :
    Algebra.IsAlgebraic R S := by
  have hSA : Function.Injective (algebraMap S A) := by
    by_contra hn
    exact one_ne_zero (h'.symm.trans (trdeg_eq_zero_of_not_injective hn))
  have hRA : Function.Injective (algebraMap R A) := by
    by_contra hn
    exact one_ne_zero (h.symm.trans (trdeg_eq_zero_of_not_injective hn))
  rw [IsScalarTower.algebraMap_eq R S A, RingHom.coe_comp] at hRA
  have : FaithfulSMul S A := (faithfulSMul_iff_algebraMap_injective S A).2 hSA
  have : FaithfulSMul R S := (faithfulSMul_iff_algebraMap_injective R S).2 hRA.of_comp
  exact isAlgebraic_of_trdeg_le (h.trans h'.symm).le (h' ▸ Cardinal.one_lt_aleph0)

end TauCeti

/-- An element transcendental over `R` lies in some transcendence basis over `R`. -/
theorem Transcendental.exists_isTranscendenceBasis_mem {R A : Type*} [CommRing R] [CommRing A]
    [Algebra R A] {x : A} (hx : Transcendental R x) :
    ∃ s : Set A, x ∈ s ∧ IsTranscendenceBasis R ((↑) : s → A) := by
  obtain ⟨s, hxs, hs⟩ := exists_isTranscendenceBasis_superset (s := {x})
    ((algebraicIndependent_singleton_iff ⟨x, Set.mem_singleton x⟩).2 hx)
  exact ⟨s, hxs (Set.mem_singleton x), hs⟩

namespace IsTranscendenceBasis

open Cardinal

universe u₁ u₂ u₃ u₄

variable {R : Type*} {A : Type u₁} {B : Type u₂} [CommRing R] [Nontrivial R] [CommRing A]
  [NoZeroDivisors A] [CommRing B] [NoZeroDivisors B] [Algebra R A] [Algebra R B]
  {ι : Type u₃} {κ : Type u₄} {v : ι → A} {w : κ → B}

/-- If the domain `A` has transcendence degree over `R` at most that of the domain `B`, then the
index type of a transcendence basis of `A` embeds into that of a transcendence basis of `B`. -/
theorem nonempty_embedding_of_lift_trdeg_le (hv : IsTranscendenceBasis R v)
    (hw : IsTranscendenceBasis R w)
    (h : lift.{u₂} (Algebra.trdeg R A) ≤ lift.{u₁} (Algebra.trdeg R B)) : Nonempty (ι ↪ κ) := by
  -- Lift `#ι = trdeg R A`, `#κ = trdeg R B` and `h` to the common universe `max u₁ u₂ u₃ u₄`.
  have h1 := congrArg lift.{max u₂ u₄} hv.lift_cardinalMk_eq_trdeg
  have h2 := congrArg lift.{max u₁ u₃} hw.lift_cardinalMk_eq_trdeg
  have h3 := lift_le.{max u₃ u₄}.2 h
  simp only [lift_lift] at h1 h2 h3
  refine lift_mk_le'.1 (lift_le.{max u₁ u₂}.1 ?_)
  rw [lift_lift, lift_lift]
  exact h1.trans_le (h3.trans_eq h2.symm)

/-- If the domains `A` and `B` have the same transcendence degree over `R`, then the index types
of transcendence bases of `A` and of `B` are in bijection. -/
theorem nonempty_equiv_of_lift_trdeg_eq (hv : IsTranscendenceBasis R v)
    (hw : IsTranscendenceBasis R w)
    (h : lift.{u₂} (Algebra.trdeg R A) = lift.{u₁} (Algebra.trdeg R B)) : Nonempty (ι ≃ κ) := by
  -- Lift `#ι = trdeg R A`, `#κ = trdeg R B` and `h` to the common universe `max u₁ u₂ u₃ u₄`.
  have h1 := congrArg lift.{max u₂ u₄} hv.lift_cardinalMk_eq_trdeg
  have h2 := congrArg lift.{max u₁ u₃} hw.lift_cardinalMk_eq_trdeg
  have h3 := congrArg lift.{max u₃ u₄} h
  simp only [lift_lift] at h1 h2 h3
  refine lift_mk_eq'.1 (lift_inj.{_, max u₁ u₂}.1 ?_)
  rw [lift_lift, lift_lift]
  exact h1.trans (h3.trans h2.symm)

/-- A transcendence basis of an uncountable integral domain `E` over a countable commutative ring
`R` has the same cardinality as `E`. This generalizes Mathlib's
`IsAlgClosed.cardinal_eq_cardinal_transcendence_basis_of_aleph0_lt` from algebraically closed
fields to arbitrary integral domains. -/
theorem cardinalMk_eq_of_aleph0_lt {R : Type u} {E : Type v} {ι : Type w} [CommRing R]
    [Countable R] [CommRing E] [IsDomain E] [Algebra R E] {x : ι → E}
    (hx : IsTranscendenceBasis R x) (hE : ℵ₀ < #E) :
    Cardinal.lift.{v} #ι = Cardinal.lift.{w} #E := by
  have : Nontrivial R := RingHom.domain_nontrivial (algebraMap R E)
  -- Rule out an empty basis via `isEmpty_iff_isAlgebraic` and
  -- `Algebra.IsAlgebraic.lift_cardinalMk_le_max`, then apply `lift_cardinalMk_eq_max_lift`.
  have : Nonempty ι := by
    by_contra hne
    rw [not_nonempty_iff] at hne
    have : Algebra.IsAlgebraic R E := hx.isEmpty_iff_isAlgebraic.1 hne
    have hinj : Function.Injective (algebraMap R E) := fun a b hab ↦
      MvPolynomial.C_injective ι R (algebraicIndependent_iff_injective_aeval.1 hx.1
        (by simpa using hab))
    have : IsDomain R := hinj.isDomain (algebraMap R E)
    have : Module.IsTorsionFree R E := Module.isTorsionFree_iff_algebraMap_injective.2 hinj
    have hle : lift.{u} #E ≤ ℵ₀ :=
      (Algebra.IsAlgebraic.lift_cardinalMk_le_max R E).trans (sup_le (by simp) le_rfl)
    exact not_le_of_gt (aleph0_lt_lift.2 hE) hle
  have h := hx.lift_cardinalMk_eq_max_lift
  have hE' : ℵ₀ < lift.{max u w} #E := aleph0_lt_lift.2 hE
  have hι : ℵ₀ < lift.{max u v} #ι := by
    by_contra hle
    exact not_le_of_gt hE' (h.le.trans (sup_le (sup_le (by simp) (le_of_not_gt hle)) le_rfl))
  have hR : lift.{max v w} #R ≤ lift.{max u v} #ι := le_trans (by simp) hι.le
  rw [sup_eq_right.2 hR, sup_eq_left.2 hι.le] at h
  exact Cardinal.lift_injective.{u, max v w} (by simpa using h.symm)

end IsTranscendenceBasis

/-- The transcendence degree of an uncountable integral domain `E` over a countable commutative
ring `k` acting faithfully on `E` is the cardinality of `E`. -/
theorem TauCeti.trdeg_eq_cardinalMk {k : Type*} {E : Type u} [CommRing k] [Countable k]
    [CommRing E] [IsDomain E] [Algebra k E] [FaithfulSMul k E]
    (hE : Cardinal.aleph0 < Cardinal.mk E) :
    Algebra.trdeg k E = Cardinal.mk E := by
  have : Nontrivial k := RingHom.domain_nontrivial (algebraMap k E)
  obtain ⟨t, ht⟩ := exists_isTranscendenceBasis k E
  rw [← ht.cardinalMk_eq_trdeg]
  exact Cardinal.lift_inj.1 (ht.cardinalMk_eq_of_aleph0_lt hE)

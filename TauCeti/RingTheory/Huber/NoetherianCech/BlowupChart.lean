/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Huber.NoetherianCech.Topology
public import TauCeti.RingTheory.GradedAlgebra.SubmoduleBlowup

/-!
# Blowup charts and the rational Čech complex

`locSubring_numerators_eq_fractionSubalgebra` identifies the ring of definition on a face
of the rational Čech complex with the fraction subalgebra of the corresponding submodule
blowup chart. Together with `facePair_ringOfDefinition`, this compares the coefficient
rings used for the filtration on the Čech complex and for the affine charts of the blowup.
The comparison uses `PairOfDefinition.locSubring_eq_adjoin` and
`submoduleBlowup.fractionSubalgebra_le_iff`.

## References

* R. Huber, *A generalization of formal schemes and rigid analytic varieties*, Math. Z. 217
  (1994), §2, (1.2)(ii) and (1.3.1)(ii).
-/

public section

open TauCeti.AlgebraicGeometry.submoduleBlowup TauCeti.Localization

namespace TauCeti.Huber.NoetherianCech

variable {B : Type*} [CommRing B] {ι : Type*} (f : ι → B)
  [TopologicalSpace B] (P : PairOfDefinition B)

/-- The ring generated over the ring of definition by the degree-`p` numerators over
`∏ i ∈ S, f i` is the submodule blowup's fraction subalgebra for the denominators `S.image f`.
Repeated denominator values do not affect the subring. See Huber (1994), §2, (1.2)(ii). -/
theorem locSubring_numerators_eq_fractionSubalgebra [DecidableEq B] {p : ℕ} {S : Finset ι}
    (hS : S.card = p + 1) {L : Type*} [CommRing L] [Algebra B L]
    [IsLocalization.Away (∏ i ∈ S, f i) L] :
    P.locSubring (numerators f p) (∏ i ∈ S, f i) L =
      (fractionSubalgebra P.ringOfDefinition (Set.range f) (S.image f) L).toSubring := by
  classical
  let e := S.equivFinOfCardEq hS
  let d : Fin (p + 1) → ι := fun k ↦ (e.symm k).val
  have hprod : ∏ k, f (d k) = ∏ i ∈ S, f i :=
    (e.symm.prod_comp fun a ↦ f a.val).trans (Finset.prod_subtype S (fun _ ↦ Iff.rfl) f).symm
  have hs := IsLocalization.Away.algebraMap_isUnit (S := L) (∏ i ∈ S, f i)
  rw [P.locSubring_eq_adjoin]
  apply congrArg Subalgebra.toSubring
  refine le_antisymm (Algebra.adjoin_le ?_) (fractionSubalgebra_le_iff.mpr ?_)
  · rintro _ ⟨⟨t, ht⟩, rfl⟩
    obtain ⟨j, rfl⟩ := (mem_numerators f).mp ht
    have hfactor (k : Fin (p + 1)) :
        ∃ z, algebraMap B L (f (d k)) * z = algebraMap B L (f (j k)) := by
      obtain ⟨v, hv⟩ := (IsLocalization.Away.isUnit_of_dvd (S := L) (∏ i ∈ S, f i)
        (Finset.dvd_prod_of_mem f (e.symm k).property)).exists_right_inv
      exact ⟨v * algebraMap B L (f (j k)), by rw [← mul_assoc, hv, one_mul]⟩
    choose z hz using hfactor
    have heq : (divBy (∏ k, f (j k)) (∏ i ∈ S, f i) : L) = ∏ k, z k := by
      apply hs.mul_left_cancel
      rw [algebraMap_mul_divBy, ← hprod]
      simp only [map_prod, ← Finset.prod_mul_distrib, hz]
    simp only [SetLike.mem_coe, heq]
    exact prod_mem fun k _ ↦ mem_fractionSubalgebra_of_mul_eq (Set.mem_range_self _)
      (Finset.mem_image_of_mem f (e.symm k).property) (hz k)
  · rintro _ ⟨i, rfl⟩ _ ha z hz
    obtain ⟨a, haS, rfl⟩ := Finset.mem_image.mp ha
    let k := e ⟨a, haS⟩
    have hdk : d k = a := congrArg Subtype.val (e.symm_apply_apply ⟨a, haS⟩)
    let j := Function.update d k i
    have heq : algebraMap B L (∏ b ∈ S, f b) * z = algebraMap B L (∏ l, f (j l)) := by
      have hj : f ∘ j = Function.update (f ∘ d) k (f i) := Function.comp_update _ _ _ _
      have hnum : ∏ l, f (j l) = f i * ∏ l ∈ Finset.univ.erase k, f (d l) := by
        rw [← Function.comp_def, hj, Finset.prod_update_of_mem (Finset.mem_univ _),
          Finset.sdiff_singleton_eq_erase]
        rfl
      have hden : f (d k) * (∏ l ∈ Finset.univ.erase k, f (d l)) = ∏ l, f (d l) :=
        Finset.mul_prod_erase Finset.univ (fun l ↦ f (d l)) (Finset.mem_univ k)
      -- Separate the selected factor before applying the equation for the individual fraction.
      rw [hnum, ← hprod, ← hden, hdk, map_mul, map_mul, mul_right_comm, hz]
    have hdiv : (divBy (∏ l, f (j l)) (∏ b ∈ S, f b) : L) = z :=
      hs.mul_left_cancel ((algebraMap_mul_divBy _ _).trans heq.symm)
    exact Algebra.subset_adjoin ⟨⟨_, (mem_numerators f).mpr ⟨j, rfl⟩⟩, hdiv⟩

end TauCeti.Huber.NoetherianCech

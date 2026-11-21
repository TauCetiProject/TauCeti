/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Idempotents
public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import TauCeti.Topology.LocallyConstant.Fiber

/-!
# Clopen subsets of `PrimeSpectrum` and idempotents

Mathlib's `PrimeSpectrum.isIdempotentElemEquivClopens` identifies idempotents `e : R` of a
commutative ring with clopen subsets `U` of `Spec R` via `U = D(e)`. This file records
compatibility of that identification with membership in prime ideals, disjoint unions, complete
orthogonal families of idempotents (in particular for the clopen fibers of a locally constant
function on `Spec R`), and ring homomorphisms.

## Main results

* `PrimeSpectrum.mem_asIdeal_isIdempotentElemEquivClopens_symm_iff`: `e_U ∈ p` iff `p ∉ U`.
* `PrimeSpectrum.isIdempotentElemEquivClopens_symm_mul_eq_zero_of_disjoint`: disjoint clopens give
  orthogonal idempotents.
* `PrimeSpectrum.isIdempotentElemEquivClopens_symm_finset_sup`: finite disjoint unions correspond
  to sums of idempotents.
* `PrimeSpectrum.completeOrthogonalIdempotents_isIdempotentElemEquivClopens_symm` and
  `PrimeSpectrum.completeOrthogonalIdempotents_fiberClopens`: finite clopen partitions of `Spec R`
  (in particular the fibers of a locally constant function) give complete orthogonal families of
  idempotents.
* `PrimeSpectrum.map_isIdempotentElemEquivClopens_symm`: compatibility of clopen idempotents with
  ring homomorphisms.
-/

public section

open TopologicalSpace

namespace PrimeSpectrum

section CommRing

variable {R : Type*} [CommRing R]

/-- The idempotent of a clopen `U` lies in a prime ideal `p` if and only if `p ∉ U`. -/
theorem mem_asIdeal_isIdempotentElemEquivClopens_symm_iff
    (U : Clopens (PrimeSpectrum R)) (p : PrimeSpectrum R) :
    (isIdempotentElemEquivClopens.symm U).val ∈ p.asIdeal ↔ p ∉ U := by
  have h : p ∈ basicOpen (isIdempotentElemEquivClopens.symm U).val ↔ p ∈ U := by
    rw [basicOpen_isIdempotentElemEquivClopens_symm]; rfl
  exact (not_iff_comm.1 h).symm

/-- Disjoint clopens have orthogonal idempotents. -/
theorem isIdempotentElemEquivClopens_symm_mul_eq_zero_of_disjoint
    {U V : Clopens (PrimeSpectrum R)} (h : Disjoint U V) :
    (isIdempotentElemEquivClopens.symm U).val * (isIdempotentElemEquivClopens.symm V).val = 0 := by
  have hinf := congrArg Subtype.val (isIdempotentElemEquivClopens_symm_inf (R := R) U V)
  rw [h.eq_bot, isIdempotentElemEquivClopens_symm_bot] at hinf
  exact hinf.symm

/-- The idempotent of a disjoint union of two clopens is the sum of their idempotents. -/
theorem isIdempotentElemEquivClopens_symm_sup_of_disjoint
    {U V : Clopens (PrimeSpectrum R)} (h : Disjoint U V) :
    (isIdempotentElemEquivClopens.symm (U ⊔ V)).val =
      (isIdempotentElemEquivClopens.symm U).val + (isIdempotentElemEquivClopens.symm V).val := by
  rw [congrArg Subtype.val (isIdempotentElemEquivClopens_symm_sup (R := R) U V)]
  dsimp only
  rw [isIdempotentElemEquivClopens_symm_mul_eq_zero_of_disjoint h, sub_zero]

/-- The idempotent of a finite pairwise-disjoint union of clopens is the sum of their
idempotents. -/
theorem isIdempotentElemEquivClopens_symm_finset_sup {ι : Type*} (s : Finset ι)
    (U : ι → Clopens (PrimeSpectrum R)) (hdisj : (s : Set ι).PairwiseDisjoint U) :
    (isIdempotentElemEquivClopens.symm (s.sup U)).val =
      ∑ i ∈ s, (isIdempotentElemEquivClopens.symm (U i)).val := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.sup_empty, Finset.sum_empty, isIdempotentElemEquivClopens_symm_bot]
  | insert a s ha ih =>
    have hda : Disjoint (U a) (s.sup U) := Finset.disjoint_sup_right.2 fun b hb ↦
      hdisj (Finset.mem_insert_self a s) (Finset.mem_insert_of_mem hb) (fun h ↦ ha (h ▸ hb))
    rw [Finset.sup_insert, isIdempotentElemEquivClopens_symm_sup_of_disjoint hda,
      Finset.sum_insert ha, ih (hdisj.subset (Finset.subset_insert a s))]

/-- A finite clopen partition of `Spec R` gives a complete orthogonal family of idempotents. -/
theorem completeOrthogonalIdempotents_isIdempotentElemEquivClopens_symm {ι : Type*} [Fintype ι]
    (U : ι → Clopens (PrimeSpectrum R)) (hdisj : Pairwise (Function.onFun Disjoint U))
    (hcover : Finset.univ.sup U = ⊤) :
    CompleteOrthogonalIdempotents fun i ↦ (isIdempotentElemEquivClopens.symm (U i)).val where
  idem i := (isIdempotentElemEquivClopens.symm (U i)).property
  ortho _ _ hij := isIdempotentElemEquivClopens_symm_mul_eq_zero_of_disjoint (hdisj hij)
  complete := by
    rw [← isIdempotentElemEquivClopens_symm_finset_sup Finset.univ U (fun _ _ _ _ h ↦ hdisj h),
      hcover, isIdempotentElemEquivClopens_symm_top]

/-- A ring homomorphism carries the idempotent of a clopen `U ⊆ Spec R` to the idempotent of its
preimage in `Spec S`. -/
theorem map_isIdempotentElemEquivClopens_symm {S : Type*} [CommRing S] (f : R →+* S)
    (U : Clopens (PrimeSpectrum R)) :
    f (isIdempotentElemEquivClopens.symm U).val =
      (isIdempotentElemEquivClopens.symm
        ⟨comap f ⁻¹' U, U.isClopen.preimage (continuous_comap f)⟩).val := by
  apply basicOpen_injOn_isIdempotentElem ((isIdempotentElemEquivClopens.symm U).property.map f)
    (isIdempotentElemEquivClopens.symm _).property
  rw [← comap_basicOpen, basicOpen_isIdempotentElemEquivClopens_symm,
    basicOpen_isIdempotentElemEquivClopens_symm]
  rfl

/-- The idempotents attached to the clopen fibers of a locally constant function on `Spec R` form
a complete orthogonal family indexed by the finite range of the function. -/
theorem completeOrthogonalIdempotents_fiberClopens {α : Type*}
    (f : LocallyConstant (PrimeSpectrum R) α) :
    CompleteOrthogonalIdempotents
      fun a : f.range_finite.toFinset ↦
        (isIdempotentElemEquivClopens.symm (f.fiberClopens a.val)).val :=
  completeOrthogonalIdempotents_isIdempotentElemEquivClopens_symm _
    (fun _ _ hab ↦ f.pairwise_disjoint_fiberClopens (Subtype.coe_ne_coe.2 hab))
    (by simpa [Finset.sup_coe] using f.finset_sup_fiberClopens)

end CommRing

end PrimeSpectrum

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.GaloisRepresentation.GlobalRamification
public import TauCeti.NumberTheory.NumberField.AbsoluteGaloisGroup.Inertia.Basic
import TauCeti.NumberTheory.NumberField.AbsoluteGaloisGroup.Inertia.Image

/-!
# Galois representations with open kernel have finite ramification set

Let `F` be a number field and `G_F` its absolute Galois group. For a finite normal subextension `E`
of `F^alg / F`, the inertia group at a prime above a place `v` of `F` unramified in `E` fixes `E`
pointwise (`TauCeti.GaloisRep.inertiaGroup_le_fixingSubgroup`).

A continuous representation `ρ` of `G_F` whose kernel is open has a kernel containing the fixing
subgroup of some finite normal `E`, by the definition of the Krull topology. It is therefore
unramified at every place unramified in `E`, and since only finitely many places of `F` ramify in
`E` (`NumberField.Chebotarev.ramifiedPrimes`), its ramification set is finite
(`TauCeti.ContinuousRep.finite_ramificationSet_of_isOpen_ker`). Open kernel is the right
hypothesis: finite image alone does not suffice, since over an indiscrete coefficient ring the
kernel of a character with finite image can be dense.

Conversely, the image of `I_Q` in `Gal(E/F)` is the inertia group of the prime of `𝓞 E` below `Q`
(`TauCeti.GaloisRep.map_inertiaGroup_restrictNormalHom`). So when the kernel of `ρ` is exactly the
fixing subgroup of `E`, that is, when `E` is the field cut out by `ρ`, `ρ` is unramified at `v`
exactly when `v` is unramified in `E`, and the ramification set of `ρ` is the set of places
ramified in `E` (`TauCeti.ContinuousRep.ramificationSet_eq_ramifiedPrimes`).

## Main results

* `TauCeti.ContinuousRep.ramificationSet_subset_ramifiedPrimes`: if the kernel of `ρ` contains the
  fixing subgroup of a finite normal `E`, then `Ram ρ` lies in the set of places ramified in `E`.
* `TauCeti.ContinuousRep.finite_ramificationSet_of_isOpen_ker`: the ramification set of a
  representation with open kernel is finite.
* `TauCeti.ContinuousRep.isUnramifiedAt_iff_notMem_ramifiedPrimes`,
  `TauCeti.ContinuousRep.ramificationSet_eq_ramifiedPrimes`: if the kernel of `ρ` is the fixing
  subgroup of a finite normal `E`, then `ρ` is unramified at `v` iff `v` is unramified in `E`.
-/

public section

noncomputable section

open NumberField IsDedekindDomain

namespace TauCeti.ContinuousRep

variable {F : Type*} [Field F] [NumberField F]
  {A M : Type*} [Semiring A] [AddCommMonoid M] [Module A M] [TopologicalSpace M]
  {ρ : ContinuousRep (Field.absoluteGaloisGroup F) A M}

/-- If the kernel of `ρ` contains the fixing subgroup of a finite normal subextension `E` of
`F^alg / F`, then `ρ` is unramified at every finite place of `F` unramified in `E`. -/
theorem ramificationSet_subset_ramifiedPrimes (E : IntermediateField F (AlgebraicClosure F))
    [NumberField E] [Normal F E] (hE : E.fixingSubgroup ≤ ρ.toRepresentation.ker) :
    ρ.ramificationSet ⊆ (Chebotarev.ramifiedPrimes F E : Set (HeightOneSpectrum (𝓞 F))) := by
  intro v hv
  by_contra hvE
  rw [Finset.mem_coe] at hvE
  refine (mem_ramificationSet_iff.1 hv) (isUnramifiedAt_iff.2 fun Q hQ hQv σ hσ ↦ ?_)
  have := hQ.isPrime
  rw [← coe_toRepresentation, ← MonoidHom.mem_ker]
  exact hE (GaloisRep.inertiaGroup_le_fixingSubgroup E hQv hvE hσ)

/-- **A representation with open kernel has finite ramification set.** The kernel contains the
fixing subgroup of a finite normal subextension `E` of `F^alg / F` (Krull topology), `ρ` is
unramified at the places unramified in `E`, and only finitely many places ramify in `E`. -/
theorem finite_ramificationSet_of_isOpen_ker
    (hρ : IsOpen (ρ.toRepresentation.ker : Set (Field.absoluteGaloisGroup F))) :
    ρ.ramificationSet.Finite := by
  obtain ⟨E, hfin, hnormal, hE⟩ := (krullTopology_mem_nhds_one_iff_of_normal F
    (AlgebraicClosure F) (ρ.toRepresentation.ker : Set (Field.absoluteGaloisGroup F))).1
      (hρ.mem_nhds (one_mem _))
  have : NumberField E := NumberField.of_module_finite F E
  exact (Chebotarev.ramifiedPrimes F E).finite_toSet.subset
    (ramificationSet_subset_ramifiedPrimes E hE)

/-- **Ramification of a representation and of its kernel field.** If the kernel of `ρ` is the
fixing subgroup of a finite normal subextension `E` of `F^alg / F`, then `ρ` is unramified at a
finite place `v` exactly when `v` is unramified in `E`. -/
theorem isUnramifiedAt_iff_notMem_ramifiedPrimes (E : IntermediateField F (AlgebraicClosure F))
    [NumberField E] [Normal F E] (hE : ρ.toRepresentation.ker = E.fixingSubgroup)
    (v : HeightOneSpectrum (𝓞 F)) :
    ρ.IsUnramifiedAt v ↔ v ∉ Chebotarev.ramifiedPrimes F E := by
  rw [← GaloisRep.forall_inertiaGroup_le_fixingSubgroup_iff E v, isUnramifiedAt_iff, ← hE]
  simp only [IsConcreteLE.le_iff, MonoidHom.mem_ker, coe_toRepresentation]

/-- **The ramification set is that of the kernel field.** If the kernel of `ρ` is the fixing
subgroup of a finite normal subextension `E` of `F^alg / F`, then the ramification set of `ρ` is
the set of finite places of `F` ramified in `E`. -/
theorem ramificationSet_eq_ramifiedPrimes (E : IntermediateField F (AlgebraicClosure F))
    [NumberField E] [Normal F E] (hE : ρ.toRepresentation.ker = E.fixingSubgroup) :
    ρ.ramificationSet = (Chebotarev.ramifiedPrimes F E : Set (HeightOneSpectrum (𝓞 F))) := by
  ext v
  rw [mem_ramificationSet_iff, isUnramifiedAt_iff_notMem_ramifiedPrimes E hE, not_not,
    Finset.mem_coe]

end TauCeti.ContinuousRep

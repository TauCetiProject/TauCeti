/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.Global.Adeles.FundamentalDomain

/-!
# Compactness of the additive adele quotient

For a number field `K`, the diagonal copy of `K` is cocompact in its adele ring.  Equivalently,
the additive quotient `𝔸[K] / K` is compact.

The proof uses a compact set of representatives: the closure of the fundamental domain `F × Ô`
of `TauCeti.GlobalNumberFields.adeleFundamentalDomain`, the product of the half-open fundamental
parallelotope of the Minkowski lattice with the integral finite adeles.  It is compact
(`TauCeti.GlobalNumberFields.isCompact_closure_adeleFundamentalDomain`) and contains a translate
by `K` of every adele, so it maps onto the quotient.

Together with the discreteness of the principal subgroup, this identifies the diagonal number
field as a lattice in the additive adele ring.  The compact quotient is also the additive global
finiteness input used in the compactness theorem for the norm-one idele class group.

## Main result

* `TauCeti.GlobalNumberFields.exists_isCompact_forall_exists_sub_algebraMap_mem`: there is a
  compact set of representatives for the additive adele quotient.
* `TauCeti.GlobalNumberFields.compactSpace_quotient_principalSubgroup`: the quotient of the adele
  ring by the diagonal copy of the number field is compact.

## References

* J. W. S. Cassels and A. Fröhlich, eds., *Algebraic Number Theory*, Chapter II, §14.
* J. Neukirch, *Algebraic Number Theory*, Chapter VI, §1.
-/

public section

open IsDedekindDomain HeightOneSpectrum NumberField
open scoped NumberField.AdeleRing

namespace TauCeti.GlobalNumberFields

variable (K : Type*) [Field K] [NumberField K]

/-- There is a compact set of representatives for the additive adele quotient: every adele can be
translated by a diagonal element of `K` into this set. -/
theorem exists_isCompact_forall_exists_sub_algebraMap_mem :
    ∃ D : Set 𝔸[K], IsCompact D ∧
      ∀ a : 𝔸[K], ∃ x : K, a - algebraMap K 𝔸[K] x ∈ D :=
  ⟨closure (adeleFundamentalDomain K), isCompact_closure_adeleFundamentalDomain K, fun a ↦
    (existsUnique_sub_algebraMap_mem_adeleFundamentalDomain K a).exists.imp
      fun _ h ↦ subset_closure h⟩

/-- **The additive adele class group is compact.** The quotient of the adele ring by the diagonal
copy of the number field is compact. -/
noncomputable instance compactSpace_quotient_principalSubgroup :
    CompactSpace (𝔸[K] ⧸ AdeleRing.principalSubgroup (𝓞 K) K) := by
  classical
  obtain ⟨D, hD, hcover⟩ := exists_isCompact_forall_exists_sub_algebraMap_mem K
  let q : 𝔸[K] → 𝔸[K] ⧸ AdeleRing.principalSubgroup (𝓞 K) K :=
    QuotientAddGroup.mk' (AdeleRing.principalSubgroup (𝓞 K) K)
  have hq : Continuous q := continuous_quot_mk
  have hsurj : Set.SurjOn q D Set.univ := by
    intro c _
    obtain ⟨a, rfl⟩ := QuotientAddGroup.mk'_surjective
      (AdeleRing.principalSubgroup (𝓞 K) K) c
    obtain ⟨x, hx⟩ := hcover a
    refine ⟨a - algebraMap K 𝔸[K] x, hx, ?_⟩
    dsimp only [q]
    rw [map_sub]
    have hprincipal : algebraMap K 𝔸[K] x ∈
        AdeleRing.principalSubgroup (𝓞 K) K := ⟨x, rfl⟩
    have hqprincipal : QuotientAddGroup.mk' (AdeleRing.principalSubgroup (𝓞 K) K)
        (algebraMap K 𝔸[K] x) = 0 :=
      (QuotientAddGroup.eq_zero_iff _).mpr hprincipal
    rw [hqprincipal, sub_zero]
  refine ⟨?_⟩
  have himage : q '' D = Set.univ :=
    hsurj.image_eq_of_mapsTo fun _ _ ↦ Set.mem_univ _
  rw [← himage]
  exact hD.image hq

end TauCeti.GlobalNumberFields

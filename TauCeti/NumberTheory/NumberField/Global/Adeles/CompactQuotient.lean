/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.Global.Adeles.Basic

import Mathlib.NumberTheory.NumberField.FiniteAdeleRing
import TauCeti.RingTheory.DedekindDomain.AdicValuation.ValuativeRel

/-!
# Compactness of the additive adele quotient

For a number field `K`, the diagonal copy of `K` is cocompact in its adele ring.  Equivalently,
the additive quotient `𝔸[K] / K` is compact.

The proof uses a compact set of representatives.  Strong approximation first subtracts an element
of `K` so that the finite component is integral everywhere.  The remaining freedom to subtract an
algebraic integer does not disturb finite integrality, and moves the infinite component into the
closed fundamental parallelepiped of the Minkowski lattice.  That parallelepiped is compact, as is
the product of all local integer rings, so their product maps onto the quotient from a compact set.

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

/-- Every infinite adele can be translated by the image of an algebraic integer into the closed
fundamental parallelepiped of the Minkowski lattice. -/
private theorem exists_sub_algebraMap_integer_mem_parallelepiped (z : K∞) :
    ∃ y : 𝓞 K, InfiniteAdeleRing.ringEquiv_mixedSpace K
      (z - algebraMap K K∞ (algebraMap (𝓞 K) K y))
      ∈ parallelepiped (mixedEmbedding.latticeBasis K) := by
  classical
  let b := mixedEmbedding.latticeBasis K
  let e := InfiniteAdeleRing.ringEquiv_mixedSpace K
  -- The lattice correction is the Minkowski embedding of an algebraic integer `y`.
  have hfloor : ((ZSpan.floor b (e z) :
      Submodule.span ℤ (Set.range b)) : mixedEmbedding.mixedSpace K) ∈
      mixedEmbedding.integerLattice K := by
    rw [← mixedEmbedding.span_latticeBasis K]
    exact (ZSpan.floor b (e z)).property
  obtain ⟨y, hy⟩ := hfloor
  have hy' : mixedEmbedding K (algebraMap (𝓞 K) K y) =
      ((ZSpan.floor b (e z) : Submodule.span ℤ (Set.range b)) :
        mixedEmbedding.mixedSpace K) := by
    simpa using hy
  have hey : e (algebraMap K K∞ (algebraMap (𝓞 K) K y)) =
      ((ZSpan.floor b (e z) : Submodule.span ℤ (Set.range b)) :
        mixedEmbedding.mixedSpace K) :=
    (InfiniteAdeleRing.mixedEmbedding_eq_algebraMap_comp
      (K := K) (x := algebraMap (𝓞 K) K y)).symm.trans hy'
  refine ⟨y, ?_⟩
  rw [map_sub, hey, ← ZSpan.fract_apply]
  exact ZSpan.fundamentalDomain_subset_parallelepiped b
    (ZSpan.fract_mem_fundamentalDomain b (e z))

/-- Subtracting the diagonal image of `x + y` from a finite adele that is integral after
subtracting `x` keeps it integral, for every algebraic integer `y`. -/
private theorem sub_algebraMap_add_integer_mem_integralAdeles (f : 𝔸ᶠ[K]) (x : K)
    (hx : ∀ v : HeightOneSpectrum (𝓞 K), f v - algebraMap K (v.adicCompletion K) x ∈
      v.adicCompletionIntegers K) (y : 𝓞 K) :
    f - algebraMap K 𝔸ᶠ[K] (x + algebraMap (𝓞 K) K y) ∈
      FiniteAdeleRing.integralAdeles (𝓞 K) K :=
  FiniteAdeleRing.mem_integralAdeles.mpr fun v ↦ by
    rw [FiniteAdeleRing.sub_apply, FiniteAdeleRing.algebraMap_apply]
    change f v - algebraMap K (v.adicCompletion K) (x + algebraMap (𝓞 K) K y) ∈ _
    rw [map_add, ← IsScalarTower.algebraMap_apply (𝓞 K) K (v.adicCompletion K), sub_add_eq_sub_sub]
    exact sub_mem (hx v) (v.coe_mem_adicCompletionIntegers y)

/-- There is a compact set of representatives for the additive adele quotient: every adele can be
translated by a diagonal element of `K` into this set. -/
theorem exists_isCompact_forall_exists_sub_algebraMap_mem :
    ∃ D : Set 𝔸[K], IsCompact D ∧
      ∀ a : 𝔸[K], ∃ x : K, a - algebraMap K 𝔸[K] x ∈ D := by
  classical
  -- The compact representative set is the product of the closed Minkowski parallelepiped with
  -- the integral finite adeles.
  let b := mixedEmbedding.latticeBasis K
  let e := InfiniteAdeleRing.ringEquiv_mixedSpace K
  let D : Set 𝔸[K] := (e.symm '' parallelepiped b) ×ˢ
    (FiniteAdeleRing.integralAdeles (𝓞 K) K : Set 𝔸ᶠ[K])
  have he : Continuous e.symm :=
    InfiniteAdeleRing.continuous_ringEquiv_mixedSpace_symm K
  refine ⟨D, (b.parallelepiped.isCompact.image he).prod FiniteAdeleRing.isCompact_integralAdeles,
    fun a ↦ ?_⟩
  -- Expose the product representation of the adele ring for the componentwise construction.
  let a' : K∞ × 𝔸ᶠ[K] := a
  -- Strong approximation makes the finite component integral after subtracting `x`.
  obtain ⟨x, hx⟩ :=
    FiniteAdeleRing.exists_forall_sub_algebraMap_mem_adicCompletionIntegers a'.2
  obtain ⟨y, hy⟩ := exists_sub_algebraMap_integer_mem_parallelepiped K (a'.1 - algebraMap K K∞ x)
  refine ⟨x + algebraMap (𝓞 K) K y, Set.mem_prod.mpr ⟨⟨_, hy, ?_⟩, ?_⟩⟩
  · -- `AdeleRing` is a type synonym for this product; exposing it lets the two components be
    -- compared through their canonical APIs.
    change e.symm _ = a'.1 - algebraMap K K∞ (x + algebraMap (𝓞 K) K y)
    rw [e.symm_apply_apply, map_add]
    abel
  · exact sub_algebraMap_add_integer_mem_integralAdeles K a'.2 x hx y
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

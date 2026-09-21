/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.Global.Adeles.Discrete

import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.Basic
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

/-- **The additive adele class group is compact.**  Every adele has a representative whose finite
component is integral at every finite place and whose infinite component lies in a fixed compact
parallelepiped for the Minkowski lattice of `𝓞 K`. -/
noncomputable instance compactSpace_quotient_principalSubgroup :
    CompactSpace (𝔸[K] ⧸ AdeleRing.principalSubgroup (𝓞 K) K) := by
  classical
  -- The compact representative set is the product of the closed Minkowski parallelepiped with
  -- the integral finite adeles.
  let b := mixedEmbedding.latticeBasis K
  let P : Set (mixedEmbedding.mixedSpace K) := b.parallelepiped
  let e := InfiniteAdeleRing.ringEquiv_mixedSpace K
  let ι : (∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletionIntegers K) → 𝔸ᶠ[K] :=
    RestrictedProduct.structureMap
      (fun v : HeightOneSpectrum (𝓞 K) ↦ v.adicCompletion K)
      (fun v ↦ (v.adicCompletionIntegers K : Set (v.adicCompletion K))) Filter.cofinite
  let D : Set 𝔸[K] := (e.symm '' P) ×ˢ Set.range ι
  have he : Continuous e.symm :=
    InfiniteAdeleRing.continuous_ringEquiv_mixedSpace_symm K
  let (v : HeightOneSpectrum (𝓞 K)) :
      IsNonarchimedeanLocalField (v.adicCompletion K) :=
    v.isNonarchimedeanLocalField_adicCompletion
  let (v : HeightOneSpectrum (𝓞 K)) :
      CompactSpace ↥(v.adicCompletionIntegers K).toSubring := by
    rw [← v.integer_eq_adicCompletionIntegers (K := K)]
    infer_instance
  have hι : Continuous ι :=
    (RestrictedProduct.isOpenEmbedding_structureMap
      (fun v ↦ Valued.isOpen_valuationSubring (v.adicCompletion K))).continuous
  have hD : IsCompact D :=
    ((b.parallelepiped.isCompact.image he).prod (isCompact_range hι))
  let q : 𝔸[K] → 𝔸[K] ⧸ AdeleRing.principalSubgroup (𝓞 K) K :=
    QuotientAddGroup.mk' (AdeleRing.principalSubgroup (𝓞 K) K)
  have hq : Continuous q := continuous_quot_mk
  have hsurj : Set.SurjOn q D Set.univ := by
    intro c _
    obtain ⟨a, rfl⟩ := QuotientAddGroup.mk'_surjective
      (AdeleRing.principalSubgroup (𝓞 K) K) c
    -- Expose the product representation of the adele ring for the componentwise construction.
    let a' : K∞ × 𝔸ᶠ[K] := a
    -- Strong approximation makes the finite component integral after subtracting `x`.
    obtain ⟨x, -, hx⟩ :=
      FiniteAdeleRing.exists_forall_valued_sub_le_and_forall_valued_sub_le_one
        a'.2 ∅ (fun _ ↦ 0)
    let z : K∞ := a'.1 - algebraMap K K∞ x
    let p : mixedEmbedding.mixedSpace K := ZSpan.fract b (e z)
    have hp : p ∈ P := ZSpan.fundamentalDomain_subset_parallelepiped b
      (ZSpan.fract_mem_fundamentalDomain b (e z))
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
      exact hy
    let u : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletionIntegers K := fun v ↦
      ⟨a'.2 v - algebraMap K (v.adicCompletion K) (x + algebraMap (𝓞 K) K y), by
        have hxa : algebraMap K (v.adicCompletion K) x - a'.2 v ∈
            v.adicCompletionIntegers K := by
          rw [mem_adicCompletionIntegers]
          exact hx v
        have hax : a'.2 v - algebraMap K (v.adicCompletion K) x ∈
            v.adicCompletionIntegers K := by
          simpa only [neg_sub] using neg_mem hxa
        rw [map_add, ← IsScalarTower.algebraMap_apply (𝓞 K) K (v.adicCompletion K),
          sub_add_eq_sub_sub]
        exact sub_mem hax (v.coe_mem_adicCompletionIntegers y)⟩
    let d : 𝔸[K] := (e.symm p, ι u)
    have hd : d ∈ D := ⟨⟨p, hp, rfl⟩, Set.mem_range_self u⟩
    refine ⟨d, hd, ?_⟩
    -- Thus `d` differs from `a` by the principal adele of `x + y` and has the same class.
    have hd_eq : d = a - algebraMap K 𝔸[K] (x + algebraMap (𝓞 K) K y) := by
      -- `AdeleRing` is a type synonym for this product; exposing it lets the two components be
      -- compared through their canonical APIs.
      have hex : e (algebraMap K K∞ x) = mixedEmbedding K x :=
        (InfiniteAdeleRing.mixedEmbedding_eq_algebraMap_comp (K := K) (x := x)).symm
      have hey : e (algebraMap K K∞ (algebraMap (𝓞 K) K y)) =
          ((ZSpan.floor b (e z) : Submodule.span ℤ (Set.range b)) :
            mixedEmbedding.mixedSpace K) :=
        (InfiniteAdeleRing.mixedEmbedding_eq_algebraMap_comp
          (K := K) (x := algebraMap (𝓞 K) K y)).symm.trans hy'
      have hfst : e.symm p =
          a'.1 - algebraMap K K∞ (x + algebraMap (𝓞 K) K y) := by
        apply e.injective
        rw [e.apply_symm_apply]
        simp only [map_sub, map_add, p, z, ZSpan.fract_apply, hex, hey]
        abel
      have hsnd : ι u =
          a'.2 - algebraMap K 𝔸ᶠ[K] (x + algebraMap (𝓞 K) K y) := by
        apply RestrictedProduct.ext
        intro v
        change (ι u) v =
          a'.2 v - algebraMap K (v.adicCompletion K) (x + algebraMap (𝓞 K) K y)
        rw [show (ι u) v = (u v : v.adicCompletion K) by
          exact RestrictedProduct.structureMap_apply _ _ v]
      change (e.symm p, ι u) =
        (a'.1 - algebraMap K K∞ (x + algebraMap (𝓞 K) K y),
          a'.2 - algebraMap K 𝔸ᶠ[K] (x + algebraMap (𝓞 K) K y))
      exact Prod.ext hfst hsnd
    rw [hd_eq]
    dsimp only [q]
    rw [map_sub]
    have hprincipal : algebraMap K 𝔸[K] (x + algebraMap (𝓞 K) K y) ∈
        AdeleRing.principalSubgroup (𝓞 K) K :=
      ⟨x + algebraMap (𝓞 K) K y, rfl⟩
    have hqprincipal : QuotientAddGroup.mk' (AdeleRing.principalSubgroup (𝓞 K) K)
        (algebraMap K 𝔸[K] (x + algebraMap (𝓞 K) K y)) = 0 :=
      (QuotientAddGroup.eq_zero_iff _).mpr hprincipal
    rw [hqprincipal, sub_zero]
  refine ⟨?_⟩
  have himage : q '' D = Set.univ :=
    hsurj.image_eq_of_mapsTo fun _ _ ↦ Set.mem_univ _
  rw [← himage]
  exact hD.image hq

end TauCeti.GlobalNumberFields

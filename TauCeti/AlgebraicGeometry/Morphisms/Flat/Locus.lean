/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Jie Xu, Shitan Xu
-/
module

public import TauCeti.AlgebraicGeometry.Morphisms.Flat.Basic
public import Mathlib.AlgebraicGeometry.Noetherian
import TauCeti.RingTheory.Flat.Locus

/-!
# The flat locus of a morphism to a locally Noetherian scheme

For a locally finite-type morphism to a locally Noetherian scheme, the locus where its stalk map
is flat is open in the source. Thus every flat point has an open neighbourhood on which the
source restriction is flat. No quasi-compactness or separatedness assumption is needed.

## References

* The Stacks Project, Section 37.15, Tag 0398, openness of the flat locus.
-/

public section

open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry.Scheme.Hom

universe u

variable {X Y : Scheme.{u}} [IsLocallyNoetherian Y] (f : X ⟶ Y) [LocallyOfFiniteType f]

/-- The flat locus of a locally finite-type morphism to a locally Noetherian scheme is open
in its source. -/
theorem isOpen_setOf_flat_stalkMap : IsOpen {x : X | (f.stalkMap x).hom.Flat} := by
  rw [isOpen_iff_forall_mem_open]
  intro x hx
  obtain ⟨U, hU, hxU, -⟩ := exists_isAffineOpen_mem_and_subset (x := f x) (U := ⊤) trivial
  obtain ⟨V, hV, hxV, hVU⟩ :=
    exists_isAffineOpen_mem_and_subset (x := x) (U := f ⁻¹ᵁ U) hxU
  let _ := (f.appLE U V hVU).hom.toAlgebra
  have : IsNoetherianRing Γ(Y, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  have : Algebra.FiniteType Γ(Y, U) Γ(X, V) := f.finiteType_appLE hU hV hVU
  let W : Set (PrimeSpectrum Γ(X, V)) :=
    {q | Module.Flat Γ(Y, U) (Localization.AtPrime q.asIdeal)}
  have hW : IsOpen W := Module.isOpen_setOf_flat_localizedModule
  refine ⟨hV.fromSpec '' W, ?_, hV.fromSpec.isOpenEmbedding.isOpenMap W hW, ?_⟩
  · rintro _ ⟨q, hq, rfl⟩
    have hqV : hV.fromSpec q ∈ V := by
      rw [← SetLike.mem_coe, ← hV.range_fromSpec]
      exact Set.mem_range_self q
    have hqp : hV.primeIdealOf ⟨hV.fromSpec q, hqV⟩ = q := by
      exact hV.fromSpec.isOpenEmbedding.injective (hV.fromSpec_primeIdealOf _)
    apply (AlgebraicGeometry.flat_stalkMap_iff U hU V hV hVU hqV).mpr
    rw [hqp]
    exact hq
  · refine ⟨hV.primeIdealOf ⟨x, hxV⟩, ?_, hV.fromSpec_primeIdealOf _⟩
    exact (AlgebraicGeometry.flat_stalkMap_iff U hU V hV hVU hxV).mp hx

/-- Every flat point of a locally finite-type morphism to a locally Noetherian scheme has an
open neighbourhood on which the source restriction is flat. -/
theorem exists_open_flat_of_flat_stalkMap {x : X} (hx : (f.stalkMap x).hom.Flat) :
    ∃ U : X.Opens, x ∈ U ∧ Flat (U.ι ≫ f) := by
  let U : X.Opens := ⟨{x : X | (f.stalkMap x).hom.Flat}, f.isOpen_setOf_flat_stalkMap⟩
  refine ⟨U, hx, Flat.of_stalkMap _ fun y ↦ ?_⟩
  have hy : (f.stalkMap y.val).hom.Flat := y.property
  have hflat : CommRingCat.flat (f.stalkMap y.val ≫ U.ι.stalkMap y) :=
    hy.comp (Flat.stalkMap U.ι y)
  rw [Scheme.Hom.stalkMap_comp]
  exact hflat

end AlgebraicGeometry.Scheme.Hom

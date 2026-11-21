/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.RegularLocalRing.Defs
public import TauCeti.AlgebraicGeometry.FormalScheme.Spf.Basic
public import TauCeti.AlgebraicGeometry.FormalScheme.Spf.CompletedNeighbourhood.Noetherian

import TauCeti.RingTheory.KrullDimension.Fiber
import TauCeti.RingTheory.RegularLocalRing.Flat

/-!
# The stalks of a formal spectrum and the completed localisations of its ring

Let `A` be an adic ring with ideal of definition `I` and `p` a point of `Spf A`, an open prime `𝔭`
of `A`. The completed localisation `Â_𝔭 = lim_n (A ⧸ Iⁿ)_𝔭`
(`TauCeti.FormalScheme.Spf.CompletedAtPrime`) is the completion of the local ring `A_𝔭` along
`I A_𝔭`. Since `I ⊆ 𝔭`, it is a local ring with maximal ideal `𝔭 Â_𝔭`. The stalk `O_{Spf A, p}` is
the colimit of the completed localisations `A_{f}` over the basic open neighbourhoods `D(f)` of `p`,
and the maps `A_{f} → Â_𝔭` induce a canonical map `O_{Spf A, p} → Â_𝔭` (EGA I, Ch. 0, 7.6.15–7.6.18;
Ch. I, 10.1.5–10.1.6).

This file shows that `O_{Spf A, p} → Â_𝔭` is a local homomorphism under which the maximal ideal of
the stalk generates the maximal ideal of `Â_𝔭`, and that for noetherian `A` it is faithfully flat.
Its closed fibre is then the residue field of `Â_𝔭`, so the stalk and `Â_𝔭` have the same Krull
dimension, and one is regular exactly when the other is. Completion of the noetherian local ring
`A_𝔭` along `I A_𝔭 ⊆ 𝔭 A_𝔭` likewise preserves the dimension and regularity
(`TauCeti.FormalScheme.Spf.ringKrullDim_completedAtPrime`,
`TauCeti.FormalScheme.Spf.isRegularLocalRing_completedAtPrime_iff`), so `A_𝔭`, the stalk and `Â_𝔭`
share these invariants. This is how the local dimension and regularity at a point of a formal
spectrum are computed from its ring.

## Main definitions

* `TauCeti.FormalScheme.Spf.stalkToCompletedAtPrime p`: the canonical map `O_{Spf A, p} → Â_𝔭`.

## Main results

* `TauCeti.FormalScheme.Spf.stalkToCompletedAtPrime_germ`: on the germ of a section over `D(f)`,
  the map `O_{Spf A, p} → Â_𝔭` is the map `A_{f} → Â_𝔭`.
* `TauCeti.FormalScheme.Spf.map_maximalIdeal_stalkToCompletedAtPrime`: the maximal ideal of the
  stalk generates the maximal ideal of `Â_𝔭`.
* `TauCeti.FormalScheme.Spf.faithfullyFlat_stalkToCompletedAtPrime`: for noetherian `A`, the map
  `O_{Spf A, p} → Â_𝔭` is faithfully flat.
* `TauCeti.FormalScheme.Spf.ringKrullDim_completedAtPrime_eq_stalk`,
  `TauCeti.FormalScheme.Spf.isRegularLocalRing_completedAtPrime_iff_stalk`: for noetherian `A`,
  the rings `Â_𝔭` and `O_{Spf A, p}` have the same Krull dimension, and one is regular if and only
  if the other is.

## References

* A. Grothendieck and J. Dieudonné, *Éléments de géométrie algébrique I*, Ch. 0, 7.6.15–7.6.18,
  and Ch. I, 10.1.5–10.1.6.
* H. Matsumura, *Commutative Ring Theory*, Theorems 15.1 and 23.7, for the invariance of the
  dimension and of regularity along a flat local homomorphism whose closed fibre is a field.
-/

public section

universe u

open CategoryTheory Limits IsLocalRing

namespace TauCeti.FormalScheme.Spf

open AdicRing

variable {A : Type u} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsAdicRing A]
  (p : carrier A)

/-! ### The map from the stalk to the completed localisation -/

/-- The identification of `colim_{f ∉ 𝔭} A_{f}` with the stalk of `Spf A` at `p`. -/
private noncomputable abbrev colimitIso :
    colimit (completedNeighbourhoodDiagram p) ≅ (Spf A).presheaf.stalk p :=
  completedNeighbourhoodColimitIso p (IsAdicRing.ideal_spec A).2.1 (IsAdicRing.ideal_spec A).1

/-- The canonical map `O_{Spf A, p} → Â_𝔭` from the stalk of `Spf A` at `p` to the completed
localisation of `A` at the corresponding open prime `𝔭`. On the germ of a section over a basic open
neighbourhood `D(f)` of `p` it is the map `A_{f} → Â_𝔭`, see
`TauCeti.FormalScheme.Spf.stalkToCompletedAtPrime_germ`. -/
noncomputable def stalkToCompletedAtPrime : (Spf A).presheaf.stalk p →+* CompletedAtPrime p :=
  (colimitToCompletedAtPrime p).comp (colimitIso p).inv.hom

/-- The map `O_{Spf A, p} → Â_𝔭` sends the germ at `p` of the section over a basic open
neighbourhood `D(f)` given by `x ∈ A_{f}` to the image of `x` under `A_{f} → Â_𝔭`. Since every
element of the stalk is such a germ, this determines the map. -/
@[simp]
theorem stalkToCompletedAtPrime_germ (f : BasicNeighbourhood p) (x : CompletedAway A f.elem) :
    stalkToCompletedAtPrime p ((Spf A).presheaf.germ (basicOpen f.elem) p
        (mem_basicOpen.mpr f.notMem)
        ((basicOpenSectionsIso (IsAdicRing.ideal_spec A).2.1 (IsAdicRing.ideal_spec A).1
          f.elem).inv x)) =
      toCompletedAtPrime p f x := by
  -- the inverse of the comparison of the colimit with the stalk sends the germ back to `x`
  have h : (colimitIso p).inv.hom ((Spf A).presheaf.germ (basicOpen f.elem) p
      (mem_basicOpen.mpr f.notMem) ((basicOpenSectionsIso (IsAdicRing.ideal_spec A).2.1
        (IsAdicRing.ideal_spec A).1 f.elem).inv x)) =
      colimit.ι (completedNeighbourhoodDiagram p) f x :=
    ConcreteCategory.congr_hom ((Iso.comp_inv_eq _).mpr (completedNeighbourhoodColimitIso_germ p
      (IsAdicRing.ideal_spec A).2.1 (IsAdicRing.ideal_spec A).1 f).symm) x
  rw [stalkToCompletedAtPrime, RingHom.comp_apply]
  exact (congrArg (colimitToCompletedAtPrime p) h).trans (colimitToCompletedAtPrime_ι p f x)

/-- The map `O_{Spf A, p} → Â_𝔭` is a local homomorphism. -/
instance isLocalHom_stalkToCompletedAtPrime : IsLocalHom (stalkToCompletedAtPrime p) :=
  inferInstanceAs (IsLocalHom ((colimitToCompletedAtPrime p).comp (colimitIso p).inv.hom))

/-- The maximal ideal of the stalk `O_{Spf A, p}` generates the maximal ideal of the completed
localisation `Â_𝔭`: the closed fibre of `O_{Spf A, p} → Â_𝔭` is the residue field of `Â_𝔭`. -/
theorem map_maximalIdeal_stalkToCompletedAtPrime :
    haveI := (Spf A).isLocalRing p
    (maximalIdeal ((Spf A).presheaf.stalk p)).map (stalkToCompletedAtPrime p) =
      maximalIdeal (CompletedAtPrime p) := by
  have := (Spf A).isLocalRing p
  refine le_antisymm (map_maximalIdeal_le (stalkToCompletedAtPrime p)) ?_
  -- `𝔭 Â_𝔭` is generated by the images of the germs of the elements of `𝔭`, which vanish at `p`
  rw [maximalIdeal_completedAtPrime, Ideal.map_le_iff_le_comap]
  intro a ha
  let f : BasicNeighbourhood p := ⟨1, (p : PrimeSpectrum A).asIdeal.primeCompl.one_mem⟩
  let x := (Spf A).presheaf.germ (basicOpen f.elem) p (mem_basicOpen.mpr f.notMem)
    ((basicOpenSectionsIso (IsAdicRing.ideal_spec A).2.1 (IsAdicRing.ideal_spec A).1 f.elem).inv
      (algebraMap A (CompletedAway A f.elem) a))
  have hx : x ∈ maximalIdeal ((Spf A).presheaf.stalk p) := by
    have h := stalkResidueFieldEquiv_residue_germ f a
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr ha, map_zero,
      map_eq_zero_iff _ (stalkResidueFieldEquiv p).injective] at h
    -- the residue map `(Spf A).residue p` of a locally ringed space is by definition the residue
    -- map of the local ring `O_{Spf A, p}`
    exact (residue_eq_zero_iff x).mp h
  have := Ideal.mem_map_of_mem (stalkToCompletedAtPrime p) hx
  rwa [stalkToCompletedAtPrime_germ, AlgHom.commutes] at this

/-- For a noetherian adic ring `A`, the map `O_{Spf A, p} → Â_𝔭` is faithfully flat. -/
theorem faithfullyFlat_stalkToCompletedAtPrime [IsNoetherianRing A] :
    (stalkToCompletedAtPrime p).FaithfullyFlat := by
  rw [stalkToCompletedAtPrime]
  exact RingHom.FaithfullyFlat.stableUnderComposition _ _
    (RingHom.FaithfullyFlat.of_bijective (f := (colimitIso p).inv.hom)
      (ConcreteCategory.bijective_of_isIso (colimitIso p).inv))
    (faithfullyFlat_colimitToCompletedAtPrime p)

/-! ### Dimension and regularity of the stalk -/

/-- The map `O_{Spf A, p} → Â_𝔭` as an algebra structure, used to apply results about flat local
algebras to it. -/
private noncomputable abbrev stalkAlgebra :
    Algebra ((Spf A).presheaf.stalk p) (CompletedAtPrime p) :=
  (stalkToCompletedAtPrime p).toAlgebra

attribute [local instance] stalkAlgebra

/-- The stalks of the formal spectrum of a noetherian adic ring are noetherian. -/
private theorem isNoetherianRing_stalk [IsNoetherianRing A] :
    IsNoetherianRing ((Spf A).presheaf.stalk p) :=
  isNoetherianRing_of_ringEquiv _ (colimitIso p).commRingCatIsoToRingEquiv

private theorem flat_stalkAlgebra [IsNoetherianRing A] :
    Module.Flat ((Spf A).presheaf.stalk p) (CompletedAtPrime p) :=
  (faithfullyFlat_stalkToCompletedAtPrime p).flat

/-- For a noetherian adic ring `A`, the completed localisation `Â_𝔭` has the Krull dimension of the
stalk `O_{Spf A, p}`. -/
theorem ringKrullDim_completedAtPrime_eq_stalk [IsNoetherianRing A] :
    ringKrullDim (CompletedAtPrime p) = ringKrullDim ((Spf A).presheaf.stalk p) :=
  haveI := (Spf A).isLocalRing p
  haveI := isNoetherianRing_stalk p
  haveI := flat_stalkAlgebra p
  ringKrullDim_eq_of_hasGoingDown_of_map_maximalIdeal_eq
    (map_maximalIdeal_stalkToCompletedAtPrime p)

/-- For a noetherian adic ring `A`, the completed localisation `Â_𝔭` is a regular local ring if and
only if the stalk `O_{Spf A, p}` is. -/
theorem isRegularLocalRing_completedAtPrime_iff_stalk [IsNoetherianRing A] :
    IsRegularLocalRing (CompletedAtPrime p) ↔ IsRegularLocalRing ((Spf A).presheaf.stalk p) :=
  haveI := (Spf A).isLocalRing p
  haveI := flat_stalkAlgebra p
  isRegularLocalRing_iff_of_flat_of_map_maximalIdeal_eq
    (map_maximalIdeal_stalkToCompletedAtPrime p)

end TauCeti.FormalScheme.Spf

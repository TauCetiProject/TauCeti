/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Cohomology.MayerVietoris
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact

/-!
# Cohomological bounds from finite affine covers

A quasi-coherent sheaf on a locally Noetherian scheme with affine diagonal has vanishing
cohomology in degrees at least the size of a nonempty finite affine cover. More locally, the
same bound holds on the union of any nonempty finite family of affine opens. Intersecting an
affine open with that union gives a union of the same number of affine opens, so Mayer–Vietoris
extends affine acyclicity inductively to these unions.

For a quasi-compact scheme this supplies a bound independent of the coefficient sheaf: there
is a positive integer `N` such that every quasi-coherent sheaf has zero cohomology in degrees
at least `N`. This is a bound from the cover, not a dimension-sharp vanishing theorem.
It supplies the starting degree for descending induction in the proof of finite-dimensionality
of coherent cohomology on projective schemes over a field. Projective `r`-space has a standard
cover by `r + 1` affine opens; the resulting
vanishing starts the induction using presentations of coherent sheaves by sums of twists
and the long exact cohomology sequence (Stacks Project, Tag 01YS). Those presentations and
the cohomology of twists are further ingredients, not proved here.

The proof uses the existing affine-open acyclicity and the vanishing consequence of
Mayer–Vietoris in `TauCeti.AlgebraicGeometry.Cohomology.MayerVietoris`.

## References

* R. Hartshorne, *Algebraic Geometry*, Chapter III, Sections 3 and 4 (affine acyclicity and
  cohomology computed using affine covers).
* Stacks Project, Tags [01XI](https://stacks.math.columbia.edu/tag/01XI) (the cover bound)
  and [01YS](https://stacks.math.columbia.edu/tag/01YS) (its use in coherent-cohomology finiteness).
-/

public section

open CategoryTheory Limits TopologicalSpace AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules TauCeti.AlgebraicGeometry.Scheme.Modules

universe u v

namespace TauCeti

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}} [IsLocallyNoetherian X]
  [IsAffineHom (pullback.diagonal (terminal.from X))]

section Coefficients

variable (M : X.Modules) [M.IsQuasicoherent]

/-- On the union of a nonempty finite family of affine opens, quasi-coherent cohomology vanishes
in every degree at least the number of members of the family. The scheme must be locally
Noetherian with affine diagonal; no properness or field hypothesis is required. -/
theorem subsingleton_cohomologyOn_biSup_of_isAffineOpen {ι : Type v}
    (s : Finset ι) (hs : s.Nonempty) (U : ι → X.Opens)
    (hU : ∀ i ∈ s, IsAffineOpen (U i)) (n : ℕ) (hn : s.card ≤ n) :
    Subsingleton (cohomologyOn M n (⨆ i ∈ s, U i)) := by
  classical
  induction s using Finset.induction_on generalizing U n with
  | empty => simp at hs
  | @insert a s ha ih =>
    have hUa : IsAffineOpen (U a) := hU a (by simp)
    have : IsNoetherianRing Γ(X, U a) := IsLocallyNoetherian.component_noetherian ⟨U a, hUa⟩
    have hUs : ∀ i ∈ s, IsAffineOpen (U i) := fun i hi ↦ hU i (by simp [hi])
    rcases s.eq_empty_or_nonempty with rfl | hs'
    · have hn' : 0 < n := by
        simp only [Finset.card_insert_of_notMem (Finset.notMem_empty a), Finset.card_empty] at hn
        omega
      obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
      simpa using subsingleton_cohomologyOn_succ_of_isAffineOpen M hUa m
    · have hcard : (insert a s).card = s.card + 1 := Finset.card_insert_of_notMem ha
      have hpos := Finset.card_pos.mpr hs'
      obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
      have hm : s.card ≤ m := by omega
      have hinter : U a ⊓ (⨆ i ∈ s, U i) = ⨆ i ∈ s, U a ⊓ U i := by
        simp only [inf_iSup_eq]
      -- The overlap is covered by the intersections with the remaining affine opens.
      have hInter : Subsingleton (cohomologyOn M m (U a ⊓ (⨆ i ∈ s, U i))) := by
        rw [hinter]
        exact ih hs' (fun i ↦ U a ⊓ U i) (fun i hi ↦ hUa.inf (hUs i hi)) m hm
      have hLeft := subsingleton_cohomologyOn_succ_of_isAffineOpen M hUa m
      have hRight := ih hs' U hUs (m + 1) (by omega)
      rw [Finset.iSup_insert]
      exact subsingleton_cohomologyOn_sup_succ M m hInter hLeft hRight

/-- A nonempty finite affine cover bounds the cohomological degrees of every quasi-coherent
sheaf by its number of members. -/
theorem subsingleton_cohomology_of_isAffineOpen_finset_cover {ι : Type v}
    (s : Finset ι) (hs : s.Nonempty) (U : ι → X.Opens)
    (hU : ∀ i ∈ s, IsAffineOpen (U i)) (hcover : (⨆ i ∈ s, U i) = ⊤)
    (n : ℕ) (hn : s.card ≤ n) : Subsingleton (Cohomology M n) := by
  have h := subsingleton_cohomologyOn_biSup_of_isAffineOpen M s hs U hU n hn
  rw [hcover] at h
  exact (cohomologyOnTopIso M n).symm.addCommGroupIsoToAddEquiv.toEquiv.subsingleton

end Coefficients

/-- A quasi-compact open has a uniform positive cohomological bound for all quasi-coherent
coefficients. The bound depends only on a finite affine cover of the open. -/
theorem exists_cohomologyOn_bound_of_isCompact {W : X.Opens} (hW : IsCompact (W : Set X)) :
    ∃ N : ℕ, 0 < N ∧ ∀ (M : X.Modules) [M.IsQuasicoherent] (n : ℕ), N ≤ n →
      Subsingleton (cohomologyOn M n W) := by
  classical
  obtain ⟨s, hs, hcover⟩ := isCompact_iff_finite_and_eq_biUnion_affineOpens.mp hW
  -- Adjoining the empty affine open keeps the cover unchanged and handles empty `W`.
  let bottom : X.affineOpens := ⟨⊥, isAffineOpen_bot X⟩
  let t := insert bottom hs.toFinset
  have ht : t.Nonempty := Finset.insert_nonempty _ _
  have htcover : (⨆ i ∈ t, (i : X.Opens)) = W := by
    simp [t, bottom, hcover, hs.mem_toFinset]
  refine ⟨t.card, Finset.card_pos.mpr ht, fun M _ n hn ↦ ?_⟩
  have h := subsingleton_cohomologyOn_biSup_of_isAffineOpen M t ht
    (fun i : X.affineOpens ↦ (i : X.Opens)) (fun i _ ↦ i.property) n hn
  rwa [htcover] at h

/-- On a quasi-compact locally Noetherian scheme with affine diagonal, all quasi-coherent
sheaves have vanishing cohomology in degrees at least a single bound depending only on the
scheme. -/
theorem exists_cohomology_bound_of_compactSpace [CompactSpace X] :
    ∃ N : ℕ, 0 < N ∧ ∀ (M : X.Modules) [M.IsQuasicoherent] (n : ℕ), N ≤ n →
      Subsingleton (Cohomology M n) := by
  obtain ⟨N, hN, h⟩ := exists_cohomologyOn_bound_of_isCompact (X := X)
    (W := ⊤) (by simpa using isCompact_univ (X := X))
  refine ⟨N, hN, fun M _ n hn ↦ ?_⟩
  have := h M n hn
  exact (cohomologyOnTopIso M n).symm.addCommGroupIsoToAddEquiv.toEquiv.subsingleton

end AlgebraicGeometry.Scheme.Modules

end TauCeti

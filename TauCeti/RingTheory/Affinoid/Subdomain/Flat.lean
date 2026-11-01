/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Affinoid.Subdomain.Rational
public import TauCeti.RingTheory.RingHom.FaithfullyFlat

import TauCeti.RingTheory.Affinoid.TopologicallyFiniteType
import TauCeti.RingTheory.Huber.LocalizationTopology.Laurent.Flat

/-!
# Flatness of classical rational covers

The structure map `A → A⟨f/g⟩` of a rational domain of an affinoid algebra is flat.
For a finite family of rational domains covering the classical maximal spectrum, the map
from `A` into the product of their coordinate algebras is faithfully flat. Neither reducedness
nor a cover of the adic spectrum is assumed. The family may be empty, in which case its
covering hypothesis forces `A` to be the zero ring.

Flatness is transported through `RationalFraction.completionLocEquiv` from the shared
flatness theorem for Huber rational localisations. Faithfulness uses the classical point
lifting theorem: every maximal ideal of `A` remains proper in some member of the cover.
These are the algebraic descent inputs for rational-cover Čech complexes; no identification
of completed and algebraic tensor products is used.

## References

* [Bosch, Güntzer, Remmert, *Non-Archimedean Analysis*][bosch-guntzer-remmert], §§7.3 and 8.2.
* [T. Wedhorn, *Adic Spaces*][wedhorn_adic], Proposition 8.30 and Corollary 8.32.
-/

public section

namespace TauCeti.RationalFraction

open Huber Huber.PairOfDefinition

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A : Type*} [NormedCommRing A] [IsUltrametricDist A] [NormedAlgebra K A] [CompleteSpace A]
  (hA : IsAffinoidAlgebra K A)

include hA in
/-- The structure map of a classical rational domain is flat. Nilpotents are allowed in `A`. -/
theorem flat_algebraMap {m : ℕ} {g : A} {f : Fin m → A}
    (h : Ideal.span (insert g (Set.range f)) = ⊤) :
    (algebraMap A (RationalFraction g f)).Flat := by
  classical
  have := IsTateRing.of_normedAlgebra K A
  have := hA.isStronglyNoetherian
  obtain ⟨P⟩ := IsHuberRing.nonempty_pairOfDefinition (A := A)
  let S := Localization.Away g
  have hden := hasDenominatorPower_of_isOpen_span P (insert g (Set.range f)) g S
    (by simp [h])
  let _ := locUniformSpace P (insert g (Set.range f)) g S hden
  have _ := isUniformAddGroup_locUniformSpace P (insert g (Set.range f)) g S hden
  have _ := isTopologicalRing_locUniformSpace P (insert g (Set.range f)) g S hden
  let e := completionLocEquiv hA P S hden h
  have he : e.symm.toRingHom.comp (toCompletionLoc P (insert g (Set.range f)) g S hden) =
      algebraMap A (RationalFraction g f) := by
    ext a
    exact completionLocEquiv_symm_toCompletionLoc hA P S hden h a
  let T : Finset A := insert g (Finset.univ.image f)
  have hT : (T : Set A) = insert g (Set.range f) := by simp [T]
  have hdenT : P.HasDenominatorPower T g S := by rwa [hT]
  -- Generalise the numerator set before substituting: the completion's uniformity depends on it.
  have hf (U : Set A) (hd : P.HasDenominatorPower U g S) (hU : U = (T : Set A)) :
      letI := locUniformSpace P U g S hd
      letI := isUniformAddGroup_locUniformSpace P U g S hd
      letI := isTopologicalRing_locUniformSpace P U g S hd
      (toCompletionLoc P U g S hd).Flat := by
    subst U
    exact flat_toCompletionLoc P T g S hdenT
  have hflat := hf _ hden hT.symm
  exact he ▸ hflat.comp (.of_bijective e.symm.bijective)

include hA in
/-- A finite cover of the classical spectrum by rational domains gives a faithfully flat map
into the product of its rational fraction algebras. The number of numerators may vary with the
member of the cover. -/
theorem faithfullyFlat_pi_algebraMap {ι : Type*} [Finite ι] {m : ι → ℕ}
    (g : ι → A) (f : (i : ι) → Fin (m i) → A)
    (h : ∀ i, Ideal.span (insert (g i) (Set.range (f i))) = ⊤)
    (hcover : ∀ x : MaximalSpectrum A, ∃ i, x ∈ rationalDomain K (g i) (f i)) :
    (RingHom.pi fun i ↦ algebraMap A (RationalFraction (g i) (f i))).FaithfullyFlat := by
  refine RingHom.FaithfullyFlat.pi_of_exists_map_ne_top (fun i ↦ flat_algebraMap hA (h i))
    fun M hM ↦ ?_
  obtain ⟨i, hi⟩ := hcover ⟨M, hM⟩
  rw [← range_maximalSpectrumComap hA (h i)] at hi
  obtain ⟨y, hy⟩ := hi
  have hcomap : y.asIdeal.comap (algebraMap A _) = M := by
    have hy' := congrArg MaximalSpectrum.asIdeal hy
    rw [IsAffinoidAlgebra.maximalSpectrumComap_asIdeal, ← Ideal.comap_coe,
      IsScalarTower.coe_toAlgHom] at hy'
    exact hy'
  refine ⟨i, fun htop ↦ y.isMaximal.ne_top ?_⟩
  apply top_le_iff.mp
  rw [← htop, ← hcomap]
  exact Ideal.map_comap_le

end TauCeti.RationalFraction

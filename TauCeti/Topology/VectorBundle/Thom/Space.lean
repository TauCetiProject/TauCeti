/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Category.TopPair
public import TauCeti.Topology.Category.TopPair.Quotient
public import TauCeti.Topology.VectorBundle.SphereBundle.Basic

/-!
# The Thom space of a vector bundle

Let `E → B` be a bundle whose fibres are normed spaces, with unit disc bundle `D(E)` and unit
sphere bundle `S(E)` (`TauCeti.discBundle`, `TauCeti.sphereBundle`). Its **Thom space**
`Th(E) = D(E)/S(E)` (`TauCeti.thomSpace`) is the pointed quotient of the pair `(D(E), S(E))`
(`TopPair.ordinaryPairQuotient`): the sphere bundle is collapsed to a basepoint, together with an
added point, so that it is the pushout of `D(E) ← S(E) → *`, the based cofibre of the inclusion
`S(E) → D(E)` (`TauCeti.isPushout_thomSpace`). When `S(E)` is empty, for instance in rank zero,
the Thom space is `D(E)` with a disjoint basepoint
(`TauCeti.thomSpaceHomeomorphOfIsEmpty`); in rank zero `D(E)` is the whole total space
(`TauCeti.thomSpaceHomeomorphOfSubsingleton`). Over an empty base the Thom space is a single point
(`TauCeti.subsingleton_thomSpace`).

For a real vector bundle of finite rank `r` over a Hausdorff CW complex, with inner-product fibres
whose norm is continuous on the total space (`TauCeti.ContinuousFiberNorm`), the Thom space is a CW
complex with one `0`-cell, the basepoint, and one `(m + r)`-cell for each `m`-cell of the base
(`TauCeti.thomSpaceCWComplex`, in `TauCeti.Topology.CWComplex.Classical.ThomSpace`).

## References

* J. W. Milnor, J. D. Stasheff, *Characteristic Classes*, Annals of Mathematics Studies 76,
  Princeton University Press, 1974, §18 (the Thom space of a vector bundle).
* A. Hatcher, *Vector Bundles and K-Theory*, §4.D (disc bundles and Thom spaces).
-/

public section

noncomputable section

open Bundle CategoryTheory Limits Set Topology

universe u

namespace TauCeti

variable {B : Type u} (F : Type*) (E : B → Type u) [∀ b, NormedAddCommGroup (E b)]
  [TopologicalSpace (TotalSpace F E)]

/-- The **Thom space** `Th(E) = D(E)/S(E)` of a bundle with normed fibres: the unit disc bundle
with the unit sphere bundle collapsed to a basepoint. It is the pointed quotient of the pair
`(D(E), S(E))`, which has a basepoint even when `S(E)` is empty. -/
def thomSpace : TopCat.{u} :=
  (discSpherePair F E).ordinaryPairQuotient

/-- The collapse map `D(E) → Th(E)`. -/
def thomSpaceπ : TopCat.of (discBundle F E) ⟶ thomSpace F E :=
  (discSpherePair F E).ordinaryPairQuotientπ

/-- The basepoint of the Thom space, the image of the unit sphere bundle. -/
def thomSpaceBasepoint : thomSpace F E :=
  (discSpherePair F E).ordinaryPairQuotientBasepoint

/-- **The Thom space is the based cofibre of `S(E) → D(E)`.** It is the pushout of the inclusion
`S(E) → D(E)` and the map from `S(E)` to a point, with the collapse map and the basepoint as the two
maps into it. -/
theorem isPushout_thomSpace :
    IsPushout (TopCat.ofHom (ContinuousMap.inclusion (sphereBundle_subset_discBundle F E)))
      (TopCat.ofHom (ContinuousMap.const (sphereBundle F E) PUnit.unit)) (thomSpaceπ F E)
      (TopCat.ofHom (ContinuousMap.const PUnit.{u + 1} (thomSpaceBasepoint F E))) :=
  (discSpherePair F E).isPushout_ordinaryPairQuotient

/-- The collapse map sends every point of the unit sphere bundle to the basepoint. -/
@[simp]
theorem thomSpaceπ_apply_of_mem_sphereBundle (v : discBundle F E)
    (hv : (v : TotalSpace F E) ∈ sphereBundle F E) :
    thomSpaceπ F E v = thomSpaceBasepoint F E :=
  (TopPair.ordinaryPairQuotientπ_eq_basepoint_iff (discSpherePair F E) v).2
    ⟨(⟨v, hv⟩ : sphereBundle F E), rfl⟩

/-- A point of the unit disc bundle is sent to the basepoint exactly when it lies in the unit
sphere bundle. -/
theorem thomSpaceπ_eq_basepoint_iff (v : discBundle F E) :
    thomSpaceπ F E v = thomSpaceBasepoint F E ↔ (v : TotalSpace F E) ∈ sphereBundle F E := by
  refine (TopPair.ordinaryPairQuotientπ_eq_basepoint_iff (discSpherePair F E) v).trans
    ⟨?_, fun hv ↦ ⟨(⟨v, hv⟩ : sphereBundle F E), rfl⟩⟩
  rintro ⟨w, rfl⟩
  exact w.property

/-- Two points of the unit disc bundle have the same image in the Thom space exactly when they are
equal or both lie in the unit sphere bundle. -/
theorem thomSpaceπ_eq_iff (v w : discBundle F E) :
    thomSpaceπ F E v = thomSpaceπ F E w ↔
      v = w ∨
        (v : TotalSpace F E) ∈ sphereBundle F E ∧ (w : TotalSpace F E) ∈ sphereBundle F E := by
  refine (TopPair.ordinaryPairQuotientπ_eq_iff (discSpherePair F E) v w).trans
    (or_congr_right (and_congr ?_ ?_)) <;>
    exact ⟨fun ⟨u, hu⟩ ↦ hu ▸ u.property, fun hv ↦ ⟨(⟨_, hv⟩ : sphereBundle F E), rfl⟩⟩

/-- Every point of the Thom space is the basepoint or the image of a point of the unit disc
bundle. -/
theorem exists_thomSpaceπ_or_eq_basepoint (z : thomSpace F E) :
    (∃ v, thomSpaceπ F E v = z) ∨ z = thomSpaceBasepoint F E :=
  (discSpherePair F E).exists_ordinaryPairQuotientπ_or_eq_basepoint z

/-- **The Thom space over an empty base is a point.** -/
instance subsingleton_thomSpace [IsEmpty B] : Subsingleton (thomSpace F E) := by
  have (z : thomSpace F E) : z = thomSpaceBasepoint F E := by
    obtain ⟨v, -⟩ | h := exists_thomSpaceπ_or_eq_basepoint F E z
    · exact isEmptyElim (v : TotalSpace F E).proj
    · exact h
  exact ⟨fun z w ↦ (this z).trans (this w).symm⟩

/-- **The Thom space of a bundle with empty sphere bundle.** If the unit sphere bundle is empty, the
Thom space is the unit disc bundle with a disjoint basepoint. -/
def thomSpaceHomeomorphOfIsEmpty [IsEmpty (sphereBundle F E)] :
    thomSpace F E ≃ₜ discBundle F E ⊕ PUnit.{u + 1} :=
  haveI : IsEmpty (discSpherePair F E).snd := ‹IsEmpty (sphereBundle F E)›
  (discSpherePair F E).ordinaryPairQuotientEmptyHomeomorph

/-- The homeomorphism `TauCeti.thomSpaceHomeomorphOfIsEmpty` is the identity on the disc bundle. -/
@[simp]
theorem thomSpaceHomeomorphOfIsEmpty_thomSpaceπ [IsEmpty (sphereBundle F E)]
    (v : discBundle F E) :
    thomSpaceHomeomorphOfIsEmpty F E (thomSpaceπ F E v) = Sum.inl v :=
  haveI : IsEmpty (discSpherePair F E).snd := ‹IsEmpty (sphereBundle F E)›
  (discSpherePair F E).ordinaryPairQuotientEmptyHomeomorph_π v

/-- The homeomorphism `TauCeti.thomSpaceHomeomorphOfIsEmpty` sends the basepoint to the added
point. -/
@[simp]
theorem thomSpaceHomeomorphOfIsEmpty_basepoint [IsEmpty (sphereBundle F E)] :
    thomSpaceHomeomorphOfIsEmpty F E (thomSpaceBasepoint F E) = Sum.inr PUnit.unit :=
  haveI : IsEmpty (discSpherePair F E).snd := ‹IsEmpty (sphereBundle F E)›
  (discSpherePair F E).ordinaryPairQuotientEmptyHomeomorph_basepoint

section RankZero

variable [TopologicalSpace B] [NormedAddCommGroup F] [Subsingleton F] [FiberBundle F E]

/-- **The Thom space in rank zero.** For a bundle of rank zero the Thom space is the total space
with a disjoint basepoint. -/
def thomSpaceHomeomorphOfSubsingleton : thomSpace F E ≃ₜ TotalSpace F E ⊕ PUnit.{u + 1} :=
  (thomSpaceHomeomorphOfIsEmpty F E).trans
    (((Homeomorph.setCongr (discBundle_eq_univ_of_subsingleton (F := F) (E := E))).trans
      (Homeomorph.Set.univ _)).sumCongr (Homeomorph.refl _))

/-- The homeomorphism `TauCeti.thomSpaceHomeomorphOfSubsingleton` sends the image of a vector to
that vector. -/
@[simp]
theorem thomSpaceHomeomorphOfSubsingleton_thomSpaceπ (v : discBundle F E) :
    thomSpaceHomeomorphOfSubsingleton F E (thomSpaceπ F E v) = Sum.inl (v : TotalSpace F E) := by
  rw [thomSpaceHomeomorphOfSubsingleton, Homeomorph.trans_apply,
    thomSpaceHomeomorphOfIsEmpty_thomSpaceπ]
  -- `Homeomorph.setCongr` and `Homeomorph.Set.univ` keep the underlying point.
  rfl

/-- The homeomorphism `TauCeti.thomSpaceHomeomorphOfSubsingleton` sends the basepoint to the added
point. -/
@[simp]
theorem thomSpaceHomeomorphOfSubsingleton_basepoint :
    thomSpaceHomeomorphOfSubsingleton F E (thomSpaceBasepoint F E) = Sum.inr PUnit.unit := by
  rw [thomSpaceHomeomorphOfSubsingleton, Homeomorph.trans_apply,
    thomSpaceHomeomorphOfIsEmpty_basepoint]
  -- The second summand is mapped by the identity.
  rfl

end RankZero

end TauCeti

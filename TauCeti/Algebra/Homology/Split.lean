/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.Homotopy
public import Mathlib.CategoryTheory.Preadditive.Projective.Basic
public import TauCeti.Algebra.Homology.Boundaries

/-!
# Split complexes are homotopy equivalent to complexes with zero differential

Let `K` be a homological complex, of any shape, in an abelian category.  Write `Zᵢ` for its cycles
and `Hᵢ` for its homology.  Suppose that in every degree the inclusion `Zᵢ ⟶ Kᵢ` of the cycles is
a split monomorphism and the projection `Zᵢ ⟶ Hᵢ` onto the homology is a split epimorphism.  Then
`K` is chain homotopy equivalent to the complex with terms `Hᵢ` and zero differentials
(`HomologicalComplex.exists_homotopyEquiv_d_eq_zero`).

Both hypotheses hold for every complex of vector spaces, and more generally of semisimple modules
(see `TauCeti.Algebra.Homology.Semisimple`).  The second holds whenever the homology objects are
projective (`HomologicalComplex.isSplitEpi_homologyπ_of_projective`).  As a mathematical remark
not formalized here, the first holds for a complex of projective modules over a principal ideal
domain, or over any hereditary ring, since the image of the differential out of `Kᵢ` is then
projective.  The result therefore reduces statements
about the homology of such complexes, such as the Künneth theorem, to complexes with zero
differential.

The construction is the classical splitting.  Choose a retraction `r : Kᵢ ⟶ Zᵢ` of the inclusion
`ι : Zᵢ ⟶ Kᵢ` and a section `s : Hᵢ ⟶ Zᵢ` of the projection `π : Zᵢ ⟶ Hᵢ`.  The chain maps are
`s ≫ ι : Hᵢ ⟶ Kᵢ` and `r ≫ π : Kᵢ ⟶ Hᵢ`, and their composite on `H` is the identity.  For a
relation `j → i` of the shape, the differential `Kⱼ ⟶ Kᵢ` corestricts to an epimorphism onto the
boundaries `Bᵢ = ker π` with kernel `Zⱼ`, so it is the cokernel of `Zⱼ ⟶ Kⱼ`.  The idempotent
`𝟙 - r ≫ ι` of `Kⱼ` kills `Zⱼ` and therefore factors through `Bᵢ`; the resulting map `Bᵢ ⟶ Kⱼ`
inverts the differential on the complement of the cycles.  Precomposing it with the
`Bᵢ`-component `r ≫ (𝟙 - π ≫ s)` of `Kᵢ` gives the homotopy `h : Kᵢ ⟶ Kⱼ`, with
`𝟙 - (r ≫ π) ≫ (s ≫ ι) = d h + h d`.

## Main results

* `HomologicalComplex.exists_homotopyEquiv_d_eq_zero`: a complex whose cycles split off and whose
  homology splits off its cycles is homotopy equivalent to a complex with zero differentials.
* `HomologicalComplex.isSplitEpi_homologyπ_of_projective`: the projection onto a projective
  homology object splits.

## References

* C. Weibel, *An Introduction to Homological Algebra*, Section 1.4 (split complexes).
-/

public section

noncomputable section

open CategoryTheory Limits

namespace HomologicalComplex

variable {C : Type*} [Category* C] [Abelian C] {ι : Type*} {c : ComplexShape ι}
  (K : HomologicalComplex C c)

/-- The projection from the cycles onto a projective homology object is a split epimorphism. -/
instance isSplitEpi_homologyπ_of_projective (i : ι) [Projective (K.homology i)] :
    IsSplitEpi (K.homologyπ i) :=
  ⟨⟨Projective.factorThru (𝟙 _) (K.homologyπ i), Projective.factorThru_comp _ _⟩⟩

namespace Split

/-! ### Inverting the differential on the complement of the cycles -/

variable [∀ i, IsSplitMono (K.iCycles i)]

/-- The differential into `Kᵢ` followed by the retraction `r : Kᵢ ⟶ Zᵢ` is the corestriction of
the differential to the cycles. -/
@[reassoc (attr := local simp)]
private lemma d_retraction (j i : ι) : K.d j i ≫ retraction (K.iCycles i) = K.toCycles j i := by
  simp [← K.toCycles_i_assoc]

/-- For a relation `j → i` of the shape, the map `Bᵢ ⟶ Kⱼ` through which the projection
`𝟙 - r ≫ ι` of `Kⱼ` onto the complement of the cycles factors. -/
private def fromBoundaries {j i : ι} (hji : c.Rel j i) : kernel (K.homologyπ i) ⟶ K.X j :=
  (CokernelCofork.IsColimit.desc' (K.toBoundariesIsCokernel hji)
    (𝟙 _ - retraction (K.iCycles j) ≫ K.iCycles j) (by simp [Preadditive.comp_sub])).1

private lemma toBoundaries_fromBoundaries {j i : ι} (hji : c.Rel j i) :
    K.toBoundaries j i ≫ fromBoundaries K hji = 𝟙 _ - retraction (K.iCycles j) ≫ K.iCycles j :=
  (CokernelCofork.IsColimit.desc' (K.toBoundariesIsCokernel hji) _ _).2

/-- The map `Bᵢ ⟶ Kⱼ` is a section of the differential: followed by the differential it is the
inclusion of the boundaries. -/
private lemma fromBoundaries_d {j i : ι} (hji : c.Rel j i) :
    fromBoundaries K hji ≫ K.d j i = kernel.ι _ ≫ K.iCycles i := by
  have := K.epi_toBoundaries hji
  rw [← cancel_epi (K.toBoundaries j i), reassoc_of% toBoundaries_fromBoundaries K hji]
  simp [Preadditive.sub_comp]

/-! ### The homotopy -/

variable [∀ i, IsSplitEpi (K.homologyπ i)]

/-- The component `r ≫ (𝟙 - π ≫ s) : Kᵢ ⟶ Bᵢ` of `Kᵢ` in the boundaries. -/
private def boundaryPart (i : ι) : K.X i ⟶ kernel (K.homologyπ i) :=
  kernel.lift _ (retraction (K.iCycles i) ≫ (𝟙 _ - K.homologyπ i ≫ section_ (K.homologyπ i)))
    (by simp [Preadditive.sub_comp])

/-- The differential into `Kᵢ`, followed by the boundary component, is the corestriction of the
differential to the boundaries. -/
private lemma d_boundaryPart (j i : ι) : K.d j i ≫ boundaryPart K i = K.toBoundaries j i := by
  rw [← cancel_mono (kernel.ι _)]
  simp [boundaryPart, Preadditive.comp_sub]

/-- The homotopy `Kᵢ ⟶ Kⱼ` for a relation `j → i` of the shape. -/
private def htpy (i j : ι) (hji : c.Rel j i) : K.X i ⟶ K.X j :=
  boundaryPart K i ≫ fromBoundaries K hji

/-- `h ≫ d` is the boundary component `r ≫ (𝟙 - π ≫ s) ≫ ι` of `Kᵢ`. -/
private lemma htpy_d {i j : ι} (hji : c.Rel j i) :
    htpy K i j hji ≫ K.d j i =
      retraction (K.iCycles i) ≫ (𝟙 _ - K.homologyπ i ≫ section_ (K.homologyπ i)) ≫
        K.iCycles i := by
  simp [htpy, fromBoundaries_d, boundaryPart]

/-- `d ≫ h` is the projection `𝟙 - r ≫ ι` onto the complement of the cycles. -/
private lemma d_htpy {i k : ι} (hik : c.Rel i k) :
    K.d i k ≫ htpy K k i hik = 𝟙 _ - retraction (K.iCycles i) ≫ K.iCycles i := by
  rw [htpy, reassoc_of% d_boundaryPart K i k, toBoundaries_fromBoundaries]

/-! ### The complex of homology objects -/

/-- The complex with the homology objects of `K` as terms and zero differentials. -/
@[simps]
private abbrev homologyComplex : HomologicalComplex C c where
  X i := K.homology i
  d _ _ := 0

/-- The inclusion `s ≫ ι : Hᵢ ⟶ Kᵢ`, a chain map since it lands in the cycles. -/
private def incl : homologyComplex K ⟶ K where
  f i := section_ (K.homologyπ i) ≫ K.iCycles i
  comm' i j _ := by simp

/-- The projection `r ≫ π : Kᵢ ⟶ Hᵢ`, a chain map since boundaries have zero homology class. -/
private def proj : K ⟶ homologyComplex K where
  f i := retraction (K.iCycles i) ≫ K.homologyπ i
  comm' i j _ := by simp

private lemma incl_proj : incl K ≫ proj K = 𝟙 _ := by
  ext i
  simp [incl, proj]

/-- The identity of `K` minus the idempotent `proj ≫ incl` is `d h + h d`.  The term `d h` is the
component of `Kᵢ` in the complement of the cycles, which vanishes when no differential leaves `i`,
and `h d` is the component in the boundaries, which vanishes when no differential arrives. -/
private lemma id_sub_proj_incl :
    𝟙 K - proj K ≫ incl K = Homotopy.nullHomotopicMap' (htpy K) := by
  ext i
  -- with no differential out of `i`, all of `Kᵢ` is cycles, so `r ≫ ι = 𝟙`
  have hZ (hn : ∀ l, ¬c.Rel i l) : retraction (K.iCycles i) ≫ K.iCycles i = 𝟙 _ := by
    have := K.isIso_iCycles i (c.next i) rfl (K.shape _ _ (hn _))
    rw [IsIso.eq_inv_of_hom_inv_id (IsSplitMono.id (K.iCycles i)), IsIso.inv_hom_id]
  -- with no differential into `i`, the cycles are the homology, so `π ≫ s = 𝟙`
  have hB (hp : ∀ l, ¬c.Rel l i) : K.homologyπ i ≫ section_ (K.homologyπ i) = 𝟙 _ := by
    have := K.isIso_homologyπ (c.prev i) i rfl (K.shape _ _ (hp _))
    rw [IsIso.eq_inv_of_inv_hom_id (IsSplitEpi.id (K.homologyπ i)), IsIso.hom_inv_id]
  simp only [HomologicalComplex.sub_f_apply, HomologicalComplex.id_f, HomologicalComplex.comp_f,
    proj, incl, Category.assoc]
  by_cases hn : c.Rel i (c.next i) <;> by_cases hp : c.Rel (c.prev i) i
  · rw [Homotopy.nullHomotopicMap'_f hp hn, d_htpy, htpy_d]
    simp only [Preadditive.sub_comp, Preadditive.comp_sub, Category.id_comp, Category.assoc]
    abel
  · have hp' : ∀ l, ¬c.Rel l i := fun l hl ↦ hp (by rwa [c.prev_eq' hl])
    rw [Homotopy.nullHomotopicMap'_f_of_not_rel_right hn hp', d_htpy, reassoc_of% hB hp']
  · have hn' : ∀ l, ¬c.Rel i l := fun l hl ↦ hn (by rwa [c.next_eq' hl])
    rw [Homotopy.nullHomotopicMap'_f_of_not_rel_left hp hn', htpy_d, Preadditive.sub_comp,
      Preadditive.comp_sub, Category.id_comp, hZ hn', Category.assoc]
  · have hp' : ∀ l, ¬c.Rel l i := fun l hl ↦ hp (by rwa [c.prev_eq' hl])
    have hn' : ∀ l, ¬c.Rel i l := fun l hl ↦ hn (by rwa [c.next_eq' hl])
    rw [Homotopy.nullHomotopicMap'_f_eq_zero hn' hp', reassoc_of% hB hp', hZ hn', sub_self]

/-- The homotopy equivalence between `K` and the complex of its homology objects with zero
differentials. -/
private def homotopyEquiv : HomotopyEquiv K (homologyComplex K) where
  hom := proj K
  inv := incl K
  homotopyHomInvId :=
    (Homotopy.equivSubZero.symm
      ((Homotopy.ofEq (id_sub_proj_incl K)).trans (Homotopy.nullHomotopy' (htpy K)))).symm
  homotopyInvHomId := Homotopy.ofEq (incl_proj K)

end Split

variable [∀ i, IsSplitMono (K.iCycles i)] [∀ i, IsSplitEpi (K.homologyπ i)]

open Split in
/-- A complex in an abelian category whose cycles split off its terms and whose homology splits off
its cycles is chain homotopy equivalent to a complex with zero differentials.  This applies to
every complex of semisimple modules, for instance of vector spaces over a division ring.  The terms
of such a complex are its homology, so by `HomotopyEquiv.toHomologyIso` they are the homology of
`K`. -/
theorem exists_homotopyEquiv_d_eq_zero :
    ∃ L : HomologicalComplex C c, (∀ i j, L.d i j = 0) ∧ Nonempty (HomotopyEquiv K L) :=
  ⟨homologyComplex K, fun _ _ ↦ rfl, ⟨homotopyEquiv K⟩⟩

end HomologicalComplex

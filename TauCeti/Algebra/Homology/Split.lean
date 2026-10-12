/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.Homotopy
public import Mathlib.CategoryTheory.Preadditive.Projective.Basic
public import TauCeti.Algebra.Homology.Boundaries
import Mathlib.Algebra.Homology.ShortComplex.ShortExact

/-!
# Split complexes are homotopy equivalent to complexes with zero differential

Let `K` be a homological complex, of any shape, in an abelian category.  Write `Zᵢ` for its cycles
and `Hᵢ` for its homology.  Suppose that in every degree the inclusion `Zᵢ ⟶ Kᵢ` of the cycles is
a split monomorphism and the projection `Zᵢ ⟶ Hᵢ` onto the homology is a split epimorphism.  Then
`K` is chain homotopy equivalent to the complex with terms `Hᵢ` and zero differentials
(`HomologicalComplex.exists_homotopyEquiv_d_eq_zero`).

Both hypotheses hold for every complex of vector spaces, and more generally of semisimple modules
(see `TauCeti.Algebra.Homology.Semisimple`).  The second holds whenever the homology objects are
projective (`HomologicalComplex.isSplitEpi_homologyπ_of_projective`).  The first holds for a
complex of projective modules over a principal ideal domain, since the image of the differential
out of `Kᵢ` is then projective (`HomologicalComplex.isSplitMono_iCycles_of_isPrincipalIdealRing`);
mathematically, the same argument works over any hereditary ring.  The result therefore reduces
statements about the homology of such complexes, such as the Künneth theorem, to complexes with
zero differential.

When only the cycles split off, the projection `r ≫ π` onto the complex `K.homologyComplex` of
homology objects (`HomologicalComplex.toHomologyComplex`) is still a chain map inducing
isomorphisms on homology (`HomologicalComplex.isIso_homologyMap_toHomologyComplex`), although it
need not be a homotopy equivalence.  This is the situation for complexes of free abelian groups,
and it is what splits the Künneth short exact sequence.

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
* `HomologicalComplex.isSplitMono_iCycles_of_projective`: the cycles split off a term whose
  quotient by them is projective.
* `HomologicalComplex.homologyComplex`, `HomologicalComplex.toHomologyComplex` and
  `HomologicalComplex.isIso_homologyMap_toHomologyComplex`: the complex of homology objects, and
  the projection onto it when the cycles split off, a quasi-isomorphism.

## References

* C. Weibel, *An Introduction to Homological Algebra*, Section 1.4 (split complexes).
-/

public section

noncomputable section

open CategoryTheory Limits

namespace HomologicalComplex

variable {C : Type*} [Category* C] {ι : Type*} {c : ComplexShape ι}

/-- The projection from the cycles onto a projective homology object is a split epimorphism.
This only requires homology in degree `i`, in a category with zero morphisms. -/
instance isSplitEpi_homologyπ_of_projective [HasZeroMorphisms C]
    (K : HomologicalComplex C c) (i : ι) [K.HasHomology i] [Projective (K.homology i)] :
    IsSplitEpi (K.homologyπ i) :=
  ⟨⟨Projective.factorThru (𝟙 _) (K.homologyπ i), Projective.factorThru_comp _ _⟩⟩

variable [Abelian C] (K : HomologicalComplex C c)

/-! ### The complex of homology objects -/

/-- The complex with the homology objects of `K` as terms and zero differentials. -/
@[expose, simps X]
def homologyComplex : HomologicalComplex C c where
  X i := K.homology i
  d _ _ := 0

/-- The complex of homology objects has zero differentials. -/
@[simp]
lemma homologyComplex_d (i j : ι) : K.homologyComplex.d i j = 0 :=
  rfl

/-- The inclusion of the cycles is a split monomorphism when the quotient of the term by its cycles
is projective. -/
instance isSplitMono_iCycles_of_projective (i : ι) [Projective (cokernel (K.iCycles i))] :
    IsSplitMono (K.iCycles i) :=
  have hS : (ShortComplex.mk (K.iCycles i) (cokernel.π (K.iCycles i))
      (cokernel.condition _)).ShortExact :=
    { exact := ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel _) }
  .mk' ⟨hS.splittingOfProjective.r, hS.splittingOfProjective.f_r⟩

variable [∀ i, IsSplitMono (K.iCycles i)]

/-- The differential into `Kᵢ` followed by the retraction `r : Kᵢ ⟶ Zᵢ` is the corestriction of
the differential to the cycles. -/
@[reassoc (attr := local simp)]
private lemma d_retraction (j i : ι) : K.d j i ≫ retraction (K.iCycles i) = K.toCycles j i := by
  simp [← K.toCycles_i_assoc]

/-- The projection `r ≫ π : Kᵢ ⟶ Hᵢ` onto the complex of homology objects, where `r` is the
chosen retraction of the inclusion of the cycles; it is a chain map since boundaries have zero
homology class.  It depends on the choice of `r`, so it need not be natural in `K`. -/
def toHomologyComplex : K ⟶ K.homologyComplex where
  f i := retraction (K.iCycles i) ≫ K.homologyπ i
  comm' i j _ := by simp [homologyComplex]

/-- The components of the projection onto the complex of homology objects. -/
@[simp]
lemma toHomologyComplex_f (i : ι) :
    K.toHomologyComplex.f i = retraction (K.iCycles i) ≫ K.homologyπ i :=
  (rfl)

/-- On the cycles, the projection onto the complex of homology objects is the projection onto
homology. -/
@[reassoc]
lemma iCycles_toHomologyComplex_f (i : ι) :
    K.iCycles i ≫ K.toHomologyComplex.f i = K.homologyπ i :=
  IsSplitMono.id_assoc _ _

/-- The projection onto the complex of homology objects induces isomorphisms on homology. -/
instance isIso_homologyMap_toHomologyComplex (i : ι) :
    IsIso (homologyMap K.toHomologyComplex i) := by
  have := K.homologyComplex.isIso_iCycles i (c.next i) rfl (by simp)
  have := K.homologyComplex.isIso_homologyπ (c.prev i) i rfl (by simp)
  -- the homology of `K.homologyComplex` is its term, through `π⁻¹ ≫ ι`, and the induced map
  -- followed by this identification is the identity
  have h : homologyMap K.toHomologyComplex i ≫ inv (K.homologyComplex.homologyπ i) ≫
      K.homologyComplex.iCycles i = 𝟙 (K.homology i) := by
    refine (cancel_epi (K.homologyπ i)).1 ?_
    rw [homologyπ_naturality_assoc, IsIso.hom_inv_id_assoc, cyclesMap_i]
    exact (iCycles_toHomologyComplex_f K i).trans (Category.comp_id _).symm
  have : IsIso (homologyMap K.toHomologyComplex i ≫ inv (K.homologyComplex.homologyπ i) ≫
      K.homologyComplex.iCycles i) := by
    rw [h]
    exact IsIso.id _
  exact IsIso.of_isIso_comp_right _ (inv (K.homologyComplex.homologyπ i) ≫
    K.homologyComplex.iCycles i)

namespace Split

/-! ### Inverting the differential on the complement of the cycles -/

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

/-! ### The inclusion of the homology objects -/

/-- The inclusion `s ≫ ι : Hᵢ ⟶ Kᵢ`, a chain map since it lands in the cycles. -/
private def incl : K.homologyComplex ⟶ K where
  f i := (section_ (K.homologyπ i) : K.homology i ⟶ _) ≫ K.iCycles i
  comm' i j _ := by simp [homologyComplex]

private lemma incl_toHomologyComplex : incl K ≫ K.toHomologyComplex = 𝟙 _ := by
  ext i
  exact (Category.assoc _ _ _).trans
    ((section_ (K.homologyπ i) ≫= K.iCycles_toHomologyComplex_f i).trans
      (IsSplitEpi.id (K.homologyπ i)))

private lemma toHomologyComplex_f_incl_f (i : ι) :
    K.toHomologyComplex.f i ≫ (incl K).f i =
      retraction (K.iCycles i) ≫ K.homologyπ i ≫ section_ (K.homologyπ i) ≫ K.iCycles i :=
  Category.assoc _ _ _

/-- The identity of `K` minus the idempotent `toHomologyComplex ≫ incl` is `d h + h d`.  The term
`d h` is the component of `Kᵢ` in the complement of the cycles, which vanishes when no differential
leaves `i`, and `h d` is the component in the boundaries, which vanishes when no differential
arrives. -/
private lemma id_sub_toHomologyComplex_incl :
    𝟙 K - K.toHomologyComplex ≫ incl K = Homotopy.nullHomotopicMap' (htpy K) := by
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
    toHomologyComplex_f_incl_f]
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
private def homotopyEquiv : HomotopyEquiv K K.homologyComplex where
  hom := K.toHomologyComplex
  inv := incl K
  homotopyHomInvId :=
    (Homotopy.equivSubZero.symm
      ((Homotopy.ofEq (id_sub_toHomologyComplex_incl K)).trans
        (Homotopy.nullHomotopy' (htpy K)))).symm
  homotopyInvHomId := Homotopy.ofEq (incl_toHomologyComplex K)

end Split

variable [∀ i, IsSplitEpi (K.homologyπ i)]

open Split in
/-- A complex in an abelian category whose cycles split off its terms and whose homology splits off
its cycles is chain homotopy equivalent to a complex with zero differentials.  This applies to
every complex of semisimple modules, for instance of vector spaces over a division ring.  The terms
of such a complex are its homology, so by `HomotopyEquiv.toHomologyIso` they are the homology of
`K`. -/
theorem exists_homotopyEquiv_d_eq_zero :
    ∃ L : HomologicalComplex C c, (∀ i j, L.d i j = 0) ∧ Nonempty (HomotopyEquiv K L) :=
  ⟨K.homologyComplex, K.homologyComplex_d, ⟨homotopyEquiv K⟩⟩

end HomologicalComplex

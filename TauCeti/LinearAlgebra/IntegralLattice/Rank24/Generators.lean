/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.IntegralLattice.Rank24.Niemeier

/-!
# Computable rational generators and coset decompositions for glued rootful rank-24 lattices

`TauCeti.LinearAlgebra.IntegralLattice.Rank24.Niemeier` constructs each of the 23 rootful Niemeier
lattices `N_r = r.lattice` by gluing the orthogonal sum `R_r = r.rootLattice` of its ADE component
root lattices along its decoded Conway--Sloane glue subgroup `H_r = r.glueSubgroup`, and shows
(`TauCeti.RootfulNiemeierType.lattice_carrier_eq_sup_span`) that `N_r` is spanned by `R_r` and any
choice of dual coset representatives of its glue generators.

Combining the componentwise simple-root vectors `TauCeti.DynkinType.piSimpleRootVectors` of
`TauCeti.LinearAlgebra.IntegralLattice.RootLattice.OrthogonalSum` with the explicit shortest
dual-lattice representatives `TauCeti.DynkinType.glueWordRepresentativeVector` and
`TauCeti.glueWordVector` of `TauCeti.LinearAlgebra.IntegralLattice.Rank24.GlueWord`, this file
makes both the simple-root generators and the shortest glue-word generators explicit and computable
in rational simple-root coordinates `∀ i, Fin (r.componentType i).rank → ℚ`, uniformly for all 23
rows (and hence immediately for all 23 named abbreviations `niemeierD24`, …,
`niemeierA1TwentyFourth`):

* `r.simpleRootVectors` is the computable `Finset` of `24` norm-`2` simple-root vectors spanning
  `r.rootLattice.carrier`;
* `r.glueGeneratorVectors` is the computable `Finset` of shortest rational glue vectors obtained
  by applying `TauCeti.glueWordVector` to the row's digit glue words `r.glueWords`, with
  `r.lattice.carrier = r.rootLattice.carrier ⊔ Submodule.span ℤ r.glueGeneratorVectors`;
* `r.generatorVectors = r.simpleRootVectors ∪ r.glueGeneratorVectors` is a computable `Finset`
  whose `ℤ`-span is literally `r.lattice.carrier` (`span_generatorVectors`);
* `glueWordRepresentativeVector_mem_lattice_carrier_iff`, `mem_lattice_carrier_iff_exists_sub_mem`,
  and `mem_lattice_carrier_iff_exists_int` characterize membership in `r.lattice.carrier` by
  explicit coset differences and coordinatewise integrality.

## Main declarations

* `TauCeti.RootfulNiemeierType.simpleRootVectors` and
  `TauCeti.RootfulNiemeierType.span_simpleRootVectors`: the `24` simple-root vectors spanning `R_r`.
* `TauCeti.RootfulNiemeierType.glueGeneratorVectors` and
  `TauCeti.RootfulNiemeierType.lattice_carrier_eq_sup_span_glueGeneratorVectors`: computable
  shortest glue-generator vectors of a row.
* `TauCeti.RootfulNiemeierType.generatorVectors` and
  `TauCeti.RootfulNiemeierType.span_generatorVectors`: computable finite `ℤ`-generating set of
  `N_r`.
* `TauCeti.RootfulNiemeierType.glueWordRepresentativeVector_mem_lattice_carrier_iff`,
  `TauCeti.RootfulNiemeierType.mem_lattice_carrier_iff_exists_sub_mem`,
  `TauCeti.RootfulNiemeierType.mem_lattice_carrier_iff_exists_int`: explicit coset-membership
  criteria for `N_r`.

## References

* J. H. Conway and N. J. A. Sloane, *Sphere Packings, Lattices and Groups*, 3rd ed., Chapter 4
  §§6--8 and Chapter 16 §1, Table 16.1.
* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Plates I--VII.
-/

public section

namespace TauCeti.RootfulNiemeierType

open IntegralLattice

/-- **Computable finite set of simple-root vectors** of a row `r`, in componentwise Bourbaki
simple-root coordinates `∀ i, Fin (r.componentType i).rank → ℚ`. -/
def simpleRootVectors (r : RootfulNiemeierType) :
    Finset (∀ i, Fin (r.componentType i).rank → ℚ) :=
  DynkinType.piSimpleRootVectors r.componentType

/-- `r.simpleRootVectors` is `DynkinType.piSimpleRootVectors r.componentType`. -/
theorem simpleRootVectors_def (r : RootfulNiemeierType) :
    r.simpleRootVectors = DynkinType.piSimpleRootVectors r.componentType :=
  (rfl)

/-- A vector belongs to `r.simpleRootVectors` if and only if it is
`DynkinType.piSimpleRootVector r.componentType p` for some componentwise simple-root index `p`. -/
@[simp]
theorem mem_simpleRootVectors_iff {r : RootfulNiemeierType}
    {v : ∀ i, Fin (r.componentType i).rank → ℚ} :
    v ∈ r.simpleRootVectors ↔
      ∃ p, DynkinType.piSimpleRootVector r.componentType p = v := by
  rw [simpleRootVectors_def, DynkinType.mem_piSimpleRootVectors_iff]

/-- Every row has `24` simple-root vectors. -/
@[simp]
theorem card_simpleRootVectors (r : RootfulNiemeierType) :
    r.simpleRootVectors.card = 24 := by
  rw [simpleRootVectors_def, DynkinType.card_piSimpleRootVectors]
  cases r <;> decide

/-- Every simple-root vector of `r` lies in `r.rootLattice.carrier`. -/
theorem simpleRootVectors_subset_rootLattice_carrier (r : RootfulNiemeierType) :
    (r.simpleRootVectors : Set (∀ i, Fin (r.componentType i).rank → ℚ)) ⊆
      r.rootLattice.carrier :=
  DynkinType.piSimpleRootVectors_subset_carrier r.componentType r.isSimplyLaced_componentType

/-- Every simple-root vector of `r` lies in `r.lattice.carrier`. -/
theorem simpleRootVectors_subset_lattice_carrier (r : RootfulNiemeierType) :
    (r.simpleRootVectors : Set (∀ i, Fin (r.componentType i).rank → ℚ)) ⊆
      r.lattice.carrier :=
  r.simpleRootVectors_subset_rootLattice_carrier.trans r.rootLattice_carrier_le_lattice_carrier

/-- Every simple-root vector of `r` has squared norm `2` in `r.lattice`. -/
theorem form_self_of_mem_simpleRootVectors (r : RootfulNiemeierType)
    {v : ∀ i, Fin (r.componentType i).rank → ℚ} (hv : v ∈ r.simpleRootVectors) :
    r.lattice.form v v = 2 := by
  obtain ⟨p, rfl⟩ := r.mem_simpleRootVectors_iff.mp hv
  rw [r.lattice_form]
  exact DynkinType.form_piSimpleRootVector_self r.componentType r.isSimplyLaced_componentType p

/-- **The `24` simple-root vectors of `r` span `r.rootLattice.carrier` over `ℤ`.** -/
@[simp]
theorem span_simpleRootVectors (r : RootfulNiemeierType) :
    Submodule.span ℤ (r.simpleRootVectors : Set (∀ i, Fin (r.componentType i).rank → ℚ)) =
      r.rootLattice.carrier :=
  DynkinType.span_piSimpleRootVectors r.componentType r.isSimplyLaced_componentType

/-- **Computable finite set of shortest glue-generator vectors** of a row `r`, obtained from the
row's digit glue words `r.glueWords` (expanded from its patterns and span mode) via
`glueWordVector`. -/
def glueGeneratorVectors (r : RootfulNiemeierType) :
    Finset (∀ i, Fin (r.componentType i).rank → ℚ) :=
  r.glueWords.image (glueWordVector r.componentType)

/-- `r.glueGeneratorVectors` is the image of `r.glueWords` under `glueWordVector`. -/
theorem glueGeneratorVectors_def (r : RootfulNiemeierType) :
    r.glueGeneratorVectors = r.glueWords.image (glueWordVector r.componentType) :=
  (rfl)

/-- A vector belongs to `r.glueGeneratorVectors` if and only if it is
`glueWordVector r.componentType l` for some digit glue word `l ∈ r.glueWords`. -/
@[simp]
theorem mem_glueGeneratorVectors_iff {r : RootfulNiemeierType}
    {v : ∀ i, Fin (r.componentType i).rank → ℚ} :
    v ∈ r.glueGeneratorVectors ↔
      ∃ l ∈ r.glueWords, glueWordVector r.componentType l = v := by
  simp [glueGeneratorVectors_def]

/-- Distinct digit glue words in `r.glueWords` produce distinct vectors in
`r.glueGeneratorVectors`, so `r.glueGeneratorVectors` has the same cardinality as `r.glueWords`. -/
@[simp]
theorem card_glueGeneratorVectors (r : RootfulNiemeierType) :
    r.glueGeneratorVectors.card = r.glueWords.card := by
  rw [glueGeneratorVectors_def]
  refine Finset.card_image_of_injOn fun l₁ hl₁ l₂ hl₂ h ↦ ?_
  obtain ⟨w₁, -, hd₁⟩ := exists_decodeGlueWord_mem_glueGenerators hl₁
  obtain ⟨w₂, -, hd₂⟩ := exists_decodeGlueWord_mem_glueGenerators hl₂
  rw [glueWordVector_eq_of_decodeGlueWord_eq_some _ _ hd₁,
    glueWordVector_eq_of_decodeGlueWord_eq_some _ _ hd₂] at h
  have hw : w₁ = w₂ := DynkinType.glueWordRepresentativeVector_injective
    r.componentType r.isSimplyLaced_componentType r.valid_componentType h
  subst hw
  exact ((decodeGlueWord_eq_some_iff _ _ _ _).mp hd₁).trans
    ((decodeGlueWord_eq_some_iff _ _ _ _).mp hd₂).symm

/-- `r.glueGeneratorVectors` is literally the image of the decoded generator set `r.glueGenerators`
under `DynkinType.glueWordRepresentativeVector`. -/
theorem coe_glueGeneratorVectors_eq_image_glueGenerators (r : RootfulNiemeierType) :
    (r.glueGeneratorVectors : Set (∀ i, Fin (r.componentType i).rank → ℚ)) =
      DynkinType.glueWordRepresentativeVector r.componentType r.isSimplyLaced_componentType ''
        r.glueGenerators := by
  rw [glueGeneratorVectors_def, Finset.coe_image]
  ext v
  constructor
  · rintro ⟨l, hl, rfl⟩
    obtain ⟨w, hw, hdec⟩ := exists_decodeGlueWord_mem_glueGenerators hl
    exact ⟨w, hw, (glueWordVector_eq_of_decodeGlueWord_eq_some _ _ hdec).symm⟩
  · rintro ⟨w, hw, rfl⟩
    exact ⟨encodeGlueWord r.componentType r.isSimplyLaced_componentType w,
      mem_glueGenerators_iff.mp hw, glueWordVector_encodeGlueWord _ _ w⟩

/-- Every glue-generator vector of `r` lies in `r.rootLattice.dualCarrier`. -/
theorem glueGeneratorVectors_subset_dualCarrier (r : RootfulNiemeierType) :
    (r.glueGeneratorVectors : Set (∀ i, Fin (r.componentType i).rank → ℚ)) ⊆
      r.rootLattice.dualCarrier := by
  rw [glueGeneratorVectors_def, Finset.coe_image]
  rintro _ ⟨l, -, rfl⟩
  exact glueWordVector_mem_dualCarrier r.componentType r.valid_componentType
    r.isSimplyLaced_componentType l

/-- **Explicit shortest-representative span formula for `N_r`**: `r.lattice.carrier` is spanned by
`r.rootLattice.carrier` together with the computable shortest glue vectors
`r.glueGeneratorVectors`. -/
theorem lattice_carrier_eq_sup_span_glueGeneratorVectors (r : RootfulNiemeierType) :
    r.lattice.carrier =
      r.rootLattice.carrier ⊔
        Submodule.span ℤ
          (r.glueGeneratorVectors : Set (∀ i, Fin (r.componentType i).rank → ℚ)) := by
  rw [lattice_def, coe_glueGeneratorVectors_eq_image_glueGenerators]
  exact DynkinType.gluedLattice_carrier_eq_sup_span_glueWordRepresentativeVector
    r.componentType r.isSimplyLaced_componentType r.valid_componentType
    r.glueSubgroup r.isIsotropic_glueSubgroup (glueSubgroup_def r).symm

/-- Every glue-generator vector of `r` lies in `r.lattice.carrier`. -/
theorem glueGeneratorVectors_subset_lattice_carrier (r : RootfulNiemeierType) :
    (r.glueGeneratorVectors : Set (∀ i, Fin (r.componentType i).rank → ℚ)) ⊆
      r.lattice.carrier := by
  rw [lattice_carrier_eq_sup_span_glueGeneratorVectors]
  exact Submodule.subset_span.trans (SetLike.coe_subset_coe.mpr le_sup_right)

/-- For every digit glue word `l ∈ r.glueWords` of the row, its rational vector
`glueWordVector r.componentType l` has squared norm `glueWordMinimum r.componentType l` in
`r.lattice`. -/
theorem form_glueWordVector_self_of_mem_glueWords (r : RootfulNiemeierType) {l : List ℕ}
    (hl : l ∈ r.glueWords) :
    r.lattice.form (glueWordVector r.componentType l) (glueWordVector r.componentType l) =
      glueWordMinimum r.componentType l := by
  rw [r.lattice_form]
  exact form_glueWordVector_self r.componentType r.valid_componentType
    r.isSimplyLaced_componentType (isValidGlueWord_of_mem_glueWords hl)

/-- Every non-zero digit glue word `l ∈ r.glueWords` of the row yields a glue-generator vector of
squared norm at least `4`. -/
theorem four_le_form_glueWordVector_self_of_mem_glueWords (r : RootfulNiemeierType) {l : List ℕ}
    (hl : l ∈ r.glueWords) (hne : l ≠ List.replicate r.components.length 0) :
    4 ≤ r.lattice.form (glueWordVector r.componentType l) (glueWordVector r.componentType l) := by
  rw [r.form_glueWordVector_self_of_mem_glueWords hl]
  obtain ⟨w, hw, hdec⟩ := exists_decodeGlueWord_mem_glueGenerators hl
  have hwmem : w ∈ r.glueSubgroup := r.glueSubgroup_def ▸ AddSubgroup.subset_closure hw
  have hw0 : w ≠ 0 := by
    rintro rfl
    exact hne (((decodeGlueWord_eq_some_iff _ _ _ _).mp hdec).trans (encodeGlueWord_zero _ _))
  rw [(decodeGlueWord_eq_some_iff _ _ _ _).mp hdec, glueWordMinimum_encodeGlueWord]
  exact four_le_sum_glueMinimum_of_mem_glueSubgroup r hwmem hw0

/-- Every nonzero vector `v ∈ r.glueGeneratorVectors` has squared norm at least `4` in
`r.lattice`. -/
theorem four_le_form_self_of_mem_glueGeneratorVectors (r : RootfulNiemeierType)
    {v : ∀ i, Fin (r.componentType i).rank → ℚ} (hv : v ∈ r.glueGeneratorVectors)
    (hv0 : v ≠ 0) : 4 ≤ r.lattice.form v v := by
  obtain ⟨l, hl, rfl⟩ := r.mem_glueGeneratorVectors_iff.mp hv
  refine r.four_le_form_glueWordVector_self_of_mem_glueWords hl ?_
  rintro rfl
  exact hv0 (glueWordVector_replicate_zero r.componentType r.components.length)

/-- **Computable finite `ℤ`-generating set of `N_r`**: the union of the `24` simple-root vectors and
the shortest glue-generator vectors of the row. -/
def generatorVectors (r : RootfulNiemeierType) :
    Finset (∀ i, Fin (r.componentType i).rank → ℚ) :=
  r.simpleRootVectors ∪ r.glueGeneratorVectors

/-- `r.generatorVectors` is the union of `r.simpleRootVectors` and `r.glueGeneratorVectors`. -/
theorem generatorVectors_def (r : RootfulNiemeierType) :
    r.generatorVectors = r.simpleRootVectors ∪ r.glueGeneratorVectors :=
  (rfl)

/-- A vector belongs to `r.generatorVectors` if and only if it is a simple-root vector or a
glue-generator vector of `r`. -/
@[simp]
theorem mem_generatorVectors_iff {r : RootfulNiemeierType}
    {v : ∀ i, Fin (r.componentType i).rank → ℚ} :
    v ∈ r.generatorVectors ↔ v ∈ r.simpleRootVectors ∨ v ∈ r.glueGeneratorVectors := by
  rw [generatorVectors_def, Finset.mem_union]

/-- **The computable finite set `r.generatorVectors` spans `r.lattice.carrier` over `ℤ`.** -/
@[simp]
theorem span_generatorVectors (r : RootfulNiemeierType) :
    Submodule.span ℤ (r.generatorVectors : Set (∀ i, Fin (r.componentType i).rank → ℚ)) =
      r.lattice.carrier := by
  rw [generatorVectors_def, Finset.coe_union, Submodule.span_union,
    span_simpleRootVectors, ← lattice_carrier_eq_sup_span_glueGeneratorVectors]

/-- Every vector in `r.generatorVectors` lies in `r.lattice.carrier`. -/
theorem generatorVectors_subset_lattice_carrier (r : RootfulNiemeierType) :
    (r.generatorVectors : Set (∀ i, Fin (r.componentType i).rank → ℚ)) ⊆
      r.lattice.carrier := by
  rw [← r.span_generatorVectors]
  exact Submodule.subset_span

/-- `glueWordRepresentativeVector` of a glue word `w` belongs to `r.lattice.carrier` if and only if
`w ∈ r.glueSubgroup`. -/
@[simp]
theorem glueWordRepresentativeVector_mem_lattice_carrier_iff (r : RootfulNiemeierType)
    (w : r.glueModule) :
    DynkinType.glueWordRepresentativeVector r.componentType
        r.isSimplyLaced_componentType w ∈
      r.lattice.carrier ↔ w ∈ r.glueSubgroup := by
  rw [lattice_def]
  exact DynkinType.glueWordRepresentativeVector_mem_gluedLattice_carrier_iff
    r.componentType r.isSimplyLaced_componentType r.valid_componentType
    r.glueSubgroup r.isIsotropic_glueSubgroup w

/-- **Explicit coset decomposition of `N_r`**: a rational vector `x` belongs to `r.lattice.carrier`
if and only if it differs from `glueWordRepresentativeVector _ _ w`, for some glue word
`w ∈ r.glueSubgroup`, by a vector in `r.rootLattice.carrier`. -/
theorem mem_lattice_carrier_iff_exists_sub_mem (r : RootfulNiemeierType)
    (x : ∀ i, Fin (r.componentType i).rank → ℚ) :
    x ∈ r.lattice.carrier ↔
      ∃ w ∈ r.glueSubgroup,
        x - DynkinType.glueWordRepresentativeVector r.componentType
          r.isSimplyLaced_componentType w ∈ r.rootLattice.carrier := by
  rw [lattice_def]
  exact DynkinType.mem_gluedLattice_carrier_iff_exists_sub_mem r.componentType
    r.isSimplyLaced_componentType r.valid_componentType r.glueSubgroup
    r.isIsotropic_glueSubgroup x

/-- **Coordinatewise integer membership criterion for `N_r`**: a rational vector `x` belongs to
`r.lattice.carrier` if and only if there is a glue word `w ∈ r.glueSubgroup` such that every
simple-root coordinate `x i j` differs from the corresponding coordinate of
`glueRepresentativeVector` by an integer. -/
theorem mem_lattice_carrier_iff_exists_int (r : RootfulNiemeierType)
    (x : ∀ i, Fin (r.componentType i).rank → ℚ) :
    x ∈ r.lattice.carrier ↔
      ∃ w ∈ r.glueSubgroup, ∀ i j, ∃ z : ℤ,
        (z : ℚ) = x i j -
          (r.componentType i).glueRepresentativeVector
            (r.isSimplyLaced_componentType i) (w i) j := by
  rw [lattice_def]
  exact DynkinType.mem_gluedLattice_carrier_iff_exists_int r.componentType
    r.isSimplyLaced_componentType r.valid_componentType r.glueSubgroup
    r.isIsotropic_glueSubgroup x

end TauCeti.RootfulNiemeierType

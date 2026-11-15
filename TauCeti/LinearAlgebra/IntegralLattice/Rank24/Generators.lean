/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.IntegralLattice.Rank24.Niemeier
public import TauCeti.LinearAlgebra.IntegralLattice.RootLattice.GlueAlphabet.Representatives

/-!
# Computable rational generators and coset decompositions for glued rootful rank-24 lattices

`TauCeti.LinearAlgebra.IntegralLattice.Rank24.Niemeier` constructs each of the 23 rootful Niemeier
lattices `N_r = r.lattice` by gluing the orthogonal sum `R_r = r.rootLattice` of its ADE component
root lattices along its decoded Conway--Sloane glue subgroup `H_r = r.glueSubgroup`, and shows
existentially (`exists_lattice_carrier_eq_sup_span_glueMinimum`) that `N_r` is spanned by `R_r` and
a choice of shortest coset representatives of the glue generators.

Using the explicit shortest dual-lattice representatives of
`TauCeti.LinearAlgebra.IntegralLattice.RootLattice.GlueAlphabet.Representatives`, this file makes
both the simple-root generators and the shortest glue-word generators completely explicit and
computable in rational simple-root coordinates `∀ i, Fin (r.componentType i).rank → ℚ`, uniformly
for all 23 rows (and hence immediately for all 23 named abbreviations `niemeierD24`, …,
`niemeierA1TwentyFourth`):

* For any ordered family `t : Fin n → DynkinType`, `TauCeti.glueWordVector t l` maps a printed
  Conway--Sloane digit list `l : List ℕ` directly to its shortest dual-lattice representative
  `fun i ↦ (t i).glueLabelVector (l.getD i 0)`.  On encoded words it agrees with
  `TauCeti.DynkinType.glueWordRepresentativeVector`, and for every valid digit word its squared
  norm equals `TauCeti.glueWordMinimum t l` (`form_glueWordVector_self`).
* For any finite family `t : ι → DynkinType`, `TauCeti.DynkinType.piSimpleRootVectors t` is the
  computable `Finset` of standard simple-root vectors across all components, of cardinality
  `∑ i, (t i).rank` and `ℤ`-span equal to the orthogonal sum of root lattices
  (`span_piSimpleRootVectors`).
* For every row `r : TauCeti.RootfulNiemeierType`:
  - `r.simpleRootVectors` is the computable `Finset` of `24` norm-`2` simple-root vectors spanning
    `r.rootLattice.carrier`;
  - `r.glueGeneratorVectors` is the computable `Finset` of shortest rational glue vectors obtained
    by applying `glueWordVector` to `r.glueWords`, with
    `r.lattice.carrier = r.rootLattice.carrier ⊔ Submodule.span ℤ r.glueGeneratorVectors`;
  - `r.generatorVectors = r.simpleRootVectors ∪ r.glueGeneratorVectors` is a computable `Finset`
    whose `ℤ`-span is literally `r.lattice.carrier` (`span_generatorVectors`);
  - `mem_lattice_carrier_iff_exists_sub_mem` and `mem_lattice_carrier_iff_exists_int` characterize
    membership in `r.lattice.carrier` by explicit coset differences and coordinatewise integrality.

## References

* J. H. Conway and N. J. A. Sloane, *Sphere Packings, Lattices and Groups*, 3rd ed., Chapter 4
  §§6--8 and Chapter 16 §1, Table 16.1.
* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Plates I--VII.
-/

public section

namespace TauCeti

open IntegralLattice

/-! ### Explicit rational vectors of Conway--Sloane digit words -/

/-- **Computable shortest dual-lattice representative of a digit glue word** `l : List ℕ` for an
ordered family `t : Fin n → DynkinType`, in componentwise Bourbaki simple-root coordinates
`∀ i, Fin (t i).rank → ℚ`.  Missing coordinates default to digit `0` (hence the zero vector). -/
def glueWordVector {n : ℕ} (t : Fin n → DynkinType) (l : List ℕ) :
    ∀ i, Fin (t i).rank → ℚ :=
  fun i ↦ (t i).glueLabelVector (l.getD i 0)

theorem glueWordVector_def {n : ℕ} (t : Fin n → DynkinType) (l : List ℕ) :
    glueWordVector t l = fun i ↦ (t i).glueLabelVector (l.getD i 0) :=
  (rfl)

@[simp]
theorem glueWordVector_apply {n : ℕ} (t : Fin n → DynkinType) (l : List ℕ) (i : Fin n) :
    glueWordVector t l i = (t i).glueLabelVector (l.getD i 0) :=
  (rfl)

/-- The empty digit list maps to the zero vector. -/
@[simp]
theorem glueWordVector_nil {n : ℕ} (t : Fin n → DynkinType) :
    glueWordVector t [] = 0 := by
  funext i
  rw [glueWordVector_apply, List.getD_nil, DynkinType.glueLabelVector_zero, Pi.zero_apply]

/-- An all-zero digit list of any length maps to the zero vector. -/
@[simp]
theorem glueWordVector_replicate_zero {n : ℕ} (t : Fin n → DynkinType) (m : ℕ) :
    glueWordVector t (List.replicate m 0) = 0 := by
  funext i
  simp [List.getD_eq_getElem?_getD]

/-- On `List.ofFn d`, the `i`-th component of `glueWordVector` is `(t i).glueLabelVector (d i)`. -/
@[simp]
theorem glueWordVector_ofFn {n : ℕ} (t : Fin n → DynkinType) (d : Fin n → ℕ) :
    glueWordVector t (List.ofFn d) = fun i ↦ (t i).glueLabelVector (d i) := by
  funext i
  rw [glueWordVector_apply, List.getD_eq_getElem _ _ (by simp), List.getElem_ofFn]

/-- **Compatibility with `encodeGlueWord`**: evaluating `glueWordVector` on the digit list of a
glue word `w` recovers `DynkinType.glueWordRepresentativeVector t ht w`. -/
@[simp]
theorem glueWordVector_encodeGlueWord {n : ℕ} (t : Fin n → DynkinType)
    (ht : ∀ i, (t i).IsSimplyLaced) (w : ∀ i, (t i).glueAlphabet (ht i)) :
    glueWordVector t (encodeGlueWord t ht w) =
      DynkinType.glueWordRepresentativeVector t ht w := by
  funext i
  rw [glueWordVector_apply, List.getD_eq_getElem _ _ (by simp), getElem_encodeGlueWord,
    DynkinType.glueWordRepresentativeVector_apply, DynkinType.glueRepresentativeVector_def]

/-- If `l` decodes to `w`, then `glueWordVector t l` equals
`glueWordRepresentativeVector t ht w`. -/
theorem glueWordVector_eq_of_decodeGlueWord_eq_some {n : ℕ} (t : Fin n → DynkinType)
    (ht : ∀ i, (t i).IsSimplyLaced) {l : List ℕ} {w : ∀ i, (t i).glueAlphabet (ht i)}
    (hw : decodeGlueWord t ht l = some w) :
    glueWordVector t l = DynkinType.glueWordRepresentativeVector t ht w := by
  rw [(decodeGlueWord_eq_some_iff t ht l w).mp hw, glueWordVector_encodeGlueWord]

/-- Every `glueWordVector` lies in the dual carrier of the orthogonal sum of component root
lattices when all components are valid and simply laced. -/
theorem glueWordVector_mem_dualCarrier {n : ℕ} (t : Fin n → DynkinType)
    (hv : ∀ i, (t i).Valid) (ht : ∀ i, (t i).IsSimplyLaced) (l : List ℕ) :
    glueWordVector t l ∈ (pi fun i ↦ (t i).rootLattice (ht i)).dualCarrier :=
  (mem_dualCarrier_pi_iff _ _).mpr fun i ↦
    (t i).glueLabelVector_mem_dualCarrier (hv i) (ht i) (l.getD i 0)

/-- If `l` decodes to `w`, then `glueWordVector t l` represents the discriminant coset
`glueWordIsometry t ht hv w`. -/
theorem mk_glueWordVector_of_decodeGlueWord_eq_some {n : ℕ} (t : Fin n → DynkinType)
    (hv : ∀ i, (t i).Valid) (ht : ∀ i, (t i).IsSimplyLaced) {l : List ℕ}
    {w : ∀ i, (t i).glueAlphabet (ht i)} (hw : decodeGlueWord t ht l = some w) :
    (Submodule.Quotient.mk ⟨glueWordVector t l, glueWordVector_mem_dualCarrier t hv ht l⟩ :
        (pi fun i ↦ (t i).rootLattice (ht i)).DiscriminantGroup) =
      DynkinType.glueWordIsometry t ht hv w := by
  have heq : (⟨glueWordVector t l, glueWordVector_mem_dualCarrier t hv ht l⟩ :
        (pi fun i ↦ (t i).rootLattice (ht i)).dualCarrier) =
      DynkinType.glueWordRepresentative t ht hv w :=
    Subtype.ext ((glueWordVector_eq_of_decodeGlueWord_eq_some t ht hw).trans
      (DynkinType.coe_glueWordRepresentative t ht hv w).symm)
  rw [heq, DynkinType.mk_glueWordRepresentative]

/-- **Squared norm of `glueWordVector`**: for every valid digit word `l`, the squared norm of
`glueWordVector t l` equals `glueWordMinimum t l`, the shortest norm of the coset named by `l`. -/
theorem form_glueWordVector_self {n : ℕ} (t : Fin n → DynkinType)
    (hv : ∀ i, (t i).Valid) (ht : ∀ i, (t i).IsSimplyLaced) {l : List ℕ}
    (hl : IsValidGlueWord t l) :
    (pi fun i ↦ (t i).rootLattice (ht i)).form (glueWordVector t l) (glueWordVector t l) =
      glueWordMinimum t l := by
  obtain ⟨w, hw⟩ := Option.isSome_iff_exists.mp ((decodeGlueWord_isSome_iff t ht l).mpr hl)
  rw [glueWordVector_eq_of_decodeGlueWord_eq_some t ht hw,
    DynkinType.form_glueWordRepresentativeVector_self t ht hv w,
    (decodeGlueWord_eq_some_iff t ht l w).mp hw, glueWordMinimum_encodeGlueWord]

/-! ### Computable simple-root generators of an orthogonal sum of ADE root lattices -/

namespace DynkinType

section SimpleRootVectors

variable {ι : Type*} [DecidableEq ι] (t : ι → DynkinType)

/-- The `(i, j)`-th simple-root vector of an orthogonal sum of component root lattices, supported
in component `i` as the `j`-th Bourbaki simple root `Pi.single j 1`. -/
def piSimpleRootVector (p : Σ i, Fin (t i).rank) : ∀ i, Fin (t i).rank → ℚ :=
  Pi.single p.1 (Pi.single p.2 1)

theorem piSimpleRootVector_def (p : Σ i, Fin (t i).rank) :
    piSimpleRootVector t p = Pi.single p.1 (Pi.single p.2 1) :=
  (rfl)

@[simp]
theorem piSimpleRootVector_apply (p : Σ i, Fin (t i).rank) (i : ι) :
    piSimpleRootVector t p i =
      Pi.single (M := fun i ↦ Fin (t i).rank → ℚ) p.1 (Pi.single p.2 1) i :=
  (rfl)

/-- Distinct `(component, simple-root)` indices produce distinct simple-root vectors. -/
theorem piSimpleRootVector_injective : Function.Injective (piSimpleRootVector t) := by
  rintro ⟨i₁, j₁⟩ ⟨i₂, j₂⟩ h
  have hval := congrArg (fun f : ∀ i, Fin (t i).rank → ℚ ↦ f i₁ j₁) h
  simp only [piSimpleRootVector_apply] at hval
  by_cases hi : i₁ = i₂
  · subst hi
    simp only [Pi.single_eq_same] at hval
    by_cases hj : j₁ = j₂
    · subst hj; rfl
    · rw [Pi.single_eq_of_ne hj] at hval
      exact absurd hval one_ne_zero
  · rw [Pi.single_eq_same, Pi.single_eq_same, Pi.single_eq_of_ne hi,
      Pi.zero_apply] at hval
    exact absurd hval one_ne_zero

variable [Fintype ι]

/-- Every `piSimpleRootVector` lies in the carrier of the orthogonal sum of root lattices. -/
theorem piSimpleRootVector_mem_carrier (ht : ∀ i, (t i).IsSimplyLaced)
    (p : Σ i, Fin (t i).rank) :
    piSimpleRootVector t p ∈ (pi fun i ↦ (t i).rootLattice (ht i)).carrier := by
  rw [piSimpleRootVector_def]
  refine single_mem_pi_carrier (fun i ↦ (t i).rootLattice (ht i)) p.1 ?_
  rw [← coe_simpleRootBasis (t p.1) (ht p.1) p.2]
  exact ((t p.1).simpleRootBasis (ht p.1) p.2).2

/-- Every `piSimpleRootVector` has squared norm `2`. -/
theorem form_piSimpleRootVector_self (ht : ∀ i, (t i).IsSimplyLaced)
    (p : Σ i, Fin (t i).rank) :
    (pi fun i ↦ (t i).rootLattice (ht i)).form
        (piSimpleRootVector t p) (piSimpleRootVector t p) = 2 := by
  rw [piSimpleRootVector_def, pi_form, piForm_single_left, Pi.single_eq_same,
    rootLattice_form_single_single, cartanMatrix_apply_same]
  norm_num

/-- **Computable finite set of simple-root vectors** of an orthogonal sum of ADE root lattices. -/
def piSimpleRootVectors : Finset (∀ i, Fin (t i).rank → ℚ) :=
  Finset.univ.image (piSimpleRootVector t)

theorem piSimpleRootVectors_def :
    piSimpleRootVectors t = Finset.univ.image (piSimpleRootVector t) :=
  (rfl)

/-- The number of simple-root vectors is the total rank `∑ i, (t i).rank`. -/
@[simp]
theorem card_piSimpleRootVectors :
    (piSimpleRootVectors t).card = ∑ i, (t i).rank := by
  rw [piSimpleRootVectors_def, Finset.card_image_of_injective _ (piSimpleRootVector_injective t),
    Finset.card_univ, Fintype.card_sigma]
  simp

/-- Every vector in `piSimpleRootVectors` belongs to the orthogonal sum of root lattices. -/
theorem piSimpleRootVectors_subset_carrier (ht : ∀ i, (t i).IsSimplyLaced) :
    (piSimpleRootVectors t : Set (∀ i, Fin (t i).rank → ℚ)) ⊆
      (pi fun i ↦ (t i).rootLattice (ht i)).carrier := by
  rw [piSimpleRootVectors_def, Finset.coe_image]
  rintro _ ⟨p, -, rfl⟩
  exact piSimpleRootVector_mem_carrier t ht p

/-- **The `ℤ`-span of `piSimpleRootVectors` is the carrier of the orthogonal sum of root
lattices.** -/
@[simp]
theorem span_piSimpleRootVectors (ht : ∀ i, (t i).IsSimplyLaced) :
    Submodule.span ℤ (piSimpleRootVectors t : Set (∀ i, Fin (t i).rank → ℚ)) =
      (pi fun i ↦ (t i).rootLattice (ht i)).carrier := by
  refine le_antisymm (Submodule.span_le.mpr (piSimpleRootVectors_subset_carrier t ht)) ?_
  intro x hx
  choose z hz using fun i ↦ ((t i).mem_rootLattice_carrier_iff (ht i) (x i)).mp
    ((mem_pi_carrier_iff _ x).mp hx i)
  have hx_eq : x = ∑ i : ι, ∑ j : Fin (t i).rank, z i j • piSimpleRootVector t ⟨i, j⟩ := by
    ext i₀ j₀
    simp only [Finset.sum_apply, Pi.smul_apply, piSimpleRootVector_apply]
    rw [Finset.sum_eq_single i₀
      (fun i _ hi ↦ Finset.sum_eq_zero fun j _ ↦ by
        rw [Pi.single_eq_of_ne hi.symm, Pi.zero_apply, smul_zero])
      (fun hi₀ ↦ absurd (Finset.mem_univ i₀) hi₀)]
    rw [Finset.sum_eq_single j₀
      (fun j _ hj ↦ by rw [Pi.single_eq_same, Pi.single_eq_of_ne hj.symm, smul_zero])
      (fun hj₀ ↦ absurd (Finset.mem_univ j₀) hj₀)]
    rw [Pi.single_eq_same, Pi.single_eq_same, zsmul_one, hz i₀ j₀]
  rw [hx_eq]
  refine Submodule.sum_mem _ fun i _ ↦ Submodule.sum_mem _ fun j _ ↦
    Submodule.smul_mem _ (z i j) (Submodule.subset_span ?_)
  exact Finset.mem_coe.mpr
    (Finset.mem_image_of_mem _ (Finset.mem_univ (⟨i, j⟩ : Σ k, Fin (t k).rank)))

end SimpleRootVectors

end DynkinType

/-! ### Computable rational generators and coset decompositions of the 23 Niemeier table lattices -/

namespace RootfulNiemeierType

/-- **Computable finite set of simple-root vectors** of a row `r`, in componentwise Bourbaki
simple-root coordinates `∀ i, Fin (r.componentType i).rank → ℚ`. -/
def simpleRootVectors (r : RootfulNiemeierType) :
    Finset (∀ i, Fin (r.componentType i).rank → ℚ) :=
  DynkinType.piSimpleRootVectors r.componentType

theorem simpleRootVectors_def (r : RootfulNiemeierType) :
    r.simpleRootVectors = DynkinType.piSimpleRootVectors r.componentType :=
  (rfl)

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
  rw [simpleRootVectors_def, DynkinType.piSimpleRootVectors_def, Finset.mem_image] at hv
  obtain ⟨p, -, rfl⟩ := hv
  rw [r.lattice_form]
  exact DynkinType.form_piSimpleRootVector_self r.componentType r.isSimplyLaced_componentType p

/-- **The `24` simple-root vectors of `r` span `r.rootLattice.carrier` over `ℤ`.** -/
@[simp]
theorem span_simpleRootVectors (r : RootfulNiemeierType) :
    Submodule.span ℤ (r.simpleRootVectors : Set (∀ i, Fin (r.componentType i).rank → ℚ)) =
      r.rootLattice.carrier :=
  DynkinType.span_piSimpleRootVectors r.componentType r.isSimplyLaced_componentType

/-- **Computable finite set of shortest glue-generator vectors** of a row `r`, obtained directly
from the printed Conway--Sloane digit words `r.glueWords` via `glueWordVector`. -/
def glueGeneratorVectors (r : RootfulNiemeierType) :
    Finset (∀ i, Fin (r.componentType i).rank → ℚ) :=
  r.glueWords.image (glueWordVector r.componentType)

theorem glueGeneratorVectors_def (r : RootfulNiemeierType) :
    r.glueGeneratorVectors = r.glueWords.image (glueWordVector r.componentType) :=
  (rfl)

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

/-- For every printed glue word `l ∈ r.glueWords`, its rational vector `glueWordVector
r.componentType l` has squared norm `glueWordMinimum r.componentType l` in `r.lattice`. -/
theorem form_glueWordVector_self_of_mem_glueWords (r : RootfulNiemeierType) {l : List ℕ}
    (hl : l ∈ r.glueWords) :
    r.lattice.form (glueWordVector r.componentType l) (glueWordVector r.componentType l) =
      glueWordMinimum r.componentType l := by
  rw [r.lattice_form]
  exact form_glueWordVector_self r.componentType r.valid_componentType
    r.isSimplyLaced_componentType (isValidGlueWord_of_mem_glueWords hl)

/-- Every non-zero printed glue word `l ∈ r.glueWords` yields a glue-generator vector of squared
norm at least `4`. -/
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

/-- **Computable finite `ℤ`-generating set of `N_r`**: the union of the `24` simple-root vectors and
the shortest glue-generator vectors of the row. -/
def generatorVectors (r : RootfulNiemeierType) :
    Finset (∀ i, Fin (r.componentType i).rank → ℚ) :=
  r.simpleRootVectors ∪ r.glueGeneratorVectors

theorem generatorVectors_def (r : RootfulNiemeierType) :
    r.generatorVectors = r.simpleRootVectors ∪ r.glueGeneratorVectors :=
  (rfl)

/-- **The computable finite set `r.generatorVectors` spans `r.lattice.carrier` over `ℤ`.** -/
@[simp]
theorem span_generatorVectors (r : RootfulNiemeierType) :
    Submodule.span ℤ (r.generatorVectors : Set (∀ i, Fin (r.componentType i).rank → ℚ)) =
      r.lattice.carrier := by
  rw [generatorVectors_def, Finset.coe_union, Submodule.span_union,
    span_simpleRootVectors, ← lattice_carrier_eq_sup_span_glueGeneratorVectors]

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

end RootfulNiemeierType

end TauCeti

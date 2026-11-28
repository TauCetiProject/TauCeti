/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Monoid
public import Mathlib.Topology.Instances.Matrix
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Block.Triangular
public import TauCeti.LinearAlgebra.Matrix.IndefiniteUnitaryGroup.Graded.Basic
public import TauCeti.LinearAlgebra.Matrix.UnitaryGroup.Block

/-!
# The unipotent group of the grades, the Bessel group and its projection to `U(X)`

Let `R` be a commutative ring with an involution and `J = TauCeti.gradedGram X s N` the graded
Gram matrix on `X ⊕ Fin s`, whose basis vectors carry the grades `TauCeti.gradedGrade X s`
(`0` on `X` and `s - 1 - 2a` on the string vector `e_a`). Write `G` for the unitary group
`Matrix.unitaryGroupOf J`, the invertible `g` with `gᴴ J g = J`. Inside `G` this file defines:

* the **unipotent group of the grades** `U = TauCeti.gradedUnipotent X s N`, the `g ∈ G` for which
  `g - 1` raises the grade by at least one, that is `g i j = δ i j` whenever
  `grade i ≤ grade j` (`TauCeti.mem_gradedUnipotent_iff`,
  `TauCeti.mem_gradedUnipotent_iff_raisesDegree`);
* the **Bessel group** `TauCeti.gradedBesselGroup X s N`, the `g ∈ G` that agree with the
  identity at the entries `(i, e_b)` with `0 ≤ grade e_b` and `grade i ≤ grade e_b`; it contains
  `U` (`TauCeti.gradedUnipotent_le_gradedBesselGroup`) and the copy of the unitary group `U(X)`
  embedded as the `X`-block by `TauCeti.gradedInclusion X s N`;
* the **degree filtration** `TauCeti.gradedUnipotentFiltration X s N d` of `U`, the `g ∈ U` for
  which `g - 1` raises the grade by at least `d`. It is decreasing, equal to `U` for `d ≤ 1`, and
  its terms are subgroups preserved by conjugation by every isometry raising the grade by at least
  `0`, such as the image of `U(X)`. For a string of odd length all grades are even, so that
  `U^{≥2} = U` (`TauCeti.gradedUnipotentFiltration_two`). The group `U^{≥2}` is the domain of the
  unipotent character of a graded hermitian form.

The `X`-block of an element of the Bessel group is unitary, and taking it is a homomorphism
`TauCeti.gradedBesselProj X s N` onto `U(X)`, continuous for any topology on `R`, which is the
identity on `U(X)`. The main result is that, when `N` is not a zero divisor, its kernel is `U`
(`TauCeti.ker_gradedBesselProj`), so that the Bessel group is the semidirect product of `U` and
`U(X)`: every element of the Bessel group is `u * a` with `u ∈ U` and `a` in the image of `U(X)`,
and `U` meets that image only in `1`. For `s = 1`, `N = 0` and one-point `X`, the matrix with rows
`(1, 0)` and `(1, 1)` lies in the Bessel group, has `X`-block `1`, and is not in `U`.

The proofs rest on facts about the columns of an element `g` of the Bessel group, read off
`gᴴ J g = J` by induction along the string, since `J` pairs only opposite grades: the columns
indexed by `X` have no component on the string in negative grade
(`TauCeti.apply_inr_inl_eq_zero_of_mem_gradedBesselGroup`), their component along the middle vector
of an odd string is killed by its norm `-N`
(`TauCeti.star_apply_inr_inl_mul_gradedGram_eq_zero_of_mem_gradedBesselGroup`), and the columns of
negative grade agree with the identity in all grades up to their own, as the columns of grade
`≥ 0` do by definition (`TauCeti.apply_inr_inr_eq_one_apply_of_mem_gradedBesselGroup`).

For a string of odd length, `U` is the unipotent Bessel group `TauCeti.besselU` of the split form,
read through the reordering `TauCeti.gradedSplitEquiv`
(`TauCeti.mem_gradedUnipotent_iff_blockUnitriangular_reindex`). All objects are defined over any
commutative ring with involution, so that for a hermitian space over a CM field `E` graded by `J`
they give the subgroups of its points over any `E`-algebra with involution, such as the adeles.

## Main definitions

* `TauCeti.gradedUnipotent X s N`: the unipotent group `U` of the flag of the grades.
* `TauCeti.gradedUnipotentFiltration X s N d`: its degree filtration.
* `TauCeti.gradedBesselGroup X s N`: the Bessel group.
* `TauCeti.gradedInclusion X s N`: the embedding of `U(X)` as the `X`-block.
* `TauCeti.gradedBesselInclusion X s N`: the same embedding into the Bessel group.
* `TauCeti.gradedBesselProj X s N`: the projection of the Bessel group onto `U(X)`.

## Main results

* `TauCeti.toBlocks₁₁_mem_unitaryGroup_of_mem_gradedBesselGroup`: the `X`-block of an element of
  the Bessel group is unitary.
* `TauCeti.gradedBesselProj_gradedBesselInclusion`: the projection is the identity on `U(X)`.
* `TauCeti.gradedBesselProj_surjective`: the projection is surjective.
* `TauCeti.ker_gradedBesselProj`: its kernel is `U`, when `N` is not a zero divisor.
* `TauCeti.exists_mem_gradedUnipotent_mul_gradedInclusion`: every element of the Bessel group is
  `u * a` with `u ∈ U` and `a ∈ U(X)`, when `N` is not a zero divisor; the decomposition is unique
  since `U` meets `U(X)` only in `1` (`TauCeti.gradedInclusion_mem_gradedUnipotent_iff`).
* `TauCeti.continuous_gradedBesselProj`: the projection is continuous.
* `TauCeti.mem_gradedUnipotent_iff_blockUnitriangular_reindex`: the comparison with `besselU`.
* `TauCeti.gradedUnipotentFiltration_two`: for a string of odd length, `U^{≥2} = U`.
* `TauCeti.mul_mul_inv_mem_gradedUnipotentFiltration`,
  `TauCeti.gradedInclusion_mul_mul_inv_mem_gradedUnipotentFiltration`: conjugation by isometries
  raising the grade by at least `0`, and by `U(X)`, preserves the filtration.

## References

* `grh-lean`, https://github.com/lsernau/grh-lean, file `src/Lib/Weil/Periods/Grading.lean`
  (declarations `New.Grading.unipotent`, `New.Grading.besselGroup`, `New.Grading.inclX`,
  `New.Grading.besselProj`, `New.Grading.exists_besselGroup_proj`,
  `New.Grading.exists_unipotent_mul_inclX`, `New.Grading.hasDegreeGe_two_of_odd`) and file
  `src/Lib/Weil/Periods/Equivariant.lean` (`New.Grading.hasDegreeGe_conj`); Apache 2.0, Copyright
  2026 Anthropic, PBC. The groups and the statements about the projection follow these
  declarations; the degree filtration as a family of subgroups is new here.
* W. T. Gan, B. H. Gross and D. Prasad, *Symplectic local root numbers, central critical
  L-values, and restriction problems in the representation theory of classical groups*,
  Astérisque 346 (2012), Section 12, for Bessel subgroups as semidirect products of a unipotent
  group and a smaller unitary group.
-/

public section

open Matrix

namespace TauCeti

variable {R : Type*} [CommRing R] [StarRing R] {X : Type*} [Fintype X] [DecidableEq X] {s : ℕ}
  {N : R}

/-! ### The unipotent group of the grades -/

variable (X s N) in
/-- The **unipotent group of the grades**: the isometries `g` of the graded Gram matrix for which
`g - 1` raises the grade by at least one, that is the block upper unitriangular matrices when the
grades are ordered decreasingly. -/
def gradedUnipotent : Subgroup (unitaryGroupOf (gradedGram X s N)) :=
  (unitriangularSubgroup (OrderDual.toDual ∘ gradedGrade X s) R).subgroupOf _

/-- An isometry `g` of the graded Gram matrix lies in the unipotent group of the grades exactly
when its entry `g i j` is that of the identity whenever `grade i ≤ grade j`. -/
@[simp]
theorem mem_gradedUnipotent_iff {g : unitaryGroupOf (gradedGram X s N)} :
    g ∈ gradedUnipotent X s N ↔ ∀ i j, gradedGrade X s i ≤ gradedGrade X s j →
      ((g : GL (X ⊕ Fin s) R) : Matrix (X ⊕ Fin s) (X ⊕ Fin s) R) i j =
        (1 : Matrix (X ⊕ Fin s) (X ⊕ Fin s) R) i j := by
  simp only [gradedUnipotent, Subgroup.mem_subgroupOf, mem_unitriangularSubgroup,
    blockUnitriangular_iff, BlockTriangular, Function.comp_apply, OrderDual.toDual_lt_toDual,
    OrderDual.toDual_inj]
  refine ⟨fun ⟨h₁, h₂⟩ i j hij ↦ hij.lt_or_eq.elim (fun h ↦ ?_) fun h ↦ h₂ h, fun h ↦
    ⟨fun i j hij ↦ ?_, fun i j hij ↦ h i j hij.le⟩⟩
  · rw [h₁ h, one_apply_ne (by rintro rfl; exact h.false)]
  · rw [h i j hij.le, one_apply_ne (by rintro rfl; exact hij.false)]

/-- An isometry `g` of the graded Gram matrix lies in the unipotent group of the grades exactly
when `g - 1` raises the grade by at least one. -/
theorem mem_gradedUnipotent_iff_raisesDegree {g : unitaryGroupOf (gradedGram X s N)} :
    g ∈ gradedUnipotent X s N ↔ RaisesDegree (gradedGrade X s) 1
      (((g : GL (X ⊕ Fin s) R) : Matrix (X ⊕ Fin s) (X ⊕ Fin s) R) - 1) := by
  rw [mem_gradedUnipotent_iff, raisesDegree_iff]
  refine forall₂_congr fun i j ↦ ?_
  rw [Matrix.sub_apply, sub_ne_zero, Int.add_one_le_iff, ← not_le, not_imp_not]

/-- For a string of odd length `2ϱ + 1`, the unipotent group of the grades is the unipotent Bessel
group `TauCeti.besselU` of the split form, read through the reordering `gradedSplitEquiv X ϱ`
(which carries the graded Gram matrix to `splitGram ϱ (middleGram N)`, `reindex_gradedGram`): an
isometry lies in it exactly when its reordered matrix is block upper unitriangular for the
levels. -/
theorem mem_gradedUnipotent_iff_blockUnitriangular_reindex {ϱ : ℕ}
    {g : unitaryGroupOf (gradedGram X (2 * ϱ + 1) N)} :
    g ∈ gradedUnipotent X (2 * ϱ + 1) N ↔
      (reindex (gradedSplitEquiv X ϱ) (gradedSplitEquiv X ϱ)
        ((g : GL (X ⊕ Fin (2 * ϱ + 1)) R) : Matrix _ _ R)).BlockUnitriangular splitLevel := by
  have hone (k l : X ⊕ Fin (2 * ϱ + 1)) :
      (1 : Matrix (SplitIndex ϱ (X ⊕ Unit)) (SplitIndex ϱ (X ⊕ Unit)) R)
        (gradedSplitEquiv X ϱ k) (gradedSplitEquiv X ϱ l) =
        (1 : Matrix (X ⊕ Fin (2 * ϱ + 1)) (X ⊕ Fin (2 * ϱ + 1)) R) k l := by
    simp [Matrix.one_apply]
  rw [mem_gradedUnipotent_iff]
  refine ⟨fun h ↦ blockUnitriangular_of_apply_eq_one_apply_of_not_lt fun i j hij ↦ ?_,
    fun h k l hkl ↦ ?_⟩
  · obtain ⟨k, rfl⟩ := (gradedSplitEquiv X ϱ).surjective i
    obtain ⟨l, rfl⟩ := (gradedSplitEquiv X ϱ).surjective j
    have := two_mul_splitLevel_gradedSplitEquiv ϱ k
    have := two_mul_splitLevel_gradedSplitEquiv ϱ l
    simpa only [reindex_apply, submatrix_apply, Equiv.symm_apply_apply, hone] using
      h _ _ (by omega)
  · have := two_mul_splitLevel_gradedSplitEquiv ϱ k
    have := two_mul_splitLevel_gradedSplitEquiv ϱ l
    rcases (show splitLevel (gradedSplitEquiv X ϱ l) ≤ splitLevel (gradedSplitEquiv X ϱ k) by
      omega).lt_or_eq with hlt | heq
    · have h0 := h.blockTriangular hlt
      simp only [reindex_apply, submatrix_apply, Equiv.symm_apply_apply] at h0
      rw [h0, one_apply_ne (by rintro rfl; exact hlt.false)]
    · have h1 := h.apply_of_eq heq.symm
      simpa only [reindex_apply, submatrix_apply, Equiv.symm_apply_apply, hone] using h1

/-! ### The degree filtration of the unipotent group -/

variable (X s N) in
/-- The **`d`-th term of the degree filtration** of the unipotent group of the grades: the
isometries `g` of the graded Gram matrix for which `g - 1` raises the grade by at least `max d 1`.
It is the unipotent group of the grades for `d ≤ 1` and decreases with `d`. -/
def gradedUnipotentFiltration (d : ℤ) : Subgroup (unitaryGroupOf (gradedGram X s N)) where
  carrier := {g | RaisesDegree (gradedGrade X s) (max d 1)
    (((g : GL (X ⊕ Fin s) R) : Matrix (X ⊕ Fin s) (X ⊕ Fin s) R) - 1)}
  one_mem' := by simp
  mul_mem' {g h} hg hh := by
    simpa using RaisesDegree.mul_sub_one hg hh (by omega)
  inv_mem' {g} hg := by
    -- `g⁻¹ - 1 = -(g⁻¹ (g - 1))`, and `g⁻¹` raises the grade by at least `0`, as `g` does.
    have hinv : RaisesDegree (gradedGrade X s) 0
        (((g⁻¹ : unitaryGroupOf (gradedGram X s N)) : GL (X ⊕ Fin s) R) :
          Matrix (X ⊕ Fin s) (X ⊕ Fin s) R) := by
      simpa [Matrix.coe_units_inv] using (RaisesDegree.of_sub_one (hg.mono (by omega))).inv
    have h : (((g⁻¹ : unitaryGroupOf (gradedGram X s N)) : GL (X ⊕ Fin s) R) :
          Matrix (X ⊕ Fin s) (X ⊕ Fin s) R) - 1 =
        -((((g⁻¹ : unitaryGroupOf (gradedGram X s N)) : GL (X ⊕ Fin s) R) :
          Matrix (X ⊕ Fin s) (X ⊕ Fin s) R) *
            (((g : GL (X ⊕ Fin s) R) : Matrix (X ⊕ Fin s) (X ⊕ Fin s) R) - 1)) := by
      simp [Matrix.mul_sub]
    rw [Set.mem_ofPred_eq, h]
    simpa using (hinv.mul hg).neg

/-- An isometry `g` of the graded Gram matrix lies in the `d`-th term of the degree filtration
exactly when `g - 1` raises the grade by at least `max d 1`. -/
theorem mem_gradedUnipotentFiltration_iff_raisesDegree {d : ℤ}
    {g : unitaryGroupOf (gradedGram X s N)} :
    g ∈ gradedUnipotentFiltration X s N d ↔ RaisesDegree (gradedGrade X s) (max d 1)
      (((g : GL (X ⊕ Fin s) R) : Matrix (X ⊕ Fin s) (X ⊕ Fin s) R) - 1) :=
  Iff.rfl

/-- An isometry `g` of the graded Gram matrix lies in the `d`-th term of the degree filtration
exactly when it lies in the unipotent group of the grades and `g - 1` raises the grade by at
least `d`. -/
theorem mem_gradedUnipotentFiltration_iff {d : ℤ} {g : unitaryGroupOf (gradedGram X s N)} :
    g ∈ gradedUnipotentFiltration X s N d ↔ g ∈ gradedUnipotent X s N ∧
      RaisesDegree (gradedGrade X s) d
        (((g : GL (X ⊕ Fin s) R) : Matrix (X ⊕ Fin s) (X ⊕ Fin s) R) - 1) := by
  rw [mem_gradedUnipotentFiltration_iff_raisesDegree, raisesDegree_max_iff,
    mem_gradedUnipotent_iff_raisesDegree, and_comm]

/-- Every term of the degree filtration lies in the unipotent group of the grades. -/
theorem gradedUnipotentFiltration_le_gradedUnipotent (d : ℤ) :
    gradedUnipotentFiltration X s N d ≤ gradedUnipotent X s N :=
  fun _ hg ↦ (mem_gradedUnipotentFiltration_iff.1 hg).1

/-- For `d ≤ 1` the `d`-th term of the degree filtration is the unipotent group of the grades. -/
theorem gradedUnipotentFiltration_eq_gradedUnipotent {d : ℤ} (hd : d ≤ 1) :
    gradedUnipotentFiltration X s N d = gradedUnipotent X s N := by
  ext g
  rw [mem_gradedUnipotentFiltration_iff, and_iff_left_iff_imp]
  exact fun hg ↦ (mem_gradedUnipotent_iff_raisesDegree.1 hg).mono hd

/-- The degree filtration is decreasing. -/
theorem gradedUnipotentFiltration_antitone :
    Antitone (gradedUnipotentFiltration (R := R) X s N) := fun _ _ hd _ hg ↦
  mem_gradedUnipotentFiltration_iff.2
    ⟨(mem_gradedUnipotentFiltration_iff.1 hg).1, (mem_gradedUnipotentFiltration_iff.1 hg).2.mono hd⟩

/-- For a string of odd length all grades are even, so the degree filtration only jumps at even
degrees: its terms of degree `2k - 1` and `2k` agree. -/
theorem gradedUnipotentFiltration_two_mul (hs : Odd s) (k : ℤ) :
    gradedUnipotentFiltration X s N (2 * k) = gradedUnipotentFiltration X s N (2 * k - 1) := by
  refine le_antisymm (gradedUnipotentFiltration_antitone (by omega)) fun g hg ↦ ?_
  rw [mem_gradedUnipotentFiltration_iff] at hg ⊢
  refine ⟨hg.1, raisesDegree_iff.2 fun i j hij ↦ ?_⟩
  obtain ⟨a, ha⟩ := even_gradedGrade hs i
  obtain ⟨b, hb⟩ := even_gradedGrade hs j
  have := raisesDegree_iff.1 hg.2 i j hij
  omega

/-- For a string of odd length the unipotent group of the grades is the second term of its degree
filtration: for every element `g`, the matrix `g - 1` raises the grade by at least two. -/
theorem gradedUnipotentFiltration_two (hs : Odd s) :
    gradedUnipotentFiltration X s N 2 = gradedUnipotent X s N := by
  simpa using (gradedUnipotentFiltration_two_mul (N := N) hs 1).trans
    (gradedUnipotentFiltration_eq_gradedUnipotent le_rfl)

/-- Conjugation by an isometry `r` raising the grade by at least `0` preserves each term of the
degree filtration. -/
theorem mul_mul_inv_mem_gradedUnipotentFiltration {d : ℤ}
    {r g : unitaryGroupOf (gradedGram X s N)}
    (hr : RaisesDegree (gradedGrade X s) 0
      (((r : GL (X ⊕ Fin s) R) : Matrix (X ⊕ Fin s) (X ⊕ Fin s) R)))
    (hg : g ∈ gradedUnipotentFiltration X s N d) :
    r * g * r⁻¹ ∈ gradedUnipotentFiltration X s N d := by
  have hr' : RaisesDegree (gradedGrade X s) 0
      (((r⁻¹ : unitaryGroupOf (gradedGram X s N)) : GL (X ⊕ Fin s) R) :
        Matrix (X ⊕ Fin s) (X ⊕ Fin s) R) := by
    simpa [Matrix.coe_units_inv] using hr.inv
  have h : (((r * g * r⁻¹ : unitaryGroupOf (gradedGram X s N)) : GL (X ⊕ Fin s) R) :
      Matrix (X ⊕ Fin s) (X ⊕ Fin s) R) - 1 =
      ((r : GL (X ⊕ Fin s) R) : Matrix (X ⊕ Fin s) (X ⊕ Fin s) R) *
        (((g : GL (X ⊕ Fin s) R) : Matrix (X ⊕ Fin s) (X ⊕ Fin s) R) - 1) *
        (((r⁻¹ : unitaryGroupOf (gradedGram X s N)) : GL (X ⊕ Fin s) R) :
          Matrix (X ⊕ Fin s) (X ⊕ Fin s) R) := by
    simp [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc]
  rw [mem_gradedUnipotentFiltration_iff_raisesDegree, h]
  simpa using (hr.mul (mem_gradedUnipotentFiltration_iff_raisesDegree.1 hg)).mul hr'

/-! ### The Bessel group -/

/-- The entries `(i, k)` at which elements of the Bessel group agree with the identity: `k` is on
the string, of grade `≥ 0`, and `grade i ≤ grade k`. -/
private def gradedBesselRel (X : Type*) (s : ℕ) (i k : X ⊕ Fin s) : Prop :=
  k.isRight ∧ 0 ≤ gradedGrade X s k ∧ gradedGrade X s i ≤ gradedGrade X s k

omit [Fintype X] [DecidableEq X] in
private theorem gradedBesselRel_split (i k j : X ⊕ Fin s) :
    gradedBesselRel X s i j → gradedBesselRel X s i k ∨ gradedBesselRel X s k j := by
  rintro ⟨hj, hj0, hij⟩
  rcases le_or_gt (gradedGrade X s k) (gradedGrade X s j) with hkj | hjk
  · exact .inr ⟨hj, hj0, hkj⟩
  · refine .inl ⟨?_, by omega, by omega⟩
    rcases k with x | b
    · rw [gradedGrade_inl] at hjk; omega
    · rfl

variable (X s N) in
/-- The **Bessel group** of the graded Gram matrix: the isometries `g` that agree with the
identity at every entry `(i, e_b)` with `e_b` on the string, `0 ≤ grade e_b` and
`grade i ≤ grade e_b`. -/
def gradedBesselGroup : Subgroup (unitaryGroupOf (gradedGram X s N)) :=
  (agreeWithOneOn (gradedBesselRel X s) R gradedBesselRel_split).subgroupOf _

/-- An isometry `g` of the graded Gram matrix lies in the Bessel group exactly when
`g i e_b = δ i e_b` whenever `0 ≤ grade e_b` and `grade i ≤ grade e_b`. -/
@[simp]
theorem mem_gradedBesselGroup_iff {g : unitaryGroupOf (gradedGram X s N)} :
    g ∈ gradedBesselGroup X s N ↔ ∀ i (b : Fin s), 0 ≤ gradedGrade X s (.inr b) →
      gradedGrade X s i ≤ gradedGrade X s (.inr b) →
      ((g : GL (X ⊕ Fin s) R) : Matrix (X ⊕ Fin s) (X ⊕ Fin s) R) i (.inr b) =
        (1 : Matrix (X ⊕ Fin s) (X ⊕ Fin s) R) i (.inr b) := by
  simp only [gradedBesselGroup, Subgroup.mem_subgroupOf, mem_agreeWithOneOn, gradedBesselRel]
  refine ⟨fun h i b hb hib ↦ h i _ ⟨rfl, hb, hib⟩, fun h i k ⟨hk, hk0, hik⟩ ↦ ?_⟩
  obtain ⟨b, rfl⟩ := Sum.isRight_iff.mp hk
  exact h i b hk0 hik

/-- The graded Bessel subgroup is closed: its prescribed matrix entries are closed conditions. -/
theorem isClosed_gradedBesselGroup [TopologicalSpace R] [T2Space R] :
    IsClosed (gradedBesselGroup X s N : Set (unitaryGroupOf (gradedGram X s N))) := by
  have hset : (gradedBesselGroup X s N : Set (unitaryGroupOf (gradedGram X s N))) =
    {g : unitaryGroupOf (gradedGram X s N) | ∀ i (b : Fin s),
      0 ≤ gradedGrade X s (.inr b) → gradedGrade X s i ≤ gradedGrade X s (.inr b) →
      ((g : GL (X ⊕ Fin s) R) : Matrix (X ⊕ Fin s) (X ⊕ Fin s) R) i (.inr b) =
        (1 : Matrix (X ⊕ Fin s) (X ⊕ Fin s) R) i (.inr b)} :=
    Set.ext fun _ ↦ mem_gradedBesselGroup_iff
  rw [hset]
  simp only [Set.ofPred_forall]
  refine isClosed_iInter fun i ↦ isClosed_iInter fun b ↦
    isClosed_iInter fun _ ↦ isClosed_iInter fun _ ↦ ?_
  have hval : Continuous (fun g : unitaryGroupOf (gradedGram X s N) ↦
      ((g : GL (X ⊕ Fin s) R) : Matrix (X ⊕ Fin s) (X ⊕ Fin s) R)) :=
    Units.continuous_val.comp continuous_subtypeVal
  exact isClosed_eq ((continuous_apply (Sum.inr b : X ⊕ Fin s)).comp
    ((continuous_apply i).comp hval)) continuous_const

/-- The unipotent group of the grades is contained in the Bessel group. -/
theorem gradedUnipotent_le_gradedBesselGroup : gradedUnipotent X s N ≤ gradedBesselGroup X s N :=
  fun _ hg ↦ mem_gradedBesselGroup_iff.mpr fun i _ _ hib ↦ mem_gradedUnipotent_iff.mp hg i _ hib

/-! ### The columns of an element of the Bessel group -/

/-- The entries of `gᴴ J g = J` for an isometry `g` of the graded Gram matrix `J`. -/
private theorem sum_star_mul_gradedGram_mul {g : GL (X ⊕ Fin s) R}
    (hg : g ∈ unitaryGroupOf (gradedGram X s N)) (i j : X ⊕ Fin s) :
    ∑ k, star ((g : Matrix (X ⊕ Fin s) (X ⊕ Fin s) R) k i) *
      (gradedGram X s N * (g : Matrix (X ⊕ Fin s) (X ⊕ Fin s) R)) k j = gradedGram X s N i j := by
  have h := congrFun (congrFun (mem_unitaryGroupOf_iff.mp hg) i) j
  rw [Matrix.mul_assoc, Matrix.mul_apply] at h
  simpa only [Matrix.star_apply] using h

/-- In a column indexed by `X` of an element `g` of the Bessel group, the component along a string
vector `e_b` of grade `≤ 0` is killed by the pairing `⟨e_b, e_{s-1-b}⟩`, which is `1`, or `-N` for
the middle vector of an odd string. -/
theorem star_apply_inr_inl_mul_gradedGram_eq_zero_of_mem_gradedBesselGroup
    {g : unitaryGroupOf (gradedGram X s N)} (hg : g ∈ gradedBesselGroup X s N) (x : X)
    {b : Fin s} (hb : gradedGrade X s (.inr b) ≤ 0) :
    star (((g : GL (X ⊕ Fin s) R) : Matrix (X ⊕ Fin s) (X ⊕ Fin s) R) (.inr b) (.inl x)) *
      gradedGram X s N (.inr b) (.inr b.rev) = 0 := by
  have hR := mem_gradedBesselGroup_iff.mp hg
  -- Induction along the string, from the lowest grade up: the entry `(e_x, e_{s-1-b})` of
  -- `gᴴ J g = J` is `star (g e_b e_x) * ⟨e_b, e_{s-1-b}⟩` plus terms of lower grade.
  induction b using WellFoundedGT.induction with
  | _ b ih =>
  have hb' : 0 ≤ gradedGrade X s (.inr b.rev) := by rw [gradedGrade_inr_rev]; omega
  have h := sum_star_mul_gradedGram_mul g.property (.inl x) (.inr b.rev)
  rw [Fintype.sum_eq_single (.inr b)] at h
  · simpa only [gradedGram_mul_apply_inr, hR _ _ hb' le_rfl, one_apply_eq, mul_one,
      gradedGram_inl_inr] using h
  · rintro (y | c) hc
    · rw [gradedGram_mul_apply_inl, hR _ _ hb' (by simpa using hb'), one_apply_ne (by simp),
        mul_zero]
    · rw [gradedGram_mul_apply_inr]
      rcases le_or_gt (gradedGrade X s (.inr c.rev)) (gradedGrade X s (.inr b.rev)) with h' | h'
      · rw [hR _ _ hb' h', one_apply_ne (by simpa using hc), mul_zero, mul_zero]
      · have h'' : gradedGrade X s (.inr c) < gradedGrade X s (.inr b) := by
          simpa only [Fin.rev_rev] using gradedGrade_inr_rev_lt_iff.mp h'
        have hcc : c ≠ c.rev := (gradedGrade_inr_ne_zero_iff (X := X)).mp (by omega)
        have := ih c (gradedGrade_inr_lt_iff.mp h'') (by omega)
        simp only [gradedGram_inr_inr_rev, hcc, ↓reduceIte, mul_one] at this
        rw [this, zero_mul]

/-- The columns indexed by `X` of an element `g` of the Bessel group have no component on the
string in negative grade. -/
theorem apply_inr_inl_eq_zero_of_mem_gradedBesselGroup
    {g : unitaryGroupOf (gradedGram X s N)} (hg : g ∈ gradedBesselGroup X s N) (x : X)
    {b : Fin s} (hb : gradedGrade X s (.inr b) < 0) :
    ((g : GL (X ⊕ Fin s) R) : Matrix (X ⊕ Fin s) (X ⊕ Fin s) R) (.inr b) (.inl x) = 0 := by
  have h := star_apply_inr_inl_mul_gradedGram_eq_zero_of_mem_gradedBesselGroup hg x hb.le
  have hbb : b ≠ b.rev := gradedGrade_inr_ne_zero_iff.mp hb.ne
  simpa only [gradedGram_inr_inr_rev, hbb, ↓reduceIte, mul_one, star_eq_zero] using h

/-- The columns indexed by `X` of an element `g` of the Bessel group have no component on the
string in grade `≤ 0`, when `N` is not a zero divisor. -/
theorem apply_inr_inl_eq_zero_of_mem_gradedBesselGroup_of_isLeftRegular (hN : IsLeftRegular N)
    {g : unitaryGroupOf (gradedGram X s N)} (hg : g ∈ gradedBesselGroup X s N) (x : X)
    {b : Fin s} (hb : gradedGrade X s (.inr b) ≤ 0) :
    ((g : GL (X ⊕ Fin s) R) : Matrix (X ⊕ Fin s) (X ⊕ Fin s) R) (.inr b) (.inl x) = 0 := by
  have h := star_apply_inr_inl_mul_gradedGram_eq_zero_of_mem_gradedBesselGroup hg x hb
  rw [gradedGram_inr_inr_rev] at h
  rw [← star_eq_zero]
  split_ifs at h
  · exact hN (by simpa [mul_comm] using h)
  · simpa using h

/-- The string columns of an element `g` of the Bessel group agree with the identity in every
grade up to their own: for columns of grade `≥ 0` this is the definition, and for columns of
negative grade it follows from `gᴴ J g = J`. -/
theorem apply_inr_inr_eq_one_apply_of_mem_gradedBesselGroup
    {g : unitaryGroupOf (gradedGram X s N)} (hg : g ∈ gradedBesselGroup X s N)
    {b c : Fin s} (hbc : gradedGrade X s (.inr b) ≤ gradedGrade X s (.inr c)) :
    ((g : GL (X ⊕ Fin s) R) : Matrix (X ⊕ Fin s) (X ⊕ Fin s) R) (.inr b) (.inr c) =
      (1 : Matrix (X ⊕ Fin s) (X ⊕ Fin s) R) (.inr b) (.inr c) := by
  have hR := mem_gradedBesselGroup_iff.mp hg
  rcases le_or_gt 0 (gradedGrade X s (.inr c)) with hc | hc
  · exact hR _ _ hc hbc
  -- Induction along the string, from the lowest grade up: the entry `(e_{s-1-b}, e_c)` of
  -- `gᴴ J g = J` is `g e_b e_c` plus terms of lower grade.
  induction b using WellFoundedGT.induction with
  | _ b ih =>
  have hb' : 0 < gradedGrade X s (.inr b.rev) := by rw [gradedGrade_inr_rev]; omega
  have hbb : b.rev ≠ b := by
    simpa only [Fin.rev_rev] using gradedGrade_inr_ne_zero_iff.mp hb'.ne'
  have h := sum_star_mul_gradedGram_mul g.property (.inr b.rev) (.inr c)
  rw [Fintype.sum_eq_single (.inr b.rev)] at h
  · rw [hR _ _ hb'.le le_rfl] at h
    simp only [one_apply_eq, star_one, one_mul, gradedGram_mul_apply_inr, Fin.rev_rev,
      gradedGram_inr_inr, hbb, ↓reduceIte] at h
    rw [h]
    by_cases hbc' : b = c
    · subst hbc'; simp [hbb]
    · simp [hbc', one_apply_ne]
  · rintro k hk
    rcases le_or_gt (gradedGrade X s k) (gradedGrade X s (.inr b.rev)) with h' | h'
    · rw [hR _ _ hb'.le h', one_apply_ne hk, star_zero, zero_mul]
    · obtain c' | c' := k
      · rw [gradedGrade_inl] at h'; omega
      have h'' : gradedGrade X s (.inr c'.rev) < gradedGrade X s (.inr b) := by
        exact gradedGrade_inr_rev_lt_iff.mp h'
      rw [gradedGram_mul_apply_inr, ih c'.rev (gradedGrade_inr_lt_iff.mp h'') (by omega),
        one_apply_ne (fun h ↦ by rw [Sum.inr.inj h] at h''; omega), mul_zero, mul_zero]

/-! ### The projection onto `U(X)` -/

/-- The `X`-block of an element of the Bessel group is unitary. -/
theorem toBlocks₁₁_mem_unitaryGroup_of_mem_gradedBesselGroup
    {g : unitaryGroupOf (gradedGram X s N)} (hg : g ∈ gradedBesselGroup X s N) :
    ((g : GL (X ⊕ Fin s) R) : Matrix (X ⊕ Fin s) (X ⊕ Fin s) R).toBlocks₁₁ ∈ unitaryGroup X R := by
  rw [mem_unitaryGroup_iff']
  ext x y
  have h := sum_star_mul_gradedGram_mul g.property (.inl x) (.inl y)
  -- The string contributes nothing: a string vector of negative grade does not occur in the
  -- column of `x`, its partner, of positive grade, does not occur in the column of `y`, and the
  -- middle vector of an odd string is killed by its norm.
  have hz : ∑ c : Fin s, star (((g : GL (X ⊕ Fin s) R) : Matrix (X ⊕ Fin s) (X ⊕ Fin s) R)
      (.inr c) (.inl x)) * (gradedGram X s N * ((g : GL (X ⊕ Fin s) R) :
        Matrix (X ⊕ Fin s) (X ⊕ Fin s) R)) (.inr c) (.inl y) = 0 := by
    refine Finset.sum_eq_zero fun c _ ↦ ?_
    rw [gradedGram_mul_apply_inr]
    rcases lt_trichotomy (gradedGrade X s (.inr c)) 0 with hc | hc | hc
    · rw [apply_inr_inl_eq_zero_of_mem_gradedBesselGroup hg x hc, star_zero, zero_mul]
    · rw [← mul_assoc,
        star_apply_inr_inl_mul_gradedGram_eq_zero_of_mem_gradedBesselGroup hg x hc.le, zero_mul]
    · rw [apply_inr_inl_eq_zero_of_mem_gradedBesselGroup hg y
        (by rw [gradedGrade_inr_rev]; omega), mul_zero, mul_zero]
  rw [Fintype.sum_sum_type, hz, add_zero] at h
  simp only [gradedGram_mul_apply_inl, gradedGram_inl_inl] at h
  simpa [Matrix.mul_apply, Matrix.star_apply, toBlocks₁₁] using h

/-- Taking the `X`-block is multiplicative on the Bessel group. -/
theorem toBlocks₁₁_mul_of_mem_gradedBesselGroup
    {g h : unitaryGroupOf (gradedGram X s N)} (hg : g ∈ gradedBesselGroup X s N)
    (hh : h ∈ gradedBesselGroup X s N) :
    (((g * h : unitaryGroupOf (gradedGram X s N)) : GL (X ⊕ Fin s) R) :
        Matrix (X ⊕ Fin s) (X ⊕ Fin s) R).toBlocks₁₁ =
      ((g : GL (X ⊕ Fin s) R) : Matrix (X ⊕ Fin s) (X ⊕ Fin s) R).toBlocks₁₁ *
        ((h : GL (X ⊕ Fin s) R) : Matrix (X ⊕ Fin s) (X ⊕ Fin s) R).toBlocks₁₁ := by
  ext x y
  simp only [Subgroup.coe_mul, Units.val_mul, toBlocks₁₁, of_apply, Matrix.mul_apply,
    Fintype.sum_sum_type]
  refine add_eq_left.mpr (Finset.sum_eq_zero fun c _ ↦ ?_)
  rcases lt_or_ge (gradedGrade X s (.inr c)) 0 with hc | hc
  · rw [apply_inr_inl_eq_zero_of_mem_gradedBesselGroup hh y hc, mul_zero]
  · rw [mem_gradedBesselGroup_iff.mp hg _ _ hc (by simpa using hc), one_apply_ne (by simp),
      zero_mul]

/-- `diag(a, 1)` is an isometry of the graded Gram matrix for unitary `a`. -/
private theorem star_fromBlocks_mul_gradedGram_mul_fromBlocks (a : unitaryGroup X R) :
    star (fromBlocks (a : Matrix X X R) 0 0 1) * gradedGram X s N *
      fromBlocks (a : Matrix X X R) 0 0 1 = gradedGram X s N := by
  rw [gradedGram_eq_fromBlocks, star_eq_conjTranspose, fromBlocks_conjTranspose]
  simp [fromBlocks_multiply, ← star_eq_conjTranspose]

variable (X s N) in
/-- The embedding of the unitary group `U(X)` in the isometries of the graded Gram matrix as the
`X`-block: `a ↦ diag(a, 1)`. -/
def gradedInclusion : unitaryGroup X R →* unitaryGroupOf (gradedGram X s N) :=
  ((Unitary.toUnits.comp UnitaryGroup.sum).comp (MonoidHom.inl _ _)).codRestrict _ fun a ↦ by
    simpa [mem_unitaryGroupOf_iff] using star_fromBlocks_mul_gradedGram_mul_fromBlocks a

@[simp]
theorem coe_gradedInclusion (a : unitaryGroup X R) :
    ((gradedInclusion X s N a : GL (X ⊕ Fin s) R) : Matrix (X ⊕ Fin s) (X ⊕ Fin s) R) =
      fromBlocks (a : Matrix X X R) 0 0 1 := by
  simp [gradedInclusion]

/-- The embedding of `U(X)` as the `X`-block is injective. -/
theorem gradedInclusion_injective : Function.Injective (gradedInclusion X s N) := fun a b h ↦
  Subtype.ext <| by
    simpa using congrArg (fun g : unitaryGroupOf (gradedGram X s N) ↦
      ((g : GL (X ⊕ Fin s) R) : Matrix (X ⊕ Fin s) (X ⊕ Fin s) R).toBlocks₁₁) h

/-- The image of `U(X)` lies in the Bessel group. The high `simp` priority takes precedence over
the entrywise expansion `mem_gradedBesselGroup_iff`. -/
@[simp high]
theorem gradedInclusion_mem_gradedBesselGroup (a : unitaryGroup X R) :
    gradedInclusion X s N a ∈ gradedBesselGroup X s N :=
  mem_gradedBesselGroup_iff.mpr fun i b _ _ ↦ by rcases i with x | c <;> simp [Matrix.one_apply]

variable (X s N) in
/-- The embedding of `U(X)` into the Bessel group as the `X`-block. -/
def gradedBesselInclusion : unitaryGroup X R →* gradedBesselGroup X s N :=
  (gradedInclusion X s N).codRestrict _ gradedInclusion_mem_gradedBesselGroup

@[simp]
theorem coe_gradedBesselInclusion (a : unitaryGroup X R) :
    (gradedBesselInclusion X s N a : unitaryGroupOf (gradedGram X s N)) =
      gradedInclusion X s N a :=
  (rfl)

/-- The unipotent group of the grades meets the image of `U(X)` only in `1`. The high `simp`
priority takes precedence over the entrywise expansion `mem_gradedUnipotent_iff`. -/
@[simp high]
theorem gradedInclusion_mem_gradedUnipotent_iff {a : unitaryGroup X R} :
    gradedInclusion X s N a ∈ gradedUnipotent X s N ↔ a = 1 := by
  refine ⟨fun h ↦ Subtype.ext ?_, fun h ↦ by rw [h, map_one]; exact one_mem _⟩
  ext x y
  simpa [Matrix.one_apply] using mem_gradedUnipotent_iff.mp h (.inl x) (.inl y) (by simp)

/-- The image of `U(X)` raises the grade by at least `0`: it is block diagonal for the
grades. -/
theorem raisesDegree_coe_gradedInclusion (a : unitaryGroup X R) :
    RaisesDegree (gradedGrade X s) 0
      ((gradedInclusion X s N a : GL (X ⊕ Fin s) R) : Matrix (X ⊕ Fin s) (X ⊕ Fin s) R) := by
  rw [coe_gradedInclusion, raisesDegree_iff]
  rintro (x | b) (y | c) h
  · simp
  · simp at h
  · simp at h
  · obtain rfl : b = c := by_contra fun hbc ↦ h (by simp [one_apply_ne hbc])
    simp

/-- Conjugation by the image of `U(X)` preserves each term of the degree filtration. -/
theorem gradedInclusion_mul_mul_inv_mem_gradedUnipotentFiltration {d : ℤ} (a : unitaryGroup X R)
    {g : unitaryGroupOf (gradedGram X s N)} (hg : g ∈ gradedUnipotentFiltration X s N d) :
    gradedInclusion X s N a * g * (gradedInclusion X s N a)⁻¹ ∈
      gradedUnipotentFiltration X s N d :=
  mul_mul_inv_mem_gradedUnipotentFiltration (raisesDegree_coe_gradedInclusion a) hg

variable (X s N) in
/-- The **projection of the Bessel group onto `U(X)`**, `g ↦` the `X`-block of `g`. -/
def gradedBesselProj : gradedBesselGroup X s N →* unitaryGroup X R where
  toFun g := ⟨_, toBlocks₁₁_mem_unitaryGroup_of_mem_gradedBesselGroup g.property⟩
  map_one' := Subtype.ext <| by ext; simp [toBlocks₁₁, Matrix.one_apply]
  map_mul' g h := Subtype.ext <| toBlocks₁₁_mul_of_mem_gradedBesselGroup g.property h.property

@[simp]
theorem coe_gradedBesselProj (g : gradedBesselGroup X s N) :
    (gradedBesselProj X s N g : Matrix X X R) =
      (((g : unitaryGroupOf (gradedGram X s N)) : GL (X ⊕ Fin s) R) :
        Matrix (X ⊕ Fin s) (X ⊕ Fin s) R).toBlocks₁₁ :=
  (rfl)

/-- The projection of the Bessel group onto `U(X)` is the identity on `U(X)`. -/
@[simp]
theorem gradedBesselProj_gradedBesselInclusion (a : unitaryGroup X R) :
    gradedBesselProj X s N (gradedBesselInclusion X s N a) = a :=
  Subtype.ext <| by simp

/-- The projection retracts the embedding of `U(X)` into the Bessel group. -/
@[simp]
theorem gradedBesselProj_comp_gradedBesselInclusion :
    (gradedBesselProj X s N).comp (gradedBesselInclusion X s N) = MonoidHom.id _ := by
  ext a : 1
  exact gradedBesselProj_gradedBesselInclusion a

/-- The projection of the Bessel group onto `U(X)` is surjective. -/
theorem gradedBesselProj_surjective : Function.Surjective (gradedBesselProj X s N) :=
  fun a ↦ ⟨gradedBesselInclusion X s N a, gradedBesselProj_gradedBesselInclusion a⟩

/-- The kernel of the projection of the Bessel group onto `U(X)` is the unipotent group of the
grades, when `N` is not a zero divisor. -/
theorem ker_gradedBesselProj (hN : IsLeftRegular N) :
    (gradedBesselProj X s N).ker =
      (gradedUnipotent X s N).subgroupOf (gradedBesselGroup X s N) := by
  ext ⟨g, hg⟩
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, mem_gradedUnipotent_iff]
  refine ⟨fun h ↦ ?_, fun h ↦ Subtype.ext ?_⟩
  · have h' := congrArg (fun a : unitaryGroup X R ↦ (a : Matrix X X R)) h
    simp only [coe_gradedBesselProj, OneMemClass.coe_one] at h'
    rintro i (y | c) hij
    · rcases i with x | b
      · simpa [toBlocks₁₁, Matrix.one_apply] using congrFun (congrFun h' x) y
      · rw [apply_inr_inl_eq_zero_of_mem_gradedBesselGroup_of_isLeftRegular hN hg y
          (by simpa using hij), one_apply_ne (by simp)]
    · rcases i with x | b
      · exact mem_gradedBesselGroup_iff.mp hg _ _ (by simpa using hij) hij
      · exact apply_inr_inr_eq_one_apply_of_mem_gradedBesselGroup hg hij
  · ext x y
    simpa [toBlocks₁₁, Matrix.one_apply] using h (.inl x) (.inl y) (by simp)

/-- An element `g` of the Bessel group times the inverse of the image of its projection onto
`U(X)` lies in the unipotent group of the grades. -/
theorem mul_inv_gradedInclusion_mem_gradedUnipotent (hN : IsLeftRegular N)
    (g : gradedBesselGroup X s N) :
    (g : unitaryGroupOf (gradedGram X s N)) *
      (gradedInclusion X s N (gradedBesselProj X s N g))⁻¹ ∈ gradedUnipotent X s N := by
  set a := gradedBesselInclusion X s N (gradedBesselProj X s N g)
  have hker : g * a⁻¹ ∈ (gradedBesselProj X s N).ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, gradedBesselProj_gradedBesselInclusion,
      mul_inv_cancel]
  rw [ker_gradedBesselProj hN, Subgroup.mem_subgroupOf] at hker
  simpa [a] using hker

/-- Every element of the Bessel group is `u * a` with `u` in the unipotent group of the grades and
`a` in the image of `U(X)`, when `N` is not a zero divisor. -/
theorem exists_mem_gradedUnipotent_mul_gradedInclusion (hN : IsLeftRegular N)
    {g : unitaryGroupOf (gradedGram X s N)} (hg : g ∈ gradedBesselGroup X s N) :
    ∃ u ∈ gradedUnipotent X s N, ∃ a, g = u * gradedInclusion X s N a :=
  ⟨_, mul_inv_gradedInclusion_mem_gradedUnipotent hN ⟨g, hg⟩, gradedBesselProj X s N ⟨g, hg⟩,
    (inv_mul_cancel_right _ _).symm⟩

/-- The projection of the Bessel group onto `U(X)` is continuous, for any topology on `R`. -/
theorem continuous_gradedBesselProj [TopologicalSpace R] :
    Continuous (gradedBesselProj X s N) := by
  refine Continuous.subtype_mk ?_ _
  have h : Continuous fun g : gradedBesselGroup X s N ↦
      (((g : unitaryGroupOf (gradedGram X s N)) : GL (X ⊕ Fin s) R) :
        Matrix (X ⊕ Fin s) (X ⊕ Fin s) R) :=
    Units.continuous_val.comp (continuous_subtypeVal.comp continuous_subtypeVal)
  exact h.matrix_submatrix Sum.inl Sum.inl

end TauCeti

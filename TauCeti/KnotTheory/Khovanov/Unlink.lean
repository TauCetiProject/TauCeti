/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Khovanov.Complex
public import TauCeti.KnotTheory.Khovanov.Rank

/-!
# Khovanov homology of crossing-free diagrams

A crossing-free oriented PD-code `D : OrientedPDCode 0` is an unlink: a finite family of
crossing-free circles. Its cube of resolutions has the single vertex `∅`, whose resolution consists
of exactly these circles, so the normalized Khovanov complex in quantum degree `j` is concentrated
in cochain degree `0`, where it is the degree-`j` piece of the circle tensor `V^{⊗ k}` of the
`k` circles. This file computes the resulting Khovanov homology of the empty link, the unknots
and the unlinks, as integral free modules and over every commutative coefficient ring:

* the homology vanishes outside cochain degree `0`, and in cochain degree `0` it is the degree-`j`
  piece of the circle tensor of the resolved circles, of rank the coefficient of `q ^ j` in
  `(q + q⁻¹) ^ k`;
* the empty link has homology `R` in bidegree `(0, 0)` and zero elsewhere;
* a crossing-free unknot, with either orientation, has homology `R` in bidegrees `(0, 1)` and
  `(0, -1)` and zero elsewhere.

These are the base values of the Khovanov invariant: the empty link and the unknot normalize it,
and the unlink of `k` components has graded rank `(q + q⁻¹) ^ k`.

## Main definitions

* `TauCeti.OrientedPDCode.emptyVertex`: the only vertex `∅` of the cube of resolutions of a
  crossing-free diagram, as a state of cochain degree `0`.
* `TauCeti.OrientedPDCode.khovanovComplexXZeroIso`: the cochain term in degree `0` of a
  crossing-free diagram is the degree-`j` piece of the circle tensor of its resolved circles.
* `TauCeti.OrientedPDCode.khovanovComplexHomologyZeroIso`: so is its homology in degree `0`.
* `TauCeti.OrientedPDCode.khovanovComplexHomologyEmptyIso`: the homology of the empty diagram in
  bidegree `(0, 0)` is `R`.
* `TauCeti.OrientedPDCode.khovanovComplexHomologyUnknotIso`: the homology of a crossing-free
  unknot in bidegrees `(0, ±1)` is `R`.

## Main results

* `TauCeti.OrientedPDCode.isZero_homology_khovanovComplex_of_ne_zero`: the homology of a
  crossing-free diagram vanishes outside cochain degree `0`.
* `TauCeti.OrientedPDCode.coeff_pow_eq_finrank_homology_khovanovComplex`: the rank of its homology
  in bidegree `(0, j)` is the coefficient of `q ^ j` in `(q + q⁻¹) ^ k` for `k` circles.
* `TauCeti.OrientedPDCode.isZero_homology_khovanovComplex_empty`,
  `TauCeti.OrientedPDCode.isZero_homology_khovanovComplex_unknot`: the homology of the empty
  diagram and of the unknot vanishes in every other bidegree.

## References

* M. Khovanov, *A categorification of the Jones polynomial*, Duke Math. J. 101 (2000).
* D. Bar-Natan, *On Khovanov's categorification of the Jones polynomial*,
  Algebr. Geom. Topol. 2 (2002).
-/

public section

noncomputable section

open CategoryTheory Limits Finset HomologicalComplex LaurentPolynomial

namespace TauCeti.OrientedPDCode

universe u

variable (D : OrientedPDCode 0) (hD : D.toPDCode.IsPlanar) (R : Type u) [CommRing R] (j : ℤ)

/-- The only vertex of the cube of resolutions of a crossing-free diagram is the degree-`j` piece of
the circle tensor of its resolved circles: with no crossings there is no quantum shift. -/
theorem resolutionCube_obj_empty :
    (D.toPDCode.resolutionCube hD R
      (j - D.positiveCrossingCount + 2 * D.negativeCrossingCount)).obj ∅ =
        ModuleCat.of R ((Khovanov.circleQuantumGrading R
          (D.toPDCode.ResolvedCircle (PDCode.cubeState ∅))).piece j) := by
  rw [D.resolutionCube_obj_normalized hD R j ∅, show D.stateQuantumShift (PDCode.cubeState ∅) = 0
    by simp [stateQuantumShift_cubeState, positiveCrossingCount_def, negativeCrossingCount_def],
    sub_zero]

/-- The only vertex `∅` of the cube of resolutions of a crossing-free diagram, as a state of
cochain degree `0`. -/
abbrev emptyVertex : {S : Finset (Fin 0) // (#S : ℤ) = 0 + D.negativeCrossingCount} :=
  ⟨∅, by simp [negativeCrossingCount_def]⟩

/-- The Khovanov complex of a crossing-free diagram vanishes outside cochain degree `0`. -/
theorem isZero_khovanovComplex_X {i : ℤ} (hi : i ≠ 0) :
    IsZero ((D.khovanovComplex hD R j).X i) := by
  rcases hi.lt_or_gt with hi | hi
  · exact CochainComplex.isZero_of_isStrictlyGE _ (-(D.negativeCrossingCount : ℤ)) i
      (by simpa [negativeCrossingCount_def] using hi)
  · exact CochainComplex.isZero_of_isStrictlyLE _ D.positiveCrossingCount i
      (by simpa [positiveCrossingCount_def] using hi)

/-- The cochain term in degree `0` of a crossing-free diagram is the degree-`j` piece of the circle
tensor of its resolved circles, through the inclusion of its only cube vertex. -/
def khovanovComplexXZeroIso :
    (D.khovanovComplex hD R j).X 0 ≅
      ModuleCat.of R ((Khovanov.circleQuantumGrading R
        (D.toPDCode.ResolvedCircle (PDCode.cubeState ∅))).piece j) where
  hom := D.khovanovComplexπ hD R j D.emptyVertex ≫
    eqToHom (D.resolutionCube_obj_empty hD R j)
  inv := eqToHom (D.resolutionCube_obj_empty hD R j).symm ≫
    D.khovanovComplexι hD R j D.emptyVertex
  hom_inv_id := by
    ext S
    obtain rfl : S = D.emptyVertex := Subsingleton.elim _ _
    simp
  inv_hom_id := by simp

/-- The degree-`0` term comparison is the projection onto the only cube vertex. -/
theorem khovanovComplexXZeroIso_hom :
    (D.khovanovComplexXZeroIso hD R j).hom =
      D.khovanovComplexπ hD R j D.emptyVertex ≫
        eqToHom (D.resolutionCube_obj_empty hD R j) :=
  (rfl)

/-- The inverse degree-`0` term comparison is the inclusion of the only cube vertex. -/
theorem khovanovComplexXZeroIso_inv :
    (D.khovanovComplexXZeroIso hD R j).inv =
      eqToHom (D.resolutionCube_obj_empty hD R j).symm ≫
        D.khovanovComplexι hD R j D.emptyVertex :=
  (rfl)

/-- **The Khovanov homology of a crossing-free diagram** in cochain degree `0` and quantum degree
`j` is the degree-`j` piece of the circle tensor of its resolved circles. -/
def khovanovComplexHomologyZeroIso :
    (D.khovanovComplex hD R j).homology 0 ≅
      ModuleCat.of R ((Khovanov.circleQuantumGrading R
        (D.toPDCode.ResolvedCircle (PDCode.cubeState ∅))).piece j) :=
  ((D.khovanovComplex hD R j).isoHomologyπ (-1) 0 (by simp)
      ((D.isZero_khovanovComplex_X hD R j (by simp)).eq_of_src _ _)).symm ≪≫
    (D.khovanovComplex hD R j).iCyclesIso 0 1 (by simp)
      ((D.isZero_khovanovComplex_X hD R j (by simp)).eq_of_tgt _ _) ≪≫
    D.khovanovComplexXZeroIso hD R j

/-- The homology of a crossing-free diagram is the cochain term itself: the comparison with the
circle tensor is induced by the inclusion of the cocycles. -/
@[reassoc (attr := simp)]
theorem homologyπ_khovanovComplexHomologyZeroIso_hom :
    (D.khovanovComplex hD R j).homologyπ 0 ≫ (D.khovanovComplexHomologyZeroIso hD R j).hom =
      (D.khovanovComplex hD R j).iCycles 0 ≫ (D.khovanovComplexXZeroIso hD R j).hom := by
  simp [khovanovComplexHomologyZeroIso]

/-- **The Khovanov homology of a crossing-free diagram vanishes outside cochain degree `0`.** -/
theorem isZero_homology_khovanovComplex_of_ne_zero {i : ℤ} (hi : i ≠ 0) :
    IsZero ((D.khovanovComplex hD R j).homology i) :=
  (ExactAt.of_isZero (D.isZero_khovanovComplex_X hD R j hi)).isZero_homology

/-- The Khovanov homology of a crossing-free diagram is free. -/
instance : Module.Free R ((D.khovanovComplex hD R j).homology 0) :=
  .of_equiv (D.khovanovComplexHomologyZeroIso hD R j).toLinearEquiv.symm

/-- The Khovanov homology of a crossing-free diagram is finitely generated. -/
instance : Module.Finite R ((D.khovanovComplex hD R j).homology 0) :=
  .equiv (D.khovanovComplexHomologyZeroIso hD R j).toLinearEquiv.symm

/-- The Khovanov homology of a crossing-free diagram vanishes in bidegree `(0, j)` when no labelling
of its resolved circles has quantum degree `j`. -/
theorem isZero_homology_khovanovComplex_zero_of_labelingQuantumDegree_ne
    (h : ∀ l, Khovanov.labelingQuantumDegree
      (D.toPDCode.ResolvedCircle (PDCode.cubeState ∅)) l ≠ j) :
    IsZero ((D.khovanovComplex hD R j).homology 0) := by
  refine IsZero.of_iso ?_ (D.khovanovComplexHomologyZeroIso hD R j)
  rw [ModuleCat.isZero_of_iff_subsingleton, Submodule.subsingleton_iff_eq_bot]
  exact Khovanov.circleQuantumGrading_piece_eq_bot h

/-- **The graded rank of the Khovanov homology of an unlink**: for a crossing-free diagram with
`k` circles, the rank of the homology in bidegree `(0, j)` is the coefficient of `q ^ j` in
`(q + q⁻¹) ^ k`. -/
theorem coeff_pow_eq_finrank_homology_khovanovComplex [Nontrivial R] :
    ((T 1 + T (-1)) ^ D.crossinglessComponentCount : ℤ[T;T⁻¹]).coeff j =
      Module.finrank R ((D.khovanovComplex hD R j).homology 0) := by
  have h := Khovanov.coeff_pow_eq_finrank_circleQuantumGrading_piece R
    (ι := D.toPDCode.ResolvedCircle (PDCode.cubeState ∅)) j
  rw [PDCode.card_resolvedCircle_eq_crossinglessComponentCount] at h
  rw [h, (D.khovanovComplexHomologyZeroIso hD R j).toLinearEquiv.finrank_eq]

section Empty

variable (hD : empty.toPDCode.IsPlanar)

/-- The empty diagram has no resolved circles. -/
private theorem isEmpty_resolvedCircle_empty :
    IsEmpty (empty.toPDCode.ResolvedCircle (PDCode.cubeState ∅)) := by
  rw [← Fintype.card_eq_zero_iff, PDCode.card_resolvedCircle_eq_crossinglessComponentCount,
    ← card_crossinglessComponents, crossinglessComponents_empty, Multiset.card_zero]

/-- The only labelling of the circles of the empty diagram has quantum degree `0`. -/
private theorem labelingQuantumDegree_empty_eq_zero_iff
    (l : empty.toPDCode.ResolvedCircle (PDCode.cubeState ∅) → Bool) :
    Khovanov.labelingQuantumDegree _ l = 0 ↔ l = fun _ ↦ false := by
  have := isEmpty_resolvedCircle_empty
  simp [Khovanov.labelingQuantumDegree_def, Subsingleton.elim l (fun _ ↦ false)]

/-- **The Khovanov homology of the empty link** in bidegree `(0, 0)` is `R`. -/
def khovanovComplexHomologyEmptyIso :
    (empty.khovanovComplex hD R 0).homology 0 ≅ ModuleCat.of R R :=
  khovanovComplexHomologyZeroIso empty hD R 0 ≪≫
    (Khovanov.circlePieceEquivOfUnique R _ labelingQuantumDegree_empty_eq_zero_iff).toModuleIso

/-- The identification of the homology of the empty diagram with `R` reads off the coordinate of a
cocycle along the empty labelling. -/
@[reassoc (attr := simp)]
theorem homologyπ_khovanovComplexHomologyEmptyIso_hom :
    (empty.khovanovComplex hD R 0).homologyπ 0 ≫ (khovanovComplexHomologyEmptyIso R hD).hom =
      (empty.khovanovComplex hD R 0).iCycles 0 ≫ (khovanovComplexXZeroIso empty hD R 0).hom ≫
        ModuleCat.ofHom ((Khovanov.circleBasis R _).coord (fun _ ↦ false) ∘ₗ
          ((Khovanov.circleQuantumGrading R _).piece 0).subtype) := by
  ext
  simp [khovanovComplexHomologyEmptyIso]

/-- The homology class corresponding to `r : R` in the homology of the empty diagram is the
multiple `r` of the basis vector of the empty labelling. -/
@[simp]
theorem coe_khovanovComplexHomologyZeroIso_hom_khovanovComplexHomologyEmptyIso_inv (r : R) :
    Subtype.val (p := (· ∈ (Khovanov.circleQuantumGrading R _).piece 0))
        ((khovanovComplexHomologyZeroIso empty hD R 0).hom
          ((khovanovComplexHomologyEmptyIso R hD).inv r)) =
      r • Khovanov.circleBasis R _ fun _ ↦ false := by
  simp [khovanovComplexHomologyEmptyIso]

/-- **The Khovanov homology of the empty link vanishes outside bidegree `(0, 0)`.** -/
theorem isZero_homology_khovanovComplex_empty {i j : ℤ} (hij : i ≠ 0 ∨ j ≠ 0) :
    IsZero ((empty.khovanovComplex hD R j).homology i) := by
  by_cases hi : i = 0
  · subst hi
    refine isZero_homology_khovanovComplex_zero_of_labelingQuantumDegree_ne empty hD R j
      fun l hl ↦ (Khovanov.abs_labelingQuantumDegree_le l).not_gt ?_
    rw [hl, Fintype.card_eq_zero_iff.2 isEmpty_resolvedCircle_empty, Nat.cast_zero, abs_pos]
    exact hij.resolve_left (not_not.2 rfl)
  · exact isZero_homology_khovanovComplex_of_ne_zero empty hD R j hi

end Empty

section Unknot

variable (o : Bool) (hD : (unknot o).toPDCode.IsPlanar)

/-- A crossing-free unknot has exactly one resolved circle. -/
private theorem card_resolvedCircle_unknot :
    Fintype.card ((unknot o).toPDCode.ResolvedCircle (PDCode.cubeState ∅)) = 1 := by
  rw [PDCode.card_resolvedCircle_eq_crossinglessComponentCount, ← card_crossinglessComponents,
    crossinglessComponents_unknot, Multiset.card_singleton]

/-- The quantum degree of a labelling of the only circle `x` of an unknot is `1` for the label `1`
and `-1` for the label `X`. -/
private theorem exists_labelingQuantumDegree_unknot
    (l : (unknot o).toPDCode.ResolvedCircle (PDCode.cubeState ∅) → Bool) :
    ∃ x, (∀ y, y = x) ∧ Khovanov.labelingQuantumDegree _ l = bif l x then -1 else 1 := by
  obtain ⟨x, hx⟩ := Fintype.card_eq_one_iff.1 (card_resolvedCircle_unknot o)
  rw [Khovanov.labelingQuantumDegree_def]
  exact ⟨x, hx, Fintype.sum_eq_single x fun y hy ↦ (hy (hx y)).elim⟩

/-- The only labelling of the circle of an unknot of degree `1` is the labelling `1` (`false`), and
the only one of degree `-1` is the labelling `X` (`true`). -/
private theorem labelingQuantumDegree_unknot_eq_iff
    (l : (unknot o).toPDCode.ResolvedCircle (PDCode.cubeState ∅) → Bool) (b : Bool) :
    Khovanov.labelingQuantumDegree _ l = (bif b then -1 else 1) ↔ l = fun _ ↦ b := by
  obtain ⟨x, hx, hdeg⟩ := exists_labelingQuantumDegree_unknot o l
  rw [hdeg, funext_iff]
  refine ⟨fun h y ↦ ?_, fun h ↦ by rw [h x]⟩
  rw [hx y]
  cases hl : l x <;> cases b <;> simp_all

/-- **The Khovanov homology of the unknot** in bidegrees `(0, 1)` and `(0, -1)` is `R`: the first
is spanned by the labelling `1` of its circle and the second by the labelling `X`. -/
def khovanovComplexHomologyUnknotIso {j : ℤ} (hj : j = 1 ∨ j = -1) :
    ((unknot o).khovanovComplex hD R j).homology 0 ≅ ModuleCat.of R R :=
  khovanovComplexHomologyZeroIso (unknot o) hD R j ≪≫
    (Khovanov.circlePieceEquivOfUnique R (fun _ ↦ decide (j = -1)) fun l ↦ by
      rcases hj with rfl | rfl
      · simpa using labelingQuantumDegree_unknot_eq_iff o l false
      · simpa using labelingQuantumDegree_unknot_eq_iff o l true).toModuleIso

/-- The identification of the homology of the unknot in quantum degree `j = ±1` with `R` reads off
the coordinate of a cocycle along the labelling `1` (for `j = 1`) or `X` (for `j = -1`) of its
circle. -/
@[reassoc (attr := simp)]
theorem homologyπ_khovanovComplexHomologyUnknotIso_hom {j : ℤ} (hj : j = 1 ∨ j = -1) :
    ((unknot o).khovanovComplex hD R j).homologyπ 0 ≫
        (khovanovComplexHomologyUnknotIso R o hD hj).hom =
      ((unknot o).khovanovComplex hD R j).iCycles 0 ≫
        (khovanovComplexXZeroIso (unknot o) hD R j).hom ≫
          ModuleCat.ofHom ((Khovanov.circleBasis R _).coord (fun _ ↦ decide (j = -1)) ∘ₗ
            ((Khovanov.circleQuantumGrading R _).piece j).subtype) := by
  ext
  simp [khovanovComplexHomologyUnknotIso]

/-- The homology class corresponding to `r : R` in the homology of the unknot in quantum degree
`j = ±1` is the multiple `r` of the basis vector of the labelling `1` (for `j = 1`) or `X` (for
`j = -1`) of its circle. -/
@[simp]
theorem coe_khovanovComplexHomologyZeroIso_hom_khovanovComplexHomologyUnknotIso_inv {j : ℤ}
    (hj : j = 1 ∨ j = -1) (r : R) :
    Subtype.val (p := (· ∈ (Khovanov.circleQuantumGrading R _).piece j))
        ((khovanovComplexHomologyZeroIso (unknot o) hD R j).hom
          ((khovanovComplexHomologyUnknotIso R o hD hj).inv r)) =
      r • Khovanov.circleBasis R _ fun _ ↦ decide (j = -1) := by
  simp [khovanovComplexHomologyUnknotIso]

/-- **The Khovanov homology of the unknot vanishes outside bidegrees `(0, 1)` and `(0, -1)`.** -/
theorem isZero_homology_khovanovComplex_unknot {i j : ℤ} (hij : i ≠ 0 ∨ (j ≠ 1 ∧ j ≠ -1)) :
    IsZero (((unknot o).khovanovComplex hD R j).homology i) := by
  by_cases hi : i = 0
  · subst hi
    have hj := hij.resolve_left (not_not.2 rfl)
    refine isZero_homology_khovanovComplex_zero_of_labelingQuantumDegree_ne (unknot o) hD R j
      fun l hl ↦ ?_
    obtain ⟨x, -, hdeg⟩ := exists_labelingQuantumDegree_unknot o l
    cases h : l x <;> simp_all
  · exact isZero_homology_khovanovComplex_of_ne_zero (unknot o) hD R j hi

end Unknot

end TauCeti.OrientedPDCode

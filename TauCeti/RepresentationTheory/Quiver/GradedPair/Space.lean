/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.DirectSum.Module
public import Mathlib.Basic.Complex.Basic
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import TauCeti.Algebra.DirectSum.Internal
import TauCeti.Data.Fintype.Fiber
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.StdBasis
import Mathlib.RingTheory.Finiteness.Cardinality

/-!
# Finite coordinate presentations of integer-graded complex vector spaces

A `TauCeti.GradedCoordSpace` is a finite-dimensional `ℤ`-graded complex vector space presented in
coordinates: it records a number `n` of basis vectors and an integer degree for each of them. Its
carrier is the coordinate space `Fin n → ℂ`, and its degree-`a` piece `S.grade a` consists of the
vectors vanishing at every coordinate of degree different from `a`. Repeated degrees are allowed,
so a grade may have any finite dimension.

These coordinate models are the carriers of the raising and lowering operators of
`TauCeti.RepresentationTheory.Quiver.GradedPair.Basic`. Every finite-dimensional internal
`ℤ`-grading of a complex vector space has such a presentation
(`TauCeti.GradedCoordSpace.exists_linearEquiv_of_isInternal`), and two presentations are related
by a grade-preserving linear equivalence exactly when their grades have equal dimensions
(`TauCeti.GradedCoordSpace.exists_linearEquiv_iff_finrank_grade_eq`).

## Main definitions

* `TauCeti.GradedCoordSpace`: a finite list of integer degrees for the coordinates of `Fin n → ℂ`.
* `TauCeti.GradedCoordSpace.grade`: the coordinate vectors supported on the degree-`a` coordinates.
* `TauCeti.GradedCoordSpace.constant`: `n` coordinates all placed in one degree.

## Main results

* `TauCeti.GradedCoordSpace.isInternal_grade`: the grades form an internal direct sum.
* `TauCeti.GradedCoordSpace.finrank_grade`: the dimension of a grade is the number of coordinates
  of that degree.
* `TauCeti.GradedCoordSpace.finite_setOf_grade_ne_bot`: only finitely many grades are nonzero.
* `TauCeti.GradedCoordSpace.exists_linearEquiv_of_isInternal`: every finite-dimensional internal
  `ℤ`-grading of a complex vector space has a coordinate presentation.
* `TauCeti.GradedCoordSpace.map_grade_of_mem_grade_iff`: a grade-preserving linear equivalence
  maps each grade onto the corresponding grade.
* `TauCeti.GradedCoordSpace.exists_linearEquiv_iff_finrank_grade_eq`: two presentations are
  isomorphic as graded vector spaces exactly when their grades have equal dimensions.

## References

* H. Atobe, S. Kondo, S. Yasuda, *Local newforms for the general linear groups over a
  non-archimedean local field*, Forum of Mathematics, Pi 10 (2022), e24, §3.1.
-/

public section

open Module

namespace TauCeti

/-- A finite coordinate presentation of a `ℤ`-graded complex vector space: `n` coordinates, each
with an integer degree. The carrier is `Fin n → ℂ`. -/
structure GradedCoordSpace where
  /-- The number of coordinates, i.e. the total dimension. -/
  n : ℕ
  /-- The degree of each coordinate. -/
  degree : Fin n → ℤ

namespace GradedCoordSpace

variable (S T : GradedCoordSpace)

/-- The complex coordinate vector space of a graded presentation. -/
abbrev Carrier : Type := Fin S.n → ℂ

/-- The degree-`a` piece: vectors vanishing at every coordinate whose degree is not `a`. -/
def grade (a : ℤ) : Submodule ℂ S.Carrier where
  carrier := {v | ∀ i, S.degree i ≠ a → v i = 0}
  zero_mem' := by simp
  add_mem' hx hy i hi := by simp [hx i hi, hy i hi]
  smul_mem' c v hv i hi := by simp [hv i hi]

variable {S} in
theorem mem_grade_iff {a : ℤ} {v : S.Carrier} : v ∈ S.grade a ↔ ∀ i, S.degree i ≠ a → v i = 0 :=
  Iff.rfl

/-- The basis vector of a coordinate lies in the grade of that coordinate's degree. -/
theorem single_mem_grade (i : Fin S.n) (x : ℂ) : Pi.single i x ∈ S.grade (S.degree i) := by
  refine mem_grade_iff.2 fun j hj ↦ ?_
  rw [Pi.single_eq_of_ne fun h ↦ hj (congrArg S.degree h)]

/-- The degree-`a` piece is spanned by the standard basis vectors of the coordinates of
degree `a`. -/
theorem grade_eq_span (a : ℤ) :
    S.grade a = Submodule.span ℂ (Pi.basisFun ℂ (Fin S.n) '' {i | S.degree i = a}) := by
  ext v
  rw [Module.Basis.mem_span_image, Finsupp.support_subset_iff, mem_grade_iff]
  simp

/-- The grades of a coordinate presentation form an internal direct sum. -/
theorem isInternal_grade : DirectSum.IsInternal S.grade := by
  rw [show S.grade = _ from funext S.grade_eq_span]
  exact Module.Basis.isInternal_span_image_fiber (Pi.basisFun ℂ (Fin S.n)) S.degree

/-- The dimension of the degree-`a` piece is the number of coordinates of degree `a`. -/
theorem finrank_grade (a : ℤ) :
    finrank ℂ (S.grade a) = (Finset.univ.filter fun i ↦ S.degree i = a).card := by
  have hli : LinearIndependent ℂ
      fun i : ({i | S.degree i = a} : Set (Fin S.n)) ↦ Pi.basisFun ℂ (Fin S.n) i :=
    (Pi.basisFun ℂ (Fin S.n)).linearIndependent.comp _ Subtype.val_injective
  rw [grade_eq_span, Set.image_eq_range, finrank_span_eq_card hli]
  simp [Fintype.card_subtype]

/-- A grade is zero exactly when no coordinate has that degree. -/
theorem grade_eq_bot_iff (a : ℤ) : S.grade a = ⊥ ↔ ∀ i, S.degree i ≠ a := by
  refine ⟨fun h i hi ↦ ?_, fun h ↦
    (Submodule.eq_bot_iff _).2 fun v hv ↦ funext fun i ↦ mem_grade_iff.1 hv i (h i)⟩
  have hmem := hi ▸ S.single_mem_grade i 1
  rw [h, Submodule.mem_bot] at hmem
  simpa using congrFun hmem i

/-- Only finitely many grades of a coordinate presentation are nonzero. -/
theorem finite_setOf_grade_ne_bot : {a | S.grade a ≠ ⊥}.Finite := by
  refine (Set.finite_range S.degree).subset fun a ha ↦ ?_
  simpa [grade_eq_bot_iff] using ha

/-! ### Constant presentations -/

/-- The presentation with `n` coordinates, all of degree `a`. -/
def constant (n : ℕ) (a : ℤ) : GradedCoordSpace :=
  ⟨n, fun _ ↦ a⟩

@[simp]
theorem n_constant (n : ℕ) (a : ℤ) : (constant n a).n = n :=
  (rfl)

@[simp]
theorem degree_constant (n : ℕ) (a : ℤ) (i : Fin (constant n a).n) :
    (constant n a).degree i = a :=
  (rfl)

/-- The constant presentation in degree `a` is concentrated in degree `a`. -/
@[simp]
theorem grade_constant_self (n : ℕ) (a : ℤ) : (constant n a).grade a = ⊤ :=
  eq_top_iff.2 fun _ _ ↦ mem_grade_iff.2 fun _ hi ↦ absurd rfl hi

/-- The constant presentation in degree `a` vanishes in every other degree. -/
@[simp]
theorem grade_constant_of_ne {n : ℕ} {a b : ℤ} (h : b ≠ a) : (constant n a).grade b = ⊥ :=
  (grade_eq_bot_iff _ _).2 fun _ ↦ h.symm

/-- The constant presentation has dimension `n` in its degree and zero elsewhere. -/
@[simp]
theorem finrank_grade_constant (n : ℕ) (a b : ℤ) :
    finrank ℂ ((constant n a).grade b) = if b = a then n else 0 := by
  split_ifs with h
  · rw [h, grade_constant_self, finrank_top, Module.finrank_fin_fun, n_constant]
  · rw [grade_constant_of_ne h, finrank_bot]

/-! ### Comparison with abstract gradings -/

/-- Every finite-dimensional internal `ℤ`-grading of a complex vector space has a coordinate
presentation: a linear equivalence with the carrier of some `GradedCoordSpace` matching each
piece of the grading with the corresponding grade. -/
theorem exists_linearEquiv_of_isInternal {V : Type*} [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] {𝒱 : ℤ → Submodule ℂ V} (h : DirectSum.IsInternal 𝒱) :
    ∃ (S : GradedCoordSpace) (e : V ≃ₗ[ℂ] S.Carrier),
      ∀ (a : ℤ) (v : V), v ∈ 𝒱 a ↔ e v ∈ S.grade a := by
  classical
  let b := h.collectedBasis fun a ↦ Module.finBasis ℂ (𝒱 a)
  have : Finite (Σ a, Fin (finrank ℂ (𝒱 a))) := Module.Finite.finite_basis b
  let σ := Finite.equivFin (Σ a, Fin (finrank ℂ (𝒱 a)))
  refine ⟨⟨_, fun i ↦ (σ.symm i).1⟩, (b.reindex σ).equivFun, fun a v ↦ ?_⟩
  simp only [mem_grade_iff, Module.Basis.equivFun_apply, Module.Basis.repr_reindex,
    Finsupp.equivMapDomain_apply]
  rw [σ.symm.forall_congr_right (q := fun x ↦ x.1 ≠ a → b.repr v x = 0)]
  refine ⟨fun hv x hx ↦ ?_, fun hv ↦ ?_⟩
  · obtain ⟨c, j⟩ := x
    exact h.collectedBasis_repr_of_mem_ne _ (Ne.symm hx) hv
  · have hspan : v ∈ Submodule.span ℂ (b '' {x | x.1 = a}) :=
      (Module.Basis.mem_span_image _).2 (Finsupp.support_subset_iff.2 hv)
    refine Submodule.span_le.2 ?_ hspan
    rintro _ ⟨x, rfl, rfl⟩
    exact h.collectedBasis_mem _ x

variable {S T} in
/-- A linear equivalence that preserves grade membership in both directions maps each grade onto
the corresponding grade. -/
theorem map_grade_of_mem_grade_iff (e : S.Carrier ≃ₗ[ℂ] T.Carrier)
    (he : ∀ (a : ℤ) (v : S.Carrier), v ∈ S.grade a ↔ e v ∈ T.grade a) (a : ℤ) :
    (S.grade a).map (e : S.Carrier →ₗ[ℂ] T.Carrier) = T.grade a := by
  ext w
  refine ⟨?_, fun hw ↦ ⟨e.symm w, by simpa [he] using hw, by simp⟩⟩
  rintro ⟨v, hv, rfl⟩
  exact (he a v).1 hv

/-- Two coordinate presentations admit a grade-preserving linear equivalence exactly when their
grades have equal dimensions. -/
theorem exists_linearEquiv_iff_finrank_grade_eq :
    (∃ e : S.Carrier ≃ₗ[ℂ] T.Carrier, ∀ (a : ℤ) (v : S.Carrier), v ∈ S.grade a ↔ e v ∈ T.grade a) ↔
      ∀ a, finrank ℂ (S.grade a) = finrank ℂ (T.grade a) := by
  constructor
  · rintro ⟨e, he⟩ a
    rw [← e.finrank_map_eq, map_grade_of_mem_grade_iff e he]
  · intro h
    simp only [finrank_grade] at h
    -- Equal fiber sizes give a degree-preserving bijection of the coordinates.
    obtain ⟨σ, hσ⟩ := Function.exists_equiv_of_occCount_eq (u := S.degree) (v := T.degree)
      fun a ↦ by rw [Function.occCount_eq_card_filter, Function.occCount_eq_card_filter, h a]
    refine ⟨LinearEquiv.funCongrLeft ℂ ℂ σ.symm, fun a v ↦ ?_⟩
    simp only [mem_grade_iff, LinearEquiv.funCongrLeft_apply, LinearMap.funLeft_apply]
    rw [← σ.forall_congr_right]
    simp [← hσ]

end GradedCoordSpace

end TauCeti

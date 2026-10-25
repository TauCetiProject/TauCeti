/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.IntegralLattice.Isometry.Class
public import TauCeti.LinearAlgebra.IntegralLattice.Isometry.Group
import TauCeti.LinearAlgebra.Determinant.Basic

/-!
# Proper isometries and proper classes of integral lattices

An isometry between two integral lattices in the same rational space `V` is *proper* when its
ambient linear equivalence of `V` has positive determinant, that is, when it preserves the
orientations of `V`. For lattices carrying the same nondegenerate form this is the usual
condition `det = 1`, and for a self-isometry it is membership in `SO(L)`
(`TauCeti.IntegralLattice.Isometry.isProper_iff_det_eq_one`). Since the lattices in `V` may carry
different forms, the ambient determinant of an isometry can be any nonzero rational number, and
positivity is the condition that is stable under composition and inversion.

Proper isometry is an equivalence relation, and its classes are the *proper classes* `cls⁺ L`,
forming `ProperIsometryQuotient V`. Every proper class lies in a class, and the class of a lattice
`M` of positive rank is the union of the proper classes of `M` and of `M` transported along any
orientation-reversing automorphism of `V`. These two proper classes coincide exactly when `M` has
an improper self-isometry, that is, when `SO(M)` has index two in `O(M)`. So the number of proper
classes in the class of `M` times the index of `SO(M)` is always `2`
(`TauCeti.IntegralLattice.natCard_fiber_toIsometryQuotient_mul_index`).

## Main definitions

* `TauCeti.IntegralLattice.Isometry.IsProper`: an isometry whose ambient determinant is positive.
* `TauCeti.IntegralLattice.ProperIsometryQuotient`: the proper classes of integral lattices in `V`.
* `TauCeti.IntegralLattice.properIsometryClass`: the proper class `cls⁺ L` of a lattice.
* `TauCeti.IntegralLattice.ProperIsometryQuotient.toIsometryQuotient`: the class containing a
  proper class.
* `TauCeti.IntegralLattice.properIsometryQuotientEquiv`: transport of proper classes along a
  rational linear equivalence.

## Main results

* `TauCeti.IntegralLattice.Isometry.isProper_trans_iff`: a composite of isometries is proper
  exactly when both factors are proper or both are improper.
* `TauCeti.IntegralLattice.properIsometryClass_transport_eq_iff`: transporting `M` along an
  orientation-reversing automorphism keeps its proper class exactly when `M` has an improper
  self-isometry.
* `TauCeti.IntegralLattice.natCard_fiber_toIsometryQuotient_mul_index`: in positive rank, the class
  of `M` contains `2 / [O(M) : SO(M)]` proper classes.

## References

* O. T. O'Meara, *Introduction to Quadratic Forms*, §102A, for classes and proper classes of
  lattices.
* J. W. S. Cassels, *Rational Quadratic Forms*, Chapter 9, §1.
-/

public section

open Module

namespace TauCeti.IntegralLattice

universe u v

variable {V : Type u} [AddCommGroup V] [Module ℚ V]

namespace Isometry

variable {L M N : IntegralLattice V}

/-- The ambient determinant of a composite of isometries is the product of the ambient
determinants. -/
theorem det_toLinearMap_trans (e : Isometry L M) (f : Isometry M N) :
    LinearMap.det (((e.trans f : Isometry L N) : V ≃ₗ[ℚ] V) : V →ₗ[ℚ] V) =
      LinearMap.det ((f : V ≃ₗ[ℚ] V) : V →ₗ[ℚ] V) *
        LinearMap.det ((e : V ≃ₗ[ℚ] V) : V →ₗ[ℚ] V) := by
  rw [← LinearMap.det_comp]
  congr 1
  ext x
  simp

/-- The ambient determinant of the inverse of an isometry is the inverse of its ambient
determinant. -/
theorem det_toLinearMap_symm (e : Isometry L M) :
    LinearMap.det ((e.symm : V ≃ₗ[ℚ] V) : V →ₗ[ℚ] V) =
      (LinearMap.det ((e : V ≃ₗ[ℚ] V) : V →ₗ[ℚ] V))⁻¹ := by
  rw [← LinearEquiv.det_coe_symm]
  congr 1
  ext x
  simp [coe_symm]

/-- An isometry between lattices in the same rational space is *proper* when its ambient linear
equivalence has positive determinant, that is, when it preserves the orientations of `V`. -/
def IsProper (e : Isometry L M) : Prop :=
  0 < LinearMap.det ((e : V ≃ₗ[ℚ] V) : V →ₗ[ℚ] V)

/-- Unfolding `IsProper`: the ambient determinant is positive. -/
theorem isProper_def {e : Isometry L M} :
    e.IsProper ↔ 0 < LinearMap.det ((e : V ≃ₗ[ℚ] V) : V →ₗ[ℚ] V) :=
  Iff.rfl

/-- An isometry is improper exactly when its ambient determinant is negative. -/
theorem not_isProper_iff {e : Isometry L M} :
    ¬e.IsProper ↔ LinearMap.det ((e : V ≃ₗ[ℚ] V) : V →ₗ[ℚ] V) < 0 := by
  rw [isProper_def, not_lt, le_iff_lt_or_eq,
    or_iff_left (LinearEquiv.isUnit_det' (e : V ≃ₗ[ℚ] V)).ne_zero]

/-- The identity isometry is proper. -/
@[simp]
theorem isProper_refl (L : IntegralLattice V) : (refl L).IsProper := by
  have h : ((refl L : V ≃ₗ[ℚ] V) : V →ₗ[ℚ] V) = LinearMap.id := LinearMap.ext fun x ↦ by simp
  rw [isProper_def, h, LinearMap.det_id]
  exact one_pos

/-- A composite of isometries is proper exactly when both factors are proper or both are
improper. -/
theorem isProper_trans_iff {e : Isometry L M} {f : Isometry M N} :
    (e.trans f).IsProper ↔ (e.IsProper ↔ f.IsProper) := by
  have he := (LinearEquiv.isUnit_det' (e : V ≃ₗ[ℚ] V)).ne_zero
  have hf := (LinearEquiv.isUnit_det' (f : V ≃ₗ[ℚ] V)).ne_zero
  rw [isProper_def, isProper_def, isProper_def, det_toLinearMap_trans]
  rcases he.lt_or_gt with he | he <;> rcases hf.lt_or_gt with hf | hf <;>
    simp [mul_pos_iff, he, hf, he.not_gt, hf.not_gt]

/-- A composite of proper isometries is proper. -/
theorem IsProper.trans {e : Isometry L M} {f : Isometry M N} (he : e.IsProper)
    (hf : f.IsProper) : (e.trans f).IsProper :=
  isProper_trans_iff.mpr (iff_of_true he hf)

/-- The inverse of an isometry is proper exactly when the isometry is. -/
@[simp]
theorem isProper_symm_iff {e : Isometry L M} : e.symm.IsProper ↔ e.IsProper := by
  rw [isProper_def, isProper_def, det_toLinearMap_symm, inv_pos]

/-- The inverse of a proper isometry is proper. -/
theorem IsProper.symm {e : Isometry L M} (he : e.IsProper) : e.symm.IsProper :=
  isProper_symm_iff.mpr he

/-- A self-isometry is proper exactly when its determinant is `1`, that is, when it lies in
`SO(L)`. -/
theorem isProper_iff_det_eq_one {e : Isometry L L} : e.IsProper ↔ det L e = 1 := by
  rw [isProper_def, ← coe_det_eq_det_toLinearMap]
  rcases det_eq_one_or_neg_one e with h | h <;> simp [h]

/-- A self-isometry is proper exactly when it lies in `SO(L)`. -/
theorem isProper_iff_mem_specialOrthogonalGroup {e : Isometry L L} :
    e.IsProper ↔ e ∈ specialOrthogonalGroup L := by
  rw [isProper_iff_det_eq_one, mem_specialOrthogonalGroup_iff]

/-- A self-isometry is improper exactly when its determinant is `-1`. -/
theorem not_isProper_iff_det_eq_neg_one {e : Isometry L L} : ¬e.IsProper ↔ det L e = -1 := by
  rw [isProper_iff_det_eq_one]
  rcases det_eq_one_or_neg_one e with h | h <;> simp [h]

/-- The canonical isometry to the transport of a lattice along an automorphism `g` of `V` is proper
exactly when `g` has positive determinant. -/
@[simp]
theorem isProper_transportIsometry_iff (L : IntegralLattice V) {g : V ≃ₗ[ℚ] V} :
    (L.transportIsometry g).IsProper ↔ 0 < LinearMap.det (g : V →ₗ[ℚ] V) := by
  rw [isProper_def]
  congr! 2
  ext x
  simp

end Isometry

section ProperIsometryQuotient

variable (V) in
/-- Proper isometry of integral lattices in a fixed rational space, as an equivalence relation. -/
def properIsometrySetoid : Setoid (IntegralLattice V) where
  r L M := ∃ e : Isometry L M, e.IsProper
  iseqv := ⟨fun L ↦ ⟨.refl L, Isometry.isProper_refl L⟩, fun ⟨e, he⟩ ↦ ⟨e.symm, he.symm⟩,
    fun ⟨e, he⟩ ⟨f, hf⟩ ↦ ⟨e.trans f, he.trans hf⟩⟩

/-- Two lattices are related by `properIsometrySetoid` exactly when a proper isometry joins
them. -/
theorem properIsometrySetoid_apply {L M : IntegralLattice V} :
    properIsometrySetoid V L M ↔ ∃ e : Isometry L M, e.IsProper :=
  Iff.rfl

variable (V) in
/-- The proper classes of integral lattices in a rational space `V`. -/
abbrev ProperIsometryQuotient : Type u := Quotient (properIsometrySetoid V)

/-- The proper class `cls⁺ L` of an integral lattice. -/
def properIsometryClass (L : IntegralLattice V) : ProperIsometryQuotient V :=
  Quotient.mk _ L

/-- Two lattices have the same proper class exactly when a proper isometry joins them. -/
@[simp]
theorem properIsometryClass_eq_properIsometryClass_iff {L M : IntegralLattice V} :
    L.properIsometryClass = M.properIsometryClass ↔ ∃ e : Isometry L M, e.IsProper :=
  Quotient.eq

/-- Lattices joined by a proper isometry have the same proper class. -/
theorem Isometry.IsProper.properIsometryClass_eq {L M : IntegralLattice V} {e : Isometry L M}
    (he : e.IsProper) : L.properIsometryClass = M.properIsometryClass :=
  properIsometryClass_eq_properIsometryClass_iff.mpr ⟨e, he⟩

/-- Every proper class is the proper class of a lattice. -/
theorem properIsometryClass_surjective :
    Function.Surjective (properIsometryClass : IntegralLattice V → ProperIsometryQuotient V) :=
  Quotient.mk_surjective

/-- A chosen representative of a proper class has that proper class. -/
@[simp]
theorem properIsometryClass_out (c : ProperIsometryQuotient V) : c.out.properIsometryClass = c :=
  Quotient.out_eq c

/-- The class containing a proper class. -/
def ProperIsometryQuotient.toIsometryQuotient : ProperIsometryQuotient V → IsometryQuotient V :=
  Quotient.lift isometryClass fun _ _ ⟨e, _⟩ ↦ e.isometryClass_eq

/-- The proper class of `L` lies in the class of `L`. -/
@[simp]
theorem toIsometryQuotient_properIsometryClass (L : IntegralLattice V) :
    L.properIsometryClass.toIsometryQuotient = L.isometryClass :=
  (rfl)

/-- Every class contains a proper class. -/
theorem ProperIsometryQuotient.toIsometryQuotient_surjective :
    Function.Surjective (toIsometryQuotient : ProperIsometryQuotient V → IsometryQuotient V) :=
  fun c ↦ ⟨c.out.properIsometryClass, by simp⟩

/-- The representative of the class of `M` has an isometry group of the cardinality of `O(M)`. -/
theorem natCard_isometry_isometryClass_out (M : IntegralLattice V) :
    Nat.card (Isometry M.isometryClass.out M.isometryClass.out) = Nat.card (Isometry M M) := by
  obtain ⟨e⟩ := isometryClass_eq_isometryClass_iff.mp (isometryClass_out M.isometryClass)
  exact e.natCard_eq

/-- The representative of the proper class of `M` has a special isometry group of the cardinality
of `SO(M)`. -/
theorem natCard_specialOrthogonalGroup_properIsometryClass_out (M : IntegralLattice V) :
    Nat.card (specialOrthogonalGroup M.properIsometryClass.out) =
      Nat.card (specialOrthogonalGroup M) := by
  obtain ⟨e, -⟩ := properIsometryClass_eq_properIsometryClass_iff.mp
    (properIsometryClass_out M.properIsometryClass)
  exact e.natCard_specialOrthogonalGroup_eq

/-- The representatives of a proper class and of the class containing it have special isometry
groups of the same cardinality. -/
theorem ProperIsometryQuotient.natCard_specialOrthogonalGroup_out_toIsometryQuotient
    (c : ProperIsometryQuotient V) :
    Nat.card (specialOrthogonalGroup c.out) =
      Nat.card (specialOrthogonalGroup c.toIsometryQuotient.out) := by
  have h : c.toIsometryQuotient.out.isometryClass = c.out.isometryClass := by
    rw [isometryClass_out, ← toIsometryQuotient_properIsometryClass, properIsometryClass_out]
  obtain ⟨e⟩ := isometryClass_eq_isometryClass_iff.mp h
  exact e.natCard_specialOrthogonalGroup_eq.symm

end ProperIsometryQuotient

section Transport

variable {W : Type v} [AddCommGroup W] [Module ℚ W]

/-- Transporting an isometry along a rational linear equivalence `f : V ≃ W` preserves
properness: its ambient map is conjugated by `f`, which does not change the determinant. -/
theorem Isometry.isProper_transport_iff (f : V ≃ₗ[ℚ] W) {M N : IntegralLattice V}
    {e : Isometry M N} :
    (((M.transportIsometry f).symm.trans e).trans (N.transportIsometry f)).IsProper ↔
      e.IsProper := by
  have h (x : W) : (M.transportIsometry f).symm x = f.symm x := by
    simpa using (M.transportIsometry f).symm_apply_apply (f.symm x)
  rw [isProper_def, isProper_def, ← LinearMap.det_conj _ f]
  congr! 2
  ext x
  simp [h]

/-- Transport along a rational linear equivalence `V ≃ W` identifies the proper classes of
integral lattices in `V` with those in `W`. -/
noncomputable def properIsometryQuotientEquiv (f : V ≃ₗ[ℚ] W) :
    ProperIsometryQuotient V ≃ ProperIsometryQuotient W where
  toFun := Quotient.map (·.transport f) fun _ _ ⟨e, he⟩ ↦
    ⟨_, (Isometry.isProper_transport_iff f).mpr he⟩
  invFun := Quotient.map (·.transport f.symm) fun _ _ ⟨e, he⟩ ↦
    ⟨_, (Isometry.isProper_transport_iff f.symm).mpr he⟩
  left_inv c := by
    obtain ⟨M, rfl⟩ := properIsometryClass_surjective c
    let e := (M.transportIsometry f).trans ((M.transport f).transportIsometry f.symm)
    have h : ((e : V ≃ₗ[ℚ] V) : V →ₗ[ℚ] V) = LinearMap.id := LinearMap.ext fun x ↦ by simp [e]
    refine (Isometry.IsProper.properIsometryClass_eq (e := e) ?_).symm
    rw [Isometry.isProper_def, h, LinearMap.det_id]
    exact one_pos
  right_inv c := by
    obtain ⟨M, rfl⟩ := properIsometryClass_surjective c
    let e := (M.transportIsometry f.symm).trans ((M.transport f.symm).transportIsometry f)
    have h : ((e : W ≃ₗ[ℚ] W) : W →ₗ[ℚ] W) = LinearMap.id := LinearMap.ext fun x ↦ by simp [e]
    refine (Isometry.IsProper.properIsometryClass_eq (e := e) ?_).symm
    rw [Isometry.isProper_def, h, LinearMap.det_id]
    exact one_pos

/-- `properIsometryQuotientEquiv f` sends the proper class of `M` to the proper class of its
transport along `f`. -/
@[simp]
theorem properIsometryQuotientEquiv_properIsometryClass (f : V ≃ₗ[ℚ] W) (M : IntegralLattice V) :
    properIsometryQuotientEquiv f M.properIsometryClass = (M.transport f).properIsometryClass :=
  (rfl)

/-- Transport of proper classes is compatible with transport of classes. -/
@[simp]
theorem toIsometryQuotient_properIsometryQuotientEquiv (f : V ≃ₗ[ℚ] W)
    (c : ProperIsometryQuotient V) :
    (properIsometryQuotientEquiv f c).toIsometryQuotient =
      isometryQuotientEquiv f c.toIsometryQuotient := by
  obtain ⟨M, rfl⟩ := properIsometryClass_surjective c
  rw [properIsometryQuotientEquiv_properIsometryClass, toIsometryQuotient_properIsometryClass,
    toIsometryQuotient_properIsometryClass, isometryQuotientEquiv_isometryClass]

end Transport

section Fiber

open ProperIsometryQuotient

variable {M : IntegralLattice V} {g : V ≃ₗ[ℚ] V}

/-- Transporting `M` along an orientation-reversing automorphism of `V` keeps its proper class
exactly when `M` has an improper self-isometry. -/
theorem properIsometryClass_transport_eq_iff (hg : LinearMap.det (g : V →ₗ[ℚ] V) < 0) :
    (M.transport g).properIsometryClass = M.properIsometryClass ↔
      ∃ e : Isometry M M, Isometry.det M e = -1 := by
  have ht : ¬(M.transportIsometry g).IsProper := by
    rw [Isometry.isProper_transportIsometry_iff, not_lt]
    exact hg.le
  rw [eq_comm, properIsometryClass_eq_properIsometryClass_iff]
  refine ⟨fun ⟨f, hf⟩ ↦ ⟨f.trans (M.transportIsometry g).symm, ?_⟩,
    fun ⟨e, he⟩ ↦ ⟨e.trans (M.transportIsometry g), ?_⟩⟩
  · rw [← Isometry.not_isProper_iff_det_eq_neg_one, Isometry.isProper_trans_iff,
      Isometry.isProper_symm_iff]
    tauto
  · rw [Isometry.isProper_trans_iff, ← Isometry.not_isProper_iff_det_eq_neg_one] at *
    tauto

/-- The class of `M` consists of the proper class of `M` and the proper class of its transport
along an orientation-reversing automorphism of `V`. -/
theorem toIsometryQuotient_eq_isometryClass_iff (hg : LinearMap.det (g : V →ₗ[ℚ] V) < 0)
    {c : ProperIsometryQuotient V} :
    c.toIsometryQuotient = M.isometryClass ↔
      c = M.properIsometryClass ∨ c = (M.transport g).properIsometryClass := by
  obtain ⟨N, rfl⟩ := properIsometryClass_surjective c
  have ht : ¬(M.transportIsometry g).IsProper := by
    rw [Isometry.isProper_transportIsometry_iff, not_lt]
    exact hg.le
  rw [toIsometryQuotient_properIsometryClass, isometryClass_eq_isometryClass_iff,
    properIsometryClass_eq_properIsometryClass_iff, properIsometryClass_eq_properIsometryClass_iff]
  refine ⟨fun ⟨e⟩ ↦ ?_, ?_⟩
  · by_cases he : e.IsProper
    · exact Or.inl ⟨e, he⟩
    · refine Or.inr ⟨e.trans (M.transportIsometry g), ?_⟩
      rw [Isometry.isProper_trans_iff]
      tauto
  · rintro (⟨e, -⟩ | ⟨e, -⟩)
    · exact ⟨e⟩
    · exact ⟨e.trans (M.transportIsometry g).symm⟩

/-- **The proper classes in a class.** For a lattice `M` of positive rank, the number of proper
classes in the class of `M` times the index of `SO(M)` in `O(M)` is `2`: the class is one proper
class when `M` has an improper self-isometry, and two proper classes otherwise. -/
theorem natCard_fiber_toIsometryQuotient_mul_index (hM : 0 < finrank ℤ M) :
    Nat.card {c : ProperIsometryQuotient V // c.toIsometryQuotient = M.isometryClass} *
      (specialOrthogonalGroup M).index = 2 := by
  classical
  have : FiniteDimensional ℚ V := M.finiteDimensional
  have : Nontrivial V := Module.nontrivial_of_finrank_pos (M.finrank_carrier ▸ hM)
  obtain ⟨g, hg⟩ := LinearEquiv.exists_det_eq_neg_one (R := ℚ) (V := V)
  have hg' : LinearMap.det (g : V →ₗ[ℚ] V) < 0 := by
    rw [← LinearEquiv.coe_det, hg]
    norm_num
  have hfib : {c : ProperIsometryQuotient V | c.toIsometryQuotient = M.isometryClass} =
      {M.properIsometryClass, (M.transport g).properIsometryClass} := by
    ext c
    exact toIsometryQuotient_eq_isometryClass_iff hg'
  rw [← Set.coe_ofPred, hfib, Nat.card_coe_set_eq]
  rcases index_specialOrthogonalGroup_eq_one_or_two M with hi | hi
  · have hne : M.properIsometryClass ≠ (M.transport g).properIsometryClass := by
      rw [ne_comm, Ne, properIsometryClass_transport_eq_iff hg',
        ← index_specialOrthogonalGroup_eq_two_iff, hi]
      norm_num
    rw [Set.ncard_pair hne, hi]
  · have heq : M.properIsometryClass = (M.transport g).properIsometryClass := by
      rw [eq_comm, properIsometryClass_transport_eq_iff hg',
        ← index_specialOrthogonalGroup_eq_two_iff, hi]
    rw [heq, Set.pair_eq_singleton, Set.ncard_singleton, hi]

/-- In positive rank, the number of proper classes in the class of `M` times `|O(M)|` is twice
`|SO(M)|`, with the convention that an infinite group has cardinality `0`. -/
theorem natCard_fiber_toIsometryQuotient_mul_natCard_isometry (hM : 0 < finrank ℤ M) :
    Nat.card {c : ProperIsometryQuotient V // c.toIsometryQuotient = M.isometryClass} *
      Nat.card (Isometry M M) = 2 * Nat.card (specialOrthogonalGroup M) := by
  rw [← (specialOrthogonalGroup M).card_mul_index, ← natCard_fiber_toIsometryQuotient_mul_index hM]
  ring

/-- In rank zero every isometry is proper, so the class of `M` is a single proper class. -/
theorem subsingleton_fiber_toIsometryQuotient_of_finrank_eq_zero (hM : finrank ℤ M = 0) :
    {c : ProperIsometryQuotient V | c.toIsometryQuotient = M.isometryClass}.Subsingleton := by
  intro c hc d hd
  obtain ⟨N, rfl⟩ := properIsometryClass_surjective c
  obtain ⟨N', rfl⟩ := properIsometryClass_surjective d
  rw [Set.mem_ofPred_eq, toIsometryQuotient_properIsometryClass,
    isometryClass_eq_isometryClass_iff] at hc hd
  obtain ⟨e⟩ := hc
  obtain ⟨e'⟩ := hd
  have : FiniteDimensional ℚ V := M.finiteDimensional
  refine Isometry.IsProper.properIsometryClass_eq (e := e.trans e'.symm) ?_
  rw [Isometry.isProper_def, LinearMap.det_eq_one_of_finrank_eq_zero (M.finrank_carrier ▸ hM)]
  exact one_pos

/-- Every class contains only finitely many proper classes: at most two in positive rank, and one
in rank zero. -/
theorem finite_fiber_toIsometryQuotient (M : IntegralLattice V) :
    {c : ProperIsometryQuotient V | c.toIsometryQuotient = M.isometryClass}.Finite := by
  rcases (finrank ℤ M).eq_zero_or_pos with hM | hM
  · exact (subsingleton_fiber_toIsometryQuotient_of_finrank_eq_zero hM).finite
  · have h := natCard_fiber_toIsometryQuotient_mul_index hM
    have : Finite {c : ProperIsometryQuotient V // c.toIsometryQuotient = M.isometryClass} :=
      Nat.finite_of_card_ne_zero fun h₀ ↦ by simp [h₀] at h
    exact Set.toFinite _

end Fiber

end TauCeti.IntegralLattice

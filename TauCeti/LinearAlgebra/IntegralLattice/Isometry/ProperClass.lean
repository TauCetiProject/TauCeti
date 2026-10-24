/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.IntegralLattice.Isometry.Class
public import TauCeti.LinearAlgebra.IntegralLattice.Isometry.Group
public import Mathlib.Data.Set.Card
import TauCeti.LinearAlgebra.Determinant.Basic

/-!
# Proper isometry classes of integral lattices

An isometry `e : L ≅ M` between two integral lattices in the same rational space `V` is
**proper** when the rational linear automorphism of `V` underlying it has positive determinant.
For a self-isometry this is the condition `det = 1` defining `SO(L)`
(`TauCeti.IntegralLattice.Isometry.isProper_iff_det_eq_one`). Each lattice of `V` carries its own
form, so the ambient determinant of an isometry between two different lattices need not be `±1`;
only its sign is used. The lattices of `V` modulo proper isometry form the proper classes
`ProperIsometryQuotient V`, which map onto the isometry classes.

In positive rank every isometry class is the image of one or of two proper classes. Choose a
rational automorphism `f` of `V` of negative determinant. Every lattice isometric to `M` is
properly isometric to `M` or to its transport along `f`, and these two proper classes coincide
exactly when `M` has an improper automorphism, that is, when `[O(M) : SO(M)] = 2`. The number of
proper classes over the class of `M` is therefore `2 / [O(M) : SO(M)]`
(`TauCeti.IntegralLattice.ncard_preimage_toIsometryQuotient_mul_index`). This is the input for
comparing the proper mass of a genus with its mass.

## Main definitions

* `TauCeti.IntegralLattice.Isometry.IsProper`: an isometry of positive ambient determinant.
* `TauCeti.IntegralLattice.ProperIsometryQuotient`: the proper classes of integral lattices in `V`.
* `TauCeti.IntegralLattice.properIsometryClass`: the proper class `cls⁺ L` of a lattice.
* `TauCeti.IntegralLattice.ProperIsometryQuotient.toIsometryQuotient`: the map `cls⁺ L ↦ cls L`.
* `TauCeti.IntegralLattice.properIsometryQuotientEquiv`: transport of proper classes along an
  ambient linear equivalence `V ≃ W`.

## Main results

* `TauCeti.IntegralLattice.Isometry.isProper_iff_det_eq_one`: a self-isometry is proper exactly
  when it lies in `SO(L)`.
* `TauCeti.IntegralLattice.Isometry.isProper_symm_iff` and
  `TauCeti.IntegralLattice.Isometry.isProper_trans_iff`: the inverse of an isometry is proper
  exactly when it is, and a composite is proper exactly when both or neither factor is.
* `TauCeti.IntegralLattice.properIsometryClass_eq_properIsometryClass_iff`: two lattices have the
  same proper class exactly when they are properly isometric.
* `TauCeti.IntegralLattice.ncard_preimage_toIsometryQuotient_mul_index`: in positive rank, the
  number of proper classes over the class of `M`, times `[O(M) : SO(M)]`, is `2`.
* `TauCeti.IntegralLattice.finite_preimage_toIsometryQuotient`: each class is the image of finitely
  many proper classes.

## References

* O. T. O'Meara, *Introduction to Quadratic Forms*, §102A, for classes and proper classes.
* J. H. Conway and N. J. A. Sloane, *Low-dimensional lattices. IV. The mass formula*,
  Proc. R. Soc. Lond. A 419 (1988), §2.
-/

public section

open Module

namespace TauCeti.IntegralLattice

universe u

variable {V : Type u} [AddCommGroup V] [Module ℚ V] {L M N : IntegralLattice V}

namespace Isometry

/-- The ambient determinant of a composite isometry is the product of the ambient
determinants. -/
theorem det_trans_toLinearMap (e : Isometry L M) (f : Isometry M N) :
    LinearMap.det (((e.trans f : Isometry L N) : V ≃ₗ[ℚ] V) : V →ₗ[ℚ] V) =
      LinearMap.det ((f : V ≃ₗ[ℚ] V) : V →ₗ[ℚ] V) *
        LinearMap.det ((e : V ≃ₗ[ℚ] V) : V →ₗ[ℚ] V) := by
  rw [toLinearEquiv_trans, LinearEquiv.coe_trans, LinearMap.det_comp]

/-- The ambient determinant of the inverse isometry is the inverse of the ambient determinant. -/
theorem det_symm_toLinearMap (e : Isometry L M) :
    LinearMap.det ((e.symm : V ≃ₗ[ℚ] V) : V →ₗ[ℚ] V) =
      (LinearMap.det ((e : V ≃ₗ[ℚ] V) : V →ₗ[ℚ] V))⁻¹ := by
  rw [toLinearEquiv_symm, ← LinearEquiv.coe_inv_det, Units.val_inv_eq_inv_val,
    LinearEquiv.coe_det]

/-- An isometry has nonzero ambient determinant. -/
theorem det_toLinearMap_ne_zero (e : Isometry L M) :
    LinearMap.det ((e : V ≃ₗ[ℚ] V) : V →ₗ[ℚ] V) ≠ 0 :=
  (e : V ≃ₗ[ℚ] V).isUnit_det'.ne_zero

/-- An isometry between two integral lattices in the same rational space is **proper** when the
rational linear automorphism underlying it has positive determinant. -/
def IsProper (e : Isometry L M) : Prop :=
  0 < LinearMap.det ((e : V ≃ₗ[ℚ] V) : V →ₗ[ℚ] V)

theorem isProper_def (e : Isometry L M) :
    e.IsProper ↔ 0 < LinearMap.det ((e : V ≃ₗ[ℚ] V) : V →ₗ[ℚ] V) :=
  Iff.rfl

/-- An isometry which is not proper has negative ambient determinant. -/
theorem not_isProper_iff (e : Isometry L M) :
    ¬ e.IsProper ↔ LinearMap.det ((e : V ≃ₗ[ℚ] V) : V →ₗ[ℚ] V) < 0 := by
  rw [isProper_def, not_lt]
  exact ⟨fun h ↦ h.lt_of_ne (det_toLinearMap_ne_zero e), le_of_lt⟩

/-- The identity isometry is proper. -/
theorem isProper_refl (L : IntegralLattice V) : (refl L).IsProper := by
  rw [isProper_def, toLinearEquiv_refl, LinearEquiv.refl_toLinearMap, LinearMap.det_id]
  exact one_pos

/-- The inverse of a proper isometry is proper. -/
theorem IsProper.symm {e : Isometry L M} (he : e.IsProper) : e.symm.IsProper := by
  rw [isProper_def, det_symm_toLinearMap]
  exact inv_pos.mpr he

/-- A composite of proper isometries is proper. -/
theorem IsProper.trans {e : Isometry L M} {f : Isometry M N} (he : e.IsProper)
    (hf : f.IsProper) : (e.trans f).IsProper := by
  rw [isProper_def, det_trans_toLinearMap]
  exact mul_pos hf he

/-- An isometry is proper exactly when its inverse is. -/
@[simp]
theorem isProper_symm_iff {e : Isometry L M} : e.symm.IsProper ↔ e.IsProper :=
  ⟨fun he ↦ e.symm_symm ▸ he.symm, IsProper.symm⟩

/-- A composite of two isometries is proper exactly when both or neither of them are proper: a
proper and an improper isometry compose to an improper one, and two improper isometries compose
to a proper one. -/
theorem isProper_trans_iff {e : Isometry L M} {f : Isometry M N} :
    (e.trans f).IsProper ↔ (e.IsProper ↔ f.IsProper) := by
  rw [isProper_def, det_trans_toLinearMap, isProper_def, isProper_def]
  rcases (det_toLinearMap_ne_zero e).lt_or_gt with he | he <;>
    rcases (det_toLinearMap_ne_zero f).lt_or_gt with hf | hf
  · simp [mul_pos_of_neg_of_neg hf he, he.not_gt, hf.not_gt]
  · simp [(mul_neg_of_pos_of_neg hf he).not_gt, he.not_gt, hf]
  · simp [(mul_neg_of_neg_of_pos hf he).not_gt, he, hf.not_gt]
  · simp [mul_pos hf he, he, hf]

/-- A self-isometry is proper exactly when its determinant is `1`. -/
theorem isProper_iff_det_eq_one (g : Isometry L L) : g.IsProper ↔ det L g = 1 := by
  rw [isProper_def, det_toLinearMap]
  rcases det_eq_one_or_neg_one g with h | h <;> simp [h]

end Isometry

/-- A self-isometry lies in `SO(L)` exactly when it is proper. -/
theorem mem_specialOrthogonalGroup_iff_isProper {g : Isometry L L} :
    g ∈ specialOrthogonalGroup L ↔ g.IsProper := by
  rw [mem_specialOrthogonalGroup_iff, Isometry.isProper_iff_det_eq_one]

section ProperIsometryQuotient

variable (V) in
/-- Proper isometry of integral lattices in a fixed rational space, as an equivalence relation. -/
def properIsometrySetoid : Setoid (IntegralLattice V) where
  r L M := ∃ e : Isometry L M, e.IsProper
  iseqv := ⟨fun L ↦ ⟨Isometry.refl L, Isometry.isProper_refl L⟩, fun ⟨e, he⟩ ↦ ⟨e.symm, he.symm⟩,
    fun ⟨e, he⟩ ⟨f, hf⟩ ↦ ⟨e.trans f, he.trans hf⟩⟩

/-- Two lattices are related by `properIsometrySetoid` exactly when they are properly
isometric. -/
theorem properIsometrySetoid_apply :
    properIsometrySetoid V L M ↔ ∃ e : Isometry L M, e.IsProper :=
  Iff.rfl

variable (V) in
/-- The proper classes of integral lattices in a rational space `V`. -/
abbrev ProperIsometryQuotient : Type u := Quotient (properIsometrySetoid V)

/-- The proper class `cls⁺ L` of an integral lattice. -/
def properIsometryClass (L : IntegralLattice V) : ProperIsometryQuotient V :=
  Quotient.mk _ L

/-- Two lattices have the same proper class exactly when they are properly isometric. -/
@[simp]
theorem properIsometryClass_eq_properIsometryClass_iff :
    L.properIsometryClass = M.properIsometryClass ↔ ∃ e : Isometry L M, e.IsProper :=
  Quotient.eq

/-- Properly isometric lattices have the same proper class. -/
theorem Isometry.IsProper.properIsometryClass_eq {e : Isometry L M} (he : e.IsProper) :
    L.properIsometryClass = M.properIsometryClass :=
  properIsometryClass_eq_properIsometryClass_iff.mpr ⟨e, he⟩

/-- Every proper class is the proper class of a lattice. -/
theorem properIsometryClass_surjective :
    Function.Surjective (properIsometryClass : IntegralLattice V → ProperIsometryQuotient V) :=
  Quotient.mk_surjective

/-- A chosen representative of a proper class has that proper class. -/
@[simp]
theorem properIsometryClass_out (c : ProperIsometryQuotient V) : c.out.properIsometryClass = c :=
  Quotient.out_eq c

/-- The isometry class of a proper class: `cls⁺ L ↦ cls L`. -/
def ProperIsometryQuotient.toIsometryQuotient :
    ProperIsometryQuotient V → IsometryQuotient V :=
  Quotient.lift isometryClass fun _ _ ⟨e, _⟩ ↦ e.isometryClass_eq

@[simp]
theorem toIsometryQuotient_properIsometryClass (L : IntegralLattice V) :
    L.properIsometryClass.toIsometryQuotient = L.isometryClass :=
  (rfl)

theorem ProperIsometryQuotient.toIsometryQuotient_surjective :
    Function.Surjective (toIsometryQuotient : ProperIsometryQuotient V → IsometryQuotient V) := by
  intro c
  obtain ⟨L, rfl⟩ := isometryClass_surjective c
  exact ⟨L.properIsometryClass, toIsometryQuotient_properIsometryClass L⟩

/-- The representative of a proper class is isometric to the representative of its class. -/
theorem ProperIsometryQuotient.nonempty_isometry_out (d : ProperIsometryQuotient V) :
    Nonempty (Isometry d.out d.toIsometryQuotient.out) := by
  rw [← isometryClass_eq_isometryClass_iff, isometryClass_out, ← properIsometryClass_out d,
    toIsometryQuotient_properIsometryClass, properIsometryClass_out]

end ProperIsometryQuotient

section Fibre

/-- Fix an isometry `t : M ≅ M'` with negative ambient determinant. Every lattice isometric to
`M` is properly isometric to `M` or to `M'`. -/
private theorem preimage_toIsometryQuotient_eq_pair {M' : IntegralLattice V} (t : Isometry M M')
    (ht : ¬ t.IsProper) :
    ProperIsometryQuotient.toIsometryQuotient ⁻¹' {M.isometryClass} =
      {M.properIsometryClass, M'.properIsometryClass} := by
  ext c
  obtain ⟨N, rfl⟩ := properIsometryClass_surjective c
  simp only [Set.mem_preimage, toIsometryQuotient_properIsometryClass, Set.mem_singleton_iff,
    isometryClass_eq_isometryClass_iff, Set.mem_insert_iff,
    properIsometryClass_eq_properIsometryClass_iff]
  refine ⟨fun ⟨e⟩ ↦ ?_, ?_⟩
  · by_cases he : e.IsProper
    · exact Or.inl ⟨e, he⟩
    · exact Or.inr ⟨e.trans t, Isometry.isProper_trans_iff.mpr (iff_of_false he ht)⟩
  · rintro (⟨e, -⟩ | ⟨e, -⟩)
    · exact ⟨e⟩
    · exact ⟨e.trans t.symm⟩

/-- With `t : M ≅ M'` of negative ambient determinant, `M` and `M'` are properly isometric
exactly when `M` has an automorphism of determinant `-1`. -/
private theorem properIsometryClass_eq_iff_exists_det_eq_neg_one {M' : IntegralLattice V}
    (t : Isometry M M') (ht : ¬ t.IsProper) :
    M.properIsometryClass = M'.properIsometryClass ↔
      ∃ g : Isometry M M, Isometry.det M g = -1 := by
  rw [properIsometryClass_eq_properIsometryClass_iff]
  constructor
  · rintro ⟨e, he⟩
    refine ⟨e.trans t.symm, ?_⟩
    have hn : ¬ (e.trans t.symm).IsProper := by
      rw [Isometry.isProper_trans_iff, Isometry.isProper_symm_iff]
      exact fun h ↦ ht (h.mp he)
    rw [Isometry.isProper_iff_det_eq_one] at hn
    exact (Isometry.det_eq_one_or_neg_one _).resolve_left hn
  · rintro ⟨g, hg⟩
    refine ⟨g.trans t, Isometry.isProper_trans_iff.mpr (iff_of_false ?_ ht)⟩
    rw [Isometry.isProper_iff_det_eq_one, hg]
    decide

/-- **Splitting of an isometry class into proper classes.** In positive rank, the number of proper
classes of lattices isometric to `M`, times the index `[O(M) : SO(M)]`, is `2`: the class of `M` is
one proper class when `M` has an improper automorphism, and two proper classes otherwise. -/
theorem ncard_preimage_toIsometryQuotient_mul_index (hV : 0 < finrank ℚ V)
    (M : IntegralLattice V) :
    (ProperIsometryQuotient.toIsometryQuotient ⁻¹' {M.isometryClass}).ncard *
      (specialOrthogonalGroup M).index = 2 := by
  have : FiniteDimensional ℚ V := Module.finite_of_finrank_pos hV
  obtain ⟨f, hf⟩ := LinearEquiv.exists_det_eq_neg_one hV
  have ht : ¬ (M.transportIsometry f).IsProper := by
    rw [Isometry.not_isProper_iff, toLinearEquiv_transportIsometry, ← LinearEquiv.coe_det, hf,
      Units.val_neg, Units.val_one]
    exact neg_one_lt_zero
  set t := M.transportIsometry f
  rw [preimage_toIsometryQuotient_eq_pair t ht]
  by_cases hg : ∃ g : Isometry M M, Isometry.det M g = -1
  · rw [(properIsometryClass_eq_iff_exists_det_eq_neg_one t ht).mpr hg, Set.pair_eq_singleton,
      Set.ncard_singleton, (index_specialOrthogonalGroup_eq_two_iff M).mpr hg]
  · have hne := (properIsometryClass_eq_iff_exists_det_eq_neg_one t ht).not.mpr hg
    have hi : (specialOrthogonalGroup M).index = 1 := by
      rcases index_specialOrthogonalGroup_eq_one_or_two M with h | h
      · exact h
      · exact absurd ((index_specialOrthogonalGroup_eq_two_iff M).mp h) hg
    rw [Set.ncard_pair hne, hi]

/-- Each class is the image of finitely many proper classes. -/
theorem finite_preimage_toIsometryQuotient (c : IsometryQuotient V) :
    (ProperIsometryQuotient.toIsometryQuotient ⁻¹' {c}).Finite := by
  have := c.out.finiteDimensional
  rcases (finrank ℚ V).eq_zero_or_pos with h | h
  · have : Subsingleton V := Module.finrank_zero_iff.mp h
    exact Set.toFinite _
  · rw [← isometryClass_out c]
    refine Set.finite_of_ncard_ne_zero fun h₀ ↦ ?_
    have h₂ := ncard_preimage_toIsometryQuotient_mul_index h c.out
    rw [h₀, zero_mul] at h₂
    omega

end Fibre

section Transport

variable {W : Type*} [AddCommGroup W] [Module ℚ W]

/-- Transport along `f : V ≃ W` sends a proper isometry `e : M ≅ N` to a proper isometry between
the transports of `M` and `N`: its ambient automorphism is the conjugate `f ∘ e ∘ f⁻¹`. -/
theorem Isometry.IsProper.transport_conj (f : V ≃ₗ[ℚ] W) {M N : IntegralLattice V}
    {e : Isometry M N} (he : e.IsProper) :
    (((M.transportIsometry f).symm.trans e).trans (N.transportIsometry f)).IsProper := by
  rw [Isometry.isProper_def, Isometry.toLinearEquiv_trans, Isometry.toLinearEquiv_trans,
    Isometry.toLinearEquiv_symm, toLinearEquiv_transportIsometry, toLinearEquiv_transportIsometry,
    LinearEquiv.coe_trans, LinearEquiv.coe_trans, LinearMap.det_conj]
  exact he

/-- The transport of `M` along `f` and back along `f⁻¹` is properly isometric to `M`. -/
private theorem isProper_transportIsometry_trans_symm (f : V ≃ₗ[ℚ] W) (M : IntegralLattice V) :
    ((M.transportIsometry f).trans ((M.transport f).transportIsometry f.symm)).IsProper := by
  rw [Isometry.isProper_def, Isometry.toLinearEquiv_trans, toLinearEquiv_transportIsometry,
    toLinearEquiv_transportIsometry, LinearEquiv.self_trans_symm, LinearEquiv.refl_toLinearMap,
    LinearMap.det_id]
  exact one_pos

/-- Transport along a rational linear equivalence `V ≃ W` identifies the proper classes of
integral lattices in `V` with those in `W`. -/
noncomputable def properIsometryQuotientEquiv (f : V ≃ₗ[ℚ] W) :
    ProperIsometryQuotient V ≃ ProperIsometryQuotient W where
  toFun := Quotient.map (·.transport f) fun _ _ ⟨_, he⟩ ↦ ⟨_, he.transport_conj f⟩
  invFun := Quotient.map (·.transport f.symm) fun _ _ ⟨_, he⟩ ↦ ⟨_, he.transport_conj f.symm⟩
  left_inv c := by
    obtain ⟨M, rfl⟩ := properIsometryClass_surjective c
    exact (isProper_transportIsometry_trans_symm f M).properIsometryClass_eq.symm
  right_inv c := by
    obtain ⟨M, rfl⟩ := properIsometryClass_surjective c
    exact (isProper_transportIsometry_trans_symm f.symm M).properIsometryClass_eq.symm

/-- `properIsometryQuotientEquiv f` sends the proper class of `M` to the proper class of its
transport along `f`. -/
@[simp]
theorem properIsometryQuotientEquiv_properIsometryClass (f : V ≃ₗ[ℚ] W)
    (M : IntegralLattice V) :
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

/-- The transport along `f` of the representative of a proper class is properly isometric to the
representative of the transported proper class. -/
theorem ProperIsometryQuotient.exists_isProper_transport_out (d : ProperIsometryQuotient V)
    (f : V ≃ₗ[ℚ] W) :
    ∃ e : Isometry (d.out.transport f) (properIsometryQuotientEquiv f d).out, e.IsProper := by
  rw [← properIsometryClass_eq_properIsometryClass_iff, properIsometryClass_out,
    ← properIsometryQuotientEquiv_properIsometryClass, properIsometryClass_out]

end Transport

end TauCeti.IntegralLattice

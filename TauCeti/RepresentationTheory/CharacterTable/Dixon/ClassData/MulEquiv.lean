/-
Copyright (c) 2026 Robert Joseph. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Joseph
-/
module

public import TauCeti.Algebra.Group.Conj
public import TauCeti.RepresentationTheory.CharacterTable.Dixon.ClassData.Basic

/-!
# Transport of numbered conjugacy data

A group equivalence transports `TauCeti.ClassData` by mapping its representative list in order.
The resulting numbering agrees with the native equivalence on conjugacy classes and preserves
inverse and power maps, class sizes, and the structure constants consumed by the Dixon algorithm.
Constructing the transported data needs no decision procedure; only the executable indexing and
finite class computations require the corresponding instances on the two groups.
-/

public section

namespace TauCeti.ClassData

variable {G H K : Type*} [Group G] [Group H] [Group K]
variable (d : ClassData G) (e : G ≃* H)

/-- Transport the ordered representatives across a group equivalence. -/
@[expose] def mapEquiv : ClassData H where
  reps := d.reps.map e
  pairwise_not_isConj := by
    rw [List.pairwise_map]
    refine d.pairwise_not_isConj.imp fun {x y} h hxy => h ?_
    simpa using e.symm.toMonoidHom.map_isConj hxy
  exists_isConj h := by
    obtain ⟨g, hg, hgh⟩ := d.exists_isConj (e.symm h)
    exact ⟨e g, List.mem_map_of_mem hg, by simpa using e.toMonoidHom.map_isConj hgh⟩

@[simp]
theorem reps_mapEquiv : (d.mapEquiv e).reps = d.reps.map e := rfl

@[simp]
theorem numClasses_mapEquiv : (d.mapEquiv e).numClasses = d.numClasses := by
  simp [numClasses]

/-- The index cast for transport preserves the natural-number value of every class number. -/
@[expose] def mapIndex : Fin d.numClasses ≃ Fin (d.mapEquiv e).numClasses :=
  finCongr (d.numClasses_mapEquiv e).symm

@[simp]
theorem val_mapIndex (i : Fin d.numClasses) : (d.mapIndex e i).val = i.val := rfl

@[simp]
theorem rep_mapEquiv (i : Fin d.numClasses) :
    (d.mapEquiv e).rep (d.mapIndex e i) = e (d.rep i) := by
  simp [rep, mapIndex]

/-- Transport of representatives agrees with the existing equivalence on conjugacy classes. -/
theorem classOf_mapEquiv (i : Fin d.numClasses) :
    (d.mapEquiv e).classOf (d.mapIndex e i) = e.conjClassesEquiv (d.classOf i) := by
  rw [classOf_eq_mk, classOf_eq_mk, rep_mapEquiv, e.conjClassesEquiv_mk]

@[simp]
theorem mapEquiv_refl : d.mapEquiv (MulEquiv.refl G) = d := by
  ext
  simp

@[simp]
theorem mapEquiv_mapEquiv (f : H ≃* K) :
    (d.mapEquiv e).mapEquiv f = d.mapEquiv (e.trans f) := by
  ext
  simp [List.map_map]

/-- Transporting back along the inverse recovers the original data. -/
theorem mapEquiv_symm : (d.mapEquiv e).mapEquiv e.symm = d := by
  rw [mapEquiv_mapEquiv]
  simp

section Executable

variable [DecidableRel (IsConj : G → G → Prop)] [DecidableRel (IsConj : H → H → Prop)]

/-- Independent conjugacy decisions give the same transported numbering. -/
@[simp]
theorem index_mapEquiv_apply (g : G) :
    (d.mapEquiv e).index (e g) = d.mapIndex e (d.index g) := by
  apply (d.mapEquiv e).index_eq_iff.mpr
  rw [rep_mapEquiv]
  exact e.toMonoidHom.map_isConj (d.isConj_rep_index g)

@[simp]
theorem indexClass_mapEquiv (C : ConjClasses G) :
    (d.mapEquiv e).indexClass (e.conjClassesEquiv C) = d.mapIndex e (d.indexClass C) := by
  induction C using Quotient.ind
  simp [ConjClasses.quotient_mk_eq_mk]

/-- The numbering square commutes with native transport of conjugacy classes. -/
theorem mapIndex_trans_equivConjClasses :
    (d.mapIndex e).trans (d.mapEquiv e).equivConjClasses =
      d.equivConjClasses.trans e.conjClassesEquiv := by
  ext i
  simpa only [Equiv.trans_apply, equivConjClasses_apply] using d.classOf_mapEquiv e i

theorem index_mapEquiv_rep_inv (i : Fin d.numClasses) :
    (d.mapEquiv e).index ((d.mapEquiv e).rep (d.mapIndex e i))⁻¹ =
      d.mapIndex e (d.index (d.rep i)⁻¹) := by
  rw [rep_mapEquiv, ← map_inv, index_mapEquiv_apply]

theorem index_mapEquiv_rep_pow (i : Fin d.numClasses) (m : ℕ) :
    (d.mapEquiv e).index ((d.mapEquiv e).rep (d.mapIndex e i) ^ m) =
      d.mapIndex e (d.index (d.rep i ^ m)) := by
  rw [rep_mapEquiv, ← map_pow, index_mapEquiv_apply]

variable [Fintype G] [Fintype H]

/-- Each transported finite class is the embedding image of its original class. -/
theorem classFinset_mapEquiv (i : Fin d.numClasses) :
    (d.mapEquiv e).classFinset (d.mapIndex e i) =
      (d.classFinset i).map e.toEquiv.toEmbedding := by
  ext h
  obtain ⟨g, rfl⟩ := e.surjective h
  simp [index_mapEquiv_apply]

@[simp]
theorem card_classFinset_mapEquiv (i : Fin d.numClasses) :
    ((d.mapEquiv e).classFinset (d.mapIndex e i)).card = (d.classFinset i).card := by
  rw [classFinset_mapEquiv, Finset.card_map]

/-- The bijection on each class preserves the complementary-factor count defining a constant. -/
@[simp]
theorem structureConstant_mapEquiv (i j k : Fin d.numClasses) :
    (d.mapEquiv e).structureConstant (d.mapIndex e i) (d.mapIndex e j) (d.mapIndex e k) =
      d.structureConstant i j k := by
  simp only [structureConstant, classFinset_mapEquiv, Finset.filter_map, Finset.card_map]
  congr 1
  apply Finset.filter_congr
  intro x _
  change (d.mapEquiv e).index ((e x)⁻¹ * (d.mapEquiv e).rep (d.mapIndex e k)) =
    d.mapIndex e j ↔ d.index (x⁻¹ * d.rep k) = j
  rw [rep_mapEquiv, ← map_inv, ← map_mul, index_mapEquiv_apply]
  exact (d.mapIndex e).injective.eq_iff

/-- Pulling back both matrix indices preserves the native transposed convention `aᵢₖⱼ`. -/
theorem classMultMatrix_mapEquiv (i : Fin d.numClasses) :
    ((d.mapEquiv e).classMultMatrix (d.mapIndex e i)).submatrix
      (d.mapIndex e) (d.mapIndex e) = d.classMultMatrix i := by
  ext j k
  simp [Matrix.submatrix_apply]

end Executable

end TauCeti.ClassData

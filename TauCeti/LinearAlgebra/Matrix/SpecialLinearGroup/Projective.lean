/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Projective
public import TauCeti.GroupTheory.Index.Basic
public import TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.Basic
import TauCeti.GroupTheory.QuotientGroup.Index

/-!
# Projective special linear groups: extension of scalars and lifted subgroups

This file defines the map on projective special linear groups induced by a ring homomorphism
and proves its identity, composition, and representative formulas.

It then records how subgroups of `PSL(n, R) = SL(n, R) ⧸ Z(SL(n, R))` correspond to subgroups of
`SL(n, R)`. The full preimage `Γ.liftSL` of `Γ ≤ PSL(n, R)` contains the centre, has the same
index as `Γ`, maps back onto `Γ`, and is compatible with conjugation; this is the correspondence
theorem `QuotientGroup.comapMk'OrderIso` read for the projective special linear group. For
`Γ ≤ SL(n, R)` the preimage of its image is `Γ.withCenter`, and the image has the index of `Γ`
when `Γ` contains the centre.

In rank two over a ring without zero divisors the centre is `{±I}`, so containing the centre
means containing `-I`. The image of `Γ ≤ SL(2, R)` in `PSL(2, R)` then has the index of `Γ` when
`-I ∈ Γ` and half of it otherwise, and has finite index exactly when `Γ` does. For `R = ℤ` this
is the dictionary between subgroups of the modular group `PSL(2, ℤ)` and the subgroups of
`SL(2, ℤ)` containing `-I`, and between the index of a subgroup of `SL(2, ℤ)` and its projective
index.

## Main declarations

* `TauCeti.SpecialLinear.projectiveMap`: extension of scalars on projective special linear
  groups.
* `TauCeti.SpecialLinear.projectiveMap_mk`: the action on quotient representatives.
* `Subgroup.liftSL`: the full preimage in `SL(n, R)` of a subgroup of `PSL(n, R)`.
* `Subgroup.map_liftSL`, `Subgroup.liftSL_map`: the image of `Γ.liftSL` is `Γ`, and the preimage
  of the image of `Γ ≤ SL(n, R)` is `Γ.withCenter`.
* `Subgroup.index_liftSL`: `Γ.liftSL` has the index of `Γ`.
* `Subgroup.liftSL_conjAct_smul`: lifting commutes with conjugation.
* `Subgroup.index_map_mk'_of_center_le`: the image in `PSL(n, R)` of a subgroup of `SL(n, R)`
  containing the centre has the same index.
* `Subgroup.index_map_mk'_of_neg_one_mem` and `Subgroup.two_mul_index_map_mk'_of_neg_one_notMem`:
  the index of the image in `PSL(2, R)` of a subgroup of `SL(2, R)`.
* `Subgroup.finiteIndex_map_mk'_iff`: that image has finite index exactly when the subgroup does.

## References

* Fred Diamond and Jerry Shurman, *A First Course in Modular Forms*, Graduate Texts in
  Mathematics 228, Springer, 2005, §1.2 (the index of `Γ` and of `±Γ`).
-/

public section

namespace TauCeti

namespace SpecialLinear

universe u v w

variable (n : ℕ)
variable {R : Type v} [CommRing R] {S : Type w} [CommRing S]

/-- Entrywise application of a ring homomorphism carries the center of a special linear group
into the center of the target special linear group. -/
theorem map_center_le_comap_center (f : R →+* S) :
    Subgroup.center (Matrix.SpecialLinearGroup (Fin n) R) ≤
      (Subgroup.center (Matrix.SpecialLinearGroup (Fin n) S)).comap
        (Matrix.SpecialLinearGroup.map f) := by
  intro g hg
  rw [Subgroup.mem_comap, Matrix.SpecialLinearGroup.mem_center_iff]
  rw [Matrix.SpecialLinearGroup.mem_center_iff] at hg
  obtain ⟨r, hr, hrg⟩ := hg
  refine ⟨f r, ?_, ?_⟩
  · rw [← map_pow, hr, map_one]
  · rw [Matrix.SpecialLinearGroup.map_apply_coe, ← hrg]
    ext i j
    by_cases hij : i = j <;>
      simp [RingHom.mapMatrix_apply, Matrix.scalar_apply, hij]

/-- Extension of scalars on projective special linear groups. -/
noncomputable def projectiveMap (f : R →+* S) :
    Matrix.ProjectiveSpecialLinearGroup (Fin n) R →*
      Matrix.ProjectiveSpecialLinearGroup (Fin n) S :=
  QuotientGroup.map
    (Subgroup.center (Matrix.SpecialLinearGroup (Fin n) R))
    (Subgroup.center (Matrix.SpecialLinearGroup (Fin n) S))
    (Matrix.SpecialLinearGroup.map f) (map_center_le_comap_center n f)

/-- Extension of scalars on projective special linear groups is computed on representatives by
entrywise application of the ring homomorphism. -/
@[simp]
theorem projectiveMap_mk (f : R →+* S) (g : Matrix.SpecialLinearGroup (Fin n) R) :
    projectiveMap n f (QuotientGroup.mk g) =
      QuotientGroup.mk (Matrix.SpecialLinearGroup.map f g) := by
  exact QuotientGroup.map_mk _ _ _ _ g

/-- Extension of scalars by the identity is the identity on projective special linear groups. -/
@[simp]
theorem projectiveMap_id :
    projectiveMap n (RingHom.id R) = MonoidHom.id _ := by
  rw [projectiveMap]
  exact QuotientGroup.map_id _ _

/-- Successive extensions of scalars compose on projective special linear groups. -/
@[simp]
theorem projectiveMap_comp {T : Type u} [CommRing T] (f : R →+* S) (g : S →+* T) :
    (projectiveMap n g).comp (projectiveMap n f) = projectiveMap n (g.comp f) := by
  rw [projectiveMap, projectiveMap, projectiveMap]
  exact QuotientGroup.map_comp_map _ _ _ _ _ _ _ _

end SpecialLinear

end TauCeti

namespace Subgroup

open Matrix

open scoped Pointwise

section Lift

variable {n : Type*} [Fintype n] [DecidableEq n] {R : Type*} [CommRing R]

/-- The full preimage in `SL(n, R)` of a subgroup `Γ` of the projective special linear group
`PSL(n, R) = SL(n, R) ⧸ Z(SL(n, R))` under the quotient map by the centre: the matrices whose
class modulo the centre lies in `Γ`. -/
def liftSL (Γ : Subgroup (ProjectiveSpecialLinearGroup n R)) :
    Subgroup (SpecialLinearGroup n R) :=
  Γ.comap (QuotientGroup.mk' (center (SpecialLinearGroup n R)))

/-- The lift is the preimage under the quotient map by the centre. -/
theorem liftSL_def (Γ : Subgroup (ProjectiveSpecialLinearGroup n R)) :
    Γ.liftSL = Γ.comap (QuotientGroup.mk' (center (SpecialLinearGroup n R))) := (rfl)

variable {Γ Γ' : Subgroup (ProjectiveSpecialLinearGroup n R)}

/-- A matrix lies in the lift of `Γ` exactly when its class in `PSL(n, R)` lies in `Γ`. -/
@[simp]
theorem mem_liftSL {g : SpecialLinearGroup n R} :
    g ∈ Γ.liftSL ↔ (g : ProjectiveSpecialLinearGroup n R) ∈ Γ := Iff.rfl

/-- The lift is the subgroup underlying the image of `Γ` under the correspondence theorem
`QuotientGroup.comapMk'OrderIso`, which bundles lifting as an order isomorphism onto the
subgroups of `SL(n, R)` containing the centre. -/
theorem liftSL_eq_comapMk'OrderIso (Γ : Subgroup (ProjectiveSpecialLinearGroup n R)) :
    Γ.liftSL = (QuotientGroup.comapMk'OrderIso (center (SpecialLinearGroup n R)) Γ :
      Subgroup (SpecialLinearGroup n R)) := (rfl)

/-- Every lift contains the centre of `SL(n, R)`. -/
theorem center_le_liftSL (Γ : Subgroup (ProjectiveSpecialLinearGroup n R)) :
    center (SpecialLinearGroup n R) ≤ Γ.liftSL :=
  QuotientGroup.le_comap_mk' _ Γ

/-- The image of the lift of `Γ` in `PSL(n, R)` is `Γ` itself. -/
@[simp]
theorem map_liftSL (Γ : Subgroup (ProjectiveSpecialLinearGroup n R)) :
    Γ.liftSL.map (QuotientGroup.mk' (center (SpecialLinearGroup n R))) = Γ :=
  map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _) Γ

/-- The lift of the image of `Γ ≤ SL(n, R)` in `PSL(n, R)` is `Γ` with the centre adjoined. -/
@[simp]
theorem liftSL_map (Γ : Subgroup (SpecialLinearGroup n R)) :
    (Γ.map (QuotientGroup.mk' (center (SpecialLinearGroup n R)))).liftSL = Γ.withCenter := by
  rw [liftSL_def, QuotientGroup.comap_map_mk', sup_comm, withCenter_def]

/-- Lifting preserves and reflects inclusions. -/
@[simp]
theorem liftSL_le_liftSL_iff : Γ.liftSL ≤ Γ'.liftSL ↔ Γ ≤ Γ' :=
  comap_le_comap_of_surjective (QuotientGroup.mk'_surjective _)

/-- Distinct subgroups of `PSL(n, R)` have distinct lifts. -/
theorem liftSL_injective :
    Function.Injective (liftSL : Subgroup (ProjectiveSpecialLinearGroup n R) → _) :=
  comap_injective (QuotientGroup.mk'_surjective _)

/-- The lifts are exactly the subgroups of `SL(n, R)` containing the centre. -/
theorem range_liftSL :
    Set.range (liftSL : Subgroup (ProjectiveSpecialLinearGroup n R) → _) =
      {Γ | center (SpecialLinearGroup n R) ≤ Γ} := by
  ext Γ
  refine ⟨?_, fun h ↦ ⟨Γ.map (QuotientGroup.mk' _), ?_⟩⟩
  · rintro ⟨Γ, rfl⟩
    exact center_le_liftSL Γ
  · rw [liftSL_map, withCenter_eq_self_iff.mpr h]

/-- The lift of the whole projective group is the whole special linear group. -/
@[simp]
theorem liftSL_top : (⊤ : Subgroup (ProjectiveSpecialLinearGroup n R)).liftSL = ⊤ :=
  comap_top _

/-- The lift of the trivial subgroup is the centre of `SL(n, R)`, which need not be trivial. -/
@[simp]
theorem liftSL_bot :
    (⊥ : Subgroup (ProjectiveSpecialLinearGroup n R)).liftSL = center (SpecialLinearGroup n R) :=
  QuotientGroup.ker_mk' _

/-- The lift of `Γ` has the same index in `SL(n, R)` as `Γ` has in `PSL(n, R)`. -/
@[simp]
theorem index_liftSL (Γ : Subgroup (ProjectiveSpecialLinearGroup n R)) :
    Γ.liftSL.index = Γ.index :=
  index_comap_of_surjective _ (QuotientGroup.mk'_surjective _)

instance (Γ : Subgroup (ProjectiveSpecialLinearGroup n R)) [Γ.FiniteIndex] :
    Γ.liftSL.FiniteIndex :=
  inferInstanceAs (Γ.comap (QuotientGroup.mk' (center (SpecialLinearGroup n R)))).FiniteIndex

/-- The image in `PSL(n, R)` of a subgroup `Γ` of `SL(n, R)` containing the centre has the index
of `Γ`. -/
theorem index_map_mk'_of_center_le {Γ : Subgroup (SpecialLinearGroup n R)}
    (h : center (SpecialLinearGroup n R) ≤ Γ) :
    (Γ.map (QuotientGroup.mk' (center (SpecialLinearGroup n R)))).index = Γ.index :=
  index_map_eq _ (QuotientGroup.mk'_surjective _) <| by rwa [QuotientGroup.ker_mk']

/-- Lifting commutes with conjugation: the lift of the conjugate of `Γ` by the class of `g` is the
conjugate of the lift of `Γ` by `g`. -/
theorem liftSL_conjAct_smul (g : SpecialLinearGroup n R)
    (Γ : Subgroup (ProjectiveSpecialLinearGroup n R)) :
    (ConjAct.toConjAct (g : ProjectiveSpecialLinearGroup n R) • Γ).liftSL =
      ConjAct.toConjAct g • Γ.liftSL := by
  ext x
  simp only [mem_pointwise_smul_iff_inv_smul_mem, mem_liftSL, ← map_inv, ConjAct.toConjAct_smul,
    QuotientGroup.mk_mul, QuotientGroup.mk_inv]

end Lift

section FinTwo

variable {R : Type*} [CommRing R]

/-- The lift of a subgroup of `PSL(2, R)` contains `-I`, which is central. -/
theorem neg_one_mem_liftSL (Γ : Subgroup (ProjectiveSpecialLinearGroup (Fin 2) R)) :
    (-1 : SpecialLinearGroup (Fin 2) R) ∈ Γ.liftSL :=
  center_le_liftSL Γ <| mem_center_iff.mpr fun g ↦ by rw [mul_neg_one, neg_one_mul]

variable [NoZeroDivisors R]

variable {Γ : Subgroup (SpecialLinearGroup (Fin 2) R)}

/-- A subgroup of `SL(2, R)` containing `-I` is the lift of its image in `PSL(2, R)`. -/
theorem liftSL_map_of_neg_one_mem (h : (-1 : SpecialLinearGroup (Fin 2) R) ∈ Γ) :
    (Γ.map (QuotientGroup.mk' (center (SpecialLinearGroup (Fin 2) R)))).liftSL = Γ := by
  rw [liftSL_map, withCenter_eq_self_iff, SpecialLinearGroup.center_le_iff_neg_one_mem]
  exact h

/-- The image in `PSL(2, R)` of a subgroup `Γ` of `SL(2, R)` containing `-I` has the index of
`Γ`. -/
theorem index_map_mk'_of_neg_one_mem (h : (-1 : SpecialLinearGroup (Fin 2) R) ∈ Γ) :
    (Γ.map (QuotientGroup.mk' (center (SpecialLinearGroup (Fin 2) R)))).index = Γ.index :=
  index_map_mk'_of_center_le <| SpecialLinearGroup.center_le_iff_neg_one_mem.mpr h

/-- The image in `PSL(2, R)` of a subgroup `Γ` of `SL(2, R)` not containing `-I` has half the
index of `Γ`: the cosets of `Γ` pair up into the cosets of `±Γ`. -/
theorem two_mul_index_map_mk'_of_neg_one_notMem
    (h : (-1 : SpecialLinearGroup (Fin 2) R) ∉ Γ) :
    2 * (Γ.map (QuotientGroup.mk' (center (SpecialLinearGroup (Fin 2) R)))).index =
      Γ.index := by
  rw [index_map_mk'_eq_index_sup, ← withCenter_def,
    SpecialLinearGroup.index_eq_two_mul_index_withCenter_of_neg_one_notMem h]

/-- The image in `PSL(2, R)` of a subgroup of `SL(2, R)` has finite index exactly when the
subgroup does. -/
theorem finiteIndex_map_mk'_iff :
    (Γ.map (QuotientGroup.mk' (center (SpecialLinearGroup (Fin 2) R)))).FiniteIndex ↔
      Γ.FiniteIndex := by
  refine ⟨fun h ↦ ?_, fun _ ↦ inferInstance⟩
  by_cases hΓ : (-1 : SpecialLinearGroup (Fin 2) R) ∈ Γ
  · exact ⟨index_map_mk'_of_neg_one_mem hΓ ▸ h.index_ne_zero⟩
  · exact ⟨two_mul_index_map_mk'_of_neg_one_notMem hΓ ▸ mul_ne_zero two_ne_zero h.index_ne_zero⟩

end FinTwo

end Subgroup

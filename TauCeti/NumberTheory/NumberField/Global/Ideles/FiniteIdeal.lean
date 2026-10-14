/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.Global.Ideles.Norm.Basic
public import TauCeti.RingTheory.DedekindDomain.FiniteAdeleRing.ClassGroup

/-!
# Fractional ideals of ideles

This file relates the fractional ideal of an idele's finite component to its valuations at
finite places. It also gives a norm-one idele representative of every ideal class.

Let `T` be a set of finite places whose classes generate the ideal class group, for instance a
finite set when the class group is finite
(`ClassGroup.exists_finite_closure_classGroupMk_image_eq_top`).
Write `I_{K,T}` for the ideles that are local units at every finite place outside `T`, and `U_T`
for the `T`-units `T.unit K`. Then every idele is a principal idele times an element of `I_{K,T}`,
and the principal ideles in `I_{K,T}` are exactly those of the `T`-units:

`I_K = Kˣ · I_{K,T}`,  `Kˣ ∩ I_{K,T} = U_T`,

so the idele class group is `C_K = I_{K,T} / U_T`. This is the form in which the cohomology of
the idele classes of a Galois extension is computed from that of the `T`-ideles and the `T`-units,
for `T` stable under the Galois group.

## Main results

* `NumberField.IdeleGroup.exists_valued_ideleFiniteCoord_mul_unitEmbedding_eq_one`:
  `I_K = Kˣ · I_{K,T}`.
* `NumberField.IdeleGroup.mem_principalSubgroup_iff_exists_mem_unit`: `Kˣ ∩ I_{K,T} = U_T`.
* `NumberField.IdeleClassGroup.exists_valued_ideleFiniteCoord_eq_one_and_mk_eq`: every idele class
  is the class of an element of `I_{K,T}`.

## References

* J. S. Milne, *Class Field Theory*, Chapter VII, §4.
* J. Neukirch, *Algebraic Number Theory*, Chapter VI, §1.
-/

public section

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
  IsDedekindDomain.FiniteAdeleRing NumberField NumberField.InfinitePlace
open scoped NumberField

namespace TauCeti.GlobalNumberFields

variable {R : Type*} [CommRing R] [IsDedekindDomain R]
variable {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]

/-- The fractional ideal of an idele's finite component is trivial exactly when the idele is a
unit at every finite place. -/
-- The finite-adele and coordinate simp lemmas already prove this equivalence.
theorem toFractionalIdeal_toFiniteIdele_eq_one_iff {x : IdeleGroup R K} :
    toFractionalIdeal (IdeleGroup.toFiniteIdele R K x) = 1 ↔
      ∀ v : HeightOneSpectrum R, Valued.v (v.ideleFiniteCoord x : v.adicCompletion K) = 1 := by
  simp only [toFractionalIdeal_eq_one_iff, adicOrd_eq_zero_iff, IdeleGroup.coe_toFiniteIdele,
    HeightOneSpectrum.coe_ideleFiniteCoord]

end TauCeti.GlobalNumberFields

namespace IsDedekindDomain.HeightOneSpectrum

variable {R : Type*} [CommRing R] [IsDedekindDomain R]
variable {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]

/-- The fractional ideal of an idele concentrated at one finite place is the corresponding
prime power, with exponent the local order of its nonzero coordinate. -/
@[simp]
theorem toFractionalIdeal_toFiniteIdele_ofAdicCompletion (v : HeightOneSpectrum R)
    (u : (v.adicCompletion K)ˣ) :
    toFractionalIdeal (IdeleGroup.toFiniteIdele R K (IdeleGroup.ofAdicCompletion R K v u)) =
      v.unitOfPrime K ^ (-WithZero.log (Valued.v (u : v.adicCompletion K))) := by
  classical
  have hself : adicOrd (IdeleGroup.toFiniteIdele R K
      (IdeleGroup.ofAdicCompletion R K v u)) v =
        -WithZero.log (Valued.v (u : v.adicCompletion K)) := by
    rw [adicOrd_def, IdeleGroup.coe_toFiniteIdele, ← HeightOneSpectrum.coe_ideleFiniteCoord,
      HeightOneSpectrum.ideleFiniteCoord_ofAdicCompletion_self]
  have hother (w : HeightOneSpectrum R) (hw : w ≠ v) :
      adicOrd (IdeleGroup.toFiniteIdele R K (IdeleGroup.ofAdicCompletion R K v u)) w = 0 := by
    rw [adicOrd_def, IdeleGroup.coe_toFiniteIdele, ← HeightOneSpectrum.coe_ideleFiniteCoord,
      HeightOneSpectrum.ideleFiniteCoord_ofAdicCompletion_of_ne w hw,
      Units.val_one, map_one, WithZero.log_one, neg_zero]
  rw [toFractionalIdeal_apply, finprod_eq_single _ v, hself]
  intro w hw
  simp only [hother w hw, zpow_zero]

end IsDedekindDomain.HeightOneSpectrum

namespace ClassGroup

open TauCeti.GlobalNumberFields

variable {K : Type*} [Field K] [NumberField K]

/-- Every ideal class is the class of the finite part of an idele of norm one. -/
theorem exists_ideleNorm_eq_one_and_toClassGroup_eq (c : ClassGroup (𝓞 K)) :
    ∃ b : IdeleGroup (𝓞 K) K, ideleNorm b = 1 ∧
      FiniteAdeleRing.toClassGroup (𝓞 K) K (IdeleGroup.toFiniteIdele (𝓞 K) K b) = c := by
  obtain ⟨f, hf⟩ := FiniteAdeleRing.toClassGroup_surjective (R := 𝓞 K) (K := K) c
  -- Correct the norm at one infinite place, which does not change the finite part.
  obtain ⟨w⟩ := (inferInstance : Nonempty (InfinitePlace K))
  obtain ⟨x, hx⟩ := exists_completionNormalizedAbsValue_eq w
    ((ideleNorm (IdeleGroup.ofFiniteIdele (𝓞 K) K f))⁻¹ : NNReal).coe_nonneg
  have hx0 : x ≠ 0 := by
    rintro rfl
    rw [map_zero] at hx
    exact Units.ne_zero _ (by exact_mod_cast hx.symm)
  refine ⟨IdeleGroup.ofFiniteIdele (𝓞 K) K f * IdeleGroup.ofCompletion (𝓞 K) K w (Units.mk0 x hx0),
    ?_, ?_⟩
  · ext
    rw [map_mul, Units.val_mul, NNReal.coe_mul, coe_ideleNorm_ofCompletion, Units.val_mk0, hx]
    simp
  · rw [map_mul, map_mul, IdeleGroup.toFiniteIdele_ofFiniteIdele,
      IdeleGroup.toFiniteIdele_ofCompletion, map_one, mul_one, hf]

end ClassGroup

/-! ### Ideles that are units outside a set of places -/

namespace NumberField.IdeleGroup

variable {R : Type*} [CommRing R] [IsDedekindDomain R]
variable {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
variable {T : Set (HeightOneSpectrum R)}

/-- **Every idele is a principal idele times an idele that is a unit at the finite places outside
`T`**, when the classes of the primes in `T` generate the ideal class group:
`I_K = Kˣ · I_{K,T}`. -/
theorem exists_valued_ideleFiniteCoord_mul_unitEmbedding_eq_one
    (hT : Subgroup.closure (HeightOneSpectrum.classGroupMk '' T) = ⊤) (x : IdeleGroup R K) :
    ∃ a : Kˣ, ∀ v ∉ T,
      Valued.v (v.ideleFiniteCoord (x * unitEmbedding R K a) : v.adicCompletion K) = 1 := by
  obtain ⟨a, ha⟩ := FiniteAdeleRing.exists_valued_mul_unitEmbedding_eq_one hT (toFiniteIdele R K x)
  refine ⟨a, fun v hv ↦ ?_⟩
  rw [HeightOneSpectrum.coe_ideleFiniteCoord, ← coe_toFiniteIdele, map_mul,
    toFiniteIdele_unitEmbedding]
  exact ha v hv

/-- A principal idele is a unit at every finite place outside `T` exactly when it comes from a
`T`-unit. -/
theorem forall_valued_ideleFiniteCoord_unitEmbedding_eq_one_iff (a : Kˣ) :
    (∀ v ∉ T,
      Valued.v (v.ideleFiniteCoord (unitEmbedding R K a) : v.adicCompletion K) = 1) ↔
      a ∈ T.unit K := by
  rw [← FiniteAdeleRing.forall_valued_unitEmbedding_eq_one_iff]
  refine forall₂_congr fun v _ ↦ ?_
  rw [HeightOneSpectrum.coe_ideleFiniteCoord, ← coe_toFiniteIdele, toFiniteIdele_unitEmbedding]

/-- **The principal ideles that are units outside `T` are those of the `T`-units**:
`Kˣ ∩ I_{K,T} = U_T`. -/
theorem mem_principalSubgroup_iff_exists_mem_unit {x : IdeleGroup R K}
    (hx : ∀ v ∉ T, Valued.v (v.ideleFiniteCoord x : v.adicCompletion K) = 1) :
    x ∈ principalSubgroup R K ↔ ∃ a ∈ T.unit K, unitEmbedding R K a = x := by
  refine ⟨fun ⟨a, ha⟩ ↦ ⟨a, ?_, ha⟩, fun ⟨a, _, ha⟩ ↦ ⟨a, ha⟩⟩
  rw [← forall_valued_ideleFiniteCoord_unitEmbedding_eq_one_iff (R := R)]
  exact ha ▸ hx

end NumberField.IdeleGroup

namespace NumberField.IdeleClassGroup

variable {R : Type*} [CommRing R] [IsDedekindDomain R]
variable {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
variable {T : Set (HeightOneSpectrum R)}

/-- **Every idele class is represented by an idele that is a unit at the finite places outside
`T`**, when the classes of the primes in `T` generate the ideal class group. With
`NumberField.IdeleGroup.mem_principalSubgroup_iff_exists_mem_unit`, this identifies `C_K` with
`I_{K,T} / U_T`. -/
theorem exists_valued_ideleFiniteCoord_eq_one_and_mk_eq
    (hT : Subgroup.closure (HeightOneSpectrum.classGroupMk '' T) = ⊤) (c : IdeleClassGroup R K) :
    ∃ x : IdeleGroup R K,
      (∀ v ∉ T, Valued.v (v.ideleFiniteCoord x : v.adicCompletion K) = 1) ∧
        (x : IdeleClassGroup R K) = c := by
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective c
  obtain ⟨a, ha⟩ := IdeleGroup.exists_valued_ideleFiniteCoord_mul_unitEmbedding_eq_one hT x
  exact ⟨x * IdeleGroup.unitEmbedding R K a, ha,
    QuotientGroup.mk_mul_of_mem x ⟨a, rfl⟩⟩

end NumberField.IdeleClassGroup

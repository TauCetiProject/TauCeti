/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Isomorphisms
public import Mathlib.LinearAlgebra.TensorAlgebra.ToTensorPower
public import Mathlib.LinearAlgebra.TensorPower.Basic
public import TauCeti.FieldTheory.MatsumotoGroup
public import TauCeti.FieldTheory.MilnorK.Basic
import TauCeti.LinearAlgebra.TensorSquare

/-!
# Homogeneous quotient bridge and degree-two identification of Milnor K-theory

This file bridges `MilnorK.degree R n` with the homogeneous tensor-power quotients
`(⨂[ℤ]^n (Additive Rˣ)) ⧸ MilnorK.relationSubmodule R n` naturally in `R`, and derives the
canonical degree-2 identification with `MatsumotoGroup R` (complementing the degree-0 and degree-1
identifications in `TauCeti.RingTheory.MilnorK.Basic`).

## Main definitions

* `TauCeti.MilnorK.toDegree`: the canonical surjection `(⨂[ℤ]^n) (Additive Rˣ) →ₗ[ℤ] degree R n`.
* `TauCeti.MilnorK.degreeEquivQuotient`: the canonical linear equivalence
  `degree R n ≃ₗ[ℤ] ((⨂[ℤ]^n) (Additive Rˣ)) ⧸ relationSubmodule R n`.
* `TauCeti.MilnorK.mapQuotient`: functorial map on degree-`n` tensor-power quotients.
* `TauCeti.MilnorK.degreeTwoEquivMatsumotoGroup`: the canonical equivalence
  `degree R 2 ≃ₗ[ℤ] MatsumotoGroup R`.

## Main results

* `TauCeti.MilnorK.degreeEquivQuotient_mapDegree`: naturality of the degree-`n` quotient bridge
  under ring homomorphisms.
* `TauCeti.MilnorK.degreeTwoEquivMatsumotoGroup_mapDegree`: naturality of the degree-2
  identification with `MatsumotoGroup`.

## References

* C. A. Weibel, *The K-book: An Introduction to Algebraic K-Theory*, Definition III.7.1 and
  Section III.6.1.
* H. Matsumoto, *Sur les sous-groupes arithmétiques des groupes semi-simples déployés*, Section 9.
-/

public section

namespace TauCeti

open scoped DirectSum TensorProduct

namespace MilnorK

section DegreeQuotient

variable (R : Type*) [CommRing R]

/-- The canonical `ℤ`-linear surjection `(⨂[ℤ]^n) (Additive Rˣ) →ₗ[ℤ] MilnorK.degree R n`. -/
noncomputable def toDegree (n : ℕ) : (⨂[ℤ]^n) (Additive Rˣ) →ₗ[ℤ] degree R n where
  toFun t := ⟨mk (TensorPower.toTensorAlgebra t),
    mem_degree_iff.mpr
      ⟨TensorPower.toTensorAlgebra t, TensorPower.toTensorAlgebra_mem_range_pow t, rfl⟩⟩
  map_add' _ _ := Subtype.ext (by simp)
  map_smul' _ _ := Subtype.ext (by simp)

/-- Underlying element of `toDegree R n t` in `MilnorK R`. -/
@[simp]
theorem coe_toDegree (n : ℕ) (t : (⨂[ℤ]^n) (Additive Rˣ)) :
    (toDegree R n t : MilnorK R) = mk (TensorPower.toTensorAlgebra t) := by
  rw [toDegree, LinearMap.coe_mk, AddHom.coe_mk]

/-- `toDegree R n` maps a pure tensor `tprod ℤ x` to the corresponding Milnor symbol. -/
theorem toDegree_tprod {n : ℕ} (x : Fin n → Additive Rˣ) :
    (toDegree R n (PiTensorProduct.tprod ℤ x) : MilnorK R) =
      symbol (List.ofFn fun i ↦ Additive.toMul (x i)) := by
  rw [coe_toDegree, mk_toTensorAlgebra_tprod]

/-- `toDegree` intertwines graded tensor multiplication with multiplication in `MilnorK R`. -/
theorem toDegree_gMul {m n : ℕ} (a : (⨂[ℤ]^m) (Additive Rˣ)) (b : (⨂[ℤ]^n) (Additive Rˣ)) :
    (toDegree R (m + n)
      (GradedMonoid.GMul.mul (A := fun k ↦ (⨂[ℤ]^k) (Additive Rˣ)) a b) : MilnorK R) =
      (toDegree R m a : MilnorK R) * (toDegree R n b : MilnorK R) := by
  rw [coe_toDegree, coe_toDegree, coe_toDegree, TensorPower.toTensorAlgebra_gMul, map_mul]

/-- The kernel of `toDegree R n` is precisely `relationSubmodule R n`. -/
theorem ker_toDegree (n : ℕ) : LinearMap.ker (toDegree R n) = relationSubmodule R n := by
  ext t
  rw [LinearMap.mem_ker, Subtype.ext_iff, coe_toDegree]
  exact toTensorAlgebra_mem_ker_iff R t

/-- `toDegree R n` is surjective onto `MilnorK.degree R n`. -/
theorem surjective_toDegree (n : ℕ) : Function.Surjective (toDegree R n) := fun x ↦ by
  induction x using degree_inductionOn with
  | zero => exact ⟨0, map_zero _⟩
  | symbol l hl =>
    refine ⟨PiTensorProduct.tprod ℤ fun i ↦ Additive.ofMul (l.get (i.cast hl.symm)),
      Subtype.ext ?_⟩
    rw [toDegree_tprod]; congr 1
    exact List.ext_get (by simp [hl]) fun _ _ _ ↦ by simp
  | add _ _ hx hy => obtain ⟨a, rfl⟩ := hx; obtain ⟨b, rfl⟩ := hy; exact ⟨a + b, map_add _ a b⟩
  | smul k _ hx => obtain ⟨a, rfl⟩ := hx; exact ⟨k • a, map_smul _ k a⟩

/-- The canonical `ℤ`-linear equivalence between `MilnorK.degree R n` and the degree-`n`
tensor-power quotient `((⨂[ℤ]^n) (Additive Rˣ)) ⧸ relationSubmodule R n`. -/
noncomputable def degreeEquivQuotient (n : ℕ) :
    degree R n ≃ₗ[ℤ] ((⨂[ℤ]^n) (Additive Rˣ)) ⧸ relationSubmodule R n :=
  ((Submodule.quotEquivOfEq (LinearMap.ker (toDegree R n)) (relationSubmodule R n)
      (ker_toDegree R n)).symm.trans
    (LinearMap.quotKerEquivOfSurjective (toDegree R n) (surjective_toDegree R n))).symm

/-- `(degreeEquivQuotient R n).symm` sends a quotient class `mk t` to `toDegree R n t`. -/
@[simp]
theorem degreeEquivQuotient_symm_mk (n : ℕ) (t : (⨂[ℤ]^n) (Additive Rˣ)) :
    (degreeEquivQuotient R n).symm (Submodule.Quotient.mk t) = toDegree R n t := by
  rw [degreeEquivQuotient, LinearEquiv.symm_symm, LinearEquiv.trans_apply,
    (LinearEquiv.symm_apply_eq _).mpr (Submodule.quotEquivOfEq_mk _ _ (ker_toDegree R n) t).symm,
    LinearMap.quotKerEquivOfSurjective_apply_mk]

/-- `degreeEquivQuotient R n` sends `toDegree R n t` to the quotient class of `t`. -/
@[simp]
theorem degreeEquivQuotient_toDegree (n : ℕ) (t : (⨂[ℤ]^n) (Additive Rˣ)) :
    degreeEquivQuotient R n (toDegree R n t) = Submodule.Quotient.mk t := by
  rw [← degreeEquivQuotient_symm_mk, LinearEquiv.apply_symm_apply]

/-- `degreeEquivQuotient R n` sends a symbol `{a₀, …, aₙ₋₁}` to the quotient class of the
corresponding pure tensor. -/
theorem degreeEquivQuotient_symbol_ofFn {n : ℕ} (a : Fin n → Rˣ) :
    degreeEquivQuotient R n
      ⟨symbol (List.ofFn a), symbol_mem_degree_of_length (List.length_ofFn (f := a))⟩ =
      Submodule.Quotient.mk (PiTensorProduct.tprod ℤ (fun i ↦ Additive.ofMul (a i))) := by
  have h : (⟨symbol (List.ofFn a), symbol_mem_degree_of_length (List.length_ofFn (f := a))⟩ :
      degree R n) = toDegree R n (PiTensorProduct.tprod ℤ (fun i ↦ Additive.ofMul (a i))) :=
    Subtype.ext (by rw [toDegree_tprod]; simp)
  rw [h, degreeEquivQuotient_toDegree]

end DegreeQuotient

section Functoriality

variable {R S : Type*} [CommRing R] [CommRing S]

private noncomputable def mapTensorPower (f : R →+* S) (n : ℕ) :
    (⨂[ℤ]^n) (Additive Rˣ) →ₗ[ℤ] (⨂[ℤ]^n) (Additive Sˣ) :=
  PiTensorProduct.map fun _ ↦ (Units.map f.toMonoidHom).toAdditive.toIntLinearMap

private theorem mapTensorPower_mem_relationSubmodule (f : R →+* S) (n : ℕ)
    {t : (⨂[ℤ]^n) (Additive Rˣ)} (ht : t ∈ relationSubmodule R n) :
    mapTensorPower f n t ∈ relationSubmodule S n := by
  refine map_mem_relationSubmodule (mapTensorPower f n) (fun x i hi hab ↦ ?_) ht
  rw [mapTensorPower, PiTensorProduct.map_tprod]
  refine tprod_mem_relationSubmodule _ (i := i) hi ?_
  simpa [Units.map] using (map_add f _ _).symm.trans ((congrArg f hab).trans (map_one f))

/-- The `ℤ`-linear map on degree-`n` tensor-power quotients induced by a ring homomorphism `f`. -/
noncomputable def mapQuotient (f : R →+* S) (n : ℕ) :
    (((⨂[ℤ]^n) (Additive Rˣ)) ⧸ relationSubmodule R n) →ₗ[ℤ]
      (((⨂[ℤ]^n) (Additive Sˣ)) ⧸ relationSubmodule S n) :=
  Submodule.mapQ (relationSubmodule R n) (relationSubmodule S n) (mapTensorPower f n)
    fun _ ht ↦ mapTensorPower_mem_relationSubmodule f n ht

/-- `mapQuotient f n` acts on quotient classes via `PiTensorProduct.map`. -/
theorem mapQuotient_mk (f : R →+* S) (n : ℕ) (t : (⨂[ℤ]^n) (Additive Rˣ)) :
    mapQuotient f n (Submodule.Quotient.mk t) = Submodule.Quotient.mk
      (PiTensorProduct.map (fun _ ↦ (Units.map f.toMonoidHom).toAdditive.toIntLinearMap) t) := by
  rw [mapQuotient, Submodule.mapQ_apply, mapTensorPower]

/-- `mapQuotient f n` maps a pure tensor `tprod ℤ x` to the pure tensor obtained by applying
`Units.map f.toMonoidHom` entrywise. -/
@[simp]
theorem mapQuotient_mk_tprod (f : R →+* S) {n : ℕ} (x : Fin n → Additive Rˣ) :
    mapQuotient f n (Submodule.Quotient.mk (PiTensorProduct.tprod ℤ x)) =
      Submodule.Quotient.mk (PiTensorProduct.tprod ℤ fun i ↦
        Additive.ofMul (Units.map f.toMonoidHom (Additive.toMul (x i)))) := by
  rw [mapQuotient_mk, PiTensorProduct.map_tprod]
  simp only [AddMonoidHom.coe_toIntLinearMap, MonoidHom.coe_toAdditive, Function.comp_apply]

/-- The quotient bridge `degreeEquivQuotient` is natural with respect to ring homomorphisms. -/
theorem degreeEquivQuotient_mapDegree (f : R →+* S) (n : ℕ) (x : degree R n) :
    degreeEquivQuotient S n (mapDegree f n x) = mapQuotient f n (degreeEquivQuotient R n x) := by
  obtain ⟨t, rfl⟩ := surjective_toDegree R n x
  rw [degreeEquivQuotient_toDegree]
  have hcomm : mapDegree f n (toDegree R n t) = toDegree S n (mapTensorPower f n t) := by
    induction t using PiTensorProduct.induction_on with
    | smul_tprod r y =>
      rw [map_smul, map_smul, map_smul, map_smul]; congr 1
      apply Subtype.ext
      rw [mapDegree_apply, toDegree_tprod, map_symbol, mapTensorPower,
        PiTensorProduct.map_tprod, toDegree_tprod]
      congr 1
      simp only [List.map_ofFn, Function.comp_def, AddMonoidHom.coe_toIntLinearMap,
        MonoidHom.coe_toAdditive, toMul_ofMul, RingHom.toMonoidHom_eq_coe]
    | add _ _ hu hv => rw [map_add, map_add, map_add, map_add, hu, hv]
  rw [hcomm, degreeEquivQuotient_toDegree, mapTensorPower, ← mapQuotient_mk]

end Functoriality

section DegreeTwo

variable (R : Type*) [CommRing R]

private theorem map_relationSubmodule_two :
    (relationSubmodule R 2).map
        ((tensorProductEquivTensorSquare ℤ
          (Additive Rˣ)).symm.toAddEquiv.toIntLinearEquiv.toLinearMap) =
      MatsumotoGroup.steinbergRelations R := by
  refine le_antisymm ?_ ?_
  · rw [relationSubmodule_def, Submodule.map_span_le]
    rintro _ ⟨x, i, hi, hab, rfl⟩
    obtain rfl : i = 0 := by omega
    rw [LinearEquiv.coe_coe, AddEquiv.coe_toIntLinearEquiv, LinearEquiv.coe_toAddEquiv,
      LinearEquiv.coe_addEquiv_apply, tensorProductEquivTensorSquare_symm_tprod,
      MatsumotoGroup.steinbergRelations_def]
    exact Submodule.subset_span ⟨Additive.toMul (x 0), Additive.toMul (x 1), hab, by simp⟩
  · rw [MatsumotoGroup.steinbergRelations_def, Submodule.span_le]
    rintro _ ⟨a, b, hab, rfl⟩
    rw [SetLike.mem_coe, Submodule.mem_map]
    refine ⟨PiTensorProduct.tprod ℤ ![Additive.ofMul a, Additive.ofMul b],
      tprod_mem_relationSubmodule _ (i := 0) (by omega) (by simpa using hab), ?_⟩
    rw [LinearEquiv.coe_coe, AddEquiv.coe_toIntLinearEquiv, LinearEquiv.coe_toAddEquiv,
      LinearEquiv.coe_addEquiv_apply, tensorProductEquivTensorSquare_symm_tprod]
    simp

/-- The canonical `ℤ`-linear equivalence `MilnorK.degree R 2 ≃ₗ[ℤ] MatsumotoGroup R`, taking
`MilnorK.symbol [a, b]` to `MatsumotoGroup.symbol a b`. -/
noncomputable def degreeTwoEquivMatsumotoGroup : degree R 2 ≃ₗ[ℤ] MatsumotoGroup R :=
  (degreeEquivQuotient R 2).trans
    (Submodule.Quotient.equiv (relationSubmodule R 2) (MatsumotoGroup.steinbergRelations R)
      (tensorProductEquivTensorSquare ℤ (Additive Rˣ)).symm.toAddEquiv.toIntLinearEquiv
      (map_relationSubmodule_two R))

/-- `degreeTwoEquivMatsumotoGroup R` sends the two-entry Milnor symbol `{a, b}` to
`MatsumotoGroup.symbol a b`. -/
theorem degreeTwoEquivMatsumotoGroup_symbol_pair (a b : Rˣ) :
    degreeTwoEquivMatsumotoGroup R ⟨symbol [a, b], symbol_mem_degree_of_length rfl⟩ =
      MatsumotoGroup.symbol a b := by
  have hsub : (⟨symbol [a, b], symbol_mem_degree_of_length rfl⟩ : degree R 2) =
      ⟨symbol (List.ofFn ![a, b]), symbol_mem_degree_of_length (List.length_ofFn (f := ![a, b]))⟩ :=
    Subtype.ext (congrArg symbol (by simp))
  rw [hsub, degreeTwoEquivMatsumotoGroup, LinearEquiv.trans_apply, degreeEquivQuotient_symbol_ofFn,
    Submodule.Quotient.equiv_apply, Submodule.mapQ_apply, LinearEquiv.coe_coe,
    AddEquiv.coe_toIntLinearEquiv, LinearEquiv.coe_toAddEquiv, LinearEquiv.coe_addEquiv_apply,
    tensorProductEquivTensorSquare_symm_tprod]
  simp

/-- `degreeTwoEquivMatsumotoGroup R` sends `ofUnit a * ofUnit b` to
`MatsumotoGroup.symbol a b`. -/
@[simp]
theorem degreeTwoEquivMatsumotoGroup_ofUnit_mul (a b : Rˣ) :
    degreeTwoEquivMatsumotoGroup R
      ⟨ofUnit a * ofUnit b,
        SetLike.GradedMul.mul_mem (ofUnit_mem_degree_one a) (ofUnit_mem_degree_one b)⟩ =
      MatsumotoGroup.symbol a b := by
  simpa [Subtype.ext_iff, symbol_pair] using degreeTwoEquivMatsumotoGroup_symbol_pair R a b

/-- `(degreeTwoEquivMatsumotoGroup R).symm` sends `MatsumotoGroup.symbol a b` to the two-entry
Milnor symbol `{a, b}`. -/
@[simp]
theorem degreeTwoEquivMatsumotoGroup_symm_symbol (a b : Rˣ) :
    (degreeTwoEquivMatsumotoGroup R).symm (MatsumotoGroup.symbol a b) =
      ⟨symbol [a, b], symbol_mem_degree_of_length rfl⟩ := by
  rw [LinearEquiv.symm_apply_eq, degreeTwoEquivMatsumotoGroup_symbol_pair]

/-- The degree-two identification `degree R 2 ≃ₗ[ℤ] MatsumotoGroup R` is natural with respect to
ring homomorphisms. -/
theorem degreeTwoEquivMatsumotoGroup_mapDegree {S : Type*} [CommRing S] (f : R →+* S)
    (x : degree R 2) :
    degreeTwoEquivMatsumotoGroup S (mapDegree f 2 x) =
      MatsumotoGroup.map f (degreeTwoEquivMatsumotoGroup R x) := by
  obtain ⟨t, rfl⟩ := surjective_toDegree R 2 x
  simp only [degreeTwoEquivMatsumotoGroup, LinearEquiv.trans_apply, degreeEquivQuotient_mapDegree,
    degreeEquivQuotient_toDegree]
  induction t using PiTensorProduct.induction_on with
  | smul_tprod r y =>
    simp only [Submodule.Quotient.mk_smul, map_smul]
    congr 1
    rw [mapQuotient_mk_tprod, Submodule.Quotient.equiv_apply, Submodule.Quotient.equiv_apply,
      Submodule.mapQ_apply, Submodule.mapQ_apply, LinearEquiv.coe_coe, LinearEquiv.coe_coe,
      AddEquiv.coe_toIntLinearEquiv, AddEquiv.coe_toIntLinearEquiv,
      LinearEquiv.coe_toAddEquiv, LinearEquiv.coe_toAddEquiv,
      LinearEquiv.coe_addEquiv_apply, LinearEquiv.coe_addEquiv_apply,
      tensorProductEquivTensorSquare_symm_tprod, tensorProductEquivTensorSquare_symm_tprod]
    have hy : y 0 ⊗ₜ[ℤ] y 1 =
        Additive.ofMul (Additive.toMul (y 0)) ⊗ₜ[ℤ] Additive.ofMul (Additive.toMul (y 1)) := by
      simp
    rw [hy, MatsumotoGroup.mk_tmul, MatsumotoGroup.mk_tmul, MatsumotoGroup.map_symbol]
  | add _ _ hu hv =>
    simp only [Submodule.Quotient.mk_add, map_add] at hu hv ⊢
    rw [hu, hv]

end DegreeTwo

end MilnorK

end TauCeti

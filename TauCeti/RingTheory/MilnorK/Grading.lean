/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Isomorphisms
public import Mathlib.RingTheory.TwoSidedIdeal.Operations
public import TauCeti.RingTheory.MilnorK.Homogeneous
public import TauCeti.RingTheory.MilnorK.MatsumotoGroup
import Mathlib.Tactic.FinCases
import TauCeti.LinearAlgebra.TensorSquare

/-!
# Steinberg kernel span, quotient functoriality, and degree-two identification of Milnor K-theory

This file complements `TauCeti.RingTheory.MilnorK.Basic` and
`TauCeti.RingTheory.MilnorK.Homogeneous` by identifying the kernel of `MilnorK.mk` as a two-sided
ideal span (`TauCeti.MilnorK.ker_mk_eq_span`), establishing functoriality of the degree-`n`
tensor-power quotients (`TauCeti.MilnorK.mapQuotient`) naturally with `TauCeti.MilnorK.degreeEquiv`
and `TauCeti.MilnorK.mapDegree`, and constructing the canonical degree-2 identification with
`TauCeti.MatsumotoGroup R` (`TauCeti.MilnorK.degreeTwoEquivMatsumotoGroup`).

## Main definitions

* `TauCeti.MilnorK.mapQuotient`: functorial map on degree-`n` tensor-power quotients
  `((⨂[ℤ]^n) (Additive Rˣ)) ⧸ steinbergRelations R n`.
* `TauCeti.MilnorK.degreeTwoEquivMatsumotoGroup`: the canonical equivalence
  `degree R 2 ≃ₗ[ℤ] MatsumotoGroup R`.

## Main results

* `TauCeti.MilnorK.ker_mk_eq_span`: the kernel of `MilnorK.mk` as a `TwoSidedIdeal.span`.
* `TauCeti.MilnorK.mapDegree_degreeEquiv` and `TauCeti.MilnorK.degreeEquiv_symm_mapDegree`:
  naturality of the degree-`n` quotient bridge under ring homomorphisms.
* `TauCeti.MilnorK.degreeTwoEquivMatsumotoGroup_mapDegree`: naturality of the degree-2
  identification with `MatsumotoGroup`.

## References

* C. A. Weibel, *The K-book: An Introduction to Algebraic K-Theory*, §III.7.1, §III.6.1.
* H. Matsumoto, *Sur les sous-groupes arithmétiques des groupes semi-simples déployés*, Section 9.
-/

public section

open scoped DirectSum TensorProduct

namespace TauCeti

namespace MilnorK

section KernelSpan

variable (R : Type*) [CommRing R]

private theorem ringCon_eq_span_ringCon :
    MilnorK.ringCon R =
      (TwoSidedIdeal.span
        {z | ∃ a b : Rˣ, (a : R) + b = 1 ∧
          z = TensorAlgebra.ι ℤ (Additive.ofMul a) *
            TensorAlgebra.ι ℤ (Additive.ofMul b)}).ringCon := by
  refine le_antisymm ?_ ?_
  · rw [MilnorK.ringCon_eq, RingCon.ringConGen_le]
    rintro _ _ h
    rcases (milnorRel_iff R).mp h with ⟨a, b, hab, rfl, rfl⟩
    rw [TwoSidedIdeal.rel_iff, sub_zero]
    exact TwoSidedIdeal.subset_span ⟨a, b, hab, rfl⟩
  · refine (TwoSidedIdeal.ringCon_le_iff
      (J := TwoSidedIdeal.ofRingCon (MilnorK.ringCon R))).mp (TwoSidedIdeal.span_le.mpr ?_)
    rintro _ ⟨a, b, hab, rfl⟩
    rw [SetLike.mem_coe, TwoSidedIdeal.mem_ofRingCon, MilnorK.ringCon_eq]
    exact RingConGen.Rel.of _ _ ((milnorRel_iff R).mpr ⟨a, b, hab, rfl, rfl⟩)

/-- The kernel of `MilnorK.mk` is the two-sided ideal of `TensorAlgebra ℤ (Additive Rˣ)` generated
by the Steinberg products `ι ℤ (Additive.ofMul a) * ι ℤ (Additive.ofMul b)` with
`(a : R) + b = 1`. -/
theorem ker_mk_eq_span :
    RingHom.ker (mk (R := R)) =
      (TwoSidedIdeal.span
        {z | ∃ a b : Rˣ, (a : R) + b = 1 ∧
          z = TensorAlgebra.ι ℤ (Additive.ofMul a) *
            TensorAlgebra.ι ℤ (Additive.ofMul b)}).asIdeal := by
  ext z
  rw [RingHom.mem_ker, ← map_zero (mk (R := R)), mk_eq_mk_iff, ← MilnorK.ringCon_eq,
    ringCon_eq_span_ringCon, TwoSidedIdeal.mem_asIdeal, TwoSidedIdeal.mem_iff]

end KernelSpan

section QuotientFunctoriality

variable {R S : Type*} [CommRing R] [CommRing S]

private noncomputable def mapTensorPower (f : R →+* S) (n : ℕ) :
    (⨂[ℤ]^n) (Additive Rˣ) →ₗ[ℤ] (⨂[ℤ]^n) (Additive Sˣ) :=
  PiTensorProduct.map fun _ ↦ (Units.map f.toMonoidHom).toAdditive.toIntLinearMap

private theorem mapTensorPower_mem_steinbergRelations (f : R →+* S) (n : ℕ)
    {t : (⨂[ℤ]^n) (Additive Rˣ)} (ht : t ∈ steinbergRelations R n) :
    mapTensorPower f n t ∈ steinbergRelations S n := by
  refine (Submodule.map_span_le (mapTensorPower f n) _ _).mpr ?_
    (Submodule.mem_map_of_mem (steinbergRelations_eq_span R n ▸ ht))
  rintro _ ⟨g, i, hi, hab, rfl⟩
  rw [mapTensorPower, PiTensorProduct.map_tprod]
  change (PiTensorProduct.tprod ℤ fun k ↦ Additive.ofMul (Units.map f.toMonoidHom (g k))) ∈
    steinbergRelations S n
  refine tprod_mem_steinbergRelations _ i hi ?_
  simpa [Units.map] using (map_add f _ _).symm.trans ((congrArg f hab).trans (map_one f))

/-- The `ℤ`-linear map on degree-`n` tensor-power quotients induced by a ring homomorphism `f`. -/
noncomputable def mapQuotient (f : R →+* S) (n : ℕ) :
    (((⨂[ℤ]^n) (Additive Rˣ)) ⧸ steinbergRelations R n) →ₗ[ℤ]
      (((⨂[ℤ]^n) (Additive Sˣ)) ⧸ steinbergRelations S n) :=
  Submodule.mapQ (steinbergRelations R n) (steinbergRelations S n) (mapTensorPower f n)
    fun _ ht ↦ mapTensorPower_mem_steinbergRelations f n ht

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

private theorem quotient_linearMap_ext {A : Type*} [AddCommGroup A] {n : ℕ}
    {φ ψ : (((⨂[ℤ]^n) (Additive Rˣ)) ⧸ steinbergRelations R n) →ₗ[ℤ] A}
    (h : ∀ x : Fin n → Additive Rˣ,
      φ (Submodule.Quotient.mk (PiTensorProduct.tprod ℤ x)) =
        ψ (Submodule.Quotient.mk (PiTensorProduct.tprod ℤ x))) :
    φ = ψ := by
  refine LinearMap.ext fun q ↦ ?_
  obtain ⟨t, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  induction t using PiTensorProduct.induction_on with
  | smul_tprod r x => simp only [Submodule.Quotient.mk_smul, map_smul, h x]
  | add _ _ hx hy => simp only [Submodule.Quotient.mk_add, map_add, hx, hy]

/-- `MilnorK.mapQuotient` preserves the identity ring homomorphism. -/
@[simp]
theorem mapQuotient_id (n : ℕ) : mapQuotient (RingHom.id R) n = LinearMap.id :=
  quotient_linearMap_ext fun x ↦ by
    simp only [mapQuotient_mk_tprod, RingHom.toMonoidHom_eq_coe, LinearMap.id_apply]
    congr 2

/-- `MilnorK.mapQuotient` preserves composition of ring homomorphisms. -/
theorem mapQuotient_comp {T : Type*} [CommRing T] (g : S →+* T) (f : R →+* S) (n : ℕ) :
    mapQuotient (g.comp f) n = (mapQuotient g n).comp (mapQuotient f n) :=
  quotient_linearMap_ext fun x ↦ by
    simp only [LinearMap.comp_apply, mapQuotient_mk_tprod, toMul_ofMul, RingHom.toMonoidHom_eq_coe]
    congr 2

/-- `degreeEquiv` intertwines `mapQuotient f n` and `mapDegree f n`. -/
theorem mapDegree_degreeEquiv (f : R →+* S) (n : ℕ)
    (q : ((⨂[ℤ]^n) (Additive Rˣ)) ⧸ steinbergRelations R n) :
    mapDegree f n (degreeEquiv R n q) = degreeEquiv S n (mapQuotient f n q) := by
  refine LinearMap.congr_fun
    (f := (mapDegree f n).comp (degreeEquiv R n).toLinearMap)
    (g := (degreeEquiv S n).toLinearMap.comp (mapQuotient f n))
    (quotient_linearMap_ext fun x ↦ Subtype.ext ?_) q
  have hx : PiTensorProduct.tprod ℤ x =
      PiTensorProduct.tprod ℤ fun k ↦ Additive.ofMul (Additive.toMul (x k)) := rfl
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, mapDegree_apply, coe_degreeEquiv_mk,
    mapQuotient_mk_tprod]
  rw [hx, ofTensorPower_tprod, ofTensorPower_tprod, map_symbol]
  congr 1
  simp [List.map_ofFn, Function.comp_def]

/-- `(degreeEquiv _ n).symm` intertwines `mapDegree f n` and `mapQuotient f n`. -/
theorem degreeEquiv_symm_mapDegree (f : R →+* S) (n : ℕ) (x : degree R n) :
    (degreeEquiv S n).symm (mapDegree f n x) =
      mapQuotient f n ((degreeEquiv R n).symm x) := by
  rw [LinearEquiv.symm_apply_eq, ← mapDegree_degreeEquiv, LinearEquiv.apply_symm_apply]

end QuotientFunctoriality

section DegreeTwo

variable (R : Type*) [CommRing R]

@[simp]
private theorem tensorProductEquivTensorSquare_symm_int_tprod (x : Fin 2 → Additive Rˣ) :
    ((tensorProductEquivTensorSquare ℤ (Additive Rˣ)).symm.toAddEquiv.toIntLinearEquiv :
        (⨂[ℤ]^2 (Additive Rˣ)) ≃ₗ[ℤ] Additive Rˣ ⊗[ℤ] Additive Rˣ)
      (PiTensorProduct.tprod ℤ x) = x 0 ⊗ₜ[ℤ] x 1 := by
  simp [tensorProductEquivTensorSquare_symm_tprod]

private theorem map_steinbergRelations_two :
    (steinbergRelations R 2).map
        ((tensorProductEquivTensorSquare ℤ
          (Additive Rˣ)).symm.toAddEquiv.toIntLinearEquiv.toLinearMap) =
      MatsumotoGroup.steinbergRelations R := by
  refine le_antisymm ?_ ?_
  · rw [steinbergRelations_eq_span, Submodule.map_span_le]
    rintro _ ⟨f, i, hi, hab, rfl⟩
    obtain rfl : i = 0 := by omega
    rw [LinearEquiv.coe_coe, tensorProductEquivTensorSquare_symm_int_tprod,
      MatsumotoGroup.steinbergRelations_def]
    exact Submodule.subset_span ⟨f 0, f 1, hab, rfl⟩
  · rw [MatsumotoGroup.steinbergRelations_def, Submodule.span_le]
    rintro _ ⟨a, b, hab, rfl⟩
    rw [SetLike.mem_coe, Submodule.mem_map]
    refine ⟨PiTensorProduct.tprod ℤ ![Additive.ofMul a, Additive.ofMul b], ?_, ?_⟩
    · have h : (fun k ↦ Additive.ofMul (![a, b] k)) = ![Additive.ofMul a, Additive.ofMul b] := by
        ext k; fin_cases k <;> rfl
      rw [← h]
      exact tprod_mem_steinbergRelations ![a, b] 0 (by omega) (by simpa using hab)
    · rw [LinearEquiv.coe_coe, tensorProductEquivTensorSquare_symm_int_tprod]
      simp

/-- The canonical `ℤ`-linear equivalence `MilnorK.degree R 2 ≃ₗ[ℤ] MatsumotoGroup R`, taking
`MilnorK.symbol [a, b]` to `MatsumotoGroup.symbol a b`. -/
noncomputable def degreeTwoEquivMatsumotoGroup : degree R 2 ≃ₗ[ℤ] MatsumotoGroup R :=
  (degreeEquiv R 2).symm.trans
    (Submodule.Quotient.equiv (steinbergRelations R 2) (MatsumotoGroup.steinbergRelations R)
      (tensorProductEquivTensorSquare ℤ (Additive Rˣ)).symm.toAddEquiv.toIntLinearEquiv
      (map_steinbergRelations_two R))

/-- `degreeTwoEquivMatsumotoGroup R` sends the image of a pure tensor `tprod ℤ x` in degree `2`
to `MatsumotoGroup.symbol (toMul (x 0)) (toMul (x 1))`. -/
@[simp]
theorem degreeTwoEquivMatsumotoGroup_degreeEquiv_mk (x : Fin 2 → Additive Rˣ) :
    degreeTwoEquivMatsumotoGroup R
        (degreeEquiv R 2 (Submodule.Quotient.mk (PiTensorProduct.tprod ℤ x))) =
      MatsumotoGroup.symbol (Additive.toMul (x 0)) (Additive.toMul (x 1)) := by
  rw [degreeTwoEquivMatsumotoGroup, LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply,
    Submodule.Quotient.equiv_apply, Submodule.mapQ_apply, LinearEquiv.coe_coe,
    tensorProductEquivTensorSquare_symm_int_tprod]
  simpa using MatsumotoGroup.mk_tmul (Additive.toMul (x 0)) (Additive.toMul (x 1))

/-- `degreeTwoEquivMatsumotoGroup R` sends the two-entry Milnor symbol `{a, b}` to
`MatsumotoGroup.symbol a b`. -/
theorem degreeTwoEquivMatsumotoGroup_symbol_pair (a b : Rˣ) :
    degreeTwoEquivMatsumotoGroup R ⟨symbol [a, b], symbol_mem_degree_of_length rfl⟩ =
      MatsumotoGroup.symbol a b := by
  have hsub : (⟨symbol [a, b], symbol_mem_degree_of_length rfl⟩ : degree R 2) =
      degreeEquiv R 2 (Submodule.Quotient.mk
        (PiTensorProduct.tprod ℤ ![Additive.ofMul a, Additive.ofMul b])) := by
    apply Subtype.ext
    rw [coe_degreeEquiv_mk]
    have h : (fun k ↦ Additive.ofMul (![a, b] k)) = ![Additive.ofMul a, Additive.ofMul b] := by
      ext k; fin_cases k <;> rfl
    rw [← h, ofTensorPower_tprod]
    simp [List.ofFn_succ]
  rw [hsub, degreeTwoEquivMatsumotoGroup_degreeEquiv_mk]
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
  obtain ⟨q, rfl⟩ := (degreeEquiv R 2).surjective x
  refine LinearMap.congr_fun
    (f := (degreeTwoEquivMatsumotoGroup S).toLinearMap.comp
      ((mapDegree f 2).comp (degreeEquiv R 2).toLinearMap))
    (g := (MatsumotoGroup.map f).comp
      ((degreeTwoEquivMatsumotoGroup R).toLinearMap.comp (degreeEquiv R 2).toLinearMap))
    (quotient_linearMap_ext fun y ↦ ?_) q
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, mapDegree_degreeEquiv,
    mapQuotient_mk_tprod, degreeTwoEquivMatsumotoGroup_degreeEquiv_mk,
    MatsumotoGroup.map_symbol, toMul_ofMul]

end DegreeTwo

end MilnorK

end TauCeti

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Isomorphisms
public import Mathlib.LinearAlgebra.TensorAlgebra.ToTensorPower
public import Mathlib.LinearAlgebra.TensorPower.Basic
public import TauCeti.FieldTheory.MilnorK.Basic
public import TauCeti.FieldTheory.MilnorK.SymbolGroup

/-!
# Homogeneous quotient bridge and low-degree identifications of Milnor K-theory

This file bridges `MilnorK.degree R n` with the homogeneous tensor-power quotients
`(⨂[ℤ]^n (Additive Rˣ)) ⧸ MilnorK.relationSubmodule R n` naturally in `R`, and derives the
canonical degree-0, degree-1, and degree-2 identifications with `ℤ`, `Additive Rˣ`, and
`SymbolGroup R`.

## Main definitions

* `TauCeti.MilnorK.toDegree`: the canonical surjection `(⨂[ℤ]^n) (Additive Rˣ) →ₗ[ℤ] degree R n`.
* `TauCeti.MilnorK.degreeEquivQuotient`: the canonical linear equivalence
  `degree R n ≃ₗ[ℤ] ((⨂[ℤ]^n) (Additive Rˣ)) ⧸ relationSubmodule R n`.
* `TauCeti.MilnorK.directSumDegreeEquiv`: the graded algebra equivalence
  `(⨁ n : ℕ, degree R n) ≃ₐ[ℤ] MilnorK R`.
* `TauCeti.MilnorK.mapQuotient`: functorial map on degree-`n` tensor-power quotients.
* `TauCeti.MilnorK.degreeZeroEquiv`: the canonical equivalence `degree R 0 ≃ₗ[ℤ] ℤ`.
* `TauCeti.MilnorK.degreeOneEquiv`: the canonical equivalence `degree R 1 ≃ₗ[ℤ] Additive Rˣ`.
* `TauCeti.MilnorK.degreeTwoEquivSymbolGroup`: the canonical equivalence
  `degree R 2 ≃ₗ[ℤ] SymbolGroup R`.

## Main results

* `TauCeti.MilnorK.degreeEquivQuotient_mapDegree`: naturality of the degree-`n` quotient bridge
  under ring homomorphisms.
* `TauCeti.MilnorK.intCast_injective`, `TauCeti.MilnorK.nontrivial`, and
  `TauCeti.MilnorK.ofUnit_injective`: injectivity of the degree-0 and degree-1 embeddings.
* `TauCeti.MilnorK.degreeTwoEquivSymbolGroup_mapDegree`: naturality of the degree-2 identification
  with `SymbolGroup`.

## References

* C. A. Weibel, *The K-book: An Introduction to Algebraic K-Theory*, Definition III.7.1 and
  Section III.6.1.
* H. Matsumoto, *Sur les sous-groupes arithmétiques des groupes semi-simples déployés*, Section 9.
-/

public section

namespace TauCeti

open scoped DirectSum TensorProduct

universe u

namespace MilnorK

section DegreeQuotient

variable (R : Type u) [CommSemiring R]

/-- The canonical `ℤ`-linear surjection `(⨂[ℤ]^n) (Additive Rˣ) →ₗ[ℤ] MilnorK.degree R n`. -/
noncomputable def toDegree (n : ℕ) : (⨂[ℤ]^n) (Additive Rˣ) →ₗ[ℤ] degree R n where
  toFun t := ⟨RingQuot.mkRingHom (milnorRel R) (TensorPower.toTensorAlgebra t),
    degree_def R n ▸
      ⟨TensorPower.toTensorAlgebra t, TensorPower.toTensorAlgebra_mem_range_pow t, rfl⟩⟩
  map_add' _ _ := Subtype.ext (by simp)
  map_smul' _ _ := Subtype.ext (by simp)

/-- Underlying element of `toDegree R n t` in `MilnorK R`. -/
@[simp]
theorem coe_toDegree (n : ℕ) (t : (⨂[ℤ]^n) (Additive Rˣ)) :
    (toDegree R n t : MilnorK R) =
      RingQuot.mkRingHom (milnorRel R) (TensorPower.toTensorAlgebra t) := by
  rw [toDegree, LinearMap.coe_mk, AddHom.coe_mk]

/-- `toDegree R n` maps a pure tensor `tprod ℤ x` to the corresponding Milnor symbol. -/
theorem toDegree_tprod {n : ℕ} (x : Fin n → Additive Rˣ) :
    (toDegree R n (PiTensorProduct.tprod ℤ x) : MilnorK R) =
      symbol (List.ofFn fun i ↦ Additive.toMul (x i)) := by
  rw [coe_toDegree, mkRingHom_toTensorAlgebra_tprod]

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

/-- The canonical graded `ℤ`-algebra equivalence `(⨁ n : ℕ, MilnorK.degree R n) ≃ₐ[ℤ] MilnorK R`. -/
noncomputable def directSumDegreeEquiv : (⨁ n : ℕ, degree R n) ≃ₐ[ℤ] MilnorK R :=
  (isInternal_degree R).coeAlgEquiv

end DegreeQuotient

section Functoriality

variable {R : Type u} {S : Type*} [CommSemiring R] [CommSemiring S]

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
        MonoidHom.coe_toAdditive, toMul_ofMul]
    | add _ _ hu hv => rw [map_add, map_add, map_add, map_add, hu, hv]
  rw [hcomm, degreeEquivQuotient_toDegree, mapTensorPower, ← mapQuotient_mk]

end Functoriality

section LowDegrees

variable (R : Type u) [CommSemiring R]

/-- The canonical `ℤ`-linear equivalence `MilnorK.degree R 0 ≃ₗ[ℤ] ℤ`. -/
noncomputable def degreeZeroEquiv : degree R 0 ≃ₗ[ℤ] ℤ :=
  (degreeEquivQuotient R 0).trans
    ((Submodule.quotEquivOfEqBot (relationSubmodule R 0) (relationSubmodule_zero R)).trans
      (PiTensorProduct.isEmptyEquiv (Fin 0)))

/-- `(degreeZeroEquiv R).symm k` has underlying value `(k : MilnorK R)`. -/
@[simp]
theorem degreeZeroEquiv_symm_apply (k : ℤ) :
    ((degreeZeroEquiv R).symm k : MilnorK R) = (k : MilnorK R) := by
  have hk : (PiTensorProduct.isEmptyEquiv (Fin 0) (R := ℤ) (s := fun _ ↦ Additive Rˣ)).symm k =
      k • PiTensorProduct.tprod ℤ Fin.elim0 :=
    (LinearEquiv.symm_apply_eq _).mpr (by
      rw [map_zsmul, PiTensorProduct.isEmptyEquiv_apply_tprod, smul_eq_mul, mul_one])
  rw [degreeZeroEquiv, LinearEquiv.trans_symm, LinearEquiv.trans_apply, LinearEquiv.trans_symm,
    LinearEquiv.trans_apply, hk, Submodule.quotEquivOfEqBot_symm_apply,
    degreeEquivQuotient_symm_mk, coe_toDegree, map_zsmul, map_zsmul,
    TensorPower.toTensorAlgebra_tprod, TensorAlgebra.tprod_apply]
  simp [zsmul_eq_mul]

/-- `degreeZeroEquiv R` sends `1 ∈ MilnorK.degree R 0` to `1 : ℤ`. -/
@[simp]
theorem degreeZeroEquiv_one : degreeZeroEquiv R ⟨1, one_mem_degree_zero⟩ = 1 :=
  (degreeZeroEquiv R).symm.injective <| Subtype.ext <| by
    rw [LinearEquiv.symm_apply_apply, degreeZeroEquiv_symm_apply, Int.cast_one]

/-- The canonical integer map `ℤ → MilnorK R` is injective for every commutative semiring `R`. -/
theorem intCast_injective : Function.Injective (Int.cast : ℤ → MilnorK R) := fun _ _ h ↦
  (degreeZeroEquiv R).symm.injective <|
    Subtype.ext (by rw [degreeZeroEquiv_symm_apply, degreeZeroEquiv_symm_apply, h])

/-- `MilnorK R` is nontrivial for every commutative semiring `R`. -/
instance nontrivial : Nontrivial (MilnorK R) := (intCast_injective R).nontrivial

/-- The canonical `ℤ`-linear equivalence `MilnorK.degree R 1 ≃ₗ[ℤ] Additive Rˣ`. -/
noncomputable def degreeOneEquiv : degree R 1 ≃ₗ[ℤ] Additive Rˣ :=
  (degreeEquivQuotient R 1).trans
    ((Submodule.quotEquivOfEqBot (relationSubmodule R 1) (relationSubmodule_one R)).trans
      (PiTensorProduct.subsingletonEquiv (0 : Fin 1)))

/-- `(degreeOneEquiv R).symm (Additive.ofMul a)` has underlying value `MilnorK.ofUnit a`. -/
@[simp]
theorem degreeOneEquiv_symm_ofMul (a : Rˣ) :
    ((degreeOneEquiv R).symm (Additive.ofMul a) : MilnorK R) = ofUnit a := by
  rw [degreeOneEquiv, LinearEquiv.trans_symm, LinearEquiv.trans_apply, LinearEquiv.trans_symm,
    LinearEquiv.trans_apply, PiTensorProduct.subsingletonEquiv_symm_apply',
    Submodule.quotEquivOfEqBot_symm_apply, degreeEquivQuotient_symm_mk, toDegree_tprod]
  simp

/-- `degreeOneEquiv R` sends `ofUnit a ∈ MilnorK.degree R 1` to `Additive.ofMul a`. -/
@[simp]
theorem degreeOneEquiv_ofUnit (a : Rˣ) :
    degreeOneEquiv R ⟨ofUnit a, ofUnit_mem_degree_one a⟩ = Additive.ofMul a :=
  (degreeOneEquiv R).symm.injective <| Subtype.ext <| by
    rw [LinearEquiv.symm_apply_apply, degreeOneEquiv_symm_ofMul]

/-- `MilnorK.ofUnit : Rˣ → MilnorK R` is injective for every commutative semiring `R`. -/
theorem ofUnit_injective : Function.Injective (ofUnit (R := R)) := fun a b h ↦ by
  have h' : (⟨ofUnit a, ofUnit_mem_degree_one a⟩ : degree R 1) =
      ⟨ofUnit b, ofUnit_mem_degree_one b⟩ := Subtype.ext h
  have h'' := congrArg (degreeOneEquiv R) h'
  rw [degreeOneEquiv_ofUnit, degreeOneEquiv_ofUnit] at h''
  exact Additive.ofMul.injective h''

private noncomputable def tensorPowerTwoToSymbolGroup :
    (⨂[ℤ]^2) (Additive Rˣ) →ₗ[ℤ] SymbolGroup R :=
  PiTensorProduct.lift
    { toFun := fun x ↦ SymbolGroup.symbol (Additive.toMul (x 0)) (Additive.toMul (x 1))
      map_update_add' := fun _ i _ _ ↦ by
        fin_cases i <;> simp [SymbolGroup.symbol_mul_left, SymbolGroup.symbol_mul_right]
      map_update_smul' := fun _ i _ _ ↦ by
        fin_cases i <;> simp [SymbolGroup.symbol_zpow_left, SymbolGroup.symbol_zpow_right] }

private theorem relationSubmodule_two_le_ker_toSymbolGroup :
    relationSubmodule R 2 ≤ LinearMap.ker (tensorPowerTwoToSymbolGroup R) := by
  rw [relationSubmodule_def, Submodule.span_le]
  rintro _ ⟨x, i, hi, hab, rfl⟩
  obtain rfl : i = 0 := by omega
  rw [SetLike.mem_coe, LinearMap.mem_ker, tensorPowerTwoToSymbolGroup, PiTensorProduct.lift.tprod]
  exact SymbolGroup.symbol_eq_zero_of_add_eq_one hab

private noncomputable def degreeTwoToSymbolGroup : degree R 2 →ₗ[ℤ] SymbolGroup R :=
  (Submodule.liftQ (relationSubmodule R 2) (tensorPowerTwoToSymbolGroup R)
      (relationSubmodule_two_le_ker_toSymbolGroup R)).comp
    (degreeEquivQuotient R 2).toLinearMap

private theorem degreeTwoToSymbolGroup_symbol_pair (a b : Rˣ) :
    degreeTwoToSymbolGroup R ⟨symbol [a, b], symbol_mem_degree_of_length rfl⟩ =
      SymbolGroup.symbol a b := by
  have hsub : (⟨symbol [a, b], symbol_mem_degree_of_length rfl⟩ : degree R 2) =
      ⟨symbol (List.ofFn ![a, b]), symbol_mem_degree_of_length (List.length_ofFn (f := ![a, b]))⟩ :=
    Subtype.ext (congrArg symbol (by simp))
  rw [hsub]
  dsimp only [degreeTwoToSymbolGroup, LinearMap.comp_apply, LinearEquiv.coe_coe]
  rw [degreeEquivQuotient_symbol_ofFn, Submodule.liftQ_apply, tensorPowerTwoToSymbolGroup,
    PiTensorProduct.lift.tprod]
  simp

private noncomputable def symbolGroupToDegreeTwo : SymbolGroup R →ₗ[ℤ] degree R 2 :=
  SymbolGroup.lift (fun a b ↦ ⟨symbol [a, b], symbol_mem_degree_of_length rfl⟩)
    { map_mul_left := fun _ _ _ ↦ Subtype.ext (by simp [symbol_pair, ofUnit_mul, add_mul])
      map_mul_right := fun _ _ _ ↦ Subtype.ext (by simp [symbol_pair, ofUnit_mul, mul_add])
      steinberg := fun hab ↦ Subtype.ext (by
        simpa [symbol_pair] using ofUnit_mul_ofUnit_eq_zero_of_add_eq_one hab) }

private theorem symbolGroupToDegreeTwo_symbol (a b : Rˣ) :
    symbolGroupToDegreeTwo R (SymbolGroup.symbol a b) =
      ⟨symbol [a, b], symbol_mem_degree_of_length rfl⟩ :=
  SymbolGroup.lift_symbol _ _ a b

/-- The canonical `ℤ`-linear equivalence `MilnorK.degree R 2 ≃ₗ[ℤ] SymbolGroup R`, taking
`MilnorK.symbol [a, b]` to `SymbolGroup.symbol a b`. -/
noncomputable def degreeTwoEquivSymbolGroup : degree R 2 ≃ₗ[ℤ] SymbolGroup R :=
  LinearEquiv.ofLinearMap (degreeTwoToSymbolGroup R) (symbolGroupToDegreeTwo R)
    (LinearMap.ext fun q ↦ by
      induction q using SymbolGroup.inductionOn with
      | symbol a b => simp [symbolGroupToDegreeTwo_symbol, degreeTwoToSymbolGroup_symbol_pair]
      | add _ _ hx hy =>
        simp only [LinearMap.comp_apply, LinearMap.id_apply, map_add] at hx hy ⊢; rw [hx, hy])
    (LinearMap.ext fun x ↦ by
      induction x using degree_inductionOn with
      | zero => simp
      | symbol l hl =>
        match l, hl with
        | [a, b], _ => simp [degreeTwoToSymbolGroup_symbol_pair, symbolGroupToDegreeTwo_symbol]
      | add _ _ hx hy =>
        simp only [LinearMap.comp_apply, LinearMap.id_apply, map_add] at hx hy ⊢; rw [hx, hy]
      | smul _ _ hx =>
        simp only [LinearMap.comp_apply, LinearMap.id_apply, map_smul] at hx ⊢; rw [hx])

/-- `degreeTwoEquivSymbolGroup R` sends the two-entry Milnor symbol `{a, b}` to
`SymbolGroup.symbol a b`. -/
@[simp]
theorem degreeTwoEquivSymbolGroup_symbol_pair (a b : Rˣ) :
    degreeTwoEquivSymbolGroup R ⟨symbol [a, b], symbol_mem_degree_of_length rfl⟩ =
      SymbolGroup.symbol a b :=
  degreeTwoToSymbolGroup_symbol_pair R a b

/-- `(degreeTwoEquivSymbolGroup R).symm` sends `SymbolGroup.symbol a b` to the two-entry Milnor
symbol `{a, b}`. -/
@[simp]
theorem degreeTwoEquivSymbolGroup_symm_symbol (a b : Rˣ) :
    (degreeTwoEquivSymbolGroup R).symm (SymbolGroup.symbol a b) =
      ⟨symbol [a, b], symbol_mem_degree_of_length rfl⟩ :=
  symbolGroupToDegreeTwo_symbol R a b

/-- The degree-two identification `degree R 2 ≃ₗ[ℤ] SymbolGroup R` is natural with respect to ring
homomorphisms. -/
theorem degreeTwoEquivSymbolGroup_mapDegree {S : Type*} [CommSemiring S] (f : R →+* S)
    (x : degree R 2) :
    degreeTwoEquivSymbolGroup S (mapDegree f 2 x) =
      SymbolGroup.map f (degreeTwoEquivSymbolGroup R x) := by
  induction x using degree_inductionOn with
  | zero => simp
  | symbol l hl =>
    match l, hl with
    | [a, b], _ =>
      have hmap : mapDegree f 2 ⟨symbol [a, b], symbol_mem_degree_of_length rfl⟩ =
          ⟨symbol [Units.map f.toMonoidHom a, Units.map f.toMonoidHom b],
            symbol_mem_degree_of_length rfl⟩ :=
        Subtype.ext (by rw [mapDegree_apply, map_symbol]; simp)
      rw [hmap, degreeTwoEquivSymbolGroup_symbol_pair, degreeTwoEquivSymbolGroup_symbol_pair,
        SymbolGroup.map_symbol]
  | add _ _ hx hy => rw [map_add, map_add, map_add, map_add, hx, hy]
  | smul _ _ hx => rw [map_smul, map_smul, map_smul, map_smul, hx]

end LowDegrees

end MilnorK

end TauCeti

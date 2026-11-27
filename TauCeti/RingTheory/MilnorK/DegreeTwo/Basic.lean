/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.MatsumotoGroup.Basic
public import TauCeti.RingTheory.MilnorK.Homogeneous
import TauCeti.LinearAlgebra.TensorPower.Basic

/-!
# Degree-two identification of Milnor K-theory

Using the homogeneous presentation `TauCeti.MilnorK.degreeEquiv` from
`TauCeti.RingTheory.MilnorK.Homogeneous`, this file identifies the degree-two Milnor K-group
`K₂ᴹ(R)` of any commutative ring `R` with `TauCeti.MatsumotoGroup R`
(`TauCeti.MilnorK.degreeTwoEquiv`) and proves naturality of `degreeTwoEquiv` with respect to
`TauCeti.MilnorK.mapDegree`.

## Main definitions

* `TauCeti.MilnorK.degreeTwoEquiv`: `K₂ᴹ(R) ≃ₗ[ℤ] MatsumotoGroup R`, sending `{a} * {b}` to
  `MatsumotoGroup.symbol a b`.

## Main results

* `TauCeti.MilnorK.degreeTwo_linearMap_ext`: extensionality for `ℤ`-linear maps out of
  `degree R 2`.
* `TauCeti.MilnorK.degreeTwoEquiv_mapDegree`: naturality of `degreeTwoEquiv` with respect to
  `MatsumotoGroup.map`.

## References

* J. Milnor, *Algebraic K-theory and quadratic forms*, Invent. Math. **9** (1970), §1.
* C. A. Weibel, *The K-book: An Introduction to Algebraic K-Theory*, Chapter III, Theorem 6.1 and
  §7.1.
-/

public section

noncomputable section

open scoped TensorProduct

namespace TauCeti.MilnorK

universe u

section CommRing

variable {R : Type u} [CommRing R]

/-- In `MilnorK.degree R 2`, the symbol `{a, b}` equals `ofUnit a * ofUnit b`. -/
theorem degreeTwo_symbol_eq_ofUnit_mul (a b : Rˣ) :
    (⟨symbol [a, b], symbol_mem_degree_of_length rfl⟩ : degree R 2) =
      ⟨ofUnit a * ofUnit b, ofUnit_mul_mem_degree_two a b⟩ :=
  Subtype.ext (by simp)

/-- Two `ℤ`-linear maps out of `degree R 2` agree if they agree on all products
`ofUnit a * ofUnit b`. -/
theorem degreeTwo_linearMap_ext {A : Type*} [AddCommMonoid A] [Module ℤ A]
    {f g : degree R 2 →ₗ[ℤ] A}
    (h : ∀ a b : Rˣ,
      f ⟨ofUnit a * ofUnit b, ofUnit_mul_mem_degree_two a b⟩ =
        g ⟨ofUnit a * ofUnit b, ofUnit_mul_mem_degree_two a b⟩) :
    f = g :=
  degree_linearMap_ext fun l hl => match l, hl with
    | [a, b], _ => by rw [degreeTwo_symbol_eq_ofUnit_mul]; exact h a b

/-- Auxiliary `ℤ`-linear map from `⨂[ℤ]^2 (Additive Rˣ)` to `MatsumotoGroup R`. -/
private def tensorPowerTwoToMatsumotoGroup (R : Type u) [CommRing R] :
    ⨂[ℤ]^2 (Additive Rˣ) →ₗ[ℤ] MatsumotoGroup R :=
  (MatsumotoGroup.steinbergRelations R).mkQ ∘ₗ
    (TauCeti.TensorPower.twoEquiv ℤ (Additive Rˣ)).symm.toLinearMap

private theorem tensorPowerTwoToMatsumotoGroup_tprod (a b : Rˣ) :
    tensorPowerTwoToMatsumotoGroup R
      (PiTensorProduct.tprod ℤ ![Additive.ofMul a, Additive.ofMul b]) =
        MatsumotoGroup.symbol a b :=
  (congrArg (MatsumotoGroup.steinbergRelations R).mkQ
    (TauCeti.TensorPower.twoEquiv_symm_tprod ℤ (Additive Rˣ)
      (Additive.ofMul a) (Additive.ofMul b))).trans (MatsumotoGroup.mk_tmul a b)

private theorem steinbergRelations_two_le_ker (R : Type u) [CommRing R] :
    steinbergRelations R 2 ≤ LinearMap.ker (tensorPowerTwoToMatsumotoGroup R) := by
  rw [steinbergRelations_eq_span, Submodule.span_le]
  rintro _ ⟨f, i, hi, h, rfl⟩
  have hi0 : i = 0 := by omega
  subst hi0
  have hf : (fun k : Fin 2 => Additive.ofMul (f k)) =
      ![Additive.ofMul (f 0), Additive.ofMul (f 1)] := by
    ext k; fin_cases k <;> rfl
  rw [SetLike.mem_coe, LinearMap.mem_ker, hf, tensorPowerTwoToMatsumotoGroup_tprod]
  exact MatsumotoGroup.symbol_of_add_eq_one h

/-- Auxiliary `ℤ`-linear map `MatsumotoGroup R →ₗ[ℤ] degree R 2` sending `{a, b}` to `a * b`. -/
private def matsumotoGroupToDegreeTwo (R : Type u) [CommRing R] :
    MatsumotoGroup R →ₗ[ℤ] degree R 2 :=
  MatsumotoGroup.liftLinear (fun a b : Rˣ => ⟨ofUnit a * ofUnit b, ofUnit_mul_mem_degree_two a b⟩)
    (isSteinbergPairing_ofUnit_mul.codRestrict (degree R 2) ofUnit_mul_mem_degree_two)

private theorem matsumotoGroupToDegreeTwo_symbol (a b : Rˣ) :
    matsumotoGroupToDegreeTwo R (MatsumotoGroup.symbol a b) =
      ⟨ofUnit a * ofUnit b, ofUnit_mul_mem_degree_two a b⟩ :=
  MatsumotoGroup.liftLinear_symbol _ _ a b

private theorem degreeEquiv_symm_ofUnit_mul (a b : Rˣ) :
    (degreeEquiv R 2).symm ⟨ofUnit a * ofUnit b, ofUnit_mul_mem_degree_two a b⟩ =
      Submodule.Quotient.mk (PiTensorProduct.tprod ℤ ![Additive.ofMul a, Additive.ofMul b]) := by
  rw [← degreeTwo_symbol_eq_ofUnit_mul]
  have hfn : ([a, b] : List Rˣ) = List.ofFn ![a, b] := by simp
  have ht : (fun i : Fin 2 => Additive.ofMul (![a, b] i)) =
      ![Additive.ofMul a, Additive.ofMul b] := by
    ext i; fin_cases i <;> rfl
  simpa only [hfn, ht] using degreeEquiv_symm_symbol (R := R) ![a, b]

variable (R) in
/-- **Degree-two identification**: `K₂ᴹ(R) ≃ₗ[ℤ] MatsumotoGroup R`, sending `ofUnit a * ofUnit b`
to `MatsumotoGroup.symbol a b`. -/
def degreeTwoEquiv : degree R 2 ≃ₗ[ℤ] MatsumotoGroup R :=
  LinearEquiv.ofLinearMap
    (((steinbergRelations R 2).liftQ (tensorPowerTwoToMatsumotoGroup R)
      (steinbergRelations_two_le_ker R)).comp (degreeEquiv R 2).symm.toLinearMap)
    (matsumotoGroupToDegreeTwo R)
    (MatsumotoGroup.linearMap_ext fun a b => by
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, matsumotoGroupToDegreeTwo_symbol,
        degreeEquiv_symm_ofUnit_mul, Submodule.liftQ_apply,
        tensorPowerTwoToMatsumotoGroup_tprod, LinearMap.id_apply])
    (degreeTwo_linearMap_ext fun a b => by
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, degreeEquiv_symm_ofUnit_mul,
        Submodule.liftQ_apply, tensorPowerTwoToMatsumotoGroup_tprod,
        matsumotoGroupToDegreeTwo_symbol, LinearMap.id_apply])

private theorem degreeTwoEquiv_symm_apply (x : MatsumotoGroup R) :
    (degreeTwoEquiv R).symm x = matsumotoGroupToDegreeTwo R x := by
  rw [degreeTwoEquiv, LinearEquiv.symm_ofLinearMap, LinearEquiv.coe_ofLinearMap]

@[simp]
theorem degreeTwoEquiv_ofUnit_mul (a b : Rˣ) :
    degreeTwoEquiv R ⟨ofUnit a * ofUnit b, ofUnit_mul_mem_degree_two a b⟩ =
      MatsumotoGroup.symbol a b := by
  have hsymm : (⟨ofUnit a * ofUnit b, ofUnit_mul_mem_degree_two a b⟩ : degree R 2) =
      (degreeTwoEquiv R).symm (MatsumotoGroup.symbol a b) := by
    rw [degreeTwoEquiv_symm_apply, matsumotoGroupToDegreeTwo_symbol]
  rw [hsymm, LinearEquiv.apply_symm_apply]

-- Not `@[simp]`: `symbol [a, b]` simplifies via `symbol_cons`/`symbol_nil`/`mul_one` to
-- `ofUnit a * ofUnit b`, so `degreeTwoEquiv_ofUnit_mul` already handles the simp-normal form.
/-- Evaluating `degreeTwoEquiv` on the two-element symbol `{a, b}` gives
`MatsumotoGroup.symbol a b`. -/
theorem degreeTwoEquiv_symbol (a b : Rˣ) :
    degreeTwoEquiv R ⟨symbol [a, b], symbol_mem_degree_of_length rfl⟩ =
      MatsumotoGroup.symbol a b := by
  rw [degreeTwo_symbol_eq_ofUnit_mul, degreeTwoEquiv_ofUnit_mul]

@[simp]
theorem degreeTwoEquiv_symm_symbol (a b : Rˣ) :
    ((degreeTwoEquiv R).symm (MatsumotoGroup.symbol a b) : MilnorK R) = ofUnit a * ofUnit b := by
  simp only [degreeTwoEquiv_symm_apply, matsumotoGroupToDegreeTwo_symbol]

end CommRing

section Map

variable {R S : Type*} [CommRing R] [CommRing S]

/-- Naturality of `degreeTwoEquiv` with respect to `MatsumotoGroup.map`. -/
theorem degreeTwoEquiv_mapDegree (f : R →+* S) (x : degree R 2) :
    degreeTwoEquiv S (mapDegree f 2 x) = MatsumotoGroup.map f (degreeTwoEquiv R x) :=
  LinearMap.congr_fun (f := (degreeTwoEquiv S).toLinearMap.comp (mapDegree f 2))
    (g := (MatsumotoGroup.map f).comp (degreeTwoEquiv R).toLinearMap)
    (degreeTwo_linearMap_ext fun a b => by
      have hmap : mapDegree f 2 ⟨ofUnit a * ofUnit b, ofUnit_mul_mem_degree_two a b⟩ =
          ⟨ofUnit (Units.map f.toMonoidHom a) * ofUnit (Units.map f.toMonoidHom b),
            ofUnit_mul_mem_degree_two _ _⟩ :=
        Subtype.ext (by simp)
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, hmap, degreeTwoEquiv_ofUnit_mul,
        MatsumotoGroup.map_symbol]) x

end Map

end TauCeti.MilnorK

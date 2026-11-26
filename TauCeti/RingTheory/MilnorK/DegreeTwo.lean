/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.GradedAlgebra.RingHom
public import TauCeti.FieldTheory.MatsumotoGroup.Basic
public import TauCeti.RingTheory.MilnorK.Homogeneous
import TauCeti.LinearAlgebra.TensorPower.Basic

/-!
# Degree-two identification and graded functoriality of Milnor K-theory

Using the homogeneous presentation `TauCeti.MilnorK.degreeEquiv` from
`TauCeti.RingTheory.MilnorK.Homogeneous`, this file identifies the degree-two Milnor K-group
`K₂ᴹ(R)` of any commutative ring `R` with `TauCeti.MatsumotoGroup R`
(`TauCeti.MilnorK.degreeTwoEquiv`), establishes `TauCeti.MilnorK.isSteinbergPairing_ofUnit_mul`,
and provides the graded functorial maps `TauCeti.MilnorK.gradedMap` and `TauCeti.MilnorK.mapDegree`
together with naturality of `degreeTwoEquiv`.

## Main definitions

* `TauCeti.MilnorK.degreeTwoEquiv`: `K₂ᴹ(R) ≃ₗ[ℤ] MatsumotoGroup R`, sending `{a} * {b}` to
  `MatsumotoGroup.symbol a b`.
* `TauCeti.MilnorK.gradedMap`: the graded ring homomorphism `degree R →+*ᵍ degree S` induced by
  `f : R →+* S`.
* `TauCeti.MilnorK.mapDegree`: the induced `ℤ`-linear map `Kₙᴹ(R) →ₗ[ℤ] Kₙᴹ(S)`.

## Main results

* `TauCeti.MilnorK.isSteinbergPairing_ofUnit_mul`: `(a, b) ↦ ofUnit a * ofUnit b` is a Steinberg
  pairing.
* `TauCeti.MilnorK.degree_linearMap_ext`, `TauCeti.MilnorK.degreeTwo_linearMap_ext`:
  extensionality for `ℤ`-linear maps out of `degree R n` and `degree R 2`.
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

/-- The degree-two product `(a, b) ↦ ofUnit a * ofUnit b` is a Steinberg pairing. -/
theorem isSteinbergPairing_ofUnit_mul :
    IsSteinbergPairing (fun a b : Rˣ => (ofUnit a * ofUnit b : MilnorK R)) where
  map_mul_left _ _ _ := by rw [ofUnit_mul, add_mul]
  map_mul_right _ _ _ := by rw [ofUnit_mul, mul_add]
  steinberg _ _ h := ofUnit_mul_ofUnit_of_add_eq_one h

/-- Any symbol of a list of length `n` lies in `MilnorK.degree R n`. -/
theorem symbol_mem_degree_of_length {n : ℕ} {l : List Rˣ} (hl : l.length = n) :
    symbol l ∈ degree R n :=
  hl ▸ symbol_mem_degree l

/-- A product of two degree-one unit classes lies in `MilnorK.degree R 2`. -/
theorem ofUnit_mul_mem_degree_two (a b : Rˣ) : ofUnit a * ofUnit b ∈ degree R 2 :=
  SetLike.GradedMul.mul_mem (ofUnit_mem_degree_one a) (ofUnit_mem_degree_one b)

/-- A submodule contains `MilnorK.degree R n` iff it contains every symbol of length `n`. -/
theorem degree_le_iff {n : ℕ} {S : Submodule ℤ (MilnorK R)} :
    degree R n ≤ S ↔ ∀ l : List Rˣ, l.length = n → symbol l ∈ S := by
  rw [degree_eq_span, Submodule.span_le]
  exact ⟨fun h l hl => h ⟨l, hl, rfl⟩, fun h _ ⟨l, hl, hx⟩ => hx ▸ h l hl⟩

/-- Two `ℤ`-linear maps out of `degree R n` agree if they agree on length-`n` symbols. -/
theorem degree_linearMap_ext {n : ℕ} {A : Type*} [AddCommMonoid A] [Module ℤ A]
    {f g : degree R n →ₗ[ℤ] A}
    (h : ∀ (l : List Rˣ) (hl : l.length = n),
      f ⟨symbol l, symbol_mem_degree_of_length hl⟩ = g ⟨symbol l, symbol_mem_degree_of_length hl⟩) :
    f = g := by
  ext ⟨x, hx⟩
  rw [degree_eq_span] at hx
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨l, hl, rfl⟩ := hy
    exact h l hl
  | zero => exact (map_zero f).trans (map_zero g).symm
  | add x₁ x₂ hx₁ hx₂ ih₁ ih₂ =>
    have hsum : (⟨x₁ + x₂, degree_eq_span (R := R) n ▸ Submodule.add_mem _ hx₁ hx₂⟩ : degree R n) =
        ⟨x₁, degree_eq_span (R := R) n ▸ hx₁⟩ + ⟨x₂, degree_eq_span (R := R) n ▸ hx₂⟩ := rfl
    rw [hsum, map_add, map_add, ih₁, ih₂]
  | smul k y hy ih =>
    have hsmul : (⟨k • y, degree_eq_span (R := R) n ▸ Submodule.smul_mem _ k hy⟩ : degree R n) =
        k • ⟨y, degree_eq_span (R := R) n ▸ hy⟩ := rfl
    rw [hsmul, map_smul, map_smul, ih (degree_eq_span (R := R) n ▸ hy)]

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
        MatsumotoGroup.symbol a b := by
  rw [← MatsumotoGroup.mk_tmul]
  exact congrArg (MatsumotoGroup.steinbergRelations R).mkQ
    ((TauCeti.TensorPower.twoEquiv ℤ (Additive Rˣ)).symm_apply_eq.mpr
      (TauCeti.TensorPower.twoEquiv_tmul ℤ (Additive Rˣ)
        (Additive.ofMul a) (Additive.ofMul b)).symm)

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
    { map_mul_left := fun _ _ _ => Subtype.ext (by simp [ofUnit_mul, add_mul])
      map_mul_right := fun _ _ _ => Subtype.ext (by simp [ofUnit_mul, mul_add])
      steinberg := fun _ _ hab => Subtype.ext (ofUnit_mul_ofUnit_of_add_eq_one hab) }

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
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, matsumotoGroupToDegreeTwo,
        MatsumotoGroup.liftLinear_symbol, degreeEquiv_symm_ofUnit_mul, Submodule.liftQ_apply,
        tensorPowerTwoToMatsumotoGroup_tprod, LinearMap.id_apply])
    (degreeTwo_linearMap_ext fun a b => by
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearMap.id_apply,
        degreeEquiv_symm_ofUnit_mul, Submodule.liftQ_apply, tensorPowerTwoToMatsumotoGroup_tprod]
      exact Subtype.ext (by simp [matsumotoGroupToDegreeTwo]))

@[simp]
theorem degreeTwoEquiv_ofUnit_mul (a b : Rˣ) :
    degreeTwoEquiv R ⟨ofUnit a * ofUnit b, ofUnit_mul_mem_degree_two a b⟩ =
      MatsumotoGroup.symbol a b := by
  have hsymm : (⟨ofUnit a * ofUnit b, ofUnit_mul_mem_degree_two a b⟩ : degree R 2) =
      (degreeTwoEquiv R).symm (MatsumotoGroup.symbol a b) :=
    Subtype.ext (by simp [degreeTwoEquiv, matsumotoGroupToDegreeTwo])
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
  simp [degreeTwoEquiv, matsumotoGroupToDegreeTwo]

end CommRing

section Map

variable {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]

/-- Graded ring homomorphism `degree R →+*ᵍ degree S` induced by `f : R →+* S`. -/
@[expose]
def gradedMap (f : R →+* S) : degree R →+*ᵍ degree S where
  toRingHom := map f
  map_mem hx := map_mem_degree f hx

@[simp]
theorem gradedMap_toRingHom (f : R →+* S) : (gradedMap f).toRingHom = map f :=
  rfl

@[simp]
theorem gradedMap_apply (f : R →+* S) (x : MilnorK R) : gradedMap f x = map f x :=
  rfl

@[simp]
theorem gradedMap_id : gradedMap (RingHom.id R) = GradedRingHom.id (degree R) :=
  GradedRingHom.ext fun x => RingHom.congr_fun map_id x

@[simp]
theorem gradedMap_comp (g : S →+* T) (f : R →+* S) :
    gradedMap (g.comp f) = (gradedMap g).comp (gradedMap f) :=
  GradedRingHom.ext fun x => RingHom.congr_fun (map_comp g f) x

/-- The degree-`n` `ℤ`-linear map `Kₙᴹ(R) →ₗ[ℤ] Kₙᴹ(S)` induced by `f : R →+* S`. -/
@[expose]
def mapDegree (f : R →+* S) (n : ℕ) : degree R n →ₗ[ℤ] degree S n :=
  ((gradedMap f).gradedAddHom n).toIntLinearMap

@[simp]
theorem mapDegree_coe (f : R →+* S) (n : ℕ) (x : degree R n) :
    (mapDegree f n x : MilnorK S) = map f x.val :=
  rfl

@[simp]
theorem mapDegree_id (n : ℕ) : mapDegree (RingHom.id R) n = LinearMap.id := by
  ext x; simp

@[simp]
theorem mapDegree_comp (g : S →+* T) (f : R →+* S) (n : ℕ) :
    mapDegree (g.comp f) n = (mapDegree g n).comp (mapDegree f n) := by
  ext x; simp

@[simp]
theorem mapDegree_symbol (f : R →+* S) {n : ℕ} (l : List Rˣ) (hl : l.length = n) :
    mapDegree f n ⟨symbol l, symbol_mem_degree_of_length hl⟩ =
      ⟨symbol (l.map (Units.map f.toMonoidHom)),
        symbol_mem_degree_of_length (by simp [hl])⟩ :=
  Subtype.ext (by simp)

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

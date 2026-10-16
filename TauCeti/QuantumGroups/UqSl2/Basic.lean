/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.FreeAlgebra
public import Mathlib.Algebra.RingQuot
public import Mathlib.Basic.Complex.Basic

/-!
# The quantized enveloping algebra of sl₂

This file defines the algebra `UqSl2 q` by generators `E`, `F`, `K`, and `K⁻¹` and relations

* `K K⁻¹ = K⁻¹ K = 1`,
* `K E = q² E K` and `K F = q⁻² F K`, and
* `E F - F E = (K - K⁻¹) / (q - q⁻¹)`.

The quotient is defined for every complex `q`.  The generic representation theory uses parameters
for which `q ≠ 0` and no positive power of `q` is one; in particular its displayed denominator is
nonzero.  The presentation-level identities below hold for every `q`; when `q = 0`, the
relations force `E = F = 0`.

The quotient construction supplies a universal property for tuples satisfying these relations.
We also package `K` as a unit and derive the commutation rules with `K⁻¹`; these are the
basic presentation-level identities used when putting words into triangular order.  Establishing
a PBW basis, and hence nontriviality of this presentation, requires additional Ore-extension
arguments and is not part of the presentation API.

## Main definitions

* `TauCeti.UqSl2`: the quotient algebra.
* `TauCeti.UqSl2.GeneratorTuple`: a tuple in a complex algebra satisfying the defining relations.
* `TauCeti.UqSl2.lift`: the algebra map induced by such a tuple.
* `TauCeti.UqSl2.kUnit`: the unit represented by `K`.

## References

* A. Virelizier, *Quantum groups*, Sections 2.3--2.4, for this rank-one presentation and Hopf
  convention.
* The quotient and universal-property API follows the construction pattern of
  `Mathlib.LinearAlgebra.CliffordAlgebra.Basic`.
-/

public section

namespace TauCeti

namespace UqSl2

/-- The four generators of the presentation of `UqSl2 q`. -/
inductive Generator
  | e
  | f
  | k
  | kInv
  deriving DecidableEq

/-- The defining relations for the quantized enveloping algebra of `sl₂`, as a relation on the
free complex algebra on `E`, `F`, `K`, and `K⁻¹`. -/
inductive Rel (q : ℂ) : FreeAlgebra ℂ Generator → FreeAlgebra ℂ Generator → Prop
  | k_mul_kInv : Rel q (FreeAlgebra.ι ℂ .k * FreeAlgebra.ι ℂ .kInv) 1
  | kInv_mul_k : Rel q (FreeAlgebra.ι ℂ .kInv * FreeAlgebra.ι ℂ .k) 1
  | k_mul_e : Rel q (FreeAlgebra.ι ℂ .k * FreeAlgebra.ι ℂ .e)
      (q ^ 2 • (FreeAlgebra.ι ℂ .e * FreeAlgebra.ι ℂ .k))
  | k_mul_f : Rel q (FreeAlgebra.ι ℂ .k * FreeAlgebra.ι ℂ .f)
      (q⁻¹ ^ 2 • (FreeAlgebra.ι ℂ .f * FreeAlgebra.ι ℂ .k))
  | e_mul_f_sub_f_mul_e : Rel q
      (FreeAlgebra.ι ℂ .e * FreeAlgebra.ι ℂ .f -
        FreeAlgebra.ι ℂ .f * FreeAlgebra.ι ℂ .e)
      ((q - q⁻¹)⁻¹ • (FreeAlgebra.ι ℂ .k - FreeAlgebra.ι ℂ .kInv))

end UqSl2

/-- The quantized enveloping algebra of `sl₂` with parameter `q`, presented by generators
`E`, `F`, `K`, and `K⁻¹` and the standard rank-one relations. -/
@[expose]
def UqSl2 (q : ℂ) : Type := RingQuot (UqSl2.Rel q)

instance (q : ℂ) : Ring (UqSl2 q) :=
  inferInstanceAs (Ring (RingQuot (UqSl2.Rel q)))

instance (q : ℂ) : Algebra ℂ (UqSl2 q) :=
  inferInstanceAs (Algebra ℂ (RingQuot (UqSl2.Rel q)))

namespace UqSl2

variable {q : ℂ}

/-- The quotient map from the free algebra to `UqSl2 q`. -/
def mkAlgHom (q : ℂ) : FreeAlgebra ℂ Generator →ₐ[ℂ] UqSl2 q :=
  RingQuot.mkAlgHom ℂ (Rel q)

/-- The image of a free generator in `UqSl2 q`. -/
def generator (q : ℂ) (g : Generator) : UqSl2 q :=
  mkAlgHom q (FreeAlgebra.ι ℂ g)

/-- The quotient map takes a free generator to the corresponding generator of `UqSl2 q`. -/
@[simp]
theorem mkAlgHom_ι (q : ℂ) (g : Generator) :
    mkAlgHom q (FreeAlgebra.ι ℂ g) = generator q g := (rfl)

/-- The raising generator `E` of `UqSl2 q`. -/
abbrev e (q : ℂ) : UqSl2 q := generator q .e

/-- The lowering generator `F` of `UqSl2 q`. -/
abbrev f (q : ℂ) : UqSl2 q := generator q .f

/-- The weight generator `K` of `UqSl2 q`. -/
abbrev k (q : ℂ) : UqSl2 q := generator q .k

/-- The inverse weight generator `K⁻¹` of `UqSl2 q`. -/
abbrev kInv (q : ℂ) : UqSl2 q := generator q .kInv

/- The defining relations below come from `RingQuot.mkAlgHom_rel`, whose equation is between
values of `RingQuot.mkAlgHom ℂ (Rel q)` in `RingQuot (Rel q)`.  Because `UqSl2 q` and `mkAlgHom q`
are definitions, `simp` does not see through them; each `show` restates that equation, by
definitional unfolding, between values of `mkAlgHom q` so that `mkAlgHom_ι` can rewrite the free
generators to the generators of `UqSl2 q`. -/

/-- `K` is a left inverse of `K⁻¹`. -/
@[simp]
theorem k_mul_kInv : k q * kInv q = 1 := by
  simpa only [map_mul, map_one, mkAlgHom_ι] using
    (show mkAlgHom q _ = mkAlgHom q _ from
      RingQuot.mkAlgHom_rel ℂ (Rel.k_mul_kInv (q := q)))

/-- `K⁻¹` is a left inverse of `K`. -/
@[simp]
theorem kInv_mul_k : kInv q * k q = 1 := by
  simpa only [map_mul, map_one, mkAlgHom_ι] using
    (show mkAlgHom q _ = mkAlgHom q _ from
      RingQuot.mkAlgHom_rel ℂ (Rel.kInv_mul_k (q := q)))

/-- The defining commutation relation `K E = q² E K`. -/
theorem k_mul_e : k q * e q = q ^ 2 • (e q * k q) := by
  simpa only [map_mul, map_smul, mkAlgHom_ι] using
    (show mkAlgHom q _ = mkAlgHom q _ from
      RingQuot.mkAlgHom_rel ℂ (Rel.k_mul_e (q := q)))

/-- The defining commutation relation `K F = q⁻² F K`. -/
theorem k_mul_f : k q * f q = q⁻¹ ^ 2 • (f q * k q) := by
  simpa only [map_mul, map_smul, mkAlgHom_ι] using
    (show mkAlgHom q _ = mkAlgHom q _ from
      RingQuot.mkAlgHom_rel ℂ (Rel.k_mul_f (q := q)))

/-- The defining commutator relation between `E` and `F`. -/
theorem e_mul_f_sub_f_mul_e :
    e q * f q - f q * e q = (q - q⁻¹)⁻¹ • (k q - kInv q) := by
  simpa only [map_sub, map_mul, map_smul, mkAlgHom_ι] using
    (show mkAlgHom q _ = mkAlgHom q _ from
      RingQuot.mkAlgHom_rel ℂ (Rel.e_mul_f_sub_f_mul_e (q := q)))

/-- The generator `K`, packaged with the specified inverse `K⁻¹`. -/
def kUnit (q : ℂ) : (UqSl2 q)ˣ where
  val := k q
  inv := kInv q
  val_inv := k_mul_kInv
  inv_val := kInv_mul_k

/-- The value of `kUnit q` is the generator `K`. -/
@[simp]
theorem kUnit_val : (kUnit q : UqSl2 q) = k q := (rfl)

/-- The inverse of `kUnit q` has value `K⁻¹`. -/
@[simp]
theorem kUnit_inv : ↑(kUnit q)⁻¹ = kInv q := (rfl)

/-- The relation `E K⁻¹ = q² K⁻¹ E`, obtained from the defining `K E` relation. -/
theorem e_mul_kInv : e q * kInv q = q ^ 2 • (kInv q * e q) := by
  have h := (SemiconjBy.units_inv_symm_left (a := kUnit q) (x := e q) (y := q ^ 2 • e q)
    (by rw [SemiconjBy, kUnit_val, k_mul_e, smul_mul_assoc])).eq
  rw [kUnit_inv, mul_smul_comm] at h
  exact h.symm

/-- The inverse-generator commutation relation `K⁻¹ E = q⁻² E K⁻¹`. -/
theorem kInv_mul_e : kInv q * e q = q⁻¹ ^ 2 • (e q * kInv q) := by
  rcases eq_or_ne q 0 with rfl | hq
  · have he : e (0 : ℂ) = 0 := by
      rw [← one_mul (e 0), ← kInv_mul_k, mul_assoc, k_mul_e]
      simp
    simp [he]
  · rw [e_mul_kInv, smul_smul]
    simp [hq]

/-- The relation `F K⁻¹ = q⁻² K⁻¹ F`, obtained from the defining `K F` relation. -/
theorem f_mul_kInv : f q * kInv q = q⁻¹ ^ 2 • (kInv q * f q) := by
  have h := (SemiconjBy.units_inv_symm_left (a := kUnit q) (x := f q) (y := q⁻¹ ^ 2 • f q)
    (by rw [SemiconjBy, kUnit_val, k_mul_f, smul_mul_assoc])).eq
  rw [kUnit_inv, mul_smul_comm] at h
  exact h.symm

/-- The inverse-generator commutation relation `K⁻¹ F = q² F K⁻¹`. -/
theorem kInv_mul_f : kInv q * f q = q ^ 2 • (f q * kInv q) := by
  rcases eq_or_ne q 0 with rfl | hq
  · have hf : f (0 : ℂ) = 0 := by
      rw [← one_mul (f 0), ← kInv_mul_k, mul_assoc, k_mul_f]
      simp
    simp [hf]
  · rw [f_mul_kInv, smul_smul]
    simp [hq]

/-- A tuple in a complex algebra satisfying the defining relations of `UqSl2 q`. -/
@[ext]
structure GeneratorTuple (q : ℂ) (A : Type*) [Ring A] [Algebra ℂ A] where
  /-- The proposed image of `E`. -/
  e : A
  /-- The proposed image of `F`. -/
  f : A
  /-- The proposed image of `K`. -/
  k : A
  /-- The proposed image of `K⁻¹`. -/
  kInv : A
  /-- The proposed images of `K` and `K⁻¹` multiply to one in this order. -/
  k_mul_kInv : k * kInv = 1
  /-- The proposed images of `K⁻¹` and `K` multiply to one in this order. -/
  kInv_mul_k : kInv * k = 1
  /-- The proposed images satisfy `K E = q² E K`. -/
  k_mul_e : k * e = q ^ 2 • (e * k)
  /-- The proposed images satisfy `K F = q⁻² F K`. -/
  k_mul_f : k * f = q⁻¹ ^ 2 • (f * k)
  /-- The proposed images satisfy the `E`--`F` commutator relation. -/
  e_mul_f_sub_f_mul_e : e * f - f * e = (q - q⁻¹)⁻¹ • (k - kInv)

namespace GeneratorTuple

variable {A : Type*} [Ring A] [Algebra ℂ A]

/-- The function on generator names underlying a generator tuple. -/
@[simp]
def toFun (x : GeneratorTuple q A) : Generator → A
  | .e => x.e
  | .f => x.f
  | .k => x.k
  | .kInv => x.kInv

end GeneratorTuple

/-- The universal property of the presentation: a tuple satisfying the defining relations extends
to a complex algebra map from `UqSl2 q`. -/
def lift {A : Type*} [Ring A] [Algebra ℂ A] (x : GeneratorTuple q A) : UqSl2 q →ₐ[ℂ] A :=
  RingQuot.liftAlgHom ℂ ⟨FreeAlgebra.lift ℂ x.toFun, by
    rintro a b (h | h | h | h | h)
    · simpa only [map_mul, map_one, FreeAlgebra.lift_ι_apply, GeneratorTuple.toFun] using
        x.k_mul_kInv
    · simpa only [map_mul, map_one, FreeAlgebra.lift_ι_apply, GeneratorTuple.toFun] using
        x.kInv_mul_k
    · simpa only [map_mul, map_smul, FreeAlgebra.lift_ι_apply, GeneratorTuple.toFun] using
        x.k_mul_e
    · simpa only [map_mul, map_smul, FreeAlgebra.lift_ι_apply, GeneratorTuple.toFun] using
        x.k_mul_f
    · simpa only [map_sub, map_mul, map_smul, FreeAlgebra.lift_ι_apply,
        GeneratorTuple.toFun] using x.e_mul_f_sub_f_mul_e⟩

variable {A : Type*} [Ring A] [Algebra ℂ A]

/-- The map induced by a generator tuple has the prescribed value on every generator. -/
@[simp]
theorem lift_generator (x : GeneratorTuple q A) (g : Generator) :
    lift x (generator q g) = x.toFun g := by
  exact (RingQuot.liftAlgHom_mkAlgHom_apply ℂ _ _ _).trans (FreeAlgebra.lift_ι_apply _ _)

/-- Two algebra maps from `UqSl2 q` agreeing on the four generators are equal. -/
@[ext high]
theorem hom_ext {F G : UqSl2 q →ₐ[ℂ] A}
    (he : F (e q) = G (e q)) (hf : F (f q) = G (f q))
    (hk : F (k q) = G (k q)) (hkInv : F (kInv q) = G (kInv q)) : F = G := by
  apply RingQuot.ringQuot_ext' ℂ F G
  apply FreeAlgebra.hom_ext
  funext g
  cases g <;> assumption

/-- Algebra maps from `UqSl2 q` are equivalent to tuples satisfying its defining relations. -/
def liftEquiv : (UqSl2 q →ₐ[ℂ] A) ≃ GeneratorTuple q A where
  toFun F :=
    { e := F (e q)
      f := F (f q)
      k := F (k q)
      kInv := F (kInv q)
      k_mul_kInv := by rw [← map_mul, k_mul_kInv, map_one]
      kInv_mul_k := by rw [← map_mul, kInv_mul_k, map_one]
      k_mul_e := by
        simpa only [map_mul, map_smul] using congrArg F (k_mul_e (q := q))
      k_mul_f := by
        simpa only [map_mul, map_smul] using congrArg F (k_mul_f (q := q))
      e_mul_f_sub_f_mul_e := by
        simpa only [map_sub, map_mul, map_smul] using
          congrArg F (e_mul_f_sub_f_mul_e (q := q)) }
  invFun := lift
  left_inv F := hom_ext (by simp) (by simp) (by simp) (by simp)
  right_inv x := by ext <;> simp

/-- The tuple associated to an algebra map records its value on `E`. -/
@[simp]
theorem liftEquiv_apply_e (F : UqSl2 q →ₐ[ℂ] A) : (liftEquiv F).e = F (e q) := (rfl)

/-- The tuple associated to an algebra map records its value on `F`. -/
@[simp]
theorem liftEquiv_apply_f (F : UqSl2 q →ₐ[ℂ] A) : (liftEquiv F).f = F (f q) := (rfl)

/-- The tuple associated to an algebra map records its value on `K`. -/
@[simp]
theorem liftEquiv_apply_k (F : UqSl2 q →ₐ[ℂ] A) : (liftEquiv F).k = F (k q) := (rfl)

/-- The tuple associated to an algebra map records its value on `K⁻¹`. -/
@[simp]
theorem liftEquiv_apply_kInv (F : UqSl2 q →ₐ[ℂ] A) :
    (liftEquiv F).kInv = F (kInv q) := (rfl)

/-- The inverse universal-property equivalence is the map induced by the tuple. -/
@[simp]
theorem liftEquiv_symm_apply (x : GeneratorTuple q A) : liftEquiv.symm x = lift x := (rfl)

end UqSl2

end TauCeti

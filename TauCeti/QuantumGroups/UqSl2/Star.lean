/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.QuantumGroups.UqSl2.Antipode

/-!
# The compact real form of `U_q(sl₂)`

For a real parameter `q`, the quantized enveloping algebra `UqSl2 q` carries the star structure
of its compact real form: the conjugate-linear antimultiplicative involution with

`K* = K`, `E* = K F`, `F* = E K⁻¹` (and hence `(K⁻¹)* = K⁻¹`).

These assignments respect the defining relations because the relations have real coefficients:
`K F K = q² K K F` and `E = q⁻² K E K⁻¹` are the conjugated forms of the `K E` and `K F`
relations, and `K F E K⁻¹ = F E` turns the starred commutator back into `E F - F E`.

For a real nonzero `q`, the star structure is compatible with the Hopf structure: the coproduct
and the counit are star homomorphisms, `Δ(x*) = Δ(x)*` and `ε(x*) = conj (ε x)`, and the antipode
satisfies `S(S(x*)*) = x`. Consequently the inverse of the antipode is `x ↦ S(x*)*`. Thus
`UqSl2 q` is a Hopf star algebra. This is the structure with respect to which invariant inner
products on its modules are defined, and through which its finite-dimensional modules are compared
with the unitary corepresentations of the compact quantum group `SU_q(2)`.

## Main definitions

* `TauCeti.UqSl2.instStarRing`: for a real parameter `q`, the star structure with `K* = K`,
  `E* = K F` and `F* = E K⁻¹`; it is conjugate-linear (`TauCeti.UqSl2.instStarModule`).

## Main results

* `TauCeti.UqSl2.star_e`, `star_f`, `star_k`, `star_kInv`: the star of the generators.
* `TauCeti.UqSl2.comul_star`: the coproduct is a star homomorphism.
* `TauCeti.UqSl2.counit_star`: the counit is a star homomorphism.
* `TauCeti.UqSl2.antipode_star_antipode_star`: `S(S(x*)*) = x`.
* `TauCeti.UqSl2.star_antipode_star`: the inverse of the antipode is `x ↦ S(x*)*`.

## Implementation notes

A conjugate-linear antimultiplicative map out of `UqSl2 q` is obtained from the universal property
of the presentation as a complex algebra map into a private copy of the opposite algebra on which
complex scalars act through complex conjugation, built with `Algebra.compHom`.

## References

* A. Klimyk and K. Schmüdgen, *Quantum Groups and Their Representations*, Springer, 1997,
  Chapter 3, for the real forms of `U_q(sl₂)` and their Hopf star structures, there stated for
  a different coproduct convention.
* A. Virelizier, *Quantum groups*, Sections 2.3--2.4, for the rank-one Hopf convention.
-/

public section

open HopfAlgebra

namespace TauCeti.UqSl2

variable (q : ℂ)

@[local simp] private theorem k_mul_kInv_mul (x : UqSl2 q) : k q * (kInv q * x) = x := by
  rw [← mul_assoc, k_mul_kInv, one_mul]

@[local simp] private theorem kInv_mul_k_mul (x : UqSl2 q) : kInv q * (k q * x) = x := by
  rw [← mul_assoc, kInv_mul_k, one_mul]

/-! ### The conjugate opposite algebra -/

/-- The opposite algebra of `UqSl2 q`, on which complex scalars act through complex conjugation.
A complex algebra map into it is a conjugate-linear antimultiplicative map into `UqSl2 q`. -/
private def ConjOpposite : Type := (UqSl2 q)ᵐᵒᵖ

private instance : Ring (ConjOpposite q) := inferInstanceAs (Ring (UqSl2 q)ᵐᵒᵖ)

private instance : Algebra ℂ (ConjOpposite q) :=
  Algebra.compHom (UqSl2 q)ᵐᵒᵖ (starRingEnd ℂ)

/-- An element of `UqSl2 q`, viewed in the conjugate opposite algebra. -/
private def toConj (x : UqSl2 q) : ConjOpposite q := MulOpposite.op x

/-- The underlying element of `UqSl2 q`. -/
private def ofConj (x : ConjOpposite q) : UqSl2 q := MulOpposite.unop x

/- The following identities unfold the operations of `ConjOpposite q`, which are those of the
opposite algebra except for the conjugated scalar action; they hold by definition. -/

private theorem ofConj_toConj (x : UqSl2 q) : ofConj q (toConj q x) = x := rfl

private theorem ofConj_injective : Function.Injective (ofConj q) :=
  MulOpposite.unop_injective

private theorem ofConj_one : ofConj q 1 = 1 := rfl

private theorem ofConj_add (a b : ConjOpposite q) :
    ofConj q (a + b) = ofConj q a + ofConj q b := rfl

private theorem ofConj_sub (a b : ConjOpposite q) :
    ofConj q (a - b) = ofConj q a - ofConj q b := rfl

private theorem ofConj_mul (a b : ConjOpposite q) :
    ofConj q (a * b) = ofConj q b * ofConj q a := rfl

private theorem ofConj_smul (c : ℂ) (a : ConjOpposite q) :
    ofConj q (c • a) = star c • ofConj q a := rfl

private theorem ofConj_algebraMap (c : ℂ) :
    ofConj q (algebraMap ℂ (ConjOpposite q) c) = algebraMap ℂ (UqSl2 q) (star c) := rfl

/-! ### The star structure -/

/-- The weight generator `K` commutes with `F E`. -/
private theorem k_mul_f_mul_e_mul_kInv : k q * f q * (e q * kInv q) = f q * e q := by
  rcases eq_or_ne q 0 with rfl | hq
  · -- At `q = 0` the relation `K F = 0 • F K` forces `F = 0`.
    have hkf : k (0 : ℂ) * f 0 = 0 := by simp [k_mul_f]
    have hf : f (0 : ℂ) = 0 := by rw [← one_mul (f 0), ← kInv_mul_k, mul_assoc, hkf, mul_zero]
    simp [hf]
  · rw [k_mul_f, e_mul_kInv, smul_mul_smul_comm, mul_assoc, ← mul_assoc (k q), k_mul_kInv,
      one_mul]
    simp [hq]

variable [Fact (IsSelfAdjoint q)]

private theorem star_q : star q = q := (Fact.out : IsSelfAdjoint q).star_eq

/-- The images of the generators under the star structure, as a generator tuple in the conjugate
opposite algebra. -/
private def starTuple : GeneratorTuple q (ConjOpposite q) where
  e := toConj q (k q * f q)
  f := toConj q (e q * kInv q)
  k := toConj q (k q)
  kInv := toConj q (kInv q)
  k_mul_kInv := ofConj_injective q (by simp [ofConj_mul, ofConj_toConj, ofConj_one])
  kInv_mul_k := ofConj_injective q (by simp [ofConj_mul, ofConj_toConj, ofConj_one])
  k_mul_e := ofConj_injective q (by
    simp only [ofConj_mul, ofConj_smul, ofConj_toConj, star_pow, star_q]
    rw [mul_assoc, f_mul_k, mul_smul_comm])
  k_mul_f := ofConj_injective q (by
    simp only [ofConj_mul, ofConj_smul, ofConj_toConj, star_pow, star_inv₀, star_q]
    -- `E = q⁻² K E K⁻¹`, obtained by multiplying `K⁻¹ E = q⁻² E K⁻¹` by `K`.
    rw [mul_assoc, kInv_mul_k, mul_one, ← mul_smul_comm, ← kInv_mul_e, ← mul_assoc, k_mul_kInv,
      one_mul])
  e_mul_f_sub_f_mul_e := ofConj_injective q (by
    simp only [ofConj_mul, ofConj_sub, ofConj_smul, ofConj_toConj, star_inv₀, star_sub, star_q]
    rw [mul_assoc (e q), ← mul_assoc (kInv q), kInv_mul_k, one_mul, k_mul_f_mul_e_mul_kInv,
      e_mul_f_sub_f_mul_e])

/-- The conjugate-linear antimultiplicative map underlying the star structure. -/
private def starFun (x : UqSl2 q) : UqSl2 q := ofConj q (lift (starTuple q) x)

private theorem starFun_mul (a b : UqSl2 q) : starFun q (a * b) = starFun q b * starFun q a := by
  simp only [starFun, map_mul, ofConj_mul]

private theorem starFun_add (a b : UqSl2 q) : starFun q (a + b) = starFun q a + starFun q b := by
  simp only [starFun, map_add, ofConj_add]

private theorem starFun_smul (c : ℂ) (a : UqSl2 q) : starFun q (c • a) = star c • starFun q a := by
  simp only [starFun, map_smul, ofConj_smul]

private theorem starFun_algebraMap (c : ℂ) :
    starFun q (algebraMap ℂ (UqSl2 q) c) = algebraMap ℂ (UqSl2 q) (star c) := by
  simp only [starFun, AlgHom.commutes, ofConj_algebraMap]

private theorem starFun_generator (g : Generator) :
    starFun q (generator q g) = ofConj q ((starTuple q).toFun g) := by
  simp only [starFun, lift_generator]

/-- For a real parameter `q`, the star structure of the compact real form of `UqSl2 q`: the
conjugate-linear antimultiplicative involution with `K* = K`, `E* = K F` and `F* = E K⁻¹`. -/
@[no_expose]
noncomputable instance instStarRing : StarRing (UqSl2 q) where
  star := starFun q
  star_involutive x := by
    induction x using UqSl2.induction with
    | generator g =>
      cases g <;>
        simp [starFun_generator, starTuple, ofConj_toConj, starFun_mul, mul_assoc]
    | algebraMap c => simp [starFun_algebraMap]
    | add a b ha hb => simp only [starFun_add, ha, hb]
    | mul a b ha hb => simp only [starFun_mul, ha, hb]
  star_mul := starFun_mul q
  star_add := starFun_add q

/-- The star structure of the compact real form is conjugate-linear. -/
instance instStarModule : StarModule ℂ (UqSl2 q) where
  star_smul := starFun_smul q

/-- The star structure is `starFun`, by definition of the instance. -/
private theorem star_eq_starFun (x : UqSl2 q) : star x = starFun q x := rfl

/-- The star of the raising generator is `E* = K F`. -/
@[simp]
theorem star_e : star (e q) = k q * f q := by
  simp [star_eq_starFun, starFun_generator, starTuple, ofConj_toConj]

/-- The star of the lowering generator is `F* = E K⁻¹`. -/
@[simp]
theorem star_f : star (f q) = e q * kInv q := by
  simp [star_eq_starFun, starFun_generator, starTuple, ofConj_toConj]

/-- The weight generator is self-adjoint: `K* = K`. -/
@[simp]
theorem star_k : star (k q) = k q := by
  simp [star_eq_starFun, starFun_generator, starTuple, ofConj_toConj]

/-- The inverse weight generator is self-adjoint: `(K⁻¹)* = K⁻¹`. -/
@[simp]
theorem star_kInv : star (kInv q) = kInv q := by
  simp [star_eq_starFun, starFun_generator, starTuple, ofConj_toConj]

/-! ### Compatibility with the Hopf structure -/

variable [Fact (q ≠ 0)]

/-- The coproduct is a star homomorphism: `Δ(x*) = Δ(x)*`. -/
@[simp]
theorem comul_star (x : UqSl2 q) :
    Coalgebra.comul (R := ℂ) (star x) = star (Coalgebra.comul (R := ℂ) x) := by
  induction x using UqSl2.induction with
  | generator g =>
    cases g <;>
      simp [Algebra.TensorProduct.tmul_mul_tmul, mul_add, add_mul]
  | algebraMap c => simp [← algebraMap_star_comm]
  | add a b ha hb => simp only [star_add, map_add, ha, hb]
  | mul a b ha hb => simp only [star_mul, Bialgebra.comul_mul, ha, hb]

/-- The counit is a star homomorphism: `ε(x*) = conj (ε x)`. -/
@[simp]
theorem counit_star (x : UqSl2 q) :
    Coalgebra.counit (R := ℂ) (star x) = star (Coalgebra.counit (R := ℂ) x) := by
  induction x using UqSl2.induction with
  | generator g => cases g <;> simp
  | algebraMap c => simp [← algebraMap_star_comm]
  | add a b ha hb => simp only [star_add, map_add, ha, hb]
  | mul a b ha hb => simp only [star_mul, Bialgebra.counit_mul, ha, hb]

/-- The antipode and the star structure satisfy `S(S(x*)*) = x`. -/
@[simp]
theorem antipode_star_antipode_star (x : UqSl2 q) :
    antipode ℂ (star (antipode ℂ (star x))) = x := by
  induction x using UqSl2.induction with
  | generator g =>
    cases g <;>
      simp [antipode_mul_antidistrib, mul_assoc]
  | algebraMap c =>
    simp [Algebra.algebraMap_eq_smul_one]
  | add a b ha hb => simp only [star_add, map_add, ha, hb]
  | mul a b ha hb => simp only [star_mul, antipode_mul_antidistrib, ha, hb]

/-- The inverse of the antipode is `x ↦ S(x*)*`. -/
theorem star_antipode_star (x : UqSl2 q) :
    star (antipode ℂ (star x)) = (antipodeEquiv q).symm (MulOpposite.op x) := by
  rw [eq_comm, AlgEquiv.symm_apply_eq, antipodeEquiv_apply, antipode_star_antipode_star]

end TauCeti.UqSl2

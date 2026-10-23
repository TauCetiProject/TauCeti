/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.Group.ContinuousAut.Basic
public import TauCeti.Topology.Algebra.Group.Profinite.ZHat.Pow
public import TauCeti.Topology.Algebra.Group.Profinite.ZHat.Units

/-!
# Continuous automorphisms of the profinite integers

Every continuous automorphism of the additive group of the profinite integers is multiplication
by a unique unit of their ring. In the multiplicative presentation `TauCeti.zHat`, multiplication
by a profinite integer `a` is the profinite power map `x ↦ x ^ᶻ a`. Consequently evaluation at
the canonical generator identifies `ContinuousAut TauCeti.zHat` with the unit group of
`Additive TauCeti.zHat`.

## Main definitions

* `TauCeti.zHat.continuousAutOfUnit`: the continuous automorphism given by profinite powering by
  a unit.
* `TauCeti.zHat.continuousAutEquivUnits`: the group isomorphism from continuous automorphisms of
  `TauCeti.zHat` to `(Additive TauCeti.zHat)ˣ`.

## References

* L. Ribes and P. Zalesskii, *Profinite Groups*, Section 4.1.
-/

public section

namespace TauCeti

open scoped zHat

namespace zHat

universe u

/-- A unit `a` of the profinite integers acts on their multiplicative presentation by the
profinite power map `x ↦ x ^ᶻ a`. Its inverse is powering by `a⁻¹`. -/
noncomputable def continuousAutOfUnit (a : (Additive zHat.{u})ˣ) : ContinuousAut zHat.{u} where
  toFun x := x ^ᶻ (a : Additive zHat.{u})
  invFun x := x ^ᶻ (a⁻¹ : (Additive zHat.{u})ˣ)
  left_inv x := by
    -- Expose the two power maps stored in the equivalence before composing their exponents.
    change (x ^ᶻ (a : Additive zHat.{u})) ^ᶻ (a⁻¹ : (Additive zHat.{u})ˣ) = x
    calc
      _ = x ^ᶻ ((a : Additive zHat.{u}) * (a⁻¹ : (Additive zHat.{u})ˣ)) :=
        (zpowHat_mul x _ _).symm
      _ = x ^ᶻ ((a * a⁻¹ : (Additive zHat.{u})ˣ) : Additive zHat.{u}) :=
        congrArg (zpowHat x) (Units.val_mul a a⁻¹).symm
      _ = x := by rw [mul_inv_cancel, Units.val_one, zpowHat_one]
  right_inv x := by
    -- Expose the two power maps stored in the equivalence before composing their exponents.
    change (x ^ᶻ (a⁻¹ : (Additive zHat.{u})ˣ)) ^ᶻ (a : Additive zHat.{u}) = x
    calc
      _ = x ^ᶻ ((a⁻¹ : (Additive zHat.{u})ˣ) * (a : Additive zHat.{u})) :=
        (zpowHat_mul x _ _).symm
      _ = x ^ᶻ ((a⁻¹ * a : (Additive zHat.{u})ˣ) : Additive zHat.{u}) :=
        congrArg (zpowHat x) (Units.val_mul a⁻¹ a).symm
      _ = x := by rw [inv_mul_cancel, Units.val_one, zpowHat_one]
  map_mul' x y := mul_zpowHat (mul_comm' x y) _
  continuous_toFun := continuous_zpowHat_prod.comp (continuous_id.prodMk continuous_const)
  continuous_invFun := continuous_zpowHat_prod.comp (continuous_id.prodMk continuous_const)

/-- The continuous automorphism attached to a unit is profinite powering by that unit. -/
@[simp]
theorem continuousAutOfUnit_apply (a : (Additive zHat.{u})ˣ) (x : zHat.{u}) :
    continuousAutOfUnit a x = x ^ᶻ (a : Additive zHat.{u}) :=
  (rfl)

/-- The inverse of the continuous automorphism attached to `a` is the automorphism attached to
`a⁻¹`. -/
@[simp]
theorem continuousAutOfUnit_symm_apply (a : (Additive zHat.{u})ˣ) (x : zHat.{u}) :
    (continuousAutOfUnit a).symm x = x ^ᶻ (a⁻¹ : (Additive zHat.{u})ˣ) :=
  (rfl)

private noncomputable def unitsToContinuousAut :
    (Additive zHat.{u})ˣ →* ContinuousAut zHat.{u} where
  toFun := continuousAutOfUnit
  map_one' := by
    ext x
    simp
  map_mul' a b := by
    ext x
    simp only [ContinuousAut.mul_apply, continuousAutOfUnit_apply, Units.val_mul, zpowHat_mul]
    exact (zpowHat_mul x _ _).symm.trans
      ((congrArg (zpowHat x) (mul_comm _ _)).trans (zpowHat_mul x _ _))

private theorem unitsToContinuousAut_apply (a : (Additive zHat.{u})ˣ) (x : zHat.{u}) :
    unitsToContinuousAut a x = x ^ᶻ (a : Additive zHat.{u}) :=
  (rfl)

/-- A continuous endomorphism of the profinite integers is multiplication by its value at the
canonical generator. -/
private theorem continuousAut_apply_eq_lift (φ : ContinuousAut zHat.{u}) (x : zHat.{u}) :
    φ x = lift (φ gen) x :=
  DFunLike.congr_fun
    (lift_unique (φ gen) (ContinuousMonoidHom.toContinuousMonoidHom φ) rfl) x

private theorem unitsToContinuousAut_injective :
    Function.Injective (unitsToContinuousAut : (Additive zHat.{u})ˣ →* ContinuousAut zHat.{u}) :=
  fun a b h ↦ Units.ext <| by
    have hg := congrArg (fun φ : ContinuousAut zHat.{u} ↦ Additive.ofMul (φ gen)) h
    simpa only [unitsToContinuousAut_apply, ← toMul_one, toMul_zpowHat, one_mul,
      ofMul_toMul] using hg

private theorem unitsToContinuousAut_surjective :
    Function.Surjective (unitsToContinuousAut :
      (Additive zHat.{u})ˣ →* ContinuousAut zHat.{u}) := by
  intro φ
  let a : Additive zHat.{u} := Additive.ofMul (φ gen)
  let b : Additive zHat.{u} := Additive.ofMul (φ.symm gen)
  have hab : a * b = 1 := by
    apply Additive.ext
    -- Unfold the two local coordinates and the ring product only at this coercion boundary.
    change lift (φ gen) (φ.symm gen) = gen
    rw [← continuousAut_apply_eq_lift φ, φ.apply_symm_apply]
  let u : (Additive zHat.{u})ˣ := Units.mkOfMulEqOne a b hab
  refine ⟨u, ContinuousMulEquiv.ext fun x ↦ ?_⟩
  -- Expose the value of `u` and the local coordinate `a` before using `toMul_zpowHat`.
  change x ^ᶻ a = φ x
  rw [← toMul_ofMul x, toMul_zpowHat, mul_comm, toMul_mul, toMul_ofMul,
    ← continuousAut_apply_eq_lift φ]

/-- **Continuous automorphisms of the profinite integers.** Evaluation at the canonical
generator identifies the continuous automorphism group of `TauCeti.zHat` with the units of its
ring `Additive TauCeti.zHat`. The inverse sends a unit `a` to the profinite power map
`x ↦ x ^ᶻ a`. -/
noncomputable def continuousAutEquivUnits :
    ContinuousAut zHat.{u} ≃* (Additive zHat.{u})ˣ :=
  (MulEquiv.ofBijective unitsToContinuousAut
    ⟨unitsToContinuousAut_injective, unitsToContinuousAut_surjective⟩).symm

/-- The inverse of the automorphism-unit equivalence is profinite powering by the unit. -/
@[simp]
theorem continuousAutEquivUnits_symm_apply (a : (Additive zHat.{u})ˣ) :
    continuousAutEquivUnits.symm a = continuousAutOfUnit a :=
  (rfl)

/-- The unit associated to a continuous automorphism is its value at the canonical generator,
read in the additive presentation. -/
@[simp]
theorem coe_continuousAutEquivUnits_apply (φ : ContinuousAut zHat.{u}) :
    (continuousAutEquivUnits φ : Additive zHat.{u}) = Additive.ofMul (φ gen) := by
  have h := continuousAutEquivUnits.symm_apply_apply φ
  have h' := congrArg (fun ψ : ContinuousAut zHat.{u} ↦ Additive.ofMul (ψ gen)) h
  rw [continuousAutEquivUnits_symm_apply, continuousAutOfUnit_apply, ← toMul_one,
    toMul_zpowHat, one_mul, ofMul_toMul] at h'
  exact h'

end zHat

end TauCeti

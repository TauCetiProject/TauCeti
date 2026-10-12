/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Padics.RingHoms
public import TauCeti.Topology.Algebra.Group.Profinite.ZHat.PadicInt
public import TauCeti.Topology.Algebra.Group.Profinite.ZHat.ZMod

/-!
# The `ℓ`-adic components of the profinite integers

For a prime `ℓ`, the ring of profinite integers `Additive zHat` maps onto the ring of `ℓ`-adic
integers: the projections `zHat.toZMod (ℓ ^ k)` onto the finite levels `ZMod (ℓ ^ k)` are
compatible along the reduction maps, so Mathlib's inverse-limit universal property of `ℤ_[ℓ]`
(`PadicInt.lift`) assembles them into a ring homomorphism

`zHat.component ℓ : Additive zHat →+* ℤ_[ℓ]`,

characterized by `PadicInt.toZModPow k (zHat.component ℓ a) = zHat.toZMod (ℓ ^ k) a`
(`zHat.toZModPow_component`, uniquely by `zHat.component_unique`).

The same map has a group-theoretic description: read multiplicatively, it is the continuous
homomorphism `zHat.lift (ofAdd 1)` from `zHat` to the pro-`ℓ` group `Multiplicative ℤ_[ℓ]`
(`zHat.component_apply`). Hence the component is continuous and surjective, and Tau Ceti's
identification `zHat.maximalProPQuotientEquivPadicInt` of the maximal pro-`ℓ` quotient of `zHat`
with `ℤ_[ℓ]` sends the class of `a` to `zHat.component ℓ a`
(`zHat.maximalProPQuotientEquivPadicInt_mk_eq_component`): the `ℓ`-adic part of the profinite
integers has one description, not two.

## Main definitions

* `TauCeti.zHat.component`: the `ℓ`-adic component `Additive zHat →+* ℤ_[ℓ]` of a profinite
  integer.

## Main results

* `TauCeti.zHat.toZModPow_component`, `TauCeti.zHat.component_unique`: reducing the component
  modulo `ℓ ^ k` is reducing modulo `ℓ ^ k`, and this characterizes the component.
* `TauCeti.zHat.component_apply`, `TauCeti.zHat.lift_ofAdd_one_padicInt_apply`: the component is
  the lift of `1 ∈ ℤ_[ℓ]`, read additively.
* `TauCeti.zHat.continuous_component`, `TauCeti.zHat.component_surjective`: the component is
  continuous and surjective.
* `TauCeti.zHat.maximalProPQuotientEquivPadicInt_mk_eq_component`: the identification of the
  maximal pro-`ℓ` quotient of `zHat` with `ℤ_[ℓ]` is the component.

## References

* L. Ribes and P. Zalesskii, *Profinite Groups*, Sections 2.3 and 4.1.
-/

public section

namespace TauCeti

namespace zHat

universe u

open Additive Multiplicative

variable (ℓ : ℕ) [Fact ℓ.Prime]

/-- **The `ℓ`-adic component of a profinite integer.** The projections of `Additive zHat` onto
the levels `ZMod (ℓ ^ k)` are compatible along the reduction maps, so the inverse-limit
universal property of `ℤ_[ℓ]` (`PadicInt.lift`) assembles them into a ring homomorphism
`Additive zHat →+* ℤ_[ℓ]`. It is characterized by `zHat.toZModPow_component`. -/
noncomputable def component : Additive zHat.{u} →+* ℤ_[ℓ] :=
  PadicInt.lift (f := fun k ↦ toZMod ⟨ℓ ^ k, pow_pos (Fact.out : ℓ.Prime).pos k⟩)
    fun k₁ k₂ hk ↦ castHom_comp_toZMod (m := ⟨ℓ ^ k₁, pow_pos (Fact.out : ℓ.Prime).pos k₁⟩)
      (n := ⟨ℓ ^ k₂, pow_pos (Fact.out : ℓ.Prime).pos k₂⟩) (pow_dvd_pow ℓ hk)

/-- **The characterizing equation of the component.** Reducing the `ℓ`-adic component of `a`
modulo `ℓ ^ k` is reducing `a` modulo `ℓ ^ k`. -/
@[simp]
theorem toZModPow_component (k : ℕ) (a : Additive zHat.{u}) :
    PadicInt.toZModPow k (component ℓ a) =
      toZMod ⟨ℓ ^ k, pow_pos (Fact.out : ℓ.Prime).pos k⟩ a :=
  RingHom.congr_fun (PadicInt.lift_spec _ k) a

/-- The characterizing equation of the component, as an equality of ring homomorphisms. -/
theorem toZModPow_comp_component (k : ℕ) :
    (PadicInt.toZModPow k).comp (component.{u} ℓ) =
      toZMod ⟨ℓ ^ k, pow_pos (Fact.out : ℓ.Prime).pos k⟩ :=
  PadicInt.lift_spec _ k

/-- **Uniqueness of the component.** A ring homomorphism `Additive zHat →+* ℤ_[ℓ]` whose
reduction modulo every `ℓ ^ k` is reduction modulo `ℓ ^ k` is the component. -/
theorem component_unique (g : Additive zHat.{u} →+* ℤ_[ℓ])
    (hg : ∀ k, (PadicInt.toZModPow k).comp g = toZMod ⟨ℓ ^ k, pow_pos (Fact.out : ℓ.Prime).pos k⟩) :
    g = component ℓ :=
  (PadicInt.lift_unique _ g hg).symm

/-- **The component is the lift of `1 ∈ ℤ_[ℓ]`.** Read multiplicatively, the `ℓ`-adic component
is the continuous homomorphism from `zHat` to `Multiplicative ℤ_[ℓ]` sending the generator to
`ofAdd 1`. -/
theorem component_apply (a : Additive zHat.{u}) :
    component ℓ a = (lift (ofAdd (1 : ℤ_[ℓ])) a.toMul).toAdd := by
  refine (PadicInt.ext_of_toZModPow.mp fun k ↦ ?_).symm
  -- Reduction modulo `ℓ ^ k` is a continuous homomorphism of the underlying additive groups, and
  -- the lift is natural in its target, so reducing the lift of `1` is lifting the residue `1`.
  let n : ℕ+ := ⟨ℓ ^ k, pow_pos (Fact.out : ℓ.Prime).pos k⟩
  let f : Multiplicative ℤ_[ℓ] →ₜ* Multiplicative (ZMod n) :=
    ⟨AddMonoidHom.toMultiplicative (PadicInt.toZModPow k).toAddMonoidHom,
      continuous_ofAdd.comp ((PadicInt.continuous_toZModPow k).comp continuous_toAdd)⟩
  -- The value of `f`, unfolded once, with `ZMod n` and `ZMod (ℓ ^ k)` identified.
  have hf (y : Multiplicative ℤ_[ℓ]) : (f y).toAdd = PadicInt.toZModPow k y.toAdd := rfl
  have hf1 : f (ofAdd 1) = ofAdd 1 := toAdd.injective ((hf _).trans (map_one _))
  rw [toZModPow_component, ← hf, map_lift, hf1, lift_ofAdd_one_apply, ofMul_toMul, toAdd_ofAdd]

/-- The lift of `1 ∈ ℤ_[ℓ]` from `zHat` to `Multiplicative ℤ_[ℓ]` is the `ℓ`-adic component,
read multiplicatively. -/
@[simp]
theorem lift_ofAdd_one_padicInt_apply (x : zHat.{u}) :
    lift (ofAdd (1 : ℤ_[ℓ])) x = ofAdd (component ℓ (ofMul x)) := by
  rw [component_apply, toMul_ofMul, ofAdd_toAdd]

/-- The `ℓ`-adic component is continuous. -/
theorem continuous_component : Continuous (component.{u} ℓ) :=
  (continuous_toAdd.comp ((lift _).continuous.comp continuous_toMul)).congr fun a ↦
    (component_apply ℓ a).symm

/-- **Agreement with the maximal pro-`ℓ` quotient.** Tau Ceti's identification of the maximal
pro-`ℓ` quotient of `zHat` with `ℤ_[ℓ]` sends the class of a profinite integer to its `ℓ`-adic
component. -/
theorem maximalProPQuotientEquivPadicInt_mk_eq_component (a : Additive zHat.{u}) :
    maximalProPQuotientEquivPadicInt ℓ (maximalProPQuotient.mk ℓ zHat a.toMul) =
      ofAdd (component ℓ a) := by
  rw [maximalProPQuotient.mk_apply, maximalProPQuotientEquivPadicInt_mk,
    lift_ofAdd_one_padicInt_apply, ofMul_toMul]

/-- The `ℓ`-adic component is surjective: it is the identification of the maximal pro-`ℓ`
quotient of `zHat` with `ℤ_[ℓ]`, after the quotient map. -/
theorem component_surjective : Function.Surjective (component.{u} ℓ) := fun u ↦ by
  obtain ⟨x, hx⟩ := maximalProPQuotient.mk_surjective ℓ zHat.{u}
    ((maximalProPQuotientEquivPadicInt ℓ).symm (ofAdd u))
  refine ⟨ofMul x, ofAdd.injective ?_⟩
  rw [← maximalProPQuotientEquivPadicInt_mk_eq_component, toMul_ofMul, hx,
    ContinuousMulEquiv.apply_symm_apply]

end zHat

end TauCeti

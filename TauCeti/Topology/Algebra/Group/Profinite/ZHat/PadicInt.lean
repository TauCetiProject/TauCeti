/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Padics.InverseLimit
public import TauCeti.Topology.Algebra.Group.Profinite.ProP.PadicInt
public import TauCeti.Topology.Algebra.Group.Profinite.Sylow.Commutative
public import TauCeti.Topology.Algebra.Group.Profinite.ZHat.Basic

/-!
# The maximal pro-`p` quotient of the profinite integers is `ℤ_p`

The maximal pro-`p` quotient of the profinite integers `ℤ̂` is the additive group of the `p`-adic
integers, `maximalProPQuotient p zHat ≃ₜ* Multiplicative ℤ_[p]`, by an isomorphism carrying the
class of the generator `zHat.gen` to `1`. Since a Sylow pro-`p` subgroup of a commutative
profinite group maps isomorphically onto the maximal pro-`p` quotient, every `p`-Sylow subgroup
of `ℤ̂` is topologically isomorphic to `ℤ_p`.

Equivalently, the quotient is the inverse limit of the finite cyclic groups
`Multiplicative (ZMod (p ^ n))`.  The comparison is the composite with the inverse-limit
presentation of `ℤ_[p]`, and sends the class of `zHat.gen` to the compatible family of ones.

These are the rank-one instances of the pro-`p` theory: a continuous homomorphism from `ℤ̂` to
a pro-`p` group factors through `ℤ_p`, and the `p`-part of `ℤ̂` may be read off from either the
quotient or a Sylow subgroup.

## Main definitions

* `TauCeti.zHat.maximalProPQuotientEquivPadicInt`: the maximal pro-`p` quotient of `ℤ̂` is the
  additive group of `ℤ_[p]`.
* `TauCeti.zHat.maximalProPQuotientEquivZModPowLimit`: the same quotient is the inverse limit
  of the groups `Multiplicative (ZMod (p ^ n))`.
* `TauCeti.IsProPSylow.continuousMulEquivPadicInt`: every `p`-Sylow subgroup of `ℤ̂` is the
  additive group of `ℤ_[p]`.

## Main results

* `TauCeti.zHat.maximalProPQuotientEquivPadicInt_mk_gen`,
  `TauCeti.zHat.maximalProPQuotientEquivPadicInt_symm_apply`: the isomorphism sends the class
  of the generator to `1`, and its inverse is the `p`-adic power of that class.

## References

* L. Ribes and P. Zalesskii, *Profinite Groups*, Sections 2.3 and 4.3.
-/

public section

namespace TauCeti

namespace zHat

section MaximalProPQuotient

variable (p : ℕ) [Fact p.Prime]

/-- **The maximal pro-`p` quotient of `ℤ̂` is `ℤ_p`.** The isomorphism
`maximalProPQuotient p zHat ≃ₜ* Multiplicative ℤ_[p]` is induced by the inclusion `ℤ → ℤ_[p]`
and carries the class of the generator to `1`; its inverse is the `p`-adic power of that class.
Both groups represent the same functor on pro-`p` groups, a continuous homomorphism out of
either being an element of the target, which is what forces the two to agree. -/
noncomputable def maximalProPQuotientEquivPadicInt :
    maximalProPQuotient p zHat ≃ₜ* Multiplicative ℤ_[p] :=
  have hZ : IsProP p (maximalProPQuotient p zHat) := isProP_maximalProPQuotient
  have hP : IsProP p (Multiplicative ℤ_[p]) := isProP_multiplicative_padicInt p
  let φ : maximalProPQuotient p zHat →* Multiplicative ℤ_[p] :=
    maximalProPQuotient.lift hP (lift (Multiplicative.ofAdd 1)).toMonoidHom
      (lift (Multiplicative.ofAdd 1)).continuous
  have hφ : Continuous φ := maximalProPQuotient.continuous_lift _ _ _
  let ψ : Multiplicative ℤ_[p] → maximalProPQuotient p zHat := fun l ↦
    hZ.padicPow (maximalProPQuotient.mk p zHat gen) l.toAdd
  have hψ : Continuous ψ :=
    hZ.continuous_padicPow.comp (continuous_toAdd.prodMk continuous_const)
  { toFun := φ
    invFun := ψ
    map_mul' := map_mul φ
    left_inv := by
      -- `ψ ∘ φ` is continuous and agrees with the identity on the dense image of `ℤ`.
      have hdense :
          DenseRange fun z : Multiplicative ℤ ↦ maximalProPQuotient.mk p zHat (ofInt z) :=
        (maximalProPQuotient.mk_surjective p zHat).denseRange.comp denseRange_ofInt
          (maximalProPQuotient.continuous_mk p zHat)
      refine congrFun (hdense.equalizer (hψ.comp hφ) continuous_id
        (funext (Multiplicative.ofAdd.surjective.forall.mpr fun n ↦ ?_)))
      simp [φ, ψ, map_zpow, toAdd_zpow, hZ.padicPow_intCast]
    right_inv l := by
      -- `φ` preserves `p`-adic powers, and the `p`-adic power of `1 ∈ ℤ_[p]` is the identity.
      simp only [ψ]
      rw [hZ.map_padicPow hP φ hφ]
      simp [φ]
    continuous_toFun := hφ
    continuous_invFun := hψ }

/-- The isomorphism from the maximal pro-`p` quotient of `ℤ̂` to `ℤ_p` is the factorisation of
the lift of `1 ∈ ℤ_[p]` through the quotient map. -/
@[simp]
theorem maximalProPQuotientEquivPadicInt_mk (x : zHat) :
    maximalProPQuotientEquivPadicInt p (x : maximalProPQuotient p zHat) =
      lift (Multiplicative.ofAdd (1 : ℤ_[p])) x :=
  maximalProPQuotient.lift_mk _ _ _ x

/-- The isomorphism from the maximal pro-`p` quotient of `ℤ̂` to `ℤ_p` sends the class of the
generator to `1`. -/
theorem maximalProPQuotientEquivPadicInt_mk_gen :
    maximalProPQuotientEquivPadicInt p (gen : maximalProPQuotient p zHat) =
      Multiplicative.ofAdd 1 := by
  simp

/-- The inverse isomorphism from `ℤ_p` to the maximal pro-`p` quotient of `ℤ̂` is the `p`-adic
power of the class of the generator. -/
@[simp]
theorem maximalProPQuotientEquivPadicInt_symm_apply (l : Multiplicative ℤ_[p]) :
    (maximalProPQuotientEquivPadicInt p).symm l =
      (isProP_maximalProPQuotient (p := p) (G := zHat)).padicPow
        (gen : maximalProPQuotient p zHat) l.toAdd :=
  -- The inverse is the `p`-adic power by definition; isolate that reduction in this opaque
  -- theorem so that the definition stays unexposed.
  (rfl)

/-- **The maximal pro-`p` quotient of `ℤ̂` is the inverse limit of `ℤ/p^nℤ`.** This is the
canonical comparison obtained by taking all residues of the `p`-adic integer associated to an
element of the maximal pro-`p` quotient. -/
noncomputable def maximalProPQuotientEquivZModPowLimit :
    maximalProPQuotient p zHat ≃ₜ* Multiplicative (PadicInt.inverseLimit p) :=
  (maximalProPQuotientEquivPadicInt p).trans
    (PadicInt.inverseLimitContinuousMulEquiv p)

/-- The inverse-limit comparison takes a class from `ℤ̂` to the compatible family of residues
of its image in `ℤ_p`. -/
@[simp]
theorem maximalProPQuotientEquivZModPowLimit_mk (x : zHat) :
    maximalProPQuotientEquivZModPowLimit p
        (x : maximalProPQuotient p zHat) =
      Multiplicative.ofAdd
        (PadicInt.toInverseLimit p (lift (Multiplicative.ofAdd (1 : ℤ_[p])) x).toAdd) := by
  rw [maximalProPQuotientEquivZModPowLimit, ContinuousMulEquiv.trans_apply,
    maximalProPQuotientEquivPadicInt_mk]
  rw [← ofAdd_toAdd (lift (Multiplicative.ofAdd (1 : ℤ_[p])) x),
    PadicInt.inverseLimitContinuousMulEquiv_apply]
  simp only [toAdd_ofAdd]

/-- The inverse-limit comparison sends the class of the generator of `ℤ̂` to the compatible
family of residues of `1`. -/
@[simp]
theorem maximalProPQuotientEquivZModPowLimit_mk_gen :
    maximalProPQuotientEquivZModPowLimit p
        (gen : maximalProPQuotient p zHat) =
      Multiplicative.ofAdd (PadicInt.toInverseLimit p 1) := by
  rw [maximalProPQuotientEquivZModPowLimit, ContinuousMulEquiv.trans_apply,
    maximalProPQuotientEquivPadicInt_mk_gen,
    PadicInt.inverseLimitContinuousMulEquiv_apply]

/-- The `n`th coordinate of the inverse-limit comparison is reduction modulo `p ^ n` after
the canonical map from `ℤ̂` to `ℤ_p`. -/
@[simp]
theorem maximalProPQuotientEquivZModPowLimit_mk_proj (x : zHat) (n : ℕ) :
    PadicInt.inverseLimit.proj p n
        (maximalProPQuotientEquivZModPowLimit p
          (x : maximalProPQuotient p zHat)).toAdd =
      PadicInt.toZModPow n (lift (Multiplicative.ofAdd (1 : ℤ_[p])) x).toAdd := by
  rw [maximalProPQuotientEquivZModPowLimit_mk, toAdd_ofAdd,
    PadicInt.inverseLimit.proj_apply, PadicInt.toInverseLimit_apply]

/-- Each coordinate of the image of the generator of `ℤ̂` in the inverse limit is `1`. -/
@[simp]
theorem maximalProPQuotientEquivZModPowLimit_mk_gen_proj (n : ℕ) :
    PadicInt.inverseLimit.proj p n
        (maximalProPQuotientEquivZModPowLimit p
          (gen : maximalProPQuotient p zHat)).toAdd = 1 := by
  rw [maximalProPQuotientEquivZModPowLimit_mk_gen, toAdd_ofAdd,
    PadicInt.inverseLimit.proj_apply, PadicInt.toInverseLimit_apply, map_one]

end MaximalProPQuotient

end zHat

/-- **Every `p`-Sylow subgroup of `ℤ̂` is `ℤ_p`**: the quotient map to the maximal pro-`p`
quotient restricts to a topological group isomorphism from the Sylow subgroup, and that quotient
is the additive group of `ℤ_[p]`. -/
noncomputable def IsProPSylow.continuousMulEquivPadicInt {p : ℕ} [Fact p.Prime]
    {P : Subgroup zHat} (hP : IsProPSylow p P) : P ≃ₜ* Multiplicative ℤ_[p] :=
  hP.continuousMulEquivMaximalProPQuotient.trans (zHat.maximalProPQuotientEquivPadicInt p)

/-- The isomorphism from a `p`-Sylow subgroup of `ℤ̂` to `ℤ_p` is the composite of the quotient
map to the maximal pro-`p` quotient with its identification with `ℤ_p`. -/
@[simp]
theorem IsProPSylow.continuousMulEquivPadicInt_apply {p : ℕ} [Fact p.Prime]
    {P : Subgroup zHat} (hP : IsProPSylow p P) (x : P) :
    hP.continuousMulEquivPadicInt x =
      zHat.maximalProPQuotientEquivPadicInt p (maximalProPQuotient.mk p zHat x) := by
  rw [continuousMulEquivPadicInt, ContinuousMulEquiv.trans_apply,
    continuousMulEquivMaximalProPQuotient_apply]

end TauCeti

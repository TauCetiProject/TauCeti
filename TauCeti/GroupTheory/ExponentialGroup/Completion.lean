/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Equiv.Defs
public import Mathlib.Algebra.Group.TypeTags.Hom
public import Mathlib.Data.Int.Cast.Lemmas
public import TauCeti.GroupTheory.ExponentialGroup.Basic
public import TauCeti.GroupTheory.ExponentialGroup.Hom

/-!
# Completions of a group with respect to a ring of exponents

Let `A` be a ring and `G` a group. An *`A`-completion* (*tensor `A`-completion*) of `G` is an
`A`-group `K` with a homomorphism `μ : G →* K` such that every homomorphism `φ : G →* H` to an
`A`-group `H` factors as `φ = ψ ∘ μ` for a unique `A`-homomorphism `ψ : K → H`. The
`ℤ[t]`-completion of a free group `F` is Lyndon's free `ℤ[t]`-group `F^{ℤ[t]}`.

This file states the universal property as a predicate `IsExponentialGroup.IsCompletion A μ` on
the homomorphism `μ`, proves that it determines `K` up to a unique isomorphism commuting with `μ`
and with exponentiation, and shows that the `A`-completion of the infinite cyclic group is the
additive group of `A`, with `n ↦ (n : A)`: the free `A`-group on one generator.

## Main definitions

* `TauCeti.IsExponentialGroup.IsCompletion A μ`: the universal property of an `A`-completion.
* `TauCeti.IsExponentialGroup.IsCompletion.lift`: the `A`-homomorphism extending a homomorphism
  to an `A`-group.
* `TauCeti.IsExponentialGroup.IsCompletion.mulEquiv`: the isomorphism between two
  `A`-completions of one group.
* `TauCeti.IsExponentialGroup.powHom g`: the `A`-homomorphism `Multiplicative A → G`,
  `ofAdd a ↦ g ^ a`, for an element `g` of an `A`-group over a commutative semiring `A`.

## Main results

* `TauCeti.IsExponentialGroup.IsCompletion.hom_ext`: `A`-homomorphisms out of an `A`-completion
  that agree on the image of `μ` are equal.
* `TauCeti.IsExponentialGroup.IsCompletion.eq_mulEquiv`: the isomorphism between two
  `A`-completions is the only one commuting with the completion maps and with exponentiation.
* `TauCeti.IsExponentialGroup.isCompletion_intCast`: for a commutative ring `A`, the map
  `Multiplicative ℤ →* Multiplicative A`, `n ↦ (n : A)`, is an `A`-completion.

## Implementation notes

The universal property quantifies over the `A`-groups `H` of one universe, which is a universe
parameter of `IsCompletion` (the first one). The comparison isomorphism `IsCompletion.mulEquiv` is
therefore stated for two completions living in that universe.

`IsCompletion` is a structure, whose target `K` carries its `A`-group structure as an instance
argument: the universal property itself mentions only the exponentiation of `K`.

`powHom` and `isCompletion_intCast` use the exponentiation of `Multiplicative A` by `A`, a scoped
instance activated by `open scoped TauCeti.IsExponentialGroup.MultiplicativePow`.

## References

* A. G. Myasnikov, V. N. Remeslennikov, D. E. Serbin, *Regular free length functions on Lyndon's
  free `ℤ[t]`-group `F^{ℤ[t]}`*, §2.1.
* O. Kharlampovich, A. Myasnikov, *Irreducible affine varieties over a free group. I*, §1,
  Definition 7.
* A. G. Myasnikov, V. N. Remeslennikov, *Exponential groups. II. Extensions of centralizers and
  tensor completion of CSA-groups*, Internat. J. Algebra Comput. 6 (1996).
-/

public section

universe w uA uG uK

namespace TauCeti

namespace IsExponentialGroup

section Completion

variable (A : Type uA) [Semiring A] {G : Type uG} [Group G]

/-- The universal property of an `A`-completion of the group `G`, for a homomorphism `μ : G →* K`
to an `A`-group `K`: every homomorphism from `G` to an `A`-group `H` factors through `μ` by a
unique homomorphism `K → H` commuting with exponentiation. The `A`-groups `H` range over the
universe `w`. -/
structure IsCompletion {K : Type uK} [Group K] [Pow K A] [IsExponentialGroup A K]
    (μ : G →* K) : Prop where
  /-- Every homomorphism from `G` to an `A`-group `H` is `ψ ∘ μ` for a unique homomorphism
  `ψ : K → H` commuting with exponentiation. -/
  existsUnique (H : Type w) [Group H] [Pow H A] [IsExponentialGroup A H] (φ : G →* H) :
    ∃! ψ : ExponentialHom A K H, ψ.toMonoidHom.comp μ = φ

variable {A}

theorem isCompletion_iff {K : Type uK} [Group K] [Pow K A] [IsExponentialGroup A K]
    {μ : G →* K} :
    IsCompletion.{w} A μ ↔ ∀ (H : Type w) [Group H] [Pow H A] [IsExponentialGroup A H]
      (φ : G →* H), ∃! ψ : ExponentialHom A K H, ψ.toMonoidHom.comp μ = φ :=
  ⟨fun h => h.existsUnique, fun h => ⟨h⟩⟩

namespace IsCompletion

section Lift

variable {K : Type uK} [Group K] [Pow K A] [IsExponentialGroup A K] {μ : G →* K}
  {H : Type w} [Group H] [Pow H A] [IsExponentialGroup A H]

/-- The homomorphism commuting with exponentiation that extends `φ : G →* H` along an
`A`-completion `μ : G →* K`. -/
noncomputable def lift (h : IsCompletion.{w} A μ) (φ : G →* H) : ExponentialHom A K H :=
  (h.existsUnique H φ).exists.choose

@[simp]
theorem lift_comp (h : IsCompletion.{w} A μ) (φ : G →* H) : (h.lift φ).toMonoidHom.comp μ = φ :=
  (h.existsUnique H φ).exists.choose_spec

@[simp]
theorem lift_eq (h : IsCompletion.{w} A μ) (φ : G →* H) (g : G) : h.lift φ (μ g) = φ g :=
  DFunLike.congr_fun (h.lift_comp φ) g

/-- Homomorphisms commuting with exponentiation, out of an `A`-completion `μ : G →* K`, are equal
if they agree on the image of `μ`. -/
theorem hom_ext (h : IsCompletion.{w} A μ) {ψ ψ' : ExponentialHom A K H}
    (hψ : ψ.toMonoidHom.comp μ = ψ'.toMonoidHom.comp μ) : ψ = ψ' :=
  (h.existsUnique H (ψ'.toMonoidHom.comp μ)).unique hψ rfl

/-- The extension of `φ` along an `A`-completion is the only homomorphism commuting with
exponentiation that restricts to `φ`. -/
theorem eq_lift (h : IsCompletion.{w} A μ) {φ : G →* H} {ψ : ExponentialHom A K H}
    (hψ : ψ.toMonoidHom.comp μ = φ) : ψ = h.lift φ :=
  h.hom_ext (hψ.trans (h.lift_comp φ).symm)

/-- Composing the extension of `φ` with a homomorphism `f` commuting with exponentiation gives the
extension of `f ∘ φ`. -/
@[simp]
theorem comp_lift (h : IsCompletion.{w} A μ) {H' : Type w} [Group H'] [Pow H' A]
    [IsExponentialGroup A H'] (f : ExponentialHom A H H') (φ : G →* H) :
    f.comp (h.lift φ) = h.lift (f.toMonoidHom.comp φ) :=
  h.eq_lift <| by rw [ExponentialHom.toMonoidHom_comp, MonoidHom.comp_assoc, lift_comp]

end Lift

section Unique

variable {K₁ K₂ : Type w} [Group K₁] [Group K₂] [Pow K₁ A] [Pow K₂ A]
  [IsExponentialGroup A K₁] [IsExponentialGroup A K₂] {μ₁ : G →* K₁} {μ₂ : G →* K₂}

@[simp]
theorem lift_self (h₁ : IsCompletion.{w} A μ₁) : h₁.lift μ₁ = ExponentialHom.id A K₁ :=
  (h₁.eq_lift (by simp)).symm

/-- The extensions of two `A`-completions of one group along each other are mutually inverse. -/
theorem lift_comp_lift (h₁ : IsCompletion.{w} A μ₁) (h₂ : IsCompletion.{w} A μ₂) :
    (h₂.lift μ₁).comp (h₁.lift μ₂) = ExponentialHom.id A K₁ := by
  simp

/-- Two `A`-completions of one group are isomorphic, by the isomorphism extending one along the
other. -/
noncomputable def mulEquiv (h₁ : IsCompletion.{w} A μ₁) (h₂ : IsCompletion.{w} A μ₂) : K₁ ≃* K₂ :=
  (h₁.lift μ₂).toMonoidHom.toMulEquiv (h₂.lift μ₁).toMonoidHom
    (by rw [← ExponentialHom.toMonoidHom_comp, lift_comp_lift, ExponentialHom.toMonoidHom_id])
    (by rw [← ExponentialHom.toMonoidHom_comp, lift_comp_lift, ExponentialHom.toMonoidHom_id])

theorem coe_mulEquiv (h₁ : IsCompletion.{w} A μ₁) (h₂ : IsCompletion.{w} A μ₂) :
    ⇑(h₁.mulEquiv h₂) = h₁.lift μ₂ := by
  rfl

@[simp]
theorem mulEquiv_symm (h₁ : IsCompletion.{w} A μ₁) (h₂ : IsCompletion.{w} A μ₂) :
    (h₁.mulEquiv h₂).symm = h₂.mulEquiv h₁ := by
  rfl

@[simp]
theorem mulEquiv_self (h₁ : IsCompletion.{w} A μ₁) : h₁.mulEquiv h₁ = MulEquiv.refl K₁ :=
  MulEquiv.ext fun k => by simp [coe_mulEquiv]

@[simp]
theorem mulEquiv_trans {K₃ : Type w} [Group K₃] [Pow K₃ A] [IsExponentialGroup A K₃]
    {μ₃ : G →* K₃} (h₁ : IsCompletion.{w} A μ₁) (h₂ : IsCompletion.{w} A μ₂)
    (h₃ : IsCompletion.{w} A μ₃) : (h₁.mulEquiv h₂).trans (h₂.mulEquiv h₃) = h₁.mulEquiv h₃ :=
  MulEquiv.ext fun k => by
    rw [MulEquiv.trans_apply, coe_mulEquiv, coe_mulEquiv, coe_mulEquiv,
      ← ExponentialHom.comp_apply, comp_lift, lift_comp]

/-- The comparison isomorphism of two `A`-completions is the only isomorphism commuting with the
completion maps and with exponentiation. -/
theorem eq_mulEquiv (h₁ : IsCompletion.{w} A μ₁) (h₂ : IsCompletion.{w} A μ₂) {e : K₁ ≃* K₂}
    (he : e.toMonoidHom.comp μ₁ = μ₂) (hpow : ∀ (k : K₁) (a : A), e (k ^ a) = e k ^ a) :
    e = h₁.mulEquiv h₂ :=
  MulEquiv.ext fun k => DFunLike.congr_fun (h₁.eq_lift (ψ := ⟨e.toMonoidHom, hpow⟩) he) k

/-- The comparison isomorphism of two `A`-completions commutes with the completion maps. -/
@[simp]
theorem mulEquiv_eq (h₁ : IsCompletion.{w} A μ₁) (h₂ : IsCompletion.{w} A μ₂) (g : G) :
    h₁.mulEquiv h₂ (μ₁ g) = μ₂ g :=
  h₁.lift_eq μ₂ g

/-- The comparison isomorphism of two `A`-completions commutes with exponentiation. -/
@[simp]
theorem mulEquiv_pow (h₁ : IsCompletion.{w} A μ₁) (h₂ : IsCompletion.{w} A μ₂) (k : K₁)
    (a : A) : h₁.mulEquiv h₂ (k ^ a) = h₁.mulEquiv h₂ k ^ a :=
  (h₁.lift μ₂).map_pow k a

end Unique

end IsCompletion

end Completion

section RankOne

open scoped MultiplicativePow

variable (A : Type uA) {G : Type uG} [Group G] [Pow G A]

/-- For an element `g` of an `A`-group over a commutative semiring `A`, the homomorphism
`Multiplicative A → G`, `ofAdd a ↦ g ^ a`; it commutes with exponentiation, where
`Multiplicative A` carries `ofAdd a ^ b = ofAdd (b * a)`. -/
def powHom [CommSemiring A] [IsExponentialGroup A G] (g : G) :
    ExponentialHom A (Multiplicative A) G where
  toFun x := g ^ x.toAdd
  map_one' := by rw [toAdd_one, IsExponentialGroup.pow_zero]
  map_mul' x y := by rw [toAdd_mul, IsExponentialGroup.pow_add]
  map_pow' x a := by
    rw [Multiplicative.toAdd_multiplicativePow, smul_eq_mul, mul_comm, IsExponentialGroup.pow_mul]

@[simp]
theorem powHom_apply [CommSemiring A] [IsExponentialGroup A G] (g : G)
    (x : Multiplicative A) : powHom A g x = g ^ x.toAdd := by
  rfl

/-- The additive group of a commutative ring `A`, written multiplicatively and receiving the
infinite cyclic group by `n ↦ (n : A)`, is the `A`-completion of the infinite cyclic group: it is
the free `A`-group on the generator `ofAdd 1`. -/
theorem isCompletion_intCast [CommRing A] :
    IsCompletion.{w} A (Int.castAddHom A).toMultiplicative := by
  refine ⟨fun H _ _ _ φ => ⟨powHom A (φ (.ofAdd 1)), ?_, fun ψ hψ => ?_⟩⟩
  · ext
    simp
  · ext x
    have h1 : ψ (.ofAdd 1) = φ (.ofAdd 1) := by
      simpa using DFunLike.congr_fun hψ (.ofAdd 1)
    have hx : x = Multiplicative.ofAdd (1 : A) ^ x.toAdd := by
      simp [MultiplicativePow.ofAdd_multiplicativePow]
    rw [hx, ψ.map_pow, h1]
    simp

end RankOne

end IsExponentialGroup

end TauCeti

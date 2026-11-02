/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.RootSubgroup.Torus.Coroot

/-!
# Steinberg's rank-one relations for a Kostant root pair

Let `U_ℤ = kostantForm e h` act on a rational vector space `V` through `ρ` and preserve an additive
subgroup `M ≤ V`, and let `(eᵢ, eⱼ)` be a root pair: designated root vectors of weights `α` and
`-α` whose images form an `sl₂` triple with the designated Cartan vector `h c`. Over a value ring
`A`, write `xᵢ` and `xⱼ` for the two root subgroups on the points of `A ⊗[ℤ] M` and, following
Steinberg, *Lectures on Chevalley Groups*, Chapter 3, Lemma 19, set

```text
n_α(u) = xᵢ(u) xⱼ(-u⁻¹) xᵢ(u)        for a unit u of A.
```

This element, `TauCeti.UniversalEnvelopingAlgebra.kostantWeylParam`, its inverse
`n_α(u)⁻¹ = n_α(-u)` and its value `n_α(1) = n` at the Weyl representative are in
`TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.RootSubgroup.Weyl.Elementary`, which needs no
torus. This file proves the relations among the `n_α(u)`, the root subgroups `xᵢ`, `xⱼ` and the
split weight torus that hold inside one root pair, and which the Steinberg presentation of a
Chevalley group imposes in rank one:

```text
n_α(u) n_α(v)⁻¹ = h_α(u v⁻¹),        so h_α(u) = n_α(u) n_α(1)⁻¹,
n_α(u) n_α(v) = h_α(-u v⁻¹),         so n_α(u)² = h_α(-1),
n_α(u) xᵢ(t) n_α(u)⁻¹ = xⱼ(-u⁻² t),
n_α(u) xⱼ(t) n_α(u)⁻¹ = xᵢ(-u² t),
n_α(u) t(s) n_α(u)⁻¹ = t(s_α s).
```

Here `h_α(u)` is the coordinate cocharacter at `c`, which scales a weight vector of weight `μ` by
`u ^ μ(c)`, and `s_α` is the reflection of torus points of `TauCeti.weylReflectTorusPoint`. They
reduce, through Chevalley's identity `n_α(u) = h_α(u) n_α(1)` of
`TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.RootSubgroup.Torus.Coroot`, to the action of the
Weyl representative and of the torus on the root subgroups. All of them hold over every value ring,
with no factorial inverted.

## Main results

* `TauCeti.UniversalEnvelopingAlgebra.kostantWeylParam_mul_inv_kostantWeylParam`,
  `TauCeti.UniversalEnvelopingAlgebra.kostantWeylParam_mul_kostantWeylParam` and
  `TauCeti.UniversalEnvelopingAlgebra.kostantWeylParam_sq`: products of two Weyl elements are
  coroot values.
* `TauCeti.UniversalEnvelopingAlgebra.kostantWeylParam_conj_kostantRootSubgroupParam_e` and
  `TauCeti.UniversalEnvelopingAlgebra.kostantWeylParam_conj_kostantRootSubgroupParam_f`:
  Steinberg's relations `n_α(u) x_{±α}(t) n_α(u)⁻¹ = x_{∓α}(-u^{∓2} t)`.
* `TauCeti.UniversalEnvelopingAlgebra.kostantWeylParam_conj_kostantTorusPoints` and
  `TauCeti.UniversalEnvelopingAlgebra.kostantWeylParam_conj_kostantCoordinateCocharacter`:
  `n_α(u)` acts on the torus by the reflection `s_α`, and inverts the coroot values.

## References

* R. Steinberg, *Lectures on Chevalley Groups*, AMS University Lecture Series 66 (2016),
  Chapter 3, Lemmas 19 and 20, and Chapter 6.
* R. W. Carter, *Simple Groups of Lie Type*, §§6.4 and 12.1.
-/

public section

open TensorProduct

namespace TauCeti.UniversalEnvelopingAlgebra

universe u v w

variable {L : Type u} [LieRing L] [LieAlgebra ℚ L]
variable {ι : Type*} {κ : Type*}
variable {V : Type v} [AddCommGroup V] [Module ℚ V]

variable (e : ι → L) (h : κ → L)
variable (ρ : _root_.UniversalEnvelopingAlgebra ℚ L →ₐ[ℚ] Module.End ℚ V)
variable (M : AddSubgroup V)
variable (hM : ∀ u ∈ kostantForm e h, ∀ v ∈ M, ρ u v ∈ M)

attribute [local instance 100] LieRing.ofAssociativeRing

-- Match tensor products to the `ℤ`-algebra instance stored by `CommAlgCat` objects.
attribute [local instance high] Algebra.toModule

variable {i j : ι}
variable (hi : IsNilpotent (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e i))))
variable (hj : IsNilpotent (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e j))))

/-! ## The rank-one relations -/

section RankOne

variable {η : Type*} (b : Module.Basis η ℤ M) (wt : η → κ → ℤ)
variable (hwt : ∀ x, IsCartanWeightVector h ρ (wt x) ((b x : M) : V))
variable {c : κ} {α : κ → ℤ}
variable (hT : IsSl2Triple (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (h c)))
  (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e i)))
  (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e j))))
variable (hα : ∀ j', ⁅h j', e i⁆ = (α j' : ℚ) • e i)
variable (hαneg : ∀ j', ⁅h j', e j⁆ = -((α j' : ℚ) • e j))

include hwt hT hα hαneg

section Torus

variable [Fintype κ] [DecidableEq κ]

/-- **Quotients of Steinberg's elements are coroot values**: `n_α(u) n_α(v)⁻¹ = h_α(u v⁻¹)`.
At `v = 1` this is Steinberg's definition `h_α(u) = n_α(u) n_α(1)⁻¹` of the coroot value, read
on the weight torus. -/
theorem kostantWeylParam_mul_inv_kostantWeylParam (A : CommAlgCat.{w} ℤ) (u v : Aˣ) :
    kostantWeylParam e h ρ M hM hi hj A u * (kostantWeylParam e h ρ M hM hi hj A v)⁻¹ =
      kostantCoordinateCocharacter M b wt A c (u * v⁻¹) := by
  rw [kostantWeylParam_def, kostantWeylParam_def,
    kostantRootSubgroupParam_mul_mul_eq_kostantCoordinateCocharacter_mul_kostantWeylGL
      e h ρ M hM b wt hwt hT hi hj hα hαneg,
    kostantRootSubgroupParam_mul_mul_eq_kostantCoordinateCocharacter_mul_kostantWeylGL
      e h ρ M hM b wt hwt hT hi hj hα hαneg, map_mul, map_inv]
  group

/-- **Products of Steinberg's elements are coroot values**: `n_α(u) n_α(v) = h_α(-u v⁻¹)`. -/
theorem kostantWeylParam_mul_kostantWeylParam (A : CommAlgCat.{w} ℤ) (u v : Aˣ) :
    kostantWeylParam e h ρ M hM hi hj A u * kostantWeylParam e h ρ M hM hi hj A v =
      kostantCoordinateCocharacter M b wt A c (-(u * v⁻¹)) := by
  rw [← inv_inv (kostantWeylParam e h ρ M hM hi hj A v), kostantWeylParam_inv,
    kostantWeylParam_mul_inv_kostantWeylParam e h ρ M hM hi hj b wt hwt hT hα hαneg, inv_neg,
    mul_neg]

/-- **The square of Steinberg's element** is the coroot value at `-1`: `n_α(u)² = h_α(-1)`, for
every unit `u`. -/
theorem kostantWeylParam_sq (A : CommAlgCat.{w} ℤ) (u : Aˣ) :
    kostantWeylParam e h ρ M hM hi hj A u ^ 2 = kostantCoordinateCocharacter M b wt A c (-1) := by
  rw [sq, kostantWeylParam_mul_kostantWeylParam e h ρ M hM hi hj b wt hwt hT hα hαneg,
    mul_inv_cancel]

/-- **Steinberg's element acts on the torus by the reflection** `s_α`:
`n_α(u) t(s) n_α(u)⁻¹ = t(s_α s)`. The coroot value `h_α(u)` relating `n_α(u)` to the Weyl
representative lies in the torus, which is commutative. -/
theorem kostantWeylParam_conj_kostantTorusPoints (A : CommAlgCat.{w} ℤ) (u : Aˣ) (s : κ → Aˣ) :
    kostantWeylParam e h ρ M hM hi hj A u * kostantTorusPoints M b wt A s *
        (kostantWeylParam e h ρ M hM hi hj A u)⁻¹ =
      kostantTorusPoints M b wt A (weylReflectTorusPoint α c s) := by
  -- Conjugation by `h_α(u) n_α(1)` is conjugation by `n_α(1)`, then by `h_α(u)`.
  have hsplit : ∀ d n g : LinearMap.GeneralLinearGroup A (A ⊗[ℤ] M),
      d * n * g * (d * n)⁻¹ = d * (n * g * n⁻¹) * d⁻¹ := fun _ _ _ => by group
  rw [kostantWeylParam_def,
    kostantRootSubgroupParam_mul_mul_eq_kostantCoordinateCocharacter_mul_kostantWeylGL
      e h ρ M hM b wt hwt hT hi hj hα hαneg,
    kostantCoordinateCocharacter_apply, hsplit,
    kostantWeylGL_conj_kostantTorusPoints e h ρ M hM hi hj hT hα hαneg b wt hwt s, ← map_inv,
    ← map_mul, ← map_mul, mul_inv_cancel_comm]

/-- **Steinberg's element inverts the coroot values**: `n_α(u) h_α(v) n_α(u)⁻¹ = h_α(v⁻¹)`. -/
theorem kostantWeylParam_conj_kostantCoordinateCocharacter (A : CommAlgCat.{w} ℤ) (u v : Aˣ) :
    kostantWeylParam e h ρ M hM hi hj A u * kostantCoordinateCocharacter M b wt A c v *
        (kostantWeylParam e h ρ M hM hi hj A u)⁻¹ =
      kostantCoordinateCocharacter M b wt A c v⁻¹ := by
  have hc : α c = 2 := rootWeight_apply_coroot_eq_two e h ρ hT (hα c)
  rw [kostantCoordinateCocharacter_apply, kostantCoordinateCocharacter_apply,
    kostantWeylParam_conj_kostantTorusPoints e h ρ M hM hi hj b wt hwt hT hα hαneg,
    weylReflectTorusPoint_apply, torusCharacter_mulSingle, hc, ← Pi.mulSingle_mul]
  congr 2
  group

end Torus

variable [Finite κ]

/-- **Steinberg's relation on the raising root subgroup**:
`n_α(u) xᵢ(t) n_α(u)⁻¹ = xⱼ(-u⁻² t)`. At `u = 1` it is the interchange of the two root subgroups
by the Weyl representative, and the coroot value `h_α(u)` rescales the parameter of `xⱼ` by
`u ^ (-α)(c) = u⁻²`. -/
theorem kostantWeylParam_conj_kostantRootSubgroupParam_e (A : CommAlgCat.{w} ℤ) (u : Aˣ) (t : A) :
    kostantWeylParam e h ρ M hM hi hj A u *
        kostantRootSubgroupParam e h ρ M hM i hi A (Multiplicative.ofAdd t) *
        (kostantWeylParam e h ρ M hM hi hj A u)⁻¹ =
      kostantRootSubgroupParam e h ρ M hM j hj A
        (Multiplicative.ofAdd (-(((u⁻¹ : Aˣ) : A) ^ 2 * t))) := by
  classical
  have := Fintype.ofFinite κ
  have hc : α c = 2 := rootWeight_apply_coroot_eq_two e h ρ hT (hα c)
  have hαneg' : ∀ j', ⁅h j', e j⁆ = (((-α) j' : ℤ) : ℚ) • e j := fun j' => by
    rw [hαneg j', Pi.neg_apply, Int.cast_neg, neg_smul]
  -- Conjugation by `h_α(u) n_α(1)` is conjugation by `n_α(1)`, then by `h_α(u)`.
  have hsplit : ∀ d n g : LinearMap.GeneralLinearGroup A (A ⊗[ℤ] M),
      d * n * g * (d * n)⁻¹ = d * (n * g * n⁻¹) * d⁻¹ := fun _ _ _ => by group
  rw [kostantWeylParam_def,
    kostantRootSubgroupParam_mul_mul_eq_kostantCoordinateCocharacter_mul_kostantWeylGL
      e h ρ M hM b wt hwt hT hi hj hα hαneg,
    hsplit, kostantWeylGL_conj_kostantRootSubgroupParam_e e h ρ M hM hi hj hT,
    kostantCoordinateCocharacter_apply,
    kostantTorusPoints_conj_kostantRootSubgroupParam e h ρ M hM b wt hwt hαneg' hj,
    torusCharacter_mulSingle, Pi.neg_apply, hc, toAdd_ofAdd]
  congr 2
  rw [zpow_neg, zpow_ofNat, ← inv_pow, Units.val_pow_eq_pow_val]
  ring

/-- **Steinberg's relation on the lowering root subgroup**:
`n_α(u) xⱼ(t) n_α(u)⁻¹ = xᵢ(-u² t)`. It is the raising relation read backwards, through
`n_α(u)⁻¹ = n_α(-u)`. -/
theorem kostantWeylParam_conj_kostantRootSubgroupParam_f (A : CommAlgCat.{w} ℤ) (u : Aˣ) (t : A) :
    kostantWeylParam e h ρ M hM hi hj A u *
        kostantRootSubgroupParam e h ρ M hM j hj A (Multiplicative.ofAdd t) *
        (kostantWeylParam e h ρ M hM hi hj A u)⁻¹ =
      kostantRootSubgroupParam e h ρ M hM i hi A
        (Multiplicative.ofAdd (-((u : A) ^ 2 * t))) := by
  -- The raising relation at `-u` and parameter `-u² t` lands on `xⱼ(t)`; conjugate it back by
  -- `n_α(-u)⁻¹ = n_α(u)`.
  have hparam : (((-u)⁻¹ : Aˣ) : A) ^ 2 * -((u : A) ^ 2 * t) = -t := by
    have hu : ((u⁻¹ : Aˣ) : A) * u = 1 := Units.inv_mul u
    rw [inv_neg, Units.val_neg, neg_sq]
    linear_combination (-t * (((u⁻¹ : Aˣ) : A) * u + 1)) * hu
  have hraise := kostantWeylParam_conj_kostantRootSubgroupParam_e e h ρ M hM hi hj b wt hwt hT hα
    hαneg A (-u) (-((u : A) ^ 2 * t))
  rw [hparam, neg_neg] at hraise
  rw [← hraise, ← kostantWeylParam_inv e h ρ M hM hi hj A u]
  group

end RankOne

end TauCeti.UniversalEnvelopingAlgebra

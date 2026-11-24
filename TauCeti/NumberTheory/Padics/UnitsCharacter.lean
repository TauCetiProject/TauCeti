/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Ring.Units
public import TauCeti.NumberTheory.LocalField.Padic
public import TauCeti.NumberTheory.LocalField.Unramified.Character
public import TauCeti.NumberTheory.Padics.PadicIntegers
import TauCeti.NumberTheory.Padics.RingHoms

/-!
# Continuous characters of `ℚ_pˣ`

Every `x ∈ ℚ_pˣ` is uniquely `x = p ^ v(x) u` with `u ∈ ℤ_pˣ`. The unit part `u = x |x|`, where
`|x| = p ^ (-v(x))` is the normalized absolute value, is the continuous character

```text
x ↦ x |x| : ℚ_pˣ → ℤ_pˣ                (`TauCeti.padicUnitPart p`),
```

written `x|x|` by Colmez. It sends `p` to `1` and is the identity on `ℤ_pˣ`. Under local class
field theory normalized by geometric Frobenius it corresponds to the cyclotomic character.

Consequently a continuous character `δ : ℚ_pˣ → G` with values in a commutative topological group
`G` is determined by `δ(p)` and by its restriction to `ℤ_pˣ`, and every such pair occurs:

```text
δ = μ_{δ(p)} · (δ|_{ℤ_pˣ} ∘ x|x|),     (ℚ_pˣ →ₜ* G) ≃* G × (ℤ_pˣ →ₜ* G),
```

where `μ_a` is the unramified character `x ↦ a ^ v(x)` (`TauCeti.unramifiedCharacter`). This is
Colmez's description of the character group `T̂(Λ)` of `ℚ_pˣ` with values in the units `G = Λˣ` of
a commutative topological ring `Λ`, where the second factor is the weight space
`TauCeti.WeightSpace p Λ`. Commutativity of `G` is needed for the product of two characters to be
a character.

## Main definitions

* `TauCeti.padicIntUnitsInclusion p`: the inclusion `ℤ_pˣ → ℚ_pˣ` as a continuous homomorphism.
* `TauCeti.padicUnitPart p`: the character `x ↦ x |x|` of `ℚ_pˣ` with values in `ℤ_pˣ`.
* `TauCeti.padicUnitsCharacterEquiv p G`: the splitting
  `(ℚ_pˣ →ₜ* G) ≃* G × (ℤ_pˣ →ₜ* G)`, `δ ↦ (δ(p), δ|_{ℤ_pˣ})`.

## Main results

* `TauCeti.padicUnitPart_apply_of_eq`: if `x = p ^ k u` with `u ∈ ℤ_pˣ`, then `x |x| = u`.
* `TauCeti.coe_eq_zpow_valuation_mul_padicUnitPart`: `x = p ^ v(x) · x |x|`.
* `TauCeti.padicUnits_hom_ext`: a homomorphism out of `ℚ_pˣ` is determined by its value at `p`
  and its restriction to `ℤ_pˣ`.
* `ContinuousMonoidHom.eq_unramifiedCharacter_mul_comp_padicUnitPart`:
  `δ = μ_{δ(p)} · (δ|_{ℤ_pˣ} ∘ x|x|)`.

## References

* P. Colmez, *Représentations de `GL₂(ℚ_p)` et `(φ, Γ)`-modules*, Astérisque 330 (2010),
  Introduction §1.
* P. Colmez, *Représentations triangulines de dimension 2*, Astérisque 319 (2008), §0.1.
-/

public section

noncomputable section

open ValuativeRel

namespace TauCeti

variable (p : ℕ) [Fact p.Prime]

/-- The inclusion `ℤ_pˣ → ℚ_pˣ` of the units of the `p`-adic integers, as a continuous
homomorphism. -/
def padicIntUnitsInclusion : ℤ_[p]ˣ →ₜ* ℚ_[p]ˣ :=
  ⟨Units.map (algebraMap ℤ_[p] ℚ_[p]).toMonoidHom,
    Continuous.units_map _ continuous_subtypeVal⟩

variable {p}

/-- The inclusion `ℤ_pˣ → ℚ_pˣ` is the identity on underlying `p`-adic numbers. -/
@[simp]
theorem coe_padicIntUnitsInclusion_apply (u : ℤ_[p]ˣ) :
    ((padicIntUnitsInclusion p u : ℚ_[p]ˣ) : ℚ_[p]) = ((u : ℤ_[p]) : ℚ_[p]) :=
  (rfl)

variable (p) in
/-- **Colmez's character `x|x|`**: the unit part `x |x| = x p ^ (-v(x))` of `x ∈ ℚ_pˣ`, as a
continuous character `ℚ_pˣ → ℤ_pˣ`. It sends `p` to `1` and is the identity on `ℤ_pˣ`
(`TauCeti.padicUnitPart_apply_of_eq`). -/
def padicUnitPart : ℚ_[p]ˣ →ₜ* ℤ_[p]ˣ where
  toFun x := PadicInt.mkUnits ((PadicInt.norm_coe _).trans (Padic.norm_unitPart x.ne_zero))
  map_one' := Units.ext <| PadicInt.ext <| by simp
  map_mul' x y := Units.ext <| PadicInt.ext <| by
    simp only [Units.val_mul, PadicInt.coe_mul, PadicInt.mkUnits_eq, Padic.coe_unitPart,
      Padic.valuation_mul x.ne_zero y.ne_zero, neg_add,
      zpow_add₀ (Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero : (p : ℚ_[p]) ≠ 0)]
    ring
  continuous_toFun := by
    refine Units.isOpenEmbedding_val.isEmbedding.continuous_iff.2 <|
      PadicInt.isOpenEmbedding_coe.isEmbedding.continuous_iff.2 ?_
    exact (Units.continuous_val.mul
      ((continuous_of_discreteTopology (f := fun n : ℤ ↦ (p : ℚ_[p]) ^ (-n))).comp
        Padic.continuous_valuation_units)).congr fun x ↦
      ((PadicInt.mkUnits_eq _).trans (Padic.coe_unitPart _)).symm

/-- The unit part of `x` is `x p ^ (-v(x))`. -/
@[simp]
theorem coe_padicUnitPart_apply (x : ℚ_[p]ˣ) :
    ((padicUnitPart p x : ℤ_[p]) : ℚ_[p]) = x * (p : ℚ_[p]) ^ (-(x : ℚ_[p]).valuation) :=
  (PadicInt.mkUnits_eq ((PadicInt.norm_coe _).trans (Padic.norm_unitPart x.ne_zero))).trans
    (Padic.coe_unitPart _)

/-- On nonzero `p`-adic numbers, the unit part `TauCeti.padicUnitPart` is the total unit part
`Padic.unitPart`. -/
theorem coe_padicUnitPart_eq_unitPart (x : ℚ_[p]ˣ) :
    ((padicUnitPart p x : ℤ_[p]ˣ) : ℤ_[p]) = Padic.unitPart (x : ℚ_[p]) :=
  PadicInt.ext ((coe_padicUnitPart_apply x).trans (Padic.coe_unitPart _).symm)

/-- **Every nonzero `p`-adic number is `p ^ v(x)` times its unit part.** -/
theorem coe_eq_zpow_valuation_mul_padicUnitPart (x : ℚ_[p]ˣ) :
    (x : ℚ_[p]) = (p : ℚ_[p]) ^ (x : ℚ_[p]).valuation * (padicUnitPart p x : ℤ_[p]) := by
  rw [coe_padicUnitPart_apply, ← Padic.coe_unitPart]
  exact Padic.eq_zpow_valuation_mul_unitPart _

/-- **The unit part of `p ^ k u` is `u`.** In particular `x|x|` sends `p` to `1` and is the
identity on `ℤ_pˣ`. -/
theorem padicUnitPart_apply_of_eq {x : ℚ_[p]ˣ} {k : ℤ} {u : ℤ_[p]ˣ}
    (hx : (x : ℚ_[p]) = (p : ℚ_[p]) ^ k * (u : ℤ_[p])) : padicUnitPart p x = u := by
  have hp : (p : ℚ_[p]) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero
  have hv : (x : ℚ_[p]).valuation = k := by
    rw [hx, Padic.valuation_p_zpow_mul k (by simp), PadicInt.valuation_coe,
      PadicInt.valuation_eq_zero_of_isUnit u.isUnit, Nat.cast_zero, add_zero]
  refine Units.ext <| PadicInt.ext ?_
  rw [coe_padicUnitPart_apply, hv, hx, zpow_neg]
  field_simp

/-- `x|x|` sends `p` to `1`. -/
@[simp]
theorem padicUnitPart_padicPrimeUnit : padicUnitPart p (padicPrimeUnit p) = 1 :=
  padicUnitPart_apply_of_eq (k := 1) (by simp)

/-- `x|x|` is the identity on `ℤ_pˣ`. -/
@[simp]
theorem padicUnitPart_padicIntUnitsInclusion (u : ℤ_[p]ˣ) :
    padicUnitPart p (padicIntUnitsInclusion p u) = u :=
  padicUnitPart_apply_of_eq (k := 0) (by simp)

/-- **Homomorphisms out of `ℚ_pˣ`.** A homomorphism from `ℚ_pˣ` to a monoid is determined by its
value at `p` and its restriction to `ℤ_pˣ`. -/
theorem padicUnits_hom_ext {M : Type*} [Monoid M] {f g : ℚ_[p]ˣ →* M}
    (hp : f (padicPrimeUnit p) = g (padicPrimeUnit p))
    (hu : ∀ u : ℤ_[p]ˣ, f (padicIntUnitsInclusion p u) = g (padicIntUnitsInclusion p u)) :
    f = g := by
  -- Pass to the units of `M`, where integer powers make sense.
  suffices f.toHomUnits = g.toHomUnits from
    MonoidHom.ext fun x ↦ congrArg Units.val (DFunLike.congr_fun this x)
  ext1 x
  have hx : x = padicPrimeUnit p ^ (x : ℚ_[p]).valuation *
      padicIntUnitsInclusion p (padicUnitPart p x) :=
    Units.ext <| by simpa using coe_eq_zpow_valuation_mul_padicUnitPart x
  rw [hx, map_mul, map_mul, map_zpow, map_zpow]
  exact congr_arg₂ (· ^ _ * ·) (Units.ext hp) (Units.ext (hu _))

end TauCeti

namespace ContinuousMonoidHom

open TauCeti

variable {p : ℕ} [Fact p.Prime] {G : Type*} [CommGroup G] [TopologicalSpace G] [ContinuousMul G]

/-- **Decomposition of a character of `ℚ_pˣ`.** A continuous character `δ` of `ℚ_pˣ` is the
product of the unramified character of `δ(p)` and its restriction to `ℤ_pˣ` composed with
`x|x|`: `δ(x) = δ(p) ^ v(x) · δ(x |x|)`. -/
theorem eq_unramifiedCharacter_mul_comp_padicUnitPart (δ : ℚ_[p]ˣ →ₜ* G) :
    δ = unramifiedCharacter ℚ_[p] (δ (padicPrimeUnit p)) *
      (δ.comp (padicIntUnitsInclusion p)).comp (padicUnitPart p) := by
  refine ContinuousMonoidHom.toMonoidHom_injective <| padicUnits_hom_ext ?_ fun u ↦ ?_
  · simp
  · simp [PadicInt.valuation_eq_zero_of_isUnit u.isUnit]

end ContinuousMonoidHom

namespace TauCeti

variable {p : ℕ} [Fact p.Prime] {G : Type*} [CommGroup G] [TopologicalSpace G] [ContinuousMul G]

variable (p G) in
/-- **Colmez's description of the characters of `ℚ_pˣ`.** A continuous character of `ℚ_pˣ` with
values in a commutative topological group `G` is the same as a pair of an element `δ(p) ∈ G` and a
continuous character `δ|_{ℤ_pˣ}` of `ℤ_pˣ`; the inverse sends `(a, κ)` to `μ_a · (κ ∘ x|x|)`. For
`G = Λˣ` the second factor is the weight space `TauCeti.WeightSpace p Λ`. -/
def padicUnitsCharacterEquiv : (ℚ_[p]ˣ →ₜ* G) ≃* G × (ℤ_[p]ˣ →ₜ* G) where
  toFun δ := (δ (padicPrimeUnit p), δ.comp (padicIntUnitsInclusion p))
  invFun aκ := unramifiedCharacter ℚ_[p] aκ.1 * aκ.2.comp (padicUnitPart p)
  left_inv δ := δ.eq_unramifiedCharacter_mul_comp_padicUnitPart.symm
  right_inv aκ := by
    refine Prod.ext (by simp) (ContinuousMonoidHom.ext fun u ↦ ?_)
    simp [PadicInt.valuation_eq_zero_of_isUnit u.isUnit]
  map_mul' δ δ' := Prod.ext rfl (ContinuousMonoidHom.ext fun _ ↦ rfl)

/-- The first component of `TauCeti.padicUnitsCharacterEquiv` is the value at `p`. -/
@[simp]
theorem padicUnitsCharacterEquiv_apply_fst (δ : ℚ_[p]ˣ →ₜ* G) :
    (padicUnitsCharacterEquiv p G δ).1 = δ (padicPrimeUnit p) :=
  (rfl)

/-- The second component of `TauCeti.padicUnitsCharacterEquiv` is the restriction to `ℤ_pˣ`. -/
@[simp]
theorem padicUnitsCharacterEquiv_apply_snd (δ : ℚ_[p]ˣ →ₜ* G) :
    (padicUnitsCharacterEquiv p G δ).2 = δ.comp (padicIntUnitsInclusion p) :=
  (rfl)

/-- The inverse of `TauCeti.padicUnitsCharacterEquiv` sends `(a, κ)` to `μ_a · (κ ∘ x|x|)`. -/
@[simp]
theorem padicUnitsCharacterEquiv_symm_apply (aκ : G × (ℤ_[p]ˣ →ₜ* G)) :
    (padicUnitsCharacterEquiv p G).symm aκ =
      unramifiedCharacter ℚ_[p] aκ.1 * aκ.2.comp (padicUnitPart p) :=
  (rfl)

end TauCeti

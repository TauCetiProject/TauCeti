/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.PadicIntegralAlgebra
public import TauCeti.NumberTheory.NumberField.TotallyPositive
public import TauCeti.NumberTheory.Padics.WeightSpace.Basic
public import TauCeti.Topology.Algebra.ContinuousMonoidHom.Units
import TauCeti.RingTheory.Norm.Congruence
import TauCeti.Topology.Algebra.Algebra.Norm
import TauCeti.Topology.Algebra.ContinuousMonoidHom.Basic
import TauCeti.Topology.Algebra.ContinuousMonoidHom.Prod

/-!
# Hilbert weight spaces and the inverse norm convention

For a number field `K` and a prime `p`, let `O_p = ℤ_p ⊗[ℤ] 𝓞 K` be the integral `p`-adic
algebra (`TauCeti.NumberField.PadicIntegralAlgebra K p`) and `N_p : O_pˣ →ₜ* ℤ_pˣ` its unit-group
norm (`TauCeti.HilbertModular.normUnitsHom`). For any topological monoid `R`,

* a **geometric weight** (`TauCeti.HilbertModular.GeometricWeight K p R`) is a continuous
  homomorphism `O_pˣ →ₜ* Rˣ`;
* an **arithmetic weight** (`TauCeti.HilbertModular.ArithmeticWeight K p R`) is a continuous
  homomorphism `(O_pˣ × ℤ_pˣ) →ₜ* Rˣ`.

Over a commutative topological monoid `R`, Mathlib's `ContinuousMonoidHom.coprod` pairs a geometric
weight `w : GeometricWeight K p R` and a central character `t : TauCeti.WeightSpace p R` into the
arithmetic weight `(x, y) ↦ w x * t y`, with `ContinuousMonoidHom.coprodEquiv` identifying
`GeometricWeight K p R × TauCeti.WeightSpace p R ≃* ArithmeticWeight K p R`.

The **inverse norm map** (`TauCeti.HilbertModular.inverseNormHom`) is the continuous group
homomorphism

```text
O_pˣ →ₜ* O_pˣ × ℤ_pˣ,       x ↦ (x ^ 2, N_p(x)⁻¹).
```

Precomposing an arithmetic weight `κ` with this map (`TauCeti.HilbertModular.inverseNormPullback`)
gives the associated geometric weight `x ↦ κ(x ^ 2, N_p(x)⁻¹)`, which for a pair `(w, t)` evaluates
to `w(x) ^ 2 * t(N_p(x))⁻¹`. On an algebraic pair `(a_σ, v)` over a splitting topological
`ℤ_p`-algebra field `E` of characteristic zero, the resulting geometric exponents are `2 * a_σ - v`
(`TauCeti.HilbertModular.inverseNormPullback_coprod_algebraic`).

For an integer `N > 2` and a global unit `η ∈ (𝓞 K)ˣ` with `η ≡ 1 (mod N 𝓞 K)`, the integral norm
`N_{K/ℚ}(η)` is `1` without any total-positivity assumption
(`TauCeti.HilbertModular.norm_ringOfIntegers_eq_one_of_mem_principalUnitGroup`). Consequently the
central factor `t(N_p(x))` vanishes both on global congruence units and on their topological closure
in `O_pˣ` (`TauCeti.HilbertModular.topologicalClosure_map_principalUnitGroup_le_ker_normUnitsHom`),
reducing `inverseNormPullback` on that closure to `w ^ 2`.

## Main definitions

* `TauCeti.HilbertModular.GeometricWeight`, `TauCeti.HilbertModular.ArithmeticWeight`: geometric
  and arithmetic weights with values in `Rˣ`.
* `TauCeti.HilbertModular.normUnitsHom`: the continuous norm `O_pˣ →ₜ* ℤ_pˣ`.
* `TauCeti.HilbertModular.inverseNormHom`: the continuous group homomorphism
  `x ↦ (x ^ 2, N_p(x)⁻¹)`.
* `TauCeti.HilbertModular.inverseNormPullback`: pullback of an arithmetic weight to a geometric
  weight along `inverseNormHom`.
* `TauCeti.HilbertModular.globalUnitInclusion`: the inclusion `(𝓞 K)ˣ →* O_pˣ`, `η ↦ 1 ⊗ η`.
* `TauCeti.HilbertModular.embeddingChar`, `TauCeti.HilbertModular.algebraicGeometricWeight`,
  `TauCeti.HilbertModular.algebraicCentralWeight`: algebraic characters attached to embeddings
  `σ : K →+* E`.

## Main results

* `TauCeti.HilbertModular.inverseNormPullback_coprod`: `(w.coprod t)` pulls back to
  `w ^ 2 * (t.comp (normUnitsHom K p))⁻¹`.
* `TauCeti.HilbertModular.inverseNormPullback_coprod_algebraic`: an algebraic pair `(a, v)` pulls
  back to the algebraic geometric weight with exponents `2 * a σ - v`.
* `TauCeti.HilbertModular.norm_ringOfIntegers_eq_one_of_mem_principalUnitGroup`: global units
  congruent to `1` modulo `N > 2` have integer norm `1`.
* `TauCeti.HilbertModular.topologicalClosure_map_principalUnitGroup_le_ker_normUnitsHom`: the
  topological closure of the congruence units in `O_pˣ` lies in the kernel of `N_p`, so the
  central factor of an arithmetic weight vanishes on it.

## References

* C. Birkbeck, B. Heuer, C. Williams, *Overconvergent Hilbert modular forms via perfectoid
  modular varieties*, Ann. Inst. Fourier 73 (2023), Definition 6.1, §6.1, and §9.1.
* F. Andreatta, A. Iovita, V. Pilloni, *The adic, cuspidal, Hilbert eigenvarieties*, Res. Math.
  Sci. 3 (2016), §2.
-/

public section

open Filter Topology
open TauCeti.NumberField
open scoped NumberField

namespace TauCeti.HilbertModular

section Weights

variable (K : Type*) [Field K] (p : ℕ) [Fact p.Prime]

/-- A **geometric weight** of level at `p` for `K` with values in a topological monoid `R`:
a continuous homomorphism `(ℤ_p ⊗[ℤ] 𝓞 K)ˣ →ₜ* Rˣ`. -/
abbrev GeometricWeight (R : Type*) [Monoid R] [TopologicalSpace R] : Type _ :=
  (PadicIntegralAlgebra K p)ˣ →ₜ* Rˣ

/-- An **arithmetic weight** for `K` at `p` with values in a topological monoid `R`: a continuous
homomorphism `((ℤ_p ⊗[ℤ] 𝓞 K)ˣ × ℤ_pˣ) →ₜ* Rˣ`. -/
abbrev ArithmeticWeight (R : Type*) [Monoid R] [TopologicalSpace R] : Type _ :=
  ((PadicIntegralAlgebra K p)ˣ × ℤ_[p]ˣ) →ₜ* Rˣ

/-- Compatibility of `w.coprod t` with a continuous homomorphism `f : R →ₜ* S` on the
coefficients. -/
theorem unitsMap_comp_coprod {R S : Type*} [CommMonoid R] [CommMonoid S] [TopologicalSpace R]
    [TopologicalSpace S] [ContinuousMul R] [ContinuousMul S] (f : R →ₜ* S)
    (w : GeometricWeight K p R) (t : WeightSpace p R) :
    f.unitsMap.comp (w.coprod t) = (f.unitsMap.comp w).coprod (f.unitsMap.comp t) :=
  ContinuousMonoidHom.comp_coprod f.unitsMap w t

/-- The unit-group norm `N_p : O_pˣ →ₜ* ℤ_pˣ` as a continuous homomorphism. -/
noncomputable def normUnitsHom : (PadicIntegralAlgebra K p)ˣ →ₜ* ℤ_[p]ˣ where
  toMonoidHom := TauCeti.Algebra.normUnits ℤ_[p]
  continuous_toFun := TauCeti.Algebra.continuous_normUnits ℤ_[p] (PadicIntegralAlgebra K p)

@[simp]
theorem coe_normUnitsHom :
    (normUnitsHom K p : (PadicIntegralAlgebra K p)ˣ →* ℤ_[p]ˣ) =
      TauCeti.Algebra.normUnits ℤ_[p] :=
  (rfl)

@[simp]
theorem normUnitsHom_apply (x : (PadicIntegralAlgebra K p)ˣ) :
    normUnitsHom K p x = TauCeti.Algebra.normUnits ℤ_[p] x :=
  (rfl)

/-- The inclusion of global units `(𝓞 K)ˣ →* O_pˣ`, `η ↦ 1 ⊗ η`. -/
noncomputable def globalUnitInclusion : (𝓞 K)ˣ →* (PadicIntegralAlgebra K p)ˣ :=
  Units.map (algebraMap (𝓞 K) (PadicIntegralAlgebra K p) : 𝓞 K →* PadicIntegralAlgebra K p)

@[simp]
theorem coe_globalUnitInclusion_apply (u : (𝓞 K)ˣ) :
    ((globalUnitInclusion K p u : (PadicIntegralAlgebra K p)ˣ) : PadicIntegralAlgebra K p) =
      algebraMap (𝓞 K) (PadicIntegralAlgebra K p) u :=
  (rfl)

theorem globalUnitInclusion_injective [NumberField K] :
    Function.Injective (globalUnitInclusion K p) :=
  fun _ _ h ↦ Units.ext <|
    PadicIntegralAlgebra.algebraMap_ringOfIntegers_injective (K := K) (p := p) <| by
      simpa only [← coe_globalUnitInclusion_apply] using congrArg Units.val h

theorem normUnitsHom_globalUnitInclusion [NumberField K] (u : (𝓞 K)ˣ) :
    normUnitsHom K p (globalUnitInclusion K p u) =
      Units.map (Int.castRingHom ℤ_[p] : ℤ →* ℤ_[p]) (TauCeti.Algebra.normUnits ℤ u) :=
  PadicIntegralAlgebra.normUnits_unitsMap_algebraMap K p u

end Weights

section InverseNorm

variable (K : Type*) [Field K] [NumberField K] (p : ℕ) [Fact p.Prime]

/-- The **inverse norm homomorphism** `O_pˣ →ₜ* O_pˣ × ℤ_pˣ`, sending `x` to `(x ^ 2, N_p(x)⁻¹)`. -/
noncomputable def inverseNormHom :
    (PadicIntegralAlgebra K p)ˣ →ₜ* (PadicIntegralAlgebra K p)ˣ × ℤ_[p]ˣ :=
  ((ContinuousMonoidHom.id (PadicIntegralAlgebra K p)ˣ) ^ 2).prod (normUnitsHom K p)⁻¹

@[simp]
theorem inverseNormHom_apply (x : (PadicIntegralAlgebra K p)ˣ) :
    inverseNormHom K p x = (x ^ 2, (TauCeti.Algebra.normUnits ℤ_[p] x)⁻¹) := by
  simp [inverseNormHom]

theorem inverseNormHom_neg_one :
    inverseNormHom K p (-1) = (1, (-1) ^ Module.finrank ℚ K) := by
  have hnorm : TauCeti.Algebra.normUnits ℤ_[p] (-1 : (PadicIntegralAlgebra K p)ˣ) =
      (-1) ^ Module.finrank ℚ K := by
    refine Units.ext ?_
    rw [TauCeti.Algebra.coe_normUnits, Units.val_pow_eq_pow_val, Units.val_neg, Units.val_one,
      ← map_one (algebraMap ℤ_[p] (PadicIntegralAlgebra K p)), ← map_neg, Algebra.norm_algebraMap,
      PadicIntegralAlgebra.finrank_eq]
    simp
  have hneg : (-1 : ℤ_[p]ˣ)⁻¹ = -1 := Units.ext (by simp)
  rw [inverseNormHom_apply, neg_one_sq, hnorm, ← inv_pow, hneg]

/-- Pullback of an arithmetic weight along the inverse norm map `x ↦ (x ^ 2, N_p(x)⁻¹)`,
producing a geometric weight. -/
noncomputable def inverseNormPullback {R : Type*} [Monoid R] [TopologicalSpace R]
    (κ : ArithmeticWeight K p R) : GeometricWeight K p R :=
  κ.comp (inverseNormHom K p)

@[simp]
theorem inverseNormPullback_apply {R : Type*} [Monoid R] [TopologicalSpace R]
    (κ : ArithmeticWeight K p R) (x : (PadicIntegralAlgebra K p)ˣ) :
    inverseNormPullback K p κ x = κ (x ^ 2, (TauCeti.Algebra.normUnits ℤ_[p] x)⁻¹) := by
  simp only [inverseNormPullback, ContinuousMonoidHom.coe_comp, Function.comp_apply,
    inverseNormHom_apply]

/-- Pullback along `inverseNormHom` commutes with postcomposition by continuous unit-group maps
(including those induced by continuous ring homomorphisms). -/
theorem unitsMap_comp_inverseNormPullback {R S : Type*} [Monoid R] [Monoid S]
    [TopologicalSpace R] [TopologicalSpace S] (f : R →ₜ* S) (κ : ArithmeticWeight K p R) :
    f.unitsMap.comp (inverseNormPullback K p κ) = inverseNormPullback K p (f.unitsMap.comp κ) :=
  (rfl)

section CommMonoid

variable {R : Type*} [CommMonoid R] [TopologicalSpace R] [ContinuousMul R]

/-- Pullback along `inverseNormHom` as a group homomorphism from arithmetic weights to geometric
weights. -/
noncomputable def inverseNormPullbackHom :
    ArithmeticWeight K p R →* GeometricWeight K p R where
  toFun := inverseNormPullback K p
  map_one' := ContinuousMonoidHom.ext fun _ ↦ rfl
  map_mul' _ _ := ContinuousMonoidHom.ext fun _ ↦ rfl

@[simp]
theorem coe_inverseNormPullbackHom :
    (inverseNormPullbackHom K p (R := R) : ArithmeticWeight K p R → GeometricWeight K p R) =
      inverseNormPullback K p :=
  (rfl)

/-- The geometric weight attached to `(w, t)` is `κ(x) = w(x) ^ 2 * t(N_p(x))⁻¹`. -/
theorem inverseNormPullback_coprod (w : GeometricWeight K p R) (t : WeightSpace p R) :
    inverseNormPullback K p (w.coprod t) = w ^ 2 * (t.comp (normUnitsHom K p))⁻¹ := by
  ext x
  simp [sq]

theorem inverseNormPullback_coprod_apply (w : GeometricWeight K p R) (t : WeightSpace p R)
    (x : (PadicIntegralAlgebra K p)ˣ) :
    inverseNormPullback K p (w.coprod t) x =
      w x ^ 2 * (t (TauCeti.Algebra.normUnits ℤ_[p] x))⁻¹ := by
  rw [inverseNormPullback_coprod]
  simp

/-- When the central character `t` is trivial, the geometric weight attached to `(w, 1)` is
`w ^ 2`. -/
@[simp]
theorem inverseNormPullback_coprod_one (w : GeometricWeight K p R) :
    inverseNormPullback K p (w.coprod (1 : WeightSpace p R)) = w ^ 2 := by
  ext x
  simp [inverseNormPullback_coprod]

/-- When `w` is trivial, the geometric weight attached to `(1, t)` is `(t ∘ N_p)⁻¹`. -/
@[simp]
theorem inverseNormPullback_one_coprod (t : WeightSpace p R) :
    inverseNormPullback K p ((1 : GeometricWeight K p R).coprod t) =
      (t.comp (normUnitsHom K p))⁻¹ := by
  ext x
  simp [inverseNormPullback_coprod]

/-- On a global unit `η ∈ (𝓞 K)ˣ`, the pullback of `(w, t)` evaluates to
`w(1 ⊗ η) ^ 2 * t(N(η))⁻¹`. -/
theorem inverseNormPullback_coprod_globalUnitInclusion (w : GeometricWeight K p R)
    (t : WeightSpace p R) (η : (𝓞 K)ˣ) :
    inverseNormPullback K p (w.coprod t) (globalUnitInclusion K p η) =
      w (globalUnitInclusion K p η) ^ 2 *
        (t (Units.map (Int.castRingHom ℤ_[p] : ℤ →* ℤ_[p])
          (TauCeti.Algebra.normUnits ℤ η)))⁻¹ := by
  rw [inverseNormPullback_coprod_apply, ← normUnitsHom_apply, normUnitsHom_globalUnitInclusion]

/-- On a global unit of norm `1`, the central factor cancels and the pullback of `(w, t)`
evaluates to `w(1 ⊗ η) ^ 2`. -/
theorem inverseNormPullback_coprod_globalUnitInclusion_of_norm_eq_one
    (w : GeometricWeight K p R) (t : WeightSpace p R) {η : (𝓞 K)ˣ}
    (hη : Algebra.norm ℤ (η : 𝓞 K) = 1) :
    inverseNormPullback K p (w.coprod t) (globalUnitInclusion K p η) =
      w (globalUnitInclusion K p η) ^ 2 := by
  have hnorm : TauCeti.Algebra.normUnits ℤ η = 1 :=
    Units.ext (by simpa [TauCeti.Algebra.coe_normUnits] using hη)
  rw [inverseNormPullback_coprod_globalUnitInclusion, hnorm]
  simp

/-- On a totally positive global unit, the integer norm is `1`, so the central factor cancels and
the pullback of `(w, t)` evaluates to `w(1 ⊗ η) ^ 2`. -/
theorem inverseNormPullback_coprod_globalUnitInclusion_of_isTotallyPositive
    (w : GeometricWeight K p R) (t : WeightSpace p R) {η : (𝓞 K)ˣ}
    (hη : NumberField.IsTotallyPositive ((η : 𝓞 K) : K)) :
    inverseNormPullback K p (w.coprod t) (globalUnitInclusion K p η) =
      w (globalUnitInclusion K p η) ^ 2 := by
  refine inverseNormPullback_coprod_globalUnitInclusion_of_norm_eq_one K p w t ?_
  have hne : ((η : 𝓞 K) : K) ≠ 0 :=
    (η.isUnit.map (algebraMap (𝓞 K) K : 𝓞 K →* K)).ne_zero
  have hpos : (0 : ℚ) < Algebra.norm ℚ ((η : 𝓞 K) : K) :=
    NumberField.norm_pos_of_isTotallyPositive hne hη
  rw [← Algebra.coe_norm_int] at hpos
  rcases Int.isUnit_iff.mp (η.isUnit.map (Algebra.norm ℤ)) with h1 | hneg
  · exact h1
  · exact absurd hpos (by rw [hneg]; norm_num)

/-- On a global unit of norm `-1`, the pullback of `(w, t)` picks up the central sign factor
`t(-1)⁻¹`. -/
theorem inverseNormPullback_coprod_globalUnitInclusion_of_norm_eq_neg_one
    (w : GeometricWeight K p R) (t : WeightSpace p R) {η : (𝓞 K)ˣ}
    (hη : Algebra.norm ℤ (η : 𝓞 K) = -1) :
    inverseNormPullback K p (w.coprod t) (globalUnitInclusion K p η) =
      w (globalUnitInclusion K p η) ^ 2 * (t (-1))⁻¹ := by
  have hnorm : TauCeti.Algebra.normUnits ℤ η = -1 :=
    Units.ext (by simpa [TauCeti.Algebra.coe_normUnits] using hη)
  rw [inverseNormPullback_coprod_globalUnitInclusion, hnorm]
  simp

end CommMonoid

end InverseNorm

section AlgebraicWeights

section EmbeddingChar

variable (K : Type*) [Field K] (p : ℕ) [Fact p.Prime] (E : Type*) [CommRing E] [TopologicalSpace E]
  [IsTopologicalAddGroup E] [Algebra ℤ_[p] E] [ContinuousSMul ℤ_[p] E]

/-- The continuous character `O_pˣ →ₜ* Eˣ` attached to a ring homomorphism `σ : K →+* E` via
`a ⊗ y ↦ a · σ(y)`. Continuity follows from the `ℤ_p`-module topology on `O_p`. -/
noncomputable def embeddingChar (σ : K →+* E) : GeometricWeight K p E :=
  let φ := PadicIntegralAlgebra.liftEquiv K p E (σ.comp (algebraMap (𝓞 K) K))
  { toMonoidHom := Units.map (φ : PadicIntegralAlgebra K p →* E)
    continuous_toFun :=
      Continuous.units_map _ (IsModuleTopology.continuous_of_linearMap φ.toLinearMap) }

variable {K p E} in
@[simp]
theorem coe_embeddingChar_apply (σ : K →+* E) (x : (PadicIntegralAlgebra K p)ˣ) :
    (embeddingChar K p E σ x : E) =
      PadicIntegralAlgebra.liftEquiv K p E (σ.comp (algebraMap (𝓞 K) K))
        (x : PadicIntegralAlgebra K p) :=
  (rfl)

variable {K p E} in
theorem coe_embeddingChar_globalUnitInclusion (σ : K →+* E) (u : (𝓞 K)ˣ) :
    (embeddingChar K p E σ (globalUnitInclusion K p u) : E) = σ ((u : 𝓞 K) : K) := by
  simp [coe_embeddingChar_apply]

end EmbeddingChar

section CentralAlgebraic

variable (p : ℕ) [Fact p.Prime] (E : Type*) [CommRing E] [TopologicalSpace E]
  [ContinuousMul E] [Algebra ℤ_[p] E] [ContinuousSMul ℤ_[p] E]

/-- The algebraic central weight `y ↦ y ^ v` on `ℤ_pˣ` with values in `Eˣ`. -/
noncomputable def algebraicCentralWeight (v : ℤ) : WeightSpace p E :=
  (ContinuousMonoidHom.unitsMap
    ⟨(algebraMap ℤ_[p] E : ℤ_[p] →* E), continuous_algebraMap ℤ_[p] E⟩) ^ v

@[simp]
theorem algebraicCentralWeight_apply (v : ℤ) (y : ℤ_[p]ˣ) :
    algebraicCentralWeight p E v y =
      Units.map (algebraMap ℤ_[p] E : ℤ_[p] →* E) y ^ v := by
  rw [algebraicCentralWeight, ContinuousMonoidHom.zpow_apply]
  congr 1
  ext
  simp

@[simp]
theorem algebraicCentralWeight_zero : algebraicCentralWeight p E 0 = 1 :=
  zpow_zero _

theorem algebraicCentralWeight_add (v₁ v₂ : ℤ) :
    algebraicCentralWeight p E (v₁ + v₂) =
      algebraicCentralWeight p E v₁ * algebraicCentralWeight p E v₂ :=
  zpow_add _ v₁ v₂

theorem algebraicCentralWeight_neg (v : ℤ) :
    algebraicCentralWeight p E (-v) = (algebraicCentralWeight p E v)⁻¹ := by
  refine ContinuousMonoidHom.ext fun y ↦ ?_
  simp [algebraicCentralWeight_apply]

end CentralAlgebraic

section Splitting

variable (K : Type*) [Field K] [NumberField K] (p : ℕ) [Fact p.Prime] (E : Type*) [Field E]
  [CharZero E] [TopologicalSpace E] [IsTopologicalRing E] [Algebra ℤ_[p] E]
  [ContinuousSMul ℤ_[p] E]

/-- The algebraic geometric weight `∏_σ embeddingChar σ ^ k σ` attached to integer exponents
`k : (K →+* E) → ℤ`. -/
noncomputable def algebraicGeometricWeight (k : (K →+* E) → ℤ) :
    GeometricWeight K p E :=
  ∏ σ : K →+* E, embeddingChar K p E σ ^ k σ

variable {K p E} in
@[simp]
theorem algebraicGeometricWeight_apply (k : (K →+* E) → ℤ)
    (x : (PadicIntegralAlgebra K p)ˣ) :
    algebraicGeometricWeight K p E k x = ∏ σ : K →+* E, embeddingChar K p E σ x ^ k σ := by
  rw [algebraicGeometricWeight]
  exact (map_prod
    (⟨⟨fun f : GeometricWeight K p E ↦ f x, by simp [ContinuousMonoidHom.one_toFun]⟩,
      fun f g ↦ ContinuousMonoidHom.mul_apply f g x⟩ : GeometricWeight K p E →* Eˣ)
    (fun σ ↦ embeddingChar K p E σ ^ k σ) Finset.univ).trans
    (Finset.prod_congr rfl fun σ _ ↦ ContinuousMonoidHom.zpow_apply _ _ _)

@[simp]
theorem algebraicGeometricWeight_zero : algebraicGeometricWeight K p E 0 = 1 := by
  simp [algebraicGeometricWeight]

theorem algebraicGeometricWeight_add (k₁ k₂ : (K →+* E) → ℤ) :
    algebraicGeometricWeight K p E (k₁ + k₂) =
      algebraicGeometricWeight K p E k₁ * algebraicGeometricWeight K p E k₂ := by
  ext x
  simp [zpow_add, Finset.prod_mul_distrib]

theorem algebraicGeometricWeight_neg (k : (K →+* E) → ℤ) :
    algebraicGeometricWeight K p E (-k) = (algebraicGeometricWeight K p E k)⁻¹ := by
  ext x
  simp [zpow_neg, Finset.prod_inv_distrib]

/-- **Algebraic exponent law for the inverse norm convention.** Over a splitting field `E` of
characteristic zero, the arithmetic pair with algebraic exponents `(a_σ, v)` pulls back under
`inverseNormHom` to the algebraic geometric weight with exponents `2 * a_σ - v`. -/
theorem inverseNormPullback_coprod_algebraic
    (hE : Module.finrank ℚ K ≤ Fintype.card (K →+* E)) (a : (K →+* E) → ℤ) (v : ℤ) :
    inverseNormPullback K p
        ((algebraicGeometricWeight K p E a).coprod (algebraicCentralWeight p E v)) =
      algebraicGeometricWeight K p E (fun σ ↦ 2 * a σ - v) := by
  refine ContinuousMonoidHom.ext fun x ↦ ?_
  have hnorm :
      Units.map (algebraMap ℤ_[p] E : ℤ_[p] →* E) (TauCeti.Algebra.normUnits ℤ_[p] x) =
        ∏ σ : K →+* E, embeddingChar K p E σ x := by
    refine Units.ext ?_
    push_cast
    simpa [TauCeti.Algebra.coe_normUnits] using
      PadicIntegralAlgebra.algebraMap_norm_eq_prod_embeddings K p hE
        (x : PadicIntegralAlgebra K p)
  rw [inverseNormPullback_coprod_apply, algebraicGeometricWeight_apply,
    algebraicGeometricWeight_apply]
  -- Rewrite `t(N_p(x))⁻¹` as `∏_σ embeddingChar σ x ^ (-v)` using `hnorm`.
  have hcentral : (algebraicCentralWeight p E v (TauCeti.Algebra.normUnits ℤ_[p] x))⁻¹ =
      ∏ σ : K →+* E, embeddingChar K p E σ x ^ (-v) := by
    rw [algebraicCentralWeight_apply, hnorm, ← zpow_neg, Finset.prod_zpow]
  rw [hcentral, ← Finset.prod_pow Finset.univ 2, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun σ _ ↦ ?_
  rw [← zpow_natCast, ← zpow_mul, ← zpow_add]
  congr 1
  omega

end Splitting

end AlgebraicWeights

section CongruenceUnits

variable (K : Type*) [Field K] (p : ℕ) [Fact p.Prime]

/-- **Norm-one theorem for congruence units.** Any global unit `η ∈ (𝓞 K)ˣ` congruent to `1`
modulo `N 𝓞 K` with `2 < N` has integer norm `1`. Neither total positivity nor coprimality of
`N` to `p` is required. -/
theorem norm_ringOfIntegers_eq_one_of_mem_principalUnitGroup {N : ℕ} (hN : 2 < N)
    {η : (𝓞 K)ˣ} (hη : η ∈ (Ideal.span {(N : 𝓞 K)}).principalUnitGroup) :
    Algebra.norm ℤ (η : 𝓞 K) = 1 :=
  Algebra.norm_eq_one_of_isUnit_of_sub_one_mem_span_natCast hN η.isUnit
    (Ideal.mem_principalUnitGroup.mp hη)

/-- Any global unit `η ∈ (𝓞 K)ˣ` congruent to `1` modulo `N 𝓞 K` with `2 < N` has unit norm `1`
over `ℤ`. -/
theorem normUnits_ringOfIntegers_eq_one_of_mem_principalUnitGroup {N : ℕ} (hN : 2 < N)
    {η : (𝓞 K)ˣ} (hη : η ∈ (Ideal.span {(N : 𝓞 K)}).principalUnitGroup) :
    TauCeti.Algebra.normUnits ℤ η = 1 :=
  Units.ext <| by
    simpa [TauCeti.Algebra.coe_normUnits] using
      norm_ringOfIntegers_eq_one_of_mem_principalUnitGroup K hN hη

variable [NumberField K]

/-- On the `p`-adic image of a global congruence unit modulo `N > 2`, the `p`-adic norm `N_p` is
trivial. -/
theorem normUnitsHom_globalUnitInclusion_eq_one_of_mem_principalUnitGroup {N : ℕ} (hN : 2 < N)
    {η : (𝓞 K)ˣ} (hη : η ∈ (Ideal.span {(N : 𝓞 K)}).principalUnitGroup) :
    normUnitsHom K p (globalUnitInclusion K p η) = 1 := by
  rw [normUnitsHom_globalUnitInclusion,
    normUnits_ringOfIntegers_eq_one_of_mem_principalUnitGroup K hN hη, map_one]

/-- **Central closure kernel theorem.** For `2 < N`, the topological closure in `O_pˣ` of the
global congruence units modulo `N` lies in the kernel of `N_p : O_pˣ →ₜ* ℤ_pˣ`. -/
theorem topologicalClosure_map_principalUnitGroup_le_ker_normUnitsHom {N : ℕ} (hN : 2 < N) :
    ((Ideal.span {(N : 𝓞 K)}).principalUnitGroup.map
      (globalUnitInclusion K p)).topologicalClosure ≤ (normUnitsHom K p).toMonoidHom.ker := by
  refine Subgroup.topologicalClosure_minimal _ ?_ (normUnitsHom K p).isClosed_ker
  rintro _ ⟨η, hη, rfl⟩
  exact normUnitsHom_globalUnitInclusion_eq_one_of_mem_principalUnitGroup K p hN hη

/-- Consequently, for every `z` in the topological closure of the congruence units modulo `N > 2`
in `O_pˣ` and every arithmetic pair `(w, t)`, the central factor `t(N_p(z))` is trivial and the
inverse norm pullback evaluates to `w(z) ^ 2`. -/
theorem inverseNormPullback_coprod_eq_sq_of_mem_topologicalClosure {R : Type*} [CommMonoid R]
    [TopologicalSpace R] [ContinuousMul R] (w : GeometricWeight K p R) (t : WeightSpace p R)
    {N : ℕ} (hN : 2 < N) {z : (PadicIntegralAlgebra K p)ˣ}
    (hz : z ∈ ((Ideal.span {(N : 𝓞 K)}).principalUnitGroup.map
      (globalUnitInclusion K p)).topologicalClosure) :
    inverseNormPullback K p (w.coprod t) z = w z ^ 2 := by
  have hnorm : TauCeti.Algebra.normUnits ℤ_[p] z = 1 :=
    topologicalClosure_map_principalUnitGroup_le_ker_normUnitsHom K p hN hz
  simp [hnorm]

end CongruenceUnits

end TauCeti.HilbertModular

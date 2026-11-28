/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.PadicIntegralAlgebra.Basic
public import TauCeti.NumberTheory.NumberField.TotallyPositive
public import TauCeti.NumberTheory.Padics.WeightSpace.Basic
public import TauCeti.Topology.Algebra.ContinuousMonoidHom.Units
import TauCeti.Topology.Algebra.ContinuousMonoidHom.Basic
import TauCeti.Topology.Algebra.ContinuousMonoidHom.Prod

/-!
# Hilbert weight spaces and the inverse norm convention

For a number field `K` and a prime `p`, let `O_p = ℤ_p ⊗[ℤ] 𝓞 K` be the integral `p`-adic
algebra (`TauCeti.NumberField.PadicIntegralAlgebra K p`) and `N_p : O_pˣ →ₜ* ℤ_pˣ` its unit-group
norm (`TauCeti.NumberField.PadicIntegralAlgebra.normUnitsHom`). For any topological monoid `R`,

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
(`TauCeti.NumberField.Units.norm_ringOfIntegers_eq_one_of_mem_principalUnitGroup`). Consequently
the central factor `t(N_p(x))` vanishes both on global congruence units and on their topological
closure in `O_pˣ`
(`PadicIntegralAlgebra.topologicalClosure_map_principalUnitGroup_le_ker_normUnitsHom`),
reducing `inverseNormPullback` on that closure to `w ^ 2`.

## Main definitions

* `TauCeti.HilbertModular.GeometricWeight`, `TauCeti.HilbertModular.ArithmeticWeight`: geometric
  and arithmetic weights with values in `Rˣ`.
* `TauCeti.HilbertModular.inverseNormHom`: the continuous group homomorphism
  `x ↦ (x ^ 2, N_p(x)⁻¹)`.
* `TauCeti.HilbertModular.inverseNormPullback`: pullback of an arithmetic weight to a geometric
  weight along `inverseNormHom`.
* `TauCeti.HilbertModular.embeddingChar`, `TauCeti.HilbertModular.algebraicGeometricWeight`:
  algebraic characters attached to embeddings `σ : K →+* E`.

## Main results

* `TauCeti.HilbertModular.inverseNormPullback_coprod`: `(w.coprod t)` pulls back to
  `w ^ 2 * (t.comp (PadicIntegralAlgebra.normUnitsHom K p))⁻¹`.
* `TauCeti.HilbertModular.inverseNormPullback_coprod_algebraic`: an algebraic pair `(a, v)` pulls
  back to the algebraic geometric weight with exponents `2 * a σ - v`.
* `TauCeti.HilbertModular.inverseNormPullback_coprod_eq_sq_of_mem_topologicalClosure`: on the
  topological closure of the congruence units modulo `N > 2` in `O_pˣ`, the central factor of an
  arithmetic weight cancels and the inverse norm pullback evaluates to `w(z) ^ 2`.

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

end Weights

section InverseNorm

variable (K : Type*) [Field K] [NumberField K] (p : ℕ) [Fact p.Prime]

/-- The **inverse norm homomorphism** `O_pˣ →ₜ* O_pˣ × ℤ_pˣ`, sending `x` to `(x ^ 2, N_p(x)⁻¹)`. -/
noncomputable def inverseNormHom :
    (PadicIntegralAlgebra K p)ˣ →ₜ* (PadicIntegralAlgebra K p)ˣ × ℤ_[p]ˣ :=
  ((ContinuousMonoidHom.id (PadicIntegralAlgebra K p)ˣ) ^ 2).prod
    (PadicIntegralAlgebra.normUnitsHom K p)⁻¹

@[simp]
theorem inverseNormHom_apply (x : (PadicIntegralAlgebra K p)ˣ) :
    inverseNormHom K p x = (x ^ 2, (TauCeti.Algebra.normUnits ℤ_[p] x)⁻¹) := by
  simp [inverseNormHom]

theorem inverseNormHom_neg_one :
    inverseNormHom K p (-1) = (1, (-1) ^ Module.finrank ℚ K) := by
  have hneg : Units.map (algebraMap ℤ_[p] (PadicIntegralAlgebra K p) :
      ℤ_[p] →* PadicIntegralAlgebra K p) (-1 : ℤ_[p]ˣ) = -1 :=
    Units.ext (by simp)
  have hnorm : TauCeti.Algebra.normUnits ℤ_[p] (-1 : (PadicIntegralAlgebra K p)ˣ) =
      (-1) ^ Module.finrank ℚ K := by
    simpa [hneg, PadicIntegralAlgebra.finrank_eq] using
      TauCeti.Algebra.normUnits_unitsMap_algebraMap ℤ_[p]
        (S := PadicIntegralAlgebra K p) (-1 : ℤ_[p]ˣ)
  simp [hnorm, ← inv_pow]

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
  ContinuousMonoidHom.ext fun x ↦ by
    simp only [inverseNormPullback, ContinuousMonoidHom.coe_comp, Function.comp_apply]

section CommMonoid

variable {R : Type*} [CommMonoid R] [TopologicalSpace R] [ContinuousMul R]

/-- The geometric weight attached to `(w, t)` is `κ(x) = w(x) ^ 2 * t(N_p(x))⁻¹`. -/
theorem inverseNormPullback_coprod (w : GeometricWeight K p R) (t : WeightSpace p R) :
    inverseNormPullback K p (w.coprod t) =
      w ^ 2 * (t.comp (PadicIntegralAlgebra.normUnitsHom K p))⁻¹ := by
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
      (t.comp (PadicIntegralAlgebra.normUnitsHom K p))⁻¹ := by
  ext x
  simp [inverseNormPullback_coprod]

/-- On a global unit `η ∈ (𝓞 K)ˣ`, the pullback of `(w, t)` evaluates to
`w(1 ⊗ η) ^ 2 * t(N(η))⁻¹`. -/
theorem inverseNormPullback_coprod_globalUnitInclusion (w : GeometricWeight K p R)
    (t : WeightSpace p R) (η : (𝓞 K)ˣ) :
    inverseNormPullback K p (w.coprod t) (PadicIntegralAlgebra.globalUnitInclusion K p η) =
      w (PadicIntegralAlgebra.globalUnitInclusion K p η) ^ 2 *
        (t (Units.map (Int.castRingHom ℤ_[p] : ℤ →* ℤ_[p])
          (TauCeti.Algebra.normUnits ℤ η)))⁻¹ := by
  rw [inverseNormPullback_coprod_apply, PadicIntegralAlgebra.normUnits_unitsMap_algebraMap]

/-- On a global unit of norm `1`, the central factor cancels and the pullback of `(w, t)`
evaluates to `w(1 ⊗ η) ^ 2`. -/
theorem inverseNormPullback_coprod_globalUnitInclusion_of_norm_eq_one
    (w : GeometricWeight K p R) (t : WeightSpace p R) {η : (𝓞 K)ˣ}
    (hη : Algebra.norm ℤ (η : 𝓞 K) = 1) :
    inverseNormPullback K p (w.coprod t) (PadicIntegralAlgebra.globalUnitInclusion K p η) =
      w (PadicIntegralAlgebra.globalUnitInclusion K p η) ^ 2 := by
  have hnorm : TauCeti.Algebra.normUnits ℤ η = 1 :=
    (TauCeti.Algebra.normUnits_eq_iff ℤ).mpr (by simpa using hη)
  rw [inverseNormPullback_coprod_globalUnitInclusion, hnorm]
  simp

/-- On a totally positive global unit, the integer norm is `1`, so the central factor cancels and
the pullback of `(w, t)` evaluates to `w(1 ⊗ η) ^ 2`. -/
theorem inverseNormPullback_coprod_globalUnitInclusion_of_isTotallyPositive
    (w : GeometricWeight K p R) (t : WeightSpace p R) {η : (𝓞 K)ˣ}
    (hη : NumberField.IsTotallyPositive ((η : 𝓞 K) : K)) :
    inverseNormPullback K p (w.coprod t) (PadicIntegralAlgebra.globalUnitInclusion K p η) =
      w (PadicIntegralAlgebra.globalUnitInclusion K p η) ^ 2 := by
  refine inverseNormPullback_coprod_globalUnitInclusion_of_norm_eq_one K p w t ?_
  have hpos : 0 < Algebra.norm ℤ (η : 𝓞 K) := by
    rw [← Int.cast_pos (R := ℚ), Algebra.coe_norm_int]
    exact NumberField.norm_pos_of_isTotallyPositive
      (η.isUnit.map (algebraMap (𝓞 K) K : 𝓞 K →* K)).ne_zero hη
  rw [← abs_of_pos hpos]
  exact Int.isUnit_iff_abs_eq.mp (η.isUnit.map (Algebra.norm ℤ))

/-- On a global unit of norm `-1`, the pullback of `(w, t)` picks up the central sign factor
`t(-1)⁻¹`. -/
theorem inverseNormPullback_coprod_globalUnitInclusion_of_norm_eq_neg_one
    (w : GeometricWeight K p R) (t : WeightSpace p R) {η : (𝓞 K)ˣ}
    (hη : Algebra.norm ℤ (η : 𝓞 K) = -1) :
    inverseNormPullback K p (w.coprod t) (PadicIntegralAlgebra.globalUnitInclusion K p η) =
      w (PadicIntegralAlgebra.globalUnitInclusion K p η) ^ 2 * (t (-1))⁻¹ := by
  have hnorm : TauCeti.Algebra.normUnits ℤ η = -1 :=
    (TauCeti.Algebra.normUnits_eq_iff ℤ).mpr (by simpa using hη)
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
    (embeddingChar K p E σ (PadicIntegralAlgebra.globalUnitInclusion K p u) : E) =
      σ ((u : 𝓞 K) : K) := by
  simp [coe_embeddingChar_apply]

end EmbeddingChar

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
  simp [algebraicGeometricWeight]

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

/-- Over a splitting field `E` of characteristic zero, the image in `Eˣ` of `N_p(x)` equals
the product of the embedding characters `embeddingChar σ x`. -/
theorem unitsMap_algebraMap_normUnits_eq_prod_embeddingChar
    (hE : Module.finrank ℚ K ≤ Fintype.card (K →+* E))
    (x : (PadicIntegralAlgebra K p)ˣ) :
    Units.map (algebraMap ℤ_[p] E : ℤ_[p] →* E) (TauCeti.Algebra.normUnits ℤ_[p] x) =
      ∏ σ : K →+* E, embeddingChar K p E σ x := by
  refine Units.ext ?_
  push_cast
  simpa [TauCeti.Algebra.coe_normUnits] using
    PadicIntegralAlgebra.algebraMap_norm_eq_prod_embeddings K p hE
      (x : PadicIntegralAlgebra K p)

/-- Over a splitting field `E` of characteristic zero, pulling back the algebraic central
character `y ↦ y ^ v` along `N_p` gives the algebraic geometric weight with constant exponent
`v`. -/
theorem algebraic_comp_normUnitsHom
    (hE : Module.finrank ℚ K ≤ Fintype.card (K →+* E)) (v : ℤ) :
    (WeightSpace.algebraic E v).comp (PadicIntegralAlgebra.normUnitsHom K p) =
      algebraicGeometricWeight K p E (fun _ ↦ v) := by
  ext x
  simp [WeightSpace.algebraic_apply,
    unitsMap_algebraMap_normUnits_eq_prod_embeddingChar K p E hE, Finset.prod_zpow]

/-- **Algebraic exponent law for the inverse norm convention.** Over a splitting field `E` of
characteristic zero, the arithmetic pair with algebraic exponents `(a_σ, v)` pulls back under
`inverseNormHom` to the algebraic geometric weight with exponents `2 * a_σ - v`. -/
theorem inverseNormPullback_coprod_algebraic
    (hE : Module.finrank ℚ K ≤ Fintype.card (K →+* E)) (a : (K →+* E) → ℤ) (v : ℤ) :
    inverseNormPullback K p
        ((algebraicGeometricWeight K p E a).coprod (WeightSpace.algebraic E v)) =
      algebraicGeometricWeight K p E (fun σ ↦ 2 * a σ - v) := by
  have hexp : (fun σ ↦ 2 * a σ - v) = (a + a) + -fun _ ↦ v := by
    ext σ
    simp only [Pi.add_apply, Pi.neg_apply]
    omega
  calc
    inverseNormPullback K p
        ((algebraicGeometricWeight K p E a).coprod (WeightSpace.algebraic E v))
      = algebraicGeometricWeight K p E a ^ 2 *
          (algebraicGeometricWeight K p E (fun _ ↦ v))⁻¹ := by
        rw [inverseNormPullback_coprod, algebraic_comp_normUnitsHom K p E hE v]
    _ = algebraicGeometricWeight K p E ((a + a) + -fun _ ↦ v) := by
        simp only [sq, algebraicGeometricWeight_add, algebraicGeometricWeight_neg]
    _ = algebraicGeometricWeight K p E (fun σ ↦ 2 * a σ - v) := by
        rw [hexp]

end Splitting

end AlgebraicWeights

section CongruenceUnits

variable (K : Type*) [Field K] [NumberField K] (p : ℕ) [Fact p.Prime]

/-- For every `z` in the topological closure of the congruence units modulo `N > 2` in `O_pˣ` and
every arithmetic pair `(w, t)`, the central factor `t(N_p(z))` is trivial and the inverse norm
pullback evaluates to `w(z) ^ 2`. -/
theorem inverseNormPullback_coprod_eq_sq_of_mem_topologicalClosure {R : Type*} [CommMonoid R]
    [TopologicalSpace R] [ContinuousMul R] (w : GeometricWeight K p R) (t : WeightSpace p R)
    {N : ℕ} (hN : 2 < N) {z : (PadicIntegralAlgebra K p)ˣ}
    (hz : z ∈ ((Ideal.span {(N : 𝓞 K)}).principalUnitGroup.map
      (PadicIntegralAlgebra.globalUnitInclusion K p)).topologicalClosure) :
    inverseNormPullback K p (w.coprod t) z = w z ^ 2 := by
  have hnorm : TauCeti.Algebra.normUnits ℤ_[p] z = 1 := by
    simpa only [ContinuousMonoidHom.coe_toMonoidHom, PadicIntegralAlgebra.coe_normUnitsHom] using
      MonoidHom.mem_ker.mp
        (PadicIntegralAlgebra.topologicalClosure_map_principalUnitGroup_le_ker_normUnitsHom
          K p hN hz)
  simp [hnorm]

end CongruenceUnits

end TauCeti.HilbertModular

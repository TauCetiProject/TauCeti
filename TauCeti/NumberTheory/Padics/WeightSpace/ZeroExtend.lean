/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Padics.UnitLocus
public import TauCeti.NumberTheory.Padics.WeightSpace.Basic
public import TauCeti.Topology.ContinuousMap.Clopen
import TauCeti.Analysis.Normed.Ring.CompactMonoid

/-!
# Continuous extension of weights by zero to `ℤ_p`

A `p`-adic weight `κ : WeightSpace p R` (`ℤ_pˣ →ₜ* Rˣ`) takes values in `Rˣ` on `ℤ_pˣ`. When `R`
is a topological monoid with zero, extending `κ` by `0` on the non-units `pℤ_p` along the clopen
decomposition `ℤ_p = ℤ_pˣ ⊔ pℤ_p` (`PadicInt.unitsClopen p`) via
`ContinuousMap.zeroExtendClopenFn` produces a continuous map `κ.zeroExtend : C(ℤ_p, R)`.

Because `pℤ_p` is a prime ideal of `ℤ_p`, a product in `ℤ_p` is a unit if and only if both factors
are units; consequently `κ.zeroExtend` is multiplicative on all of `ℤ_p`
(`TauCeti.WeightSpace.zeroExtend_apply_mul`). Over a topological semiring with continuous addition,
`κ.zeroExtend` agrees with `ContinuousMap.zeroExtendClopen` on `PadicInt.unitsClopen p`, and over a
seminormed ring it preserves the supremum norm of `κ.weightTest`, which equals `1` when the
seminorm is multiplicative with `‖1‖ = 1`.

## Main definitions

* `TauCeti.WeightSpace.zeroExtend`: continuous extension of `κ : WeightSpace p R` by `0` on `pℤ_p`.

## Main results

* `TauCeti.WeightSpace.zeroExtend_apply_of_isUnit`, `TauCeti.WeightSpace.zeroExtend_coe_unit`,
  `TauCeti.WeightSpace.zeroExtend_apply_of_not_isUnit`: values on units and non-units of `ℤ_p`.
* `TauCeti.WeightSpace.zeroExtend_apply_mul`, `TauCeti.WeightSpace.zeroExtend_apply_pow`:
  `κ.zeroExtend` preserves multiplication and natural powers on all of `ℤ_p`.
* `TauCeti.WeightSpace.zeroExtend_injective`, `TauCeti.WeightSpace.zeroExtend_inj`: a weight is
  uniquely determined by its zero-extension.
* `TauCeti.WeightSpace.zeroExtend_one`, `TauCeti.WeightSpace.zeroExtend_mul`,
  `TauCeti.WeightSpace.zeroExtend_pow`: compatibility with `1`, multiplication, and positive powers
  of weights.
* `TauCeti.WeightSpace.zeroExtend_inclusion_apply_of_isUnit`,
  `TauCeti.WeightSpace.norm_zeroExtend_inclusion_zpow`: evaluation and norm of zero-extended
  algebraic weights.
* `TauCeti.WeightSpace.zeroExtend_eq_zeroExtendClopen`: agreement with
  `ContinuousMap.zeroExtendClopen` over a topological semiring with continuous addition.
* `TauCeti.WeightSpace.norm_zeroExtend`, `TauCeti.WeightSpace.norm_zeroExtend_eq_one`: supremum norm
  of `κ.zeroExtend`.

## References

* P. Colmez, *Fonctions d'une variable p-adique*, Astérisque 330 (2010), §I.3.
* J. Rodrigues Jacinto and C. Williams, *An introduction to p-adic L-functions*, §§3–4.
-/

public section

namespace TauCeti.WeightSpace

variable {p : ℕ} [Fact p.Prime]

section MonoidWithZero

variable {R : Type*} [MonoidWithZero R] [TopologicalSpace R]

/-- **Continuous extension of a weight by zero.** A weight `κ : ℤ_pˣ →ₜ* Rˣ` extends to a
continuous map `C(ℤ_p, R)` equal to `x ↦ (κ u : R)` when `x = ↑u` is a unit and to `0` on the
complementary clopen ideal `pℤ_p`. -/
noncomputable def zeroExtend (κ : WeightSpace p R) : C(ℤ_[p], R) :=
  ContinuousMap.zeroExtendClopenFn (PadicInt.unitsClopen p)
    ((κ.weightTest : C(ℤ_[p]ˣ, R)).comp
      ((PadicInt.unitsHomeomorphIsUnit p).symm : C(PadicInt.unitsClopen p, ℤ_[p]ˣ)))

/-- At a unit `x : ℤ_p`, `κ.zeroExtend x` is the weight evaluated at `hx.unit`. -/
theorem zeroExtend_apply_of_isUnit (κ : WeightSpace p R) {x : ℤ_[p]} (hx : IsUnit x) :
    κ.zeroExtend x = κ hx.unit := by
  have hmem : x ∈ PadicInt.unitsClopen p := (PadicInt.mem_unitsClopen p).mpr hx
  have hu : (PadicInt.unitsHomeomorphIsUnit p).symm ⟨x, hmem⟩ = hx.unit :=
    Units.ext ((PadicInt.unitsHomeomorphIsUnit_symm_apply p ⟨x, hmem⟩).trans hx.unit_spec.symm)
  rw [zeroExtend, ContinuousMap.zeroExtendClopenFn_apply_mem _ _ hmem,
    ContinuousMap.comp_apply, ContinuousMap.coe_ofClass, ContinuousMap.coe_ofClass,
    weightTest_apply, hu]

@[simp] theorem zeroExtend_coe_unit (κ : WeightSpace p R) (u : ℤ_[p]ˣ) :
    κ.zeroExtend u = κ u := by
  rw [zeroExtend_apply_of_isUnit κ u.isUnit, Units.ext u.isUnit.unit_spec]

/-- At a non-unit `x ∈ pℤ_p`, `κ.zeroExtend x = 0`. -/
@[simp] theorem zeroExtend_apply_of_not_isUnit (κ : WeightSpace p R) {x : ℤ_[p]} (hx : ¬IsUnit x) :
    κ.zeroExtend x = 0 :=
  ContinuousMap.zeroExtendClopenFn_apply_not_mem _ _ (mt (PadicInt.mem_unitsClopen p).mp hx)

/-- At `0 : ℤ_p`, `κ.zeroExtend 0 = 0` (already simplified by `zeroExtend_apply_of_not_isUnit`). -/
theorem zeroExtend_apply_zero (κ : WeightSpace p R) : κ.zeroExtend 0 = 0 :=
  κ.zeroExtend_apply_of_not_isUnit not_isUnit_zero

@[simp] theorem zeroExtend_apply_one (κ : WeightSpace p R) : κ.zeroExtend 1 = 1 := by
  simpa using κ.zeroExtend_coe_unit 1

/-- Because `pℤ_p` is a prime ideal (`IsUnit (x * y) ↔ IsUnit x ∧ IsUnit y`), the zero-extension
of a weight is multiplicative on all of `ℤ_p`. -/
@[simp] theorem zeroExtend_apply_mul (κ : WeightSpace p R) (x y : ℤ_[p]) :
    κ.zeroExtend (x * y) = κ.zeroExtend x * κ.zeroExtend y := by
  by_cases hx : IsUnit x
  · by_cases hy : IsUnit y
    · have hxy : IsUnit (x * y) := hx.mul hy
      have hu : hxy.unit = hx.unit * hy.unit :=
        Units.ext (by rw [IsUnit.unit_spec, Units.val_mul, IsUnit.unit_spec, IsUnit.unit_spec])
      rw [zeroExtend_apply_of_isUnit κ hxy, zeroExtend_apply_of_isUnit κ hx,
        zeroExtend_apply_of_isUnit κ hy, hu, map_mul, Units.val_mul]
    · have hxy : ¬IsUnit (x * y) := fun h ↦ hy (isUnit_of_mul_isUnit_right h)
      rw [zeroExtend_apply_of_not_isUnit κ hxy, zeroExtend_apply_of_not_isUnit κ hy, mul_zero]
  · have hxy : ¬IsUnit (x * y) := fun h ↦ hx (isUnit_of_mul_isUnit_left h)
    rw [zeroExtend_apply_of_not_isUnit κ hxy, zeroExtend_apply_of_not_isUnit κ hx, zero_mul]

/-- Zero-extension commutes with all natural powers `x ^ n` on `ℤ_p` (including `n = 0`, where both
sides equal `1`). -/
@[simp] theorem zeroExtend_apply_pow (κ : WeightSpace p R) (x : ℤ_[p]) (n : ℕ) :
    κ.zeroExtend (x ^ n) = κ.zeroExtend x ^ n := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, pow_succ, zeroExtend_apply_mul, ih]

/-- The zero-extension of the trivial weight `1 : WeightSpace p R` is the indicator `1_{ℤ_pˣ}`. -/
theorem zeroExtend_one :
    (1 : WeightSpace p R).zeroExtend =
      ContinuousMap.zeroExtendClopenFn (PadicInt.unitsClopen p) 1 := by
  ext x; by_cases hx : IsUnit x
  · simp [zeroExtend_apply_of_isUnit _ hx, (PadicInt.mem_unitsClopen p).mpr hx]
  · simp [hx, mt (PadicInt.mem_unitsClopen p).mp hx]

@[simp] theorem zeroExtend_one_apply_of_isUnit {x : ℤ_[p]} (hx : IsUnit x) :
    (1 : WeightSpace p R).zeroExtend x = 1 := by
  simp [zeroExtend_apply_of_isUnit _ hx]

/-- A weight is determined by its zero-extension to `ℤ_p`. -/
theorem zeroExtend_injective : Function.Injective (zeroExtend (p := p) (R := R)) :=
  fun _ _ h ↦ ContinuousMonoidHom.ext fun u ↦ Units.ext <| by
    simpa only [zeroExtend_coe_unit] using DFunLike.congr_fun h (u : ℤ_[p])

@[simp] theorem zeroExtend_inj {κ κ' : WeightSpace p R} :
    κ.zeroExtend = κ'.zeroExtend ↔ κ = κ' := zeroExtend_injective.eq_iff

end MonoidWithZero

section CommMonoidWithZero

variable {R : Type*} [CommMonoidWithZero R] [TopologicalSpace R] [ContinuousMul R]

@[simp] theorem zeroExtend_mul (κ κ' : WeightSpace p R) :
    (κ * κ').zeroExtend = κ.zeroExtend * κ'.zeroExtend := by
  ext x; by_cases hx : IsUnit x <;> simp [zeroExtend_apply_of_isUnit, hx]

/-- Positive powers of a weight commute with zero-extension (at `n = 0`, `(κ ^ 0).zeroExtend`
vanishes on `pℤ_p` while `κ.zeroExtend ^ 0 = 1` everywhere). -/
theorem zeroExtend_pow (κ : WeightSpace p R) {n : ℕ} (hn : n ≠ 0) :
    (κ ^ n).zeroExtend = κ.zeroExtend ^ n := by
  ext x; by_cases hx : IsUnit x <;> simp [zeroExtend_apply_of_isUnit, hx, zero_pow hn]

@[simp] theorem zeroExtend_pow_apply_of_isUnit (κ : WeightSpace p R) (n : ℕ) {x : ℤ_[p]}
    (hx : IsUnit x) : (κ ^ n).zeroExtend x = κ.zeroExtend x ^ n := by
  simp [zeroExtend_apply_of_isUnit _ hx]

end CommMonoidWithZero

section Semiring

variable {R : Type*} [Semiring R] [TopologicalSpace R] [ContinuousAdd R]

/-- Over a topological semiring with continuous addition, `WeightSpace.zeroExtend` agrees with
`ContinuousMap.zeroExtendClopen` on `PadicInt.unitsClopen p`. -/
theorem zeroExtend_eq_zeroExtendClopen (S : Type*) [Semiring S] [Module S R]
    [ContinuousConstSMul S R] (κ : WeightSpace p R) :
    κ.zeroExtend = ContinuousMap.zeroExtendClopen S (PadicInt.unitsClopen p)
      ((κ.weightTest : C(ℤ_[p]ˣ, R)).comp
        ((PadicInt.unitsHomeomorphIsUnit p).symm : C(PadicInt.unitsClopen p, ℤ_[p]ˣ))) :=
  (ContinuousMap.zeroExtendClopen_apply _ _).symm

end Semiring

section Seminormed

variable {R : Type*} [SeminormedRing R]

/-- Zero-extension preserves the supremum norm of the underlying test character on `ℤ_pˣ`. -/
theorem norm_zeroExtend (κ : WeightSpace p R) :
    ‖κ.zeroExtend‖ = ‖(κ.weightTest : C(ℤ_[p]ˣ, R))‖ := by
  rw [zeroExtend, ContinuousMap.norm_zeroExtendClopenFn]
  let g := (κ.weightTest : C(ℤ_[p]ˣ, R)).comp
    ((PadicInt.unitsHomeomorphIsUnit p).symm : C(PadicInt.unitsClopen p, ℤ_[p]ˣ))
  exact le_antisymm
    ((ContinuousMap.norm_le _ (norm_nonneg _)).mpr fun _ ↦
      ContinuousMap.norm_coe_le_norm (κ.weightTest : C(ℤ_[p]ˣ, R)) _)
    ((ContinuousMap.norm_le _ (norm_nonneg _)).mpr fun u ↦ by
      simpa only [g, ContinuousMap.comp_apply, ContinuousMap.coe_ofClass,
        Homeomorph.symm_apply_apply] using
        ContinuousMap.norm_coe_le_norm g (PadicInt.unitsHomeomorphIsUnit p u))

/-- For a multiplicative seminorm with `‖1‖ = 1`, every zero-extended weight has supremum norm `1`.
-/
@[simp] theorem norm_zeroExtend_eq_one [NormMulClass R] [NormOneClass R] (κ : WeightSpace p R) :
    ‖κ.zeroExtend‖ = 1 := by
  refine le_antisymm ((ContinuousMap.norm_le _ zero_le_one).mpr fun x ↦ ?_) ?_
  · by_cases hx : IsUnit x
    · rw [zeroExtend_apply_of_isUnit κ hx, κ.norm_apply_eq_one_of_compactSpace]
    · simp [hx]
  · simpa only [zeroExtend_apply_one, norm_one] using ContinuousMap.norm_coe_le_norm κ.zeroExtend 1

/-- On units of `ℤ_p`, `(inclusion R).zeroExtend` agrees with `padicIntAlgebraMap p R`. -/
@[simp] theorem zeroExtend_inclusion_apply_of_isUnit [NormedAlgebra ℚ_[p] R] {x : ℤ_[p]}
    (hx : IsUnit x) : (inclusion (p := p) R).zeroExtend x = padicIntAlgebraMap p R x := by
  rw [zeroExtend_apply_of_isUnit _ hx, coe_inclusion_apply, IsUnit.unit_spec]

/-- Over any commutative seminormed `ℚ_p`-algebra with `‖1‖ = 1` (without requiring a
multiplicative norm), the zero-extension of every integer-power weight `inclusion K ^ m` (`m ∈ ℤ`)
has supremum norm `1`. -/
@[simp] theorem norm_zeroExtend_inclusion_zpow {K : Type*} [SeminormedCommRing K] [NormOneClass K]
    [NormedAlgebra ℚ_[p] K] (m : ℤ) : ‖(inclusion (p := p) K ^ m).zeroExtend‖ = 1 := by
  refine le_antisymm ((ContinuousMap.norm_le _ zero_le_one).mpr fun x ↦ ?_) ?_
  · by_cases hx : IsUnit x
    · rw [zeroExtend_apply_of_isUnit _ hx, ContinuousMonoidHom.zpow_apply, ← map_zpow,
        coe_inclusion_apply, norm_padicIntAlgebraMap, PadicInt.isUnit_iff.mp (hx.unit ^ m).isUnit]
    · simp [hx]
  · simpa only [zeroExtend_apply_one, norm_one] using
      ContinuousMap.norm_coe_le_norm (inclusion (p := p) K ^ m).zeroExtend 1

end Seminormed

end TauCeti.WeightSpace

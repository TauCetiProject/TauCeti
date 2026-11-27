/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.HodgeStar.Contraction
public import TauCeti.Analysis.InnerProductSpace.HodgeStar.Kahler.Basic
import TauCeti.Analysis.InnerProductSpace.Orthonormal.Coordinates
import TauCeti.LinearAlgebra.CliffordAlgebra.Contraction
import TauCeti.LinearAlgebra.ExteriorAlgebra.Contraction
import TauCeti.LinearAlgebra.ExteriorPower.NumberOperator

/-!
# The Lefschetz operator and its adjoint

Let `V` be a finite-dimensional real inner product space of dimension `2n` with an orthogonal
almost complex structure `J`, and let `ω ∈ ⋀² V` be its Kähler two-vector
`TauCeti.AlmostComplexStructure.kahlerForm`. The **Lefschetz operator** `L = ω ∧ ·` maps
`⋀ᵏ V` to `⋀ᵏ⁺² V`, and the **dual Lefschetz operator** `Λ` is its adjoint for the inner products
of the exterior powers. This file proves the basic commutator identity of the pointwise Lefschetz
algebra,

  `[Λ, L] = (n - k) Id` on `⋀ᵏ V`,

which is pure linear algebra: no closedness of a fundamental form is involved. At a point of a
Hermitian manifold, `V` is the tangent space with its metric and complex structure, and `L` and
`Λ` act on forms through the musical identification `TauCeti.alternatingFormEquiv`.

The proof writes `ω = (1/2) ∑ᵢ bᵢ ∧ J bᵢ` in an orthonormal basis `b`, so that
`Λ = (1/2) ∑ᵢ ι_{J bᵢ} ι_{bᵢ}` with `ι_u` the contraction by `⟪u, ·⟫`. Contracting `ω ∧ x` gives
`ι_u (ω ∧ x) = J u ∧ x + ω ∧ ι_u x`, that is `[ι_u, L] = ε_{J u}`, so that
`[Λ, L] = (1/2) ∑ᵢ (ι_{J bᵢ} ε_{J bᵢ} - ε_{bᵢ} ι_{bᵢ})`. The Koszul identity
`ι_u ε_u + ε_u ι_u = ‖u‖²` and the number operator `∑ᵢ ε_{bᵢ} ι_{bᵢ} = k` on `⋀ᵏ V`, applied to
the orthonormal bases `b` and `J b`, give `(1/2) (2n - k - k) = n - k`.

## Main definitions

* `TauCeti.AlmostComplexStructure.lefschetz J k`: the Lefschetz operator
  `L : ⋀ᵏ V → ⋀ᵏ⁺² V`, `x ↦ ω ∧ x`.
* `TauCeti.AlmostComplexStructure.dualLefschetz J k`: its adjoint `Λ : ⋀ᵏ⁺² V → ⋀ᵏ V`.

## Main results

* `contractLeft_kahlerForm_mul`: `ι_u (ω ∧ x) = J u ∧ x + ω ∧ ι_u x` in the exterior algebra.
* `dualLefschetz_eq_sum`: `Λ = (1/2) ∑ᵢ ι_{J bᵢ} ι_{bᵢ}` for every orthonormal basis `b`.
* `dualLefschetz_lefschetz_sub_lefschetz_dualLefschetz`: `[Λ, L] = (n - k) Id` on `⋀ᵏ V` for
  `k ≥ 2`, and `dualLefschetz_lefschetz_of_lt_two`: `Λ L = (n - k) Id` on `⋀ᵏ V` for `k < 2`.
* `zeroEquiv_dualLefschetz_zero`: on two-vectors, `Λ y = ⟪ω, y⟫` in degree zero, and
  `zeroEquiv_dualLefschetz_kahlerForm`: `Λ ω = n`.

## References

* D. Huybrechts, *Complex Geometry: An Introduction*, Springer (2005), §1.2.
* P. Griffiths and J. Harris, *Principles of Algebraic Geometry*, Wiley (1978), Chapter 0, §7.
-/

public section

noncomputable section

open Module exteriorPower CliffordAlgebra
open scoped RealInnerProductSpace

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

namespace TauCeti.AlmostComplexStructure

variable (J : AlmostComplexStructure V)

/-! ### The Lefschetz operator and its adjoint -/

/-- The **Lefschetz operator** `L = ω ∧ ·` of an almost complex structure `J` on a real inner
product space: exterior multiplication by the Kähler two-vector `ω = J.kahlerForm`, from the `k`-th
exterior power to the `(k + 2)`-th. Mathlib's `exteriorPower.wedge ℝ V 2 k ω` is the same product
with values in degree `2 + k`, which is not definitionally `k + 2`. -/
def lefschetz (k : ℕ) : ⋀[ℝ]^k V →ₗ[ℝ] ⋀[ℝ]^(k + 2) V :=
  (LinearMap.mulLeft ℝ (J.kahlerForm : ExteriorAlgebra ℝ V)).restrict fun _ hx ↦
    add_comm 2 k ▸ SetLike.mul_mem_graded J.kahlerForm.property hx

/-- The Lefschetz operator is left multiplication by `ω` in the exterior algebra. -/
@[simp]
theorem coe_lefschetz_apply (k : ℕ) (x : ⋀[ℝ]^k V) :
    (J.lefschetz k x : ExteriorAlgebra ℝ V) = J.kahlerForm * x :=
  (rfl)

/-- The **dual Lefschetz operator** `Λ : ⋀ᵏ⁺² V → ⋀ᵏ V`, the adjoint of the Lefschetz operator
`L = ω ∧ ·` for the inner products of the exterior powers. -/
def dualLefschetz (k : ℕ) : ⋀[ℝ]^(k + 2) V →ₗ[ℝ] ⋀[ℝ]^k V :=
  LinearMap.adjoint (J.lefschetz k)

/-- The dual Lefschetz operator is the adjoint of the Lefschetz operator. -/
theorem dualLefschetz_def (k : ℕ) : J.dualLefschetz k = LinearMap.adjoint (J.lefschetz k) :=
  (rfl)

/-- The adjoint of the Lefschetz operator is the dual Lefschetz operator. -/
@[simp]
theorem adjoint_lefschetz (k : ℕ) : LinearMap.adjoint (J.lefschetz k) = J.dualLefschetz k :=
  (rfl)

/-- The adjoint of the dual Lefschetz operator is the Lefschetz operator. -/
@[simp]
theorem adjoint_dualLefschetz (k : ℕ) : LinearMap.adjoint (J.dualLefschetz k) = J.lefschetz k :=
  LinearMap.adjoint_adjoint _

/-- `⟪L x, y⟫ = ⟪x, Λ y⟫`. -/
theorem inner_lefschetz_left (k : ℕ) (x : ⋀[ℝ]^k V) (y : ⋀[ℝ]^(k + 2) V) :
    ⟪J.lefschetz k x, y⟫ = ⟪x, J.dualLefschetz k y⟫ :=
  (LinearMap.adjoint_inner_right _ x y).symm

/-- `⟪Λ y, x⟫ = ⟪y, L x⟫`. -/
theorem inner_dualLefschetz_left (k : ℕ) (y : ⋀[ℝ]^(k + 2) V) (x : ⋀[ℝ]^k V) :
    ⟪J.dualLefschetz k y, x⟫ = ⟪y, J.lefschetz k x⟫ :=
  LinearMap.adjoint_inner_left _ x y

section Basis

variable {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ V)

/-- The Lefschetz operator in an orthonormal basis `b`:
`L = (1/2) ∑ᵢ ε_{bᵢ} ε_{J bᵢ}`, with `ε_u` exterior multiplication by `u`. -/
theorem lefschetz_eq_sum (k : ℕ) :
    J.lefschetz k = (2⁻¹ : ℝ) • ∑ i,
      ExteriorAlgebra.wedgeLeft (b i) (k + 1) ∘ₗ ExteriorAlgebra.wedgeLeft (J (b i)) k := by
  refine LinearMap.ext fun x ↦ Subtype.ext ?_
  simp [coe_kahlerForm J b, Finset.sum_mul, mul_assoc]

/-- The dual Lefschetz operator in an orthonormal basis `b`:
`Λ = (1/2) ∑ᵢ ι_{J bᵢ} ι_{bᵢ}`, with `ι_u` the contraction by `⟪u, ·⟫`. -/
theorem dualLefschetz_eq_sum (k : ℕ) :
    J.dualLefschetz k = (2⁻¹ : ℝ) • ∑ i,
      koszulDifferential (innerₗ V (J (b i))) k ∘ₗ koszulDifferential (innerₗ V (b i)) (k + 1) := by
  rw [dualLefschetz_def, lefschetz_eq_sum J b]
  simp [map_sum, LinearMap.adjoint_comp, adjoint_wedgeLeft]

/-- The dual Lefschetz operator in the exterior algebra, in an orthonormal basis `b`:
`Λ y = (1/2) ∑ᵢ ι_{J bᵢ} ι_{bᵢ} y`. -/
theorem coe_dualLefschetz_apply (k : ℕ) (y : ⋀[ℝ]^(k + 2) V) :
    (J.dualLefschetz k y : ExteriorAlgebra ℝ V) = (2⁻¹ : ℝ) • ∑ i,
      contractLeft (Q := (0 : QuadraticForm ℝ V)) (innerₗ V (J (b i)))
        (contractLeft (innerₗ V (b i)) y) := by
  simp [dualLefschetz_eq_sum J b]

end Basis

/-- The Lefschetz operator sends `1 ∈ ⋀⁰ V` to the Kähler two-vector `ω`. -/
@[simp]
theorem lefschetz_zero_ιMulti (v : Fin 0 → V) :
    J.lefschetz 0 (ιMulti ℝ 0 v) = J.kahlerForm := by
  ext
  simp [ExteriorAlgebra.ιMulti_apply]

/-- In degree zero the dual Lefschetz operator is the inner product with the Kähler two-vector:
`Λ y = ⟪ω, y⟫` for `y ∈ ⋀² V`, under `⋀⁰ V ≃ ℝ`. -/
@[simp]
theorem zeroEquiv_dualLefschetz_zero (y : ⋀[ℝ]^2 V) :
    zeroEquiv ℝ V (J.dualLefschetz 0 y) = ⟪J.kahlerForm, y⟫ := by
  have h : J.dualLefschetz 0 y =
      zeroEquiv ℝ V (J.dualLefschetz 0 y) • ιMulti ℝ 0 (Fin.elim0 : Fin 0 → V) :=
    (zeroEquiv ℝ V).injective (by simp)
  have hinner := inner_dualLefschetz_left J 0 y (ιMulti ℝ 0 Fin.elim0)
  rw [lefschetz_zero_ιMulti, h, real_inner_smul_left, inner_ιMulti_ιMulti] at hinner
  simpa [real_inner_comm] using hinner

/-! ### The commutator `[Λ, L]` -/

variable {J} (hJ : ∀ v w, ⟪J v, J w⟫ = ⟪v, w⟫)
include hJ

/-- **Contraction commutes with `L` up to `J`**: for an orthogonal `J`,
`ι_u (ω ∧ x) = J u ∧ x + ω ∧ ι_u x` in the exterior algebra, where `ι_u` is the contraction by
`⟪u, ·⟫`. Equivalently `[ι_u, L] = ε_{J u}`, because the contraction of `ω` by `⟪u, ·⟫` is
`J u`. -/
theorem contractLeft_kahlerForm_mul (u : V) (x : ExteriorAlgebra ℝ V) :
    contractLeft (Q := (0 : QuadraticForm ℝ V)) (innerₗ V u) (J.kahlerForm * x) =
      ExteriorAlgebra.ι ℝ (J u) * x +
        J.kahlerForm * contractLeft (Q := (0 : QuadraticForm ℝ V)) (innerₗ V u) x := by
  rw [contractLeft_mul, contractLeft_kahlerForm hJ,
    ExteriorAlgebra.involute_of_mem_exteriorPower J.kahlerForm.property]
  simp

/-- The commutator `[Λ, L]` in the exterior algebra, before the number operators are evaluated:
with `b` the standard orthonormal basis,
`∑ᵢ ι_{J bᵢ} ι_{bᵢ} (ω ∧ x) = (dim V) x - ∑ᵢ ε_{bᵢ} ι_{bᵢ} x - ∑ᵢ ε_{J bᵢ} ι_{J bᵢ} x +
ω ∧ ∑ᵢ ι_{J bᵢ} ι_{bᵢ} x`. -/
private theorem sum_contractLeft_contractLeft_kahlerForm_mul (x : ExteriorAlgebra ℝ V) :
    ∑ i, contractLeft (Q := (0 : QuadraticForm ℝ V)) (innerₗ V (J (stdOrthonormalBasis ℝ V i)))
        (contractLeft (innerₗ V (stdOrthonormalBasis ℝ V i)) (J.kahlerForm * x)) =
      (finrank ℝ V : ℝ) • x -
        ∑ i, ExteriorAlgebra.ι ℝ (stdOrthonormalBasis ℝ V i) *
          contractLeft (Q := (0 : QuadraticForm ℝ V)) (innerₗ V (stdOrthonormalBasis ℝ V i)) x -
        ∑ i, ExteriorAlgebra.ι ℝ (J (stdOrthonormalBasis ℝ V i)) *
          contractLeft (Q := (0 : QuadraticForm ℝ V)) (innerₗ V (J (stdOrthonormalBasis ℝ V i))) x +
        J.kahlerForm * ∑ i,
          contractLeft (Q := (0 : QuadraticForm ℝ V)) (innerₗ V (J (stdOrthonormalBasis ℝ V i)))
            (contractLeft (innerₗ V (stdOrthonormalBasis ℝ V i)) x) := by
  set b := stdOrthonormalBasis ℝ V
  -- Each term is `ι_{J b} (J b ∧ x + ω ∧ ι_b x)`, which is
  -- `x - J b ∧ ι_{J b} x - b ∧ ι_b x + ω ∧ ι_{J b} ι_b x`,
  -- using `[ι_u, L] = ε_{J u}` twice, `⟪J b, J b⟫ = 1` and `J (J b) = -b`.
  have h (i) : contractLeft (Q := (0 : QuadraticForm ℝ V)) (innerₗ V (J (b i)))
      (contractLeft (innerₗ V (b i)) (J.kahlerForm * x)) =
      x - ExteriorAlgebra.ι ℝ (b i) *
          contractLeft (Q := (0 : QuadraticForm ℝ V)) (innerₗ V (b i)) x -
        ExteriorAlgebra.ι ℝ (J (b i)) *
          contractLeft (Q := (0 : QuadraticForm ℝ V)) (innerₗ V (J (b i))) x +
        J.kahlerForm * contractLeft (Q := (0 : QuadraticForm ℝ V)) (innerₗ V (J (b i)))
          (contractLeft (innerₗ V (b i)) x) := by
    simp [contractLeft_kahlerForm_mul hJ, contractLeft_ι_mul, hJ]
    abel
  simp [h, Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.mul_sum, Nat.cast_smul_eq_nsmul]

/-- **The commutator of the dual Lefschetz and Lefschetz operators** in the exterior algebra: for
`x ∈ ⋀ᵏ V` and `Λₐ = (1/2) ∑ᵢ ι_{J bᵢ} ι_{bᵢ}`, `Λₐ (ω ∧ x) - ω ∧ Λₐ x = (n - k) x` with
`2n = dim V`. -/
private theorem commutator_of_mem {k : ℕ} {x : ExteriorAlgebra ℝ V} (hx : x ∈ ⋀[ℝ]^k V) :
    (2⁻¹ : ℝ) • ∑ i, contractLeft (Q := (0 : QuadraticForm ℝ V))
        (innerₗ V (J (stdOrthonormalBasis ℝ V i)))
        (contractLeft (innerₗ V (stdOrthonormalBasis ℝ V i)) (J.kahlerForm * x)) -
      J.kahlerForm * ((2⁻¹ : ℝ) • ∑ i, contractLeft (Q := (0 : QuadraticForm ℝ V))
        (innerₗ V (J (stdOrthonormalBasis ℝ V i)))
        (contractLeft (innerₗ V (stdOrthonormalBasis ℝ V i)) x)) =
      ((finrank ℝ V : ℝ) / 2 - k) • x := by
  set b := stdOrthonormalBasis ℝ V
  -- The number operators of `b` and of the orthonormal basis `J b` are both `k` on `⋀ᵏ V`.
  have hN (b' : OrthonormalBasis (Fin (finrank ℝ V)) ℝ V) : ∑ i, ExteriorAlgebra.ι ℝ (b' i) *
      contractLeft (Q := (0 : QuadraticForm ℝ V)) (innerₗ V (b' i)) x = (k : ℝ) • x := by
    simpa [b'.toBasis_coord_real, Nat.cast_smul_eq_nsmul] using
      b'.toBasis.sum_ι_mul_contractLeft_coord hx
  have hJe (v : V) : J.linearEquiv.isometryOfInner hJ v = J v :=
    congrFun (LinearEquiv.coe_isometryOfInner _ hJ) v
  have hJb := hN (b.map (J.linearEquiv.isometryOfInner hJ))
  simp only [OrthonormalBasis.map_apply, hJe] at hJb
  rw [sum_contractLeft_contractLeft_kahlerForm_mul hJ, hN b, hJb, mul_smul_comm]
  module

/-- **`[Λ, L] = (n - k) Id` on `⋀ᵏ V`** for `k ≥ 2`, where `dim V = 2n`: for `x ∈ ⋀ᵏ⁺² V`,
`Λ (L x) - L (Λ x) = (n - (k + 2)) x`. -/
theorem dualLefschetz_lefschetz_sub_lefschetz_dualLefschetz (k : ℕ) (x : ⋀[ℝ]^(k + 2) V) :
    J.dualLefschetz (k + 2) (J.lefschetz (k + 2) x) - J.lefschetz k (J.dualLefschetz k x) =
      ((finrank ℝ V : ℝ) / 2 - (k + 2)) • x := by
  ext
  simpa [coe_dualLefschetz_apply (b := stdOrthonormalBasis ℝ V)] using
    commutator_of_mem hJ x.property

/-- **`Λ L = (n - k) Id` on `⋀ᵏ V`** for `k < 2`, where `dim V = 2n`: in these degrees `Λ`
vanishes, so the commutator `[Λ, L]` is `Λ L`. -/
theorem dualLefschetz_lefschetz_of_lt_two {k : ℕ} (hk : k < 2) (x : ⋀[ℝ]^k V) :
    J.dualLefschetz k (J.lefschetz k x) = ((finrank ℝ V : ℝ) / 2 - k) • x := by
  -- The double contraction of an element of degree below two vanishes.
  have h (u w : V) : contractLeft (Q := (0 : QuadraticForm ℝ V)) (innerₗ V u)
      (contractLeft (innerₗ V w) (x : ExteriorAlgebra ℝ V)) = 0 := by
    obtain _ | _ | k := k
    · rw [ExteriorAlgebra.contractLeft_eq_zero_of_mem_exteriorPower_zero _ x.property, map_zero]
    · exact ExteriorAlgebra.contractLeft_eq_zero_of_mem_exteriorPower_zero _
        (ExteriorAlgebra.contractLeft_mem_exteriorPower _ x.property)
    · omega
  ext
  simpa [coe_dualLefschetz_apply (b := stdOrthonormalBasis ℝ V), h] using
    commutator_of_mem hJ x.property

/-- **`Λ ω = n`**, where `dim V = 2n`: the dual Lefschetz operator sends the Kähler two-vector to
`n` under `⋀⁰ V ≃ ℝ`. -/
theorem zeroEquiv_dualLefschetz_kahlerForm :
    zeroEquiv ℝ V (J.dualLefschetz 0 J.kahlerForm) = (finrank ℝ V : ℝ) / 2 := by
  rw [zeroEquiv_dualLefschetz_zero, inner_kahlerForm_self hJ]

end TauCeti.AlmostComplexStructure

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Basis.Bilinear
public import Mathlib.LinearAlgebra.ExteriorPower.BilinForm
public import TauCeti.LinearAlgebra.ExteriorAlgebra.AlgebraMapInv
public import TauCeti.LinearAlgebra.ExteriorAlgebra.Contraction
public import TauCeti.LinearAlgebra.ExteriorAlgebra.DegreeScaling
public import TauCeti.LinearAlgebra.ExteriorPower.Basis
public import TauCeti.LinearAlgebra.Matrix.SesquilinearForm

/-!
# The Gram and Hermitian metrics of an exterior algebra

Let `M` be a module over a commutative ring `R`, `σ : R →+* R` a ring endomorphism, and
`h : M →ₛₗ[σ] M →ₗ[R] R` a `σ`-sesquilinear form on `M`, `σ`-semilinear in its first argument and
`R`-linear in its second. This file constructs the basis-free exterior Gram form
`h.exteriorAlgebraGram` on `ExteriorAlgebra R M` and its degree-`p` restriction
`h.exteriorPowerGram p` on `⋀[R]^p M` (the `σ`-sesquilinear generalization of
`LinearMap.BilinForm.exteriorPower`), without assuming `M` is free or finitely generated, and
identifies them with the wedge-basis forms attached to any finite ordered basis of `M`.

The form `h.exteriorAlgebraGram` is characterized by two properties:

* on the vacuum, `h.exteriorAlgebraGram 1 t = ExteriorAlgebra.algebraMapInv t`, so in particular
  `h.exteriorAlgebraGram 1 1 = 1` and `1` is orthogonal to every positive exterior degree;
* **exterior multiplication by `x` is left-adjoint to contraction by `h(x, ·)`**:
  `h.exteriorAlgebraGram (x ∧ s) t = h.exteriorAlgebraGram s (h(x, ·) ⌋ t)`.

From these two identities follow the global properties of the exterior Gram pairing:

* **Orthogonality of distinct degrees**: `⋀[R]^p M` and `⋀[R]^q M` are orthogonal whenever `p ≠ q`,
  so pairing against a `p`-vector depends only on the degree-`p` homogeneous projection.
* **Gram-determinant formula**: in every degree `p` (including degree zero, where the empty
  determinant is `1`, and top degree),
  `h.exteriorAlgebraGram (x₀ ∧ ⋯ ∧ x_{p-1}) (y₀ ∧ ⋯ ∧ y_{p-1}) = det (h (xᵢ, yⱼ))`.
* **Reverse adjointness, functoriality, and `σ`-symmetry**: whenever `∀ y, σ (h x y) = h y x`,
  contraction by `h x` is also left-adjoint to exterior multiplication by `x`; linear maps
  preserving `h` preserve `h.exteriorAlgebraGram`; and when `σ` is involutive and `h` is
  `σ`-symmetric, so are `h.exteriorAlgebraGram` and `h.exteriorPowerGram p`.

These are the identities behind the creation and annihilation operators of a Fock space: in the
spinor module `⋀ W` of a complex structure, the Clifford action of a vector is a sum of a creation
and an annihilation operator, and their adjointness makes Clifford multiplication by a real vector
skew-Hermitian. Moreover, the degree scaling `T_r`, which multiplies the `p`-th exterior power by
`r ^ p`, has adjoint `T_{σ r}` for `h.exteriorAlgebraGram`, so pulling `h.exteriorAlgebraGram` back
along `T_r` multiplies it by `(σ r * r) ^ p` on `⋀[R]^p M`; this is how the metrics of differently
normalized Fock actions compare.

In degree two, `h.exteriorAlgebraGram (x₁ ∧ x₂) (y₁ ∧ y₂) = h x₁ y₁ * h x₂ y₂ - h x₁ y₂ * h x₂ y₁`.
Any tensor-square form `T` on `M ⊗[R] M` with `T (a ⊗ b) (c ⊗ d) = h a c * h b d` instead satisfies
`T (x₁ ⊗ x₂ - x₂ ⊗ x₁) (y₁ ⊗ y₂ - y₂ ⊗ y₁) = 2 * h.exteriorAlgebraGram (x₁ ∧ x₂) (y₁ ∧ y₂)`, so for
`h`-orthonormal `w₁, w₂` the wedge `w₁ ∧ w₂` has self-pairing `1` while the antisymmetrized tensor
`w₁ ⊗ w₂ - w₂ ⊗ w₁` has self-pairing `2`.

When `M` has a finite ordered basis `b`, the form `Matrix.toLinearMapₛₗ₂ σ b.ExteriorAlgebra
b.ExteriorAlgebra 1` making the increasing wedge basis orthonormal equals
`(Matrix.toLinearMapₛₗ₂ σ b b 1).exteriorAlgebraGram`. Thus `H = Matrix.toLinearMapₛₗ₂ σ
b.ExteriorAlgebra b.ExteriorAlgebra 1` depends only on `h = Matrix.toLinearMapₛₗ₂ σ b b 1`, makes
distinct degrees orthogonal, satisfies left creation–contraction adjointness and degree-scaling
adjointness unconditionally (and reverse contraction–creation adjointness when `σ` is involutive),
and evaluates on pure wedges as the Gram determinant of `h`.

## Main definitions

* `LinearMap.exteriorAlgebraGram`: the `σ`-sesquilinear exterior Gram form on
  `ExteriorAlgebra R M` induced by `h : M →ₛₗ[σ] M →ₗ[R] R`.
* `LinearMap.exteriorPowerGram`: its restriction to the `p`-th exterior power `⋀[R]^p M`,
  generalizing `LinearMap.BilinForm.exteriorPower`
  (`LinearMap.exteriorPowerGram_eq_bilinForm_exteriorPower`).

## Main results

* `LinearMap.exteriorAlgebraGram_ι_mul_left` and `LinearMap.exteriorAlgebraGram_ι_mul_right`:
  exterior multiplication by `x` is unconditionally left-adjoint to contraction by `h x`, and
  contraction by `h x` is left-adjoint to exterior multiplication by `x` whenever
  `∀ y, σ (h x y) = h y x`.
* `LinearMap.eq_exteriorAlgebraGram_iff` and `LinearMap.eq_exteriorAlgebraGram_of_ιMulti`:
  characterizations of `h.exteriorAlgebraGram` by vacuum pairing and left creation–contraction
  adjointness, and by degree orthogonality and Gram-determinant values on pure wedges.
* `LinearMap.exteriorAlgebraGram_eq_zero_of_mem_exteriorPower`: distinct exterior degrees are
  orthogonal.
* `LinearMap.exteriorAlgebraGram_ιMulti` and `LinearMap.exteriorPowerGram_ιMulti`: the
  Gram-determinant formula in every degree `p`.
* `LinearMap.apply_sub_tmul_swap_eq_two_mul_exteriorAlgebraGram`: the antisymmetrized tensor-square
  pairing is twice the degree-two exterior Gram determinant.
* `LinearMap.exteriorAlgebraGram_map_map`: linear maps preserving `h` preserve
  `h.exteriorAlgebraGram`.
* `LinearMap.exteriorAlgebraGram_degreeScaling_left` and
  `LinearMap.exteriorAlgebraGram_degreeScaling_degreeScaling_of_mem_exteriorPower`: degree-scaling
  adjointness `T_r` vs `T_{σ r}` and `(σ r * r) ^ p` rescaling on `⋀[R]^p M`.
* `LinearMap.IsSymm.exteriorAlgebraGram` and `LinearMap.IsSymm.exteriorPowerGram`: `σ`-symmetry
  passes to the exterior algebra and exterior powers for any involutive `σ`.
* `Module.Basis.toLinearMapₛₗ₂_exteriorAlgebra_eq_exteriorAlgebraGram` and
  `Module.Basis.toLinearMapₛₗ₂_exteriorPower_eq_exteriorPowerGram`: the wedge-basis forms on
  `b.ExteriorAlgebra` and `b.exteriorPower p` agree with the Gram forms of the basis form of `b`.

## References

* W. Greub, *Multilinear Algebra*, 2nd ed., Springer (1978), Chapter 5.
* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry* (1989), Chapter I §5.
* L. Nicolaescu, *Lectures on the Geometry of Manifolds* (online author edition, `Lectures.pdf`),
  §2.2.4.
-/

public section

open CliffordAlgebra Matrix TauCeti.ExteriorAlgebra
open scoped TensorProduct

namespace LinearMap

section ExteriorAlgebraGram

variable {R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N] {σ : R →+* R}

/-- Local type synonym equipping linear forms on `⋀ M` with the `σ`-twisted `R`-module structure,
so `CliffordAlgebra.foldr` can construct a `σ`-semilinear map out of `⋀ M` without competing
`Module` instances. -/
private def ExteriorGramDual (_σ : R →+* R) (M : Type*) [AddCommGroup M] [Module R M] : Type _ :=
  _root_.ExteriorAlgebra R M →ₗ[R] R

private instance : AddCommGroup (ExteriorGramDual σ M) :=
  inferInstanceAs (AddCommGroup (_root_.ExteriorAlgebra R M →ₗ[R] R))

private instance : Module R (ExteriorGramDual σ M) :=
  Module.compHom (_root_.ExteriorAlgebra R M →ₗ[R] R) σ

private def toExteriorGramDual (φ : _root_.ExteriorAlgebra R M →ₗ[R] R) : ExteriorGramDual σ M := φ

private def ofExteriorGramDual (φ : ExteriorGramDual σ M) : _root_.ExteriorAlgebra R M →ₗ[R] R := φ

private theorem ofExteriorGramDual_toExteriorGramDual (φ : _root_.ExteriorAlgebra R M →ₗ[R] R) :
    ofExteriorGramDual (σ := σ) (toExteriorGramDual (σ := σ) φ) = φ := rfl

private theorem ofExteriorGramDual_injective :
    Function.Injective (ofExteriorGramDual (σ := σ) (M := M)) := fun _ _ h ↦ h

private theorem ofExteriorGramDual_zero :
    ofExteriorGramDual (0 : ExteriorGramDual σ M) = 0 := rfl

private theorem ofExteriorGramDual_add (φ ψ : ExteriorGramDual σ M) :
    ofExteriorGramDual (φ + ψ) = ofExteriorGramDual φ + ofExteriorGramDual ψ := rfl

private theorem ofExteriorGramDual_smul (r : R) (φ : ExteriorGramDual σ M) :
    ofExteriorGramDual (r • φ) = σ r • ofExteriorGramDual φ := rfl

/-- One creation–contraction adjointness step in `ExteriorGramDual`: send `φ` to
`t ↦ φ (h x ⌋ t)`. -/
private def exteriorGramStep (h : M →ₛₗ[σ] M →ₗ[R] R) :
    M →ₗ[R] ExteriorGramDual σ M →ₗ[R] ExteriorGramDual σ M where
  toFun x :=
    { toFun φ := toExteriorGramDual
        ((ofExteriorGramDual φ).comp (contractLeft (Q := (0 : QuadraticForm R M)) (h x)))
      map_add' φ ψ := ofExteriorGramDual_injective (LinearMap.add_comp _ _ _)
      map_smul' r φ := ofExteriorGramDual_injective (LinearMap.smul_comp _ _ _) }
  map_add' x y := by
    ext φ : 1
    exact ofExteriorGramDual_injective (by ext t; simp [ofExteriorGramDual_add,
      ofExteriorGramDual_toExteriorGramDual])
  map_smul' r x := by
    ext φ : 1
    exact ofExteriorGramDual_injective (by ext t; simp [ofExteriorGramDual_smul,
      ofExteriorGramDual_toExteriorGramDual])

/-- Applying `exteriorGramStep h x` twice vanishes by `contractLeft_contractLeft`. -/
private theorem exteriorGramStep_self (h : M →ₛₗ[σ] M →ₗ[R] R) (x : M)
    (φ : ExteriorGramDual σ M) :
    exteriorGramStep h x (exteriorGramStep h x φ) = (0 : QuadraticForm R M) x • φ := by
  rw [_root_.zero_apply, zero_smul]
  exact ofExteriorGramDual_injective (by
    ext t
    simp [exteriorGramStep, ofExteriorGramDual_zero, ofExteriorGramDual_toExteriorGramDual,
      contractLeft_contractLeft])

/-- **The basis-free exterior Gram form** of a `σ`-sesquilinear form `h : M →ₛₗ[σ] M →ₗ[R] R`: the
unique `σ`-sesquilinear form on `ExteriorAlgebra R M` satisfying
`h.exteriorAlgebraGram 1 t = ExteriorAlgebra.algebraMapInv t` and
`h.exteriorAlgebraGram (ι R x * s) t = h.exteriorAlgebraGram s (h x ⌋ t)`. -/
def exteriorAlgebraGram (h : M →ₛₗ[σ] M →ₗ[R] R) :
    _root_.ExteriorAlgebra R M →ₛₗ[σ] _root_.ExteriorAlgebra R M →ₗ[R] R where
  toFun s :=
    ofExteriorGramDual (CliffordAlgebra.foldr (0 : QuadraticForm R M) (exteriorGramStep h)
      (exteriorGramStep_self h)
      (toExteriorGramDual _root_.ExteriorAlgebra.algebraMapInv.toLinearMap) s)
  map_add' s₁ s₂ := by
    rw [map_add, ofExteriorGramDual_add]
  map_smul' r s := by
    rw [LinearMap.map_smul, ofExteriorGramDual_smul]

/-- Pairing the vacuum on the left extracts the degree-zero scalar component. -/
@[simp]
theorem exteriorAlgebraGram_one_left (h : M →ₛₗ[σ] M →ₗ[R] R)
    (t : _root_.ExteriorAlgebra R M) :
    h.exteriorAlgebraGram 1 t = _root_.ExteriorAlgebra.algebraMapInv t := by
  simp [exteriorAlgebraGram, ofExteriorGramDual_toExteriorGramDual]

/-- Pairing a scalar on the left multiplies the constant term of the right argument by `σ r`. -/
@[simp]
theorem exteriorAlgebraGram_algebraMap_left (h : M →ₛₗ[σ] M →ₗ[R] R) (r : R)
    (t : _root_.ExteriorAlgebra R M) :
    h.exteriorAlgebraGram (algebraMap R _ r) t =
      σ r * _root_.ExteriorAlgebra.algebraMapInv t := by
  rw [Algebra.algebraMap_eq_smul_one, map_smulₛₗ, LinearMap.smul_apply,
    exteriorAlgebraGram_one_left, smul_eq_mul]

/-- **Exterior multiplication is adjoint to contraction**: for any `σ`-sesquilinear form `h` on
`M`, `h.exteriorAlgebraGram (x ∧ s) t = h.exteriorAlgebraGram s (h x ⌋ t)`. -/
theorem exteriorAlgebraGram_ι_mul_left (h : M →ₛₗ[σ] M →ₗ[R] R) (x : M)
    (s t : _root_.ExteriorAlgebra R M) :
    h.exteriorAlgebraGram (_root_.ExteriorAlgebra.ι R x * s) t =
      h.exteriorAlgebraGram s (contractLeft (Q := (0 : QuadraticForm R M)) (h x) t) := by
  simp [exteriorAlgebraGram, exteriorGramStep, ofExteriorGramDual_toExteriorGramDual]

/-- Pairing a single generator on the left takes the constant term of the contraction by `h x`. -/
theorem exteriorAlgebraGram_ι_left (h : M →ₛₗ[σ] M →ₗ[R] R) (x : M)
    (t : _root_.ExteriorAlgebra R M) :
    h.exteriorAlgebraGram (_root_.ExteriorAlgebra.ι R x) t =
      _root_.ExteriorAlgebra.algebraMapInv
        (contractLeft (Q := (0 : QuadraticForm R M)) (h x) t) := by
  simpa only [mul_one, exteriorAlgebraGram_one_left] using
    h.exteriorAlgebraGram_ι_mul_left x 1 t

/-- On degree-one generators, the exterior Gram form recovers the underlying form `h`. -/
@[simp]
theorem exteriorAlgebraGram_ι_ι (h : M →ₛₗ[σ] M →ₗ[R] R) (x y : M) :
    h.exteriorAlgebraGram (_root_.ExteriorAlgebra.ι R x) (_root_.ExteriorAlgebra.ι R y) =
      h x y := by
  rw [exteriorAlgebraGram_ι_left, contractLeft_ι, AlgHom.commutes, Algebra.algebraMap_self_apply]

/-- Pairing the vacuum on the right applies `σ` to the constant term of the left argument. -/
@[simp]
theorem exteriorAlgebraGram_one_right (h : M →ₛₗ[σ] M →ₗ[R] R)
    (s : _root_.ExteriorAlgebra R M) :
    h.exteriorAlgebraGram s 1 = σ (_root_.ExteriorAlgebra.algebraMapInv s) := by
  induction s using CliffordAlgebra.left_induction with
  | algebraMap r => simp
  | add x y hx hy => simp [hx, hy]
  | ι_mul s x _ =>
    change h.exteriorAlgebraGram (_root_.ExteriorAlgebra.ι R x * s) 1 = _
    simp [exteriorAlgebraGram_ι_mul_left]

/-- Pairing a scalar on the right multiplies `σ` of the constant term of `s` by `r`. -/
@[simp]
theorem exteriorAlgebraGram_algebraMap_right (h : M →ₛₗ[σ] M →ₗ[R] R)
    (s : _root_.ExteriorAlgebra R M) (r : R) :
    h.exteriorAlgebraGram s (algebraMap R _ r) =
      σ (_root_.ExteriorAlgebra.algebraMapInv s) * r := by
  rw [Algebra.algebraMap_eq_smul_one, map_smul, exteriorAlgebraGram_one_right, smul_eq_mul,
    mul_comm]

/-- **Universal characterization of the exterior Gram form**: a `σ`-sesquilinear form `H` on `⋀ M`
is `h.exteriorAlgebraGram` if and only if `H 1 1 = 1`, `H 1 (y ∧ t) = 0` for all `y` and `t`, and
exterior multiplication by `x` is left-adjoint to contraction by `h x`. -/
theorem eq_exteriorAlgebraGram_iff (h : M →ₛₗ[σ] M →ₗ[R] R)
    (H : _root_.ExteriorAlgebra R M →ₛₗ[σ] _root_.ExteriorAlgebra R M →ₗ[R] R) :
    H = h.exteriorAlgebraGram ↔
      H 1 1 = 1 ∧ (∀ y t, H 1 (_root_.ExteriorAlgebra.ι R y * t) = 0) ∧
        ∀ x s t, H (_root_.ExteriorAlgebra.ι R x * s) t =
          H s (contractLeft (Q := (0 : QuadraticForm R M)) (h x) t) := by
  refine ⟨?_, fun ⟨hone, hzero, hadj⟩ ↦ ?_⟩
  · rintro rfl
    exact ⟨by simp, fun y t ↦ by simp, h.exteriorAlgebraGram_ι_mul_left⟩
  · have hvac (t : _root_.ExteriorAlgebra R M) : H 1 t = h.exteriorAlgebraGram 1 t := by
      induction t using CliffordAlgebra.left_induction with
      | algebraMap r =>
        rw [Algebra.algebraMap_eq_smul_one, map_smul, map_smul, hone,
          exteriorAlgebraGram_one_left, map_one]
      | add x y hx hy => rw [map_add, map_add, hx, hy]
      | ι_mul t y _ =>
        change H 1 (_root_.ExteriorAlgebra.ι R y * t) =
          h.exteriorAlgebraGram 1 (_root_.ExteriorAlgebra.ι R y * t)
        simp [hzero]
    refine LinearMap.ext fun s ↦ ?_
    induction s using CliffordAlgebra.left_induction with
    | algebraMap r =>
      refine LinearMap.ext fun t ↦ ?_
      rw [Algebra.algebraMap_eq_smul_one, map_smulₛₗ, map_smulₛₗ, LinearMap.smul_apply,
        LinearMap.smul_apply, hvac]
    | add x y hx hy => rw [map_add, map_add, hx, hy]
    | ι_mul s x hs =>
      refine LinearMap.ext fun t ↦ ?_
      change H (_root_.ExteriorAlgebra.ι R x * s) t =
        h.exteriorAlgebraGram (_root_.ExteriorAlgebra.ι R x * s) t
      rw [hadj, exteriorAlgebraGram_ι_mul_left, hs]

/-! ### Degree orthogonality and the Gram-determinant formula -/

/-- Pure wedges of distinct degrees are orthogonal for `h.exteriorAlgebraGram`. -/
theorem exteriorAlgebraGram_ιMulti_eq_zero_of_ne (h : M →ₛₗ[σ] M →ₗ[R] R) {p q : ℕ} (hpq : p ≠ q)
    (x : Fin p → M) (y : Fin q → M) :
    h.exteriorAlgebraGram (_root_.ExteriorAlgebra.ιMulti R p x)
        (_root_.ExteriorAlgebra.ιMulti R q y) = 0 := by
  induction p generalizing q with
  | zero =>
    rcases q with _ | q
    · exact absurd rfl hpq
    · simp [_root_.ExteriorAlgebra.ιMulti_zero_apply, _root_.ExteriorAlgebra.ιMulti_succ_apply]
  | succ p ih =>
    rcases q with _ | q
    · simp [_root_.ExteriorAlgebra.ιMulti_zero_apply, _root_.ExteriorAlgebra.ιMulti_succ_apply]
    · have hpq' : p ≠ q := fun h' ↦ hpq (congrArg Nat.succ h')
      rw [_root_.ExteriorAlgebra.ιMulti_succ_apply, exteriorAlgebraGram_ι_mul_left,
        TauCeti.ExteriorAlgebra.contractLeft_ιMulti, map_sum]
      exact Finset.sum_eq_zero fun j _ ↦ by rw [map_smul, ih hpq', smul_zero]

/-- **Distinct exterior degrees are orthogonal** for `h.exteriorAlgebraGram` on all of `⋀ M`. -/
theorem exteriorAlgebraGram_eq_zero_of_mem_exteriorPower (h : M →ₛₗ[σ] M →ₗ[R] R) {p q : ℕ}
    (hpq : p ≠ q) {s t : _root_.ExteriorAlgebra R M} (hs : s ∈ ⋀[R]^p M) (ht : t ∈ ⋀[R]^q M) :
    h.exteriorAlgebraGram s t = 0 := by
  rw [← Submodule.ext_iff.mp (_root_.ExteriorAlgebra.ιMulti_span_fixedDegree R p)] at hs
  rw [← Submodule.ext_iff.mp (_root_.ExteriorAlgebra.ιMulti_span_fixedDegree R q)] at ht
  induction hs using Submodule.span_induction with
  | mem s hs =>
    obtain ⟨x, rfl⟩ := hs
    induction ht using Submodule.span_induction with
    | mem t ht =>
      obtain ⟨y, rfl⟩ := ht
      exact h.exteriorAlgebraGram_ιMulti_eq_zero_of_ne hpq x y
    | zero => simp
    | add t₁ t₂ _ _ ht₁ ht₂ => rw [map_add, ht₁, ht₂, add_zero]
    | smul r t _ ht => rw [map_smul, ht, smul_zero]
  | zero => simp
  | add s₁ s₂ _ _ hs₁ hs₂ => rw [map_add, LinearMap.add_apply, hs₁, hs₂, add_zero]
  | smul r s _ hs => rw [map_smulₛₗ, LinearMap.smul_apply, hs, smul_zero]

/-- Pairing two finite homogeneous decompositions discards every cross-degree term. -/
theorem exteriorAlgebraGram_sum_of_mem_exteriorPower (h : M →ₛₗ[σ] M →ₗ[R] R)
    (I : Finset ℕ) (s t : ℕ → _root_.ExteriorAlgebra R M)
    (hs : ∀ p ∈ I, s p ∈ ⋀[R]^p M) (ht : ∀ q ∈ I, t q ∈ ⋀[R]^q M) :
    h.exteriorAlgebraGram (∑ p ∈ I, s p) (∑ q ∈ I, t q) =
      ∑ p ∈ I, h.exteriorAlgebraGram (s p) (t p) := by
  rw [map_sum h.exteriorAlgebraGram, LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun p hp ↦ ?_
  rw [map_sum]
  refine Finset.sum_eq_single p (fun q hq hqp ↦ ?_) (fun hp' ↦ absurd hp hp')
  exact h.exteriorAlgebraGram_eq_zero_of_mem_exteriorPower hqp.symm (hs p hp) (ht q hq)

/-- Pairing a `p`-vector on the left against an arbitrary multivector depends only on the
degree-`p` homogeneous projection of the right argument. -/
theorem exteriorAlgebraGram_proj_right (h : M →ₛₗ[σ] M →ₗ[R] R) {p : ℕ}
    {s : _root_.ExteriorAlgebra R M} (hs : s ∈ ⋀[R]^p M) (t : _root_.ExteriorAlgebra R M) :
    h.exteriorAlgebraGram s (GradedRing.proj (fun q ↦ ⋀[R]^q M) p t) =
      h.exteriorAlgebraGram s t := by
  induction t using DirectSum.Decomposition.inductionOn fun q ↦ ⋀[R]^q M with
  | zero => simp
  | homogeneous x =>
    rename_i q
    by_cases hpq : p = q
    · subst hpq
      rw [GradedRing.proj_apply,
        DirectSum.decompose_of_mem_same (fun q ↦ ⋀[R]^q M) x.property]
    · rw [GradedRing.proj_apply,
        DirectSum.decompose_of_mem_ne (fun q ↦ ⋀[R]^q M) x.property (Ne.symm hpq),
        map_zero, h.exteriorAlgebraGram_eq_zero_of_mem_exteriorPower hpq hs x.property]
  | add t₁ t₂ ht₁ ht₂ => rw [map_add, map_add, map_add, ht₁, ht₂]

/-- Pairing an arbitrary multivector on the left against a `p`-vector on the right depends only on
the degree-`p` homogeneous projection of the left argument. -/
theorem exteriorAlgebraGram_proj_left (h : M →ₛₗ[σ] M →ₗ[R] R) {p : ℕ}
    (s : _root_.ExteriorAlgebra R M) {t : _root_.ExteriorAlgebra R M} (ht : t ∈ ⋀[R]^p M) :
    h.exteriorAlgebraGram (GradedRing.proj (fun q ↦ ⋀[R]^q M) p s) t =
      h.exteriorAlgebraGram s t := by
  induction s using DirectSum.Decomposition.inductionOn fun q ↦ ⋀[R]^q M with
  | zero => simp
  | homogeneous x =>
    rename_i q
    by_cases hpq : p = q
    · subst hpq
      rw [GradedRing.proj_apply,
        DirectSum.decompose_of_mem_same (fun q ↦ ⋀[R]^q M) x.property]
    · rw [GradedRing.proj_apply,
        DirectSum.decompose_of_mem_ne (fun q ↦ ⋀[R]^q M) x.property (Ne.symm hpq),
        map_zero, LinearMap.zero_apply,
        h.exteriorAlgebraGram_eq_zero_of_mem_exteriorPower (Ne.symm hpq) x.property ht]
  | add s₁ s₂ hs₁ hs₂ =>
    rw [map_add, map_add, LinearMap.add_apply, map_add, LinearMap.add_apply, hs₁, hs₂]

/-- **The Gram-determinant formula** in every degree `p` (including degree zero, where the empty
determinant is `1`, and top degree):
`h.exteriorAlgebraGram (x₀ ∧ ⋯ ∧ x_{p-1}) (y₀ ∧ ⋯ ∧ y_{p-1}) = det (h (xᵢ, yⱼ))`. -/
@[simp↓]
theorem exteriorAlgebraGram_ιMulti (h : M →ₛₗ[σ] M →ₗ[R] R) {p : ℕ} (x y : Fin p → M) :
    h.exteriorAlgebraGram (_root_.ExteriorAlgebra.ιMulti R p x)
        (_root_.ExteriorAlgebra.ιMulti R p y) =
      (Matrix.of fun i j ↦ h (x i) (y j)).det := by
  induction p with
  | zero => simp [_root_.ExteriorAlgebra.ιMulti_zero_apply]
  | succ p ih =>
    rw [_root_.ExteriorAlgebra.ιMulti_succ_apply, exteriorAlgebraGram_ι_mul_left,
      TauCeti.ExteriorAlgebra.contractLeft_ιMulti, map_sum,
      Matrix.det_succ_row_zero (Matrix.of fun i j ↦ h (x i) (y j))]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [map_smul, ih, smul_eq_mul]
    simp only [Matrix.of_apply]
    refine congrArg (_ * ·) (congrArg Matrix.det (Matrix.ext fun i k ↦ ?_))
    simp [Matrix.vecTail, Fin.removeNth_apply]

/-- **Characterization of the exterior Gram form by degree orthogonality and Gram determinants**:
`h.exteriorAlgebraGram` is the unique `σ`-sesquilinear form on `⋀ M` for which distinct exterior
powers are orthogonal and pure wedges pair by the `p × p` Gram determinant of `h`. -/
theorem eq_exteriorAlgebraGram_of_ιMulti (h : M →ₛₗ[σ] M →ₗ[R] R)
    (B : _root_.ExteriorAlgebra R M →ₛₗ[σ] _root_.ExteriorAlgebra R M →ₗ[R] R)
    (horth : ∀ {p q : ℕ}, p ≠ q → ∀ {s : _root_.ExteriorAlgebra R M}, s ∈ ⋀[R]^p M →
      ∀ {t : _root_.ExteriorAlgebra R M}, t ∈ ⋀[R]^q M → B s t = 0)
    (hdet : ∀ (p : ℕ) (x y : Fin p → M),
      B (_root_.ExteriorAlgebra.ιMulti R p x) (_root_.ExteriorAlgebra.ιMulti R p y) =
        (Matrix.of fun i j ↦ h (x i) (y j)).det) :
    B = h.exteriorAlgebraGram := by
  refine LinearMap.ext fun s ↦ ?_
  have hs : s ∈ (⊤ : Submodule R (_root_.ExteriorAlgebra R M)) := trivial
  rw [← _root_.ExteriorAlgebra.ιMulti_span] at hs
  induction hs using Submodule.span_induction with
  | mem s hs =>
    obtain ⟨⟨p, x⟩, rfl⟩ := hs
    refine LinearMap.ext fun t ↦ ?_
    have ht : t ∈ (⊤ : Submodule R (_root_.ExteriorAlgebra R M)) := trivial
    rw [← _root_.ExteriorAlgebra.ιMulti_span] at ht
    induction ht using Submodule.span_induction with
    | mem t ht =>
      obtain ⟨⟨q, y⟩, rfl⟩ := ht
      dsimp only
      by_cases hpq : p = q
      · subst hpq
        rw [hdet, exteriorAlgebraGram_ιMulti]
      · have hx : _root_.ExteriorAlgebra.ιMulti R p x ∈ ⋀[R]^p M := by
          rw [← exteriorPower.ιMulti_apply_coe]; exact SetLike.coe_mem _
        have hy : _root_.ExteriorAlgebra.ιMulti R q y ∈ ⋀[R]^q M := by
          rw [← exteriorPower.ιMulti_apply_coe]; exact SetLike.coe_mem _
        rw [horth hpq hx hy, h.exteriorAlgebraGram_ιMulti_eq_zero_of_ne hpq x y]
    | zero => simp
    | add t₁ t₂ _ _ ht₁ ht₂ => rw [map_add, map_add, ht₁, ht₂]
    | smul r t _ ht => rw [map_smul, map_smul, ht]
  | zero => simp
  | add s₁ s₂ _ _ hs₁ hs₂ => rw [map_add, map_add, hs₁, hs₂]
  | smul r s _ hs => rw [map_smulₛₗ, map_smulₛₗ, hs]

/-- Explicit `2 × 2` Gram-determinant formula in exterior degree two. -/
theorem exteriorAlgebraGram_ι_mul_ι (h : M →ₛₗ[σ] M →ₗ[R] R) (x₁ x₂ y₁ y₂ : M) :
    h.exteriorAlgebraGram (_root_.ExteriorAlgebra.ι R x₁ * _root_.ExteriorAlgebra.ι R x₂)
        (_root_.ExteriorAlgebra.ι R y₁ * _root_.ExteriorAlgebra.ι R y₂) =
      h x₁ y₁ * h x₂ y₂ - h x₁ y₂ * h x₂ y₁ := by
  have h₂ (u₁ u₂ : M) : _root_.ExteriorAlgebra.ι R u₁ * _root_.ExteriorAlgebra.ι R u₂ =
      _root_.ExteriorAlgebra.ιMulti R 2 ![u₁, u₂] := by
    simp [_root_.ExteriorAlgebra.ιMulti_succ_apply, _root_.ExteriorAlgebra.ιMulti_zero_apply]
  rw [h₂ x₁ x₂, h₂ y₁ y₂, exteriorAlgebraGram_ιMulti, Matrix.det_fin_two]
  simp

/-- **Degree-two comparison with the antisymmetrized tensor square**: any `σ`-sesquilinear form `T`
on `M ⊗[R] M` factoring on pure tensors as `T (a ⊗ b) (c ⊗ d) = h a c * h b d` pairs the
antisymmetrized tensors `x₁ ⊗ x₂ - x₂ ⊗ x₁` and `y₁ ⊗ y₂ - y₂ ⊗ y₁` as **twice** the degree-two
exterior Gram determinant. -/
theorem apply_sub_tmul_swap_eq_two_mul_exteriorAlgebraGram (h : M →ₛₗ[σ] M →ₗ[R] R)
    {T : M ⊗[R] M →ₛₗ[σ] M ⊗[R] M →ₗ[R] R}
    (hT : ∀ a b c d, T (a ⊗ₜ b) (c ⊗ₜ d) = h a c * h b d) (x₁ x₂ y₁ y₂ : M) :
    T (x₁ ⊗ₜ x₂ - x₂ ⊗ₜ x₁) (y₁ ⊗ₜ y₂ - y₂ ⊗ₜ y₁) =
      2 * h.exteriorAlgebraGram (_root_.ExteriorAlgebra.ι R x₁ * _root_.ExteriorAlgebra.ι R x₂)
        (_root_.ExteriorAlgebra.ι R y₁ * _root_.ExteriorAlgebra.ι R y₂) := by
  simp only [map_sub, LinearMap.sub_apply, hT, exteriorAlgebraGram_ι_mul_ι]
  ring

/-- For an `h`-orthonormal pair `w₁, w₂`, the wedge `w₁ ∧ w₂` has Gram self-pairing `1` (see
`LinearMap.apply_sub_tmul_swap_eq_two_mul_exteriorAlgebraGram` for the factor-of-`2` comparison
with `w₁ ⊗ w₂ - w₂ ⊗ w₁`). -/
theorem exteriorAlgebraGram_ι_mul_ι_self_of_orthonormal (h : M →ₛₗ[σ] M →ₗ[R] R) {w₁ w₂ : M}
    (hw₁ : h w₁ w₁ = 1) (hw₂ : h w₂ w₂ = 1) (h₁₂ : h w₁ w₂ = 0) :
    h.exteriorAlgebraGram (_root_.ExteriorAlgebra.ι R w₁ * _root_.ExteriorAlgebra.ι R w₂)
        (_root_.ExteriorAlgebra.ι R w₁ * _root_.ExteriorAlgebra.ι R w₂) = 1 := by
  rw [exteriorAlgebraGram_ι_mul_ι, hw₁, hw₂, h₁₂, zero_mul, mul_one, sub_zero]

/-- **Top-degree Gram determinant against a rank-`n` basis**: for `b : Basis (Fin n) R M` and two
`n`-tuples `x, y : Fin n → M`, the exterior Gram pairing of their wedges factors as
`σ (b.det x) * b.det y` times the Gram determinant of the basis `b`. -/
theorem exteriorAlgebraGram_ιMulti_eq_map_det_mul_det_mul_det (h : M →ₛₗ[σ] M →ₗ[R] R) {n : ℕ}
    (b : Module.Basis (Fin n) R M) (x y : Fin n → M) :
    h.exteriorAlgebraGram (_root_.ExteriorAlgebra.ιMulti R n x)
        (_root_.ExteriorAlgebra.ιMulti R n y) =
      σ (b.det x) * b.det y * (Matrix.of fun i j ↦ h (b i) (b j)).det := by
  have hx := congrArg (Subtype.val : ⋀[R]^n M → _root_.ExteriorAlgebra R M)
    (b.exteriorPower_ιMulti_eq_det_smul x)
  have hy := congrArg (Subtype.val : ⋀[R]^n M → _root_.ExteriorAlgebra R M)
    (b.exteriorPower_ιMulti_eq_det_smul y)
  simp only [Submodule.coe_smul_of_tower, exteriorPower.ιMulti_apply_coe] at hx hy
  simp only [hx, hy, map_smulₛₗ, LinearMap.smul_apply, RingHom.id_apply,
    exteriorAlgebraGram_ιMulti, smul_eq_mul]
  ring

/-! ### Symmetry, functoriality, and degree scaling -/

/-- For an involutive `σ`, if `h` is `σ`-symmetric (`σ (h x y) = h y x`), then so is
`h.exteriorAlgebraGram`: `σ (h.exteriorAlgebraGram s t) = h.exteriorAlgebraGram t s`. -/
theorem map_exteriorAlgebraGram_swap (h : M →ₛₗ[σ] M →ₗ[R] R) (hσ : Function.Involutive σ)
    (hh : ∀ x y, σ (h x y) = h y x) (s t : _root_.ExteriorAlgebra R M) :
    σ (h.exteriorAlgebraGram s t) = h.exteriorAlgebraGram t s := by
  have hs : s ∈ (⊤ : Submodule R (_root_.ExteriorAlgebra R M)) := trivial
  rw [← _root_.ExteriorAlgebra.ιMulti_span] at hs
  induction hs using Submodule.span_induction with
  | mem s hs =>
    obtain ⟨⟨p, x⟩, rfl⟩ := hs
    dsimp only
    have ht : t ∈ (⊤ : Submodule R (_root_.ExteriorAlgebra R M)) := trivial
    rw [← _root_.ExteriorAlgebra.ιMulti_span] at ht
    induction ht using Submodule.span_induction with
    | mem t ht =>
      obtain ⟨⟨q, y⟩, rfl⟩ := ht
      dsimp only
      by_cases hpq : p = q
      · subst hpq
        rw [exteriorAlgebraGram_ιMulti, exteriorAlgebraGram_ιMulti, σ.map_det,
          ← Matrix.det_transpose (Matrix.of fun i j ↦ h (y i) (x j))]
        congr 1
        ext i j
        simp [RingHom.mapMatrix_apply, hh (x i) (y j)]
      · rw [exteriorAlgebraGram_ιMulti_eq_zero_of_ne h hpq,
          exteriorAlgebraGram_ιMulti_eq_zero_of_ne h (Ne.symm hpq), map_zero]
    | zero => simp
    | add t₁ t₂ _ _ ht₁ ht₂ => rw [map_add, map_add, map_add, LinearMap.add_apply, ht₁, ht₂]
    | smul r t _ ht =>
      rw [map_smul, smul_eq_mul, map_mul, map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, ht]
  | zero => simp
  | add s₁ s₂ _ _ hs₁ hs₂ =>
    rw [map_add, LinearMap.add_apply, map_add, map_add, hs₁, hs₂]
  | smul r s _ hs =>
    rw [map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, map_mul, hσ r, map_smul, smul_eq_mul, hs]

/-- **The exterior Gram form of a `σ`-symmetric sesquilinear form is `σ`-symmetric** for any
involutive ring endomorphism `σ`. -/
theorem IsSymm.exteriorAlgebraGram [RingHomInvPair σ σ] {h : M →ₛₗ[σ] M →ₗ[R] R}
    (hh : h.IsSymm) : h.exteriorAlgebraGram.IsSymm :=
  isSymm_def.mpr <|
    h.map_exteriorAlgebraGram_swap (fun _ ↦ RingHomInvPair.comp_apply_eq₂) fun x y ↦ hh.eq x y

/-- **Contraction is adjoint to exterior multiplication on the right** whenever
`∀ y, σ (h x y) = h y x`: `h.exteriorAlgebraGram s (x ∧ t) = h.exteriorAlgebraGram (h x ⌋ s) t`. -/
theorem exteriorAlgebraGram_ι_mul_right (h : M →ₛₗ[σ] M →ₗ[R] R) {x : M}
    (hh : ∀ y, σ (h x y) = h y x) (s t : _root_.ExteriorAlgebra R M) :
    h.exteriorAlgebraGram s (_root_.ExteriorAlgebra.ι R x * t) =
      h.exteriorAlgebraGram (contractLeft (Q := (0 : QuadraticForm R M)) (h x) s) t := by
  induction s using CliffordAlgebra.left_induction generalizing t with
  | algebraMap r =>
    simp [exteriorAlgebraGram_algebraMap_left, contractLeft_algebraMap]
  | add s₁ s₂ hs₁ hs₂ =>
    simp only [map_add, LinearMap.add_apply, hs₁, hs₂]
  | ι_mul s y hs =>
    change h.exteriorAlgebraGram (_root_.ExteriorAlgebra.ι R y * s)
        (_root_.ExteriorAlgebra.ι R x * t) =
      h.exteriorAlgebraGram
        (contractLeft (Q := (0 : QuadraticForm R M)) (h x)
          (_root_.ExteriorAlgebra.ι R y * s)) t
    rw [exteriorAlgebraGram_ι_mul_left, contractLeft_ι_mul, map_sub, map_smul, hs,
      contractLeft_ι_mul, map_sub, map_smulₛₗ, LinearMap.sub_apply, LinearMap.smul_apply,
      exteriorAlgebraGram_ι_mul_left, smul_eq_mul, smul_eq_mul, hh y]

/-- **Linear maps preserving `h` preserve the exterior Gram form** on all of `⋀ M`. -/
theorem exteriorAlgebraGram_map_map (h : M →ₛₗ[σ] M →ₗ[R] R) (h' : N →ₛₗ[σ] N →ₗ[R] R)
    (f : M →ₗ[R] N) (hf : ∀ x y, h' (f x) (f y) = h x y) (s t : _root_.ExteriorAlgebra R M) :
    h'.exteriorAlgebraGram (_root_.ExteriorAlgebra.map f s) (_root_.ExteriorAlgebra.map f t) =
      h.exteriorAlgebraGram s t := by
  induction s using CliffordAlgebra.left_induction generalizing t with
  | algebraMap r =>
    simp [exteriorAlgebraGram_algebraMap_left]
  | add s₁ s₂ hs₁ hs₂ =>
    simp only [map_add, LinearMap.add_apply, hs₁, hs₂]
  | ι_mul s x hs =>
    have hfx : h' (f x) ∘ₗ f = h x := LinearMap.ext (hf x)
    change h'.exteriorAlgebraGram
        (_root_.ExteriorAlgebra.map f (_root_.ExteriorAlgebra.ι R x * s))
        (_root_.ExteriorAlgebra.map f t) =
      h.exteriorAlgebraGram (_root_.ExteriorAlgebra.ι R x * s) t
    rw [map_mul, _root_.ExteriorAlgebra.map_apply_ι, exteriorAlgebraGram_ι_mul_left,
      _root_.ExteriorAlgebra.contractLeft_map, hfx, hs, exteriorAlgebraGram_ι_mul_left]

/-- **The adjoint of the degree scaling by `r` is the degree scaling by `σ r`**:
`h.exteriorAlgebraGram (T_r s) t = h.exteriorAlgebraGram s (T_{σ r} t)`. -/
theorem exteriorAlgebraGram_degreeScaling_left (h : M →ₛₗ[σ] M →ₗ[R] R) (r : Rˣ)
    (s t : _root_.ExteriorAlgebra R M) :
    h.exteriorAlgebraGram (degreeScaling r s) t =
      h.exteriorAlgebraGram s (degreeScaling (Units.map σ.toMonoidHom r) t) := by
  induction s using CliffordAlgebra.left_induction generalizing t with
  | algebraMap c =>
    rw [AlgEquiv.commutes, exteriorAlgebraGram_algebraMap_left,
      exteriorAlgebraGram_algebraMap_left, _root_.ExteriorAlgebra.degreeScaling_apply,
      _root_.ExteriorAlgebra.algebraMapInv_map]
  | add s₁ s₂ hs₁ hs₂ =>
    simp only [map_add, LinearMap.add_apply, hs₁, hs₂]
  | ι_mul s x hs =>
    change h.exteriorAlgebraGram (degreeScaling r (_root_.ExteriorAlgebra.ι R x * s)) t = _
    rw [map_mul, degreeScaling_ι, smul_mul_assoc, map_smulₛₗ, LinearMap.smul_apply,
      exteriorAlgebraGram_ι_mul_left, hs, exteriorAlgebraGram_ι_mul_left,
      _root_.ExteriorAlgebra.degreeScaling_contractLeft]
    have hr : σ r * ↑(Units.map σ.toMonoidHom r)⁻¹ = 1 :=
      Units.mul_inv (Units.map σ.toMonoidHom r)
    rw [map_smul, smul_eq_mul, smul_eq_mul, ← mul_assoc, hr, one_mul]

/-- **The degree scaling rescales `h.exteriorAlgebraGram` by `(σ r * r) ^ p` on `⋀[R]^p M`.** -/
theorem exteriorAlgebraGram_degreeScaling_degreeScaling_of_mem_exteriorPower
    (h : M →ₛₗ[σ] M →ₗ[R] R) (r : Rˣ) {p : ℕ} {s : _root_.ExteriorAlgebra R M}
    (hs : s ∈ ⋀[R]^p M) (t : _root_.ExteriorAlgebra R M) :
    h.exteriorAlgebraGram (degreeScaling r s) (degreeScaling r t) =
      (σ r * r) ^ p * h.exteriorAlgebraGram s t := by
  have hs' : degreeScaling r s ∈ ⋀[R]^p M := by
    rw [degreeScaling_of_mem_exteriorPower r hs]
    exact Submodule.smul_mem _ _ hs
  induction t using DirectSum.Decomposition.inductionOn fun q ↦ ⋀[R]^q M with
  | zero => simp
  | homogeneous x =>
    rename_i q
    by_cases hpq : p = q
    · subst hpq
      rw [degreeScaling_of_mem_exteriorPower r hs,
        degreeScaling_of_mem_exteriorPower r x.property,
        map_smul, map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, smul_eq_mul, map_pow]
      ring
    · have hx' : degreeScaling r (x : _root_.ExteriorAlgebra R M) ∈ ⋀[R]^q M := by
        rw [degreeScaling_of_mem_exteriorPower r x.property]
        exact Submodule.smul_mem _ _ x.property
      rw [h.exteriorAlgebraGram_eq_zero_of_mem_exteriorPower hpq hs' hx',
        h.exteriorAlgebraGram_eq_zero_of_mem_exteriorPower hpq hs x.property, mul_zero]
  | add t₁ t₂ ht₁ ht₂ => rw [map_add, map_add, map_add, ht₁, ht₂, mul_add]

end ExteriorAlgebraGram

section ExteriorPowerGram

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] {σ : R →+* R}

/-- **The basis-free Gram form on the `p`-th exterior power `⋀[R]^p M`** induced by a
`σ`-sesquilinear form `h : M →ₛₗ[σ] M →ₗ[R] R`: the restriction of `h.exteriorAlgebraGram` to the
homogeneous submodule `⋀[R]^p M`. For `σ = RingHom.id R`, this is the `σ`-twisted generalization of
`LinearMap.BilinForm.exteriorPower` (`LinearMap.exteriorPowerGram_eq_bilinForm_exteriorPower`). -/
def exteriorPowerGram (h : M →ₛₗ[σ] M →ₗ[R] R) (p : ℕ) :
    (⋀[R]^p M) →ₛₗ[σ] (⋀[R]^p M) →ₗ[R] R :=
  h.exteriorAlgebraGram.domRestrict₁₂ (⋀[R]^p M) (⋀[R]^p M)

/-- `h.exteriorPowerGram p` evaluates as `h.exteriorAlgebraGram` on the underlying multivectors. -/
theorem exteriorPowerGram_apply (h : M →ₛₗ[σ] M →ₗ[R] R) (p : ℕ) (s t : ⋀[R]^p M) :
    h.exteriorPowerGram p s t =
      h.exteriorAlgebraGram (s : _root_.ExteriorAlgebra R M) (t : _root_.ExteriorAlgebra R M) :=
  h.exteriorAlgebraGram.domRestrict₁₂_apply (⋀[R]^p M) (⋀[R]^p M) s t

/-- **The Gram-determinant formula on `⋀[R]^p M`**:
`h.exteriorPowerGram p (x₀ ∧ ⋯ ∧ x_{p-1}) (y₀ ∧ ⋯ ∧ y_{p-1}) = det (h (xᵢ, yⱼ))`. -/
@[simp]
theorem exteriorPowerGram_ιMulti (h : M →ₛₗ[σ] M →ₗ[R] R) (p : ℕ) (x y : Fin p → M) :
    h.exteriorPowerGram p (exteriorPower.ιMulti R p x) (exteriorPower.ιMulti R p y) =
      (Matrix.of fun i j ↦ h (x i) (y j)).det := by
  rw [exteriorPowerGram_apply, exteriorPower.ιMulti_apply_coe, exteriorPower.ιMulti_apply_coe,
    exteriorAlgebraGram_ιMulti]

/-- `h.exteriorPowerGram p` is uniquely determined by its Gram-determinant values on pure wedges. -/
theorem eq_exteriorPowerGram_iff (h : M →ₛₗ[σ] M →ₗ[R] R) (p : ℕ)
    (B : (⋀[R]^p M) →ₛₗ[σ] (⋀[R]^p M) →ₗ[R] R) :
    B = h.exteriorPowerGram p ↔
      ∀ x y : Fin p → M, B (exteriorPower.ιMulti R p x) (exteriorPower.ιMulti R p y) =
        (Matrix.of fun i j ↦ h (x i) (y j)).det := by
  refine ⟨fun hB ↦ hB ▸ h.exteriorPowerGram_ιMulti p, fun hB ↦ ?_⟩
  refine LinearMap.ext_on (exteriorPower.ιMulti_span R p M) ?_
  rintro _ ⟨x, rfl⟩
  refine exteriorPower.linearMap_ext (AlternatingMap.ext fun y ↦ ?_)
  simpa using hB x y

/-- For an `R`-bilinear form (`σ = RingHom.id R`), `LinearMap.exteriorPowerGram` agrees with
`LinearMap.BilinForm.exteriorPower`. -/
theorem exteriorPowerGram_eq_bilinForm_exteriorPower (h : LinearMap.BilinForm R M) (p : ℕ) :
    h.exteriorPowerGram p = LinearMap.BilinForm.exteriorPower h p := by
  symm
  refine (h.eq_exteriorPowerGram_iff p _).mpr fun x y ↦ ?_
  rw [LinearMap.BilinForm.bilinForm_ιMulti_ιMulti, ← Matrix.det_transpose]
  refine congrArg Matrix.det (Matrix.ext fun i j ↦ ?_)
  rw [Matrix.transpose_apply, Matrix.of_apply, Matrix.of_apply]

/-- **The exterior-power Gram form of a `σ`-symmetric sesquilinear form is `σ`-symmetric.** -/
theorem IsSymm.exteriorPowerGram [RingHomInvPair σ σ] {h : M →ₛₗ[σ] M →ₗ[R] R}
    (hh : h.IsSymm) (p : ℕ) : (h.exteriorPowerGram p).IsSymm :=
  hh.exteriorAlgebraGram.domRestrict (⋀[R]^p M)

end ExteriorPowerGram

end LinearMap

namespace Module.Basis

section SesquilinearBasis

variable {R M I : Type*} [CommRing R] [AddCommGroup M] [Module R M]
  [Fintype I] [LinearOrder I] (b : Module.Basis I R M)

/-- Exterior multiplication by a basis vector is adjoint to contraction by its coordinate, for the
`σ`-sesquilinear wedge-basis form of any ring endomorphism `σ`. -/
private theorem toLinearMapₛₗ₂_exteriorAlgebra_ι_basis_mul (σ : R →+* R) (i : I)
    (s t : _root_.ExteriorAlgebra R M) :
    toLinearMapₛₗ₂ σ b.ExteriorAlgebra b.ExteriorAlgebra
        (1 : Matrix (Finset I) (Finset I) R) (_root_.ExteriorAlgebra.ι R (b i) * s) t =
      toLinearMapₛₗ₂ σ b.ExteriorAlgebra b.ExteriorAlgebra
        (1 : Matrix (Finset I) (Finset I) R) s
        (contractLeft (Q := (0 : QuadraticForm R M)) (b.coord i) t) := by
  set H := toLinearMapₛₗ₂ σ b.ExteriorAlgebra b.ExteriorAlgebra
    (1 : Matrix (Finset I) (Finset I) R)
  have key : H.comp (LinearMap.mulLeft R (_root_.ExteriorAlgebra.ι R (b i))) =
      H.compl₂ (contractLeft (Q := (0 : QuadraticForm R M)) (b.coord i)) := by
    refine LinearMap.ext_basis b.ExteriorAlgebra b.ExteriorAlgebra fun S T ↦ ?_
    simp only [LinearMap.comp_apply, LinearMap.mulLeft_apply, LinearMap.compl₂_apply,
      ι_mul_basis, contractLeft_coord_basis]
    split_ifs with hiS hiT hiT <;>
      simp only [H, Units.smul_def, map_zsmul, map_zero, LinearMap.zero_apply,
        LinearMap.smul_apply, toLinearMapₛₗ₂_apply_basis, Matrix.one_apply]
    · have hne : S ≠ T.erase i := by rintro rfl; simp at hiS
      simp [hne]
    · by_cases hST : insert i S = T
      · subst hST
        simp [Finset.erase_insert hiS]
      · have hne : S ≠ T.erase i := by rintro rfl; exact hST (Finset.insert_erase hiT)
        simp [hST, hne]
    · have hne : insert i S ≠ T := by rintro rfl; exact hiT (Finset.mem_insert_self i S)
      simp [hne]
  exact LinearMap.congr_fun₂ key s t

/-- **The wedge-basis `σ`-sesquilinear form is the exterior Gram form** of the `σ`-sesquilinear
form making `b` orthonormal. -/
theorem toLinearMapₛₗ₂_exteriorAlgebra_eq_exteriorAlgebraGram (σ : R →+* R) :
    toLinearMapₛₗ₂ σ b.ExteriorAlgebra b.ExteriorAlgebra
        (1 : Matrix (Finset I) (Finset I) R) =
      (toLinearMapₛₗ₂ σ b b (1 : Matrix I I R)).exteriorAlgebraGram := by
  classical
  rw [LinearMap.eq_exteriorAlgebraGram_iff]
  have hvac (t : _root_.ExteriorAlgebra R M) :
      toLinearMapₛₗ₂ σ b.ExteriorAlgebra b.ExteriorAlgebra
        (1 : Matrix (Finset I) (Finset I) R) 1 t = _root_.ExteriorAlgebra.algebraMapInv t := by
    have hempty : b.ExteriorAlgebra ∅ = 1 := by simp [b.exteriorAlgebra_eq_prod_map_sort]
    rw [← hempty, toLinearMapₛₗ₂_one_basis_eq_coord, Module.Basis.coord_apply,
      b.exteriorAlgebra_repr_empty]
  refine ⟨by rw [hvac, map_one],
    fun y t ↦ by rw [hvac, map_mul, _root_.ExteriorAlgebra.algebraMapInv_ι, zero_mul],
    fun x s t ↦ ?_⟩
  rw [← b.sum_repr x]
  simp only [map_sum, map_smul, map_smulₛₗ, Finset.sum_mul, smul_mul_assoc,
    LinearMap.sum_apply, LinearMap.smul_apply, toLinearMapₛₗ₂_one_basis_eq_coord,
    toLinearMapₛₗ₂_exteriorAlgebra_ι_basis_mul]

/-- On `⋀[R]^p M`, the form making `b.exteriorPower p` orthonormal is `(toLinearMapₛₗ₂ σ b b 1)`'s
exterior-power Gram form. -/
theorem toLinearMapₛₗ₂_exteriorPower_eq_exteriorPowerGram (σ : R →+* R) (p : ℕ) :
    toLinearMapₛₗ₂ σ (b.exteriorPower p) (b.exteriorPower p)
        (1 : Matrix (Set.powersetCard I p) (Set.powersetCard I p) R) =
      (toLinearMapₛₗ₂ σ b b (1 : Matrix I I R)).exteriorPowerGram p := by
  refine LinearMap.ext_basis (b.exteriorPower p) (b.exteriorPower p) fun S T ↦ ?_
  rw [toLinearMapₛₗ₂_apply_basis, LinearMap.exteriorPowerGram_apply,
    ← _root_.ExteriorAlgebra.basis_eq_coe_basis, ← _root_.ExteriorAlgebra.basis_eq_coe_basis,
    ← b.toLinearMapₛₗ₂_exteriorAlgebra_eq_exteriorAlgebraGram, toLinearMapₛₗ₂_apply_basis]
  simp [Matrix.one_apply, Subtype.coe_inj]

end SesquilinearBasis

end Module.Basis

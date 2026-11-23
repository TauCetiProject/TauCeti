/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.BilinearForm.Basic
public import Mathlib.LinearAlgebra.ExteriorPower.BilinForm
public import Mathlib.LinearAlgebra.Matrix.SesquilinearForm
import Mathlib.Algebra.Algebra.RestrictScalars
import TauCeti.LinearAlgebra.Matrix.SesquilinearForm

/-!
# Sesquilinear Gram forms on exterior powers

Let `M` be a module over a commutative ring `R`, `σ : R →+* R` a ring endomorphism, and
`B : M →ₛₗ[σ] M →ₗ[R] R` a `σ`-sesquilinear form on `M` (`σ`-semilinear in its first argument and
`R`-linear in its second). Without choosing a basis or assuming finiteness or freeness of `M`,
`B` induces a `σ`-sesquilinear Gram form `B.sesqExteriorPower n` on every exterior power
`⋀[R]^n M`, uniquely determined on pure wedges by the Gram determinant

  `B.sesqExteriorPower n (v₀ ∧ ⋯ ∧ v_{n-1}) (w₀ ∧ ⋯ ∧ w_{n-1}) = det (B (v i) (w j))`.

Mathlib's `exteriorPower.pairingDual` and `LinearMap.BilinForm.exteriorPower` handle only the
bilinear case (`σ = RingHom.id R`), whereas Hermitian metrics on complexified exterior algebras and
polarized Fock spaces require conjugate-linear-first Gram forms. `LinearMap.sesqExteriorPower`
extends that construction to arbitrary `σ`-sesquilinear forms and feeds
`LinearMap.sesqExteriorAlgebra` (`TauCeti/LinearAlgebra/ExteriorAlgebra/HermitianMetric.lean`),
complexified exterior metrics (`TauCeti/LinearAlgebra/ExteriorPower/Complexification.lean`,
`TauCeti/LinearAlgebra/ExteriorAlgebra/Complexification.lean`), and Fock metrics
(`TauCeti/RepresentationTheory/Spin/Polarization/Fock/Metric.lean`).

When `σ = RingHom.id R`, `B.sesqExteriorPower n` agrees with Mathlib's `B.exteriorPower n`.
When `σ` is involutive and `B` is `σ`-Hermitian (`B.IsSymm`), `B.sesqExteriorPower n` is
`σ`-Hermitian as well. When `M` has a finite ordered basis `b`, the form making the induced basis
`b.exteriorPower n` orthonormal is the `n`-th exterior Gram form of the form making `b`
orthonormal.

## Main definitions

* `LinearMap.sesqExteriorPower`: the induced `σ`-sesquilinear Gram form on `⋀[R]^n M`.

## Main results

* `LinearMap.sesqExteriorPower_ιMulti`: pairing a pure wedge gives
  `alternatingMapToDual R M n (B ∘ v)`.
* `LinearMap.sesqExteriorPower_ιMulti_ιMulti`: evaluation on pure wedges as `det (B (v i) (w j))`.
* `LinearMap.eq_sesqExteriorPower_iff`: uniqueness by values on pure wedges.
* `LinearMap.sesqExteriorPower_map_map`: naturality under `R`-linear maps preserving the form.
* `LinearMap.IsSymm.sesqExteriorPower`: `σ`-Hermitian symmetry for involutive `σ`.
* `LinearMap.BilinForm.sesqExteriorPower_eq_exteriorPower`: bilinear specialization matching
  Mathlib's `LinearMap.BilinForm.exteriorPower`.
* `Module.Basis.toLinearMapₛₗ₂_exteriorPower_one`: compatibility with the coordinate form of
  `b.exteriorPower n`.

## References

* W. Greub, *Multilinear Algebra*, 2nd ed., Springer (1978), Chapter 5.
* L. I. Nicolaescu, *Lectures on the Geometry of Manifolds*, 3rd ed., World Scientific (2020),
  §2.2.4.
-/

public section

open exteriorPower Matrix

namespace LinearMap

variable {R M M' : Type*} [CommRing R] {σ : R →+* R}
  [AddCommGroup M] [Module R M] [AddCommGroup M'] [Module R M']

/-- The `σ`-sesquilinear Gram form induced on the `n`-th exterior power `⋀[R]^n M` by a
`σ`-sesquilinear form `B : M →ₛₗ[σ] M →ₗ[R] R`. On pure wedges it evaluates to the determinant of
the Gram matrix `(B (v i) (w j))` (`LinearMap.sesqExteriorPower_ιMulti_ιMulti`). -/
noncomputable def sesqExteriorPower (B : M →ₛₗ[σ] M →ₗ[R] R) (n : ℕ) :
    ⋀[R]^n M →ₛₗ[σ] ⋀[R]^n M →ₗ[R] R :=
  letI : Algebra R R := σ.toAlgebra
  let N := Module.Dual R (⋀[R]^n M)
  let alt : AlternatingMap R M (RestrictScalars R R N) (Fin n) :=
    { toFun v := (RestrictScalars.addEquiv R R N).symm (alternatingMapToDual R M n (B ∘ v))
      map_update_add' v i x y := by
        simp only [Function.comp_update, map_add]
        exact congrArg (RestrictScalars.addEquiv R R N).symm
          ((alternatingMapToDual R M n).map_update_add (B ∘ v) i (B x) (B y))
      map_update_smul' v i c x := by
        simp only [Function.comp_update, map_smulₛₗ, RingHom.id_apply]
        simp [RestrictScalars.smul_def, RingHom.algebraMap_toAlgebra]
      map_eq_zero_of_eq' v i j hv hij := by
        simp [(alternatingMapToDual R M n).map_eq_zero_of_eq (B ∘ v) (by simp [hv]) hij] }
  let toDual : RestrictScalars R R N →ₛₗ[σ] N :=
    { toFun := RestrictScalars.addEquiv R R N
      map_add' := map_add _
      map_smul' c x := RestrictScalars.addEquiv_map_smul R R N c x }
  let f : ⋀[R]^n M →ₗ[R] RestrictScalars R R N :=
    @alternatingMapLinearEquiv R _ n M (RestrictScalars R R N) _ _ _
      (RestrictScalars.module R R N) alt
  toDual.comp f

/-- Pairing a pure wedge `ιMulti R n v` with `B.sesqExteriorPower n` yields the linear
functional `alternatingMapToDual R M n (B ∘ v)`. -/
theorem sesqExteriorPower_ιMulti (B : M →ₛₗ[σ] M →ₗ[R] R) (n : ℕ) (v : Fin n → M) :
    B.sesqExteriorPower n (ιMulti R n v) = alternatingMapToDual R M n (B ∘ v) := by
  unfold sesqExteriorPower
  let N := Module.Dual R (⋀[R]^n M)
  -- `σ.toAlgebra` competes with `Algebra.id R` and `RestrictScalars` has separate `AddCommMonoid`
  -- / `AddCommGroup` instances, so we supply `RestrictScalars.module` explicitly.
  exact (congrArg (RestrictScalars.addEquiv R R N)
    (@alternatingMapLinearEquiv_apply_ιMulti R _ n M (RestrictScalars R R N) _ _ _
      (@RestrictScalars.module R R N _ _ _ σ.toAlgebra _) _ v)).trans
    ((RestrictScalars.addEquiv R R N).apply_symm_apply _)

/-- **Gram-determinant formula on pure wedges**: `B.sesqExteriorPower n` pairs two pure wedges by
`det (B (v i) (w j))`. -/
@[simp]
theorem sesqExteriorPower_ιMulti_ιMulti (B : M →ₛₗ[σ] M →ₗ[R] R) (n : ℕ) (v w : Fin n → M) :
    B.sesqExteriorPower n (ιMulti R n v) (ιMulti R n w) =
      (Matrix.of fun i j ↦ B (v i) (w j)).det := by
  rw [sesqExteriorPower_ιMulti, alternatingMapToDual_apply_ιMulti, ← Matrix.det_transpose]
  refine congrArg Matrix.det ?_
  ext i j
  simp [Matrix.transpose_apply]

/-- A `σ`-sesquilinear form on `⋀[R]^n M` equals `B.sesqExteriorPower n` if and only if it takes
the Gram-determinant values on pure wedges. -/
theorem eq_sesqExteriorPower_iff {B : M →ₛₗ[σ] M →ₗ[R] R} {n : ℕ}
    {F : ⋀[R]^n M →ₛₗ[σ] ⋀[R]^n M →ₗ[R] R} :
    F = B.sesqExteriorPower n ↔
      ∀ v w : Fin n → M,
        F (ιMulti R n v) (ιMulti R n w) = (Matrix.of fun i j ↦ B (v i) (w j)).det := by
  refine ⟨by rintro rfl; exact B.sesqExteriorPower_ιMulti_ιMulti n, fun h ↦ ?_⟩
  refine LinearMap.ext_on_range (ιMulti_span R n M) fun v ↦ ?_
  refine LinearMap.ext_on_range (ιMulti_span R n M) fun w ↦ ?_
  rw [h, sesqExteriorPower_ιMulti_ιMulti]

/-- In degree zero, `B.sesqExteriorPower 0` multiplies the `σ`-twisted first scalar by the second;
in particular it is independent of `B` and equals `1` on the empty wedge. -/
@[simp]
theorem sesqExteriorPower_degree_zero_apply (B : M →ₛₗ[σ] M →ₗ[R] R) (x y : ⋀[R]^0 M) :
    B.sesqExteriorPower 0 x y = σ (zeroEquiv R M x) * zeroEquiv R M y := by
  conv_lhs => rw [← (zeroEquiv R M).symm_apply_apply x, ← (zeroEquiv R M).symm_apply_apply y]
  simp only [zeroEquiv_symm_apply, map_smulₛₗ, LinearMap.smul_apply,
    sesqExteriorPower_ιMulti_ιMulti, det_isEmpty, smul_eq_mul, mul_one, RingHom.id_apply]
  exact mul_comm _ _

/-- In positive degree, the exterior Gram form of the zero form is zero. (In degree zero it sends
`1, 1` to the empty determinant `1`.) -/
@[simp]
theorem sesqExteriorPower_zero (n : ℕ) [NeZero n] :
    (0 : M →ₛₗ[σ] M →ₗ[R] R).sesqExteriorPower n = 0 := by
  have : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp (NeZero.pos n)
  symm
  rw [eq_sesqExteriorPower_iff]
  intro v w
  have h0 : (Matrix.of fun _ _ : Fin n ↦ (0 : R)) = 0 := rfl
  simp [h0]

/-- **Naturality of the exterior Gram form**: an `R`-linear map pulling `B'` back to `B` pulls
`B'.sesqExteriorPower n` back to `B.sesqExteriorPower n`. -/
theorem sesqExteriorPower_map_map {B : M →ₛₗ[σ] M →ₗ[R] R} {B' : M' →ₛₗ[σ] M' →ₗ[R] R}
    {f : M →ₗ[R] M'} (hf : ∀ u w, B' (f u) (f w) = B u w) (n : ℕ) (x y : ⋀[R]^n M) :
    B'.sesqExteriorPower n (exteriorPower.map n f x) (exteriorPower.map n f y) =
      B.sesqExteriorPower n x y := by
  have h : ((B'.sesqExteriorPower n).comp (exteriorPower.map n f)).compl₂
      (exteriorPower.map n f) = B.sesqExteriorPower n := by
    rw [eq_sesqExteriorPower_iff]
    intro v w
    simp [map_apply_ιMulti, Function.comp_def, hf]
  exact LinearMap.congr_fun₂ h x y

/-- **Hermitian symmetry on exterior powers**: if `σ` is involutive and `B` is `σ`-Hermitian, then
`B.sesqExteriorPower n` is `σ`-Hermitian. -/
theorem IsSymm.sesqExteriorPower {B : M →ₛₗ[σ] M →ₗ[R] R} (hσ : Function.Involutive σ)
    (hB : B.IsSymm) (n : ℕ) : (B.sesqExteriorPower n).IsSymm := by
  -- For fixed pure wedge `v`, both sides are `σ`-semilinear in `y`.
  have hpure (v : Fin n → M) (y : ⋀[R]^n M) :
      σ (B.sesqExteriorPower n (ιMulti R n v) y) = B.sesqExteriorPower n y (ιMulti R n v) := by
    let lhs : ⋀[R]^n M →ₛₗ[σ] R :=
      { toFun z := σ (B.sesqExteriorPower n (ιMulti R n v) z)
        map_add' z₁ z₂ := by simp
        map_smul' c z := by simp }
    have hlhs : lhs = (B.sesqExteriorPower n).flip (ιMulti R n v) := by
      refine LinearMap.ext_on_range (ιMulti_span R n M) fun w ↦ ?_
      simp only [lhs, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.flip_apply,
        sesqExteriorPower_ιMulti_ιMulti, RingHom.map_det]
      rw [← Matrix.det_transpose]
      congr 1
      ext i j
      exact hB.eq (v j) (w i)
    exact DFunLike.congr_fun hlhs y
  -- For fixed `y`, involutivity of `σ` makes `x ↦ σ (B.sesqExteriorPower n x y)` `R`-linear.
  refine isSymm_def.mpr fun x y ↦ ?_
  let lhs : ⋀[R]^n M →ₗ[R] R :=
    { toFun z := σ (B.sesqExteriorPower n z y)
      map_add' z₁ z₂ := by simp
      map_smul' c z := by simp [hσ c] }
  have hlhs : lhs = B.sesqExteriorPower n y :=
    LinearMap.ext_on_range (ιMulti_span R n M) fun v ↦ hpure v y
  exact DFunLike.congr_fun hlhs x

/-- When `σ` is the identity, `LinearMap.sesqExteriorPower` agrees with Mathlib's bilinear
exterior-power form `LinearMap.BilinForm.exteriorPower`. -/
theorem BilinForm.sesqExteriorPower_eq_exteriorPower (B : LinearMap.BilinForm R M) (n : ℕ) :
    LinearMap.sesqExteriorPower B n = B.exteriorPower n := by
  symm
  rw [eq_sesqExteriorPower_iff]
  intro v w
  rw [BilinForm.bilinForm_ιMulti_ιMulti, ← Matrix.det_transpose]
  refine congrArg Matrix.det ?_
  ext i j
  simp [Matrix.transpose_apply]

end LinearMap

namespace Module.Basis

/-- **Coordinate comparison on exterior powers**: for a finite ordered basis `b` of `M`, the
`σ`-sesquilinear form making the induced basis `b.exteriorPower n` orthonormal is the `n`-th
exterior Gram form of the `σ`-sesquilinear form making `b` orthonormal. -/
theorem toLinearMapₛₗ₂_exteriorPower_one {R M I : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [Fintype I] [LinearOrder I] (b : _root_.Module.Basis I R M) (σ : R →+* R) (n : ℕ) :
    toLinearMapₛₗ₂ σ (b.exteriorPower n) (b.exteriorPower n)
        (1 : Matrix (Set.powersetCard I n) (Set.powersetCard I n) R) =
      (toLinearMapₛₗ₂ σ b b (1 : Matrix I I R)).sesqExteriorPower n := by
  refine LinearMap.ext_basis (b.exteriorPower n) (b.exteriorPower n) fun s t ↦ ?_
  rw [toLinearMapₛₗ₂_one_basis_eq_coord, exteriorPower.basis_coord, exteriorPower.basis_apply,
    exteriorPower.basis_apply, exteriorPower.ιMulti_family, exteriorPower.ιMulti_family,
    exteriorPower.ιMultiDual_apply_ιMulti, LinearMap.sesqExteriorPower_ιMulti_ιMulti,
    ← Matrix.det_transpose]
  congr 1
  ext i j
  simp [toLinearMapₛₗ₂_one_basis_eq_coord]

end Module.Basis

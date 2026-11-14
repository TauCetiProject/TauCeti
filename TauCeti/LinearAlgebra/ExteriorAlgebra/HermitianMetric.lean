/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Basis.Bilinear
public import TauCeti.LinearAlgebra.ExteriorAlgebra.Contraction
public import TauCeti.LinearAlgebra.ExteriorAlgebra.DegreeScaling
public import TauCeti.LinearAlgebra.ExteriorPower.SesquilinearForm
public import TauCeti.LinearAlgebra.Matrix.SesquilinearForm

/-!
# Sesquilinear Gram forms and the Hermitian metric of an exterior algebra

Let `M` be a module over a commutative ring `R`, `σ : R →+* R` a ring endomorphism, and
`B : M →ₛₗ[σ] M →ₗ[R] R` a `σ`-sesquilinear form on `M`. Assembling the exterior-power Gram forms
`B.sesqExteriorPower n` orthogonally across the grading `⋀ M = ⨁ₙ ⋀ⁿ M` gives a basis-free
`σ`-sesquilinear Gram form `B.sesqExteriorAlgebra` on the whole exterior algebra
`ExteriorAlgebra R M`:

* on homogeneous elements of distinct degrees `p ≠ q`, `B.sesqExteriorAlgebra` vanishes;
* on pure wedges of degree `n` (including degree zero, where it sends `1, 1` to the empty
  determinant `1`), `B.sesqExteriorAlgebra` evaluates to the Gram determinant
  `det (B (v i) (w j))`;
* exterior multiplication by `x` is adjoint to contraction by `B x`,
  `B.sesqExteriorAlgebra (x ∧ s) t = B.sesqExteriorAlgebra s (B x ⌋ t)`, without any basis or
  finiteness assumption.

When `M` has a finite ordered basis `b`, the coordinate form
`Matrix.toLinearMapₛₗ₂ σ b.ExteriorAlgebra b.ExteriorAlgebra 1` making the increasing wedge basis
orthonormal equals `(Matrix.toLinearMapₛₗ₂ σ b b 1).sesqExteriorAlgebra`, so it inherits degree
orthogonality and the Gram-determinant formula in every degree. Over a commutative star ring `R`
with `σ = starRingEnd R`, this is the Hermitian exterior Gram metric used in Fock-space and
spinor-form constructions.

## Main definitions

* `LinearMap.sesqExteriorAlgebra`: the basis-free `σ`-sesquilinear Gram form on
  `ExteriorAlgebra R M`.

## Main results

* `LinearMap.sesqExteriorAlgebra_coe_coe` and
  `LinearMap.sesqExteriorAlgebra_eq_zero_of_mem_exteriorPower_of_ne`: restriction to `⋀[R]^n M` and
  orthogonality of distinct exterior powers.
* `LinearMap.sesqExteriorAlgebra_ιMulti_ιMulti`: the Gram-determinant formula on pure wedges in
  every degree.
* `LinearMap.sesqExteriorAlgebra_ι_mul_left` and `LinearMap.sesqExteriorAlgebra_ι_mul_right`:
  basis-free creation–annihilation adjointness.
* `LinearMap.IsSymm.sesqExteriorAlgebra`: `σ`-Hermitian symmetry when `σ` is involutive.
* `ExteriorAlgebra.toLinearMapₛₗ₂_exteriorAlgebra_one`: the wedge-basis form equals
  `(Matrix.toLinearMapₛₗ₂ σ b b 1).sesqExteriorAlgebra`.
* `ExteriorAlgebra.toLinearMapₛₗ₂_exteriorAlgebra_ιMulti_ιMulti` and
  `ExteriorAlgebra.toLinearMapₛₗ₂_exteriorAlgebra_eq_zero_of_mem_exteriorPower_of_ne`: the
  Gram-determinant formula and degree orthogonality for the wedge-basis form.
* `ExteriorAlgebra.toLinearMapₛₗ₂_ι_mul_left`, `ExteriorAlgebra.toLinearMapₛₗ₂_ι_mul_right`,
  `ExteriorAlgebra.toLinearMapₛₗ₂_eq_of_toLinearMapₛₗ₂_eq`, and
  `ExteriorAlgebra.toLinearMapₛₗ₂_degreeScaling_left`: adjointness and basis-independence for the
  wedge-basis Hermitian form.

## References

* W. Greub, *Multilinear Algebra*, 2nd ed., Springer (1978), Chapter 5.
* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry* (1989), Chapter I §5.
* L. I. Nicolaescu, *Lectures on the Geometry of Manifolds*, 3rd ed., World Scientific (2020),
  §2.2.4.
-/

public section

open CliffordAlgebra Matrix TauCeti.ExteriorAlgebra
open scoped DirectSum

namespace ExteriorAlgebra

variable {R M I : Type*} [CommRing R] [StarRing R] [AddCommGroup M] [Module R M]
  [Fintype I] [LinearOrder I] (b : Module.Basis I R M)

/-- **The vacuum is a unit vector**: `H 1 1 = 1` for the Hermitian form making the wedge basis
orthonormal.

Not `@[simp]`: `Matrix.toLinearMapₛₗ₂_apply` already expands the left-hand side. -/
theorem toLinearMapₛₗ₂_apply_one_one :
    toLinearMapₛₗ₂ (starRingEnd R) b.ExteriorAlgebra b.ExteriorAlgebra
      (1 : Matrix (Finset I) (Finset I) R) 1 1 = 1 := by
  have h : b.ExteriorAlgebra ∅ = 1 := by simp [b.exteriorAlgebra_eq_prod_map_sort]
  rw [← h, toLinearMapₛₗ₂_apply_basis, one_apply_eq]

/-- Exterior multiplication by a basis vector is adjoint to contraction by its coordinate. -/
private theorem toLinearMapₛₗ₂_ι_basis_mul (i : I) (s t : _root_.ExteriorAlgebra R M) :
    toLinearMapₛₗ₂ (starRingEnd R) b.ExteriorAlgebra b.ExteriorAlgebra
        (1 : Matrix (Finset I) (Finset I) R) (_root_.ExteriorAlgebra.ι R (b i) * s) t =
      toLinearMapₛₗ₂ (starRingEnd R) b.ExteriorAlgebra b.ExteriorAlgebra
        (1 : Matrix (Finset I) (Finset I) R) s
        (contractLeft (Q := (0 : QuadraticForm R M)) (b.coord i) t) := by
  set H := toLinearMapₛₗ₂ (starRingEnd R) b.ExteriorAlgebra b.ExteriorAlgebra
    (1 : Matrix (Finset I) (Finset I) R)
  have key : H.comp (LinearMap.mulLeft R (_root_.ExteriorAlgebra.ι R (b i))) =
      H.compl₂ (contractLeft (Q := (0 : QuadraticForm R M)) (b.coord i)) := by
    refine LinearMap.ext_basis b.ExteriorAlgebra b.ExteriorAlgebra fun S T ↦ ?_
    simp only [LinearMap.comp_apply, LinearMap.mulLeft_apply, LinearMap.compl₂_apply,
      ι_mul_basis, contractLeft_coord_basis]
    -- Both sides are the shuffle sign when `T = insert i S` with `i ∉ S`, and zero otherwise.
    split_ifs with hiS hiT hiT <;>
      simp only [H, Units.smul_def, map_zsmul, map_zero, LinearMap.zero_apply,
        LinearMap.smul_apply, toLinearMapₛₗ₂_apply_basis, Matrix.one_apply]
    · simp [show S ≠ T.erase i by rintro rfl; simp at hiS]
    · by_cases hST : insert i S = T
      · subst hST
        simp [Finset.erase_insert hiS]
      · simp [hST, show S ≠ T.erase i by rintro rfl; exact hST (Finset.insert_erase hiT)]
    · simp [show insert i S ≠ T by rintro rfl; exact hiT (Finset.mem_insert_self i S)]
  exact LinearMap.congr_fun₂ key s t

/-- **Exterior multiplication is adjoint to contraction**: for the Hermitian form `h` making `b`
orthonormal and the form `H` making the wedge basis orthonormal,
`H (x ∧ s) t = H s (h(x, ·) ⌋ t)`. -/
theorem toLinearMapₛₗ₂_ι_mul_left (x : M) (s t : _root_.ExteriorAlgebra R M) :
    toLinearMapₛₗ₂ (starRingEnd R) b.ExteriorAlgebra b.ExteriorAlgebra
        (1 : Matrix (Finset I) (Finset I) R) (_root_.ExteriorAlgebra.ι R x * s) t =
      toLinearMapₛₗ₂ (starRingEnd R) b.ExteriorAlgebra b.ExteriorAlgebra
        (1 : Matrix (Finset I) (Finset I) R) s
        (contractLeft (Q := (0 : QuadraticForm R M))
          (toLinearMapₛₗ₂ (starRingEnd R) b b (1 : Matrix I I R) x) t) := by
  rw [← b.sum_repr x]
  simp only [map_sum, map_smul, map_smulₛₗ, Finset.sum_mul, smul_mul_assoc,
    LinearMap.sum_apply, LinearMap.smul_apply, toLinearMapₛₗ₂_one_basis_eq_coord,
    toLinearMapₛₗ₂_ι_basis_mul]

/-- **Contraction is adjoint to exterior multiplication**: for the Hermitian form `h` making `b`
orthonormal and the form `H` making the wedge basis orthonormal,
`H s (x ∧ t) = H (h(x, ·) ⌋ s) t`. -/
theorem toLinearMapₛₗ₂_ι_mul_right (x : M) (s t : _root_.ExteriorAlgebra R M) :
    toLinearMapₛₗ₂ (starRingEnd R) b.ExteriorAlgebra b.ExteriorAlgebra
        (1 : Matrix (Finset I) (Finset I) R) s (_root_.ExteriorAlgebra.ι R x * t) =
      toLinearMapₛₗ₂ (starRingEnd R) b.ExteriorAlgebra b.ExteriorAlgebra
        (1 : Matrix (Finset I) (Finset I) R)
        (contractLeft (Q := (0 : QuadraticForm R M))
          (toLinearMapₛₗ₂ (starRingEnd R) b b (1 : Matrix I I R) x) s) t := by
  rw [← star_toLinearMapₛₗ₂_one_apply, toLinearMapₛₗ₂_ι_mul_left, star_toLinearMapₛₗ₂_one_apply]

/-- **The Hermitian form of `⋀ M` depends only on the Hermitian form of `M`**: if two finite
ordered bases `b` and `b'` of `M` are orthonormal for the same Hermitian form, then their wedge
bases are orthonormal for the same Hermitian form on `⋀ M`. -/
theorem toLinearMapₛₗ₂_eq_of_toLinearMapₛₗ₂_eq {I' : Type*} [Fintype I'] [LinearOrder I']
    (b' : Module.Basis I' R M)
    (h : toLinearMapₛₗ₂ (starRingEnd R) b b (1 : Matrix I I R) =
      toLinearMapₛₗ₂ (starRingEnd R) b' b' (1 : Matrix I' I' R)) :
    toLinearMapₛₗ₂ (starRingEnd R) b.ExteriorAlgebra b.ExteriorAlgebra
        (1 : Matrix (Finset I) (Finset I) R) =
      toLinearMapₛₗ₂ (starRingEnd R) b'.ExteriorAlgebra b'.ExteriorAlgebra
        (1 : Matrix (Finset I') (Finset I') R) := by
  set H := toLinearMapₛₗ₂ (starRingEnd R) b.ExteriorAlgebra b.ExteriorAlgebra
    (1 : Matrix (Finset I) (Finset I) R)
  set H' := toLinearMapₛₗ₂ (starRingEnd R) b'.ExteriorAlgebra b'.ExteriorAlgebra
    (1 : Matrix (Finset I') (Finset I') R)
  -- Both forms pair the vacuum with `t` by the scalar part of `t`.
  have hone (t : _root_.ExteriorAlgebra R M) : H 1 t = H' 1 t := by
    induction t using CliffordAlgebra.left_induction with
    | algebraMap r =>
      simp only [H, H', Algebra.algebraMap_eq_smul_one, map_smul, toLinearMapₛₗ₂_apply_one_one]
    | add x y hx hy => rw [map_add, map_add, hx, hy]
    | ι_mul t m _ =>
      rw [toLinearMapₛₗ₂_ι_mul_right, toLinearMapₛₗ₂_ι_mul_right, contractLeft_one,
        contractLeft_one, map_zero, map_zero, LinearMap.zero_apply]
  refine LinearMap.ext fun s ↦ ?_
  induction s using CliffordAlgebra.left_induction with
  | algebraMap r =>
    refine LinearMap.ext fun t ↦ ?_
    rw [Algebra.algebraMap_eq_smul_one, map_smulₛₗ, map_smulₛₗ, LinearMap.smul_apply,
      LinearMap.smul_apply, hone]
  | add x y hx hy => rw [map_add, map_add, hx, hy]
  | ι_mul s m hs =>
    refine LinearMap.ext fun t ↦ ?_
    rw [toLinearMapₛₗ₂_ι_mul_left, toLinearMapₛₗ₂_ι_mul_left, hs, h]

/-- **The adjoint of the degree scaling by `r` is the degree scaling by `star r`**: for the form `H`
making the wedge basis orthonormal, `H (T_r s) t = H s (T_{star r} t)`. -/
theorem toLinearMapₛₗ₂_degreeScaling_left (r : Rˣ) (s t : _root_.ExteriorAlgebra R M) :
    toLinearMapₛₗ₂ (starRingEnd R) b.ExteriorAlgebra b.ExteriorAlgebra
        (1 : Matrix (Finset I) (Finset I) R) (degreeScaling r s) t =
      toLinearMapₛₗ₂ (starRingEnd R) b.ExteriorAlgebra b.ExteriorAlgebra
        (1 : Matrix (Finset I) (Finset I) R) s (degreeScaling (star r) t) := by
  set H := toLinearMapₛₗ₂ (starRingEnd R) b.ExteriorAlgebra b.ExteriorAlgebra
    (1 : Matrix (Finset I) (Finset I) R)
  have key : H.comp (degreeScaling r).toLinearMap =
      H.compl₂ (degreeScaling (star r)).toLinearMap := by
    refine LinearMap.ext_basis b.ExteriorAlgebra b.ExteriorAlgebra fun S T ↦ ?_
    simp only [H, LinearMap.comp_apply, LinearMap.compl₂_apply, AlgEquiv.toLinearMap_apply,
      degreeScaling_basis, map_smulₛₗ, LinearMap.smul_apply, toLinearMapₛₗ₂_apply_basis,
      Matrix.one_apply, Units.coe_star, smul_eq_mul, starRingEnd_apply, star_pow, RingHom.id_apply]
    split_ifs with hST
    · rw [hST]
    · simp only [mul_zero]
  exact LinearMap.congr_fun₂ key s t

/-- **The degree scaling rescales the metric on each exterior power**: for the form `H` making the
wedge basis orthonormal and `s` in the `p`-th exterior power, `H (T_r s) (T_r t)` is
`(star r * r) ^ p` times `H s t`. -/
theorem toLinearMapₛₗ₂_degreeScaling_degreeScaling_of_mem_exteriorPower (r : Rˣ) {p : ℕ}
    {s : _root_.ExteriorAlgebra R M} (hs : s ∈ ⋀[R]^p M) (t : _root_.ExteriorAlgebra R M) :
    toLinearMapₛₗ₂ (starRingEnd R) b.ExteriorAlgebra b.ExteriorAlgebra
        (1 : Matrix (Finset I) (Finset I) R) (degreeScaling r s) (degreeScaling r t) =
      (star (r : R) * r) ^ p * toLinearMapₛₗ₂ (starRingEnd R) b.ExteriorAlgebra b.ExteriorAlgebra
        (1 : Matrix (Finset I) (Finset I) R) s t := by
  -- Move the right-hand scaling across as `T_{star r}`, which also acts on `s` by a scalar.
  have h := toLinearMapₛₗ₂_degreeScaling_left b (star r) s t
  rw [star_star] at h
  rw [degreeScaling_of_mem_exteriorPower r hs, map_smulₛₗ, LinearMap.smul_apply, ← h,
    degreeScaling_of_mem_exteriorPower _ hs, map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul,
    smul_eq_mul]
  simp only [Units.coe_star, starRingEnd_apply, star_pow, star_star]
  ring

end ExteriorAlgebra

namespace LinearMap

variable {R M M' : Type*} [CommRing R] {σ : R →+* R}
  [AddCommGroup M] [Module R M] [AddCommGroup M'] [Module R M']

/-- The `n`-th homogeneous projection `ExteriorAlgebra R M →ₗ[R] ⋀[R]^n M`. -/
private noncomputable def exteriorComponent (n : ℕ) :
    _root_.ExteriorAlgebra R M →ₗ[R] ⋀[R]^n M :=
  (DirectSum.component R ℕ (fun k ↦ ⋀[R]^k M) n).comp
    (DirectSum.decomposeLinearEquiv (fun k ↦ ⋀[R]^k M)).toLinearMap

/-- The basis-free `σ`-sesquilinear Gram form on `ExteriorAlgebra R M` induced by
`B : M →ₛₗ[σ] M →ₗ[R] R`: the orthogonal direct sum of `B.sesqExteriorPower n` across the
homogeneous exterior powers `⋀[R]^n M`. -/
noncomputable def sesqExteriorAlgebra (B : M →ₛₗ[σ] M →ₗ[R] R) :
    _root_.ExteriorAlgebra R M →ₛₗ[σ] _root_.ExteriorAlgebra R M →ₗ[R] R :=
  let φ : (n : ℕ) → ⋀[R]^n M →+ (_root_.ExteriorAlgebra R M →ₗ[R] R) := fun n ↦
    { toFun sn := (B.sesqExteriorPower n sn).comp (exteriorComponent n)
      map_zero' := by simp
      map_add' x y := by ext t; simp }
  let Φ := DirectSum.toAddMonoid φ
  { toFun s := Φ (DirectSum.decompose (fun n ↦ ⋀[R]^n M) s)
    map_add' s₁ s₂ := by simp
    map_smul' c s := by
      rw [DirectSum.decompose_smul]
      generalize DirectSum.decompose (fun n ↦ ⋀[R]^n M) s = d
      induction d using DirectSum.induction_on with
      | zero => simp
      | of n x =>
        rw [← DirectSum.lof_eq_of R, ← map_smul, DirectSum.lof_eq_of, DirectSum.lof_eq_of]
        ext t
        simp [Φ, φ]
      | add x y hx hy => simp [smul_add, hx, hy] }

/-- On homogeneous elements of the same degree `n`, `B.sesqExteriorAlgebra` agrees with
`B.sesqExteriorPower n`. -/
@[simp]
theorem sesqExteriorAlgebra_coe_coe (B : M →ₛₗ[σ] M →ₗ[R] R) {n : ℕ} (x y : ⋀[R]^n M) :
    B.sesqExteriorAlgebra (x : _root_.ExteriorAlgebra R M) (y : _root_.ExteriorAlgebra R M) =
      B.sesqExteriorPower n x y := by
  simp only [sesqExteriorAlgebra, LinearMap.coe_mk, AddHom.coe_mk, DirectSum.decompose_coe,
    DirectSum.toAddMonoid_of, AddMonoidHom.coe_mk]
  simp [exteriorComponent, DirectSum.decomposeLinearEquiv_apply, ← DirectSum.lof_eq_of R]

/-- **Distinct exterior powers are orthogonal** for `B.sesqExteriorAlgebra`. -/
theorem sesqExteriorAlgebra_eq_zero_of_mem_exteriorPower_of_ne (B : M →ₛₗ[σ] M →ₗ[R] R)
    {p q : ℕ} (hpq : p ≠ q) {s t : _root_.ExteriorAlgebra R M}
    (hs : s ∈ ⋀[R]^p M) (ht : t ∈ ⋀[R]^q M) :
    B.sesqExteriorAlgebra s t = 0 := by
  let s' : ⋀[R]^p M := ⟨s, hs⟩
  let t' : ⋀[R]^q M := ⟨t, ht⟩
  change B.sesqExteriorAlgebra (s' : _root_.ExteriorAlgebra R M)
    (t' : _root_.ExteriorAlgebra R M) = 0
  simp only [sesqExteriorAlgebra, LinearMap.coe_mk, AddHom.coe_mk, DirectSum.decompose_coe,
    DirectSum.toAddMonoid_of, AddMonoidHom.coe_mk]
  simp [exteriorComponent, DirectSum.decomposeLinearEquiv_apply, ← DirectSum.lof_eq_of R,
    DirectSum.component.of, hpq.symm]

/-- **Gram-determinant formula on the exterior algebra**: in every degree `n` (including `n = 0`),
`B.sesqExteriorAlgebra` evaluates on pure wedges to `det (B (v i) (w j))`. -/
@[simp]
theorem sesqExteriorAlgebra_ιMulti_ιMulti (B : M →ₛₗ[σ] M →ₗ[R] R) (n : ℕ) (v w : Fin n → M) :
    B.sesqExteriorAlgebra (_root_.ExteriorAlgebra.ιMulti R n v)
        (_root_.ExteriorAlgebra.ιMulti R n w) =
      (Matrix.of fun i j ↦ B (v i) (w j)).det := by
  rw [← exteriorPower.ιMulti_apply_coe, ← exteriorPower.ιMulti_apply_coe,
    sesqExteriorAlgebra_coe_coe, sesqExteriorPower_ιMulti_ιMulti]

/-- The vacuum `1` is a unit vector for `B.sesqExteriorAlgebra`: `B.sesqExteriorAlgebra 1 1 = 1`. -/
@[simp]
theorem sesqExteriorAlgebra_one_one (B : M →ₛₗ[σ] M →ₗ[R] R) :
    B.sesqExteriorAlgebra 1 1 = 1 := by
  have h1 : (1 : _root_.ExteriorAlgebra R M) = _root_.ExteriorAlgebra.ιMulti R 0 Fin.elim0 := by
    simp [_root_.ExteriorAlgebra.ιMulti_zero_apply]
  rw [h1, sesqExteriorAlgebra_ιMulti_ιMulti, det_isEmpty]

/-- On generators `ι R v` and `ι R w`, `B.sesqExteriorAlgebra` recovers `B v w`. -/
@[simp]
theorem sesqExteriorAlgebra_ι_ι (B : M →ₛₗ[σ] M →ₗ[R] R) (v w : M) :
    B.sesqExteriorAlgebra (_root_.ExteriorAlgebra.ι R v) (_root_.ExteriorAlgebra.ι R w) =
      B v w := by
  have hι (u : M) : _root_.ExteriorAlgebra.ι R u = _root_.ExteriorAlgebra.ιMulti R 1 ![u] := by
    simp [_root_.ExteriorAlgebra.ιMulti_succ_apply, _root_.ExteriorAlgebra.ιMulti_zero_apply]
  rw [hι v, hι w, sesqExteriorAlgebra_ιMulti_ιMulti, det_unique]
  simp

/-- **Naturality on the exterior algebra**: an `R`-linear map pulling `B'` back to `B` pulls
`B'.sesqExteriorAlgebra` back to `B.sesqExteriorAlgebra`. -/
theorem sesqExteriorAlgebra_map_map {B : M →ₛₗ[σ] M →ₗ[R] R} {B' : M' →ₛₗ[σ] M' →ₗ[R] R}
    {f : M →ₗ[R] M'} (hf : ∀ u w, B' (f u) (f w) = B u w) (s t : _root_.ExteriorAlgebra R M) :
    B'.sesqExteriorAlgebra (_root_.ExteriorAlgebra.map f s) (_root_.ExteriorAlgebra.map f t) =
      B.sesqExteriorAlgebra s t := by
  have h : ((B'.sesqExteriorAlgebra.comp (_root_.ExteriorAlgebra.map f).toLinearMap).compl₂
      (_root_.ExteriorAlgebra.map f).toLinearMap) = B.sesqExteriorAlgebra := by
    refine LinearMap.ext_on_range (_root_.ExteriorAlgebra.ιMulti_span R M) fun ⟨p, u⟩ ↦ ?_
    refine LinearMap.ext_on_range (_root_.ExteriorAlgebra.ιMulti_span R M) fun ⟨q, v⟩ ↦ ?_
    simp only [LinearMap.compl₂_apply, LinearMap.comp_apply, AlgHom.toLinearMap_apply,
      ← exteriorPower.ιMulti_apply_coe, ← exteriorPower.coe_map]
    rcases eq_or_ne p q with rfl | hpq
    · simp only [sesqExteriorAlgebra_coe_coe, sesqExteriorPower_map_map hf]
    · rw [B'.sesqExteriorAlgebra_eq_zero_of_mem_exteriorPower_of_ne hpq (Subtype.prop _)
          (Subtype.prop _),
        B.sesqExteriorAlgebra_eq_zero_of_mem_exteriorPower_of_ne hpq (Subtype.prop _)
          (Subtype.prop _)]
  exact LinearMap.congr_fun₂ h s t

/-- **Hermitian symmetry on the exterior algebra**: if `σ` is involutive and `B` is `σ`-Hermitian,
then `B.sesqExteriorAlgebra` is `σ`-Hermitian. -/
theorem IsSymm.sesqExteriorAlgebra {B : M →ₛₗ[σ] M →ₗ[R] R} (hσ : Function.Involutive σ)
    (hB : B.IsSymm) : B.sesqExteriorAlgebra.IsSymm := by
  refine isSymm_def.mpr fun s t ↦ ?_
  induction s using DirectSum.Decomposition.inductionOn fun p ↦ ⋀[R]^p M with
  | zero => simp
  | add x y hx hy => simp [hx, hy]
  | @homogeneous p s =>
    induction t using DirectSum.Decomposition.inductionOn fun q ↦ ⋀[R]^q M with
    | zero => simp
    | add x y hx hy => simp [hx, hy]
    | @homogeneous q t =>
      rcases eq_or_ne p q with rfl | hpq
      · simp only [sesqExteriorAlgebra_coe_coe]
        exact (hB.sesqExteriorPower hσ p).eq s t
      · rw [B.sesqExteriorAlgebra_eq_zero_of_mem_exteriorPower_of_ne hpq s.2 t.2,
          B.sesqExteriorAlgebra_eq_zero_of_mem_exteriorPower_of_ne hpq.symm t.2 s.2, map_zero]

/-- **Basis-free creation–annihilation adjointness**: exterior multiplication by `x` is adjoint to
contraction by `B x` with respect to `B.sesqExteriorAlgebra`, with no basis or finiteness
assumption on `M`. -/
theorem sesqExteriorAlgebra_ι_mul_left (B : M →ₛₗ[σ] M →ₗ[R] R) (x : M)
    (s t : _root_.ExteriorAlgebra R M) :
    B.sesqExteriorAlgebra (_root_.ExteriorAlgebra.ι R x * s) t =
      B.sesqExteriorAlgebra s (contractLeft (Q := (0 : QuadraticForm R M)) (B x) t) := by
  have key : B.sesqExteriorAlgebra.comp (LinearMap.mulLeft R (_root_.ExteriorAlgebra.ι R x)) =
      B.sesqExteriorAlgebra.compl₂ (contractLeft (Q := (0 : QuadraticForm R M)) (B x)) := by
    refine LinearMap.ext_on_range (_root_.ExteriorAlgebra.ιMulti_span R M) fun ⟨p, u⟩ ↦ ?_
    refine LinearMap.ext_on_range (_root_.ExteriorAlgebra.ιMulti_span R M) fun ⟨q, v⟩ ↦ ?_
    simp only [LinearMap.comp_apply, LinearMap.mulLeft_apply, LinearMap.compl₂_apply]
    have htail : Matrix.vecTail (Fin.cons x u) = u := by
      ext i
      simp [Matrix.vecTail]
    have hcons : _root_.ExteriorAlgebra.ι R x * _root_.ExteriorAlgebra.ιMulti R p u =
        _root_.ExteriorAlgebra.ιMulti R (p + 1) (Fin.cons x u) := by
      rw [_root_.ExteriorAlgebra.ιMulti_succ_apply, Fin.cons_zero, htail]
    have hmem (k : ℕ) (w : Fin k → M) : _root_.ExteriorAlgebra.ιMulti R k w ∈ ⋀[R]^k M := by
      rw [← exteriorPower.ιMulti_apply_coe]
      exact (exteriorPower.ιMulti R k w).2
    rw [hcons]
    rcases q with _ | q
    · rw [B.sesqExteriorAlgebra_eq_zero_of_mem_exteriorPower_of_ne (Nat.succ_ne_zero p)
          (hmem (p + 1) _) (hmem 0 v),
        contractLeft_eq_zero_of_mem_exteriorPower_zero (B x) (hmem 0 v), map_zero]
    · rcases eq_or_ne p q with rfl | hpq
      · rw [sesqExteriorAlgebra_ιMulti_ιMulti, Matrix.det_succ_row_zero, contractLeft_ιMulti,
          map_sum]
        refine Finset.sum_congr rfl fun j _ ↦ ?_
        have hsub : (Matrix.of fun i k : Fin (p + 1) ↦
            B (@Fin.cons p (fun _ ↦ M) x u i) (v k)).submatrix Fin.succ j.succAbove =
              Matrix.of fun i k ↦ B (u i) (j.removeNth v k) := by
          ext i k
          simp [Fin.removeNth_apply]
        rw [map_smul, sesqExteriorAlgebra_ιMulti_ιMulti, smul_eq_mul, hsub]
        simp only [Matrix.of_apply, Fin.cons_zero]
      · rw [B.sesqExteriorAlgebra_eq_zero_of_mem_exteriorPower_of_ne (by omega)
            (hmem (p + 1) _) (hmem (q + 1) v),
          B.sesqExteriorAlgebra_eq_zero_of_mem_exteriorPower_of_ne hpq
            (hmem p u) (contractLeft_mem_exteriorPower (B x) (hmem (q + 1) v))]
  exact LinearMap.congr_fun₂ key s t

/-- **Basis-free right creation–annihilation adjointness**: when `B` is `σ`-Hermitian,
`B.sesqExteriorAlgebra s (x ∧ t) = B.sesqExteriorAlgebra (B x ⌋ s) t`. -/
theorem sesqExteriorAlgebra_ι_mul_right {B : M →ₛₗ[σ] M →ₗ[R] R} (hB : B.IsSymm) (x : M)
    (s t : _root_.ExteriorAlgebra R M) :
    B.sesqExteriorAlgebra s (_root_.ExteriorAlgebra.ι R x * t) =
      B.sesqExteriorAlgebra (contractLeft (Q := (0 : QuadraticForm R M)) (B x) s) t := by
  have key : B.sesqExteriorAlgebra.compl₂ (LinearMap.mulLeft R (_root_.ExteriorAlgebra.ι R x)) =
      B.sesqExteriorAlgebra.comp (contractLeft (Q := (0 : QuadraticForm R M)) (B x)) := by
    refine LinearMap.ext_on_range (_root_.ExteriorAlgebra.ιMulti_span R M) fun ⟨p, u⟩ ↦ ?_
    refine LinearMap.ext_on_range (_root_.ExteriorAlgebra.ιMulti_span R M) fun ⟨q, v⟩ ↦ ?_
    simp only [LinearMap.comp_apply, LinearMap.mulLeft_apply, LinearMap.compl₂_apply]
    have htail : Matrix.vecTail (Fin.cons x v) = v := by ext i; simp [Matrix.vecTail]
    have hcons : _root_.ExteriorAlgebra.ι R x * _root_.ExteriorAlgebra.ιMulti R q v =
        _root_.ExteriorAlgebra.ιMulti R (q + 1) (Fin.cons x v) := by
      rw [_root_.ExteriorAlgebra.ιMulti_succ_apply, Fin.cons_zero, htail]
    have hmem (k : ℕ) (w : Fin k → M) : _root_.ExteriorAlgebra.ιMulti R k w ∈ ⋀[R]^k M := by
      rw [← exteriorPower.ιMulti_apply_coe]; exact (exteriorPower.ιMulti R k w).2
    rw [hcons]
    rcases p with _ | p
    · rw [B.sesqExteriorAlgebra_eq_zero_of_mem_exteriorPower_of_ne (Nat.zero_ne_add_one q)
          (hmem 0 u) (hmem (q + 1) _),
        contractLeft_eq_zero_of_mem_exteriorPower_zero (B x) (hmem 0 u), map_zero,
        LinearMap.zero_apply]
    · rcases eq_or_ne p q with rfl | hpq
      · rw [sesqExteriorAlgebra_ιMulti_ιMulti, Matrix.det_succ_column_zero, contractLeft_ιMulti,
          map_sum, LinearMap.sum_apply]
        refine Finset.sum_congr rfl fun i _ ↦ ?_
        have hsub : (Matrix.of fun j k : Fin (p + 1) ↦
            B (u j) (@Fin.cons p (fun _ ↦ M) x v k)).submatrix i.succAbove Fin.succ =
              Matrix.of fun j k ↦ B (i.removeNth u j) (v k) := by
          ext j k; simp [Fin.removeNth_apply]
        rw [map_smulₛₗ, LinearMap.smul_apply, sesqExteriorAlgebra_ιMulti_ιMulti, smul_eq_mul,
          map_mul, map_pow, map_neg, map_one, hB.eq x (u i), hsub]
        simp only [Matrix.of_apply, Fin.cons_zero]
      · rw [B.sesqExteriorAlgebra_eq_zero_of_mem_exteriorPower_of_ne (by omega)
            (hmem (p + 1) u) (hmem (q + 1) _),
          B.sesqExteriorAlgebra_eq_zero_of_mem_exteriorPower_of_ne hpq
            (contractLeft_mem_exteriorPower (B x) (hmem (p + 1) u)) (hmem q v)]
  exact LinearMap.congr_fun₂ key s t

/-- **Basis-free degree-scaling adjointness**: the degree scaling by `r : Rˣ` on the left is adjoint
to the degree scaling by `Units.map σ.toMonoidHom r` on the right. -/
theorem sesqExteriorAlgebra_degreeScaling_left (B : M →ₛₗ[σ] M →ₗ[R] R) (r : Rˣ)
    (s t : _root_.ExteriorAlgebra R M) :
    B.sesqExteriorAlgebra (degreeScaling r s) t =
      B.sesqExteriorAlgebra s (degreeScaling (Units.map σ.toMonoidHom r) t) := by
  induction s using DirectSum.Decomposition.inductionOn fun p ↦ ⋀[R]^p M with
  | zero => simp
  | add x y hx hy => simp [hx, hy]
  | @homogeneous p s =>
    induction t using DirectSum.Decomposition.inductionOn fun q ↦ ⋀[R]^q M with
    | zero => simp
    | add x y hx hy => simp [hx, hy]
    | @homogeneous q t =>
      rw [degreeScaling_of_mem_exteriorPower r s.2,
        degreeScaling_of_mem_exteriorPower (Units.map σ.toMonoidHom r) t.2]
      rcases eq_or_ne p q with rfl | hpq
      · simp
      · simp [B.sesqExteriorAlgebra_eq_zero_of_mem_exteriorPower_of_ne hpq s.2 t.2]

/-- **Basis-free degree-scaling rescaling**: on `s ∈ ⋀[R]^p M`, `B.sesqExteriorAlgebra` rescales
under `degreeScaling r` in both arguments by `(σ r * r) ^ p`. -/
theorem sesqExteriorAlgebra_degreeScaling_degreeScaling_of_mem_exteriorPower
    (B : M →ₛₗ[σ] M →ₗ[R] R) (r : Rˣ) {p : ℕ} {s : _root_.ExteriorAlgebra R M}
    (hs : s ∈ ⋀[R]^p M) (t : _root_.ExteriorAlgebra R M) :
    B.sesqExteriorAlgebra (degreeScaling r s) (degreeScaling r t) =
      (σ r * r) ^ p * B.sesqExteriorAlgebra s t := by
  rw [degreeScaling_of_mem_exteriorPower r hs, map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul,
    map_pow]
  induction t using DirectSum.Decomposition.inductionOn fun q ↦ ⋀[R]^q M with
  | zero => simp
  | add x y hx hy => simp [hx, hy, mul_add]
  | @homogeneous q t =>
    rw [degreeScaling_of_mem_exteriorPower r t.2, map_smul, smul_eq_mul]
    rcases eq_or_ne p q with rfl | hpq
    · rw [mul_pow]
      ring
    · simp [B.sesqExteriorAlgebra_eq_zero_of_mem_exteriorPower_of_ne hpq hs t.2]

end LinearMap

namespace ExteriorAlgebra

variable {R M I : Type*} [CommRing R] [AddCommGroup M] [Module R M]
  [Fintype I] [LinearOrder I] (b : Module.Basis I R M)

/-- **The wedge-basis coordinate form is the exterior Gram form**: for any ring endomorphism `σ`,
the `σ`-sesquilinear form making `b.ExteriorAlgebra` orthonormal equals
`(toLinearMapₛₗ₂ σ b b 1).sesqExteriorAlgebra`. -/
theorem toLinearMapₛₗ₂_exteriorAlgebra_one (σ : R →+* R) :
    toLinearMapₛₗ₂ σ b.ExteriorAlgebra b.ExteriorAlgebra (1 : Matrix (Finset I) (Finset I) R) =
      (toLinearMapₛₗ₂ σ b b (1 : Matrix I I R)).sesqExteriorAlgebra := by
  refine LinearMap.ext_basis b.ExteriorAlgebra b.ExteriorAlgebra fun S T ↦ ?_
  rw [toLinearMapₛₗ₂_apply_basis, Matrix.one_apply]
  rcases eq_or_ne S.card T.card with hcard | hcard
  · let s : Set.powersetCard I S.card := ⟨S, rfl⟩
    let t : Set.powersetCard I S.card := ⟨T, Set.powersetCard.mem_iff.mpr hcard.symm⟩
    have hS : b.ExteriorAlgebra S = (b.exteriorPower S.card s : _root_.ExteriorAlgebra R M) :=
      basis_eq_coe_basis b s
    have hT : b.ExteriorAlgebra T = (b.exteriorPower S.card t : _root_.ExteriorAlgebra R M) :=
      basis_eq_coe_basis b t
    have hst : (s = t) ↔ (S = T) := Subtype.ext_iff
    rw [hS, hT, LinearMap.sesqExteriorAlgebra_coe_coe, ← toLinearMapₛₗ₂_exteriorPower_one,
      toLinearMapₛₗ₂_apply_basis, Matrix.one_apply]
    simp [hst]
  · have hne : S ≠ T := fun h ↦ hcard (congrArg Finset.card h)
    let s : Set.powersetCard I S.card := ⟨S, rfl⟩
    let t : Set.powersetCard I T.card := ⟨T, rfl⟩
    have hS : b.ExteriorAlgebra S ∈ ⋀[R]^S.card M := by
      rw [show S = s.1 from rfl, basis_eq_coe_basis b s]
      exact (b.exteriorPower S.card s).2
    have hT : b.ExteriorAlgebra T ∈ ⋀[R]^T.card M := by
      rw [show T = t.1 from rfl, basis_eq_coe_basis b t]
      exact (b.exteriorPower T.card t).2
    rw [LinearMap.sesqExteriorAlgebra_eq_zero_of_mem_exteriorPower_of_ne _ hcard hS hT]
    simp [hne]

/-- **Gram-determinant formula for the wedge-basis form**: in every degree `p` (including `p = 0`),
the form making `b.ExteriorAlgebra` orthonormal evaluates on pure wedges to the Gram determinant of
the form making `b` orthonormal. -/
theorem toLinearMapₛₗ₂_exteriorAlgebra_ιMulti_ιMulti (σ : R →+* R) (p : ℕ) (v w : Fin p → M) :
    toLinearMapₛₗ₂ σ b.ExteriorAlgebra b.ExteriorAlgebra (1 : Matrix (Finset I) (Finset I) R)
        (_root_.ExteriorAlgebra.ιMulti R p v) (_root_.ExteriorAlgebra.ιMulti R p w) =
      (Matrix.of fun i j ↦ toLinearMapₛₗ₂ σ b b (1 : Matrix I I R) (v i) (w j)).det := by
  rw [toLinearMapₛₗ₂_exteriorAlgebra_one, LinearMap.sesqExteriorAlgebra_ιMulti_ιMulti]

/-- **Distinct exterior powers are orthogonal for the wedge-basis form.** -/
theorem toLinearMapₛₗ₂_exteriorAlgebra_eq_zero_of_mem_exteriorPower_of_ne (σ : R →+* R)
    {p q : ℕ} (hpq : p ≠ q) {s t : _root_.ExteriorAlgebra R M}
    (hs : s ∈ ⋀[R]^p M) (ht : t ∈ ⋀[R]^q M) :
    toLinearMapₛₗ₂ σ b.ExteriorAlgebra b.ExteriorAlgebra (1 : Matrix (Finset I) (Finset I) R)
        s t = 0 := by
  rw [toLinearMapₛₗ₂_exteriorAlgebra_one]
  exact LinearMap.sesqExteriorAlgebra_eq_zero_of_mem_exteriorPower_of_ne _ hpq hs ht

end ExteriorAlgebra

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Basis.Bilinear
public import TauCeti.LinearAlgebra.ExteriorAlgebra.Contraction
public import TauCeti.LinearAlgebra.ExteriorAlgebra.DegreeScaling
public import TauCeti.LinearAlgebra.ExteriorPower.Projection
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
orthogonality, the Gram-determinant formula, creation–annihilation adjointness, basis-independence,
and degree-scaling adjointness directly for any ring endomorphism `σ`. Over a commutative star ring
`R` with `σ = starRingEnd R`, this is the Hermitian exterior Gram metric used in Fock-space and
spinor-form constructions.

## Main definitions

* `LinearMap.sesqExteriorAlgebra`: the basis-free `σ`-sesquilinear Gram form on
  `ExteriorAlgebra R M`.

## Main results

* `LinearMap.sesqExteriorAlgebra_coe_left`, `LinearMap.sesqExteriorAlgebra_coe_right`,
  `LinearMap.sesqExteriorAlgebra_coe_coe`,
  `LinearMap.sesqExteriorAlgebra_eq_zero_of_mem_exteriorPower_of_ne`, and
  `LinearMap.eq_sesqExteriorAlgebra_iff`: projection formulas, restriction to `⋀[R]^n M`,
  orthogonality of distinct exterior powers, and uniqueness characterization.
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
  wedge-basis `σ`-sesquilinear form.

## References

* W. Greub, *Multilinear Algebra*, 2nd ed., Springer (1978), Chapter 5.
* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry* (1989), Chapter I §5.
* L. I. Nicolaescu, *Lectures on the Geometry of Manifolds*, 3rd ed., World Scientific (2020),
  §2.2.4.
-/

public section

open CliffordAlgebra Matrix TauCeti.ExteriorAlgebra
open scoped DirectSum

namespace LinearMap

variable {R M M' : Type*} [CommRing R] {σ : R →+* R}
  [AddCommGroup M] [Module R M] [AddCommGroup M'] [Module R M']

/-- The basis-free `σ`-sesquilinear Gram form on `ExteriorAlgebra R M` induced by
`B : M →ₛₗ[σ] M →ₗ[R] R`: the orthogonal direct sum of `B.sesqExteriorPower n` across the
homogeneous exterior powers `⋀[R]^n M`. -/
noncomputable def sesqExteriorAlgebra (B : M →ₛₗ[σ] M →ₗ[R] R) :
    _root_.ExteriorAlgebra R M →ₛₗ[σ] _root_.ExteriorAlgebra R M →ₗ[R] R :=
  let Φ : (⨁ n, ⋀[R]^n M) →ₗ[R] (_root_.ExteriorAlgebra R M →ₛₗ[σ] R) :=
    DirectSum.toModule R ℕ (_root_.ExteriorAlgebra R M →ₛₗ[σ] R) fun n ↦
      { toFun y := ((B.sesqExteriorPower n).flip y).comp (TauCeti.exteriorPower.proj R M n)
        map_add' y₁ y₂ := by ext x; simp
        map_smul' c y := by ext x; simp }
  (Φ.comp (DirectSum.decomposeLinearEquiv (fun n ↦ ⋀[R]^n M)).toLinearMap).flip

/-- Pairing an arbitrary element with a homogeneous element of degree `n` projects the first
argument onto `⋀[R]^n M` and evaluates `B.sesqExteriorPower n`. -/
theorem sesqExteriorAlgebra_coe_right (B : M →ₛₗ[σ] M →ₗ[R] R) {n : ℕ}
    (x : _root_.ExteriorAlgebra R M) (y : ⋀[R]^n M) :
    B.sesqExteriorAlgebra x (y : _root_.ExteriorAlgebra R M) =
      B.sesqExteriorPower n (TauCeti.exteriorPower.proj R M n x) y := by
  simp [sesqExteriorAlgebra]

/-- Pairing a homogeneous element of degree `n` with an arbitrary element projects the second
argument onto `⋀[R]^n M` and evaluates `B.sesqExteriorPower n`. -/
theorem sesqExteriorAlgebra_coe_left (B : M →ₛₗ[σ] M →ₗ[R] R) {n : ℕ}
    (x : ⋀[R]^n M) (y : _root_.ExteriorAlgebra R M) :
    B.sesqExteriorAlgebra (x : _root_.ExteriorAlgebra R M) y =
      B.sesqExteriorPower n x (TauCeti.exteriorPower.proj R M n y) := by
  induction y using DirectSum.Decomposition.inductionOn fun m ↦ ⋀[R]^m M with
  | zero => simp
  | add y₁ y₂ hy₁ hy₂ => simp [hy₁, hy₂]
  | @homogeneous m y =>
    rcases eq_or_ne n m with rfl | hnm
    · rw [sesqExteriorAlgebra_coe_right, TauCeti.exteriorPower.proj_coe,
        TauCeti.exteriorPower.proj_coe]
    · rw [sesqExteriorAlgebra_coe_right,
        TauCeti.exteriorPower.proj_eq_zero_of_mem_of_ne hnm x.2,
        TauCeti.exteriorPower.proj_eq_zero_of_mem_of_ne hnm.symm y.2,
        map_zero, LinearMap.zero_apply, map_zero]

/-- On homogeneous elements of the same degree `n`, `B.sesqExteriorAlgebra` agrees with
`B.sesqExteriorPower n`. -/
@[simp]
theorem sesqExteriorAlgebra_coe_coe (B : M →ₛₗ[σ] M →ₗ[R] R) {n : ℕ} (x y : ⋀[R]^n M) :
    B.sesqExteriorAlgebra (x : _root_.ExteriorAlgebra R M) (y : _root_.ExteriorAlgebra R M) =
      B.sesqExteriorPower n x y := by
  rw [sesqExteriorAlgebra_coe_right, TauCeti.exteriorPower.proj_coe]

/-- **Distinct exterior powers are orthogonal** for `B.sesqExteriorAlgebra`. -/
theorem sesqExteriorAlgebra_eq_zero_of_mem_exteriorPower_of_ne (B : M →ₛₗ[σ] M →ₗ[R] R)
    {p q : ℕ} (hpq : p ≠ q) {s t : _root_.ExteriorAlgebra R M}
    (hs : s ∈ ⋀[R]^p M) (ht : t ∈ ⋀[R]^q M) :
    B.sesqExteriorAlgebra s t = 0 := by
  rw [sesqExteriorAlgebra_coe_right B s ⟨t, ht⟩,
    TauCeti.exteriorPower.proj_eq_zero_of_mem_of_ne hpq hs, map_zero, LinearMap.zero_apply]

/-- A `σ`-sesquilinear form on `ExteriorAlgebra R M` equals `B.sesqExteriorAlgebra` if and only if
it restricts to `B.sesqExteriorPower n` on each homogeneous exterior power `⋀[R]^n M` and makes
distinct exterior powers orthogonal. -/
theorem eq_sesqExteriorAlgebra_iff {B : M →ₛₗ[σ] M →ₗ[R] R}
    {F : _root_.ExteriorAlgebra R M →ₛₗ[σ] _root_.ExteriorAlgebra R M →ₗ[R] R} :
    F = B.sesqExteriorAlgebra ↔
      (∀ (n : ℕ) (x y : ⋀[R]^n M), F x y = B.sesqExteriorPower n x y) ∧
      (∀ {p q : ℕ}, p ≠ q → ∀ (x : ⋀[R]^p M) (y : ⋀[R]^q M), F x y = 0) := by
  refine ⟨by rintro rfl; exact ⟨fun _ _ _ ↦ sesqExteriorAlgebra_coe_coe B _ _,
      fun hpq x y ↦ B.sesqExteriorAlgebra_eq_zero_of_mem_exteriorPower_of_ne hpq x.2 y.2⟩,
    fun ⟨hsame, hne⟩ ↦ ?_⟩
  refine LinearMap.ext fun s ↦ LinearMap.ext fun t ↦ ?_
  induction s using DirectSum.Decomposition.inductionOn fun p ↦ ⋀[R]^p M with
  | zero => simp
  | add s₁ s₂ hs₁ hs₂ => simp [hs₁, hs₂]
  | @homogeneous p s =>
    induction t using DirectSum.Decomposition.inductionOn fun q ↦ ⋀[R]^q M with
    | zero => simp
    | add t₁ t₂ ht₁ ht₂ => simp [ht₁, ht₂]
    | @homogeneous q t =>
      rcases eq_or_ne p q with rfl | hpq
      · rw [hsame, sesqExteriorAlgebra_coe_coe]
      · rw [hne hpq, B.sesqExteriorAlgebra_eq_zero_of_mem_exteriorPower_of_ne hpq s.2 t.2]

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
    rw [eq_sesqExteriorAlgebra_iff]
    refine ⟨fun n x y ↦ ?_, fun hpq x y ↦ ?_⟩
    · simp only [LinearMap.compl₂_apply, LinearMap.comp_apply, AlgHom.toLinearMap_apply,
        ← exteriorPower.coe_map, sesqExteriorAlgebra_coe_coe, sesqExteriorPower_map_map hf]
    · simp only [LinearMap.compl₂_apply, LinearMap.comp_apply, AlgHom.toLinearMap_apply,
        ← exteriorPower.coe_map]
      exact B'.sesqExteriorAlgebra_eq_zero_of_mem_exteriorPower_of_ne hpq
        (Subtype.prop _) (Subtype.prop _)
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
    simp only [LinearMap.comp_apply, LinearMap.compl₂_apply]
    rw [← LinearMap.compAlternatingMap_apply (LinearMap.mulLeft R (_root_.ExteriorAlgebra.ι R x)),
      ← _root_.ExteriorAlgebra.ιMulti_succ_curryLeft, AlternatingMap.curryLeft_apply_apply]
    rcases q with _ | q
    · rw [B.sesqExteriorAlgebra_eq_zero_of_mem_exteriorPower_of_ne (Nat.succ_ne_zero p)
          (_root_.ExteriorAlgebra.ιMulti_range R (p + 1) ⟨_, rfl⟩)
          (_root_.ExteriorAlgebra.ιMulti_range R 0 ⟨v, rfl⟩),
        contractLeft_eq_zero_of_mem_exteriorPower_zero (B x)
          (_root_.ExteriorAlgebra.ιMulti_range R 0 ⟨v, rfl⟩), map_zero]
    · rcases eq_or_ne p q with rfl | hpq
      · rw [sesqExteriorAlgebra_ιMulti_ιMulti, Matrix.det_succ_row_zero, contractLeft_ιMulti,
          map_sum]
        refine Finset.sum_congr rfl fun j _ ↦ ?_
        have hsub : (Matrix.of fun i k : Fin (p + 1) ↦
            B (Matrix.vecCons x u i) (v k)).submatrix Fin.succ j.succAbove =
              Matrix.of fun i k ↦ B (u i) (j.removeNth v k) := by
          ext i k
          simp [Fin.removeNth_apply]
        rw [map_smul, sesqExteriorAlgebra_ιMulti_ιMulti, smul_eq_mul, hsub]
        simp only [Matrix.of_apply, Matrix.cons_val_zero]
      · rw [B.sesqExteriorAlgebra_eq_zero_of_mem_exteriorPower_of_ne (by omega)
            (_root_.ExteriorAlgebra.ιMulti_range R (p + 1) ⟨_, rfl⟩)
            (_root_.ExteriorAlgebra.ιMulti_range R (q + 1) ⟨v, rfl⟩),
          B.sesqExteriorAlgebra_eq_zero_of_mem_exteriorPower_of_ne hpq
            (_root_.ExteriorAlgebra.ιMulti_range R p ⟨u, rfl⟩)
            (contractLeft_mem_exteriorPower (B x)
              (_root_.ExteriorAlgebra.ιMulti_range R (q + 1) ⟨v, rfl⟩))]
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
    simp only [LinearMap.comp_apply, LinearMap.compl₂_apply]
    rw [← LinearMap.compAlternatingMap_apply (LinearMap.mulLeft R (_root_.ExteriorAlgebra.ι R x)),
      ← _root_.ExteriorAlgebra.ιMulti_succ_curryLeft, AlternatingMap.curryLeft_apply_apply]
    rcases p with _ | p
    · rw [B.sesqExteriorAlgebra_eq_zero_of_mem_exteriorPower_of_ne (Nat.zero_ne_add_one q)
          (_root_.ExteriorAlgebra.ιMulti_range R 0 ⟨u, rfl⟩)
          (_root_.ExteriorAlgebra.ιMulti_range R (q + 1) ⟨_, rfl⟩),
        contractLeft_eq_zero_of_mem_exteriorPower_zero (B x)
          (_root_.ExteriorAlgebra.ιMulti_range R 0 ⟨u, rfl⟩), map_zero, LinearMap.zero_apply]
    · rcases eq_or_ne p q with rfl | hpq
      · rw [sesqExteriorAlgebra_ιMulti_ιMulti, Matrix.det_succ_column_zero, contractLeft_ιMulti,
          map_sum, LinearMap.sum_apply]
        refine Finset.sum_congr rfl fun i _ ↦ ?_
        have hsub : (Matrix.of fun j k : Fin (p + 1) ↦
            B (u j) (Matrix.vecCons x v k)).submatrix i.succAbove Fin.succ =
              Matrix.of fun j k ↦ B (i.removeNth u j) (v k) := by
          ext j k; simp [Fin.removeNth_apply]
        rw [map_smulₛₗ, LinearMap.smul_apply, sesqExteriorAlgebra_ιMulti_ιMulti, smul_eq_mul,
          map_mul, map_pow, map_neg, map_one, hB.eq x (u i), hsub]
        simp only [Matrix.of_apply, Matrix.cons_val_zero]
      · rw [B.sesqExteriorAlgebra_eq_zero_of_mem_exteriorPower_of_ne (by omega)
            (_root_.ExteriorAlgebra.ιMulti_range R (p + 1) ⟨u, rfl⟩)
            (_root_.ExteriorAlgebra.ιMulti_range R (q + 1) ⟨_, rfl⟩),
          B.sesqExteriorAlgebra_eq_zero_of_mem_exteriorPower_of_ne hpq
            (contractLeft_mem_exteriorPower (B x)
              (_root_.ExteriorAlgebra.ιMulti_range R (p + 1) ⟨u, rfl⟩))
            (_root_.ExteriorAlgebra.ιMulti_range R q ⟨v, rfl⟩)]
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
      rw [basis_eq_coe_basis b s]
      exact (b.exteriorPower S.card s).2
    have hT : b.ExteriorAlgebra T ∈ ⋀[R]^T.card M := by
      rw [basis_eq_coe_basis b t]
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

/-- **The vacuum is a unit vector**: `H 1 1 = 1` for the `σ`-sesquilinear form making the wedge
basis orthonormal.

Not `@[simp]`: `Matrix.toLinearMapₛₗ₂_apply` already expands the left-hand side. -/
theorem toLinearMapₛₗ₂_apply_one_one (σ : R →+* R) :
    toLinearMapₛₗ₂ σ b.ExteriorAlgebra b.ExteriorAlgebra
      (1 : Matrix (Finset I) (Finset I) R) 1 1 = 1 := by
  rw [toLinearMapₛₗ₂_exteriorAlgebra_one, LinearMap.sesqExteriorAlgebra_one_one]

/-- **Exterior multiplication is adjoint to contraction**: for the `σ`-sesquilinear form `h` making
`b` orthonormal and the form `H` making the wedge basis orthonormal,
`H (x ∧ s) t = H s (h(x, ·) ⌋ t)`. -/
theorem toLinearMapₛₗ₂_ι_mul_left (σ : R →+* R) (x : M) (s t : _root_.ExteriorAlgebra R M) :
    toLinearMapₛₗ₂ σ b.ExteriorAlgebra b.ExteriorAlgebra
        (1 : Matrix (Finset I) (Finset I) R) (_root_.ExteriorAlgebra.ι R x * s) t =
      toLinearMapₛₗ₂ σ b.ExteriorAlgebra b.ExteriorAlgebra
        (1 : Matrix (Finset I) (Finset I) R) s
        (contractLeft (Q := (0 : QuadraticForm R M))
          (toLinearMapₛₗ₂ σ b b (1 : Matrix I I R) x) t) := by
  rw [toLinearMapₛₗ₂_exteriorAlgebra_one, LinearMap.sesqExteriorAlgebra_ι_mul_left]

/-- **Contraction is adjoint to exterior multiplication**: for an involutive ring endomorphism `σ`,
the form `h` making `b` orthonormal, and the form `H` making the wedge basis orthonormal,
`H s (x ∧ t) = H (h(x, ·) ⌋ s) t`. -/
theorem toLinearMapₛₗ₂_ι_mul_right {σ : R →+* R} (hσ : Function.Involutive σ) (x : M)
    (s t : _root_.ExteriorAlgebra R M) :
    toLinearMapₛₗ₂ σ b.ExteriorAlgebra b.ExteriorAlgebra
        (1 : Matrix (Finset I) (Finset I) R) s (_root_.ExteriorAlgebra.ι R x * t) =
      toLinearMapₛₗ₂ σ b.ExteriorAlgebra b.ExteriorAlgebra
        (1 : Matrix (Finset I) (Finset I) R)
        (contractLeft (Q := (0 : QuadraticForm R M))
          (toLinearMapₛₗ₂ σ b b (1 : Matrix I I R) x) s) t := by
  have hB : (toLinearMapₛₗ₂ σ b b (1 : Matrix I I R)).IsSymm :=
    LinearMap.isSymm_def.mpr fun u v ↦ by
      rw [toLinearMapₛₗ₂_one_apply, toLinearMapₛₗ₂_one_apply]
      simp [hσ _, mul_comm]
  rw [toLinearMapₛₗ₂_exteriorAlgebra_one, LinearMap.sesqExteriorAlgebra_ι_mul_right hB]

/-- **The wedge-basis form of `⋀ M` depends only on the form of `M`**: if two finite ordered bases
`b` and `b'` of `M` are orthonormal for the same `σ`-sesquilinear form, then their wedge bases are
orthonormal for the same `σ`-sesquilinear form on `⋀ M`. -/
theorem toLinearMapₛₗ₂_eq_of_toLinearMapₛₗ₂_eq {σ : R →+* R}
    {I' : Type*} [Fintype I'] [LinearOrder I'] (b' : Module.Basis I' R M)
    (h : toLinearMapₛₗ₂ σ b b (1 : Matrix I I R) =
      toLinearMapₛₗ₂ σ b' b' (1 : Matrix I' I' R)) :
    toLinearMapₛₗ₂ σ b.ExteriorAlgebra b.ExteriorAlgebra
        (1 : Matrix (Finset I) (Finset I) R) =
      toLinearMapₛₗ₂ σ b'.ExteriorAlgebra b'.ExteriorAlgebra
        (1 : Matrix (Finset I') (Finset I') R) := by
  rw [toLinearMapₛₗ₂_exteriorAlgebra_one, toLinearMapₛₗ₂_exteriorAlgebra_one, h]

/-- **The adjoint of the degree scaling by `r` is the degree scaling by `σ r`**: for the form `H`
making the wedge basis orthonormal, `H (T_r s) t = H s (T_{σ r} t)`. -/
theorem toLinearMapₛₗ₂_degreeScaling_left (σ : R →+* R) (r : Rˣ)
    (s t : _root_.ExteriorAlgebra R M) :
    toLinearMapₛₗ₂ σ b.ExteriorAlgebra b.ExteriorAlgebra
        (1 : Matrix (Finset I) (Finset I) R) (degreeScaling r s) t =
      toLinearMapₛₗ₂ σ b.ExteriorAlgebra b.ExteriorAlgebra
        (1 : Matrix (Finset I) (Finset I) R) s (degreeScaling (Units.map σ.toMonoidHom r) t) := by
  rw [toLinearMapₛₗ₂_exteriorAlgebra_one, LinearMap.sesqExteriorAlgebra_degreeScaling_left]

/-- **The degree scaling rescales the metric on each exterior power**: for the form `H` making the
wedge basis orthonormal and `s` in the `p`-th exterior power, `H (T_r s) (T_r t)` is
`(σ r * r) ^ p` times `H s t`. -/
theorem toLinearMapₛₗ₂_degreeScaling_degreeScaling_of_mem_exteriorPower (σ : R →+* R) (r : Rˣ)
    {p : ℕ} {s : _root_.ExteriorAlgebra R M} (hs : s ∈ ⋀[R]^p M)
    (t : _root_.ExteriorAlgebra R M) :
    toLinearMapₛₗ₂ σ b.ExteriorAlgebra b.ExteriorAlgebra
        (1 : Matrix (Finset I) (Finset I) R) (degreeScaling r s) (degreeScaling r t) =
      (σ r * r) ^ p * toLinearMapₛₗ₂ σ b.ExteriorAlgebra b.ExteriorAlgebra
        (1 : Matrix (Finset I) (Finset I) R) s t := by
  rw [toLinearMapₛₗ₂_exteriorAlgebra_one,
    LinearMap.sesqExteriorAlgebra_degreeScaling_degreeScaling_of_mem_exteriorPower _ r hs]

end ExteriorAlgebra

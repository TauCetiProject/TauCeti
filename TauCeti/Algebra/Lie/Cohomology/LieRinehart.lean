/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.LieRinehartAlgebra.Defs
public import TauCeti.Algebra.Lie.Cohomology.ChevalleyEilenberg
public import TauCeti.LinearAlgebra.Alternating.RestrictScalars
import TauCeti.Algebra.LieRinehartAlgebra.Basic

/-!
# Lie–Rinehart multilinearity of the Chevalley–Eilenberg operators

Let `(A, L)` be a Lie–Rinehart algebra over a commutative ring `R`. Forgetting the `A`-module
structure on `L` makes `A` a Lie module over `L`, so the Lie derivative `⁅x, ·⁆` and
`TauCeti.LieModule.Cohomology.d R L A n` act on `L [⋀^Fin n]→ₗ[R] A`.

The Leibniz rules of `LieRinehartRing` cancel the non-tensorial derivative terms whenever the input
cochain `ω : L [⋀^Fin n]→ₗ[A] A` is `A`-multilinear, yielding `A`-multilinear operators `lieDeriv`
and `extDeriv`. Because scalar restriction is injective and intertwines `curryLeft`, `lieDeriv`, and
`extDeriv`, Cartan's homotopy formula, the commutator identities, naturality, and `d ∘ d = 0`
transfer directly from `TauCeti.LieModule.Cohomology`.

## Main definitions

* `TauCeti.LieRinehartAlgebra.lieDeriv`: the `A`-multilinear Lie derivative along `x : L`.
* `TauCeti.LieRinehartAlgebra.extDeriv`: the `A`-multilinear Chevalley–Eilenberg differential.

## Main results

* `TauCeti.LieModule.Cohomology.d_smul_apply`: scalar Leibniz expansion of `d R L A n (a • η)`.
* `TauCeti.LieRinehartAlgebra.curryLeft_extDeriv_succ`: Cartan's formula `ι_x d = L_x - d ι_x`.
* `TauCeti.LieRinehartAlgebra.extDeriv_extDeriv`: `d ∘ d = 0` on `A`-multilinear cochains.

## References

* G. S. Rinehart, *Differential forms on general commutative algebras*, Trans. Amer. Math. Soc.
  108 (1963), 195–222, §2.
* K. C. H. Mackenzie, *General theory of Lie groupoids and Lie algebroids*, London Math. Soc.
  Lecture Note Ser. 213, Cambridge University Press (2005), §7.1.
-/

public section

open AlternatingMap Fin

namespace TauCeti

namespace LieModule.Cohomology

/-- **Scalar Leibniz formula** for the Chevalley–Eilenberg differential over a Lie–Rinehart
algebra: multiplying an `R`-cochain `η` by `a : A` adds the alternating sum of derivatives of `a`
paired with `η` on the remaining arguments. -/
theorem d_smul_apply {R A L : Type*} [CommRing R] [CommRing A] [Algebra R A]
    [LieRing L] [LieAlgebra R L] [Module A L] [LieRingModule L A]
    [LieRinehartRing A L] [LieRinehartAlgebra R A L] {n : ℕ} (a : A)
    (η : L [⋀^Fin n]→ₗ[R] A) (v : Fin (n + 1) → L) :
    d R L A n (a • η) v =
      a * d R L A n η v +
        ∑ i : Fin (n + 1), (-1 : ℤ) ^ (i : ℕ) • (⁅v i, a⁆ * η (i.removeNth v)) := by
  cases n with
  | zero =>
    rw [d_zero_apply, d_zero_apply, smul_apply, smul_eq_mul, LieRinehartRing.leibniz_mul_right,
      smul_eq_mul, sum_univ_one, val_zero, pow_zero, one_smul,
      Subsingleton.elim ((0 : Fin 1).removeNth v) ![]]
  | succ m =>
    rw [d_succ_apply, d_succ_apply]
    simp only [smul_apply, smul_eq_mul, LieRinehartRing.leibniz_mul_right, zsmul_add,
      Finset.sum_add_distrib, mul_add, Finset.mul_sum, mul_smul_comm]
    abel

end LieModule.Cohomology

namespace LieRinehartAlgebra

variable (R A L : Type*) [CommRing R] [CommRing A] [Algebra R A]
  [LieRing L] [LieAlgebra R L] [Module A L] [LieRingModule L A]
  [LieRinehartRing A L] [LieRinehartAlgebra R A L]

section LieDeriv

private theorem lie_restrictScalars_update_smul {ι : Type*} [Fintype ι] [DecidableEq ι]
    (x : L) (ω : L [⋀^ι]→ₗ[A] A) (v : ι → L) (j : ι) (a : A) (y : L) :
    ⁅x, ω.restrictScalars R⁆ (Function.update v j (a • y)) =
      a • ⁅x, ω.restrictScalars R⁆ (Function.update v j y) := by
  set u := Function.update v j y
  have hu : Function.update v j (a • y) = Function.update u j (a • u j) := by simp [u]
  rw [hu, smul_eq_mul, AlternatingMap.lie_apply, AlternatingMap.lie_apply]
  simp only [restrictScalars_apply]
  have hω : ω (Function.update u j (a • u j)) = a * ω u := by simp [Function.update_eq_self]
  rw [hω, LieRinehartRing.leibniz_mul_right, smul_eq_mul,
    ← Finset.add_sum_erase _ _ (Finset.mem_univ j),
    ← Finset.add_sum_erase _ _ (Finset.mem_univ j), mul_sub, mul_add]
  have hdiag : ω (Function.update (Function.update u j (a • u j)) j
      ⁅x, Function.update u j (a • u j) j⁆) =
      a * ω (Function.update u j ⁅x, u j⁆) + ⁅x, a⁆ * ω u := by
    rw [Function.update_self, Function.update_idem, LieRinehartRing.leibniz_smul_right,
      ω.map_update_add, ω.map_update_smul, ω.map_update_smul, Function.update_eq_self,
      smul_eq_mul, smul_eq_mul]
  have hoff : ∑ i ∈ Finset.univ.erase j, ω (Function.update (Function.update u j (a • u j)) i
      ⁅x, Function.update u j (a • u j) i⁆) =
      a * ∑ i ∈ Finset.univ.erase j, ω (Function.update u i ⁅x, u i⁆) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i hi ↦ ?_
    have hij : i ≠ j := Finset.ne_of_mem_erase hi
    rw [Function.update_of_ne hij, Function.update_comm hij.symm, ω.map_update_smul, smul_eq_mul]
    congr 2
    exact Function.update_eq_self_iff.2 (Function.update_of_ne hij.symm ⁅x, u i⁆ u).symm
  rw [hdiag, hoff]
  ring

/-- The Lie derivative `L_x` along `x : L` on `A`-multilinear alternating maps `L [⋀^ι]→ₗ[A] A`,
as an `R`-linear endomorphism. -/
def lieDeriv {ι : Type*} [Fintype ι] [I : DecidableEq ι] (x : L) :
    (L [⋀^ι]→ₗ[A] A) →ₗ[R] L [⋀^ι]→ₗ[A] A where
  toFun ω := mkOfUpdateSMul ⁅x, ω.restrictScalars R⁆ fun [I' : DecidableEq ι] v j a y ↦ by
    obtain rfl : I' = I := Subsingleton.elim _ _
    exact lie_restrictScalars_update_smul R A L x ω v j a y
  map_add' ω₁ ω₂ := restrictScalars_injective R <| by simp
  map_smul' r ω := restrictScalars_injective R <| by
    simp only [restrictScalars_mkOfUpdateSMul, restrictScalars_smul]
    exact lie_smul r x (ω.restrictScalars R)

variable {R A L} {ι : Type*} [Fintype ι] [DecidableEq ι]

@[simp] theorem restrictScalars_lieDeriv (x : L) (ω : L [⋀^ι]→ₗ[A] A) :
    (lieDeriv R A L x ω).restrictScalars R = ⁅x, ω.restrictScalars R⁆ :=
  restrictScalars_mkOfUpdateSMul _ _

theorem lieDeriv_apply (x : L) (ω : L [⋀^ι]→ₗ[A] A) (v : ι → L) :
    lieDeriv R A L x ω v = ⁅x, ω v⁆ - ∑ i, ω (Function.update v i ⁅x, v i⁆) := by
  rw [← restrictScalars_apply R, restrictScalars_lieDeriv, AlternatingMap.lie_apply]
  simp only [restrictScalars_apply]

@[simp] theorem lieDeriv_add_left (x y : L) (ω : L [⋀^ι]→ₗ[A] A) :
    lieDeriv R A L (x + y) ω = lieDeriv R A L x ω + lieDeriv R A L y ω :=
  restrictScalars_injective R <| by
    simp only [restrictScalars_add, restrictScalars_lieDeriv]
    exact add_lie x y (ω.restrictScalars R)

@[simp] theorem lieDeriv_const_smul_left (r : R) (x : L) (ω : L [⋀^ι]→ₗ[A] A) :
    lieDeriv R A L (r • x) ω = r • lieDeriv R A L x ω :=
  restrictScalars_injective R <| by
    simp only [restrictScalars_smul, restrictScalars_lieDeriv]
    exact smul_lie r x (ω.restrictScalars R)

@[simp] theorem lieDeriv_zero_left (ω : L [⋀^ι]→ₗ[A] A) : lieDeriv R A L (0 : L) ω = 0 := by
  rw [← zero_smul R (0 : L), lieDeriv_const_smul_left, zero_smul]

/-- The Leibniz rule `L_x (a • ω) = a • L_x ω + ⁅x, a⁆ • ω` for scalar multiplication of cochains
by `a : A`. -/
theorem lieDeriv_smul_right (x : L) (a : A) (ω : L [⋀^ι]→ₗ[A] A) :
    lieDeriv R A L x (a • ω) = a • lieDeriv R A L x ω + ⁅x, a⁆ • ω := by
  ext v
  simp only [lieDeriv_apply, smul_apply, add_apply, smul_eq_mul, LieRinehartRing.leibniz_mul_right,
    ← Finset.mul_sum]
  ring

/-- Cartan's commutator identity `[L_x, ι_y] = ι_⁅x, y⁆` on `A`-multilinear cochains. -/
theorem curryLeft_lieDeriv {n : ℕ} (x : L) (ω : L [⋀^Fin (n + 1)]→ₗ[A] A) (y : L) :
    (lieDeriv R A L x ω).curryLeft y =
      lieDeriv R A L x (ω.curryLeft y) - ω.curryLeft ⁅x, y⁆ :=
  restrictScalars_injective R <| by
    simp [← curryLeft_restrictScalars, AlternatingMap.curryLeft_lie]

/-- The Lie derivative is a representation of `L`: `[L_x, L_y] = L_⁅x, y⁆`. -/
theorem lieDeriv_lieDeriv_sub (x y : L) (ω : L [⋀^ι]→ₗ[A] A) :
    lieDeriv R A L x (lieDeriv R A L y ω) - lieDeriv R A L y (lieDeriv R A L x ω) =
      lieDeriv R A L ⁅x, y⁆ ω :=
  restrictScalars_injective R <| by
    simp only [restrictScalars_sub, restrictScalars_lieDeriv]
    exact sub_eq_iff_eq_add.2 (LieRingModule.leibniz_lie x y (ω.restrictScalars R))

/-- Scalar multiplication in the direction of the Lie derivative:
`(L_{a • x} ω) v = a * (L_x ω) v + ∑ i, (-1)^i ⁅vᵢ, a⁆ * (ι_x ω)(v̂ᵢ)`. -/
theorem lieDeriv_smul_left_apply {n : ℕ} (a : A) (x : L) (ω : L [⋀^Fin (n + 1)]→ₗ[A] A)
    (v : Fin (n + 1) → L) :
    lieDeriv R A L (a • x) ω v =
      a * lieDeriv R A L x ω v +
        ∑ i : Fin (n + 1), (-1 : ℤ) ^ (i : ℕ) • (⁅v i, a⁆ * ω.curryLeft x (i.removeNth v)) := by
  rw [lieDeriv_apply, lieDeriv_apply, LieRinehartRing.lie_smul_eq_mul]
  have hsum :
      ∑ i : Fin (n + 1), ω (Function.update v i ⁅a • x, v i⁆) =
        a * (∑ i : Fin (n + 1), ω (Function.update v i ⁅x, v i⁆)) -
          ∑ i : Fin (n + 1), (-1 : ℤ) ^ (i : ℕ) • (⁅v i, a⁆ * ω.curryLeft x (i.removeNth v)) := by
    simp_rw [LieRinehartRing.leibniz_smul_left, ω.map_update_sub, ω.map_update_smul, smul_eq_mul,
      Finset.sum_sub_distrib, ← Finset.mul_sum]
    refine congrArg _ (Finset.sum_congr rfl fun i _ ↦ ?_)
    rw [← Fin.insertNth_removeNth i x v, ω.map_insertNth, ← curryLeft_apply_apply, mul_smul_comm]
  rw [hsum]
  ring

end LieDeriv

section ExtDeriv

variable {R A L}

private theorem curryLeft_d_restrictScalars_smul {n : ℕ} (ω : L [⋀^Fin n]→ₗ[A] A) (a : A) (x : L) :
    (LieModule.Cohomology.d R L A n (ω.restrictScalars R)).curryLeft (a • x) =
      a • (LieModule.Cohomology.d R L A n (ω.restrictScalars R)).curryLeft x := by
  cases n with
  | zero =>
    ext v
    obtain rfl : v = ![] := Subsingleton.elim v ![]
    simp [LieModule.Cohomology.curryLeft_d_zero, AlternatingMap.lie_apply]
  | succ m =>
    have hcurry : (ω.restrictScalars R).curryLeft (a • x) = a • (ω.restrictScalars R).curryLeft x :=
      ext fun w ↦ by simp [Matrix.vecCons]
    rw [LieModule.Cohomology.curryLeft_d_succ, LieModule.Cohomology.curryLeft_d_succ, hcurry,
      ← restrictScalars_lieDeriv (a • x) ω, ← restrictScalars_lieDeriv x ω]
    ext v
    simp only [sub_apply, smul_apply, smul_eq_mul, LieModule.Cohomology.d_smul_apply,
      restrictScalars_apply, lieDeriv_smul_left_apply, curryLeft_restrictScalars]
    ring

variable (R A L)

/-- The Chevalley–Eilenberg differential `(L [⋀^Fin n]→ₗ[A] A) →ₗ[R] L [⋀^Fin (n + 1)]→ₗ[A] A` of a
Lie–Rinehart algebra `(A, L)` over `R`. -/
def extDeriv (n : ℕ) : (L [⋀^Fin n]→ₗ[A] A) →ₗ[R] L [⋀^Fin (n + 1)]→ₗ[A] A where
  toFun ω := mkOfCurryLeftSMul (LieModule.Cohomology.d R L A n (ω.restrictScalars R))
    (curryLeft_d_restrictScalars_smul ω)
  map_add' _ _ := restrictScalars_injective R <| by simp
  map_smul' _ _ := restrictScalars_injective R <| by simp

variable {R A L}

@[simp] theorem restrictScalars_extDeriv (n : ℕ) (ω : L [⋀^Fin n]→ₗ[A] A) :
    (extDeriv R A L n ω).restrictScalars R =
      LieModule.Cohomology.d R L A n (ω.restrictScalars R) :=
  restrictScalars_mkOfCurryLeftSMul _ _

/-- In degree zero, `(d ω)(x) = ⁅x, ω ![]⁆`. -/
@[simp] theorem extDeriv_zero_apply (ω : L [⋀^Fin 0]→ₗ[A] A) (v : Fin 1 → L) :
    extDeriv R A L 0 ω v = ⁅v 0, ω ![]⁆ := by
  rw [← restrictScalars_apply R, restrictScalars_extDeriv, LieModule.Cohomology.d_zero_apply,
    restrictScalars_apply]

/-- **The Chevalley–Eilenberg formula** for `A`-multilinear cochains of positive degree. -/
theorem extDeriv_succ_apply {n : ℕ} (ω : L [⋀^Fin (n + 1)]→ₗ[A] A) (v : Fin (n + 2) → L) :
    extDeriv R A L (n + 1) ω v =
      ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) • ⁅v i, ω (i.removeNth v)⁆ +
        ∑ i : Fin (n + 1), ∑ j ≥ i, (-1 : ℤ) ^ (i + j + 1 : ℕ) •
          ω (Matrix.vecCons ⁅v i.castSucc, v j.succ⁆ (j.removeNth (i.castSucc.removeNth v))) := by
  rw [← restrictScalars_apply R, restrictScalars_extDeriv, LieModule.Cohomology.d_succ_apply]
  simp only [restrictScalars_apply]

/-- Cartan's formula in degree zero: `ι_x (d ω) = L_x ω`. -/
@[simp] theorem curryLeft_extDeriv_zero (ω : L [⋀^Fin 0]→ₗ[A] A) (x : L) :
    (extDeriv R A L 0 ω).curryLeft x = lieDeriv R A L x ω :=
  restrictScalars_injective R <| by simp [← curryLeft_restrictScalars]

/-- **Cartan's formula** `ι_x (d ω) = L_x ω - d (ι_x ω)` on `A`-multilinear cochains. -/
@[simp] theorem curryLeft_extDeriv_succ {n : ℕ} (ω : L [⋀^Fin (n + 1)]→ₗ[A] A) (x : L) :
    (extDeriv R A L (n + 1) ω).curryLeft x =
      lieDeriv R A L x ω - extDeriv R A L n (ω.curryLeft x) :=
  restrictScalars_injective R <| by simp [← curryLeft_restrictScalars]

/-- The differential commutes with the Lie derivative: `L_x (d ω) = d (L_x ω)`. -/
@[simp] theorem lieDeriv_extDeriv (n : ℕ) (x : L) (ω : L [⋀^Fin n]→ₗ[A] A) :
    lieDeriv R A L x (extDeriv R A L n ω) = extDeriv R A L n (lieDeriv R A L x ω) :=
  restrictScalars_injective R <| by simp

/-- The Chevalley–Eilenberg differential of a Lie–Rinehart algebra squares to zero. -/
@[simp] theorem extDeriv_extDeriv (n : ℕ) (ω : L [⋀^Fin n]→ₗ[A] A) :
    extDeriv R A L (n + 1) (extDeriv R A L n ω) = 0 :=
  restrictScalars_injective R <| by simp

theorem extDeriv_comp_extDeriv (n : ℕ) : extDeriv R A L (n + 1) ∘ₗ extDeriv R A L n = 0 :=
  LinearMap.ext (extDeriv_extDeriv n)

/-- Scalar Leibniz rule for `extDeriv` evaluated on a tuple of elements of `L`. -/
theorem extDeriv_smul_apply {n : ℕ} (a : A) (ω : L [⋀^Fin n]→ₗ[A] A) (v : Fin (n + 1) → L) :
    extDeriv R A L n (a • ω) v =
      a * extDeriv R A L n ω v +
        ∑ i : Fin (n + 1), (-1 : ℤ) ^ (i : ℕ) • (⁅v i, a⁆ * ω (i.removeNth v)) := by
  rw [← restrictScalars_apply R, restrictScalars_extDeriv, restrictScalars_smul,
    LieModule.Cohomology.d_smul_apply, ← restrictScalars_extDeriv]
  simp only [restrictScalars_apply]

end ExtDeriv

end LieRinehartAlgebra

end TauCeti

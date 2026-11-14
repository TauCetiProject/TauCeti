/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.LieRinehartAlgebra.Defs
public import TauCeti.Algebra.Lie.Cohomology.ChevalleyEilenberg
public import TauCeti.LinearAlgebra.Alternating.RestrictScalars

/-!
# Lie–Rinehart multilinearity of the Chevalley–Eilenberg operators

Let `(A, L)` be a Lie–Rinehart algebra over a commutative ring `R`. Forgetting the `A`-module
structure on `L` makes `A` a Lie module over the `R`-Lie algebra `L`, so the Lie derivative
`⁅x, ·⁆` and the Chevalley–Eilenberg differential `TauCeti.LieModule.Cohomology.d R L A n` act on
`R`-multilinear alternating maps `L [⋀^Fin n]→ₗ[R] A`.

The Leibniz rules of `LieRinehartRing` cancel the non-tensorial derivative terms whenever the input
cochain `ω : L [⋀^Fin n]→ₗ[A] A` is `A`-multilinear:
* For any `x : L`, `⁅x, ω.restrictScalars R⁆` is `A`-multilinear (`lieDeriv`).
* On any `R`-multilinear `η : L [⋀^Fin n]→ₗ[R] A`, `d R L A n (a • η)` satisfies the Leibniz rule
  with respect to `a : A` (`d_smul_apply`).
* Combining this Leibniz rule with Cartan's formula `ι_x d = L_x - d ι_x` cancels the scalar
  derivatives in `(d R L A n (ω.restrictScalars R)).curryLeft (a • x)`, proving that `d` preserves
  `A`-multilinearity (`extDeriv`).

Because scalar restriction `(L [⋀^Fin n]→ₗ[A] A) → (L [⋀^Fin n]→ₗ[R] A)` is injective and
intertwines `curryLeft`, `lieDeriv`, and `extDeriv`, Cartan's homotopy formula, the commutator
identities `[L_x, ι_y] = ι_{[x, y]}` and `[L_x, L_y] = L_{[x, y]}`, naturality `[L_x, d] = 0`, and
`d ∘ d = 0` transfer directly from `TauCeti.LieModule.Cohomology`.

## Main definitions

* `TauCeti.LieRinehartAlgebra.lieDeriv`: the `A`-multilinear Lie derivative along `x : L` on
  `L [⋀^ι]→ₗ[A] A`.
* `TauCeti.LieRinehartAlgebra.extDeriv`: the `A`-multilinear Chevalley–Eilenberg differential
  `(L [⋀^Fin n]→ₗ[A] A) →ₗ[R] L [⋀^Fin (n + 1)]→ₗ[A] A`.

## Main results

* `TauCeti.LieModule.Cohomology.d_smul_apply`: the scalar Leibniz expansion of `d R L A n (a • η)`.
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

section LieRinehartRing

variable {A L : Type*} [CommRing A] [LieRing L] [Module A L] [LieRingModule L A]
  [LieRinehartRing A L]

/-- The Leibniz rule in the first slot of the Lie bracket of a Lie–Rinehart ring:
`⁅a • x, y⁆ = a • ⁅x, y⁆ - ⁅y, a⁆ • x`. -/
theorem LieRinehartRing.leibniz_smul_left (a : A) (x y : L) :
    ⁅a • x, y⁆ = a • ⁅x, y⁆ - ⁅y, a⁆ • x := by
  rw [← lie_skew (a • x) y, LieRinehartRing.leibniz_smul_right, neg_add, ← smul_neg,
    lie_skew x y, sub_eq_add_neg]

end LieRinehartRing

namespace LieModule.Cohomology

variable {R A L : Type*} [CommRing R] [CommRing A] [Algebra R A]
  [LieRing L] [LieAlgebra R L] [Module A L] [LieRingModule L A]
  [LieRinehartRing A L] [LieRinehartAlgebra R A L]

/-- **Scalar Leibniz formula** for the Chevalley–Eilenberg differential over a Lie–Rinehart
algebra: multiplying an `R`-cochain `η` by `a : A` adds the alternating sum of derivatives of `a`
paired with `η` on the remaining arguments. -/
theorem d_smul_apply {n : ℕ} (a : A) (η : L [⋀^Fin n]→ₗ[R] A) (v : Fin (n + 1) → L) :
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
      Finset.sum_add_distrib, mul_add]
    have h1 :
        ∑ i : Fin (m + 2), (-1 : ℤ) ^ (i : ℕ) • (a * ⁅v i, η (i.removeNth v)⁆) =
          a * ∑ i : Fin (m + 2), (-1 : ℤ) ^ (i : ℕ) • ⁅v i, η (i.removeNth v)⁆ := by
      simp_rw [Finset.mul_sum, mul_smul_comm]
    have h2 :
        ∑ i : Fin (m + 1), ∑ j ≥ i, (-1 : ℤ) ^ (i + j + 1 : ℕ) •
            (a * η (Matrix.vecCons ⁅v i.castSucc, v j.succ⁆
              (j.removeNth (i.castSucc.removeNth v)))) =
          a * ∑ i : Fin (m + 1), ∑ j ≥ i, (-1 : ℤ) ^ (i + j + 1 : ℕ) •
            η (Matrix.vecCons ⁅v i.castSucc, v j.succ⁆
              (j.removeNth (i.castSucc.removeNth v))) := by
      simp_rw [Finset.mul_sum, mul_smul_comm]
    rw [h1, h2]
    abel

end LieModule.Cohomology

namespace LieRinehartAlgebra

variable (R A L : Type*) [CommRing R] [CommRing A] [Algebra R A]
  [LieRing L] [LieAlgebra R L] [Module A L] [LieRingModule L A]
  [LieRinehartRing A L] [LieRinehartAlgebra R A L]

section LieDeriv

/-- On an `A`-multilinear alternating map `ω`, the Lie derivative `⁅x, ω.restrictScalars R⁆`
remains `A`-multilinear: the scalar derivative from `⁅x, a * ω u⁆` cancels the scalar derivative
from `⁅x, a • y⁆` in the updated slot. -/
private theorem lie_restrictScalars_update_smul {ι : Type*} [Fintype ι] [DecidableEq ι]
    (x : L) (ω : L [⋀^ι]→ₗ[A] A) (v : ι → L) (j : ι) (a : A) (y : L) :
    ⁅x, ω.restrictScalars R⁆ (Function.update v j (a • y)) =
      a • ⁅x, ω.restrictScalars R⁆ (Function.update v j y) := by
  let u := Function.update v j y
  have hu_smul : Function.update v j (a • y) = Function.update u j (a • u j) := by
    simp [u]
  have hu_self : Function.update v j y = u := rfl
  rw [hu_smul, hu_self, smul_eq_mul, AlternatingMap.lie_apply, AlternatingMap.lie_apply]
  have hval : ⁅x, (ω.restrictScalars R) (Function.update u j (a • u j))⁆ =
      a * ⁅x, ω u⁆ + ⁅x, a⁆ * ω u := by
    have hω : ω (Function.update u j (a • u j)) = a * ω u := by
      simp [Function.update_eq_self]
    rw [restrictScalars_apply, hω, LieRinehartRing.leibniz_mul_right, smul_eq_mul]
  have hsum :
      ∑ i : ι, (ω.restrictScalars R)
          (Function.update (Function.update u j (a • u j)) i
            ⁅x, Function.update u j (a • u j) i⁆) =
        a * (∑ i : ι, ω (Function.update u i ⁅x, u i⁆)) + ⁅x, a⁆ * ω u := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j),
      ← Finset.add_sum_erase _ _ (Finset.mem_univ j), mul_add]
    have hdiag :
        (ω.restrictScalars R)
            (Function.update (Function.update u j (a • u j)) j
              ⁅x, Function.update u j (a • u j) j⁆) =
          a * ω (Function.update u j ⁅x, u j⁆) + ⁅x, a⁆ * ω u := by
      rw [restrictScalars_apply, Function.update_self, Function.update_idem,
        LieRinehartRing.leibniz_smul_right, ω.map_update_add, ω.map_update_smul, ω.map_update_smul,
        Function.update_eq_self, smul_eq_mul, smul_eq_mul]
    have hoff :
        ∑ i ∈ Finset.univ.erase j, (ω.restrictScalars R)
            (Function.update (Function.update u j (a • u j)) i
              ⁅x, Function.update u j (a • u j) i⁆) =
          a * ∑ i ∈ Finset.univ.erase j, ω (Function.update u i ⁅x, u i⁆) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i hi ↦ ?_
      have hij : i ≠ j := Finset.ne_of_mem_erase hi
      rw [restrictScalars_apply, Function.update_of_ne hij, Function.update_comm hij.symm,
        ω.map_update_smul, smul_eq_mul]
      congr 2
      exact Function.update_eq_self_iff.2 (Function.update_of_ne hij.symm ⁅x, u i⁆ u).symm
    rw [hdiag, hoff]
    ring
  rw [hval, hsum, restrictScalars_apply]
  simp only [restrictScalars_apply]
  ring

/-- The Lie derivative `L_x` along `x : L` on `A`-multilinear alternating maps `L [⋀^ι]→ₗ[A] A`,
as an `R`-linear endomorphism. -/
def lieDeriv {ι : Type*} [Fintype ι] [I : DecidableEq ι] (x : L) :
    (L [⋀^ι]→ₗ[A] A) →ₗ[R] L [⋀^ι]→ₗ[A] A where
  toFun ω := mkOfUpdateSMul ⁅x, ω.restrictScalars R⁆ fun [I' : DecidableEq ι] v j a y ↦ by
    obtain rfl : I' = I := Subsingleton.elim _ _
    exact lie_restrictScalars_update_smul R A L x ω v j a y
  map_add' ω₁ ω₂ := restrictScalars_injective R
    (LieRingModule.lie_add x (ω₁.restrictScalars R) (ω₂.restrictScalars R))
  map_smul' r ω := restrictScalars_injective R (LieModule.lie_smul r x (ω.restrictScalars R))

variable {R A L}

@[simp]
theorem restrictScalars_lieDeriv {ι : Type*} [Fintype ι] [DecidableEq ι]
    (x : L) (ω : L [⋀^ι]→ₗ[A] A) :
    (lieDeriv R A L x ω).restrictScalars R = ⁅x, ω.restrictScalars R⁆ :=
  (rfl)

theorem lieDeriv_apply {ι : Type*} [Fintype ι] [DecidableEq ι]
    (x : L) (ω : L [⋀^ι]→ₗ[A] A) (v : ι → L) :
    lieDeriv R A L x ω v = ⁅x, ω v⁆ - ∑ i, ω (Function.update v i ⁅x, v i⁆) :=
  AlternatingMap.lie_apply x (ω.restrictScalars R) v

@[simp]
theorem lieDeriv_zero_left {ι : Type*} [Fintype ι] [DecidableEq ι] (ω : L [⋀^ι]→ₗ[A] A) :
    lieDeriv R A L (0 : L) ω = 0 :=
  restrictScalars_injective R <|
    (AddMonoidHom.mk' (fun x : L ↦ ⁅x, ω.restrictScalars R⁆)
      fun x y ↦ LieRingModule.add_lie x y (ω.restrictScalars R)).map_zero

@[simp]
theorem lieDeriv_add_left {ι : Type*} [Fintype ι] [DecidableEq ι]
    (x y : L) (ω : L [⋀^ι]→ₗ[A] A) :
    lieDeriv R A L (x + y) ω = lieDeriv R A L x ω + lieDeriv R A L y ω :=
  restrictScalars_injective R (LieRingModule.add_lie x y (ω.restrictScalars R))

@[simp]
theorem lieDeriv_smul_const_left {ι : Type*} [Fintype ι] [DecidableEq ι]
    (r : R) (x : L) (ω : L [⋀^ι]→ₗ[A] A) :
    lieDeriv R A L (r • x) ω = r • lieDeriv R A L x ω :=
  restrictScalars_injective R (LieModule.smul_lie r x (ω.restrictScalars R))

/-- The Leibniz rule `L_x (a • ω) = a • L_x ω + ⁅x, a⁆ • ω` for scalar multiplication of cochains
by `a : A`. -/
theorem lieDeriv_smul_right {ι : Type*} [Fintype ι] [DecidableEq ι]
    (x : L) (a : A) (ω : L [⋀^ι]→ₗ[A] A) :
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
    rw [← curryLeft_restrictScalars, restrictScalars_lieDeriv, AlternatingMap.curryLeft_lie,
      restrictScalars_sub, restrictScalars_lieDeriv]
    simp only [curryLeft_restrictScalars]

/-- The Lie derivative is a representation of `L`: `[L_x, L_y] = L_⁅x, y⁆`. -/
theorem lieDeriv_lieDeriv_sub {ι : Type*} [Fintype ι] [DecidableEq ι]
    (x y : L) (ω : L [⋀^ι]→ₗ[A] A) :
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
    congr 1
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [← Fin.insertNth_removeNth i x v, ω.map_insertNth, ← curryLeft_apply_apply, mul_smul_comm]
  rw [hsum]
  ring

end LieDeriv

section ExtDeriv

variable {R A L}

/-- The interior product of `d (ω.restrictScalars R)` is `A`-linear whenever `ω` is
`A`-multilinear. -/
private theorem curryLeft_d_restrictScalars_smul {n : ℕ} (ω : L [⋀^Fin n]→ₗ[A] A) (a : A) (x : L) :
    (LieModule.Cohomology.d R L A n (ω.restrictScalars R)).curryLeft (a • x) =
      a • (LieModule.Cohomology.d R L A n (ω.restrictScalars R)).curryLeft x := by
  cases n with
  | zero =>
    ext v
    have hv : v = ![] := Subsingleton.elim v ![]
    subst hv
    simp [LieModule.Cohomology.curryLeft_d_zero, AlternatingMap.lie_apply]
  | succ m =>
    ext v
    have hcurry :
        (ω.restrictScalars R).curryLeft (a • x) = a • (ω.restrictScalars R).curryLeft x := by
      ext w
      simp only [curryLeft_restrictScalars, restrictScalars_apply, curryLeft_apply_apply,
        smul_apply]
      simpa [Matrix.vecCons] using ω.map_vecCons_smul w a x
    rw [LieModule.Cohomology.curryLeft_d_succ, LieModule.Cohomology.curryLeft_d_succ,
      sub_apply, smul_apply, sub_apply, smul_eq_mul, hcurry,
      LieModule.Cohomology.d_smul_apply]
    have hL₁ : ⁅a • x, ω.restrictScalars R⁆ v = lieDeriv R A L (a • x) ω v := (rfl)
    have hL₂ : ⁅x, ω.restrictScalars R⁆ v = lieDeriv R A L x ω v := (rfl)
    rw [hL₁, hL₂, lieDeriv_smul_left_apply]
    simp only [curryLeft_restrictScalars, restrictScalars_apply]
    ring

variable (R A L)

/-- The Chevalley–Eilenberg differential `(L [⋀^Fin n]→ₗ[A] A) →ₗ[R] L [⋀^Fin (n + 1)]→ₗ[A] A` of a
Lie–Rinehart algebra `(A, L)` over `R`. -/
def extDeriv (n : ℕ) : (L [⋀^Fin n]→ₗ[A] A) →ₗ[R] L [⋀^Fin (n + 1)]→ₗ[A] A where
  toFun ω := mkOfCurryLeftSMul (LieModule.Cohomology.d R L A n (ω.restrictScalars R))
    (curryLeft_d_restrictScalars_smul ω)
  map_add' ω₁ ω₂ := restrictScalars_injective R <| by simp
  map_smul' r ω := restrictScalars_injective R <| by simp

variable {R A L}

@[simp]
theorem restrictScalars_extDeriv (n : ℕ) (ω : L [⋀^Fin n]→ₗ[A] A) :
    (extDeriv R A L n ω).restrictScalars R =
      LieModule.Cohomology.d R L A n (ω.restrictScalars R) :=
  (rfl)

/-- In degree zero, `(d ω)(x) = ⁅x, ω ![]⁆`. -/
@[simp]
theorem extDeriv_zero_apply (ω : L [⋀^Fin 0]→ₗ[A] A) (v : Fin 1 → L) :
    extDeriv R A L 0 ω v = ⁅v 0, ω ![]⁆ :=
  LieModule.Cohomology.d_zero_apply (ω.restrictScalars R) v

/-- **The Chevalley–Eilenberg formula** for `A`-multilinear cochains of positive degree. -/
theorem extDeriv_succ_apply {n : ℕ} (ω : L [⋀^Fin (n + 1)]→ₗ[A] A) (v : Fin (n + 2) → L) :
    extDeriv R A L (n + 1) ω v =
      ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) • ⁅v i, ω (i.removeNth v)⁆ +
        ∑ i : Fin (n + 1), ∑ j ≥ i, (-1 : ℤ) ^ (i + j + 1 : ℕ) •
          ω (Matrix.vecCons ⁅v i.castSucc, v j.succ⁆ (j.removeNth (i.castSucc.removeNth v))) :=
  LieModule.Cohomology.d_succ_apply (ω.restrictScalars R) v

/-- Cartan's formula in degree zero: `ι_x (d ω) = L_x ω`. -/
@[simp]
theorem curryLeft_extDeriv_zero (ω : L [⋀^Fin 0]→ₗ[A] A) (x : L) :
    (extDeriv R A L 0 ω).curryLeft x = lieDeriv R A L x ω :=
  restrictScalars_injective R <| by
    rw [← curryLeft_restrictScalars, restrictScalars_extDeriv,
      LieModule.Cohomology.curryLeft_d_zero, restrictScalars_lieDeriv]

/-- **Cartan's formula** `ι_x (d ω) = L_x ω - d (ι_x ω)` on `A`-multilinear cochains. -/
@[simp]
theorem curryLeft_extDeriv_succ {n : ℕ} (ω : L [⋀^Fin (n + 1)]→ₗ[A] A) (x : L) :
    (extDeriv R A L (n + 1) ω).curryLeft x =
      lieDeriv R A L x ω - extDeriv R A L n (ω.curryLeft x) :=
  restrictScalars_injective R <| by
    rw [← curryLeft_restrictScalars, restrictScalars_extDeriv,
      LieModule.Cohomology.curryLeft_d_succ, restrictScalars_sub, restrictScalars_lieDeriv,
      restrictScalars_extDeriv, curryLeft_restrictScalars]

/-- The differential commutes with the Lie derivative: `L_x (d ω) = d (L_x ω)`. -/
@[simp]
theorem lieDeriv_extDeriv (n : ℕ) (x : L) (ω : L [⋀^Fin n]→ₗ[A] A) :
    lieDeriv R A L x (extDeriv R A L n ω) = extDeriv R A L n (lieDeriv R A L x ω) :=
  restrictScalars_injective R <| by simp

/-- The Chevalley–Eilenberg differential of a Lie–Rinehart algebra squares to zero. -/
@[simp]
theorem extDeriv_extDeriv (n : ℕ) (ω : L [⋀^Fin n]→ₗ[A] A) :
    extDeriv R A L (n + 1) (extDeriv R A L n ω) = 0 :=
  restrictScalars_injective R <| by simp

theorem extDeriv_comp_extDeriv (n : ℕ) :
    extDeriv R A L (n + 1) ∘ₗ extDeriv R A L n = 0 :=
  LinearMap.ext (extDeriv_extDeriv n)

/-- Scalar Leibniz rule for `extDeriv` evaluated on a tuple of elements of `L`. -/
theorem extDeriv_smul_apply {n : ℕ} (a : A) (ω : L [⋀^Fin n]→ₗ[A] A) (v : Fin (n + 1) → L) :
    extDeriv R A L n (a • ω) v =
      a * extDeriv R A L n ω v +
        ∑ i : Fin (n + 1), (-1 : ℤ) ^ (i : ℕ) • (⁅v i, a⁆ * ω (i.removeNth v)) :=
  LieModule.Cohomology.d_smul_apply a (ω.restrictScalars R) v

end ExtDeriv

end LieRinehartAlgebra

end TauCeti

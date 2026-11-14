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
# The Chevalley–Eilenberg complex of a Lie–Rinehart algebra

Let `(A, L)` be a Lie–Rinehart algebra over a commutative ring `R`. Forgetting the `A`-module
structure on `L` leaves a Lie algebra `L` over `R` acting on `A`, together with its
Chevalley–Eilenberg complex `TauCeti.LieModule.Cohomology.cochainComplex R L A` of `R`-multilinear
alternating cochains `L [⋀^Fin n]→ₗ[R] A`. Because the Lie bracket on `L` and the action of `L` on
`A` satisfy the Lie–Rinehart Leibniz rules, both the Lie derivative `⁅x, ·⁆` and the
Chevalley–Eilenberg differential preserve the `R`-submodule of `A`-multilinear alternating cochains
`L [⋀^Fin n]→ₗ[A] A` (embedded via `AlternatingMap.restrictScalars R`).

We do not register a `Bracket L (L [⋀^ι]→ₗ[A] A)` instance: when `L` is an `A`-Lie algebra with
trivial anchor, `AlternatingMap.instBracket` already equips `L [⋀^ι]→ₗ[A] A` with a bracket over
`A`, and the two brackets agree only as `R`-linear maps while traversing different typeclass paths.
Instead, `TauCeti.LieRinehartAlgebra.lieDeriv` exposes the Lie derivative as an explicit `R`-linear
map.

The construction adapts the inductive Cartan-calculus presentation of
`TauCeti.Algebra.Lie.Cohomology.ChevalleyEilenberg` by restricting the Lie-algebra operators along
`AlternatingMap.restrictScalars`.

## Main definitions

* `TauCeti.LieRinehartAlgebra.lieDeriv`: the Lie derivative `L_x` on `A`-multilinear alternating
  cochains `L [⋀^ι]→ₗ[A] A`, bundled as an `R`-bilinear map.
* `TauCeti.LieRinehartAlgebra.d`: the Rinehart Chevalley–Eilenberg differential
  `(L [⋀^Fin n]→ₗ[A] A) →ₗ[R] L [⋀^Fin (n + 1)]→ₗ[A] A`.
* `TauCeti.LieRinehartAlgebra.cochainComplex`: the Chevalley–Eilenberg cochain complex of `(A, L)`
  in `ModuleCat R`.
* `TauCeti.LieRinehartAlgebra.restrictScalarsChainMap`: the chain map embedding the Lie–Rinehart
  cochain complex into the Lie-algebra Chevalley–Eilenberg complex of `L` with coefficients in `A`.
* `TauCeti.LieRinehartAlgebra.cohomology`: the `n`-th Lie–Rinehart cohomology `H^n(L; A)`.

## Main results

* `TauCeti.LieRinehartAlgebra.curryLeft_lieDeriv`: `[L_x, ι_y] = ι_{[x, y]}`.
* `TauCeti.LieRinehartAlgebra.lieDeriv_lie`: `[L_x, L_y] = L_{[x, y]}`.
* `TauCeti.LieRinehartAlgebra.curryLeft_d_succ`: Cartan's formula `ι_x d ω = L_x ω - d (ι_x ω)`.
* `TauCeti.LieRinehartAlgebra.lieDeriv_d`: `L_x (d ω) = d (L_x ω)`.
* `TauCeti.LieRinehartAlgebra.d_d`: `d (d ω) = 0`.
* `TauCeti.LieRinehartAlgebra.d_one_apply`, `TauCeti.LieRinehartAlgebra.d_succ_apply`: the explicit
  Chevalley–Eilenberg formula in degree `1` and in arbitrary positive degree.

## References

* G. S. Rinehart, *Differential forms on general commutative algebras*, Trans. Amer. Math. Soc.
  108 (1963), 195–222.
* C. Chevalley and S. Eilenberg, *Cohomology theory of Lie groups and Lie algebras*, Trans. Amer.
  Math. Soc. 63 (1948), 85–124.
* J. Huebschmann, *Poisson cohomology and quantization*, J. Reine Angew. Math. 408 (1990), 57–113.
-/

public section

open AlternatingMap Function

namespace TauCeti.LieRinehartAlgebra

variable (R A L : Type*) [CommRing R] [CommRing A] [Algebra R A]
  [LieRing L] [LieAlgebra R L] [Module A L] [LieRingModule L A]
  [LieRinehartRing A L] [LieRinehartAlgebra R A L]

section LieDeriv

variable {R A L}

/-- The Lie-algebra action `⁅x, ω.restrictScalars R⁆` on an `A`-multilinear alternating cochain `ω`
remains `A`-linear in each argument: the derivative `⁅x, a⁆ * ω w` produced by the Leibniz rule on
values cancels the `⁅x, a⁆ • w i` term produced by the Leibniz rule in the `i`-th slot. -/
private theorem lie_restrictScalars_map_update_smul {ι : Type*} [Fintype ι] [DecidableEq ι]
    (x : L) (ω : L [⋀^ι]→ₗ[A] A) (v : ι → L) (i : ι) (a : A) (y : L) :
    ⁅x, ω.restrictScalars R⁆ (update v i (a • y)) =
      a • ⁅x, ω.restrictScalars R⁆ (update v i y) := by
  let w : ι → L := update v i y
  have hw_eq : update v i (a • y) = update w i (a • w i) := by
    simp [w]
  have hself : update w i (w i) = w := update_eq_self i w
  -- In slot `i`, the Lie–Rinehart Leibniz rule produces an extra `⁅x, a⁆ * ω w` term.
  have hterm_eq :
      ω (update (update w i (a • w i)) i ⁅x, update w i (a • w i) i⁆) =
        a • ω (update w i ⁅x, w i⁆) + ⁅x, a⁆ * ω w := by
    rw [update_self, update_idem, LieRinehartRing.leibniz_smul_right, ω.map_update_add,
      ω.map_update_smul, ω.map_update_smul, hself, smul_eq_mul, smul_eq_mul]
  -- In every other slot `j ≠ i`, the scalar `a` factors out directly by `A`-linearity in slot `i`.
  have hterm_ne (j : ι) (hj : j ≠ i) :
      ω (update (update w i (a • w i)) j ⁅x, update w i (a • w i) j⁆) =
        a • ω (update w j ⁅x, w j⁆) := by
    have hcomm :
        update (update w i (a • w i)) j ⁅x, w j⁆ =
          update (update w j ⁅x, w j⁆) i (a • update w j ⁅x, w j⁆ i) := by
      rw [update_of_ne hj.symm, update_comm hj.symm]
    rw [update_of_ne hj, hcomm, ω.map_update_smul, update_eq_self]
  have hsum :
      ∑ j : ι, ω (update (update w i (a • w i)) j ⁅x, update w i (a • w i) j⁆) =
        a • (∑ j : ι, ω (update w j ⁅x, w j⁆)) + ⁅x, a⁆ * ω w := by
    rw [← Finset.insert_erase (Finset.mem_univ i), Finset.sum_insert (Finset.notMem_erase i _),
      Finset.sum_insert (Finset.notMem_erase i _), hterm_eq,
      Finset.sum_congr rfl fun j hj ↦ hterm_ne j (Finset.ne_of_mem_erase hj),
      ← Finset.smul_sum, smul_add]
    abel
  rw [hw_eq, AlternatingMap.lie_apply, AlternatingMap.lie_apply]
  simp only [restrictScalars_apply]
  rw [ω.map_update_smul, hself, smul_eq_mul, LieRinehartRing.leibniz_mul_right, hsum, smul_sub]
  abel

variable (R A L)

/-- The Lie derivative `L_x` on `A`-multilinear alternating cochains `L [⋀^ι]→ₗ[A] A` of a
Lie–Rinehart algebra `(A, L)` over `R`, bundled as an `R`-bilinear map. -/
def lieDeriv {ι : Type*} [Fintype ι] [DecidableEq ι] :
    L →ₗ[R] (L [⋀^ι]→ₗ[A] A) →ₗ[R] L [⋀^ι]→ₗ[A] A where
  toFun x :=
    { toFun ω :=
        { toFun := ⇑⁅x, ω.restrictScalars R⁆
          map_update_add' := fun [_] m i y₁ y₂ ↦ by
            convert ⁅x, ω.restrictScalars R⁆.map_update_add m i y₁ y₂
          map_update_smul' := fun [_] m i c y ↦ by
            convert lie_restrictScalars_map_update_smul (R := R) x ω m i c y
          map_eq_zero_of_eq' := ⁅x, ω.restrictScalars R⁆.map_eq_zero_of_eq' }
      map_add' ω₁ ω₂ := by ext v; simp
      map_smul' c ω := by
        ext v
        change ⁅x, (c • ω).restrictScalars R⁆ v = c • ⁅x, ω.restrictScalars R⁆ v
        simp [Finset.smul_sum, smul_sub] }
  map_add' x y := by ext ω v; simp [Finset.sum_add_distrib]; abel
  map_smul' c x := by ext ω v; simp [Finset.smul_sum, smul_sub]

variable {R A L}

@[simp]
theorem restrictScalars_lieDeriv {ι : Type*} [Fintype ι] [DecidableEq ι]
    (x : L) (ω : L [⋀^ι]→ₗ[A] A) :
    (lieDeriv R A L x ω).restrictScalars R = ⁅x, ω.restrictScalars R⁆ := by
  ext v
  simp [lieDeriv]

@[simp]
theorem lieDeriv_apply {ι : Type*} [Fintype ι] [DecidableEq ι]
    (x : L) (ω : L [⋀^ι]→ₗ[A] A) (v : ι → L) :
    lieDeriv R A L x ω v = ⁅x, ω v⁆ - ∑ i, ω (update v i ⁅x, v i⁆) := by
  have h := AlternatingMap.lie_apply x (ω.restrictScalars R) v
  simp only [← restrictScalars_lieDeriv, restrictScalars_apply] at h
  exact h

/-- The Lie derivative is a Lie algebra representation: `L_{[x, y]} = L_x ∘ L_y - L_y ∘ L_x`. -/
theorem lieDeriv_lie {ι : Type*} [Fintype ι] [DecidableEq ι]
    (x y : L) (ω : L [⋀^ι]→ₗ[A] A) :
    lieDeriv R A L ⁅x, y⁆ ω =
      lieDeriv R A L x (lieDeriv R A L y ω) - lieDeriv R A L y (lieDeriv R A L x ω) := by
  refine restrictScalars_injective R ?_
  rw [restrictScalars_sub, restrictScalars_lieDeriv, restrictScalars_lieDeriv,
    restrictScalars_lieDeriv, restrictScalars_lieDeriv, restrictScalars_lieDeriv,
    LieRingModule.leibniz_lie x y (ω.restrictScalars R)]
  abel

/-- Commutation of the Lie derivative with interior product: `[L_x, ι_y] = ι_{[x, y]}`. -/
theorem curryLeft_lieDeriv {n : ℕ} (x : L) (ω : L [⋀^Fin (n + 1)]→ₗ[A] A) (y : L) :
    (lieDeriv R A L x ω).curryLeft y =
      lieDeriv R A L x (ω.curryLeft y) - ω.curryLeft ⁅x, y⁆ := by
  refine restrictScalars_injective R ?_
  rw [← curryLeft_restrictScalars, restrictScalars_lieDeriv, curryLeft_lie,
    restrictScalars_sub, curryLeft_restrictScalars, restrictScalars_lieDeriv,
    curryLeft_restrictScalars]

end LieDeriv

section Differential

variable {R A L}

/-- The Lie-algebra Chevalley–Eilenberg differential `LieModule.Cohomology.d R L A n` preserves
`A`-multilinearity: in degree `0` this is `LieRinehartRing.lie_smul_eq_mul`, in positive degrees
slots `j.succ` follow inductively from Cartan's formula `ι_x d = L_x - d ι_x`, and slot `0` follows
from slot `1` by alternation. -/
private theorem d_restrictScalars_map_update_smul :
    ∀ (n : ℕ) (ω : L [⋀^Fin n]→ₗ[A] A) (v : Fin (n + 1) → L) (i : Fin (n + 1)) (a : A) (y : L),
      LieModule.Cohomology.d R L A n (ω.restrictScalars R) (update v i (a • y)) =
        a • LieModule.Cohomology.d R L A n (ω.restrictScalars R) (update v i y)
  | 0, ω, v, i, a, y => by
    obtain rfl : i = 0 := Fin.eq_zero i
    simp [LieModule.Cohomology.d_zero_apply]
  | n + 1, ω, v, i, a, y => by
    -- Build the `A`-multilinear differential in degree `n` from the induction hypothesis.
    let D (η : L [⋀^Fin n]→ₗ[A] A) : L [⋀^Fin (n + 1)]→ₗ[A] A :=
      { toFun := ⇑(LieModule.Cohomology.d R L A n (η.restrictScalars R))
        map_update_add' := fun [_] m k x₁ x₂ ↦
          (LieModule.Cohomology.d R L A n (η.restrictScalars R)).map_update_add m k x₁ x₂
        map_update_smul' := fun [_] m k c x ↦ by
          convert d_restrictScalars_map_update_smul n η m k c x
        map_eq_zero_of_eq' :=
          (LieModule.Cohomology.d R L A n (η.restrictScalars R)).map_eq_zero_of_eq' }
    have hsucc (u : Fin (n + 2) → L) (j : Fin (n + 1)) (z : L) :
        LieModule.Cohomology.d R L A (n + 1) (ω.restrictScalars R) (update u j.succ (a • z)) =
          a • LieModule.Cohomology.d R L A (n + 1) (ω.restrictScalars R) (update u j.succ z) := by
      have hcons (w : L) :
          update u j.succ w = Matrix.vecCons (u 0) (update (Fin.tail u) j w) := by
        ext r
        refine Fin.cases ?_ (fun s ↦ ?_) r
        · simp [Matrix.vecCons, update_of_ne (Fin.succ_ne_zero j).symm]
        · by_cases hs : s = j <;> simp [hs, Matrix.vecCons, Fin.tail]
      -- After inserting `u 0`, Cartan's formula expresses `d ω` via two `A`-multilinear maps.
      let ψ : L [⋀^Fin (n + 1)]→ₗ[A] A := lieDeriv R A L (u 0) ω - D (ω.curryLeft (u 0))
      have hψ (r : Fin (n + 1) → L) :
          LieModule.Cohomology.d R L A (n + 1) (ω.restrictScalars R) (Matrix.vecCons (u 0) r) =
            ψ r := by
        rw [← curryLeft_apply_apply, LieModule.Cohomology.curryLeft_d_succ, sub_apply,
          ← restrictScalars_lieDeriv, restrictScalars_apply, curryLeft_restrictScalars]
        simp only [ψ, sub_apply]
        rfl
      rw [hcons, hcons, hψ, hψ]
      exact ψ.map_update_smul (Fin.tail u) j a z
    refine Fin.cases ?_ (fun j ↦ hsucc v j y) i
    -- Slot `0` reduces to slot `1 = (0 : Fin (n + 1)).succ` by swapping the first two arguments.
    have h01 : (0 : Fin (n + 2)) ≠ 1 := Fin.zero_ne_one
    have hswap (z : L) :
        update v 0 z ∘ Equiv.swap (0 : Fin (n + 2)) 1 =
          update (v ∘ Equiv.swap 0 1) ((0 : Fin (n + 1)).succ) z := by
      ext r
      by_cases hr0 : r = 0
      · subst hr0; simp [Equiv.swap_apply_left]
      · by_cases hr1 : r = 1
        · subst hr1; simp [Equiv.swap_apply_right]
        · simp [Equiv.swap_apply_of_ne_of_ne hr0 hr1, hr0, hr1]
    set F := LieModule.Cohomology.d R L A (n + 1) (ω.restrictScalars R)
    apply neg_injective
    rw [← F.map_swap (update v 0 (a • y)) h01, hswap, hsucc (v ∘ Equiv.swap 0 1) 0 y, ← hswap,
      F.map_swap (update v 0 y) h01, smul_neg]

variable (R A L)

/-- The Chevalley–Eilenberg differential of a Lie–Rinehart algebra `(A, L)` over `R`, sending
`A`-multilinear alternating `n`-cochains to `(n + 1)`-cochains. -/
def d (n : ℕ) : (L [⋀^Fin n]→ₗ[A] A) →ₗ[R] L [⋀^Fin (n + 1)]→ₗ[A] A where
  toFun ω :=
    { toFun := ⇑(LieModule.Cohomology.d R L A n (ω.restrictScalars R))
      map_update_add' := fun [_] m k x₁ x₂ ↦
        (LieModule.Cohomology.d R L A n (ω.restrictScalars R)).map_update_add m k x₁ x₂
      map_update_smul' := fun [_] m k c x ↦ by
        convert d_restrictScalars_map_update_smul (R := R) n ω m k c x
      map_eq_zero_of_eq' :=
        (LieModule.Cohomology.d R L A n (ω.restrictScalars R)).map_eq_zero_of_eq' }
  map_add' ω₁ ω₂ := by
    ext v
    simp
  map_smul' c ω := by
    ext v
    change LieModule.Cohomology.d R L A n ((c • ω).restrictScalars R) v =
      c • LieModule.Cohomology.d R L A n (ω.restrictScalars R) v
    rw [restrictScalars_smul, map_smul]
    rfl

variable {R A L}

@[simp]
theorem restrictScalars_d (n : ℕ) (ω : L [⋀^Fin n]→ₗ[A] A) :
    (d R A L n ω).restrictScalars R = LieModule.Cohomology.d R L A n (ω.restrictScalars R) := by
  ext v
  simp [d]

/-- Cartan's formula in degree zero: `ι_x (d ω) = L_x ω`. -/
@[simp]
theorem curryLeft_d_zero (ω : L [⋀^Fin 0]→ₗ[A] A) (x : L) :
    (d R A L 0 ω).curryLeft x = lieDeriv R A L x ω := by
  refine restrictScalars_injective R ?_
  rw [← curryLeft_restrictScalars, restrictScalars_d, LieModule.Cohomology.curryLeft_d_zero,
    restrictScalars_lieDeriv]

/-- **Cartan's magic formula** `ι_x (d ω) = L_x ω - d (ι_x ω)` for a Lie–Rinehart algebra. -/
@[simp]
theorem curryLeft_d_succ {n : ℕ} (ω : L [⋀^Fin (n + 1)]→ₗ[A] A) (x : L) :
    (d R A L (n + 1) ω).curryLeft x = lieDeriv R A L x ω - d R A L n (ω.curryLeft x) := by
  refine restrictScalars_injective R ?_
  rw [← curryLeft_restrictScalars, restrictScalars_d, LieModule.Cohomology.curryLeft_d_succ,
    restrictScalars_sub, restrictScalars_lieDeriv, restrictScalars_d, curryLeft_restrictScalars]

/-- Cartan's magic formula solved for the Lie derivative: `L_x ω = ι_x (d ω) + d (ι_x ω)`. -/
theorem lieDeriv_eq_curryLeft_d_add_d_curryLeft {n : ℕ} (x : L)
    (ω : L [⋀^Fin (n + 1)]→ₗ[A] A) :
    lieDeriv R A L x ω = (d R A L (n + 1) ω).curryLeft x + d R A L n (ω.curryLeft x) := by
  rw [curryLeft_d_succ, sub_add_cancel]

/-- Scaling the differentiating element by `a : A` in degree `0` scales the Lie derivative. -/
@[simp]
theorem lieDeriv_smul_left_zero (a : A) (x : L) (ω : L [⋀^Fin 0]→ₗ[A] A) :
    lieDeriv R A L (a • x) ω = a • lieDeriv R A L x ω := by
  rw [← curryLeft_d_zero, map_smul, curryLeft_d_zero]

/-- Scaling the differentiating element by `a : A` in positive degree satisfies
`L_{a • x} ω = a • ι_x (d ω) + d (a • ι_x ω)`. -/
theorem lieDeriv_smul_left_succ {n : ℕ} (a : A) (x : L) (ω : L [⋀^Fin (n + 1)]→ₗ[A] A) :
    lieDeriv R A L (a • x) ω =
      a • (d R A L (n + 1) ω).curryLeft x + d R A L n (a • ω.curryLeft x) := by
  rw [lieDeriv_eq_curryLeft_d_add_d_curryLeft, map_smul, map_smul]

/-- The Lie–Rinehart differential in degree zero evaluates the anchor action `⁅v 0, ω ![]⁆`. -/
@[simp]
theorem d_zero_apply (ω : L [⋀^Fin 0]→ₗ[A] A) (v : Fin 1 → L) :
    d R A L 0 ω v = ⁅v 0, ω ![]⁆ := by
  have h := LieModule.Cohomology.d_zero_apply (ω.restrictScalars R) v
  rwa [← restrictScalars_d, restrictScalars_apply, restrictScalars_apply] at h

/-- Evaluating `d` on the constant `0`-cochain of `a : A` gives the anchor derivative `⁅v 0, a⁆`. -/
theorem d_zero_constOfIsEmpty (a : A) (v : Fin 1 → L) :
    d R A L 0 (AlternatingMap.constOfIsEmpty A L (Fin 0) a) v = ⁅v 0, a⁆ := by
  simp

/-- **The Chevalley–Eilenberg formula** in arbitrary positive degree for a Lie–Rinehart algebra:
`(d ω)(v₀, …, vₙ₊₁) = ∑ i, (-1)^i ⁅vᵢ, ω(…, v̂ᵢ, …)⁆`
`  + ∑_{i ≤ j} (-1)^(i + j + 1) ω(⁅v_{i.castSucc}, v_{j.succ}⁆, …)`. -/
theorem d_succ_apply {n : ℕ} (ω : L [⋀^Fin (n + 1)]→ₗ[A] A) (v : Fin (n + 2) → L) :
    d R A L (n + 1) ω v =
      ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) • ⁅v i, ω (i.removeNth v)⁆ +
        ∑ i : Fin (n + 1), ∑ j ≥ i, (-1 : ℤ) ^ (i + j + 1 : ℕ) •
          ω (Matrix.vecCons ⁅v i.castSucc, v j.succ⁆ (j.removeNth (i.castSucc.removeNth v))) := by
  have h := LieModule.Cohomology.d_succ_apply (ω.restrictScalars R) v
  simp only [← restrictScalars_d, restrictScalars_apply] at h
  exact h

/-- The degree-`1` Chevalley–Eilenberg formula `(d ω)(x, y) = ⁅x, ω(y)⁆ - ⁅y, ω(x)⁆ - ω(⁅x, y⁆)`. -/
theorem d_one_apply (ω : L [⋀^Fin 1]→ₗ[A] A) (x y : L) :
    d R A L 1 ω ![x, y] = ⁅x, ω ![y]⁆ - ⁅y, ω ![x]⁆ - ω ![⁅x, y⁆] := by
  have hy : update ![y] 0 ⁅x, y⁆ = ![⁅x, y⁆] := by ext i; fin_cases i; rfl
  rw [← curryLeft_apply_apply, curryLeft_d_succ, sub_apply, lieDeriv_apply, d_zero_apply,
    Fin.sum_univ_one]
  simp only [Matrix.cons_val_zero, curryLeft_apply_apply, hy]
  abel_nf

/-- The Lie derivative commutes with the differential: `L_x (d ω) = d (L_x ω)`. -/
@[simp]
theorem lieDeriv_d (n : ℕ) (x : L) (ω : L [⋀^Fin n]→ₗ[A] A) :
    lieDeriv R A L x (d R A L n ω) = d R A L n (lieDeriv R A L x ω) := by
  refine restrictScalars_injective R ?_
  rw [restrictScalars_lieDeriv, restrictScalars_d, restrictScalars_d, restrictScalars_lieDeriv,
    LieModule.Cohomology.lie_d]

/-- The Chevalley–Eilenberg differential of a Lie–Rinehart algebra squares to zero. -/
@[simp]
theorem d_d (n : ℕ) (ω : L [⋀^Fin n]→ₗ[A] A) : d R A L (n + 1) (d R A L n ω) = 0 := by
  refine restrictScalars_injective R ?_
  rw [restrictScalars_d, restrictScalars_d, restrictScalars_zero, LieModule.Cohomology.d_d]

variable (R A L) in
/-- The Chevalley–Eilenberg differential squares to zero as a composite of `R`-linear maps. -/
theorem d_comp_d (n : ℕ) : d R A L (n + 1) ∘ₗ d R A L n = 0 :=
  LinearMap.ext (d_d (R := R) n)

end Differential

/-! ### The cochain complex and Lie–Rinehart cohomology -/

/-- The Chevalley–Eilenberg cochain complex of a Lie–Rinehart algebra `(A, L)` over `R`, with
degree-`n` cochains `L [⋀^Fin n]→ₗ[A] A`. -/
@[expose] noncomputable def cochainComplex : CochainComplex (ModuleCat R) ℕ :=
  CochainComplex.of (fun n ↦ ModuleCat.of R (L [⋀^Fin n]→ₗ[A] A))
    (fun n ↦ ModuleCat.ofHom (d R A L n)) fun n ↦ by
      rw [← ModuleCat.ofHom_comp, d_comp_d, ModuleCat.ofHom_zero]

@[simp]
theorem cochainComplex_X (n : ℕ) :
    (cochainComplex R A L).X n = ModuleCat.of R (L [⋀^Fin n]→ₗ[A] A) :=
  (rfl)

@[simp]
theorem cochainComplex_d_succ (n : ℕ) :
    (cochainComplex R A L).d n (n + 1) = ModuleCat.ofHom (d R A L n) := by
  simp [cochainComplex]

/-- Scalar restriction from `A`-multilinear to `R`-multilinear cochains as a cochain map from the
Lie–Rinehart Chevalley–Eilenberg complex to the Lie-algebra Chevalley–Eilenberg complex of `L` with
coefficients in `A`. -/
noncomputable def restrictScalarsChainMap :
    cochainComplex R A L ⟶ LieModule.Cohomology.cochainComplex R L A where
  f n := ModuleCat.ofHom (AlternatingMap.restrictScalarsLM R R)
  comm' := by
    rintro n _ rfl
    dsimp [cochainComplex, LieModule.Cohomology.cochainComplex]
    rw [CochainComplex.of_d, CochainComplex.of_d, ← ModuleCat.ofHom_comp, ← ModuleCat.ofHom_comp]
    congr 1
    ext ω v
    simp

@[simp]
theorem restrictScalarsChainMap_f (n : ℕ) :
    (restrictScalarsChainMap R A L).f n =
      ModuleCat.ofHom (AlternatingMap.restrictScalarsLM R R) :=
  (rfl)

/-- The `n`-th Lie–Rinehart cohomology `H^n(L; A)` of `(A, L)` over `R`. -/
noncomputable abbrev cohomology (n : ℕ) : ModuleCat R :=
  (cochainComplex R A L).homology n

end TauCeti.LieRinehartAlgebra

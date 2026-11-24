/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps
public import Mathlib.Analysis.Normed.Operator.Mul
public import TauCeti.Topology.Algebra.Module.Alternating.Wedge.Assoc
import TauCeti.Logic.Equiv.Fin.Basic

/-!
# Wedge powers of real alternating forms

For a real continuous alternating form `φ` of degree `k`, the wedge power
`ContinuousAlternatingMap.wedgePow φ m` is the form `φ ∧ ⋯ ∧ φ` of degree `k * m`, with `m`
factors, for the real wedge `ContinuousAlternatingMap.pairedWedge` along multiplication. The empty
power is the constant `0`-form `1`.

For a two-form `ω`, inserting a vector into a wedge power obeys the power rule

`ι_v (ω ^ (m + 1)) = (m + 1) • (ι_v ω ∧ ω ^ m)`

(`ContinuousAlternatingMap.wedgePow_succ_apply_vecCons`), which follows from the antiderivation
rule of the interior product together with associativity and graded commutativity of the wedge. It
computes the top power of `ω` on a standard family: if vectors `qᵢ, pᵢ` satisfy
`ω(qᵢ, qⱼ) = 0` and `ω(qᵢ, pⱼ) = δᵢⱼ`, then `ω ^ m` takes the value `m!` on
`(q₀, p₀, q₁, p₁, …)` (`ContinuousAlternatingMap.wedgePow_apply_finProdFinEquiv`). Applied to a
Darboux basis this is the classical normalization of the symplectic volume form `ωⁿ / n!`.

After a one-form `a`, a wedge power of a two-form `B` does not change when a two-form `b ∧ a`
divisible by `a` is added to `B`: `a ∧ (B + b ∧ a)ᵐ = a ∧ Bᵐ`, because every additional term
contains `a` twice (`ContinuousAlternatingMap.pairedWedge_wedgePow_add_pairedWedge`). Since
`d (f α) = f dα + df ∧ α`, this is the linear algebra behind the scaling law
`(f α) ∧ (d (f α))ᵐ = f ^ (m + 1) • α ∧ (dα)ᵐ` of the contact volume form.

## Main definitions

* `ContinuousAlternatingMap.wedgePow φ m`: the `m`-th wedge power of a real alternating form.

## Main results

* `ContinuousAlternatingMap.wedgePow_one_apply`: the first power of a form is the form itself.
* `ContinuousAlternatingMap.wedgePow_compContinuousLinearMap`: wedge powers commute with
  pullback along continuous linear maps.
* `ContinuousAlternatingMap.wedgePow_smul`: `(c φ) ^ m = c ^ m φ ^ m`.
* `ContinuousAlternatingMap.wedgePow_succ_apply_vecCons`: the power rule for inserting a vector
  into a wedge power of a two-form.
* `ContinuousAlternatingMap.curryLeftTopological_wedgePow_succ_eq_zero`: a vector in the kernel
  of a two-form lies in the kernel of each of its positive powers.
* `ContinuousAlternatingMap.wedgePow_apply_finProdFinEquiv`: the `m`-th power of a two-form takes
  the value `m!` on a family of `m` standard pairs.
* `ContinuousAlternatingMap.pairedWedge_wedgePow_add_pairedWedge`: `a ∧ (B + b ∧ a)ᵐ = a ∧ Bᵐ`
  for one-forms `a` and `b` and a two-form `B`.
* `ContinuousAlternatingMap.pairedWedge_smul_wedgePow_smul_add_pairedWedge`: the linear scaling
  law `(c a) ∧ (c B + b ∧ a)ᵐ = c ^ (m + 1) • a ∧ Bᵐ` behind the contact volume form.

## References

* John M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Graduate Texts in Mathematics 218,
  Springer, 2013, Chapter 14 (the wedge product and Lemma 14.13 on interior products).
* D. McDuff and D. Salamon, *Introduction to Symplectic Topology*, 3rd ed., Oxford University
  Press, 2017, Chapter 3 (the volume form `ωⁿ / n!`).
-/

public section

noncomputable section

open TauCeti

namespace ContinuousAlternatingMap

variable {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]

/-! ### Wedge powers -/

/-- The `m`-th wedge power `φ ∧ ⋯ ∧ φ` of a real alternating form `φ` of degree `k`, a form of
degree `k * m`. The empty power is the constant `0`-form `1`, and `φ ^ (m + 1) = φ ^ m ∧ φ`. -/
def wedgePow {k : ℕ} (φ : E [⋀^Fin k]→L[ℝ] ℝ) : (m : ℕ) → E [⋀^Fin (k * m)]→L[ℝ] ℝ
  | 0 => constOfIsEmpty ℝ E (Fin 0) 1
  | m + 1 => pairedWedge (ContinuousLinearMap.mul ℝ ℝ) (ContinuousLinearMap.mul ℝ ℝ).continuous₂
      (wedgePow φ m) φ

variable {k : ℕ}

/-- The empty wedge power is the constant `0`-form `1`. -/
@[simp]
theorem wedgePow_zero_apply (φ : E [⋀^Fin k]→L[ℝ] ℝ) (v : Fin 0 → E) :
    DFunLike.coe (F := E [⋀^Fin 0]→L[ℝ] ℝ) (wedgePow φ 0) v = 1 := (rfl)

/-- The successor wedge power is the previous power wedged with the form. -/
theorem wedgePow_succ (φ : E [⋀^Fin k]→L[ℝ] ℝ) (m : ℕ) :
    wedgePow φ (m + 1) = pairedWedge (ContinuousLinearMap.mul ℝ ℝ)
      (ContinuousLinearMap.mul ℝ ℝ).continuous₂ (wedgePow φ m) φ := (rfl)

/-- The first wedge power of a form `φ` of degree `k` evaluates as `φ` itself, once the input
family is reindexed along `k * 1 = k`. -/
@[simp]
theorem wedgePow_one_apply (φ : E [⋀^Fin k]→L[ℝ] ℝ) (v : Fin (k * 1) → E) :
    wedgePow φ 1 v = φ (v ∘ Fin.cast (Nat.mul_one k).symm) := by
  rw [wedgePow_succ, pairedWedge_apply_zero_left, wedgePow_zero_apply,
    ContinuousLinearMap.mul_apply', one_mul]

/-- Wedge powers commute with pullback along continuous linear maps. -/
@[simp]
theorem wedgePow_compContinuousLinearMap {E' : Type*} [AddCommGroup E'] [Module ℝ E']
    [TopologicalSpace E'] (φ : E [⋀^Fin k]→L[ℝ] ℝ) (f : E' →L[ℝ] E) (m : ℕ) :
    (wedgePow φ m).compContinuousLinearMap f = wedgePow (φ.compContinuousLinearMap f) m := by
  induction m with
  | zero => ext v; rfl
  | succ m ih => rw [wedgePow_succ, wedgePow_succ, pairedWedge_compContinuousLinearMap, ih]

/-- Scalars come out of a wedge power raised to the number of factors: `(c φ) ^ m = c ^ m φ ^ m`. -/
@[simp]
theorem wedgePow_smul (c : ℝ) (φ : E [⋀^Fin k]→L[ℝ] ℝ) (m : ℕ) :
    wedgePow (c • φ) m = (c ^ m) • wedgePow φ m := by
  induction m with
  | zero => rw [pow_zero, one_smul]; rfl
  | succ m ih =>
    rw [wedgePow_succ, wedgePow_succ, ih, pairedWedge_smul_left, pairedWedge_smul_right, smul_smul,
      pow_succ]

/-! ### The power rule for two-forms -/

/-- **The power rule for interior products.** Inserting a vector `v` into the `(m + 1)`-th wedge
power of a two-form `ω` gives `(m + 1) • (ι_v ω ∧ ω ^ m)`:
`ω ^ (m + 1) (v, w) = (m + 1) * (ι_v ω ∧ ω ^ m) (w)`. -/
theorem wedgePow_succ_apply_vecCons (ω : E [⋀^Fin 2]→L[ℝ] ℝ) (m : ℕ) (v : E)
    (w : Fin (2 * m + 1) → E) :
    wedgePow ω (m + 1) (Matrix.vecCons v w) =
      (m + 1) * pairedWedge (ContinuousLinearMap.mul ℝ ℝ)
        (ContinuousLinearMap.mul ℝ ℝ).continuous₂ (curryLeftTopological (n := 1) ω v)
        (wedgePow ω m) (w ∘ Fin.cast (Nat.add_comm 1 (2 * m))) := by
  induction m with
  | zero =>
    rw [wedgePow_succ, pairedWedge_apply_zero_left, pairedWedge_apply_zero_right]
    simp only [ContinuousLinearMap.mul_apply', curryLeftTopological_apply_apply,
      wedgePow_zero_apply, Nat.cast_zero, zero_add, one_mul, mul_one]
    -- The two tuples differ only by value-preserving `Fin.cast`s.
    congr 1
  | succ m ih =>
    rw [wedgePow_succ, ← curryLeftTopological_apply_apply (n := 2 * m + 1 + 1 + 1),
      curryLeftTopological_pairedWedge (k := 2 * m + 1) (l := 1),
      pairedWedge_apply_of_left_eq_smul_cast _ _ (Nat.add_comm 1 (2 * m)) ((m : ℝ) + 1)
        (fun w ↦ by rw [curryLeftTopological_apply_apply, ih, smul_eq_mul]),
      pairedWedge_assoc (ContinuousLinearMap.mul ℝ ℝ) (ContinuousLinearMap.mul ℝ ℝ)
        (ContinuousLinearMap.mul ℝ ℝ) (ContinuousLinearMap.mul ℝ ℝ)
        (ContinuousLinearMap.mul ℝ ℝ).continuous₂ (ContinuousLinearMap.mul ℝ ℝ).continuous₂
        (ContinuousLinearMap.mul ℝ ℝ).continuous₂ (ContinuousLinearMap.mul ℝ ℝ).continuous₂
        (fun a b c ↦ by simp [mul_assoc]),
      pairedWedge_comm _ (fun a b ↦ mul_comm a b) (wedgePow ω (m + 1))]
    have h₁ : (-1 : ℝ) ^ (2 * m + 1 + 1) = 1 := Even.neg_one_pow ⟨m + 1, by ring⟩
    have h₂ : (-1 : ℝ) ^ (2 * (m + 1) * 1) = 1 := Even.neg_one_pow ⟨m + 1, by ring⟩
    simp only [h₁, h₂, ← wedgePow_succ, Function.comp_def, Fin.cast_cast, one_smul]
    -- The remaining summands agree up to the definitional equality `2 * m + 2 = 2 * (m + 1)` of
    -- the degree of `ω ^ (m + 1)`, which `ring` does not see through.
    have key (a b : ℝ) (hab : a = b) : ((m : ℝ) + 1) * a + b = ((m + 1 : ℕ) + 1 : ℝ) * b := by
      subst hab
      push_cast
      ring
    exact key _ _ rfl

/-- If `ω(v, w) = 0` for every `w`, then the interior product of `v` with every positive power of
`ω` vanishes. -/
theorem curryLeftTopological_wedgePow_succ_eq_zero (ω : E [⋀^Fin 2]→L[ℝ] ℝ) (m : ℕ) {v : E}
    (hv : ∀ w, ω ![v, w] = 0) :
    curryLeftTopological (n := 2 * m + 1) (ω.wedgePow (m + 1)) v = 0 := by
  have h₀ : curryLeftTopological (n := 1) ω v = 0 := by
    ext u
    rw [curryLeftTopological_apply_apply, coe_zero, Pi.zero_apply, ← hv (u 0)]
    congr 1
    ext i
    fin_cases i <;> rfl
  ext w
  rw [curryLeftTopological_apply_apply, coe_zero, Pi.zero_apply]
  refine (wedgePow_succ_apply_vecCons ω m v w).trans ?_
  rw [h₀, pairedWedge_zero_left, coe_zero, Pi.zero_apply, mul_zero]

/-! ### Wedge powers after a covector -/

/-- The real wedge is associative, read with the reindexing on the right-hand side. -/
private theorem pairedWedge_mul_assoc_apply {k l m : ℕ} (φ : E [⋀^Fin k]→L[ℝ] ℝ)
    (ψ : E [⋀^Fin l]→L[ℝ] ℝ) (χ : E [⋀^Fin m]→L[ℝ] ℝ) (v : Fin (k + (l + m)) → E) :
    pairedWedge (ContinuousLinearMap.mul ℝ ℝ) (ContinuousLinearMap.mul ℝ ℝ).continuous₂ φ
        (pairedWedge (ContinuousLinearMap.mul ℝ ℝ) (ContinuousLinearMap.mul ℝ ℝ).continuous₂ ψ χ)
        v =
      pairedWedge (ContinuousLinearMap.mul ℝ ℝ) (ContinuousLinearMap.mul ℝ ℝ).continuous₂
        (pairedWedge (ContinuousLinearMap.mul ℝ ℝ) (ContinuousLinearMap.mul ℝ ℝ).continuous₂ φ ψ)
        χ (v ∘ Fin.cast (Nat.add_assoc k l m)) := by
  rw [pairedWedge_assoc (ContinuousLinearMap.mul ℝ ℝ) (ContinuousLinearMap.mul ℝ ℝ)
    (ContinuousLinearMap.mul ℝ ℝ) (ContinuousLinearMap.mul ℝ ℝ)
    (ContinuousLinearMap.mul ℝ ℝ).continuous₂ (ContinuousLinearMap.mul ℝ ℝ).continuous₂
    (ContinuousLinearMap.mul ℝ ℝ).continuous₂ (ContinuousLinearMap.mul ℝ ℝ).continuous₂
    (fun x y z ↦ by simp [mul_assoc])]
  congr 1

/-- For real one-forms `a` and `b` and any form `Q`, `a ∧ Q ∧ b ∧ a = 0`, because `a` occurs
twice. -/
private theorem pairedWedge_pairedWedge_pairedWedge_eq_zero {p : ℕ}
    (a b : E [⋀^Fin 1]→L[ℝ] ℝ) (Q : E [⋀^Fin p]→L[ℝ] ℝ) :
    pairedWedge (ContinuousLinearMap.mul ℝ ℝ) (ContinuousLinearMap.mul ℝ ℝ).continuous₂ a
      (pairedWedge (ContinuousLinearMap.mul ℝ ℝ) (ContinuousLinearMap.mul ℝ ℝ).continuous₂ Q
        (pairedWedge (ContinuousLinearMap.mul ℝ ℝ) (ContinuousLinearMap.mul ℝ ℝ).continuous₂
          b a)) = 0 := by
  have haa := pairedWedge_self_eq_zero_of_odd (ContinuousLinearMap.mul ℝ ℝ).continuous₂
    mul_comm odd_one a
  -- `(b ∧ a) ∧ a = b ∧ (a ∧ a) = 0`.
  have hba : pairedWedge (ContinuousLinearMap.mul ℝ ℝ) (ContinuousLinearMap.mul ℝ ℝ).continuous₂
      (pairedWedge (ContinuousLinearMap.mul ℝ ℝ) (ContinuousLinearMap.mul ℝ ℝ).continuous₂ b a)
      a = 0 := by
    ext v
    rw [pairedWedge_assoc (ContinuousLinearMap.mul ℝ ℝ) (ContinuousLinearMap.mul ℝ ℝ)
      (ContinuousLinearMap.mul ℝ ℝ) (ContinuousLinearMap.mul ℝ ℝ)
      (ContinuousLinearMap.mul ℝ ℝ).continuous₂ (ContinuousLinearMap.mul ℝ ℝ).continuous₂
      (ContinuousLinearMap.mul ℝ ℝ).continuous₂ (ContinuousLinearMap.mul ℝ ℝ).continuous₂
      (fun x y z ↦ by simp [mul_assoc]), haa, pairedWedge_zero_right]
    rfl
  -- `a ∧ (Q ∧ (b ∧ a)) = ±((b ∧ a) ∧ a) ∧ Q`, up to reindexing the arguments.
  ext v
  rw [pairedWedge_mul_assoc_apply, pairedWedge_comm _ mul_comm, pairedWedge_mul_assoc_apply, hba]
  simp

/-- **Wedge powers after a covector ignore two-forms divisible by it.** For real one-forms `a`
and `b` and a two-form `B`, adding `b ∧ a` to `B` does not change `a ∧ Bᵐ`:
`a ∧ (B + b ∧ a)ᵐ = a ∧ Bᵐ`. No finite dimensionality is needed. -/
theorem pairedWedge_wedgePow_add_pairedWedge {m : ℕ} (a b : E [⋀^Fin 1]→L[ℝ] ℝ)
    (B : E [⋀^Fin 2]→L[ℝ] ℝ) :
    pairedWedge (ContinuousLinearMap.mul ℝ ℝ) (ContinuousLinearMap.mul ℝ ℝ).continuous₂ a
        (wedgePow (B + pairedWedge (ContinuousLinearMap.mul ℝ ℝ)
          (ContinuousLinearMap.mul ℝ ℝ).continuous₂ b a) m) =
      pairedWedge (ContinuousLinearMap.mul ℝ ℝ) (ContinuousLinearMap.mul ℝ ℝ).continuous₂ a
        (wedgePow B m) := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [wedgePow_succ, pairedWedge_add_right, pairedWedge_add_right,
      pairedWedge_pairedWedge_pairedWedge_eq_zero, add_zero, wedgePow_succ]
    ext v
    rw [pairedWedge_mul_assoc_apply, pairedWedge_mul_assoc_apply, ih]

/-- **The linear scaling law of the contact volume form.** For real one-forms `a` and `b`, a
two-form `B` and a scalar `c`,
`(c a) ∧ (c B + b ∧ a)ᵐ = c ^ (m + 1) • a ∧ Bᵐ`.
At a point where `β = f α`, this is `β ∧ (dβ)ᵐ = f ^ (m + 1) • α ∧ (dα)ᵐ`, with `b = df`. -/
theorem pairedWedge_smul_wedgePow_smul_add_pairedWedge (m : ℕ) (c : ℝ)
    (a b : E [⋀^Fin 1]→L[ℝ] ℝ) (B : E [⋀^Fin 2]→L[ℝ] ℝ) :
    pairedWedge (ContinuousLinearMap.mul ℝ ℝ) (ContinuousLinearMap.mul ℝ ℝ).continuous₂ (c • a)
        (wedgePow (c • B + pairedWedge (ContinuousLinearMap.mul ℝ ℝ)
          (ContinuousLinearMap.mul ℝ ℝ).continuous₂ b a) m) =
      c ^ (m + 1) • pairedWedge (ContinuousLinearMap.mul ℝ ℝ)
        (ContinuousLinearMap.mul ℝ ℝ).continuous₂ a (wedgePow B m) := by
  rw [pairedWedge_smul_left, pairedWedge_wedgePow_add_pairedWedge, wedgePow_smul,
    pairedWedge_smul_right, smul_smul, pow_succ']

/-! ### The value on standard pairs -/

/-- **The value of the top power on standard pairs.** If vectors `qᵢ = b (i, 0)` and
`pᵢ = b (i, 1)` satisfy `ω(qᵢ, qⱼ) = 0` and `ω(qᵢ, pⱼ) = δᵢⱼ`, then the `m`-th wedge
power of `ω` takes the value `m!` on `(q₀, p₀, q₁, p₁, …)`. -/
theorem wedgePow_apply_finProdFinEquiv (ω : E [⋀^Fin 2]→L[ℝ] ℝ) {m : ℕ}
    (b : Fin m × Fin 2 → E) (h₀₀ : ∀ i j, ω ![b (i, 0), b (j, 0)] = 0)
    (h₀₁ : ∀ i j, ω ![b (i, 0), b (j, 1)] = if i = j then 1 else 0) :
    wedgePow ω m (fun r ↦ b (finProdFinEquiv.symm (Fin.cast (Nat.mul_comm 2 m) r))) =
      m.factorial := by
  induction m with
  | zero => exact (wedgePow_zero_apply ω _).trans (by simp)
  | succ m ih =>
    rw [comp_finProdFinEquiv_symm_succ, wedgePow_succ_apply_vecCons,
      pairedWedge_apply_vecCons_of_forall, curryLeftTopological_apply_apply,
      ih _ (fun i j ↦ h₀₀ _ _) (fun i j ↦ by simpa using h₀₁ i.succ j.succ)]
    · simp [h₀₁, Nat.factorial_succ]
    · intro r
      rw [curryLeftTopological_apply_apply]
      obtain ⟨i, j⟩ := finProdFinEquiv.symm (Fin.cast (Nat.mul_comm 2 m) r)
      fin_cases j
      · exact h₀₀ _ _
      · simp [h₀₁, (Fin.succ_ne_zero i).symm]

end ContinuousAlternatingMap

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps
public import Mathlib.Analysis.Normed.Operator.Mul
public import TauCeti.Topology.Algebra.Module.Alternating.Wedge.Assoc
import TauCeti.Data.Fin.Tuple.Basic
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
Darboux basis this is the classical normalization of the symplectic volume form `ωⁿ / n!`. More
generally, if `ω(qᵢ, pⱼ) = cᵢ δᵢⱼ`, the value is `m! ∏ᵢ cᵢ`
(`ContinuousAlternatingMap.wedgePow_apply_finProdFinEquiv_eq_mul_prod`).

## Main definitions

* `ContinuousAlternatingMap.wedgePow φ m`: the `m`-th wedge power of a real alternating form.

## Main results

* `ContinuousAlternatingMap.wedgePow_one_apply`: the first power of a form is the form itself.
* `ContinuousAlternatingMap.wedgePow_compContinuousLinearMap`: wedge powers commute with
  pullback along continuous linear maps.
* `ContinuousAlternatingMap.wedgePow_smul`: `(c φ) ^ m = c ^ m φ ^ m`.
* `ContinuousAlternatingMap.wedgePow_succ_apply_vecCons`: the power rule for inserting a vector
  into a wedge power of a two-form.
* `ContinuousAlternatingMap.wedgePow_succ_apply_vecCons_vecCons`: splitting off a pair `(x, y)`
  with `ω(x, ·)` vanishing on the remaining vectors.
* `ContinuousAlternatingMap.pairedWedge_curryLeftTopological_wedgePow_succ_apply`: inserting a
  vector `q` into `φ ^ (k + 1)` and wedging with `ψ` gives `(k + 1) φ(q, p) (φ ^ k ∧ ψ)(R)` on
  `(p, R)` when `φ(q, ·)` kills `R`.
* `ContinuousAlternatingMap.curryLeftTopological_wedgePow_succ_eq_zero`: a vector in the kernel
  of a two-form lies in the kernel of each of its positive powers.
* `ContinuousAlternatingMap.pairedWedge_wedgePow_apply_vecCons_of_forall`: for a vector `v` in
  the kernel of a two-form `ω` and a covector `a`, `ι_v (a ∧ ωᵐ) = a(v) ωᵐ`.
* `ContinuousAlternatingMap.wedgePow_apply_finProdFinEquiv_eq_mul_prod`: the `m`-th power of a
  two-form takes the value `m! ∏ᵢ cᵢ` on a family of `m` pairs with `ω(qᵢ, pⱼ) = cᵢ δᵢⱼ`.
* `ContinuousAlternatingMap.wedgePow_apply_finProdFinEquiv`: the `m`-th power of a two-form takes
  the value `m!` on a family of `m` standard pairs.

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
      pairedWedge_mul_assoc,
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

/-- **Splitting off a pair.** If `ω(x, qᵢ) = 0` for every `i`, then the `(m + 1)`-th wedge power
of a two-form `ω` takes the value `(m + 1) ω(x, y) ω ^ m (q)` on `(x, y, q₀, q₁, …)`. -/
theorem wedgePow_succ_apply_vecCons_vecCons (ω : E [⋀^Fin 2]→L[ℝ] ℝ) (m : ℕ) {x : E} (y : E)
    {q : Fin (2 * m) → E} (hq : ∀ i, ω ![x, q i] = 0) :
    wedgePow ω (m + 1) (Matrix.vecCons x (Matrix.vecCons y q)) =
      (m + 1) * (ω ![x, y] * wedgePow ω m q) := by
  rw [wedgePow_succ_apply_vecCons, pairedWedge_apply_vecCons_of_forall _ _ _ _ _ _ fun i ↦ by
      rw [curryLeftTopological_apply_apply, hq], curryLeftTopological_apply_apply,
    ContinuousLinearMap.mul_apply']

/-- **Inserting a vector into a power and wedging.** For a two-form `φ`, a form `ψ` of degree `d`
and vectors `q`, `p`, `R` such that `φ(q, Rᵢ) = 0` for every `i`, the interior product of `q` with
`φ ^ (k + 1)`, wedged with `ψ`, takes the value `(k + 1) φ(q, p) (φ ^ k ∧ ψ)(R)` on `(p, R)`.
The tuple `R` may be indexed by any `Fin n` with `n = 2 k + d`. -/
theorem pairedWedge_curryLeftTopological_wedgePow_succ_apply (φ : E [⋀^Fin 2]→L[ℝ] ℝ) (k : ℕ)
    {d n : ℕ} (ψ : E [⋀^Fin d]→L[ℝ] ℝ) (q p : E) (R : Fin n → E) (h : 2 * k + 1 + d = n + 1)
    (hqR : ∀ i, φ ![q, R i] = 0) :
    pairedWedge (ContinuousLinearMap.mul ℝ ℝ) (ContinuousLinearMap.mul ℝ ℝ).continuous₂
        (curryLeftTopological (n := 2 * k + 1) (wedgePow φ (k + 1)) q) ψ
        (Matrix.vecCons p R ∘ Fin.cast h) =
      (k + 1) * (φ ![q, p] * pairedWedge (ContinuousLinearMap.mul ℝ ℝ)
        (ContinuousLinearMap.mul ℝ ℝ).continuous₂ (wedgePow φ k) ψ (R ∘ Fin.cast (by omega))) := by
  obtain rfl : n = 2 * k + d := by omega
  rw [pairedWedge_apply_of_left_eq_smul_cast _ _ (Nat.add_comm 1 (2 * k)) ((k : ℝ) + 1)
    (fun w ↦ by rw [curryLeftTopological_apply_apply, wedgePow_succ_apply_vecCons, smul_eq_mul]),
    smul_eq_mul, pairedWedge_mul_assoc, Fin.cast_refl, Function.comp_id]
  congr 1
  rw [Fin.comp_cast_comp_cast, Fin.comp_cast_comp_cast,
    pairedWedge_apply_vecCons_of_forall _ _ _ _ _ _ fun i ↦ by
      rw [curryLeftTopological_apply_apply]
      simpa using hqR i,
    curryLeftTopological_apply_apply, ContinuousLinearMap.mul_apply']

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

/-- **Inserting a kernel vector into `a ∧ ωᵐ`.** If `ω(v, w) = 0` for every `w`, then for every
covector `a` the interior product of `v` with `a ∧ ωᵐ` is `a(v) ωᵐ`:
`(a ∧ ωᵐ)(v, w) = a(v) ωᵐ(w)`. For a contact form `α` and its Reeb field `v`, this says that
`ι_v (α ∧ (dα)ᵐ) = (dα)ᵐ`. -/
theorem pairedWedge_wedgePow_apply_vecCons_of_forall (a : E [⋀^Fin 1]→L[ℝ] ℝ)
    (ω : E [⋀^Fin 2]→L[ℝ] ℝ) (m : ℕ) {v : E} (hv : ∀ w, ω ![v, w] = 0) (w : Fin (2 * m) → E) :
    pairedWedge (ContinuousLinearMap.mul ℝ ℝ) (ContinuousLinearMap.mul ℝ ℝ).continuous₂ a
        (ω.wedgePow m) (Matrix.vecCons v w ∘ Fin.cast (Nat.add_comm 1 (2 * m))) =
      a ![v] * ω.wedgePow m w := by
  cases m with
  | zero =>
    rw [pairedWedge_apply_zero_right, wedgePow_zero_apply, ContinuousLinearMap.mul_apply',
      mul_one, wedgePow_zero_apply, mul_one]
    congr 1
    ext i
    fin_cases i
    rfl
  | succ m =>
    -- The antiderivation rule: `ι_v (a ∧ ψ) = a(v) ψ - a ∧ ι_v ψ` with `ψ = ωᵐ⁺¹`, whose
    -- interior product with `v` vanishes.
    have h := curryLeftTopological_pairedWedge (k := 0) (l := 2 * m + 1)
      (ContinuousLinearMap.mul ℝ ℝ) (ContinuousLinearMap.mul ℝ ℝ).continuous₂ a
      (ω.wedgePow (m + 1)) v (w ∘ Fin.cast (show 0 + 1 + (2 * m + 1) = 2 * (m + 1) by omega))
    rw [curryLeftTopological_apply_apply, curryLeftTopological_wedgePow_succ_eq_zero ω m hv,
      pairedWedge_zero_right, coe_zero, Pi.zero_apply, smul_zero, add_zero,
      pairedWedge_apply_zero_left, ContinuousLinearMap.mul_apply',
      curryLeftTopological_apply_apply] at h
    -- The remaining tuples agree up to value-preserving `Fin.cast`s.
    have hw : Matrix.vecCons v w ∘ Fin.cast (Nat.add_comm 1 (2 * (m + 1))) =
        Matrix.vecCons v (w ∘ Fin.cast (show 0 + 1 + (2 * m + 1) = 2 * (m + 1) by omega)) := by
      funext i
      exact Fin.cases rfl (fun j ↦ rfl) i
    have h₀ : (Matrix.vecCons v 0 : Fin (0 + 1) → E) = ![v] := by
      funext i
      exact Fin.cases rfl (fun j ↦ j.elim0) i
    rw [hw, h, h₀]
    -- `((w ∘ Fin.cast _) ∘ Fin.cast _) ∘ Fin.cast _` is `w` up to value-preserving casts.
    rfl

/-! ### The value on standard pairs -/

/-- **The first one-form kills the later pairs.** If the vectors `qᵢ = b (i, 0)` and
`pᵢ = b (i, 1)` satisfy `φ(qᵢ, qⱼ) = 0` and `φ(qᵢ, pⱼ) = cᵢ δᵢⱼ`, then `φ(q₀, ·)` vanishes on the
pairs with index `i ≥ 1`. -/
theorem apply_zero_comp_succ_eq_zero (φ : E [⋀^Fin 2]→L[ℝ] ℝ) {m : ℕ}
    (b : Fin (m + 1) × Fin 2 → E) (c : Fin (m + 1) → ℝ) (h₀₀ : ∀ i j, φ ![b (i, 0), b (j, 0)] = 0)
    (h₀₁ : ∀ i j, φ ![b (i, 0), b (j, 1)] = if i = j then c i else 0) (ij : Fin m × Fin 2) :
    φ ![b (0, 0), (b ∘ Prod.map Fin.succ id) ij] = 0 := by
  obtain ⟨j, k⟩ := ij
  fin_cases k
  · exact h₀₀ 0 j.succ
  · simpa [(Fin.succ_ne_zero j).symm] using h₀₁ 0 j.succ

/-- **The value of the top power on diagonal pairs.** If vectors `qᵢ = b (i, 0)` and
`pᵢ = b (i, 1)` satisfy `ω(qᵢ, qⱼ) = 0` and `ω(qᵢ, pⱼ) = cᵢ δᵢⱼ`, then the `m`-th wedge power of
`ω` takes the value `m! ∏ᵢ cᵢ` on `(q₀, p₀, q₁, p₁, …)`. -/
theorem wedgePow_apply_finProdFinEquiv_eq_mul_prod (ω : E [⋀^Fin 2]→L[ℝ] ℝ) {m : ℕ}
    (b : Fin m × Fin 2 → E) (c : Fin m → ℝ) (h₀₀ : ∀ i j, ω ![b (i, 0), b (j, 0)] = 0)
    (h₀₁ : ∀ i j, ω ![b (i, 0), b (j, 1)] = if i = j then c i else 0) :
    wedgePow ω m (fun r ↦ b (finProdFinEquiv.symm (Fin.cast (Nat.mul_comm 2 m) r))) =
      m.factorial * ∏ i, c i := by
  induction m with
  | zero => exact (wedgePow_zero_apply ω _).trans (by simp)
  | succ m ih =>
    rw [comp_finProdFinEquiv_symm_succ, wedgePow_succ_apply_vecCons,
      pairedWedge_apply_vecCons_of_forall, curryLeftTopological_apply_apply,
      ih _ (c ∘ Fin.succ) (fun i j ↦ h₀₀ _ _) (fun i j ↦ by simpa using h₀₁ i.succ j.succ)]
    · simp [h₀₁, Nat.factorial_succ, Fin.prod_univ_succ]
      ring
    · intro r
      rw [curryLeftTopological_apply_apply]
      exact apply_zero_comp_succ_eq_zero ω b c h₀₀ h₀₁ _

/-- **The value of the top power on standard pairs.** If vectors `qᵢ = b (i, 0)` and
`pᵢ = b (i, 1)` satisfy `ω(qᵢ, qⱼ) = 0` and `ω(qᵢ, pⱼ) = δᵢⱼ`, then the `m`-th wedge
power of `ω` takes the value `m!` on `(q₀, p₀, q₁, p₁, …)`. -/
theorem wedgePow_apply_finProdFinEquiv (ω : E [⋀^Fin 2]→L[ℝ] ℝ) {m : ℕ}
    (b : Fin m × Fin 2 → E) (h₀₀ : ∀ i j, ω ![b (i, 0), b (j, 0)] = 0)
    (h₀₁ : ∀ i j, ω ![b (i, 0), b (j, 1)] = if i = j then 1 else 0) :
    wedgePow ω m (fun r ↦ b (finProdFinEquiv.symm (Fin.cast (Nat.mul_comm 2 m) r))) =
      m.factorial := by
  simpa using wedgePow_apply_finProdFinEquiv_eq_mul_prod ω b 1 h₀₀ (by simpa using h₀₁)

end ContinuousAlternatingMap

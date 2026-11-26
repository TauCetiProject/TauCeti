/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.LinearMap
public import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic.FieldSimp

/-!
# Triangles of arrows between inner product spaces and the Gram forms of their chains

A *triangle of arrows* of size `m` consists of inner product spaces `F i n` over `𝕜` (`ℝ` or `ℂ`)
with linear maps

* `a t i n : F i n → F i (n + 1)`, the arrows along the row `i`, and
* `d t i n : F i (n + 1) → F (i + 1) n`, the descents from the row `i` to the row `i + 1`,

all depending on a parameter `t : I`, together with nonzero real weights `w t n` and isometries
`j i : V → F i 0` embedding one space `V` at the start of every row. The squares
`F i (n + 1) → F i (n + 2) → F (i + 1) (n + 1)` and `F i (n + 1) → F (i + 1) n → F (i + 1) (n + 1)`
commute up to scalars (`TauCeti.ArrowTriangle.SquareCommutes`), the first arrow `a` of each row is
adjoint to `d` on the copies of `V`, and `d ∘ a` maps the copy of `V` in the row `i` injectively to
the copy in the row `i + 1` (`TauCeti.IsArrowTriangle`).

The *weighted chain* of the row `i` (`TauCeti.ArrowTriangle.weightedChain`) is the composite of the
first `n` arrows `a t i k` of the row, the `k`-th multiplied by `w t k`. Moving the descent `d` of
the first step past the chain, one square at a time, and using the adjoint law, computes the Gram
form of the chain of the row `i` from that of the row `i + 1`. By induction on the length:

* the weighted chains are injective on `V`
  (`TauCeti.IsArrowTriangle.eq_zero_of_weightedChain_eq_zero`);
* if the constants of the squares have prescribed moduli and the squares obey an adjoint law with
  constants of modulus `1` (`TauCeti.ArrowTriangle.HasSquareModuli`), and the Gram forms of the
  first arrows are given by endomorphisms `S t i`, then the Gram form of the full chain of the row
  `i` is that of the product `S t i ⋯ S t (m - 1)`, times a ratio of weights and a constant whose
  modulus is the product of the moduli of the squares
  (`TauCeti.IsArrowTriangle.exists_inner_weightedChain_eq`).

Here "modulus" is an abstract unital multiplicative relation `M c f` between functions
`c : I → 𝕜` and `f : I → ℝ`, read "`c` has modulus `f`"; in the application it means
"`c` agrees with `f` up to norm powers at the places of a twist".

In the application `F i n` is a space of automorphic forms on the unitary group of the hermitian
space attached to the interval `[i + 1, i + n]`, the arrow `a` is the theta lift that adds the
greatest element and `d` is the adjoint of the lift that adds the least element; the computation
gives the Gram operator of a chain of theta lifts.

## Main declarations

* `TauCeti.IsArrowTriangle`: the conditions on a triangle of arrows.
* `TauCeti.ArrowTriangle.weightedChain`: the weighted chain of a row.
* `TauCeti.ArrowTriangle.HasSquareModuli`: moduli of the square constants and the adjoint law.
* `TauCeti.IsArrowTriangle.eq_zero_of_weightedChain_eq_zero`: chains are injective on `V`.
* `TauCeti.IsArrowTriangle.exists_inner_weightedChain_eq`: the Gram form of a full chain.

## References

* Adapted from grh-lean (https://github.com/lsernau/grh-lean, Apache 2.0, Copyright 2026
  Anthropic, PBC), `src/New/Determinant/Chain/TriangleNorms.lean`: `New.Exchange.IsTriangle`,
  `New.Exchange.HasSquareModuli`, `New.Exchange.IsTriangle.eq_zero_of_weightedChain_eq_zero` and
  `New.Exchange.IsTriangle.exists_inner_weightedChain_eq`, there for `ℂ` and natural weights.
-/

public section

open Finset ComplexConjugate
open scoped InnerProductSpace

namespace TauCeti

variable {𝕜 I V : Type*} [RCLike 𝕜]
  {F : ℕ → ℕ → Type*} [∀ i n : ℕ, NormedAddCommGroup (F i n)]
  [∀ i n : ℕ, InnerProductSpace 𝕜 (F i n)]
  [NormedAddCommGroup V] [InnerProductSpace 𝕜 V]
  (m : ℕ) (w : I → ℕ → ℝ) (M : (I → 𝕜) → (I → ℝ) → Prop) (L : ℕ → ℕ → I → ℝ)
  (a : I → ∀ i n : ℕ, F i n →ₗ[𝕜] F i (n + 1))
  (d : I → ∀ i n : ℕ, F i (n + 1) →ₗ[𝕜] F (i + 1) n) (j : ∀ i : ℕ, V →ₗᵢ[𝕜] F i 0)

namespace ArrowTriangle

/-- The square at `(i, n)` commutes up to `β`: on `F i (n + 1)`, `w t n` times `a ∘ d` equals
`w t (n + 2) / conj (β t)` times `d ∘ a`. Where `β t = 0` the second scalar is `0`. -/
def SquareCommutes (i n : ℕ) (β : I → 𝕜) : Prop :=
  ∀ (t : I) (y : F i (n + 1)),
    (w t n : 𝕜) • a t (i + 1) n (d t i n y) =
      ((w t (n + 2) : 𝕜) / conj (β t)) • d t i (n + 1) (a t i (n + 1) y)

/-- The adjoint law of the square at `(i, n)` with constant `κ`: every `z` in `F i (n + 2)` has an
adjoint vector `x` for `a`, `⟪a y, z⟫ = ⟪y, x⟫`, with `⟪d x, y'⟫ = κ t * ⟪d z, a y'⟫`. -/
def SquareAdjoint (i n : ℕ) (κ : I → 𝕜) : Prop :=
  ∀ (t : I) (z : F i (n + 1 + 1)), ∃ x : F i (n + 1),
    (∀ y : F i (n + 1), ⟪a t i (n + 1) y, z⟫_𝕜 = ⟪y, x⟫_𝕜) ∧
    ∀ y : F (i + 1) n, ⟪d t i n x, y⟫_𝕜 = κ t * ⟪d t i (n + 1) z, a t (i + 1) n y⟫_𝕜

variable {w a d}

/-- Unfolding `SquareCommutes`. -/
theorem squareCommutes_iff {i n : ℕ} {β : I → 𝕜} :
    SquareCommutes w a d i n β ↔ ∀ (t : I) (y : F i (n + 1)),
      (w t n : 𝕜) • a t (i + 1) n (d t i n y) =
        ((w t (n + 2) : 𝕜) / conj (β t)) • d t i (n + 1) (a t i (n + 1) y) :=
  Iff.rfl

/-- Unfolding `SquareAdjoint`. -/
theorem squareAdjoint_iff {i n : ℕ} {κ : I → 𝕜} :
    SquareAdjoint a d i n κ ↔ ∀ (t : I) (z : F i (n + 1 + 1)), ∃ x : F i (n + 1),
      (∀ y : F i (n + 1), ⟪a t i (n + 1) y, z⟫_𝕜 = ⟪y, x⟫_𝕜) ∧
      ∀ y : F (i + 1) n, ⟪d t i n x, y⟫_𝕜 = κ t * ⟪d t i (n + 1) z, a t (i + 1) n y⟫_𝕜 :=
  Iff.rfl

end ArrowTriangle

open ArrowTriangle

/-- A triangle of arrows of size `m`: inner product spaces `F i n` with arrows
`a t i n : F i n → F i (n + 1)` along the rows and descents `d t i n : F i (n + 1) → F (i + 1) n`,
nonzero weights `w t n` and isometries `j i : V → F i 0`. The squares with `i + n + 2 ≤ m`
commute up to scalars; on the copies of `V` the first arrow `a` is adjoint to `d`, and `d ∘ a` maps
each copy injectively to the next. -/
structure IsArrowTriangle : Prop where
  /-- The weights do not vanish. -/
  weight_ne_zero (t : I) (n : ℕ) : w t n ≠ 0
  /-- Each square, for `i + n + 2 ≤ m`, commutes up to a scalar function. -/
  square_commutes (i n : ℕ) (h : i + (n + 1) < m) : ∃ β : I → 𝕜, SquareCommutes w a d i n β
  /-- On the copies of `V`, the first arrow `a` of the row `i` is adjoint to `d`. -/
  first_adjoint (i : ℕ) (hi : i < m) (t : I) (y : V) (z : F i (0 + 1)) :
    ⟪z, a t i 0 (j i y)⟫_𝕜 = ⟪d t i 0 z, j (i + 1) y⟫_𝕜
  /-- `d ∘ a` maps the copy of `V` in the row `i` to the copy of `V` in the row `i + 1`. -/
  comp_mem_range (i : ℕ) (hi : i < m) (t : I) (y : V) :
    d t i 0 (a t i 0 (j i y)) ∈ Set.range (j (i + 1))
  /-- `d ∘ a` has trivial kernel on the copy of `V` in the row `i`. -/
  eq_zero_of_comp_eq_zero (i : ℕ) (hi : i < m) (t : I) (y : V)
    (hy : d t i 0 (a t i 0 (j i y)) = 0) : y = 0

namespace ArrowTriangle

/-- The moduli of the constants of the squares of a triangle of size `m`, and the adjoint law. The
relation `M c f` is read "`c` has modulus `f`". -/
structure HasSquareModuli : Prop where
  /-- The constant `1` has modulus `1`. -/
  modulus_one : M 1 1
  /-- Moduli multiply. -/
  modulus_mul {c c' : I → 𝕜} {f f' : I → ℝ} (hc : M c f) (hc' : M c' f') : M (c * c') (f * f')
  /-- The square at `(i, n)`, for `i + n + 2 ≤ m`, commutes up to a scalar function of modulus
  `L (i + 1) (i + 1 + n + 1)`. -/
  exists_modulus_commutes (i n : ℕ) (h : i + (n + 1) < m) :
    ∃ β : I → 𝕜, M β (L (i + 1) (i + 1 + n + 1)) ∧ SquareCommutes w a d i n β
  /-- Each square, for `i + n + 2 ≤ m`, obeys the adjoint law with a constant of modulus `1`. -/
  square_adjoint (i n : ℕ) (h : i + (n + 1) < m) : ∃ κ : I → 𝕜, M κ 1 ∧ SquareAdjoint a d i n κ

/-- The weighted chain of the row `i`: the composite `F i 0 → F i n` of the first `n` arrows
`a t i k` (`k < n`), each multiplied by its weight `w t k`. -/
def weightedChain (t : I) (i : ℕ) : ∀ n : ℕ, F i 0 →ₗ[𝕜] F i n
  | 0 => LinearMap.id
  | n + 1 => ((w t n : 𝕜) • a t i n) ∘ₗ weightedChain t i n

/-- The weighted chain of length `0` is the identity. -/
@[simp]
theorem weightedChain_zero_apply (t : I) (i : ℕ) (y : F i 0) : weightedChain w a t i 0 y = y := by
  simp [weightedChain]

/-- The weighted chain of length `n + 1` is the arrow `a t i n`, weighted by `w t n`, after the
chain of length `n`. -/
@[simp]
theorem weightedChain_succ_apply (t : I) (i n : ℕ) (y : F i 0) :
    weightedChain w a t i (n + 1) y = (w t n : 𝕜) • a t i n (weightedChain w a t i n y) := by
  simp [weightedChain]

/-- `d` moves past the weighted chain up to `β`: the `n`-chain of the row `i + 1` after `d ∘ a` is
`w t (n + 1) / (w t 1 * w t 0 * conj (β t))` times `d` after the `(n + 1)`-chain of the row `i`. -/
def ChainCommutes (i n : ℕ) (β : I → 𝕜) : Prop :=
  ∀ (t : I) (y : F i 0),
    weightedChain w a t (i + 1) n (d t i 0 (a t i 0 y)) =
      ((w t (n + 1) : 𝕜) / (w t 1 * w t 0 * conj (β t))) •
        d t i n (weightedChain w a t i (n + 1) y)

/-- The arrow `a t i n` after the `n`-chain is adjoint to `d` on chains, up to `κ`:
`⟪z, a X⟫ = κ t * ⟪d z, Y⟫`, where `X` is the `n`-chain of the row `i` at `j i y` and `Y` the
`n`-chain of the row `i + 1` at `j (i + 1) y`. -/
def ChainAdjoint (i n : ℕ) (κ : I → 𝕜) : Prop :=
  ∀ (t : I) (y : V) (z : F i (n + 1)),
    ⟪z, a t i n (weightedChain w a t i n (j i y))⟫_𝕜 =
      κ t * ⟪d t i n z, weightedChain w a t (i + 1) n (j (i + 1) y)⟫_𝕜

variable {m w M L a d j}

/-- Unfolding `ChainCommutes`. -/
theorem chainCommutes_iff {i n : ℕ} {β : I → 𝕜} :
    ChainCommutes w a d i n β ↔ ∀ (t : I) (y : F i 0),
      weightedChain w a t (i + 1) n (d t i 0 (a t i 0 y)) =
        ((w t (n + 1) : 𝕜) / (w t 1 * w t 0 * conj (β t))) •
          d t i n (weightedChain w a t i (n + 1) y) :=
  Iff.rfl

/-- Unfolding `ChainAdjoint`. -/
theorem chainAdjoint_iff {i n : ℕ} {κ : I → 𝕜} :
    ChainAdjoint w a d j i n κ ↔ ∀ (t : I) (y : V) (z : F i (n + 1)),
      ⟪z, a t i n (weightedChain w a t i n (j i y))⟫_𝕜 =
        κ t * ⟪d t i n z, weightedChain w a t (i + 1) n (j (i + 1) y)⟫_𝕜 :=
  Iff.rfl

/-- One more square extends the commutation of `d` with the chains: from `ChainCommutes` at `n`
with `β` and `SquareCommutes` at `(i, n)` with `β'` follows `ChainCommutes` at `n + 1` with
`β * β'`. -/
theorem ChainCommutes.succ {i n : ℕ} {β β' : I → 𝕜} (h_chain : ChainCommutes w a d i n β)
    (h_square : SquareCommutes w a d i n β') :
    ChainCommutes w a d i (n + 1) (β * β') := by
  intro t y
  set Y : F i (n + 1) := weightedChain w a t i (n + 1) y with hY
  set c : 𝕜 := (w t (n + 1) : 𝕜) / (w t 1 * w t 0 * conj (β t))
  calc
    weightedChain w a t (i + 1) (n + 1) (d t i 0 (a t i 0 y)) =
        c • (w t n : 𝕜) • a t (i + 1) n (d t i n Y) := by
      rw [weightedChain_succ_apply, h_chain, map_smul, smul_comm]
    _ = c • ((w t (n + 2) : 𝕜) / conj (β' t)) • d t i (n + 1) (a t i (n + 1) Y) := by
      rw [h_square]
    _ = ((w t (n + 2) : 𝕜) / (w t 1 * w t 0 * conj ((β * β') t))) •
        d t i (n + 1) (weightedChain w a t i (n + 1 + 1) y) := by
      rw [weightedChain_succ_apply, ← hY, map_smul, smul_smul, smul_smul, Pi.mul_apply, map_mul]
      congr 1
      ring

/-- One more square extends the adjoint law along the chains: from `ChainAdjoint` at `n` with `κ`
and `SquareAdjoint` at `(i, n)` with `κ'` follows `ChainAdjoint` at `n + 1` with `κ * κ'`. -/
theorem ChainAdjoint.succ {i n : ℕ} {κ κ' : I → 𝕜} (h_chain : ChainAdjoint w a d j i n κ)
    (h_square : SquareAdjoint a d i n κ') :
    ChainAdjoint w a d j i (n + 1) (κ * κ') := by
  intro t y z
  -- Move the last arrow to the other side of the inner product: `x` is its adjoint vector at `z`.
  obtain ⟨x, adjoint_a, adjoint_d⟩ := h_square t z
  rw [weightedChain_succ_apply, weightedChain_succ_apply]
  set X : F i n := weightedChain w a t i n (j i y)
  set Y : F (i + 1) n := weightedChain w a t (i + 1) n (j (i + 1) y)
  calc
    ⟪z, a t i (n + 1) ((w t n : 𝕜) • a t i n X)⟫_𝕜 = w t n * ⟪x, a t i n X⟫_𝕜 := by
      rw [← inner_conj_symm, adjoint_a, inner_conj_symm, inner_smul_right]
    _ = w t n * (κ t * ⟪d t i n x, Y⟫_𝕜) := by rw [h_chain]
    _ = (κ * κ') t * ⟪d t i (n + 1) z, (w t n : 𝕜) • a t (i + 1) n Y⟫_𝕜 := by
      rw [adjoint_d, inner_smul_right, Pi.mul_apply]
      ring

/-- In a triangle with square moduli, the adjoint law holds along the chains with a constant of
modulus `1`, for `i + n < m`. -/
theorem HasSquareModuli.exists_chainAdjoint (h_tri : IsArrowTriangle m w a d j)
    (h_moduli : HasSquareModuli m w M L a d) (i n : ℕ) (hi : i + n < m) :
    ∃ κ : I → 𝕜, M κ 1 ∧ ChainAdjoint w a d j i n κ := by
  induction n with
  | zero =>
    exact ⟨1, h_moduli.modulus_one, fun t y z ↦ by
      simp [h_tri.first_adjoint i hi]⟩
  | succ n ih =>
    obtain ⟨κ, hκ, h_chain⟩ := ih (by lia)
    obtain ⟨κ', hκ', h_square⟩ := h_moduli.square_adjoint i n hi
    exact ⟨κ * κ', by simpa using h_moduli.modulus_mul hκ hκ', h_chain.succ h_square⟩

/-- For nonzero weights, `d` moves past the empty chain with constant `1`. -/
theorem chainCommutes_zero (hw : ∀ t n, w t n ≠ 0) (i : ℕ) : ChainCommutes w a d i 0 1 := by
  intro t y
  have h0 : (w t 0 : 𝕜) ≠ 0 := by exact_mod_cast hw t 0
  have h1 : (w t 1 : 𝕜) ≠ 0 := by exact_mod_cast hw t 1
  simp only [weightedChain_zero_apply, weightedChain_succ_apply, zero_add, map_smul,
    Pi.one_apply, map_one, mul_one, smul_smul]
  rw [show (w t 1 : 𝕜) / (w t 1 * w t 0) * w t 0 = 1 by field_simp, one_smul]

end ArrowTriangle

namespace IsArrowTriangle

variable {m w M L a d j}

/-- In a triangle, `d` moves past the chains up to scalars: for `i + n < m` some `β` satisfies
`ChainCommutes`. -/
theorem exists_chainCommutes (h_tri : IsArrowTriangle m w a d j) (i n : ℕ) (hi : i + n < m) :
    ∃ β : I → 𝕜, ChainCommutes w a d i n β := by
  induction n with
  | zero => exact ⟨1, chainCommutes_zero h_tri.weight_ne_zero i⟩
  | succ n ih =>
    obtain ⟨β, h_chain⟩ := ih (by lia)
    obtain ⟨β', h_square⟩ := h_tri.square_commutes i n hi
    exact ⟨β * β', h_chain.succ h_square⟩

/-- Under `HasSquareModuli`, for `i + n < m` some `β` whose modulus is the product of the
`L (i + 1) k` over `i + 1 < k ≤ i + 1 + n` satisfies `ChainCommutes`. -/
theorem exists_modulus_chainCommutes (h_tri : IsArrowTriangle m w a d j)
    (h_moduli : HasSquareModuli m w M L a d) (i n : ℕ) (hi : i + n < m) :
    ∃ β : I → 𝕜, M β (∏ k ∈ Ioc (i + 1) (i + 1 + n), L (i + 1) k) ∧
      ChainCommutes w a d i n β := by
  induction n with
  | zero =>
    exact ⟨1, by simpa [Ioc_self] using h_moduli.modulus_one,
      chainCommutes_zero h_tri.weight_ne_zero i⟩
  | succ n ih =>
    obtain ⟨β, hβ, h_chain⟩ := ih (by lia)
    obtain ⟨β', hβ', h_square⟩ := h_moduli.exists_modulus_commutes i n hi
    refine ⟨β * β', ?_, h_chain.succ h_square⟩
    -- The product of the moduli gains the factor of the new square.
    rw [← add_assoc, prod_Ioc_succ_top (by lia)]
    exact h_moduli.modulus_mul hβ hβ'

/-- **Weighted chains are injective on `V`.** In a triangle of size `m`, for `i + n ≤ m` and any
parameter `t`, if the weighted chain of length `n` of the row `i` kills `j i y`, then `y = 0`. -/
theorem eq_zero_of_weightedChain_eq_zero (h_tri : IsArrowTriangle m w a d j) {t : I}
    (n i : ℕ) (hi : i + n ≤ m) (y : V) (hy : weightedChain w a t i n (j i y) = 0) : y = 0 := by
  induction n generalizing i y with
  | zero => rwa [weightedChain_zero_apply, map_eq_zero_iff _ (j i).injective] at hy
  | succ n ih =>
    -- Pass to the row `i + 1`: the chain there kills `x`, where `j x = d (a (j y))`.
    obtain ⟨β, h_commutes⟩ := h_tri.exists_chainCommutes i n (by lia)
    obtain ⟨x, hx⟩ := h_tri.comp_mem_range i (by lia) t y
    have h_next : weightedChain w a t (i + 1) n (j (i + 1) x) = 0 := by
      rw [hx, h_commutes, hy, map_zero, smul_zero]
    have hx_zero : x = 0 := ih (i + 1) (by lia) x h_next
    exact h_tri.eq_zero_of_comp_eq_zero i (by lia) t y (by rw [← hx, hx_zero, map_zero])

/-- In a triangle with `V ≠ 0`, the constant `β` of `ChainCommutes` vanishes at no parameter. -/
theorem ne_zero_of_chainCommutes [Nontrivial V] (h_tri : IsArrowTriangle m w a d j) {i n : ℕ}
    (hi : i + n < m) {β : I → 𝕜} (h_commutes : ChainCommutes w a d i n β) (t : I) :
    β t ≠ 0 := by
  intro hβ_zero
  obtain ⟨y, hy⟩ := exists_ne (0 : V)
  obtain ⟨x, hx⟩ := h_tri.comp_mem_range i (by lia) t y
  -- The scalar of `ChainCommutes` is a quotient by `0`, that is `0`: the chain of the row `i + 1`
  -- kills `x`.
  have h_next : weightedChain w a t (i + 1) n (j (i + 1) x) = 0 := by
    simp [hx, h_commutes t, hβ_zero]
  have hx_zero : x = 0 := h_tri.eq_zero_of_weightedChain_eq_zero n (i + 1) (by lia) x h_next
  exact hy (h_tri.eq_zero_of_comp_eq_zero i (by lia) t y (by rw [← hx, hx_zero, map_zero]))

/-- In a triangle with `V ≠ 0`, the constant of a commuting square vanishes at no parameter: both
sides of `SquareCommutes` differ by a nonzero factor. -/
theorem ne_zero_of_squareCommutes [Nontrivial V] (h_tri : IsArrowTriangle m w a d j) {i n : ℕ}
    (hi : i + (n + 1) < m) {β' : I → 𝕜} (h_square : SquareCommutes w a d i n β') (t : I) :
    β' t ≠ 0 := by
  obtain ⟨β, h_chain⟩ := h_tri.exists_chainCommutes i n (by lia)
  exact right_ne_zero_of_mul (h_tri.ne_zero_of_chainCommutes hi (h_chain.succ h_square) t)

/-- The Gram form of the `(n + 1)`-chain of the row `i` through the `n`-chain of the row `i + 1`:
if `j (i + 1) x' = d (a (j i x))`, then the form at `(x, z)` is
`κ t * β t * (w 0 * w 1 * w n / w (n + 1))` times the form of the shorter chain at `(x', z)`. -/
theorem inner_weightedChain_succ (h_tri : IsArrowTriangle m w a d j) {i n : ℕ} (hi : i + n < m)
    {β κ : I → 𝕜} (h_commutes : ChainCommutes w a d i n β) (h_adjoint : ChainAdjoint w a d j i n κ)
    {t : I} {x x' : V} (hx' : j (i + 1) x' = d t i 0 (a t i 0 (j i x))) (z : V) :
    ⟪weightedChain w a t i (n + 1) (j i x), weightedChain w a t i (n + 1) (j i z)⟫_𝕜 =
      κ t * β t * ((w t 0 * w t 1 * w t n / w t (n + 1) : ℝ) : 𝕜) *
        ⟪weightedChain w a t (i + 1) n (j (i + 1) x'),
          weightedChain w a t (i + 1) n (j (i + 1) z)⟫_𝕜 := by
  rcases subsingleton_or_nontrivial V with h_trivial | h_nontrivial
  · simp [Subsingleton.elim z 0]
  have hβ : β t ≠ 0 := h_tri.ne_zero_of_chainCommutes hi h_commutes t
  set X : F i (n + 1) := weightedChain w a t i (n + 1) (j i x) with hX
  set X' : F (i + 1) n := weightedChain w a t (i + 1) n (j (i + 1) x')
  set Y : F (i + 1) n := weightedChain w a t (i + 1) n (j (i + 1) z)
  have chain_x' : X' = ((w t (n + 1) : 𝕜) / (w t 1 * w t 0 * conj (β t))) • d t i n X := by
    rw [hX, ← h_commutes, ← hx']
  have inner_chain_x' :
      ⟪X', Y⟫_𝕜 = (w t (n + 1) : 𝕜) / (w t 1 * w t 0 * β t) * ⟪d t i n X, Y⟫_𝕜 := by
    simp [chain_x', inner_smul_left, mul_comm]
  have hw (k : ℕ) : (w t k : 𝕜) ≠ 0 := by exact_mod_cast h_tri.weight_ne_zero t k
  calc
    ⟪X, weightedChain w a t i (n + 1) (j i z)⟫_𝕜 = w t n * (κ t * ⟪d t i n X, Y⟫_𝕜) := by
      rw [weightedChain_succ_apply, inner_smul_right, h_adjoint]
    _ = κ t * β t * ((w t 0 * w t 1 * w t n / w t (n + 1) : ℝ) : 𝕜) * ⟪X', Y⟫_𝕜 := by
      rw [inner_chain_x']
      push_cast
      field_simp [hw 0, hw 1, hw (n + 1)]

/-- **The Gram form of a full chain.** Take a triangle of size `m` whose squares have constants of
moduli `L` and obey the adjoint law (`HasSquareModuli`). Let `s : U → V`, endomorphisms `S t i` of
`U` and constants `C i` of modulus `1` give the Gram forms of the first arrows,
`w t 0 * ⟪a (j x), a (j (s y))⟫ = C i t * ⟪x, s (S t i y)⟫`. For `i + n = m` the weighted chain of
length `n` of the row `i` has the Gram form `κ t * (w 0 * w 1 ^ n / w n) * ⟪x, s (T y)⟫`, with
`T = S t i ⋯ S t (m - 1)` and `κ` of modulus the product of the `L r k` over `i < r < k ≤ m`. -/
theorem exists_inner_weightedChain_eq (h_tri : IsArrowTriangle m w a d j)
    (h_moduli : HasSquareModuli m w M L a d) {U : Type*} [AddCommGroup U] [Module 𝕜 U]
    {s : U → V} (S : I → ℕ → Module.End 𝕜 U) {C : ℕ → I → 𝕜} (hC : ∀ i : ℕ, M (C i) 1)
    (hS : ∀ i < m, ∀ (t : I) (x : V) (y : U),
      w t 0 * ⟪a t i 0 (j i x), a t i 0 (j i (s y))⟫_𝕜 = C i t * ⟪x, s (S t i y)⟫_𝕜)
    (n i : ℕ) (hi : i + n = m) :
    ∃ κ : I → 𝕜,
      M κ (∏ r ∈ Ioc i m, ∏ k ∈ Ioc r m, L r k) ∧
      ∀ (t : I) (x : V) (y : U),
        ⟪weightedChain w a t i n (j i x), weightedChain w a t i n (j i (s y))⟫_𝕜 =
          κ t * ((w t 0 * w t 1 ^ n / w t n : ℝ) : 𝕜) *
            ⟪x, s (((List.range' i n).map (S t)).prod y)⟫_𝕜 := by
  -- Induction on `n`, from the row `i + 1` to the row `i`. The Gram form of the chain of the row
  -- `i` at `x` is a multiple of that of the shorter chain of the row `i + 1` at `x'`, where
  -- `j x' = d (a (j x))`; pairing with `x'` is the Gram form of the first arrow.
  induction n generalizing i with
  | zero =>
    obtain rfl : i = m := hi
    refine ⟨1, by simpa [Ioc_self] using h_moduli.modulus_one, fun t x y ↦ ?_⟩
    have := h_tri.weight_ne_zero t 0
    simp [this]
  | succ n ih =>
    have hin_lt : i + n < m := by lia
    have hi_lt : i < m := by lia
    have h_end : i + 1 + n = m := by lia
    obtain ⟨κ, hκ, gram_next⟩ := ih (i + 1) h_end
    obtain ⟨β, hβ, h_commutes⟩ : ∃ β : I → 𝕜,
        M β (∏ k ∈ Ioc (i + 1) m, L (i + 1) k) ∧ ChainCommutes w a d i n β := by
      simpa only [h_end] using h_tri.exists_modulus_chainCommutes h_moduli i n hin_lt
    obtain ⟨κ', hκ', h_adjoint⟩ := h_moduli.exists_chainAdjoint h_tri i n hin_lt
    -- The squares between the rows `i` and `i + 1` give the factors with `r = i + 1`.
    have h_modulus : M (κ' * β * κ * C i) (∏ r ∈ Ioc i m, ∏ k ∈ Ioc r m, L r k) := by
      rw [← prod_Ioc_consecutive _ i.le_succ hi_lt, Nat.Ioc_succ_singleton, prod_singleton]
      simpa only [one_mul, mul_one] using
        h_moduli.modulus_mul (h_moduli.modulus_mul (h_moduli.modulus_mul hκ' hβ) hκ) (hC i)
    refine ⟨κ' * β * κ * C i, h_modulus, fun t x y ↦ ?_⟩
    rw [List.range'_succ, List.map_cons, List.prod_cons, mul_apply_eq_comp]
    obtain ⟨x', hx'⟩ := h_tri.comp_mem_range i hi_lt t x
    set T : Module.End 𝕜 U := ((List.range' (i + 1) n).map (S t)).prod
    have gram_first : w t 0 * ⟪x', s (T y)⟫_𝕜 = C i t * ⟪x, s (S t i (T y))⟫_𝕜 := by
      rw [← (j (i + 1)).inner_map_map, hx', ← h_tri.first_adjoint i hi_lt, hS i hi_lt]
    have hw (k : ℕ) : (w t k : 𝕜) ≠ 0 := by exact_mod_cast h_tri.weight_ne_zero t k
    calc
      ⟪weightedChain w a t i (n + 1) (j i x), weightedChain w a t i (n + 1) (j i (s y))⟫_𝕜 =
          κ' t * β t * ((w t 0 * w t 1 * w t n / w t (n + 1) : ℝ) : 𝕜) *
            (κ t * ((w t 0 * w t 1 ^ n / w t n : ℝ) : 𝕜) * ⟪x', s (T y)⟫_𝕜) := by
        rw [h_tri.inner_weightedChain_succ hin_lt h_commutes h_adjoint hx', gram_next]
      _ = κ' t * β t * κ t * ((w t 0 * w t 1 ^ (n + 1) / w t (n + 1) : ℝ) : 𝕜) *
          (w t 0 * ⟪x', s (T y)⟫_𝕜) := by
        push_cast
        field_simp [hw n, hw (n + 1)]
        ring
      _ = (κ' * β * κ * C i) t * ((w t 0 * w t 1 ^ (n + 1) / w t (n + 1) : ℝ) : 𝕜) *
          ⟪x, s (S t i (T y))⟫_𝕜 := by
        rw [gram_first, Pi.mul_apply, Pi.mul_apply, Pi.mul_apply]
        ring

end IsArrowTriangle

end TauCeti

/-
Copyright (c) 2026 The Tau Ceti Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Star.Basic
import Mathlib.Algebra.Field.Basic
import Mathlib.Tactic.Ring

/-!
# Injectivity of weighted chains in triangles of linear maps

Given a triangle of vector spaces `F i n` over a field `𝕜` with a star operation `star`, arrows
`a t i n : F i n →ₗ[𝕜] F i (n + 1)` along row `i`, descent maps
`d t i n : F i (n + 1) →ₗ[𝕜] F (i + 1) n` down a row, nonzero weights `w t n : ℕ`, and injective
linear embeddings `j i : V →ₗ[𝕜] F i 0`, this file defines the weighted chain along a row and
proves that square commutation up to scalars yields chain commutation, injectivity of every
weighted chain of length `n` with `i + n ≤ m` on `j i V`, and nonvanishing of chain-commutation
scalars when `V` is nontrivial.

## Main definitions and results

* `TauCeti.weightedChain`: composite of the first `n` weighted arrows `(w t k : 𝕜) • a t i k`.
* `TauCeti.SquareCommutes`, `TauCeti.ChainCommutes`: single-square and `n`-chain commutation laws.
* `TauCeti.IsTriangleArrows`: axiomatic triangle of arrows with square commutation and injective
  first-step descent `d ∘ a` on `j i V`.
* `TauCeti.ChainCommutes.succ`: inductive step extending `ChainCommutes` across one square.
* `TauCeti.IsTriangleArrows.eq_zero_of_weightedChain_eq_zero`: injectivity of weighted chains
  for `i + n ≤ m`.
* `TauCeti.IsTriangleArrows.ne_zero_of_chainCommutes`: nonvanishing of chain-commutation scalars
  when `V` is nontrivial.

## Provenance

Adapted from `src/New/Determinant/Chain/TriangleNorms.lean` (`New.Exchange.weightedChain`,
`New.Exchange.SquareCommutes`, `New.Exchange.ChainCommutes`, `New.Exchange.IsTriangle`,
`New.Exchange.ChainCommutes.succ`, `New.Exchange.IsTriangle.eq_zero_of_weightedChain_eq_zero`,
`New.Exchange.IsTriangle.ne_zero_of_chainCommutes`) in
<https://github.com/lsernau/grh-lean> at commit `72fead102f663d5c7a407964a13dc0cf9d977207`.
-/

@[expose] public section

namespace TauCeti

variable {𝕜 I V : Type*} [Field 𝕜] [StarRing 𝕜] [AddCommGroup V] [Module 𝕜 V]
variable {F : ℕ → ℕ → Type*} [∀ i n, AddCommGroup (F i n)] [∀ i n, Module 𝕜 (F i n)]

/-- The composite `F i 0 →ₗ[𝕜] F i n` of the first `n` arrows `a t i k` (`k < n`) of row `i`,
each scaled by the weight `(w t k : 𝕜)`. -/
def weightedChain (w : I → ℕ → ℕ) (a : I → ∀ i n, F i n →ₗ[𝕜] F i (n + 1)) (t : I) (i : ℕ) :
    ∀ n : ℕ, F i 0 →ₗ[𝕜] F i n
  | 0 => LinearMap.id
  | n + 1 => ((w t n : 𝕜) • a t i n).comp (weightedChain w a t i n)

/-- The square at `(i, n)` commutes up to `β : I → 𝕜`:
`(w t n : 𝕜) • a (i + 1) n (d i n y)` equals
`((w t (n + 2) : 𝕜) / star (β t)) • d i (n + 1) (a i (n + 1) y)`. -/
def SquareCommutes (w : I → ℕ → ℕ) (a : I → ∀ i n, F i n →ₗ[𝕜] F i (n + 1))
    (d : I → ∀ i n, F i (n + 1) →ₗ[𝕜] F (i + 1) n) (i n : ℕ) (β : I → 𝕜) : Prop :=
  ∀ (t : I) (y : F i (n + 1)),
    (w t n : 𝕜) • a t (i + 1) n (d t i n y) =
      ((w t (n + 2) : 𝕜) / star (β t)) • d t i (n + 1) (a t i (n + 1) y)

/-- The descent `d` moves past the `n`-chain of row `i` up to `β : I → 𝕜`. -/
def ChainCommutes (w : I → ℕ → ℕ) (a : I → ∀ i n, F i n →ₗ[𝕜] F i (n + 1))
    (d : I → ∀ i n, F i (n + 1) →ₗ[𝕜] F (i + 1) n) (i n : ℕ) (β : I → 𝕜) : Prop :=
  ∀ (t : I) (y : F i 0),
    weightedChain w a t (i + 1) n (d t i 0 (a t i 0 y)) =
      ((w t (n + 1) : 𝕜) / ((w t 1 : 𝕜) * (w t 0 : 𝕜) * star (β t))) •
        d t i n (weightedChain w a t i (n + 1) y)

/-- A triangle of linear arrows of size `m`: squares commute up to scalars, `j i` embeds `V`
injectively into `F i 0`, and `d ∘ a` maps `j i V` injectively into `j (i + 1) V`. -/
structure IsTriangleArrows (m : ℕ) (w : I → ℕ → ℕ)
    (a : I → ∀ i n, F i n →ₗ[𝕜] F i (n + 1))
    (d : I → ∀ i n, F i (n + 1) →ₗ[𝕜] F (i + 1) n)
    (j : ∀ i, V →ₗ[𝕜] F i 0) : Prop where
  /-- Each embedding `j i` is injective. -/
  j_injective (i : ℕ) : Function.Injective (j i)
  /-- Each square with `i + n + 2 ≤ m` commutes up to a scalar function. -/
  square_commutes (i n : ℕ) (h : i + (n + 1) < m) : ∃ β : I → 𝕜, SquareCommutes w a d i n β
  /-- `d ∘ a` maps the copy of `V` in row `i` into the copy of `V` in row `i + 1`. -/
  comp_mem_range (i : ℕ) (hi : i < m) (t : I) (y : V) :
    d t i 0 (a t i 0 (j i y)) ∈ Set.range (j (i + 1))
  /-- `d ∘ a` has trivial kernel on `j i V`. -/
  eq_zero_of_first (i : ℕ) (hi : i < m) (t : I) (y : V) (hy : d t i 0 (a t i 0 (j i y)) = 0) :
    y = 0

/-- Extending `ChainCommutes` from `n` to `n + 1` using `SquareCommutes` multiplies the scalar
functions `β` and `β'`. -/
theorem ChainCommutes.succ {w : I → ℕ → ℕ} {a : I → ∀ i n, F i n →ₗ[𝕜] F i (n + 1)}
    {d : I → ∀ i n, F i (n + 1) →ₗ[𝕜] F (i + 1) n} {i n : ℕ} {β β' : I → 𝕜}
    (h_chain : ChainCommutes w a d i n β) (h_square : SquareCommutes w a d i n β') :
    ChainCommutes w a d i (n + 1) (β * β') := by
  intro t y
  set Y : F i (n + 1) := weightedChain w a t i (n + 1) y with hY
  set c : 𝕜 := (w t (n + 1) : 𝕜) / ((w t 1 : 𝕜) * (w t 0 : 𝕜) * star (β t))
  calc
    weightedChain w a t (i + 1) (n + 1) (d t i 0 (a t i 0 y))
        = c • (w t n : 𝕜) • a t (i + 1) n (d t i n Y) := by
          rw [weightedChain, LinearMap.comp_apply, LinearMap.smul_apply, h_chain, map_smul,
            smul_comm]
    _ = c • ((w t (n + 2) : 𝕜) / star (β' t)) • d t i (n + 1) (a t i (n + 1) Y) := by
          rw [h_square]
    _ = ((w t (n + 2) : 𝕜) / ((w t 1 : 𝕜) * (w t 0 : 𝕜) * star ((β * β') t))) •
          d t i (n + 1) (weightedChain w a t i (n + 1 + 1) y) := by
          rw [weightedChain, LinearMap.comp_apply, LinearMap.smul_apply, ← hY, map_smul,
            smul_smul, smul_smul, Pi.mul_apply, star_mul']
          congr 1
          ring

/-- In a triangle of size `m` with nonzero weights in `𝕜`, every `i + n < m` admits a scalar
function `β : I → 𝕜` satisfying `ChainCommutes w a d i n β`. -/
theorem IsTriangleArrows.exists_chainCommutes {m : ℕ} {w : I → ℕ → ℕ}
    {a : I → ∀ i n, F i n →ₗ[𝕜] F i (n + 1)} {d : I → ∀ i n, F i (n + 1) →ₗ[𝕜] F (i + 1) n}
    {j : ∀ i, V →ₗ[𝕜] F i 0} (hw : ∀ (t : I) (n : ℕ), (w t n : 𝕜) ≠ 0)
    (h_tri : IsTriangleArrows m w a d j) (i n : ℕ) (hi : i + n < m) :
    ∃ β : I → 𝕜, ChainCommutes w a d i n β := by
  induction n with
  | zero =>
    refine ⟨1, fun t y ↦ ?_⟩
    simp only [weightedChain, LinearMap.id_apply, LinearMap.comp_apply, LinearMap.smul_apply,
      Pi.one_apply, star_one, mul_one, map_smul, smul_smul]
    have h1 : (w t (0 + 1) : 𝕜) / ((w t 1 : 𝕜) * (w t 0 : 𝕜)) * (w t 0 : 𝕜) = 1 := by
      rw [show (0 + 1 : ℕ) = 1 from rfl, div_mul_eq_mul_div, mul_comm (w t 1 : 𝕜) (w t 0 : 𝕜),
        mul_div_mul_left _ _ (hw t 0), div_self (hw t 1)]
    rw [h1, one_smul]
  | succ n ih =>
    obtain ⟨β, h_chain⟩ := ih (by omega)
    obtain ⟨β', h_square⟩ := h_tri.square_commutes i n hi
    exact ⟨β * β', h_chain.succ h_square⟩

/-- In a triangle of size `m` with nonzero weights in `𝕜`, the weighted chain of length `n` along
row `i` (`i + n ≤ m`) is injective on `j i V`. -/
theorem IsTriangleArrows.eq_zero_of_weightedChain_eq_zero {m : ℕ} {w : I → ℕ → ℕ}
    {a : I → ∀ i n, F i n →ₗ[𝕜] F i (n + 1)} {d : I → ∀ i n, F i (n + 1) →ₗ[𝕜] F (i + 1) n}
    {j : ∀ i, V →ₗ[𝕜] F i 0} (hw : ∀ (t : I) (n : ℕ), (w t n : 𝕜) ≠ 0)
    (h_tri : IsTriangleArrows m w a d j) {t : I} (n i : ℕ) (hi : i + n ≤ m) (y : V)
    (hy : weightedChain w a t i n (j i y) = 0) :
    y = 0 := by
  induction n generalizing i y with
  | zero =>
    exact (map_eq_zero_iff (j i) (h_tri.j_injective i)).mp hy
  | succ n ih =>
    obtain ⟨β, h_commutes⟩ := h_tri.exists_chainCommutes hw i n (by omega)
    obtain ⟨x, hx⟩ := h_tri.comp_mem_range i (by omega) t y
    have h_next : weightedChain w a t (i + 1) n (j (i + 1) x) = 0 := by
      rw [hx, h_commutes, hy, map_zero, smul_zero]
    have hx_zero : x = 0 := ih (i + 1) (by omega) x h_next
    exact h_tri.eq_zero_of_first i (by omega) t y (by rw [← hx, hx_zero, map_zero])

/-- In a triangle of size `m` with nonzero weights in `𝕜` and nontrivial `V`, any scalar function
`β` witnessing `ChainCommutes w a d i n β` for `i + n < m` is everywhere nonzero. -/
theorem IsTriangleArrows.ne_zero_of_chainCommutes {m : ℕ} {w : I → ℕ → ℕ}
    {a : I → ∀ i n, F i n →ₗ[𝕜] F i (n + 1)} {d : I → ∀ i n, F i (n + 1) →ₗ[𝕜] F (i + 1) n}
    {j : ∀ i, V →ₗ[𝕜] F i 0} (hw : ∀ (t : I) (n : ℕ), (w t n : 𝕜) ≠ 0) [Nontrivial V]
    (h_tri : IsTriangleArrows m w a d j) {i n : ℕ} (hi : i + n < m) {β : I → 𝕜}
    (h_commutes : ChainCommutes w a d i n β) (t : I) :
    β t ≠ 0 := by
  intro hβ_zero
  obtain ⟨y, hy⟩ := exists_ne (0 : V)
  obtain ⟨x, hx⟩ := h_tri.comp_mem_range i (by omega) t y
  have h_next : weightedChain w a t (i + 1) n (j (i + 1) x) = 0 := by
    simp [hx, h_commutes t, hβ_zero]
  have hx_zero : x = 0 := h_tri.eq_zero_of_weightedChain_eq_zero hw n (i + 1) (by omega) x h_next
  exact hy (h_tri.eq_zero_of_first i (by omega) t y (by rw [← hx, hx_zero, map_zero]))

end TauCeti

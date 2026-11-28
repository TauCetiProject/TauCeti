/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.ArrowTriangle.Basic

/-!
# Constructing an arrow triangle from local descents

To compare the Gram forms of two rows, the descents in consecutive squares must agree on
shared edges. Starting with the adjoint datum at the first edge of each row, iterate the
update of the descent datum to obtain this compatibility. Injectivity of the first lift on the
base forms gives trivial kernel for its composition with the first descent, by adjointness.

The construction follows `New.Data.exists_isTriangle` in `New/Determinant/Chain/ChainNorms.lean`
of [grh-lean](https://github.com/lsernau/grh-lean) at `72fead1`.
-/

public section

open ComplexConjugate
open scoped InnerProductSpace

namespace TauCeti.ArrowTriangle

/-- Starting from a specified descent datum at the first edge of each row and an update `next`,
choose a single family of descent data for the entire triangle. It suffices to check the two
square laws and their moduli on consecutive data `p`, `next i n p`; the first edge must have
adjointness, preservation of the base forms and injectivity of the lift on those forms.

The returned data satisfy the initial and successor equations as well as the triangle and
square-moduli conditions, so that the same descent can be used in both adjacent squares. -/
theorem exists_isArrowTriangle_of_descentData
    {𝕜 I V : Type*} [RCLike 𝕜]
    {F : ℕ → ℕ → Type*} [∀ i n, NormedAddCommGroup (F i n)]
    [∀ i n, InnerProductSpace 𝕜 (F i n)] [NormedAddCommGroup V] [InnerProductSpace 𝕜 V]
    {m : ℕ} {w : I → ℕ → ℝ} {M : (I → 𝕜) → (I → ℝ) → Prop} {L : ℕ → ℕ → I → ℝ}
    {a : I → ∀ i n, F i n →ₗ[𝕜] F i (n + 1)} {j : ∀ i, V →ₗᵢ[𝕜] F i 0}
    {D : ℕ → ℕ → Type*}
    (descend : ∀ i n, D i n → I → (F i (n + 1) →ₗ[𝕜] F (i + 1) n))
    (initial : ∀ i, D i 0) (next : ∀ i n, D i n → D i (n + 1))
    (hw : ∀ t n, w t n ≠ 0) (hone : M 1 1)
    (hmul : ∀ {c c' f f'}, M c f → M c' f' → M (c * c') (f * f'))
    (hfirst : ∀ i < m, ∀ t (y : V) (z : F i 1),
      ⟪z, a t i 0 (j i y)⟫_𝕜 = ⟪descend i 0 (initial i) t z, j (i + 1) y⟫_𝕜)
    (hrange : ∀ i < m, ∀ t (y : V),
      descend i 0 (initial i) t (a t i 0 (j i y)) ∈ Set.range (j (i + 1)))
    (hinj : ∀ i < m, ∀ t, Function.Injective (fun y : V ↦ a t i 0 (j i y)))
    (hcomm : ∀ i n, i + (n + 1) < m → ∀ p : D i n,
      ∃ β : I → 𝕜, M β (L (i + 1) (i + 1 + n + 1)) ∧
        ∀ t (y : F i (n + 1)),
          (w t n : 𝕜) • a t (i + 1) n (descend i n p t y) =
            ((w t (n + 2) : 𝕜) / conj (β t)) •
              descend i (n + 1) (next i n p) t (a t i (n + 1) y))
    (hadj : ∀ i n, i + (n + 1) < m → ∀ p : D i n,
      ∃ κ : I → 𝕜, M κ 1 ∧ ∀ t (z : F i (n + 1 + 1)), ∃ x : F i (n + 1),
        (∀ y : F i (n + 1), ⟪a t i (n + 1) y, z⟫_𝕜 = ⟪y, x⟫_𝕜) ∧
        ∀ y : F (i + 1) n,
          ⟪descend i n p t x, y⟫_𝕜 =
            κ t * ⟪descend i (n + 1) (next i n p) t z, a t (i + 1) n y⟫_𝕜) :
    ∃ p : ∀ i n, D i n, (∀ i, p i 0 = initial i) ∧ (∀ i n, p i (n + 1) = next i n (p i n)) ∧
      let d (t : I) (i n : ℕ) := descend i n (p i n) t
      IsArrowTriangle m w a d j ∧ HasSquareModuli m w M L a d := by
  let p (i : ℕ) : ∀ n, D i n := fun n ↦ Nat.rec (initial i) (next i) n
  have hp₀ (i : ℕ) : p i 0 = initial i := rfl
  have hp_succ (i n : ℕ) : p i (n + 1) = next i n (p i n) := rfl
  let d (t : I) (i n : ℕ) := descend i n (p i n) t
  have hc (i n : ℕ) (hi : i + (n + 1) < m) :
      ∃ β, M β (L (i + 1) (i + 1 + n + 1)) ∧ SquareCommutes w a d i n β := by
    simpa only [squareCommutes_iff, d, hp_succ] using hcomm i n hi (p i n)
  have ha (i n : ℕ) (hi : i + (n + 1) < m) :
      ∃ κ, M κ 1 ∧ SquareAdjoint a d i n κ := by
    simpa only [squareAdjoint_iff, d, hp_succ] using hadj i n hi (p i n)
  refine ⟨p, hp₀, hp_succ, ?_, ⟨hone, hmul, hc, ha⟩⟩
  refine ⟨hw, ?_, ?_, ?_, ?_⟩
  · intro i n hi
    obtain ⟨β, _, hβ⟩ := hc i n hi
    exact ⟨β, hβ⟩
  · simpa only [d, hp₀] using hfirst
  · simpa only [d, hp₀] using hrange
  · intro i hi t y hy
    have hy₀ : descend i 0 (initial i) t (a t i 0 (j i y)) = 0 := by
      simpa only [d, hp₀] using hy
    have hzero : ⟪a t i 0 (j i y), a t i 0 (j i y)⟫_𝕜 = 0 := by
      rw [hfirst i hi, hy₀, inner_zero_left]
    apply hinj i hi t
    simpa only [map_zero] using inner_self_eq_zero.mp hzero

end TauCeti.ArrowTriangle

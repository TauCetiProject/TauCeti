/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.GroupTheory.Perm.Cycle.Product

/-!
# Examples: cycle products and cycle terms

* `Equiv.Perm.cycleProduct`: the identity permutation returns the chosen entry; the
  transposition starting at `0` gives `x₀x₁`, starting at `1` gives `x₁x₀`, and a function with
  `T(ab) = T(ba)` takes the same value on both.
* `cycleTerm`: the empty tuple gives `1`; the identity on two entries gives `T(x₀)T(x₁)`; the
  transposition gives `T(x₀x₁)`, with one cycle factor; for `T(ab) = T(ba)`, relabelling the
  entries does not change it.
-/

open TauCeti Equiv

variable {R : Type*} [Monoid R] {A : Type*} [CommMonoid A]

-- The identity permutation returns the chosen entry.
example {n : ℕ} (x : Fin n → R) (i : Fin n) : (1 : Perm (Fin n)).cycleProduct x i = x i :=
  Perm.cycleProduct_one x i

-- The transposition starting at `0` gives `x₀x₁` ...
example (x : Fin 2 → R) : (swap 0 1 : Perm (Fin 2)).cycleProduct x 0 = x 0 * x 1 :=
  Perm.cycleProduct_swap_left x (by decide)

-- ... and starting at `1` gives `x₁x₀`.
example (x : Fin 2 → R) : (swap 0 1 : Perm (Fin 2)).cycleProduct x 1 = x 1 * x 0 :=
  Perm.cycleProduct_swap_right x (by decide)

-- For `T(ab) = T(ba)`, both starting points give the same value.
example (T : R → A) (hT : ∀ a b, T (a * b) = T (b * a)) (x : Fin 2 → R) :
    T ((swap 0 1 : Perm (Fin 2)).cycleProduct x 1) =
      T ((swap 0 1 : Perm (Fin 2)).cycleProduct x 0) :=
  Perm.map_cycleProduct_eq_of_sameCycle hT x ⟨1, by decide⟩

-- The empty tuple has cycle term `1`.
example (T : R → A) (x : Fin 0 → R) : cycleTerm T 1 x = 1 :=
  cycleTerm_fin_zero T 1 x

-- The identity on two entries gives `T(x₀)T(x₁)`.
example (T : R → A) (x : Fin 2 → R) : cycleTerm T 1 x = T (x 0) * T (x 1) := by
  simp [Fin.prod_univ_two]

-- The transposition gives `T(x₀x₁)`, with one cycle factor.
example (T : R → A) (x : Fin 2 → R) : cycleTerm T (swap 0 1) x = T (x 0 * x 1) :=
  cycleTerm_swap_fin_two T x

-- For `T(ab) = T(ba)`, relabelling the entries does not change the cycle term.
example {n : ℕ} (T : R → A) (hT : ∀ a b, T (a * b) = T (b * a)) (σ τ : Perm (Fin n))
    (x : Fin n → R) : cycleTerm T (τ * σ * τ⁻¹) (x ∘ ⇑τ⁻¹) = cycleTerm T σ x :=
  cycleTerm_conj hT σ τ x

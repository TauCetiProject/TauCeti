/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Hom.Defs

/-!
# Iterating endomorphisms followed by power maps

An endomorphism commutes with power maps. Thus iterating an endomorphism followed by
the `q`-th power map gives its iterate followed by the `q ^ m`-th power map. This
identifies power-map iterates of finite-order twists.
-/

public section

namespace MonoidHom

/-- Iterating a power map composed with an endomorphism multiplies the exponents
and iterates the endomorphism. -/
theorem iterate_apply_eq_iterate_pow {T : Type*} [Monoid T] (F θ : T →* T) (q : ℕ)
    (hF : ∀ t, F t = θ t ^ q) (m : ℕ) (t : T) :
    (⇑F)^[m] t = (⇑θ)^[m] t ^ (q ^ m) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Function.iterate_succ_apply', ih, hF, map_pow, ← pow_mul,
      ← Function.iterate_succ_apply' (⇑θ) m t, Nat.pow_succ]

end MonoidHom

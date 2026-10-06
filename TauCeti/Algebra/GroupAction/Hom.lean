/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Action.Defs

/-!
# Composition of maps compatible with scalar actions

Maps intertwining scalar actions along maps of the scalars remain compatible after composition.
This applies to unbundled maps as well as to homomorphisms: neither the maps nor the scalar actions
need satisfy any additional algebraic laws.
-/

public section

namespace Function

/-- Maps compatible with scalar actions along `φ` and `ψ` compose to a map compatible with the
scalar action along `φ ∘ ψ`. -/
theorem comp_map_smul {G H K M N P : Type*} [SMul G M] [SMul H N] [SMul K P]
    (f : M → N) (q : N → P) (φ : H → G) (ψ : K → H)
    (hf : ∀ (h : H) (m : M), f (φ h • m) = h • f m)
    (hq : ∀ (k : K) (n : N), q (ψ k • n) = k • q n) (k : K) (m : M) :
    (q ∘ f) ((φ ∘ ψ) k • m) = k • (q ∘ f) m := by
  simp only [Function.comp_apply, hf, hq]

end Function

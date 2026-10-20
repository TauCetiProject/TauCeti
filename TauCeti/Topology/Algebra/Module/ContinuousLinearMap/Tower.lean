/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic

/-!
# Composites along a tower of continuous linear maps

Given continuous linear maps `P n : E (n + 1) → E n`, the composite
`P m ∘ P (m + 1) ∘ ⋯ ∘ P (m + k - 1) : E (m + k) → E m` is `TauCeti.towerComp P m k`. If maps
`U n : E n → G` are compatible with the tower, `U (n + 1) = U n ∘ P n`, then `U m` composed with
the tower composite from level `m + k` is `U (m + k)`. Such towers appear in gliding-hump
arguments, which sum vectors chosen at successive levels.

## Main declarations

* `TauCeti.towerComp`: the composite `E (m + k) → E m` of a tower of continuous linear maps.
* `TauCeti.apply_towerComp`: compatible maps factor through the tower composites.
-/

public section

namespace TauCeti

variable {R : Type*} [Semiring R] {E : ℕ → Type*} [∀ n, TopologicalSpace (E n)]
  [∀ n, AddCommMonoid (E n)] [∀ n, Module R (E n)] (P : ∀ n, E (n + 1) →L[R] E n)

/-- The composite `P m ∘ P (m + 1) ∘ ⋯ ∘ P (m + k - 1) : E (m + k) → E m` along a tower of
continuous linear maps `P n : E (n + 1) → E n`. -/
def towerComp (m : ℕ) : ∀ k, E (m + k) →L[R] E m
  | 0 => ContinuousLinearMap.id R (E m)
  | k + 1 => (towerComp m k).comp (P (m + k))

/-- The empty tower composite is the identity. -/
@[simp]
theorem towerComp_zero (m : ℕ) : towerComp P m 0 = ContinuousLinearMap.id R (E m) := (rfl)

/-- Extending the tower composite by one level precomposes with the next map of the tower. -/
@[simp]
theorem towerComp_succ (m k : ℕ) :
    towerComp P m (k + 1) = (towerComp P m k).comp (P (m + k)) := (rfl)

/-- Maps `U n : E n → G` compatible with the tower, `U (n + 1) = U n ∘ P n`, factor through
the tower composites: `U m ∘ towerComp P m k = U (m + k)`. -/
theorem apply_towerComp {G : Type*} [TopologicalSpace G] [AddCommMonoid G] [Module R G]
    {U : ∀ n, E n →L[R] G} (hU : ∀ n, U (n + 1) = (U n).comp (P n)) (m : ℕ) :
    ∀ k (v : E (m + k)), U m (towerComp P m k v) = U (m + k) v
  | 0, _ => rfl
  | k + 1, v => by
    rw [towerComp_succ, ContinuousLinearMap.comp_apply, apply_towerComp hU m k]
    exact (DFunLike.congr_fun (hU (m + k)) v).symm

end TauCeti

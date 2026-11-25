/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import Mathlib.Topology.Instances.Real.Lemmas
import TauCeti.Order.Partition.Finpartition
import TauCeti.Topology.LocallyConstant.CompactSupport

/-!
# Examples of locally constant functions with compact support

This file tests `LocallyConstant.compactlySupported`, the module `C_c^∞(X, M)`:

* on the finite discrete space `Fin 3`, `C_c^∞(Fin 3, ℤ)` is the module of all functions
  `Fin 3 → ℤ`;
* on the empty space, `C_c^∞(X, M) = 0`;
* on `ℝ` with its usual topology, every locally constant compactly supported `f : ℝ → ℤ` is `0`;
* the indicator `1_K • a` of a compact open set takes the value `a` on `K` and `0` off `K`, and it
  vanishes for the coefficient `0` and for `K = ∅`;
* elements of `C_c^∞(X, ℤ)` are equal when they agree at every point;
* two compact-open expansions of a test function, given by finite families of compact open sets,
  have a common refinement by a finite partition into compact open sets.
-/

open TopologicalSpace LocallyConstant

/-! ### 1. A finite discrete space -/

/-- On the finite discrete space `Fin 3`, the compactly supported locally constant functions are all
functions `Fin 3 → ℤ`. -/
example : compactlySupported ℤ (Fin 3) ℤ ≃ₗ[ℤ] (Fin 3 → ℤ) :=
  (LinearEquiv.ofTop _ (compactlySupported_eq_top ℤ (Fin 3) ℤ)).trans
    { toFun := fun f => f
      invFun := fun g => ⟨g, IsLocallyConstant.of_discrete g⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      left_inv := fun _ => LocallyConstant.ext fun _ => rfl
      -- The underlying function of `⟨g, _⟩` is `g` by projection.
      right_inv := fun _ => rfl }

/-! ### 2. The empty space -/

example : compactlySupported ℤ Empty ℤ = ⊥ :=
  eq_bot_iff.2 fun _ _ => (Submodule.mem_bot ℤ).2 (ext fun x => x.elim)

/-! ### 3. The real line -/

/-- A locally constant function `ℝ → ℤ` with compact support is zero, since `ℝ` is connected and
not compact. -/
example (f : LocallyConstant ℝ ℤ) (hf : HasCompactSupport f) : f = 0 :=
  (Submodule.mem_bot ℤ).1 (compactlySupported_eq_bot ℤ ℝ ℤ ▸ mem_compactlySupported.2 hf)

/-! ### 4. Compact-open indicators -/

section Indicator

variable {X : Type*} [TopologicalSpace X] [T2Space X] (K : CompactOpens X)

example (a : ℤ) {x : X} (hx : x ∈ K) : compactOpenIndicator K a x = a := by
  simp [hx]

example (a : ℤ) {x : X} (hx : x ∉ K) : compactOpenIndicator K a x = 0 := by
  simp [hx]

example : compactOpenIndicator K (0 : ℤ) = 0 := by
  simp

example (a : ℤ) : compactOpenIndicator (⊥ : CompactOpens X) a = 0 := by
  simp

example (a : ℤ) : compactOpenIndicator K a ∈ compactlySupported ℤ X ℤ :=
  compactOpenIndicator_mem_compactlySupported K a

/-- Elements of `C_c^∞(X, ℤ)` are compared pointwise with the `ext` tactic. -/
example (f g : compactlySupported ℤ X ℤ)
    (h : ∀ x, (f : LocallyConstant X ℤ) x = (g : LocallyConstant X ℤ) x) : f = g := by
  ext x
  exact h x

end Indicator

/-! ### 5. Common refinements of compact-open expansions -/

/-- Two finite families `K` and `L` of compact open sets, such as the sets of two compact-open
expansions of the same function, have a common refinement: a finite partition of their union into
compact open sets each of which lies inside or is disjoint from every `K i` and every `L j`, so that
every `K i` and every `L j` is the union of the parts inside it. -/
example {X : Type*} [TopologicalSpace X] [T2Space X] {m n : ℕ} (K : Fin m → CompactOpens X)
    (L : Fin n → CompactOpens X) [DecidableLE (CompactOpens X)] :
    ∃ P : Finpartition (Finset.univ.sup (Sum.elim K L)),
      (∀ i, {p ∈ P.parts | p ≤ K i}.sup id = K i) ∧ ∀ j, {p ∈ P.parts | p ≤ L j}.sup id = L j := by
  obtain ⟨P, hP⟩ := Finpartition.exists_forall_le_or_disjoint Finset.univ (Sum.elim K L)
  refine ⟨P, fun i => ?_, fun j => ?_⟩
  · exact P.sup_filter_le_eq (Finset.le_sup (f := Sum.elim K L) (Finset.mem_univ (Sum.inl i)))
      (hP (Sum.inl i) (Finset.mem_univ _))
  · exact P.sup_filter_le_eq (Finset.le_sup (f := Sum.elim K L) (Finset.mem_univ (Sum.inr j)))
      (hP (Sum.inr j) (Finset.mem_univ _))

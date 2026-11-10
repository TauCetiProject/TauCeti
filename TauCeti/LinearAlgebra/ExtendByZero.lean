/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Pi

/-!
# Linear extension of coordinate functions by zero

Mathlib's `Function.ExtendByZero.linearMap` along an injective index map `e` evaluates at `e i`
to the `i`-th coordinate. Along `Fin.castSucc` it views `M^N` as the coordinate hyperplane of
`M^(N + 1)` with vanishing last coordinate, and `Fin.init` inverts it. Along `Fin.succ` it is
the coordinate shift `e_i ↦ e_(i + 1)`, which together with the first basis vector
`e₀ = Pi.single 0 1` splits `R^(N + 1)`: every vector is its first coordinate times `e₀` plus
the shift of its tail.
-/

public section

namespace Function.ExtendByZero

variable (R : Type*) {M : Type*} [Semiring R] [AddCommMonoid M] [Module R M]

/-- Extension by zero along an injective index map evaluates at `e i` to the `i`-th
coordinate. -/
theorem linearMap_apply_of_injective {ι κ : Type*} {e : ι → κ} (he : Injective e)
    (v : ι → M) (i : ι) : linearMap R M e v (e i) = v i :=
  he.extend_apply v 0 i

/-- Extension by zero vanishes outside the range of the index map. -/
theorem linearMap_apply_of_notMem_range {ι κ : Type*} {e : ι → κ} (v : ι → M)
    {j : κ} (hj : j ∉ Set.range e) : linearMap R M e v j = 0 :=
  Function.extend_apply' v (0 : κ → M) j hj

/-- Extension by zero along an injective index map sends the basis vector at `i` to the basis
vector at `e i`. -/
theorem linearMap_single {ι κ : Type*} [DecidableEq ι] [DecidableEq κ] {e : ι → κ}
    (he : Injective e) (i : ι) (a : M) : linearMap R M e (Pi.single i a) = Pi.single (e i) a :=
  he.extend_single i a

omit [Semiring R] [AddCommMonoid M] [Module R M] in
/-- `Function.extend` along a composite `f₂₃ ∘ f₁₂` is the iterated extension, provided only the
outer map `f₂₃` is injective. At `f₂₃ k` both sides choose a preimage of the same predicate
(`f₂₃ (f₁₂ a) = f₂₃ k` is equivalent to `f₁₂ a = k`) and so agree, and away from the range of `f₂₃`
both sides fall back on `e'`. -/
private theorem extend_comp_of_injective_right {α β γ δ : Type*} {f₁₂ : α → β} {f₂₃ : β → γ}
    (h : Injective f₂₃) (g : α → δ) (e' : γ → δ) :
    extend (f₂₃ ∘ f₁₂) g e' = extend f₂₃ (extend f₁₂ g (e' ∘ f₂₃)) e' := by
  classical
  funext x
  simp only [Function.comp_def]
  by_cases hk : ∃ k, f₂₃ k = x
  · obtain ⟨k, rfl⟩ := hk
    rw [h.extend_apply]
    by_cases hx : ∃ a, f₁₂ a = k
    · have hpred : (fun a => f₂₃ (f₁₂ a) = f₂₃ k) = fun a => f₁₂ a = k :=
        funext fun a => propext h.eq_iff
      rw [extend_def, extend_def]
      simp only [hx, dite_true, hpred]
    · rw [extend_apply' _ _ _ hx,
        extend_apply' _ _ _ (fun ⟨a, ha⟩ => hx ⟨a, h.eq_iff.1 ha⟩)]
  · rw [extend_apply' _ _ _ hk, extend_apply' _ _ _ (fun ⟨a, ha⟩ => hk ⟨_, ha⟩)]

/-- Extension by zero along `e' ∘ e` is the composite of the extensions, provided the outer map
`e'` is injective; the inner map `e` may be arbitrary. -/
theorem linearMap_comp {ι κ η : Type*} {e : ι → κ} {e' : κ → η} (he' : Injective e') :
    linearMap R M (e' ∘ e) = linearMap R M e' ∘ₗ linearMap R M e := by
  ext v : 1
  exact extend_comp_of_injective_right he' v 0

/-- Extension by zero along the identity is the identity. -/
@[simp]
theorem linearMap_id {ι : Type*} : linearMap R M (id : ι → ι) = LinearMap.id := by
  ext v : 1
  exact extend_id v 0

variable {N : ℕ}

/-- Taking the initial segment undoes the extension by zero along `Fin.castSucc`. -/
@[simp]
theorem init_linearMap_castSucc (v : Fin N → M) :
    Fin.init (linearMap R M Fin.castSucc v) = v := by
  funext i
  rw [Fin.init, linearMap_apply_of_injective R (Fin.castSucc_injective N)]

/-- The extension by zero along `Fin.castSucc` vanishes at the last coordinate. -/
theorem linearMap_castSucc_last (v : Fin N → M) :
    linearMap R M Fin.castSucc v (Fin.last N) = 0 := by
  simp

variable {R} in
/-- Every vector of `R^(N + 1)` is its first coordinate times `e₀` plus the shift of its tail. -/
theorem eq_smul_single_zero_add_linearMap_succ_tail (w : Fin (N + 1) → R) :
    w = w 0 • Pi.single 0 1 + linearMap R R Fin.succ (Fin.tail w) := by
  funext i
  cases i using Fin.cases with
  | zero => simp
  | succ i =>
    rw [Pi.add_apply, linearMap_apply_of_injective R (Fin.succ_injective N)]
    simp [Fin.tail]

end Function.ExtendByZero

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Zhiyuan Zhang, Leheng Chen
-/
module

public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Prod

/-!
# Basic lemmas on iterated derivatives

This file collects general results about `iteratedDeriv`:

* `TauCeti.iteratedDeriv_iteratedDeriv`: iterated derivatives compose additively.
* `TauCeti.iteratedDeriv_eq_of_derivative_tower`, `TauCeti.contDiff_of_derivative_tower`: in a
  sequence of functions linked by ordinary derivatives, the iterated derivatives of the initial
  function are the later functions, and the initial function is smooth.
* `TauCeti.iteratedDeriv_const_pi`: the `k`-th iterated derivative of a constant-across-coordinates
  family `ζ ↦ fun _ : α ↦ g ζ` is the constant family of `k`-th iterated derivatives.
* `TauCeti.iteratedDerivInr`: the `k`-th iterated derivative of `f : (σ ⊕ τ → 𝕜) → F` in the
  distinguished coordinate indexed by a unique type `τ`, together with its evaluation lemmas
  (`TauCeti.iteratedDerivInr_apply`, `TauCeti.iteratedDerivInr_zero`,
  `TauCeti.iteratedDerivInr_sumElim`, `TauCeti.iteratedDerivInr_const_pi`) and the
  Fréchet-derivative step (`DifferentiableAt.iteratedDerivInr_succ_eq_fderiv`).
-/

public section

open scoped ContDiff

namespace TauCeti

variable {𝕜 E : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- The `n`-th derivative of the `k`-th derivative is the `(n + k)`-th derivative. -/
theorem iteratedDeriv_iteratedDeriv (n k : ℕ) (f : 𝕜 → E) :
    iteratedDeriv n (iteratedDeriv k f) = iteratedDeriv (n + k) f := by
  simp only [iteratedDeriv_eq_iterate, Function.iterate_add_apply]

/-- In a tower of functions with the stated successive ordinary derivatives, the `k`-th iterated
derivative of the zeroth function is the `k`-th function. -/
theorem iteratedDeriv_eq_of_derivative_tower {F : ℕ → 𝕜 → E}
    (hF : ∀ k x, HasDerivAt (F k) (F (k + 1) x) x) (k : ℕ) : iteratedDeriv k (F 0) = F k := by
  -- `F` semiconjugates the successor to `deriv`, so `F k = deriv^[k] (F 0)`.
  have h : Function.Semiconj F Nat.succ deriv := fun n => (funext fun x => (hF n x).deriv).symm
  simpa [iteratedDeriv_eq_iterate, Nat.succ_iterate] using ((h.iterate_right k).eq 0).symm

/-- A tower of functions with the stated successive ordinary derivatives gives a smooth zeroth
function. -/
theorem contDiff_of_derivative_tower (F : ℕ → 𝕜 → E)
    (hF : ∀ k x, HasDerivAt (F k) (F (k + 1) x) x) : ContDiff 𝕜 ∞ (F 0) := by
  apply contDiff_of_differentiable_iteratedDeriv (n := ⊤)
  intro k _
  rw [iteratedDeriv_eq_of_derivative_tower hF k]
  exact fun x ↦ (hF k x).differentiableAt

variable {σ τ F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- The `k`-th iterated derivative of a constant-across-coordinates family `ζ ↦ fun _ : α ↦ g ζ`
is the constant family of `k`-th iterated derivatives. -/
theorem iteratedDeriv_const_pi {α : Type*} [Fintype α] (k : ℕ) (g : 𝕜 → F) (w : 𝕜) :
    iteratedDeriv k (fun ζ (_ : α) ↦ g ζ) w = fun _ ↦ iteratedDeriv k g w := by
  by_cases hα : Nonempty α
  · induction k generalizing w with
    | zero => rfl
    | succ k ih =>
      rw [iteratedDeriv_succ, iteratedDeriv_succ]
      have hfun : iteratedDeriv k (fun ζ (_ : α) ↦ g ζ) = fun ζ (_ : α) ↦ iteratedDeriv k g ζ :=
        funext ih
      rw [hfun]
      by_cases hd : DifferentiableAt 𝕜 (iteratedDeriv k g) w
      · exact (hasDerivAt_pi.mpr fun _ ↦ hd.hasDerivAt).deriv
      · have hd' : ¬ DifferentiableAt 𝕜 (fun ζ (_ : α) ↦ iteratedDeriv k g ζ) w := fun h ↦
          hd ((differentiableAt_pi.mp h) (Classical.arbitrary α))
        rw [deriv_zero_of_not_differentiableAt hd, deriv_zero_of_not_differentiableAt hd']
        rfl
  · funext a
    exact (hα ⟨a⟩).elim

/-- The `k`-th iterated derivative of `f : (σ ⊕ τ → 𝕜) → F` in the distinguished coordinate indexed
by the unique type `τ`. -/
noncomputable def iteratedDerivInr [Unique τ] (k : ℕ) (f : (σ ⊕ τ → 𝕜) → F)
    (z : σ ⊕ τ → 𝕜) : F :=
  iteratedDeriv k (fun w ↦ f (Sum.elim (z ∘ Sum.inl) (fun _ ↦ w))) (z (.inr default))

/-- Unfolding `TauCeti.iteratedDerivInr` at a point `z`. -/
theorem iteratedDerivInr_apply [Unique τ] (k : ℕ) (f : (σ ⊕ τ → 𝕜) → F) (z : σ ⊕ τ → 𝕜) :
    iteratedDerivInr k f z =
      iteratedDeriv k (fun w ↦ f (Sum.elim (z ∘ Sum.inl) (fun _ ↦ w))) (z (.inr default)) := by
  rw [iteratedDerivInr]

/-- The `0`-th iterated derivative in the `Sum.inr` coordinate is the function itself. -/
@[simp]
theorem iteratedDerivInr_zero [Unique τ] (f : (σ ⊕ τ → 𝕜) → F) :
    iteratedDerivInr 0 f = f := by
  funext z
  simp only [iteratedDerivInr, iteratedDeriv_zero]
  congr 1
  funext j
  rcases j with i | t
  · rfl
  · simp [Unique.eq_default t]

/-- Evaluating `iteratedDerivInr k f` at `Sum.elim x (fun _ ↦ w)` gives the `k`-th iterated
derivative of the vertical slice `ζ ↦ f (Sum.elim x (fun _ ↦ ζ))` at `w`. -/
@[simp]
theorem iteratedDerivInr_sumElim [Unique τ] (k : ℕ) (f : (σ ⊕ τ → 𝕜) → F)
    (x : σ → 𝕜) (w : 𝕜) :
    iteratedDerivInr k f (Sum.elim x (fun _ ↦ w)) =
      iteratedDeriv k (fun ζ ↦ f (Sum.elim x (fun _ ↦ ζ))) w := by
  simp only [iteratedDerivInr, Sum.elim_comp_inl, Sum.elim_inr]

/-- Differentiating a constant-across-coordinates family `y ↦ fun _ : α ↦ f y` in the `Sum.inr`
coordinate commutes with forming the constant tuple. -/
theorem iteratedDerivInr_const_pi {α : Type*} [Fintype α] [Unique τ] (k : ℕ)
    (f : (σ ⊕ τ → 𝕜) → F) (z : σ ⊕ τ → 𝕜) :
    iteratedDerivInr k (fun y (_ : α) ↦ f y) z = fun _ ↦ iteratedDerivInr k f z :=
  iteratedDeriv_const_pi k _ _

end TauCeti

section IteratedDerivInr

variable {𝕜 σ τ F : Type*} [NontriviallyNormedField 𝕜] [Unique τ]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- If `TauCeti.iteratedDerivInr k f` is differentiable at `z`, then its `(k + 1)`-th derivative in
the `Sum.inr` coordinate equals its Fréchet derivative at `z` in the unit `Sum.inr` direction
`Sum.elim 0 (fun _ ↦ 1)`. -/
theorem DifferentiableAt.iteratedDerivInr_succ_eq_fderiv [Finite σ] {f : (σ ⊕ τ → 𝕜) → F} {k : ℕ}
    {z : σ ⊕ τ → 𝕜} (hf : DifferentiableAt 𝕜 (TauCeti.iteratedDerivInr k f) z) :
    TauCeti.iteratedDerivInr (k + 1) f z =
      fderiv 𝕜 (TauCeti.iteratedDerivInr k f) z (Sum.elim 0 (fun _ ↦ 1)) := by
  let _ := Fintype.ofFinite σ
  let v : σ ⊕ τ → 𝕜 := Sum.elim 0 (fun _ ↦ 1)
  let φ : 𝕜 → (σ ⊕ τ → 𝕜) := fun w ↦ z + (w - z (.inr default)) • v
  have hφ_eq (w : 𝕜) : φ w = Sum.elim (z ∘ Sum.inl) (fun _ ↦ w) := by
    ext (i | t)
    · simp [φ, v]
    · simp [φ, v, Unique.eq_default t]
  have hφ_deriv : HasDerivAt φ v (z (.inr default)) := by
    simpa [φ] using
      (((hasDerivAt_id (z (.inr default))).sub_const (z (.inr default))).smul_const v).const_add z
  have hφz : φ (z (.inr default)) = z := by simp [φ]
  have hGφ := hφz ▸ hf.hasFDerivAt
  have hstep : TauCeti.iteratedDerivInr (k + 1) f z =
      deriv (fun w ↦ TauCeti.iteratedDerivInr k f (φ w)) (z (.inr default)) := by
    simp only [TauCeti.iteratedDerivInr, hφ_eq, Sum.elim_comp_inl, Sum.elim_inr, iteratedDeriv_succ]
  rw [hstep]
  simpa [hφz, Function.comp_def] using (hGφ.comp_hasDerivAt (z (.inr default)) hφ_deriv).deriv

end IteratedDerivInr

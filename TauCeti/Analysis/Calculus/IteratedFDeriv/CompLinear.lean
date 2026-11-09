/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Normed.Operator.Prod

/-!
# Iterated derivatives of a composition with a linear map

Precomposing a function with a continuous linear map `g` multiplies the norm of its `i`-th
iterated derivative by at most `‖g‖ ^ i`. This is the norm form of Mathlib's
`ContinuousLinearMap.iteratedFDeriv_comp_right`; for a linear isometry equivalence the norm is
preserved (`LinearIsometryEquiv.norm_iteratedFDeriv_comp_right`). Since the projections of a
product have norm at most one, reading a function on one factor of a product does not increase the
norms of its iterated derivatives (`TauCeti.norm_iteratedFDeriv_comp_fst_le`,
`TauCeti.norm_iteratedFDeriv_comp_snd_le`). This needs no differentiability of the function: for
a continuous linear map with a continuous linear right inverse, precomposition acts on the
iterated derivatives by precomposition in every slot
(`ContinuousLinearMap.iteratedFDeriv_comp_right_of_rightInverse`).

For a function of one variable, postcomposition with a continuous linear map commutes with the
iterated derivative `iteratedDeriv`. This is the one-variable form of Mathlib's
`ContinuousLinearMap.iteratedFDeriv_comp_left`, used for instance to test identities between
iterated derivatives of vector-valued functions against continuous linear functionals.

A continuous linear map itself has vanishing iterated derivatives of every order at least two
(`ContinuousLinearMap.iteratedFDeriv_add_two`), and its iterated derivatives of positive order have
norm at most its own norm (`ContinuousLinearMap.norm_iteratedFDeriv_le_norm`). In particular the
projections of a product have iterated derivatives of positive order of norm at most one
(`TauCeti.norm_iteratedFDeriv_fst_le_one`, `TauCeti.norm_iteratedFDeriv_snd_le_one`).
-/

public section

namespace ContinuousLinearMap

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {G : Type*} [NormedAddCommGroup G] [NormedSpace 𝕜 G]
  {n : WithTop ℕ∞}

/-- Precomposition with a continuous linear map `g` multiplies the norm of the `i`-th iterated
derivative by at most `‖g‖ ^ i`. -/
theorem norm_iteratedFDeriv_comp_right_le (g : G →L[𝕜] E) {f : E → F} (hf : ContDiff 𝕜 n f)
    (x : G) {i : ℕ} (hi : i ≤ n) :
    ‖iteratedFDeriv 𝕜 i (f ∘ g) x‖ ≤ ‖iteratedFDeriv 𝕜 i f (g x)‖ * ‖g‖ ^ i := by
  rw [g.iteratedFDeriv_comp_right hf x hi]
  exact ((iteratedFDeriv 𝕜 i f (g x)).norm_compContinuousLinearMap_le _).trans_eq
    (by rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin])

/-- Precomposition with a continuous linear map `g` that has a continuous linear right inverse `s`
multiplies the derivative by `g`, with no differentiability assumption: where `h` is not
differentiable at `g x`, neither is `h ∘ g` at `x`, so both derivatives are `0`. -/
theorem fderiv_comp_right_of_rightInverse (g : G →L[𝕜] E) (s : E →L[𝕜] G)
    (hgs : Function.RightInverse s g) (h : E → F) (x : G) :
    fderiv 𝕜 (h ∘ g) x = (fderiv 𝕜 h (g x)).comp g := by
  by_cases hd : DifferentiableAt 𝕜 h (g x)
  · rw [fderiv_comp x hd g.differentiableAt, g.fderiv]
  · have hnd : ¬ DifferentiableAt 𝕜 (h ∘ g) x := fun hd' ↦ hd (by
      have hx : (fun u ↦ s u + (x - s (g x))) (g x) = x := by simp
      have hcomp : h = (h ∘ g) ∘ fun u ↦ s u + (x - s (g x)) := by
        funext u
        simp [hgs _]
      have := (hx ▸ hd').comp (g x)
        (by fun_prop : DifferentiableAt 𝕜 (fun u ↦ s u + (x - s (g x))) (g x))
      rwa [← hcomp] at this)
    rw [fderiv_zero_of_not_differentiableAt hnd, fderiv_zero_of_not_differentiableAt hd]
    simp

/-- Postcomposition with a continuous linear map `Φ` that has a continuous linear left inverse `Ψ`
multiplies the derivative by `Φ`, with no differentiability assumption: where `k` is not
differentiable at `y`, neither is `Φ ∘ k`, so both derivatives are `0`. -/
theorem fderiv_comp_left_of_leftInverse {X : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
    (Φ : E →L[𝕜] F) (Ψ : F →L[𝕜] E) (hΨΦ : Function.LeftInverse Ψ Φ) (k : X → E) (y : X) :
    fderiv 𝕜 (Φ ∘ k) y = Φ.comp (fderiv 𝕜 k y) := by
  by_cases hd : DifferentiableAt 𝕜 k y
  · rw [fderiv_comp y Φ.differentiableAt hd, Φ.fderiv]
  · have hnd : ¬ DifferentiableAt 𝕜 (Φ ∘ k) y := fun hd' ↦ hd (by
      have : k = Ψ ∘ (Φ ∘ k) := by
        funext u
        simp [hΨΦ _]
      rw [this]
      exact Ψ.differentiableAt.comp y hd')
    rw [fderiv_zero_of_not_differentiableAt hnd, fderiv_zero_of_not_differentiableAt hd]
    simp

/-- **Iterated derivatives under precomposition with a split surjection.** If a continuous linear
map `g` has a continuous linear right inverse `s`, the `i`-th derivative of `f ∘ g` is the `i`-th
derivative of `f` at `g x` precomposed with `g` in every slot. Unlike
`ContinuousLinearMap.iteratedFDeriv_comp_right`, no differentiability of `f` is needed. -/
theorem iteratedFDeriv_comp_right_of_rightInverse (g : G →L[𝕜] E) (s : E →L[𝕜] G)
    (hgs : Function.RightInverse s g) (f : E → F) (i : ℕ) :
    iteratedFDeriv 𝕜 i (f ∘ g) = fun x ↦
      (iteratedFDeriv 𝕜 i f (g x)).compContinuousLinearMap fun _ ↦ g := by
  induction i with
  | zero =>
    funext x
    ext m
    simp [iteratedFDeriv_zero_apply, ContinuousMultilinearMap.compContinuousLinearMap_apply]
  | succ i ih =>
    let Φ := ContinuousMultilinearMap.compContinuousLinearMapL (F := F) (fun _ : Fin i ↦ g)
    let Ψ := ContinuousMultilinearMap.compContinuousLinearMapL (F := F) (fun _ : Fin i ↦ s)
    have hΨΦ : Function.LeftInverse Ψ Φ := fun M ↦ by
      ext m
      simp [Φ, Ψ, hgs _]
    have h1 : iteratedFDeriv 𝕜 i (f ∘ g) = Φ ∘ (iteratedFDeriv 𝕜 i f ∘ g) := by
      rw [ih]
      rfl
    funext x
    rw [iteratedFDeriv_succ_eq_comp_left, Function.comp_apply, h1,
      fderiv_comp_left_of_leftInverse Φ Ψ hΨΦ, fderiv_comp_right_of_rightInverse g s hgs,
      iteratedFDeriv_succ_eq_comp_left, Function.comp_apply]
    ext m
    simp [Φ]
    rfl

/-- Postcomposition with a continuous linear map `g` commutes with the `i`-th iterated derivative
of a function of one variable that is `C^i` at the point. -/
theorem iteratedDeriv_comp_left (g : F →L[𝕜] G) {f : 𝕜 → F} {x : 𝕜} (hf : ContDiffAt 𝕜 n f x)
    {i : ℕ} (hi : i ≤ n) : iteratedDeriv i (g ∘ f) x = g (iteratedDeriv i f x) := by
  simp [iteratedDeriv_eq_iteratedFDeriv, g.iteratedFDeriv_comp_left hf hi]

/-- A continuous linear map has vanishing iterated derivatives of every order at least two. -/
@[simp]
theorem iteratedFDeriv_add_two (g : E →L[𝕜] F) (j : ℕ) (x : E) :
    iteratedFDeriv 𝕜 (j + 2) g x = 0 := by
  rw [← norm_eq_zero, ← norm_iteratedFDeriv_fderiv]
  have h : fderiv 𝕜 g = fun _ ↦ g := funext fun _ ↦ g.fderiv
  rw [h, iteratedFDeriv_succ_const]
  simp

/-- A continuous linear map `g` has iterated derivatives of every positive order of norm at most
`‖g‖`. -/
theorem norm_iteratedFDeriv_le_norm (g : E →L[𝕜] F) {k : ℕ} (hk : 1 ≤ k) (x : E) :
    ‖iteratedFDeriv 𝕜 k g x‖ ≤ ‖g‖ := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le' hk
  rcases j with _ | j
  · rw [norm_iteratedFDeriv_one, g.fderiv]
  · rw [g.iteratedFDeriv_add_two, norm_zero]
    exact norm_nonneg g

end ContinuousLinearMap

namespace TauCeti

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {G : Type*} [NormedAddCommGroup G] [NormedSpace 𝕜 G]
  {n : WithTop ℕ∞}

/-- Reading a function on the first factor of a product does not increase the norms of its
iterated derivatives. -/
theorem norm_iteratedFDeriv_comp_fst_le {f : E → F} (p : E × G) {i : ℕ} :
    ‖iteratedFDeriv 𝕜 i (f ∘ Prod.fst) p‖ ≤ ‖iteratedFDeriv 𝕜 i f p.1‖ := by
  have h := congr_fun ((ContinuousLinearMap.fst 𝕜 E G).iteratedFDeriv_comp_right_of_rightInverse
    (ContinuousLinearMap.inl 𝕜 E G) (fun _ ↦ rfl) f i) p
  rw [ContinuousLinearMap.coe_fst'] at h
  rw [h]
  exact ((iteratedFDeriv 𝕜 i f p.1).norm_compContinuousLinearMap_le _).trans
    (by rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
        exact mul_le_of_le_one_right (norm_nonneg _)
          (pow_le_one₀ (norm_nonneg _) (ContinuousLinearMap.norm_fst_le 𝕜 E G)))

/-- Reading a function on the second factor of a product does not increase the norms of its
iterated derivatives. -/
theorem norm_iteratedFDeriv_comp_snd_le {f : G → F} (p : E × G) {i : ℕ} :
    ‖iteratedFDeriv 𝕜 i (f ∘ Prod.snd) p‖ ≤ ‖iteratedFDeriv 𝕜 i f p.2‖ := by
  have h := congr_fun ((ContinuousLinearMap.snd 𝕜 E G).iteratedFDeriv_comp_right_of_rightInverse
    (ContinuousLinearMap.inr 𝕜 E G) (fun _ ↦ rfl) f i) p
  rw [ContinuousLinearMap.coe_snd'] at h
  rw [h]
  exact ((iteratedFDeriv 𝕜 i f p.2).norm_compContinuousLinearMap_le _).trans
    (by rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
        exact mul_le_of_le_one_right (norm_nonneg _)
          (pow_le_one₀ (norm_nonneg _) (ContinuousLinearMap.norm_snd_le 𝕜 E G)))

/-- The first projection of a product has iterated derivatives of every positive order of norm at
most one. -/
theorem norm_iteratedFDeriv_fst_le_one {k : ℕ} (hk : 1 ≤ k) (p : E × G) :
    ‖iteratedFDeriv 𝕜 k (Prod.fst : E × G → E) p‖ ≤ 1 := by
  have h := (ContinuousLinearMap.fst 𝕜 E G).norm_iteratedFDeriv_le_norm hk p
  rw [ContinuousLinearMap.coe_fst'] at h
  exact h.trans (ContinuousLinearMap.norm_fst_le 𝕜 E G)

/-- The second projection of a product has iterated derivatives of every positive order of norm at
most one. -/
theorem norm_iteratedFDeriv_snd_le_one {k : ℕ} (hk : 1 ≤ k) (p : E × G) :
    ‖iteratedFDeriv 𝕜 k (Prod.snd : E × G → G) p‖ ≤ 1 := by
  have h := (ContinuousLinearMap.snd 𝕜 E G).norm_iteratedFDeriv_le_norm hk p
  rw [ContinuousLinearMap.coe_snd'] at h
  exact h.trans (ContinuousLinearMap.norm_snd_le 𝕜 E G)

end TauCeti

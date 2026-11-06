/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Normed.Operator.Prod

/-!
# Iterated derivatives of a composition with a linear map

Precomposing a function with a continuous linear map `g` multiplies the norm of its `i`-th
iterated derivative by at most `‖g‖ ^ i`. This is the norm form of Mathlib's
`ContinuousLinearMap.iteratedFDeriv_comp_right`; for a linear isometry equivalence the norm is
preserved (`LinearIsometryEquiv.norm_iteratedFDeriv_comp_right`). Since the projections of a
product have norm at most one, reading a function on one factor of a product does not increase the
norms of its iterated derivatives (`TauCeti.norm_iteratedFDeriv_comp_fst_le`,
`TauCeti.norm_iteratedFDeriv_comp_snd_le`).

For a function of one variable, postcomposition with a continuous linear map commutes with the
iterated derivative `iteratedDeriv`. This is the one-variable form of Mathlib's
`ContinuousLinearMap.iteratedFDeriv_comp_left`, used for instance to test identities between
iterated derivatives of vector-valued functions against continuous linear functionals.

Postcomposition with a continuous linear map also preserves uniform bounds on the derivatives of
order at most `k` (`ContinuousLinearMap.exists_norm_iteratedFDeriv_comp_left_le`), which is how
bounded-derivative coefficients pass to their components.
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

/-- Postcomposition with a continuous linear map `g` commutes with the `i`-th iterated derivative
of a function of one variable that is `C^i` at the point. -/
theorem iteratedDeriv_comp_left (g : F →L[𝕜] G) {f : 𝕜 → F} {x : 𝕜} (hf : ContDiffAt 𝕜 n f x)
    {i : ℕ} (hi : i ≤ n) : iteratedDeriv i (g ∘ f) x = g (iteratedDeriv i f x) := by
  simp [iteratedDeriv_eq_iteratedFDeriv, g.iteratedFDeriv_comp_left hf hi]

/-- Postcomposition with a continuous linear map `g` preserves uniform bounds on the derivatives
of order at most `k` of a `C^k` function. -/
theorem exists_norm_iteratedFDeriv_comp_left_le (g : F →L[𝕜] G) {f : E → F} {k : ℕ}
    (hf : ContDiff 𝕜 k f) (hbd : ∀ i ≤ k, ∃ C, ∀ x, ‖iteratedFDeriv 𝕜 i f x‖ ≤ C) :
    ∀ i ≤ k, ∃ C, ∀ x, ‖iteratedFDeriv 𝕜 i (fun x ↦ g (f x)) x‖ ≤ C := by
  intro i hi
  obtain ⟨C, hC⟩ := hbd i hi
  exact ⟨‖g‖ * C, fun x ↦ (g.norm_iteratedFDeriv_comp_left hf.contDiffAt (mod_cast hi)).trans
    (mul_le_mul_of_nonneg_left (hC x) (norm_nonneg g))⟩

end ContinuousLinearMap

namespace TauCeti

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {G : Type*} [NormedAddCommGroup G] [NormedSpace 𝕜 G]
  {n : WithTop ℕ∞}

/-- Reading a function on the first factor of a product does not increase the norms of its
iterated derivatives. -/
theorem norm_iteratedFDeriv_comp_fst_le {f : E → F} (hf : ContDiff 𝕜 n f) (p : E × G) {i : ℕ}
    (hi : i ≤ n) : ‖iteratedFDeriv 𝕜 i (f ∘ Prod.fst) p‖ ≤ ‖iteratedFDeriv 𝕜 i f p.1‖ := by
  have h := (ContinuousLinearMap.fst 𝕜 E G).norm_iteratedFDeriv_comp_right_le hf p hi
  rw [ContinuousLinearMap.coe_fst'] at h
  exact h.trans (mul_le_of_le_one_right (norm_nonneg _)
    (pow_le_one₀ (norm_nonneg _) (ContinuousLinearMap.norm_fst_le 𝕜 E G)))

/-- Reading a function on the second factor of a product does not increase the norms of its
iterated derivatives. -/
theorem norm_iteratedFDeriv_comp_snd_le {f : G → F} (hf : ContDiff 𝕜 n f) (p : E × G) {i : ℕ}
    (hi : i ≤ n) : ‖iteratedFDeriv 𝕜 i (f ∘ Prod.snd) p‖ ≤ ‖iteratedFDeriv 𝕜 i f p.2‖ := by
  have h := (ContinuousLinearMap.snd 𝕜 E G).norm_iteratedFDeriv_comp_right_le hf p hi
  rw [ContinuousLinearMap.coe_snd'] at h
  exact h.trans (mul_le_of_le_one_right (norm_nonneg _)
    (pow_le_one₀ (norm_nonneg _) (ContinuousLinearMap.norm_snd_le 𝕜 E G)))

end TauCeti

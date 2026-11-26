/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import TauCeti.Analysis.Distribution.ChangeOfVariables
public import TauCeti.Analysis.Distribution.SmulLeft
import TauCeti.Analysis.Calculus.FDeriv.Equiv

/-!
# Notions of microlocal regularity of distributions

Microlocal regularity of distributions, such as microlocal smoothness
(`Distribution.IsMicrolocallySmoothAt`) or microlocal `H^s` regularity
(`Distribution.IsMicrolocallySobolevAt`), is a predicate `P Ω T x ξ` on complex distributions `T`
on open sets `Ω` of a finite-dimensional real inner product space `E`, points `x` and covectors
`ξ`, read as vectors of `E` through the inner product. Its transfer to manifolds and vector
bundles, chart by chart and frame by frame, only uses a few closure properties, which
`Distribution.IsInvariantMicrolocalRegularity P` records: the pairs `(x, ξ)` where `P` holds form
an open set, `P` holds for the zero distribution, is preserved by sums, complex multiples and smooth
multiples, is unchanged by smooth multiples not vanishing at the point, depends only on the ray
through `ξ`, is unchanged by restriction to smaller open sets, and is preserved by pullback along
smooth changes of variables (`Distribution.compCLMOfOpenPartialHomeomorph`), covectors pulling back
by the transpose of the derivative.

Pullback invariance gives its own converse
(`Distribution.IsInvariantMicrolocalRegularity.compCLMOfOpenPartialHomeomorph_iff`): `e^* T`
satisfies `P` at `(x, ξ)` exactly when `T` satisfies `P` at `(e x, (De⁻¹(e x))ᵀ ξ)`. Pulling back
along `e⁻¹` returns the restriction of `T` to `e '' U`, which satisfies `P` exactly where `T` does.
So the set of nonzero covectors where `P` fails, such as the wave front set, transforms by the
transpose of the derivative
(`Distribution.IsInvariantMicrolocalRegularity.setOf_compCLMOfOpenPartialHomeomorph`).

This is the microlocal analogue of `Distribution.IsInvariantLocalRegularity`.

## References

* L. Hörmander, *The Analysis of Linear Partial Differential Operators I*, second edition,
  Springer, 1990, §8.2 (the wave front set on a manifold, defined through its invariance under
  diffeomorphisms).
* L. Hörmander, *Lectures on Nonlinear Hyperbolic Differential Equations*, Springer, 1997, §11.1
  (the `H^s` wave front set and its invariance under diffeomorphisms).
-/

public section

noncomputable section

open Set TopologicalSpace
open scoped Distributions ContDiff InnerProduct

namespace Distribution

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- A predicate `P Ω T x ξ` on complex distributions `T` on open sets `Ω ⊆ E`, points `x` and
covectors `ξ`, read as "`T` is regular at `(x, ξ)`", is an **invariant notion of microlocal
regularity** if the pairs `(x, ξ)` where it holds form an open set, it holds for the zero
distribution at every point of `Ω`, it is preserved by sums, complex multiples and smooth
multiples, it is unchanged by smooth multiples not vanishing at the point, it depends only on the
ray through `ξ`, it is unchanged by restriction to smaller open sets, and it is preserved by
pullback along smooth changes of variables, covectors pulling back by the transpose of the
derivative. These are the operations relating the local representatives of a distribution on a
vector bundle in two charts and frames. -/
structure IsInvariantMicrolocalRegularity (P : (Ω : Opens E) → 𝓓'(Ω, ℂ) → E → E → Prop) :
    Prop where
  isOpen_setOf (Ω : Opens E) (T : 𝓓'(Ω, ℂ)) : IsOpen {p : E × E | P Ω T p.1 p.2}
  zero {Ω : Opens E} {x : E} (hx : x ∈ Ω) (ξ : E) : P Ω 0 x ξ
  add {Ω : Opens E} {S T : 𝓓'(Ω, ℂ)} {x ξ : E} (hS : P Ω S x ξ) (hT : P Ω T x ξ) :
    P Ω (S + T) x ξ
  smul {Ω : Opens E} {T : 𝓓'(Ω, ℂ)} {x ξ : E} (c : ℂ) (hT : P Ω T x ξ) : P Ω (c • T) x ξ
  smul_covector {Ω : Opens E} {T : 𝓓'(Ω, ℂ)} {x ξ : E} {r : ℝ} (hr : 0 < r) (hT : P Ω T x ξ) :
    P Ω T x (r • ξ)
  smulLeftCLM {Ω : Opens E} {T : 𝓓'(Ω, ℂ)} {x ξ : E} {g : E → ℝ} (hg : ContDiff ℝ ∞ g)
    (hT : P Ω T x ξ) : P Ω (smulLeftCLM hg T) x ξ
  smulLeftCLM_iff {Ω : Opens E} {T : 𝓓'(Ω, ℂ)} {x ξ : E} {g : E → ℝ} (hg : ContDiff ℝ ∞ g)
    (hx : g x ≠ 0) : P Ω (Distribution.smulLeftCLM hg T) x ξ ↔ P Ω T x ξ
  restrictCLM_iff {Ω Ω' : Opens E} (h : Ω' ≤ Ω) {T : 𝓓'(Ω, ℂ)} {x : E} (hx : x ∈ Ω') (ξ : E) :
    P Ω' (restrictCLM T) x ξ ↔ P Ω T x ξ
  compCLMOfOpenPartialHomeomorph {e : OpenPartialHomeomorph E E} {U Ω : Opens E}
    (he : ContDiffOn ℝ (⊤ : ℕ∞) e e.source) (he' : ContDiffOn ℝ (⊤ : ℕ∞) e.symm e.target)
    (hU : (U : Set E) ⊆ e.source) (hUΩ : MapsTo e U Ω) {T : 𝓓'(Ω, ℂ)} {x ξ : E} (hx : x ∈ U)
    (hT : P Ω T (e x) (((fderiv ℝ e.symm (e x))†) ξ)) :
    P U (compCLMOfOpenPartialHomeomorph e he he' hU hUΩ T) x ξ

namespace IsInvariantMicrolocalRegularity

variable {P : (Ω : Opens E) → 𝓓'(Ω, ℂ) → E → E → Prop}

/-- A finite sum of distributions satisfying an invariant notion of microlocal regularity `P` at
`(x, ξ)`, for a point `x` of `Ω`, satisfies `P` at `(x, ξ)`. -/
theorem sum (hP : IsInvariantMicrolocalRegularity P) {Ω : Opens E} {ι : Type*} {t : Finset ι}
    {T : ι → 𝓓'(Ω, ℂ)} {x : E} (hx : x ∈ Ω) {ξ : E} (h : ∀ i ∈ t, P Ω (T i) x ξ) :
    P Ω (∑ i ∈ t, T i) x ξ :=
  Finset.sum_induction _ (fun S ↦ P Ω S x ξ) (fun _ _ ↦ hP.add) (hP.zero hx ξ) h

/-- An invariant notion of microlocal regularity depends only on the ray through the covector. -/
theorem smul_covector_iff (hP : IsInvariantMicrolocalRegularity P) {Ω : Opens E} {T : 𝓓'(Ω, ℂ)}
    {x ξ : E} {r : ℝ} (hr : 0 < r) : P Ω T x (r • ξ) ↔ P Ω T x ξ :=
  ⟨fun h ↦ by simpa [smul_smul, inv_mul_cancel₀ hr.ne'] using hP.smul_covector (inv_pos.2 hr) h,
    hP.smul_covector hr⟩

variable {e : OpenPartialHomeomorph E E} {U Ω : Opens E}
  {he : ContDiffOn ℝ (⊤ : ℕ∞) e e.source} {he' : ContDiffOn ℝ (⊤ : ℕ∞) e.symm e.target}
  {hU : (U : Set E) ⊆ e.source} {hUΩ : MapsTo e U Ω}

/-- **Invariance under changes of variables.** For an invariant notion of microlocal regularity
`P`, the pullback `e^* T` of a distribution `T` along `e` satisfies `P` at `(x, ξ)`, for `x ∈ U`,
exactly when `T` satisfies `P` at `(e x, (De⁻¹(e x))ᵀ ξ)`. -/
theorem compCLMOfOpenPartialHomeomorph_iff (hP : IsInvariantMicrolocalRegularity P)
    {T : 𝓓'(Ω, ℂ)} {x ξ : E} (hx : x ∈ U) :
    P U (Distribution.compCLMOfOpenPartialHomeomorph e he he' hU hUΩ T) x ξ ↔
      P Ω T (e x) (((fderiv ℝ e.symm (e x))†) ξ) := by
  refine ⟨fun h ↦ ?_, hP.compCLMOfOpenPartialHomeomorph he he' hU hUΩ hx⟩
  -- Pull `e^* T` back along `e⁻¹` from the image `V = e '' U`, which gives back `T` on `V`.
  have hxs : x ∈ e.source := hU hx
  let V : Opens E := ⟨e '' U, e.isOpen_image_of_subset_source U.isOpen hU⟩
  have hVΩ : V ≤ Ω := image_subset_iff.2 hUΩ
  have hVt : (V : Set E) ⊆ e.symm.source := by
    rintro _ ⟨z, hz, rfl⟩
    exact e.map_source (hU hz)
  have hVU : MapsTo e.symm V U := by
    rintro _ ⟨z, hz, rfl⟩
    rwa [e.left_inv (hU hz)]
  have hUV : MapsTo e U V := fun z hz ↦ ⟨z, hz, rfl⟩
  have hexV : e x ∈ V := ⟨x, hx, rfl⟩
  have hres : Distribution.compCLMOfOpenPartialHomeomorph e he he' hU hUΩ T =
      Distribution.compCLMOfOpenPartialHomeomorph e he he' hU hUV (restrictCLM T) := by
    rw [← restrictCLM_compCLMOfOpenPartialHomeomorph le_rfl hVΩ, restrictCLM_self]
  rw [hres] at h
  have he₁' : ContDiffOn ℝ (⊤ : ℕ∞) e.symm.symm e.symm.target := by simpa using he
  -- The covector `(De⁻¹(e x))ᵀ ξ` pulls back along `e⁻¹` to `ξ`.
  have h' : P U (Distribution.compCLMOfOpenPartialHomeomorph e he he' hU hUV (restrictCLM T))
      (e.symm (e x)) (((fderiv ℝ e.symm.symm (e.symm (e x)))†) (((fderiv ℝ e.symm (e x))†) ξ)) := by
    simpa only [OpenPartialHomeomorph.symm_symm, e.left_inv hxs,
      e.adjoint_fderiv_apply_adjoint_fderiv_symm_apply_of_contDiffOn he he' (by simp) hxs] using h
  have h₂ := hP.compCLMOfOpenPartialHomeomorph he' he₁' hVt hVU hexV h'
  rwa [compCLMOfOpenPartialHomeomorph_symm_apply_apply (he₁ := he') (he₁' := he₁'),
    hP.restrictCLM_iff hVΩ hexV] at h₂

/-- **The singular set under a change of variables.** For an invariant notion of microlocal
regularity `P`, the nonzero covectors at which the pullback `e^* T` fails `P` are the `(x, ξ)` with
`x ∈ U` and `(e x, (De⁻¹(e x))ᵀ ξ)` a nonzero covector at which `T` fails `P`: covectors pull back
by the transpose of the derivative. For microlocal smoothness this is the transformation rule of
the wave front set. -/
theorem setOf_compCLMOfOpenPartialHomeomorph (hP : IsInvariantMicrolocalRegularity P)
    (T : 𝓓'(Ω, ℂ)) :
    {p : E × E | p.1 ∈ U ∧ p.2 ≠ 0 ∧
      ¬ P U (Distribution.compCLMOfOpenPartialHomeomorph e he he' hU hUΩ T) p.1 p.2} =
      {p : E × E | p.1 ∈ U ∧ (e p.1, ((fderiv ℝ e.symm (e p.1))†) p.2) ∈
        {q : E × E | q.1 ∈ Ω ∧ q.2 ≠ 0 ∧ ¬ P Ω T q.1 q.2}} := by
  ext ⟨x, ξ⟩
  simp only [mem_ofPred_eq]
  constructor
  · rintro ⟨hx, hξ, h⟩
    refine ⟨hx, hUΩ hx, fun h0 ↦ hξ ?_, fun h' ↦
      h ((hP.compCLMOfOpenPartialHomeomorph_iff hx).2 h')⟩
    rw [← e.adjoint_fderiv_apply_adjoint_fderiv_symm_apply_of_contDiffOn he he' (by simp) (hU hx) ξ,
      h0, map_zero]
  · rintro ⟨hx, -, hξ, h⟩
    exact ⟨hx, fun h0 ↦ hξ (by rw [h0, map_zero]), fun h' ↦
      h ((hP.compCLMOfOpenPartialHomeomorph_iff hx).1 h')⟩

end IsInvariantMicrolocalRegularity

end Distribution

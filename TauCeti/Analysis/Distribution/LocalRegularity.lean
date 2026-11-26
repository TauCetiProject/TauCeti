/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Distribution.ChangeOfVariables
public import TauCeti.Analysis.Distribution.SmulLeft

/-!
# Notions of local regularity of distributions

Local regularity scales of distributions, such as being `H^s` near a point
(`Distribution.IsLocallySobolevAt`) or `B^s_{p,q}` near a point
(`Distribution.IsLocallyMemBesovAt`), are predicates `P Ω T x` on complex distributions `T` on
open sets `Ω ⊆ E` and points `x`. Their transfer to manifolds and vector bundles, chart by chart
and frame by frame, only uses a few closure properties, which this file records:

* `Distribution.IsLocalRegularity P`: the points where `P` holds form an open set, and `P` holds
  for the zero distribution at points of `Ω` and is preserved by sums and complex multiples.
* `Distribution.IsInvariantLocalRegularity P`: in addition, `P` is preserved by smooth multiples,
  is unchanged by restriction to smaller open sets, and is preserved by pullback along smooth
  changes of variables (`Distribution.compCLMOfOpenPartialHomeomorph`). These are the operations
  relating the local representatives of a distribution on a vector bundle in two charts and
  frames.

Pullback invariance gives its own converse
(`Distribution.IsInvariantLocalRegularity.compCLMOfOpenPartialHomeomorph_iff`): `e^* T` satisfies
`P` near `x` exactly when `T` satisfies `P` near `e x`. Pulling back along `e⁻¹` returns the
restriction of `T` to `e '' U`, which satisfies `P` exactly where `T` does.

## References

* L. Hörmander, *The Analysis of Linear Partial Differential Operators III*, Springer, 1985,
  Appendix B.1 (local spaces on manifolds are defined chart by chart, using their invariance under
  diffeomorphisms and multiplication by smooth functions).
-/

public section

noncomputable section

open Set TopologicalSpace
open scoped Distributions ContDiff

namespace Distribution

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A predicate `P Ω T x` on complex distributions `T` on open sets `Ω ⊆ E` and points `x`, read as
"`T` is regular near `x`", is a **notion of local regularity** if the points where it holds form an
open set, it holds for the zero distribution at every point of `Ω`, and it is preserved by sums and
complex multiples. -/
structure IsLocalRegularity (P : (Ω : Opens E) → 𝓓'(Ω, ℂ) → E → Prop) : Prop where
  isOpen_setOf (Ω : Opens E) (T : 𝓓'(Ω, ℂ)) : IsOpen {x | P Ω T x}
  zero {Ω : Opens E} {x : E} (hx : x ∈ Ω) : P Ω 0 x
  add {Ω : Opens E} {S T : 𝓓'(Ω, ℂ)} {x : E} (hS : P Ω S x) (hT : P Ω T x) : P Ω (S + T) x
  smul {Ω : Opens E} {T : 𝓓'(Ω, ℂ)} {x : E} (c : ℂ) (hT : P Ω T x) : P Ω (c • T) x

variable {P : (Ω : Opens E) → 𝓓'(Ω, ℂ) → E → Prop}

/-- A finite sum of distributions satisfying a notion of local regularity `P` near a point `x` of
`Ω` satisfies `P` near `x`. -/
theorem IsLocalRegularity.sum (hP : IsLocalRegularity P) {Ω : Opens E} {ι : Type*}
    {t : Finset ι} {T : ι → 𝓓'(Ω, ℂ)} {x : E} (hx : x ∈ Ω) (h : ∀ i ∈ t, P Ω (T i) x) :
    P Ω (∑ i ∈ t, T i) x :=
  Finset.sum_induction _ (fun S ↦ P Ω S x) (fun _ _ ↦ hP.add) (hP.zero hx) h

variable [FiniteDimensional ℝ E]

/-- A notion of local regularity `P` is **invariant** if it is preserved by smooth multiples and by
pullback along smooth changes of variables, and is unchanged by restriction to smaller open sets.
These are the operations relating the local representatives of a distribution on a vector bundle in
two charts and frames. -/
structure IsInvariantLocalRegularity (P : (Ω : Opens E) → 𝓓'(Ω, ℂ) → E → Prop) : Prop
    extends IsLocalRegularity P where
  smulLeftCLM {Ω : Opens E} {T : 𝓓'(Ω, ℂ)} {x : E} {g : E → ℝ} (hg : ContDiff ℝ ∞ g)
    (hT : P Ω T x) : P Ω (smulLeftCLM hg T) x
  restrictCLM_iff {Ω Ω' : Opens E} (h : Ω' ≤ Ω) {T : 𝓓'(Ω, ℂ)} {x : E} (hx : x ∈ Ω') :
    P Ω' (restrictCLM T) x ↔ P Ω T x
  compCLMOfOpenPartialHomeomorph {e : OpenPartialHomeomorph E E} {U Ω : Opens E}
    (he : ContDiffOn ℝ (⊤ : ℕ∞) e e.source) (he' : ContDiffOn ℝ (⊤ : ℕ∞) e.symm e.target)
    (hU : (U : Set E) ⊆ e.source) (hUΩ : MapsTo e U Ω) {T : 𝓓'(Ω, ℂ)} {x : E} (hx : x ∈ U)
    (hT : P Ω T (e x)) : P U (compCLMOfOpenPartialHomeomorph e he he' hU hUΩ T) x

/-- **Invariance under changes of variables.** For an invariant notion of local regularity `P`, the
pullback `e^* T` of a distribution `T` along `e` satisfies `P` near a point `x ∈ U` exactly when `T`
satisfies `P` near `e x`. -/
theorem IsInvariantLocalRegularity.compCLMOfOpenPartialHomeomorph_iff
    (hP : IsInvariantLocalRegularity P) {e : OpenPartialHomeomorph E E} {U Ω : Opens E}
    {he : ContDiffOn ℝ (⊤ : ℕ∞) e e.source} {he' : ContDiffOn ℝ (⊤ : ℕ∞) e.symm e.target}
    {hU : (U : Set E) ⊆ e.source} {hUΩ : MapsTo e U Ω} {T : 𝓓'(Ω, ℂ)} {x : E} (hx : x ∈ U) :
    P U (Distribution.compCLMOfOpenPartialHomeomorph e he he' hU hUΩ T) x ↔ P Ω T (e x) := by
  refine ⟨fun h ↦ ?_, hP.compCLMOfOpenPartialHomeomorph he he' hU hUΩ hx⟩
  -- Pull back along `e⁻¹` from the open set `V = e '' U`, which returns the restriction `T|_V`.
  let V : Opens E := ⟨e '' U, (e.isOpen_image_iff_of_subset_source hU).2 U.isOpen⟩
  have hV : (V : Set E) ⊆ e.symm.source := by
    rintro _ ⟨y, hy, rfl⟩
    exact e.map_source (hU hy)
  have hVU : MapsTo e.symm V U := by
    rintro _ ⟨y, hy, rfl⟩
    rwa [e.left_inv (hU hy)]
  have hUV : MapsTo e U V := fun y hy ↦ ⟨y, hy, rfl⟩
  have hVΩ : V ≤ Ω := by
    rintro _ ⟨y, hy, rfl⟩
    exact hUΩ hy
  have hexV : e x ∈ V := ⟨x, hx, rfl⟩
  have hres : Distribution.compCLMOfOpenPartialHomeomorph e he he' hU hUΩ T =
      Distribution.compCLMOfOpenPartialHomeomorph e he he' hU hUV (restrictCLM T) := by
    rw [← restrictCLM_compCLMOfOpenPartialHomeomorph le_rfl hVΩ, restrictCLM_self]
  rw [hres, ← e.left_inv (hU hx)] at h
  have he₁' : ContDiffOn ℝ (⊤ : ℕ∞) e.symm.symm e.symm.target := by simpa using he
  have := hP.compCLMOfOpenPartialHomeomorph he' he₁' hV hVU hexV h
  rwa [compCLMOfOpenPartialHomeomorph_symm_apply_apply (he₁ := he') (he₁' := he₁'),
    hP.restrictCLM_iff hVΩ hexV] at this

end Distribution

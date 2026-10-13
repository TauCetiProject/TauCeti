/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.Morse.TrajectorySpace
public import TauCeti.Geometry.Manifold.LinearSlice

/-!
# The Morse–Smale condition for a negative-gradient flow

Let `E` be a finite-dimensional real inner product space and `f : E → ℝ` a function whose gradient
is globally Lipschitz, so that the negative-gradient flow `negativeGradientFlow f hf` exists for all
time. The results on transverse intersections and level slices of connecting trajectories
(`TauCeti.Analysis.Calculus.Morse.Transversality`, `…TrajectorySpace`) take transversality of the
unstable set of `p` and the stable set of `q` at a point `y` as a hypothesis.

`IsMorseSmale f hf` states that this transversality holds at every common point of the unstable
set of every critical point `p` and the stable set of every critical point `q`. For a function all
of whose critical points are nondegenerate, this is the classical Morse–Smale condition. It is a
plain predicate: the regularity of `f` and the nondegeneracy of its critical points are separate
hypotheses of the statements that use it, as in the pointwise theorems it is meant to feed.

## Main declarations

* `TauCeti.IsMorseSmale f hf`: the unstable set of each critical point `p` and the stable set of
  each critical point `q` are transverse at each of their common points.
* `TauCeti.isMorseSmale_iff`: the unfolded form of the predicate.
* `TauCeti.IsMorseSmale.transverse`: its pointwise elimination.
* `TauCeti.isMorseSmale_congr`: the predicate does not depend on the Lipschitz witness.
* `TauCeti.IsMorseSmale.exists_isManifold_unstableSet_inter_stableSet`: under the Morse–Smale
  condition, the set of points on trajectories from `p` to `q` is a `C¹` manifold of dimension
  `morseIndex f p - morseIndex f q`, embedded in `E`.
* `TauCeti.IsMorseSmale.exists_isManifold_unstableSet_inter_stableSet_level`: for `p ≠ q`, each
  level slice of it, the space of unparametrized trajectories, is a `C¹` manifold of dimension
  `morseIndex f p - morseIndex f q - 1`, embedded in `E`.

## References

* M. Audin and M. Damian, *Morse Theory and Floer Homology*, Springer Universitext, 2014,
  Chapter 3.
-/

public section

open scoped Gradient NNReal Manifold

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- **The Morse–Smale condition.** For a function `f` with `K`-Lipschitz gradient, the unstable set
of each critical point `p` and the stable set of each critical point `q` of the negative-gradient
flow are transverse at each common point `y`: their tangent spaces at `y` span the whole space. -/
def IsMorseSmale (f : E → ℝ) {K : ℝ≥0} (hf : LipschitzWith K (∇ f)) : Prop :=
  ∀ ⦃p q y : E⦄, fderiv ℝ f p = 0 → fderiv ℝ f q = 0 →
    y ∈ Flow.unstableSet (negativeGradientFlow f hf) p →
    y ∈ Flow.stableSet (negativeGradientFlow f hf) q →
    Submodule.span ℝ (tangentConeAt ℝ (Flow.unstableSet (negativeGradientFlow f hf) p) y) ⊔
      Submodule.span ℝ (tangentConeAt ℝ (Flow.stableSet (negativeGradientFlow f hf) q) y) = ⊤

/-- The introduction and elimination rule for `IsMorseSmale`: transversality of the unstable set of
each critical point `p` and the stable set of each critical point `q` at each common point. -/
theorem isMorseSmale_iff (f : E → ℝ) {K : ℝ≥0} (hf : LipschitzWith K (∇ f)) :
    IsMorseSmale f hf ↔ ∀ ⦃p q y : E⦄, fderiv ℝ f p = 0 → fderiv ℝ f q = 0 →
      y ∈ Flow.unstableSet (negativeGradientFlow f hf) p →
      y ∈ Flow.stableSet (negativeGradientFlow f hf) q →
      Submodule.span ℝ (tangentConeAt ℝ (Flow.unstableSet (negativeGradientFlow f hf) p) y) ⊔
        Submodule.span ℝ (tangentConeAt ℝ (Flow.stableSet (negativeGradientFlow f hf) q) y) = ⊤ :=
  Iff.rfl

/-- **Pointwise transversality.** For a Morse–Smale function, the tangent spaces at a common point
of the unstable set of a critical point and the stable set of a critical point span the whole
space. -/
theorem IsMorseSmale.transverse {f : E → ℝ} {K : ℝ≥0} {hf : LipschitzWith K (∇ f)}
    (h : IsMorseSmale f hf) {p q y : E} (hp : fderiv ℝ f p = 0) (hq : fderiv ℝ f q = 0)
    (hyu : y ∈ Flow.unstableSet (negativeGradientFlow f hf) p)
    (hys : y ∈ Flow.stableSet (negativeGradientFlow f hf) q) :
    Submodule.span ℝ (tangentConeAt ℝ (Flow.unstableSet (negativeGradientFlow f hf) p) y) ⊔
      Submodule.span ℝ (tangentConeAt ℝ (Flow.stableSet (negativeGradientFlow f hf) q) y) = ⊤ :=
  h hp hq hyu hys

/-- **Independence of the Lipschitz witness.** The Morse–Smale condition does not depend on the
Lipschitz bound used to define the negative-gradient flow. -/
theorem isMorseSmale_congr (f : E → ℝ) {K K' : ℝ≥0} (hf : LipschitzWith K (∇ f))
    (hf' : LipschitzWith K' (∇ f)) : IsMorseSmale f hf ↔ IsMorseSmale f hf' := by
  rw [isMorseSmale_iff, isMorseSmale_iff, negativeGradientFlow_congr f hf hf']

/-- Two subspaces of the same dimension are exchanged by a continuous linear automorphism. -/
private theorem exists_continuousLinearEquiv_mem_iff (V L : Submodule ℝ E)
    (h : Module.finrank ℝ V = Module.finrank ℝ L) :
    ∃ Φ : E ≃L[ℝ] E, ∀ z, z ∈ V ↔ Φ z ∈ L := by
  have h' : Module.finrank ℝ Vᗮ = Module.finrank ℝ Lᗮ := by
    have h1 := Submodule.finrank_add_finrank_orthogonal V
    have h2 := Submodule.finrank_add_finrank_orthogonal L
    omega
  have hV := Submodule.isCompl_orthogonal (K := V)
  have hL := Submodule.isCompl_orthogonal (K := L)
  let Φ : E ≃ₗ[ℝ] E := (Submodule.prodEquivOfIsCompl V Vᗮ hV).symm.trans
    (((LinearEquiv.ofFinrankEq V L h).prodCongr (LinearEquiv.ofFinrankEq Vᗮ Lᗮ h')).trans
      (Submodule.prodEquivOfIsCompl L Lᗮ hL))
  refine ⟨Φ.toContinuousLinearEquiv, fun z ↦ ?_⟩
  have h1 := (Submodule.prodEquivOfIsCompl_symm_apply_snd_eq_zero V Vᗮ hV (x := z)).symm
  have h2 := (Submodule.prodEquivOfIsCompl_symm_apply_snd_eq_zero L Lᗮ hL
    (x := Φ.toContinuousLinearEquiv z)).symm
  rw [h1, h2]
  simp [Φ]

/-- A subset of `E` that is flattened near each of its points by a `C¹` chart onto a subspace of
dimension `d` is a `C¹` manifold modelled on any complemented subspace `L` of dimension `d`. -/
private theorem exists_isManifold_of_charts {s : Set E} {L N : Submodule ℝ E}
    (hLN : Submodule.IsTopCompl L N)
    (hcharts : ∀ y ∈ s, ∃ (e : OpenPartialHomeomorph E E) (V : Submodule ℝ E), y ∈ e.source ∧
      (∀ z ∈ e.source, ContDiffAt ℝ 1 e z) ∧ (∀ z ∈ e.target, ContDiffAt ℝ 1 e.symm z) ∧
      (∀ z ∈ e.source, z ∈ s ↔ e z ∈ V) ∧ Module.finrank ℝ V = Module.finrank ℝ L) :
    ∃ C : ChartedSpace L s, letI := C
      IsManifold 𝓘(ℝ, L) 1 s ∧ ContMDiff 𝓘(ℝ, L) 𝓘(ℝ, E) 1 (Subtype.val : s → E) := by
  refine exists_isManifold_of_linearSubspaceCharts (I := 𝓘(ℝ, E)) hLN fun y ↦ ?_
  obtain ⟨e, V, hy, he, hes, hmem, hdim⟩ := hcharts y y.2
  obtain ⟨Φ, hΦ⟩ := exists_continuousLinearEquiv_mem_iff V L hdim
  refine ⟨e.transHomeomorph Φ.toHomeomorph, by simpa using hy, fun z hz ↦ ?_, fun z hz ↦ ?_,
    fun z hz ↦ ?_⟩
  · rw [OpenPartialHomeomorph.transHomeomorph_source] at hz
    exact (Φ.contDiff.contDiffAt.comp z (he z hz)).contMDiffAt
  · have hz' : Φ.symm z ∈ e.target := by simpa using hz
    exact ((hes _ hz').comp z Φ.symm.contDiff.contDiffAt).contMDiffAt
  · rw [OpenPartialHomeomorph.transHomeomorph_source] at hz
    simpa [hΦ] using hmem z hz

variable {p q : E} {c : ℝ}

/-- **The connecting locus is a manifold.** Under the Morse–Smale condition, for nondegenerate
critical points `p` and `q` of a `C²` function, the set `W^u(p) ∩ W^s(q)` of points on trajectories
from `p` to `q` is a `C¹` manifold of dimension `morseIndex f p - morseIndex f q`: it is modelled on
any complemented subspace `L` of that dimension, and its inclusion into `E` is `C¹`. -/
theorem IsMorseSmale.exists_isManifold_unstableSet_inter_stableSet (h : IsMorseSmale f hf)
    (hfs : ContDiff ℝ 2 f) (hp : IsNondegenerateCriticalPoint f p)
    (hq : IsNondegenerateCriticalPoint f q) {L N : Submodule ℝ E}
    (hLN : Submodule.IsTopCompl L N) (hL : Module.finrank ℝ L + morseIndex f q = morseIndex f p) :
    ∃ C : ChartedSpace L ↥(Flow.unstableSet (negativeGradientFlow f hf) p ∩
        Flow.stableSet (negativeGradientFlow f hf) q), letI := C
      IsManifold 𝓘(ℝ, L) 1 ↥(Flow.unstableSet (negativeGradientFlow f hf) p ∩
        Flow.stableSet (negativeGradientFlow f hf) q) ∧
      ContMDiff 𝓘(ℝ, L) 𝓘(ℝ, E) 1 (Subtype.val : ↥(Flow.unstableSet (negativeGradientFlow f hf) p ∩
        Flow.stableSet (negativeGradientFlow f hf) q) → E) := by
  refine exists_isManifold_of_charts hLN fun y ⟨hyu, hys⟩ ↦ ?_
  have htr := h.transverse hp.fderiv_eq_zero hq.fderiv_eq_zero hyu hys
  obtain ⟨e, hye, he, hes, hmem⟩ :=
    hp.exists_unstableSet_inter_stableSet_chart hq hfs hf hyu hys htr
  refine ⟨e, _, hye, he, hes, hmem, ?_⟩
  have hdim := hp.finrank_span_tangentConeAt_unstableSet_inter_stableSet_add_morseIndex hq hfs hf
    hyu hys htr
  rw [hp.span_tangentConeAt_unstableSet_inter_stableSet hq hfs hf hyu hys htr] at hdim
  omega

/-- **The space of unparametrized trajectories is a manifold.** Under the Morse–Smale condition,
for distinct nondegenerate critical points `p` and `q` of a `C²` function, each level slice
`W^u(p) ∩ W^s(q) ∩ {f = c}` is a `C¹` manifold of dimension `morseIndex f p - morseIndex f q - 1`:
it is modelled on any complemented subspace `L` of that dimension, and its inclusion into `E` is
`C¹`. -/
theorem IsMorseSmale.exists_isManifold_unstableSet_inter_stableSet_level (h : IsMorseSmale f hf)
    (hfs : ContDiff ℝ 2 f) (hp : IsNondegenerateCriticalPoint f p)
    (hq : IsNondegenerateCriticalPoint f q) (hpq : p ≠ q) {L N : Submodule ℝ E}
    (hLN : Submodule.IsTopCompl L N)
    (hL : Module.finrank ℝ L + morseIndex f q + 1 = morseIndex f p) :
    ∃ C : ChartedSpace L ↥(Flow.unstableSet (negativeGradientFlow f hf) p ∩
        Flow.stableSet (negativeGradientFlow f hf) q ∩ {x | f x = c}), letI := C
      IsManifold 𝓘(ℝ, L) 1 ↥(Flow.unstableSet (negativeGradientFlow f hf) p ∩
        Flow.stableSet (negativeGradientFlow f hf) q ∩ {x | f x = c}) ∧
      ContMDiff 𝓘(ℝ, L) 𝓘(ℝ, E) 1 (Subtype.val : ↥(Flow.unstableSet (negativeGradientFlow f hf) p ∩
        Flow.stableSet (negativeGradientFlow f hf) q ∩ {x | f x = c}) → E) := by
  refine exists_isManifold_of_charts hLN fun y ⟨⟨hyu, hys⟩, hyc⟩ ↦ ?_
  have htr := h.transverse hp.fderiv_eq_zero hq.fderiv_eq_zero hyu hys
  obtain ⟨e, hye, he, hes, hmem⟩ :=
    hp.exists_unstableSet_inter_stableSet_level_chart hq hfs hf hpq hyu hys htr hyc
  refine ⟨e, _, hye, he, hes, hmem, ?_⟩
  have hdim := hp.finrank_span_tangentConeAt_unstableSet_inter_stableSet_level_add_morseIndex hq
    hfs hf hpq hyu hys htr hyc
  rw [hp.span_tangentConeAt_unstableSet_inter_stableSet_level hq hfs hf hpq hyu hys htr hyc]
    at hdim
  omega

end TauCeti

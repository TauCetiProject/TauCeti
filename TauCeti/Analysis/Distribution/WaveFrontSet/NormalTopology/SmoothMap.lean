/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Distribution.WaveFrontSet.NormalTopology.ChangeOfVariables
public import TauCeti.Analysis.Distribution.WaveFrontSet.NormalTopology.Pullback
public import TauCeti.Analysis.Distribution.WaveFrontSet.NormalTopology.Submersion
public import TauCeti.Analysis.Distribution.WaveFrontSet.Pullback.SmoothMap
import TauCeti.Analysis.Calculus.FDeriv.Basic
import TauCeti.Analysis.Calculus.ProjectionGraph

/-!
# Continuity of the pullback along a smooth map in the normal topology

Let `f` be smooth on an open set `Ω` of a finite-dimensional real inner product space `E`, with
values in an open set `Ω'` of `E'`, and let `Γ` be a cone of nonzero covectors over `Ω'`, closed in
`Ω' × (E' \ {0})`, which does not meet the normal set of `f`: no `(f x, η) ∈ Γ` with `x ∈ Ω` has
`Df(x)ᵀ η = 0`. Every distribution `T` with wave front set in `Γ` then has a pullback `f^* T`
(`Distribution.pullback`), whose wave front set lies in the fixed cone

`f^* Γ = {(x, Df(x)ᵀ η) | x ∈ Ω, (f x, η) ∈ Γ}` (`TauCeti.covectorPullback`).

This file proves that the pullback is continuous for the normal topologies of Hörmander's spaces
(`TauCeti.WaveFrontSpace.pullbackCLM`):

`f^* : 𝓓'_Γ(Ω') →L[ℂ] 𝓓'_{f^* Γ}(Ω)`

(Brouder, Dang and Hélein, Theorem 6.3). It is assembled from the continuity of the pullback to
`E × {0}`, along surjective linear maps and along changes of variables.

## The argument

The pullback is `f^* T = ι^* (g^* T)`, where `g (x, y) = f x + y` (`TauCeti.addSnd`) is a
submersion on the open set `W = {(x, y) | x ∈ Ω, f x + y ∈ Ω'}` and `ι x = (x, 0)`
(`Distribution.pullback_eq_pullbackInl`). The submersion factors as `g = π ∘ Φ` through the shear
`Φ (x, y) = (x, f x + y)`, a smooth change of variables of `E × E'` over `Ω` with inverse
`(x, z) ↦ (x, z - f x)` (the inverse of the graph chart
`ContinuousLinearMap.projectionGraphChart`), and the projection `π (x, z) = z`. So `g^* = Φ^* π^*`
(`Distribution.compCLMOfSubmersion_comp`), and `f^*` is the composition of three maps already known
to be continuous in the normal topology, with fixed cones in between:

* `π^* : 𝓓'_Γ(Ω') →L[ℂ] 𝓓'_{πᵀ Γ}(E × Ω')` (`TauCeti.WaveFrontSpace.pullbackLinearCLM`);
* `Φ^* : 𝓓'_{πᵀ Γ}(E × Ω') →L[ℂ] 𝓓'_{Φ^* πᵀ Γ}(W)`
  (`TauCeti.WaveFrontSpace.compCLMOfOpenPartialHomeomorph`), with
  `Φ^* πᵀ Γ ⊆ g^* Γ` by the chain rule;
* `ι^* : 𝓓'_{g^* Γ}(W) →L[ℂ] 𝓓'_{ιᵀ g^* Γ}(Ω)` (`TauCeti.WaveFrontSpace.pullbackInlCLM`), with
  `ιᵀ g^* Γ ⊆ f^* Γ`.

Each step needs its source cone closed. A pulled-back cone is closed when the transposed
derivatives have continuous left inverses (`TauCeti.isOpen_diff_covectorPullback_of_leftInverse`).
For `πᵀ Γ` this holds for every surjective linear map (`TauCeti.isOpen_diff_pullbackLinearCone`).
For `g^* Γ` it holds since `Dg(x, y)ᵀ η = (Df(x)ᵀ η, η)` recovers `η` as the second component.
The restriction `ι^*` also needs `g^* Γ` to contain no conormal covector `((x, 0), (0, η))` of
`E × {0}`: such a covector comes from some `(f x, η) ∈ Γ` with `Df(x)ᵀ η = 0`, which the hypothesis
on the normal set of `f` excludes (`TauCeti.notMem_covectorPullback_addSnd`).

## Main declarations

* `TauCeti.WaveFrontSpace.pullbackCLM`: the pullback `f^* : 𝓓'_Γ(Ω') →L[ℂ] 𝓓'_{f^* Γ}(Ω)`.
* `TauCeti.WaveFrontSpace.toDistribution_pullbackCLM`: it is `Distribution.pullback`.

## References

* L. Hörmander, *The Analysis of Linear Partial Differential Operators I*, second edition,
  Springer, 1990, Theorem 8.2.4 (the pullback and its sequential continuity on `𝓓'_Γ`).
* C. Brouder, N. V. Dang, F. Hélein, *Continuity of the fundamental operations on distributions
  having a specified wave front set (with a counterexample by Semyon Alesker)*, Studia Math. 232
  (2016), arXiv:1409.7662v2, Theorem 6.3 (continuity of the pullback in the normal topology).
-/

public section

noncomputable section

open Function Set TopologicalSpace MeasureTheory WithLp ContinuousLinearMap
open scoped Distributions ContDiff InnerProduct

namespace TauCeti

variable {E E' : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup E'] [InnerProductSpace ℝ E']

/-! ### The shear `(x, y) ↦ (x, f x + y)` -/

section Shear

variable {Ω : Opens E} {Ω' : Opens E'} {f : E → E'}

private theorem differentiableAt_of_mem (hf : ContDiffOn ℝ ∞ f Ω) {x : E} (hx : x ∈ Ω) :
    DifferentiableAt ℝ f x :=
  (hf.contDiffAt (Ω.isOpen.mem_nhds hx)).differentiableAt (by simp)

/-- The displacement `(x, y) ↦ (0, f x)` of the shear is continuous where `x ∈ Ω`. -/
private theorem continuousOn_shearDisp (hf : ContinuousOn f Ω) :
    ContinuousOn (fun p : WithLp 2 (E × E') ↦ inrL2 ℝ E E' (f p.fst))
      ((inlL2 ℝ E E' ∘L fstL 2 ℝ E E').range ∩ fstL 2 ℝ E E' ⁻¹' Ω) :=
  (inrL2 ℝ E E').continuous.comp_continuousOn
    (hf.comp (fstL 2 ℝ E E').continuous.continuousOn fun _ hp ↦ hp.2)

/-- The shear `Φ (x, y) = (x, f x + y)` over `Ω`, with inverse `(x, z) ↦ (x, z - f x)`: the inverse
of the chart straightening the graph of `x ↦ (0, f x)` over the range `E × {0}` of the projection
`(x, y) ↦ (x, 0)`. It factors the submersion `g (x, y) = f x + y` as `g = π ∘ Φ`. -/
private def shear (hf : ContinuousOn f Ω) :
    OpenPartialHomeomorph (WithLp 2 (E × E')) (WithLp 2 (E × E')) :=
  ((inlL2 ℝ E E' ∘L fstL 2 ℝ E E').projectionGraphChart (fun p ↦ inrL2 ℝ E E' (f p.fst))
    (Ω.isOpen.preimage (fstL 2 ℝ E E').continuous) (continuousOn_shearDisp hf)
    fun _ _ ↦ by simp).symm

private theorem shear_apply (hf : ContinuousOn f Ω) (p : WithLp 2 (E × E')) :
    shear hf p = p + inrL2 ℝ E E' (f p.fst) := by
  simp [shear]

private theorem mem_shear_source {hf : ContinuousOn f Ω} {p : WithLp 2 (E × E')} :
    p ∈ (shear hf).source ↔ p.fst ∈ Ω := by
  simp [shear]

private theorem mem_shear_target {hf : ContinuousOn f Ω} {p : WithLp 2 (E × E')} :
    p ∈ (shear hf).target ↔ p.fst ∈ Ω := by
  simp [shear]

/-- The displacement `(x, y) ↦ (0, f x)` is smooth at points with `x ∈ Ω`. -/
private theorem contDiffAt_shearDisp (hf : ContDiffOn ℝ ∞ f Ω) {p : WithLp 2 (E × E')}
    (hp : p.fst ∈ Ω) :
    ContDiffAt ℝ ∞ (fun q : WithLp 2 (E × E') ↦ inrL2 ℝ E E' (f q.fst)) p :=
  (inrL2 ℝ E E').contDiff.contDiffAt.comp p
    ((hf.contDiffAt (Ω.isOpen.mem_nhds hp)).comp p (fstL 2 ℝ E E').contDiff.contDiffAt)

private theorem contDiffOn_shear (hf : ContDiffOn ℝ ∞ f Ω) :
    ContDiffOn ℝ (⊤ : ℕ∞) (shear hf.continuousOn) (shear hf.continuousOn).source := fun p hp ↦
  (ContinuousLinearMap.contDiffAt_projectionGraphChart_symm _ _ _ _ _
    (contDiffAt_shearDisp hf (by simpa using mem_shear_source.1 hp))).contDiffWithinAt

private theorem contDiffOn_shear_symm (hf : ContDiffOn ℝ ∞ f Ω) :
    ContDiffOn ℝ (⊤ : ℕ∞) (shear hf.continuousOn).symm (shear hf.continuousOn).target :=
  fun p hp ↦ (ContinuousLinearMap.contDiffAt_projectionGraphChart _ _ _ _ _
    (contDiffAt_shearDisp hf (by simpa using mem_shear_target.1 hp))).contDiffWithinAt

/-- The derivative of the shear is `(u, v) ↦ (u, Df(x) u + v)`. -/
private theorem hasFDerivAt_shear (hf : ContDiffOn ℝ ∞ f Ω) {p : WithLp 2 (E × E')}
    (hp : p.fst ∈ Ω) :
    HasFDerivAt (shear hf.continuousOn)
      (ContinuousLinearMap.id ℝ _ + inrL2 ℝ E E' ∘L fderiv ℝ f p.fst ∘L fstL 2 ℝ E E') p := by
  have hfd : HasFDerivAt f (fderiv ℝ f p.fst) p.fst := (differentiableAt_of_mem hf hp).hasFDerivAt
  have h : ⇑(shear hf.continuousOn) = fun q ↦ q + inrL2 ℝ E E' (f q.fst) :=
    funext (shear_apply hf.continuousOn)
  rw [h]
  exact (hasFDerivAt_id p).add
    ((inrL2 ℝ E E').hasFDerivAt.comp p (hfd.comp p (fstL 2 ℝ E E').hasFDerivAt))

private theorem surjective_fderiv_shear (hf : ContDiffOn ℝ ∞ f Ω) {p : WithLp 2 (E × E')}
    (hp : p.fst ∈ Ω) : Surjective (fderiv ℝ (shear hf.continuousOn) p) := fun w ↦
  ⟨w - inrL2 ℝ E E' (fderiv ℝ f p.fst w.fst), by
    rw [(hasFDerivAt_shear hf hp).fderiv]
    simp⟩

/-- The submersion `g (x, y) = f x + y` is the projection `(x, z) ↦ z` after the shear. -/
private theorem sndL_comp_shear (hf : ContinuousOn f Ω) :
    ⇑(sndL 2 ℝ E E') ∘ shear hf = addSnd f := by
  ext p
  simp [shear_apply, add_comm]

/-- The open set `E × Ω'` on which `(x, z) ↦ z` maps into `Ω'`. -/
private def sndPreimage (Ω' : Opens E') : Opens (WithLp 2 (E × E')) :=
  ⟨sndL 2 ℝ E E' ⁻¹' Ω', Ω'.isOpen.preimage (sndL 2 ℝ E E').continuous⟩

@[simp]
private theorem mem_sndPreimage {p : WithLp 2 (E × E')} :
    p ∈ sndPreimage Ω' ↔ sndL 2 ℝ E E' p ∈ Ω' :=
  Iff.rfl

private theorem mapsTo_sndL_sndPreimage :
    MapsTo (sndL 2 ℝ E E') (sndPreimage (E := E) Ω') Ω' := fun _ hp ↦ mem_sndPreimage.1 hp

private theorem addSndDomain_subset_shear_source (hf : ContinuousOn f Ω) :
    (addSndDomain hf Ω' : Set (WithLp 2 (E × E'))) ⊆ (shear hf).source := fun _ hp ↦
  mem_shear_source.2 (mem_addSndDomain.1 hp).1

private theorem mapsTo_shear_addSndDomain (hf : ContinuousOn f Ω) :
    MapsTo (shear hf) (addSndDomain hf Ω')
      (sndPreimage (E := E) Ω' : Set (WithLp 2 (E × E'))) := fun p hp ↦ by
  rw [SetLike.mem_coe, mem_sndPreimage, ← comp_apply (f := ⇑(sndL 2 ℝ E E')), sndL_comp_shear]
  exact mapsTo_addSnd hf hp

end Shear

/-! ### The cone `g^* Γ` of the submersion `(x, y) ↦ f x + y` -/

section AddSndCone

variable [FiniteDimensional ℝ E] [FiniteDimensional ℝ E'] {Ω : Opens E} {Ω' : Opens E'}
  {f : E → E'} {Γ : Set (E' × E')}

/-- The second component `(x, y) ↦ y` recovers `η` from `Dg(x, y)ᵀ η = (Df(x)ᵀ η, η)`. -/
private theorem sndL_adjoint_fderiv_addSnd (hf : ContDiffOn ℝ ∞ f Ω) {p : WithLp 2 (E × E')}
    (hp : p ∈ addSndDomain hf.continuousOn Ω') (η : E') :
    sndL 2 ℝ E E' ((fderiv ℝ (addSnd f) p).adjoint η) = η := by
  simp [adjoint_fderiv_addSnd_apply (differentiableAt_of_mem hf (mem_addSndDomain.1 hp).1)]

/-- **The cone `g^* Γ` is closed** in `W × ((E × E') \ {0})`, since the transpose of
`Dg(x, y)` has the continuous left inverse `(x, y) ↦ y`. -/
private theorem isOpen_diff_covectorPullback_addSnd (hf : ContDiffOn ℝ ∞ f Ω)
    (hΓ : IsOpen (((Ω' : Set E') ×ˢ {0}ᶜ) \ Γ)) :
    IsOpen (((addSndDomain hf.continuousOn Ω' : Set (WithLp 2 (E × E'))) ×ˢ {0}ᶜ) \
      covectorPullback (addSnd f) (addSndDomain hf.continuousOn Ω') Γ) :=
  isOpen_diff_covectorPullback_of_leftInverse (addSndDomain hf.continuousOn Ω').isOpen
    (mapsTo_addSnd hf.continuousOn) (contDiffOn_addSnd hf).continuousOn
    ((contDiffOn_addSnd hf).continuousOn_fderiv_of_isOpen (addSndDomain _ _).isOpen (by simp))
    (fun _ ↦ sndL 2 ℝ E E') continuousOn_const (fun _ hp ↦ sndL_adjoint_fderiv_addSnd hf hp) hΓ

/-- The cone `g^* Γ` contains no zero covector, since the transpose of `Dg(x, y)` is injective. -/
private theorem ne_zero_of_mem_covectorPullback_addSnd (hf : ContDiffOn ℝ ∞ f Ω)
    (hΓ0 : ∀ p ∈ Γ, p.2 ≠ 0) {q : WithLp 2 (E × E') × WithLp 2 (E × E')}
    (hq : q ∈ covectorPullback (addSnd f) (addSndDomain hf.continuousOn Ω') Γ) : q.2 ≠ 0 :=
  ne_zero_of_mem_covectorPullback
    (fun _ hp ↦ LeftInverse.injective (sndL_adjoint_fderiv_addSnd hf hp)) hΓ0 hq

/-- **The chain rule for the cones.** Pulling `Γ` back along the projection `π (x, z) = z` and
then along the shear `Φ` gives covectors of `g^* Γ`, since `g = π ∘ Φ`. -/
private theorem covectorPullback_shear_subset (hf : ContDiffOn ℝ ∞ f Ω) :
    covectorPullback (shear hf.continuousOn) (addSndDomain hf.continuousOn Ω')
        (pullbackLinearCone (sndL 2 ℝ E E') Γ) ⊆
      covectorPullback (addSnd f) (addSndDomain hf.continuousOn Ω') Γ := by
  rintro ⟨p, ζ⟩ hmem
  obtain ⟨hp, ζ₁, hζ₁, hζ₁ζ⟩ := mem_covectorPullback.1 hmem
  obtain ⟨η, hη, hηζ₁⟩ := mem_pullbackLinearCone.1 hζ₁
  have hpΩ := (mem_addSndDomain.1 hp).1
  have hg : sndL 2 ℝ E E' (shear hf.continuousOn p) = addSnd f p :=
    congrFun (sndL_comp_shear hf.continuousOn) p
  have hd : fderiv ℝ (addSnd f) p = sndL 2 ℝ E E' ∘L fderiv ℝ (shear hf.continuousOn) p := by
    rw [← sndL_comp_shear hf.continuousOn, fderiv_comp p (sndL 2 ℝ E E').differentiableAt
      (hasFDerivAt_shear hf hpΩ).differentiableAt, ContinuousLinearMap.fderiv]
  refine mem_covectorPullback.2 ⟨hp, η, by rwa [← hg], ?_⟩
  rw [hd, adjoint_comp, ContinuousLinearMap.comp_apply, hηζ₁, hζ₁ζ]

/-- Restricting `g^* Γ` to `E × {0}` gives covectors of `f^* Γ`, since
`Dg(x, 0)ᵀ η = (Df(x)ᵀ η, η)`. -/
private theorem pullbackInlCone_covectorPullback_addSnd_subset (hf : ContDiffOn ℝ ∞ f Ω) :
    pullbackInlCone (covectorPullback (addSnd f) (addSndDomain hf.continuousOn Ω') Γ) ⊆
      covectorPullback f Ω Γ := by
  rintro ⟨x, ξ⟩ hmem
  obtain ⟨η, hη⟩ := mem_pullbackInlCone.1 hmem
  have hxΩ : x ∈ Ω := by simpa using (mem_addSndDomain.1 (mem_covectorPullback.1 hη).1).1
  obtain ⟨-, hΓ, hξ⟩ := (mem_covectorPullback_addSnd_iff (p := toLp 2 (x, 0))
    (differentiableAt_of_mem hf hxΩ)).1 hη
  exact mem_covectorPullback.2 ⟨hxΩ, η, by simpa using hΓ, by simpa using hξ⟩

end AddSndCone

/-! ### The pullback as a composition -/

section Measurable

variable [FiniteDimensional ℝ E] [FiniteDimensional ℝ E'] [MeasurableSpace E] [BorelSpace E]
  [MeasurableSpace E'] [BorelSpace E'] {Ω : Opens E} {Ω' : Opens E'} {f : E → E'}
  {Γ : Set (E' × E')}

/-- **The submersion `g` factors through the shear.** The pullback along `g (x, y) = f x + y` is
the pullback along the projection `π (x, z) = z` followed by the pullback along the shear
`Φ (x, y) = (x, f x + y)`. -/
private theorem addSndPullback_eq (hf : ContDiffOn ℝ ∞ f Ω) (T : 𝓓'(Ω', ℂ)) :
    Distribution.addSndPullback hf T =
      Distribution.compCLMOfOpenPartialHomeomorph (shear hf.continuousOn) (contDiffOn_shear hf)
        (contDiffOn_shear_symm hf) (addSndDomain_subset_shear_source hf.continuousOn)
        (mapsTo_shear_addSndDomain hf.continuousOn)
        (Distribution.compCLMOfSubmersion volume volume (sndL 2 ℝ E E')
          (sndL 2 ℝ E E').contDiff.contDiffOn mapsTo_sndL_sndPreimage
          (fun x _ ↦ surjective_fderiv_of_surjective (sndL_surjective ℝ E E') x) T) := by
  have hg := sndL_comp_shear hf.continuousOn
  have hgf : ContDiffOn ℝ ∞ (sndL 2 ℝ E E' ∘ shear hf.continuousOn)
      (addSndDomain hf.continuousOn Ω') := hg ▸ contDiffOn_addSnd hf
  have hgfΩ : MapsTo (sndL 2 ℝ E E' ∘ shear hf.continuousOn) (addSndDomain hf.continuousOn Ω')
      Ω' := hg ▸ mapsTo_addSnd hf.continuousOn
  have hgfsurj : ∀ p ∈ addSndDomain hf.continuousOn Ω',
      Surjective (fderiv ℝ (sndL 2 ℝ E E' ∘ shear hf.continuousOn) p) :=
    hg ▸ surjective_fderiv_addSnd _ (hf.differentiableOn (by simp))
  rw [← Distribution.compCLMOfSubmersion_eq_compCLMOfOpenPartialHomeomorph volume
      (hsurj := fun p hp ↦ surjective_fderiv_shear hf (mem_addSndDomain.1 hp).1),
    ← Distribution.compCLMOfSubmersion_comp volume volume (ρ := volume) (hgf := hgf)
      (hgfΩ := hgfΩ) (hgfsurj := hgfsurj),
    Distribution.addSndPullback_eq_compCLMOfSubmersion]
  exact DFunLike.congr_fun (Distribution.compCLMOfSubmersion_congr volume volume hgf hgfΩ hgfsurj
    fun p _ ↦ congrFun hg p) T

end Measurable

/-! ### The pullback as a continuous linear map -/

namespace WaveFrontSpace

variable [FiniteDimensional ℝ E] [FiniteDimensional ℝ E'] [MeasurableSpace E] [BorelSpace E]
  [MeasurableSpace E'] [BorelSpace E'] {Ω : Opens E} {Ω' : Opens E'} {Γ : Set (E' × E')}

/-- **Continuity of the pullback along a smooth map in the normal topology.** Let `f` be smooth on
`Ω`, mapping `Ω` into `Ω'`, and let `Γ` be a cone of nonzero covectors over `Ω'`, closed in
`Ω' × (E' \ {0})`, which does not meet the normal set of `f`: no `(f x, η) ∈ Γ` with `x ∈ Ω` has
`Df(x)ᵀ η = 0`. Then the pullback `f^* T` (`Distribution.pullback`) is a continuous linear map from
`𝓓'_Γ(Ω')` to `𝓓'_{f^* Γ}(Ω)`, where `f^* Γ = {(x, Df(x)ᵀ η) | x ∈ Ω, (f x, η) ∈ Γ}`
(`TauCeti.covectorPullback`) (Brouder, Dang and Hélein, Theorem 6.3). -/
def pullbackCLM (f : E → E') (hf : ContDiffOn ℝ ∞ f Ω) (hfΩ : MapsTo f Ω Ω')
    (hΓ : IsOpen (((Ω' : Set E') ×ˢ {0}ᶜ) \ Γ))
    (hcone : ∀ p ∈ Γ, ∀ t : ℝ, 0 < t → (p.1, t • p.2) ∈ Γ) (hΓ0 : ∀ p ∈ Γ, p.2 ≠ 0)
    (hN : ∀ x ∈ Ω, ∀ η, (f x, η) ∈ Γ → (fderiv ℝ f x).adjoint η ≠ 0) :
    WaveFrontSpace Ω' Γ →L[ℂ] WaveFrontSpace Ω (covectorPullback f Ω Γ) :=
  inclusionCLM (pullbackInlCone_covectorPullback_addSnd_subset hf) ∘L
    pullbackInlCLM (mapsTo_inl_addSndDomain hf.continuousOn hfΩ)
      (isOpen_diff_covectorPullback_addSnd hf hΓ)
      (fun _ hp _ ht ↦ smul_mem_covectorPullback hcone hp ht)
      (fun _ hp ↦ ne_zero_of_mem_covectorPullback_addSnd hf hΓ0 hp)
      (fun x hx η _ ↦
        notMem_covectorPullback_addSnd (differentiableAt_of_mem hf hx) (hN x hx) η) ∘L
    inclusionCLM (covectorPullback_shear_subset hf) ∘L
    compCLMOfOpenPartialHomeomorph (shear hf.continuousOn) (contDiffOn_shear hf)
      (contDiffOn_shear_symm hf) (addSndDomain_subset_shear_source hf.continuousOn)
      (mapsTo_shear_addSndDomain hf.continuousOn)
      (isOpen_diff_pullbackLinearCone (sndPreimage Ω').isOpen mapsTo_sndL_sndPreimage
        (sndL_surjective ℝ E E') hΓ)
      (fun _ hp _ ht ↦ smul_mem_pullbackLinearCone hcone hp ht)
      (fun _ hp ↦ ne_zero_of_mem_pullbackLinearCone (sndL_surjective ℝ E E') hΓ0 hp) ∘L
    pullbackLinearCLM (sndL 2 ℝ E E') mapsTo_sndL_sndPreimage (sndL_surjective ℝ E E') hΓ hcone hΓ0

@[simp]
theorem toDistribution_pullbackCLM {f : E → E'} (hf : ContDiffOn ℝ ∞ f Ω)
    (hfΩ : MapsTo f Ω Ω') (hΓ : IsOpen (((Ω' : Set E') ×ˢ {0}ᶜ) \ Γ))
    (hcone : ∀ p ∈ Γ, ∀ t : ℝ, 0 < t → (p.1, t • p.2) ∈ Γ) (hΓ0 : ∀ p ∈ Γ, p.2 ≠ 0)
    (hN : ∀ x ∈ Ω, ∀ η, (f x, η) ∈ Γ → (fderiv ℝ f x).adjoint η ≠ 0)
    (u : WaveFrontSpace Ω' Γ) :
    (pullbackCLM f hf hfΩ hΓ hcone hΓ0 hN u).toDistribution =
      u.toDistribution.pullback f hf hfΩ fun x hx η hη ↦
        hN x hx η (u.waveFrontSet_toDistribution_subset hη) := by
  simp only [pullbackCLM, ContinuousLinearMap.comp_apply, toDistribution_inclusionCLM,
    toDistribution_pullbackInlCLM, toDistribution_compCLMOfOpenPartialHomeomorph,
    toDistribution_pullbackLinearCLM]
  rw [Distribution.pullback_eq_pullbackInl hf hfΩ _ (addSndPullback_eq hf _)]

end WaveFrontSpace

end TauCeti

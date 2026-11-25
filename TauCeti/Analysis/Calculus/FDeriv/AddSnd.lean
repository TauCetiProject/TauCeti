/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Topology.Sets.Opens
public import TauCeti.Analysis.InnerProductSpace.ProdL2
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# The submersion `(x, y) ↦ f x + y`

For a map `f : E → E'` between real normed spaces, the map `g (x, y) = f x + y` on the
Euclidean product `WithLp 2 (E × E')` (`TauCeti.addSnd`) factors `f` as `x ↦ g (x, 0)`. If `f` is
differentiable on an open set `Ω`, then `g` is a submersion on the open set
`W = {(x, y) | x ∈ Ω, f x + y ∈ Ω'}` (`TauCeti.addSndDomain`) and maps it into `Ω'`. Its
derivative is `Dg(x, y) (u, v) = Df(x) u + v`, with transpose `η ↦ (Df(x)ᵀ η, η)`. This is how
Hörmander reduces the pullback of a distribution along `f` to a pullback along a submersion.
The transpose is stated for inner product spaces, the only place where an inner product enters.

## Main declarations

* `TauCeti.addSnd`: the map `g (x, y) = f x + y`.
* `TauCeti.addSndDomain`: the open set `{(x, y) | x ∈ Ω, f x + y ∈ Ω'}`.
* `TauCeti.contDiffOn_addSnd`, `TauCeti.mapsTo_addSnd`, `TauCeti.surjective_fderiv_addSnd`:
  `g` is a submersion from `W` into `Ω'`, as smooth as `f`.
* `TauCeti.fderiv_addSnd`, `TauCeti.adjoint_fderiv_addSnd_apply`: the derivative of `g` and its
  transpose.
* `TauCeti.mapsTo_inl_addSndDomain`: the inclusion `x ↦ (x, 0)` maps `Ω` into `W`.

## References

* L. Hörmander, *The Analysis of Linear Partial Differential Operators I*, second edition,
  Springer, 1990, proof of Theorem 8.2.4.
-/

public section

open Function Set TopologicalSpace WithLp
open scoped ContDiff

namespace TauCeti

section NormedSpace

variable {E E' : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup E'] [NormedSpace ℝ E'] {Ω : Opens E} {Ω' : Opens E'} {f : E → E'}

/-- The submersion `g (x, y) = f x + y` through which `f` factors as `x ↦ g (x, 0)`. -/
def addSnd (f : E → E') (p : WithLp 2 (E × E')) : E' :=
  f p.fst + p.snd

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℝ E'] in
/-- The value of `g (x, y) = f x + y`. -/
@[simp]
theorem addSnd_apply (f : E → E') (p : WithLp 2 (E × E')) : addSnd f p = f p.fst + p.snd :=
  (rfl)

private theorem addSnd_eq (f : E → E') :
    addSnd f = f ∘ fstL 2 ℝ E E' + sndL 2 ℝ E E' :=
  rfl

/-- The open set `{(x, y) | x ∈ Ω, f x + y ∈ Ω'}` on which `g` is a submersion into `Ω'`. -/
def addSndDomain (hf : ContinuousOn f Ω) (Ω' : Opens E') : Opens (WithLp 2 (E × E')) :=
  ⟨fstL 2 ℝ E E' ⁻¹' Ω ∩ addSnd f ⁻¹' Ω', by
    refine ContinuousOn.isOpen_inter_preimage ?_ (Ω.isOpen.preimage (fstL 2 ℝ E E').continuous)
      Ω'.isOpen
    rw [addSnd_eq]
    exact (hf.comp (fstL 2 ℝ E E').continuous.continuousOn (mapsTo_preimage _ _)).add
      (sndL 2 ℝ E E').continuous.continuousOn⟩

/-- Membership in `{(x, y) | x ∈ Ω, f x + y ∈ Ω'}`. -/
@[simp]
theorem mem_addSndDomain {hf : ContinuousOn f Ω} {p : WithLp 2 (E × E')} :
    p ∈ addSndDomain hf Ω' ↔ p.fst ∈ Ω ∧ f p.fst + p.snd ∈ Ω' :=
  Iff.rfl

/-- If `f` is `C^n` on `Ω`, then `g (x, y) = f x + y` is `C^n` on
`{(x, y) | x ∈ Ω, f x + y ∈ Ω'}`. -/
theorem contDiffOn_addSnd {n : WithTop ℕ∞} (hf : ContDiffOn ℝ n f Ω) :
    ContDiffOn ℝ n (addSnd f) (addSndDomain hf.continuousOn Ω') := by
  rw [addSnd_eq]
  exact ((hf.comp (fstL 2 ℝ E E').contDiff.contDiffOn (mapsTo_preimage _ _)).add
    (sndL 2 ℝ E E').contDiff.contDiffOn).mono inter_subset_left

/-- The map `g (x, y) = f x + y` maps `{(x, y) | x ∈ Ω, f x + y ∈ Ω'}` into `Ω'`. -/
theorem mapsTo_addSnd (hf : ContinuousOn f Ω) :
    MapsTo (addSnd f) (addSndDomain hf Ω') Ω' := fun _ hp ↦ by
  simpa using (mem_addSndDomain.1 hp).2

/-- If `f` is differentiable at `x`, the derivative of `g (x, y) = f x + y` is
`Dg(x, y) (u, v) = Df(x) u + v`. -/
theorem fderiv_addSnd {p : WithLp 2 (E × E')} (hf : DifferentiableAt ℝ f p.fst) :
    fderiv ℝ (addSnd f) p = (fderiv ℝ f p.fst).comp (fstL 2 ℝ E E') + sndL 2 ℝ E E' := by
  rw [addSnd_eq]
  exact ((hf.hasFDerivAt.comp p (fstL 2 ℝ E E').hasFDerivAt).add
    (sndL 2 ℝ E E').hasFDerivAt).fderiv

/-- If `f` is differentiable on `Ω`, then `g (x, y) = f x + y` has surjective derivative on
`{(x, y) | x ∈ Ω, f x + y ∈ Ω'}`. -/
theorem surjective_fderiv_addSnd (hc : ContinuousOn f Ω) (hf : DifferentiableOn ℝ f Ω) :
    ∀ p ∈ addSndDomain hc Ω', Surjective (fderiv ℝ (addSnd f) p) := fun p hp w ↦
  have hx := (mem_addSndDomain.1 hp).1
  ⟨toLp 2 (0, w), by simp [fderiv_addSnd ((hf _ hx).differentiableAt (Ω.isOpen.mem_nhds hx))]⟩

/-- The inclusion `x ↦ (x, 0)` maps `Ω` into `{(x, y) | x ∈ Ω, f x + y ∈ Ω'}`. -/
theorem mapsTo_inl_addSndDomain (hf : ContinuousOn f Ω) (hfΩ : MapsTo f Ω Ω') :
    MapsTo (fun x ↦ toLp 2 (x, (0 : E'))) (Ω : Set E) (addSndDomain hf Ω') := fun x hx ↦
  mem_addSndDomain.2 ⟨hx, by simpa using hfΩ hx⟩

end NormedSpace

section InnerProductSpace

variable {E E' : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup E'] [InnerProductSpace ℝ E'] [CompleteSpace E'] {f : E → E'}

/-- The transpose of `Dg(x, y)` is `η ↦ (Df(x)ᵀ η, η)`. -/
theorem adjoint_fderiv_addSnd_apply {p : WithLp 2 (E × E')} (hf : DifferentiableAt ℝ f p.fst)
    (η : E') :
    (fderiv ℝ (addSnd f) p).adjoint η = toLp 2 ((fderiv ℝ f p.fst).adjoint η, η) := by
  rw [fderiv_addSnd hf, map_add, ContinuousLinearMap.adjoint_comp, adjoint_fstL,
    adjoint_sndL]
  refine ofLp_injective 2 ?_
  ext <;> simp

end InnerProductSpace

end TauCeti

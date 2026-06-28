/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Analysis.InnerProductSpace.HarmonicIsometry

/-!
# Dilation invariance of the Laplacian and harmonic functions

`TauCeti.Analysis.InnerProductSpace.Laplacian` and
`TauCeti.Analysis.InnerProductSpace.HarmonicIsometry` record invariance under rigid motions.
This file adds the companion scale-change bookkeeping: under the right-composition
`x ↦ c • x`, the Laplacian scales by `c ^ 2`, and harmonicity is preserved and reflected when
`c ≠ 0`.

These lemmas are a small Lane C prerequisite from the PDE roadmap. They let later mean-value,
maximum-principle, and Poisson-kernel arguments normalize balls by translating and rescaling
without reproving the Laplacian calculation each time.

## Main declarations

* `TauCeti.laplacian_comp_smul_right`: `Δ (fun x ↦ f (c • x)) =
  fun x ↦ c ^ 2 • Δ f (c • x)`.
* `TauCeti.harmonicAt_comp_smul_right_iff`: harmonicity is invariant under nonzero dilation.
* `TauCeti.harmonicOnNhd_comp_smul_right_iff`: set-level nonzero dilation invariance.
-/

public section

noncomputable section

namespace TauCeti

open InnerProductSpace Laplacian Topology

variable
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [NormedSpace ℝ F] in
/-- Scalar dilation as a continuous linear equivalence. -/
private abbrev smulLeftContinuousLinearEquiv (c : ℝ) (hc : c ≠ 0) : E ≃L[ℝ] E :=
  ContinuousLinearEquiv.smulLeft (Units.mk0 c hc)

omit [FiniteDimensional ℝ E] in
private lemma smulLeftContinuousLinearEquiv_apply (c : ℝ) (hc : c ≠ 0) (x : E) :
    smulLeftContinuousLinearEquiv (E := E) c hc x = c • x := by
  simp [smulLeftContinuousLinearEquiv]

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [NormedSpace ℝ F] in
/-- Precomposition by a homeomorphism transports vanishing in a neighbourhood. -/
private theorem eventuallyEq_zero_comp_homeomorph_iff (h : E ≃ₜ E) (g : E → F) (x : E) :
    (g ∘ h =ᶠ[𝓝 x] 0) ↔ (g =ᶠ[𝓝 (h x)] 0) := by
  rw [← h.map_nhds_eq x]
  constructor
  · intro hyp
    refine Filter.eventually_map.mpr ?_
    filter_upwards [hyp] with y hy
    simpa using hy
  · intro hyp
    have hyp' := Filter.eventually_map.mp hyp
    filter_upwards [hyp'] with y hy
    simpa using hy

/-- **Scaling law for the Laplacian under dilation.**

Right-composition by `x ↦ c • x` multiplies the Laplacian by `c ^ 2`. The statement is
unconditional in `f`, matching Mathlib's unconditional definition of `Δ` through iterated
Fréchet derivatives. -/
theorem laplacian_comp_smul_right (c : ℝ) (f : E → F) :
    Δ (fun x ↦ f (c • x)) = fun x ↦ c ^ 2 • (Δ f) (c • x) := by
  by_cases hc : c = 0
  · subst c
    ext x
    simp
  · let l : E ≃L[ℝ] E := smulLeftContinuousLinearEquiv c hc
    have hfun : (fun x : E ↦ f (c • x)) = f ∘ l := by
      funext x
      simp [l, smulLeftContinuousLinearEquiv]
    rw [hfun]
    ext x
    simp only [laplacian_eq_iteratedFDeriv_orthonormalBasis (f ∘ l)
      (stdOrthonormalBasis ℝ E), laplacian_eq_iteratedFDeriv_orthonormalBasis f
      (stdOrthonormalBasis ℝ E), Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    have hder :
        (iteratedFDeriv ℝ 2 (f ∘ l) x)
            ![(stdOrthonormalBasis ℝ E) i, (stdOrthonormalBasis ℝ E) i] =
          ((iteratedFDeriv ℝ 2 f (l x)).compContinuousLinearMap fun _ => (l : E →L[ℝ] E))
            ![(stdOrthonormalBasis ℝ E) i, (stdOrthonormalBasis ℝ E) i] := by
      have h := l.iteratedFDerivWithin_comp_right f uniqueDiffOn_univ (Set.mem_univ (l x)) 2
      simpa [← iteratedFDerivWithin_univ, Set.preimage_univ] using
        congrArg
          (fun L : ContinuousMultilinearMap ℝ (fun _ : Fin 2 => E) F =>
            L ![(stdOrthonormalBasis ℝ E) i, (stdOrthonormalBasis ℝ E) i]) h
    rw [hder]
    rw [ContinuousMultilinearMap.compContinuousLinearMap_apply]
    have hx : l x = c • x := by
      simp [l, smulLeftContinuousLinearEquiv]
    rw [hx]
    let M := iteratedFDeriv ℝ 2 f (c • x)
    let v : Fin 2 → E := ![(stdOrthonormalBasis ℝ E) i, (stdOrthonormalBasis ℝ E) i]
    change M (fun j => c • v j) = c ^ 2 • M v
    simpa [M, v, pow_two] using M.map_smul_univ (fun _ : Fin 2 => c) v

/-- **Harmonicity is invariant under nonzero dilation.**

For `c ≠ 0`, the function `x ↦ f (c • x)` is harmonic at `x` iff `f` is harmonic at
`c • x`. -/
theorem harmonicAt_comp_smul_right_iff (c : ℝ) (hc : c ≠ 0) {f : E → F} {x : E} :
    HarmonicAt (fun y ↦ f (c • y)) x ↔ HarmonicAt f (c • x) := by
  let l : E ≃L[ℝ] E := smulLeftContinuousLinearEquiv c hc
  have hfun : (fun y : E ↦ f (c • y)) = f ∘ l := by
    funext y
    simp [l, smulLeftContinuousLinearEquiv]
  have hcd : ContDiffAt ℝ 2 (fun y : E ↦ f (c • y)) x ↔
      ContDiffAt ℝ 2 f (c • x) := by
    rw [hfun]
    have h := l.contDiffAt_comp_iff (f := f) (n := 2) (x := l x)
    have hx₁ : l.symm (l x) = x := by simp
    have hx₂ : l x = c • x := by
      simp [l, smulLeftContinuousLinearEquiv]
    rwa [hx₁, hx₂] at h
  have hlap : (Δ (fun y : E ↦ f (c • y)) =ᶠ[𝓝 x] 0) ↔
      (Δ f =ᶠ[𝓝 (c • x)] 0) := by
    rw [laplacian_comp_smul_right c f]
    have hscale : (fun y : E ↦ c ^ 2 • (Δ f) (c • y)) = (fun z ↦ c ^ 2 • z) ∘ (Δ f ∘ l) := by
      funext y
      simp [l, smulLeftContinuousLinearEquiv, Function.comp_apply]
    rw [hscale]
    have hzero : Function.Injective (fun z : F ↦ c ^ 2 • z) := by
      exact smul_right_injective F (pow_ne_zero 2 hc)
    constructor
    · intro h
      have h' : Δ f ∘ l =ᶠ[𝓝 x] 0 := by
        filter_upwards [h] with y hy
        exact hzero (by simpa using hy)
      have := eventuallyEq_zero_comp_homeomorph_iff l.toHomeomorph (Δ f) x
      have hmain := this.1 h'
      simpa [l, smulLeftContinuousLinearEquiv] using hmain
    · intro h
      have := eventuallyEq_zero_comp_homeomorph_iff l.toHomeomorph (Δ f) x
      have h' : Δ f ∘ l =ᶠ[𝓝 x] 0 := this.2 (by simpa [l, smulLeftContinuousLinearEquiv] using h)
      filter_upwards [h'] with y hy
      change c ^ 2 • (Δ f (l y)) = 0
      have hy0 : Δ f (l y) = 0 := by simpa [Function.comp_apply] using hy
      rw [hy0]
      simp
  exact ⟨fun hf ↦ ⟨hcd.1 hf.1, hlap.1 hf.2⟩,
    fun hf ↦ ⟨hcd.2 hf.1, hlap.2 hf.2⟩⟩

/-- Harmonicity on a neighbourhood of a set is invariant under nonzero dilation. -/
theorem harmonicOnNhd_comp_smul_right_iff (c : ℝ) (hc : c ≠ 0) {f : E → F}
    {s : Set E} :
    HarmonicOnNhd (fun y ↦ f (c • y)) ((fun y ↦ c • y) ⁻¹' s) ↔
      HarmonicOnNhd f s := by
  let l : E ≃L[ℝ] E := smulLeftContinuousLinearEquiv c hc
  constructor
  · intro hf y hy
    have hy' : c • (l.symm y) = y := by
      change l (l.symm y) = y
      exact l.apply_symm_apply y
    have hpre : c • (l.symm y) ∈ s := by rwa [hy']
    have h := hf (l.symm y) hpre
    simpa [hy'] using (harmonicAt_comp_smul_right_iff c hc).1 h
  · intro hf x hx
    exact (harmonicAt_comp_smul_right_iff c hc).2 (hf (c • x) hx)

end TauCeti

end

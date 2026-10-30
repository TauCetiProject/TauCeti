/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.BochnerLinearization
public import TauCeti.LinearAlgebra.End.SquareZero

/-!
# Face germs detect the ambient ineffective kernel

Consider a finite group fixing a point `x`, a chart `χ` centred at `x` in a Banach space
over a nontrivially normed field in which the group order is invertible, and a continuous
linear map `q` to the normal-coordinate space. Suppose the action's coordinate maps are strictly
differentiable at the origin. An element preserving the normal coordinates near `x` acts as the
identity near `x` if and only if it fixes the germ parametrized
by `χ.symm` on `ker q`. More generally, testing on a subset of this kernel with unique
derivatives at zero suffices, including relative quadrants when that hypothesis is verified.

The map `q` may collect several labelled normal coordinates, so the result applies equally
to face intersections. It need not be surjective. Preserving the normal coordinates themselves
is essential: reflection in a hyperplane fixes that hyperplane but not an ambient neighborhood.
No faithfulness hypothesis is imposed, and the conclusion retains the actual group elements.

The proof combines finite-order shear rigidity with the derivative detection theorem from
Bochner linearization. This is a local statement in straightened coordinates; it does not
construct collars or assert the same conclusion for face-permuting actions.

## References

* S. Bochner, *Compact groups of differentiable transformations*, Ann. of Math. (2) 46
  (1945), 372–381.
* A. Adem, J. Leida and Y. Ruan, *Orbifolds and Stringy Topology*, Chapter 1.
-/

public section

open Filter Topology TauCeti

namespace OpenPartialHomeomorph

variable {𝕜 G X E F : Type*} [NontriviallyNormedField 𝕜] [Group G] [Fintype G]
  [Invertible (Fintype.card G : 𝕜)]
  [TopologicalSpace X] [MulAction G X] [ContinuousConstSMul G X]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- For a finite action fixing `x`, an element preserving linear normal coordinates in a chart
centred at `x` has identity germ on the common coordinate kernel if and only if it has identity
ambient germ. The test set `s` in the kernel need only have unique derivatives at zero,
so it can be a relative quadrant rather than a whole neighborhood. The coordinate maps need
only be strictly differentiable at the origin; normal coordinates need only be preserved
near it. The group order must be invertible in the coefficient field. -/
theorem eventually_smul_eq_iff_on_ker (χ : OpenPartialHomeomorph X E) {x : X}
    (hx : x ∈ χ.source) (hχx : χ x = 0) (hfix : ∀ g : G, g • x = x)
    (q : E →L[𝕜] F) {s : Set q.ker} (hs : UniqueDiffWithinAt 𝕜 s 0)
    {L : G → E →L[𝕜] E}
    (hL : ∀ g : G, HasStrictFDerivAt (χ ∘ (g • ·) ∘ χ.symm) (L g) 0)
    (g : G) (hq : q ∘ χ ∘ (g • ·) ∘ χ.symm =ᶠ[𝓝 0] q) :
    (∀ᶠ y : X in 𝓝 x, g • y = y) ↔
      ∀ᶠ v : q.ker in 𝓝[s] 0, g • χ.symm (v : E) = χ.symm (v : E) := by
  have hx0 : (0 : E) ∈ χ.target := hχx ▸ χ.map_source hx
  have hχsymm0 : χ.symm 0 = x := by rw [← hχx, χ.left_inv hx]
  have hT : Tendsto (fun v : q.ker ↦ χ.symm (v : E)) (𝓝[s] 0) (𝓝 x) := by
    have h := (χ.continuousAt_symm hx0).tendsto.comp
      (q.ker.subtypeL.continuous.tendsto (0 : q.ker))
    simpa [hχsymm0, Function.comp_def] using h.mono_left nhdsWithin_le_nhds
  constructor
  · exact fun h ↦ hT.eventually h
  · intro hface
    have hD (a : G) : HasStrictFDerivAt (χ ∘ (a • ·) ∘ χ.symm) (L a) (χ x) := by
      rw [hχx]
      exact hL a
    let σ := isotropyRepresentation hx hfix fun a ↦ (hD a).differentiableAt
    have hσ (a : G) : σ a = L a := by
      rw [isotropyRepresentation_apply, (hD a).hasFDerivAt.fderiv]
    have hderiv (a : G) : HasFDerivAt (χ ∘ (a • ·) ∘ χ.symm) (σ a) 0 := by
      rw [hσ]
      exact (hL a).hasFDerivAt
    -- Restrict the actual chart inverse to the kernel; its points lie in the target near zero.
    have hright : ∀ᶠ v : q.ker in 𝓝[s] 0, χ (χ.symm (v : E)) = (v : E) := by
      apply Filter.Eventually.filter_mono nhdsWithin_le_nhds
      simpa using (q.ker.subtypeL.continuous.tendsto (0 : q.ker)).eventually
        (χ.eventually_right_inverse hx0)
    have hface' : (χ ∘ (g • ·) ∘ χ.symm) ∘ q.ker.subtypeL =ᶠ[𝓝[s] 0] q.ker.subtypeL := by
      filter_upwards [hface, hright] with v hv hrv
      simp [Function.comp_def, hv, hrv]
    -- Differentiate the identity on the tangent kernel, using its actual subspace topology.
    have hfaceDeriv : (σ g).comp q.ker.subtypeL = q.ker.subtypeL := by
      have hd := (hderiv g).comp_hasFDerivWithinAt (s := s) (0 : q.ker)
        q.ker.subtypeL.hasFDerivAt.hasFDerivWithinAt
      apply hs.eq hd
      exact q.ker.subtypeL.hasFDerivAt.hasFDerivWithinAt.congr_of_eventuallyEq hface'
        (by simp [Function.comp_def, hχsymm0, hfix, hχx])
    -- Preserved normal coordinates force the displacement range into the tangent kernel.
    have hnormal : q.comp (σ g) = q := by
      have hd := q.hasFDerivAt.comp (0 : E) (hderiv g)
      exact hd.unique (q.hasFDerivAt.congr_of_eventuallyEq hq)
    have hfixed : q.ker ≤ LinearMap.ker ((σ g : Module.End 𝕜 E) - 1) := by
      intro v hv
      have h := DFunLike.congr_fun hfaceDeriv ⟨v, hv⟩
      simpa using sub_eq_zero.mpr h
    have hrange : LinearMap.range ((σ g : Module.End 𝕜 E) - 1) ≤ q.ker := by
      rintro v ⟨w, rfl⟩
      have h := DFunLike.congr_fun hnormal w
      simpa using sub_eq_zero.mpr h
    have hpow : (σ g : Module.End 𝕜 E) ^ Fintype.card G = 1 := by
      have h : (σ g) ^ Fintype.card G = 1 := by
        rw [← map_pow, pow_card_eq_one, map_one]
      simpa using congrArg ContinuousLinearMap.toLinearMap h
    have hone : σ g = 1 := ContinuousLinearMap.coe_injective <|
      Module.End.eq_one_of_pow_eq_one_of_range_sub_one_le (σ g : Module.End 𝕜 E) q.ker
        (Invertible.ne_zero _) hpow hfixed hrange
    exact MulAction.mem_germKernel.mp <|
      (χ.map_eq_one_iff_mem_germKernel hx hfix σ
        (hasStrictFDerivAt_conj_smul_isotropyRepresentation hx hfix hD) g).mp hone

end OpenPartialHomeomorph

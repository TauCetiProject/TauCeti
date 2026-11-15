/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Morse.Bott.Basic

/-!
# A function along a transverse slice of a critical submanifold

Let `i : S → M` be a critical submanifold of a function `f` on a boundaryless manifold
(`TauCeti.SmoothEmbedding.IsCriticalSubmanifold`), and let `φ : V → M` be a map from a normed space
with `φ y = i s`, which is `C²` at `y`. This file reads `f` along `φ`: the **slice** `f ∘ φ` is a
function on `V`.

The slice has a critical point at `y`, since `df` vanishes at `i s`. Its Hessian there is the
normal Hessian of the submanifold (`TauCeti.SmoothEmbedding.IsCriticalSubmanifold.normalHessian`)
evaluated on the normal classes of the images of its arguments under the derivative of `φ`: this
is the second-order chain rule at a critical point (`TauCeti.criticalHessian_comp_apply`), and
the critical Hessian vanishes on the tangent space of the submanifold. No condition is put on the
derivative of `φ` for these two statements.

Call `φ` **transverse** at `y` when `v ↦ [dφ_y v]`, the derivative of `φ` followed by the
projection to the normal space `T_{i s} M ⧸ T_{i s} S`, is bijective; the fibres of a tubular
neighbourhood of the submanifold, and the normal exponential on the orthogonal normal space, are
such slices. For a transverse slice the Hessian of `f ∘ φ` at `y` is the normal Hessian read
through a linear isomorphism, so:

* if the submanifold is Morse–Bott, `y` is a nondegenerate critical point of `f ∘ φ`;
* conversely, if `y` is a nondegenerate critical point of `f ∘ φ`, the normal Hessian at `s` is
  nondegenerate;
* the Morse index of `f ∘ φ` at `y` is the Morse index of `f` at `i s`.

This is Bott's description of a nondegenerate critical manifold: the restriction of `f` to each
normal slice has a nondegenerate critical point on the core, of the index of the critical manifold.
It is what makes the fibre restrictions of `f` read through a tubular neighbourhood satisfy the
hypotheses of the parametric Morse lemma on a vector bundle
(`TauCeti.exists_parametric_morse_partialDiffeomorph`).

## Main results

In the namespace `TauCeti.SmoothEmbedding`:

* `IsCriticalSubmanifold.fderiv_comp_eq_zero`: a slice through the submanifold is critical there.
* `IsCriticalSubmanifold.fderiv_fderiv_comp_apply`: its Hessian there is the normal Hessian of
  the normal classes of the derivatives.
* `IsNondegenerateCriticalSubmanifold.isNondegenerateCriticalPoint_comp`: a transverse slice
  through a Morse–Bott submanifold has a nondegenerate critical point there.
* `IsCriticalSubmanifold.ker_normalHessian_eq_bot_of_isNondegenerateCriticalPoint_comp`: if a
  transverse slice has a nondegenerate critical point, the normal Hessian is nondegenerate.
* `IsCriticalSubmanifold.morseIndex_comp`: the Morse index of a transverse slice is the Morse
  index of `f` at the core point.

## References

* R. Bott, *Nondegenerate critical manifolds*, Annals of Mathematics 60 (1954), 248–261.
-/

public section

open Function
open scoped ContDiff Manifold

noncomputable section

namespace TauCeti.SmoothEmbedding

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [I.Boundaryless] [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I 2 M]
  {E' H' S : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
  {J : ModelWithCorners ℝ E' H'} [TopologicalSpace S] [ChartedSpace H' S]
  {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  {f : M → ℝ} {n : ℕ∞ω} {i : SmoothEmbedding J I n S M} (hn : n ≠ 0)
  {φ : V → M} {y : V} {s : S}

variable (i) in
/-- The linear map `v ↦ [dφ_y v]` from `V` to the normal space at `s`. For `φ y = i s`, its
bijectivity is the transversality of the slice `φ` to the submanifold. -/
private def sliceNormalMap (φ : V → M) (y : V) (s : S) : V →ₗ[ℝ] i.NormalSpace s hn :=
  -- Every tangent space of `M` is the model space `E`, so `dφ_y` lands in `T_{i s} M`.
  (i.normalClass s hn).comp ((mfderiv 𝓘(ℝ, V) I φ y).toLinearMap : V →ₗ[ℝ] E)

omit [I.Boundaryless] [IsManifold I 2 M] in
private theorem sliceNormalMap_apply (v : V) :
    i.sliceNormalMap hn φ y s v = i.normalClass s hn (mfderiv 𝓘(ℝ, V) I φ y v) :=
  rfl

omit [I.Boundaryless] [IsManifold I 2 M] in
private theorem surjective_sliceNormalMap_iff :
    Surjective (i.sliceNormalMap hn φ y s) ↔
      Surjective fun v : V ↦ i.normalClass s hn (mfderiv 𝓘(ℝ, V) I φ y v) :=
  Iff.rfl

omit [I.Boundaryless] [IsManifold I 2 M] in
private theorem bijective_sliceNormalMap_iff :
    Bijective (i.sliceNormalMap hn φ y s) ↔
      Bijective fun v : V ↦ i.normalClass s hn (mfderiv 𝓘(ℝ, V) I φ y v) :=
  Iff.rfl

namespace IsCriticalSubmanifold

variable (h : i.IsCriticalSubmanifold f)
include h

omit [I.Boundaryless] [IsManifold I 2 M] in
/-- **A slice through a critical submanifold is critical there.** If `φ y = i s` and `φ` is
differentiable at `y`, the derivative of `f ∘ φ` at `y` vanishes. -/
theorem fderiv_comp_eq_zero (hφy : φ y = i s) (hφ : MDifferentiableAt 𝓘(ℝ, V) I φ y) :
    fderiv ℝ (f ∘ φ) y = 0 := by
  have hf : MDifferentiableAt I 𝓘(ℝ) f (φ y) :=
    hφy ▸ (h.contMDiffAt s).mdifferentiableAt two_ne_zero
  have hcrit : mfderiv I 𝓘(ℝ) f (φ y) = 0 := by
    rw [hφy]
    exact mem_criticalPoints_iff_mfderiv_eq_zero.mp (h.mem_criticalPoints s)
  have hcomp := mfderiv_comp y hf hφ
  rw [hcrit, ContinuousLinearMap.zero_comp, mfderiv_eq_fderiv] at hcomp
  exact hcomp

/-- **The Hessian of a slice is the normal Hessian.** If `φ y = i s` and `φ` is `C²` at `y`, the
Hessian of `f ∘ φ` at `y` is the normal Hessian at `s` evaluated on the normal classes of the
images of its arguments under the derivative of `φ`. -/
theorem fderiv_fderiv_comp_apply (hφy : φ y = i s) (hφ : ContMDiffAt 𝓘(ℝ, V) I 2 φ y)
    (u w : V) :
    fderiv ℝ (fderiv ℝ (f ∘ φ)) y u w =
      h.normalHessian hn s (i.normalClass s hn (mfderiv 𝓘(ℝ, V) I φ y u))
        (i.normalClass s hn (mfderiv 𝓘(ℝ, V) I φ y w)) := by
  have key := criticalHessian_comp_apply hφy (h.contMDiffAt s) hφ (h.mem_criticalPoints s) u w
  rw [criticalHessian_modelSpace] at key
  exact key.trans (h.normalHessian_normalClass hn s _ _).symm

/-- In terms of `sliceNormalMap`, the Hessian of a slice is the normal Hessian. -/
private theorem fderiv_fderiv_comp_apply_sliceNormalMap (hφy : φ y = i s)
    (hφ : ContMDiffAt 𝓘(ℝ, V) I 2 φ y) (u w : V) :
    fderiv ℝ (fderiv ℝ (f ∘ φ)) y u w =
      h.normalHessian hn s (i.sliceNormalMap hn φ y s u) (i.sliceNormalMap hn φ y s w) := by
  rw [sliceNormalMap_apply, sliceNormalMap_apply]
  exact h.fderiv_fderiv_comp_apply hn hφy hφ u w

/-- **A transverse slice detects nondegeneracy.** If `φ y = i s`, `φ` is `C²` at `y`, the map
`v ↦ [dφ_y v]` onto the normal space at `s` is surjective, and `y` is a nondegenerate critical
point of `f ∘ φ`, then the normal Hessian of the submanifold at `s` is nondegenerate. -/
theorem ker_normalHessian_eq_bot_of_isNondegenerateCriticalPoint_comp (hφy : φ y = i s)
    (hφ : ContMDiffAt 𝓘(ℝ, V) I 2 φ y)
    (hsurj : Surjective fun v : V ↦ i.normalClass s hn (mfderiv 𝓘(ℝ, V) I φ y v))
    (hN : IsNondegenerateCriticalPoint (f ∘ φ) y) :
    LinearMap.ker (h.normalHessian hn s) = ⊥ := by
  obtain ⟨e, he⟩ := hN.isInvertible
  refine (Submodule.eq_bot_iff _).mpr fun p hp ↦ ?_
  obtain ⟨v, rfl⟩ := ((surjective_sliceNormalMap_iff hn).2 hsurj) p
  -- A normal class in the kernel of the normal Hessian pairs to zero with every normal class, so
  -- its preimage lies in the kernel of the invertible Hessian of the slice.
  have hv : v = 0 := by
    refine e.injective ?_
    rw [map_zero, ← ContinuousLinearEquiv.coe_coe, he]
    ext w
    rw [h.fderiv_fderiv_comp_apply_sliceNormalMap hn hφy hφ v w,
      LinearMap.congr_fun (LinearMap.mem_ker.mp hp), LinearMap.zero_apply, zero_apply]
  rw [hv, map_zero]

variable [FiniteDimensional ℝ E]

/-- **The index of a transverse slice.** If `φ y = i s`, `φ` is `C²` at `y` and the map
`v ↦ [dφ_y v]` from `V` to the normal space at `s` is bijective, then the Morse index of `f ∘ φ`
at `y` is the Morse index of `f` at `i s`. -/
theorem morseIndex_comp (hφy : φ y = i s) (hφ : ContMDiffAt 𝓘(ℝ, V) I 2 φ y)
    (hbij : Bijective fun v : V ↦ i.normalClass s hn (mfderiv 𝓘(ℝ, V) I φ y v)) :
    morseIndex (f ∘ φ) y = manifoldMorseIndex I f (i s) := by
  let L : V ≃ₗ[ℝ] i.NormalSpace s hn :=
    LinearEquiv.ofBijective _ ((bijective_sliceNormalMap_iff hn).2 hbij)
  have hQ : hessianQuadraticForm (f ∘ φ) y =
      (h.normalHessian hn s).toQuadraticMap.comp L.toLinearMap := by
    ext v
    rw [hessianQuadraticForm_apply, h.fderiv_fderiv_comp_apply_sliceNormalMap hn hφy hφ v v]
    simp [L]
  rw [morseIndex_def, hQ, ← h.sigNeg_normalHessian hn s]
  exact QuadraticMap.Equivalent.sigNeg_eq
    ⟨(QuadraticMap.isometryEquivOfCompLinearEquiv (h.normalHessian hn s).toQuadraticMap L).symm⟩

end IsCriticalSubmanifold

namespace IsNondegenerateCriticalSubmanifold

variable (h : i.IsNondegenerateCriticalSubmanifold f)
include h

/-- **Transverse slices of a Morse–Bott submanifold are nondegenerate.** If `φ y = i s`, `φ` is `C²`
at `y` and the map `v ↦ [dφ_y v]` from the finite-dimensional space `V` to the normal space at `s`
is bijective, then `y` is a nondegenerate critical point of `f ∘ φ`: its Hessian is the
nondegenerate normal Hessian read through a linear isomorphism. -/
theorem isNondegenerateCriticalPoint_comp [FiniteDimensional ℝ V] (hφy : φ y = i s)
    (hφ : ContMDiffAt 𝓘(ℝ, V) I 2 φ y)
    (hbij : Bijective fun v : V ↦ i.normalClass s hn (mfderiv 𝓘(ℝ, V) I φ y v)) :
    IsNondegenerateCriticalPoint (f ∘ φ) y := by
  have hf : ContMDiffAt I 𝓘(ℝ) 2 f (φ y) := hφy ▸ h.contMDiffAt s
  refine ⟨(hf.comp y hφ).contDiffAt,
    h.toIsCriticalSubmanifold.fderiv_comp_eq_zero hφy (hφ.mdifferentiableAt two_ne_zero),
    ContinuousLinearMap.isInvertible_of_injective ?_⟩
  exact h.injective_of_normalHessian_eq hn
    (LinearEquiv.ofBijective _ ((bijective_sliceNormalMap_iff hn).2 hbij)) fun u w ↦
    (h.toIsCriticalSubmanifold.fderiv_fderiv_comp_apply_sliceNormalMap hn hφy hφ u w).symm

end IsNondegenerateCriticalSubmanifold

end TauCeti.SmoothEmbedding

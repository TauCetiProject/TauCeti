/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Morse.Bott.Basic
public import TauCeti.Geometry.Manifold.TubularNeighborhood.Riemannian.Fiber

/-!
# A function along the normal fibres of a critical submanifold

Let `i : S → M` be a critical submanifold of a function `f` on a boundaryless Riemannian manifold
`M` (`TauCeti.SmoothEmbedding.IsCriticalSubmanifold`). At `s : S`, the normal exponential
(`TauCeti.SmoothEmbedding.normalExp`) sends the orthogonal complement `W` of the tangent space of
the submanifold at `i s` into `M`, by the Riemannian exponential at `i s`. Near `0` this is the
fibre over `s` of the tubular neighbourhood of the submanifold. This file reads `f` along it: the
**normal slice** `v ↦ f (exp_{i s} v)` is a function on the finite-dimensional inner product space
`W`, with value `f (i s)` at `0`.

The normal slice has a critical point at `0`, and its Hessian there is the normal Hessian of the
submanifold (`TauCeti.SmoothEmbedding.IsCriticalSubmanifold.normalHessian`) evaluated on normal
classes: the derivative of the normal exponential at `0` is the inclusion of `W` into the tangent
space, so this is the second-order chain rule at a critical point
(`TauCeti.criticalHessian_comp_apply`). Since `W` maps isomorphically onto the normal space, the
critical submanifold is Morse–Bott exactly when `0` is a nondegenerate critical point of every
normal slice. In general the Morse index of the normal slice at `0` is the Morse index of `f` at
`i s`. This is Bott's description of a nondegenerate critical manifold: `f` restricted to each
normal slice of a tubular neighbourhood has a nondegenerate critical point on the core, of the
index of the critical manifold. It identifies the vertical Hessian of `f` read through the normal
exponential, the fibre quadratic form of a Morse–Bott normal form on the normal bundle, with the
normal Hessian.

## Main results

In the namespace `TauCeti.SmoothEmbedding`:

* `IsCriticalSubmanifold.fderiv_comp_normalExp_fiber_zero`: the normal slice is critical at `0`.
* `IsCriticalSubmanifold.fderiv_fderiv_comp_normalExp_fiber_zero_apply`: its Hessian at `0` is the
  normal Hessian.
* `isNondegenerateCriticalSubmanifold_iff_forall_isNondegenerateCriticalPoint`, in the namespace
  `IsCriticalSubmanifold`: a critical submanifold is Morse–Bott exactly when every normal slice has
  a nondegenerate critical point at `0`.
* `IsCriticalSubmanifold.morseIndex_comp_normalExp_fiber_zero`: the Morse index of a normal slice
  at `0` is the Morse index of `f` at the core point.

## References

* R. Bott, *Nondegenerate critical manifolds*, Annals of Mathematics 60 (1954), 248–261.
-/

public noncomputable section

open Bundle Manifold Set Function Topology
open scoped ContDiff InnerProductSpace Manifold

namespace TauCeti.SmoothEmbedding

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  [RiemannianBundle (fun y : M ↦ TangentSpace I y)]
  [IsContMDiffRiemannianBundle I ∞ E (fun y : M ↦ TangentSpace I y)]
  {E' H' S P : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
  {J : ModelWithCorners ℝ E' H'} [TopologicalSpace S] [ChartedSpace H' S]
  {f : M → ℝ} {n : ℕ∞ω} {i : SmoothEmbedding J I n S M} (hn : n ≠ 0)

namespace IsCriticalSubmanifold

variable (h : i.IsCriticalSubmanifold f)
include h

/-- The normal slice `v ↦ f (exp_{i s} v)` of a critical submanifold is `C²` at `0`. -/
theorem contDiffAt_comp_normalExp_fiber_zero (s : S) :
    ContDiffAt ℝ 2
      (fun v : (i.tangentRange s hn)ᗮ ↦ f (i.normalExp (P := P) hn ⟨s, i.normalClass s hn v⟩))
      0 := by
  have hf : ContMDiffAt I 𝓘(ℝ) 2 f
      (i.normalExp (P := P) hn ⟨s, i.normalClass s hn ((0 : (i.tangentRange s hn)ᗮ) :
        TangentSpace I (i s))⟩) := by
    rw [i.normalExp_fiber_zero (P := P) hn s]
    exact h.contMDiffAt s
  exact (hf.comp (0 : (i.tangentRange s hn)ᗮ)
    ((i.contMDiffAt_normalExp_fiber_zero (P := P) hn s).of_le (by norm_cast))).contDiffAt

/-- The normal slice `v ↦ f (exp_{i s} v)` of a critical submanifold has a critical point at `0`.
-/
theorem fderiv_comp_normalExp_fiber_zero (s : S) :
    fderiv ℝ
      (fun v : (i.tangentRange s hn)ᗮ ↦ f (i.normalExp (P := P) hn ⟨s, i.normalClass s hn v⟩))
      0 = 0 := by
  have hcrit : i.normalExp (P := P) hn ⟨s, i.normalClass s hn ((0 : (i.tangentRange s hn)ᗮ) :
      TangentSpace I (i s))⟩ ∈ criticalPoints I f := by
    rw [i.normalExp_fiber_zero (P := P) hn s]
    exact h.mem_criticalPoints s
  have hf : MDifferentiableAt I 𝓘(ℝ) f
      (i.normalExp (P := P) hn ⟨s, i.normalClass s hn ((0 : (i.tangentRange s hn)ᗮ) :
        TangentSpace I (i s))⟩) := by
    rw [i.normalExp_fiber_zero (P := P) hn s]
    exact (h.contMDiffAt s).mdifferentiableAt two_ne_zero
  have hcomp := mfderiv_comp (0 : (i.tangentRange s hn)ᗮ) hf
    ((i.contMDiffAt_normalExp_fiber_zero (P := P) hn s).mdifferentiableAt (by simp))
  rw [mem_criticalPoints_iff_mfderiv_eq_zero.mp hcrit, ContinuousLinearMap.zero_comp,
    mfderiv_eq_fderiv] at hcomp
  exact hcomp

/-- **The Hessian of a normal slice is the normal Hessian.** For a critical submanifold `i` of `f`
and `s : S`, the Hessian at `0` of the normal slice `v ↦ f (exp_{i s} v)` on the orthogonal normal
space is the normal Hessian at `s` evaluated on the normal classes of its arguments. -/
theorem fderiv_fderiv_comp_normalExp_fiber_zero_apply (s : S) (u w : (i.tangentRange s hn)ᗮ) :
    fderiv ℝ (fderiv ℝ
      (fun v : (i.tangentRange s hn)ᗮ ↦ f (i.normalExp (P := P) hn ⟨s, i.normalClass s hn v⟩)))
      0 u w = h.normalHessian hn s (i.normalClass s hn u) (i.normalClass s hn w) := by
  have key := criticalHessian_comp_apply
    (φ := fun v : (i.tangentRange s hn)ᗮ ↦ i.normalExp (P := P) hn ⟨s, i.normalClass s hn v⟩)
    (y := 0) (i.normalExp_fiber_zero hn s) (h.contMDiffAt s)
    ((i.contMDiffAt_normalExp_fiber_zero (P := P) hn s).of_le (by norm_cast))
    (h.mem_criticalPoints s) u w
  rw [criticalHessian_modelSpace] at key
  refine key.trans ?_
  -- The vertical derivative of the normal exponential at `0` is the inclusion of the
  -- orthogonal normal space.
  rw [mfderiv_normalExp_fiber_zero_apply (P := P) i hn s u,
    mfderiv_normalExp_fiber_zero_apply (P := P) i hn s w, normalHessian_normalClass]
  -- `NormedSpace.fromTangentSpace` is by definition the identity of the model space.
  rfl

end IsCriticalSubmanifold

namespace IsCriticalSubmanifold

variable (h : i.IsCriticalSubmanifold f)
include h

/-- The Hessian quadratic form of the normal slice at `0` is the quadratic form of the normal
Hessian, read through the identification of the orthogonal normal space with the normal space. -/
private theorem hessianQuadraticForm_comp_normalExp_fiber_zero (s : S) :
    hessianQuadraticForm
      (fun v : (i.tangentRange s hn)ᗮ ↦ f (i.normalExp (P := P) hn ⟨s, i.normalClass s hn v⟩)) 0 =
      (h.normalHessian hn s).toQuadraticMap.comp
        (i.normalSpaceOrthogonalComplementEquiv s hn).symm.toLinearEquiv.toLinearMap := by
  ext v
  rw [hessianQuadraticForm_apply, h.fderiv_fderiv_comp_normalExp_fiber_zero_apply hn s v v]
  simp

/-- **Bott's normal-slice criterion.** A critical submanifold `i` of `f` is Morse–Bott exactly
when, at every `s : S`, the normal slice `v ↦ f (exp_{i s} v)` on the orthogonal normal space has
a nondegenerate critical point at `0`. -/
theorem isNondegenerateCriticalSubmanifold_iff_forall_isNondegenerateCriticalPoint :
    i.IsNondegenerateCriticalSubmanifold f ↔ ∀ s, IsNondegenerateCriticalPoint
      (fun v : (i.tangentRange s hn)ᗮ ↦ f (i.normalExp (P := P) hn ⟨s, i.normalClass s hn v⟩))
      0 := by
  constructor
  · intro hB s
    have : FiniteDimensional ℝ (TangentSpace I (i s)) := inferInstanceAs (FiniteDimensional ℝ E)
    refine ⟨h.contDiffAt_comp_normalExp_fiber_zero hn s, h.fderiv_comp_normalExp_fiber_zero hn s,
      ContinuousLinearMap.isInvertible_of_injective ?_⟩
    refine hB.injective_of_normalHessian_eq hn
      (i.normalSpaceOrthogonalComplementEquiv s hn).symm.toLinearEquiv fun u w ↦ ?_
    simp only [ContinuousLinearEquiv.coe_toLinearEquiv,
      normalSpaceOrthogonalComplementEquiv_symm_apply]
    exact (h.fderiv_fderiv_comp_normalExp_fiber_zero_apply hn s u w).symm
  · intro hN
    refine ⟨h, fun s ↦ (h.ker_normalHessian_eq_bot_iff hn s).mp ?_⟩
    obtain ⟨e, he⟩ := (hN s).isInvertible
    refine (Submodule.eq_bot_iff _).mpr fun p hp ↦ ?_
    obtain ⟨v, rfl⟩ := (i.normalSpaceOrthogonalComplementEquiv s hn).symm.surjective p
    -- A normal class in the kernel of the normal Hessian pairs to zero with every normal class,
    -- so its orthogonal representative lies in the kernel of the invertible slice Hessian.
    have hv : v = 0 := by
      refine e.injective ?_
      rw [map_zero, ← ContinuousLinearEquiv.coe_coe, he]
      ext w
      have hp' := LinearMap.congr_fun (LinearMap.mem_ker.mp hp)
        ((i.normalSpaceOrthogonalComplementEquiv s hn).symm w)
      simp only [normalSpaceOrthogonalComplementEquiv_symm_apply, LinearMap.zero_apply] at hp'
      rw [h.fderiv_fderiv_comp_normalExp_fiber_zero_apply hn s v w, hp',
        zero_apply]
    rw [hv, map_zero]

/-- **The index of a normal slice.** For a critical submanifold `i` of `f` and `s : S`, the Morse
index at `0` of the normal slice `v ↦ f (exp_{i s} v)` on the orthogonal normal space is the Morse
index of `f` at `i s`. -/
theorem morseIndex_comp_normalExp_fiber_zero (s : S) :
    morseIndex
      (fun v : (i.tangentRange s hn)ᗮ ↦ f (i.normalExp (P := P) hn ⟨s, i.normalClass s hn v⟩))
      0 = manifoldMorseIndex I f (i s) := by
  rw [morseIndex_def, h.hessianQuadraticForm_comp_normalExp_fiber_zero hn s,
    ← h.sigNeg_normalHessian hn s]
  exact QuadraticMap.Equivalent.sigNeg_eq
    ⟨(QuadraticMap.isometryEquivOfCompLinearEquiv (h.normalHessian hn s).toQuadraticMap
      (i.normalSpaceOrthogonalComplementEquiv s hn).symm.toLinearEquiv).symm⟩

end IsCriticalSubmanifold

end TauCeti.SmoothEmbedding

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Morse.Bott.Slice
public import TauCeti.Geometry.Manifold.TubularNeighborhood.Riemannian.Fiber
import TauCeti.Analysis.Calculus.IteratedFDeriv.CompContinuousLinearEquiv

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
* `IsCriticalSubmanifold.fderiv_comp_normalExp_mk_zero`,
  `IsCriticalSubmanifold.fderiv_fderiv_comp_normalExp_mk_zero_apply` and
  `IsNondegenerateCriticalSubmanifold.isInvertible_fderiv_fderiv_comp_normalExp_mk_zero`: the
  normal slice read on the intrinsic normal space, with its quotient norm, is critical at `0`, with
  the normal Hessian as Hessian, which is invertible in the Morse–Bott case.

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

omit [I.Boundaryless] [T2Space M] in
/-- The normal slice through the normal exponential, read on the intrinsic normal space, is the
normal slice on the orthogonal normal space precomposed with the orthogonal-representative
equivalence. -/
private theorem comp_normalExp_mk_eq_comp (s : S) :
    (fun v : i.NormalSpace s hn ↦ f (i.normalExp (P := P) hn ⟨s, v⟩)) =
      (fun w : (i.tangentRange s hn)ᗮ ↦
        f (i.normalExp (P := P) hn ⟨s, i.normalClass s hn w⟩)) ∘
        i.normalSpaceOrthogonalComplementEquiv s hn := by
  ext v
  rw [comp_apply, ← normalSpaceOrthogonalComplementEquiv_symm_apply,
    ContinuousLinearEquiv.symm_apply_apply]

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

omit h in
/-- The normal exponential on the orthogonal normal space is `C²` at `0`. -/
private theorem contMDiffAt_two_normalExp_fiber_zero (s : S) :
    ContMDiffAt 𝓘(ℝ, (i.tangentRange s hn)ᗮ) I 2
      (fun v : (i.tangentRange s hn)ᗮ ↦ i.normalExp (P := P) hn ⟨s, i.normalClass s hn v⟩) 0 :=
  (i.contMDiffAt_normalExp_fiber_zero (P := P) hn s).of_le (by norm_cast)

/-- The normal slice `v ↦ f (exp_{i s} v)` of a critical submanifold has a critical point at `0`.
-/
theorem fderiv_comp_normalExp_fiber_zero (s : S) :
    fderiv ℝ
      (fun v : (i.tangentRange s hn)ᗮ ↦ f (i.normalExp (P := P) hn ⟨s, i.normalClass s hn v⟩))
      0 = 0 :=
  h.fderiv_comp_eq_zero
    (φ := fun v : (i.tangentRange s hn)ᗮ ↦ i.normalExp (P := P) hn ⟨s, i.normalClass s hn v⟩)
    (y := 0) (i.normalExp_fiber_zero hn s)
    ((i.contMDiffAt_normalExp_fiber_zero (P := P) hn s).mdifferentiableAt (by simp))

/-- **The Hessian of a normal slice is the normal Hessian.** For a critical submanifold `i` of `f`
and `s : S`, the Hessian at `0` of the normal slice `v ↦ f (exp_{i s} v)` on the orthogonal normal
space is the normal Hessian at `s` evaluated on the normal classes of its arguments. -/
theorem fderiv_fderiv_comp_normalExp_fiber_zero_apply (s : S) (u w : (i.tangentRange s hn)ᗮ) :
    fderiv ℝ (fderiv ℝ
      (fun v : (i.tangentRange s hn)ᗮ ↦ f (i.normalExp (P := P) hn ⟨s, i.normalClass s hn v⟩)))
      0 u w = h.normalHessian hn s (i.normalClass s hn u) (i.normalClass s hn w) := by
  refine (h.fderiv_fderiv_comp_apply hn
      (φ := fun v : (i.tangentRange s hn)ᗮ ↦ i.normalExp (P := P) hn ⟨s, i.normalClass s hn v⟩)
      (y := 0) (i.normalExp_fiber_zero hn s)
    (contMDiffAt_two_normalExp_fiber_zero hn s) u w).trans ?_
  -- The vertical derivative of the normal exponential at `0` is the inclusion of the
  -- orthogonal normal space.
  rw [mfderiv_normalExp_fiber_zero_apply (P := P) i hn s u,
    mfderiv_normalExp_fiber_zero_apply (P := P) i hn s w]
  -- `NormedSpace.fromTangentSpace` is by definition the identity of the model space.
  rfl

omit h in
/-- The normal exponential on the orthogonal normal space is a transverse slice: its derivative at
`0` followed by the projection to the normal space is the identification of the orthogonal normal
space with the normal space. -/
private theorem bijective_normalClass_mfderiv_normalExp_fiber_zero (s : S) :
    Bijective fun v : (i.tangentRange s hn)ᗮ ↦ i.normalClass s hn
      (mfderiv 𝓘(ℝ, (i.tangentRange s hn)ᗮ) I
        (fun v : (i.tangentRange s hn)ᗮ ↦ i.normalExp (P := P) hn ⟨s, i.normalClass s hn v⟩) 0
        v) := by
  convert (i.normalSpaceOrthogonalComplementEquiv s hn).symm.bijective using 2 with v
  rw [mfderiv_normalExp_fiber_zero_apply (P := P) i hn s v,
    normalSpaceOrthogonalComplementEquiv_symm_apply]
  -- `NormedSpace.fromTangentSpace` is by definition the identity of the model space.
  rfl

/-- **Bott's normal-slice criterion.** A critical submanifold `i` of `f` is Morse–Bott exactly
when, at every `s : S`, the normal slice `v ↦ f (exp_{i s} v)` on the orthogonal normal space has
a nondegenerate critical point at `0`. -/
theorem isNondegenerateCriticalSubmanifold_iff_forall_isNondegenerateCriticalPoint :
    i.IsNondegenerateCriticalSubmanifold f ↔ ∀ s, IsNondegenerateCriticalPoint
      (fun v : (i.tangentRange s hn)ᗮ ↦ f (i.normalExp (P := P) hn ⟨s, i.normalClass s hn v⟩))
      0 := by
  have hφ (s : S) := contMDiffAt_two_normalExp_fiber_zero (P := P) (i := i) hn s
  constructor
  · intro hB s
    exact hB.isNondegenerateCriticalPoint_comp hn
      (φ := fun v : (i.tangentRange s hn)ᗮ ↦ i.normalExp (P := P) hn ⟨s, i.normalClass s hn v⟩)
      (y := 0) (i.normalExp_fiber_zero hn s) (hφ s)
      (bijective_normalClass_mfderiv_normalExp_fiber_zero hn s)
  · intro hN
    exact ⟨h, fun s ↦ (h.ker_normalHessian_eq_bot_iff hn s).mp
      (h.ker_normalHessian_eq_bot_of_isNondegenerateCriticalPoint_comp hn
        (φ := fun v : (i.tangentRange s hn)ᗮ ↦ i.normalExp (P := P) hn ⟨s, i.normalClass s hn v⟩)
        (y := 0) (i.normalExp_fiber_zero hn s) (hφ s)
        (bijective_normalClass_mfderiv_normalExp_fiber_zero hn s).2 (hN s))⟩

/-- **The index of a normal slice.** For a critical submanifold `i` of `f` and `s : S`, the Morse
index at `0` of the normal slice `v ↦ f (exp_{i s} v)` on the orthogonal normal space is the Morse
index of `f` at `i s`. -/
theorem morseIndex_comp_normalExp_fiber_zero (s : S) :
    morseIndex
      (fun v : (i.tangentRange s hn)ᗮ ↦ f (i.normalExp (P := P) hn ⟨s, i.normalClass s hn v⟩))
      0 = manifoldMorseIndex I f (i s) :=
  h.morseIndex_comp hn
    (φ := fun v : (i.tangentRange s hn)ᗮ ↦ i.normalExp (P := P) hn ⟨s, i.normalClass s hn v⟩)
    (y := 0) (i.normalExp_fiber_zero hn s)
    (contMDiffAt_two_normalExp_fiber_zero hn s)
    (bijective_normalClass_mfderiv_normalExp_fiber_zero hn s)

/-- The normal slice read on the intrinsic normal space over `s`, with its quotient norm
(`TauCeti.SmoothEmbedding.normalSpaceNormedAddCommGroup`), is critical at `0`. -/
theorem fderiv_comp_normalExp_mk_zero (s : S) :
    letI := i.normalSpaceNormedAddCommGroup s hn
    letI := i.normalSpaceNormedSpace s hn
    fderiv ℝ (fun v : i.NormalSpace s hn ↦ f (i.normalExp (P := P) hn ⟨s, v⟩)) 0 = 0 := by
  let := i.normalSpaceNormedAddCommGroup s hn
  let := i.normalSpaceNormedSpace s hn
  rw [comp_normalExp_mk_eq_comp, ContinuousLinearEquiv.comp_right_fderiv, map_zero,
    h.fderiv_comp_normalExp_fiber_zero hn s, ContinuousLinearMap.zero_comp]

/-- The Hessian at `0` of the normal slice read on the intrinsic normal space over `s`, with its
quotient norm, is the normal Hessian. -/
theorem fderiv_fderiv_comp_normalExp_mk_zero_apply (s : S) (u w : i.NormalSpace s hn) :
    letI := i.normalSpaceNormedAddCommGroup s hn
    letI := i.normalSpaceNormedSpace s hn
    fderiv ℝ (fderiv ℝ fun v : i.NormalSpace s hn ↦ f (i.normalExp (P := P) hn ⟨s, v⟩)) 0 u w =
      h.normalHessian hn s u w := by
  let := i.normalSpaceNormedAddCommGroup s hn
  let := i.normalSpaceNormedSpace s hn
  rw [comp_normalExp_mk_eq_comp, ContinuousLinearEquiv.fderiv_fderiv_comp_right_apply_apply,
    map_zero, h.fderiv_fderiv_comp_normalExp_fiber_zero_apply hn s,
    ← normalSpaceOrthogonalComplementEquiv_symm_apply,
    ← normalSpaceOrthogonalComplementEquiv_symm_apply, ContinuousLinearEquiv.symm_apply_apply,
    ContinuousLinearEquiv.symm_apply_apply]

end IsCriticalSubmanifold

namespace IsNondegenerateCriticalSubmanifold

variable (h : i.IsNondegenerateCriticalSubmanifold f)
include h

/-- For a Morse–Bott critical submanifold, the Hessian at `0` of the normal slice read on the
intrinsic normal space over `s`, with its quotient norm, is invertible. -/
theorem isInvertible_fderiv_fderiv_comp_normalExp_mk_zero (s : S) :
    letI := i.normalSpaceNormedAddCommGroup s hn
    letI := i.normalSpaceNormedSpace s hn
    (fderiv ℝ (fderiv ℝ fun v : i.NormalSpace s hn ↦
      f (i.normalExp (P := P) hn ⟨s, v⟩)) 0).IsInvertible := by
  let := i.normalSpaceNormedAddCommGroup s hn
  let := i.normalSpaceNormedSpace s hn
  exact ContinuousLinearMap.isInvertible_of_injective (𝕜 := ℝ) (E := i.NormalSpace s hn)
    (h.injective_of_normalHessian_eq hn (LinearEquiv.refl ℝ _) fun u w ↦
      (h.toIsCriticalSubmanifold.fderiv_fderiv_comp_normalExp_mk_zero_apply (P := P) hn s u
        w).symm)

end IsNondegenerateCriticalSubmanifold

end TauCeti.SmoothEmbedding

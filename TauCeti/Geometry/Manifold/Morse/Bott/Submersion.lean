/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Morse.Bott.Family
public import TauCeti.Geometry.Manifold.RegularValue.ManifoldLevel
import TauCeti.LinearAlgebra.QuadraticForm.Signature.Comp

/-!
# Pulling Morse functions back along submersions

Let `π : M → N` be a submersion, a map whose derivative is surjective at every point, and let
`f` be a Morse function on `N`. The pullback `f ∘ π` is the basic example of a Morse–Bott
function: its critical set is the union of the fibres of `π` over the critical points of `f`, and
along each such fibre the Hessian of `f ∘ π` is the Hessian of `f` read through the derivative of
`π`, which is as nondegenerate as possible. This is the pullback Bott function of a fibre bundle
over a Morse base, whose Morse–Bott complex compares with the Morse complex of the base with
coefficients in the homology of the fibres.

* **Critical points.** By the chain rule `d(f ∘ π)_z = df_{π z} ∘ dπ_z`, and `dπ_z` is surjective,
  so `z` is a critical point of `f ∘ π` exactly when `π z` is a critical point of `f`
  (`TauCeti.mem_criticalPoints_comp_iff_of_isRegularPoint`,
  `TauCeti.criticalPoints_comp_of_isRegularPoint`).
* **Hessians.** At such a point the second-order chain rule
  (`TauCeti.criticalHessian_comp_apply`) gives `Hess (f ∘ π) z (v, w) = Hess f (π z) (dπ v, dπ w)`.
  So the kernel of the Hessian of `f ∘ π` is the preimage under `dπ_z` of the kernel of the Hessian
  of `f` (`TauCeti.ker_criticalHessian_comp`), which is the kernel of `dπ_z` when `π z` is
  nondegenerate (`TauCeti.IsManifoldNondegenerateCriticalPoint.ker_criticalHessian_comp`). The
  Hessian of `f ∘ π` is the pullback of that of `f` along a surjection, so it has the same negative
  index of inertia: the Morse index of `f ∘ π` at `z` is the Morse index of `f` at `π z`
  (`TauCeti.manifoldMorseIndex_comp_of_isRegularPoint`).
* **Critical submanifolds.** A smooth embedding into the fibre over a nondegenerate critical point
  whose tangent spaces contain the kernels of `dπ` is therefore a nondegenerate critical
  submanifold of `f ∘ π` (`TauCeti.SmoothEmbedding.isNondegenerateCriticalSubmanifold_comp`); the
  regular fibre itself is one
  (`TauCeti.isNondegenerateCriticalSubmanifold_comp_regularFiber`).
* **Normal spaces.** Along such a fibre the derivative of `π` vanishes on the tangent space, so it
  descends to the normal space of the fibre, and the normal Hessian is the Hessian of `f` at the
  base point read through it
  (`TauCeti.SmoothEmbedding.IsCriticalSubmanifold.normalHessian_comp_apply`): the normal Hessian
  of a critical fibre is pulled back from the fixed Hessian of `f` at its base point.
* **Morse–Bott families.** If `π` is a smooth submersion of finite-dimensional boundaryless
  manifolds, `f` is Morse, and the fibres of `π` over the critical points of `f` are preconnected,
  then the regular fibres over the critical points of `f` in the range of `π` exhibit `f ∘ π` as a
  Morse–Bott function (`TauCeti.isMorseBottFamily_comp_of_isRegularPoint`).

## References

* R. Bott, *Nondegenerate critical manifolds*, Annals of Mathematics 60 (1954), 248–261
  (nondegenerate critical manifolds and Morse–Bott functions).
-/

public section

open Function Module Set
open scoped ContDiff Manifold

namespace TauCeti

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  {F G N : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace G]
  {J : ModelWithCorners ℝ F G} [TopologicalSpace N] [ChartedSpace G N]
  {π : M → N} {f : N → ℝ} {z : M}

section CriticalPoints

/-- **Critical points of a pullback.** At a point `z` where `π` is differentiable with surjective
derivative, and `f` is differentiable at `π z`, the point `z` is a critical point of `f ∘ π` exactly
when `π z` is a critical point of `f`. -/
theorem mem_criticalPoints_comp_iff_of_isRegularPoint (hf : MDifferentiableAt J 𝓘(ℝ) f (π z))
    (hπ : MDifferentiableAt I J π z) (hreg : IsRegularPoint I J π z) :
    z ∈ criticalPoints I (f ∘ π) ↔ π z ∈ criticalPoints J f := by
  rw [mem_criticalPoints_iff_mfderiv_eq_zero, mem_criticalPoints_iff_mfderiv_eq_zero,
    mfderiv_comp z hf hπ]
  refine ⟨fun h ↦ ContinuousLinearMap.ext fun w ↦ ?_,
    fun h ↦ by rw [h, ContinuousLinearMap.zero_comp]⟩
  obtain ⟨v, rfl⟩ := isRegularPoint_iff.1 hreg w
  exact congr($h v)

/-- **The critical set of a pullback along a submersion.** For a differentiable `f` and a
differentiable `π` whose derivative is surjective everywhere, the critical points of `f ∘ π` are
the points over the critical points of `f`. -/
theorem criticalPoints_comp_of_isRegularPoint (hf : MDifferentiable J 𝓘(ℝ) f)
    (hπ : MDifferentiable I J π) (hreg : ∀ z, IsRegularPoint I J π z) :
    criticalPoints I (f ∘ π) = π ⁻¹' criticalPoints J f :=
  ext fun z ↦ mem_criticalPoints_comp_iff_of_isRegularPoint (hf (π z)) (hπ z) (hreg z)

end CriticalPoints

section Hessian

variable [I.Boundaryless] [J.Boundaryless]

/-- **The kernel of the Hessian of a pullback.** Over a critical point of a function `f` which is
`C²` there, at a point where `π` is `C²` with surjective derivative, the kernel of the critical
Hessian of `f ∘ π` is the preimage under the derivative of `π` of the kernel of the critical
Hessian of `f`. -/
theorem ker_criticalHessian_comp (hf : ContMDiffAt J 𝓘(ℝ) 2 f (π z))
    (hπ : ContMDiffAt I J 2 π z) (hcrit : π z ∈ criticalPoints J f)
    (hreg : IsRegularPoint I J π z) :
    (criticalHessian I (f ∘ π) z).ker =
      (criticalHessian J f (π z)).ker.comap (mfderiv I J π z).toLinearMap := by
  have hcomp := criticalHessian_comp_apply rfl hf hπ hcrit
  ext v
  simp only [LinearMap.mem_ker, Submodule.mem_comap, ContinuousLinearMap.coe_coe]
  refine ⟨fun hv ↦ ContinuousLinearMap.ext fun u ↦ ?_, fun hv ↦ ContinuousLinearMap.ext fun w ↦ ?_⟩
  · obtain ⟨w, rfl⟩ := isRegularPoint_iff.1 hreg u
    rw [← hcomp, hv, zero_apply, zero_apply]
  · rw [hcomp, hv, zero_apply, zero_apply]

/-- **The kernel of the Hessian of a pullback at a nondegenerate critical point.** Over a
nondegenerate critical point of `f`, at a point where `π` is `C²` with surjective derivative, the
kernel of the critical Hessian of `f ∘ π` is the kernel of the derivative of `π`: the Hessian
degenerates exactly along the fibre. -/
theorem IsManifoldNondegenerateCriticalPoint.ker_criticalHessian_comp
    (hx : IsManifoldNondegenerateCriticalPoint J f (π z)) (hπ : ContMDiffAt I J 2 π z)
    (hreg : IsRegularPoint I J π z) :
    (criticalHessian I (f ∘ π) z).ker = (mfderiv I J π z).ker := by
  obtain ⟨hf, -, hinv⟩ := isManifoldNondegenerateCriticalPoint_iff_criticalHessian.1 hx
  rw [TauCeti.ker_criticalHessian_comp hf hπ hx.mem_criticalPoints hreg,
    LinearMap.ker_eq_bot.2 hinv.injective, Submodule.comap_bot]

/-- **The Morse index of a pullback.** Over a critical point of a function `f` which is `C²`
there, at a point where `π` is `C²` with surjective derivative, the Morse index of `f ∘ π` is the
Morse index of `f`: the Hessian of `f ∘ π` is the Hessian of `f` pulled back along the surjective
derivative of `π`, which preserves the negative index of inertia. -/
theorem manifoldMorseIndex_comp_of_isRegularPoint [FiniteDimensional ℝ E]
    (hf : ContMDiffAt J 𝓘(ℝ) 2 f (π z)) (hπ : ContMDiffAt I J 2 π z)
    (hcrit : π z ∈ criticalPoints J f) (hreg : IsRegularPoint I J π z) :
    manifoldMorseIndex I (f ∘ π) z = manifoldMorseIndex J f (π z) := by
  have hQ : (criticalHessian I (f ∘ π) z).toBilinForm.toQuadraticMap =
      (criticalHessian J f (π z)).toBilinForm.toQuadraticMap.comp
        (mfderiv I J π z).toLinearMap := by
    ext v
    exact criticalHessian_comp_apply rfl hf hπ hcrit v v
  rw [manifoldMorseIndex_eq_sigNeg_criticalHessian, manifoldMorseIndex_eq_sigNeg_criticalHessian,
    hQ, QuadraticForm.sigNeg_comp_of_surjective _ (isRegularPoint_iff.1 hreg)]

end Hessian

namespace SmoothEmbedding

variable {E' H' S : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
  {K : ModelWithCorners ℝ E' H'} [TopologicalSpace S] [ChartedSpace H' S] {n : ℕ∞ω}
  {i : SmoothEmbedding K I n S M} {x : N}

section Boundaryless

variable [I.Boundaryless] [J.Boundaryless]

/-- **Fibres over nondegenerate critical points are Morse–Bott critical submanifolds of the
pullback.** Let `i` be a smooth embedding into the fibre of `π` over a nondegenerate critical point
`x` of `f`, along which `π` is `C²` with surjective derivative, and whose tangent spaces contain the
kernels of the derivative of `π`. Then `i` is a nondegenerate critical submanifold of `f ∘ π`. -/
theorem isNondegenerateCriticalSubmanifold_comp
    (hx : IsManifoldNondegenerateCriticalPoint J f x) (hix : ∀ s, π (i s) = x)
    (hπ : ∀ s, ContMDiffAt I J 2 π (i s)) (hreg : ∀ s, IsRegularPoint I J π (i s))
    (hker : ∀ s, (mfderiv I J π (i s)).ker ≤ (mfderiv K I i s).toLinearMap.range) :
    i.IsNondegenerateCriticalSubmanifold (f ∘ π) := by
  have hx' (s : S) : IsManifoldNondegenerateCriticalPoint J f (π (i s)) := hix s ▸ hx
  have hf (s : S) : ContMDiffAt J 𝓘(ℝ) 2 f (π (i s)) :=
    (isManifoldNondegenerateCriticalPoint_iff_criticalHessian.1 (hx' s)).1
  refine
    { contMDiffAt := fun s ↦ (hf s).comp (i s) (hπ s)
      mem_criticalPoints := fun s ↦ ?_
      ker_criticalHessian_le := fun s ↦ ?_ }
  · refine (mem_criticalPoints_comp_iff_of_isRegularPoint
      ((hf s).mdifferentiableAt two_ne_zero) ((hπ s).mdifferentiableAt two_ne_zero) (hreg s)).2 ?_
    exact (hx' s).mem_criticalPoints
  · rw [(hx' s).ker_criticalHessian_comp (hπ s) (hreg s)]
    exact hker s

end Boundaryless

section NormalSpace

variable (hn : n ≠ 0)

/-- **The normal Hessian of a fibre is the Hessian of the base.** Let `i` be a critical submanifold
of `f ∘ π` lying over a critical point of a function `f` which is `C²` there, along which `π` is
`C²`, and whose tangent spaces lie in the kernels of the derivative of `π`. Then the derivative of
`π` descends to the normal space of `i` (`TauCeti.SmoothEmbedding.normalLift`), and the normal
Hessian of `i` at `s` is the critical Hessian of `f` at `π (i s)` read through this map. -/
theorem IsCriticalSubmanifold.normalHessian_comp_apply [I.Boundaryless] [IsManifold I 2 M]
    [J.Boundaryless] (h : i.IsCriticalSubmanifold (f ∘ π)) (s : S)
    (hf : ContMDiffAt J 𝓘(ℝ) 2 f (π (i s))) (hπ : ContMDiffAt I J 2 π (i s))
    (hcrit : π (i s) ∈ criticalPoints J f)
    (hker : i.tangentRange s hn ≤ (mfderiv I J π (i s)).ker) (p q : i.NormalSpace s hn) :
    h.normalHessian hn s p q =
      criticalHessian J f (π (i s))
        (i.normalLift s hn (mfderiv I J π (i s)).toLinearMap (fun _ hv ↦ hker hv) p)
        (i.normalLift s hn (mfderiv I J π (i s)).toLinearMap (fun _ hv ↦ hker hv) q) := by
  obtain ⟨v, rfl⟩ := i.normalClass_surjective s hn p
  obtain ⟨w, rfl⟩ := i.normalClass_surjective s hn q
  have hlift (u : TangentSpace I (i s)) :=
    i.normalLift_normalClass s hn (mfderiv I J π (i s)).toLinearMap (fun _ hv ↦ hker hv) u
  rw [h.normalHessian_normalClass, hlift v, hlift w]
  exact criticalHessian_comp_apply rfl hf hπ hcrit v w

end NormalSpace

end SmoothEmbedding

section RegularFiber

variable [FiniteDimensional ℝ E] [I.Boundaryless] [FiniteDimensional ℝ F] [J.Boundaryless]
  {m : ℕ∞ω} [IsManifold I m M] [IsManifold J m N] {x : N}

/-- **The regular fibre over a nondegenerate critical point is a Morse–Bott critical submanifold
of the pullback.** Let `π` be a `C^m` map, `m ≥ 2`, of finite-dimensional boundaryless manifolds
and `x` a regular value of `π` which is a nondegenerate critical point of `f`. With its regular
fibre atlas, the inclusion of the fibre `{z // π z = x}` is a nondegenerate critical submanifold of
`f ∘ π`. -/
theorem isNondegenerateCriticalSubmanifold_comp_regularFiber (hm : 2 ≤ m)
    (hπ : ContMDiff I J m π) (hreg : IsRegularValue I J π x)
    (hx : IsManifoldNondegenerateCriticalPoint J f x) :
    letI := regularFiberChartedSpace (one_le_two.trans hm) hπ BoundarylessManifold.isInteriorPoint
      hreg
    (SmoothEmbedding.ofIsSmoothEmbedding (Subtype.val : {z : M // π z = x} → M)
      (isSmoothEmbedding_coe_regularFiber (one_le_two.trans hm) hπ
        BoundarylessManifold.isInteriorPoint hreg)).IsNondegenerateCriticalSubmanifold
      (f ∘ π) := by
  let := regularFiberChartedSpace (one_le_two.trans hm) hπ BoundarylessManifold.isInteriorPoint
    hreg
  refine SmoothEmbedding.isNondegenerateCriticalSubmanifold_comp hx (fun z ↦ ?_) (fun z ↦ ?_)
    (fun z ↦ ?_) fun z ↦ ?_
  · rw [SmoothEmbedding.ofIsSmoothEmbedding_apply]; exact z.2
  · rw [SmoothEmbedding.ofIsSmoothEmbedding_apply]; exact (hπ z).of_le hm
  · rw [SmoothEmbedding.ofIsSmoothEmbedding_apply]; exact hreg.isRegularPoint z.2
  · rw [SmoothEmbedding.coe_ofIsSmoothEmbedding]
    exact (range_mfderiv_coe_regularFiber (one_le_two.trans hm) hπ
      BoundarylessManifold.isInteriorPoint hreg z).ge

/-- **The pullback of a Morse function along a submersion is Morse–Bott.** Let `π` be a smooth
submersion of finite-dimensional boundaryless manifolds and `f` a Morse function on `N` whose
critical points have preconnected fibres. Then the regular fibres of `π` over the critical points
of `f` in the range of `π`, each with its regular fibre atlas, exhibit `f ∘ π` as a Morse–Bott
function. Its critical submanifolds are these fibres, and at each point of the fibre over `x` the
Morse index of `f ∘ π` is the Morse index of `f` at `x`
(`TauCeti.manifoldMorseIndex_comp_of_isRegularPoint`). -/
theorem isMorseBottFamily_comp_of_isRegularPoint [IsManifold I ∞ M] [IsManifold J ∞ N]
    (hπ : ContMDiff I J ∞ π) (hreg : ∀ z, IsRegularPoint I J π z) (hf : IsMorse J f)
    (hconn : ∀ x ∈ criticalPoints J f, IsPreconnected (π ⁻¹' {x})) :
    letI (x : ↥(criticalPoints J f ∩ range π)) :
        ChartedSpace (Fin (finrank ℝ E - finrank ℝ F) → ℝ) {z : M // π z = x} :=
      regularFiberChartedSpace (by simp) hπ BoundarylessManifold.isInteriorPoint
        (isRegularValue_iff.2 fun z _ ↦ hreg z)
    IsMorseBottFamily (I := I) (n := ∞)
      (fun x : ↥(criticalPoints J f ∩ range π) ↦
        SmoothEmbedding.ofIsSmoothEmbedding (Subtype.val : {z : M // π z = x} → M)
          (isSmoothEmbedding_coe_regularFiber (by simp) hπ BoundarylessManifold.isInteriorPoint
            (isRegularValue_iff.2 fun z _ ↦ hreg z)))
      (f ∘ π) := by
  let (x : ↥(criticalPoints J f ∩ range π)) :
      ChartedSpace (Fin (finrank ℝ E - finrank ℝ F) → ℝ) {z : M // π z = x} :=
    regularFiberChartedSpace (by simp) hπ BoundarylessManifold.isInteriorPoint
      (isRegularValue_iff.2 fun z _ ↦ hreg z)
  have (x : ↥(criticalPoints J f ∩ range π)) : Nonempty {z : M // π z = x} := by
    obtain ⟨z, hz⟩ := x.2.2
    exact ⟨⟨z, hz⟩⟩
  have (x : ↥(criticalPoints J f ∩ range π)) : PreconnectedSpace {z : M // π z = x} :=
    Subtype.preconnectedSpace (hconn x x.2.1)
  have hfπ : ContMDiff I 𝓘(ℝ) ∞ (f ∘ π) := hf.contMDiff.comp hπ
  refine .of_pairwise_disjoint (by simp) hfπ
    (fun x ↦ isNondegenerateCriticalSubmanifold_comp_regularFiber (by simp) hπ
      (isRegularValue_iff.2 fun z _ ↦ hreg z)
      (hf.isManifoldNondegenerateCriticalPoint_of_mem_criticalPoints x.2.1))
    (fun x y hxy ↦ ?_) fun z hz ↦ ?_
  · refine disjoint_left.2 ?_
    rintro _ ⟨a, rfl⟩ ⟨b, hb⟩
    simp only [SmoothEmbedding.ofIsSmoothEmbedding_apply] at hb
    exact hxy (Subtype.ext (a.2.symm.trans (hb ▸ b.2)))
  · have hz' : π z ∈ criticalPoints J f := by
      rwa [criticalPoints_comp_of_isRegularPoint (hf.contMDiff.mdifferentiable (by simp))
        (hπ.mdifferentiable (by simp)) hreg] at hz
    exact mem_iUnion.2 ⟨⟨π z, hz', z, rfl⟩, ⟨z, rfl⟩, by simp⟩

end RegularFiber

end TauCeti

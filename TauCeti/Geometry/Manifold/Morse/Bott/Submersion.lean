/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Morse.Bott.Family
public import TauCeti.Geometry.Manifold.Morse.Submersion
public import TauCeti.Geometry.Manifold.RegularValue.ManifoldLevel
public import TauCeti.Geometry.Manifold.SmoothEmbedding.NormalSpace.Level

/-!
# Pulling a Morse function back along a submersion

Let `π : Z → B` be a map whose derivative is onto at `z` and let `f : B → ℝ`. By the chain rule,
`z` is a critical point of `f ∘ π` exactly when `π z` is a critical point of `f`, and there the
critical Hessian of `f ∘ π` is the critical Hessian of `f` read through `dπ`:

`Hess (f ∘ π) z (u, w) = Hess f (π z) (dπ u, dπ w)`.

Since `dπ` is onto, the kernel of the Hessian of `f ∘ π` at `z` is the preimage under `dπ` of the
kernel of the Hessian of `f` at `π z`, and the two Morse indices agree. At a nondegenerate critical
point `p` of `f` the kernel of the Hessian of `f ∘ π` is therefore exactly the kernel of `dπ`,
which is the tangent space of the fibre `π⁻¹(p)`. So the fibres of a submersion over the
nondegenerate critical points of `f` are Morse–Bott critical submanifolds of `f ∘ π`, of the index
of `f` at the base point; the pointwise statements are in
`TauCeti.Geometry.Manifold.Morse.Submersion`. The derivative `dπ` identifies the normal space of
such a fibre with `T_p B` and carries the normal Hessian to the Hessian of `f` at `p`, so the
negative normal spaces of `f ∘ π` along the fibre are the preimages of the negative spaces of the
Hessian of `f` at `p`.

For a smooth submersion between finite-dimensional boundaryless manifolds whose fibres over the
critical points of a Morse function `f` are nonempty and connected, these fibres exhibit `f ∘ π` as
a Morse–Bott function. Connectedness of the fibres is needed: the pieces of a Morse–Bott family are
the connected components of the critical set.

## Main results

* `TauCeti.SmoothEmbedding.isCriticalSubmanifold_comp`: a submanifold mapped by `π` to a critical
  point of `f` is a critical submanifold of `f ∘ π`.
* `TauCeti.SmoothEmbedding.isNondegenerateCriticalSubmanifold_comp`: if moreover the point is
  nondegenerate, `dπ` is onto along the submanifold and the kernel of `dπ` is tangent to it, the
  submanifold is Morse–Bott for `f ∘ π`.
* `TauCeti.SmoothEmbedding.IsCriticalSubmanifold.normalHessian_comp_apply`: along a submanifold
  whose tangent spaces are the kernels of `dπ`, the identification
  `TauCeti.SmoothEmbedding.normalSpaceEquivOfSurjective` of the normal space with the tangent space
  of the base carries the normal Hessian of `f ∘ π` to the Hessian of `f`.
* `TauCeti.isNondegenerateCriticalSubmanifold_comp_regularFiber`: the regular fibre of `π` over a
  nondegenerate critical point of `f` is a Morse–Bott critical submanifold of `f ∘ π`.
* `TauCeti.IsMorse.isMorseBottFamily_comp`: the fibres of a submersion over the critical points of
  a Morse function, when nonempty and connected, exhibit `f ∘ π` as a Morse–Bott function.

## References

* R. Bott, *Nondegenerate critical manifolds*, Annals of Mathematics 60 (1954), 248–261.
* A. Banyaga and D. E. Hurtubise, *Lectures on Morse Homology*, Kluwer, 2004, Section 3.5.
-/

public section

open Function Set
open scoped ContDiff Manifold

noncomputable section

namespace TauCeti

variable {E H B : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace B] [ChartedSpace H B]
  {E' H' Z : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
  {I' : ModelWithCorners ℝ E' H'} [TopologicalSpace Z] [ChartedSpace H' Z]
  {π : Z → B} {f : B → ℝ}

/-! ### Submanifolds of the fibres -/

namespace SmoothEmbedding

variable {F G S : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace G]
  {J : ModelWithCorners ℝ F G} [TopologicalSpace S] [ChartedSpace G S] {n : ℕ∞ω}
  {i : SmoothEmbedding J I' n S Z} {p : B}

/-- **A submanifold of a critical fibre is a critical submanifold of the pullback.** If `π` maps
a submanifold `i` to a critical point `p` of a function `f` which is `C²` there, and `π` is `C²`
along `i`, then `i` is a critical submanifold of `f ∘ π`. No condition on `dπ` is needed. -/
theorem isCriticalSubmanifold_comp (hf : ContMDiffAt I 𝓘(ℝ) 2 f p)
    (hp : p ∈ criticalPoints I f) (hπ : ∀ s, ContMDiffAt I' I 2 π (i s))
    (hπi : ∀ s, π (i s) = p) : i.IsCriticalSubmanifold (f ∘ π) where
  contMDiffAt s := by
    have hf' : ContMDiffAt I 𝓘(ℝ) 2 f (π (i s)) := hπi s ▸ hf
    exact hf'.comp (i s) (hπ s)
  mem_criticalPoints s := by
    have hf' : ContMDiffAt I 𝓘(ℝ) 2 f (π (i s)) := hπi s ▸ hf
    have hp' : π (i s) ∈ criticalPoints I f := hπi s ▸ hp
    rw [mem_criticalPoints_iff_mfderiv_eq_zero,
      mfderiv_comp (i s) (hf'.mdifferentiableAt two_ne_zero) ((hπ s).mdifferentiableAt two_ne_zero),
      mem_criticalPoints_iff_mfderiv_eq_zero.1 hp', ContinuousLinearMap.zero_comp]

variable [I.Boundaryless] [I'.Boundaryless]

/-- **The pullback of a Morse function is Morse–Bott along the fibres.** Let `p` be a
nondegenerate critical point of `f`, and let `i` be a submanifold mapped by `π` to `p`, along which
`π` is `C²` with onto derivative. If the kernel of `dπ` is tangent to `i`, as it is for the fibre
`π⁻¹(p)` itself, then `i` is a Morse–Bott critical submanifold of `f ∘ π`: the kernel of the
critical Hessian of `f ∘ π` is the kernel of `dπ`. -/
theorem isNondegenerateCriticalSubmanifold_comp
    (hp : IsManifoldNondegenerateCriticalPoint I f p) (hπ : ∀ s, ContMDiffAt I' I 2 π (i s))
    (hπi : ∀ s, π (i s) = p) (hreg : ∀ s, IsRegularPoint I' I π (i s))
    (hker : ∀ s, (mfderiv I' I π (i s)).ker ≤ (mfderiv J I' i s).toLinearMap.range) :
    i.IsNondegenerateCriticalSubmanifold (f ∘ π) where
  toIsCriticalSubmanifold :=
    isCriticalSubmanifold_comp hp.contMDiffAt hp.mem_criticalPoints hπ hπi
  ker_criticalHessian_le s v hv := by
    have hp' : IsManifoldNondegenerateCriticalPoint I f (π (i s)) := hπi s ▸ hp
    rw [(hreg s).ker_criticalHessian_comp hp'.contMDiffAt (hπ s) hp'.mem_criticalPoints,
      Submodule.mem_comap, LinearMap.mem_ker, ContinuousLinearMap.coe_coe] at hv
    -- The Hessian of `f` at `p` is injective, so `dπ v = 0` and `v` is tangent to `i`.
    exact hker s (hp'.isInvertible_criticalHessian.injective (hv.trans (map_zero _).symm))

/-- **The normal Hessian of the pullback is the Hessian of the base.** Along a critical
submanifold `i` of `f ∘ π` whose tangent spaces are the kernels of `dπ`, at a point where `π` is
`C²` with onto derivative and maps `i s` to a critical point of `f` at which `f` is `C²`, the
normal Hessian of `f ∘ π` is the critical Hessian of `f` at `π (i s)`, read through the
identification `TauCeti.SmoothEmbedding.normalSpaceEquivOfSurjective` of the normal space with
the tangent space of the base. In particular the negative normal spaces of `f ∘ π` along `i` are
the preimages of the negative spaces of the Hessian of `f`. -/
theorem IsCriticalSubmanifold.normalHessian_comp_apply [IsManifold I' 2 Z] (hn : n ≠ 0)
    (h : i.IsCriticalSubmanifold (f ∘ π)) (s : S) (hreg : IsRegularPoint I' I π (i s))
    (htan : i.isImmersion.tangentRange s hn = (mfderiv I' I π (i s)).ker)
    (hf : ContMDiffAt I 𝓘(ℝ) 2 f (π (i s))) (hπ : ContMDiffAt I' I 2 π (i s))
    (hcrit : π (i s) ∈ criticalPoints I f) (a b : i.isImmersion.NormalSpace s hn) :
    h.normalHessian hn s a b =
      criticalHessian I f (π (i s)) (i.normalSpaceEquivOfSurjective s hn hreg htan a)
        (i.normalSpaceEquivOfSurjective s hn hreg htan b) := by
  obtain ⟨v, rfl⟩ := i.isImmersion.normalClass_surjective s hn a
  obtain ⟨w, rfl⟩ := i.isImmersion.normalClass_surjective s hn b
  rw [h.normalHessian_normalClass, normalSpaceEquivOfSurjective_normalClass,
    normalSpaceEquivOfSurjective_normalClass, criticalHessian_comp_apply rfl hf hπ hcrit]

end SmoothEmbedding

/-! ### Regular fibres over critical points -/

section RegularFiber

variable [FiniteDimensional ℝ E] [FiniteDimensional ℝ E'] [I.Boundaryless] [I'.Boundaryless]
  {m : ℕ∞ω} [IsManifold I m B] [IsManifold I' m Z] {p : B}

/-- **The fibre over a nondegenerate critical point is Morse–Bott.** Let `π : Z → B` be a `C^m`
map, `m ≥ 2`, between finite-dimensional boundaryless manifolds, and let `p` be a regular value of
`π` which is a nondegenerate critical point of `f`. Then the fibre `π⁻¹(p)`, with its regular-fibre
atlas `TauCeti.regularFiberChartedSpace`, is a Morse–Bott critical submanifold of `f ∘ π`. -/
theorem isNondegenerateCriticalSubmanifold_comp_regularFiber (hm : 2 ≤ m)
    (hπ : ContMDiff I' I m π) (hreg : IsRegularValue I' I π p)
    (hp : IsManifoldNondegenerateCriticalPoint I f p) :
    letI := regularFiberChartedSpace (one_le_two.trans hm) hπ BoundarylessManifold.isInteriorPoint
      hreg
    SmoothEmbedding.IsNondegenerateCriticalSubmanifold
      (SmoothEmbedding.ofIsSmoothEmbedding _ (isSmoothEmbedding_coe_regularFiber
        (one_le_two.trans hm) hπ BoundarylessManifold.isInteriorPoint hreg)) (f ∘ π) := by
  let := regularFiberChartedSpace (one_le_two.trans hm) hπ BoundarylessManifold.isInteriorPoint
    hreg
  refine SmoothEmbedding.isNondegenerateCriticalSubmanifold_comp hp (fun z ↦ ?_) (fun z ↦ ?_)
    (fun z ↦ ?_) fun z ↦ ?_ <;> rw [SmoothEmbedding.ofIsSmoothEmbedding_apply]
  · exact (hπ z.val).of_le hm
  · exact z.property
  · exact hreg.isRegularPoint z.property
  · rw [SmoothEmbedding.coe_ofIsSmoothEmbedding, range_mfderiv_coe_regularFiber]

end RegularFiber

/-! ### The pullback Morse–Bott function -/

variable [FiniteDimensional ℝ E] [FiniteDimensional ℝ E'] [I.Boundaryless] [I'.Boundaryless]
  [IsManifold I ∞ B] [IsManifold I' ∞ Z]

/-- **The pullback of a Morse function along a submersion is Morse–Bott.** Let `π : Z → B` be a
smooth submersion between finite-dimensional boundaryless manifolds and `f` a Morse function on `B`
such that the fibre of `π` over every critical point of `f` is nonempty and connected. Then the
fibres over the critical points of `f`, with their regular-fibre atlases, exhibit `f ∘ π` as a
Morse–Bott function: the critical set of `f ∘ π` is the preimage of that of `f`, and the Morse
index along the fibre over `p` is the Morse index of `f` at `p`
(`TauCeti.IsRegularPoint.manifoldMorseIndex_comp`). -/
theorem IsMorse.isMorseBottFamily_comp (hf : IsMorse I f) (hπ : ContMDiff I' I ∞ π)
    (hreg : ∀ z, IsRegularPoint I' I π z)
    (hconn : ∀ p ∈ criticalPoints I f, IsConnected {z | π z = p}) :
    letI (p : criticalPoints I f) := regularFiberChartedSpace (by simp) hπ
      BoundarylessManifold.isInteriorPoint (isRegularValue_iff.2 fun z _ ↦ hreg z) (c := p.val)
    IsMorseBottFamily (fun p : criticalPoints I f ↦ SmoothEmbedding.ofIsSmoothEmbedding _
      (isSmoothEmbedding_coe_regularFiber (by simp) hπ
        BoundarylessManifold.isInteriorPoint (isRegularValue_iff.2 fun z _ ↦ hreg z) (c := p.val)))
      (f ∘ π) := by
  have hm : (2 : ℕ∞ω) ≤ ∞ := by simp
  have hreg' (p : B) : IsRegularValue I' I π p := isRegularValue_iff.2 fun z _ ↦ hreg z
  let (p : criticalPoints I f) := regularFiberChartedSpace (one_le_two.trans hm) hπ
    BoundarylessManifold.isInteriorPoint (hreg' p.val)
  have (p : criticalPoints I f) : Nonempty {z // π z = p.val} :=
    (hconn p.val p.property).nonempty.to_subtype
  have (p : criticalPoints I f) : PreconnectedSpace {z // π z = p.val} :=
    isPreconnected_iff_preconnectedSpace.1 (hconn p.val p.property).isPreconnected
  refine .of_pairwise_disjoint hm (hf.contMDiff.comp hπ)
    (fun p ↦ isNondegenerateCriticalSubmanifold_comp_regularFiber hm hπ (hreg' p.val)
      (hf.isManifoldNondegenerateCriticalPoint_of_mem_criticalPoints p.property)) ?_ ?_
  · -- Fibres over distinct points are disjoint.
    intro p q hpq
    refine disjoint_left.2 ?_
    rintro _ ⟨z, rfl⟩ ⟨w, hw⟩
    rw [SmoothEmbedding.coe_ofIsSmoothEmbedding, SmoothEmbedding.coe_ofIsSmoothEmbedding] at hw
    exact hpq (Subtype.ext (z.property.symm.trans (hw ▸ w.property)))
  · -- A critical point of `f ∘ π` lies over a critical point of `f`.
    intro z hz
    have hπz : π z ∈ criticalPoints I f :=
      ((hreg z).mem_criticalPoints_comp_iff ((hπ z).mdifferentiableAt (by simp))
        ((hf.contMDiff (π z)).mdifferentiableAt (by simp))).1 hz
    exact mem_iUnion.2 ⟨⟨π z, hπz⟩, ⟨z, rfl⟩, by rw [SmoothEmbedding.coe_ofIsSmoothEmbedding]⟩

end TauCeti

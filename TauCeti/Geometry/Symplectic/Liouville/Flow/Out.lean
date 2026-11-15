/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Flow.FlowOut
public import TauCeti.Geometry.Manifold.LocalDiffeomorph.Injective
public import TauCeti.Geometry.Symplectic.Liouville.LinearAtInfinity

/-!
# The cylindrical end of a completion as a half-symplectization

Let `M` be a completion of the Liouville domain `W ⊆ M` (`TauCeti.IsLiouvilleCompletion`), with
Liouville field `Z` and Liouville flow `ψ`, on a finite-dimensional boundaryless manifold. The
boundary `∂W` is parametrized by a smooth immersion `ι : S → M` of a boundaryless manifold of one
dimension less, injective with image the frontier of `W`; for instance the inclusion of a regular
level of a defining function.

The Liouville field crosses the boundary outwards, so it is transverse along `ι`
(`TauCeti.IsLiouvilleDomain.isTransverseAlong`), and by the flow-out theorem
(`TauCeti.isLocalDiffeomorph_globalFlow_comp`) the map `Φ (t, s) = ψₜ (ι s)` is a local
diffeomorphism `ℝ × S → M` (`TauCeti.IsLiouvilleDomain.isLocalDiffeomorph_flowOf_comp`). Distinct
Liouville trajectories through the boundary are disjoint, so `Φ` is injective
(`TauCeti.IsLiouvilleDomain.injective_flowOf_comp`). So the whole symplectization `ℝ × S` embeds
openly in `M` along the Liouville flow (`TauCeti.IsLiouvilleDomain.isOpenEmbedding_flowOf_comp`),
and `Φ` maps `(0, ∞) × S` bijectively onto the complement of `W`
(`TauCeti.IsLiouvilleCompletion.bijOn_flowOf_comp`).

Hence `Φ` restricts to a diffeomorphism from `(0, ∞) × S` onto `M \ W`
(`TauCeti.IsLiouvilleCompletion.cylindricalEndPartialDiffeomorph`). Together with
`TauCeti.mpullback_globalFlow_comp_eq_symplectization`, which shows `Φ^* α = eᵗ ι^* α`, this
identifies the cylindrical end of the completion, in the coordinate `r = eᵗ`, with the end
`(1, ∞) × ∂W` of the symplectization of the contact boundary `(∂W, ι^* α)`, smoothly in both
directions. The inverse sends a point `x ∉ W` to the logarithm of its radial coordinate and the
boundary point it flows out of.

## Main results

* `TauCeti.IsLiouvilleDomain.isTransverseAlong`: the Liouville field is transverse along every
  differentiable map into the boundary.
* `TauCeti.IsLiouvilleDomain.isLocalDiffeomorph_flowOf_comp`: the Liouville flow-out of an
  immersed boundary is a local diffeomorphism.
* `TauCeti.IsLiouvilleDomain.isOpenEmbedding_flowOf_comp`: the flow-out of an injectively
  immersed boundary is an open embedding of `ℝ × S`.
* `TauCeti.IsLiouvilleCompletion.bijOn_flowOf_comp`: on a completion, the flow-out maps
  `(0, ∞) × S` bijectively onto the complement of `W`.
* `TauCeti.IsLiouvilleCompletion.cylindricalEndPartialDiffeomorph`: the Liouville flow-out of the
  boundary, as a diffeomorphism from `(0, ∞) × S` onto the complement of `W`.
* `TauCeti.IsLiouvilleCompletion.cylindricalEndPartialDiffeomorph_symm_apply_fst`: its inverse
  reads off the logarithm of the radial coordinate.

## References

* P. Seidel, *A biased view of symplectic cohomology*, Current Developments in Mathematics 2006,
  Section 3 (Liouville domains and their completions).
* K. Cieliebak, Y. Eliashberg, *From Stein to Weinstein and Back*, AMS Colloquium Publications 59,
  2012, Section 11.1.
* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Graduate Texts in Mathematics 218,
  Springer, 2013, Theorem 9.20 (the flow-out theorem).
-/

public section

open Function Module Set
open scoped Manifold

namespace TauCeti

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless] [TopologicalSpace M]
  [ChartedSpace H M] [T2Space M] [IsManifold I (⊤ : ℕ∞) M] {ω : SmoothTwoForm I M}
  {α : SmoothForm I M ℝ 1} {W : Set M} {Z : (x : M) → TangentSpace I x}
  {E' H' S : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
  {J : ModelWithCorners ℝ E' H'} {ι : S → M}

/-! ### Injectivity and image of the flow-out -/

/-- **The Liouville trajectories through an injectively parametrized boundary are disjoint.** If
the Liouville field of a Liouville domain is complete and `ι : S → M` is an injective map into
the boundary, then `(t, s) ↦ ψₜ (ι s)` is injective on `ℝ × S`. -/
theorem IsLiouvilleDomain.injective_flowOf_comp (h : IsLiouvilleDomain ω α W)
    (hZ : RoughForm.interior Z ω.1 = α.1) (hc : IsCompleteVectorField Z) (hιinj : Injective ι)
    (hιW : ∀ s, ι s ∈ frontier W) :
    Injective (fun p : ℝ × S ↦ flowOf Z p.1 (ι p.2)) := fun p q hpq ↦ by
  have := h.injOn_flowOf hZ hc (x₁ := (ι p.2, p.1)) (x₂ := (ι q.2, q.1)) ⟨hιW _, mem_univ _⟩
    ⟨hιW _, mem_univ _⟩ hpq
  simp only [Prod.mk.injEq] at this
  exact Prod.ext this.2 (hιinj this.1)

/-- **The cylindrical end of a completion in boundary coordinates.** Let `M` be a completion of
the Liouville domain `W`, with Liouville flow `ψ`, and let `ι : S → M` be an injective map onto
the boundary of `W`. Then `(t, s) ↦ ψₜ (ι s)` is a bijection from `(0, ∞) × S` onto the
complement of `W`. -/
theorem IsLiouvilleCompletion.bijOn_flowOf_comp (h : IsLiouvilleCompletion ω α W)
    (hZ : RoughForm.interior Z ω.1 = α.1) (hιinj : Injective ι) (hιW : range ι = frontier W) :
    BijOn (fun p : ℝ × S ↦ flowOf Z p.1 (ι p.2)) (Ioi 0 ×ˢ univ) Wᶜ := by
  -- `(t, s) ↦ (t, ι s)` is a bijection onto `(0, ∞) × ∂W`; compose with the flow map.
  have hmap : BijOn (Prod.map id ι) (Ioi (0 : ℝ) ×ˢ (univ : Set S)) (Ioi 0 ×ˢ frontier W) := by
    have := (bijOn_id (Ioi (0 : ℝ))).prodMap (hιinj.bijOn_image (s := univ))
    rwa [image_univ, hιW] at this
  exact (h.bijOn_flowOf_Ioi_prod_frontier hZ).comp hmap

/-! ### Smoothness of the flow-out -/

variable [TopologicalSpace S] [ChartedSpace H' S]

namespace IsLiouvilleDomain

omit [FiniteDimensional ℝ E] [T2Space M] in
/-- **The Liouville field is transverse to the boundary.** If `ι : S → M` is a differentiable map
into the boundary of a Liouville domain, then the Liouville field is transverse along `ι`: at
every point of `S` it does not lie in the image of the differential of `ι`, since it crosses the
boundary strictly outwards. -/
theorem isTransverseAlong (h : IsLiouvilleDomain ω α W) (hZ : RoughForm.interior Z ω.1 = α.1)
    (hι : MDifferentiable J I ι) (hιW : ∀ s, ι s ∈ frontier W) :
    IsTransverseAlong J Z ι := by
  obtain ⟨f, c, hf, rfl, hfc⟩ := h.exists_sublevel_of_interior_eq hZ
  rw [frontier_setOf_le_eq_of_mvfderiv_pos hf fun y hy ↦ (hfc y hy).2] at hιW
  refine isTransverseAlong_iff.2 fun s hs ↦ ?_
  obtain ⟨w, hw⟩ := LinearMap.mem_range.1 hs
  rw [ContinuousLinearMap.coe_coe] at hw
  -- `f ∘ ι` is constant, so `df (Z (ι s)) = df (dι w) = d(f ∘ ι) w` vanishes.
  have hfι : f ∘ ι = fun _ ↦ c := funext hιW
  have h0 : mvfderiv I f (ι s) (Z (ι s)) = 0 := by
    rw [mvfderiv_apply_eq_mfderiv_apply, ← hw, ← mfderiv_comp_apply (I' := I) s
      (((hfc _ (hιW s)).1).mdifferentiableAt (by simp)) (hι s) w,
      hfι, mfderiv_const]
    -- The zero map applied to `w`, read in the tangent space of `ℝ` at `c`.
    rfl
  exact (hfc _ (hιW s)).2.ne' h0

variable [IsManifold J (⊤ : ℕ∞) S] [BoundarylessManifold J S]

/-- **The Liouville flow-out of the boundary is a local diffeomorphism.** Let `W` be a Liouville
domain whose Liouville field `Z` is complete, with flow `ψ`, and let `ι : S → M` be a smooth
immersion into the boundary of `W` of a boundaryless manifold of one dimension less. Then
`(t, s) ↦ ψₜ (ι s)` is a local diffeomorphism `ℝ × S → M`. -/
theorem isLocalDiffeomorph_flowOf_comp (h : IsLiouvilleDomain ω α W)
    (hZ : RoughForm.interior Z ω.1 = α.1) (hc : IsCompleteVectorField Z)
    (hι : ContMDiff J I (⊤ : ℕ∞) ι) (himm : ∀ s, Injective (mfderiv J I ι s))
    (hιW : ∀ s, ι s ∈ frontier W) (hdim : finrank ℝ E = finrank ℝ E' + 1) :
    IsLocalDiffeomorph (𝓘(ℝ).prod J) I (⊤ : ℕ∞) (fun p : ℝ × S ↦ flowOf Z p.1 (ι p.2)) := by
  have hZs := h.contMDiff_of_interior_eq hZ
  rw [flowOf_eq_globalFlow (hZs.of_le (by simp)) hc]
  exact isLocalDiffeomorph_globalFlow_comp hc le_top hZs hι himm
    (h.isTransverseAlong hZ (hι.mdifferentiable (by simp)) hιW) hdim

/-- **The symplectization of the boundary embeds along the Liouville flow.** Let `W` be a
Liouville domain whose Liouville field is complete, with flow `ψ`, and let `ι : S → M` be a smooth
injective immersion into the boundary of `W` of a boundaryless manifold of one dimension less.
Then `(t, s) ↦ ψₜ (ι s)` is an open embedding of `ℝ × S` into `M`. -/
theorem isOpenEmbedding_flowOf_comp (h : IsLiouvilleDomain ω α W)
    (hZ : RoughForm.interior Z ω.1 = α.1) (hc : IsCompleteVectorField Z)
    (hι : ContMDiff J I (⊤ : ℕ∞) ι) (himm : ∀ s, Injective (mfderiv J I ι s))
    (hιinj : Injective ι) (hιW : ∀ s, ι s ∈ frontier W) (hdim : finrank ℝ E = finrank ℝ E' + 1) :
    Topology.IsOpenEmbedding (fun p : ℝ × S ↦ flowOf Z p.1 (ι p.2)) :=
  (h.isLocalDiffeomorph_flowOf_comp hZ hc hι himm hιW hdim).isLocalHomeomorph
    |>.isOpenEmbedding_of_injective (h.injective_flowOf_comp hZ hc hιinj hιW)

end IsLiouvilleDomain

namespace IsLiouvilleCompletion

variable [IsManifold J (⊤ : ℕ∞) S] [BoundarylessManifold J S] [Nonempty S]

/-- **The cylindrical end of a completion is the positive half of the symplectization of the
boundary.** Let `M` be a completion of the Liouville domain `W`, on a finite-dimensional
boundaryless manifold, with Liouville flow `ψ`, and let `ι : S → M` be a smooth injective
immersion onto the boundary of `W`, from a boundaryless manifold of one dimension less. Then
`(t, s) ↦ ψₜ (ι s)` restricts to a diffeomorphism from `(0, ∞) × S` onto the complement of `W`. -/
noncomputable def cylindricalEndPartialDiffeomorph (h : IsLiouvilleCompletion ω α W)
    (hZ : RoughForm.interior Z ω.1 = α.1) (hι : ContMDiff J I (⊤ : ℕ∞) ι)
    (himm : ∀ s, Injective (mfderiv J I ι s)) (hιinj : Injective ι) (hιW : range ι = frontier W)
    (hdim : finrank ℝ E = finrank ℝ E' + 1) :
    PartialDiffeomorph (𝓘(ℝ).prod J) I (ℝ × S) M (⊤ : ℕ∞) :=
  ((h.isLocalDiffeomorph_flowOf_comp hZ (h.isCompleteVectorField hZ) hι himm
    (fun s ↦ hιW ▸ mem_range_self s) hdim).isLocalDiffeomorphOn _).partialDiffeomorphOfInjOn
    (isOpen_Ioi.prod isOpen_univ) (h.bijOn_flowOf_comp hZ hιinj hιW).injOn

variable (h : IsLiouvilleCompletion ω α W) (hZ : RoughForm.interior Z ω.1 = α.1)
  (hι : ContMDiff J I (⊤ : ℕ∞) ι) (himm : ∀ s, Injective (mfderiv J I ι s)) (hιinj : Injective ι)
  (hιW : range ι = frontier W) (hdim : finrank ℝ E = finrank ℝ E' + 1)

/-- The diffeomorphism `cylindricalEndPartialDiffeomorph` is the Liouville flow-out of the
boundary. -/
@[simp]
theorem coe_cylindricalEndPartialDiffeomorph :
    ⇑(h.cylindricalEndPartialDiffeomorph hZ hι himm hιinj hιW hdim) =
      fun p : ℝ × S ↦ flowOf Z p.1 (ι p.2) :=
  IsLocalDiffeomorphOn.coe_partialDiffeomorphOfInjOn ..

/-- The source of `cylindricalEndPartialDiffeomorph` is `(0, ∞) × S`. -/
@[simp]
theorem cylindricalEndPartialDiffeomorph_source :
    (h.cylindricalEndPartialDiffeomorph hZ hι himm hιinj hιW hdim).source = Ioi 0 ×ˢ univ :=
  IsLocalDiffeomorphOn.partialDiffeomorphOfInjOn_source ..

/-- The target of `cylindricalEndPartialDiffeomorph` is the complement of the Liouville domain. -/
@[simp]
theorem cylindricalEndPartialDiffeomorph_target :
    (h.cylindricalEndPartialDiffeomorph hZ hι himm hιinj hιW hdim).target = Wᶜ := by
  rw [cylindricalEndPartialDiffeomorph, IsLocalDiffeomorphOn.partialDiffeomorphOfInjOn_target,
    (h.bijOn_flowOf_comp hZ hιinj hιW).image_eq]

/-- **The time coordinate of the end is the logarithm of the radial coordinate.** The inverse of
`cylindricalEndPartialDiffeomorph` sends a point `x` outside the Liouville domain to
`(log r(x), s)`, where `r` is the radial coordinate of the completion and `ι s` is the boundary
point `x` flows out of. -/
theorem cylindricalEndPartialDiffeomorph_symm_apply_fst {x : M} (hx : x ∉ W) :
    ((h.cylindricalEndPartialDiffeomorph hZ hι himm hιinj hιW hdim).symm x).1 =
      Real.log (liouvilleRadialCoordinate Z W x) := by
  set Φ := h.cylindricalEndPartialDiffeomorph hZ hι himm hιinj hιW hdim
  have hxt : x ∈ Φ.target := by rwa [cylindricalEndPartialDiffeomorph_target]
  have hps : Φ.symm x ∈ Φ.source := Φ.map_target hxt
  rw [cylindricalEndPartialDiffeomorph_source] at hps
  -- `x = ψₜ (ι s)` with `t > 0` and `ι s ∈ ∂W`, so `r(x) = eᵗ`.
  have hx' : flowOf Z (Φ.symm x).1 (ι (Φ.symm x).2) = x :=
    (congrFun (coe_cylindricalEndPartialDiffeomorph h hZ hι himm hιinj hιW hdim)
      (Φ.symm x)).symm.trans (Φ.toPartialEquiv.right_inv hxt)
  rw [← hx', h.liouvilleRadialCoordinate_flowOf hZ (hιW ▸ mem_range_self _) hps.1.le,
    Real.log_exp, hx']

end IsLiouvilleCompletion

end TauCeti

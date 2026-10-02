/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Conformal.Jordan.UpperHalfPlane
public import TauCeti.Topology.JordanCurve.OnePoint
import Mathlib.Topology.Bornology.BoundedOperation
import TauCeti.Analysis.Complex.Conformal.ImageSimplyConnected

/-!
# Carathéodory's theorem for unbounded domains bounded by a line

An unbounded domain `U` whose frontier is homeomorphic to the real line is a Jordan domain on the
Riemann sphere: its frontier, together with the point at infinity, is a Jordan curve.  Inverting
about a point `p` outside the closure of `U` turns it into a bounded Jordan domain, to which
Carathéodory's theorem on the closed upper half-plane applies.  Undoing the inversion gives a
conformal map of the upper half-plane onto `U` which extends to a bijection of the closed upper
half-plane onto the closure of `U`, of the real line onto the frontier of `U`, and which tends
to infinity at infinity.

The inversion `z ↦ (z - p)⁻¹` is a bijection of `ℂ` (it sends `p` to `0` because `0⁻¹ = 0`),
inverted by `w ↦ w⁻¹ + p`.  It is not continuous at `p`, but on a set whose closure omits `p` it
behaves as a homeomorphism should, which is what the first results below record.

## Main results

* `TauCeti.closure_image_inv_sub`, `TauCeti.frontier_image_inv_sub`: inverting an unbounded set
  about a point outside its closure adjoins `0` to the inverted closure and frontier.
* `TauCeti.isJordanCurve_insert_zero_image_inv_sub`: a closed copy of the real line, inverted
  about a point off it and completed by `0`, is a Jordan curve.
* `TauCeti.exists_continuousOn_bijOn_upperHalfPlaneSet_of_frontier_homeomorph_real`:
  Carathéodory's theorem on the closed upper half-plane for a simply connected domain whose
  frontier is homeomorphic to the real line, with infinity sent to infinity.
* `TauCeti.exists_prevertices_of_frontier_homeomorph_real`: such a map with real prevertices
  sent to prescribed frontier points.

## References

* C. Carathéodory, Über die gegenseitige Beziehung der Ränder bei der konformen Abbildung,
  Math. Ann. 73 (1913).
* Ch. Pommerenke, Boundary Behaviour of Conformal Maps, Springer, 1992, Ch. 2.
-/

public section

open Bornology Complex Filter Function Metric Set Topology UpperHalfPlane

namespace TauCeti

variable {p : ℂ}

/-- The inversion about `p` is injective on all of `ℂ`. -/
private theorem injective_inv_sub : Injective fun z : ℂ => (z - p)⁻¹ :=
  fun _ _ h => sub_left_injective (inv_injective h)

/-- On all of `ℂ`, the inversion about `p` is inverted by `w ↦ w⁻¹ + p`, so it maps any set `S`
bijectively onto its image with that inverse. -/
private theorem bijOn_inv_add_image_inv_sub (S : Set ℂ) :
    BijOn (fun w : ℂ => w⁻¹ + p) ((fun z : ℂ => (z - p)⁻¹) '' S) S :=
  injective_inv_sub.injOn.bijOn_image.symm ⟨fun _ _ => by simp, fun _ _ => by simp⟩

/-- The inversion about `p` is continuous on any set omitting `p`. -/
private theorem continuousOn_inv_sub {S : Set ℂ} (hp : p ∉ S) :
    ContinuousOn (fun z : ℂ => (z - p)⁻¹) S := fun _ hz =>
  ((continuous_sub_right p).continuousAt.inv₀
    (sub_ne_zero.2 fun h => hp (h ▸ hz))).continuousWithinAt

/-- The inversion about `p` is holomorphic on any set omitting `p`. -/
private theorem differentiableOn_inv_sub {S : Set ℂ} (hp : p ∉ S) :
    DifferentiableOn ℂ (fun z : ℂ => (z - p)⁻¹) S := fun _ hz =>
  ((differentiableAt_id.sub_const p).inv
    (sub_ne_zero.2 fun h => hp (h ▸ hz))).differentiableWithinAt

/-- The inversion about `p` vanishes only at `p`. -/
private theorem zero_notMem_image_inv_sub {S : Set ℂ} (hp : p ∉ S) :
    (0 : ℂ) ∉ (fun z : ℂ => (z - p)⁻¹) '' S := by
  rintro ⟨z, hz, hz0⟩
  rw [inv_eq_zero, sub_eq_zero] at hz0
  exact hp (hz0 ▸ hz)

/-- **The closure of an inverted set.**  Inverting an unbounded set `U` about a point `p` outside
its closure, the closure of the image is the image of the closure of `U` together with `0`, the
image of the point at infinity. -/
theorem closure_image_inv_sub {U : Set ℂ} (hp : p ∉ closure U) (hU : ¬IsBounded U) :
    closure ((fun z : ℂ => (z - p)⁻¹) '' U) =
      insert 0 ((fun z : ℂ => (z - p)⁻¹) '' closure U) := by
  refine Subset.antisymm (fun w hw => ?_) (insert_subset ?_ (continuousOn_inv_sub hp).image_closure)
  · rcases eq_or_ne w 0 with rfl | hw0
    · exact mem_insert _ _
    -- away from `0` the inverse inversion is continuous and carries the image back onto `U`
    have hk : ContinuousAt (fun u : ℂ => u⁻¹ + p) w :=
      (continuousAt_inv₀ hw0).add continuousAt_const
    have hmem := mem_closure_image hk hw
    simp only [image_image, inv_inv, sub_add_cancel, image_id'] at hmem
    exact mem_insert_of_mem _ ⟨_, hmem, by simp⟩
  · -- `0` is the limit of the inversion along `U` at infinity
    have hne : NeBot (cobounded ℂ ⊓ 𝓟 U) := by
      refine inf_principal_neBot_iff.2 fun s hs => not_disjoint_iff_nonempty_inter.1 fun hd => hU ?_
      exact (isBounded_compl_iff.2 hs).subset hd.subset_compl_left
    have ht : Tendsto (fun z : ℂ => (z - p)⁻¹) (cobounded ℂ ⊓ 𝓟 U) (𝓝 0) :=
      (tendsto_inv₀_cobounded.comp (tendsto_sub_const_cobounded p)).mono_left inf_le_left
    exact mem_closure_of_tendsto ht
      (eventually_inf_principal.2 (Eventually.of_forall fun z hz => mem_image_of_mem _ hz))

/-- **The frontier of an inverted open set.**  Inverting an unbounded open set `U` about a point
`p` outside its closure, the frontier of the image is the image of the frontier of `U` together
with `0`, the image of the point at infinity. -/
theorem frontier_image_inv_sub {U : Set ℂ} (hUo : IsOpen U) (hp : p ∉ closure U)
    (hU : ¬IsBounded U) :
    frontier ((fun z : ℂ => (z - p)⁻¹) '' U) =
      insert 0 ((fun z : ℂ => (z - p)⁻¹) '' frontier U) := by
  have hpU : p ∉ U := fun h => hp (subset_closure h)
  have hVo : IsOpen ((fun z : ℂ => (z - p)⁻¹) '' U) :=
    isOpen_image_of_differentiableOn_of_injOn hUo (differentiableOn_inv_sub hpU)
      injective_inv_sub.injOn
  rw [hVo.frontier_eq, closure_image_inv_sub hp hU, hUo.frontier_eq,
    image_sdiff injective_inv_sub, insert_sdiff_of_notMem _ (zero_notMem_image_inv_sub hpU)]

/-- **A line through infinity, inverted, is a Jordan curve.**  If `C` is a closed subset of `ℂ`
homeomorphic to the real line and `p ∉ C`, then the image of `C` under the inversion about `p`,
completed by `0`, is a Jordan curve: the homeomorphism is proper, so both ends of the line tend to
infinity, and inverting sends them both to `0`. -/
theorem isJordanCurve_insert_zero_image_inv_sub {C : Set ℂ} (hC : IsClosed C) (e : C ≃ₜ ℝ)
    (hp : p ∉ C) : IsJordanCurve (insert 0 ((fun z : ℂ => (z - p)⁻¹) '' C)) := by
  let Φ : OnePoint ℝ → ℂ := fun x => x.elim 0 fun t => ((e.symm t : ℂ) - p)⁻¹
  have hemb : IsClosedEmbedding fun t => (e.symm t : ℂ) :=
    hC.isClosedEmbedding_subtypeVal.comp e.symm.isClosedEmbedding
  have hΦ : Continuous Φ := by
    refine (OnePoint.continuous_iff Φ).2 ⟨?_, ?_⟩
    · rw [coclosedCompact_eq_cocompact]
      exact tendsto_inv₀_cobounded.comp ((tendsto_sub_const_cobounded p).comp
        (cobounded_eq_cocompact (α := ℂ) ▸ hemb.tendsto_cocompact))
    · exact (continuousOn_inv_sub hp).comp_continuous hemb.continuous fun t => (e.symm t).2
  have hΦi : Injective Φ := by
    have hne (t : ℝ) : ((e.symm t : ℂ) - p)⁻¹ ≠ 0 :=
      inv_ne_zero (sub_ne_zero.2 fun h => hp (h ▸ (e.symm t).2))
    rintro (_ | s) (_ | t) h
    · rfl
    · exact absurd h.symm (hne t)
    · exact absurd h (hne s)
    · exact congrArg _ (e.symm.injective (Subtype.ext (injective_inv_sub h)))
  convert isJordanCurve_univ_onePoint_real.image hΦ.continuousOn hΦi.injOn using 1
  ext w
  simp only [mem_insert_iff, mem_image, mem_univ, true_and, OnePoint.exists]
  refine or_congr (eq_comm.trans (by rfl)) ⟨?_, ?_⟩
  · rintro ⟨z, hz, rfl⟩
    exact ⟨e ⟨z, hz⟩, by simp [Φ]⟩
  · rintro ⟨t, rfl⟩
    exact ⟨_, (e.symm t).2, rfl⟩

/-- **Carathéodory's theorem for a domain bounded by a line.**  Let `U` be a simply connected open
subset of `ℂ` whose closure is not the whole plane and whose frontier is homeomorphic to the real
line.  Then there is a map which is continuous on the closed upper half-plane, holomorphic on the
open upper half-plane, a bijection from the open upper half-plane onto `U`, from the closed upper
half-plane onto the closure of `U` and from the real line onto the frontier of `U`, and which
tends to infinity at infinity within the closed half-plane. -/
theorem exists_continuousOn_bijOn_upperHalfPlaneSet_of_frontier_homeomorph_real {U : Set ℂ}
    (hUo : IsOpen U) (hUc : IsSimplyConnected U) (hUd : closure U ≠ univ)
    (hUJ : Nonempty (frontier U ≃ₜ ℝ)) :
    ∃ f : ℂ → ℂ, ContinuousOn f {z | 0 ≤ z.im} ∧
      DifferentiableOn ℂ f upperHalfPlaneSet ∧
      BijOn f upperHalfPlaneSet U ∧ BijOn f {z | 0 ≤ z.im} (closure U) ∧
      BijOn f {z | z.im = 0} (frontier U) ∧
      Tendsto f (cobounded ℂ ⊓ 𝓟 {z | 0 ≤ z.im}) (cobounded ℂ) := by
  obtain ⟨e⟩ := hUJ
  obtain ⟨p, hp⟩ : ∃ p, p ∉ closure U := by
    by_contra! h
    exact hUd (eq_univ_of_forall h)
  have hpU : p ∉ U := fun h => hp (subset_closure h)
  have hpF : p ∉ frontier U := fun h => hp (frontier_subset_closure h)
  -- `U` is unbounded: otherwise its frontier would be compact, and so would the real line
  have hU : ¬IsBounded U := fun hb => by
    have := isCompact_iff_compactSpace.1 (isCompact_of_isClosed_isBounded isClosed_frontier
      (hb.closure.subset frontier_subset_closure))
    exact not_compactSpace_iff.2 inferInstance (e.compactSpace)
  -- inverting about `p` turns `U` into a bounded Jordan domain `g '' U`
  set g : ℂ → ℂ := fun z => (z - p)⁻¹
  have hgd : DifferentiableOn ℂ g U := differentiableOn_inv_sub hpU
  have hgi : InjOn g U := injective_inv_sub.injOn
  have hVb : IsBounded (g '' U) := by
    obtain ⟨r, hr, hrU⟩ := Metric.isOpen_iff.1 isClosed_closure.isOpen_compl _ hp
    refine isBounded_iff_forall_norm_le.2 ⟨r⁻¹, ?_⟩
    rintro _ ⟨z, hz, rfl⟩
    have hzr : r ≤ ‖z - p‖ := by
      by_contra! h
      exact hrU (by rwa [mem_ball, dist_eq_norm]) (subset_closure hz)
    simpa [g, norm_inv] using inv_anti₀ hr hzr
  have hVF := frontier_image_inv_sub hUo hp hU
  obtain ⟨φ, hφc, hφd, hφH, hφcl, hφR, hφ0⟩ :=
    exists_continuousOn_bijOn_upperHalfPlaneSet_of_isJordanCurve_frontier
      (isOpen_image_of_differentiableOn_of_injOn hUo hgd hgi)
      (isSimplyConnected_image_of_differentiableOn_of_injOn hUo hUc hgd hgi) hVb
      (hVF ▸ isJordanCurve_insert_zero_image_inv_sub isClosed_frontier e hpF)
      (hVF ▸ mem_insert 0 _)
  -- undo the inversion
  have hsdiff {S : Set ℂ} (hS : p ∉ S) : insert 0 (g '' S) \ {0} = g '' S :=
    insert_sdiff_self_of_notMem (zero_notMem_image_inv_sub hS)
  rw [closure_image_inv_sub hp hU, hsdiff hp] at hφcl
  rw [hVF, hsdiff hpF] at hφR
  have hφ0' : ∀ z ∈ {z : ℂ | 0 ≤ z.im}, φ z ≠ 0 := fun z hz h =>
    zero_notMem_image_inv_sub hp (h ▸ hφcl.mapsTo hz)
  have hH0 : upperHalfPlaneSet ⊆ {z : ℂ | 0 ≤ z.im} := ofPred_subset_ofPred.mpr fun _ => le_of_lt
  refine ⟨fun z => (φ z)⁻¹ + p, ?_, ?_, (bijOn_inv_add_image_inv_sub U).comp hφH,
    (bijOn_inv_add_image_inv_sub _).comp hφcl, (bijOn_inv_add_image_inv_sub _).comp hφR, ?_⟩
  · exact (hφc.inv₀ hφ0').add continuousOn_const
  · exact (hφd.inv fun z hz => hφ0' z (hH0 hz)).add_const p
  · refine (tendsto_add_const_cobounded p).comp (tendsto_inv₀_nhdsNE_zero.comp ?_)
    exact tendsto_nhdsWithin_iff.2 ⟨hφ0, eventually_inf_principal.2 (Eventually.of_forall hφ0')⟩

/-- A Carathéodory map of the upper half-plane onto a simply connected domain whose frontier is
homeomorphic to the real line, tending to infinity at infinity, together with real prevertices
`a i` mapping to prescribed frontier points `v i`. -/
theorem exists_prevertices_of_frontier_homeomorph_real
    {ι : Type*} {U : Set ℂ} (hUo : IsOpen U) (hUc : IsSimplyConnected U)
    (hUd : closure U ≠ univ) (hUJ : Nonempty (frontier U ≃ₜ ℝ)) {v : ι → ℂ} (hv : Injective v)
    (hvU : ∀ i, v i ∈ frontier U) :
    ∃ f : ℂ → ℂ, ∃ a : ι → ℝ, Injective a ∧
      DifferentiableOn ℂ f upperHalfPlaneSet ∧ ContinuousOn f {z : ℂ | 0 ≤ z.im} ∧
      InjOn f {z : ℂ | 0 ≤ z.im} ∧ BijOn f upperHalfPlaneSet U ∧ (∀ i, f (a i) = v i) ∧
      Tendsto f (cobounded ℂ ⊓ 𝓟 {z : ℂ | 0 ≤ z.im}) (cobounded ℂ) := by
  obtain ⟨f, hfc, hfd, hfH, hfcl, hfR, hfinf⟩ :=
    exists_continuousOn_bijOn_upperHalfPlaneSet_of_frontier_homeomorph_real hUo hUc hUd hUJ
  -- every prescribed point lies on the frontier, so it has a real preimage under `f`
  choose x hx hfx using fun i => hfR.surjOn (hvU i)
  have hax (i : ι) : (((x i).re : ℝ) : ℂ) = x i :=
    Complex.ext (by simp) (by simpa using (hx i).symm)
  have hfa (i : ι) : f (x i).re = v i := by rw [hax, hfx]
  refine ⟨f, fun i => (x i).re, fun i j h => hv ?_, hfd, hfc, hfcl.injOn, hfH, hfa, hfinf⟩
  rw [← hfa i, ← hfa j, show (x i).re = (x j).re from h]

end TauCeti

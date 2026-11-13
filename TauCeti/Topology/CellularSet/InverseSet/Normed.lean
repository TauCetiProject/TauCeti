/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.CellularSet.Basic
import TauCeti.AlgebraicTopology.Singular.InvarianceOfDomain
import TauCeti.Analysis.Normed.Module.Ball.Radial.OrderIso
import TauCeti.Analysis.Normed.Module.Connected
import TauCeti.Topology.Separation.InvFunOn

/-!
# The only inverse set of a map of a cell between spaces of the same dimension is cellular

Let `E` and `F` be finite-dimensional real normed spaces of the same dimension, and let
`f : E → F` be continuous on an open set `U ⊆ E` and injective on `U` away from the fibre
`M = U ∩ f⁻¹{p}` of a single point `p`. In M. Brown's language, `M` is the only inverse set of `f`
on `U`.

The first result is the one-inverse-set case of Brown's Theorem 0: if `M` is compact, then `f`
maps `U` onto an open subset of `F` (`IsOpen.image_of_continuousOn_of_injOn_sdiff`). Away from
`p` this is Brouwer's invariance of domain, applied to `U \ M`. At a value `p` of `f` on `U`,
choose a compact `K ⊆ U` with `M` in its interior `V`. A small ball `ball p r` around `p` misses
the image of `K \ V`, so within it the image of `V \ M` is relatively closed in the punctured ball
and open. In dimension at least two the punctured ball is connected, and the image of `V \ M`
accumulates at `p`, so it fills the punctured ball. In dimension one the punctured ball has two
sides; if the image of `V \ M` filled only one, then the segments leaving `M` in the two
directions of `E` would cross the same values near `p`, contradicting injectivity.

The second result is Brown's Theorem 3, for `f` continuous on the closed unit ball `B` of `E` and
injective on `B` away from a fibre `M = B ∩ f⁻¹{p}` which lies in the open unit ball: if `M` is
nonempty, that is `p ∈ f '' B`, then `M` is cellular
(`TauCeti.isCellularSet_closedBall_inter_preimage_of_finrank_eq`). Given an open `U ⊇ M`, choose a
homeomorphism `h` of `F` which fixes a neighbourhood of `p` and pulls the compact set `f '' B`
into the open set `f '' (U ∩ ball 0 1)`. Then `g = f⁻¹ ∘ h ∘ f` on `B \ M`, extended by the
identity on `M`, is a continuous injection of `B` into `U` which is the identity near `M`, so its
image is a closed cell in `U` with `M` in its interior
(`TauCeti.exists_continuousOn_injOn_image_closedBall_subset_of_injOn_closedBall_sdiff`).

Maps of an `n`-cell into the unit sphere `Sⁿ` of a space of dimension `n + 1` reduce to this case
through a stereographic projection
(`TauCeti.isCellularSet_closedBall_inter_preimage` in
`TauCeti.Topology.CellularSet.InverseSet.Sphere`).

These are steps in Brown's proof of the generalized Schoenflies theorem. There, the map of the
sphere `Sⁿ` collapsing the two outer pieces of a bicollar has exactly two inverse sets, and
Theorem 4 applies Theorem 3 to recognize both of them as cellular.

## Main results

* `IsOpen.image_of_continuousOn_of_injOn_sdiff`: the image of an open set under a map injective
  on it away from one compact fibre is open (Brown's Theorem 0 for one inverse set).
* `TauCeti.exists_continuousOn_injOn_image_closedBall_subset_of_injOn_closedBall_sdiff`: every
  neighbourhood of a nonempty only inverse set contains a closed cell with the inverse set in its
  interior.
* `TauCeti.isCellularSet_closedBall_inter_preimage_of_finrank_eq`: a nonempty only inverse set is
  cellular (Brown's Theorem 3).

## References

* M. Brown, *A proof of the generalized Schoenflies theorem*, Bull. Amer. Math. Soc. 66 (1960),
  74–76, Theorems 0 and 3.
-/

public section

open Set Metric Filter Topology Function Module

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F] {f : E → F} {p : F}

namespace TauCeti

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
/-- Let `m` be a point of an open set `U` on which `f` is continuous, with `f m = p`, and leave `m`
along a direction `w` on which `φ ∘ f` exceeds `φ p` at every positive time with `m + s • w ∈ U`
and `f (m + s • w)` near `p`. Then for some `t > 0` the segment from `m` to `m + t • w` stays in
`U`, and the values of `φ ∘ f` on it cover the interval `Ioc (φ p) (φ (f (m + t • w)))` at
positive times. -/
private theorem exists_segment_Ioc_subset {U : Set E} (hU : IsOpen U) (hf : ContinuousOn f U)
    {m : E} (hmU : m ∈ U) (hfm : f m = p) (w : E) (φ : F →L[ℝ] ℝ) {r : ℝ} (hr : 0 < r)
    (hlt : ∀ s : ℝ, 0 < s → m + s • w ∈ U → f (m + s • w) ∈ ball p r → φ p < φ (f (m + s • w))) :
    ∃ t : ℝ, 0 < t ∧ (∀ s ∈ Icc 0 t, m + s • w ∈ U) ∧ φ p < φ (f (m + t • w)) ∧
      ∀ v ∈ Ioc (φ p) (φ (f (m + t • w))), ∃ s ∈ Ioc 0 t, φ (f (m + s • w)) = v := by
  have hfc : ContinuousAt f m := hf.continuousAt (hU.mem_nhds hmU)
  have hN : U ∩ f ⁻¹' ball p r ∈ 𝓝 m :=
    inter_mem (hU.mem_nhds hmU) (hfc.preimage_mem_nhds (hfm ▸ ball_mem_nhds (f m) hr))
  have hγ : Tendsto (fun s : ℝ ↦ m + s • w) (𝓝 0) (𝓝 m) := by
    have : Continuous fun s : ℝ ↦ m + s • w := by fun_prop
    simpa using this.tendsto 0
  obtain ⟨δ, hδ, hδN⟩ := Metric.mem_nhds_iff.1 (hγ hN)
  have hmem (s : ℝ) (hs : s ∈ Icc 0 (δ / 2)) : m + s • w ∈ U ∧ f (m + s • w) ∈ ball p r :=
    hδN (by rw [mem_ball, Real.dist_0_eq_abs, abs_of_nonneg hs.1]; linarith [hs.2])
  have hcont : ContinuousOn (fun s : ℝ ↦ φ (f (m + s • w))) (Icc 0 (δ / 2)) :=
    φ.continuous.comp_continuousOn (hf.comp (by fun_prop) fun s hs ↦ (hmem s hs).1)
  refine ⟨δ / 2, half_pos hδ, fun s hs ↦ (hmem s hs).1,
    hlt _ (half_pos hδ) (hmem _ ⟨(half_pos hδ).le, le_rfl⟩).1 (hmem _ ⟨(half_pos hδ).le, le_rfl⟩).2,
    fun v hv ↦ ?_⟩
  exact intermediate_value_Ioc (half_pos hδ).le hcont (by simpa only [zero_smul, add_zero, hfm])

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
/-- **The one-dimensional case of Brown's Theorem 0.** Let `f` be continuous on an open set `U`
and injective on `U` away from the nonempty compact fibre `M = U ∩ f ⁻¹' {p}`, and let `φ` be an
injective linear form on `F`. Then the points of `U \ M` sent near `p` cannot all have `φ`-value
above `φ p`: the segments leaving `M` from its two extreme points along a linear form `ψ` on `E`
would reach the same `φ`-value at two distinct points. -/
private theorem false_of_forall_lt {U : Set E} (hU : IsOpen U) (hf : ContinuousOn f U)
    (hinj : InjOn f (U \ f ⁻¹' {p})) (hM : IsCompact (U ∩ f ⁻¹' {p}))
    (hne : (U ∩ f ⁻¹' {p}).Nonempty) {ψ : E →L[ℝ] ℝ} {v₀ : E} (hv₀ : ψ v₀ = 1)
    {φ : F →L[ℝ] ℝ} (hφ : Injective φ) {r : ℝ} (hr : 0 < r)
    (hlt : ∀ y ∈ U \ f ⁻¹' {p}, f y ∈ ball p r → φ p < φ (f y)) : False := by
  -- The two extreme points of `M` for `ψ`, and the segments leaving `M` from them.
  obtain ⟨m₁, hm₁, hmin⟩ := hM.exists_isMinOn hne ψ.continuous.continuousOn
  obtain ⟨m₂, hm₂, hmax⟩ := hM.exists_isMaxOn hne ψ.continuous.continuousOn
  have hψ₁ (s : ℝ) : ψ (m₁ + s • -v₀) = ψ m₁ - s := by simp [hv₀, sub_eq_add_neg]
  have hψ₂ (s : ℝ) : ψ (m₂ + s • v₀) = ψ m₂ + s := by simp [hv₀]
  obtain ⟨t₁, -, hU₁, hlt₁, hivt₁⟩ := exists_segment_Ioc_subset hU hf hm₁.1 hm₁.2 (-v₀)
    φ hr fun s hs hsU hsr ↦ hlt _ ⟨hsU, fun hsp ↦ by
      have := isMinOn_iff.1 hmin _ ⟨hsU, hsp⟩
      rw [hψ₁] at this
      linarith⟩ hsr
  obtain ⟨t₂, -, hU₂, hlt₂, hivt₂⟩ := exists_segment_Ioc_subset hU hf hm₂.1 hm₂.2 v₀
    φ hr fun s hs hsU hsr ↦ hlt _ ⟨hsU, fun hsp ↦ by
      have := isMaxOn_iff.1 hmax _ ⟨hsU, hsp⟩
      rw [hψ₂] at this
      linarith⟩ hsr
  -- Both segments reach the common value `v` at points `y₁ ≠ y₂` outside `M`.
  set v := min (φ (f (m₁ + t₁ • -v₀))) (φ (f (m₂ + t₂ • v₀)))
  obtain ⟨s₁, hs₁, hv₁⟩ := hivt₁ v ⟨lt_min hlt₁ hlt₂, min_le_left _ _⟩
  obtain ⟨s₂, hs₂, hv₂⟩ := hivt₂ v ⟨lt_min hlt₁ hlt₂, min_le_right _ _⟩
  have hne₁₂ : m₁ + s₁ • -v₀ ≠ m₂ + s₂ • v₀ := by
    intro h
    have h' := congrArg ψ h
    rw [hψ₁, hψ₂] at h'
    have := isMinOn_iff.1 hmin _ hm₂
    linarith [hs₁.1, hs₂.1]
  have hout (y : E) (hyU : y ∈ U) (hy : φ (f y) = v) : y ∈ U \ f ⁻¹' {p} :=
    ⟨hyU, fun hyp ↦
      (lt_min hlt₁ hlt₂).ne ((congrArg φ (mem_singleton_iff.1 hyp)).symm.trans hy)⟩
  exact hne₁₂ (hinj (hout _ (hU₁ s₁ (Ioc_subset_Icc_self hs₁)) hv₁)
    (hout _ (hU₂ s₂ (Ioc_subset_Icc_self hs₂)) hv₂) (hφ (hv₁.trans hv₂.symm)))

/-- **Brown's Theorem 0 in dimension one, near `p`.** In the setting of
`IsOpen.image_of_continuousOn_of_injOn_sdiff` with `dim E = dim F = 1` and a nonempty fibre
`M = U ∩ f ⁻¹' {p}`, suppose that every preconnected subset of the punctured ball
`ball p r \ {p}` meeting `S = f '' (U \ M)` lies in `S`. Then `S` fills the punctured ball: both
of its sides `{φ < φ p}` and `{φ > φ p}`, for a linear isomorphism `φ : F ≃ ℝ`, meet `S` by
`TauCeti.false_of_forall_lt`. -/
private theorem ball_sdiff_singleton_subset_of_finrank_eq_one (hEF : finrank ℝ E = finrank ℝ F)
    (h1 : finrank ℝ F = 1) {U : Set E} (hU : IsOpen U) (hf : ContinuousOn f U)
    (hinj : InjOn f (U \ f ⁻¹' {p})) (hM : IsCompact (U ∩ f ⁻¹' {p}))
    (hne : (U ∩ f ⁻¹' {p}).Nonempty) {r : ℝ} (hr : 0 < r)
    (hconn : ∀ T ⊆ ball p r \ {p}, IsPreconnected T →
      (T ∩ f '' (U \ f ⁻¹' {p})).Nonempty → T ⊆ f '' (U \ f ⁻¹' {p})) :
    ball p r \ {p} ⊆ f '' (U \ f ⁻¹' {p}) := by
  set S := f '' (U \ f ⁻¹' {p})
  have hpS : p ∉ S := fun ⟨z, hz, hzp⟩ ↦ hz.2 hzp
  let φ : F ≃L[ℝ] ℝ := ContinuousLinearEquiv.ofFinrankEq (by rw [finrank_self, h1])
  let ψ : E ≃L[ℝ] ℝ := ContinuousLinearEquiv.ofFinrankEq (by rw [finrank_self, hEF, h1])
  have hψ : (ψ : E →L[ℝ] ℝ) (ψ.symm 1) = 1 := ψ.apply_symm_apply 1
  -- The two sides of `p` in `ball p r`.
  set L := ball p r ∩ {y | φ y < φ p}
  set R := ball p r ∩ {y | φ p < φ y}
  have hLR : ball p r \ {p} ⊆ L ∪ R := fun y ⟨hy, hyp⟩ ↦
    (lt_or_gt_of_ne (φ.injective.ne hyp)).imp (fun h ↦ ⟨hy, h⟩) fun h ↦ ⟨hy, h⟩
  have hLsub : L ⊆ ball p r \ {p} := fun y hy ↦ ⟨hy.1, fun h ↦ (lt_irrefl (φ p)) (h ▸ hy.2)⟩
  have hRsub : R ⊆ ball p r \ {p} := fun y hy ↦ ⟨hy.1, fun h ↦ (lt_irrefl (φ p)) (h ▸ hy.2)⟩
  have hLc : IsPreconnected L := ((convex_ball p r).inter
    (convex_halfSpace_lt φ.toLinearEquiv.toLinearMap.isLinear (φ p))).isPreconnected
  have hRc : IsPreconnected R := ((convex_ball p r).inter
    (convex_halfSpace_gt φ.toLinearEquiv.toLinearMap.isLinear (φ p))).isPreconnected
  -- If one side misses `S`, the points of `U \ M` sent near `p` all lie on the other side.
  have hside (φ' : F →L[ℝ] ℝ) (hφ' : Injective φ')
      (h : ∀ y ∈ S, y ∈ ball p r → φ' y ≠ φ' p → φ' p < φ' y) : False :=
    false_of_forall_lt hU hf hinj hM hne hψ hφ' hr fun y hy hyr ↦
      h _ ⟨y, hy, rfl⟩ hyr (hφ'.ne fun h ↦ hpS (h ▸ ⟨y, hy, rfl⟩))
  by_cases hL : (L ∩ S).Nonempty
  · by_cases hR : (R ∩ S).Nonempty
    · exact hLR.trans (union_subset (hconn L hLsub hLc hL) (hconn R hRsub hRc hR))
    refine (hside (-(φ : F →L[ℝ] ℝ)) (fun a b hab ↦ φ.injective (neg_injective hab))
      fun y hyS hyr hne ↦ ?_).elim
    rw [neg_apply, neg_apply, ne_eq, neg_inj] at hne
    rw [neg_apply, neg_apply, neg_lt_neg_iff]
    exact (lt_or_gt_of_ne hne).resolve_right fun h ↦ hR ⟨y, ⟨hyr, h⟩, hyS⟩
  refine (hside φ φ.injective fun y hyS hyr hne ↦ ?_).elim
  exact (lt_or_gt_of_ne hne).resolve_left fun h ↦ hL ⟨y, ⟨hyr, h⟩, hyS⟩


end TauCeti

open TauCeti in
/-- **Brown's Theorem 0, for one inverse set.** Let `E` and `F` be finite-dimensional real normed
spaces of the same dimension, and let `f : E → F` be continuous on an open set `U` and injective
on `U` away from the fibre `U ∩ f ⁻¹' {p}`. If this fibre is compact, then `f` maps `U` onto an
open set. For an empty fibre this is invariance of domain,
`IsOpen.image_of_continuousOn_of_injOn`. -/
theorem IsOpen.image_of_continuousOn_of_injOn_sdiff {U : Set E} (hU : IsOpen U)
    (hf : ContinuousOn f U) (hinj : InjOn f (U \ f ⁻¹' {p})) (hM : IsCompact (U ∩ f ⁻¹' {p}))
    (hEF : finrank ℝ E = finrank ℝ F) : IsOpen (f '' U) := by
  -- Away from `p`, this is invariance of domain on `V \ f ⁻¹' {p}` for open `V ⊆ U`.
  have hVo {V : Set E} (hV : IsOpen V) (hVU : V ⊆ U) : IsOpen (f '' (V \ f ⁻¹' {p})) := by
    have hV' : IsOpen (V \ f ⁻¹' {p}) :=
      (hf.mono hVU).isOpen_inter_preimage hV isOpen_compl_singleton
    exact hV'.image_of_continuousOn_of_injOn (hf.mono (sdiff_subset.trans hVU))
      (hinj.mono (sdiff_subset_sdiff_left hVU)) hEF
  refine isOpen_iff_mem_nhds.2 ?_
  rintro _ ⟨x, hxU, rfl⟩
  by_cases hxp : f x = p
  swap
  · exact mem_of_superset ((hVo hU subset_rfl).mem_nhds ⟨x, ⟨hxU, hxp⟩, rfl⟩)
      (image_mono sdiff_subset)
  rw [hxp]
  rcases Nat.lt_or_ge (finrank ℝ F) 1 with h0 | h1
  · -- In dimension zero every subset of `F` is open.
    have : Subsingleton F := finrank_zero_iff (R := ℝ).1 (by omega)
    exact univ_mem' fun y ↦ ⟨x, hxU, Subsingleton.elim _ _⟩
  have : Nontrivial E := finrank_pos_iff (R := ℝ).1 (by omega)
  set M := U ∩ f ⁻¹' {p}
  have hne : M.Nonempty := ⟨x, hxU, hxp⟩
  -- A compact neighbourhood `K ⊆ U` of `M`, with interior `V`.
  obtain ⟨K, hK, hMK, hKU⟩ := exists_compact_between hM hU inter_subset_left
  set V := interior K
  have hVU : V ⊆ U := interior_subset.trans hKU
  have hVM : V ∩ f ⁻¹' {p} = M :=
    Subset.antisymm (fun z hz ↦ ⟨hVU hz.1, hz.2⟩) (subset_inter hMK inter_subset_right)
  set S := f '' (V \ f ⁻¹' {p})
  have hS : IsOpen S := hVo isOpen_interior hVU
  have hpS : p ∉ S := fun ⟨z, hz, hzp⟩ ↦ hz.2 hzp
  -- A ball around `p` misses the image of `K \ V`.
  have hKV : IsCompact (f '' (K \ V)) :=
    (hK.diff isOpen_interior).image_of_continuousOn (hf.mono (sdiff_subset.trans hKU))
  obtain ⟨r, hr, hrK⟩ := Metric.isOpen_iff.1 hKV.isClosed.isOpen_compl p fun ⟨z, hz, hzp⟩ ↦
    hz.2 (hMK ⟨hKU hz.1, hzp⟩)
  -- Within that ball, `S` is relatively closed in the punctured ball.
  have hSball (y : F) (hy : y ∈ ball p r) (hyc : y ∈ closure S) (hyp : y ≠ p) : y ∈ S := by
    obtain ⟨z, hz, rfl⟩ := closure_minimal (image_mono (sdiff_subset.trans interior_subset))
      (hK.image_of_continuousOn (hf.mono hKU)).isClosed hyc
    have hzV : z ∈ V := by
      by_contra hzV
      exact hrK hy ⟨z, ⟨hz, hzV⟩, rfl⟩
    exact ⟨z, ⟨hzV, hyp⟩, rfl⟩
  have hconn (T : Set F) (hT : T ⊆ ball p r \ {p}) (hTc : IsPreconnected T)
      (hTS : (T ∩ S).Nonempty) : T ⊆ S :=
    hTc.subset_of_closure_inter_subset hS hTS fun y hy ↦
      hSball y (hT hy.2).1 hy.1 (hT hy.2).2
  -- `S` accumulates at `p`: the nonempty compact set `M` is not all of `E`, so it has a frontier
  -- point, which is a limit of points of `V \ M`.
  have hpcl : p ∈ closure S := by
    obtain ⟨m, hm⟩ := nonempty_frontier_iff.2 ⟨hne, fun h ↦ noncompact_univ E (h ▸ hM)⟩
    rw [frontier_eq_closure_inter_closure, hM.isClosed.closure_eq] at hm
    have hmV : m ∈ closure (V \ f ⁻¹' {p}) :=
      closure_mono (t := V \ f ⁻¹' {p})
        (fun z (hz : z ∈ V ∩ Mᶜ) ↦ ⟨hz.1, fun hzp ↦ hz.2 ⟨hVU hz.1, hzp⟩⟩)
        (isOpen_interior.inter_closure ⟨hMK hm.1, hm.2⟩)
    have := (hf.continuousAt (hU.mem_nhds hm.1.1)).continuousWithinAt.mem_closure_image hmV
    rwa [mem_singleton_iff.1 hm.1.2] at this
  suffices hsub : ball p r \ {p} ⊆ S by
    refine mem_of_superset (ball_mem_nhds p hr) fun y hy ↦ ?_
    rcases eq_or_ne y p with rfl | hyp
    · exact ⟨x, hxU, hxp⟩
    · obtain ⟨z, hz, rfl⟩ := hsub ⟨hy, hyp⟩
      exact ⟨z, hVU hz.1, rfl⟩
  rcases h1.eq_or_lt with h1 | h2
  · exact ball_sdiff_singleton_subset_of_finrank_eq_one hEF h1.symm isOpen_interior
      (hf.mono hVU) (hinj.mono (sdiff_subset_sdiff_left hVU)) (by rwa [hVM]) (by rwa [hVM]) hr
      hconn
  · -- In dimension at least two, the punctured ball is connected.
    refine hconn _ subset_rfl (isConnected_ball_sdiff_singleton ?_ p hr).isPreconnected ?_
    · rw [← finrank_eq_rank]
      exact_mod_cast h2
    obtain ⟨y, hyS, hy⟩ := Metric.mem_closure_iff.1 hpcl r hr
    exact ⟨y, ⟨by rwa [mem_ball, dist_comm], fun h ↦ hpS (h ▸ hyS)⟩, hyS⟩

namespace TauCeti

/-- **Cell neighbourhoods of the only inverse set.** Let `E` and `F` be finite-dimensional real
normed spaces of the same dimension and `f : E → F` a map continuous on the closed unit ball,
injective on it away from the nonempty fibre `M = closedBall 0 1 ∩ f ⁻¹' {p}`, which lies in the
open unit ball. Then every open `U ⊇ M` contains a closed cell, the image of the closed unit ball
under a map `g` continuous and injective on it, whose open cell contains `M` in its interior. -/
theorem exists_continuousOn_injOn_image_closedBall_subset_of_injOn_closedBall_sdiff
    (hEF : finrank ℝ E = finrank ℝ F) (hf : ContinuousOn f (closedBall 0 1))
    (hinj : InjOn f (closedBall 0 1 \ f ⁻¹' {p})) (hM : closedBall 0 1 ∩ f ⁻¹' {p} ⊆ ball 0 1)
    (hp : p ∈ f '' closedBall 0 1) {U : Set E} (hU : IsOpen U)
    (hMU : closedBall 0 1 ∩ f ⁻¹' {p} ⊆ U) :
    ∃ g : E → E, ContinuousOn g (closedBall 0 1) ∧ InjOn g (closedBall 0 1) ∧
      closedBall 0 1 ∩ f ⁻¹' {p} ⊆ interior (g '' ball 0 1) ∧ g '' closedBall 0 1 ⊆ U := by
  /- The map is `g = f⁻¹ ∘ h ∘ f` away from `M` and the identity on `M`, where `h` is a
  homeomorphism of `F` fixing a neighbourhood of `p` and pulling `f '' closedBall 0 1` into
  `f '' (U ∩ ball 0 1)`, which is open by Brown's Theorem 0. Then `g` is continuous and injective
  on the closed ball and maps it into `U`, by
  `ContinuousOn.exists_continuousOn_injOn_mapsTo_of_mapsTo_image`, and it is the identity near
  `M`. -/
  set B := closedBall (0 : E) 1
  set M := B ∩ f ⁻¹' {p}
  have hUB : U ∩ ball 0 1 ⊆ B := inter_subset_right.trans ball_subset_closedBall
  have hUM : (U ∩ ball 0 1) ∩ f ⁻¹' {p} = M :=
    Subset.antisymm (fun z hz ↦ ⟨hUB hz.1, hz.2⟩) fun z hz ↦ ⟨⟨hMU hz, hM hz⟩, hz.2⟩
  have hMc : IsCompact M := (isCompact_closedBall 0 1).of_isClosed_subset
    (hf.preimage_isClosed_of_isClosed isClosed_closedBall isClosed_singleton) inter_subset_left
  -- A ball `ball p ε` lies in the image of `U ∩ ball 0 1`, which is open by Theorem 0.
  obtain ⟨ε, hε, hεU⟩ := Metric.isOpen_iff.1
    ((hU.inter isOpen_ball).image_of_continuousOn_of_injOn_sdiff (hf.mono hUB)
      (hinj.mono (sdiff_subset_sdiff_left hUB)) (by rwa [hUM]) hEF) p
    (by obtain ⟨m, hmB, hmp⟩ := hp; exact ⟨m, ⟨hMU ⟨hmB, hmp⟩, hM ⟨hmB, hmp⟩⟩, hmp⟩)
  -- The homeomorphism `h` of `F` fixing `closedBall p (ε / 2)` and pulling `f '' B` into
  -- `ball p ε`.
  obtain ⟨R, hR⟩ := ((isCompact_closedBall (0 : E) 1).image_of_continuousOn hf).isBounded
    |>.subset_closedBall p
  have hε34 : ε / 2 < 3 * ε / 4 := by linarith
  obtain ⟨ρ, hρ_fix, hρ_maps⟩ := exists_homeomorph_eqOn_closedBall_mapsTo_closedBall (E := F)
    (r := R) (half_pos hε).le hε34
  set h : F ≃ₜ F := (Homeomorph.subRight p).trans (ρ.trans (Homeomorph.addRight p))
  have hh_fix : EqOn h id (closedBall p (ε / 2)) := fun y hy ↦ by
    have hy' : y - p ∈ closedBall (0 : F) (ε / 2) := by
      rwa [mem_closedBall_zero_iff, ← mem_closedBall_iff_norm]
    simp [h, hρ_fix hy']
  have hh_maps : MapsTo h (closedBall p R) (ball p ε) := fun y hy ↦ by
    have hyR : y - p ∈ closedBall (0 : F) R := by
      rwa [mem_closedBall_zero_iff, ← mem_closedBall_iff_norm]
    have hy' := hρ_maps hyR
    rw [mem_closedBall_zero_iff] at hy'
    rw [mem_ball_iff_norm]
    simp only [h, Homeomorph.trans_apply, Homeomorph.coe_subRight, Homeomorph.coe_addRight,
      add_sub_cancel_right]
    linarith
  have hh_mapsU : MapsTo h (f '' B) (f '' (B ∩ (U ∩ ball 0 1))) := by
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨u, hu, hfu⟩ := hεU (hh_maps (hR ⟨x, hx, rfl⟩))
    exact ⟨u, ⟨ball_subset_closedBall hu.2, hu⟩, hfu⟩
  obtain ⟨g, hgc, hgi, hgU, -, hg_id⟩ := hf.exists_continuousOn_injOn_mapsTo_of_mapsTo_image
    (isCompact_closedBall 0 1) hinj (subset_inter hMU hM) h.continuous.continuousOn
    h.injective.injOn
    (eventuallyEq_of_mem (mem_nhdsWithin_of_mem_nhds (closedBall_mem_nhds p (half_pos hε)))
      hh_fix) hh_mapsU
  refine ⟨g, hgc, hgi, ?_, hgU.image_subset.trans (inter_subset_right.trans inter_subset_left)⟩
  -- `g` is the identity on the open neighbourhood `ball 0 1 ∩ f ⁻¹' ball p (ε / 2)` of `M`.
  have hNo : IsOpen (ball (0 : E) 1 ∩ f ⁻¹' ball p (ε / 2)) :=
    (hf.mono ball_subset_closedBall).isOpen_inter_preimage isOpen_ball isOpen_ball
  have hMN : M ⊆ ball (0 : E) 1 ∩ f ⁻¹' ball p (ε / 2) := fun m hm ↦
    ⟨hM hm, by rw [mem_preimage, mem_singleton_iff.1 hm.2]; exact mem_ball_self (by positivity)⟩
  have hNg : ball (0 : E) 1 ∩ f ⁻¹' ball p (ε / 2) ⊆ g '' ball 0 1 := fun y hy ↦
    ⟨y, hy.1, hg_id y (ball_subset_closedBall hy.1) (hh_fix (ball_subset_closedBall hy.2))⟩
  exact hMN.trans (interior_maximal hNg hNo)

/-- **Brown's Theorem 3: the only inverse set of a map of a cell is cellular.** Let `E` and `F`
be finite-dimensional real normed spaces of the same dimension and `f : E → F` a map continuous on
the closed unit ball, injective on it away from the nonempty fibre
`M = closedBall 0 1 ∩ f ⁻¹' {p}`, which lies in the open unit ball. Then `M` is cellular. -/
theorem isCellularSet_closedBall_inter_preimage_of_finrank_eq (hEF : finrank ℝ E = finrank ℝ F)
    (hf : ContinuousOn f (closedBall 0 1)) (hinj : InjOn f (closedBall 0 1 \ f ⁻¹' {p}))
    (hM : closedBall 0 1 ∩ f ⁻¹' {p} ⊆ ball 0 1) (hp : p ∈ f '' closedBall 0 1) :
    IsCellularSet E (closedBall (0 : E) 1 ∩ f ⁻¹' {p}) :=
  isCellularSet_of_forall_isOpen
    (hf.preimage_isClosed_of_isClosed isClosed_closedBall isClosed_singleton) fun _ hU hMU ↦
      exists_continuousOn_injOn_image_closedBall_subset_of_injOn_closedBall_sdiff hEF hf hinj hM
        hp hU hMU

end TauCeti

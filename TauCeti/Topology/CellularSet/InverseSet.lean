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

/-!
# The inverse set of a map of a cell is cellular

Let `E` and `F` be finite-dimensional real normed spaces of the same dimension, and let
`f : E → F` be continuous on the closed unit ball `B` of `E`. Suppose that `f` is injective on `B`
away from the fibre `M = B ∩ f⁻¹{p}` of a single point `p`, and that `M` lies in the open unit
ball. In M. Brown's language, `M` is the only inverse set of the map `f` of the cell `B`.

The first result is the one-inverse-set case of Brown's Theorem 0: `f` maps every open set `U`
with `M ⊆ U ⊆ ball 0 1` onto an open subset of `F`
(`TauCeti.isOpen_image_of_injOn_closedBall_diff`). Away from `p` this is Brouwer's invariance of
domain, applied to `U \ M`. At `p`, a small ball `ball p r` around `p` misses the image of
`B \ U`, so within it the image of `U \ M` is relatively closed in the punctured ball and open.
In dimension at least two the punctured ball is connected, and the image of `U \ M` accumulates
at `p`, so it fills the punctured ball. In dimension one the punctured ball has two sides; if
the image of `U \ M` filled only one, then the segments leaving `M` in the two directions of `E`
would cross the same values near `p`, contradicting injectivity.

The second result is Brown's Theorem 3: `M` is cellular
(`TauCeti.isCellularSet_of_injOn_closedBall_diff`). Given an open `U ⊇ M`, choose a
homeomorphism `h` of `F` which fixes a neighbourhood of `p` and pulls the compact set `f '' B`
into the open set `f '' (U ∩ ball 0 1)`. Then `g = f⁻¹ ∘ h ∘ f` on `B \ M`, extended by the
identity on `M`, is a continuous injection of `B` into `U` which is the identity near `M`, so its
image is a closed cell in `U` with `M` in its interior
(`TauCeti.exists_cell_subset_of_injOn_closedBall_diff`).

These are steps in Brown's proof of the generalized Schoenflies theorem. There, the map of the
sphere `Sⁿ` collapsing the two outer pieces of a bicollar has exactly two inverse sets, and
Theorem 4 applies Theorem 3 to recognize both of them as cellular.

## Main results

* `TauCeti.isOpen_image_of_injOn_closedBall_diff`: the image of an open neighbourhood of the only
  inverse set is open (Brown's Theorem 0 for one inverse set).
* `TauCeti.exists_cell_subset_of_injOn_closedBall_diff`: every neighbourhood of the only inverse
  set contains a closed cell with the inverse set in its interior.
* `TauCeti.isCellularSet_of_injOn_closedBall_diff`: the only inverse set is cellular (Brown's
  Theorem 3).

## References

* M. Brown, *A proof of the generalized Schoenflies theorem*, Bull. Amer. Math. Soc. 66 (1960),
  74–76, Theorems 0 and 3.
-/

public section

open Set Metric Filter Topology Function Module

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F] {f : E → F} {p : F}

namespace TauCeti

omit [NormedSpace ℝ F] [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
/-- If the fibre `M = closedBall 0 1 ∩ f ⁻¹' {p}` of a map continuous on the closed unit ball is
nonempty and lies in the open unit ball, then some point of `M` is a limit of points of the open
unit ball outside `M`: otherwise `M` would be clopen in the connected open ball, so `f` would be
constant on the closed ball and `M` would contain the unit sphere. -/
private theorem exists_mem_closure_ball_diff [Nontrivial E] (hf : ContinuousOn f (closedBall 0 1))
    (hM : closedBall 0 1 ∩ f ⁻¹' {p} ⊆ ball 0 1)
    (hne : (closedBall (0 : E) 1 ∩ f ⁻¹' {p}).Nonempty) :
    ∃ m ∈ closedBall (0 : E) 1 ∩ f ⁻¹' {p},
      m ∈ closure (ball 0 1 \ (closedBall 0 1 ∩ f ⁻¹' {p})) := by
  set M := closedBall (0 : E) 1 ∩ f ⁻¹' {p}
  by_contra! hcon
  have hMopen : IsOpen M := by
    refine isOpen_iff_mem_nhds.2 fun m hm ↦ ?_
    filter_upwards [isClosed_closure.isOpen_compl.mem_nhds (hcon m hm),
      isOpen_ball.mem_nhds (hM hm)] with y hy hyb
    by_contra hyM
    exact hy (subset_closure ⟨hyb, hyM⟩)
  have hMclosed : IsClosed M := hf.preimage_isClosed_of_isClosed isClosed_closedBall
    isClosed_singleton
  obtain ⟨m, hm⟩ := hne
  have hball : ball (0 : E) 1 ⊆ M :=
    (convex_ball 0 1).isPreconnected.subset_isClopen ⟨hMclosed, hMopen⟩ ⟨m, hM hm, hm⟩
  -- So `f = p` on the open ball, hence on the closed ball, which then lies in `M`.
  have heq : EqOn f (fun _ ↦ p) (closedBall 0 1) :=
    EqOn.of_subset_closure (fun x hx ↦ (hball hx).2) hf continuousOn_const ball_subset_closedBall
      (closure_ball (0 : E) one_ne_zero).symm.subset
  obtain ⟨x, hx⟩ := (NormedSpace.sphere_nonempty (x := (0 : E))).2 zero_le_one
  have hxM := hM ⟨sphere_subset_closedBall hx, heq (sphere_subset_closedBall hx)⟩
  rw [mem_ball, mem_sphere.1 hx] at hxM
  exact lt_irrefl _ hxM

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
/-- Let `m ∈ U ⊆ ball 0 1` with `f m = p`, and leave `m` along a direction `w` on which `φ ∘ f`
exceeds `φ p` at every positive time with `m + s • w ∈ U` and `f (m + s • w)` near `p`. Then for
some `t > 0` the segment from `m` to `m + t • w` stays in `U`, and the values of `φ ∘ f` on it
cover the interval `Ioc (φ p) (φ (f (m + t • w)))` at positive times. -/
private theorem exists_segment_Ioc_subset (hf : ContinuousOn f (closedBall 0 1)) {U : Set E}
    (hU : IsOpen U) (hUb : U ⊆ ball 0 1) {m : E} (hmU : m ∈ U) (hfm : f m = p) (w : E)
    (φ : F →L[ℝ] ℝ) {r : ℝ} (hr : 0 < r)
    (hlt : ∀ s : ℝ, 0 < s → m + s • w ∈ U → f (m + s • w) ∈ ball p r → φ p < φ (f (m + s • w))) :
    ∃ t : ℝ, 0 < t ∧ (∀ s ∈ Icc 0 t, m + s • w ∈ U) ∧ φ p < φ (f (m + t • w)) ∧
      ∀ v ∈ Ioc (φ p) (φ (f (m + t • w))), ∃ s ∈ Ioc 0 t, φ (f (m + s • w)) = v := by
  have hfc : ContinuousAt f m :=
    hf.continuousAt (mem_of_superset (isOpen_ball.mem_nhds (hUb hmU)) ball_subset_closedBall)
  have hN : U ∩ f ⁻¹' ball p r ∈ 𝓝 m :=
    inter_mem (hU.mem_nhds hmU) (hfc.preimage_mem_nhds (hfm ▸ ball_mem_nhds (f m) hr))
  have hγ : Tendsto (fun s : ℝ ↦ m + s • w) (𝓝 0) (𝓝 m) := by
    have : Continuous fun s : ℝ ↦ m + s • w := by fun_prop
    simpa using this.tendsto 0
  obtain ⟨δ, hδ, hδN⟩ := Metric.mem_nhds_iff.1 (hγ hN)
  have hmem (s : ℝ) (hs : s ∈ Icc 0 (δ / 2)) : m + s • w ∈ U ∧ f (m + s • w) ∈ ball p r :=
    hδN (by rw [mem_ball, Real.dist_0_eq_abs, abs_of_nonneg hs.1]; linarith [hs.2])
  have hcont : ContinuousOn (fun s : ℝ ↦ φ (f (m + s • w))) (Icc 0 (δ / 2)) :=
    φ.continuous.comp_continuousOn (hf.comp (by fun_prop) fun s hs ↦
      ball_subset_closedBall (hUb (hmem s hs).1))
  refine ⟨δ / 2, half_pos hδ, fun s hs ↦ (hmem s hs).1,
    hlt _ (half_pos hδ) (hmem _ ⟨(half_pos hδ).le, le_rfl⟩).1 (hmem _ ⟨(half_pos hδ).le, le_rfl⟩).2,
    fun v hv ↦ ?_⟩
  -- The intermediate value theorem on `[0, δ / 2]`; the value `v > φ p` is not taken at `0`.
  obtain ⟨s, hs, hsv⟩ := intermediate_value_Icc (half_pos hδ).le hcont
    ⟨by simpa [hfm] using hv.1.le, hv.2⟩
  refine ⟨s, ⟨lt_of_le_of_ne hs.1 fun h ↦ ?_, hs.2⟩, hsv⟩
  subst h
  simp only [zero_smul, add_zero, hfm] at hsv
  exact hv.1.ne hsv

omit [FiniteDimensional ℝ F] in
/-- **The one-dimensional case of Brown's Theorem 0.** Let `M = closedBall 0 1 ∩ f ⁻¹' {p}` be a
nonempty fibre inside an open set `U ⊆ ball 0 1`, with `f` injective on the closed ball away from
`M`, and let `φ` be an injective linear form on `F`. Then the points of `U \ M` sent near `p` cannot
all have `φ`-value above `φ p`: the segments leaving `M` from its two extreme points along a linear
form `ψ` on `E` would reach the same `φ`-value at two distinct points. -/
private theorem false_of_forall_lt (hf : ContinuousOn f (closedBall 0 1))
    (hinj : InjOn f (closedBall 0 1 \ f ⁻¹' {p})) {U : Set E} (hU : IsOpen U)
    (hMU : closedBall 0 1 ∩ f ⁻¹' {p} ⊆ U) (hUb : U ⊆ ball 0 1)
    (hne : (closedBall (0 : E) 1 ∩ f ⁻¹' {p}).Nonempty) {ψ : E →L[ℝ] ℝ} {v₀ : E} (hv₀ : ψ v₀ = 1)
    {φ : F →L[ℝ] ℝ} (hφ : Injective φ) {r : ℝ} (hr : 0 < r)
    (hlt : ∀ y ∈ U \ (closedBall 0 1 ∩ f ⁻¹' {p}), f y ∈ ball p r → φ p < φ (f y)) : False := by
  set M := closedBall (0 : E) 1 ∩ f ⁻¹' {p}
  have hUB : U ⊆ closedBall 0 1 := hUb.trans ball_subset_closedBall
  have hMc : IsCompact M := (isCompact_closedBall 0 1).of_isClosed_subset
    (hf.preimage_isClosed_of_isClosed isClosed_closedBall isClosed_singleton) inter_subset_left
  -- The two extreme points of `M` for `ψ`, and the segments leaving `M` from them.
  obtain ⟨m₁, hm₁, hmin⟩ := hMc.exists_isMinOn hne ψ.continuous.continuousOn
  obtain ⟨m₂, hm₂, hmax⟩ := hMc.exists_isMaxOn hne ψ.continuous.continuousOn
  have hψ₁ (s : ℝ) : ψ (m₁ + s • -v₀) = ψ m₁ - s := by simp [hv₀, sub_eq_add_neg]
  have hψ₂ (s : ℝ) : ψ (m₂ + s • v₀) = ψ m₂ + s := by simp [hv₀]
  obtain ⟨t₁, -, hU₁, hlt₁, hivt₁⟩ := exists_segment_Ioc_subset hf hU hUb (hMU hm₁) hm₁.2 (-v₀)
    φ hr fun s hs hsU hsr ↦ hlt _ ⟨hsU, fun hsM ↦ by
      have := isMinOn_iff.1 hmin _ hsM
      rw [hψ₁] at this
      linarith⟩ hsr
  obtain ⟨t₂, -, hU₂, hlt₂, hivt₂⟩ := exists_segment_Ioc_subset hf hU hUb (hMU hm₂) hm₂.2 v₀
    φ hr fun s hs hsU hsr ↦ hlt _ ⟨hsU, fun hsM ↦ by
      have := isMaxOn_iff.1 hmax _ hsM
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
  have hout (y : E) (hyU : y ∈ U) (hy : φ (f y) = v) : y ∈ closedBall 0 1 \ f ⁻¹' {p} :=
    ⟨hUB hyU, fun hyp ↦ (lt_min hlt₁ hlt₂).ne ((congrArg φ (show f y = p from hyp)).symm.trans hy)⟩
  exact hne₁₂ (hinj (hout _ (hU₁ s₁ (Ioc_subset_Icc_self hs₁)) hv₁)
    (hout _ (hU₂ s₂ (Ioc_subset_Icc_self hs₂)) hv₂) (hφ (hv₁.trans hv₂.symm)))

/-- **Brown's Theorem 0 in dimension one, near `p`.** In the setting of
`TauCeti.isOpen_image_of_injOn_closedBall_diff` with `dim E = dim F = 1`, suppose that every
preconnected subset of the punctured ball `ball p r \ {p}` meeting `S = f '' (U \ M)` lies in `S`.
Then `S` fills the punctured ball: both of its sides `{φ < φ p}` and `{φ > φ p}`, for a linear
isomorphism `φ : F ≃ ℝ`, meet `S` by `TauCeti.false_of_forall_lt`. -/
private theorem ball_sdiff_singleton_subset_of_finrank_eq_one (hEF : finrank ℝ E = finrank ℝ F)
    (h1 : finrank ℝ F = 1) (hf : ContinuousOn f (closedBall 0 1))
    (hinj : InjOn f (closedBall 0 1 \ f ⁻¹' {p})) {U : Set E} (hU : IsOpen U)
    (hMU : closedBall 0 1 ∩ f ⁻¹' {p} ⊆ U) (hUb : U ⊆ ball 0 1)
    (hne : (closedBall (0 : E) 1 ∩ f ⁻¹' {p}).Nonempty) {r : ℝ} (hr : 0 < r)
    (hconn : ∀ T ⊆ ball p r \ {p}, IsPreconnected T →
      (T ∩ f '' (U \ (closedBall 0 1 ∩ f ⁻¹' {p}))).Nonempty →
        T ⊆ f '' (U \ (closedBall 0 1 ∩ f ⁻¹' {p}))) :
    ball p r \ {p} ⊆ f '' (U \ (closedBall 0 1 ∩ f ⁻¹' {p})) := by
  set S := f '' (U \ (closedBall 0 1 ∩ f ⁻¹' {p}))
  have hpS : p ∉ S := by
    rintro ⟨z, hz, hzp⟩
    exact hz.2 ⟨ball_subset_closedBall (hUb hz.1), hzp⟩
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
    false_of_forall_lt hf hinj hU hMU hUb hne hψ hφ' hr fun y hy hyr ↦
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

/-- **Brown's Theorem 0, for one inverse set.** Let `E` and `F` be finite-dimensional real normed
spaces of the same dimension and `f : E → F` a map continuous on the closed unit ball, injective on
it away from the fibre `M = closedBall 0 1 ∩ f ⁻¹' {p}`. Then `f` maps every open set `U` with
`M ⊆ U ⊆ ball 0 1` onto an open set. -/
theorem isOpen_image_of_injOn_closedBall_diff (hEF : finrank ℝ E = finrank ℝ F)
    (hf : ContinuousOn f (closedBall 0 1)) (hinj : InjOn f (closedBall 0 1 \ f ⁻¹' {p}))
    {U : Set E} (hU : IsOpen U) (hMU : closedBall 0 1 ∩ f ⁻¹' {p} ⊆ U) (hUb : U ⊆ ball 0 1) :
    IsOpen (f '' U) := by
  set M := closedBall (0 : E) 1 ∩ f ⁻¹' {p}
  have hUB : U ⊆ closedBall 0 1 := hUb.trans ball_subset_closedBall
  have hMc : IsClosed M := hf.preimage_isClosed_of_isClosed isClosed_closedBall isClosed_singleton
  -- Away from `p`, this is invariance of domain on `U \ M`.
  set S := f '' (U \ M)
  have hS : IsOpen S := (hU.sdiff hMc).image_of_continuousOn_of_injOn
    (hf.mono (sdiff_subset.trans hUB))
    (hinj.mono fun x (hx : x ∈ U \ M) ↦
      (⟨hUB hx.1, fun hfx ↦ hx.2 ⟨hUB hx.1, hfx⟩⟩ : x ∈ closedBall 0 1 \ f ⁻¹' {p})) hEF
  have hpS : p ∉ S := by
    rintro ⟨z, hz, hzp⟩
    exact hz.2 ⟨hUB hz.1, hzp⟩
  rcases M.eq_empty_or_nonempty with hMe | hne
  · simpa [S, hMe] using hS
  refine isOpen_iff_mem_nhds.2 ?_
  rintro _ ⟨x, hxU, rfl⟩
  by_cases hx : x ∈ M
  swap
  · exact mem_of_superset (hS.mem_nhds ⟨x, ⟨hxU, hx⟩, rfl⟩) (image_mono sdiff_subset)
  have hfx : f x = p := hx.2
  rw [hfx]
  rcases Nat.lt_or_ge (finrank ℝ F) 1 with h0 | h1
  · -- In dimension zero every subset of `F` is open.
    have : Subsingleton F := finrank_zero_iff (R := ℝ).1 (by omega)
    exact univ_mem' fun y ↦ ⟨x, hxU, Subsingleton.elim _ _⟩
  have : Nontrivial E := finrank_pos_iff (R := ℝ).1 (by omega)
  -- A ball around `p` misses the image of `closedBall 0 1 \ U`.
  have hK : IsCompact (f '' (closedBall 0 1 \ U)) :=
    ((isCompact_closedBall 0 1).diff hU).image_of_continuousOn (hf.mono sdiff_subset)
  obtain ⟨r, hr, hrK⟩ := Metric.isOpen_iff.1 hK.isClosed.isOpen_compl p fun ⟨z, hz, hzp⟩ ↦
    hz.2 (hMU ⟨hz.1, hzp⟩)
  -- Within that ball, `S` is relatively closed in the punctured ball.
  have hSball (y : F) (hy : y ∈ ball p r) (hyc : y ∈ closure S) (hyp : y ≠ p) : y ∈ S := by
    obtain ⟨z, hz, rfl⟩ := closure_minimal (image_mono (sdiff_subset.trans hUB))
      ((isCompact_closedBall 0 1).image_of_continuousOn hf).isClosed hyc
    have hzU : z ∈ U := by
      by_contra hzU
      exact hrK hy ⟨z, ⟨hz, hzU⟩, rfl⟩
    exact ⟨z, ⟨hzU, fun hzM ↦ hyp hzM.2⟩, rfl⟩
  have hconn (T : Set F) (hT : T ⊆ ball p r \ {p}) (hTc : IsPreconnected T)
      (hTS : (T ∩ S).Nonempty) : T ⊆ S :=
    hTc.subset_of_closure_inter_subset hS hTS fun y hy ↦
      hSball y (hT hy.2).1 hy.1 (hT hy.2).2
  -- `S` accumulates at `p`, because `M` has a point in the closure of `U \ M`.
  have hpcl : p ∈ closure S := by
    obtain ⟨m, hm, hmc⟩ := exists_mem_closure_ball_diff hf (hMU.trans hUb) hne
    have hmU : m ∈ closure (U \ M) := by
      rw [mem_closure_iff_nhds] at hmc ⊢
      intro t ht
      obtain ⟨y, hyt, -, hyM⟩ := hmc (t ∩ U) (inter_mem ht (hU.mem_nhds (hMU hm)))
      exact ⟨y, hyt.1, hyt.2, hyM⟩
    have := ((hf m hm.1).mono (sdiff_subset.trans hUB)).mem_closure_image hmU
    rwa [show f m = p from hm.2] at this
  have hSnear (ε : ℝ) (hε : 0 < ε) : ∃ y ∈ S, y ∈ ball p ε := by
    obtain ⟨y, hyS, hy⟩ := Metric.mem_closure_iff.1 hpcl ε hε
    exact ⟨y, hyS, by rwa [mem_ball, dist_comm]⟩
  suffices hsub : ball p r \ {p} ⊆ S by
    refine mem_of_superset (ball_mem_nhds p hr) fun y hy ↦ ?_
    rcases eq_or_ne y p with rfl | hyp
    · exact ⟨x, hxU, hfx⟩
    · exact image_mono sdiff_subset (hsub ⟨hy, hyp⟩)
  rcases h1.eq_or_lt with h1 | h2
  · exact ball_sdiff_singleton_subset_of_finrank_eq_one hEF h1.symm hf hinj hU hMU hUb hne hr
      hconn
  · -- In dimension at least two, the punctured ball is connected.
    refine hconn _ subset_rfl (isConnected_ball_sdiff_singleton ?_ p hr).isPreconnected ?_
    · rw [← finrank_eq_rank]
      exact_mod_cast h2
    obtain ⟨y, hyS, hy⟩ := hSnear r hr
    exact ⟨y, ⟨hy, fun h ↦ hpS (h ▸ hyS)⟩, hyS⟩

/-- **Cell neighbourhoods of the only inverse set.** Let `E` and `F` be finite-dimensional real
normed spaces of the same dimension and `f : E → F` a map continuous on the closed unit ball,
injective on it away from the nonempty fibre `M = closedBall 0 1 ∩ f ⁻¹' {p}`, which lies in the
open unit ball. Then every open `U ⊇ M` contains a closed cell, the image of the closed unit ball
under a map `g` continuous and injective on it, whose open cell contains `M` in its interior. -/
theorem exists_cell_subset_of_injOn_closedBall_diff (hEF : finrank ℝ E = finrank ℝ F)
    (hf : ContinuousOn f (closedBall 0 1)) (hinj : InjOn f (closedBall 0 1 \ f ⁻¹' {p}))
    (hM : closedBall 0 1 ∩ f ⁻¹' {p} ⊆ ball 0 1) (hp : p ∈ f '' closedBall 0 1) {U : Set E}
    (hU : IsOpen U) (hMU : closedBall 0 1 ∩ f ⁻¹' {p} ⊆ U) :
    ∃ g : E → E, ContinuousOn g (closedBall 0 1) ∧ InjOn g (closedBall 0 1) ∧
      closedBall 0 1 ∩ f ⁻¹' {p} ⊆ interior (g '' ball 0 1) ∧ g '' closedBall 0 1 ⊆ U := by
  /- The map is `g = f⁻¹ ∘ h ∘ f` away from `M` and the identity on `M`, where `h` is a
  homeomorphism of `F` fixing a neighbourhood of `p` and pulling `f '' closedBall 0 1` into
  `f '' (U ∩ ball 0 1)`, which is open by Brown's Theorem 0. Then `g` is injective, maps the closed
  ball into `U`, and is the identity near `M`; it is continuous at the points of `M` because it is
  the identity near them, and elsewhere because `g x` is the unique point of the compact closed
  ball with `f (g x) = h (f x)`. -/
  classical
  set B := closedBall (0 : E) 1
  set M := B ∩ f ⁻¹' {p}
  -- A ball `ball p ε` lies in the image of `U ∩ ball 0 1`, which is open by Theorem 0.
  obtain ⟨ε, hε, hεU⟩ := Metric.isOpen_iff.1
    (isOpen_image_of_injOn_closedBall_diff hEF hf hinj (hU.inter isOpen_ball)
      (subset_inter hMU hM) inter_subset_right) p
    (by obtain ⟨m, hmB, hmp⟩ := hp; exact ⟨m, ⟨hMU ⟨hmB, hmp⟩, hM ⟨hmB, hmp⟩⟩, hmp⟩)
  -- The homeomorphism `h` of `F` fixing `closedBall p (ε / 2)` and pulling `f '' B` into
  -- `ball p ε`.
  obtain ⟨R, hR⟩ := ((isCompact_closedBall (0 : E) 1).image_of_continuousOn hf).isBounded
    |>.subset_closedBall p
  obtain ⟨h, hh_fix, hh_maps⟩ := exists_homeomorph_eqOn_closedBall_mapsTo_ball p R hε
  have hhp : h p = p := hh_fix (mem_closedBall_self (by positivity))
  have hh_ne (y : F) (hy : y ≠ p) : h y ≠ p := fun h' ↦ hy (h.injective (h'.trans hhp.symm))
  have hh_mapsU (x : E) (hx : x ∈ B) : h (f x) ∈ f '' (U ∩ ball 0 1) :=
    hεU (hh_maps (hR ⟨x, hx, rfl⟩))
  have hfp (x : E) (hx : x ∈ B) (hxM : x ∉ M) : f x ≠ p := fun hfx ↦ hxM ⟨hx, hfx⟩
  -- The map `g`: the identity on `M`, and the `f`-preimage of `h ∘ f` elsewhere.
  set g : E → E := fun x ↦ if x ∈ M then x else invFunOn f B (h (f x))
  have hgM (x : E) (hx : x ∈ M) : g x = x := by simp [g, hx]
  have hg_spec (x : E) (hx : x ∈ B) (hxM : x ∉ M) :
      g x ∈ U ∩ ball 0 1 ∧ f (g x) = h (f x) := by
    obtain ⟨u, hu, hfu⟩ := hh_mapsU x hx
    have hex : ∃ a ∈ B, f a = h (f x) := ⟨u, ball_subset_closedBall hu.2, hfu⟩
    have hgx : g x = invFunOn f B (h (f x)) := by simp [g, hxM]
    have hne : h (f x) ≠ p := hh_ne _ (hfp x hx hxM)
    have hfgx : f (g x) = h (f x) := hgx ▸ invFunOn_eq hex
    have hgu : g x = u := hinj ⟨hgx ▸ invFunOn_mem hex, fun hc ↦ hne (hfgx.symm.trans hc)⟩
      ⟨ball_subset_closedBall hu.2, fun hc ↦ hne (hfu.symm.trans hc)⟩ (hfgx.trans hfu.symm)
    exact ⟨hgu ▸ hu, hgu ▸ hfu⟩
  have hgB : MapsTo g B B := fun x hx ↦ by
    by_cases hxM : x ∈ M
    · rwa [hgM x hxM]
    · exact ball_subset_closedBall (hg_spec x hx hxM).1.2
  have hfg (x : E) (hx : x ∈ B) : f (g x) = h (f x) := by
    by_cases hxM : x ∈ M
    · rw [hgM x hxM, show f x = p from hxM.2, hhp]
    · exact (hg_spec x hx hxM).2
  -- Near `M`, where `h` is the identity, so is `g`.
  have hg_id (x : E) (hx : x ∈ B) (hxV : f x ∈ ball p (ε / 2)) : g x = x := by
    by_cases hxM : x ∈ M
    · exact hgM x hxM
    · refine hinj ⟨hgB hx, fun hgx ↦ hh_ne _ (hfp x hx hxM) ((hfg x hx).symm.trans hgx)⟩
        ⟨hx, hfp x hx hxM⟩ ?_
      rw [hfg x hx, hh_fix (ball_subset_closedBall hxV), id]
  refine ⟨g, fun x hx ↦ ?_, fun x hx y hy hxy ↦ ?_, ?_, ?_⟩
  · by_cases hxV : f x ∈ ball p (ε / 2)
    · refine continuousWithinAt_id.congr_of_eventuallyEq ?_ (hg_id x hx hxV)
      filter_upwards [self_mem_nhdsWithin, (hf x hx).preimage_mem_nhdsWithin
        (isOpen_ball.mem_nhds hxV)] with y hyB hyV
      exact hg_id y hyB hyV
    /- Away from `M`, `g y` is the unique point of the compact ball `B` with `f (g y) = h (f y)`,
    and this characterization passes to cluster points. -/
    have hxM : x ∉ M := fun hxM ↦ hxV (by rw [show f x = p from hxM.2]; exact mem_ball_self (by
      positivity))
    have hgBev : ∀ᶠ y in 𝓝[B] x, g y ∈ B := eventually_mem_nhdsWithin.mono fun y hy ↦ hgB hy
    refine (isCompact_closedBall 0 1).tendsto_nhds_of_unique_mapClusterPt hgBev
      fun z hz hcl ↦ ?_
    have ht : Tendsto (f ∘ g) (𝓝[B] x) (𝓝 (h (f x))) :=
      (h.continuous.continuousAt.tendsto.comp (hf x hx)).congr'
        (eventually_mem_nhdsWithin.mono fun y hy ↦ (hfg y hy).symm)
    have hcl' : MapClusterPt (f z) (𝓝[B] x) (f ∘ g) :=
      hcl.tendsto_comp' ((hf z hz).mono_left (inf_le_inf_left _ (tendsto_principal.2 hgBev)))
    have hfz : f z = h (f x) := eq_of_nhds_neBot (ClusterPt.mono hcl' ht)
    have hne : h (f x) ≠ p := hh_ne _ (hfp x hx hxM)
    exact hinj ⟨hz, fun hzp ↦ hne (hfz.symm.trans hzp)⟩
      ⟨hgB hx, fun hgp ↦ hne ((hfg x hx).symm.trans hgp)⟩ (hfz.trans (hfg x hx).symm)
  · have hfxy : f x = f y := h.injective (by rw [← hfg x hx, ← hfg y hy, hxy])
    by_cases hxM : x ∈ M
    · have hyM : y ∈ M := ⟨hy, show f y = p from hfxy ▸ hxM.2⟩
      rwa [hgM x hxM, hgM y hyM] at hxy
    · exact hinj ⟨hx, hfp x hx hxM⟩ ⟨hy, fun hyp ↦ hfp x hx hxM (hfxy.trans hyp)⟩ hfxy
  · -- `g` is the identity on the open neighbourhood `ball 0 1 ∩ f ⁻¹' ball p (ε / 2)` of `M`.
    have hNo : IsOpen (ball (0 : E) 1 ∩ f ⁻¹' ball p (ε / 2)) :=
      (hf.mono ball_subset_closedBall).isOpen_inter_preimage isOpen_ball isOpen_ball
    have hMN : M ⊆ ball (0 : E) 1 ∩ f ⁻¹' ball p (ε / 2) := fun m hm ↦
      ⟨hM hm, by rw [mem_preimage, show f m = p from hm.2]; exact mem_ball_self (by positivity)⟩
    have hNg : ball (0 : E) 1 ∩ f ⁻¹' ball p (ε / 2) ⊆ g '' ball 0 1 := fun y hy ↦
      ⟨y, hy.1, hg_id y (ball_subset_closedBall hy.1) hy.2⟩
    exact hMN.trans (interior_maximal hNg hNo)
  · rintro _ ⟨x, hx, rfl⟩
    by_cases hxM : x ∈ M
    · rw [hgM x hxM]
      exact hMU hxM
    · exact (hg_spec x hx hxM).1.1

/-- **Brown's Theorem 3: the only inverse set of a map of a cell is cellular.** Let `E` and `F`
be finite-dimensional real normed spaces of the same dimension and `f : E → F` a map continuous on
the closed unit ball, injective on it away from the nonempty fibre
`M = closedBall 0 1 ∩ f ⁻¹' {p}`, which lies in the open unit ball. Then `M` is cellular. -/
theorem isCellularSet_of_injOn_closedBall_diff (hEF : finrank ℝ E = finrank ℝ F)
    (hf : ContinuousOn f (closedBall 0 1)) (hinj : InjOn f (closedBall 0 1 \ f ⁻¹' {p}))
    (hM : closedBall 0 1 ∩ f ⁻¹' {p} ⊆ ball 0 1) (hp : p ∈ f '' closedBall 0 1) :
    IsCellularSet E (closedBall (0 : E) 1 ∩ f ⁻¹' {p}) :=
  isCellularSet_of_forall_isOpen
    (hf.preimage_isClosed_of_isClosed isClosed_closedBall isClosed_singleton)
    fun _ hU hMU ↦ exists_cell_subset_of_injOn_closedBall_diff hEF hf hinj hM hp hU hMU

end TauCeti

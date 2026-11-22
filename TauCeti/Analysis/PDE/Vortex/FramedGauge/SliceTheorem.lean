/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Vortex.FramedGauge.CoulombGauge
public import TauCeti.Analysis.PDE.Vortex.FramedGauge.Proper
public import TauCeti.Analysis.PDE.Vortex.FramedGauge.Slice
public import Mathlib.Topology.Algebra.ProperAction.Basic
public import TauCeti.Topology.Algebra.GroupAction.SliceChart
public import TauCeti.Topology.Algebra.ProperAction.TransverseSlice

/-!
# The proper action of the Sobolev gauge group and the Coulomb slice theorem

For an integer `k ≥ 3`, the Sobolev framed gauge group `G_(k+1)`
(`TauCeti.Vortex.SobolevTopologicalGaugeGroup`) acts freely and continuously on the continuous
fields of the affine space `A_m^k = x_m + H^k(ℂ; iT*ℂ ⊕ ℂ)` of framed degree-`m` plane vortex
fields (`TauCeti.Vortex.SobolevFieldSpace`), with quotient map
`π : A_m^k → A_m^k / G_(k+1)`. This file proves that the action is proper and that the Coulomb
slice through a field is a local chart of the quotient.

**Properness.** The action is proper in the sense of Bourbaki: `(u, y) ↦ (u · y, y)` is a proper
map (`TauCeti.Vortex.SobolevFieldSpace.properSMul`). This is the sequential properness
`TauCeti.Vortex.SobolevFieldSpace.exists_gaugeTransform_eq_and_tendsto`, which holds along every
filter, applied along ultrafilters.

**The Coulomb slice.** At a field `x` the Coulomb slice is the set of fields `y` with
`d₀* (y - x) = 0` (`TauCeti.Vortex.SobolevFieldSpace.coulombSlice`), where `d₀* = gaugeAdjoint x`
is the formal `L²` adjoint of the infinitesimal gauge action at `x`. Two of its properties near `x`
are proved earlier: every nearby field `y` is moved into the slice by a gauge `g y` depending
continuously on `y`, with `g x = 1`
(`SobolevFieldSpace.exists_mem_nhds_continuousOn_forall_gaugeAdjoint_smul_sub_eq_zero`),
and a gauge near `1` keeping a nearby field in the slice is `1`
(`TauCeti.Vortex.SobolevFieldSpace.exists_mem_nhds_forall_eq_one_of_gaugeAdjoint_sub_eq_zero`).

* **The slice meets each nearby orbit once.** There is an open neighbourhood `U` of `x` in the
  slice such that the action map `(u, y) ↦ u · y` is injective on `G_(k+1) × U`. Near `(1, x)` this
  is the local uniqueness of the Coulomb gauge: if `a · y = b · y'` with `y, y'` in the slice near
  `x` and `a, b` near `1`, then `b⁻¹ a` is near `1` and keeps `y` in the slice, so `a = b`.
  Properness and freeness of the action upgrade injectivity near `(1, x)` to injectivity on
  `G_(k+1) × U` (`ProperSMul.exists_mem_nhds_injOn_smul_slice`).
* **Local triviality.** There is an open neighbourhood `U` of `x` in the slice such that the action
  map `G_(k+1) × U → A_m^k`, `(u, y) ↦ u · y`, is an open embedding
  (`TauCeti.Vortex.SobolevFieldSpace.exists_isOpen_isOpenEmbedding_smul_coulombSlice`). It is
  injective by the previous point, and it is open because near `u · y` the map
  `z ↦ (u (g (u⁻¹ z))⁻¹, g (u⁻¹ z) · u⁻¹ z)` is a continuous local inverse, the Coulomb gauge `g`
  being trivial on the slice near `x`.
* **The slice theorem.** On the same kind of neighbourhood `U`, `π` is an open embedding of `U`
  into `A_m^k / G_(k+1)`
  (`TauCeti.Vortex.SobolevFieldSpace.exists_isOpen_isOpenEmbedding_quotientMk_coulombSlice`). So
  near `π x` the quotient is homeomorphic to an open subset of the Coulomb slice.

The last two statements are the orbit-space charts from slices
(`TauCeti.MulAction.isOpenEmbedding_smul_slice`,
`TauCeti.MulAction.isOpenEmbedding_quotientMk_slice`) for the slice `U ⊆ coulombSlice x`. Their
hypotheses, the injectivity and the local homeomorphism property of the action map on
`G_(k+1) × U`, are what this file proves.

Restricted to vortices, the slice theorem and the Coulomb slice chart of the vortices in the slice
(`TauCeti.Vortex.coulombSliceChart`) are the two ingredients of a chart of dimension `2m` of the
Sobolev moduli space of vortices at the orbit of a smooth vortex. Assembling them, and the
smoothness of the transition maps between such charts, are not treated here.

## Main definitions

* `TauCeti.Vortex.SobolevFieldSpace.coulombSlice x`: the Coulomb slice `d₀* (y - x) = 0` at `x`.

## Main results

* `TauCeti.Vortex.SobolevFieldSpace.properSMul`: for `k ≥ 3`, `G_(k+1)` acts properly on `A_m^k`.
* `TauCeti.Vortex.SobolevFieldSpace.exists_isOpen_isOpenEmbedding_smul_coulombSlice`: the gauge
  orbits through the slice near `x` form an open set homeomorphic to `G_(k+1) × U`.
* `TauCeti.Vortex.SobolevFieldSpace.exists_isOpen_isOpenEmbedding_quotientMk_coulombSlice`: the
  slice theorem.

## References

* A. Jaffe and C. H. Taubes, *Vortices and Monopoles*, Progress in Physics 2, Birkhäuser, 1980,
  Chapter III.
* S. K. Donaldson and P. B. Kronheimer, *The Geometry of Four-Manifolds*, Oxford University Press,
  1990, Section 4.2.
-/

public section

noncomputable section

namespace TauCeti.Vortex

open Filter Topology Set

namespace SobolevFieldSpace

open SobolevTopologicalGaugeGroup

variable {f : ContDiffBump (0 : ℝ)} {m k : ℕ} {hs : 1 < (k : ℝ) + 1}

/-! ### Properness of the action -/

/-- **The Sobolev gauge group acts properly on the framed fields.** For an integer `k ≥ 3`, the
action of `G_(k+1)` on the continuous fields of `A_m^k` is proper in the sense of Bourbaki: the map
`(u, y) ↦ (u · y, y)` is proper. -/
theorem properSMul [Fact (1 < k)] (hk : 2 < k) :
    ProperSMul (SobolevTopologicalGaugeGroup hs) (SobolevFieldSpace f m k) := by
  refine properSMul_iff_continuousSMul_ultrafilter_tendsto.2 ⟨inferInstance, fun 𝒰 y₁ y₂ h ↦ ?_⟩
  have h₁ : Tendsto (fun q : SobolevTopologicalGaugeGroup hs × SobolevFieldSpace f m k ↦ q.1 • q.2)
      (𝒰 : Filter _) (𝓝 y₁) := h.fst_nhds
  have h₂ : Tendsto (fun q : SobolevTopologicalGaugeGroup hs × SobolevFieldSpace f m k ↦ q.2)
      (𝒰 : Filter _) (𝓝 y₂) := h.snd_nhds
  obtain ⟨u, hu, hconv⟩ := exists_gaugeTransform_eq_and_tendsto hk
    (l := (𝒰 : Filter (SobolevTopologicalGaugeGroup hs × SobolevFieldSpace f m k)))
    (xs := fun q ↦ q.2) (ys := fun q ↦ q.1 • q.2) (us := fun q ↦ q.1)
    (fun q ↦ (coe_smul q.1 q.2).symm) h₂ h₁
  exact ⟨u, ext (by rw [coe_smul, hu]), hconv⟩

/-! ### The Coulomb slice -/

/-- **The Coulomb slice** at a field `x` of `A_m^k`: the fields `y` with `d₀* (y - x) = 0`, where
`d₀* = gaugeAdjoint x` is the formal `L²` adjoint of the infinitesimal gauge action at `x`. -/
def coulombSlice (x : SobolevFieldSpace f m k) : Set (SobolevFieldSpace f m k) :=
  {y | ∀ z, gaugeAdjoint x (⇑y - ⇑x) z = 0}

@[simp]
theorem mem_coulombSlice {x y : SobolevFieldSpace f m k} :
    y ∈ coulombSlice x ↔ ∀ z, gaugeAdjoint x (⇑y - ⇑x) z = 0 :=
  Iff.rfl

/-- A field lies in its own Coulomb slice. -/
theorem self_mem_coulombSlice (x : SobolevFieldSpace f m k) : x ∈ coulombSlice x := fun z ↦ by
  simp [gaugeAdjoint_def]

variable [Fact (1 < k)]

variable (hs) in
/-- The Coulomb slice of `x` meets the gauge orbits near `x` at most once near the identity: the
action map `(u, s) ↦ u · s` on `G_(k+1)` times the slice is injective near `(1, x)`. -/
private theorem exists_mem_nhds_injOn_smul_coulombSlice (hk : 3 ≤ k)
    (x : SobolevFieldSpace f m k) :
    ∃ N ∈ 𝓝 ((1 : SobolevTopologicalGaugeGroup hs),
      (⟨x, self_mem_coulombSlice x⟩ : coulombSlice x)),
      InjOn (fun p : SobolevTopologicalGaugeGroup hs × coulombSlice x ↦
        p.1 • (p.2 : SobolevFieldSpace f m k)) N := by
  obtain ⟨U, hU, N₀, hN₀, huniq⟩ :=
    exists_mem_nhds_forall_eq_one_of_gaugeAdjoint_sub_eq_zero hs hk x
  -- Gauges `a, b` near `1` have `b⁻¹ a ∈ N₀`.
  have hcont : Tendsto (fun q : SobolevTopologicalGaugeGroup hs × SobolevTopologicalGaugeGroup hs ↦
      q.2⁻¹ * q.1) (𝓝 (1, 1)) (𝓝 1) :=
    (by fun_prop : Continuous fun q : SobolevTopologicalGaugeGroup hs ×
      SobolevTopologicalGaugeGroup hs ↦ q.2⁻¹ * q.1).tendsto' _ _ (by simp)
  have hW := hcont hN₀
  rw [nhds_prod_eq] at hW
  obtain ⟨N₁, hN₁, hN₁N₀⟩ := mem_prod_self_iff.1 hW
  refine ⟨N₁ ×ˢ (Subtype.val ⁻¹' U), prod_mem_nhds hN₁
    (continuous_subtypeVal.continuousAt.preimage_mem_nhds hU), ?_⟩
  rintro ⟨a, s, hs⟩ ⟨ha, hsU⟩ ⟨b, s', hs'⟩ ⟨hb, -⟩ (h : a • s = b • s')
  have hmove : (b⁻¹ * a) • s = s' := by rw [mul_smul, h, inv_smul_smul]
  have hba : b⁻¹ * a = 1 :=
    huniq s hsU _ (hN₁N₀ (show (a, b) ∈ N₁ ×ˢ N₁ from ⟨ha, hb⟩)) hs (hmove ▸ hs')
  rw [hba, one_smul] at hmove
  rw [inv_mul_eq_one] at hba
  simp only [hba, hmove]

variable (hs) in
/-- An open neighbourhood `V` of `x` on which the Coulomb gauge `g`, moving fields into the slice of
`x`, is continuous and trivial on the slice, and such that the action map is injective on
`G_(k+1)` times the part of the slice in `V`. -/
private theorem exists_isOpen_coulombGauge (hk : 3 ≤ k) (x : SobolevFieldSpace f m k) :
    ∃ V : Set (SobolevFieldSpace f m k), IsOpen V ∧ x ∈ V ∧
      ∃ g : SobolevFieldSpace f m k → SobolevTopologicalGaugeGroup hs,
        (∀ y ∈ V, ContinuousAt g y) ∧ (∀ y ∈ V, g y • y ∈ coulombSlice x) ∧
        (∀ y ∈ V ∩ coulombSlice x, g y = 1) ∧
        InjOn (fun p : SobolevTopologicalGaugeGroup hs × coulombSlice x ↦
          p.1 • (p.2 : SobolevFieldSpace f m k)) (univ ×ˢ (Subtype.val ⁻¹' V)) := by
  have := properSMul (f := f) (m := m) (hs := hs) (by omega)
  -- Properness and freeness upgrade injectivity near `(1, x)` to injectivity on `G_(k+1) × U₁`.
  obtain ⟨N, hN, hinjN⟩ := exists_mem_nhds_injOn_smul_coulombSlice hs hk x
  obtain ⟨U₁, hU₁, hinj⟩ := ProperSMul.exists_mem_nhds_injOn_smul_slice
    continuous_subtypeVal.continuousAt (eq_bot_iff.2 fun u hu ↦ Subgroup.mem_bot.2 <|
      IsCancelSMul.right_cancel u 1 x (by rw [one_smul]; exact hu)) hN hinjN
  obtain ⟨V₁, hV₁, hV₁U₁⟩ := mem_nhds_subtype _ _ _ |>.1 hU₁
  obtain ⟨U, hU, N₀, hN₀, huniq⟩ :=
    exists_mem_nhds_forall_eq_one_of_gaugeAdjoint_sub_eq_zero hs hk x
  obtain ⟨Ug, hUg, g, hg, hgx, hgS⟩ :=
    exists_mem_nhds_continuousOn_forall_gaugeAdjoint_smul_sub_eq_zero hs hk x
  have hgN₀ : g ⁻¹' N₀ ∈ 𝓝 x := (hg.continuousAt hUg).preimage_mem_nhds (by rwa [hgx])
  set V := interior (V₁ ∩ U ∩ interior Ug ∩ g ⁻¹' N₀)
  refine ⟨V, isOpen_interior, mem_interior_iff_mem_nhds.2 <| inter_mem
      (inter_mem (inter_mem hV₁ hU) (interior_mem_nhds.2 hUg)) hgN₀, g,
    fun y hy ↦ hg.continuousAt (mem_interior_iff_mem_nhds.1 (interior_subset hy).1.2),
    fun y hy ↦ hgS y (interior_subset (interior_subset hy).1.2), fun w hw ↦ ?_,
    hinj.mono (prod_mono subset_rfl fun s hs ↦ hV₁U₁ (interior_subset hs).1.1.1)⟩
  -- On the slice near `x` the Coulomb gauge is near `1`, hence trivial.
  have hw' := interior_subset hw.1
  exact huniq w hw'.1.1.2 (g w) hw'.2 hw.2 (hgS w (interior_subset hw'.1.2))

variable (hs) in
/-- Near `x`, the action map `(u, s) ↦ u · s` on `G_(k+1)` times the Coulomb slice of `x`,
restricted to `G_(k+1) × U` for an open neighbourhood `U` of `x` in the slice, is an open
embedding. -/
private theorem exists_isOpen_isOpenEmbedding_domRestrict_smul (hk : 3 ≤ k)
    (x : SobolevFieldSpace f m k) :
    ∃ U : Set (coulombSlice x), IsOpen U ∧ ⟨x, self_mem_coulombSlice x⟩ ∈ U ∧
      IsOpenEmbedding ((univ ×ˢ U).domRestrict
        fun p : SobolevTopologicalGaugeGroup hs × coulombSlice x ↦
          p.1 • (p.2 : SobolevFieldSpace f m k)) := by
  obtain ⟨V, hVo, hxV, g, hg, hgS, hg1, hinj⟩ := exists_isOpen_coulombGauge hs hk x
  refine ⟨Subtype.val ⁻¹' V, continuous_subtypeVal.isOpen_preimage _ hVo, hxV,
    .of_continuous_injective_isOpenMap ((continuous_fst.smul
      (continuous_subtypeVal.comp continuous_snd)).continuousOn.domRestrict) ?_ ?_⟩
  · exact fun p q h ↦ Subtype.ext (hinj p.property q.property h)
  · -- Near `z = u · y`, the map `z' ↦ (u (g (u⁻¹ z'))⁻¹, g (u⁻¹ z') · u⁻¹ z')` is a continuous
    -- local inverse with value `(u, y)` at `z`.
    intro W hW
    obtain ⟨W₁, hW₁, rfl⟩ := isOpen_induced_iff.1 hW
    obtain ⟨W', hW', rfl⟩ :=
      isOpen_induced_iff.1 ((IsEmbedding.id.prodMap IsEmbedding.subtypeVal).isOpen_iff.1 hW₁)
    rw [isOpen_iff_mem_nhds]
    rintro _ ⟨⟨⟨u, y, hyS⟩, hp⟩, hW'y, rfl⟩
    have hyV : y ∈ V := hp.2
    have hy : y ∈ V ∩ coulombSlice x := ⟨hyV, hyS⟩
    have hA : Tendsto (fun z ↦ u⁻¹ • z) (𝓝 (u • y)) (𝓝 y) := by
      simpa only [inv_smul_smul] using (continuous_const_smul u⁻¹).tendsto (u • y)
    have hgt : Tendsto (fun z ↦ g (u⁻¹ • z)) (𝓝 (u • y)) (𝓝 1) := by
      have := (hg y hyV).tendsto.comp hA
      rw [hg1 y hy] at this
      exact this
    have hrt : Tendsto (fun z ↦ g (u⁻¹ • z) • u⁻¹ • z) (𝓝 (u • y)) (𝓝 y) := by
      simpa only [one_smul] using hgt.smul hA
    have hpt : Tendsto (fun z ↦ (u * (g (u⁻¹ • z))⁻¹, g (u⁻¹ • z) • u⁻¹ • z)) (𝓝 (u • y))
        (𝓝 (u, y)) := by
      simpa only [inv_one, mul_one] using (tendsto_const_nhds.mul hgt.inv).prodMk_nhds hrt
    filter_upwards [hpt (hW'.mem_nhds hW'y), hA (hVo.mem_nhds hyV), hrt (hVo.mem_nhds hyV)]
      with z hzW hzV hrV
    refine ⟨⟨⟨u * (g (u⁻¹ • z))⁻¹, ⟨_, hgS _ hzV⟩⟩, mem_univ _, hrV⟩, hzW, ?_⟩
    simp only [domRestrict_apply, mul_smul, inv_smul_smul, smul_inv_smul]

variable (hs) in
/-- The action map on `G_(k+1)` times the Coulomb slice of `x` is injective and a local
homeomorphism on `G_(k+1) × U`, for an open neighbourhood `U` of `x` in the slice: the hypotheses
of the orbit-space charts from slices. -/
private theorem exists_isOpen_injOn_isLocalHomeomorphOn_smul (hk : 3 ≤ k)
    (x : SobolevFieldSpace f m k) :
    ∃ U : Set (coulombSlice x), IsOpen U ∧ ⟨x, self_mem_coulombSlice x⟩ ∈ U ∧
      InjOn (fun p : SobolevTopologicalGaugeGroup hs × coulombSlice x ↦
        p.1 • (p.2 : SobolevFieldSpace f m k)) (univ ×ˢ U) ∧
      IsLocalHomeomorphOn (fun p : SobolevTopologicalGaugeGroup hs × coulombSlice x ↦
        p.1 • (p.2 : SobolevFieldSpace f m k)) (univ ×ˢ U) := by
  obtain ⟨U, hUo, hxU, hemb⟩ := exists_isOpen_isOpenEmbedding_domRestrict_smul hs hk x
  exact ⟨U, hUo, hxU, injOn_iff_injective.2 hemb.injective,
    (isLocalHomeomorphOn_iff_isOpenEmbedding_restrict _).2 fun p hp ↦
      ⟨_, (isOpen_univ.prod hUo).mem_nhds hp, hemb⟩⟩

variable (hs) in
/-- **The Coulomb slice theorem for framed vortex fields: local triviality.** Let `x` be a
continuous field of `A_m^k`, `k ≥ 3`. There is an open neighbourhood `U` of `x` in its Coulomb slice
such that the action map `G_(k+1) × U → A_m^k`, `(u, y) ↦ u · y`, is an open embedding. So the
gauge orbits through `U` fill an open set of `A_m^k`, homeomorphic to `G_(k+1) × U`. -/
theorem exists_isOpen_isOpenEmbedding_smul_coulombSlice (hk : 3 ≤ k)
    (x : SobolevFieldSpace f m k) :
    ∃ U : Set (coulombSlice x), IsOpen U ∧ ⟨x, self_mem_coulombSlice x⟩ ∈ U ∧
      IsOpenEmbedding fun p : SobolevTopologicalGaugeGroup hs × U ↦
        p.1 • ((p.2 : coulombSlice x) : SobolevFieldSpace f m k) := by
  obtain ⟨U, hUo, hxU, hinj, hloc⟩ := exists_isOpen_injOn_isLocalHomeomorphOn_smul hs hk x
  exact ⟨U, hUo, hxU, TauCeti.MulAction.isOpenEmbedding_smul_slice hUo hinj hloc⟩

variable (hs) in
/-- **The Coulomb slice theorem for framed vortex fields.** Let `x` be a continuous field of
`A_m^k`, `k ≥ 3`. There is an open neighbourhood `U` of `x` in its Coulomb slice on which the
quotient map `A_m^k → A_m^k / G_(k+1)` is an open embedding. So near the orbit of `x` the quotient
is homeomorphic to an open subset of the Coulomb slice. -/
theorem exists_isOpen_isOpenEmbedding_quotientMk_coulombSlice (hk : 3 ≤ k)
    (x : SobolevFieldSpace f m k) :
    ∃ U : Set (coulombSlice x), IsOpen U ∧ ⟨x, self_mem_coulombSlice x⟩ ∈ U ∧
      IsOpenEmbedding fun y : U ↦
        Quotient.mk (MulAction.orbitRel (SobolevTopologicalGaugeGroup hs)
          (SobolevFieldSpace f m k)) ((y : coulombSlice x) : SobolevFieldSpace f m k) := by
  obtain ⟨U, hUo, hxU, hinj, hloc⟩ := exists_isOpen_injOn_isLocalHomeomorphOn_smul hs hk x
  exact ⟨U, hUo, hxU, TauCeti.MulAction.isOpenEmbedding_quotientMk_slice hUo hinj hloc⟩

end SobolevFieldSpace

end TauCeti.Vortex

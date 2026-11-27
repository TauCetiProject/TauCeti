/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.ReImTopology
public import Mathlib.Topology.Sets.Opens
public import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Topology.UniformSpace.HeineCantor

/-!
# Upper halves of open planar sets

The open upper half `W ∩ {0 < im}` of an open set `W ⊆ ℂ` is packaged as an open set,
`TopologicalSpace.Opens.upperHalf`. A closed half-plane `{a ≤ im}` is closed
(`Complex.isClosed_setOfPred_le_im`), so its trace on an open set is locally closed
(`IsOpen.isLocallyClosed_inter_setOfPred_le_im`), and it is a neighbourhood of each point of the
open half-plane `{a < im}` (`TauCeti.setOfPred_le_im_mem_nhds`). A relatively open subset
`Ω ∩ {0 ≤ im}` of the closed upper half-plane has interior `Ω ∩ {0 < im}`
(`TauCeti.interior_inter_setOf_im_nonneg`), which as an open set is the upper half of `Ω`
(`TopologicalSpace.Opens.interior_inter_setOf_im_nonneg_eq_upperHalf`), and every point of
`Ω ∩ {0 ≤ im}` is a limit of interior points
(`TauCeti.subset_closure_interior_inter_setOf_im_nonneg`). The set `Ω ∩ {0 ≤ im}` is also the
closed upper part of a conjugation-invariant open set
(`TauCeti.exists_isOpen_mapsTo_conj_inter_setOf_im_nonneg_eq`), and a compact subset of a
conjugation-invariant open set lies in a conjugation-invariant open set with compact closure inside
it (`TauCeti.exists_mapsTo_conj_between_and_isCompact_closure`). If the closure of `U` lies in `Ω`,
the closure of `U ∩ {0 ≤ im}` lies in `Ω ∩ {0 ≤ im}`
(`TauCeti.closure_inter_setOf_im_nonneg_subset`). A local property holds on
`Ω ∩ {0 ≤ im}` once it holds on the upper half of `Ω` and on the half-discs centred on the real
axis (`TauCeti.inter_setOf_im_nonneg_induction`). A function continuous on `Ω ∩ {0 ≤ im}` and
zero on `Ω ∩ ℝ` is uniformly small near the axis on compact sets
(`TauCeti.exists_forall_norm_lt_of_im_lt`).
-/

public noncomputable section

open TopologicalSpace
open scoped Topology

/-- The open upper half `W ∩ {0 < im}` of an open planar set `W`. -/
def TopologicalSpace.Opens.upperHalf (W : Opens ℂ) : Opens ℂ :=
  ⟨(W : Set ℂ) ∩ {z : ℂ | 0 < z.im},
    W.isOpen.inter (isOpen_lt continuous_const Complex.continuous_im)⟩

@[simp]
theorem TopologicalSpace.Opens.coe_upperHalf (W : Opens ℂ) :
    (W.upperHalf : Set ℂ) = (W : Set ℂ) ∩ {z : ℂ | 0 < z.im} := (rfl)

@[simp]
theorem TopologicalSpace.Opens.mem_upperHalf {W : Opens ℂ} {z : ℂ} :
    z ∈ W.upperHalf ↔ z ∈ W ∧ 0 < z.im :=
  (Iff.rfl)

/-- Taking upper halves is monotone. -/
theorem TopologicalSpace.Opens.upperHalf_mono {V W : Opens ℂ} (h : V ≤ W) :
    V.upperHalf ≤ W.upperHalf :=
  fun _ hz => Opens.mem_upperHalf.2 ⟨h (Opens.mem_upperHalf.1 hz).1, (Opens.mem_upperHalf.1 hz).2⟩

/-- The upper half of an open planar set lies in its closed upper half. -/
theorem TopologicalSpace.Opens.coe_upperHalf_subset (W : Opens ℂ) :
    (W.upperHalf : Set ℂ) ⊆ (W : Set ℂ) ∩ {z : ℂ | 0 ≤ z.im} :=
  fun _ hz => ⟨(Opens.mem_upperHalf.1 hz).1, (Opens.mem_upperHalf.1 hz).2.le⟩

/-- A closed half-plane `{a ≤ im}` is closed. -/
theorem Complex.isClosed_setOfPred_le_im (a : ℝ) : IsClosed {z : ℂ | a ≤ z.im} :=
  isClosed_le continuous_const Complex.continuous_im

/-- The trace `Ω ∩ {a ≤ im}` of a closed half-plane on an open set is locally closed. -/
theorem IsOpen.isLocallyClosed_inter_setOfPred_le_im {Ω : Set ℂ} (hΩ : IsOpen Ω) (a : ℝ) :
    IsLocallyClosed (Ω ∩ {z : ℂ | a ≤ z.im}) :=
  hΩ.isLocallyClosed.inter (Complex.isClosed_setOfPred_le_im a).isLocallyClosed

namespace TauCeti

/-- A closed half-plane `{z : ℂ | a ≤ z.im}` is a neighbourhood of each point of the open
half-plane `{z | a < z.im}`. -/
theorem setOfPred_le_im_mem_nhds {a : ℝ} {w : ℂ} (hw : a < w.im) :
    {z : ℂ | a ≤ z.im} ∈ 𝓝 w :=
  mem_interior_iff_mem_nhds.mp (by rwa [Complex.interior_setOfPred_le_im])

/-- A relatively open subset `Ω ∩ {0 ≤ im}` of the closed upper half-plane has interior
`Ω ∩ {0 < im}` in `ℂ`: points on the real axis are not interior, since every neighbourhood meets
`{z | z.im < 0}`. -/
theorem interior_inter_setOf_im_nonneg {Ω : Set ℂ} (hΩ : IsOpen Ω) :
    interior (Ω ∩ {z : ℂ | 0 ≤ z.im}) = Ω ∩ {z : ℂ | 0 < z.im} := by
  rw [interior_inter, hΩ.interior_eq, Complex.interior_setOfPred_le_im]

/-- For `Ω` open, every point of `Ω ∩ {0 ≤ im}`, including the points on the real axis, lies in
the closure of its interior. -/
theorem subset_closure_interior_inter_setOf_im_nonneg {Ω : Set ℂ} (hΩ : IsOpen Ω) :
    Ω ∩ {z : ℂ | 0 ≤ z.im} ⊆ closure (interior (Ω ∩ {z : ℂ | 0 ≤ z.im})) := by
  intro x hx
  rw [interior_inter_setOf_im_nonneg hΩ]
  exact hΩ.inter_closure ⟨hx.1, by rw [Complex.closure_setOfPred_lt_im]; exact hx.2⟩

/-- **A conjugation-invariant open set with the same closed upper part.** For `Ω` open, the open
set `Ω' = {z | re z + i |im z| ∈ Ω}` is invariant under conjugation and has the same closed upper
part `Ω ∩ {0 ≤ im}` as `Ω`. -/
theorem exists_isOpen_mapsTo_conj_inter_setOf_im_nonneg_eq {Ω : Set ℂ} (hΩ : IsOpen Ω) :
    ∃ Ω' : Set ℂ, IsOpen Ω' ∧ Set.MapsTo (starRingEnd ℂ) Ω' Ω' ∧
      Ω' ∩ {z : ℂ | 0 ≤ z.im} = Ω ∩ {z : ℂ | 0 ≤ z.im} := by
  refine ⟨(fun z : ℂ ↦ (z.re : ℂ) + |z.im| * Complex.I) ⁻¹' Ω, hΩ.preimage (by fun_prop),
    fun z hz ↦ by simpa using hz, ?_⟩
  ext z
  exact and_congr_left fun h ↦ by
    rw [Set.mem_preimage, abs_of_nonneg (show 0 ≤ z.im from h), Complex.re_add_im]

/-- **A conjugation-invariant open set between a compact set and an open set.** If `Ω ⊆ ℂ` is open
and invariant under conjugation and `K ⊆ Ω` is compact, there is an open set `W`, invariant under
conjugation, with `K ⊆ W` and compact closure contained in `Ω`. -/
theorem exists_mapsTo_conj_between_and_isCompact_closure {K : Set ℂ} (hK : IsCompact K)
    {Ω : Opens ℂ} (hΩ : Set.MapsTo (starRingEnd ℂ) Ω Ω) (hKΩ : K ⊆ Ω) :
    ∃ W : Opens ℂ, Set.MapsTo (starRingEnd ℂ) W W ∧ K ⊆ W ∧ closure (W : Set ℂ) ⊆ Ω ∧
      IsCompact (closure (W : Set ℂ)) := by
  -- Take an open set between `K ∪ conj K` and `Ω`, and intersect it with its conjugate.
  obtain ⟨V, hVo, hKV, hVΩ, hVc⟩ := exists_open_between_and_isCompact_closure
    (hK.union (hK.image Complex.continuous_conj)) Ω.isOpen
    (Set.union_subset hKΩ (Set.image_subset_iff.2 fun z hz => hΩ (hKΩ hz)))
  have hW : closure (V ∩ starRingEnd ℂ ⁻¹' V) ⊆ closure V := closure_mono Set.inter_subset_left
  refine ⟨⟨V ∩ starRingEnd ℂ ⁻¹' V, hVo.inter (hVo.preimage Complex.continuous_conj)⟩,
    fun z hz => ⟨hz.2, by simpa using hz.1⟩,
    fun z hz => ⟨hKV (Or.inl hz), hKV (Or.inr ⟨z, hz, rfl⟩)⟩, hW.trans hVΩ,
    hVc.of_isClosed_subset isClosed_closure hW⟩

/-- The closure of `U ∩ {0 ≤ im}` lies in `Ω ∩ {0 ≤ im}` when the closure of `U` lies in `Ω`,
since it lies in `closure U ∩ {0 ≤ im}`. -/
theorem closure_inter_setOf_im_nonneg_subset {Ω U : Set ℂ} (hUΩ : closure U ⊆ Ω) :
    closure (U ∩ {z | 0 ≤ z.im}) ⊆ Ω ∩ {z | 0 ≤ z.im} :=
  (closure_minimal (Set.inter_subset_inter_left _ subset_closure)
    (isClosed_closure.inter (Complex.isClosed_setOfPred_le_im 0))).trans
    (Set.inter_subset_inter_left _ hUΩ)
/-- **Induction on half-discs.** A property `P` of subsets of `ℂ` holds on `Ω ∩ {0 ≤ im}` if it
can be checked on relative neighbourhoods of each point, and holds on the upper half
`Ω ∩ {0 < im}` and on the half-discs `ball x r ∩ {0 ≤ im}` centred on the real axis inside `Ω`. -/
theorem inter_setOf_im_nonneg_induction {Ω : Opens ℂ} (P : Set ℂ → Prop)
    (hP : (∀ z ∈ (Ω : Set ℂ) ∩ {z | 0 ≤ z.im},
      ∃ V ∈ 𝓝[(Ω : Set ℂ) ∩ {z | 0 ≤ z.im}] z, P V) → P ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}))
    (hint : P Ω.upperHalf)
    (hbd : ∀ x r : ℝ, 0 < r → Metric.ball (x : ℂ) r ⊆ Ω →
      P (Metric.ball (x : ℂ) r ∩ {z | 0 ≤ z.im})) :
    P ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) := by
  refine hP fun z hz => ?_
  simp only [Set.mem_inter_iff, Set.mem_ofPred_eq] at hz
  rcases hz.2.lt_or_eq with hz0 | hz0
  · exact ⟨Ω.upperHalf, mem_nhdsWithin_of_mem_nhds (Ω.upperHalf.isOpen.mem_nhds
      (Opens.mem_upperHalf.2 ⟨hz.1, hz0⟩)), hint⟩
  · have hzx : ((z.re : ℝ) : ℂ) = z := Complex.ext (by simp) (by simp [hz0])
    obtain ⟨r, hr, hrΩ⟩ := Metric.isOpen_iff.1 Ω.isOpen _ (hzx.symm ▸ hz.1)
    exact ⟨Metric.ball (z.re : ℂ) r ∩ {z | 0 ≤ z.im}, mem_nhdsWithin.2
      ⟨Metric.ball (z.re : ℂ) r, Metric.isOpen_ball, hzx ▸ Metric.mem_ball_self hr,
        fun w hw => ⟨hw.1, hw.2.2⟩⟩, hbd z.re r hr hrΩ⟩

end TauCeti

/-- The interior of the half-disc `Ω ∩ {0 ≤ im}`, as an open set, is the upper half of `Ω`. -/
theorem TopologicalSpace.Opens.interior_inter_setOf_im_nonneg_eq_upperHalf (Ω : Opens ℂ) :
    Opens.interior ((Ω : Set ℂ) ∩ {z : ℂ | 0 ≤ z.im}) = Ω.upperHalf :=
  Opens.ext ((TauCeti.interior_inter_setOf_im_nonneg Ω.isOpen).trans (Opens.coe_upperHalf Ω).symm)

namespace TauCeti

open Metric Set

/-- A function continuous on `Ω ∩ {0 ≤ im}` and zero on `Ω ∩ ℝ` is uniformly small near the axis
on every compact subset of `Ω ∩ {0 ≤ im}`. -/
theorem exists_forall_norm_lt_of_im_lt {E : Type*} [NormedAddCommGroup E] {Ω : Opens ℂ}
    {g : ℂ → E}
    (hgc : ContinuousOn g ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im})) (hg0 : ∀ x : ℝ, (x : ℂ) ∈ Ω → g x = 0)
    {T : Set ℂ} (hT : IsCompact T) (hTΩ : T ⊆ Ω) (hT0 : T ⊆ {z | 0 ≤ z.im}) {ε : ℝ}
    (hε : 0 < ε) : ∃ δ > 0, ∀ z ∈ T, z.im < δ → ‖g z‖ < ε := by
  have hclosed : IsClosed {z : ℂ | 0 ≤ z.im} := Complex.isClosed_setOfPred_le_im 0
  obtain ⟨r, hr, hrΩ⟩ := hT.exists_cthickening_subset_open Ω.isOpen hTΩ
  have hC : IsCompact (cthickening r T ∩ {z : ℂ | 0 ≤ z.im}) := hT.cthickening.inter_right hclosed
  obtain ⟨δ, hδ, hgδ⟩ := Metric.uniformContinuousOn_iff.1 (hC.uniformContinuousOn_of_continuous
    (hgc.mono fun z hz => ⟨hrΩ hz.1, hz.2⟩)) ε hε
  refine ⟨min δ r, lt_min hδ hr, fun z hzT hzδ => ?_⟩
  have hz0 : 0 ≤ z.im := hT0 hzT
  have hdist : dist (z.re : ℂ) z = z.im := by
    rw [Complex.dist_eq_re_im]
    simp [Real.sqrt_sq hz0]
  have hz' : (z.re : ℂ) ∈ cthickening r T ∩ {z : ℂ | 0 ≤ z.im} :=
    ⟨mem_cthickening_of_dist_le _ z r T hzT (by linarith [min_le_right δ r]), by simp⟩
  have h := hgδ z ⟨self_subset_cthickening T hzT, hz0⟩ _ hz'
    (by rw [dist_comm, hdist]; linarith [min_le_left δ r])
  rwa [hg0 _ (hrΩ hz'.1), dist_zero_right] at h

end TauCeti

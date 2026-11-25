/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca, The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Action.Pointwise.Set.Basic
public import Mathlib.Topology.Algebra.Group.Basic
public import TauCeti.Geometry.Euclidean.FirstContact.Basic

/-!
# First contact for translates of a closed set

Let two closed sets lie in a topological additive group, and continuously translate one of
them over a compact set of times. If all their intersections lie in a fixed compact set,
the contact times form a compact set and hence have a greatest element when nonempty.

For translations along a unit vector in an inner product space, a continuous map with closed
image lies locally below any continuous local graph of the barrier through its last contact
point. At interior points of a manifold source, differentiability gives tangency to each such
graph. Avoidance of the source boundary guarantees interiority of all contact points.

## References

* R. Brasca, [closed-barrier formalization](https://github.com/riccardobrasca/ColdingMinicozziTheory/commit/cfee5e52aa5576999d055c12bd0f004b0d7cba9f).
* O. Chodosh, *Introduction to minimal surfaces*, proof of Theorem 20.1.
-/

public section

open Filter Function Manifold Set Topology
open scoped InnerProductSpace Manifold Pointwise

namespace TauCeti

section ContactTimes

variable {A τ : Type*} [AddGroup A] [TopologicalSpace A] [IsTopologicalAddGroup A]
  [TopologicalSpace τ] {D : Set τ} {a : τ → A} {S C K : Set A}

/-- The contact times of a continuous translation of a closed set against another closed set
form a compact set if the times range over a compact set and the intersections lie in a
fixed compact set. -/
theorem isCompact_contactTimes (hD : IsCompact D) (ha : ContinuousOn a D)
    (hS : IsClosed S) (hC : IsClosed C) (hK : IsCompact K)
    (hsweep : ∀ t ∈ D, (a t +ᵥ S) ∩ C ⊆ K) :
    IsCompact {t ∈ D | ((a t +ᵥ S) ∩ C).Nonempty} := by
  let : CompactSpace D := isCompact_iff_compactSpace.1 hD
  let P : Set (A × D) := {p | p.1 ∈ C ∧ (-a p.2 : A) + p.1 ∈ S}
  have hmem (x : A) (t : D) : (x, t) ∈ P ↔ x ∈ (a t +ᵥ S) ∩ C := by
    change (x ∈ C ∧ (-a t : A) + x ∈ S) ↔ _
    rw [mem_inter_iff, mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add, and_comm]
  have hP : IsCompact P :=
    (hK.prod isCompact_univ).of_isClosed_subset
      ((hC.preimage continuous_fst).inter
        (hS.preimage ((ha.domRestrict.comp continuous_snd).neg.add continuous_fst)))
      fun p hp ↦ ⟨hsweep p.2 p.2.property ((hmem p.1 p.2).1 hp), mem_univ _⟩
  have himage : (fun p : A × D ↦ (p.2 : τ)) '' P =
      {t ∈ D | ((a t +ᵥ S) ∩ C).Nonempty} := by
    ext t
    constructor
    · rintro ⟨⟨x, s⟩, hs, rfl⟩
      exact ⟨s.property, x, (hmem x s).1 hs⟩
    · rintro ⟨ht, x, hx⟩
      exact ⟨(x, ⟨t, ht⟩), (hmem x ⟨t, ht⟩).2 hx, rfl⟩
  rw [← himage]
  exact hP.image (continuous_subtypeVal.comp continuous_snd)

variable [LinearOrder τ] [ClosedIciTopology τ]

/-- A continuous translation with nonempty contact times and compact times and contact sweep
has a greatest contact time. -/
theorem exists_isGreatest_contactTime (hD : IsCompact D) (ha : ContinuousOn a D)
    (hS : IsClosed S) (hC : IsClosed C) (hK : IsCompact K)
    (hsweep : ∀ t ∈ D, (a t +ᵥ S) ∩ C ⊆ K)
    (hne : ∃ t ∈ D, ((a t +ᵥ S) ∩ C).Nonempty) :
    ∃ t₀, IsGreatest {t ∈ D | ((a t +ᵥ S) ∩ C).Nonempty} t₀ := by
  obtain ⟨t, ht, hcontact⟩ := hne
  exact (isCompact_contactTimes hD ha hS hC hK hsweep).exists_isGreatest ⟨t, ht, hcontact⟩

end ContactTimes

/-- In a proper pseudometric additive group, a bounded contact sweep is enough for attainment
of the greatest contact time. -/
theorem exists_isGreatest_contactTime_of_isBounded {A τ : Type*} [PseudoMetricSpace A]
    [ProperSpace A] [AddGroup A] [IsTopologicalAddGroup A] [TopologicalSpace τ]
    [LinearOrder τ] [ClosedIciTopology τ] {D : Set τ} {a : τ → A} {S C : Set A}
    (hD : IsCompact D) (ha : ContinuousOn a D) (hS : IsClosed S) (hC : IsClosed C)
    (hbdd : Bornology.IsBounded (⋃ t ∈ D, (a t +ᵥ S) ∩ C))
    (hne : ∃ t ∈ D, ((a t +ᵥ S) ∩ C).Nonempty) :
    ∃ t₀, IsGreatest {t ∈ D | ((a t +ᵥ S) ∩ C).Nonempty} t₀ :=
  exists_isGreatest_contactTime hD ha hS hC hbdd.isCompact_closure
    (fun t ht _ hx ↦ subset_closure (mem_iUnion₂.2 ⟨t, ht, hx⟩)) hne

section LocalGraph

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] {e : F}
  {M : Type*} [TopologicalSpace M] {f : M → F} {S : Set F} {g : (ℝ ∙ e)ᗮ → ℝ} {T : ℝ}

/-- If the height function takes value `t₀` at `f x`, and a continuous local graph lies in
the unshifted barrier, then absence of later contacts forces the height to be at most `t₀`
near `x`. -/
theorem eventually_heightAboveGraph_le_of_disjoint (he : ‖e‖ = 1) {x : M} {t₀ : ℝ}
    (ht₀ : t₀ < T) (hf : ContinuousAt f x)
    (hdisj : ∀ t ∈ Ioc t₀ T, Disjoint ((t • e) +ᵥ S) (range f))
    (hg : ContinuousAt g ((ℝ ∙ e)ᗮ.orthogonalProjectionOnto (f x)))
    (hgS : ∀ᶠ k : (ℝ ∙ e)ᗮ in 𝓝 ((ℝ ∙ e)ᗮ.orthogonalProjectionOnto (f x)),
      (k : F) + g k • e ∈ S)
    (hx : heightAboveGraph e g (f x) = t₀) :
    ∀ᶠ y in 𝓝 x, heightAboveGraph e g (f y) ≤ t₀ := by
  let P := (ℝ ∙ e)ᗮ.orthogonalProjectionOnto
  have hPf : ContinuousAt (fun y ↦ P (f y)) x := P.continuous.continuousAt.comp hf
  have hh : ContinuousAt (fun y ↦ heightAboveGraph e g (f y)) x := by
    simp only [heightAboveGraph_def]
    exact ((continuous_const.inner continuous_id).continuousAt.comp hf).sub
      (ContinuousAt.comp (f := fun y ↦ P (f y)) hg hPf)
  have hxT : heightAboveGraph e g (f x) < T := by rwa [hx]
  filter_upwards [hPf.eventually hgS, hh.eventually (gt_mem_nhds hxT)] with y hyS hyT
  by_contra hlt
  let t := heightAboveGraph e g (f y)
  have hy : f y ∈ translatedGraph e {k | (k : F) + g k • e ∈ S} g t :=
    (mem_translatedGraph_iff he).2 ⟨hyS, rfl⟩
  rw [translatedGraph_def] at hy
  obtain ⟨k, hk, hky⟩ := hy
  have hyS' : f y ∈ (t • e) +ᵥ S := by
    change (k : F) + (g k + t) • e = f y at hky
    refine mem_vadd_set.2 ⟨(k : F) + g k • e, hk, ?_⟩
    simpa only [vadd_eq_add, add_smul, add_assoc, add_left_comm, add_comm] using hky
  exact disjoint_left.1 (hdisj t ⟨not_le.1 hlt, hyT.le⟩) hyS' (mem_range_self y)

/-- The translates `t e +ᵥ S` of a closed barrier against the closed image of a continuous
map have a last contact in `[0,T)` when there is contact in the interval, none at `T`, and the
contact sweep lies in a compact set. At that time the height of the map is locally at most
the contact height for every continuous local graph of the barrier through the point. -/
theorem exists_firstContact_translate (hf : Continuous f) (hC : IsClosed (range f))
    (he : ‖e‖ = 1) (hS : IsClosed S) (hT : Disjoint ((T • e) +ᵥ S) (range f))
    (hcontact : ∃ t ∈ Icc 0 T, (((t • e) +ᵥ S) ∩ range f).Nonempty)
    {K : Set F} (hK : IsCompact K)
    (hsweep : ∀ t ∈ Icc 0 T, ((t • e) +ᵥ S) ∩ range f ⊆ K) :
    ∃ t₀ ∈ Ico 0 T, (((t₀ • e) +ᵥ S) ∩ range f).Nonempty ∧
      (∀ t ∈ Icc 0 T, (((t • e) +ᵥ S) ∩ range f).Nonempty → t ≤ t₀) ∧
      ∀ (x : M) (g : (ℝ ∙ e)ᗮ → ℝ),
        ContinuousAt g ((ℝ ∙ e)ᗮ.orthogonalProjectionOnto (f x)) →
        (∀ᶠ k : (ℝ ∙ e)ᗮ in 𝓝 ((ℝ ∙ e)ᗮ.orthogonalProjectionOnto (f x)),
          (k : F) + g k • e ∈ S) →
        heightAboveGraph e g (f x) = t₀ →
        ∀ᶠ y in 𝓝 x, heightAboveGraph e g (f y) ≤ t₀ := by
  obtain ⟨t₀, ⟨ht₀, hne⟩, hmax⟩ := exists_isGreatest_contactTime isCompact_Icc
    (continuous_id.smul continuous_const).continuousOn hS hC hK hsweep hcontact
  have hlt : t₀ < T := lt_of_le_of_ne ht₀.2 fun ht ↦ by
    obtain ⟨y, hyS, hyC⟩ : (((T • e) +ᵥ S) ∩ range f).Nonempty := ht ▸ hne
    exact disjoint_left.1 hT hyS hyC
  refine ⟨t₀, ⟨ht₀.1, hlt⟩, hne, fun t ht h ↦ hmax ⟨ht, h⟩, fun x g hg hgS hx ↦ ?_⟩
  refine eventually_heightAboveGraph_le_of_disjoint he hlt hf.continuousAt ?_ hg hgS hx
  intro t ht
  exact disjoint_left.2 fun y hyS hyC ↦
    ht.1.not_ge (hmax ⟨⟨ht₀.1.trans ht.1.le, ht.2⟩, ⟨y, hyS, hyC⟩⟩)

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [ChartedSpace H M]

/-- If the translated barrier misses the image of the source boundary, every last contact point
is interior. If the map is differentiable there, its derivative is tangent to every
differentiable local graph of the barrier through the point. -/
theorem exists_firstContact_translate_tangent (hf : Continuous f) (hC : IsClosed (range f))
    (he : ‖e‖ = 1) (hS : IsClosed S) (hT : Disjoint ((T • e) +ᵥ S) (range f))
    (hcontact : ∃ t ∈ Icc 0 T, (((t • e) +ᵥ S) ∩ range f).Nonempty)
    {K : Set F} (hK : IsCompact K)
    (hsweep : ∀ t ∈ Icc 0 T, ((t • e) +ᵥ S) ∩ range f ⊆ K)
    (hbdry : ∀ t ∈ Icc 0 T, ∀ x, I.IsBoundaryPoint x → f x ∉ (t • e) +ᵥ S) :
    ∃ t₀ ∈ Ico 0 T, (((t₀ • e) +ᵥ S) ∩ range f).Nonempty ∧
      (∀ t ∈ Icc 0 T, (((t • e) +ᵥ S) ∩ range f).Nonempty → t ≤ t₀) ∧
      ∀ x, f x ∈ (t₀ • e) +ᵥ S → I.IsInteriorPoint x ∧
        ∀ g : (ℝ ∙ e)ᗮ → ℝ, DifferentiableAt ℝ g ((ℝ ∙ e)ᗮ.orthogonalProjectionOnto (f x)) →
          (∀ᶠ k : (ℝ ∙ e)ᗮ in 𝓝 ((ℝ ∙ e)ᗮ.orthogonalProjectionOnto (f x)),
            (k : F) + g k • e ∈ S) →
          heightAboveGraph e g (f x) = t₀ →
          (∀ᶠ y in 𝓝 x, heightAboveGraph e g (f y) ≤ t₀) ∧
          (MDifferentiableAt I 𝓘(ℝ, F) f x →
            ∀ v : TangentSpace I x, ⟪e, mvfderiv I f x v⟫_ℝ =
              fderiv ℝ g ((ℝ ∙ e)ᗮ.orthogonalProjectionOnto (f x))
                ((ℝ ∙ e)ᗮ.orthogonalProjectionOnto (mvfderiv I f x v))) := by
  obtain ⟨t₀, ht₀, hne, hmax, hside⟩ :=
    exists_firstContact_translate hf hC he hS hT hcontact hK hsweep
  refine ⟨t₀, ht₀, hne, hmax, fun x hx ↦ ?_⟩
  have hxI : I.IsInteriorPoint x := (I.isInteriorPoint_iff_not_isBoundaryPoint x).2
    (fun hb ↦ hbdry t₀ ⟨ht₀.1, ht₀.2.le⟩ x hb hx)
  refine ⟨hxI, fun g hg hgS hxg ↦ ?_⟩
  have hle := hside x g hg.continuousAt hgS hxg
  have hmax' : IsLocalMax (fun y ↦ heightAboveGraph e g (f y)) x := by
    filter_upwards [hle] with y hy
    simpa only [hxg] using hy
  exact ⟨hle, fun hfd v ↦ inner_mvfderiv_eq_fderiv_of_isLocalExtr hxI (Or.inr hmax') hfd hg v⟩

end LocalGraph

end TauCeti

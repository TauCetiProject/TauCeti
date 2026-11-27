/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.VectorBundle.Orientation.OrientedFrame
public import TauCeti.Topology.VectorBundle.OrthonormalFrame.Reduction.Lift
public import TauCeti.Topology.VectorBundle.OrthonormalFrame.UnitSection
import TauCeti.Analysis.InnerProductSpace.Reflection

/-!
# Positively oriented frames adapted to a unit section

Let `E → B` be an oriented vector bundle with fibre inner products, with orientation `s`, let `o`
be an orientation of the model space `V`, and let `σ` be a section of `E`. The positively oriented
orthonormal frames sending a vector `v₀` of `V` to `σ` form the set
`TauCeti.OrthonormalFrameBundle.orientedSectionFrames s o σ v₀`, the intersection of the
positively oriented frames (`TauCeti.OrthonormalFrameBundle.orientedFrames`) and the frames adapted
to `σ` (`TauCeti.OrthonormalFrameBundle.sectionFrames`). An orthogonal transformation keeps such a
frame in the set exactly when it is special orthogonal and fixes `v₀`
(`TauCeti.OrthonormalFrameBundle.smul_mem_orientedSectionFrames_iff`), so the special orthogonal
stabilizer `SO(N - 1)` of `v₀` (`TauCeti.specialOrthogonalStabilizer`) acts on them on the right,
freely and transitively on fibres.

For `V = ℝᴺ` with `N ≥ 2`, a unit vector `v₀` and a continuous section `σ` of unit vectors, these
frames are locally trivial with fibre `SO(N - 1)`, equivariantly
(`TauCeti.OrthonormalFrameBundle.exists_trivialization_orientedSectionFrames`). Near a point, take
a continuous local adapted frame (from `exists_trivialization_sectionFrames`); where it is not
positively oriented, compose it with a fixed reflection `r` of `ℝᴺ` fixing `v₀`, which exists
since `N ≥ 2` (`TauCeti.exists_det_eq_neg_one_apply_eq_self`). Orientation is locally constant,
so the corrected frame is continuous. Hence the frames form a lift of the orthonormal frame bundle
along `SO(N - 1) ⊆ O(N)` (`TauCeti.OrthonormalFrameBundle.orientedSectionFrameLift`): the
reduction of the structure group to `SO(N - 1)` given by the orientation and the section.

For `N = 3` this is the `SO(2)`-reduction of the tangent bundle of an oriented Riemannian
three-manifold given by a unit vector field, whose orthogonal planes form an oriented plane field.
The hypothesis `N ≥ 2` is needed: in rank one the unique frame adapted to `σ` need not be
positively oriented.

## Main definitions

* `TauCeti.OrthonormalFrameBundle.orientedSectionFrames s o σ v₀`: the positively oriented
  orthonormal frames sending `v₀` to `σ`.
* `TauCeti.OrthonormalFrameBundle.orientedSectionFrameLift`: for a continuous unit section of a
  bundle of rank `N ≥ 2`, these frames as a lift along `SO(N - 1) ⊆ O(N)`.

## Main results

* `TauCeti.OrthonormalFrameBundle.smul_mem_orientedSectionFrames_iff`: an orthogonal
  transformation keeps an oriented adapted frame oriented and adapted exactly when it is special
  orthogonal and fixes `v₀`.
* `TauCeti.OrthonormalFrameBundle.exists_trivialization_orientedSectionFrames`: for a continuous
  unit section in rank `N ≥ 2`, the oriented adapted frames are locally trivial with fibre the
  special orthogonal stabilizer of `v₀`.

## References

* S. Kobayashi, K. Nomizu, *Foundations of Differential Geometry*, Vol. I, Interscience, 1963,
  Chapter I, §5 (reduction of the structure group).
* J. W. Milnor, J. D. Stasheff, *Characteristic Classes*, Annals of Mathematics Studies 76,
  Princeton (1974), §12 (oriented bundles and the structure group `SO(n)`).
-/

public section

noncomputable section

open Bundle Set MulOpposite Module
open scoped Topology

universe w

namespace TauCeti.OrthonormalFrameBundle

section Action

variable {B : Type*} [TopologicalSpace B] {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {E : B → Type*} [∀ x, NormedAddCommGroup (E x)] [∀ x, InnerProductSpace ℝ (E x)]
  [TopologicalSpace (TotalSpace F E)] [FiberBundle F E] [VectorBundle ℝ F E]
  {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] {ι : Type*}
  (s : VectorBundleOrientation F E ι) (o : Orientation ℝ V ι) (σ : ∀ b, E b) (v₀ : V)

/-- The positively oriented orthonormal frames adapted to the section `σ`: those transporting the
orientation `o` of `V` to the orientation `s` of the fibre and sending `v₀` to the value of `σ` at
their base point. -/
def orientedSectionFrames : Set (OrthonormalFrameBundle ℝ F E V) :=
  sectionFrames F σ v₀ ∩ orientedFrames s o

variable {s o σ v₀}

@[simp]
theorem mem_orientedSectionFrames_iff {p : OrthonormalFrameBundle ℝ F E V} :
    p ∈ orientedSectionFrames s o σ v₀ ↔ p.frame v₀ = σ p.proj ∧ p ∈ orientedFrames s o := by
  rw [orientedSectionFrames, mem_inter_iff, mem_sectionFrames_iff]

variable [Fintype ι] [CompleteSpace V]

/-- An orthogonal transformation keeps a positively oriented frame adapted to `σ` positively
oriented and adapted exactly when it is special orthogonal and fixes `v₀`, provided `card ι` is the
dimension of `V`. -/
theorem smul_mem_orientedSectionFrames_iff (hι : Fintype.card ι = finrank ℝ V)
    {p : OrthonormalFrameBundle ℝ F E V} (hp : p ∈ orientedSectionFrames s o σ v₀)
    {g : unitary (V →L[ℝ] V)} :
    op g • p ∈ orientedSectionFrames s o σ v₀ ↔ g ∈ specialOrthogonalStabilizer V v₀ := by
  rw [orientedSectionFrames, mem_inter_iff, smul_mem_sectionFrames_iff hp.1,
    smul_mem_orientedFrames_iff hι hp.2]
  exact Subgroup.mem_inf.symm

/-- The orthogonal transformations carrying a positively oriented frame adapted to `σ` to such a
frame are those of the special orthogonal stabilizer of `v₀`, which therefore acts on these frames
on the right, freely and transitively on fibres. -/
instance [Fact (Fintype.card ι = finrank ℝ V)] :
    SMulMemIff (specialOrthogonalStabilizer V v₀) (orientedSectionFrames s o σ v₀) :=
  ⟨smul_mem_orientedSectionFrames_iff Fact.out⟩

end Action

/-! ### Local triviality -/

section Trivialization

variable {N : ℕ}

variable {B : Type*} [TopologicalSpace B] {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {E : B → Type*} [∀ x, NormedAddCommGroup (E x)] [∀ x, InnerProductSpace ℝ (E x)]
  [TopologicalSpace (TotalSpace F E)] [FiberBundle F E] [VectorBundle ℝ F E]
  [ContinuousFiberNorm F E] {ι : Type*} [Fintype ι]
  [Fact (Fintype.card ι = finrank ℝ (EuclideanSpace ℝ (Fin N)))]
  {s : VectorBundleOrientation F E ι} {o : Orientation ℝ (EuclideanSpace ℝ (Fin N)) ι}
  {σ : ∀ b, E b} {v₀ : EuclideanSpace ℝ (Fin N)}

/-- In dimension `N ≥ 2` some orthogonal transformation of `ℝᴺ` fixes `v₀` and is not special
orthogonal. -/
private theorem exists_apply_eq_self_notMem (hN : 2 ≤ N) (v₀ : EuclideanSpace ℝ (Fin N)) :
    ∃ r : unitary (EuclideanSpace ℝ (Fin N) →L[ℝ] EuclideanSpace ℝ (Fin N)),
      (r : EuclideanSpace ℝ (Fin N) →L[ℝ] EuclideanSpace ℝ (Fin N)) v₀ = v₀ ∧
        r ∉ specialOrthogonalGroup (EuclideanSpace ℝ (Fin N)) := by
  obtain ⟨r, hr, hrv⟩ := exists_det_eq_neg_one_apply_eq_self
    (by rwa [finrank_euclideanSpace_fin]) v₀
  refine ⟨Unitary.linearIsometryEquiv.symm r, by simpa using hrv, ?_⟩
  have hdet : ((Unitary.linearIsometryEquiv.symm r : unitary _) :
      EuclideanSpace ℝ (Fin N) →L[ℝ] EuclideanSpace ℝ (Fin N)).det = -1 := by
    rw [Unitary.coe_symm_linearIsometryEquiv_apply, ContinuousLinearMap.det, ← hr,
      LinearEquiv.coe_det]
    rfl
  rw [notMem_specialOrthogonalGroup_iff_det_neg, hdet]
  norm_num

/-- Near every point there is a continuous local frame that is positively oriented and adapted to
a continuous unit section: a continuous local adapted frame, composed with `r` where it is not
positively oriented. Orientation is locally constant, so the correction is continuous. -/
private theorem exists_continuousOn_mem_orientedSectionFrames
    (hσ : Continuous fun y ↦ (⟨y, σ y⟩ : TotalSpace F E)) (hσ₁ : ∀ y, ‖σ y‖ = 1)
    (hv₀ : ‖v₀‖ = 1) (hN : 2 ≤ N) (hF : finrank ℝ F = N) (x : B) :
    ∃ U : Set B, IsOpen U ∧ x ∈ U ∧
      ∃ q : B → OrthonormalFrameBundle ℝ F E (EuclideanSpace ℝ (Fin N)), ContinuousOn q U ∧
        ∀ y ∈ U, q y ∈ orientedSectionFrames s o σ v₀ ∧ (q y).proj = y := by
  have hι : Fintype.card ι = finrank ℝ (EuclideanSpace ℝ (Fin N)) := Fact.out
  -- A continuous local frame adapted to `σ`.
  obtain ⟨t₁, hx₁, -⟩ := exists_trivialization_sectionFrames (F := F) hσ hσ₁ hv₀ hF x
  obtain ⟨r, hrv, hr⟩ := exists_apply_eq_self_notMem hN v₀
  let s₁ : B → OrthonormalFrameBundle ℝ F E (EuclideanSpace ℝ (Fin N)) := fun y ↦
    (t₁.toOpenPartialHomeomorph.symm (y, 1) : sectionFrames F σ v₀)
  have hs₁S (y : B) : s₁ y ∈ sectionFrames F σ v₀ :=
    (t₁.toOpenPartialHomeomorph.symm (y, 1)).property
  have hs₁ : ContinuousOn s₁ t₁.baseSet :=
    continuous_subtypeVal.comp_continuousOn
      (t₁.toOpenPartialHomeomorph.continuousOn_symm.comp
        (continuousOn_id.prodMk continuousOn_const) fun _ hy ↦ t₁.mem_target.2 hy)
  -- Where the adapted frame is not positively oriented, compose it with `r`.
  classical
  let k : B → unitary (EuclideanSpace ℝ (Fin N) →L[ℝ] EuclideanSpace ℝ (Fin N)) := fun y ↦
    if s₁ y ∈ orientedFrames s o then 1 else r
  have hkS (y : B) : op (k y) • s₁ y ∈ orientedSectionFrames s o σ v₀ := by
    by_cases h : s₁ y ∈ orientedFrames s o
    · simp only [k, h, ↓reduceIte, op_one, one_smul]
      exact ⟨hs₁S y, h⟩
    · simp only [k, h, ite_false]
      refine ⟨(smul_mem_sectionFrames_iff (hs₁S y)).2 hrv, ?_⟩
      by_contra hn
      exact (smul_mem_orientedFrames_iff hι ((notMem_orientedFrames_iff hι).1 h)).not.2 hr
        ((notMem_orientedFrames_iff hι).1 hn)
  -- Orientation is locally constant, so `k` is locally constant.
  have hk : ContinuousOn k t₁.baseSet := fun y hy ↦ by
    have hs₁y : ContinuousAt s₁ y := hs₁.continuousAt (t₁.open_baseSet.mem_nhds hy)
    refine ((continuousAt_const (y := k y)).congr ?_).continuousWithinAt
    by_cases h : s₁ y ∈ orientedFrames s o
    · filter_upwards [hs₁y.preimage_mem_nhds ((isOpen_orientedFrames hι).mem_nhds h)] with z hz
      simp only [k, h, mem_preimage.1 hz, ↓reduceIte]
    · have h' := (notMem_orientedFrames_iff hι).1 h
      filter_upwards [hs₁y.preimage_mem_nhds ((isOpen_orientedFrames hι).mem_nhds h')] with z hz
      simp only [k, h, (notMem_orientedFrames_iff hι).2 (mem_preimage.1 hz), ↓reduceIte]
  exact ⟨t₁.baseSet, t₁.open_baseSet, hx₁, fun y ↦ op (k y) • s₁ y,
    (continuous_op.comp_continuousOn hk).smul hs₁,
    fun y hy ↦ ⟨hkS y, t₁.proj_symm_apply' hy⟩⟩

/-- **The positively oriented frames adapted to a continuous unit section are locally trivial.**
For a bundle of rank `N ≥ 2` with continuous fibre norms, a continuous section `σ` of unit vectors
and a unit vector `v₀` of `ℝᴺ`, the positively oriented orthonormal frames sending `v₀` to `σ` are
locally trivial with fibre the special orthogonal stabilizer `SO(N - 1)` of `v₀`, by
trivializations equivariant for its right action. -/
theorem exists_trivialization_orientedSectionFrames
    (hσ : Continuous fun y ↦ (⟨y, σ y⟩ : TotalSpace F E)) (hσ₁ : ∀ y, ‖σ y‖ = 1)
    (hv₀ : ‖v₀‖ = 1) (hN : 2 ≤ N) (hF : finrank ℝ F = N) (x : B) :
    ∃ t : Trivialization (specialOrthogonalStabilizer (EuclideanSpace ℝ (Fin N)) v₀)
        (fun p : orientedSectionFrames s o σ v₀ ↦
          (p : OrthonormalFrameBundle ℝ F E (EuclideanSpace ℝ (Fin N))).proj),
      x ∈ t.baseSet ∧ ∀ (g : specialOrthogonalStabilizer (EuclideanSpace ℝ (Fin N)) v₀)
        (p : orientedSectionFrames s o σ v₀)
        (hgp : op (g : unitary (EuclideanSpace ℝ (Fin N) →L[ℝ] EuclideanSpace ℝ (Fin N))) •
          (p : OrthonormalFrameBundle ℝ F E (EuclideanSpace ℝ (Fin N))) ∈
            orientedSectionFrames s o σ v₀),
        (p : OrthonormalFrameBundle ℝ F E (EuclideanSpace ℝ (Fin N))).proj ∈ t.baseSet →
          t ⟨_, hgp⟩ = ((t p).1, (t p).2 * g) := by
  have : FiniteDimensional ℝ F := Module.finite_of_finrank_pos (by omega)
  obtain ⟨U, hU, hxU, q, hq, hqS⟩ :=
    exists_continuousOn_mem_orientedSectionFrames (s := s) (o := o) hσ hσ₁ hv₀ hN hF x
  -- The orthonormal frame bundle trivialized near `x`.
  obtain ⟨T, hxT, hT⟩ := exists_trivialization (𝕜 := ℝ) (F := F) (E := E)
    (V := EuclideanSpace ℝ (Fin N)) (finrank_euclideanSpace_fin.trans hF.symm) x
  have : T.orthonormalFrameBundleFiber.IsEquivariant :=
    T.isEquivariant_orthonormalFrameBundleFiber_iff.2 fun p _ g ↦ congrArg Prod.snd (hT g p)
  have he (g : unitary (EuclideanSpace ℝ (Fin N) →L[ℝ] EuclideanSpace ℝ (Fin N)))
      (p : OrthonormalFrameBundle ℝ F E (EuclideanSpace ℝ (Fin N))) (_ : p.proj ∈ T.baseSet) :
      (T (op g • p)).2 = (T p).2 * g :=
    congrArg Prod.snd (hT g p)
  -- The local frame of `T`, acted on by the coordinate of `q`, is `q`.
  have hcS (y : B) (hy : y ∈ T.baseSet ∩ U) :
      op (T (q y)).2 • T.toOpenPartialHomeomorph.symm (y, 1) ∈
        orientedSectionFrames s o σ v₀ := by
    have h := T.op_snd_smul_symm_one (fun _ _ ↦ rfl) he (p := q y)
      (by rw [(hqS y hy.2).2]; exact hy.1)
    rw [(hqS y hy.2).2] at h
    rw [h]
    exact (hqS y hy.2).1
  have hc : ContinuousOn (fun y ↦ (T (q y)).2) (T.baseSet ∩ U) :=
    continuous_snd.comp_continuousOn
      (T.toOpenPartialHomeomorph.continuousOn.comp (f := q) (hq.mono inter_subset_right)
        fun y (hy : y ∈ T.baseSet ∩ U) ↦ T.mem_source.2 (by rw [(hqS y hy.2).2]; exact hy.1))
  obtain ⟨t, ht, hteq⟩ := exists_trivialization_of_continuousOn_smul_mem (T := T)
    (H := specialOrthogonalStabilizer _ v₀) (S := orientedSectionFrames s o σ v₀)
    inter_subset_left hcS (T.open_baseSet.inter hU) hc ⟨hxT, hxU⟩
  exact ⟨t, ht ▸ ⟨hxT, hxU⟩, fun g p hgp hp ↦ hteq g p hgp (ht ▸ hp)⟩

end Trivialization

/-! ### The reduction as a lift of the orthonormal frame bundle -/

section Lift

variable {X : Type*} [TopologicalSpace X] {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {E : X → Type w} [∀ x, NormedAddCommGroup (E x)] [∀ x, InnerProductSpace ℝ (E x)]
  [TopologicalSpace (TotalSpace F E)] [FiberBundle F E] [VectorBundle ℝ F E]
  [ContinuousFiberNorm F E] {N : ℕ} {ι : Type*} [Fintype ι]
  [Fact (Fintype.card ι = finrank ℝ (EuclideanSpace ℝ (Fin N)))]
  {σ : ∀ x, E x} {v₀ : EuclideanSpace ℝ (Fin N)}

variable (s : VectorBundleOrientation F E ι) (o : Orientation ℝ (EuclideanSpace ℝ (Fin N)) ι)

/-- **The positively oriented frames adapted to a unit section** of an oriented bundle of rank
`N ≥ 2`, as a lift of the orthonormal frame bundle along `SO(N - 1) ⊆ O(N)`, where `SO(N - 1)` is
the special orthogonal stabilizer of the unit vector `v₀`: the reduction of the structure group to
`SO(N - 1)` given by the orientation and the section. -/
@[expose] def orientedSectionFrameLift
    (hσ : Continuous fun x ↦ (⟨x, σ x⟩ : TotalSpace F E)) (hσ₁ : ∀ x, ‖σ x‖ = 1)
    (hv₀ : ‖v₀‖ = 1) (hN : 2 ≤ N) (hF : finrank ℝ F = N) :
    OrthonormalFrameLift F E N (specialOrthogonalStabilizer (EuclideanSpace ℝ (Fin N)) v₀)
      ((euclideanLinearEquivHom ℝ (Fin N)).comp
        (specialOrthogonalStabilizer (EuclideanSpace ℝ (Fin N)) v₀).subtype) :=
  reductionLift <| isLocallyTrivialReduction_iff.2 <|
    exists_trivialization_orientedSectionFrames (s := s) (o := o) hσ hσ₁ hv₀ hN hF

variable (hσ : Continuous fun x ↦ (⟨x, σ x⟩ : TotalSpace F E)) (hσ₁ : ∀ x, ‖σ x‖ = 1)
  (hv₀ : ‖v₀‖ = 1) (hN : 2 ≤ N) (hF : finrank ℝ F = N)

@[simp]
theorem orientedSectionFrameLift_P :
    (orientedSectionFrameLift s o hσ hσ₁ hv₀ hN hF).P =
      ReductionFiber (orientedSectionFrames s o σ v₀) :=
  (rfl)

/-- The frame of a point of the reduction is that oriented adapted frame itself. -/
@[simp]
theorem orientedSectionFrameLift_toFrame
    (p : TotalSpace (specialOrthogonalStabilizer (EuclideanSpace ℝ (Fin N)) v₀)
      (ReductionFiber (orientedSectionFrames s o σ v₀))) :
    (orientedSectionFrameLift s o hσ hσ₁ hv₀ hN hF).toFrame p = ⟨p.proj, p.snd.val.frame⟩ :=
  (rfl)

end Lift

end TauCeti.OrthonormalFrameBundle

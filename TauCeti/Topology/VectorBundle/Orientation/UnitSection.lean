/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.VectorBundle.Orientation.OrientedFrame
public import TauCeti.Topology.VectorBundle.OrthonormalFrame.Reduction.Lift
public import TauCeti.Topology.VectorBundle.OrthonormalFrame.UnitSection

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
(`TauCeti.OrthonormalFrameBundle.isLocallyTrivialReduction_orientedSectionFrames`). The frames
adapted to `σ` are locally trivial with fibre the stabilizer `O(N - 1)` of `v₀`
(`exists_trivialization_sectionFrames`), and a fixed reflection `r` of `ℝᴺ` fixing `v₀`, which
exists since `N ≥ 2` (`Unitary.exists_det_eq_neg_one_apply_eq_self`), corrects a local adapted
frame into the positively oriented ones
(`TauCeti.OrthonormalFrameBundle.isLocallyTrivialReduction_inter_orientedFrames`). Hence the
frames form a lift of the orthonormal frame bundle along `SO(N - 1) ⊆ O(N)`
(`TauCeti.OrthonormalFrameBundle.orientedSectionFrameLift`): the reduction of the structure group
to `SO(N - 1)` given by the orientation and the section.

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
* `TauCeti.OrthonormalFrameBundle.isLocallyTrivialReduction_orientedSectionFrames`: for a
  continuous unit section in rank `N ≥ 2`, the oriented adapted frames are a locally trivial
  reduction to the special orthogonal stabilizer of `v₀`.

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
    smul_mem_orientedFrames_iff hι hp.2, mem_specialOrthogonalStabilizer_iff,
    ← mem_specialOrthogonalGroup_iff, MulAction.mem_stabilizer_iff, Submonoid.smul_def,
    ContinuousLinearMap.smul_def]

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
  (s : VectorBundleOrientation F E ι) (o : Orientation ℝ (EuclideanSpace ℝ (Fin N)) ι)
  {σ : ∀ b, E b} {v₀ : EuclideanSpace ℝ (Fin N)}

/-- **The positively oriented frames adapted to a continuous unit section are locally trivial.**
For a bundle of rank `N ≥ 2` with continuous fibre norms, a continuous section `σ` of unit vectors
and a unit vector `v₀` of `ℝᴺ`, the positively oriented orthonormal frames sending `v₀` to `σ` are
a locally trivial reduction to the special orthogonal stabilizer `SO(N - 1)` of `v₀`. The frames
adapted to `σ` are a locally trivial reduction to the stabilizer of `v₀`, which contains a
reflection of determinant `-1` since `N ≥ 2`
(`Unitary.exists_det_eq_neg_one_apply_eq_self`). -/
theorem isLocallyTrivialReduction_orientedSectionFrames
    (hσ : Continuous fun y ↦ (⟨y, σ y⟩ : TotalSpace F E)) (hσ₁ : ∀ y, ‖σ y‖ = 1)
    (hv₀ : ‖v₀‖ = 1) (hN : 2 ≤ N) (hF : finrank ℝ F = N) :
    IsLocallyTrivialReduction
      (proj : OrthonormalFrameBundle ℝ F E (EuclideanSpace ℝ (Fin N)) → B)
      (specialOrthogonalStabilizer (EuclideanSpace ℝ (Fin N)) v₀)
      (orientedSectionFrames s o σ v₀) := by
  have : FiniteDimensional ℝ F := Module.finite_of_finrank_pos (by omega)
  have hS : IsLocallyTrivialReduction
      (proj : OrthonormalFrameBundle ℝ F E (EuclideanSpace ℝ (Fin N)) → B)
      (MulAction.stabilizer _ v₀) (sectionFrames F σ v₀) :=
    isLocallyTrivialReduction_iff.2 fun x ↦ by
      obtain ⟨t, hxt, ht⟩ := exists_trivialization_sectionFrames hσ hσ₁ hv₀ hF x
      exact ⟨t, hxt, fun g p hgp hp ↦ SMulMemIff.smul_eq_mk g p hgp ▸ ht g p hp⟩
  -- A reflection fixing `v₀` reverses orientation.
  obtain ⟨r, hr, hrv⟩ := Unitary.exists_det_eq_neg_one_apply_eq_self
    (by rwa [finrank_euclideanSpace_fin]) v₀
  rw [specialOrthogonalStabilizer_def]
  exact isLocallyTrivialReduction_inter_orientedFrames s o hS (MulAction.mem_stabilizer_iff.2 hrv)
    (notMem_specialOrthogonalGroup_iff_det_neg.2 (by rw [hr]; norm_num))

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
  reductionLift (isLocallyTrivialReduction_orientedSectionFrames s o hσ hσ₁ hv₀ hN hF)

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

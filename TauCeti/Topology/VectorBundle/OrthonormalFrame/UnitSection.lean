/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Matrix.SpecialOrthogonal
public import TauCeti.Topology.VectorBundle.OrthonormalFrame.Reduction.Basic

/-!
# Orthonormal frames adapted to a unit section

Let `E → B` be a vector bundle with fibre inner products and `σ` a section of `E`. For a vector
`v₀` of the model space `V`, an orthonormal frame `φ : V ≃ₗᵢ[ℝ] E b` is *adapted to `σ`* when it
sends `v₀` to `σ b`. The adapted frames form the set
`TauCeti.OrthonormalFrameBundle.sectionFrames F σ v₀`. An orthogonal transformation `g` of `V`
keeps an adapted frame adapted exactly when it fixes `v₀`
(`TauCeti.OrthonormalFrameBundle.smul_mem_sectionFrames_iff`), so the stabilizer of `v₀` in the
orthogonal group acts on the adapted frames on the right, freely and transitively on fibres
(`TauCeti.OrthonormalFrameBundle.SMulMemIff`).

For `V = ℝᴺ`, a unit vector `v₀` and a continuous section `σ` of unit vectors of a bundle of rank
`N` with continuous fibre norms, the adapted frames are locally trivial with fibre the stabilizer
`O(N - 1)` of `v₀`, equivariantly for its action
(`TauCeti.OrthonormalFrameBundle.exists_trivialization_sectionFrames`). Over the base set of a
local Gram–Schmidt frame `τ`, the section read in that frame is a continuous unit vector
`u y = τ_y⁻¹ (σ y)`, and composing `τ_y` with a rotation taking `v₀` to `u y` adapts it. The
rotation `TauCeti.sphereRotation v₀ (u y)` depends continuously on `u y` away from `-v₀`; near a
point where `u = -v₀`, compose instead the rotation taking `-v₀` to `u y` with `-1`.

This is the reduction of the structure group used to restrict structures along a boundary: for
`E = W ⊕ ℝ` with the unit section of the trivial summand, and `v₀` the last basis vector of
`ℝᴺ`, the adapted frames are the frames of `W ⊕ ℝ` coming from frames of `W`.

## Main definitions

* `TauCeti.OrthonormalFrameBundle.sectionFrames F σ v₀`: the orthonormal frames sending `v₀` to
  the section `σ`.
* The instance `TauCeti.OrthonormalFrameBundle.SMulMemIff (MulAction.stabilizer _ v₀)
  (sectionFrames F σ v₀)`.

## Main results

* `TauCeti.OrthonormalFrameBundle.smul_mem_sectionFrames_iff`: an orthogonal transformation keeps
  an adapted frame adapted exactly when it fixes `v₀`.
* `TauCeti.OrthonormalFrameBundle.exists_trivialization_sectionFrames`: for a continuous unit
  section, the adapted frames are locally trivial with fibre the stabilizer of `v₀`.

## References

* S. Kobayashi, K. Nomizu, *Foundations of Differential Geometry*, Vol. I, Interscience, 1963,
  Chapter I, §5 (reduction of the structure group).
* H. B. Lawson, M.-L. Michelsohn, *Spin Geometry*, Princeton University Press, 1989, Chapter II,
  §2 (restriction of Spin structures to hypersurfaces).
-/

public section

noncomputable section

open Bundle Set MulOpposite Module Metric
open scoped Topology

namespace TauCeti.OrthonormalFrameBundle

section Action

variable {B : Type*} (F : Type*) {E : B → Type*} [∀ x, NormedAddCommGroup (E x)]
  [∀ x, InnerProductSpace ℝ (E x)] {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  (σ : ∀ b, E b) (v₀ : V)

/-- The orthonormal frames adapted to the section `σ`: those sending `v₀` to the value of `σ` at
their base point. -/
def sectionFrames : Set (OrthonormalFrameBundle ℝ F E V) :=
  {p | p.frame v₀ = σ p.proj}

variable {F σ v₀}

@[simp]
theorem mem_sectionFrames_iff {p : OrthonormalFrameBundle ℝ F E V} :
    p ∈ sectionFrames F σ v₀ ↔ p.frame v₀ = σ p.proj :=
  Iff.rfl

/-- The frame `φ` over `y` is adapted to `σ` when it sends `v₀` to `σ y`. -/
theorem mk_mem_sectionFrames_iff {y : B} {φ : V ≃ₗᵢ[ℝ] E y} :
    (⟨y, φ⟩ : OrthonormalFrameBundle ℝ F E V) ∈ sectionFrames F σ v₀ ↔ φ v₀ = σ y :=
  Iff.rfl

variable [CompleteSpace V]

/-- An orthogonal transformation keeps a frame adapted to `σ` adapted exactly when it fixes
`v₀`. -/
theorem smul_mem_sectionFrames_iff {p : OrthonormalFrameBundle ℝ F E V}
    (hp : p ∈ sectionFrames F σ v₀) {g : unitary (V →L[ℝ] V)} :
    op g • p ∈ sectionFrames F σ v₀ ↔ g ∈ MulAction.stabilizer (unitary (V →L[ℝ] V)) v₀ := by
  simp only [mem_sectionFrames_iff, frame_smul_apply, proj_smul, unop_op]
  rw [← hp, p.frame.injective.eq_iff, MulAction.mem_stabilizer_iff, Submonoid.smul_def,
    ContinuousLinearMap.smul_def]

/-- The orthogonal transformations carrying a frame adapted to `σ` to an adapted frame are those
fixing `v₀`, which therefore act on the adapted frames on the right, freely and transitively on
fibres. -/
instance : SMulMemIff (MulAction.stabilizer (unitary (V →L[ℝ] V)) v₀) (sectionFrames F σ v₀) :=
  ⟨smul_mem_sectionFrames_iff⟩

end Action

/-! ### Local triviality -/

section Trivialization

variable {N : ℕ}

variable {B : Type*} [TopologicalSpace B] {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {E : B → Type*} [∀ x, NormedAddCommGroup (E x)] [∀ x, InnerProductSpace ℝ (E x)]
  [TopologicalSpace (TotalSpace F E)] [FiberBundle F E] [VectorBundle ℝ F E]
  [ContinuousFiberNorm F E] {σ : ∀ b, E b} {v₀ : EuclideanSpace ℝ (Fin N)}

/-- Over an open set on which a continuous correction `c` sends `v₀` to the section read in the
local Gram–Schmidt frame of `e`, the adapted frames are trivial. -/
private theorem exists_trivialization_of_correction (e : Trivialization F (π F E)) [e.IsLinear ℝ]
    (cF : Module.Basis (Fin N) ℝ F) {U : Set B} (hUe : U ⊆ e.baseSet) (hU : IsOpen U)
    {c : B → unitary (EuclideanSpace ℝ (Fin N) →L[ℝ] EuclideanSpace ℝ (Fin N))}
    (hc : ContinuousOn c U)
    (hcv : ∀ y ∈ U, (c y : EuclideanSpace ℝ (Fin N) →L[ℝ] EuclideanSpace ℝ (Fin N)) v₀ =
      (e.orthonormalFrameAt cF (EuclideanSpace.basisFun (Fin N) ℝ) y).symm (σ y))
    {x : B} (hx : x ∈ U) :
    ∃ t : Trivialization (MulAction.stabilizer
          (unitary (EuclideanSpace ℝ (Fin N) →L[ℝ] EuclideanSpace ℝ (Fin N))) v₀)
        (fun p : sectionFrames F σ v₀ ↦
          (p : OrthonormalFrameBundle ℝ F E (EuclideanSpace ℝ (Fin N))).proj),
      x ∈ t.baseSet ∧ ∀ g (p : sectionFrames F σ v₀),
        (p : OrthonormalFrameBundle ℝ F E (EuclideanSpace ℝ (Fin N))).proj ∈ t.baseSet →
          t (op g • p) = ((t p).1, (t p).2 * g) := by
  obtain ⟨t, ht, hteq⟩ := exists_trivialization_of_continuousOn_smul_mem
    (T := e.orthonormalFrameBundle cF (EuclideanSpace.basisFun (Fin N) ℝ))
    (H := MulAction.stabilizer _ v₀) (S := sectionFrames F σ v₀)
    (fun _ hy ↦ (e.baseSet_orthonormalFrameBundle cF
      (EuclideanSpace.basisFun (Fin N) ℝ)).symm ▸ hUe hy) (fun y hy ↦ by
      simp only [e.orthonormalFrameBundle_symm_apply' cF, op_one, one_smul, mem_sectionFrames_iff,
        frame_smul_apply, proj_smul, unop_op, hcv y hy, LinearIsometryEquiv.apply_symm_apply])
    hU hc hx
  exact ⟨t, ht ▸ hx, fun g p hp ↦
    SMulMemIff.apply_smul_eq_of_apply_mk_eq fun hgp ↦ hteq g p hgp (ht ▸ hp)⟩

/-- **The frames adapted to a continuous unit section are locally trivial.** For a bundle of rank
`N` with continuous fibre norms, a continuous section `σ` of unit vectors and a unit vector `v₀`
of `ℝᴺ`, the orthonormal frames sending `v₀` to `σ` are locally trivial with fibre the stabilizer
`O(N - 1)` of `v₀`, by trivializations equivariant for its right action. -/
theorem exists_trivialization_sectionFrames
    (hσ : Continuous fun y ↦ (⟨y, σ y⟩ : TotalSpace F E)) (hσ₁ : ∀ y, ‖σ y‖ = 1)
    (hv₀ : ‖v₀‖ = 1) (hF : finrank ℝ F = N) (x : B) :
    ∃ t : Trivialization (MulAction.stabilizer
          (unitary (EuclideanSpace ℝ (Fin N) →L[ℝ] EuclideanSpace ℝ (Fin N))) v₀)
        (fun p : sectionFrames F σ v₀ ↦
          (p : OrthonormalFrameBundle ℝ F E (EuclideanSpace ℝ (Fin N))).proj),
      x ∈ t.baseSet ∧ ∀ g (p : sectionFrames F σ v₀),
        (p : OrthonormalFrameBundle ℝ F E (EuclideanSpace ℝ (Fin N))).proj ∈ t.baseSet →
          t (op g • p) = ((t p).1, (t p).2 * g) := by
  have hN : 0 < N := by
    by_contra h0
    obtain rfl : N = 0 := by omega
    rw [Subsingleton.elim v₀ 0, norm_zero] at hv₀
    exact zero_ne_one hv₀
  have : FiniteDimensional ℝ F := Module.finite_of_finrank_pos (hF ▸ hN)
  let e := trivializationAt F E x
  let cF := Module.finBasisOfFinrankEq ℝ F hF
  let τ := e.orthonormalFrameAt cF (EuclideanSpace.basisFun (Fin N) ℝ)
  -- The section read in the local frame, as a point of the unit sphere.
  let u : B → sphere (0 : EuclideanSpace ℝ (Fin N)) 1 := fun y ↦
    ⟨(τ y).symm (σ y), by rw [mem_sphere_zero_iff_norm, LinearIsometryEquiv.norm_map, hσ₁]⟩
  have hu : ContinuousOn u e.baseSet :=
    Topology.IsInducing.subtypeVal.continuousOn_iff.2
      ((e.continuousOn_orthonormalFrameAt_symm cF (EuclideanSpace.basisFun (Fin N) ℝ)).comp
        hσ.continuousOn fun _ hy ↦ hy)
  let b : sphere (0 : EuclideanSpace ℝ (Fin N)) 1 := ⟨v₀, by rwa [mem_sphere_zero_iff_norm]⟩
  have hx := mem_baseSet_trivializationAt F E x
  by_cases hux : u x = -b
  · -- Near `x`, compose the rotation taking `-v₀` to `u` with `-1`.
    have hb : -b ≠ b := (ne_neg_of_mem_unit_sphere ℝ b).symm
    refine exists_trivialization_of_correction e cF (U := e.baseSet ∩ u ⁻¹' {-(-b)}ᶜ)
      inter_subset_left (hu.isOpen_inter_preimage e.open_baseSet isOpen_compl_singleton)
      (c := fun y ↦ sphereRotationUnitary (-b) (u y) * -1)
      (((continuousOn_sphereRotationUnitary (-b)).comp (hu.mono inter_subset_left)
        fun _ hy ↦ hy.2).mul continuousOn_const)
      (fun y hy ↦ ?_) ⟨hx, by simpa [hux] using hb⟩
    have := sphereRotationUnitary_apply_of_ne hy.2
    simp only [coe_neg_sphere] at this
    simpa [u, b, Unitary.coe_neg] using this
  · -- Near `x`, the rotation taking `v₀` to `u` adapts the local frame.
    refine exists_trivialization_of_correction e cF (U := e.baseSet ∩ u ⁻¹' {-b}ᶜ)
      inter_subset_left (hu.isOpen_inter_preimage e.open_baseSet isOpen_compl_singleton)
      (c := fun y ↦ sphereRotationUnitary b (u y))
      ((continuousOn_sphereRotationUnitary b).comp (hu.mono inter_subset_left) fun _ hy ↦ hy.2)
      (fun y hy ↦ ?_) ⟨hx, hux⟩
    simpa [u, b] using sphereRotationUnitary_apply_of_ne hy.2

end Trivialization

end TauCeti.OrthonormalFrameBundle

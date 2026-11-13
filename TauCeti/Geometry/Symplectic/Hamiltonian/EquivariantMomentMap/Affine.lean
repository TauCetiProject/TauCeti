/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Hamiltonian.EquivariantMomentMap.Basic
public import TauCeti.RepresentationTheory.Affine

/-!
# The affine coadjoint action of a moment map

For a symplectic group action on a preconnected manifold, the equivariance defect
`θ(g) = μ(g • x₀) - Ad*_g μ(x₀)` of an infinitesimal moment map is independent of `x₀`
and is a group cocycle. We use it to construct an actual `MulAction` on the algebraic
dual of the Lie algebra, with formula `g • ν = Ad*_g ν + θ(g)`.

The moment map is equivariant for this action, even if the group is disconnected.
Changing its normalization by a constant conjugates the affine action by translation.
In particular, `μ - ν` is coadjoint-equivariant exactly when `ν` is fixed by the affine
action. Thus the action, rather than just its infinitesimal cocycle, records the obstruction
to an equivariant normalization.

The construction is algebraic; the identity derivative of the defect is computed by
`IsMomentMap.mvfderiv_momentDefect_one` in `EquivariantMomentMap.Basic`. No topology on the
algebraic dual is installed here, nor is the affine action a global instance.

## References

* Jerrold Marsden and Tudor Ratiu, *Introduction to Mechanics and Symmetry*, second edition,
  §§11.4 and 12.3 (the nonequivariance cocycle and affine coadjoint action).
-/

public section

noncomputable section

open scoped Manifold ContDiff

namespace TauCeti.SmoothTwoForm.IsMomentMap

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [LieGroup I (minSmoothness ℝ 3) G]
  {E' H' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [CompleteSpace E']
  [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H' M] [IsManifold I' ∞ M]
  [PreconnectedSpace M] [MulAction G M] [ContMDiffSMul I I' ∞ G M]
  {σ : SmoothTwoForm I' M} {μ : M → Module.Dual ℝ (GroupLieAlgebra I G)}
  (h : σ.IsMomentMap (InfinitesimalAction.fundamental I G I' M) μ)
  (hσ : ∀ g : G, SmoothForm.mpullback (fun x : M ↦ g • x)
    (ContMDiffSMul.contMDiff_const_smul (I := I) g) σ = σ)

attribute [local instance] lieGroupOne

/-- The affine coadjoint action for which `μ` is equivariant. The basepoint only evaluates
its point-independent defect; `affineCoadjointAction_eq` shows the action is independent of it.
Install this action locally, not alongside a linear coadjoint action on the same carrier. -/
@[instance_reducible]
def affineCoadjointAction (x₀ : M) : MulAction G (Module.Dual ℝ (GroupLieAlgebra I G)) :=
  (Lie.coadjointRepresentation ℝ I G).affineMulAction (fun g ↦ momentDefect μ g x₀)
    (fun g k ↦ (h.momentDefect_mul_eq (hσ g) k x₀).trans (add_comm _ _))

/-- The affine coadjoint action is the affine action of the moment-defect cocycle. -/
theorem affineCoadjointAction_def (x₀ : M) :
    h.affineCoadjointAction hσ x₀ =
      (Lie.coadjointRepresentation ℝ I G).affineMulAction (fun g ↦ momentDefect μ g x₀)
        (fun g k ↦ (h.momentDefect_mul_eq (hσ g) k x₀).trans (add_comm _ _)) :=
  (rfl)

/-- The action is the coadjoint representation plus the moment-map defect. -/
@[simp high]
theorem affineCoadjointAction_smul (x₀ : M) (g : G)
    (ν : Module.Dual ℝ (GroupLieAlgebra I G)) :
    letI := h.affineCoadjointAction hσ x₀
    g • ν = Lie.coadjointRepresentation ℝ I G g ν + momentDefect μ g x₀ :=
  Representation.affineMulAction_smul _ _ _ g ν

/-- Differences transform by the linear coadjoint representation. -/
theorem affineCoadjointAction_smul_sub_smul (x₀ : M) (g : G)
    (ν ν' : Module.Dual ℝ (GroupLieAlgebra I G)) :
    letI := h.affineCoadjointAction hσ x₀
    g • ν - g • ν' = Lie.coadjointRepresentation ℝ I G g (ν - ν') := by
  rw [affineCoadjointAction_def]
  exact Representation.affineMulAction_smul_sub_smul _ _ _ g ν ν'

/-- A covector is fixed exactly when the moment defect is its coadjoint coboundary. -/
theorem affineCoadjointAction_smul_eq_self_iff (x₀ : M) (g : G)
    (ν : Module.Dual ℝ (GroupLieAlgebra I G)) :
    letI := h.affineCoadjointAction hσ x₀
    g • ν = ν ↔ momentDefect μ g x₀ = ν - Lie.coadjointRepresentation ℝ I G g ν := by
  rw [affineCoadjointAction_def]
  exact Representation.affineMulAction_smul_eq_self_iff _ _ _ g ν

/-- The affine coadjoint action does not depend on the chosen point. -/
theorem affineCoadjointAction_eq (x₀ x₁ : M) :
    h.affineCoadjointAction hσ x₀ = h.affineCoadjointAction hσ x₁ := by
  apply MulAction.ext
  funext g ν
  exact (h.affineCoadjointAction_smul hσ x₀ g ν).trans
    ((congrArg (Lie.coadjointRepresentation ℝ I G g ν + ·)
      (h.momentDefect_eq (hσ g) x₀ x₁)).trans
      (h.affineCoadjointAction_smul hσ x₁ g ν).symm)

/-- An infinitesimal moment map is equivariant for its affine coadjoint action, with no
connectedness assumption on the group. -/
theorem apply_smul_affineCoadjointAction (x₀ : M) (g : G) (x : M) :
    letI := h.affineCoadjointAction hσ x₀
    μ (g • x) = g • μ x := by
  rw [affineCoadjointAction_smul]
  exact h.apply_smul_eq_add_momentDefect (hσ g) x x₀

/-- Shifting a moment map by a constant conjugates its affine coadjoint action by the
same translation. -/
theorem affineCoadjointAction_add_const_smul_add (x₀ : M)
    (c ν : Module.Dual ℝ (GroupLieAlgebra I G)) (g : G) :
    (letI := (h.add_const c).affineCoadjointAction hσ x₀; g • (ν + c)) =
      (letI := h.affineCoadjointAction hσ x₀; g • ν) + c := by
  rw [affineCoadjointAction_def, affineCoadjointAction_def]
  apply Representation.affineMulAction_smul_add
  rw [momentDefect_add_const]
  abel

/-- A normalization `μ - ν` is coadjoint-equivariant exactly when `ν` is a global fixed
point of the affine coadjoint action. This tests all components of the group. -/
theorem isEquivariantMomentMap_sub_const_iff (x₀ : M)
    (ν : Module.Dual ℝ (GroupLieAlgebra I G)) :
    letI := h.affineCoadjointAction hσ x₀
    σ.IsEquivariantMomentMap (fun x ↦ μ x - ν) ↔ ∀ g : G, g • ν = ν := by
  have hm : σ.IsMomentMap (InfinitesimalAction.fundamental I G I' M) (fun x ↦ μ x - ν) := by
    simpa only [sub_eq_add_neg] using h.add_const (-ν)
  rw [hm.isEquivariantMomentMap_iff hσ x₀]
  apply forall_congr'
  intro g
  rw [h.affineCoadjointAction_smul_eq_self_iff hσ x₀, map_sub,
    h.apply_smul_eq_add_momentDefect (hσ g) x₀ x₀]
  rw [sub_eq_sub_iff_add_eq_add, add_assoc, add_left_cancel_iff, eq_sub_iff_add_eq]

end TauCeti.SmoothTwoForm.IsMomentMap

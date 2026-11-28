/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.GroupAction.LocallyFree
public import TauCeti.Geometry.Symplectic.Hamiltonian.MomentMap.Level
import TauCeti.Geometry.Lie.Adjoint.Basic
import TauCeti.Geometry.Symplectic.Hamiltonian.MomentMap.Critical
import TauCeti.Geometry.Symplectic.Manifold.Invariants
import TauCeti.Topology.Algebra.ConstMulAction
import TauCeti.LinearAlgebra.BilinearForm.Isometry.FiniteOrder

/-!
# Locally free points of a symplectic toric manifold are free

Let a compact commutative Lie group `G` with Lie algebra `𝔤`, such as a torus, act smoothly and
effectively on a compact connected symplectic manifold `(M, σ)` without boundary, preserving `σ`,
with moment map `μ : M → 𝔤*`, and suppose that `dim M = 2 dim G`. So `(M, σ, μ)` is a symplectic
toric manifold. This file proves that wherever the action is locally free, it is free: if the
isotropy algebra `𝔤_x = {ξ | ξ_M(x) = 0}` is trivial, then so is the stabilizer `G_x`
(`TauCeti.SmoothTwoForm.IsMomentMap.stabilizer_eq_bot_of_isotropy_eq_bot`).

The argument is linear algebra at `x`.

* **The orbit is Lagrangian.** On a compact manifold the cocycle of a moment map of an abelian Lie
  algebra vanishes (`TauCeti.SmoothTwoForm.IsMomentMap.momentCocycle_eq_zero_of_isLieAbelian`):
  it is constant, and at a maximum `p` of `μ^ξ` it is `σ_p(ξ_M, η_M) = dμ^ξ_p(η_M) = 0`. So the
  orbit tangent space `L = 𝔤 · x` is isotropic, and as `𝔤_x = 0` it has dimension
  `dim G = ½ dim M`, so it is Lagrangian.
* **The stabilizer acts on `T_x M` with finite order, preserving `σ_x` and fixing `L`.** The
  stabilizer is a closed subgroup of the compact group `G` with trivial Lie algebra `𝔤_x`, so it is
  finite. Since `G` is commutative, the differential `dg_x` of an element `g ∈ G_x` sends `ξ_M(x)`
  to `(Ad_g ξ)_M(x) = ξ_M(x)`.
* **Hence `dg_x = 1`.** A linear isometry of finite order fixing a Lagrangian subspace pointwise is
  the identity (`LinearMap.IsOrthogonal.eq_one_of_isOfFinOrder`). For an effective action on a
  connected manifold, an element of a finite stabilizer with `dg_x = 1` is `1`
  (`TauCeti.injective_tangentRepresentation`).

By the moment-map differential identity, `𝔤_x = 0` exactly when `dμ_x` is surjective, so the action
is free exactly over the regular points of `μ`
(`TauCeti.SmoothTwoForm.IsMomentMap.stabilizer_eq_bot_iff_differential_surjective`), and it is free
on a dense open set
(`TauCeti.SmoothTwoForm.IsMomentMap.exists_isOpen_dense_forall_stabilizer_eq_bot`).

Without `dim M = 2 dim G` this fails. The circle acting on `ℂP²` by
`t • [z₀ : z₁ : z₂] = [z₀ : t z₁ : t² z₂]` is Hamiltonian and locally free at `[1 : 0 : 1]`, which
is not fixed, but `-1` fixes that point.

## Main results

All declarations are in the namespace `TauCeti.SmoothTwoForm.IsMomentMap`.

* `stabilizer_eq_bot_of_isotropy_eq_bot`, `stabilizer_eq_bot_iff_isotropy_eq_bot`: on a symplectic
  toric manifold the action is free exactly where it is locally free.
* `stabilizer_eq_bot_iff_differential_surjective`: the action is free exactly at the points where
  `dμ_x` is surjective.
* `exists_isOpen_dense_forall_stabilizer_eq_bot`: the action is free on a dense open set.

## References

* T. Delzant, *Hamiltoniens périodiques et images convexes de l'application moment*, Bull. Soc.
  Math. France 116 (1988), 315–339.
* A. Cannas da Silva, *Lectures on Symplectic Geometry*, Lecture Notes in Mathematics 1764,
  Springer, 2001, Sections 27–29.
-/

public section

noncomputable section

open Module Set
open scoped ContDiff Manifold

namespace TauCeti

namespace SmoothTwoForm

namespace IsMomentMap

section Toric

attribute [local instance] LieGroup.minSmoothness_of_isRCLikeNormedField
attribute [local instance] ContMDiffMul.boundarylessManifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [CommGroup G] [LieGroup I ∞ G] [T2Space G]
  [CompactSpace G]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'} [I'.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H' M] [IsManifold I' ∞ M] [T2Space M]
  [CompactSpace M] [PreconnectedSpace M] [MulAction G M] [ContMDiffSMul I I' ∞ G M]
  [FaithfulSMul G M]
  {σ : SmoothTwoForm I' M} {μ : M → Module.Dual ℝ (GroupLieAlgebra I G)}

/-- **Locally free points of a symplectic toric manifold are free.** Let a compact commutative Lie
group `G` act smoothly and effectively on a compact connected symplectic manifold `(M, σ)` without
boundary, preserving `σ`, with moment map `μ`, and with `dim M = 2 dim G`. If the isotropy algebra
`𝔤_x` is trivial, then the stabilizer of `x` is trivial. -/
theorem stabilizer_eq_bot_of_isotropy_eq_bot
    (h : σ.IsMomentMap (InfinitesimalAction.fundamental I G I' M) μ) (hσ : σ.IsSymplectic)
    (hG : ∀ g : G, SmoothForm.mpullback (fun x : M ↦ g • x)
      (ContMDiffSMul.contMDiff_const_smul (I := I) g) σ = σ)
    (hdim : finrank ℝ E' = 2 * finrank ℝ E) {x : M}
    (hx : (InfinitesimalAction.fundamental I G I' M).isotropy x = ⊥) :
    MulAction.stabilizer G x = ⊥ := by
  have : IsMulCommutative G := ⟨⟨mul_comm⟩⟩
  have : CompleteSpace E' := FiniteDimensional.completeSpace ℝ E'
  have : ContinuousSMul G M := ContMDiffSMul.continuousSMul (I := I) (I' := I') ∞
  have : ContMDiffConstSMul I' ∞ G M := ⟨ContMDiffSMul.contMDiff_const_smul (I := I)⟩
  -- The stabilizer is discrete and compact, hence finite.
  have : DiscreteTopology (MulAction.stabilizer G x) :=
    (Lie.discreteTopology_stabilizer_iff_isotropy_eq_bot (I := I) (I' := I')).2 hx
  have : CompactSpace (MulAction.stabilizer G x) := isCompact_iff_compactSpace.1
    (isClosed_stabilizer (continuous_id.smul continuous_const)).isCompact
  have : Finite (MulAction.stabilizer G x) := finite_of_compact_of_discrete
  -- The orbit tangent space `L = 𝔤 · x` contains its symplectic complement `ker dμ_x`.
  have hL : (σ.bilinFormAt x).orthogonal ((InfinitesimalAction.fundamental I G I' M).orbitTangent x)
      ≤ (InfinitesimalAction.fundamental I G I' M).orbitTangent x := by
    rw [← h.ker_differential x, h.ker_differential_eq_orbitTangent
      (hσ.isNondegenerate.nondegenerate_bilinFormAt x)
      (h.momentCocycle_eq_zero_of_isLieAbelian hσ.isClosed x) (lieAnnihilator_eq_top ℝ _ _)
      (by rw [InfinitesimalAction.finrank_orbitTangent_of_isotropy_eq_bot _ x hx, hdim,
        finrank_tangentSpace (I := I) (1 : G)])]
  -- Each element of the stabilizer acts on `T_x M` by a linear isometry of `σ_x` of finite order
  -- fixing `L` pointwise, hence trivially, and the tangent representation is faithful.
  have hs (g : G) (_ : g ∈ MulAction.stabilizer G x) : ContMDiff I' I' 1 fun y : M ↦ g • y :=
    (ContMDiffSMul.contMDiff_const_smul (I := I) g).of_le ENat.LEInfty.out
  set ρ := tangentRepresentation fun g hg ↦ (hs g hg).mdifferentiableAt one_ne_zero
  refine (Subgroup.eq_bot_iff_forall _).2 fun g hg ↦ congrArg Subtype.val
    ((injective_iff_map_eq_one _).1 (injective_tangentRepresentation hs) ⟨g, hg⟩ ?_)
  have hfin : IsOfFinOrder (ρ ⟨g, hg⟩ : TangentSpace I' x →L[ℝ] TangentSpace I' x).toLinearMap :=
    (ContinuousLinearMap.toLinearMapRingHom.toMonoidHom.comp ρ.toMonoidHom).isOfFinOrder
      (isOfFinOrder_of_finite (⟨g, hg⟩ : MulAction.stabilizer G x))
  -- `TangentSpace I' x` is the model space `E'` by definition.
  have : HasUniqueDiv (TangentSpace I' x) := HasUniqueDiv.of_isTorsionFree ℝ E'
  have hone := LinearMap.IsOrthogonal.eq_one_of_isOfFinOrder (fun u v ↦ ?_) hL (fun v hv ↦ ?_) hfin
  · ext v
    exact LinearMap.congr_fun hone v
  · simpa only [IsNondegenerate.symplecticFormAt_apply, ← SmoothForm.bilinFormAt_apply,
      ContinuousLinearMap.coe_coe] using
      hσ.isNondegenerate.symplecticFormAt_tangentRepresentation (fun g _ ↦ hG g) _ ⟨g, hg⟩ u v
  · obtain ⟨ξ, rfl⟩ := (InfinitesimalAction.mem_orbitTangent_iff _ x).1 hv
    simp only [InfinitesimalAction.fundamental_apply, ContinuousLinearMap.coe_coe, ρ,
      tangentRepresentation_fundamentalVectorField, Lie.adjointContinuousLinearMap_eq_id,
      ContinuousLinearMap.id_apply]

/-- **A symplectic toric manifold is free exactly where it is locally free.** For a symplectic
toric manifold, the stabilizer of `x` is trivial exactly when the isotropy algebra `𝔤_x` is. -/
theorem stabilizer_eq_bot_iff_isotropy_eq_bot
    (h : σ.IsMomentMap (InfinitesimalAction.fundamental I G I' M) μ) (hσ : σ.IsSymplectic)
    (hG : ∀ g : G, SmoothForm.mpullback (fun x : M ↦ g • x)
      (ContMDiffSMul.contMDiff_const_smul (I := I) g) σ = σ)
    (hdim : finrank ℝ E' = 2 * finrank ℝ E) {x : M} :
    MulAction.stabilizer G x = ⊥ ↔ (InfinitesimalAction.fundamental I G I' M).isotropy x = ⊥ :=
  have : CompleteSpace E' := FiniteDimensional.completeSpace ℝ E'
  ⟨Lie.isotropy_eq_bot_of_stabilizer_eq_bot (I := I) (I' := I'),
    h.stabilizer_eq_bot_of_isotropy_eq_bot hσ hG hdim⟩

/-- **A symplectic toric manifold is free exactly over the regular points of its moment map.** For
a symplectic toric manifold, the stabilizer of `x` is trivial exactly when the differential
`dμ_x : T_x M → 𝔤*` of the moment map is surjective. -/
theorem stabilizer_eq_bot_iff_differential_surjective
    (h : σ.IsMomentMap (InfinitesimalAction.fundamental I G I' M) μ) (hσ : σ.IsSymplectic)
    (hG : ∀ g : G, SmoothForm.mpullback (fun x : M ↦ g • x)
      (ContMDiffSMul.contMDiff_const_smul (I := I) g) σ = σ)
    (hdim : finrank ℝ E' = 2 * finrank ℝ E) {x : M} :
    MulAction.stabilizer G x = ⊥ ↔ Function.Surjective (h.differential x) := by
  rw [h.differential_surjective_iff (hσ.isNondegenerate.nondegenerate_bilinFormAt x)]
  exact h.stabilizer_eq_bot_iff_isotropy_eq_bot hσ hG hdim

/-- **A symplectic toric manifold is free on a dense open set.** For a symplectic toric manifold,
there is a dense open set of points `x` whose stabilizer is trivial. -/
theorem exists_isOpen_dense_forall_stabilizer_eq_bot
    (h : σ.IsMomentMap (InfinitesimalAction.fundamental I G I' M) μ) (hσ : σ.IsSymplectic)
    (hG : ∀ g : G, SmoothForm.mpullback (fun x : M ↦ g • x)
      (ContMDiffSMul.contMDiff_const_smul (I := I) g) σ = σ)
    (hdim : finrank ℝ E' = 2 * finrank ℝ E) :
    ∃ U : Set M, IsOpen U ∧ Dense U ∧ ∀ x ∈ U, MulAction.stabilizer G x = ⊥ := by
  have : IsMulCommutative G := ⟨⟨mul_comm⟩⟩
  have : CompleteSpace E' := FiniteDimensional.completeSpace ℝ E'
  obtain ⟨U, hU, hUd, hUx⟩ :=
    Lie.exists_isOpen_dense_forall_isotropy_eq_bot (I := I) (I' := I') (G := G) (M := M)
  exact ⟨U, hU, hUd, fun x hx ↦ h.stabilizer_eq_bot_of_isotropy_eq_bot hσ hG hdim (hUx x hx)⟩

end Toric

end IsMomentMap

end SmoothTwoForm

end TauCeti

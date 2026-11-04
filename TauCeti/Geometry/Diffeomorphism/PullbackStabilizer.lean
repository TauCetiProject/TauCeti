/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Group.ClosedSubgroup
public import TauCeti.Geometry.Diffeomorphism.Congr
public import TauCeti.Geometry.Manifold.ContMDiffMap.Chart.Pullback
public import TauCeti.Geometry.Manifold.DifferentialForm.Chart
public import TauCeti.Geometry.Manifold.DifferentialForm.Pullback.Smooth

/-!
# Diffeomorphisms preserving a differential form

For a smooth differential form `α` on a manifold `M`, the smooth self-diffeomorphisms `φ` with
`φ^* α = α` form a subgroup `TauCeti.SmoothForm.pullbackStabilizer α` of `Diff(M)`. For a
symplectic form `ω` this is the symplectomorphism group `Symp(M, ω)`; for a contact form it is the
group of strict contactomorphisms, and for a volume form the group of volume-preserving
diffeomorphisms.

When `M` is compact and its model space is locally compact, this subgroup is closed for the weak
Whitney `C^∞` topology (`TauCeti.SmoothForm.isClosed_pullbackStabilizer`,
`TauCeti.SmoothForm.closedPullbackStabilizer`). When `M` is moreover Hausdorff, `Diff(M)` is a
topological group for this topology (`Diffeomorph.isTopologicalGroup`), and the stabilizer is a
closed topological subgroup. The condition `φ^* α = α` is the family of
equations `(φ^* α)_x = α_x`, one for each point `x`; read in the chart centred at `x`, each side
depends continuously on `φ` by `TauCeti.continuous_inChartAt_mpullback`, which only involves the
first derivative of `φ` at `x`.

A diffeomorphism `e : M → N` with `e^* β = α` conjugates the stabilizer of `α` onto that of `β`
(`TauCeti.SmoothForm.map_diffCongr_pullbackStabilizer`).

## References

* D. McDuff and D. Salamon, *Introduction to Symplectic Topology*, 3rd ed., Oxford University
  Press, 2017, Chapter 10.
-/

public section

open scoped Manifold ContDiff

namespace TauCeti.SmoothForm

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {k : ℕ}

/-- The smooth self-diffeomorphisms `φ` of `M` pulling the smooth form `α` back to itself,
`φ^* α = α`, as a subgroup of `Diff(M)`. For a symplectic form `ω` this is the symplectomorphism
group `Symp(M, ω)`. -/
def pullbackStabilizer (α : SmoothForm I M F k) : Subgroup (M ≃ₘ⟮I, I⟯ M) where
  carrier := {φ | mpullback φ φ.contMDiff α = α}
  one_mem' := by
    apply Subtype.ext
    simp only [coe_mpullback, Diffeomorph.coe_one, TauCeti.mpullback_id]
  mul_mem' {φ ψ} hφ hψ := by
    have hφ' : (mpullback φ φ.contMDiff α).1 = α.1 := congrArg Subtype.val hφ
    have hψ' : (mpullback ψ ψ.contMDiff α).1 = α.1 := congrArg Subtype.val hψ
    apply Subtype.ext
    simp only [coe_mpullback] at hφ' hψ' ⊢
    rw [Diffeomorph.coe_mul, TauCeti.mpullback_comp (ψ.mdifferentiable (by simp))
      (φ.mdifferentiable (by simp)), hφ', hψ']
  inv_mem' {φ} hφ := mpullback_symm_eq_of_mpullback_eq hφ

/-- A diffeomorphism lies in the stabilizer of `α` exactly when it pulls `α` back to itself. -/
@[simp]
theorem mem_pullbackStabilizer_iff {α : SmoothForm I M F k} {φ : M ≃ₘ⟮I, I⟯ M} :
    φ ∈ pullbackStabilizer α ↔ mpullback φ φ.contMDiff α = α :=
  Iff.rfl

variable {E' H' N : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
  {J : ModelWithCorners ℝ E' H'} [TopologicalSpace N] [ChartedSpace H' N] [IsManifold J ∞ N]

/-- If a diffeomorphism `e : M → N` pulls `β` back to `α`, then a self-diffeomorphism `φ` of `M`
preserves `α` exactly when its conjugate `e ∘ φ ∘ e⁻¹` preserves `β`. -/
theorem diffCongr_mem_pullbackStabilizer_iff (e : M ≃ₘ⟮I, J⟯ N) {α : SmoothForm I M F k}
    {β : SmoothForm J N F k} (h : mpullback e e.contMDiff β = α) {φ : M ≃ₘ⟮I, I⟯ M} :
    Diffeomorph.diffCongr e φ ∈ pullbackStabilizer β ↔ φ ∈ pullbackStabilizer α := by
  subst h
  have hconj : mpullback (Diffeomorph.diffCongr e φ) (Diffeomorph.diffCongr e φ).contMDiff β =
      mpullback e.symm e.symm.contMDiff (mpullback φ φ.contMDiff (mpullback e e.contMDiff β)) := by
    apply Subtype.ext
    simp only [coe_mpullback]
    rw [Diffeomorph.diffCongr_apply, Diffeomorph.coe_trans, Diffeomorph.coe_trans,
      TauCeti.mpullback_comp ((φ.contMDiff.comp e.symm.contMDiff).mdifferentiable (by simp))
        (e.mdifferentiable (by simp)),
      TauCeti.mpullback_comp (e.symm.mdifferentiable (by simp)) (φ.mdifferentiable (by simp))]
  rw [mem_pullbackStabilizer_iff, mem_pullbackStabilizer_iff, hconj]
  constructor
  · intro hφ
    have h' := congrArg (mpullback e e.contMDiff) hφ
    rwa [mpullback_mpullback_symm] at h'
  · intro hφ
    rw [hφ]
    exact mpullback_symm_mpullback e β

/-- A diffeomorphism `e : M → N` pulling `β` back to `α` conjugates the stabilizer of `α` onto the
stabilizer of `β`. For symplectic forms, conjugation by a symplectomorphism identifies the
symplectomorphism groups. -/
theorem map_diffCongr_pullbackStabilizer (e : M ≃ₘ⟮I, J⟯ N) {α : SmoothForm I M F k}
    {β : SmoothForm J N F k} (h : mpullback e e.contMDiff β = α) :
    (pullbackStabilizer α).map (Diffeomorph.diffCongr e).toMonoidHom = pullbackStabilizer β := by
  ext ψ
  rw [Subgroup.mem_map_equiv, ← diffCongr_mem_pullbackStabilizer_iff e h,
    MulEquiv.apply_symm_apply]

section Topology

open scoped TauCeti.ManifoldWeakWhitney TauCeti.DiffeomorphWeakWhitney

variable [CompactSpace M] [LocallyCompactSpace E]

/-- On a compact manifold whose model space is locally compact, the diffeomorphisms preserving a
smooth form are closed in the weak Whitney `C^∞` topology. In particular the symplectomorphism
group of a compact symplectic manifold is closed. -/
theorem isClosed_pullbackStabilizer (α : SmoothForm I M F k) :
    IsClosed (pullbackStabilizer α : Set (M ≃ₘ⟮I, I⟯ M)) := by
  have hset : (pullbackStabilizer α : Set (M ≃ₘ⟮I, I⟯ M)) = ⋂ x : M,
      {φ : M ≃ₘ⟮I, I⟯ M | (TauCeti.mpullback I I φ α.1).inChartAt x (extChartAt I x x) =
        RoughForm.inChartAt α.1 x (extChartAt I x x)} := by
    ext φ
    simp only [SetLike.mem_coe, mem_pullbackStabilizer_iff, Set.mem_iInter, Set.mem_ofPred_eq,
      Subtype.ext_iff, coe_mpullback, funext_iff]
    exact forall_congr' fun x ↦ (RoughForm.inChartAt_chart_eq_iff (mem_extChartAt_source x)).symm
  rw [hset]
  exact isClosed_iInter fun x ↦ isClosed_eq
    ((continuous_inChartAt_mpullback α.isSmoothForm (by simp) x (mem_extChartAt_target x)).comp
      Diffeomorph.isEmbedding_toContMDiffMap.continuous) continuous_const

/-- The diffeomorphisms preserving a smooth form, as a closed subgroup of the weak Whitney space
of diffeomorphisms of a compact manifold. For a symplectic form `ω` this is `Symp(M, ω)`. -/
def closedPullbackStabilizer (α : SmoothForm I M F k) : ClosedSubgroup (M ≃ₘ⟮I, I⟯ M) :=
  ⟨pullbackStabilizer α, isClosed_pullbackStabilizer α⟩

/-- The carrier of the closed stabilizer is the stabilizer subgroup. -/
@[simp]
theorem coe_closedPullbackStabilizer (α : SmoothForm I M F k) :
    (closedPullbackStabilizer α : Subgroup (M ≃ₘ⟮I, I⟯ M)) = pullbackStabilizer α := (rfl)

/-- Membership in the closed stabilizer is preservation of the form. -/
@[simp]
theorem mem_closedPullbackStabilizer_iff {α : SmoothForm I M F k} {φ : M ≃ₘ⟮I, I⟯ M} :
    φ ∈ closedPullbackStabilizer α ↔ mpullback φ φ.contMDiff α = α :=
  Iff.rfl

end Topology

end TauCeti.SmoothForm

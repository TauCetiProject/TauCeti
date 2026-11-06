/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Diffeomorphism.Congr
public import TauCeti.Geometry.Manifold.ContMDiffMap.Chart.FormPullback
public import Mathlib.Topology.Algebra.Group.ClosedSubgroup

/-!
# Diffeomorphisms preserving a differential form

For a smooth form `α` on a manifold `M`, the diffeomorphisms `φ` of `M` with `φ^* α = α` form a
subgroup of the diffeomorphism group, `TauCeti.SmoothForm.diffeomorphStabilizer α`. For a
symplectic form `ω` this is the symplectomorphism group `Symp(M, ω)`; for a volume form it is the
group of volume-preserving diffeomorphisms.

When `M` is compact, the diffeomorphism group carries the weak Whitney (`C^∞`) topology, and the
subgroup is closed (`TauCeti.SmoothForm.isClosed_diffeomorphStabilizer`). Indeed, the condition
`φ^* α = α` is the intersection over `x ∈ M` of the first-jet conditions `(φ^* α)_x = α_x`, and
each value `(φ^* α)_x` depends continuously on `φ`
(`TauCeti.SmoothForm.continuous_mpullback_diffeomorph_apply`). We record the subgroup as a
`ClosedSubgroup`, `TauCeti.SmoothForm.closedDiffeomorphStabilizer`. When the model space is
locally compact and `M` is Hausdorff, the diffeomorphism group is a topological group
(`Diffeomorph.isTopologicalGroup`), so the stabilizer is a closed topological subgroup.

The stabilizer is natural: a diffeomorphism `e : M → N` conjugates the stabilizer of `e^* β`
onto the stabilizer of `β` (`TauCeti.SmoothForm.diffeomorphStabilizer_mpullback`), through the
conjugation isomorphism `Diffeomorph.diffCongr e`.

Neither closedness nor nondegeneracy of `α` is used, and the form may take values in any normed
space.

## References

* D. McDuff and D. Salamon, *Introduction to Symplectic Topology*, 3rd ed., Oxford, 2017,
  Chapter 10 (the group of symplectomorphisms with the `C^∞` topology).
-/

public section

open scoped Manifold ContDiff TauCeti.ManifoldWeakWhitney TauCeti.DiffeomorphWeakWhitney

namespace TauCeti.SmoothForm

variable {E H M E' H' M' F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
  {I' : ModelWithCorners ℝ E' H'} [TopologicalSpace M'] [ChartedSpace H' M'] [IsManifold I' ∞ M']
  [NormedAddCommGroup F] [NormedSpace ℝ F] {k : ℕ}

/-- The diffeomorphisms of `M` preserving a smooth form `α`, that is, with `φ^* α = α`. For a
symplectic form `ω` this is the symplectomorphism group `Symp(M, ω)`. -/
def diffeomorphStabilizer (α : SmoothForm I M F k) : Subgroup (M ≃ₘ⟮I, I⟯ M) where
  carrier := {φ | mpullback φ φ.contMDiff α = α}
  one_mem' := by simp [Diffeomorph.coe_one, mpullback_id]
  mul_mem' {φ ψ} hφ hψ := by
    simp only [Set.mem_ofPred_eq] at hφ hψ ⊢
    rw [Diffeomorph.mul_def, mpullback_trans, hφ, hψ]
  inv_mem' {φ} hφ := mpullback_symm_eq_of_mpullback_eq hφ

/-- Membership in the stabilizer of a form is invariance of the form under pullback. -/
@[simp]
theorem mem_diffeomorphStabilizer_iff {α : SmoothForm I M F k} {φ : M ≃ₘ⟮I, I⟯ M} :
    φ ∈ α.diffeomorphStabilizer ↔ mpullback φ φ.contMDiff α = α := Iff.rfl

/-- Pointwise form of membership in the stabilizer: `φ` preserves `α` exactly when
`α_{φ x}(dφ_x v₁, …, dφ_x v_k) = α_x(v₁, …, v_k)` for all points and tangent vectors. -/
theorem mem_diffeomorphStabilizer_iff_forall_apply {α : SmoothForm I M F k}
    {φ : M ≃ₘ⟮I, I⟯ M} :
    φ ∈ α.diffeomorphStabilizer ↔
      ∀ x (v : Fin k → TangentSpace I x), α.1 (φ x) (fun i ↦ mfderiv I I φ x (v i)) = α.1 x v := by
  rw [mem_diffeomorphStabilizer_iff]
  refine ⟨fun h x v ↦ ?_, fun h ↦ Subtype.ext <| funext fun x ↦
    ContinuousAlternatingMap.ext fun v ↦ ?_⟩
  · rw [← mpullback_apply φ φ.contMDiff, h]
  · rw [mpullback_apply]
    exact h x v

/-- **Naturality of the stabilizer.** Conjugation by a diffeomorphism `e : M → M'` carries the
diffeomorphisms preserving `e^* β` onto those preserving `β`. -/
theorem diffeomorphStabilizer_mpullback (e : M ≃ₘ⟮I, I'⟯ M') (β : SmoothForm I' M' F k) :
    (mpullback e e.contMDiff β).diffeomorphStabilizer =
      β.diffeomorphStabilizer.comap (Diffeomorph.diffCongr e).toMonoidHom := by
  ext φ
  rw [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, mem_diffeomorphStabilizer_iff,
    mem_diffeomorphStabilizer_iff, Diffeomorph.diffCongr_apply, mpullback_trans, mpullback_trans]
  constructor
  · intro h
    rw [h, mpullback_symm_mpullback]
  · intro h
    exact (mpullback_mpullback_symm e _).symm.trans (by rw [h])

section Topology

variable [CompactSpace M] [LocallyCompactSpace E]

/-- The value at a fixed point of the pullback of a smooth form depends continuously on the
diffeomorphism, for the weak Whitney topology. -/
theorem continuous_mpullback_diffeomorph_apply (β : SmoothForm I' M' F k) (x : M) :
    Continuous fun φ : M ≃ₘ⟮I, I'⟯ M' ↦ (mpullback φ φ.contMDiff β).1 x :=
  (continuous_mpullback_contMDiffMap_apply β x).comp Diffeomorph.continuous_toContMDiffMap

/-- On a compact manifold, the diffeomorphisms preserving a smooth form are closed in the weak
Whitney topology. In particular the symplectomorphism group `Symp(M, ω)` is closed. -/
theorem isClosed_diffeomorphStabilizer (α : SmoothForm I M F k) :
    IsClosed (α.diffeomorphStabilizer : Set (M ≃ₘ⟮I, I⟯ M)) := by
  have hset : (α.diffeomorphStabilizer : Set (M ≃ₘ⟮I, I⟯ M)) =
      ⋂ x, {φ : M ≃ₘ⟮I, I⟯ M | (mpullback φ φ.contMDiff α).1 x = α.1 x} := by
    ext φ
    simp only [SetLike.mem_coe, mem_diffeomorphStabilizer_iff, Set.mem_iInter, Set.mem_ofPred_eq]
    exact ⟨fun h x ↦ by rw [h], fun h ↦ Subtype.ext (funext h)⟩
  rw [hset]
  exact isClosed_iInter fun x ↦
    isClosed_eq (continuous_mpullback_diffeomorph_apply α x) continuous_const

/-- The diffeomorphisms of a compact manifold preserving a smooth form, as a closed subgroup of
the diffeomorphism group with its weak Whitney topology. -/
def closedDiffeomorphStabilizer (α : SmoothForm I M F k) : ClosedSubgroup (M ≃ₘ⟮I, I⟯ M) :=
  ⟨α.diffeomorphStabilizer, α.isClosed_diffeomorphStabilizer⟩

/-- The underlying subgroup of the closed stabilizer is the stabilizer. -/
@[simp]
theorem coe_closedDiffeomorphStabilizer (α : SmoothForm I M F k) :
    (α.closedDiffeomorphStabilizer : Subgroup (M ≃ₘ⟮I, I⟯ M)) = α.diffeomorphStabilizer :=
  (rfl)

/-- Membership in the closed stabilizer is invariance of the form under pullback. -/
@[simp]
theorem mem_closedDiffeomorphStabilizer_iff {α : SmoothForm I M F k} {φ : M ≃ₘ⟮I, I⟯ M} :
    φ ∈ α.closedDiffeomorphStabilizer ↔ mpullback φ φ.contMDiff α = α :=
  Iff.rfl

end Topology

end TauCeti.SmoothForm

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Diffeomorphism.Congr
public import TauCeti.Geometry.Manifold.DifferentialForm.Pullback.Smooth

/-!
# Conjugating the stabilizer of a differential form

For a smooth differential form `α` on a manifold `M`, the smooth self-diffeomorphisms `φ` with
`φ^* α = α` form the subgroup `TauCeti.SmoothForm.diffeomorphStabilizer α` of `Diff(M)`. For a
symplectic form `ω` this is the symplectomorphism group `Symp(M, ω)`; for a contact form it is the
group of strict contactomorphisms, and for a volume form the group of volume-preserving
diffeomorphisms.

A diffeomorphism `e : M → N` with `e^* β = α` conjugates the stabilizer of `α` onto that of `β`
(`Diffeomorph.map_diffCongr_diffeomorphStabilizer`): a self-diffeomorphism `φ` of `M` preserves
`α` exactly when `e ∘ φ ∘ e⁻¹` preserves `β`
(`Diffeomorph.diffCongr_mem_diffeomorphStabilizer_iff`). For symplectic forms, a symplectomorphism
`(M, α) ≅ (N, β)` thus identifies `Symp(M, α)` with `Symp(N, β)`.

## References

* D. McDuff and D. Salamon, *Introduction to Symplectic Topology*, 3rd ed., Oxford University
  Press, 2017, Chapter 10.
-/

public section

open scoped Manifold ContDiff

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {E' H' N : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
  {J : ModelWithCorners ℝ E' H'} [TopologicalSpace N] [ChartedSpace H' N] [IsManifold J ∞ N]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {k : ℕ}

namespace Diffeomorph

open TauCeti (SmoothForm)
open TauCeti.SmoothForm

/-- If a diffeomorphism `e : M → N` pulls `β` back to `α`, then a self-diffeomorphism `φ` of `M`
preserves `α` exactly when its conjugate `e ∘ φ ∘ e⁻¹` preserves `β`. -/
theorem diffCongr_mem_diffeomorphStabilizer_iff (e : M ≃ₘ⟮I, J⟯ N) {α : SmoothForm I M F k}
    {β : SmoothForm J N F k} (h : mpullback e e.contMDiff β = α) {φ : M ≃ₘ⟮I, I⟯ M} :
    diffCongr e φ ∈ diffeomorphStabilizer β ↔ φ ∈ diffeomorphStabilizer α := by
  subst h
  have hconj : mpullback (diffCongr e φ) (diffCongr e φ).contMDiff β =
      mpullback e.symm e.symm.contMDiff (mpullback φ φ.contMDiff (mpullback e e.contMDiff β)) := by
    apply Subtype.ext
    simp only [coe_mpullback]
    rw [diffCongr_apply, coe_trans, coe_trans,
      TauCeti.mpullback_comp ((φ.contMDiff.comp e.symm.contMDiff).mdifferentiable (by simp))
        (e.mdifferentiable (by simp)),
      TauCeti.mpullback_comp (e.symm.mdifferentiable (by simp)) (φ.mdifferentiable (by simp))]
  rw [mem_diffeomorphStabilizer, mem_diffeomorphStabilizer, hconj]
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
theorem map_diffCongr_diffeomorphStabilizer (e : M ≃ₘ⟮I, J⟯ N) {α : SmoothForm I M F k}
    {β : SmoothForm J N F k} (h : mpullback e e.contMDiff β = α) :
    (diffeomorphStabilizer α).map (diffCongr e).toMonoidHom = diffeomorphStabilizer β := by
  ext ψ
  rw [Subgroup.mem_map_equiv, ← diffCongr_mem_diffeomorphStabilizer_iff e h,
    MulEquiv.apply_symm_apply]

end Diffeomorph

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.VectorBundle.Determinant

/-!
# The determinant line of a trivial bundle

Let `F` be a finite-dimensional normed space over a complete nontrivially normed field `𝕜`, of
dimension `r`. The determinant line `det (B × F) = ⋀ʳ (B × F)` of the trivial bundle `B × F`
(`TauCeti.DetBundle 𝕜 F (Bundle.Trivial B F)`) is the trivial line `B × 𝕜`: each fibre `⋀ʳ F` is
identified with `𝕜` by the fixed coordinate `TauCeti.DetBundle.modelCoord F` of the basis
`Module.finBasis 𝕜 F` (`TauCeti.DetBundle.trivialEquiv`), and these identifications form a
homeomorphism of total spaces `det (B × F) ≃ B × 𝕜` (`TauCeti.DetBundle.trivialHomeomorph`). It is
continuous because, read in the trivialization of `det (B × F)` induced from the canonical
trivialization of `B × F`, it is the identity of `𝕜`.

For `𝕜 = ℂ` and `F = ℂʳ` this is the canonical isomorphism `det(ℂʳ) ≃ ℂ` of the determinant line of
a trivial complex vector bundle.

## Main definitions

* `TauCeti.DetBundle.trivialEquiv`: the identification `⋀ʳ F ≃ 𝕜` of the fibres of the
  determinant line of the trivial bundle `B × F`.
* `TauCeti.DetBundle.trivialHomeomorph`: the determinant line of the trivial bundle `B × F` is
  the trivial line bundle `B × 𝕜`.

## References

* J. W. Milnor, J. D. Stasheff, *Characteristic Classes*, Annals of Mathematics Studies 76,
  Princeton (1974), §14.
-/

public section

noncomputable section

open Bundle Module

namespace TauCeti

namespace DetBundle

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {B : Type*} {F : Type*} [NormedAddCommGroup F]
  [NormedSpace 𝕜 F] [FiniteDimensional 𝕜 F]

variable (𝕜 B F) in
/-- **The determinant line of a trivial bundle is trivial**, fibrewise: the fibre `⋀ʳ F` of the
determinant line of `B × F` is identified with `𝕜` by the fixed coordinate
`TauCeti.DetBundle.modelCoord F`, which reads `v₁ ∧ ⋯ ∧ vᵣ` as the determinant of `(v₁, …, vᵣ)` in
the basis `Module.finBasis 𝕜 F` (`TauCeti.DetBundle.trivialEquiv_ιMulti`). -/
def trivialEquiv (x : B) : DetBundle 𝕜 F (Trivial B F) x ≃L[𝕜] Trivial B 𝕜 x :=
  (linearEquiv 𝕜 F (Trivial B F) x ≪≫ₗ modelCoord F).toContinuousLinearEquivOfIsModuleTopology

/-- The identification of the determinant line of a trivial bundle with `𝕜` reads
`v₁ ∧ ⋯ ∧ vᵣ` as the determinant of `(v₁, …, vᵣ)` in the basis `Module.finBasis 𝕜 F`. -/
theorem trivialEquiv_ιMulti (x : B) (v : Fin (finrank 𝕜 F) → F) :
    trivialEquiv 𝕜 B F x ((linearEquiv 𝕜 F (Trivial B F) x).symm (exteriorPower.ιMulti 𝕜 _ v)) =
      (Module.finBasis 𝕜 F).det v := by
  rw [trivialEquiv, LinearEquiv.coe_toContinuousLinearEquivOfIsModuleTopology,
    LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply,
    Module.Basis.exteriorPowerTopEquiv_apply_ιMulti]

/-- The identification of the determinant line of a trivial bundle with `𝕜` is the fixed coordinate
`TauCeti.DetBundle.modelCoord F` of the determinant line of the model fibre. -/
theorem trivialEquiv_apply (x : B) (v : DetBundle 𝕜 F (Trivial B F) x) :
    trivialEquiv 𝕜 B F x v = modelCoord F (linearEquiv 𝕜 F (Trivial B F) x v) := by
  rw [trivialEquiv, LinearEquiv.coe_toContinuousLinearEquivOfIsModuleTopology,
    LinearEquiv.trans_apply]

variable [TopologicalSpace B]

/-- The chart coordinate of the trivialization of the determinant line of `B × F` induced by its
canonical trivialization is the fixed coordinate `TauCeti.DetBundle.modelCoord F`. -/
private theorem chartCoord_trivializationAt (y x : B)
    (hx : x ∈ (trivializationAt F (Trivial B F) y).baseSet) (v : DetBundle 𝕜 F (Trivial B F) x) :
    chartCoord (trivializationAt F (Trivial B F) y) hx v = trivialEquiv 𝕜 B F x v := by
  -- The canonical trivialization of `B × F` is the identity on each fibre.
  have h : (trivializationAt F (Trivial B F) y).linearEquivAt 𝕜 x hx = LinearEquiv.refl 𝕜 F :=
    LinearEquiv.ext fun _ ↦ rfl
  rw [chartCoord_apply, h, LinearEquiv.exteriorPower_refl, LinearEquiv.refl_apply,
    trivialEquiv_apply]

variable [CompleteSpace 𝕜]

variable (𝕜 B F) in
/-- **The determinant line of a trivial bundle is trivial.** The fibrewise identifications
`TauCeti.DetBundle.trivialEquiv` of `⋀ʳ F` with `𝕜` form a homeomorphism of total spaces
`det (B × F) ≃ B × 𝕜`. -/
def trivialHomeomorph :
    TotalSpace 𝕜 (DetBundle 𝕜 F (Trivial B F)) ≃ₜ TotalSpace 𝕜 (Trivial B 𝕜) :=
  bundleHomeomorph (trivialEquiv 𝕜 B F) <|
    FiberBundle.continuous_totalSpaceMk_of_trivializationAt (fun x ↦ trivialEquiv 𝕜 B F x)
      continuous_id fun y x v _ _ ↦ by
      have hx : x ∈ (trivializationAt F (Trivial B F) y).baseSet := Set.mem_univ x
      rw [trivializationAt_eq, trivialization_apply_mk _ hx, chartCoord_trivializationAt]
      simp only [Trivial.fiberBundle_trivializationAt', Trivial.trivialization_apply, id]

@[simp]
theorem trivialHomeomorph_apply (p : TotalSpace 𝕜 (DetBundle 𝕜 F (Trivial B F))) :
    trivialHomeomorph 𝕜 B F p = ⟨p.proj, trivialEquiv 𝕜 B F p.proj p.snd⟩ :=
  bundleHomeomorph_apply _ _ p

@[simp]
theorem trivialHomeomorph_symm_apply (p : TotalSpace 𝕜 (Trivial B 𝕜)) :
    (trivialHomeomorph 𝕜 B F).symm p = ⟨p.proj, (trivialEquiv 𝕜 B F p.proj).symm p.snd⟩ :=
  bundleHomeomorph_symm_apply _ _ p

end DetBundle

end TauCeti

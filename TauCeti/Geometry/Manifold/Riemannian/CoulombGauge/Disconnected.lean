/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.CoulombGauge
public import TauCeti.Geometry.Manifold.Riemannian.Restriction.Codifferential

/-!
# Coulomb gauge on manifolds with compact connected components

On a positive-dimensional boundaryless oriented Riemannian manifold with compact connected
components, every smooth one-form has a coclosed representative modulo exact forms.
In particular this holds on compact manifolds, without assuming connectedness.

The construction uses the connected solver
`TauCeti.SmoothForm.exists_codifferential_sub_mextDerivₗ_eq_zero` on each component.

## Main results

* `TauCeti.SmoothForm.exists_codifferential_sub_mextDerivₗ_eq_zero_of_isCompact_connectedComponent`:
  a global Coulomb gauge when every connected component is compact.
* `TauCeti.SmoothForm.exists_codifferential_sub_mextDerivₗ_eq_zero_of_compactSpace`:
  a global Coulomb gauge on compact manifolds.
-/

public section

noncomputable section

open Bundle Manifold MeasureTheory TopologicalSpace
open scoped ContDiff Manifold TauCeti

namespace TauCeti.SmoothForm

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M]

variable [FiniteDimensional ℝ E] [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
  [I.Boundaryless] [T2Space M]

/-- On a positive-dimensional boundaryless oriented Riemannian manifold with compact
connected components, every smooth one-form has a coclosed representative modulo exact forms.
The smooth potential has no prescribed normalization. -/
theorem exists_codifferential_sub_mextDerivₗ_eq_zero_of_isCompact_connectedComponent {m l : ℕ}
    (o : Manifold.Orientation I M (Fin m)) (hkl : 0 + 1 + l = m)
    (hc : ∀ x : M, IsCompact (connectedComponent x)) (a : SmoothForm I M ℝ 1) :
    ∃ f : SmoothForm I M ℝ 0, codifferential o hkl (a - mextDerivₗ I 0 f) = 0 := by
  let : LocallyConnectedSpace H := I.toHomeomorph.locallyConnectedSpace
  let : LocallyConnectedSpace M := ChartedSpace.locallyConnectedSpace H M
  let U (x : M) : Opens M := ⟨connectedComponent x, isOpen_connectedComponent⟩
  have hsolve (V : Set.range U) :
      ∃ f : SmoothForm I V.val ℝ 0, codifferential (o.restrict V.val) hkl
        (mpullback (Subtype.val : V.val → M) contMDiff_subtypeVal a - mextDerivₗ I 0 f) = 0 := by
    obtain ⟨V, x, rfl⟩ := V
    let : CompactSpace (U x) :=
      isCompact_iff_compactSpace.mp (hc x)
    let : PreconnectedSpace (U x) :=
      isPreconnected_iff_preconnectedSpace.mp isConnected_connectedComponent.isPreconnected
    let : MeasurableSpace (U x) := borel (U x)
    let : BorelSpace (U x) := ⟨rfl⟩
    obtain ⟨f, -, hf⟩ :=
      exists_codifferential_sub_mextDerivₗ_eq_zero (o.restrict (U x)) hkl
        (mpullback (Subtype.val : U x → M) contMDiff_subtypeVal a)
    exact ⟨f, hf⟩
  choose f hf using hsolve
  obtain ⟨F, hF⟩ := exists_zeroForm_mpullback_eq_of_partition (I := I) (U := U)
    (fun x ↦ mem_connectedComponent)
    (fun h ↦ SetLike.coe_injective (connectedComponent_eq h).symm) f
  refine ⟨F, ?_⟩
  apply Subtype.ext
  funext x
  let y : U x := ⟨x, mem_connectedComponent⟩
  have hpullδ : mpullback (Subtype.val : U x → M) contMDiff_subtypeVal
      (codifferential o hkl (a - mextDerivₗ I 0 F)) = 0 := by
    rw [← codifferential_mpullback_subtypeVal, map_sub, ← mextDerivₗ_mpullback, hF x]
    exact hf ⟨U x, ⟨x, rfl⟩⟩
  ext v
  rw [Subsingleton.elim v 0]
  simp only [Submodule.coe_zero, Pi.zero_apply, ContinuousAlternatingMap.coe_zero]
  have h := congrArg (β := ℝ) (fun b : SmoothForm I (U x) ℝ 0 ↦ b.val y 0) hpullδ
  simp only [coe_mpullback_subtype_val_apply, Submodule.coe_zero, Pi.zero_apply,
    ContinuousAlternatingMap.coe_zero] at h ⊢
  exact h

/-- Every smooth one-form on a positive-dimensional compact boundaryless oriented Riemannian
manifold is the sum of an exact form and a coclosed form. The smooth potential has no prescribed
normalization. -/
theorem exists_codifferential_sub_mextDerivₗ_eq_zero_of_compactSpace [CompactSpace M] {m l : ℕ}
    (o : Manifold.Orientation I M (Fin m)) (hkl : 0 + 1 + l = m)
    (a : SmoothForm I M ℝ 1) :
    ∃ f : SmoothForm I M ℝ 0, codifferential o hkl (a - mextDerivₗ I 0 f) = 0 :=
  exists_codifferential_sub_mextDerivₗ_eq_zero_of_isCompact_connectedComponent o hkl
    (fun _ ↦ isClosed_connectedComponent.isCompact) a

end TauCeti.SmoothForm

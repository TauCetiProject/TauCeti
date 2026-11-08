/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Topology.OpenPartialHomeomorph.Constructions

/-!
# Shear charts of a normed space

Given a linear homeomorphism `A : V × W ≃L[𝕜] Y` and a map `g : V → W` which is `C^m` on an open
set, the shear `(u, w) ↦ (u, w - g u)` of the graph of `g` is a partial homeomorphism of `Y`,
`C^m` with `C^m` inverse, once read through `A`.

## Main declarations

* `ContinuousLinearEquiv.exists_contDiffOn_shear`: the existence of such a shear chart, with its
  explicit formula and source.
-/

public section

open scoped ContDiff

namespace ContinuousLinearEquiv

variable {𝕜 V W Y : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup V] [NormedSpace 𝕜 V] [NormedAddCommGroup W] [NormedSpace 𝕜 W]
  [NormedAddCommGroup Y] [NormedSpace 𝕜 Y] {m : ℕ∞ω}

/-- **A shear chart of a normed space**: given a linear homeomorphism `A : V × W ≃ Y`, a basepoint
`c₀` and a map `g : V → W` which is `C^m` on an open set `U`, there is a partial homeomorphism of
`Y`, `C^m` with `C^m` inverse, which sends `x` to `A (u, w - g u)`, where `(u, w) = A⁻¹ (x - c₀)`,
and whose source is the set of points with `u ∈ U`. -/
theorem exists_contDiffOn_shear (A : (V × W) ≃L[𝕜] Y) (c₀ : Y) {U : Set V}
    (hU : IsOpen U) {g : V → W} (hg : ContDiffOn 𝕜 m g U) :
    ∃ Ψ : OpenPartialHomeomorph Y Y, ContDiffOn 𝕜 m Ψ Ψ.source ∧ ContDiffOn 𝕜 m Ψ.symm Ψ.target ∧
      (∀ x, x ∈ Ψ.source ↔ (A.symm (x - c₀)).1 ∈ U) ∧
      ∀ x, Ψ x = A ((A.symm (x - c₀)).1, (A.symm (x - c₀)).2 - g (A.symm (x - c₀)).1) := by
  have hminus : ContDiffOn 𝕜 m (fun p : V × W ↦ (p.1, p.2 - g p.1)) (Prod.fst ⁻¹' U) :=
    contDiffOn_fst.prodMk (contDiffOn_snd.sub
      (hg.comp contDiffOn_fst (fun _ hp ↦ hp)))
  have hplus : ContDiffOn 𝕜 m (fun p : V × W ↦ (p.1, p.2 + g p.1)) (Prod.fst ⁻¹' U) :=
    contDiffOn_fst.prodMk (contDiffOn_snd.add
      (hg.comp contDiffOn_fst (fun _ hp ↦ hp)))
  -- Subtract the smooth graph in the transverse coordinate.
  let shear : OpenPartialHomeomorph (V × W) (V × W) :=
    { toFun := fun p ↦ (p.1, p.2 - g p.1)
      invFun := fun p ↦ (p.1, p.2 + g p.1)
      source := Prod.fst ⁻¹' U
      target := Prod.fst ⁻¹' U
      map_source' := fun _ hp ↦ hp
      map_target' := fun _ hp ↦ hp
      left_inv' := fun p _ ↦ by simp
      right_inv' := fun p _ ↦ by simp
      open_source := hU.preimage continuous_fst
      open_target := hU.preimage continuous_fst
      continuousOn_toFun := hminus.continuousOn
      continuousOn_invFun := hplus.continuousOn }
  let affine := (Homeomorph.addRight (-c₀)).trans A.symm.toHomeomorph
  let Ψ := (affine.toOpenPartialHomeomorph.trans shear).transHomeomorph A.toHomeomorph
  have hΨ_apply (x : Y) : Ψ x =
      A ((A.symm (x - c₀)).1, (A.symm (x - c₀)).2 - g (A.symm (x - c₀)).1) := by
    simp only [Ψ, OpenPartialHomeomorph.transHomeomorph_apply, Function.comp_apply,
      OpenPartialHomeomorph.trans_apply, Homeomorph.toOpenPartialHomeomorph_apply,
      affine, Homeomorph.trans_apply, Homeomorph.coe_addRight,
      ContinuousLinearEquiv.coe_toHomeomorph, ← sub_eq_add_neg]
    rfl
  refine ⟨Ψ, ?_, ?_, fun x ↦ ?_, hΨ_apply⟩
  · exact A.contDiff.comp_contDiffOn
      (hminus.comp (A.symm.contDiff.comp (contDiff_id.add contDiff_const)).contDiffOn
        (fun _ (hp : _ ∈ Ψ.source) ↦ hp.2))
  · exact (A.contDiff.comp_contDiffOn
      (hplus.comp A.symm.contDiff.contDiffOn (fun _ hp ↦ Set.mem_of_mem_inter_left hp))).add
        contDiffOn_const
  · simp [Ψ, affine, shear, ← sub_eq_add_neg]

end ContinuousLinearEquiv

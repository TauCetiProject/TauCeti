/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.RegularValue.Level

/-!
# Regular levels of scalar functions

Let `f : M → ℝ` be a function on a boundaryless manifold modelled on a finite-dimensional real
space `E`, which is `C¹` at every point of the level `f⁻¹(c)`, and let `c` be a regular value of
`f`. Then the actual subtype `{x // f x = c}` carries the atlas
`TauCeti.scalarRegularLevelChartedSpace`, modelled on `Fin (dim E - 1) → ℝ`, and is a `C^m`
manifold when `f` is `C^m` at the points of the level, `m ≥ 1`
(`TauCeti.isManifold_scalarRegularLevel`).

This is the regular-level atlas `TauCeti.regularLevelChartedSpace` of a map into a
finite-dimensional space, for the target `ℝ`, with the model dimension `dim E - dim ℝ` written as
`dim E - 1`. The linearization at `x` is the derivative

`D_x = fderiv ℝ (f ∘ (extChartAt I x).symm) (extChartAt I x x)`

of `f` in the preferred extended chart. Writing `π_x` for the chosen projection of `E` onto
`ker D_x` and `K_x : ker D_x ≃ (Fin (dim E - 1) → ℝ)` for the index-model identification, the
preferred chart at `x` is

`w ↦ K_x (π_x (extChartAt I x w - extChartAt I x x))`

(`TauCeti.scalarRegularLevelChartAt_apply`). Its inverse is the inverse preferred extended chart
of `M` applied to the inverse implicit-function chart of `f - c` on the zero slice
(`TauCeti.coe_scalarRegularLevelChartAt_symm_apply`). These explicit charts, rather than an
existential atlas, are what comparisons with normal forms of `f` near the level use; the
existential `TauCeti.exists_isManifold_sectionZero_of_contMDiff` does not determine them.

For this atlas the level is an embedded submanifold: the inclusion `{x // f x = c} → M` is a
`C^m` immersion with complement `ℝ` and a topological embedding, hence a smooth embedding
(`TauCeti.isSmoothEmbedding_coe_scalarRegularLevel`), and its differential at `x` has range
`ker (mfderiv I 𝓘(ℝ) f x)` (`TauCeti.range_mfderiv_coe_scalarRegularLevel`).

## Main declarations

* `TauCeti.scalarRegularLevelChartAt` and `TauCeti.scalarRegularLevelChartedSpace`: the preferred
  charts and the atlas of a regular scalar level.
* `TauCeti.scalarRegularLevelChartAt_apply`, `TauCeti.scalarRegularLevelChartAt_source`,
  `TauCeti.scalarRegularLevelChartAt_symm_zero`,
  `TauCeti.mem_scalarRegularLevelChartAt_target_iff` and
  `TauCeti.coe_scalarRegularLevelChartAt_symm_apply`: the chart formulas.
* `TauCeti.isManifold_scalarRegularLevel`: the level is a manifold of dimension `dim E - 1`.
* `TauCeti.isImmersionOfComplement_coe_scalarRegularLevel` and
  `TauCeti.isSmoothEmbedding_coe_scalarRegularLevel`: the inclusion of the level is an immersion
  with complement `ℝ` and a smooth embedding.
* `TauCeti.range_mfderiv_coe_scalarRegularLevel`: the tangent space of the level at `x` is the
  kernel of the differential of `f` at `x`.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Graduate Texts in Mathematics 218,
  Springer, 2013, Corollary 5.14 (regular level sets) and Proposition 5.38 (their tangent
  spaces).
-/

public section

open Function Module Set
open scoped ContDiff Manifold Topology

namespace TauCeti

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] {f : M → ℝ} {c : ℝ}

variable (E) in
/-- The model dimension `dim E - dim ℝ` of a regular scalar level is `dim E - 1`. -/
private theorem finrank_sub_finrank_real : finrank ℝ E - finrank ℝ ℝ = finrank ℝ E - 1 := by
  rw [finrank_self]

variable [I.Boundaryless] [ChartedSpace H M] [FiniteDimensional ℝ E]
  (hf : ∀ x, f x = c → ContMDiffAt I 𝓘(ℝ) 1 f x) (hreg : IsRegularValue I 𝓘(ℝ) f c)

/-- The preferred chart at a point `x` of a regular level `f⁻¹(c)`, modelled on
`Fin (dim E - 1) → ℝ`: the regular-level chart `TauCeti.regularLevelChartAt` of `f` at `x`. It
reads a point `w` as the kernel component of `extChartAt I x w - extChartAt I x x` for the
derivative of `f` in the preferred extended chart at `x`
(`TauCeti.scalarRegularLevelChartAt_apply`). -/
noncomputable def scalarRegularLevelChartAt (x : {x : M // f x = c}) :
    OpenPartialHomeomorph {x : M // f x = c} (Fin (finrank ℝ E - 1) → ℝ) :=
  regularLevelChartAt hf hreg (finrank_sub_finrank_real E) x

/-- Every point of the level lies in the source of its preferred chart. -/
theorem mem_scalarRegularLevelChartAt_source (x : {x : M // f x = c}) :
    x ∈ (scalarRegularLevelChartAt hf hreg x).source :=
  mem_regularLevelChartAt_source hf hreg _ x

/-- The atlas of a regular scalar level `f⁻¹(c)`: the regular-level atlas
`TauCeti.regularLevelChartedSpace` of `f`, with preferred charts
`TauCeti.scalarRegularLevelChartAt`. It is modelled on `Fin (dim E - 1) → ℝ`. -/
@[irreducible]
noncomputable def scalarRegularLevelChartedSpace :
    ChartedSpace (Fin (finrank ℝ E - 1) → ℝ) {x : M // f x = c} :=
  regularLevelChartedSpace hf hreg (finrank_sub_finrank_real E)

/-- The installed preferred charts are `TauCeti.scalarRegularLevelChartAt`. -/
@[simp]
theorem scalarRegularLevelChartedSpace_chartAt (x : {x : M // f x = c}) :
    @chartAt (Fin (finrank ℝ E - 1) → ℝ) _ {x : M // f x = c} _
      (scalarRegularLevelChartedSpace hf hreg) x = scalarRegularLevelChartAt hf hreg x := by
  unfold scalarRegularLevelChartedSpace
  exact regularLevelChartedSpace_chartAt hf hreg _ x

/-- The installed atlas consists exactly of the preferred charts. -/
@[simp]
theorem scalarRegularLevelChartedSpace_atlas :
    @atlas (Fin (finrank ℝ E - 1) → ℝ) _ {x : M // f x = c} _
      (scalarRegularLevelChartedSpace hf hreg) = range (scalarRegularLevelChartAt hf hreg) := by
  unfold scalarRegularLevelChartedSpace
  exact regularLevelChartedSpace_atlas hf hreg _

/-- The preferred chart at `x` reads the displacement `extChartAt I x w - extChartAt I x x` through
the chosen projection onto the kernel of the preferred-chart derivative `D` of `f` at `x`,
followed by the identification of that kernel with `Fin (dim E - 1) → ℝ`. -/
theorem scalarRegularLevelChartAt_apply (x w : {x : M // f x = c}) :
    scalarRegularLevelChartAt hf hreg x w =
      let D := fderiv ℝ (f ∘ (extChartAt I (x : M)).symm) (extChartAt I (x : M) x)
      D.kerModelEquiv D.isFredholm_of_finiteDimensional.finite_ker
        (hreg.isRegularPoint x.2).finrank_ker_fderiv_comp_extChartAt_symm
        (Classical.choose D.isFredholm_of_finiteDimensional.closedComplemented_ker
          (extChartAt I (x : M) w - extChartAt I (x : M) x)) :=
  regularLevelChartAt_apply hf hreg _ x w

/-- A preferred chart is centred at its point. -/
@[simp]
theorem scalarRegularLevelChartAt_apply_self (x : {x : M // f x = c}) :
    scalarRegularLevelChartAt hf hreg x x = 0 :=
  regularLevelChartAt_apply_self hf hreg _ x

/-- The origin belongs to the target of every preferred chart. -/
theorem mem_scalarRegularLevelChartAt_target (x : {x : M // f x = c}) :
    (0 : Fin (finrank ℝ E - 1) → ℝ) ∈ (scalarRegularLevelChartAt hf hreg x).target :=
  mem_regularLevelChartAt_target hf hreg _ x

/-- The inverse preferred chart at `x` sends the origin to `x`. -/
@[simp]
theorem scalarRegularLevelChartAt_symm_zero (x : {x : M // f x = c}) :
    (scalarRegularLevelChartAt hf hreg x).symm 0 = x :=
  regularLevelChartAt_symm_zero hf hreg _ x

/-- The source of the preferred chart at `x`: points of the level in the preferred chart of `M`
at `x` whose extended coordinates lie in the source of the implicit-function chart of `f - c` and
in the neighbourhood where its derivative stays invertible. -/
@[simp]
theorem scalarRegularLevelChartAt_source (x : {x : M // f x = c}) :
    (scalarRegularLevelChartAt hf hreg x).source =
      let D := fderiv ℝ (f ∘ (extChartAt I (x : M)).symm) (extChartAt I (x : M) x)
      let hD : HasStrictFDerivAt (fun y ↦ f ((extChartAt I (x : M)).symm y) - c) D
          (extChartAt I (x : M) x) :=
        ((hf x x.2).contDiffAt_comp_extChartAt_symm.hasStrictFDerivAt one_ne_zero).sub_const c
      let hD' := LinearMap.range_eq_top.2
        (hreg.isRegularPoint x.2).surjective_fderiv_comp_extChartAt_symm
      let hker := D.isFredholm_of_finiteDimensional.closedComplemented_ker
      {w : {x : M // f x = c} | (w : M) ∈ (chartAt H (x : M)).source ∧
        extChartAt I (x : M) w ∈
        (hD.implicitToOpenPartialHomeomorphOfComplemented _ D hD' hker).source ∩
          hD.implicitCoordSource hD' hker} :=
  regularLevelChartAt_source hf hreg _ x

/-- The target of the preferred chart at `x`: model points `k` whose kernel vector `K.symm k`
gives a point `(0, K.symm k)` of the implicit-function chart target of `f - c`, whose inverse lies
in the regular neighbourhood and in the target of the preferred extended chart at `x`. -/
@[simp]
theorem mem_scalarRegularLevelChartAt_target_iff (x : {x : M // f x = c})
    (k : Fin (finrank ℝ E - 1) → ℝ) :
    k ∈ (scalarRegularLevelChartAt hf hreg x).target ↔
      let D := fderiv ℝ (f ∘ (extChartAt I (x : M)).symm) (extChartAt I (x : M) x)
      let hD : HasStrictFDerivAt (fun y ↦ f ((extChartAt I (x : M)).symm y) - c) D
          (extChartAt I (x : M) x) :=
        ((hf x x.2).contDiffAt_comp_extChartAt_symm.hasStrictFDerivAt one_ne_zero).sub_const c
      let hD' := LinearMap.range_eq_top.2
        (hreg.isRegularPoint x.2).surjective_fderiv_comp_extChartAt_symm
      let hker := D.isFredholm_of_finiteDimensional.closedComplemented_ker
      let K := D.kerModelEquiv D.isFredholm_of_finiteDimensional.finite_ker
        (hreg.isRegularPoint x.2).finrank_ker_fderiv_comp_extChartAt_symm
      let Φ := hD.implicitToOpenPartialHomeomorphOfComplemented _ D hD' hker
      (0, K.symm k) ∈ Φ.target ∧ Φ.symm (0, K.symm k) ∈ hD.implicitCoordSource hD' hker ∧
        Φ.symm (0, K.symm k) ∈ (extChartAt I (x : M)).target :=
  mem_regularLevelChartAt_target_iff hf hreg _ x k

/-- On its target, the inverse preferred chart at `x` is the inverse preferred extended chart of
`M` at `x`, applied to the inverse implicit-function chart of `f - c` on the zero slice. -/
theorem coe_scalarRegularLevelChartAt_symm_apply (x : {x : M // f x = c})
    {k : Fin (finrank ℝ E - 1) → ℝ} (hk : k ∈ (scalarRegularLevelChartAt hf hreg x).target) :
    ((scalarRegularLevelChartAt hf hreg x).symm k : M) =
      let D := fderiv ℝ (f ∘ (extChartAt I (x : M)).symm) (extChartAt I (x : M) x)
      let hD : HasStrictFDerivAt (fun y ↦ f ((extChartAt I (x : M)).symm y) - c) D
          (extChartAt I (x : M) x) :=
        ((hf x x.2).contDiffAt_comp_extChartAt_symm.hasStrictFDerivAt one_ne_zero).sub_const c
      let hD' := LinearMap.range_eq_top.2
        (hreg.isRegularPoint x.2).surjective_fderiv_comp_extChartAt_symm
      let hker := D.isFredholm_of_finiteDimensional.closedComplemented_ker
      let K := D.kerModelEquiv D.isFredholm_of_finiteDimensional.finite_ker
        (hreg.isRegularPoint x.2).finrank_ker_fderiv_comp_extChartAt_symm
      (extChartAt I (x : M)).symm
        ((hD.implicitToOpenPartialHomeomorphOfComplemented _ D hD' hker).symm (0, K.symm k)) :=
  coe_regularLevelChartAt_symm_apply hf hreg _ x hk

/-- A regular level `f⁻¹(c)` of a function which is `C^m` near the level, with `m ≥ 1`, is a
`C^m` manifold of dimension `dim E - 1` for its preferred atlas. -/
theorem isManifold_scalarRegularLevel {m : ℕ∞ω} [IsManifold I m M] (hm : 1 ≤ m)
    (hfm : ∀ x, f x = c → ContMDiffAt I 𝓘(ℝ) m f x) (hreg : IsRegularValue I 𝓘(ℝ) f c) :
    letI := scalarRegularLevelChartedSpace (fun x hx ↦ (hfm x hx).of_le hm) hreg
    IsManifold 𝓘(ℝ, Fin (finrank ℝ E - 1) → ℝ) m {x : M // f x = c} := by
  unfold scalarRegularLevelChartedSpace
  exact isManifold_regularLevel hm hfm hreg (finrank_sub_finrank_real E)

/-- **The inclusion of a regular level is an immersion with complement `ℝ`.** For the preferred
atlas `TauCeti.scalarRegularLevelChartedSpace`, the inclusion of a regular level `f⁻¹(c)` of a
function which is `C^m` near the level, `m ≥ 1`, is a `C^m` immersion whose normal forms have the
line `ℝ` of values of `f` as complement. -/
theorem isImmersionOfComplement_coe_scalarRegularLevel {m : ℕ∞ω} [IsManifold I m M] (hm : 1 ≤ m)
    (hfm : ∀ x, f x = c → ContMDiffAt I 𝓘(ℝ) m f x) (hreg : IsRegularValue I 𝓘(ℝ) f c) :
    letI := scalarRegularLevelChartedSpace (fun x hx ↦ (hfm x hx).of_le hm) hreg
    Manifold.IsImmersionOfComplement ℝ 𝓘(ℝ, Fin (finrank ℝ E - 1) → ℝ) I m
      (Subtype.val : {x : M // f x = c} → M) := by
  unfold scalarRegularLevelChartedSpace
  exact isImmersionOfComplement_coe_regularLevel hm hfm hreg (finrank_sub_finrank_real E)

/-- **A regular level is an embedded submanifold.** For the preferred atlas
`TauCeti.scalarRegularLevelChartedSpace`, the inclusion of a regular level `f⁻¹(c)` of a function
which is `C^m` near the level, `m ≥ 1`, is a `C^m` smooth embedding. -/
theorem isSmoothEmbedding_coe_scalarRegularLevel {m : ℕ∞ω} [IsManifold I m M] (hm : 1 ≤ m)
    (hfm : ∀ x, f x = c → ContMDiffAt I 𝓘(ℝ) m f x) (hreg : IsRegularValue I 𝓘(ℝ) f c) :
    letI := scalarRegularLevelChartedSpace (fun x hx ↦ (hfm x hx).of_le hm) hreg
    Manifold.IsSmoothEmbedding 𝓘(ℝ, Fin (finrank ℝ E - 1) → ℝ) I m
      (Subtype.val : {x : M // f x = c} → M) := by
  unfold scalarRegularLevelChartedSpace
  exact isSmoothEmbedding_coe_regularLevel hm hfm hreg (finrank_sub_finrank_real E)

/-- **The tangent space of a regular level is the kernel of `df`.** At a point `x` of a regular
level `f⁻¹(c)`, the differential of the inclusion, for the preferred atlas
`TauCeti.scalarRegularLevelChartedSpace`, has range the kernel of the differential of `f` at
`x`. -/
theorem range_mfderiv_coe_scalarRegularLevel [IsManifold I 1 M] (x : {x : M // f x = c}) :
    letI := scalarRegularLevelChartedSpace hf hreg
    (mfderiv 𝓘(ℝ, Fin (finrank ℝ E - 1) → ℝ) I (Subtype.val : {x : M // f x = c} → M) x).range =
      (mfderiv I 𝓘(ℝ) f x).ker := by
  unfold scalarRegularLevelChartedSpace
  exact range_mfderiv_coe_regularLevel hf hreg (finrank_sub_finrank_real E) x

end TauCeti

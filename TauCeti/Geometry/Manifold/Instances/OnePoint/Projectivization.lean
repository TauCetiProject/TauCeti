/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.Diffeomorph
public import TauCeti.Geometry.Manifold.Instances.OnePoint.Basic
public import TauCeti.Geometry.Manifold.Instances.Projectivization
public import TauCeti.LinearAlgebra.Projectivization.OnePoint

/-!
# The projective line `OnePoint 𝕜` is the projective space `ℙ 𝕜 (Fin 2 → 𝕜)`

Mathlib identifies the one-point compactification `OnePoint 𝕜` with the projectivization
`ℙ 𝕜 (Fin 2 → 𝕜)` as a set, by `OnePoint.equivProjectivization`: `t ↦ [t : 1]` and
`∞ ↦ [1 : 0]`. Both sides carry an analytic manifold structure over a proper nontrivially normed
field `𝕜`. The projective line `OnePoint 𝕜` is charted by its affine coordinate and its inverted
coordinate (`OnePoint.instChartedSpace`), modelled on `𝕜`; the projective space is charted by its
two standard affine charts (`Projectivization.instChartedSpace`), modelled on `Fin 1 → 𝕜`.

This file shows that the two atlases match under `OnePoint.equivProjectivization`, through the
linear identification of `Fin 1 → 𝕜` with `𝕜` that sends `z` to the constant family `fun _ ↦ z`.
The affine chart at the coordinate `1` reads `[t : 1]` as `t`, so it is the affine coordinate of
`OnePoint 𝕜`; the affine chart at the coordinate `0` reads `[t : 1]` as `t⁻¹` and `[1 : 0]` as `0`,
so it is the inverted coordinate. Consequently the identification and its inverse are analytic,
and `OnePoint.equivProjectivization` is a `C^n` diffeomorphism for every order `n`
(`OnePoint.diffeomorphProjectivization`), and in particular a homeomorphism (through
`Diffeomorph.toHomeomorph`).

For `𝕜 = ℂ` this is the biholomorphism between the Riemann sphere `OnePoint ℂ` and the complex
projective line `ℂℙ¹`, so that statements about either model of the Riemann sphere transport to
the other.

## Main declarations

* `OnePoint.affineChart_one_equivProjectivization` and
  `OnePoint.affineChart_zero_equivProjectivization`: the two affine charts of `ℙ 𝕜 (Fin 2 → 𝕜)`
  are the affine and inverted coordinates of `OnePoint 𝕜`.
* `OnePoint.contMDiff_equivProjectivization` and `OnePoint.contMDiff_equivProjectivization_symm`:
  the identification and its inverse are analytic.
* `OnePoint.diffeomorphProjectivization`: the identification as a `C^n` diffeomorphism.

## References

* Otto Forster, *Lectures on Riemann Surfaces*, Graduate Texts in Mathematics 81,
  Springer, 1981, §1.5.
* P. Griffiths and J. Harris, *Principles of Algebraic Geometry*, Chapter 0, §1.
-/

public noncomputable section

open Set
open scoped ContDiff Manifold LinearAlgebra.Projectivization

namespace OnePoint

/-! ### The charts in homogeneous coordinates -/

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [DecidableEq 𝕜]

/-- The standard affine chart of `ℙ 𝕜 (Fin 2 → 𝕜)` at the coordinate `1` is the affine coordinate
of `OnePoint 𝕜`: it reads `[t : 1]` as `t`. Off its domain, at `[1 : 0]`, both sides are `0`. -/
@[simp]
theorem affineChart_one_equivProjectivization (x : OnePoint 𝕜) :
    Projectivization.affineChart 1 (equivProjectivization 𝕜 x) = fun _ ↦ affineChart x := by
  induction x using OnePoint.rec <;> funext j <;> fin_cases j <;> simp

/-- The standard affine chart of `ℙ 𝕜 (Fin 2 → 𝕜)` at the coordinate `0` is the inverted coordinate
of `OnePoint 𝕜`: it reads `[t : 1]` as `t⁻¹` and `[1 : 0]` as `0`. -/
@[simp]
theorem affineChart_zero_equivProjectivization [ProperSpace 𝕜] (x : OnePoint 𝕜) :
    Projectivization.affineChart 0 (equivProjectivization 𝕜 x) = fun _ ↦ invChart x := by
  induction x using OnePoint.rec <;> simp

/-! ### Analyticity -/

variable [ProperSpace 𝕜]

/-- The identification `OnePoint.equivProjectivization` of the projective line with
`ℙ 𝕜 (Fin 2 → 𝕜)` is analytic. -/
theorem contMDiff_equivProjectivization :
    ContMDiff 𝓘(𝕜) 𝓘(𝕜, Fin 1 → 𝕜) ω (equivProjectivization 𝕜) := by
  have hconst : ContMDiff 𝓘(𝕜) 𝓘(𝕜, Fin 1 → 𝕜) ω fun z : 𝕜 ↦ fun _ : Fin 1 ↦ z :=
    (contDiff_pi.2 fun _ ↦ contDiff_id).contMDiff
  -- Near each point, the identification is the inverse of an affine chart of `ℙ 𝕜 (Fin 2 → 𝕜)`
  -- composed with the chart of `OnePoint 𝕜` at that point.
  intro x
  induction x using OnePoint.rec with
  | infty =>
    refine (((Projectivization.contMDiff_affineChart_symm 0 ω).comp_contMDiffOn
      (hconst.comp_contMDiffOn (contMDiffOn_chart (x := (∞ : OnePoint 𝕜))))).congr
      fun y hy ↦ ?_).contMDiffAt ((chartAt 𝕜 _).open_source.mem_nhds (mem_chart_source 𝕜 _))
    rw [chartAt_infty, invChart_source, mem_compl_singleton_iff] at hy
    simp only [Function.comp_apply, chartAt_infty, ← affineChart_zero_equivProjectivization]
    exact ((Projectivization.affineChart 0).left_inv
      (by simpa using hy)).symm
  | coe z =>
    refine (((Projectivization.contMDiff_affineChart_symm 1 ω).comp_contMDiffOn
      (hconst.comp_contMDiffOn (contMDiffOn_chart (x := (z : OnePoint 𝕜))))).congr
      fun y hy ↦ ?_).contMDiffAt ((chartAt 𝕜 _).open_source.mem_nhds (mem_chart_source 𝕜 _))
    rw [chartAt_coe, affineChart_source, mem_compl_singleton_iff] at hy
    simp only [Function.comp_apply, chartAt_coe, ← affineChart_one_equivProjectivization]
    exact ((Projectivization.affineChart 1).left_inv
      (by simpa using hy)).symm

/-- The inverse of the identification `OnePoint.equivProjectivization` of the projective line with
`ℙ 𝕜 (Fin 2 → 𝕜)` is analytic. -/
theorem contMDiff_equivProjectivization_symm :
    ContMDiff 𝓘(𝕜, Fin 1 → 𝕜) 𝓘(𝕜) ω (equivProjectivization 𝕜).symm := by
  have heval : ContMDiff 𝓘(𝕜, Fin 1 → 𝕜) 𝓘(𝕜) ω fun z : Fin 1 → 𝕜 ↦ z 0 :=
    (ContinuousLinearMap.proj 0 : (Fin 1 → 𝕜) →L[𝕜] 𝕜).contDiff.contMDiff
  -- Near each point, the inverse is the inverse of a chart of `OnePoint 𝕜` composed with an
  -- affine chart of `ℙ 𝕜 (Fin 2 → 𝕜)` containing that point.
  intro p
  obtain ⟨i, hp⟩ := Projectivization.exists_mem_affineOpen p
  have hnhds := (Projectivization.isOpen_affineOpen i).mem_nhds hp
  fin_cases i
  · refine ((contMDiff_invChart_symm.comp_contMDiffOn (heval.comp_contMDiffOn
      (Projectivization.contMDiffOn_affineChart 0 ω))).congr fun q hq ↦ ?_).contMDiffAt hnhds
    obtain ⟨y, rfl⟩ := (equivProjectivization 𝕜).surjective q
    rw [equivProjectivization_mem_affineOpen_zero_iff] at hq
    simpa using (invChart.left_inv (x := y) (by simpa using hq)).symm
  · refine ((contMDiff_coe.comp_contMDiffOn (heval.comp_contMDiffOn
      (Projectivization.contMDiffOn_affineChart 1 ω))).congr fun q hq ↦ ?_).contMDiffAt hnhds
    obtain ⟨y, rfl⟩ := (equivProjectivization 𝕜).surjective q
    rw [equivProjectivization_mem_affineOpen_one_iff] at hq
    obtain ⟨z, rfl⟩ := ne_infty_iff_exists.1 hq
    simp

/-! ### The diffeomorphism -/

variable (𝕜)

/-- The projective line `OnePoint 𝕜` and the projective space `ℙ 𝕜 (Fin 2 → 𝕜)` are `C^n`
diffeomorphic for every `n`, through `OnePoint.equivProjectivization`: `t ↦ [t : 1]` and
`∞ ↦ [1 : 0]`. For `𝕜 = ℂ` and `n = ∞` this is the biholomorphism between the Riemann sphere and
`ℂℙ¹`; its underlying homeomorphism is `Diffeomorph.toHomeomorph`. -/
def diffeomorphProjectivization (n : ℕ∞ω) :
    OnePoint 𝕜 ≃ₘ^n⟮𝓘(𝕜), 𝓘(𝕜, Fin 1 → 𝕜)⟯ ℙ 𝕜 (Fin 2 → 𝕜) where
  toEquiv := equivProjectivization 𝕜
  contMDiff_toFun := contMDiff_equivProjectivization.of_le le_top
  contMDiff_invFun := contMDiff_equivProjectivization_symm.of_le le_top

@[simp]
theorem coe_diffeomorphProjectivization (n : ℕ∞ω) :
    ⇑(diffeomorphProjectivization 𝕜 n) = equivProjectivization 𝕜 :=
  (rfl)

@[simp]
theorem coe_diffeomorphProjectivization_symm (n : ℕ∞ω) :
    ⇑(diffeomorphProjectivization 𝕜 n).symm = (equivProjectivization 𝕜).symm :=
  (rfl)

end OnePoint

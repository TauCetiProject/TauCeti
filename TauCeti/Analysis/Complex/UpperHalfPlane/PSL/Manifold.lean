/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.UpperHalfPlane.Manifold
public import TauCeti.Analysis.Complex.UpperHalfPlane.PSL.Action
public import TauCeti.Geometry.Manifold.Algebra.SMul

import TauCeti.Analysis.Complex.UpperHalfPlane.MoebiusAction

/-!
# Smooth and holomorphic matrix-group actions on the upper half-plane

Every element of `PSL(2, ℝ)` acts on the upper half-plane by a biholomorphism, while every element
of `GL(2, ℝ)` (and hence of `PGL(2, ℝ)`, `SL(2, R)`, and `PSL(2, R)` for any `ℝ`-algebra `R`) acts
by a real-analytic map for the real manifold structure `𝓘(ℝ, ℂ)`: positive-determinant matrices act
holomorphically (`UpperHalfPlane.contMDiff_smul`), the reflection `UpperHalfPlane.J : z ↦ -conj z`
is the restriction of a continuous real-linear involution of `ℂ`, and negative-determinant matrices
factor through `J`.

Expressing these actions as `ContMDiffConstSMul` instances packages each transformation through the
generic `Diffeomorph.constSmul` constructor, and subgroups inherit the same smooth or holomorphic
actions through `SetLike.contMDiffConstSMul`.

## Main declarations

* `UpperHalfPlane.instContMDiffConstSMulPSL2`: the action of each element of `PSL(2, ℝ)` is
  holomorphic (`𝓘(ℂ, ℂ)`).
* `TauCeti.UpperHalfPlane.contMDiff_J_smul`: the reflection `UpperHalfPlane.J : z ↦ -conj z` is
  real-analytic on `ℍ`.
* `TauCeti.UpperHalfPlane.instContMDiffConstSMulGLReal`,
  `TauCeti.UpperHalfPlane.instContMDiffConstSMulPGLReal`,
  `TauCeti.UpperHalfPlane.instContMDiffConstSMulSL2Real`,
  `TauCeti.UpperHalfPlane.instContMDiffConstSMulPSL2Real`: `GL(2, ℝ)`, `PGL(2, ℝ)`, `SL(2, R)`, and
  `PSL(2, R)` act on `ℍ` by real-analytic maps (`𝓘(ℝ, ℂ)`).

## References

* Svetlana Katok, *Fuchsian Groups*, University of Chicago Press (1992), §1.1.
* Alan Beardon, *The Geometry of Discrete Groups*, Springer GTM 91 (1983), §7.2.
-/

public section

noncomputable section

open scoped ComplexConjugate ContDiff Manifold MatrixGroups UpperHalfPlane

namespace UpperHalfPlane

/-- The action of each element of `PSL(2, ℝ)` on the upper half-plane is holomorphic. -/
instance instContMDiffConstSMulPSL2 : ContMDiffConstSMul 𝓘(ℂ, ℂ) ∞ PSL(2, ℝ) ℍ where
  contMDiff_const_smul q := by
    refine QuotientGroup.induction_on q fun g ↦ ?_
    simpa only [pslMk_smul, Matrix.SpecialLinearGroup.toGL_smul] using
      UpperHalfPlane.contMDiff_smul (n := ∞)
        (g := Matrix.SpecialLinearGroup.toGL g) (by simp)

end UpperHalfPlane

namespace TauCeti.UpperHalfPlane

open _root_.UpperHalfPlane

/-- The reflection `UpperHalfPlane.J : z ↦ -conj z` is real-analytic on `ℍ` (and hence `C^n` of
every order `n : ℕ∞ω`). -/
theorem contMDiff_J_smul {n : ℕ∞ω} : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) n (J • · : ℍ → ℍ) := by
  apply ContMDiff.of_comp_isOpenEmbedding isOpenEmbedding_coe
  have hcoe : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) n UpperHalfPlane.coe := fun _ ↦ contMDiffAt_extChartAt
  have hfun : UpperHalfPlane.coe ∘ (J • · : ℍ → ℍ) = (-Complex.conjCLE : ℂ →L[ℝ] ℂ) ∘
      UpperHalfPlane.coe := by
    funext z
    simp [coe_J_smul]
  rw [hfun]
  exact (-Complex.conjCLE : ℂ →L[ℝ] ℂ).contDiff.contMDiff.comp hcoe

/-- Every element of `GL(2, ℝ)` acts on `ℍ` by a real-analytic map (and hence smoothly of every
order `n : ℕ∞ω`). -/
instance instContMDiffConstSMulGLReal {n : ℕ∞ω} :
    ContMDiffConstSMul 𝓘(ℝ, ℂ) n (GL (Fin 2) ℝ) ℍ where
  contMDiff_const_smul g := by
    -- Positive-determinant matrices act holomorphically; negative-determinant ones factor via `J`.
    have hpos {h : GL (Fin 2) ℝ} (hh : 0 < h.det.val) :
        ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) n (h • · : ℍ → ℍ) := by
      simpa only [modelWithCornersSelf_restrictScalars] using
        ((UpperHalfPlane.contMDiff_smul (n := ω) hh).restrictScalars ℝ).of_le le_top
    rcases g.det.ne_zero.lt_or_gt with hg | hg
    · have hJg : 0 < (J * g).det.val := by simpa using hg
      have hcomp : (g • · : ℍ → ℍ) = (J • ·) ∘ ((J * g) • ·) := by
        funext z
        simp [smul_smul, ← mul_assoc, ← sq]
      rw [hcomp]
      exact contMDiff_J_smul.comp (hpos hJg)
    · exact hpos hg

/-- Every element of `PGL(2, ℝ)` acts on `ℍ` by a real-analytic map. -/
instance instContMDiffConstSMulPGLReal {n : ℕ∞ω} :
    ContMDiffConstSMul 𝓘(ℝ, ℂ) n PGL(2, ℝ) ℍ where
  contMDiff_const_smul q := by
    induction q using Matrix.ProjGenLinGroup.induction_on with | mk g =>
    simpa only [pglMk_smul] using contMDiff_const_smul (I := 𝓘(ℝ, ℂ)) (n := n) g

/-- Every element of `SL(2, R)` acts on `ℍ` by a real-analytic map. -/
instance instContMDiffConstSMulSL2Real {R : Type*} [CommRing R] [Algebra R ℝ] {n : ℕ∞ω} :
    ContMDiffConstSMul 𝓘(ℝ, ℂ) n SL(2, R) ℍ :=
  MulAction.contMDiffConstSMul_compHom (I := 𝓘(ℝ, ℂ)) (f := Matrix.SpecialLinearGroup.mapGL ℝ)

/-- Every element of `PSL(2, R)` acts on `ℍ` by a real-analytic map. -/
instance instContMDiffConstSMulPSL2Real {R : Type*} [CommRing R] [Algebra R ℝ] {n : ℕ∞ω} :
    ContMDiffConstSMul 𝓘(ℝ, ℂ) n PSL(2, R) ℍ where
  contMDiff_const_smul q := by
    refine QuotientGroup.induction_on q fun g ↦ ?_
    simpa only [pslMk_smul] using contMDiff_const_smul (I := 𝓘(ℝ, ℂ)) (n := n) g

end TauCeti.UpperHalfPlane

end

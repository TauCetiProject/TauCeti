/-
Copyright (c) 2026 The Tau Ceti authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti authors
-/
module

public import Mathlib.Analysis.Complex.UpperHalfPlane.Metric
public import Mathlib.Analysis.Complex.UpperHalfPlane.ProperAction
public import TauCeti.Analysis.Complex.UpperHalfPlane.PSL.Action
public import TauCeti.Topology.Algebra.Matrix.ProjectiveSpecialLinearGroup

/-!
# Proper action of `PSL(2, ℝ)` on the upper half-plane

The Möbius action of `PSL(2, ℝ)` on the upper half-plane is continuous, transitive, isometric
for the hyperbolic metric, and proper. Each of these is descended from the corresponding
property of Mathlib's `SL(2, ℝ)` action using the surjective quotient map
`SL(2, ℝ) → PSL(2, ℝ)`.

The isometric action extends to the whole of Mathlib's action `UpperHalfPlane.glAction` of
`GL(2, ℝ)` and to the induced action of `PGL(2, ℝ)`. This includes the orientation-reversing,
antiholomorphic elements of negative determinant: each is the reflection `z ↦ -conj z`, the
action of Mathlib's `UpperHalfPlane.J`, composed with an element of positive determinant.

## Main declarations

* `IsIsometricSMul (GL (Fin 2) ℝ) ℍ` and `IsIsometricSMul PGL(2, ℝ) ℍ`: every element of
  `GL(2, ℝ)` and of `PGL(2, ℝ)` acts on `ℍ` by an isometry of the hyperbolic distance.

## References

* Svetlana Katok, *Fuchsian Groups*, Chapter 1.
-/

public section

noncomputable section

open scoped MatrixGroups

open Matrix.SpecialLinearGroup UpperHalfPlane

namespace TauCeti.UpperHalfPlane

/-- The effective `PSL(2, ℝ)` action on the upper half-plane is jointly continuous. -/
instance : ContinuousSMul PSL(2, ℝ) ℍ where
  continuous_smul := by
    rw [← (QuotientGroup.isOpenQuotientMap_mk.prodMap IsOpenQuotientMap.id).continuous_comp_iff]
    have hfun :
        (fun p : PSL(2, ℝ) × ℍ ↦ p.1 • p.2) ∘
            Prod.map (QuotientGroup.mk : SL(2, ℝ) → PSL(2, ℝ)) id =
          fun p : SL(2, ℝ) × ℍ ↦ p.1 • p.2 := by
      funext p
      exact UpperHalfPlane.pslMk_smul p.1 p.2
    rw [hfun]
    exact continuous_smul

/-- The effective `PSL(2, ℝ)` action on the upper half-plane is by hyperbolic isometries. -/
instance : IsIsometricSMul PSL(2, ℝ) ℍ where
  isometry_smul q := by
    induction q using QuotientGroup.induction_on with | _ g =>
    simpa only [UpperHalfPlane.pslMk_smul] using isometry_smul ℍ g

/-- Every element of `GL(2, ℝ)` acts on `ℍ` by a hyperbolic isometry, including the
orientation-reversing elements of negative determinant, which act through complex
conjugation. -/
instance : IsIsometricSMul (GL (Fin 2) ℝ) ℍ where
  isometry_smul g := by
    -- an element of positive determinant acts as its normalized representative in `PSL(2, ℝ)`
    have pos (h : GL (Fin 2) ℝ) (hh : 0 < h.det.val) : Isometry (h • · : ℍ → ℍ) := by
      have hiso := isometry_smul ℍ (glPosToPSL2R ⟨h, (Matrix.mem_glpos h).2 hh⟩)
      simpa only [glPosToPSL2R_smul, Subgroup.mk_smul] using hiso
    rcases g.det.ne_zero.lt_or_gt with hg | hg
    · -- `g = J * (J * g)`, and `J * g` has positive determinant
      have hJg : 0 < (J * g).det.val := by simpa using hg
      have hfun : (g • · : ℍ → ℍ) = (J • ·) ∘ ((J * g) • ·) := by
        funext z
        rw [Function.comp_apply, smul_smul, ← mul_assoc, ← sq, J_sq, one_mul]
      -- the orientation-reversing involution `J : z ↦ -conj z` is an isometry
      have hJ : Isometry (J • · : ℍ → ℍ) :=
        Isometry.of_dist_eq fun z w ↦ by
          rw [UpperHalfPlane.dist_eq, UpperHalfPlane.dist_eq, coe_J_smul, coe_J_smul,
            dist_neg_neg, Complex.dist_conj_conj, J_smul_im, J_smul_im]
      rw [hfun]
      exact hJ.comp (pos (J * g) hJg)
    · exact pos g hg

/-- Every element of `PGL(2, ℝ)` acts on `ℍ` by a hyperbolic isometry. -/
instance : IsIsometricSMul PGL(2, ℝ) ℍ where
  isometry_smul g := by
    induction g using Matrix.ProjGenLinGroup.induction_on with | mk g =>
    simpa only [pglMk_smul] using isometry_smul ℍ g

/-- The effective `PSL(2, ℝ)` action on the upper half-plane is transitive. -/
instance : MulAction.IsPretransitive PSL(2, ℝ) ℍ where
  exists_smul_eq x y := by
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq SL(2, ℝ) x y
    exact ⟨(g : PSL(2, ℝ)), by simpa only [UpperHalfPlane.pslMk_smul] using hg⟩

/-- The orbit map at `I` for the effective `PSL(2, ℝ)` action is proper. -/
theorem isProperMap_psl_smul_I : IsProperMap fun g : PSL(2, ℝ) ↦ g • I := by
  apply isProperMap_of_comp_of_surj QuotientGroup.continuous_mk (by fun_prop)
  · have hfun :
        (fun g : PSL(2, ℝ) ↦ g • I) ∘
            (QuotientGroup.mk : SL(2, ℝ) → PSL(2, ℝ)) =
          fun g : SL(2, ℝ) ↦ g • I := by
      funext g
      exact UpperHalfPlane.pslMk_smul g I
    rw [hfun]
    exact isProperMap_smul_I
  · exact QuotientGroup.mk_surjective

/-- The effective `PSL(2, ℝ)` action on the upper half-plane is proper. -/
instance : ProperSMul PSL(2, ℝ) ℍ :=
  MulAction.properSMul_of_proper_orbitMap isProperMap_psl_smul_I

end TauCeti.UpperHalfPlane

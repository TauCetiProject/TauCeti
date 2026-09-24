/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.Algebra.SMul
public import Mathlib.Geometry.Manifold.Algebra.Structures
public import TauCeti.Geometry.Toric.Analytic.Cone.Manifold
public import TauCeti.Geometry.Toric.Analytic.Cone.TorusAction.Basic
public import TauCeti.Geometry.Toric.Analytic.Torus.Manifold

/-!
# The torus action on an affine toric chart is holomorphic

The coordinate-free complex torus `ComplexTorus N` acts on the complex points of every submonoid
`S` of the character lattice `N →+ ℤ`, and in particular on the affine chart of a toric cone, by
multiplying the value of a point on the monomial of `s ∈ S` by the value of the torus point on
`s`. This file proves that the action is jointly continuous and, for a cone with an extending
basis, jointly holomorphic.

Continuity holds for an arbitrary submonoid and for the monomial-embedding topology of any finite
generating family: every monomial value of `t • x` is the product of a character evaluation of `t`
and a monomial value of `x`. Holomorphy is stated for the charted-space structures of the torus
attached to any free presentation of its character lattice and of the affine chart attached to any
extending basis, numbering of the rays and generating family. In these coordinates a torus point
multiplies each chart coordinate by its value on the corresponding dual basis character, and both
factors are holomorphic.

These are the analytic properties of the affine torus actions which the torus action on the
realization of a fan is glued from.

## Main declarations

* `TauCeti.Toric.AffineSemigroupComplexPoint.continuousSMul_affinePointTopology_complexTorus`: the
  torus acts jointly continuously on the complex points of any finitely generated submonoid of the
  character lattice.
* `TauCeti.Toric.contMDiffSMul_coneChartedSpace`: the torus acts holomorphically on the affine
  chart of a cone with an extending basis.

## References

* W. Fulton, *Introduction to Toric Varieties*, §§1.2 and 2.1.
* D. Cox, J. Little and H. Schenck, *Toric Varieties*, §§1.1 and 3.1.
-/

public section

open scoped ContDiff Manifold
open Multiplicative Topology

namespace TauCeti.Toric

variable {N : Type*} [AddCommGroup N] {r : ℕ}

namespace AffineSemigroupComplexPoint

/-- The torus acts jointly continuously on the complex points of a submonoid of the character
lattice, for the monomial-embedding topology of any finite generating family. -/
theorem continuousSMul_affinePointTopology_complexTorus {S : AddSubmonoid (IntegralCharacter N)}
    (g : AddGeneratingFamily S r) :
    letI := affinePointTopology g
    ContinuousSMul (ComplexTorus N) (AffineSemigroupComplexPoint S) := by
  let _ := affinePointTopology g
  refine ⟨(continuous_iff_forall_continuous_apply_single g _).2 fun s ↦ ?_⟩
  simp only [ambient_smul_apply_single]
  exact (Units.continuous_val.comp ((continuous_complexTorus_apply (s : IntegralCharacter N)).comp
    continuous_fst)).mul ((continuous_apply_single g s).comp continuous_snd)

end AffineSemigroupComplexPoint

variable {V ι : Type*} [AddCommGroup V] [Module ℝ V] {i : N →+ V} {σ : PointedCone ℝ V}
  {s k l : ℕ} [Fintype ι]

/-- The torus acts holomorphically on the affine chart of a cone with an extending basis. The
torus carries the charted-space structure of a free presentation `e` of its character lattice, and
the chart that of the extending basis `B`, a numbering `κ` of the rays and a generating family
`g`. By `TauCeti.Toric.contMDiff_id_complexTorusChartedSpace` and
`TauCeti.Toric.contMDiff_id_coneChartedSpace`, these choices do not affect the complex
structures. -/
theorem contMDiffSMul_coneChartedSpace (hi : IsIntegralLattice i) (hσ : IsToricCone i σ)
    {B : Module.Basis (ToricRay σ ⊕ Fin l) ℤ N} (hB : ∀ ρ, IsPrimitiveGenerator i ρ (B (Sum.inl ρ)))
    (κ : ToricRay σ ≃ Fin k) (g : AddGeneratingFamily (dualSemigroup hi σ) s)
    (e : IntegralCharacter N ≃+ (ι →₀ ℤ)) (n : ℕ∞ω) :
    let _ := affinePointTopology g
    let _ := coneChartedSpace hi hσ hB κ g
    let _ := complexTorusChartedSpace e
    ContMDiffSMul 𝓘(ℂ, ι → ℂ) 𝓘(ℂ, (Fin k → ℂ) × (Fin l → ℂ)) n (ComplexTorus N)
      (AffineSemigroupComplexPoint (dualSemigroup hi σ)) := by
  let _ := affinePointTopology g
  let _ := coneChartedSpace hi hσ hB κ g
  let _ := complexTorusChartedSpace e
  -- The ambient chart coordinates of a point, and the values of a torus point on characters.
  have hx := contMDiff_coneChartAmbient hi hσ hB κ g n
  have hT (m : IntegralCharacter N) :
      ContMDiff 𝓘(ℂ, ι → ℂ) 𝓘(ℂ, ℂ) n fun t : ComplexTorus N ↦ (t m : ℂ) :=
    (Units.contMDiff_val.comp (contMDiff_characterEvaluation e m n)).congr fun t ↦ by
      simp [characterEvaluation_apply]
  refine ⟨(contMDiff_coneChartAmbient_comp_iff hi hσ hB κ g).1 ?_⟩
  -- In the ambient coordinates, a torus point multiplies each coordinate by its value on the
  -- corresponding dual basis character.
  refine ContMDiff.prodMk_space (contMDiff_pi_space.2 fun a ↦ ?_)
    (contMDiff_pi_space.2 fun c ↦ ?_)
  · refine (((hT (dualSemigroupCoord hi hσ hB (Sum.inl (κ.symm a)))).comp contMDiff_fst).mul
      ((((contDiff_apply ℂ ℂ a).comp contDiff_fst).contMDiff.comp hx).comp
        contMDiff_snd)).congr fun p ↦ ?_
    simp
  · refine (((hT (dualSemigroupCoord hi hσ hB (Sum.inr c))).comp contMDiff_fst).mul
      ((((contDiff_apply ℂ ℂ c).comp contDiff_snd).contMDiff.comp hx).comp
        contMDiff_snd)).congr fun p ↦ ?_
    simp

end TauCeti.Toric

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.Diffeomorph
public import TauCeti.Geometry.Manifold.Instances.OnePoint.PSLAction
public import TauCeti.Geometry.Manifold.Instances.OnePoint.Triple.Normalization
public import TauCeti.Geometry.Manifold.IsManifold.Pi
import Mathlib.Geometry.Manifold.SmoothEmbedding
import TauCeti.Geometry.Manifold.SmoothEmbedding.Basic

/-!
# `PSL(2, ℂ)` is biholomorphic to the ordered triples of distinct points of the Riemann sphere

The ordered triples of distinct points of the Riemann sphere form an open subset
`OnePoint.distinctTriples ℂ` of the product manifold `Fin 3 → OnePoint ℂ`, and hence a complex
manifold modelled on `ℂ³`. For an ordered triple `b` of distinct points, the orbit map
`g ↦ (g • b 0, g • b 1, g • b 2)`, the homeomorphism `OnePoint.pslHomeomorphDistinctTriples b`, is
holomorphic by the joint analyticity of the Möbius action (`OnePoint.instContMDiffSMulPSL`), and
its inverse, which sends a triple to the unique Möbius transformation carrying `b` to it, is
holomorphic by `OnePoint.contMDiff_pslHomeomorphDistinctTriples_symm`. So the orbit map is a
biholomorphism `OnePoint.pslDiffeomorphDistinctTriples b` from the complex Lie group `PSL(2, ℂ)`
onto the ordered triples of distinct points. Through it, three marked points normalize the
automorphisms of a genus-zero domain holomorphically.

## Main declarations

* `OnePoint.pslDiffeomorphDistinctTriples`: for an ordered triple `b` of distinct points, the
  biholomorphism `g ↦ (g • b 0, g • b 1, g • b 2)` from `PSL(2, ℂ)` onto the ordered triples of
  distinct points of the Riemann sphere.

## References

* Otto Forster, *Lectures on Riemann Surfaces*, Graduate Texts in Mathematics 81, Springer, 1981,
  §2 (the Möbius transformations of the Riemann sphere).
-/

public section

noncomputable section

open Function Matrix
open scoped ContDiff Manifold MatrixGroups

namespace OnePoint

/-- **`PSL(2, ℂ)` is biholomorphic to the ordered triples of distinct points of the Riemann
sphere.** For an ordered triple `b` of distinct points, the orbit map
`g ↦ (g • b 0, g • b 1, g • b 2)` is a biholomorphism from the complex Lie group `PSL(2, ℂ)` onto
the open subset of `(OnePoint ℂ)³` of ordered triples of distinct points; its inverse sends a
triple `p` to the unique Möbius transformation carrying `b` to `p`. -/
def pslDiffeomorphDistinctTriples (b : distinctTriples ℂ) :
    PSL(2, ℂ) ≃ₘ^ω⟮𝓘(ℂ, SpecialLinearGroup.Model (Fin 2) ℂ),
      ModelWithCorners.pi fun _ : Fin 3 ↦ 𝓘(ℂ)⟯ distinctTriples ℂ where
  toEquiv := (pslHomeomorphDistinctTriples b).toEquiv
  contMDiff_toFun := by
    refine ((Manifold.IsSmoothEmbedding.of_opens (I := ModelWithCorners.pi fun _ : Fin 3 ↦ 𝓘(ℂ))
      (n := ω) (distinctTriples ℂ)).contMDiff_iff_comp).2 (contMDiff_pi_iff.2 fun i ↦ ?_)
    have hb : ContMDiff 𝓘(ℂ, SpecialLinearGroup.Model (Fin 2) ℂ) 𝓘(ℂ) ω
        fun _ : PSL(2, ℂ) ↦ (b : Fin 3 → OnePoint ℂ) i :=
      contMDiff_const
    exact (contMDiff_id.smul hb).congr fun g ↦ pslHomeomorphDistinctTriples_apply_coe b g i
  contMDiff_invFun :=
    contMDiff_pslHomeomorphDistinctTriples_symm (fun p ↦ p.property)
      (fun i ↦ (contMDiff_apply (Mi := fun _ : Fin 3 ↦ OnePoint ℂ) (Ii := fun _ ↦ 𝓘(ℂ))
        (i := i)).comp contMDiff_subtypeVal) b

/-- `OnePoint.pslDiffeomorphDistinctTriples b` moves each point of `b`. -/
@[simp]
theorem pslDiffeomorphDistinctTriples_apply_coe (b : distinctTriples ℂ) (g : PSL(2, ℂ))
    (i : Fin 3) :
    (pslDiffeomorphDistinctTriples b g : Fin 3 → OnePoint ℂ) i =
      g • (b : Fin 3 → OnePoint ℂ) i :=
  pslHomeomorphDistinctTriples_apply_coe b g i

/-- The inverse of `OnePoint.pslDiffeomorphDistinctTriples b` is the inverse of the homeomorphism
`OnePoint.pslHomeomorphDistinctTriples b`: it sends a triple to the unique Möbius transformation
carrying `b` to it. -/
@[simp]
theorem pslDiffeomorphDistinctTriples_symm_apply (b p : distinctTriples ℂ) :
    (pslDiffeomorphDistinctTriples b).symm p = (pslHomeomorphDistinctTriples b).symm p :=
  (rfl)

end OnePoint

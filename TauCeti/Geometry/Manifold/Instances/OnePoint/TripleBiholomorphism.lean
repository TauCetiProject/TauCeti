/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.Diffeomorph
public import TauCeti.Geometry.Manifold.Instances.OnePoint.Moebius
public import TauCeti.Geometry.Manifold.Instances.OnePoint.TripleNormalization
public import TauCeti.Geometry.Manifold.IsManifold.Pi
import Mathlib.Geometry.Manifold.SmoothEmbedding
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Composition
import TauCeti.Geometry.Manifold.SmoothEmbedding.Basic
import TauCeti.Topology.Constructions.Pi

/-!
# `PSL(2, ℂ)` is biholomorphic to the ordered triples of distinct points of the Riemann sphere

Give `PSL(2, 𝕜) = SL(2, 𝕜) ⧸ Z(SL(2, 𝕜))`, for `𝕜 = ℝ` or `ℂ`, its analytic Lie group structure
as the quotient of `SL(2, 𝕜)` by its finite center (`Subgroup.instLieGroupDiscreteQuotient`). This
file proves that the Möbius action of `PSL(2, 𝕜)` on the projective line `OnePoint 𝕜` is jointly
analytic (`OnePoint.instContMDiffSMulPSL`): the map `(g, x) ↦ g • x` is analytic on
`PSL(2, 𝕜) × OnePoint 𝕜`, including at `∞`. For `𝕜 = ℂ` this is the holomorphic action of the
automorphism group of the Riemann sphere. The proof lifts the action along the projection
`SL(2, 𝕜) → PSL(2, 𝕜)`, a local diffeomorphism, where it is the action of the general linear
group (`OnePoint.instContMDiffSMul`) restricted along the analytic inclusion
`SL(2, 𝕜) → GL(2, 𝕜)`.

The ordered triples of distinct points of the projective line form an open subset
`OnePoint.distinctTriples 𝕜` of the product manifold `Fin 3 → OnePoint 𝕜`, and hence a manifold
modelled on `𝕜³`. For an ordered triple `b` of distinct points of the Riemann sphere, the orbit
map `g ↦ (g • b 0, g • b 1, g • b 2)` is holomorphic by the joint analyticity of the action, and
its inverse, which sends a triple to the unique Möbius transformation carrying `b` to it, is
holomorphic by `OnePoint.contMDiff_pslHomeomorphDistinctTriples_symm`. So the orbit map is a
biholomorphism `OnePoint.pslDiffeomorphDistinctTriples b` from `PSL(2, ℂ)` onto the ordered
triples of distinct points. Through it, three marked points normalize the automorphisms of a
genus-zero domain holomorphically.

## Main declarations

* `OnePoint.instContMDiffSMulPSL`: the Möbius action of `PSL(2, 𝕜)` on `OnePoint 𝕜` is jointly
  analytic.
* `OnePoint.distinctTriples`: the open set of ordered triples of distinct points.
* `OnePoint.pslDiffeomorphDistinctTriples`: for an ordered triple `b` of distinct points, the
  biholomorphism `g ↦ (g • b 0, g • b 1, g • b 2)` from `PSL(2, ℂ)` onto the ordered triples of
  distinct points of the Riemann sphere.

## References

* Otto Forster, *Lectures on Riemann Surfaces*, Graduate Texts in Mathematics 81, Springer, 1981,
  §2 (the Möbius transformations of the Riemann sphere).
-/

public section

noncomputable section

open Function Matrix TopologicalSpace
open scoped ContDiff Manifold MatrixGroups Matrix.Norms.Operator

attribute [local instance] Matrix.linftyOpTopologicalSpace

namespace OnePoint

section Action

variable {𝕜 : Type*} [RCLike 𝕜] [DecidableEq 𝕜]

/-- **The Möbius action of `PSL(2, 𝕜)` on the projective line is jointly analytic**, for the
analytic Lie group structure of `PSL(2, 𝕜)` as the quotient of `SL(2, 𝕜)` by its finite center.
For `𝕜 = ℂ` this is the holomorphic action of the automorphism group of the Riemann sphere. -/
instance instContMDiffSMulPSL :
    ContMDiffSMul 𝓘(𝕜, SpecialLinearGroup.Model (Fin 2) 𝕜) 𝓘(𝕜) ω PSL(2, 𝕜) (OnePoint 𝕜) where
  contMDiff_smul := by
    -- Lift the action along the projection `SL(2, 𝕜) → PSL(2, 𝕜)` in the group factor, which
    -- is put second so that `IsLocalDiffeomorph.contMDiff_comp_prodMap_iff` applies.
    have hSL : ContMDiff (𝓘(𝕜).prod 𝓘(𝕜, SpecialLinearGroup.Model (Fin 2) 𝕜)) 𝓘(𝕜) ω
        fun p : OnePoint 𝕜 × SL(2, 𝕜) ↦ SpecialLinearGroup.toGL p.2 • p.1 :=
      ((SpecialLinearGroup.contMDiff_toGL (n := Fin 2) (𝕜 := 𝕜)).comp contMDiff_snd).smul
        contMDiff_fst
    have hPSL : ContMDiff (𝓘(𝕜).prod 𝓘(𝕜, SpecialLinearGroup.Model (Fin 2) 𝕜)) 𝓘(𝕜) ω
        fun p : OnePoint 𝕜 × PSL(2, 𝕜) ↦ p.2 • p.1 :=
      ((Subgroup.isLocalDiffeomorph_quotientMk (I := 𝓘(𝕜, SpecialLinearGroup.Model (Fin 2) 𝕜))
        (n := ω) (Subgroup.center SL(2, 𝕜))).contMDiff_comp_prodMap_iff
          (g := fun p : OnePoint 𝕜 × PSL(2, 𝕜) ↦ p.2 • p.1) QuotientGroup.mk_surjective le_rfl).1
        (hSL.congr fun p ↦ pslMk_smul p.2 p.1)
    exact hPSL.comp (contMDiff_snd.prodMk contMDiff_fst)

end Action

section Triples

variable (𝕜 : Type*) [NontriviallyNormedField 𝕜] [ProperSpace 𝕜]

/-- The ordered triples of distinct points of the projective line `OnePoint 𝕜`, as an open subset
of the product manifold `Fin 3 → OnePoint 𝕜`. -/
def distinctTriples : Opens (Fin 3 → OnePoint 𝕜) :=
  ⟨{p | Injective p}, TauCeti.isOpen_setOf_injective⟩

variable {𝕜}

/-- A triple lies in `OnePoint.distinctTriples 𝕜` exactly when its points are distinct. -/
@[simp]
theorem mem_distinctTriples {p : Fin 3 → OnePoint 𝕜} : p ∈ distinctTriples 𝕜 ↔ Injective p :=
  Iff.rfl

end Triples

/-- **`PSL(2, ℂ)` is biholomorphic to the ordered triples of distinct points of the Riemann
sphere.** For an ordered triple `b` of distinct points, the orbit map
`g ↦ (g • b 0, g • b 1, g • b 2)` is a biholomorphism from the complex Lie group `PSL(2, ℂ)` onto
the open subset of `(OnePoint ℂ)³` of ordered triples of distinct points; its inverse sends a
triple `p` to the unique Möbius transformation carrying `b` to `p`. -/
def pslDiffeomorphDistinctTriples (b : {p : Fin 3 → OnePoint ℂ // Injective p}) :
    PSL(2, ℂ) ≃ₘ^ω⟮𝓘(ℂ, SpecialLinearGroup.Model (Fin 2) ℂ),
      ModelWithCorners.pi fun _ : Fin 3 ↦ 𝓘(ℂ)⟯ distinctTriples ℂ where
  toFun g := ⟨pslHomeomorphDistinctTriples b g, (pslHomeomorphDistinctTriples b g).property⟩
  invFun p := (pslHomeomorphDistinctTriples b).symm ⟨p, p.property⟩
  left_inv g := (pslHomeomorphDistinctTriples b).symm_apply_eq.2 (Subtype.ext rfl)
  right_inv p :=
    Subtype.ext (congrArg Subtype.val ((pslHomeomorphDistinctTriples b).apply_symm_apply _))
  contMDiff_toFun := by
    refine ((Manifold.IsSmoothEmbedding.of_opens (I := ModelWithCorners.pi fun _ : Fin 3 ↦ 𝓘(ℂ))
      (n := ω) (distinctTriples ℂ)).contMDiff_iff_comp).2 (contMDiff_pi_iff.2 fun i ↦ ?_)
    have hb : ContMDiff 𝓘(ℂ, SpecialLinearGroup.Model (Fin 2) ℂ) 𝓘(ℂ) ω
        fun _ : PSL(2, ℂ) ↦ (b : Fin 3 → OnePoint ℂ) i :=
      contMDiff_const
    exact (contMDiff_id.smul hb).congr fun g ↦ pslHomeomorphDistinctTriples_apply_coe b g i
  contMDiff_invFun :=
    contMDiff_pslHomeomorphDistinctTriples_symm (fun p ↦ mem_distinctTriples.1 p.property)
      (fun i ↦ (contMDiff_apply (Mi := fun _ : Fin 3 ↦ OnePoint ℂ) (Ii := fun _ ↦ 𝓘(ℂ))
        (i := i)).comp contMDiff_subtypeVal) b

/-- `OnePoint.pslDiffeomorphDistinctTriples b` moves each point of `b`. -/
@[simp]
theorem pslDiffeomorphDistinctTriples_apply_coe (b : {p : Fin 3 → OnePoint ℂ // Injective p})
    (g : PSL(2, ℂ)) (i : Fin 3) :
    (pslDiffeomorphDistinctTriples b g : Fin 3 → OnePoint ℂ) i =
      g • (b : Fin 3 → OnePoint ℂ) i :=
  pslHomeomorphDistinctTriples_apply_coe b g i

/-- The inverse of `OnePoint.pslDiffeomorphDistinctTriples b` is the inverse of the homeomorphism
`OnePoint.pslHomeomorphDistinctTriples b`: it sends a triple to the unique Möbius transformation
carrying `b` to it. -/
@[simp]
theorem pslDiffeomorphDistinctTriples_symm_apply (b : {p : Fin 3 → OnePoint ℂ // Injective p})
    (p : distinctTriples ℂ) :
    (pslDiffeomorphDistinctTriples b).symm p =
      (pslHomeomorphDistinctTriples b).symm ⟨p, mem_distinctTriples.1 p.property⟩ :=
  (rfl)

end OnePoint

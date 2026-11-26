/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Homotopy.LoopSpace.TorusClass
public import TauCeti.Topology.PathSpace.Moore.Rotation

import TauCeti.AlgebraicTopology.Singular.Sphere

/-!
# The torus class of the rotation of a loop

Rotating a free loop `f : S¹ → Q` once around itself is the loop of free loops
`t ↦ (z ↦ f (exp (2πit) z))` based at `f`. The torus it sweeps out,
`(s, t) ↦ f (exp (2πi(s + t)))`, factors through the multiplication `S¹ × S¹ → S¹`, and
`H₂(S¹; ℤ) = 0`, so its class in `H₂(Q; ℤ)` vanishes
(`TauCeti.freeLoopTorusClassHom_eq_zero_of_forall_apply_eq_mul`). The same holds for the rotation
loop `TauCeti.MooreFreeLoopSpace.rotationLoop γ` of a free Moore loop `γ`, which starts `γ` at each
of its points in turn: read as a circle map, the rotation of `γ` by the fraction `s` of its length
is `γ` precomposed with the rotation of the circle by `exp (2πis)`
(`TauCeti.MooreFreeLoopSpace.toCircleMap_rotate`), so the torus class of the rotation loop is zero
(`TauCeti.MooreFreeLoopSpace.torusClassHom_fundamentalGroupHom_rotationLoop`).

So every rank-one local system on the free loop space whose monodromy is read off the torus class,
such as `(-1) ^ ⟨w₂, -⟩` for a class `w₂ ∈ H²(Q; ℤ/2)`, acts trivially along the rotation of every
loop. This is the input for the triviality of the Viterbo twist along the rotation of a loop.

## Main results

* `TauCeti.freeLoopTorusClassHom_eq_zero_of_forall_apply_eq_mul`: the loop of rotations of a circle
  map has zero torus class.
* `TauCeti.MooreFreeLoopSpace.torusClassHom_fundamentalGroupHom_rotationLoop`: the rotation loop of
  a free Moore loop has zero torus class.

## References

* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, §4.1 (the loop of loops rotating a loop
  around itself).
-/

public section

noncomputable section

open AlgebraicTopology CategoryTheory unitInterval
open scoped NNReal Topology Topology.Homotopy

namespace TauCeti

variable {Q : Type} [TopologicalSpace Q]

/-- The loop of rotations of the circle, `t ↦ (z ↦ exp (2πit) z)`, as a loop of free loops of the
circle based at the identity. -/
private def circleRotationGenLoop : Ω^ (Fin 1) C(Circle, Circle) (ContinuousMap.id Circle) :=
  ⟨ContinuousMap.curry ⟨fun p : (Fin 1 → I) × Circle ↦ unitToCircle (p.1 0) * p.2, by fun_prop⟩,
    by
      rintro t ⟨i, hi⟩
      rw [Subsingleton.elim i 0] at hi
      ext z
      rcases hi with hi | hi <;> simp [hi, unitToCircle_zero, unitToCircle_one]⟩

private theorem circleRotationGenLoop_apply (t : Fin 1 → I) (z : Circle) :
    circleRotationGenLoop t z = unitToCircle (t 0) * z :=
  (rfl)

/-- **The loop of rotations of a circle map has zero torus class**: if a loop `Λ` of free loops at
`f : S¹ → Q` is `t ↦ (z ↦ f (exp (2πit) z))`, then the torus it sweeps out factors through the
circle, whose second homology vanishes, so its torus class is `0`. -/
theorem freeLoopTorusClassHom_eq_zero_of_forall_apply_eq_mul {f : C(Circle, Q)}
    (Λ : Ω^ (Fin 1) C(Circle, Q) f) (hΛ : ∀ t z, Λ t z = f (unitToCircle (t 0) * z)) :
    freeLoopTorusClassHom Q f
      (Additive.ofMul (⟦Λ⟧ : HomotopyGroup (Fin 1) C(Circle, Q) f)) = 0 := by
  have h := cubicalFreeLoopTorusClassHom_mk_eq_homologyMap ℤ f circleRotationGenLoop Λ
    fun t z ↦ by rw [hΛ, circleRotationGenLoop_apply]
  -- The second cubical homology of the circle vanishes, as its singular homology does.
  have hc : Subsingleton (((normalizedCubicalChainComplex ℤ).obj (TopCat.of Circle)).homology 2) :=
    ModuleCat.isZero_iff_subsingleton.1 <|
      (isZero_singularHomology_circle_of_two_le (ModuleCat.of ℤ ℤ) le_rfl).of_iso
        (singularCubicalHomologyIso ℤ (TopCat.of Circle) 2).symm
  rw [freeLoopTorusClassHom_apply, h,
    Subsingleton.elim (cubicalFreeLoopTorusClassHom Circle ℤ _ _) 0, map_zero, map_zero]
  -- The two zeros are those of the homology of `singularChains` and of `singularHomologyFunctor`,
  -- which agree by definition.
  rfl

namespace MooreFreeLoopSpace

/-- **The rotation loop has zero torus class**: rotating a free Moore loop `γ` once around itself
sweeps out a torus whose class in `H₂(Q; ℤ)` vanishes. -/
theorem torusClassHom_fundamentalGroupHom_rotationLoop (γ : MooreFreeLoopSpace Q) :
    γ.torusClassHom (Additive.ofMul (MooreLoopSpace.fundamentalGroupHom γ γ.rotationLoop)) = 0 := by
  rw [torusClassHom_fundamentalGroupHom, neg_eq_zero]
  refine freeLoopTorusClassHom_eq_zero_of_forall_apply_eq_mul _ fun t z ↦ ?_
  rw [GenLoop.genLoopEquivOfUnique_symm_apply, Path.map_coe, Function.comp_apply,
    MooreLoopSpace.toPath_apply, rotationLoop_apply, MooreLoopSpace.length_toMoorePath,
    length_rotationLoop, toCircleMap_rotate, Fin.default_eq_zero]

end MooreFreeLoopSpace

end TauCeti

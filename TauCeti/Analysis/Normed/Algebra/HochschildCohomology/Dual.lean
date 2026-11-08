/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Algebra.HochschildCohomology.Coboundary
public import TauCeti.Analysis.Normed.Module.Dual.Bimodule
public import TauCeti.RingTheory.CyclicCohomology.Continuous.Basic
import TauCeti.Data.Fin.Tuple.Basic

/-!
# Continuous scalar cochains and bounded dual coefficients

Currying the initial argument identifies continuous scalar `(n + 1)`-cochains with bounded
`n`-cochains taking values in the continuous dual. The identification uses Mathlib's
`ContinuousMultilinearMap.curryLeft` followed by `ContinuousLinearMap.flipMultilinear`;
its inverse is `ContinuousMultilinearMap.flipLinear` followed by
`ContinuousLinearMap.uncurryLeft`. Both directions are continuous linear equivalences,
by `continuousMultilinearCurryLeftEquiv` and `ContinuousLinearMap.flipMultilinearEquiv`.

The dual coefficients have actions `(a · f)(x) = f(xa)` and `(f · a)(x) = f(ax)`, given by
`ContinuousLinearMap.dualAction` applied to right and left multiplication respectively.
We prove that currying intertwines every coface and the Hochschild differentials, and
therefore preserves and reflects cocycles and actual coboundaries. No closure of the
coboundary range is taken.

These comparisons connect continuous cyclic cochains to bounded Hochschild cochains with
dual coefficients. They apply to nonunital normed algebras as well, and require neither
completeness nor a norm-one unit.

## References

* A. Connes, *Noncommutative Geometry*, Chapter III, §1.
* H. G. Dales, *Banach Algebras and Automatic Continuity*, §2.8.

The coface comparison follows the algebraic argument in
`TauCeti.RingTheory.HochschildCohomology.Dual`, with bounded dual actions in place of
algebraic dual actions.
-/

public section

noncomputable section

namespace ContinuousMultilinearMap

open TauCeti ContinuousLinearMap

variable {𝕜 A : Type*} [NontriviallyNormedField 𝕜]
  [NonUnitalNormedRing A] [NormedSpace 𝕜 A]
  [IsScalarTower 𝕜 A A] [SMulCommClass 𝕜 A A] {n : ℕ}

/-- After currying the initial argument into the continuous dual, each bounded bimodule
coface is the corresponding scalar Hochschild coface. -/
theorem hochschildBimoduleCoface_curryLeft_flipMultilinear
    (φ : ContinuousMultilinearMap 𝕜 (fun _ : Fin (n + 1) ↦ A) 𝕜)
    (i : Fin (n + 2)) (a : Fin (n + 1) → A) (x : A) :
    hochschildBimoduleCoface
        (dualAction (ContinuousLinearMap.mul 𝕜 A).flip)
        (dualAction (ContinuousLinearMap.mul 𝕜 A)) i
        φ.curryLeft.flipMultilinear a x = φ (hochschildFace i (Fin.cons x a)) := by
  induction i using Fin.cases with
  | zero =>
    conv_rhs => rw [← Fin.castSucc_zero (n := n + 1), hochschildFace_castSucc]
    simp only [hochschildBimoduleCoface_zero_apply, dualAction_apply_apply,
      flip_apply, ContinuousLinearMap.mul_apply', flipMultilinear_apply_apply,
      curryLeft_apply, Fin.castSucc_zero, Fin.contractNth_zero_cons]
  | succ i =>
    induction i using Fin.lastCases with
    | last =>
      simp only [Fin.succ_last]
      simp only [hochschildBimoduleCoface_last_apply, dualAction_apply_apply,
        ContinuousLinearMap.mul_apply', flipMultilinear_apply_apply, curryLeft_apply,
        hochschildFace_last, Fin.cons_last, Fin.cons_succ, Fin.cons_zero, Fin.init_def]
    | cast j =>
      conv_rhs => rw [Fin.succ_castSucc, hochschildFace_castSucc, ← Fin.succ_castSucc]
      simp only [hochschildBimoduleCoface_castSucc_succ_apply, flipMultilinear_apply_apply,
        curryLeft_apply, Fin.contractNth_succ_cons]

/-- Currying the initial variable intertwines the continuous scalar Hochschild differential
and the bounded Hochschild differential with continuous-dual coefficients. -/
theorem curryLeft_flipMultilinear_continuousHochschildCoboundary
    (φ : ContinuousMultilinearMap 𝕜 (fun _ : Fin (n + 1) ↦ A) 𝕜) :
    (continuousHochschildCoboundary 𝕜 A 𝕜 n φ).curryLeft.flipMultilinear =
      hochschildBimoduleCoboundary
        (dualAction (ContinuousLinearMap.mul 𝕜 A).flip)
        (dualAction (ContinuousLinearMap.mul 𝕜 A)) n φ.curryLeft.flipMultilinear := by
  ext a x
  rw [flipMultilinear_apply_apply, curryLeft_apply,
    continuousHochschildCoboundary_apply, hochschildCoboundary_apply,
    hochschildBimoduleCoboundary_apply]
  simp only [sum_apply, smul_apply, coe_coe,
    hochschildBimoduleCoface_curryLeft_flipMultilinear]

/-- The inverse currying map also intertwines the two Hochschild differentials. -/
theorem continuousHochschildCoboundary_flipLinear_uncurryLeft
    (ψ : ContinuousMultilinearMap 𝕜 (fun _ : Fin n ↦ A) (StrongDual 𝕜 A)) :
    continuousHochschildCoboundary 𝕜 A 𝕜 n ψ.flipLinear.uncurryLeft =
      (hochschildBimoduleCoboundary
        (dualAction (ContinuousLinearMap.mul 𝕜 A).flip)
        (dualAction (ContinuousLinearMap.mul 𝕜 A)) n ψ).flipLinear.uncurryLeft := by
  have h := curryLeft_flipMultilinear_continuousHochschildCoboundary
    (𝕜 := 𝕜) (A := A) (n := n) ψ.flipLinear.uncurryLeft
  ext a
  have hx := congrArg (fun f ↦ f (Fin.tail a) (a 0)) h
  simpa only [ContinuousLinearMap.curry_uncurryLeft, flipMultilinear_flipLinear,
    flipMultilinear_apply_apply, curryLeft_apply, Fin.cons_self_tail,
    ContinuousLinearMap.uncurryLeft_apply, flipLinear_apply_apply] using hx

/-- A continuous scalar cochain is a Hochschild cocycle exactly when its curried bounded
cochain with dual coefficients is a cocycle. -/
theorem hochschildBimoduleCoboundary_curryLeft_flipMultilinear_eq_zero_iff
    (φ : ContinuousMultilinearMap 𝕜 (fun _ : Fin (n + 1) ↦ A) 𝕜) :
    hochschildBimoduleCoboundary
        (dualAction (ContinuousLinearMap.mul 𝕜 A).flip)
        (dualAction (ContinuousLinearMap.mul 𝕜 A)) n φ.curryLeft.flipMultilinear = 0 ↔
      continuousHochschildCoboundary 𝕜 A 𝕜 n φ = 0 := by
  rw [← curryLeft_flipMultilinear_continuousHochschildCoboundary]
  constructor
  · intro h
    ext a
    have hx := congrArg (fun f ↦ f (Fin.tail a) (a 0)) h
    simpa only [flipMultilinear_apply_apply, curryLeft_apply, Fin.cons_self_tail,
      zero_apply] using hx
  · intro h
    ext a x
    simp only [h, flipMultilinear_apply_apply, curryLeft_apply, zero_apply]

/-- Currying preserves and reflects actual Hochschild coboundaries, not just the closures
of their ranges. The primitives are transported by the two native currying maps. -/
theorem exists_hochschildBimoduleCoboundary_eq_curryLeft_flipMultilinear_iff
    (φ : ContinuousMultilinearMap 𝕜 (fun _ : Fin (n + 2) ↦ A) 𝕜) :
    (∃ ψ, hochschildBimoduleCoboundary
        (dualAction (ContinuousLinearMap.mul 𝕜 A).flip)
        (dualAction (ContinuousLinearMap.mul 𝕜 A)) n ψ = φ.curryLeft.flipMultilinear) ↔
      ∃ θ, continuousHochschildCoboundary 𝕜 A 𝕜 n θ = φ := by
  constructor
  · rintro ⟨ψ, hψ⟩
    refine ⟨ψ.flipLinear.uncurryLeft, ?_⟩
    rw [continuousHochschildCoboundary_flipLinear_uncurryLeft, hψ,
      flipLinear_flipMultilinear, uncurry_curryLeft]
  · rintro ⟨θ, hθ⟩
    exact ⟨θ.curryLeft.flipMultilinear,
      (curryLeft_flipMultilinear_continuousHochschildCoboundary θ).symm.trans
        (congrArg (fun f ↦ f.curryLeft.flipMultilinear) hθ)⟩

end ContinuousMultilinearMap

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.VectorBundle.LocalFrame
public import TauCeti.Geometry.Manifold.DifferentialForm.Regularity
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Torsion
import TauCeti.Geometry.Manifold.DifferentialForm.VectorField

/-!
# Exterior derivative of one-forms against torsion-free parallel frames

On a `C¹` manifold equipped with a torsion-free connection `cov` on its tangent bundle, the
invariant exterior-derivative formula `dη(X, Y) = X(η(Y)) - Y(η(X)) - η([X, Y])` simplifies
whenever `X` and `Y` have vanishing covariant derivative at a point `y`: torsion-freeness forces
`[X, Y]_y = 0`. Consequently, if `s` is a `C^n` (`n ≥ 1`) local frame of the tangent bundle on a
neighbourhood of `y` whose members have vanishing covariant derivative at `y`, then any one-form
`η` differentiable at `y` whose pairings `z ↦ η z ![s i z]` have vanishing differential at `y`
satisfies `dη_y = 0`.

## Main results

* `CovariantDerivative.IsTorsionFree.mextDeriv_eq_zero_of_isLocalFrameOn`: a one-form
  differentiable at `y` whose pairings against a local frame `s` (around `y`, with `cov (s i) y = 0`
  for a torsion-free connection `cov`) have vanishing differential at `y` has `mextDeriv η y = 0`.

## References

* J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed., Springer GTM 176 (2018),
  Proposition 7.11.
* S. Kobayashi and K. Nomizu, *Foundations of Differential Geometry*, Vol. I, Interscience (1963),
  Chapter II, §9.
* `TauCeti.mextDeriv_apply_one` for the invariant exterior-derivative formula in degree one and
  `Module.Basis.ext_alternating` for extending vanishing from frame pairs to all tangent vectors.
-/

public section

open Bundle Filter VectorField
open scoped ContDiff Manifold Topology

namespace CovariantDerivative

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

/-- **Closedness of one-forms against a torsion-free parallel frame.** Let `s` be a `C^n` (`n ≥ 1`)
local frame of the tangent bundle on a neighbourhood `W` of `y` whose members satisfy
`cov (s i) y = 0` for a torsion-free connection `cov`. Any one-form `η` differentiable at `y`
whose pairings `z ↦ η z ![s i z]` have vanishing differential at `y` satisfies
`mextDeriv η y = 0`. -/
theorem IsTorsionFree.mextDeriv_eq_zero_of_isLocalFrameOn [IsManifold I 1 M]
    {cov : _root_.CovariantDerivative I E (TangentSpace I : M → Type _)} (ht : cov.IsTorsionFree)
    {ι : Type*} {n : WithTop ℕ∞} (hn : 1 ≤ n) {s : ι → Π y : M, TangentSpace I y} {W : Set M}
    {y : M} (hW : W ∈ 𝓝 y) (hs : IsLocalFrameOn I E n s W)
    (hpar : ∀ i, cov (s i) y = 0)
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {η : TauCeti.RoughForm I M F 1}
    (hη : MDifferentiableAt I (I.prod 𝓘(ℝ, E [⋀^Fin 1]→L[ℝ] F))
      (fun z ↦ TotalSpace.mk' (E [⋀^Fin 1]→L[ℝ] F) z (η z)) y)
    (hconst : ∀ i, mvfderiv I (fun z ↦ η z ![s i z]) y = 0) :
    TauCeti.mextDeriv η y = 0 := by
  have hy : y ∈ W := mem_of_mem_nhds hW
  have hn0 : n ≠ 0 := by rintro rfl; exact absurd hn (by simp)
  have hs_diff (i : ι) : MDiffAt (T% (s i)) y :=
    ((hs.contMDiffOn i).contMDiffAt hW).mdifferentiableAt hn0
  -- On frame pairs `(s i y, s j y)`, both directional terms and the Lie bracket term vanish.
  have hη0 : η y ![0] = 0 := (η y).toMultilinearMap.map_coord_zero (0 : Fin 1) rfl
  have hbasis (i j : ι) : TauCeti.mextDeriv η y ![s i y, s j y] = 0 := by
    rw [TauCeti.mextDeriv_apply_one hη (hs_diff i) (hs_diff j), hconst j, hconst i,
      ht.mlieBracket_eq_zero_of_cov_eq_zero (hs_diff i) (hs_diff j) (hpar i) (hpar j)]
    simp [hη0]
  -- Extend from basis pairs to arbitrary pairs via `Module.Basis.ext_alternating`.
  refine ContinuousAlternatingMap.toAlternatingMap_injective <|
    (hs.toBasisAt hy).ext_alternating fun v _ ↦ ?_
  have hv : (fun k : Fin 2 ↦ hs.toBasisAt hy (v k)) = ![s (v 0) y, s (v 1) y] := by
    ext k
    fin_cases k <;> simp [hs.toBasisAt_coe hy]
  simpa only [ContinuousAlternatingMap.coe_toAlternatingMap,
    ContinuousAlternatingMap.toAlternatingMap_zero, zero_apply, hv] using hbasis (v 0) (v 1)

end CovariantDerivative

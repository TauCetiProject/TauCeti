/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Submersion.Basic
public import TauCeti.Geometry.Manifold.Submersion.EhresmannConnection

/-!
# The Ehresmann connection of a Riemannian submersion

Let `f : M → N` be a Riemannian submersion, so a `C^∞` submersion. When `m ≤ ∞` (so `m + 1 ≤ ∞`,
which excludes the analytic case `m = ω`), `M` is a `C^(m+1)` manifold and the metric of `M` is of
class `C^m`, the orthogonal complements of the kernels of the derivative of `f` form an Ehresmann
connection of `f` of class `C^m`
(`Manifold.IsSubmersion.isEhresmannConnection_orthogonal_ker_mfderiv`). The horizontal lift
of any Ehresmann connection with these horizontal spaces is the isometric horizontal lift
`TauCeti.IsRiemannianSubmersion.horizontalLift`, the adjoint of the derivative
(`TauCeti.IsRiemannianSubmersion.horizontalLift_eq_isEhresmannConnection_horizontalLift`).
-/

public section

open Bundle Manifold
open scoped ContDiff Manifold

namespace TauCeti.IsRiemannianSubmersion

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {G : Type*} [TopologicalSpace G] {J : ModelWithCorners ℝ F G}
  {N : Type*} [TopologicalSpace N] [ChartedSpace G N]
  [RiemannianBundle (fun y : N ↦ TangentSpace J y)]
  {n : ℕ∞ω} {f : M → N}

/-- For a Riemannian submersion, the horizontal lift of an Ehresmann connection whose horizontal
spaces are the orthogonal complements of the kernels of the derivative is the isometric horizontal
lift `TauCeti.IsRiemannianSubmersion.horizontalLift`, the adjoint of the derivative. -/
theorem horizontalLift_eq_isEhresmannConnection_horizontalLift (h : IsRiemannianSubmersion I J f)
    (hE : IsEhresmannConnection I J n f fun x ↦ (mfderiv I J f x).kerᗮ) (x : M)
    (w : TangentSpace J (f x)) :
    h.horizontalLift x w = (hE.horizontalLift x w : TangentSpace I x) :=
  congrArg Subtype.val
    ((hE.eq_horizontalLift_iff (w := ⟨_, h.horizontalLift_mem_orthogonal_ker x w⟩)).2
      (h.mfderiv_horizontalLift x w))

end TauCeti.IsRiemannianSubmersion

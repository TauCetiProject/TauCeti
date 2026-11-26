/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.Global.AdelicPoints.Basic
public import TauCeti.RepresentationTheory.Automorphic.SmoothFunction

/-!
# Finite-level smooth functions on adelic groups of points

For an affine group over a number field, the product splitting identifies its adelic points
with its archimedean and finite points. With a smooth structure on the archimedean points,
the algebra of finite-level smooth functions evaluates on the full adelic group by this
splitting. The left-invariant subalgebra for the rational diagonal consists of functions
invariant under left multiplication by rational points.
-/

public section

noncomputable section

open NumberField WithConv
open scoped ContDiff Manifold

namespace TauCeti
namespace AdelicPoints

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]

/-- The algebra of finite-level smooth functions on the adelic points of an affine group. -/
abbrev SmoothFunction (I : ModelWithCorners ℝ E H) (K A : Type*) [Field K] [NumberField K]
    [CommRing A] [HopfAlgebra K A] [ChartedSpace H (InfinitePoints K A)]
    [Nonempty (CompactOpenSubgroup (FiniteAdelicPoints (𝓞 K) K A))] :=
  AdelicSmoothFunction I (InfinitePoints K A) (FiniteAdelicPoints (𝓞 K) K A)

end AdelicPoints

namespace AdelicSmoothFunction

open AdelicPoints

variable {K A E H : Type*} [Field K] [NumberField K] [CommRing A] [HopfAlgebra K A]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [ChartedSpace H (InfinitePoints K A)]
  [Nonempty (CompactOpenSubgroup (FiniteAdelicPoints (𝓞 K) K A))]

/-- Evaluate on an adelic point using its archimedean and finite components. -/
def evalAdelic (f : SmoothFunction I K A) (x : AdelicPoints (𝓞 K) K A) : ℂ :=
  f.eval (prodContinuousMulEquiv (𝓞 K) K A x)

@[simp]
theorem evalAdelic_apply (f : SmoothFunction I K A) (x : AdelicPoints (𝓞 K) K A) :
    f.evalAdelic x = f.eval (infiniteProjection (𝓞 K) K A x, finiteProjection (𝓞 K) K A x) := by
  rw [evalAdelic, prodContinuousMulEquiv_apply]

/-- Values on the full adelic group determine a finite-level smooth function. -/
theorem evalAdelic_injective :
    Function.Injective (evalAdelic : SmoothFunction I K A → AdelicPoints (𝓞 K) K A → ℂ) :=
  fun _ _ h ↦ ext ((prodContinuousMulEquiv (𝓞 K) K A).surjective.forall.mpr (congrFun h))

/-- The subalgebra invariant by left translation by the image of the rational diagonal. -/
def rationalLeftInvariant : Subalgebra ℂ (SmoothFunction I K A) :=
  leftInvariant (((prodContinuousMulEquiv (𝓞 K) K A).toMonoidHom.comp
    (diagonal (𝓞 K) K A)).range)

/-- Rational left invariance is tested by multiplying by the image of each rational point. -/
@[simp]
theorem mem_rationalLeftInvariant_iff (f : SmoothFunction I K A) :
    f ∈ rationalLeftInvariant ↔ ∀ (γ : WithConv (A →ₐ[K] K)) (x : AdelicPoints (𝓞 K) K A),
      f.evalAdelic (diagonal (𝓞 K) K A γ * x) = f.evalAdelic x := by
  let e := prodContinuousMulEquiv (𝓞 K) K A
  rw [rationalLeftInvariant, mem_leftInvariant_iff]
  constructor
  · intro hf γ x
    simpa only [evalAdelic, map_mul] using
      hf ⟨e (diagonal (𝓞 K) K A γ), ⟨γ, rfl⟩⟩ (e x)
  · rintro hf ⟨_, γ, rfl⟩ x
    obtain ⟨y, rfl⟩ := e.surjective x
    have hy := hf γ y
    rw [evalAdelic, map_mul, evalAdelic] at hy
    exact hy

/-- Finite-level smooth functions are continuous on the full adelic group. -/
theorem continuous_evalAdelic (f : SmoothFunction I K A) : Continuous f.evalAdelic :=
  f.continuous_eval.comp (prodContinuousMulEquiv (𝓞 K) K A).continuous

variable [ContMDiffMul I ∞ (InfinitePoints K A)]

/-- Right translation on the adelic points agrees with the product-group action. -/
theorem evalAdelic_rightTranslate (f : SmoothFunction I K A) (x y : AdelicPoints (𝓞 K) K A) :
    (rightTranslate (prodContinuousMulEquiv (𝓞 K) K A y) f).evalAdelic x =
      f.evalAdelic (x * y) := by
  rw [evalAdelic, rightTranslate_eval, evalAdelic, map_mul]

end AdelicSmoothFunction
end TauCeti

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.LocalDiffeomorph.RadialContraction
public import TauCeti.Geometry.Manifold.SmoothEmbedding.LocalDiffeomorph
public import TauCeti.Geometry.Manifold.Orientation.Preserving
import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace

/-!
# Radial contraction of bundled smooth embeddings

A radial contraction with nonnegative parameter can precompose a smooth embedding from a
finite-dimensional real normed space or postcompose an embedding into that space. The bundled
operations preserve every regularity at most `∞`; coercion and application lemmas describe their
underlying functions.

A radial contraction preserves every orientation of `E` at its centre
(`TauCeti.isOrientationPreservingAt_radialContraction_self`), so precomposing an embedding with a
radial contraction about the origin keeps it orientation-preserving at the origin
(`TauCeti.SmoothEmbedding.isOrientationPreservingAt_compRadialContraction`).
-/

public section

noncomputable section

open Set Filter Topology
open scoped Manifold ContDiff Pointwise

namespace TauCeti.SmoothEmbedding

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {n : ℕ∞ω}

variable {F H N : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace H]
  {J : ModelWithCorners ℝ F H} [TopologicalSpace N] [ChartedSpace H N]
  {E₀ H₀ M : Type*} [NormedAddCommGroup E₀] [NormedSpace ℝ E₀] [TopologicalSpace H₀]
  {I : ModelWithCorners ℝ E₀ H₀} [TopologicalSpace M] [ChartedSpace H₀ M]

/-- A smooth embedding of `E` precomposed with the radial contraction about `0` with parameter
`κ ≥ 0`, preserving any regularity `n ≤ ∞`. -/
def compRadialContraction (f : SmoothEmbedding 𝓘(ℝ, E) J n E N) (hn : n ≤ ∞)
    {κ : ℝ}
    (hκ : 0 ≤ κ) :
    SmoothEmbedding 𝓘(ℝ, E) J n E N :=
  f.compLocalDiffeomorph (radialContraction 0 κ) (isLocalDiffeomorph_radialContraction 0 hn hκ)
    (isEmbedding_radialContraction 0 hκ)

@[simp]
theorem coe_compRadialContraction (f : SmoothEmbedding 𝓘(ℝ, E) J n E N) (hn : n ≤ ∞)
    {κ : ℝ} (hκ : 0 ≤ κ) :
    ⇑(f.compRadialContraction hn hκ) = f ∘ radialContraction 0 κ := by
  rw [compRadialContraction, coe_compLocalDiffeomorph]

@[simp]
theorem compRadialContraction_apply (f : SmoothEmbedding 𝓘(ℝ, E) J n E N) (hn : n ≤ ∞)
    {κ : ℝ} (hκ : 0 ≤ κ) (x : E) :
    f.compRadialContraction hn hκ x = f (radialContraction 0 κ x) := by
  rw [coe_compRadialContraction, Function.comp_apply]

/-- A smooth embedding into `E` followed by the radial contraction about `c` with parameter
`κ ≥ 0`, preserving any regularity `n ≤ ∞`. -/
def transRadialContraction (f : SmoothEmbedding I 𝓘(ℝ, E) n M E)
    (c : E) (hn : n ≤ ∞)
    {κ : ℝ}
    (hκ : 0 ≤ κ) :
    SmoothEmbedding I 𝓘(ℝ, E) n M E :=
  f.transLocalDiffeomorph (radialContraction c κ) (s := univ)
    (fun y _ => isLocalDiffeomorph_iff.1 (isLocalDiffeomorph_radialContraction c hn hκ) y)
    ((isEmbedding_radialContraction c hκ).comp IsEmbedding.subtypeVal) (subset_univ _)

@[simp]
theorem coe_transRadialContraction (f : SmoothEmbedding I 𝓘(ℝ, E) n M E)
    (c : E) (hn : n ≤ ∞)
    {κ : ℝ}
    (hκ : 0 ≤ κ) : ⇑(f.transRadialContraction c hn hκ) = radialContraction c κ ∘ f :=
  f.coe_transLocalDiffeomorph _ _ _ _

@[simp]
theorem transRadialContraction_apply (f : SmoothEmbedding I 𝓘(ℝ, E) n M E)
    (c : E) (hn : n ≤ ∞)
    {κ : ℝ}
    (hκ : 0 ≤ κ) (x : M) : f.transRadialContraction c hn hκ x = radialContraction c κ (f x) := by
  rw [coe_transRadialContraction, Function.comp_apply]

section Orientation

variable {X : Type*} [TopologicalSpace X] [ChartedSpace E X] [IsManifold 𝓘(ℝ, E) ∞ X]
  {ι : Type*} [Fintype ι]

/-- A radial contraction preserves every orientation of `E` at its centre. -/
theorem _root_.TauCeti.isOrientationPreservingAt_radialContraction_self
    (o : Manifold.Orientation 𝓘(ℝ, E) E ι) (c : E) (κ : ℝ) :
    o.IsOrientationPreservingAt o (radialContraction c κ) c := by
  -- Its derivative at the centre is the identity.
  have hd : mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (radialContraction c κ) c = ContinuousLinearMap.id ℝ E := by
    rw [mfderiv_eq_fderiv, (hasFDerivAt_radialContraction_self c κ).fderiv]
    ext v
    rfl
  refine (Manifold.Orientation.isOrientationPreservingAt_iff _ _ _ _).mpr
    ⟨ContinuousLinearEquiv.refl ℝ E, hd.symm, ?_⟩
  -- The tangent spaces at `c` and at its image `radialContraction c κ c = c` are both `E`;
  -- generalize the image point to substitute it.
  have key : ∀ y : E, y = c → _root_.Orientation.map ι
      (ContinuousLinearEquiv.refl ℝ (TangentSpace 𝓘(ℝ, E) c)).toLinearEquiv
        (o.orientationAt c) = o.orientationAt y := by
    rintro y rfl
    exact Equiv.ext_iff.mp (_root_.Orientation.map_refl ι) _
  exact key _ (radialContraction_self c κ)

/-- Precomposing an embedding of `E` with a radial contraction about the origin keeps it
orientation-preserving at the origin. -/
theorem isOrientationPreservingAt_compRadialContraction
    (f : SmoothEmbedding 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ E X) {κ : ℝ} (hκ : 0 ≤ κ)
    {o : Manifold.Orientation 𝓘(ℝ, E) E ι} {oM : Manifold.Orientation 𝓘(ℝ, E) X ι}
    (hf : o.IsOrientationPreservingAt oM f 0) :
    o.IsOrientationPreservingAt oM (f.compRadialContraction le_rfl hκ) 0 := by
  rw [coe_compRadialContraction]
  rw [← radialContraction_self (0 : E) κ] at hf
  exact hf.comp (isOrientationPreservingAt_radialContraction_self o 0 κ)

end Orientation

end TauCeti.SmoothEmbedding

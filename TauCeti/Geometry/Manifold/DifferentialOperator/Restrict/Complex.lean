/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialOperator.Restrict.Basic
public import TauCeti.Geometry.Manifold.VectorBundle.Tangent.Restriction
public import TauCeti.Geometry.Manifold.VectorField.ComplexDerivation

/-!
# Open restriction of complex derivations on a real manifold

A complex derivation on a finite-dimensional Hausdorff real manifold acts on local smooth
functions on any open subset. Its value depends only on the germ of the input, and its action
on restrictions of global functions characterizes it uniquely. Restriction commutes with
multiplication by smooth complex functions and with Lie brackets. Under the correspondence
between complex derivations and complexified vector fields, it is the complex-linear extension
of vector-field restriction.

We use `Derivation.complexifyEquiv` to extend the real restriction map
`TopologicalSpace.Opens.restrictDerivation` by scalars from ℝ to ℂ.
-/

public noncomputable section

open TopologicalSpace Filter
open scoped Manifold ContDiff Topology

namespace TopologicalSpace.Opens

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

/-- Restriction of complex derivations of smooth complex-valued functions to an open submanifold,
obtained by restricting the real and imaginary derivations. -/
def restrictComplexDerivation (U : Opens M) :
    Derivation ℂ C^∞⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯ C^∞⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯ →ₗ[ℂ]
      Derivation ℂ C^∞⟮I, U; 𝓘(ℝ, ℂ), ℂ⟯ C^∞⟮I, U; 𝓘(ℝ, ℂ), ℂ⟯ :=
  Derivation.complexifyEquiv.toLinearMap ∘ₗ (U.restrictDerivation (I := I)).baseChange ℂ ∘ₗ
    Derivation.complexifyEquiv.symm.toLinearMap

variable (U : Opens M) (δ : Derivation ℂ C^∞⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯ C^∞⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯)

/-- The restriction of a complex derivation has the restricted real and imaginary parts as
its two complexified summands. -/
theorem restrictComplexDerivation_eq_complexify_add :
    U.restrictComplexDerivation δ = Derivation.complexify (U.restrictDerivation δ.re) +
      Complex.I • Derivation.complexify (U.restrictDerivation δ.im) := by
  simp [restrictComplexDerivation]

variable {U}

/-- Taking the real part commutes with restriction of a complex derivation. -/
@[simp]
theorem _root_.Derivation.re_restrictComplexDerivation :
    (U.restrictComplexDerivation δ).re = U.restrictDerivation δ.re := by
  simp [restrictComplexDerivation_eq_complexify_add]

/-- Taking the imaginary part commutes with restriction of a complex derivation. -/
@[simp]
theorem _root_.Derivation.im_restrictComplexDerivation :
    (U.restrictComplexDerivation δ).im = U.restrictDerivation δ.im := by
  simp [restrictComplexDerivation_eq_complexify_add]

variable (U)

/-- Complexifying a real derivation commutes with restriction to an open subset. -/
@[simp]
theorem restrictComplexDerivation_complexify (D : Derivation ℝ C^∞⟮I, M; ℝ⟯ C^∞⟮I, M; ℝ⟯) :
    U.restrictComplexDerivation (Derivation.complexify D) =
      Derivation.complexify (U.restrictDerivation D) :=
  Derivation.ext_re_im (by simp) (by simp)

/-- Restricting a complex derivation and evaluating on a local function gives its value on
any global function with the same germ. -/
theorem restrictComplexDerivation_apply_of_eventuallyEq
    {f : C^∞⟮I, U; 𝓘(ℝ, ℂ), ℂ⟯} {g : C^∞⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯} {x : U}
    (hg : (g : M → ℂ) ∘ Subtype.val =ᶠ[𝓝 x] f) :
    U.restrictComplexDerivation δ f x = δ g x := by
  have hr : (g.re : M → ℝ) ∘ Subtype.val =ᶠ[𝓝 x] f.re := by
    filter_upwards [hg] with y hy using by simpa using congrArg Complex.re hy
  have hi : (g.im : M → ℝ) ∘ Subtype.val =ᶠ[𝓝 x] f.im := by
    filter_upwards [hg] with y hy using by simpa using congrArg Complex.im hy
  conv_rhs => rw [← δ.complexify_re_add_I_smul_complexify_im]
  rw [restrictComplexDerivation_eq_complexify_add]
  simp only [add_apply, smul_apply, Derivation.complexify_apply, ContMDiffMap.coe_add,
    Pi.add_apply, ContMDiffMap.complex_smul_apply, ContMDiffMap.ofReal_apply,
    restrictDerivation_apply_of_eventuallyEq _ hr, restrictDerivation_apply_of_eventuallyEq _ hi]

/-- On restrictions of global functions the restricted derivation agrees with the global one. -/
@[simp]
theorem restrictComplexDerivation_apply_restrict (g : C^∞⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯) :
    U.restrictComplexDerivation δ (g.restrict U) = (δ g).restrict U := by
  ext x
  rw [ContMDiffMap.restrict_apply]
  exact U.restrictComplexDerivation_apply_of_eventuallyEq δ (by rw [ContMDiffMap.coe_restrict])

/-- A derivation on an open submanifold is the restriction of a given complex derivation
exactly when they agree on restrictions of global functions. -/
theorem eq_restrictComplexDerivation_iff
    {δ' : Derivation ℂ C^∞⟮I, U; 𝓘(ℝ, ℂ), ℂ⟯ C^∞⟮I, U; 𝓘(ℝ, ℂ), ℂ⟯} :
    δ' = U.restrictComplexDerivation δ ↔
      ∀ g : C^∞⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯, δ' (g.restrict U) = (δ g).restrict U := by
  refine ⟨fun h g ↦ h ▸ U.restrictComplexDerivation_apply_restrict δ g, fun h ↦ ?_⟩
  have hreal (u : C^∞⟮I, M; ℝ⟯) :
      ContMDiffMap.ofReal (u.restrict U) = (ContMDiffMap.ofReal u).restrict U := by
    ext x
    simp
  apply Derivation.ext_re_im
  · rw [Derivation.re_restrictComplexDerivation, eq_restrictDerivation_iff]
    intro u
    ext x
    simp [hreal, h]
  · rw [Derivation.im_restrictComplexDerivation, eq_restrictDerivation_iff]
    intro u
    ext x
    simp [hreal, h]

/-- Multiplication by a smooth complex function commutes with restriction of derivations. -/
@[simp]
theorem restrictComplexDerivation_smul (f : C^∞⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯) :
    U.restrictComplexDerivation (f • δ) = f.restrict U • U.restrictComplexDerivation δ := by
  symm
  apply (U.eq_restrictComplexDerivation_iff _).2
  intro g
  ext x
  simp

/-- Restriction preserves the commutator of complex derivations. -/
@[simp]
theorem restrictComplexDerivation_lie
    (η : Derivation ℂ C^∞⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯ C^∞⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯) :
    U.restrictComplexDerivation ⁅δ, η⁆ = ⁅U.restrictComplexDerivation δ,
      U.restrictComplexDerivation η⁆ := by
  symm
  apply (U.eq_restrictComplexDerivation_iff _).2
  intro g
  simp [Derivation.commutator_apply]

variable {U}

open TauCeti in
/-- Under the identification of complex derivations with complexified vector fields,
restricting a derivation restricts the vector field in each tensor summand. -/
theorem _root_.Derivation.complexDerivationEquivComplexifiedVectorField_restrictComplexDerivation
    [BoundarylessManifold I M] :
    complexDerivationEquivComplexifiedVectorField (U.restrictComplexDerivation δ) =
      (U.restrictVectorField (I := I)).baseChange ℂ
        (complexDerivationEquivComplexifiedVectorField δ) := by
  have h (D : Derivation ℝ C^∞⟮I, M; ℝ⟯ C^∞⟮I, M; ℝ⟯) :
      derivationEquivSmoothVectorField (U.restrictDerivation D) =
        U.restrictVectorField (derivationEquivSmoothVectorField D) := by
    ext x
    simp only [Derivation.derivationEquivSmoothVectorField_apply_apply, restrictVectorField_apply,
      Derivation.vectorField_restrictDerivation]
  simp [h]

end TopologicalSpace.Opens

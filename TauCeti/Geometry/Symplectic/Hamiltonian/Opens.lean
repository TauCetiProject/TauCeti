/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Hamiltonian.Manifold
public import TauCeti.Geometry.Symplectic.Manifold.Opens
import TauCeti.Geometry.Manifold.RegularValue

/-!
# Hamiltonian vector fields and Poisson brackets on open submanifolds

Let `σ` be a nondegenerate two-form on a finite-dimensional manifold `M` and let `U` be an open
subset, carrying the restricted form `σ|_U`, the pullback of `σ` along the inclusion
(`TauCeti.SmoothTwoForm.IsNondegenerate.mpullback_subtype_val`). The tangent spaces of `U` are
those of `M`, and in these terms Hamiltonian vector fields and Poisson brackets are local: the
Hamiltonian vector field of the restriction `f|_U` for `σ|_U` is the restriction of the
Hamiltonian vector field of `f` for `σ`, and the Poisson bracket of two restrictions is the
restriction of their Poisson bracket. Both are the naturality of these constructions under maps
pulling one form back to the other (`TauCeti.SmoothTwoForm.IsNondegenerate.poissonBracket_comp`),
applied to the inclusion, whose differential is everywhere invertible.

So a family of Poisson-commuting functions on `M` restricts to a Poisson-commuting family on every
open subset (`TauCeti.SmoothTwoForm.IsNondegenerate.poissonBracket_comp_subtype_val_eq_zero`), with
the restricted Hamiltonian vector fields. This is how Hamiltonian systems are
localized to neighbourhoods on which their flows are complete.
-/

public section

open TopologicalSpace
open scoped Manifold ContDiff

namespace TauCeti.SmoothTwoForm.IsNondegenerate

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {σ : SmoothTwoForm I M} (hσ : σ.IsNondegenerate) (U : Opens M)
include hσ

/-- **Hamiltonian vector fields are local.** On an open subset `U`, with the restricted form, the
Hamiltonian vector field of the restriction of `f` is the Hamiltonian vector field of `f`, read in
the common tangent space of `U` and `M`. -/
theorem hamiltonianVectorField_comp_subtype_val {f : M → ℝ} {y : U}
    (hf : MDifferentiableAt I 𝓘(ℝ) f y) :
    SmoothTwoForm.hamiltonianVectorField
        (SmoothForm.mpullback (Subtype.val : U → M) contMDiff_subtype_val σ) (f ∘ Subtype.val) y =
      σ.hamiltonianVectorField f y := by
  rw [← (hσ.mpullback_subtype_val U).mfderiv_hamiltonianVectorField_comp hσ contMDiff_subtype_val
    rfl (isRegularPoint_iff.1 (isRegularPoint_subtype_val y)) hf, Manifold.mfderiv_subtype_val,
    ContinuousLinearEquiv.coe_coe, Manifold.tangentSpaceOpenEquiv_apply]

/-- **Poisson brackets are local.** On an open subset `U`, with the restricted form, the Poisson
bracket of the restrictions of `f` and `g` is the restriction of their Poisson bracket. -/
theorem poissonBracket_comp_subtype_val {f g : M → ℝ} {y : U}
    (hf : MDifferentiableAt I 𝓘(ℝ) f y) (hg : MDifferentiableAt I 𝓘(ℝ) g y) :
    SmoothTwoForm.poissonBracket
        (SmoothForm.mpullback (Subtype.val : U → M) contMDiff_subtype_val σ) (f ∘ Subtype.val)
        (g ∘ Subtype.val) y = σ.poissonBracket f g y :=
  (hσ.mpullback_subtype_val U).poissonBracket_comp hσ contMDiff_subtype_val rfl
    (isRegularPoint_iff.1 (isRegularPoint_subtype_val y)) hf hg

/-- **Poisson-commuting families restrict to open subsets.** If the components of a differentiable
family `F` pairwise Poisson-commute for `σ`, then their restrictions to an open subset `U`
pairwise Poisson-commute for the restricted form. -/
theorem poissonBracket_comp_subtype_val_eq_zero {ι : Type*} [Fintype ι] {F : M → ι → ℝ}
    (hF : MDifferentiable I 𝓘(ℝ, ι → ℝ) F)
    (hcomm : ∀ i j x, σ.poissonBracket (F · i) (F · j) x = 0) (i j : ι) (y : U) :
    SmoothTwoForm.poissonBracket
        (SmoothForm.mpullback (Subtype.val : U → M) contMDiff_subtype_val σ) (fun y : U ↦ F y i)
        (fun y : U ↦ F y j) y = 0 :=
  (hσ.poissonBracket_comp_subtype_val U (mdifferentiableAt_pi_space.1 (hF y) i)
    (mdifferentiableAt_pi_space.1 (hF y) j)).trans (hcomm i j y)

end TauCeti.SmoothTwoForm.IsNondegenerate

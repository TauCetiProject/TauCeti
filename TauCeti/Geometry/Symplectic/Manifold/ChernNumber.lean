/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Manifold.AlmostComplex.ComplexTangentBundle
public import TauCeti.Geometry.Symplectic.Manifold.AlmostComplex.Polar
public import TauCeti.Topology.VectorBundle.Complex.Clutching

/-!
# The first Chern number of a symplectic manifold on spheres

Let `ω` be a fiberwise nondegenerate smooth two-form on a manifold `M`, for instance a symplectic
form, and let `J` be a smooth almost complex structure tamed by `ω`. With `J` as multiplication by
`i`, the tangent bundle is a complex vector bundle `(TM, J)`
(`TauCeti.ContMDiffAlmostComplexStructure.toContinuousComplexStructure`), whose clutching number
`TauCeti.clutchingNumberHom` is a homomorphism `π₂(M, x) → ℤ`: the first Chern number of `(TM, J)`
on spheres.

The first Chern number of `M` is this homomorphism for any `ω`-tame `J`: it does not depend on the
choice (`TauCeti.SmoothTwoForm.Tames.clutchingNumberHom_eq`). If `ω` tames `J₀` and `J₁`, then
`J₀ v + J₁ v ≠ 0` for every nonzero tangent vector `v`, because `ω(v, J₀ v)` and `ω(v, J₁ v)` are
both positive (`TauCeti.SmoothTwoForm.Tames.injective_add`). So `J₀ + J₁` is a complex linear
isomorphism from `(TM, J₀)` to `(TM, J₁)` (`TauCeti.Bundle.ContinuousComplexStructure.fiberCongr`),
and isomorphic complex vector bundles have the same clutching numbers
(`TauCeti.Bundle.ContinuousComplexStructure.clutchingNumberHom_eq_of_injective_add`). No path of
tame structures from `J₀` to `J₁` is needed.

Tame structures exist on Hausdorff σ-compact manifolds, as compatible ones do
(`TauCeti.SmoothTwoForm.IsNondegenerate.exists_compatible`), so the first Chern number
`TauCeti.SmoothTwoForm.IsNondegenerate.chernNumberHom` of `ω` is defined there, from a chosen
compatible structure, and agrees with the clutching number of every tame one
(`TauCeti.SmoothTwoForm.IsNondegenerate.chernNumberHom_eq_clutchingNumberHom`). This is the Chern
number by which recapping a capped orbit of Hamiltonian Floer theory with a sphere shifts its
grading. The complex model fibre `G` is any finite-dimensional complex normed space of half the
real dimension of the model space of `M`. No comparison with a cohomological first Chern class is
made here.

## Main definitions

* `TauCeti.SmoothTwoForm.IsNondegenerate.chernNumberHom`: the first Chern number
  `π₂(M, x) → ℤ` of a nondegenerate two-form.

## Main results

* `TauCeti.SmoothTwoForm.Tames.clutchingNumberHom_eq`: almost complex structures tamed by the same
  two-form have the same first Chern number on spheres.
* `TauCeti.SmoothTwoForm.IsNondegenerate.chernNumberHom_eq_clutchingNumberHom`: the first Chern
  number of `ω` is the clutching number of `(TM, J)` for every `ω`-tame `J`.

## References

* D. McDuff and D. Salamon, *Introduction to Symplectic Topology*, third edition, Oxford (2017),
  Section 4.1 (the first Chern class of a symplectic vector bundle does not depend on the
  compatible complex structure).
* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., AMS (2012),
  Appendix C.1 (the first Chern number of a bundle over a surface by clutching).
-/

public section

noncomputable section

open scoped ContDiff Manifold Topology

namespace TauCeti.SmoothTwoForm

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M]
  (G : Type*) [NormedAddCommGroup G] [NormedSpace ℂ G] [FiniteDimensional ℂ G]
  [Fact (Module.finrank ℝ E = 2 * Module.finrank ℂ G)]
  {form : SmoothTwoForm I M} {J J₀ J₁ : SmoothAlmostComplexStructure I M}

/-- **The first Chern number does not depend on the tame almost complex structure.** Smooth almost
complex structures `J₀` and `J₁` tamed by a common two-form make the tangent bundle into complex
vector bundles with the same clutching number homomorphism `π₂(M, x) → ℤ`. -/
theorem Tames.clutchingNumberHom_eq (h₀ : form.Tames J₀) (h₁ : form.Tames J₁) (x : M) :
    clutchingNumberHom G (J₁.toContMDiff 0).toContinuousComplexStructure.Fiber x =
      clutchingNumberHom G (J₀.toContMDiff 0).toContinuousComplexStructure.Fiber x :=
  Bundle.ContinuousComplexStructure.clutchingNumberHom_eq_of_injective_add G _ _
    (fun y ↦ by
      simpa only [FunLike.coe_add, Pi.add_def,
        ContMDiffAlmostComplexStructure.toContinuousComplexStructure_apply,
        SmoothAlmostComplexStructure.toContMDiff_apply] using h₀.injective_add h₁ y) x

variable [T2Space M] [SigmaCompactSpace M]

/-- The **first Chern number** `π₂(M, x) → ℤ` of a nondegenerate smooth two-form `ω`, such as a
symplectic form, on a Hausdorff σ-compact manifold: the clutching number of the complex vector
bundle `(TM, J)` for a compatible almost complex structure `J`. It is the clutching number for
every `ω`-tame `J` (`TauCeti.SmoothTwoForm.IsNondegenerate.chernNumberHom_eq_clutchingNumberHom`).
-/
def IsNondegenerate.chernNumberHom (h : form.IsNondegenerate) (x : M) :
    Additive (π_ 2 M x) →+ ℤ :=
  clutchingNumberHom G (h.exists_compatible.choose.toContMDiff 0).toContinuousComplexStructure.Fiber
    x

/-- **The first Chern number from any tame structure.** The first Chern number of a nondegenerate
two-form `ω` is the clutching number of the complex vector bundle `(TM, J)` for every `ω`-tame
almost complex structure `J`. -/
theorem IsNondegenerate.chernNumberHom_eq_clutchingNumberHom (h : form.IsNondegenerate)
    (hJ : form.Tames J) (x : M) :
    h.chernNumberHom G x =
      clutchingNumberHom G (J.toContMDiff 0).toContinuousComplexStructure.Fiber x :=
  hJ.clutchingNumberHom_eq G h.exists_compatible.choose_spec.tames x

end TauCeti.SmoothTwoForm

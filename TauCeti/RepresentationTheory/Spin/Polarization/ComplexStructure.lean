/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Complex.QuadraticForm
public import TauCeti.RepresentationTheory.Spin.Polarization.Complement

/-!
# The polarization of a complexified quadratic space by a complex structure

Let `Q` be a quadratic form on a real vector space `V` and `J` an almost complex structure on `V`
preserving `Q`. The complex-linear extension of `J` to `ℂ ⊗[ℝ] V` has the two eigenspaces
`W = ker (J - i)` and `W' = ker (J + i)`, which are complementary
(`TauCeti.AlmostComplexStructure.isCompl_eigenspace_baseChange_I_neg_I`) and totally isotropic for
the base-changed form (`TauCeti.AlmostComplexStructure.isTotallyIsotropic_eigenspace_baseChange_I`
and `TauCeti.AlmostComplexStructure.isTotallyIsotropic_eigenspace_baseChange_neg_I`). When `Q` is
nondegenerate and `V` is finite-dimensional, `W` and `W'` therefore polarize `Q.baseChange ℂ`, and
the polar form pairs them perfectly. This is the polarization from which the exterior model `⋀ W`
of the spinor module of an even-dimensional Euclidean space with an orthogonal complex structure is
built; the geometric convention takes `Q (v) = -g (v, v)` for the metric `g`.

A real vector `v` decomposes as `1 ⊗ v = v^(1,0) + v^(0,1)`, with
`v^(1,0) = (v - i J v) / 2 ∈ W` and `v^(0,1) = (v + i J v) / 2 ∈ W'`
(`TauCeti.AlmostComplexStructure.holomorphicPart` and
`TauCeti.AlmostComplexStructure.antiholomorphicPart`); this is the decomposition the polarization
uses. Their pairing is `TauCeti.AlmostComplexStructure.polar_holomorphicPart_antiholomorphicPart`.

## Main definitions

* `TauCeti.AlmostComplexStructure.spinPolarizationData`: the polarization of `Q.baseChange ℂ` by
  the `i`- and `-i`-eigenspaces of the complexified complex structure.

## Main results

* `TauCeti.AlmostComplexStructure.spinPolarizationData_decompositionEquiv_symm_tmul`: the
  polarization decomposes `1 ⊗ v` as `(v^(1,0), v^(0,1))`.

## References

* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry*, Chapter I, for spinor modules of
  even-dimensional Euclidean spaces.
* C. Chevalley, *The Algebraic Theory of Spinors*, Chapter II, for spinor modules attached to a
  decomposition into complementary totally isotropic subspaces.
-/

public section

open Module.End QuadraticMap
open scoped TensorProduct

namespace TauCeti.AlmostComplexStructure

universe u

variable {V : Type u} [AddCommGroup V] [Module ℝ V] (J : AlmostComplexStructure V)
  {Q : QuadraticForm ℝ V}

/-! ## The polarization -/

/-- **The polarization of a complexified quadratic space by a complex structure.** For a
nondegenerate quadratic form `Q` on a finite-dimensional real vector space and an almost complex
structure `J` preserving `Q`, the `i`- and `-i`-eigenspaces of the complexification of `J` are the
two isotropic summands of a polarization of `Q.baseChange ℂ`, with no orthogonal remainder. Its
pairing field identifies the `-i`-eigenspace with the dual of the `i`-eigenspace through the
polar form. -/
noncomputable def spinPolarizationData [FiniteDimensional ℝ V] (hQJ : ∀ v, Q (J v) = Q v)
    (hQ : Q.Nondegenerate) : SpinPolarizationData (Q.baseChange ℂ) :=
  SpinPolarizationData.ofIsCompl (QuadraticForm.Nondegenerate.baseChange hQ)
    J.isCompl_eigenspace_baseChange_I_neg_I (J.isTotallyIsotropic_eigenspace_baseChange_I hQJ)
    (J.isTotallyIsotropic_eigenspace_baseChange_neg_I hQJ)

section Polarization

variable [FiniteDimensional ℝ V] (hQJ : ∀ v, Q (J v) = Q v) (hQ : Q.Nondegenerate)

@[simp]
theorem spinPolarizationData_W :
    (J.spinPolarizationData hQJ hQ).W =
      eigenspace (J.toLinearMap.baseChange ℂ) Complex.I :=
  SpinPolarizationData.ofIsCompl_W ..

@[simp]
theorem spinPolarizationData_W' :
    (J.spinPolarizationData hQJ hQ).W' =
      eigenspace (J.toLinearMap.baseChange ℂ) (-Complex.I) :=
  SpinPolarizationData.ofIsCompl_W' ..

@[simp]
theorem spinPolarizationData_line : (J.spinPolarizationData hQJ hQ).line = ⊥ :=
  SpinPolarizationData.ofIsCompl_line ..

/-- The `(1,0)`-part of a real vector lies in the first isotropic summand of the polarization. -/
theorem holomorphicPart_mem_spinPolarizationData_W (v : V) :
    J.holomorphicPart v ∈ (J.spinPolarizationData hQJ hQ).W := by
  rw [spinPolarizationData_W]
  exact J.holomorphicPart_mem_eigenspace_baseChange_I v

/-- The `(0,1)`-part of a real vector lies in the second isotropic summand of the
polarization. -/
theorem antiholomorphicPart_mem_spinPolarizationData_W' (v : V) :
    J.antiholomorphicPart v ∈ (J.spinPolarizationData hQJ hQ).W' := by
  rw [spinPolarizationData_W']
  exact J.antiholomorphicPart_mem_eigenspace_baseChange_neg_I v

/-- The decomposition of a real vector `1 ⊗ v` along the polarization is
`(v^(1,0), v^(0,1))`, with no component in the orthogonal remainder. -/
@[simp]
theorem spinPolarizationData_decompositionEquiv_symm_tmul (v : V) :
    (J.spinPolarizationData hQJ hQ).decompositionEquiv.symm ((1 : ℂ) ⊗ₜ v) =
      ((⟨J.holomorphicPart v, J.holomorphicPart_mem_spinPolarizationData_W hQJ hQ v⟩,
        ⟨J.antiholomorphicPart v, J.antiholomorphicPart_mem_spinPolarizationData_W' hQJ hQ v⟩),
        0) := by
  rw [← J.holomorphicPart_add_antiholomorphicPart v]
  simpa using (J.spinPolarizationData hQJ hQ).decompositionEquiv_symm_apply
    ⟨J.holomorphicPart v, _⟩ ⟨J.antiholomorphicPart v, _⟩ 0

end Polarization

end TauCeti.AlmostComplexStructure

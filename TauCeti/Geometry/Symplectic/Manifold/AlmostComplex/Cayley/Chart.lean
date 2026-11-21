/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.VectorBundle.Hom
public import TauCeti.Analysis.Normed.Algebra.CayleyChart
public import TauCeti.Geometry.Symplectic.Cayley.Basic
public import TauCeti.Geometry.Symplectic.Manifold.AlmostComplex.ContMDiff
public import TauCeti.Geometry.Symplectic.Manifold.TwoForm
import TauCeti.Algebra.Algebra.NatCast
import TauCeti.Geometry.Manifold.VectorBundle.Tangent.Endomorphism

/-!
# Cayley charts of almost complex structures of finite regularity

Let `J₀` be a `Cⁿ` almost complex structure on a manifold `M`. The almost complex structures `J`
with `J₀ + J` invertible are parametrized by the sections of `End(TM)` that anticommute with `J₀`,
as in the Cayley chart of linear complex structures: a `Cⁿ` section `η`
with `1 + η` invertible at every point gives the `Cⁿ` almost complex structure

`J₀.cayleyParam η = (1 + η)⁻¹ J₀ (1 + η)`,

conjugate to `J₀` at every point (`TauCeti.ContMDiffAlmostComplexStructure.cayleyParam`), and a
`Cⁿ` almost complex structure `J` with `J₀ + J` invertible at every point has the `Cⁿ` Cayley
coordinate

`J₀.cayleyCoord J = (J₀ - J)(J₀ + J)⁻¹`

(`TauCeti.ContMDiffAlmostComplexStructure.cayleyCoord`), a section of `End(TM)` anticommuting with
`J₀`. These are the pointwise maps `TauCeti.cayleyParam` and `TauCeti.cayleyCoord` of the Cayley
chart on square roots of `-1`, applied fibrewise; the content here is that they preserve the
regularity `Cⁿ` of sections, for every finite or infinite `n`, and that they are mutually inverse
(`TauCeti.ContMDiffAlmostComplexStructure.cayleyEquiv`). So the `Cⁿ` almost complex structures `J`
with `J₀ + J` everywhere invertible are parametrized by the `J₀`-antilinear `Cⁿ` sections of
`End(TM)`, the sections `Y` with `Y J₀ + J₀ Y = 0` that vary almost complex structures in
transversality arguments. The regularity is read in the trivializations
of the tangent bundle, in which a fibre endomorphism becomes its conjugate by a linear
isomorphism; conjugation commutes with both maps (`TauCeti.map_cayleyParam`,
`TauCeti.map_cayleyCoord`), which are analytic jointly in the base point
(`TauCeti.analyticAt_uncurry_cayleyParam`, `TauCeti.analyticAt_uncurry_cayleyCoord`), so the
general criterion `ContMDiffAt.comp₂_hom_bundle` for such fibrewise operations applies.

The chart restricts to tame and to compatible structures. Let `σ` be a nondegenerate smooth
two-form and let `J₀` be compatible with `σ` at every point. At each point the linear Cayley
transform identifies the `σ`-tame complex structures with the Cayley ball and the `σ`-compatible
ones with the compatible Cayley ball (`TauCeti.SymplecticForm.Compatible.cayleyEquiv`,
`TauCeti.SymplecticForm.Compatible.compatibleCayleyEquiv`), and the Cayley coordinate of a section
is this linear transform at every point
(`TauCeti.ContMDiffAlmostComplexStructure.cayley_almostComplexStructureAt`). Hence:

* `J₀.cayleyParam η` is tamed by `σ` exactly where `η` lies in the Cayley ball
  (`TauCeti.ContMDiffAlmostComplexStructure.tames_cayleyParam_iff`), and is compatible with `σ`
  exactly where `η` lies in the compatible Cayley ball
  (`TauCeti.ContMDiffAlmostComplexStructure.compatible_cayleyParam_iff`);
* every structure tamed by `σ` lies in the domain of the chart
  (`TauCeti.ContMDiffAlmostComplexStructure.isUnit_add_of_tames`);
* the `Cⁿ` structures tamed by `σ` correspond to the `Cⁿ` sections with values in the Cayley balls
  (`TauCeti.ContMDiffAlmostComplexStructure.tameCayleyEquiv`), and the `Cⁿ` structures compatible
  with `σ` to those with values in the compatible Cayley balls
  (`TauCeti.ContMDiffAlmostComplexStructure.compatibleCayleyEquiv`).

In the compatible case the coordinate `η` is moreover self-adjoint for the metric
`g₀ = σ(·, J₀ ·)`, so the chart of compatible structures is modelled on the sections that
anticommute with `J₀` and are `g₀`-self-adjoint.

The charts are bijections preserving the regularity `Cⁿ`; no topology is put on the spaces of
sections and structures here, so continuity of the charts for a `Cⁿ` topology is not asserted.

## Main definitions

* `TauCeti.ContMDiffAlmostComplexStructure.cayleyParam`: the structure `(1 + η)⁻¹ J₀ (1 + η)`.
* `TauCeti.ContMDiffAlmostComplexStructure.cayleyCoord`: the section `(J₀ - J)(J₀ + J)⁻¹`.
* `TauCeti.ContMDiffAlmostComplexStructure.cayleyEquiv`: the Cayley chart, between antilinear
  sections with `1 + η` invertible and structures with `J₀ + J` invertible.
* `TauCeti.ContMDiffAlmostComplexStructure.tameCayleyEquiv`,
  `TauCeti.ContMDiffAlmostComplexStructure.compatibleCayleyEquiv`: its restrictions to tame and to
  compatible structures.

## Main results

* `ContMDiffAt.cayleyParam_hom_bundle`, `ContMDiffAt.cayleyCoord_hom_bundle`: the fibrewise Cayley
  maps of two `Cⁿ` families of tangent endomorphisms are `Cⁿ` where they are defined.
* `TauCeti.ContMDiffAlmostComplexStructure.cayleyCoord_cayleyParam`,
  `TauCeti.ContMDiffAlmostComplexStructure.cayleyParam_cayleyCoord`: the two maps are mutually
  inverse.
* `TauCeti.ContMDiffAlmostComplexStructure.tames_cayleyParam_iff`,
  `TauCeti.ContMDiffAlmostComplexStructure.compatible_cayleyParam_iff`: tameness and
  compatibility read in the chart.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., AMS
  Colloquium Publications **52**, 2012, Section 3.2 and Appendix B (spaces of almost complex
  structures of finite regularity and their Banach manifold charts).
* D. McDuff and D. Salamon, *Introduction to Symplectic Topology*, 3rd ed., Oxford University
  Press, 2017, Section 2.5 (the Cayley transform of linear complex structures).
* J. W. Robbin and D. A. Salamon, *A construction of the Deligne–Mumford orbifold*,
  J. Eur. Math. Soc. **8** (2006), 611–699, §7 (the conjugation chart `(1 + η)⁻¹ J₀ (1 + η)`).
-/

public section

open Bundle
open scoped Manifold ContDiff

noncomputable section

/-! ### Regularity of the fibrewise Cayley maps -/

section Regularity

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {EP HP P : Type*} [NormedAddCommGroup EP] [NormedSpace ℝ EP] [TopologicalSpace HP]
  {IP : ModelWithCorners ℝ EP HP} [TopologicalSpace P] [ChartedSpace HP P]
  {n : WithTop ℕ∞} {f : P → M}
  {A B : (q : P) → TangentSpace I (f q) →L[ℝ] TangentSpace I (f q)} {q₀ : P}

open TauCeti in
/-- **Regularity of the fibrewise Cayley parametrization.** For two families `A` and `B` of tangent
endomorphisms along a map `f`, both `Cⁿ` at `q₀` as sections of `End(TM)`, the family
`TauCeti.cayleyParam (A q) (B q) = (1 + B q)⁻¹ A q (1 + B q)` is `Cⁿ` at `q₀` when `1 + B q₀` is
invertible. -/
theorem ContMDiffAt.cayleyParam_hom_bundle (hf : ContMDiffAt IP I n f q₀)
    (hA : ContMDiffAt IP (I.prod 𝓘(ℝ, E →L[ℝ] E)) n
      (fun q ↦ TotalSpace.mk' (E →L[ℝ] E)
        (E := fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x) (f q) (A q)) q₀)
    (hB : ContMDiffAt IP (I.prod 𝓘(ℝ, E →L[ℝ] E)) n
      (fun q ↦ TotalSpace.mk' (E →L[ℝ] E)
        (E := fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x) (f q) (B q)) q₀)
    (hu : IsUnit (1 + B q₀)) :
    ContMDiffAt IP (I.prod 𝓘(ℝ, E →L[ℝ] E)) n
      (fun q ↦ TotalSpace.mk' (E →L[ℝ] E)
        (E := fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x) (f q)
        (cayleyParam (A q) (B q))) q₀ :=
  ContMDiffAt.comp₂_hom_bundle (g := Function.uncurry cayleyParam)
    (fun L ↦ (analyticAt_uncurry_cayleyParam (𝕜 := ℝ)
      (by simpa only [map_add, map_one] using hu.map L.conjContinuousAlgEquiv)).contDiffAt)
    (fun _ L a b ↦ map_cayleyParam L.conjContinuousAlgEquiv a b) hf hA hB

open TauCeti in
/-- **Regularity of the fibrewise Cayley coordinate.** For two families `A` and `B` of tangent
endomorphisms along a map `f`, both `Cⁿ` at `q₀` as sections of `End(TM)`, the family
`TauCeti.cayleyCoord (A q) (B q) = (A q - B q)(A q + B q)⁻¹` is `Cⁿ` at `q₀` when `A q₀ + B q₀` is
invertible. -/
theorem ContMDiffAt.cayleyCoord_hom_bundle (hf : ContMDiffAt IP I n f q₀)
    (hA : ContMDiffAt IP (I.prod 𝓘(ℝ, E →L[ℝ] E)) n
      (fun q ↦ TotalSpace.mk' (E →L[ℝ] E)
        (E := fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x) (f q) (A q)) q₀)
    (hB : ContMDiffAt IP (I.prod 𝓘(ℝ, E →L[ℝ] E)) n
      (fun q ↦ TotalSpace.mk' (E →L[ℝ] E)
        (E := fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x) (f q) (B q)) q₀)
    (hu : IsUnit (A q₀ + B q₀)) :
    ContMDiffAt IP (I.prod 𝓘(ℝ, E →L[ℝ] E)) n
      (fun q ↦ TotalSpace.mk' (E →L[ℝ] E)
        (E := fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x) (f q)
        (cayleyCoord (A q) (B q))) q₀ :=
  ContMDiffAt.comp₂_hom_bundle (g := Function.uncurry cayleyCoord)
    (fun L ↦ (analyticAt_uncurry_cayleyCoord (𝕜 := ℝ)
      (by simpa only [map_add] using hu.map L.conjContinuousAlgEquiv)).contDiffAt)
    (fun _ L a b ↦ map_cayleyCoord L.conjContinuousAlgEquiv a b) hf hA hB

end Regularity

namespace TauCeti

namespace ContMDiffAlmostComplexStructure

section Chart

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] {n : ℕ∞}
  {J₀ J : ContMDiffAlmostComplexStructure I n M}
  {η : ContMDiffSection I (E →L[ℝ] E) n fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x}

/-! ### The Cayley chart -/

variable (J₀) in
/-- **The Cayley parametrization of almost complex structures.** For a `Cⁿ` almost complex
structure `J₀` and a `Cⁿ` section `η` of `End(TM)` with `1 + η` invertible at every point, the `Cⁿ`
almost complex structure `(1 + η)⁻¹ J₀ (1 + η)`. For `J₀`-antilinear `η` it is the inverse of the
Cayley coordinate (`TauCeti.ContMDiffAlmostComplexStructure.cayleyEquiv`). -/
def cayleyParam
    (η : ContMDiffSection I (E →L[ℝ] E) n fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x)
    (hη : ∀ x, IsUnit (1 + η x)) : ContMDiffAlmostComplexStructure I n M where
  toEndomorphism :=
    { toFun := fun x ↦ TauCeti.cayleyParam (J₀.toEndomorphism x) (η x)
      contMDiff_toFun := fun x ↦ ContMDiffAt.cayleyParam_hom_bundle (f := id) contMDiffAt_id
        (J₀.toEndomorphism.contMDiff x) (η.contMDiff x) (hη x) }
  square_neg x := by
    rw [← ContinuousLinearMap.mul_def, ← ContinuousLinearMap.one_def]
    exact cayleyParam_mul_self (J₀.toEndomorphism_mul_self x) (hη x)

/-- The value of the Cayley parametrization at a point. -/
@[simp]
theorem cayleyParam_toEndomorphism_apply (hη : ∀ x, IsUnit (1 + η x)) (x : M) :
    (J₀.cayleyParam η hη).toEndomorphism x = TauCeti.cayleyParam (J₀.toEndomorphism x) (η x) :=
  (rfl)

variable (J₀ J) in
/-- **The Cayley coordinate of almost complex structures.** For `Cⁿ` almost complex structures
`J₀` and `J` with `J₀ + J` invertible at every point, the `Cⁿ` section `(J₀ - J)(J₀ + J)⁻¹` of
`End(TM)`. It anticommutes with `J₀`
(`TauCeti.ContMDiffAlmostComplexStructure.cayleyCoord_mul_eq_neg_mul`), and the Cayley
parametrization recovers `J` from it
(`TauCeti.ContMDiffAlmostComplexStructure.cayleyParam_cayleyCoord`). -/
def cayleyCoord (hJ : ∀ x, IsUnit (J₀.toEndomorphism x + J.toEndomorphism x)) :
    ContMDiffSection I (E →L[ℝ] E) n fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x where
  toFun x := TauCeti.cayleyCoord (J₀.toEndomorphism x) (J.toEndomorphism x)
  contMDiff_toFun x := ContMDiffAt.cayleyCoord_hom_bundle (f := id) contMDiffAt_id
    (J₀.toEndomorphism.contMDiff x) (J.toEndomorphism.contMDiff x) (hJ x)

/-- The value of the Cayley coordinate at a point. -/
@[simp]
theorem cayleyCoord_apply (hJ : ∀ x, IsUnit (J₀.toEndomorphism x + J.toEndomorphism x))
    (x : M) :
    J₀.cayleyCoord J hJ x = TauCeti.cayleyCoord (J₀.toEndomorphism x) (J.toEndomorphism x) :=
  (rfl)

/-- The Cayley parametrization sends `0` to `J₀`. -/
@[simp]
theorem cayleyParam_zero (hη : ∀ x, IsUnit (1 + (0 : ContMDiffSection I (E →L[ℝ] E) n
    fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x) x)) :
    J₀.cayleyParam 0 hη = J₀ := by
  ext x v
  simp

/-- The Cayley coordinate of `J₀` relative to itself is `0`. -/
@[simp]
theorem cayleyCoord_self (hJ : ∀ x, IsUnit (J₀.toEndomorphism x + J₀.toEndomorphism x)) :
    J₀.cayleyCoord J₀ hJ = 0 := by
  ext x
  simp

/-- **The Cayley coordinate is antilinear**: it anticommutes with `J₀` at every point. -/
theorem cayleyCoord_mul_eq_neg_mul
    (hJ : ∀ x, IsUnit (J₀.toEndomorphism x + J.toEndomorphism x)) (x : M) :
    J₀.cayleyCoord J hJ x * J₀.toEndomorphism x = -(J₀.toEndomorphism x * J₀.cayleyCoord J hJ x) :=
  TauCeti.cayleyCoord_mul_eq_neg_mul (J₀.toEndomorphism_mul_self x) (J.toEndomorphism_mul_self x)

/-- For a `J₀`-antilinear section `η`, the Cayley parametrization lies in the domain of the Cayley
coordinate: `J₀ + J₀.cayleyParam η` is invertible at every point. -/
theorem isUnit_add_cayleyParam
    (hη' : ∀ x, η x * J₀.toEndomorphism x = -(J₀.toEndomorphism x * η x))
    (hη : ∀ x, IsUnit (1 + η x)) (x : M) :
    IsUnit (J₀.toEndomorphism x + (J₀.cayleyParam η hη).toEndomorphism x) :=
  TauCeti.isUnit_add_cayleyParam (IsUnit.ofNat_of_algebra (K := ℝ) two_ne_zero.isUnit)
    (J₀.toEndomorphism_mul_self x) (hη' x) (hη x)

/-- The Cayley coordinate lies in the domain of the Cayley parametrization: `1 + J₀.cayleyCoord J`
is invertible at every point. -/
theorem isUnit_one_add_cayleyCoord
    (hJ : ∀ x, IsUnit (J₀.toEndomorphism x + J.toEndomorphism x)) (x : M) :
    IsUnit (1 + J₀.cayleyCoord J hJ x) :=
  TauCeti.isUnit_one_add_cayleyCoord (IsUnit.ofNat_of_algebra (K := ℝ) two_ne_zero.isUnit)
    (J₀.toEndomorphism_mul_self x) (hJ x)

/-- **The Cayley coordinate inverts the Cayley parametrization** on the `J₀`-antilinear sections. -/
@[simp]
theorem cayleyCoord_cayleyParam
    (hη' : ∀ x, η x * J₀.toEndomorphism x = -(J₀.toEndomorphism x * η x))
    (hη : ∀ x, IsUnit (1 + η x)) :
    J₀.cayleyCoord (J₀.cayleyParam η hη) (isUnit_add_cayleyParam hη' hη) = η := by
  refine ContMDiffSection.ext fun x ↦ ?_
  simp only [cayleyCoord_apply, cayleyParam_toEndomorphism_apply]
  exact TauCeti.cayleyCoord_cayleyParam (IsUnit.ofNat_of_algebra (K := ℝ) two_ne_zero.isUnit)
    (J₀.toEndomorphism_mul_self x) (hη' x) (hη x)

/-- **The Cayley parametrization inverts the Cayley coordinate.** -/
@[simp]
theorem cayleyParam_cayleyCoord
    (hJ : ∀ x, IsUnit (J₀.toEndomorphism x + J.toEndomorphism x)) :
    J₀.cayleyParam (J₀.cayleyCoord J hJ) (isUnit_one_add_cayleyCoord hJ) = J := by
  ext x v
  simp only [cayleyParam_toEndomorphism_apply, cayleyCoord_apply]
  rw [TauCeti.cayleyParam_cayleyCoord (IsUnit.ofNat_of_algebra (K := ℝ) two_ne_zero.isUnit)
    (J₀.toEndomorphism_mul_self x) (J.toEndomorphism_mul_self x) (hJ x)]

variable (J₀) in
/-- **The Cayley chart of almost complex structures of finite regularity.** For a `Cⁿ` almost
complex structure `J₀`, the Cayley parametrization `η ↦ (1 + η)⁻¹ J₀ (1 + η)` is a bijection from
the `J₀`-antilinear `Cⁿ` sections `η` of `End(TM)` with `1 + η` invertible at every point onto the
`Cⁿ` almost complex structures `J` with `J₀ + J` invertible at every point. Its inverse is the
Cayley coordinate `J ↦ (J₀ - J)(J₀ + J)⁻¹`. -/
def cayleyEquiv :
    {η : ContMDiffSection I (E →L[ℝ] E) n fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x //
      (∀ x, η x * J₀.toEndomorphism x = -(J₀.toEndomorphism x * η x)) ∧ ∀ x, IsUnit (1 + η x)} ≃
    {J : ContMDiffAlmostComplexStructure I n M //
      ∀ x, IsUnit (J₀.toEndomorphism x + J.toEndomorphism x)} where
  toFun η := ⟨J₀.cayleyParam η η.2.2, isUnit_add_cayleyParam η.2.1 η.2.2⟩
  invFun J :=
    ⟨J₀.cayleyCoord J J.2, cayleyCoord_mul_eq_neg_mul J.2, isUnit_one_add_cayleyCoord J.2⟩
  left_inv η := Subtype.ext (cayleyCoord_cayleyParam η.2.1 η.2.2)
  right_inv J := Subtype.ext (cayleyParam_cayleyCoord J.2)

/-- The Cayley chart is the Cayley parametrization. -/
@[simp]
theorem coe_cayleyEquiv_apply
    (η : {η : ContMDiffSection I (E →L[ℝ] E) n
        fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x //
      (∀ x, η x * J₀.toEndomorphism x = -(J₀.toEndomorphism x * η x)) ∧ ∀ x, IsUnit (1 + η x)}) :
    (J₀.cayleyEquiv η : ContMDiffAlmostComplexStructure I n M) = J₀.cayleyParam η η.2.2 :=
  (rfl)

/-- The inverse of the Cayley chart is the Cayley coordinate. -/
@[simp]
theorem coe_cayleyEquiv_symm_apply
    (J : {J : ContMDiffAlmostComplexStructure I n M //
      ∀ x, IsUnit (J₀.toEndomorphism x + J.toEndomorphism x)}) :
    (J₀.cayleyEquiv.symm J : ContMDiffSection I (E →L[ℝ] E) n
      fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x) = J₀.cayleyCoord J J.2 :=
  (rfl)

end Chart

/-! ### Tame and compatible structures in the Cayley chart -/

section Form

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] {n : ℕ∞}
  {J₀ J : ContMDiffAlmostComplexStructure I n M}
  {η : ContMDiffSection I (E →L[ℝ] E) n fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x}
  {σ : SmoothTwoForm I M} (hσ : σ.IsNondegenerate)

variable (J₀ J) in
/-- **The Cayley coordinate is the linear Cayley transform.** At every point, the Cayley coordinate
`(J₀ - J)(J₀ + J)⁻¹` of two almost complex structures is the Cayley transform
`-(1 + J₀ J)(1 - J₀ J)⁻¹` of the complex structures they induce on the tangent space. -/
theorem cayley_almostComplexStructureAt (x : M) :
    (J₀.almostComplexStructureAt x).cayley (J.almostComplexStructureAt x) =
      (TauCeti.cayleyCoord (J₀.toEndomorphism x) (J.toEndomorphism x)).toLinearMap := by
  rw [AlmostComplexStructure.cayley_eq_cayleyFormula, almostComplexStructureAt_toLinearMap,
    almostComplexStructureAt_toLinearMap, ← cayleyCoord_eq_cayleyFormula
      (coe_toEndomorphism_mul_self J₀ x) (coe_toEndomorphism_mul_self J x)]
  exact (ContinuousLinearMap.coe_cayleyCoord (V := E) _ _).symm

/-- At a point where `η` is `J₀`-antilinear, the linear Cayley transform of the Cayley
parametrization `J₀.cayleyParam η` relative to `J₀` is `η`. -/
theorem cayley_almostComplexStructureAt_cayleyParam {x : M}
    (hη' : η x * J₀.toEndomorphism x = -(J₀.toEndomorphism x * η x))
    (hη : ∀ x, IsUnit (1 + η x)) :
    (J₀.almostComplexStructureAt x).cayley ((J₀.cayleyParam η hη).almostComplexStructureAt x) =
      (η x).toLinearMap := by
  rw [cayley_almostComplexStructureAt, cayleyParam_toEndomorphism_apply,
    TauCeti.cayleyCoord_cayleyParam (IsUnit.ofNat_of_algebra (K := ℝ) two_ne_zero.isUnit)
      (J₀.toEndomorphism_mul_self x) hη' (hη x)]

/-- At a point where `η` lies in the Cayley ball, the Cayley parametrization is the inverse linear
Cayley transform of `η x`. -/
private theorem almostComplexStructureAt_cayleyParam {x : M}
    (h₀ : (hσ.symplecticFormAt x).Compatible (J₀.almostComplexStructureAt x))
    (hC : (η x).toLinearMap ∈ (hσ.symplecticFormAt x).cayleyBall (J₀.almostComplexStructureAt x))
    (hη : ∀ x, IsUnit (1 + η x)) :
    (J₀.cayleyParam η hη).almostComplexStructureAt x = (h₀.cayleyEquiv.symm ⟨_, hC⟩).val := by
  refine AlmostComplexStructure.toLinearMap_injective ?_
  rw [SymplecticForm.Compatible.cayleyEquiv_symm_apply_toLinearMap,
    almostComplexStructureAt_toLinearMap, almostComplexStructureAt_toLinearMap,
    cayleyParam_toEndomorphism_apply, ← cayleyParam_eq_mul_mul_inverse
      (coe_toEndomorphism_mul_self J₀ x) (by simpa using (SymplecticForm.mem_cayleyBall.1 hC).1)]
  exact ContinuousLinearMap.coe_cayleyParam (V := E) _ _

/-- **Tameness in the Cayley chart.** Let `J₀` be compatible with `σ` at `x`, and `η`
`J₀`-antilinear at `x`. Then `σ` tames the Cayley parametrization `J₀.cayleyParam η` at `x`
exactly when `η x` lies in the Cayley ball of `σ` at `J₀`. -/
theorem tames_cayleyParam_iff {x : M}
    (h₀ : (hσ.symplecticFormAt x).Compatible (J₀.almostComplexStructureAt x))
    (hη' : η x * J₀.toEndomorphism x = -(J₀.toEndomorphism x * η x))
    (hη : ∀ x, IsUnit (1 + η x)) :
    (hσ.symplecticFormAt x).Tames ((J₀.cayleyParam η hη).almostComplexStructureAt x) ↔
      (η x).toLinearMap ∈ (hσ.symplecticFormAt x).cayleyBall (J₀.almostComplexStructureAt x) := by
  refine ⟨fun h ↦ ?_, fun hC ↦ ?_⟩
  · rw [← cayley_almostComplexStructureAt_cayleyParam hη' hη]
    exact h₀.cayley_mem_cayleyBall h
  · rw [almostComplexStructureAt_cayleyParam hσ h₀ hC hη]
    exact (h₀.cayleyEquiv.symm _).2

/-- **Compatibility in the Cayley chart.** Let `J₀` be compatible with `σ` at `x`, and `η`
`J₀`-antilinear at `x`. Then the Cayley parametrization `J₀.cayleyParam η` is compatible with `σ`
at `x` exactly when `η x` lies in the compatible Cayley ball of `σ` at `J₀`: the Cayley ball,
intersected with the endomorphisms self-adjoint for the metric `σ(·, J₀ ·)`. -/
theorem compatible_cayleyParam_iff {x : M}
    (h₀ : (hσ.symplecticFormAt x).Compatible (J₀.almostComplexStructureAt x))
    (hη' : η x * J₀.toEndomorphism x = -(J₀.toEndomorphism x * η x))
    (hη : ∀ x, IsUnit (1 + η x)) :
    (hσ.symplecticFormAt x).Compatible ((J₀.cayleyParam η hη).almostComplexStructureAt x) ↔
      (η x).toLinearMap ∈
        (hσ.symplecticFormAt x).compatibleCayleyBall (J₀.almostComplexStructureAt x) := by
  refine ⟨fun h ↦ ?_, fun hC ↦ ?_⟩
  · rw [← cayley_almostComplexStructureAt_cayleyParam hη' hη]
    exact (h₀.cayley_mem_compatibleCayleyBall_iff h.tames).2 h
  · have ht := (tames_cayleyParam_iff hσ h₀ hη' hη).2
      (SymplecticForm.compatibleCayleyBall_subset_cayleyBall hC)
    rw [← cayley_almostComplexStructureAt_cayleyParam hη' hη] at hC
    exact (h₀.cayley_mem_compatibleCayleyBall_iff ht).1 hC

/-- **Tame structures lie in the Cayley chart.** If `σ` tames `J₀` and `J` at `x`, then
`J₀ + J` is invertible at `x`. -/
theorem isUnit_add_of_tames {x : M}
    (h₀ : (hσ.symplecticFormAt x).Tames (J₀.almostComplexStructureAt x))
    (h : (hσ.symplecticFormAt x).Tames (J.almostComplexStructureAt x)) :
    IsUnit (J₀.toEndomorphism x + J.toEndomorphism x) := by
  have hu := h₀.isUnit_one_sub_mul h
  rw [almostComplexStructureAt_toLinearMap, almostComplexStructureAt_toLinearMap,
    ← isUnit_add_iff_isUnit_one_sub_mul (coe_toEndomorphism_mul_self J₀ x)] at hu
  exact (ContinuousLinearMap.isUnit_iff_isUnit_toLinearMap (E := E)).2 hu

omit [FiniteDimensional ℝ E] in
/-- A section with a value in the Cayley ball of `σ` at `J₀` anticommutes with `J₀` there. -/
theorem mul_eq_neg_mul_of_mem_cayleyBall {x : M}
    (hC : (η x).toLinearMap ∈ (hσ.symplecticFormAt x).cayleyBall (J₀.almostComplexStructureAt x)) :
    η x * J₀.toEndomorphism x = -(J₀.toEndomorphism x * η x) := by
  have h := (SymplecticForm.mem_cayleyBall.1 hC).1
  rw [almostComplexStructureAt_toLinearMap] at h
  exact ContinuousLinearMap.coe_injective (by simpa using h)

/-- A section with a value `η x` in the Cayley ball of `σ` at `J₀` has `1 + η x` invertible, as the
Cayley parametrization requires. -/
theorem isUnit_one_add_of_mem_cayleyBall {x : M}
    (hC : (η x).toLinearMap ∈ (hσ.symplecticFormAt x).cayleyBall (J₀.almostComplexStructureAt x)) :
    IsUnit (1 + η x) := by
  have h : IsUnit ((1 + η x : TangentSpace I x →L[ℝ] TangentSpace I x) :
      TangentSpace I x →ₗ[ℝ] TangentSpace I x) := by
    simpa using SymplecticForm.isUnit_one_add_of_mem_cayleyBall hC
  exact (ContinuousLinearMap.isUnit_iff_isUnit_toLinearMap (E := E)).2 h

omit [FiniteDimensional ℝ E] in
/-- A section with a value in the compatible Cayley ball of `σ` at `J₀` anticommutes with `J₀`
there. -/
theorem mul_eq_neg_mul_of_mem_compatibleCayleyBall {x : M}
    (hC : (η x).toLinearMap ∈
      (hσ.symplecticFormAt x).compatibleCayleyBall (J₀.almostComplexStructureAt x)) :
    η x * J₀.toEndomorphism x = -(J₀.toEndomorphism x * η x) :=
  mul_eq_neg_mul_of_mem_cayleyBall hσ (SymplecticForm.compatibleCayleyBall_subset_cayleyBall hC)

/-- A section with a value `η x` in the compatible Cayley ball of `σ` at `J₀` has `1 + η x`
invertible, as the Cayley parametrization requires. -/
theorem isUnit_one_add_of_mem_compatibleCayleyBall {x : M}
    (hC : (η x).toLinearMap ∈
      (hσ.symplecticFormAt x).compatibleCayleyBall (J₀.almostComplexStructureAt x)) :
    IsUnit (1 + η x) :=
  isUnit_one_add_of_mem_cayleyBall hσ (SymplecticForm.compatibleCayleyBall_subset_cayleyBall hC)

variable (J₀) in
/-- **The Cayley chart of tame structures.** Let `J₀` be a `Cⁿ` almost complex structure
compatible with a nondegenerate two-form `σ`. The Cayley parametrization is a bijection from the
`Cⁿ` sections `η` of `End(TM)` with values in the Cayley balls of `σ` at `J₀` onto the `Cⁿ` almost
complex structures tamed by `σ`, with inverse the Cayley coordinate. -/
def tameCayleyEquiv (h₀ : ∀ x, (hσ.symplecticFormAt x).Compatible (J₀.almostComplexStructureAt x)) :
    {η : ContMDiffSection I (E →L[ℝ] E) n fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x //
      ∀ x, (η x).toLinearMap ∈ (hσ.symplecticFormAt x).cayleyBall (J₀.almostComplexStructureAt x)} ≃
    {J : ContMDiffAlmostComplexStructure I n M //
      ∀ x, (hσ.symplecticFormAt x).Tames (J.almostComplexStructureAt x)} where
  toFun η := ⟨J₀.cayleyParam η fun x ↦ isUnit_one_add_of_mem_cayleyBall hσ (η.2 x), fun x ↦
    (tames_cayleyParam_iff hσ (h₀ x) (mul_eq_neg_mul_of_mem_cayleyBall hσ (η.2 x))
      fun x ↦ isUnit_one_add_of_mem_cayleyBall hσ (η.2 x)).2 (η.2 x)⟩
  invFun J := ⟨J₀.cayleyCoord J fun x ↦ isUnit_add_of_tames hσ (h₀ x).tames (J.2 x), fun x ↦ by
    rw [cayleyCoord_apply, ← cayley_almostComplexStructureAt]
    exact (h₀ x).cayley_mem_cayleyBall (J.2 x)⟩
  left_inv η := Subtype.ext (cayleyCoord_cayleyParam
    (fun x ↦ mul_eq_neg_mul_of_mem_cayleyBall hσ (η.2 x))
    fun x ↦ isUnit_one_add_of_mem_cayleyBall hσ (η.2 x))
  right_inv J := Subtype.ext
    (cayleyParam_cayleyCoord fun x ↦ isUnit_add_of_tames hσ (h₀ x).tames (J.2 x))

/-- The Cayley chart of tame structures is the Cayley parametrization. -/
@[simp]
theorem coe_tameCayleyEquiv_apply
    (h₀ : ∀ x, (hσ.symplecticFormAt x).Compatible (J₀.almostComplexStructureAt x))
    (η : {η : ContMDiffSection I (E →L[ℝ] E) n
        fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x //
      ∀ x, (η x).toLinearMap ∈
        (hσ.symplecticFormAt x).cayleyBall (J₀.almostComplexStructureAt x)}) :
    (J₀.tameCayleyEquiv hσ h₀ η : ContMDiffAlmostComplexStructure I n M) =
      J₀.cayleyParam η fun x ↦ isUnit_one_add_of_mem_cayleyBall hσ (η.2 x) :=
  (rfl)

/-- The inverse of the Cayley chart of tame structures is the Cayley coordinate. -/
@[simp]
theorem coe_tameCayleyEquiv_symm_apply
    (h₀ : ∀ x, (hσ.symplecticFormAt x).Compatible (J₀.almostComplexStructureAt x))
    (J : {J : ContMDiffAlmostComplexStructure I n M //
      ∀ x, (hσ.symplecticFormAt x).Tames (J.almostComplexStructureAt x)}) :
    ((J₀.tameCayleyEquiv hσ h₀).symm J : ContMDiffSection I (E →L[ℝ] E) n
      fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x) =
      J₀.cayleyCoord J fun x ↦ isUnit_add_of_tames hσ (h₀ x).tames (J.2 x) :=
  (rfl)

variable (J₀) in
/-- **The Cayley chart of compatible structures.** Let `J₀` be a `Cⁿ` almost complex structure
compatible with a nondegenerate two-form `σ`. The Cayley parametrization is a bijection from the
`Cⁿ` sections `η` of `End(TM)` with values in the compatible Cayley balls of `σ` at `J₀` onto the
`Cⁿ` almost complex structures compatible with `σ`, with inverse the Cayley coordinate. -/
def compatibleCayleyEquiv
    (h₀ : ∀ x, (hσ.symplecticFormAt x).Compatible (J₀.almostComplexStructureAt x)) :
    {η : ContMDiffSection I (E →L[ℝ] E) n fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x //
      ∀ x, (η x).toLinearMap ∈
        (hσ.symplecticFormAt x).compatibleCayleyBall (J₀.almostComplexStructureAt x)} ≃
    {J : ContMDiffAlmostComplexStructure I n M //
      ∀ x, (hσ.symplecticFormAt x).Compatible (J.almostComplexStructureAt x)} where
  toFun η := ⟨J₀.cayleyParam η fun x ↦ isUnit_one_add_of_mem_compatibleCayleyBall hσ (η.2 x),
    fun x ↦ (compatible_cayleyParam_iff hσ (h₀ x)
      (mul_eq_neg_mul_of_mem_compatibleCayleyBall hσ (η.2 x))
      fun x ↦ isUnit_one_add_of_mem_compatibleCayleyBall hσ (η.2 x)).2 (η.2 x)⟩
  invFun J := ⟨J₀.cayleyCoord J fun x ↦ isUnit_add_of_tames hσ (h₀ x).tames (J.2 x).tames,
    fun x ↦ by
      rw [cayleyCoord_apply, ← cayley_almostComplexStructureAt]
      exact ((h₀ x).cayley_mem_compatibleCayleyBall_iff (J.2 x).tames).2 (J.2 x)⟩
  left_inv η := Subtype.ext (cayleyCoord_cayleyParam
    (fun x ↦ mul_eq_neg_mul_of_mem_compatibleCayleyBall hσ (η.2 x))
    fun x ↦ isUnit_one_add_of_mem_compatibleCayleyBall hσ (η.2 x))
  right_inv J := Subtype.ext
    (cayleyParam_cayleyCoord fun x ↦ isUnit_add_of_tames hσ (h₀ x).tames (J.2 x).tames)

/-- The Cayley chart of compatible structures is the Cayley parametrization. -/
@[simp]
theorem coe_compatibleCayleyEquiv_apply
    (h₀ : ∀ x, (hσ.symplecticFormAt x).Compatible (J₀.almostComplexStructureAt x))
    (η : {η : ContMDiffSection I (E →L[ℝ] E) n
        fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x //
      ∀ x, (η x).toLinearMap ∈
        (hσ.symplecticFormAt x).compatibleCayleyBall (J₀.almostComplexStructureAt x)}) :
    (J₀.compatibleCayleyEquiv hσ h₀ η : ContMDiffAlmostComplexStructure I n M) =
      J₀.cayleyParam η fun x ↦ isUnit_one_add_of_mem_compatibleCayleyBall hσ (η.2 x) :=
  (rfl)

/-- The inverse of the Cayley chart of compatible structures is the Cayley coordinate. -/
@[simp]
theorem coe_compatibleCayleyEquiv_symm_apply
    (h₀ : ∀ x, (hσ.symplecticFormAt x).Compatible (J₀.almostComplexStructureAt x))
    (J : {J : ContMDiffAlmostComplexStructure I n M //
      ∀ x, (hσ.symplecticFormAt x).Compatible (J.almostComplexStructureAt x)}) :
    ((J₀.compatibleCayleyEquiv hσ h₀).symm J : ContMDiffSection I (E →L[ℝ] E) n
      fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x) =
      J₀.cayleyCoord J fun x ↦ isUnit_add_of_tames hσ (h₀ x).tames (J.2 x).tames :=
  (rfl)

end Form

end ContMDiffAlmostComplexStructure

end TauCeti

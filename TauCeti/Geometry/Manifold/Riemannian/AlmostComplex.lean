/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.HodgeStar.Kahler
public import TauCeti.Geometry.Manifold.DifferentialForm.AlmostComplexType
public import TauCeti.Geometry.Manifold.DifferentialForm.DegreeOne
public import TauCeti.Geometry.Manifold.Riemannian.HodgeStar
public import TauCeti.Geometry.Manifold.VectorBundle.Riemannian.Riesz
import TauCeti.Geometry.Manifold.VectorBundle.Riemannian.ChartGram

/-!
# Smooth forms on almost-Hermitian Riemannian manifolds

Let `(M, g)` be a Riemannian manifold equipped with a smooth almost complex structure `J` that is
fibrewise orthogonal (`⟪J_x u, J_x w⟫ = ⟪u, w⟫`). This file bridges the pointwise exterior-power
algebra of `TauCeti.AlmostComplexStructure` (`kahlerForm`, `lieMap`, and Riesz duality) with global
smooth differential forms:

1. Under `TauCeti.alternatingFormEquiv` and `Riemannian.Tensor.rieszDual`, a smooth one-form `a`
   corresponds fibrewise to its Riesz-dual tangent vector, and `J.covectorComplexStructure`
   intertwines with `J_x`
   (`TauCeti.SmoothAlmostComplexStructure.rieszDual_covectorComplexStructure`).
2. The fibrewise Kähler two-vectors `(J.almostComplexStructureAt x).kahlerForm` assemble into a
   smooth two-form `J.kahlerTwoForm hJ : SmoothForm I M ℝ 2` representing `ω_x(u, w) = ⟪J_x u, w⟫`.
3. Under `(alternatingFormEquiv (TangentSpace I x) 2).symm`, the negative real derivation
   `-J.toEndomorphism.realAlternatingDerivation` on smooth two-forms acts fibrewise as
   `exteriorPower.lieMap 2 (J.almostComplexStructureAt x).toLinearMap`.

## Main definitions

* `TauCeti.SmoothAlmostComplexStructure.kahlerTwoForm`: the smooth Kähler two-form
  `ω_x(u, w) = ⟪J_x u, w⟫` of an orthogonal smooth almost complex structure `J`.

## Main results

* `TauCeti.SmoothForm.alternatingFormEquiv_rieszDual_degreeOneEquiv`: fibrewise identification of a
  smooth one-form with its Riesz-dual tangent vector under `alternatingFormEquiv`.
* `TauCeti.SmoothAlmostComplexStructure.rieszDual_covectorComplexStructure`: Riesz duality
  intertwines `J.covectorComplexStructure` with `J`.
* `TauCeti.SmoothAlmostComplexStructure.isSmoothForm_kahlerForm`: smoothness of the Kähler
  two-form.
* `TauCeti.SmoothAlmostComplexStructure.alternatingFormEquiv_symm_kahlerTwoForm` and
  `SmoothAlmostComplexStructure.alternatingFormEquiv_symm_neg_realAlternatingDerivation_two`:
  fibrewise bivector formulas for `J.kahlerTwoForm` and
  `-J.toEndomorphism.realAlternatingDerivation`.

## References

* D. Huybrechts, *Complex Geometry: An Introduction*, Universitext, Springer, 2005, Section 1.2.
* S. K. Donaldson and P. B. Kronheimer, *The Geometry of Four-Manifolds*, Oxford University Press,
  1990.
-/

public section

noncomputable section

open Bundle Module Set exteriorPower
open scoped Manifold ContDiff RealInnerProductSpace Topology

namespace TauCeti

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [FiniteDimensional ℝ E] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]

namespace SmoothForm

/-- Under `alternatingFormEquiv`, a smooth one-form at `x` corresponds to the tangent vector given
by the Riesz dual of `SmoothForm.degreeOneEquiv`. -/
theorem alternatingFormEquiv_rieszDual_degreeOneEquiv (a : SmoothForm I M ℝ 1) (x : M) :
    (letI : FiniteDimensional ℝ (TangentSpace I x) :=
      VectorBundle.finiteDimensional ℝ E (TangentSpace I) x
     alternatingFormEquiv (TangentSpace I x) 1
      (ιMulti ℝ 1 ![Riemannian.Tensor.rieszDual (I := I) x (degreeOneEquiv a x)])) =
      a.1 x := by
  let _ : FiniteDimensional ℝ (TangentSpace I x) :=
    VectorBundle.finiteDimensional ℝ E (TangentSpace I) x
  ext w
  have hw : ![w 0] = w := funext fun i ↦ by fin_cases i; rfl
  rw [alternatingFormEquiv_ιMulti_apply, Matrix.det_fin_one]
  simp only [Matrix.of_apply, Matrix.cons_val_fin_one, Riemannian.Tensor.inner_rieszDual,
    degreeOneEquiv_apply_apply_vec, hw]

end SmoothForm

namespace SmoothAlmostComplexStructure

/-- When `J` is fibrewise orthogonal, `J.covectorComplexStructure` corresponds under the Riesz
isomorphism on `T_x M` to `J_x`. -/
theorem rieszDual_covectorComplexStructure {J : SmoothAlmostComplexStructure I M}
    (hJ : ∀ (x : M) (u w : TangentSpace I x), ⟪J x u, J x w⟫ = ⟪u, w⟫)
    (a : SmoothForm I M ℝ 1) (x : M) :
    Riemannian.Tensor.rieszDual (I := I) x
        (SmoothForm.degreeOneEquiv (J.covectorComplexStructure a) x) =
      J x (Riemannian.Tensor.rieszDual (I := I) x (SmoothForm.degreeOneEquiv a x)) := by
  let _ : FiniteDimensional ℝ (TangentSpace I x) :=
    VectorBundle.finiteDimensional ℝ E (TangentSpace I) x
  have hJ' : ∀ u w : TangentSpace I x,
      ⟪J.almostComplexStructureAt x u, J.almostComplexStructureAt x w⟫ = ⟪u, w⟫ := by
    simpa only [almostComplexStructureAt_apply] using hJ x
  symm
  rw [Riemannian.Tensor.eq_rieszDual_iff_inner_eq]
  intro w
  rw [SmoothForm.degreeOneEquiv_apply_apply_vec, covectorComplexStructure_apply_vec,
    ← SmoothForm.degreeOneEquiv_apply_apply_vec, ← Riemannian.Tensor.inner_rieszDual]
  simpa only [almostComplexStructureAt_apply] using
    AlmostComplexStructure.inner_apply_left hJ'
      (Riemannian.Tensor.rieszDual (I := I) x (SmoothForm.degreeOneEquiv a x)) w

/-- Under `(alternatingFormEquiv _ 2).symm`, `-J.toEndomorphism.realAlternatingDerivation` of an
orthogonal `J` acts on smooth two-forms as `exteriorPower.lieMap 2 J_x`. -/
theorem alternatingFormEquiv_symm_neg_realAlternatingDerivation_two
    {J : SmoothAlmostComplexStructure I M}
    (hJ : ∀ (x : M) (u w : TangentSpace I x), ⟪J x u, J x w⟫ = ⟪u, w⟫)
    (η : SmoothForm I M ℝ 2) (x : M) :
    (letI : FiniteDimensional ℝ (TangentSpace I x) :=
      VectorBundle.finiteDimensional ℝ E (TangentSpace I) x
     (alternatingFormEquiv (TangentSpace I x) 2).symm
       ((-J.toEndomorphism.realAlternatingDerivation η).1 x)) =
      (letI : FiniteDimensional ℝ (TangentSpace I x) :=
        VectorBundle.finiteDimensional ℝ E (TangentSpace I) x
       exteriorPower.lieMap 2 (J.almostComplexStructureAt x).toLinearMap
         ((alternatingFormEquiv (TangentSpace I x) 2).symm (η.1 x))) := by
  let _ : FiniteDimensional ℝ (TangentSpace I x) :=
    VectorBundle.finiteDimensional ℝ E (TangentSpace I) x
  have hJ' : ∀ u w : TangentSpace I x,
      ⟪J.almostComplexStructureAt x u, J.almostComplexStructureAt x w⟫ = ⟪u, w⟫ := by
    simpa only [almostComplexStructureAt_apply] using hJ x
  have hskew := AlmostComplexStructure.inner_apply_left hJ'
  refine ext_inner_ιMulti_two fun u w ↦ ?_
  rw [inner_alternatingFormEquiv_symm_ιMulti, inner_lieMap_left hskew,
    lieMap_two_apply_ιMulti, inner_add_right, inner_alternatingFormEquiv_symm_ιMulti,
    inner_alternatingFormEquiv_symm_ιMulti, Submodule.coe_neg, Pi.neg_apply,
    ContinuousAlternatingMap.neg_apply, ContMDiffSection.realAlternatingDerivation_apply,
    Fin.sum_univ_two]
  have hu0 : Function.update ![u, w] 0 (J.toEndomorphism x (![u, w] 0)) = ![J x u, w] :=
    funext fun i ↦ by fin_cases i <;> rfl
  have hu1 : Function.update ![u, w] 1 (J.toEndomorphism x (![u, w] 1)) = ![u, J x w] :=
    funext fun i ↦ by fin_cases i <;> rfl
  have hJlin (z : TangentSpace I x) :
      (J.almostComplexStructureAt x).toLinearMap z = J x z :=
    almostComplexStructureAt_apply J x z
  rw [hu0, hu1, hJlin u, hJlin w]

section SmoothKahler

variable [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]

/-- **Smoothness of the Kähler two-form** of an orthogonal smooth almost complex structure `J` on a
smooth Riemannian manifold. -/
theorem isSmoothForm_kahlerForm (J : SmoothAlmostComplexStructure I M)
    (hJ : ∀ (x : M) (u w : TangentSpace I x), ⟪J x u, J x w⟫ = ⟪u, w⟫) :
    IsSmoothForm I ∞
      (fun x ↦ alternatingFormEquiv (TangentSpace I x) 2
        (J.almostComplexStructureAt x).kahlerForm) := by
  have : IsManifold I (∞ + 1) M := by simpa using (inferInstance : IsManifold I ∞ M)
  rw [isSmoothForm_iff_forall_contMDiffAt_trivializationAt_apply]
  intro x v
  set e := trivializationAt E (TangentSpace I) x
  let b := Module.finBasis ℝ E
  have hbase : e.baseSet ∈ 𝓝 x :=
    e.open_baseSet.mem_nhds (FiberBundle.mem_baseSet_trivializationAt' x)
  have hexp (y : M) (w : E) : e.symmL ℝ y w =
      ∑ k, b.repr w k • Riemannian.Tensor.chartLocalFrame (I := I) x k y := by
    conv_lhs => rw [← b.sum_repr w]
    rw [map_sum]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    rw [map_smul, Riemannian.Tensor.chartLocalFrame_eq_symmL]
  have hval (y : M) : alternatingFormEquiv (TangentSpace I y) 2
      (J.almostComplexStructureAt y).kahlerForm (e.symmL ℝ y ∘ v) =
      ∑ i, b.repr (v 0) i * ∑ j, b.repr (v 1) j *
        ⟪J y (Riemannian.Tensor.chartLocalFrame (I := I) x i y),
          Riemannian.Tensor.chartLocalFrame (I := I) x j y⟫ := by
    let _ : FiniteDimensional ℝ (TangentSpace I y) :=
      VectorBundle.finiteDimensional ℝ E (TangentSpace I) y
    have hJ' : ∀ u w : TangentSpace I y,
        ⟪J.almostComplexStructureAt y u, J.almostComplexStructureAt y w⟫ = ⟪u, w⟫ := by
      simpa only [almostComplexStructureAt_apply] using hJ y
    have hv : e.symmL ℝ y ∘ v = ![e.symmL ℝ y (v 0), e.symmL ℝ y (v 1)] :=
      funext fun k ↦ by fin_cases k <;> rfl
    have hJy (w : TangentSpace I y) : J y w = J.toEndomorphism y w := rfl
    rw [hv, alternatingFormEquiv_apply, AlmostComplexStructure.inner_kahlerForm_ιMulti hJ',
      almostComplexStructureAt_apply, hJy, hexp y (v 0), hexp y (v 1), map_sum, sum_inner]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [map_smul, real_inner_smul_left, inner_sum]
    congr 1
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [real_inner_smul_right, hJy]
  have hJi (i : Fin (Module.finrank ℝ E)) : ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞
      (fun y ↦ TotalSpace.mk' E (E := fun y : M ↦ TangentSpace I y) y
        (J y (Riemannian.Tensor.chartLocalFrame (I := I) x i y))) e.baseSet :=
    J.toEndomorphism.contMDiff.contMDiffOn.clm_bundle_apply
      (Riemannian.Tensor.contMDiffOn_chartLocalFrame (I := I) (n := ∞) x i)
  have hinner (i j : Fin (Module.finrank ℝ E)) : ContMDiffAt I 𝓘(ℝ) ∞
      (fun y ↦ ⟪J y (Riemannian.Tensor.chartLocalFrame (I := I) x i y),
        Riemannian.Tensor.chartLocalFrame (I := I) x j y⟫) x :=
    ContMDiffAt.inner_bundle (IB := I) (n := ∞) (F := E) (E := fun y : M ↦ TangentSpace I y)
      ((hJi i).contMDiffAt hbase)
      ((Riemannian.Tensor.contMDiffOn_chartLocalFrame (I := I) (n := ∞) x j).contMDiffAt hbase)
  exact (contMDiffAt_finsetSum (t := Finset.univ) fun i _ ↦
    (contMDiffAt_const (c := b.repr (v 0) i)).mul <|
    contMDiffAt_finsetSum (t := Finset.univ) fun j _ ↦
      (contMDiffAt_const (c := b.repr (v 1) j)).mul (hinner i j)).congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun y ↦ by simpa only [Pi.mul_apply] using hval y)

/-- **The smooth Kähler two-form** `ω_x(u, w) = ⟪J_x u, w⟫` associated to an orthogonal smooth
almost complex structure `J` on a smooth Riemannian manifold. -/
def kahlerTwoForm (J : SmoothAlmostComplexStructure I M)
    (hJ : ∀ (x : M) (u w : TangentSpace I x), ⟪J x u, J x w⟫ = ⟪u, w⟫) :
    SmoothForm I M ℝ 2 :=
  ⟨fun x ↦ alternatingFormEquiv (TangentSpace I x) 2 (J.almostComplexStructureAt x).kahlerForm,
    (J.isSmoothForm_kahlerForm hJ).mem_smoothBundleForms⟩

theorem kahlerTwoForm_apply (J : SmoothAlmostComplexStructure I M)
    (hJ : ∀ (x : M) (u w : TangentSpace I x), ⟪J x u, J x w⟫ = ⟪u, w⟫) (x : M) :
    (J.kahlerTwoForm hJ).1 x =
      (letI : FiniteDimensional ℝ (TangentSpace I x) :=
        VectorBundle.finiteDimensional ℝ E (TangentSpace I) x
       alternatingFormEquiv (TangentSpace I x) 2 (J.almostComplexStructureAt x).kahlerForm) :=
  (rfl)

@[simp]
theorem alternatingFormEquiv_symm_kahlerTwoForm (J : SmoothAlmostComplexStructure I M)
    (hJ : ∀ (x : M) (u w : TangentSpace I x), ⟪J x u, J x w⟫ = ⟪u, w⟫) (x : M) :
    (letI : FiniteDimensional ℝ (TangentSpace I x) :=
      VectorBundle.finiteDimensional ℝ E (TangentSpace I) x
     (alternatingFormEquiv (TangentSpace I x) 2).symm ((J.kahlerTwoForm hJ).1 x)) =
      (letI : FiniteDimensional ℝ (TangentSpace I x) :=
        VectorBundle.finiteDimensional ℝ E (TangentSpace I) x
       (J.almostComplexStructureAt x).kahlerForm) := by
  let _ : FiniteDimensional ℝ (TangentSpace I x) :=
    VectorBundle.finiteDimensional ℝ E (TangentSpace I) x
  exact LinearEquiv.symm_apply_apply _ _

@[simp]
theorem kahlerTwoForm_apply_two (J : SmoothAlmostComplexStructure I M)
    (hJ : ∀ (x : M) (u w : TangentSpace I x), ⟪J x u, J x w⟫ = ⟪u, w⟫) (x : M)
    (u w : TangentSpace I x) :
    (J.kahlerTwoForm hJ).1 x ![u, w] = ⟪J x u, w⟫ := by
  let _ : FiniteDimensional ℝ (TangentSpace I x) :=
    VectorBundle.finiteDimensional ℝ E (TangentSpace I) x
  have hJ' : ∀ u' w' : TangentSpace I x,
      ⟪J.almostComplexStructureAt x u', J.almostComplexStructureAt x w'⟫ = ⟪u', w'⟫ := by
    simpa only [almostComplexStructureAt_apply] using hJ x
  rw [kahlerTwoForm_apply, alternatingFormEquiv_apply,
    AlmostComplexStructure.inner_kahlerForm_ιMulti hJ', almostComplexStructureAt_apply]

end SmoothKahler

end SmoothAlmostComplexStructure

end TauCeti

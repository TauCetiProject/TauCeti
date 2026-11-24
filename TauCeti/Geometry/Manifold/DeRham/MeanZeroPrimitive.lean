/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DeRham.Basic
public import TauCeti.Geometry.Manifold.DifferentialForm.Naturality
public import Mathlib.Geometry.Manifold.Algebra.SmoothFunctions
public import Mathlib.Geometry.Manifold.Diffeomorph
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Integral.Average
public import Mathlib.MeasureTheory.Measure.OpenPos
public import TauCeti.Geometry.Manifold.Topology
import TauCeti.Geometry.Manifold.MFDeriv.Constancy
import TauCeti.MeasureTheory.Integral.ConnectedComponent
import TauCeti.MeasureTheory.Integral.ContinuousMap

/-!
# Mean-zero primitives of exact one-forms

Let `M` be a compact smooth manifold and `μ` a finite measure on `M` which charges every nonempty
open set, such as the Liouville measure `|ωⁿ / n!|` of a symplectic form. An exact one-form `α` has
a smooth primitive `f`, with `df = α`, and any two primitives differ by a locally constant
function. Exactly one primitive has mean zero on every connected component `M_j`: if `f` is any
primitive, it is

`(S α)(x) = f(x) - ⨍_{M_j} f dμ`  for `x ∈ M_j`

(`TauCeti.meanZeroPrimitive_apply_eq_sub_setAverage`). This file constructs the selector
`S = TauCeti.meanZeroPrimitive I μ` as a linear map from the exact one-forms to the smooth real
functions on `M`. Its value `S α` is a primitive of `α`
(`TauCeti.mextDeriv_ofFunction_meanZeroPrimitive`) with integral zero over every connected component
(`TauCeti.setIntegral_connectedComponent_meanZeroPrimitive`), and these two properties
characterize it (`TauCeti.eq_meanZeroPrimitive_iff`). It is injective, and on a connected manifold
`S α` is the primitive of `α` with integral zero over `M`.

The selector is natural: if a diffeomorphism `Φ : M → N` carries `μ` to a measure `ν` on `N`, then
the mean-zero primitive of the pullback `Φ^* α` is the composite `(S α) ∘ Φ`
(`TauCeti.meanZeroPrimitive_eq_comp_of_measurePreserving`). For the Liouville measure this applies
to every symplectomorphism.

Normalizing primitives in this way picks out a canonical Hamiltonian for each exact symplectic
vector field, the normalization used to compare Hamiltonian isotopies with paths of zero flux.

## Main definitions

* `TauCeti.meanZeroPrimitive I μ`: the linear map sending an exact one-form to its primitive with
  mean zero on every connected component.

## Main results

* `TauCeti.mextDeriv_ofFunction_meanZeroPrimitive`: `d (S α) = α`.
* `TauCeti.setIntegral_connectedComponent_meanZeroPrimitive`: `S α` has integral zero over every
  connected component.
* `TauCeti.eq_meanZeroPrimitive_iff`: these two properties characterize `S α` among differentiable
  functions.
* `TauCeti.meanZeroPrimitive_apply_eq_sub_setAverage`: `S α = f - ⨍_{M_j} f dμ` on each component
  `M_j`, for any primitive `f`.
* `TauCeti.meanZeroPrimitive_apply_eq_sub_average`: on a connected manifold, `S α = f - ⨍_M f dμ`.
* `TauCeti.meanZeroPrimitive_eq_comp_of_measurePreserving`: naturality under measure-preserving
  diffeomorphisms.

## References

* Dusa McDuff and Dietmar Salamon, *Introduction to Symplectic Topology*, 3rd ed., Oxford
  Graduate Texts in Mathematics 27, Oxford University Press, 2017, Section 10.2 (Hamiltonian
  functions normalized to have mean zero, and the flux homomorphism).
-/

public section

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ContDiff Manifold

namespace TauCeti

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I 2 M] [MeasurableSpace M] {μ : Measure M}

section Normalize

/-! ### Subtracting the componentwise average -/

variable (μ) in
/-- A function minus its average over the connected component of each point. -/
private def normalize (f : M → ℝ) : M → ℝ :=
  fun x ↦ f x - ⨍ y in connectedComponent x, f y ∂μ

omit [IsManifold I 2 M] in
include I in
private theorem isLocallyConstant_setAverage (f : M → ℝ) :
    IsLocallyConstant fun x ↦ ⨍ y in connectedComponent x, f y ∂μ :=
  have := I.locallyPathConnectedSpace_of_chartedSpace M
  isLocallyConstant_setAverage_connectedComponent f

omit [IsManifold I 2 M] in
private theorem contMDiff_normalize {f : M → ℝ} {n : WithTop ℕ∞}
    (hf : ContMDiff I 𝓘(ℝ, ℝ) n f) : ContMDiff I 𝓘(ℝ, ℝ) n (normalize μ f) :=
  hf.sub ((isLocallyConstant_setAverage (I := I) f).contMDiff)

omit [IsManifold I 2 M] in
private theorem mdifferentiable_normalize {f : M → ℝ} (hf : MDifferentiable I 𝓘(ℝ, ℝ) f) :
    MDifferentiable I 𝓘(ℝ, ℝ) (normalize μ f) :=
  hf.sub (((isLocallyConstant_setAverage (I := I) f).contMDiff (n := 1)).mdifferentiable
    one_ne_zero)

omit [IsManifold I 2 M] in
private theorem mextDeriv_normalize (f : M → ℝ) :
    mextDeriv (RoughForm.ofFunction I (normalize μ f)) = mextDeriv (RoughForm.ofFunction I f) := by
  funext x
  refine mextDeriv_ofFunction_eq_of_eventuallyEq_add_const (c := -⨍ y in connectedComponent x,
    f y ∂μ) ?_
  filter_upwards [(IsLocallyConstant.iff_eventually_eq _).mp
    (isLocallyConstant_setAverage (I := I) (μ := μ) f) x] with y hy
  rw [normalize, hy, sub_eq_add_neg]

omit [IsManifold I 2 M] in
private theorem setIntegral_normalize [OpensMeasurableSpace M] [IsFiniteMeasure μ] (f : M → ℝ)
    (x : M) : ∫ y in connectedComponent x, normalize μ f y ∂μ = 0 :=
  setIntegral_connectedComponent_sub_setAverage (measure_ne_top μ _) f

variable [OpensMeasurableSpace M] [CompactSpace M] [IsFiniteMeasure μ]

omit [IsManifold I 2 M] in
private theorem normalize_add {f g : M → ℝ} (hf : Continuous f) (hg : Continuous g) :
    normalize μ (f + g) = normalize μ f + normalize μ g := by
  funext x
  simp only [normalize, Pi.add_apply]
  rw [setAverage_fun_add hf.integrable_of_compactSpace.integrableOn
    hg.integrable_of_compactSpace.integrableOn]
  ring

omit [IsManifold I 2 M] [OpensMeasurableSpace M] [CompactSpace M] [IsFiniteMeasure μ] in
private theorem normalize_smul (c : ℝ) (f : M → ℝ) :
    normalize μ (c • f) = c • normalize μ f := by
  funext x
  simp only [normalize, Pi.smul_apply, smul_eq_mul]
  rw [setAverage_eq, setAverage_eq, integral_const_mul, smul_eq_mul, smul_eq_mul]
  ring

variable [μ.IsOpenPosMeasure]

/-- On a compact manifold with a finite measure charging every nonempty open set, two
differentiable functions with the same differential and the same integral over every connected
component are equal. -/
private theorem eq_of_mextDeriv_eq_of_setIntegral_eq {f g : M → ℝ}
    (hf : MDifferentiable I 𝓘(ℝ, ℝ) f) (hg : MDifferentiable I 𝓘(ℝ, ℝ) g)
    (hfg : mextDeriv (RoughForm.ofFunction I f) = mextDeriv (RoughForm.ofFunction I g))
    (hint : ∀ x, ∫ y in connectedComponent x, f y ∂μ = ∫ y in connectedComponent x, g y ∂μ) :
    f = g := by
  have := I.locallyPathConnectedSpace_of_chartedSpace M
  have hd : ∀ x, mfderiv I 𝓘(ℝ, ℝ) (f - g) x = 0 := fun x ↦ by
    rw [mfderiv_sub (hf x) (hg x)]
    ext v
    have h := congrArg (fun φ ↦ φ x ![v]) hfg
    simp only [mextDeriv_ofFunction_apply] at h
    exact sub_eq_zero.mpr h
  have hlc : IsLocallyConstant (f - g) := (hf.sub hg).isLocallyConstant_of_mfderiv_eq_zero hd
  funext x
  refine sub_eq_zero.mp
    (hlc.apply_eq_zero_of_setIntegral_connectedComponent_eq_zero (measure_ne_top μ _) ?_)
  rw [Pi.sub_def, integral_sub hf.continuous.integrable_of_compactSpace.integrableOn
    hg.continuous.integrable_of_compactSpace.integrableOn, hint x, sub_self]

/-- Two differentiable functions with the same differential have the same normalization. -/
private theorem normalize_eq_normalize {f g : M → ℝ} (hf : MDifferentiable I 𝓘(ℝ, ℝ) f)
    (hg : MDifferentiable I 𝓘(ℝ, ℝ) g)
    (hfg : mextDeriv (RoughForm.ofFunction I f) = mextDeriv (RoughForm.ofFunction I g)) :
    normalize μ f = normalize μ g :=
  eq_of_mextDeriv_eq_of_setIntegral_eq (mdifferentiable_normalize hf) (mdifferentiable_normalize hg)
    (by rw [mextDeriv_normalize, mextDeriv_normalize, hfg])
    fun x ↦ by rw [setIntegral_normalize, setIntegral_normalize]

end Normalize

section Primitive

/-! ### The mean-zero primitive -/

omit [MeasurableSpace M] in
/-- The smooth primitive of an exact one-form chosen by
`TauCeti.exists_contMDiff_mextDeriv_eq_of_mem_exactForms`. -/
private def primitive (α : exactForms I M 1) : M → ℝ :=
  (exists_contMDiff_mextDeriv_eq_of_mem_exactForms I α.property).choose

omit [MeasurableSpace M] in
private theorem contMDiff_primitive (α : exactForms I M 1) :
    ContMDiff I 𝓘(ℝ, ℝ) ∞ (primitive α) :=
  (exists_contMDiff_mextDeriv_eq_of_mem_exactForms I α.property).choose_spec.1

omit [MeasurableSpace M] in
private theorem mextDeriv_primitive (α : exactForms I M 1) :
    mextDeriv (RoughForm.ofFunction I (primitive α)) =
      ((α : SmoothForm I M ℝ 1) : RoughForm I M ℝ 1) :=
  (exists_contMDiff_mextDeriv_eq_of_mem_exactForms I α.property).choose_spec.2

variable [OpensMeasurableSpace M] [CompactSpace M] [IsFiniteMeasure μ] [μ.IsOpenPosMeasure]

/-- The normalized chosen primitive of a sum is the sum of the normalized chosen primitives. -/
private theorem normalize_primitive_add (α β : exactForms I M 1) :
    normalize μ (primitive (α + β)) = normalize μ (primitive α) + normalize μ (primitive β) := by
  have hα := contMDiff_primitive α
  have hβ := contMDiff_primitive β
  rw [← normalize_add hα.continuous hβ.continuous]
  refine normalize_eq_normalize ((contMDiff_primitive _).mdifferentiable (by simp))
    ((hα.add hβ).mdifferentiable (by simp)) ?_
  rw [mextDeriv_ofFunction_add (hα.mdifferentiable (by simp)) (hβ.mdifferentiable (by simp)),
    mextDeriv_primitive, mextDeriv_primitive, mextDeriv_primitive, Submodule.coe_add,
    Submodule.coe_add]

/-- The normalized chosen primitive of a multiple is the multiple of the normalized chosen
primitive. -/
private theorem normalize_primitive_smul (c : ℝ) (α : exactForms I M 1) :
    normalize μ (primitive (c • α)) = c • normalize μ (primitive α) := by
  have hα := contMDiff_primitive α
  rw [← normalize_smul]
  refine normalize_eq_normalize ((contMDiff_primitive _).mdifferentiable (by simp))
    (((contDiff_const_smul c).comp_contMDiff hα).mdifferentiable (by simp)) ?_
  rw [RoughForm.ofFunction_smul, mextDeriv_smul, mextDeriv_primitive, mextDeriv_primitive,
    Submodule.coe_smul, Submodule.coe_smul]

variable (I μ) in
/-- The **mean-zero primitive** of an exact one-form `α` on a compact manifold with a finite
measure `μ` charging every nonempty open set: the unique smooth function `S α` with `d (S α) = α`
and with integral zero over every connected component of `M`. If `f` is any primitive of `α`,
then `S α = f - ⨍_{M_j} f dμ` on each component `M_j`. The selector `S` is linear. -/
def meanZeroPrimitive : exactForms I M 1 →ₗ[ℝ] C^∞⟮I, M; ℝ⟯ where
  toFun α := ⟨normalize μ (primitive α), contMDiff_normalize (contMDiff_primitive α)⟩
  map_add' α β := ContMDiffMap.ext fun x ↦ congrFun (normalize_primitive_add α β) x
  map_smul' c α := ContMDiffMap.ext fun x ↦ congrFun (normalize_primitive_smul c α) x

private theorem coe_meanZeroPrimitive (α : exactForms I M 1) :
    ⇑(meanZeroPrimitive I μ α) = normalize μ (primitive α) :=
  (rfl)

/-- The mean-zero primitive of `α` is a primitive of `α`: `d (S α) = α`. -/
@[simp]
theorem mextDeriv_ofFunction_meanZeroPrimitive (α : exactForms I M 1) :
    mextDeriv (RoughForm.ofFunction I (meanZeroPrimitive I μ α)) =
      ((α : SmoothForm I M ℝ 1) : RoughForm I M ℝ 1) := by
  rw [coe_meanZeroPrimitive, mextDeriv_normalize, mextDeriv_primitive]

/-- The mean-zero primitive of `α` is a primitive of `α`, as an identity of smooth forms. -/
theorem mextDerivₗ_ofFunction_meanZeroPrimitive (α : exactForms I M 1) :
    mextDerivₗ I 0 (SmoothForm.ofFunction (meanZeroPrimitive I μ α)) = α :=
  Subtype.ext <| by
    rw [mextDerivₗ_apply, SmoothForm.coe_ofFunction, mextDeriv_ofFunction_meanZeroPrimitive]

/-- The mean-zero primitive has integral zero over every connected component. -/
@[simp]
theorem setIntegral_connectedComponent_meanZeroPrimitive (α : exactForms I M 1) (x : M) :
    ∫ y in connectedComponent x, meanZeroPrimitive I μ α y ∂μ = 0 :=
  setIntegral_normalize _ x

/-- **The characterization of the mean-zero primitive.** A differentiable function is the
mean-zero primitive of `α` exactly when it is a primitive of `α` with integral zero over every
connected component. -/
theorem eq_meanZeroPrimitive_iff {α : exactForms I M 1} {f : M → ℝ}
    (hf : MDifferentiable I 𝓘(ℝ, ℝ) f) :
    f = meanZeroPrimitive I μ α ↔ mextDeriv (RoughForm.ofFunction I f) =
      ((α : SmoothForm I M ℝ 1) : RoughForm I M ℝ 1) ∧
      ∀ x, ∫ y in connectedComponent x, f y ∂μ = 0 := by
  refine ⟨?_, fun ⟨hdf, hint⟩ ↦ eq_of_mextDeriv_eq_of_setIntegral_eq hf
    ((meanZeroPrimitive I μ α).contMDiff.mdifferentiable (by simp))
    (by rw [hdf, mextDeriv_ofFunction_meanZeroPrimitive]) fun x ↦ by
      rw [hint, setIntegral_connectedComponent_meanZeroPrimitive]⟩
  rintro rfl
  exact ⟨mextDeriv_ofFunction_meanZeroPrimitive α,
    setIntegral_connectedComponent_meanZeroPrimitive α⟩

/-- **The mean-zero primitive from any primitive.** If `f` is a differentiable primitive of `α`,
then at a point of the connected component `M_j` the mean-zero primitive of `α` is
`f - ⨍_{M_j} f dμ`. -/
theorem meanZeroPrimitive_apply_eq_sub_setAverage {α : exactForms I M 1} {f : M → ℝ}
    (hf : MDifferentiable I 𝓘(ℝ, ℝ) f)
    (hdf : mextDeriv (RoughForm.ofFunction I f) = ((α : SmoothForm I M ℝ 1) : RoughForm I M ℝ 1))
    (x : M) :
    meanZeroPrimitive I μ α x = f x - ⨍ y in connectedComponent x, f y ∂μ := by
  rw [coe_meanZeroPrimitive, normalize_eq_normalize
    ((contMDiff_primitive α).mdifferentiable (by simp)) hf (by rw [hdf, mextDeriv_primitive])]
  rfl

/-- On a connected manifold, the mean-zero primitive of `α` is `f - ⨍_M f dμ` for any
differentiable primitive `f` of `α`. -/
theorem meanZeroPrimitive_apply_eq_sub_average [PreconnectedSpace M] {α : exactForms I M 1}
    {f : M → ℝ} (hf : MDifferentiable I 𝓘(ℝ, ℝ) f)
    (hdf : mextDeriv (RoughForm.ofFunction I f) = ((α : SmoothForm I M ℝ 1) : RoughForm I M ℝ 1))
    (x : M) :
    meanZeroPrimitive I μ α x = f x - ⨍ y, f y ∂μ := by
  rw [meanZeroPrimitive_apply_eq_sub_setAverage hf hdf,
    PreconnectedSpace.connectedComponent_eq_univ, Measure.restrict_univ]

/-- On a connected manifold, the mean-zero primitive has integral zero. -/
@[simp]
theorem integral_meanZeroPrimitive [PreconnectedSpace M] (α : exactForms I M 1) :
    ∫ y, meanZeroPrimitive I μ α y ∂μ = 0 := by
  have h := setIntegral_connectedComponent_meanZeroPrimitive (μ := μ) α
  by_cases hM : Nonempty M
  · obtain ⟨x⟩ := hM
    simpa [PreconnectedSpace.connectedComponent_eq_univ] using h x
  · have := not_nonempty_iff.mp hM
    exact integral_eq_zero_of_ae (Eventually.of_forall isEmptyElim)

/-- The mean-zero primitive determines the exact form: `S` is injective. -/
theorem meanZeroPrimitive_injective : Function.Injective (meanZeroPrimitive I μ) := by
  intro α β h
  refine Subtype.ext <| Subtype.ext ?_
  rw [← mextDeriv_ofFunction_meanZeroPrimitive (μ := μ) α,
    ← mextDeriv_ofFunction_meanZeroPrimitive (μ := μ) β, h]

end Primitive

section Naturality

/-! ### Naturality -/

variable {E' H' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
  {J : ModelWithCorners ℝ E' H'} {N : Type*} [TopologicalSpace N] [ChartedSpace H' N]
  [IsManifold J 2 N] [MeasurableSpace N] {ν : Measure N}
  [BorelSpace M] [CompactSpace M] [IsFiniteMeasure μ] [μ.IsOpenPosMeasure]
  [BorelSpace N] [CompactSpace N] [IsFiniteMeasure ν] [ν.IsOpenPosMeasure]

/-- **Naturality of the mean-zero primitive.** Let `Φ : M → N` be a diffeomorphism carrying the
measure `μ` to `ν`. If the exact form `β` on `M` is the pullback `Φ^* α` of an exact form `α` on
`N`, then the mean-zero primitive of `β` is the mean-zero primitive of `α` composed with `Φ`. -/
theorem meanZeroPrimitive_eq_comp_of_measurePreserving (Φ : M ≃ₘ⟮I, J⟯ N)
    (hΦ : MeasurePreserving Φ μ ν) {α : exactForms J N 1} {β : exactForms I M 1}
    (hβ : ((β : SmoothForm I M ℝ 1) : RoughForm I M ℝ 1) =
      mpullback I J Φ ((α : SmoothForm J N ℝ 1) : RoughForm J N ℝ 1)) :
    ⇑(meanZeroPrimitive I μ β) = meanZeroPrimitive J ν α ∘ Φ := by
  have hS := (meanZeroPrimitive J ν α).contMDiff.mdifferentiable (n := ∞) (by simp)
  have hΦd : MDifferentiable I J Φ := Φ.contMDiff.mdifferentiable (by simp)
  refine ((eq_meanZeroPrimitive_iff (hS.comp hΦd)).mpr ⟨?_, fun x ↦ ?_⟩).symm
  · rw [hβ, ← mpullback_mextDeriv_ofFunction hΦd hS, mextDeriv_ofFunction_meanZeroPrimitive]
  · have hC : Φ '' connectedComponent x = connectedComponent (Φ x) := by
      simpa [connectedComponentIn_univ, image_univ_of_surjective Φ.surjective] using
        Φ.toHomeomorph.image_connectedComponentIn (mem_univ x)
    simp only [Function.comp_apply]
    rw [← hΦ.setIntegral_image_emb Φ.toHomeomorph.measurableEmbedding, hC,
      setIntegral_connectedComponent_meanZeroPrimitive]

end Naturality

end TauCeti

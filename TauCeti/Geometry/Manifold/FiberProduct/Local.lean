/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.FiberProduct.Equation
public import TauCeti.Geometry.Manifold.RegularValue.Level
public import TauCeti.Geometry.Manifold.SmoothEmbedding.Basic
import TauCeti.Geometry.Manifold.Immersion.Basic
import TauCeti.Geometry.Manifold.Immersion.LocalDiffeomorph
import TauCeti.Geometry.Manifold.LocalDiffeomorph.OpenSubset
import TauCeti.Geometry.Manifold.PullbackGroupoid

/-!
# Transverse fibre products in a target-coordinate patch

For smooth maps `f : X → N` and `g : Y → N` transverse along their fibre product, a target
coordinate patch `φ` gives an embedded manifold on the actual subtype
`{p : X × Y // f p.1 = g p.2 ∧ f p.1 ∈ φ.source}`. Its topology is the subspace topology and
its dimension is `dim X + dim Y - dim N`. Its tangent image consists exactly of pairs of
vectors with equal images under `df` and `dg`.

`PartialDiffeomorph.exists_isManifold_localFiberProduct_isSmoothEmbedding` constructs this
structure by applying the regular-level theorem to the coordinate-difference equation on the
open subset where both maps take values in `φ.source`. This local construction allows
fibre-product charts to be glued over different target-coordinate patches. No Hausdorff or
countability hypotheses are used, and the local fibre product may be empty.

The smooth universal property is supplied by the returned embedding and
`Manifold.IsSmoothEmbedding.contMDiff_iff_comp`: a map to this subtype is smooth exactly when
its composite with the inclusion into `X × Y` is smooth.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Springer (2013),
  Theorem 6.30 (transverse preimages), applied to the diagonal in `N × N`.
-/

public section

open Function Set Module TauCeti
open scoped Manifold ContDiff Topology

namespace PartialDiffeomorph

variable {EX HX X EY HY Y EN HN N : Type*}
  [NormedAddCommGroup EX] [NormedSpace ℝ EX] [TopologicalSpace HX]
  [NormedAddCommGroup EY] [NormedSpace ℝ EY] [TopologicalSpace HY]
  [NormedAddCommGroup EN] [NormedSpace ℝ EN] [TopologicalSpace HN]
  {IX : ModelWithCorners ℝ EX HX} {IY : ModelWithCorners ℝ EY HY}
  {IN : ModelWithCorners ℝ EN HN}
  [TopologicalSpace X] [ChartedSpace HX X]
  [TopologicalSpace Y] [ChartedSpace HY Y]
  [TopologicalSpace N] [ChartedSpace HN N]
  {n : ℕ∞ω} (φ : PartialDiffeomorph IN 𝓘(ℝ, EN) N EN n)
  {f : X → N} {g : Y → N}

private def fiberProductDomain (hf : Continuous f) (hg : Continuous g) :
    TopologicalSpace.Opens (X × Y) :=
  ⟨(f ⁻¹' φ.source) ×ˢ (g ⁻¹' φ.source),
    (φ.open_source.preimage hf).prod (φ.open_source.preimage hg)⟩

private def fiberProductZeroHomeomorph (hf : Continuous f) (hg : Continuous g) :
    {p : φ.fiberProductDomain hf hg // φ.fiberProductEquation f g p.1 = 0} ≃ₜ
      {p : X × Y // f p.1 = g p.2 ∧ f p.1 ∈ φ.source} where
  toFun p := ⟨p.1.1, (φ.fiberProductEquation_eq_zero_iff p.1.2.1 p.1.2.2).1 p.2, p.1.2.1⟩
  invFun p := ⟨⟨p.1, p.2.2, by simpa only [mem_preimage, ← p.2.1] using p.2.2⟩,
    (φ.fiberProductEquation_eq_zero_iff p.2.2 (p.2.1 ▸ p.2.2)).2 p.2.1⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := (continuous_subtype_val.subtype_mk _).subtype_mk _

private theorem coe_fiberProductZeroHomeomorph_symm (hf : Continuous f) (hg : Continuous g)
    (p : {p : X × Y // f p.1 = g p.2 ∧ f p.1 ∈ φ.source}) :
    ((φ.fiberProductZeroHomeomorph hf hg).symm p).1.1 = p.1 := (rfl)

variable (hn : 1 ≤ n) (hf : ContMDiff IX IN n f) (hg : ContMDiff IY IN n g)

private theorem contMDiff_fiberProductDomain_equation :
    ContMDiff (IX.prod IY) 𝓘(ℝ, EN) n
      (fun p : φ.fiberProductDomain hf.continuous hg.continuous ↦
        φ.fiberProductEquation f g p.1) := by
  exact (φ.contMDiffOn_fiberProductEquation hf hg).comp_contMDiff
    contMDiff_subtype_val fun p ↦ p.2

include hn in
private theorem isRegularValue_fiberProductDomain_equation
    (htrans : ∀ p : X × Y, f p.1 = g p.2 → f p.1 ∈ φ.source →
      (mfderiv IX IN f p.1).range ⊔
        (((tangentSpaceCast IN (g p.2) (f p.1)).toContinuousLinearMap).comp
          (mfderiv IY IN g p.2)).range = ⊤) :
    IsRegularValue (IX.prod IY) 𝓘(ℝ, EN)
      (fun p : φ.fiberProductDomain hf.continuous hg.continuous ↦
        φ.fiberProductEquation f g p.1) 0 := by
  rw [isRegularValue_iff]
  intro p hp
  have hfg := (φ.fiberProductEquation_eq_zero_iff p.2.1 p.2.2).1 hp
  have hn0 : n ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one hn)
  have hreg := (φ.isRegularPoint_fiberProductEquation_iff hn0
    ((hf p.1.1).mdifferentiableAt hn0) ((hg p.1.2).mdifferentiableAt hn0)
    hfg p.2.1).2 (htrans p.1 hfg p.2.1)
  have hD := (isLocalDiffeomorph_subtype_val
    (I := IX.prod IY) (n := n) p).isInvertible_mfderiv hn0
  have hEq : (fun p : φ.fiberProductDomain hf.continuous hg.continuous ↦
      φ.fiberProductEquation f g p.1) = φ.fiberProductEquation f g ∘ Subtype.val := rfl
  rw [isRegularPoint_iff, hEq, mfderiv_comp _
    ((φ.contMDiffOn_fiberProductEquation hf hg).contMDiffAt
      ((φ.fiberProductDomain hf.continuous hg.continuous).isOpen.mem_nhds p.2)
      |>.mdifferentiableAt hn0) (contMDiff_subtype_val.mdifferentiableAt hn0)]
  exact (isRegularPoint_iff.1 hreg).comp hD.surjective

variable [IsManifold IX n X] [IsManifold IY n Y] [IX.Boundaryless] [IY.Boundaryless]
  [FiniteDimensional ℝ EX] [FiniteDimensional ℝ EY] [FiniteDimensional ℝ EN]

include hn hf hg in
/-- **A transverse fibre product in a target-coordinate patch is an embedded submanifold.**
The topology is the inherited subspace topology, the model dimension is
`dim X + dim Y - dim N`, and the tangent image is the space of pairs with equal derivative
images. Transversality is required only at equal-value pairs in the chosen patch.

The returned smooth embedding also gives the smooth universal property through
`Manifold.IsSmoothEmbedding.contMDiff_iff_comp`, without a separate continuity hypothesis. -/
theorem exists_isManifold_localFiberProduct_isSmoothEmbedding
    (htrans : ∀ p : X × Y, f p.1 = g p.2 → f p.1 ∈ φ.source →
      (mfderiv IX IN f p.1).range ⊔
        (((tangentSpaceCast IN (g p.2) (f p.1)).toContinuousLinearMap).comp
          (mfderiv IY IN g p.2)).range = ⊤) :
    ∃ cs : ChartedSpace (Fin (finrank ℝ EX + finrank ℝ EY - finrank ℝ EN) → ℝ)
        {p : X × Y // f p.1 = g p.2 ∧ f p.1 ∈ φ.source},
      letI := cs
      IsManifold 𝓘(ℝ, Fin (finrank ℝ EX + finrank ℝ EY - finrank ℝ EN) → ℝ) n
        {p : X × Y // f p.1 = g p.2 ∧ f p.1 ∈ φ.source} ∧
      Manifold.IsSmoothEmbedding
        𝓘(ℝ, Fin (finrank ℝ EX + finrank ℝ EY - finrank ℝ EN) → ℝ) (IX.prod IY) n
        (Subtype.val : {p : X × Y // f p.1 = g p.2 ∧ f p.1 ∈ φ.source} → X × Y) ∧
      ∀ (p : {p : X × Y // f p.1 = g p.2 ∧ f p.1 ∈ φ.source})
        (v : TangentSpace (IX.prod IY) p.1),
        v ∈ (mfderiv
          𝓘(ℝ, Fin (finrank ℝ EX + finrank ℝ EY - finrank ℝ EN) → ℝ) (IX.prod IY)
          (Subtype.val : {p : X × Y // f p.1 = g p.2 ∧ f p.1 ∈ φ.source} → X × Y) p).range ↔
        mfderiv IX IN f p.1.1 v.1 =
          tangentSpaceCast IN (g p.1.2) (f p.1.1) (mfderiv IY IN g p.1.2 v.2) := by
  let d := finrank ℝ EX + finrank ℝ EY - finrank ℝ EN
  let U := φ.fiberProductDomain hf.continuous hg.continuous
  let q : U → EN := fun p ↦ φ.fiberProductEquation f g p.1
  have hq : ContMDiff (IX.prod IY) 𝓘(ℝ, EN) n q :=
    φ.contMDiff_fiberProductDomain_equation hf hg
  have hreg : IsRegularValue (IX.prod IY) 𝓘(ℝ, EN) q 0 :=
    φ.isRegularValue_fiberProductDomain_equation hn hf hg htrans
  have hd : finrank ℝ (EX × EY) - finrank ℝ EN = d := by rw [finrank_prod]
  let := regularLevelChartedSpace (fun p _ ↦ (hq p).of_le hn) hreg hd
  have := isManifold_regularLevel hn (fun p _ ↦ hq p) hreg hd
  let e := φ.fiberProductZeroHomeomorph hf.continuous hg.continuous
  let := e.symm.pullbackChartedSpace (H := Fin d → ℝ)
  have := e.symm.pullback_isManifold 𝓘(ℝ, Fin d → ℝ) n
  have hinc := isSmoothEmbedding_coe_regularLevel hn (fun p _ ↦ hq p) hreg hd
  have hi : Manifold.IsImmersion 𝓘(ℝ, Fin d → ℝ) (IX.prod IY) n
      (Subtype.val : {p : X × Y // f p.1 = g p.2 ∧ f p.1 ∈ φ.source} → X × Y) := by
    have hcomp : (Subtype.val : {p : X × Y // f p.1 = g p.2 ∧ f p.1 ∈ φ.source} → X × Y) =
        (Subtype.val : U → X × Y) ∘ Subtype.val ∘
          e.symm.pullbackDiffeomorph 𝓘(ℝ, Fin d → ℝ) n := by
      funext p
      rw [comp_apply, comp_apply, Homeomorph.coe_pullbackDiffeomorph]
      exact (φ.coe_fiberProductZeroHomeomorph_symm hf.continuous hg.continuous p).symm
    rw [hcomp]
    exact isImmersion_isLocalDiffeomorphAt_comp (fun _ ↦ isLocalDiffeomorph_subtype_val _)
      (isImmersion_comp_diffeomorph _ hinc.isImmersion)
  refine ⟨inferInstance, inferInstance, ⟨hi, Topology.IsEmbedding.subtypeVal⟩, ?_⟩
  intro p v
  have hn0 : n ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one hn)
  have hr := (φ.isRegularPoint_fiberProductEquation_iff hn0
    ((hf p.1.1).mdifferentiableAt hn0) ((hg p.1.2).mdifferentiableAt hn0)
    p.2.1 p.2.2).2 (htrans p.1 p.2.1 p.2.2)
  have hdim := hr.finrank_ker_mfderiv_add_finrank
  rw [finrank_prod] at hdim
  have heq := hr.range_mfderiv_eq_ker_mfderiv
    (.of_forall fun z ↦ (φ.fiberProductEquation_eq_zero_iff z.2.2
      (z.2.1 ▸ z.2.2)).2 z.2.1) ((hi.isImmersionAt p).mfderiv_injective hn0)
    (by rw [finrank_fin_fun, finrank_prod]; omega)
  rw [heq, ← TauCeti.ker_mvfderiv]
  exact φ.mem_ker_mvfderiv_fiberProductEquation_iff hn0
    ((hf p.1.1).mdifferentiableAt hn0) ((hg p.1.2).mdifferentiableAt hn0) p.2.1 p.2.2 v

end PartialDiffeomorph

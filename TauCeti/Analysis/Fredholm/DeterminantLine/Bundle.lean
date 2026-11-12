/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Module.ModuleTopology
public import Mathlib.Topology.VectorBundle.Basic
public import TauCeti.Analysis.Fredholm.DeterminantLine.Chart
public import TauCeti.Topology.VectorBundle.Orientation.Cover.Transport
import TauCeti.Analysis.Fredholm.Stabilization

/-!
# The determinant line bundle of Fredholm operators

Let `E` and `F` be Banach spaces over a complete nontrivially normed field `𝕜`. The determinant
lines `det (ker T) ⊗ (det (F ⧸ range T))^*` of the Fredholm operators `T : E →L[𝕜] F`
(`TauCeti.FredholmDetLine`) form a line bundle over the space of Fredholm operators, with the
topology of the operator norm. This file constructs it as a vector bundle with model fibre `𝕜`,
although kernels and cokernels jump.

The trivializations are the kernel charts of `TauCeti.Analysis.Fredholm.DeterminantLine.Chart`.
Near a Fredholm operator `T₀` there are a finite-dimensional stabilizer `S ≤ F` and a kernel
coordinate `q` such that `(T.coprod S.subtypeL).prod q` is invertible for all `T` in a
neighbourhood `U` of `T₀`
(`ContinuousLinearMap.IsFredholm.exists_stabilization_kernel_coordinates`), and then
`ContinuousLinearMap.detLineChartEquiv` identifies the determinant line of every `T ∈ U` with one
fixed line, hence with `𝕜`. Two such charts differ over the intersection of their
domains by multiplication by a continuous nowhere-vanishing function
(`ContinuousLinearMap.exists_continuous_detLineChartEquiv_symm_eq_smul`), so Mathlib's
`VectorPrebundle` gives the total space a topology for which these charts are trivializations.
Each fibre carries its module topology, for which every linear isomorphism with `𝕜` is a
homeomorphism.

Over `ℝ` the bundle has an orientation double cover, and its projection is a covering map
(`TauCeti.FredholmDetLine.isCoveringMap_proj`). Orientations of determinant lines are therefore
transported along continuous paths of Fredholm operators by lifting to this cover
(`TauCeti.VectorBundleOrientationCover.orientationTransport`), canonically and without any choice
of connection. This transport is how orientations of moduli spaces in Morse and Floer theory,
which are orientations of the determinant lines of their linearized operators, are compared along
paths of operators. A family of vectors is continuous in the total space exactly when it is
continuous when read in kernel charts, for every kernel chart and not only those chosen to build
the bundle (`TauCeti.FredholmDetLine.continuous_detLineChartEquiv`,
`TauCeti.FredholmDetLine.continuous_of_continuous_detLineChartEquiv`).

## Main definitions

* `TauCeti.FredholmDetLine`: the determinant line of a Fredholm operator, the fibre of the bundle.
* `TauCeti.FredholmDetLine.vectorPrebundle`: the kernel-chart pretrivializations.
* The instances `TopologicalSpace (TotalSpace 𝕜 (FredholmDetLine 𝕜 E F))`,
  `FiberBundle 𝕜 (FredholmDetLine 𝕜 E F)` and `VectorBundle 𝕜 𝕜 (FredholmDetLine 𝕜 E F)`.

## Main results

* `TauCeti.FredholmDetLine.continuous_detLineChartEquiv`: every kernel chart is continuous on
  continuous families in the total space.
* `TauCeti.FredholmDetLine.continuous_of_continuous_detLineChartEquiv`: conversely, a family is
  continuous in the total space if it is continuous when read in a kernel chart.
* `TauCeti.FredholmDetLine.isCoveringMap_proj`: over `ℝ`, the orientation double cover of the
  determinant line bundle is a covering map.

## References

* D. McDuff, D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  AMS Colloquium Publications 52, 2012, Section A.2 (determinant line bundles).
* A. Zinger, *The determinant line bundle for Fredholm operators: construction, properties, and
  classification*, Math. Scand. 118 (2016), 203–268, arXiv:1304.6368.
-/

public section

noncomputable section

open Bundle Module Set TensorProduct Topology

namespace TauCeti

variable (𝕜 E F : Type*) [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- The determinant line `det (ker T) ⊗ (det (F ⧸ range T))^*` of a Fredholm operator `T`
(`LinearMap.detLine`), the fibre over `T` of the determinant line bundle on the space of Fredholm
operators. It is a line (`ContinuousLinearMap.IsFredholm.finrank_detLine`) and carries its module
topology. The body is exposed so that elements of `LinearMap.detLine` can be used as elements of
the fibre. -/
@[expose] def FredholmDetLine (T : {T : E →L[𝕜] F // T.IsFredholm}) : Type _ :=
  ((T : E →L[𝕜] F) : E →ₗ[𝕜] F).detLine

namespace FredholmDetLine

variable {𝕜 E F}

instance (T : {T : E →L[𝕜] F // T.IsFredholm}) : AddCommGroup (FredholmDetLine 𝕜 E F T) :=
  inferInstanceAs (AddCommGroup (LinearMap.detLine _))

instance (T : {T : E →L[𝕜] F // T.IsFredholm}) : Module 𝕜 (FredholmDetLine 𝕜 E F T) :=
  inferInstanceAs (Module 𝕜 (LinearMap.detLine _))

/-- The fibres of the determinant line bundle carry their module topology. -/
instance (T : {T : E →L[𝕜] F // T.IsFredholm}) : TopologicalSpace (FredholmDetLine 𝕜 E F T) :=
  moduleTopology 𝕜 _

instance (T : {T : E →L[𝕜] F // T.IsFredholm}) : IsModuleTopology 𝕜 (FredholmDetLine 𝕜 E F T) :=
  ⟨rfl⟩

end FredholmDetLine

end TauCeti

end

end

/-! ### Kernel charts over open sets of Fredholm operators

The charts below are internal to this file: they are declared outside the public section, so
they are private to the module.
-/

noncomputable section

open Bundle Module Set TensorProduct Topology

namespace TauCeti.FredholmDetLine

universe u𝕜 uE uF

variable {𝕜 : Type u𝕜} {E : Type uE} {F : Type uF} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F]

variable (𝕜 E F) in
/-- A kernel chart of the determinant lines over an open set `U` of Fredholm operators: a
finite-dimensional stabilizer `D : Λ →L[𝕜] F` and a coordinate `q` on `E × Λ` with values in a
finite-dimensional space `G`, such that `(T.coprod D).prod q` is invertible for every `T ∈ U`,
together with an identification of the model line `det G ⊗ (det Λ)^*` with `𝕜`. The spaces `Λ`
and `G` are carried with their norms, so that the module structures on them are the ones of the
transition theorem `ContinuousLinearMap.exists_continuous_detLineChartEquiv_symm_eq_smul`. -/
structure Chart where
  /-- The space of stabilizing directions. -/
  Λ : Type uF
  [normedAddCommGroup_Λ : NormedAddCommGroup Λ]
  [normedSpace_Λ : NormedSpace 𝕜 Λ]
  [finiteDimensional_Λ : FiniteDimensional 𝕜 Λ]
  /-- The model of the stabilized kernels. -/
  G : Type (max uE uF)
  [normedAddCommGroup_G : NormedAddCommGroup G]
  [normedSpace_G : NormedSpace 𝕜 G]
  [finiteDimensional_G : FiniteDimensional 𝕜 G]
  /-- The stabilizer. -/
  D : Λ →L[𝕜] F
  /-- The kernel coordinate. -/
  q : E × Λ →L[𝕜] G
  /-- The domain of the chart. -/
  U : Set {T : E →L[𝕜] F // T.IsFredholm}
  isOpen_U : IsOpen U
  isInvertible : ∀ T ∈ U, (((T : E →L[𝕜] F).coprod D).prod q).IsInvertible
  /-- The identification of the model line with `𝕜`. -/
  line : TauCeti.detLine 𝕜 G ⊗[𝕜] Dual 𝕜 (TauCeti.detLine 𝕜 Λ) ≃ₗ[𝕜] 𝕜

attribute [instance] Chart.normedAddCommGroup_Λ Chart.normedSpace_Λ Chart.finiteDimensional_Λ
  Chart.normedAddCommGroup_G Chart.normedSpace_G Chart.finiteDimensional_G

namespace Chart

variable (c : Chart 𝕜 E F)

/-- The chart identification of the determinant line of an operator of `c.U` with `𝕜`. -/
def equiv {T : {T : E →L[𝕜] F // T.IsFredholm}} (hT : T ∈ c.U) :
    FredholmDetLine 𝕜 E F T ≃ₗ[𝕜] 𝕜 :=
  (ContinuousLinearMap.detLineChartEquiv (T : E →L[𝕜] F) c.D c.q (c.isInvertible T hT)).trans
    c.line

open Classical in
/-- The chart read on all fibres, zero outside `c.U`. -/
def coord (T : {T : E →L[𝕜] F // T.IsFredholm}) : FredholmDetLine 𝕜 E F T →ₗ[𝕜] 𝕜 :=
  if hT : T ∈ c.U then (c.equiv hT).toLinearMap else 0

open Classical in
/-- The inverse of the chart on all fibres, zero outside `c.U`. -/
def coordSymm (T : {T : E →L[𝕜] F // T.IsFredholm}) : 𝕜 →ₗ[𝕜] FredholmDetLine 𝕜 E F T :=
  if hT : T ∈ c.U then (c.equiv hT).symm.toLinearMap else 0

theorem coord_of_mem {T : {T : E →L[𝕜] F // T.IsFredholm}} (hT : T ∈ c.U) :
    c.coord T = (c.equiv hT).toLinearMap :=
  dite_eq_left hT

theorem coordSymm_of_mem {T : {T : E →L[𝕜] F // T.IsFredholm}} (hT : T ∈ c.U) :
    c.coordSymm T = (c.equiv hT).symm.toLinearMap :=
  dite_eq_left hT

/-- The transition from the chart `c` to the chart `c'` at an operator in both domains. -/
theorem coord_apply_of_mem {T : {T : E →L[𝕜] F // T.IsFredholm}} (hT : T ∈ c.U)
    (y : FredholmDetLine 𝕜 E F T) :
    c.coord T y = c.line (ContinuousLinearMap.detLineChartEquiv (T : E →L[𝕜] F) c.D c.q
      (c.isInvertible T hT) y) := by
  rw [c.coord_of_mem hT]
  rfl

theorem coord_coordSymm_of_mem {c c' : Chart 𝕜 E F} {T : {T : E →L[𝕜] F // T.IsFredholm}}
    (hT : T ∈ c.U) (hT' : T ∈ c'.U) (v : 𝕜) :
    c'.coord T (c.coordSymm T v) = c'.line (ContinuousLinearMap.detLineChartEquiv
      (T : E →L[𝕜] F) c'.D c'.q (c'.isInvertible T hT')
        ((ContinuousLinearMap.detLineChartEquiv (T : E →L[𝕜] F) c.D c.q
          (c.isInvertible T hT)).symm (c.line.symm v))) := by
  rw [c.coordSymm_of_mem hT, c'.coord_of_mem hT']
  rfl

/-- The pretrivialization of the determinant lines over the domain of a kernel chart. -/
def pretrivialization : Pretrivialization 𝕜 (π 𝕜 (FredholmDetLine 𝕜 E F)) where
  toFun p := (p.1, c.coord p.1 p.2)
  invFun p := ⟨p.1, c.coordSymm p.1 p.2⟩
  source := π 𝕜 (FredholmDetLine 𝕜 E F) ⁻¹' c.U
  target := c.U ×ˢ univ
  map_source' _ h := ⟨h, mem_univ _⟩
  map_target' _ h := h.1
  left_inv' := by
    rintro ⟨T, y⟩ (hT : T ∈ c.U)
    simp [c.coord_of_mem hT, c.coordSymm_of_mem hT]
  right_inv' := by
    rintro ⟨T, v⟩ ⟨hT, -⟩
    simp [c.coord_of_mem hT, c.coordSymm_of_mem hT]
  open_target := c.isOpen_U.prod isOpen_univ
  baseSet := c.U
  open_baseSet := c.isOpen_U
  source_eq := rfl
  target_eq := rfl
  proj_toFun _ _ := rfl

theorem pretrivialization_apply (p : TotalSpace 𝕜 (FredholmDetLine 𝕜 E F)) :
    c.pretrivialization p = (p.1, c.coord p.1 p.2) :=
  (rfl)

theorem baseSet_pretrivialization : c.pretrivialization.baseSet = c.U :=
  (rfl)

instance isLinear_pretrivialization : c.pretrivialization.IsLinear 𝕜 where
  linear _ _ := (c.coord _).isLinear

theorem pretrivialization_symm {T : {T : E →L[𝕜] F // T.IsFredholm}} (hT : T ∈ c.U) (v : 𝕜) :
    c.pretrivialization.symm T v = c.coordSymm T v := by
  apply (c.equiv hT).injective
  have := congrArg Prod.snd (c.pretrivialization.apply_mk_symm hT v)
  simp only [pretrivialization_apply, c.coord_of_mem hT, LinearEquiv.coe_coe] at this
  rw [this, c.coordSymm_of_mem hT, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]

/-- The coordinate changes between two kernel charts are continuous. -/
theorem exists_coordChange [CompleteSpace 𝕜] [CompleteSpace E] (c c' : Chart 𝕜 E F) :
    ∃ f : {T : E →L[𝕜] F // T.IsFredholm} → 𝕜 →L[𝕜] 𝕜,
      ContinuousOn f (c.pretrivialization.baseSet ∩ c'.pretrivialization.baseSet) ∧
        ∀ b ∈ c.pretrivialization.baseSet ∩ c'.pretrivialization.baseSet, ∀ v : 𝕜,
          f b v = (c'.pretrivialization ⟨b, c.pretrivialization.symm b v⟩).2 := by
  let g (b : {T : E →L[𝕜] F // T.IsFredholm}) : 𝕜 := c'.coord b (c.coordSymm b 1)
  refine ⟨fun b ↦ g b • ContinuousLinearMap.id 𝕜 𝕜, ?_, fun b hb v ↦ ?_⟩
  · refine (show ContinuousOn g _ from ?_).smul continuousOn_const
    rw [baseSet_pretrivialization, baseSet_pretrivialization,
      continuousOn_iff_continuous_domRestrict]
    rcases isEmpty_or_nonempty ↥(c.U ∩ c'.U) with hW | hW
    · exact continuous_iff_continuousAt.2 fun w ↦ isEmptyElim w
    obtain ⟨w₀⟩ := hW
    -- Over the overlap the transition is a continuous multiple of its value at `w₀`.
    obtain ⟨k, hk, -, hkv⟩ := ContinuousLinearMap.exists_continuous_detLineChartEquiv_symm_eq_smul
      (T := fun w : ↥(c.U ∩ c'.U) ↦ ((w : {T : E →L[𝕜] F // T.IsFredholm}) : E →L[𝕜] F))
      (continuous_subtype_val.comp continuous_subtype_val)
      (fun w ↦ c'.isInvertible w w.2.2) (fun w ↦ c.isInvertible w w.2.1) w₀
    have hg (w : ↥(c.U ∩ c'.U)) : g w = k w * g w₀ := by
      simp only [g]
      rw [coord_coordSymm_of_mem w.2.1 w.2.2, coord_coordSymm_of_mem w₀.2.1 w₀.2.2,
        hkv w (c.line.symm 1)]
      exact c'.line.map_smul (k w) _
    exact (hk.mul continuous_const).congr fun w ↦ (hg w).symm
  · rw [pretrivialization_apply, c.pretrivialization_symm hb.1]
    have hv : v = v • (1 : 𝕜) := (mul_one v).symm
    conv_rhs => rw [hv, map_smul, map_smul]
    simp [g, mul_comm]

/-- A kernel chart is a homeomorphism on each fibre over its domain, the fibre carrying its
module topology. -/
theorem isInducing_coord {T : {T : E →L[𝕜] F // T.IsFredholm}} (hT : T ∈ c.U) :
    IsInducing (c.coord T) := by
  have := IsModuleTopology.toContinuousAdd 𝕜 (FredholmDetLine 𝕜 E F T)
  let h : FredholmDetLine 𝕜 E F T ≃ₜ 𝕜 :=
    { toEquiv := (c.equiv hT).toEquiv
      continuous_toFun := IsModuleTopology.continuous_of_linearMap (c.equiv hT).toLinearMap
      continuous_invFun :=
        IsModuleTopology.continuous_of_linearMap (c.equiv hT).symm.toLinearMap }
  rw [c.coord_of_mem hT]
  exact h.isInducing

end Chart

variable [CompleteSpace 𝕜] [CompleteSpace E] [CompleteSpace F]

/-- Every Fredholm operator lies in the domain of a kernel chart. -/
theorem exists_chart (T₀ : {T : E →L[𝕜] F // T.IsFredholm}) :
    ∃ c : Chart 𝕜 E F, T₀ ∈ c.U := by
  obtain ⟨S, -, -, hS, q, U, hU, hT₀, hinv⟩ :=
    T₀.2.exists_stabilization_kernel_coordinates
      (T := fun T : {T : E →L[𝕜] F // T.IsFredholm} ↦ (T : E →L[𝕜] F))
      continuous_subtype_val.continuousAt (D := ⊤) (by simp)
  have := (T₀.2.coprod_of_finiteDimensional S.subtypeL).finite_ker
  have hline : finrank 𝕜 (TauCeti.detLine 𝕜 (LinearMap.ker
      ((T₀ : E →L[𝕜] F).coprod S.subtypeL : E × S →ₗ[𝕜] F)) ⊗[𝕜]
      Dual 𝕜 (TauCeti.detLine 𝕜 S)) = finrank 𝕜 𝕜 := by
    rw [← (ContinuousLinearMap.detLineChartEquiv _ _ q (hinv T₀ hT₀)).finrank_eq,
      T₀.2.finrank_detLine, finrank_self]
  have := Module.finite_of_finrank_eq_succ (hline.trans (finrank_self 𝕜))
  exact ⟨⟨S, _, S.subtypeL, q, U, hU, hinv, LinearEquiv.ofFinrankEq _ _ hline⟩, hT₀⟩

/-- The kernel chart chosen at a Fredholm operator. -/
def chartAt (T₀ : {T : E →L[𝕜] F // T.IsFredholm}) : Chart 𝕜 E F :=
  (exists_chart T₀).choose

theorem mem_chartAt (T₀ : {T : E →L[𝕜] F // T.IsFredholm}) : T₀ ∈ (chartAt T₀).U :=
  (exists_chart T₀).choose_spec

end TauCeti.FredholmDetLine

end

public section

noncomputable section

open Bundle Module Set TensorProduct Topology

namespace TauCeti.FredholmDetLine

section VectorBundle

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [CompleteSpace F]

variable (𝕜 E F) in
/-- The kernel-chart pretrivializations of the determinant line bundle on the space of Fredholm
operators, one chosen at each operator. -/
def vectorPrebundle : VectorPrebundle 𝕜 𝕜 (FredholmDetLine 𝕜 E F) where
  pretrivializationAtlas := range fun T₀ ↦ (chartAt T₀).pretrivialization
  pretrivialization_linear' := by
    rintro _ ⟨T₀, rfl⟩
    infer_instance
  pretrivializationAt T₀ := (chartAt T₀).pretrivialization
  mem_base_pretrivializationAt T₀ := mem_chartAt T₀
  pretrivialization_mem_atlas T₀ := ⟨T₀, rfl⟩
  exists_coordChange := by
    rintro _ ⟨T₁, rfl⟩ _ ⟨T₂, rfl⟩
    exact Chart.exists_coordChange _ _
  totalSpaceMk_isInducing T₀ := by
    simp only [Function.comp_def, Chart.pretrivialization_apply]
    exact isInducing_const_prod.2 ((chartAt T₀).isInducing_coord (mem_chartAt T₀))

/-- The topology on the total space of the determinant line bundle. -/
instance : TopologicalSpace (TotalSpace 𝕜 (FredholmDetLine 𝕜 E F)) :=
  (vectorPrebundle 𝕜 E F).totalSpaceTopology

/-- The determinant lines of Fredholm operators form a fibre bundle with fibre `𝕜`. -/
instance : FiberBundle 𝕜 (FredholmDetLine 𝕜 E F) :=
  (vectorPrebundle 𝕜 E F).toFiberBundle

/-- The determinant lines of Fredholm operators form a line bundle. -/
instance : VectorBundle 𝕜 𝕜 (FredholmDetLine 𝕜 E F) :=
  (vectorPrebundle 𝕜 E F).toVectorBundle

/-- **Kernel charts read continuous families continuously.** Let `σ` be a continuous family of
vectors of the determinant line bundle, and `(D, q)` a kernel chart of every operator `(σ x).proj`.
Then for every linear functional `ψ` on the model line, `x ↦ ψ (detLineChartEquiv (σ x).proj D q _
(σ x).2)` is continuous. This holds for every kernel chart, not only for those chosen to build
the trivializations of the bundle. -/
theorem continuous_detLineChartEquiv {X : Type*} [TopologicalSpace X] {Λ G : Type*}
    [NormedAddCommGroup Λ] [NormedSpace 𝕜 Λ] [FiniteDimensional 𝕜 Λ]
    [NormedAddCommGroup G] [NormedSpace 𝕜 G] [FiniteDimensional 𝕜 G]
    {D : Λ →L[𝕜] F} {q : E × Λ →L[𝕜] G} {σ : X → TotalSpace 𝕜 (FredholmDetLine 𝕜 E F)}
    (hσ : Continuous σ) (h : ∀ x, ((((σ x).proj : E →L[𝕜] F).coprod D).prod q).IsInvertible)
    (ψ : TauCeti.detLine 𝕜 G ⊗[𝕜] Dual 𝕜 (TauCeti.detLine 𝕜 Λ) →ₗ[𝕜] 𝕜) :
    Continuous fun x ↦
      ψ (ContinuousLinearMap.detLineChartEquiv ((σ x).proj : E →L[𝕜] F) D q (h x) (σ x).2) := by
  refine continuous_iff_continuousAt.2 fun x₀ ↦ ?_
  let c := chartAt (σ x₀).proj
  let W := σ ⁻¹' (π 𝕜 (FredholmDetLine 𝕜 E F) ⁻¹' c.U)
  have hW : IsOpen W := (c.isOpen_U.preimage (FiberBundle.continuous_proj 𝕜 _)).preimage hσ
  have hx₀ : x₀ ∈ W := mem_chartAt _
  -- Along `σ`, the chosen chart at `(σ x₀).proj` is continuous on `W`, being a trivialization.
  have hcoord : Continuous fun w : W ↦ c.coord (σ w).proj (σ w).2 := by
    let e := (vectorPrebundle 𝕜 E F).trivializationOfMemPretrivializationAtlas
      (e := c.pretrivialization) ⟨(σ x₀).proj, rfl⟩
    exact continuous_snd.comp <| e.continuousOn.comp_continuous (hσ.comp continuous_subtype_val)
      fun w ↦ w.2
  -- On `W`, the chart `(D, q)` is a continuous multiple of the chosen one.
  obtain ⟨k, hk, -, hkv⟩ := ContinuousLinearMap.exists_continuous_detLineChartEquiv_symm_eq_smul
    (T := fun w : W ↦ ((σ w).proj : E →L[𝕜] F))
    (continuous_subtype_val.comp <| (FiberBundle.continuous_proj 𝕜 _).comp
      (hσ.comp continuous_subtype_val))
    (fun w ↦ h w) (fun w ↦ c.isInvertible _ w.2) ⟨x₀, hx₀⟩
  let L : 𝕜 →ₗ[𝕜] 𝕜 := ψ ∘ₗ
    (ContinuousLinearMap.detLineChartEquiv ((σ x₀).proj : E →L[𝕜] F) D q (h x₀)).toLinearMap ∘ₗ
    (ContinuousLinearMap.detLineChartEquiv ((σ x₀).proj : E →L[𝕜] F) c.D c.q
      (c.isInvertible _ hx₀)).symm.toLinearMap ∘ₗ c.line.symm.toLinearMap
  have hval (w : W) : ψ (ContinuousLinearMap.detLineChartEquiv ((σ w).proj : E →L[𝕜] F) D q (h w)
      (σ w).2) = k w * L (c.coord (σ w).proj (σ w).2) := by
    rw [c.coord_apply_of_mem w.2]
    conv_lhs => rw [← (ContinuousLinearMap.detLineChartEquiv ((σ w).proj : E →L[𝕜] F) c.D c.q
      (c.isInvertible _ w.2)).symm_apply_apply (σ w).2, ← c.line.symm_apply_apply
        (ContinuousLinearMap.detLineChartEquiv _ c.D c.q _ (σ w).2)]
    rw [hkv w]
    exact ψ.map_smul (k w) _
  have hcont : ContinuousOn (fun x ↦ ψ (ContinuousLinearMap.detLineChartEquiv
      ((σ x).proj : E →L[𝕜] F) D q (h x) (σ x).2)) W := by
    rw [continuousOn_iff_continuous_domRestrict]
    exact (hk.mul (L.continuous_of_finiteDimensional.comp hcoord)).congr fun w ↦ (hval w).symm
  exact hcont.continuousAt (hW.mem_nhds hx₀)

/-- **Continuity can be checked in any kernel chart.** Let `σ` be a family of vectors of the
determinant line bundle over a continuous family of operators `(σ x).proj`, all in the domain of
one kernel chart `(D, q)`. If `σ` read in this chart and an identification `ψ` of its model line
with `𝕜` is continuous, then `σ` is continuous in the total space. -/
theorem continuous_of_continuous_detLineChartEquiv {X : Type*} [TopologicalSpace X] {Λ G : Type*}
    [NormedAddCommGroup Λ] [NormedSpace 𝕜 Λ] [FiniteDimensional 𝕜 Λ]
    [NormedAddCommGroup G] [NormedSpace 𝕜 G] [FiniteDimensional 𝕜 G]
    {D : Λ →L[𝕜] F} {q : E × Λ →L[𝕜] G} {σ : X → TotalSpace 𝕜 (FredholmDetLine 𝕜 E F)}
    (hp : Continuous fun x ↦ (σ x).proj)
    (h : ∀ x, ((((σ x).proj : E →L[𝕜] F).coprod D).prod q).IsInvertible)
    (ψ : TauCeti.detLine 𝕜 G ⊗[𝕜] Dual 𝕜 (TauCeti.detLine 𝕜 Λ) ≃ₗ[𝕜] 𝕜)
    (hψ : Continuous fun x ↦
      ψ (ContinuousLinearMap.detLineChartEquiv ((σ x).proj : E →L[𝕜] F) D q (h x) (σ x).2)) :
    Continuous σ := by
  refine continuous_iff_continuousAt.2 fun x₀ ↦ ?_
  let c := chartAt (σ x₀).proj
  let W := (fun x ↦ (σ x).proj) ⁻¹' c.U
  have hW : IsOpen W := c.isOpen_U.preimage hp
  have hx₀ : x₀ ∈ W := mem_chartAt _
  let e := (vectorPrebundle 𝕜 E F).trivializationOfMemPretrivializationAtlas
    (e := c.pretrivialization) ⟨(σ x₀).proj, rfl⟩
  -- On `W`, the chosen chart at `(σ x₀).proj` is a continuous multiple of the chart `(D, q)`.
  obtain ⟨k, hk, -, hkv⟩ := ContinuousLinearMap.exists_continuous_detLineChartEquiv_symm_eq_smul
    (T := fun w : W ↦ ((σ w).proj : E →L[𝕜] F)) (continuous_subtype_val.comp
      (hp.comp continuous_subtype_val)) (fun w ↦ c.isInvertible _ w.2) (fun w ↦ h w) ⟨x₀, hx₀⟩
  let L : 𝕜 →ₗ[𝕜] 𝕜 := c.line.toLinearMap ∘ₗ
    (ContinuousLinearMap.detLineChartEquiv ((σ x₀).proj : E →L[𝕜] F) c.D c.q
      (c.isInvertible _ hx₀)).toLinearMap ∘ₗ
    (ContinuousLinearMap.detLineChartEquiv ((σ x₀).proj : E →L[𝕜] F) D q (h x₀)).symm.toLinearMap
      ∘ₗ ψ.symm.toLinearMap
  have hval (w : W) : c.coord (σ w).proj (σ w).2 =
      k w * L (ψ (ContinuousLinearMap.detLineChartEquiv ((σ w).proj : E →L[𝕜] F) D q (h w)
        (σ w).2)) := by
    rw [c.coord_apply_of_mem w.2]
    conv_lhs => rw [← (ContinuousLinearMap.detLineChartEquiv ((σ w).proj : E →L[𝕜] F) D q
      (h w)).symm_apply_apply (σ w).2, ← ψ.symm_apply_apply
        (ContinuousLinearMap.detLineChartEquiv _ D q _ (σ w).2)]
    rw [hkv w]
    exact c.line.map_smul (k w) _
  have hcoord : Continuous fun w : W ↦ c.coord (σ w).proj (σ w).2 :=
    (hk.mul (L.continuous_of_finiteDimensional.comp (hψ.comp continuous_subtype_val))).congr
      fun w ↦ (hval w).symm
  -- On `W`, `σ` is the inverse of the trivialization applied to its continuous coordinates.
  have hσ : ContinuousOn σ W := by
    rw [continuousOn_iff_continuous_domRestrict]
    exact (e.continuousOn_symm.comp_continuous
      ((hp.comp continuous_subtype_val).prodMk hcoord) fun w ↦ ⟨w.2, mem_univ _⟩).congr
      fun w ↦ congrArg (TotalSpace.mk' 𝕜 (σ w).proj) (e.symm_apply_apply_mk w.2 (σ w).2)
  exact hσ.continuousAt (hW.mem_nhds hx₀)

end VectorBundle

/-! ### Orientation transport -/

section Orientation

variable (E F : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- **The orientation double cover of the determinant line bundle is a covering map.** Lifting
paths of Fredholm operators to it transports orientations of determinant lines
(`TauCeti.VectorBundleOrientationCover.orientationTransport`). -/
theorem isCoveringMap_proj :
    IsCoveringMap (VectorBundleOrientationCover.proj :
      VectorBundleOrientationCover ℝ (FredholmDetLine ℝ E F) (Fin 1) →
        {T : E →L[ℝ] F // T.IsFredholm}) :=
  VectorBundleOrientationCover.isCoveringMap_proj (by simp)

end Orientation

end TauCeti.FredholmDetLine

end

end

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Fredholm.DeterminantLine.Chart
public import Mathlib.Topology.VectorBundle.Basic
public import Mathlib.Topology.Algebra.Module.ModuleTopology
import TauCeti.Analysis.Fredholm.Stabilization

/-!
# The determinant line bundle of Fredholm operators

The determinant lines `det (ker T) ⊗ (det (F ⧸ range T))^*` of the Fredholm operators
`T : E →L[𝕜] F` between Banach spaces form a line bundle over the space of Fredholm operators,
although kernel and cokernel jump. This file constructs it as a Mathlib vector bundle
(`VectorBundle 𝕜 𝕜 (TauCeti.FredholmDetLine 𝕜 E F)`), with the kernel charts of
`TauCeti.Analysis.Fredholm.DeterminantLine.Chart` as its local trivializations.

The base is the subtype `{T : E →L[𝕜] F // T.IsFredholm}` of Fredholm operators with the
operator-norm topology, and the fibre `TauCeti.FredholmDetLine 𝕜 E F T` over `T` is a copy of the
determinant line of `T`, carrying the topology of a finite-dimensional vector space
(`moduleTopology`). For a continuous family of Fredholm operators `f : C(X, {T // T.IsFredholm})`,
the determinant line bundle of the family is the pullback `f *ᵖ FredholmDetLine 𝕜 E F`, a vector
bundle by Mathlib's `VectorBundle.pullback`.

A kernel chart is a finite stabilization `D₂ : Λ →L[𝕜] F` together with a kernel coordinate
`q : E × Λ →L[𝕜] G`, with `Λ` and `G` finite-dimensional. Its base set is the open set of the
Fredholm operators `T` for which the pair `(T.coprod D₂).prod q` is invertible
(`TauCeti.FredholmDetLine.pretrivialization`), and over it the chart is the isomorphism
`ContinuousLinearMap.detLineChartEquiv` with the fixed line `det G ⊗ (det Λ)^*`, read in a fixed
coordinate of that line (`TauCeti.FredholmDetLine.chartCoord`). The transition between two charts
is multiplication by a continuous nowhere-vanishing scalar
(`ContinuousLinearMap.exists_continuous_detLineChartEquiv_symm_eq_smul`), so the charts with
standard models `Λ = 𝕜ⁿ` and `G = 𝕜ᵐ` form a vector prebundle
(`TauCeti.FredholmDetLine.vectorPrebundle`). Every Fredholm operator lies in the base set of such a
chart (`ContinuousLinearMap.IsFredholm.exists_isInvertible_prod_coprod`), by the stabilization
theorem `ContinuousLinearMap.IsFredholm.exists_stabilization_kernel_coordinates`.

## Main definitions

* `TauCeti.FredholmDetLine 𝕜 E F`: the determinant lines of the Fredholm operators from `E` to `F`,
  as a family of topological vector spaces over the space of Fredholm operators.
* `TauCeti.FredholmDetLine.pretrivialization`: the kernel chart of a stabilization and a kernel
  coordinate, as a pretrivialization.
* `TauCeti.FredholmDetLine.trivialization`: a kernel chart with standard models, as a
  trivialization of the determinant line bundle.

## Main results

* `TauCeti.FredholmDetLine.continuousOn_pretrivialization_coordChange`: the transition between two
  kernel charts is continuous on the overlap of their base sets.
* `TauCeti.FredholmDetLine.fiberBundle`, `TauCeti.FredholmDetLine.vectorBundle`: the determinant
  lines form a vector bundle of rank one (`TauCeti.FredholmDetLine.finrank_eq_one`).

## References

* D. McDuff, D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  AMS Colloquium Publications 52, 2012, Section A.2 (determinant line bundles).
* A. Zinger, *The determinant line bundle for Fredholm operators: construction, properties, and
  classification*, Math. Scand. 118 (2016), 203–268, arXiv:1304.6368.
-/

public section

noncomputable section

open Bundle Set Topology Module TensorProduct ContinuousLinearMap

namespace TauCeti

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

variable (𝕜 E F) in
/-- The **determinant lines of Fredholm operators**: over a Fredholm operator `T : E →L[𝕜] F`, a
copy of its determinant line `det (ker T) ⊗ (det (F ⧸ range T))^*`. It carries the topology of a
finite-dimensional vector space, and these lines form a vector bundle over the space of Fredholm
operators (`TauCeti.FredholmDetLine.vectorBundle`). Use `TauCeti.FredholmDetLine.linearEquiv` to
pass to the determinant line itself. -/
def FredholmDetLine (T : {T : E →L[𝕜] F // T.IsFredholm}) : Type _ :=
  (T.1 : E →ₗ[𝕜] F).detLine

namespace FredholmDetLine

variable {T : {T : E →L[𝕜] F // T.IsFredholm}}

instance : AddCommGroup (FredholmDetLine 𝕜 E F T) :=
  inferInstanceAs (AddCommGroup (T.1 : E →ₗ[𝕜] F).detLine)

instance : Module 𝕜 (FredholmDetLine 𝕜 E F T) :=
  inferInstanceAs (Module 𝕜 (T.1 : E →ₗ[𝕜] F).detLine)

/-- The determinant line of a Fredholm operator carries its topology as a finite-dimensional
vector space, the finest topology making addition and scalar multiplication continuous. -/
instance : TopologicalSpace (FredholmDetLine 𝕜 E F T) := moduleTopology 𝕜 _

instance : IsModuleTopology 𝕜 (FredholmDetLine 𝕜 E F T) := ⟨rfl⟩

instance : ContinuousAdd (FredholmDetLine 𝕜 E F T) := IsModuleTopology.toContinuousAdd 𝕜 _

variable (T) in
/-- The fibre of `TauCeti.FredholmDetLine` over `T` is the determinant line of `T`. -/
def linearEquiv : FredholmDetLine 𝕜 E F T ≃ₗ[𝕜] (T.1 : E →ₗ[𝕜] F).detLine :=
  LinearEquiv.refl 𝕜 _

omit [CompleteSpace 𝕜] [CompleteSpace E] in
/-- The determinant line of a Fredholm operator is a line. -/
@[simp]
theorem finrank_eq_one : finrank 𝕜 (FredholmDetLine 𝕜 E F T) = 1 :=
  (linearEquiv T).finrank_eq.trans (LinearMap.finrank_detLine _)

variable {Λ G : Type*} [NormedAddCommGroup Λ] [NormedSpace 𝕜 Λ] [FiniteDimensional 𝕜 Λ]
  [NormedAddCommGroup G] [NormedSpace 𝕜 G] [FiniteDimensional 𝕜 G]

/-- The coordinate of a kernel chart: the kernel chart `ContinuousLinearMap.detLineChartEquiv`
identifies the determinant line of `T` with the fixed line `det G ⊗ (det Λ)^*`, which is then
identified with `𝕜` by a fixed isomorphism depending only on `Λ` and `G`. -/
def chartCoord (D₂ : Λ →L[𝕜] F) (q : E × Λ →L[𝕜] G)
    (h : ((T.1.coprod D₂).prod q).IsInvertible) : FredholmDetLine 𝕜 E F T ≃ₗ[𝕜] 𝕜 :=
  linearEquiv T ≪≫ₗ detLineChartEquiv T.1 D₂ q h ≪≫ₗ LinearEquiv.ofFinrankEq _ _ (by
    rw [finrank_tensorProduct, Subspace.dual_finrank_eq, TauCeti.finrank_detLine,
      TauCeti.finrank_detLine, finrank_self])

omit [CompleteSpace 𝕜] [CompleteSpace E] in
/-- A chart coordinate is the kernel chart `ContinuousLinearMap.detLineChartEquiv`, followed by an
identification of the fixed line `det G ⊗ (det Λ)^*` with `𝕜` that does not depend on `T`. -/
theorem chartCoord_def (D₂ : Λ →L[𝕜] F) (q : E × Λ →L[𝕜] G)
    (h : ((T.1.coprod D₂).prod q).IsInvertible) :
    chartCoord D₂ q h = linearEquiv T ≪≫ₗ detLineChartEquiv T.1 D₂ q h ≪≫ₗ
      LinearEquiv.ofFinrankEq _ _ (by
        rw [finrank_tensorProduct, Subspace.dual_finrank_eq, TauCeti.finrank_detLine,
          TauCeti.finrank_detLine, finrank_self]) :=
  (rfl)

omit [CompleteSpace 𝕜] [CompleteSpace E] in
/-- A chart coordinate is a homeomorphism onto `𝕜`. -/
theorem isInducing_chartCoord (D₂ : Λ →L[𝕜] F) (q : E × Λ →L[𝕜] G)
    (h : ((T.1.coprod D₂).prod q).IsInvertible) : IsInducing (chartCoord D₂ q h) :=
  (Homeomorph.mk (chartCoord D₂ q h).toEquiv
    (IsModuleTopology.continuous_of_linearMap (chartCoord D₂ q h).toLinearMap)
    (IsModuleTopology.continuous_of_linearMap
      (chartCoord D₂ q h).symm.toLinearMap)).isInducing

/-- The transition between the coordinates of two kernel charts, relative to its value at a base
point, is multiplication by a continuous nowhere-vanishing scalar along a continuous family of
Fredholm operators. -/
private theorem exists_continuous_chartCoord_symm_eq_smul {X : Type*} [TopologicalSpace X]
    {S : X → {T : E →L[𝕜] F // T.IsFredholm}} (hS : Continuous S)
    {Λ₃ G₃ : Type*} [NormedAddCommGroup Λ₃] [NormedSpace 𝕜 Λ₃] [FiniteDimensional 𝕜 Λ₃]
    [NormedAddCommGroup G₃] [NormedSpace 𝕜 G₃] [FiniteDimensional 𝕜 G₃]
    {D₂ : Λ →L[𝕜] F} {q : E × Λ →L[𝕜] G} {D₃ : Λ₃ →L[𝕜] F} {q₃ : E × Λ₃ →L[𝕜] G₃}
    (h : ∀ x, (((S x).1.coprod D₂).prod q).IsInvertible)
    (h₃ : ∀ x, (((S x).1.coprod D₃).prod q₃).IsInvertible) (x₀ : X) :
    ∃ c : X → 𝕜, Continuous c ∧ (∀ x, c x ≠ 0) ∧ ∀ x v,
      chartCoord D₃ q₃ (h₃ x) ((chartCoord D₂ q (h x)).symm v) =
        c x • chartCoord D₃ q₃ (h₃ x₀) ((chartCoord D₂ q (h x₀)).symm v) := by
  obtain ⟨c, hc, hc0, hcv⟩ := exists_continuous_detLineChartEquiv_symm_eq_smul
    (continuous_subtype_val.comp hS) h₃ h x₀
  refine ⟨c, hc, hc0, fun x v ↦ ?_⟩
  simp only [chartCoord, linearEquiv, LinearEquiv.trans_apply, LinearEquiv.symm_trans_apply]
  rw [← map_smul]
  exact congrArg _ (hcv x _)

variable (D₂ : Λ →L[𝕜] F) (q : E × Λ →L[𝕜] G)

omit [FiniteDimensional 𝕜 G] in
/-- The Fredholm operators `T` for which the stabilized pair `(T.coprod D₂).prod q` is invertible
form an open set. -/
theorem isOpen_setOf_isInvertible_prod_coprod :
    IsOpen {T : {T : E →L[𝕜] F // T.IsFredholm} | ((T.1.coprod D₂).prod q).IsInvertible} := by
  have : CompleteSpace Λ := FiniteDimensional.completeSpace 𝕜 Λ
  have hc : Continuous fun T : {T : E →L[𝕜] F // T.IsFredholm} ↦ (T.1.coprod D₂).prod q :=
    (prodL (E := E × Λ) (F := F) (G := G) 𝕜).continuous.comp
      ((continuous_subtype_val.continuousLinearMapCoprod continuous_const).prodMk
        continuous_const)
  exact isOpen_setOfPred_isInvertible.preimage hc

open scoped Classical in
/-- **The kernel chart as a pretrivialization.** Over the Fredholm operators `T` for which the pair
`(T.coprod D₂).prod q` is invertible, the determinant line of `T` is identified with `𝕜` by the
kernel chart coordinate `TauCeti.FredholmDetLine.chartCoord`. -/
def pretrivialization : Pretrivialization 𝕜 (π 𝕜 (FredholmDetLine 𝕜 E F)) where
  toFun p := ⟨p.proj, if h : ((p.proj.1.coprod D₂).prod q).IsInvertible then
    chartCoord D₂ q h p.2 else 0⟩
  invFun p := ⟨p.1, if h : ((p.1.1.coprod D₂).prod q).IsInvertible then
    (chartCoord D₂ q h).symm p.2 else 0⟩
  source := TotalSpace.proj ⁻¹' {T | ((T.1.coprod D₂).prod q).IsInvertible}
  target := {T | ((T.1.coprod D₂).prod q).IsInvertible} ×ˢ univ
  map_source' _ h := ⟨h, mem_univ _⟩
  map_target' _ h := h.1
  left_inv' := by
    rintro ⟨T, v⟩ (h : ((T.1.coprod D₂).prod q).IsInvertible)
    simp only [dite_eq_left h, LinearEquiv.symm_apply_apply]
  right_inv' := by
    rintro ⟨T, c⟩ ⟨h : ((T.1.coprod D₂).prod q).IsInvertible, -⟩
    simp only [dite_eq_left h, LinearEquiv.apply_symm_apply]
  open_target := (isOpen_setOf_isInvertible_prod_coprod D₂ q).prod isOpen_univ
  baseSet := {T | ((T.1.coprod D₂).prod q).IsInvertible}
  open_baseSet := isOpen_setOf_isInvertible_prod_coprod D₂ q
  source_eq := (rfl)
  target_eq := (rfl)
  proj_toFun _ _ := (rfl)

/-- The base set of a kernel chart consists of the Fredholm operators whose stabilized pair is
invertible. -/
@[simp]
theorem mem_pretrivialization_baseSet_iff :
    T ∈ (pretrivialization D₂ q).baseSet ↔ ((T.1.coprod D₂).prod q).IsInvertible := (Iff.rfl)

open scoped Classical in
private theorem pretrivialization_apply (p : TotalSpace 𝕜 (FredholmDetLine 𝕜 E F)) :
    pretrivialization D₂ q p = (p.proj, if h : ((p.proj.1.coprod D₂).prod q).IsInvertible then
      chartCoord D₂ q h p.2 else 0) := (rfl)

variable {D₂ q}

/-- Over its base set, a kernel chart reads the determinant line in the chart coordinate. -/
theorem pretrivialization_apply_mk (h : ((T.1.coprod D₂).prod q).IsInvertible)
    (v : FredholmDetLine 𝕜 E F T) :
    pretrivialization D₂ q ⟨T, v⟩ = (T, chartCoord D₂ q h v) := by
  rw [pretrivialization_apply, dite_eq_left h]

/-- Over its base set, the inverse of a kernel chart is the inverse chart coordinate. -/
theorem pretrivialization_symm_apply (h : ((T.1.coprod D₂).prod q).IsInvertible) (c : 𝕜) :
    (pretrivialization D₂ q).symm T c = (chartCoord D₂ q h).symm c := by
  have key := (pretrivialization D₂ q).apply_mk_symm h c
  rw [pretrivialization_apply_mk h, Prod.mk.injEq] at key
  exact (chartCoord D₂ q h).injective (by simpa using key.2)

instance : (pretrivialization D₂ q).IsLinear 𝕜 where
  linear T h := by
    simp only [pretrivialization_apply_mk h]
    exact (chartCoord D₂ q h).toLinearMap.isLinear

variable {Λ₃ G₃ : Type*} [NormedAddCommGroup Λ₃] [NormedSpace 𝕜 Λ₃] [FiniteDimensional 𝕜 Λ₃]
  [NormedAddCommGroup G₃] [NormedSpace 𝕜 G₃] [FiniteDimensional 𝕜 G₃]
  {D₃ : Λ₃ →L[𝕜] F} {q₃ : E × Λ₃ →L[𝕜] G₃}

/-- **Transitions between kernel charts are continuous.** The coordinate in the chart of
`(D₃, q₃)` of the point with coordinate `1` in the chart of `(D₂, q)` depends continuously on the
Fredholm operator over the overlap of the two base sets. By linearity it determines the whole
transition. -/
theorem continuousOn_pretrivialization_coordChange :
    ContinuousOn (fun T ↦ (pretrivialization D₃ q₃ ⟨T, (pretrivialization D₂ q).symm T 1⟩).2)
      ((pretrivialization D₂ q).baseSet ∩ (pretrivialization D₃ q₃).baseSet) := by
  set U := (pretrivialization D₂ q).baseSet ∩ (pretrivialization D₃ q₃).baseSet
  rcases U.eq_empty_or_nonempty with hU | ⟨T₀, hT₀⟩
  · rw [hU]
    exact continuousOn_empty _
  rw [continuousOn_iff_continuous_domRestrict]
  obtain ⟨c, hc, -, hcv⟩ := exists_continuous_chartCoord_symm_eq_smul continuous_subtype_val
    (fun T : U ↦ T.2.1) (fun T : U ↦ T.2.2) ⟨T₀, hT₀⟩
  refine (hc.smul (continuous_const (y := chartCoord D₃ q₃ hT₀.2
    ((chartCoord D₂ q hT₀.1).symm 1)))).congr fun T ↦ ?_
  rw [domRestrict_apply, pretrivialization_symm_apply T.2.1, pretrivialization_apply_mk T.2.2,
    hcv, Pi.smul_apply']

/-- The transition between two kernel charts is multiplication by a continuous scalar on the
overlap of their base sets. -/
private theorem exists_continuousOn_coordChange :
    ∃ f : {T : E →L[𝕜] F // T.IsFredholm} → 𝕜 →L[𝕜] 𝕜,
      ContinuousOn f ((pretrivialization D₂ q).baseSet ∩ (pretrivialization D₃ q₃).baseSet) ∧
      ∀ T ∈ (pretrivialization D₂ q).baseSet ∩ (pretrivialization D₃ q₃).baseSet, ∀ v : 𝕜,
        f T v = (pretrivialization D₃ q₃ ⟨T, (pretrivialization D₂ q).symm T v⟩).2 := by
  refine ⟨fun T ↦ (pretrivialization D₃ q₃ ⟨T, (pretrivialization D₂ q).symm T 1⟩).2 •
    ContinuousLinearMap.id 𝕜 𝕜, continuousOn_pretrivialization_coordChange.smul continuousOn_const,
    fun T hT v ↦ ?_⟩
  simp only [smul_apply, ContinuousLinearMap.id_apply,
    pretrivialization_symm_apply hT.1, pretrivialization_apply_mk hT.2]
  conv_rhs => rw [← mul_one v, ← smul_eq_mul, map_smul, map_smul]
  rw [smul_eq_mul, smul_eq_mul, mul_comm]

variable (𝕜 E F) [CompleteSpace F]

/-- Every Fredholm operator lies in the base set of a kernel chart with standard models. -/
private theorem exists_pretrivialization (T : {T : E →L[𝕜] F // T.IsFredholm}) :
    ∃ e : Pretrivialization 𝕜 (π 𝕜 (FredholmDetLine 𝕜 E F)),
      (∃ (n m : ℕ) (D₂ : (Fin n → 𝕜) →L[𝕜] F) (q : E × (Fin n → 𝕜) →L[𝕜] (Fin m → 𝕜)),
        e = pretrivialization D₂ q) ∧ T ∈ e.baseSet := by
  obtain ⟨n, m, D₂, q, h⟩ := T.2.exists_isInvertible_prod_coprod
  exact ⟨_, ⟨n, m, D₂, q, rfl⟩, h⟩

/-- **The determinant line bundle as a vector prebundle.** Its atlas consists of the kernel charts
`TauCeti.FredholmDetLine.pretrivialization` with standard models `Λ = 𝕜ⁿ` and `G = 𝕜ᵐ`; their
transitions are continuous (`TauCeti.FredholmDetLine.continuousOn_pretrivialization_coordChange`)
and they cover the space of Fredholm operators
(`ContinuousLinearMap.IsFredholm.exists_isInvertible_prod_coprod`). -/
def vectorPrebundle : VectorPrebundle 𝕜 𝕜 (FredholmDetLine 𝕜 E F) where
  pretrivializationAtlas := {e | ∃ (n m : ℕ) (D₂ : (Fin n → 𝕜) →L[𝕜] F)
    (q : E × (Fin n → 𝕜) →L[𝕜] (Fin m → 𝕜)), e = pretrivialization D₂ q}
  pretrivialization_linear' := by
    rintro _ ⟨n, m, D₂, q, rfl⟩
    infer_instance
  pretrivializationAt T := Classical.choose (exists_pretrivialization 𝕜 E F T)
  mem_base_pretrivializationAt T := (Classical.choose_spec (exists_pretrivialization 𝕜 E F T)).2
  pretrivialization_mem_atlas T := (Classical.choose_spec (exists_pretrivialization 𝕜 E F T)).1
  exists_coordChange := by
    rintro _ ⟨n, m, D₂, q, rfl⟩ _ ⟨n₃, m₃, D₃, q₃, rfl⟩
    exact exists_continuousOn_coordChange
  totalSpaceMk_isInducing T := by
    obtain ⟨⟨n, m, D₂, q, he⟩, hT⟩ := Classical.choose_spec (exists_pretrivialization 𝕜 E F T)
    rw [he] at hT ⊢
    convert (isInducing_const_prod (x := T)).mpr (isInducing_chartCoord D₂ q hT) using 1
    ext v : 1
    exact pretrivialization_apply_mk hT v

/-- A pretrivialization belongs to the atlas of the determinant line bundle exactly when it is a
kernel chart with standard models. -/
theorem mem_pretrivializationAtlas_iff
    (e : Pretrivialization 𝕜 (π 𝕜 (FredholmDetLine 𝕜 E F))) :
    e ∈ (vectorPrebundle 𝕜 E F).pretrivializationAtlas ↔
      ∃ (n m : ℕ) (D₂ : (Fin n → 𝕜) →L[𝕜] F) (q : E × (Fin n → 𝕜) →L[𝕜] (Fin m → 𝕜)),
        e = pretrivialization D₂ q := (Iff.rfl)

/-- The topology of the determinant line bundle, for which the kernel charts are local
trivializations. -/
instance topologicalSpaceTotalSpace : TopologicalSpace (TotalSpace 𝕜 (FredholmDetLine 𝕜 E F)) :=
  (vectorPrebundle 𝕜 E F).totalSpaceTopology

/-- The determinant lines of Fredholm operators form a fibre bundle. -/
instance fiberBundle : FiberBundle 𝕜 (FredholmDetLine 𝕜 E F) :=
  (vectorPrebundle 𝕜 E F).toFiberBundle

/-- **The determinant line bundle.** The determinant lines of the Fredholm operators from `E` to
`F` form a vector bundle of rank one over the space of Fredholm operators. -/
instance vectorBundle : VectorBundle 𝕜 𝕜 (FredholmDetLine 𝕜 E F) :=
  (vectorPrebundle 𝕜 E F).toVectorBundle

variable {𝕜 E F} {n m : ℕ}

/-- A kernel chart with standard models, as a trivialization of the determinant line bundle. -/
def trivialization (D₂ : (Fin n → 𝕜) →L[𝕜] F) (q : E × (Fin n → 𝕜) →L[𝕜] (Fin m → 𝕜)) :
    Trivialization 𝕜 (π 𝕜 (FredholmDetLine 𝕜 E F)) :=
  (vectorPrebundle 𝕜 E F).trivializationOfMemPretrivializationAtlas ⟨n, m, D₂, q, rfl⟩

variable (D₂ : (Fin n → 𝕜) →L[𝕜] F) (q : E × (Fin n → 𝕜) →L[𝕜] (Fin m → 𝕜))

instance : MemTrivializationAtlas (trivialization D₂ q) :=
  ⟨⟨_, ⟨n, m, D₂, q, rfl⟩, rfl⟩⟩

@[simp]
theorem trivialization_baseSet :
    (trivialization D₂ q).baseSet = {T | ((T.1.coprod D₂).prod q).IsInvertible} := (rfl)

/-- The trivialization of a kernel chart is the kernel chart. -/
@[simp]
theorem trivialization_toPretrivialization :
    (trivialization D₂ q).toPretrivialization = pretrivialization D₂ q := (rfl)

/-- Over its base set, the trivialization of a kernel chart reads the determinant line in the chart
coordinate. -/
theorem trivialization_apply_mk {T : {T : E →L[𝕜] F // T.IsFredholm}}
    (h : ((T.1.coprod D₂).prod q).IsInvertible) (v : FredholmDetLine 𝕜 E F T) :
    trivialization D₂ q ⟨T, v⟩ = (T, chartCoord D₂ q h v) :=
  pretrivialization_apply_mk h v

/-- Over its base set, the inverse of the trivialization of a kernel chart is the inverse chart
coordinate. -/
theorem trivialization_symm_apply {T : {T : E →L[𝕜] F // T.IsFredholm}}
    (h : ((T.1.coprod D₂).prod q).IsInvertible) (c : 𝕜) :
    (trivialization D₂ q).symm T c = (chartCoord D₂ q h).symm c :=
  pretrivialization_symm_apply h c

end FredholmDetLine

end TauCeti

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.MFDeriv.Atlas
public import Mathlib.Geometry.Manifold.VectorBundle.Tangent
public import TauCeti.Geometry.Manifold.FiberBundle.Submersion
public import TauCeti.Geometry.Manifold.VectorBundle.Tangent.Cast
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace

/-!
# The vertical tangent bundle of a smooth fibre bundle

Unlike a product `B × F`, a general smooth fibre bundle `π : E → B` carries no canonical horizontal
complement to its fibres: only the vertical subbundle `VE = ker(dπ) ⊆ TE` of vectors tangent to the
fibres is intrinsic. Geometrically, `VE` models infinitesimal fibrewise variations of sections,
serves as the target of the pointwise Cartan contact maps on `J¹E`, and gives the linear model
`Hom(π^* TB, VE)` over which the first-jet bundle `J¹E → E` is an affine bundle.

Because Mathlib's `FiberBundle.chartedSpace` charts total spaces only for normed-space fibres, the
vertical bundle is indexed over `TauCeti.ManifoldTotalSpace F E` with projection
`TauCeti.ManifoldTotalSpace.proj`. For `C^(n + 1)` manifold and bundle data, restricting the
preferred tangent trivializations to `{0} × EF` in `TauCeti.VerticalSpace.vectorPrebundle` equips
`TauCeti.VerticalBundle IB IF F E` with a `C^n` vector bundle structure (`contMDiffVectorBundle`):
one derivative of the `C^(n + 1)` bundle transitions is consumed by the vertical transition map
`TauCeti.VerticalSpace.coordChange`. By contrast, the bundle inclusion
`TauCeti.VerticalBundle.toTangentBundle` is `C^n` for every `n : ℕ∞ω` already on a `C^1` bundle
(`contMDiff_toTangentBundle`), and pulls back `C^n` regularity via
`contMDiffWithinAt_toTangentBundle_comp_iff`, because in matching preferred trivializations of `VE`
and `TE` it is the constant linear inclusion `w ↦ (0, w)`.

## Main definitions and results

* `TauCeti.verticalSubmodule` and `TauCeti.VerticalSpace`: the kernel submodule `ker (mfderiv proj)`
  and vertical tangent space type, with ambient inclusion `VerticalSpace.subtypeL`, submodule
  equivalence `VerticalSpace.equivSubmodule`, and preferred-chart linear equivalence
  `VerticalSpace.modelEquivAt`.
* `TauCeti.VerticalSpace.vectorPrebundle` and `contMDiffVectorBundle`: the `C^n` vector bundle
  structure on `TauCeti.VerticalBundle IB IF F E` for `C^(n + 1)` bundle data.
* `TauCeti.VerticalBundle.toTangentBundle`, `contMDiffWithinAt_toTangentBundle_comp_iff`, and
  `contMDiff_toTangentBundle`: the bundle inclusion `VE → TE` and its pullback regularity criterion.
* `TauCeti.VerticalSpace.verticalLift` and `hasMFDerivAt_homeomorph_mk_add_smul`: for a vector
  bundle `V → B`, the canonical fibre-translation identification `V_{z.proj} ≃L[𝕜] V_z V` realized
  by differentiating affine lines `t ↦ z + t • w` in the fibre.

## References

* I. Kolář, P. W. Michor, J. Slovák, *Natural Operations in Differential Geometry*, Springer,
  1993, §§6.11, 9.3.
* D. J. Saunders, *The Geometry of Jet Bundles*, Cambridge University Press, 1989, §§1.2, 2.2.
* Tangent-coordinate bridges and submersion projection derivatives (including
  `fst_comp_tangentCoordChange`, `fst_continuousLinearMapAt_tangent`, and `mfderiv_proj_symmL`)
  come from `TauCeti.Geometry.Manifold.VectorBundle.Tangent.Cast` (base-point bridges),
  `TauCeti.Geometry.Manifold.VectorBundle.Tangent.Basic`
  (`continuousLinearMapAt_symmL_coordChange`), and
  `TauCeti.Geometry.Manifold.FiberBundle.Submersion` (generalizing
  `TauCeti.Geometry.Manifold.VectorBundle.Submersion`).
-/

public section
noncomputable section

open Bundle Set Filter ContinuousLinearMap
open scoped Manifold Topology ContDiff

namespace TauCeti
section ManifoldFiber

variable {𝕜 B : Type*} [NontriviallyNormedField 𝕜]
  {EB : Type*} [NormedAddCommGroup EB] [NormedSpace 𝕜 EB] {HB : Type*} [TopologicalSpace HB]
  {IB : ModelWithCorners 𝕜 EB HB} [TopologicalSpace B] [ChartedSpace HB B]
  {EF : Type*} [NormedAddCommGroup EF] [NormedSpace 𝕜 EF] {HF : Type*} [TopologicalSpace HF]
  {IF : ModelWithCorners 𝕜 EF HF} {F : Type*} [TopologicalSpace F] [ChartedSpace HF F]
  {E : B → Type*} [TopologicalSpace (TotalSpace F E)] [∀ b, TopologicalSpace (E b)]
  [FiberBundle F E]

variable (IB IF F E) in
/-- The vertical tangent submodule `ker (mfderiv proj z)` inside `TangentSpace (IB.prod IF) z` at
`z : ManifoldTotalSpace F E`. -/
def verticalSubmodule (z : ManifoldTotalSpace F E) :
    Submodule 𝕜 (TangentSpace (IB.prod IF) z) :=
  (mfderiv (IB.prod IF) IB (ManifoldTotalSpace.proj : ManifoldTotalSpace F E → B) z).ker

variable (IB IF F E) in
/-- `verticalSubmodule` is the kernel of `mfderiv proj z`. -/
theorem verticalSubmodule_eq (z : ManifoldTotalSpace F E) :
    verticalSubmodule IB IF F E z =
      (mfderiv (IB.prod IF) IB (ManifoldTotalSpace.proj : ManifoldTotalSpace F E → B) z).ker :=
  (rfl)

/-- A tangent vector at `z` belongs to `verticalSubmodule` iff `mfderiv proj z` vanishes on it. -/
@[simp]
theorem mem_verticalSubmodule_iff {z : ManifoldTotalSpace F E}
    {v : TangentSpace (IB.prod IF) z} :
    v ∈ verticalSubmodule IB IF F E z ↔
      mfderiv (IB.prod IF) IB (ManifoldTotalSpace.proj : ManifoldTotalSpace F E → B) z v = 0 :=
  Iff.rfl

variable (IB IF F E) in
/-- Vertical tangent space `ker (mfderiv proj z)` of `E` at `z : ManifoldTotalSpace F E`, carried by
`verticalSubmodule IB IF F E z`. -/
def VerticalSpace (z : ManifoldTotalSpace F E) : Type _ :=
  ↥(verticalSubmodule IB IF F E z)

namespace VerticalSpace
variable {z : ManifoldTotalSpace F E}

instance : AddCommGroup (VerticalSpace IB IF F E z) :=
  inferInstanceAs (AddCommGroup ↥(verticalSubmodule IB IF F E z))

instance : Module 𝕜 (VerticalSpace IB IF F E z) :=
  inferInstanceAs (Module 𝕜 ↥(verticalSubmodule IB IF F E z))

instance : TopologicalSpace (VerticalSpace IB IF F E z) :=
  inferInstanceAs (TopologicalSpace ↥(verticalSubmodule IB IF F E z))

instance : IsTopologicalAddGroup (VerticalSpace IB IF F E z) :=
  inferInstanceAs (IsTopologicalAddGroup ↥(verticalSubmodule IB IF F E z))

instance : ContinuousSMul 𝕜 (VerticalSpace IB IF F E z) :=
  inferInstanceAs (ContinuousSMul 𝕜 ↥(verticalSubmodule IB IF F E z))

instance : T2Space (VerticalSpace IB IF F E z) :=
  inferInstanceAs (T2Space ↥(verticalSubmodule IB IF F E z))

instance : Inhabited (VerticalSpace IB IF F E z) :=
  inferInstanceAs (Inhabited ↥(verticalSubmodule IB IF F E z))

/-- The underlying ambient tangent vector of `v : VerticalSpace IB IF F E z`. -/
@[coe]
def val (v : VerticalSpace IB IF F E z) : TangentSpace (IB.prod IF) z :=
  Subtype.val v

instance : CoeOut (VerticalSpace IB IF F E z) (TangentSpace (IB.prod IF) z) :=
  ⟨val⟩

/-- Construct a vertical tangent vector at `z` from an ambient tangent vector in
`verticalSubmodule IB IF F E z`. -/
def mk (v : TangentSpace (IB.prod IF) z) (hv : v ∈ verticalSubmodule IB IF F E z) :
    VerticalSpace IB IF F E z :=
  ⟨v, hv⟩

/-- Coercing `mk v hv` into `TangentSpace` recovers `v`. -/
@[simp]
theorem val_mk (v : TangentSpace (IB.prod IF) z) (hv : v ∈ verticalSubmodule IB IF F E z) :
    ((mk v hv : VerticalSpace IB IF F E z) : TangentSpace (IB.prod IF) z) = v :=
  (rfl)

/-- Eta law reconstructing `v : VerticalSpace` from its ambient tangent vector. -/
@[simp]
theorem mk_val (v : VerticalSpace IB IF F E z)
    (hv : (v : TangentSpace (IB.prod IF) z) ∈ verticalSubmodule IB IF F E z) :
    mk (v : TangentSpace (IB.prod IF) z) hv = v :=
  (rfl)

/-- Continuous linear inclusion of `VerticalSpace IB IF F E z` into the ambient
`TangentSpace (IB.prod IF) z`. -/
def subtypeL : VerticalSpace IB IF F E z →L[𝕜] TangentSpace (IB.prod IF) z :=
  (verticalSubmodule IB IF F E z).subtypeL

/-- Coercing `VerticalSpace.subtypeL` to a function agrees with `VerticalSpace.val`. -/
@[simp]
theorem coe_subtypeL :
    ⇑(subtypeL (IB := IB) (IF := IF) (F := F) (E := E) (z := z)) = val :=
  (rfl)

/-- Canonical continuous linear equivalence between `VerticalSpace IB IF F E z` and the submodule
carrier `↥(verticalSubmodule IB IF F E z)`. -/
def equivSubmodule (z : ManifoldTotalSpace F E) :
    VerticalSpace IB IF F E z ≃L[𝕜] ↥(verticalSubmodule IB IF F E z) :=
  ContinuousLinearEquiv.refl 𝕜 ↥(verticalSubmodule IB IF F E z)

/-- Applying `equivSubmodule z` preserves the underlying ambient tangent vector. -/
@[simp]
theorem coe_equivSubmodule_apply (z : ManifoldTotalSpace F E)
    (v : VerticalSpace IB IF F E z) :
    ((equivSubmodule z v : ↥(verticalSubmodule IB IF F E z)) :
      TangentSpace (IB.prod IF) z) = v :=
  (rfl)

/-- Applying `(equivSubmodule z).symm` wraps a submodule element via `VerticalSpace.mk`. -/
@[simp]
theorem equivSubmodule_symm_apply (z : ManifoldTotalSpace F E)
    (v : ↥(verticalSubmodule IB IF F E z)) :
    (equivSubmodule z).symm v = mk v.val v.property :=
  (rfl)

/-- Two vertical tangent vectors at `z` are equal iff their ambient tangent vectors agree. -/
@[ext]
theorem ext {v w : VerticalSpace IB IF F E z}
    (h : (v : TangentSpace (IB.prod IF) z) = w) : v = w :=
  Subtype.ext h

/-- Coercion from `VerticalSpace` into the ambient `TangentSpace` is injective. -/
theorem coe_injective (z : ManifoldTotalSpace F E) :
    Function.Injective
      ((↑) : VerticalSpace IB IF F E z → TangentSpace (IB.prod IF) z) :=
  Subtype.coe_injective

@[simp] theorem coe_zero :
    ((0 : VerticalSpace IB IF F E z) : TangentSpace (IB.prod IF) z) = 0 := (rfl)

@[simp] theorem coe_add (v w : VerticalSpace IB IF F E z) :
    ((v + w : VerticalSpace IB IF F E z) : TangentSpace (IB.prod IF) z) = v + w := (rfl)

@[simp] theorem coe_neg (v : VerticalSpace IB IF F E z) :
    ((-v : VerticalSpace IB IF F E z) : TangentSpace (IB.prod IF) z) = -v := (rfl)

@[simp] theorem coe_sub (v w : VerticalSpace IB IF F E z) :
    ((v - w : VerticalSpace IB IF F E z) : TangentSpace (IB.prod IF) z) = v - w := (rfl)

@[simp] theorem coe_smul (c : 𝕜) (v : VerticalSpace IB IF F E z) :
    ((c • v : VerticalSpace IB IF F E z) : TangentSpace (IB.prod IF) z) = c • v := (rfl)

/-- The bundle projection differential vanishes on every vertical tangent vector. -/
@[simp]
theorem mfderiv_proj_coe (z : ManifoldTotalSpace F E) (v : VerticalSpace IB IF F E z) :
    mfderiv (IB.prod IF) IB (ManifoldTotalSpace.proj : ManifoldTotalSpace F E → B) z v = 0 :=
  v.property

/-- In model coordinates via `tangentSpaceCastModel`, every vertical tangent vector has zero base
component. -/
@[simp]
theorem tangentSpaceCastModel_coe_fst (z : ManifoldTotalSpace F E)
    (v : VerticalSpace IB IF F E z) :
    (tangentSpaceCastModel (IB.prod IF) z v).1 = 0 := by
  rw [← ManifoldTotalSpace.tangentSpaceCastModel_mfderiv_proj, mfderiv_proj_coe, map_zero]

/-- Preferred-chart coordinate equivalence `VerticalSpace IB IF F E z ≃L[𝕜] EF` reading the fibre
component in model coordinates at `z`. -/
def modelEquivAt (z : ManifoldTotalSpace F E) : VerticalSpace IB IF F E z ≃L[𝕜] EF :=
  let e : ↥(verticalSubmodule IB IF F E z) ≃L[𝕜] EF :=
    ContinuousLinearEquiv.ofContinuousLinearMap
      ((ContinuousLinearMap.snd 𝕜 EB EF).comp
        ((tangentSpaceCastModel (IB.prod IF) z).toContinuousLinearMap.comp
          (verticalSubmodule IB IF F E z).subtypeL))
      (ContinuousLinearMap.codRestrict
        ((tangentSpaceCastModel (IB.prod IF) z).symm.toContinuousLinearMap.comp
          (ContinuousLinearMap.inr 𝕜 EB EF))
        (verticalSubmodule IB IF F E z)
        fun w ↦ mem_verticalSubmodule_iff.2 <|
          (ContinuousLinearEquiv.map_eq_zero_iff (tangentSpaceCastModel IB z.proj)).1 <| by simp)
      (ContinuousLinearMap.ext fun w ↦ by simp)
      (ContinuousLinearMap.ext fun v ↦ Subtype.ext <|
        (tangentSpaceCastModel (IB.prod IF) z).injective <|
        Prod.ext
          (by
            simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply,
              Submodule.coe_subtypeL, Submodule.subtype_apply,
              ContinuousLinearMap.coe_codRestrict_apply, ContinuousLinearEquiv.coe_coe,
              ContinuousLinearEquiv.apply_symm_apply, ContinuousLinearMap.inr_apply,
              ContinuousLinearMap.coe_snd']
            rw [← ManifoldTotalSpace.tangentSpaceCastModel_mfderiv_proj,
              mem_verticalSubmodule_iff.1 v.property, map_zero])
          (by simp))
  e

/-- `modelEquivAt z` reads the second model-space coordinate of a vertical tangent vector. -/
@[simp]
theorem modelEquivAt_apply (z : ManifoldTotalSpace F E) (v : VerticalSpace IB IF F E z) :
    modelEquivAt z v = (tangentSpaceCastModel (IB.prod IF) z v).2 :=
  (rfl)

/-- `(modelEquivAt z).symm` embeds `w : EF` as `(0, w)` via `(tangentSpaceCastModel _ z).symm`. -/
@[simp]
theorem coe_modelEquivAt_symm_apply (z : ManifoldTotalSpace F E) (w : EF) :
    ((modelEquivAt (IB := IB) (IF := IF) (F := F) (E := E) z).symm w :
        TangentSpace (IB.prod IF) z) =
      (tangentSpaceCastModel (IB.prod IF) z).symm (0, w) :=
  (rfl)

section Bundle
variable [IsManifold IB 1 B] [IsManifold IF 1 F] [ContMDiffFiberBundle 1 F E IB IF]

/-- In any preferred tangent trivialization around `i` containing `z`, the first coordinate of a
vertical tangent vector at `z` vanishes. -/
theorem continuousLinearMapAt_coe_fst {i z : ManifoldTotalSpace F E}
    (hi : z ∈ (chartAt (ModelProd HB HF) i).source) (v : VerticalSpace IB IF F E z) :
    ((trivializationAt (EB × EF) (TangentSpace (IB.prod IF)) i).continuousLinearMapAt 𝕜 z v).1 =
      0 := by
  rw [ManifoldTotalSpace.fst_continuousLinearMapAt_tangent hi, mfderiv_proj_coe, map_zero]

/-- In any preferred tangent trivialization around `i` containing `z`, a tangent vector with
coordinate `(0, w)` belongs to `verticalSubmodule`. -/
theorem symmL_zero_mem_verticalSubmodule {i z : ManifoldTotalSpace F E}
    (hi : z ∈ (chartAt (ModelProd HB HF) i).source) (w : EF) :
    (trivializationAt (EB × EF) (TangentSpace (IB.prod IF)) i).symmL 𝕜 z (0, w) ∈
      verticalSubmodule IB IF F E z :=
  mem_verticalSubmodule_iff.2 (by rw [ManifoldTotalSpace.mfderiv_proj_symmL hi, map_zero])

open Classical in
/-- Local pretrivialization of `VerticalSpace IB IF F E` over the chart domain of `i`. -/
def pretrivializationAt (i : ManifoldTotalSpace F E) :
    Pretrivialization EF (π EF (VerticalSpace IB IF F E)) where
  toFun p := (p.proj, ((trivializationAt (EB × EF) (TangentSpace (IB.prod IF))
    i).continuousLinearMapAt 𝕜 p.proj p.snd).2)
  invFun q := if hq : q.1 ∈ (chartAt (ModelProd HB HF) i).source then
      ⟨q.1, mk ((trivializationAt (EB × EF) (TangentSpace (IB.prod IF)) i).symmL 𝕜 q.1 (0, q.2))
        (symmL_zero_mem_verticalSubmodule hq q.2)⟩
    else ⟨q.1, 0⟩
  source := π EF (VerticalSpace IB IF F E) ⁻¹' (chartAt (ModelProd HB HF) i).source
  target := (chartAt (ModelProd HB HF) i).source ×ˢ univ
  map_source' _ hp := ⟨hp, mem_univ _⟩
  map_target' _ hq := by split_ifs with h; exacts [h, (h hq.1).elim]
  left_inv' := by
    rintro ⟨z, v⟩ (hz : z ∈ (chartAt (ModelProd HB HF) i).source)
    dsimp only; rw [dite_eq_left hz]; congr 1; ext; rw [val_mk]
    set eT := trivializationAt (EB × EF) (TangentSpace (IB.prod IF)) i
    have hpair : (0, (eT.continuousLinearMapAt 𝕜 z v).2) = eT.continuousLinearMapAt 𝕜 z v :=
      Prod.ext (continuousLinearMapAt_coe_fst hz v).symm rfl
    rw [hpair, eT.symmL_continuousLinearMapAt hz]
  right_inv' := by
    rintro ⟨z, w⟩ ⟨hz : z ∈ (chartAt _ i).source, -⟩; dsimp only; rw [dite_eq_left hz]
    simp only [val_mk,
      (trivializationAt (EB × EF) (TangentSpace (IB.prod IF)) i).continuousLinearMapAt_symmL hz]
  open_target := (chartAt (ModelProd HB HF) i).open_source.prod isOpen_univ
  baseSet := (chartAt (ModelProd HB HF) i).source
  open_baseSet := (chartAt (ModelProd HB HF) i).open_source
  source_eq := rfl
  target_eq := rfl
  proj_toFun _ _ := rfl

@[simp]
theorem pretrivializationAt_apply (i : ManifoldTotalSpace F E)
    (p : TotalSpace EF (VerticalSpace IB IF F E)) :
    pretrivializationAt i p = (p.proj, ((trivializationAt (EB × EF)
      (TangentSpace (IB.prod IF)) i).continuousLinearMapAt 𝕜 p.proj p.snd).2) :=
  (rfl)

/-- Over the chart domain of `i`, `(pretrivializationAt i).symm z w` embeds `(0, w)` via the
inverse tangent trivialization `symmL`. -/
theorem pretrivializationAt_symm_apply {i z : ManifoldTotalSpace F E}
    (hz : z ∈ (chartAt (ModelProd HB HF) i).source) (w : EF) :
    (pretrivializationAt (IB := IB) (IF := IF) (F := F) (E := E) i).symm z w =
      mk ((trivializationAt (EB × EF) (TangentSpace (IB.prod IF)) i).symmL 𝕜 z (0, w))
        (symmL_zero_mem_verticalSubmodule hz w) :=
  TotalSpace.mk_injective z (((pretrivializationAt i).mk_symm hz w).trans (dite_eq_left hz))

instance pretrivializationAt_isLinear (i : ManifoldTotalSpace F E) :
    (pretrivializationAt (IB := IB) (IF := IF) (F := F) (E := E) i).IsLinear 𝕜 where
  linear z _ := (((ContinuousLinearMap.snd 𝕜 EB EF).comp
    (((trivializationAt (EB × EF) (TangentSpace (IB.prod IF)) i).continuousLinearMapAt
      𝕜 z).comp (verticalSubmodule IB IF F E z).subtypeL)).isLinear)

/-- Vertical coordinate change from chart `i` to chart `j` at `z`. -/
def coordChange (i j z : ManifoldTotalSpace F E) : EF →L[𝕜] EF :=
  (ContinuousLinearMap.snd 𝕜 EB EF).comp
    ((tangentCoordChange (IB.prod IF) i j z).comp (ContinuousLinearMap.inr 𝕜 EB EF))

@[simp]
theorem coordChange_apply (i j z : ManifoldTotalSpace F E) (w : EF) :
    coordChange (IB := IB) (IF := IF) (F := F) (E := E) i j z w =
      (tangentCoordChange (IB.prod IF) i j z (0, w)).2 :=
  (rfl)

/-- On the domain of chart `i`, `VerticalSpace.coordChange i i z` is the identity. -/
theorem coordChange_self {i z : ManifoldTotalSpace F E}
    (hz : z ∈ (chartAt (ModelProd HB HF) i).source) (w : EF) :
    coordChange (IB := IB) (IF := IF) (F := F) (E := E) i i z w = w := by
  rw [coordChange_apply, tangentCoordChange_self ((extChartAt_source (IB.prod IF) i).symm ▸ hz)]

/-- On triple chart overlaps, `VerticalSpace.coordChange` satisfies the cocycle law. -/
theorem coordChange_comp {i j k z : ManifoldTotalSpace F E}
    (hz : z ∈ (chartAt (ModelProd HB HF) i).source ∩
      (chartAt (ModelProd HB HF) j).source ∩
      (chartAt (ModelProd HB HF) k).source) (w : EF) :
    coordChange (IB := IB) (IF := IF) (F := F) (E := E) j k z
        (coordChange (IB := IB) (IF := IF) (F := F) (E := E) i j z w) =
      coordChange (IB := IB) (IF := IF) (F := F) (E := E) i k z w := by
  have hfst : (tangentCoordChange (IB.prod IF) i j z ((0 : EB), w)).1 = 0 := by
    have h := DFunLike.congr_fun
      (ManifoldTotalSpace.fst_comp_tangentCoordChange (IB := IB) (IF := IF) hz.1.1 hz.1.2)
      ((0 : EB), w)
    simpa using h
  have hpair : ((0 : EB), coordChange (IB := IB) (IF := IF) (F := F) (E := E) i j z w) =
      tangentCoordChange (IB.prod IF) i j z ((0 : EB), w) :=
    Prod.ext hfst.symm rfl
  have hz' : z ∈ (extChartAt (IB.prod IF) i).source ∩
      (extChartAt (IB.prod IF) j).source ∩
      (extChartAt (IB.prod IF) k).source := by
    rwa [extChartAt_source, extChartAt_source, extChartAt_source]
  rw [coordChange_apply, hpair, tangentCoordChange_comp hz', ← coordChange_apply]

private theorem pretrivializationAt_apply_symm {i j z : ManifoldTotalSpace F E}
    (hz : z ∈ (chartAt (ModelProd HB HF) i).source ∩ (chartAt (ModelProd HB HF) j).source)
    (w : EF) :
    coordChange (IB := IB) (IF := IF) (F := F) (E := E) i j z w =
      (pretrivializationAt (IB := IB) (IF := IF) (F := F) (E := E) j
        ⟨z, (pretrivializationAt i).symm z w⟩).2 := by
  rcases hz with ⟨hzi, hzj⟩
  rw [pretrivializationAt_apply, pretrivializationAt_symm_apply hzi]
  dsimp only
  rw [val_mk, TauCeti.Manifold.continuousLinearMapAt_symmL_coordChange hzi hzj, coordChange_apply]

/-- For a `C^(n + 1)` fibre bundle over `C^(n + 1)` base and fibre manifolds, the vertical
coordinate change `VerticalSpace.coordChange i j` is `C^n` on chart overlaps. -/
theorem contMDiffOn_coordChange {n : ℕ∞ω} [IsManifold IB (n + 1) B] [IsManifold IF (n + 1) F]
    [ContMDiffFiberBundle (n + 1) F E IB IF] (i j : ManifoldTotalSpace F E) :
    ContMDiffOn (IB.prod IF) 𝓘(𝕜, EF →L[𝕜] EF) n
      (coordChange (IB := IB) (IF := IF) (F := F) (E := E) i j)
      ((chartAt (ModelProd HB HF) i).source ∩ (chartAt (ModelProd HB HF) j).source) := by
  have : IsManifold IB n B := .of_le (n := n + 1) le_self_add
  have : IsManifold IF n F := .of_le (n := n + 1) le_self_add
  have : ContMDiffFiberBundle n F E IB IF := .of_le (n := n + 1) le_self_add
  exact contMDiffOn_const.clm_comp (((tangentBundleCore.isContMDiff (I := IB.prod IF)
    (M := ManifoldTotalSpace F E) (n := n)).contMDiffOn_coordChange (achart _ i)
    (achart _ j)).clm_comp contMDiffOn_const)

/-- The `VectorPrebundle` giving `VerticalSpace IB IF F E` its vector bundle structure. -/
def vectorPrebundle : VectorPrebundle 𝕜 EF (VerticalSpace IB IF F E) where
  pretrivializationAtlas := range (pretrivializationAt (IB := IB) (IF := IF) (F := F) (E := E))
  pretrivialization_linear' := by rintro _ ⟨i, rfl⟩; infer_instance
  pretrivializationAt := pretrivializationAt
  mem_base_pretrivializationAt z := mem_chart_source _ z
  pretrivialization_mem_atlas z := ⟨z, rfl⟩
  exists_coordChange := by
    rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩
    have : IsManifold IB (0 + 1) B := (by simpa); have : IsManifold IF (0 + 1) F := by simpa
    have : ContMDiffFiberBundle (0 + 1) F E IB IF := by simpa
    exact ⟨coordChange (IB := IB) (IF := IF) (F := F) (E := E) i j,
      (contMDiffOn_coordChange (n := 0) i j).continuousOn,
      fun _ hz w ↦ pretrivializationAt_apply_symm hz w⟩
  totalSpaceMk_isInducing z := by
    have hfun : (pretrivializationAt (IB := IB) (IF := IF) (F := F) (E := E) z ∘ TotalSpace.mk z) =
        Prod.mk z ∘ modelEquivAt z := by
      funext v
      rw [Function.comp_apply, Function.comp_apply, pretrivializationAt_apply]
      dsimp only
      rw [TauCeti.Manifold.continuousLinearMapAt_trivializationAt_self_eq_tangentSpaceCastModel,
        ContinuousLinearEquiv.coe_coe, ← modelEquivAt_apply]
    exact hfun ▸ (isInducing_prodMkRight z).comp (modelEquivAt z).toHomeomorph.isInducing

instance instTopologicalSpaceTotalSpace :
    TopologicalSpace (TotalSpace EF (VerticalSpace IB IF F E)) :=
  (vectorPrebundle (IB := IB) (IF := IF) (F := F) (E := E)).totalSpaceTopology

instance instFiberBundle : FiberBundle EF (VerticalSpace IB IF F E) :=
  (vectorPrebundle (IB := IB) (IF := IF) (F := F) (E := E)).toFiberBundle

instance instVectorBundle : VectorBundle 𝕜 EF (VerticalSpace IB IF F E) :=
  (vectorPrebundle (IB := IB) (IF := IF) (F := F) (E := E)).toVectorBundle

@[simp]
theorem trivializationAt_baseSet (i : ManifoldTotalSpace F E) :
    (trivializationAt EF (VerticalSpace IB IF F E) i).baseSet =
      (chartAt (ModelProd HB HF) i).source :=
  (rfl)

@[simp]
theorem trivializationAt_apply (i : ManifoldTotalSpace F E)
    (p : TotalSpace EF (VerticalSpace IB IF F E)) :
    trivializationAt EF (VerticalSpace IB IF F E) i p = (p.proj, ((trivializationAt (EB × EF)
      (TangentSpace (IB.prod IF)) i).continuousLinearMapAt 𝕜 p.proj p.snd).2) :=
  (rfl)

/-- Over the chart domain of `i`, `(trivializationAt EF (VerticalSpace ...) i).symm z w` embeds
`(0, w)` via the inverse tangent trivialization `symmL`. -/
theorem trivializationAt_symm_apply {i z : ManifoldTotalSpace F E}
    (hz : z ∈ (chartAt (ModelProd HB HF) i).source) (w : EF) :
    (trivializationAt EF (VerticalSpace IB IF F E) i).symm z w =
      mk ((trivializationAt (EB × EF) (TangentSpace (IB.prod IF)) i).symmL 𝕜 z (0, w))
        (symmL_zero_mem_verticalSubmodule hz w) :=
  pretrivializationAt_symm_apply hz w

/-- Over the chart domain of `i`, coercing `(trivializationAt EF (VerticalSpace ...) i).symmL 𝕜 z w`
into `TangentSpace` gives `(trivializationAt (EB × EF) (TangentSpace ...) i).symmL 𝕜 z (0, w)`. -/
theorem coe_symmL_trivializationAt_apply {i z : ManifoldTotalSpace F E}
    (hz : z ∈ (chartAt (ModelProd HB HF) i).source) (w : EF) :
    (((trivializationAt EF (VerticalSpace IB IF F E) i).symmL 𝕜 z w :
        VerticalSpace IB IF F E z) : TangentSpace (IB.prod IF) z) =
      (trivializationAt (EB × EF) (TangentSpace (IB.prod IF)) i).symmL 𝕜 z (0, w) := by
  rw [Trivialization.symmL_apply (R := 𝕜) _ hz, trivializationAt_symm_apply hz, val_mk]

/-- Over its own base point `z`, the preferred trivialization of `VerticalSpace` evaluates as
`modelEquivAt z`. -/
@[simp]
theorem continuousLinearMapAt_trivializationAt_self (z : ManifoldTotalSpace F E)
    (v : VerticalSpace IB IF F E z) :
    (trivializationAt EF (VerticalSpace IB IF F E) z).continuousLinearMapAt 𝕜 z v =
      modelEquivAt z v := by
  rw [Trivialization.continuousLinearMapAt_apply_of_mem (R := 𝕜) _
      (mem_baseSet_trivializationAt EF (VerticalSpace IB IF F E) z),
    trivializationAt_apply,
    TauCeti.Manifold.continuousLinearMapAt_trivializationAt_self_eq_tangentSpaceCastModel,
    ContinuousLinearEquiv.coe_coe, ← modelEquivAt_apply]

/-- Over its own base point `z`, the inverse preferred trivialization `symm` of `VerticalSpace`
evaluates as `(modelEquivAt z).symm`. -/
@[simp]
theorem trivializationAt_symm_self (z : ManifoldTotalSpace F E) (w : EF) :
    (trivializationAt EF (VerticalSpace IB IF F E) z).symm z w = (modelEquivAt z).symm w := by
  ext
  rw [← Trivialization.symmL_apply (R := 𝕜) _ (mem_chart_source _ z),
    coe_symmL_trivializationAt_apply (mem_chart_source _ z), coe_modelEquivAt_symm_apply,
    TauCeti.Manifold.symmL_trivializationAt_self_eq_tangentSpaceCastModel_symm,
    ContinuousLinearEquiv.coe_coe]

/-- Over its own base point `z`, the inverse preferred trivialization `symmL` of `VerticalSpace`
equals `(modelEquivAt z).symm` as a continuous linear map. -/
@[simp]
theorem symmL_trivializationAt_self (z : ManifoldTotalSpace F E) :
    (trivializationAt EF (VerticalSpace IB IF F E) z).symmL 𝕜 z =
      (modelEquivAt z).symm.toContinuousLinearMap := by
  ext w
  rw [Trivialization.symmL_apply (R := 𝕜) _ (mem_chart_source _ z), trivializationAt_symm_self,
    ContinuousLinearEquiv.coe_coe]

/-- For a `C^(n + 1)` fibre bundle over `C^(n + 1)` base and fibre manifolds, `VerticalSpace` forms
a `C^n` vector bundle over `ManifoldTotalSpace F E`. -/
theorem contMDiffVectorBundle {n : ℕ∞ω} [IsManifold IB (n + 1) B] [IsManifold IF (n + 1) F]
    [ContMDiffFiberBundle (n + 1) F E IB IF] :
    ContMDiffVectorBundle n EF (VerticalSpace IB IF F E) (IB.prod IF) := by
  have : (vectorPrebundle (IB := IB) (IF := IF) (F := F) (E := E)).IsContMDiff (IB.prod IF) n := by
    refine ⟨?_⟩; rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩
    exact ⟨coordChange i j, contMDiffOn_coordChange i j,
      fun _ hz w ↦ pretrivializationAt_apply_symm hz w⟩
  exact (vectorPrebundle (IB := IB) (IF := IF) (F := F) (E := E)).contMDiffVectorBundle (IB.prod IF)

omit [IsManifold IB 1 B] [IsManifold IF 1 F] [ContMDiffFiberBundle 1 F E IB IF] in
instance [IsManifold IB ∞ B] [IsManifold IF ∞ F] [ContMDiffFiberBundle ∞ F E IB IF] :
    ContMDiffVectorBundle ∞ EF (VerticalSpace IB IF F E) (IB.prod IF) := by
  have : IsManifold IB (∞ + 1) B := (by simpa); have : IsManifold IF (∞ + 1) F := by simpa
  have : ContMDiffFiberBundle (∞ + 1) F E IB IF := (by simpa); exact contMDiffVectorBundle

omit [IsManifold IB 1 B] [IsManifold IF 1 F] [ContMDiffFiberBundle 1 F E IB IF] in
instance [IsManifold IB ω B] [IsManifold IF ω F] [ContMDiffFiberBundle ω F E IB IF] :
    ContMDiffVectorBundle ω EF (VerticalSpace IB IF F E) (IB.prod IF) := by
  have : IsManifold IB (ω + 1) B := (by simpa); have : IsManifold IF (ω + 1) F := by simpa
  have : ContMDiffFiberBundle (ω + 1) F E IB IF := (by simpa); exact contMDiffVectorBundle

end Bundle
end VerticalSpace

variable (IB IF F E) in
/-- The **vertical tangent bundle** `VE` of a smooth fibre bundle `E`. -/
abbrev VerticalBundle := TotalSpace EF (VerticalSpace IB IF F E)

namespace VerticalBundle

/-- The canonical bundle inclusion from `VerticalBundle` into `TangentBundle`. -/
def toTangentBundle (p : VerticalBundle IB IF F E) :
    TangentBundle (IB.prod IF) (ManifoldTotalSpace F E) :=
  ⟨p.proj, p.snd⟩

/-- Projecting `toTangentBundle p` onto `ManifoldTotalSpace F E` recovers `p.proj`. -/
@[simp]
theorem proj_toTangentBundle (p : VerticalBundle IB IF F E) :
    (toTangentBundle p).proj = p.proj :=
  (rfl)

/-- The fibre component of `toTangentBundle p` is `p.snd` coerced into `TangentSpace`. -/
@[simp]
theorem snd_toTangentBundle (p : VerticalBundle IB IF F E) :
    (toTangentBundle p).snd = (p.snd : TangentSpace (IB.prod IF) p.proj) :=
  (rfl)

/-- The canonical bundle inclusion `VerticalBundle → TangentBundle` is injective. -/
theorem toTangentBundle_injective :
    Function.Injective (toTangentBundle (IB := IB) (IF := IF) (F := F) (E := E)) := by
  rintro ⟨z₁, v₁⟩ ⟨z₂, v₂⟩ h; obtain rfl : z₁ = z₂ := congrArg TotalSpace.proj h
  exact congrArg (TotalSpace.mk' EF z₁) (VerticalSpace.ext (eq_of_heq (TotalSpace.mk.inj h).2))

section Regularity
variable [IsManifold IB 1 B] [IsManifold IF 1 F] [ContMDiffFiberBundle 1 F E IB IF]
  {M EM HM : Type*} [NormedAddCommGroup EM] [NormedSpace 𝕜 EM] [TopologicalSpace HM]
  {IM : ModelWithCorners 𝕜 EM HM} [TopologicalSpace M] [ChartedSpace HM M]

/-- A map into `VerticalBundle` is `C^n` within `s` at `x₀` iff its composition with
`VerticalBundle.toTangentBundle` into `TangentBundle` is `C^n` within `s` at `x₀`. Only `C^1`
bundle regularity is required, for arbitrary `n : ℕ∞ω`. -/
theorem contMDiffWithinAt_toTangentBundle_comp_iff {n : ℕ∞ω}
    {g : M → VerticalBundle IB IF F E} {s : Set M} {x₀ : M} :
    ContMDiffWithinAt IM ((IB.prod IF).prod 𝓘(𝕜, EB × EF)) n
        (toTangentBundle (IB := IB) (IF := IF) (F := F) (E := E) ∘ g) s x₀ ↔
      ContMDiffWithinAt IM ((IB.prod IF).prod 𝓘(𝕜, EF)) n g s x₀ := by
  rw [Bundle.contMDiffWithinAt_totalSpace_iff, Bundle.contMDiffWithinAt_totalSpace_iff]
  simp only [Function.comp_def, proj_toTangentBundle]
  refine and_congr_right fun hproj ↦ ?_
  have hmem : ∀ᶠ x in 𝓝[s] x₀,
      (g x).proj ∈ (chartAt (ModelProd HB HF) (g x₀).proj).source :=
    hproj.continuousWithinAt.preimage_mem_nhdsWithin
      ((chartAt (ModelProd HB HF) (g x₀).proj).open_source.mem_nhds
        (mem_chart_source _ (g x₀).proj))
  have hpair_at {p : VerticalBundle IB IF F E}
      (hp : p.proj ∈ (chartAt (ModelProd HB HF) (g x₀).proj).source) :
      (trivializationAt (EB × EF) (TangentSpace (IB.prod IF)) (g x₀).proj
        (toTangentBundle p)).2 =
        ((0 : EB), (trivializationAt EF (VerticalSpace IB IF F E) (g x₀).proj p).2) := by
    have h1 := VerticalSpace.continuousLinearMapAt_coe_fst hp p.snd
    rw [Trivialization.continuousLinearMapAt_apply_of_mem (R := 𝕜) _ hp] at h1
    refine Prod.ext h1 ?_
    rw [VerticalSpace.trivializationAt_apply,
      Trivialization.continuousLinearMapAt_apply_of_mem (R := 𝕜) _ hp, toTangentBundle]
  -- In the matching trivializations over `(g x₀).proj`, `toTangentBundle` acts as `w ↦ (0, w)`.
  have hpair : (fun x ↦ (trivializationAt (EB × EF) (TangentSpace (IB.prod IF)) (g x₀).proj
        (toTangentBundle (g x))).2) =ᶠ[𝓝[s] x₀]
      fun x ↦ ((0 : EB),
        (trivializationAt EF (VerticalSpace IB IF F E) (g x₀).proj (g x)).2) := by
    filter_upwards [hmem] with x hx using hpair_at hx
  have hpair₀ := hpair_at (mem_chart_source (ModelProd HB HF) (g x₀).proj)
  constructor
  · intro h
    have h' : ContMDiffWithinAt IM 𝓘(𝕜, EB × EF) n
        (fun x ↦ ((0 : EB),
          (trivializationAt EF (VerticalSpace IB IF F E) (g x₀).proj (g x)).2)) s x₀ :=
      h.congr_of_eventuallyEq hpair.symm hpair₀.symm
    have hsnd := (ContinuousLinearMap.snd 𝕜 EB EF).contDiff.comp_contMDiffWithinAt h'
    exact hsnd
  · intro h
    exact ((contMDiffWithinAt_const (c := (0 : EB))).prodMk_space h).congr_of_eventuallyEq
      hpair hpair₀

/-- Pointwise `ContMDiffAt` form of `contMDiffWithinAt_toTangentBundle_comp_iff`. -/
theorem contMDiffAt_toTangentBundle_comp_iff {n : ℕ∞ω}
    {g : M → VerticalBundle IB IF F E} {x₀ : M} :
    ContMDiffAt IM ((IB.prod IF).prod 𝓘(𝕜, EB × EF)) n
        (toTangentBundle (IB := IB) (IF := IF) (F := F) (E := E) ∘ g) x₀ ↔
      ContMDiffAt IM ((IB.prod IF).prod 𝓘(𝕜, EF)) n g x₀ := by
  simp only [← contMDiffWithinAt_univ, contMDiffWithinAt_toTangentBundle_comp_iff]

/-- Setwise `ContMDiffOn` form of `contMDiffWithinAt_toTangentBundle_comp_iff`. -/
theorem contMDiffOn_toTangentBundle_comp_iff {n : ℕ∞ω}
    {g : M → VerticalBundle IB IF F E} {s : Set M} :
    ContMDiffOn IM ((IB.prod IF).prod 𝓘(𝕜, EB × EF)) n
        (toTangentBundle (IB := IB) (IF := IF) (F := F) (E := E) ∘ g) s ↔
      ContMDiffOn IM ((IB.prod IF).prod 𝓘(𝕜, EF)) n g s :=
  forall₂_congr fun _ _ ↦ contMDiffWithinAt_toTangentBundle_comp_iff

/-- Global `ContMDiff` form of `contMDiffWithinAt_toTangentBundle_comp_iff`. -/
theorem contMDiff_toTangentBundle_comp_iff {n : ℕ∞ω}
    {g : M → VerticalBundle IB IF F E} :
    ContMDiff IM ((IB.prod IF).prod 𝓘(𝕜, EB × EF)) n
        (toTangentBundle (IB := IB) (IF := IF) (F := F) (E := E) ∘ g) ↔
      ContMDiff IM ((IB.prod IF).prod 𝓘(𝕜, EF)) n g := by
  simp only [← contMDiffOn_univ, contMDiffOn_toTangentBundle_comp_iff]

/-- On any `C^1` fibre bundle over `C^1` base and fibre manifolds, the bundle inclusion
`VerticalBundle.toTangentBundle` is `C^n` for every `n : ℕ∞ω`: in matching preferred
trivializations of `VE` and `TE` it is the constant linear inclusion `w ↦ (0, w)`. -/
theorem contMDiff_toTangentBundle (n : ℕ∞ω) :
    ContMDiff ((IB.prod IF).prod 𝓘(𝕜, EF)) ((IB.prod IF).prod 𝓘(𝕜, EB × EF)) n
      (toTangentBundle (IB := IB) (IF := IF) (F := F) (E := E)) :=
  (contMDiff_toTangentBundle_comp_iff (IM := (IB.prod IF).prod 𝓘(𝕜, EF)) (g := id)).2 contMDiff_id

end Regularity
end VerticalBundle
end ManifoldFiber

namespace VerticalSpace
variable {𝕜 B : Type*} [NontriviallyNormedField 𝕜]
  {EB : Type*} [NormedAddCommGroup EB] [NormedSpace 𝕜 EB] {HB : Type*} [TopologicalSpace HB]
  {IB : ModelWithCorners 𝕜 EB HB} {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [TopologicalSpace B] [ChartedSpace HB B]
  {V : B → Type*} [TopologicalSpace (TotalSpace F V)] [∀ b, AddCommMonoid (V b)]
  [∀ b, Module 𝕜 (V b)] [∀ b, TopologicalSpace (V b)] [FiberBundle F V] [VectorBundle 𝕜 F V]

variable (IB) in
/-- Canonical equivalence `V z.proj ≃L[𝕜] VerticalSpace IB 𝓘(𝕜, F) F V z` identifying a vector
bundle fibre with the vertical tangent space along that fibre via translation. -/
def verticalLift (z : ManifoldTotalSpace F V) :
    V z.proj ≃L[𝕜] VerticalSpace IB 𝓘(𝕜, F) F V z :=
  ((trivializationAt F V z.proj).continuousLinearEquivAt 𝕜 z.proj
    (mem_baseSet_trivializationAt F V z.proj)).trans (modelEquivAt z).symm

/-- In preferred vertical model coordinates at `z`, `verticalLift IB z w` agrees with the preferred
vector-bundle coordinate of `w` at `z.proj`. -/
theorem modelEquivAt_verticalLift (z : ManifoldTotalSpace F V) (w : V z.proj) :
    modelEquivAt z (verticalLift IB z w) =
      (trivializationAt F V z.proj).continuousLinearMapAt 𝕜 z.proj w := by
  rw [verticalLift, ContinuousLinearEquiv.trans_apply, ContinuousLinearEquiv.apply_symm_apply,
    Trivialization.continuousLinearEquivAt_apply]
  exact ((trivializationAt F V z.proj).continuousLinearMapAt_apply_of_mem (R := 𝕜)
    (mem_baseSet_trivializationAt F V z.proj) w).symm

/-- Inverting `verticalLift IB z` applies the inverse preferred vector-bundle trivialization at
`z.proj` to `modelEquivAt z v`. -/
@[simp]
theorem verticalLift_symm_apply (z : ManifoldTotalSpace F V)
    (v : VerticalSpace IB 𝓘(𝕜, F) F V z) :
    (verticalLift IB z).symm v =
      (trivializationAt F V z.proj).symmL 𝕜 z.proj (modelEquivAt z v) := by
  apply (verticalLift IB z).injective
  rw [ContinuousLinearEquiv.apply_symm_apply]
  apply (modelEquivAt z).injective
  rw [modelEquivAt_verticalLift,
    (trivializationAt F V z.proj).continuousLinearMapAt_symmL
      (mem_baseSet_trivializationAt F V z.proj)]

private theorem extChartAt_homeomorph_mk_add_smul {i z : ManifoldTotalSpace F V}
    (hbi : z.proj ∈ (trivializationAt F V i.proj).baseSet) (w : V z.proj) (t : 𝕜) :
    extChartAt (IB.prod 𝓘(𝕜, F)) i (ManifoldTotalSpace.homeomorph F V ⟨z.proj, z.snd + t • w⟩) =
      (extChartAt IB i.proj z.proj, (trivializationAt F V i.proj ⟨z.proj, z.snd⟩).2 +
        t • (trivializationAt F V i.proj ⟨z.proj, w⟩).2) := by
  obtain ⟨xi, rfl⟩ := (ManifoldTotalSpace.homeomorph F V).surjective i
  rw [ManifoldTotalSpace.proj_homeomorph] at hbi ⊢
  have hl := (trivializationAt F V xi.proj).linear 𝕜 hbi
  rw [ManifoldTotalSpace.extChartAt_homeomorph_apply,
    (trivializationAt F V xi.proj).coe_fst' (x := ⟨z.proj, z.snd + t • w⟩) hbi, hl.map_add,
    hl.map_smul]
  simp

private theorem hasFDerivAt_extChartAt_homeomorph_mk_add_smul {i z : ManifoldTotalSpace F V}
    (hbi : z.proj ∈ (trivializationAt F V i.proj).baseSet) (w : V z.proj) :
    HasFDerivAt
      (fun t : 𝕜 ↦
        extChartAt (IB.prod 𝓘(𝕜, F)) i
          (ManifoldTotalSpace.homeomorph F V ⟨z.proj, z.snd + t • w⟩))
      (ContinuousLinearMap.toSpanSingleton 𝕜
        ((0 : EB), (trivializationAt F V i.proj ⟨z.proj, w⟩).2)) 0 := by
  simp_rw [extChartAt_homeomorph_mk_add_smul (IB := IB) hbi w]
  exact (HasDerivAt.prodMk (hasDerivAt_const (0 : 𝕜) _)
    (by simpa only [one_smul] using
      ((hasDerivAt_id' (0 : 𝕜)).smul_const _).const_add _)).hasFDerivAt

/-- Differentiating the affine fibre curve `t ↦ homeomorph F V ⟨z.proj, z.snd + t • w⟩` at `t = 0`
yields the vertical lift `verticalLift IB z w` inside `TangentSpace (IB.prod 𝓘(𝕜, F)) z`. -/
theorem hasMFDerivAt_homeomorph_mk_add_smul (z : ManifoldTotalSpace F V) (w : V z.proj) :
    HasMFDerivAt 𝓘(𝕜) (IB.prod 𝓘(𝕜, F))
      (fun t : 𝕜 ↦ ManifoldTotalSpace.homeomorph F V ⟨z.proj, z.snd + t • w⟩) 0
      (ContinuousLinearMap.smulRight
        (tangentSpaceCastModel 𝓘(𝕜) (0 : 𝕜)).toContinuousLinearMap
        (verticalLift IB z w : TangentSpace (IB.prod 𝓘(𝕜, F)) z)) := by
  have hb := mem_baseSet_trivializationAt F V z.proj
  set γ : 𝕜 → ManifoldTotalSpace F V := fun t ↦
    ManifoldTotalSpace.homeomorph F V ⟨z.proj, z.snd + t • w⟩
  set v₀ := (trivializationAt F V z.proj ⟨z.proj, z.snd⟩).2
  set v₁ := (trivializationAt F V z.proj ⟨z.proj, w⟩).2
  -- Step 1: continuity of `γ` at `0` via linearity of the preferred trivialization.
  have hlin (t : 𝕜) : (trivializationAt F V z.proj ⟨z.proj, z.snd + t • w⟩).2 = v₀ + t • v₁ := by
    have hl := (trivializationAt F V z.proj).linear 𝕜 hb; rw [hl.map_add, hl.map_smul]
  have hcont : ContMDiffAt 𝓘(𝕜) (IB.prod 𝓘(𝕜, F)) 0 γ 0 := by
    refine ManifoldTotalSpace.contMDiffAt_iff.2 ⟨contMDiffAt_const, ?_⟩
    dsimp only [γ]; simp_rw [hlin]
    exact contMDiffAt_const.add (contMDiffAt_id.smul contMDiffAt_const)
  have hγ0 : γ 0 = z := by
    simp only [γ, zero_smul, add_zero, ← ManifoldTotalSpace.homeomorph_symm_apply,
      Homeomorph.apply_symm_apply]
  -- Step 2: translate the target continuous linear map into model coordinates `EB × F`.
  have hw_coord : modelEquivAt (IB := IB) z (verticalLift IB z w) = v₁ := by
    rw [modelEquivAt_verticalLift,
      (trivializationAt F V z.proj).continuousLinearMapAt_apply_of_mem (R := 𝕜) hb]
  have hmap : ((tangentSpaceCastModel (IB.prod 𝓘(𝕜, F)) (γ 0) :
        TangentSpace (IB.prod 𝓘(𝕜, F)) (γ 0) →L[𝕜] EB × F) ∘L
      ContinuousLinearMap.smulRight
        (tangentSpaceCastModel 𝓘(𝕜) (0 : 𝕜)).toContinuousLinearMap
        (verticalLift IB z w : TangentSpace (IB.prod 𝓘(𝕜, F)) z) ∘L
      ((tangentSpaceCastModel 𝓘(𝕜) (0 : 𝕜)).symm : 𝕜 →L[𝕜] TangentSpace 𝓘(𝕜) (0 : 𝕜))) =
      ContinuousLinearMap.toSpanSingleton 𝕜 ((0 : EB), v₁) := by
    refine ContinuousLinearMap.ext fun c ↦ ?_
    let u : TangentSpace (IB.prod 𝓘(𝕜, F)) z :=
      ContinuousLinearMap.smulRight
        (tangentSpaceCastModel 𝓘(𝕜) (0 : 𝕜)).toContinuousLinearMap
        (verticalLift IB z w : TangentSpace (IB.prod 𝓘(𝕜, F)) z)
        ((tangentSpaceCastModel 𝓘(𝕜) (0 : 𝕜)).symm c)
    refine (TauCeti.Manifold.tangentSpaceCastModel_apply (IB.prod 𝓘(𝕜, F)) (γ 0) u).trans <|
      (TauCeti.Manifold.tangentSpaceCastModel_apply (IB.prod 𝓘(𝕜, F)) z u).symm.trans ?_
    dsimp only [u]
    rw [ContinuousLinearMap.smulRight_apply, ContinuousLinearEquiv.coe_coe,
      ContinuousLinearEquiv.apply_symm_apply, map_smul, ContinuousLinearMap.toSpanSingleton_apply]
    exact congrArg (c • ·) (Prod.ext (VerticalSpace.tangentSpaceCastModel_coe_fst z _) hw_coord)
  -- Step 3: compute the chart derivative via `hasFDerivAt_extChartAt_homeomorph_mk_add_smul`.
  refine ⟨hcont.continuousAt, ?_⟩
  rw [hmap, writtenInExtChartAt, hγ0, extChartAt_model_space_eq_id, PartialEquiv.refl_symm,
    PartialEquiv.refl_coe, id_eq]
  exact (hasFDerivAt_extChartAt_homeomorph_mk_add_smul (IB := IB) hb w).hasFDerivWithinAt

/-- In any preferred chart `i` of `ManifoldTotalSpace F V` containing `z`, `verticalLift IB z`
agrees in vertical coordinates with the vector-bundle trivialization at `i.proj` — not only at
`i = z`. -/
theorem continuousLinearMapAt_verticalLift [IsManifold IB 1 B] [ContMDiffVectorBundle 1 F V IB]
    {i z : ManifoldTotalSpace F V} (hi : z ∈ (chartAt (ModelProd HB F) i).source)
    (w : V z.proj) :
    (trivializationAt F (VerticalSpace IB 𝓘(𝕜, F) F V) i).continuousLinearMapAt 𝕜 z
        (verticalLift IB z w) =
      (trivializationAt F V i.proj).continuousLinearMapAt 𝕜 z.proj w := by
  have hbi := (ManifoldTotalSpace.proj_mem_of_mem_chartAt_source hi).1
  have h0eq : ManifoldTotalSpace.homeomorph F V ⟨z.proj, z.snd + (0 : 𝕜) • w⟩ = z := by
    simp only [zero_smul, add_zero, ← ManifoldTotalSpace.homeomorph_symm_apply,
      Homeomorph.apply_symm_apply]
  have hcomp := ((mdifferentiableAt_extChartAt (I := IB.prod 𝓘(𝕜, F))
    (h0eq.symm ▸ hi)).hasMFDerivAt.comp 0
      (hasMFDerivAt_homeomorph_mk_add_smul (IB := IB) z w)).2
  rw [writtenInExtChartAt_model_space, modelWithCornersSelf_coe, range_id,
    extChartAt_model_space_eq_id, PartialEquiv.refl_coe, id_eq, hasFDerivWithinAt_univ] at hcomp
  have huniq := DFunLike.congr_fun
    (hcomp.unique (hasFDerivAt_extChartAt_homeomorph_mk_add_smul (IB := IB) hbi w)) (1 : 𝕜)
  simp only [comp_apply, ContinuousLinearEquiv.coe_coe, toSpanSingleton_apply,
    TauCeti.Manifold.tangentSpaceCastModel_apply, one_smul] at huniq
  rw [h0eq, ← TangentBundle.continuousLinearMapAt_trivializationAt hi] at huniq
  simp only [smulRight_apply, ContinuousLinearEquiv.coe_coe,
    ContinuousLinearEquiv.apply_symm_apply, one_smul] at huniq
  rw [(trivializationAt F (VerticalSpace IB 𝓘(𝕜, F) F V) i).continuousLinearMapAt_apply_of_mem
      (R := 𝕜) hi,
    (trivializationAt F V i.proj).continuousLinearMapAt_apply_of_mem (R := 𝕜) hbi,
    trivializationAt_apply]
  exact congrArg Prod.snd huniq

end VerticalSpace
end TauCeti

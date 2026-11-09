/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.SmoothEmbedding
public import Mathlib.Geometry.Manifold.VectorBundle.Basic
public import TauCeti.Topology.VectorBundle.Subbundle
import Mathlib.Geometry.Manifold.Algebra.LieGroup
import Mathlib.Geometry.Manifold.Notation
import TauCeti.Analysis.Normed.Module.FiniteDimension
import TauCeti.Analysis.Normed.Operator.QuotientRange
import TauCeti.Geometry.Manifold.ContMDiff.FiniteDimension
import TauCeti.Geometry.Manifold.ContMDiff.LeftInverse
import TauCeti.Geometry.Manifold.ContMDiff.NormedSpace
import TauCeti.Geometry.Manifold.Immersion.LocalDiffeomorph
import TauCeti.Geometry.Manifold.LocalDiffeomorph.FiberwiseLinear
import TauCeti.Geometry.Manifold.SmoothEmbedding.Extension
import TauCeti.Geometry.Manifold.VectorBundle.Trivialization

/-!
# Subbundles spanned by smooth local frames, and subbundle inclusions

Let `𝕜 → 𝕜'` be a normed field extension, and let `E` be a `C^n` bundle over a `𝕜`-manifold
`B`, with compatible `𝕜`- and `𝕜'`-vector bundle structures on the same atlas and model fibre
`F`. Let `V` assign to every point `x` a `𝕜'`-subspace `V x` of the fibre `E x`. A continuous
local frame `X` of `V` on an open
set `U` gives the local trivialization `TauCeti.IsSubbundleFrameOn.trivialization` of `V`, which
sends a vector of `V y` to its coordinates in the basis `X · y`; with the subspace topology, these
trivializations make `V` a topological vector bundle. This file shows that when the sections
`X i` are `C^n`, the coordinate changes between such trivializations are `C^n`. This is the
compatibility condition for the trivializations of `C^n` local frames to form a `C^n` vector
bundle structure on `V`, a `C^n` subbundle of `E`. When `V` has `C^n` local frames of a fixed
finite size near every point (`TauCeti.HasLocalContMDiffSubbundleFrames`), the atlas of all their
trivializations is such a structure
(`TauCeti.HasLocalContMDiffSubbundleFrames.contMDiffVectorBundle`). The distributions of a
manifold (`TauCeti.IsContMDiffDistribution.contMDiffVectorBundle`) and conormal bundles
(`TauCeti.CotangentBundle.conormalContMDiffVectorBundle`) are instances.

Read in a trivialization of `E` near a point `y₀`, a `C^n` frame `X` becomes a `C^n` family of
injective operators `A_X y : (𝕜')ᵏ →L[𝕜'] F`, namely `c ↦ ∑ i, c i • X i y`
(`TauCeti.IsSubbundleFrameOn.contMDiffAt_trivOperator`). Such a family has `C^n` left inverses
near `y₀` (`ContMDiffAt.exists_contMDiffAt_leftInverse`), and the coordinate change from the frame
`X` to a second frame `Y` is `L_Y y ∘ A_X y` for a `𝕜'`-linear left inverse `L_Y y` of
`A_Y y`. All smoothness is over the ground field `𝕜`. The finite-frame coordinate argument uses
`IsRCLikeNormedField 𝕜'` for Hahn–Banach splitting; it requires no finite rank of the ambient
fibre. In particular it applies to complex subbundles of real-smooth complex vector bundles
without assuming an ambient global trivialization. The native subspace topology, frame
trivializations and coordinate changes are unchanged.

Conversely, whenever a family of subspaces `V x ⊆ E (f x)` along `f : B' → B` carries a `C^n`
vector bundle structure with finite-dimensional model fibre `F'` inside a finite-dimensional model
fibre `F` and its canonical inclusion into `TotalSpace F E` is `C^n`, that inclusion has the
immersion normal form: over the same base `B` with no boundarylessness hypothesis
(`TauCeti.isImmersion_totalSpace_subbundle`, `TauCeti.isSmoothEmbedding_totalSpace_subbundle`), and
along an embedding `f : B' → B` of a boundaryless manifold `B'` into an arbitrary manifold `B`
(`TauCeti.isImmersion_lift_totalSpace_subbundle`,
`TauCeti.isSmoothEmbedding_lift_totalSpace_subbundle`). In bundle trivializations the fibrewise
inclusion is a `C^n` family of split injections `A x : F' →L[𝕜] F`; adjoining a fixed complement
`Q` produces a local `C^n` trivialization diffeomorphism straightening `V` to `F' × {0}`.

## Main results

* `TauCeti.IsSubbundleFrameOn.contMDiffAt_trivOperator`: `C^n` sections of `E`, read in a
  trivialization of `E`, form a `C^n` family of operators.
* `TauCeti.IsSubbundleFrameOn.contMDiffOn_coordChangeL`: the coordinate changes between the
  trivializations of two `C^n` local frames of `V` are `C^n` on the intersection of their domains.
* `TauCeti.HasLocalContMDiffSubbundleFrames.contMDiffVectorBundle`: **smooth local frame
  criterion**: a family of subspaces with `C^n` local frames of a fixed finite size near every
  point is a `C^n` subbundle of `E`.
* `TauCeti.IsSubbundleFrameOn.contMDiffAt_totalSpace_subbundle`: the canonical inclusion of a
  frame-trivialized `C^n` subbundle into `TotalSpace F E` is `C^n`.
* `TauCeti.isImmersion_totalSpace_subbundle`, `TauCeti.isSmoothEmbedding_totalSpace_subbundle`:
  a `C^n` vector subbundle over `B` whose canonical inclusion into `TotalSpace F E` is `C^n` is
  immersed (and, with the subspace topology, `C^n`-embedded) in `TotalSpace F E`.
* `TauCeti.isImmersion_lift_totalSpace_subbundle`,
  `TauCeti.isSmoothEmbedding_lift_totalSpace_subbundle`: the same for a `C^n` subbundle of `f *ᵖ E`
  lifted into `TotalSpace F E` along an embedding `f : B' → B` of a boundaryless manifold `B'`.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Springer GTM 218 (2013), Lemma 10.32
  and Proposition 10.34.
-/

public section

noncomputable section

open Set Filter Function Bundle Topology Module Manifold
open scoped Manifold ContDiff

namespace TauCeti.IsSubbundleFrameOn

variable {𝕜 𝕜' : Type*} [NontriviallyNormedField 𝕜] [NontriviallyNormedField 𝕜']
  [NormedAlgebra 𝕜 𝕜']
  {EB : Type*} [NormedAddCommGroup EB] [NormedSpace 𝕜 EB]
  {HB : Type*} [TopologicalSpace HB] {IB : ModelWithCorners 𝕜 EB HB}
  {B : Type*} [TopologicalSpace B] [ChartedSpace HB B]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] [NormedSpace 𝕜' F]
  [IsScalarTower 𝕜 𝕜' F] {E : B → Type*}
  [∀ x, AddCommMonoid (E x)] [∀ x, Module 𝕜 (E x)]
  [TopologicalSpace (TotalSpace F E)]
  [∀ x, TopologicalSpace (E x)] [FiberBundle F E] [VectorBundle 𝕜 F E]
  {n : ℕ∞ω} [ContMDiffVectorBundle n F E IB]
  {ι : Type*} [Fintype ι]

/-- A family of sections `X i` of `E` that are `C^n` at `y`, read in the trivialization of `E` at
any point `y₀` whose base set contains `y`, is an operator `c ↦ ∑ i, c i • X i` depending `C^n`
over `𝕜` on the base point at `y`, retaining its `𝕜'`-linear coefficients. -/
theorem contMDiffAt_trivOperator {X : ι → Π x, E x} {y₀ y : B}
    (hX : ∀ i, CMDiffAt n (T% (X i)) y) (hy : y ∈ (trivializationAt F E y₀).baseSet) :
    ContMDiffAt IB 𝓘(𝕜, (ι → 𝕜') →L[𝕜'] F) n (trivOperator 𝕜' F X y₀) y := by
  have h (i : ι) := ((trivializationAt F E y₀).contMDiffAt_section_iff hy).mp (hX i)
  rw [funext (trivOperator_eq_sum (𝕜 := 𝕜') (F := F) (X := X) y₀)]
  exact contMDiffAt_finsetSum fun i _ ↦ ((ContinuousLinearMap.smulRightL 𝕜' (ι → 𝕜') F
    (ContinuousLinearMap.proj i)).restrictScalars 𝕜 |>.contDiff.contDiffAt).comp_contMDiffAt (h i)

variable [∀ x, Module 𝕜' (E x)] [VectorBundle 𝕜' F E]
  {V : Π x, Submodule 𝕜' (E x)} [IsRCLikeNormedField 𝕜']

/-- **Coordinate changes between `C^n` local frames are `C^n`.** If `X` and `Y` are local frames
of `V` on open sets `U` and `U'` whose sections are `C^n`, then the coordinate change from the
trivialization of `X` to that of `Y` is a `C^n` family of `𝕜'`-linear operators over the ground
field `𝕜` on `U ∩ U'`. The finite frame may span a subspace of an infinite-dimensional ambient
fibre. -/
theorem contMDiffOn_coordChangeL {X Y : ι → Π x, E x} {U U' : Set B}
    (hX : IsSubbundleFrameOn F V X U) (hU : IsOpen U) (hXn : ∀ i, CMDiff[U] n (T% (X i)))
    (hY : IsSubbundleFrameOn F V Y U') (hU' : IsOpen U') (hYn : ∀ i, CMDiff[U'] n (T% (Y i))) :
    letI := subbundleTopology F (F' := ι → 𝕜') V
    ContMDiffOn IB 𝓘(𝕜, (ι → 𝕜') →L[𝕜'] ι → 𝕜') n
      (fun y ↦ ((hX.trivialization hU).coordChangeL 𝕜' (hY.trivialization hU') y :
        (ι → 𝕜') →L[𝕜'] ι → 𝕜')) (U ∩ U') := by
  let := subbundleTopology F (F' := ι → 𝕜') V
  have : CompleteSpace 𝕜' := by
    let := IsRCLikeNormedField.rclike 𝕜'
    infer_instance
  intro y₀ hy₀
  refine ContMDiffAt.contMDiffWithinAt ?_
  have hy₀e := FiberBundle.mem_baseSet_trivializationAt' (F := F) (E := E) y₀
  have hAX := contMDiffAt_trivOperator (𝕜 := 𝕜) (𝕜' := 𝕜') (y₀ := y₀)
    (fun i ↦ (hXn i).contMDiffAt (hU.mem_nhds hy₀.1)) hy₀e
  have hAY := contMDiffAt_trivOperator (𝕜 := 𝕜) (𝕜' := 𝕜') (y₀ := y₀)
    (fun i ↦ (hYn i).contMDiffAt (hU'.mem_nhds hy₀.2)) hy₀e
  -- Coordinates in `Y` are recovered from the vector read in the trivialization of `E` by a
  -- `C^n` left inverse of the frame operator of `Y`.
  obtain ⟨L, hL, hLinv⟩ := hAY.exists_contMDiffAt_leftInverse
    (.of_injective_of_finiteDimensional_domain (hY.injective_trivOperator hy₀.2))
  have hcomp : ContMDiffAt IB 𝓘(𝕜, (ι → 𝕜') →L[𝕜'] ι → 𝕜') n
      (fun y ↦ (L y).comp (trivOperator 𝕜' F X y₀ y)) y₀ :=
    ((ContinuousLinearMap.compL 𝕜' (ι → 𝕜') F (ι → 𝕜')).bilinearRestrictScalars 𝕜)
      |>.isBoundedBilinearMap.contDiff.comp_contMDiffAt (hL.prodMk_space hAX)
  refine hcomp.congr_of_eventuallyEq ?_
  filter_upwards [hLinv, (hU.inter hU').mem_nhds hy₀,
    (trivializationAt F E y₀).open_baseSet.mem_nhds hy₀e] with y hyL hy hye
  ext1 c
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
    (hX.trivialization hU).coordChangeL_apply' (R := 𝕜') (hY.trivialization hU')
      (by simpa only [trivialization_baseSet] using hy),
    trivialization_symm_apply hX hU (q := (y, c)) hy.1]
  rw [trivialization_apply hY hU' (p := TotalSpace.mk' (ι → 𝕜') (E := fun x ↦ V x) y _) hy.2]
  -- The coordinates `d` of the vector in `Y` and its coordinates `c` in `X` describe the same
  -- vector of `E y`, so the frame operators of `Y` and of `X` send them to the same point.
  set d := (hY.basis hy.2).equivFun ((hX.basis hy.1).equivFun.symm c)
  have hd : ∑ i, d i • Y i y = ∑ i, c i • X i y := by
    rw [← coe_basis_equivFun_symm hY hy.2, ← coe_basis_equivFun_symm hX hy.1,
      LinearEquiv.symm_apply_apply]
  rw [← hyL d, trivOperator_apply hye, trivOperator_apply hye, hd]

variable [∀ x, IsScalarTower 𝕜 𝕜' (E x)]

/-- **The canonical inclusion of a frame-trivialized subbundle is `C^n`.** At any point `p` in the
domain `U` of a `C^n` local frame `X` whose trivialization belongs to the bundle atlas of `V`, the
canonical inclusion `(x, v) ↦ (x, ↑v)` from `TotalSpace (ι → 𝕜') (fun x ↦ V x)` into
`TotalSpace F E` is `C^n` over the ground field `𝕜`, with its original scalar structures. -/
theorem contMDiffAt_totalSpace_subbundle {X : ι → Π x, E x} {U : Set B}
    (hX : IsSubbundleFrameOn F V X U) (hU : IsOpen U) (hXn : ∀ i, CMDiff[U] n (T% (X i)))
    [letI := subbundleTopology F (F' := ι → 𝕜') V; FiberBundle (ι → 𝕜') (fun x ↦ V x)]
    [letI := subbundleTopology F (F' := ι → 𝕜') V; VectorBundle 𝕜 (ι → 𝕜') (fun x ↦ V x)]
    [letI := subbundleTopology F (F' := ι → 𝕜') V;
      ContMDiffVectorBundle n (ι → 𝕜') (fun x ↦ V x) IB]
    [letI := subbundleTopology F (F' := ι → 𝕜') V; MemTrivializationAtlas (hX.trivialization hU)]
    {p : TotalSpace (ι → 𝕜') (fun x ↦ V x)} (hp : p.proj ∈ U) :
    letI := subbundleTopology F (F' := ι → 𝕜') V
    ContMDiffAt (IB.prod 𝓘(𝕜, ι → 𝕜')) (IB.prod 𝓘(𝕜, F)) n
      (fun q : TotalSpace (ι → 𝕜') (fun x ↦ V x) ↦ (⟨q.proj, q.2⟩ : TotalSpace F E)) p := by
  let := subbundleTopology F (F' := ι → 𝕜') V
  have hproj : ContMDiffAt (IB.prod 𝓘(𝕜, ι → 𝕜')) IB n
      (fun q : TotalSpace (ι → 𝕜') (fun x ↦ V x) ↦ q.proj) p :=
    (Bundle.contMDiff_proj (fun x ↦ V x)).contMDiffAt
  rw [Bundle.contMDiffAt_totalSpace]
  refine ⟨hproj, ?_⟩
  have hpE := FiberBundle.mem_baseSet_trivializationAt' (F := F) (E := E) p.proj
  have hA := (contMDiffAt_trivOperator (𝕜 := 𝕜) (𝕜' := 𝕜') (y₀ := p.proj)
    (fun i ↦ (hXn i).contMDiffAt (hU.mem_nhds hp)) hpE).comp p hproj
  let eV := hX.trivialization hU
  have hpV : p ∈ eV.source := eV.mem_source.mpr (by simpa [eV] using hp)
  have hcoord : ContMDiffAt (IB.prod 𝓘(𝕜, ι → 𝕜')) 𝓘(𝕜, ι → 𝕜') n (fun q ↦ (eV q).2) p :=
    ((eV.contMDiffOn (IB := IB) (n := n)).contMDiffAt (eV.open_source.mem_nhds hpV)).snd
  have hA' : ContMDiffAt (IB.prod 𝓘(𝕜, ι → 𝕜')) 𝓘(𝕜, (ι → 𝕜') →L[𝕜] F) n
      (fun q ↦ (trivOperator 𝕜' F X p.proj q.proj).restrictScalars 𝕜) p :=
    (ContinuousLinearMap.restrictScalarsIsometry 𝕜' (ι → 𝕜') F 𝕜 𝕜).toContinuousLinearMap
      |>.contDiff.comp_contMDiffAt hA
  refine (hA'.clm_apply hcoord).congr_of_eventuallyEq ?_
  filter_upwards [eV.open_source.mem_nhds hpV,
    hproj.continuousAt.preimage_mem_nhds
      ((trivializationAt F E p.proj).open_baseSet.mem_nhds hpE)] with q hqV hqE
  have hqU : q.proj ∈ U := by simpa [eV] using eV.mem_source.mp hqV
  dsimp only [Function.comp_apply, eV]
  rw [trivialization_apply hX hU hqU, ContinuousLinearMap.coe_restrictScalars',
    trivOperator_apply hqE, ← coe_basis_equivFun_symm hX hqU,
    LinearEquiv.symm_apply_apply]

end TauCeti.IsSubbundleFrameOn

namespace TauCeti

section ContMDiffFrames

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {EB : Type*} [NormedAddCommGroup EB] [NormedSpace 𝕜 EB]
  {HB : Type*} [TopologicalSpace HB] {IB : ModelWithCorners 𝕜 EB HB}
  {B : Type*} [TopologicalSpace B] [ChartedSpace HB B] {n : ℕ∞ω}
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] {E : B → Type*}
  [∀ x, AddCommMonoid (E x)] [∀ x, Module 𝕜 (E x)] [TopologicalSpace (TotalSpace F E)]
  [∀ x, TopologicalSpace (E x)] [FiberBundle F E] {ι : Type*}

variable (IB n F ι) in
/-- Every point of the base has an open neighbourhood carrying a local frame of the family of
subspaces `V`, indexed by `ι`, whose members are `C^n` sections of `E`. Over `ℝ` or `ℂ`, when `ι`
is finite and `E` is a `C^n` vector bundle, such a family, with the subspace topology, is a `C^n`
vector bundle with model fibre `ι → 𝕜`, a `C^n` subbundle of `E`
(`TauCeti.HasLocalContMDiffSubbundleFrames.contMDiffVectorBundle`). -/
def HasLocalContMDiffSubbundleFrames (V : Π x, Submodule 𝕜 (E x)) : Prop :=
  ∀ x, ∃ U : Set B, IsOpen U ∧ x ∈ U ∧
    ∃ X : ι → Π x, E x, IsSubbundleFrameOn F V X U ∧ ∀ i, CMDiff[U] n (T% (X i))

variable {V : Π x, Submodule 𝕜 (E x)}

/-- Unfolding `TauCeti.HasLocalContMDiffSubbundleFrames`. -/
theorem hasLocalContMDiffSubbundleFrames_iff :
    HasLocalContMDiffSubbundleFrames IB n F ι V ↔
      ∀ x, ∃ U : Set B, IsOpen U ∧ x ∈ U ∧
        ∃ X : ι → Π x, E x, IsSubbundleFrameOn F V X U ∧ ∀ i, CMDiff[U] n (T% (X i)) :=
  Iff.rfl

namespace HasLocalContMDiffSubbundleFrames

/-- `C^n` local frames are in particular continuous local frames. -/
theorem hasLocalSubbundleFrames (hV : HasLocalContMDiffSubbundleFrames IB n F ι V) :
    HasLocalSubbundleFrames F ι V :=
  hasLocalSubbundleFrames_iff.mpr fun x ↦ by
    obtain ⟨U, hU, hx, X, hX, -⟩ := hV x
    exact ⟨U, hU, hx, X, hX⟩

/-- `C^n` local frames are `C^m` local frames for every `m ≤ n`. -/
theorem of_le {m : ℕ∞ω} (hV : HasLocalContMDiffSubbundleFrames IB n F ι V) (hmn : m ≤ n) :
    HasLocalContMDiffSubbundleFrames IB m F ι V := fun x ↦ by
  obtain ⟨U, hU, hx, X, hX, hXn⟩ := hV x
  exact ⟨U, hU, hx, X, hX, fun i ↦ (hXn i).of_le hmn⟩

variable [VectorBundle 𝕜 F E] [IsRCLikeNormedField 𝕜]

/-- A family of subspaces with `C^n` local frames indexed by a finite type `ι` near every point is
a fibre bundle with fibre `ι → 𝕜`, the topology of its total space being that of a subspace of the
total space of `E`. Its trivializations are those of all `C^n` local frames of `V` on open sets
(`TauCeti.IsSubbundleFrameOn.trivialization`). Use this definition as a local instance; it chooses
a local frame near every point. -/
@[instance_reducible]
def fiberBundle [Finite ι] (hV : HasLocalContMDiffSubbundleFrames IB n F ι V) :
    letI := subbundleTopology F (F' := ι → 𝕜) V
    FiberBundle (ι → 𝕜) fun x ↦ V x :=
  letI := subbundleTopology F (F' := ι → 𝕜) V
  let U := fun x ↦ (hV x).choose
  have hU := fun x ↦ (hV x).choose_spec
  let X := fun x ↦ (hU x).2.2.choose
  have hX := fun x ↦ (hU x).2.2.choose_spec
  { totalSpaceMk_isInducing' := isInducing_totalSpaceMk_subbundle F (ι → 𝕜) V
    trivializationAtlas' :=
      {e | ∃ (U : Set B) (hU : IsOpen U) (Y : ι → Π x, E x) (hY : IsSubbundleFrameOn F V Y U),
        (∀ i, CMDiff[U] n (T% (Y i))) ∧ hY.trivialization hU = e}
    trivializationAt' := fun x ↦ (hX x).1.trivialization (hU x).1
    mem_baseSet_trivializationAt' := fun x ↦ by
      rw [IsSubbundleFrameOn.trivialization_baseSet]
      exact (hU x).2.1
    trivialization_mem_atlas' := fun x ↦ ⟨U x, (hU x).1, X x, (hX x).1, (hX x).2, rfl⟩ }

/-- The trivializations of `hV.fiberBundle` are the trivializations of the `C^n` local frames of
`V` on open sets. -/
theorem mem_trivializationAtlas_fiberBundle_iff [Finite ι]
    (hV : HasLocalContMDiffSubbundleFrames IB n F ι V)
    (e : letI := subbundleTopology F (F' := ι → 𝕜) V
      Trivialization (ι → 𝕜) (π (ι → 𝕜) fun x ↦ V x)) :
    letI := subbundleTopology F (F' := ι → 𝕜) V
    letI := hV.fiberBundle
    e ∈ trivializationAtlas (ι → 𝕜) (fun x ↦ V x) ↔
      ∃ (U : Set B) (hU : IsOpen U) (Y : ι → Π x, E x) (hY : IsSubbundleFrameOn F V Y U),
        (∀ i, CMDiff[U] n (T% (Y i))) ∧ hY.trivialization hU = e :=
  Iff.rfl

/-- A family of subspaces with `C^n` local frames indexed by a finite type `ι` near every point,
with the subspace topology of the total space of `E` and the atlas of `hV.fiberBundle`, is a
topological vector bundle with model fibre `ι → 𝕜`. -/
theorem vectorBundle [Fintype ι] (hV : HasLocalContMDiffSubbundleFrames IB n F ι V) :
    letI := subbundleTopology F (F' := ι → 𝕜) V
    letI := hV.fiberBundle
    VectorBundle 𝕜 (ι → 𝕜) fun x ↦ V x :=
  vectorBundle_of_forall_mem_trivializationAtlas hV.fiberBundle fun e he ↦ by
    obtain ⟨U, hU, Y, hY, -, rfl⟩ := (mem_trivializationAtlas_fiberBundle_iff hV e).mp he
    exact ⟨U, hU, Y, hY, rfl⟩

/-- **Smooth local frame criterion for subbundles.** If `E` is a `C^n` vector bundle and the
family of subspaces `V` has `C^n` local frames indexed by a finite type `ι` near every point, then
`V`, with the subspace topology of the total space of `E` and the atlas of `hV.fiberBundle`, is a
`C^n` vector bundle with model fibre `ι → 𝕜`: a `C^n` subbundle of `E`. -/
theorem contMDiffVectorBundle [Fintype ι] [ContMDiffVectorBundle n F E IB]
    (hV : HasLocalContMDiffSubbundleFrames IB n F ι V) :
    letI := subbundleTopology F (F' := ι → 𝕜) V
    letI := hV.fiberBundle
    letI := hV.vectorBundle
    ContMDiffVectorBundle n (ι → 𝕜) (fun x ↦ V x) IB := by
  let := subbundleTopology F (F' := ι → 𝕜) V
  let := hV.fiberBundle
  let := hV.vectorBundle
  refine ⟨fun e e' he he' ↦ ?_⟩
  obtain ⟨U, hU, Y, hY, hYn, rfl⟩ := (mem_trivializationAtlas_fiberBundle_iff hV e).mp he.out
  obtain ⟨U', hU', Y', hY', hYn', rfl⟩ := (mem_trivializationAtlas_fiberBundle_iff hV e').mp he'.out
  simpa only [IsSubbundleFrameOn.trivialization_baseSet] using
    hY.contMDiffOn_coordChangeL hU hYn hY' hU' hYn'

end HasLocalContMDiffSubbundleFrames

end ContMDiffFrames

section SubbundleInclusion

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  {EB : Type*} [NormedAddCommGroup EB] [NormedSpace 𝕜 EB]
  {HB : Type*} [TopologicalSpace HB] {IB : ModelWithCorners 𝕜 EB HB}
  {B : Type*} [TopologicalSpace B] [ChartedSpace HB B]
  {EB' : Type*} [NormedAddCommGroup EB'] [NormedSpace 𝕜 EB']
  {HB' : Type*} [TopologicalSpace HB'] {IB' : ModelWithCorners 𝕜 EB' HB'}
  {B' : Type*} [TopologicalSpace B'] [ChartedSpace HB' B']
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {F' : Type*} [NormedAddCommGroup F'] [NormedSpace 𝕜 F']
  {E : B → Type*} [∀ x, AddCommMonoid (E x)] [∀ x, Module 𝕜 (E x)]
  [TopologicalSpace (TotalSpace F E)] [∀ x, TopologicalSpace (E x)]
  [FiberBundle F E] [VectorBundle 𝕜 F E]
  {n : ℕ∞ω} [ContMDiffVectorBundle n F E IB]

omit [CompleteSpace 𝕜] in
/-- For a fixed vector `w : F'`, reading `x ↦ (f x, eV.symm x w)` in the ambient trivialization `eE`
at `f x₀` gives a `C^n` map on `eV.baseSet ∩ f ⁻¹' eE.baseSet`. -/
private theorem contMDiffOn_subbundleCoord_apply
    {f : B' → B} {V : Π x : B', Submodule 𝕜 (E (f x))}
    [TopologicalSpace (TotalSpace F' (fun x ↦ V x))] [FiberBundle F' (fun x ↦ V x)]
    [VectorBundle 𝕜 F' (fun x ↦ V x)] [ContMDiffVectorBundle n F' (fun x ↦ V x) IB']
    (hinc : ContMDiff (IB'.prod 𝓘(𝕜, F')) (IB.prod 𝓘(𝕜, F)) n
      (fun p : TotalSpace F' (fun x ↦ V x) ↦ (⟨f p.proj, p.2⟩ : TotalSpace F E)))
    (x₀ : B') (w : F') :
    let eV := trivializationAt F' (fun x ↦ V x) x₀
    let eE := trivializationAt F E (f x₀)
    ContMDiffOn IB' 𝓘(𝕜, F) n
      (fun x ↦ (eE ⟨f x, ((eV.symm x w : V x) : E (f x))⟩).2)
      (eV.baseSet ∩ f ⁻¹' eE.baseSet) := by
  intro eV eE x hx
  have hxV : (x, w) ∈ eV.target := eV.mem_target.mpr hx.1
  have hsecV : ContMDiffAt IB' (IB'.prod 𝓘(𝕜, F')) n
      (fun y ↦ (⟨y, eV.symm y w⟩ : TotalSpace F' (fun x ↦ V x))) x := by
    have hsymm := (eV.contMDiffOn_symm (IB := IB') (n := n)).contMDiffAt
      (eV.open_target.mem_nhds hxV)
    refine (hsymm.comp x (contMDiffAt_id.prodMk contMDiffAt_const)).congr_of_eventuallyEq ?_
    filter_upwards [eV.open_baseSet.mem_nhds hx.1] with y hy
    exact eV.mk_symm hy w
  have hincAt : ContMDiffAt IB' (IB.prod 𝓘(𝕜, F)) n
      (fun y ↦ (⟨f y, ((eV.symm y w : V y) : E (f y))⟩ : TotalSpace F E)) x :=
    (hinc _).comp x hsecV
  have hxE : (⟨f x, ((eV.symm x w : V x) : E (f x))⟩ : TotalSpace F E) ∈ eE.source :=
    eE.mem_source.mpr hx.2
  exact (((eE.contMDiffOn (IB := IB) (n := n)).contMDiffAt
    (eE.open_source.mem_nhds hxE) |>.comp x hincAt).snd).contMDiffWithinAt

/-- Expressing a `C^n` fibrewise subspace inclusion `V x ⊆ E (f x)` in the preferred bundle
trivializations at `x₀` and `f x₀` yields a `C^n` family of continuous linear maps `F' →L[𝕜] F` on
the overlap of their base sets, injective at `x₀`. -/
private theorem exists_contMDiffOn_subbundleCoord [FiniteDimensional 𝕜 F']
    {f : B' → B} {V : Π x : B', Submodule 𝕜 (E (f x))}
    [TopologicalSpace (TotalSpace F' (fun x ↦ V x))] [FiberBundle F' (fun x ↦ V x)]
    [VectorBundle 𝕜 F' (fun x ↦ V x)] [ContMDiffVectorBundle n F' (fun x ↦ V x) IB']
    (hinc : ContMDiff (IB'.prod 𝓘(𝕜, F')) (IB.prod 𝓘(𝕜, F)) n
      (fun p : TotalSpace F' (fun x ↦ V x) ↦ (⟨f p.proj, p.2⟩ : TotalSpace F E)))
    (x₀ : B') :
    let eV := trivializationAt F' (fun x ↦ V x) x₀
    let eE := trivializationAt F E (f x₀)
    ∃ A : B' → F' →L[𝕜] F,
      ContMDiffOn IB' 𝓘(𝕜, F' →L[𝕜] F) n A (eV.baseSet ∩ f ⁻¹' eE.baseSet) ∧
      (∀ x ∈ eV.baseSet ∩ f ⁻¹' eE.baseSet, ∀ w : F',
        (eE ⟨f x, ((eV.symm x w : V x) : E (f x))⟩).2 = A x w) ∧
      Injective (A x₀) := by
  intro eV eE
  let U : Set B' := eV.baseSet ∩ f ⁻¹' eE.baseSet
  let subL (x : B') : V x →L[𝕜] E (f x) :=
    { toLinearMap := (V x).subtype, cont := continuous_subtype_val }
  let A : B' → F' →L[𝕜] F := fun x ↦
    ContinuousLinearMap.inCoordinates F' (fun x ↦ V x) F E x₀ x (f x₀) (f x) (subL x)
  have hAeq : ∀ x ∈ U, ∀ w : F', (eE ⟨f x, ((eV.symm x w : V x) : E (f x))⟩).2 = A x w := by
    intro x hx w
    simp only [A, ContinuousLinearMap.inCoordinates, ContinuousLinearMap.comp_apply, subL,
      Trivialization.continuousLinearMapAt_apply_of_mem (R := 𝕜) _ hx.2,
      (trivializationAt F' (fun x ↦ V x) x₀).symmL_apply hx.1, eE, eV]
    rfl
  refine ⟨A, fun x hx ↦ contMDiffWithinAt_clm_apply.mpr fun w ↦
    ((contMDiffOn_subbundleCoord_apply hinc x₀ w).congr fun y hy ↦ (hAeq y hy w).symm) x hx,
    hAeq, ?_⟩
  have hx₀V : x₀ ∈ eV.baseSet := FiberBundle.mem_baseSet_trivializationAt F' (fun x ↦ V x) x₀
  have hx₀E : f x₀ ∈ eE.baseSet := FiberBundle.mem_baseSet_trivializationAt F E (f x₀)
  dsimp only [A]
  rw [ContinuousLinearMap.inCoordinates_eq hx₀V hx₀E]
  exact (eE.continuousLinearEquivAt 𝕜 (f x₀) hx₀E).injective.comp
    (Subtype.val_injective.comp (eV.continuousLinearEquivAt 𝕜 x₀ hx₀V).symm.injective)

omit [CompleteSpace 𝕜] [ChartedSpace HB' B'] [VectorBundle 𝕜 F E]
  [ContMDiffVectorBundle n F E IB] in
/-- Over `eV.source ∩ proj ⁻¹' (f ⁻¹' W)`, composing `eV`, `Prod.map f inl₀`,
`fiberwiseLinearPartialDiffeomorph L hW hL hL_inv`, and `eE.symm` recovers the canonical lift
`q ↦ (f q.proj, ↑q.2)` whenever `L y (inl₀ w) = A (r y) w` on `W`. -/
private theorem symm_fiberwiseLinearPartialDiffeomorph_subbundle_eventuallyEq [CompleteSpace F]
    {f : B' → B} {V : Π x : B', Submodule 𝕜 (E (f x))}
    [TopologicalSpace (TotalSpace F' (fun x ↦ V x))] [∀ x, TopologicalSpace (V x)]
    [FiberBundle F' (fun x ↦ V x)]
    {p : TotalSpace F' (fun x ↦ V x)} (hf_cont : Continuous f)
    {r : B → B'} {W : Set B} (hW : IsOpen W) (hfpW : f p.proj ∈ W)
    (hWE : ∀ y ∈ W, y ∈ (trivializationAt F E (f p.proj)).baseSet)
    (hrW : ∀ q : B', f q ∈ W → r (f q) = q)
    {A : B' → F' →L[𝕜] F}
    (hAeq : ∀ x ∈ (trivializationAt F' (fun x ↦ V x) p.proj).baseSet ∩
        f ⁻¹' (trivializationAt F E (f p.proj)).baseSet, ∀ w : F',
      (trivializationAt F E (f p.proj)
        ⟨f x, (((trivializationAt F' (fun x ↦ V x) p.proj).symm x w : V x) : E (f x))⟩).2 =
        A x w)
    {inl₀ : F' → F} {L : B → F →L[𝕜] F}
    (hL : ContMDiffOn IB 𝓘(𝕜, F →L[𝕜] F) n L W)
    (hL_inv : ∀ y ∈ W, (L y).IsInvertible)
    (hL_inl : ∀ y ∈ W, ∀ w : F', L y (inl₀ w) = A (r y) w) :
    let eV := trivializationAt F' (fun x ↦ V x) p.proj
    let eE := trivializationAt F E (f p.proj)
    let Φ := fiberwiseLinearPartialDiffeomorph L hW hL hL_inv
    (⇑eE.toOpenPartialHomeomorph.symm ∘ ⇑Φ ∘ Prod.map f inl₀) ∘ ⇑eV =ᶠ[𝓝 p]
      fun q : TotalSpace F' (fun x ↦ V x) ↦ (⟨f q.proj, q.2⟩ : TotalSpace F E) := by
  intro eV eE Φ
  have hp_eV : p ∈ eV.source :=
    eV.mem_source.mpr (FiberBundle.mem_baseSet_trivializationAt F' (fun x ↦ V x) p.proj)
  have hmem : eV.source ∩ (fun q : TotalSpace F' (fun x ↦ V x) ↦ f q.proj) ⁻¹' W ∈ 𝓝 p :=
    (eV.open_source.inter (hW.preimage (hf_cont.comp (FiberBundle.continuous_proj F' _)))).mem_nhds
      ⟨hp_eV, hfpW⟩
  filter_upwards [hmem] with q ⟨hqV, hfqW⟩
  have hq_base : q.proj ∈ eV.baseSet := eV.mem_source.mp hqV
  have hfq_base : f q.proj ∈ eE.baseSet := hWE _ hfqW
  dsimp only [Function.comp_apply, Prod.map]
  have hΦq : Φ (f (eV q).1, inl₀ (eV q).2) = (f q.proj, A q.proj (eV q).2) := by
    rw [eV.coe_fst' hq_base, fiberwiseLinearPartialDiffeomorph_apply, hL_inl _ hfqW,
      hrW q.proj hfqW]
  rw [hΦq, ← hAeq q.proj ⟨hq_base, hfq_base⟩ (eV q).2, eV.symm_apply_apply_mk hq_base q.2]
  let zE : TotalSpace F E := ⟨f q.proj, q.2⟩
  rw [show (f q.proj, (eE zE).2) = eE zE from Prod.ext (eE.coe_fst' (x := zE) hfq_base).symm rfl]
  exact eE.toOpenPartialHomeomorph.left_inv (eE.mem_source.mpr hfq_base)

/-- Core normal-form construction for a `C^n` subbundle inclusion along a map `f : B' → B` admitting
a local `C^n` retraction near `f p.proj`. -/
private theorem exists_isImmersionAtOfComplement_subbundle_of_retraction
    [FiniteDimensional 𝕜 F] [FiniteDimensional 𝕜 F'] [IsManifold IB n B] [IsManifold IB' n B']
    {P : Type*} [NormedAddCommGroup P] [NormedSpace 𝕜 P]
    {f : B' → B} {V : Π x : B', Submodule 𝕜 (E (f x))}
    [TopologicalSpace (TotalSpace F' (fun x ↦ V x))] [FiberBundle F' (fun x ↦ V x)]
    [VectorBundle 𝕜 F' (fun x ↦ V x)] [ContMDiffVectorBundle n F' (fun x ↦ V x) IB']
    {p : TotalSpace F' (fun x ↦ V x)}
    (hf : IsImmersionAtOfComplement P IB' IB n f p.proj) (hf_cont : Continuous f)
    {Vr : Set B} (hVr : IsOpen Vr) (hfp : f p.proj ∈ Vr)
    {r : B → B'} (hr : ContMDiffOn IB IB' n r Vr) (hr_inv : ∀ x, f x ∈ Vr → r (f x) = x)
    (hinc : ContMDiff (IB'.prod 𝓘(𝕜, F')) (IB.prod 𝓘(𝕜, F)) n
      (fun q : TotalSpace F' (fun x ↦ V x) ↦ (⟨f q.proj, q.2⟩ : TotalSpace F E))) :
    ∃ (Q : Submodule 𝕜 F) (_ : Nonempty ((F' × Q) ≃L[𝕜] F)),
      IsImmersionAtOfComplement (P × Q) (IB'.prod 𝓘(𝕜, F')) (IB.prod 𝓘(𝕜, F)) n
        (fun q : TotalSpace F' (fun x ↦ V x) ↦ (⟨f q.proj, q.2⟩ : TotalSpace F E)) p := by
  have : CompleteSpace F := FiniteDimensional.complete 𝕜 F
  let eV := trivializationAt F' (fun x ↦ V x) p.proj
  let eE := trivializationAt F E (f p.proj)
  have hx₀V : p.proj ∈ eV.baseSet := FiberBundle.mem_baseSet_trivializationAt F' (fun x ↦ V x) _
  have hx₀E : f p.proj ∈ eE.baseSet := FiberBundle.mem_baseSet_trivializationAt F E _
  obtain ⟨A, hAU, hAeq, hAinj⟩ := exists_contMDiffOn_subbundleCoord hinc p.proj
  -- Pull `A` back along the local retraction `r` to obtain a `C^n` operator family on `B`.
  let W₀ : Set B := (Vr ∩ r ⁻¹' (eV.baseSet ∩ f ⁻¹' eE.baseSet)) ∩ eE.baseSet
  have hW₀ : IsOpen W₀ :=
    (hr.continuousOn.isOpen_inter_preimage hVr
      (eV.open_baseSet.inter (eE.open_baseSet.preimage hf_cont))).inter eE.open_baseSet
  have hfx₀W₀ : f p.proj ∈ W₀ :=
    ⟨⟨hfp, by rw [mem_preimage, hr_inv p.proj hfp]; exact ⟨hx₀V, hx₀E⟩⟩, hx₀E⟩
  have hAr : ContMDiffOn IB 𝓘(𝕜, F' →L[𝕜] F) n (fun y ↦ A (r y)) W₀ :=
    hAU.comp (hr.mono fun _ hy ↦ hy.1.1) fun _ hy ↦ hy.1.2
  obtain ⟨Q, _, VQ, hVQ, hfx₀VQ, hInv0⟩ :=
    (hAr.continuousOn.continuousAt (hW₀.mem_nhds hfx₀W₀)).exists_isInvertible_coprod_subtypeL
      (by rw [hr_inv p.proj hfp]; exact .of_injective_of_finiteDimensional hAinj)
  have hW : IsOpen (VQ ∩ W₀) := hVQ.inter hW₀
  have hfx₀W : f p.proj ∈ VQ ∩ W₀ := ⟨hfx₀VQ, hfx₀W₀⟩
  have hInv : ∀ y ∈ VQ ∩ W₀, ((A (r y)).coprod Q.subtypeL).IsInvertible := fun y hy ↦ hInv0 y hy.1
  obtain ⟨e₀, _⟩ := hInv (f p.proj) hfx₀W
  refine ⟨Q, ⟨e₀⟩, ?_⟩
  let L : B → F →L[𝕜] F := fun y ↦ ((A (r y)).coprod Q.subtypeL) ∘L (e₀.symm : F →L[𝕜] F' × Q)
  have hL : ContMDiffOn IB 𝓘(𝕜, F →L[𝕜] F) n L (VQ ∩ W₀) :=
    ((hAr.mono inter_subset_right).clm_coprod contMDiffOn_const).clm_comp contMDiffOn_const
  have hL_inv : ∀ y ∈ VQ ∩ W₀, (L y).IsInvertible :=
    fun y hy ↦ ContinuousLinearMap.isInvertible_comp_equiv.mpr (hInv y hy)
  let Φ := fiberwiseLinearPartialDiffeomorph L hW hL hL_inv
  let inl₀ : F' → F := fun w ↦ e₀ (w, 0)
  have hpV : eV p = (p.proj, (eV p).2) := Prod.ext (eV.coe_fst' hx₀V) rfl
  have hprod : IsImmersionAtOfComplement (P × Q) (IB'.prod 𝓘(𝕜, F')) (IB.prod 𝓘(𝕜, F)) n
      (Prod.map f inl₀) (eV p) :=
    hpV ▸ hf.prodMap (IsImmersionAtOfComplement.mk_of_continuousAt_of_extChartAt
      (e₀.continuous.comp (ContinuousLinearMap.inl 𝕜 F' Q).continuous).continuousAt
      e₀ fun _ _ ↦ rfl)
  have hΦ : IsLocalDiffeomorphAt (IB.prod 𝓘(𝕜, F)) (IB.prod 𝓘(𝕜, F)) n Φ
      (Prod.map f inl₀ (eV p)) :=
    PartialDiffeomorph.isLocalDiffeomorphAt (IB.prod 𝓘(𝕜, F)) (IB.prod 𝓘(𝕜, F)) n Φ
      (by simp [Φ, eV.coe_fst' hx₀V, hfx₀W])
  have heEsymm : IsLocalDiffeomorphAt (IB.prod 𝓘(𝕜, F)) (IB.prod 𝓘(𝕜, F)) n
      eE.toOpenPartialHomeomorph.symm (Φ (Prod.map f inl₀ (eV p))) :=
    eE.isLocalDiffeomorphAt_symm (eE.mem_target.mpr (by simp [Φ, eV.coe_fst' hx₀V, hx₀E]))
  exact (isImmersionAtOfComplement_comp_isLocalDiffeomorphAt
    (eV.isLocalDiffeomorphAt (eV.mem_source.mpr hx₀V))
    (isImmersionAtOfComplement_isLocalDiffeomorphAt_comp heEsymm
      (isImmersionAtOfComplement_isLocalDiffeomorphAt_comp hΦ hprod))).congr_of_eventuallyEq
    (symm_fiberwiseLinearPartialDiffeomorph_subbundle_eventuallyEq hf_cont hW hfx₀W
      (fun _ hy ↦ hy.2.2) (fun q hfq ↦ hr_inv q hfq.2.1.1) hAeq hL hL_inv fun _ _ _ ↦ by
        simp [L, inl₀])

omit [VectorBundle 𝕜 F E] [ContMDiffVectorBundle n F E IB] in
private theorem isImmersion_of_forall_exists_complement [FiniteDimensional 𝕜 F]
    {P : Type*} [NormedAddCommGroup P] [NormedSpace 𝕜 P]
    {f : B' → B} {V : Π x : B', Submodule 𝕜 (E (f x))}
    [TopologicalSpace (TotalSpace F' (fun x ↦ V x))] [∀ x, TopologicalSpace (V x)]
    [FiberBundle F' (fun x ↦ V x)]
    (h : ∀ p : TotalSpace F' (fun x ↦ V x),
      ∃ (Q : Submodule 𝕜 F) (_ : Nonempty ((F' × Q) ≃L[𝕜] F)),
        IsImmersionAtOfComplement (P × Q) (IB'.prod 𝓘(𝕜, F')) (IB.prod 𝓘(𝕜, F)) n
          (fun q : TotalSpace F' (fun x ↦ V x) ↦ (⟨f q.proj, q.2⟩ : TotalSpace F E)) p) :
    IsImmersion (IB'.prod 𝓘(𝕜, F')) (IB.prod 𝓘(𝕜, F)) n
      (fun q : TotalSpace F' (fun x ↦ V x) ↦ (⟨f q.proj, q.2⟩ : TotalSpace F E)) := by
  rcases isEmpty_or_nonempty (TotalSpace F' (fun x ↦ V x)) with _ | ⟨⟨p₀⟩⟩
  · exact IsImmersionOfComplement.isImmersion (F := PUnit.{1}) fun p ↦ isEmptyElim p
  obtain ⟨Q₀, ⟨e₀⟩, _⟩ := h p₀
  refine IsImmersionOfComplement.isImmersion (F := P × Q₀) fun p ↦ ?_
  obtain ⟨Q, ⟨e⟩, hp⟩ := h p
  obtain ⟨eQ⟩ := nonempty_continuousLinearEquiv_of_prod_continuousLinearEquiv e e₀
  exact hp.trans_F (ContinuousLinearEquiv.prodCongr (.refl 𝕜 P) eQ)

section SameBase

variable [FiniteDimensional 𝕜 F] [FiniteDimensional 𝕜 F'] [IsManifold IB n B]
  {V : Π x : B, Submodule 𝕜 (E x)}
  [TopologicalSpace (TotalSpace F' (fun x ↦ V x))] [FiberBundle F' (fun x ↦ V x)]
  [VectorBundle 𝕜 F' (fun x ↦ V x)] [ContMDiffVectorBundle n F' (fun x ↦ V x) IB]

/-- If `V` is a `C^n` vector subbundle of `E` over `B` whose canonical inclusion into
`TotalSpace F E` is `C^n`, that inclusion is a `C^n` immersion at every point. Neither `B` nor its
model need be boundaryless or finite-dimensional. -/
theorem isImmersionAt_totalSpace_subbundle
    (hinc : ContMDiff (IB.prod 𝓘(𝕜, F')) (IB.prod 𝓘(𝕜, F)) n
      (fun p : TotalSpace F' (fun x ↦ V x) ↦ (⟨p.proj, p.2⟩ : TotalSpace F E)))
    (p : TotalSpace F' (fun x ↦ V x)) :
    IsImmersionAt (IB.prod 𝓘(𝕜, F')) (IB.prod 𝓘(𝕜, F)) n
      (fun q : TotalSpace F' (fun x ↦ V x) ↦ (⟨q.proj, q.2⟩ : TotalSpace F E)) p := by
  obtain ⟨Q, _, h⟩ := exists_isImmersionAtOfComplement_subbundle_of_retraction
    (P := PUnit.{1}) (f := fun x ↦ x) (V := V) (IsImmersionOfComplement.id p.proj) continuous_id
    isOpen_univ (mem_univ _) contMDiffOn_id (fun _ _ ↦ rfl) hinc
  exact h.isImmersionAt

/-- If `V` is a `C^n` vector subbundle of `E` over `B` whose canonical inclusion into
`TotalSpace F E` is `C^n`, that inclusion is a `C^n` immersion. Neither `B` nor its model need be
boundaryless or finite-dimensional. -/
theorem isImmersion_totalSpace_subbundle
    (hinc : ContMDiff (IB.prod 𝓘(𝕜, F')) (IB.prod 𝓘(𝕜, F)) n
      (fun p : TotalSpace F' (fun x ↦ V x) ↦ (⟨p.proj, p.2⟩ : TotalSpace F E))) :
    IsImmersion (IB.prod 𝓘(𝕜, F')) (IB.prod 𝓘(𝕜, F)) n
      (fun q : TotalSpace F' (fun x ↦ V x) ↦ (⟨q.proj, q.2⟩ : TotalSpace F E)) :=
  isImmersion_of_forall_exists_complement (P := PUnit.{1}) (f := fun x ↦ x) (V := V) fun p ↦
    exists_isImmersionAtOfComplement_subbundle_of_retraction (IsImmersionOfComplement.id p.proj)
      continuous_id isOpen_univ (mem_univ _) contMDiffOn_id (fun _ _ ↦ rfl) hinc

end SameBase

/-- With the subspace topology `subbundleTopology`, a `C^n` vector subbundle `V` of `E` over `B`
whose canonical inclusion into `TotalSpace F E` is `C^n` is `C^n`-smoothly embedded in
`TotalSpace F E`. -/
theorem isSmoothEmbedding_totalSpace_subbundle [FiniteDimensional 𝕜 F] [FiniteDimensional 𝕜 F']
    [IsManifold IB n B] {V : Π x : B, Submodule 𝕜 (E x)}
    [letI := subbundleTopology F (F' := F') V; FiberBundle F' (fun x ↦ V x)]
    [letI := subbundleTopology F (F' := F') V; VectorBundle 𝕜 F' (fun x ↦ V x)]
    [letI := subbundleTopology F (F' := F') V; ContMDiffVectorBundle n F' (fun x ↦ V x) IB]
    (hinc :
      letI := subbundleTopology F (F' := F') V
      ContMDiff (IB.prod 𝓘(𝕜, F')) (IB.prod 𝓘(𝕜, F)) n
        (fun p : TotalSpace F' (fun x ↦ V x) ↦ (⟨p.proj, p.2⟩ : TotalSpace F E))) :
    letI := subbundleTopology F (F' := F') V
    IsSmoothEmbedding (IB.prod 𝓘(𝕜, F')) (IB.prod 𝓘(𝕜, F)) n
      (fun q : TotalSpace F' (fun x ↦ V x) ↦ (⟨q.proj, q.2⟩ : TotalSpace F E)) := by
  let := subbundleTopology F (F' := F') V
  exact ⟨isImmersion_totalSpace_subbundle hinc, isEmbedding_totalSpace_subbundle F F' V⟩

section AlongEmbedding

variable [FiniteDimensional 𝕜 F] [FiniteDimensional 𝕜 F'] [IsManifold IB n B]
  [IsManifold IB' n B'] [IB'.Boundaryless]

/-- Along a topological embedding `f : B' → B` of a boundaryless manifold `B'` that is a `C^n`
immersion at `p.proj`, a `C^n` vector subbundle `V` of `f *ᵖ E` whose canonical inclusion into
`TotalSpace F E` is `C^n` is a `C^n` immersion at `p`. The ambient manifold `B` need not be
boundaryless. -/
theorem isImmersionAt_lift_totalSpace_subbundle {f : B' → B}
    {V : Π x : B', Submodule 𝕜 (E (f x))}
    [TopologicalSpace (TotalSpace F' (fun x ↦ V x))] [FiberBundle F' (fun x ↦ V x)]
    [VectorBundle 𝕜 F' (fun x ↦ V x)] [ContMDiffVectorBundle n F' (fun x ↦ V x) IB']
    {p : TotalSpace F' (fun x ↦ V x)}
    (hf_imm : IsImmersionAt IB' IB n f p.proj) (hf_emb : IsEmbedding f)
    (hinc : ContMDiff (IB'.prod 𝓘(𝕜, F')) (IB.prod 𝓘(𝕜, F)) n
      (fun q : TotalSpace F' (fun x ↦ V x) ↦ (⟨f q.proj, q.2⟩ : TotalSpace F E))) :
    IsImmersionAt (IB'.prod 𝓘(𝕜, F')) (IB.prod 𝓘(𝕜, F)) n
      (fun q : TotalSpace F' (fun x ↦ V x) ↦ (⟨f q.proj, q.2⟩ : TotalSpace F E)) p := by
  obtain ⟨Vr, hVr, hfp, r, hr, hr_inv⟩ := hf_imm.exists_contMDiffOn_retraction hf_emb
  obtain ⟨Q, _, h⟩ := exists_isImmersionAtOfComplement_subbundle_of_retraction
    hf_imm.isImmersionAtOfComplement_complement hf_emb.continuous hVr hfp hr hr_inv hinc
  exact h.isImmersionAt

/-- Along a `C^n` smooth embedding `f : B' → B` of a boundaryless manifold `B'`, a `C^n` vector
subbundle `V` of `f *ᵖ E` whose canonical inclusion into `TotalSpace F E` is `C^n` is a `C^n`
immersion into `TotalSpace F E`. The ambient manifold `B` need not be boundaryless. -/
theorem isImmersion_lift_totalSpace_subbundle {f : B' → B}
    {V : Π x : B', Submodule 𝕜 (E (f x))}
    [TopologicalSpace (TotalSpace F' (fun x ↦ V x))] [FiberBundle F' (fun x ↦ V x)]
    [VectorBundle 𝕜 F' (fun x ↦ V x)] [ContMDiffVectorBundle n F' (fun x ↦ V x) IB']
    (hf : IsSmoothEmbedding IB' IB n f)
    (hinc : ContMDiff (IB'.prod 𝓘(𝕜, F')) (IB.prod 𝓘(𝕜, F)) n
      (fun q : TotalSpace F' (fun x ↦ V x) ↦ (⟨f q.proj, q.2⟩ : TotalSpace F E))) :
    IsImmersion (IB'.prod 𝓘(𝕜, F')) (IB.prod 𝓘(𝕜, F)) n
      (fun q : TotalSpace F' (fun x ↦ V x) ↦ (⟨f q.proj, q.2⟩ : TotalSpace F E)) :=
  isImmersion_of_forall_exists_complement (P := hf.isImmersion.complement) (f := f) (V := V)
    fun p ↦ by
      let hfc := hf.isImmersion.isImmersionOfComplement_complement p.proj
      obtain ⟨Vr, hVr, hfp, r, hr, hr_inv⟩ :=
        hfc.isImmersionAt.exists_contMDiffOn_retraction hf.isEmbedding
      exact exists_isImmersionAtOfComplement_subbundle_of_retraction hfc
        hf.isEmbedding.continuous hVr hfp hr hr_inv hinc

/-- Along a `C^n` smooth embedding `f : B' → B` of a boundaryless manifold `B'`, a `C^n` vector
subbundle `V` over `B'` whose canonical inclusion `(x, v) ↦ (f x, v)` into `TotalSpace F E` is
`C^n` and a topological embedding is `C^n`-smoothly embedded in `TotalSpace F E`. -/
theorem isSmoothEmbedding_lift_totalSpace_subbundle {f : B' → B}
    {V : Π x : B', Submodule 𝕜 (E (f x))}
    [TopologicalSpace (TotalSpace F' (fun x ↦ V x))] [FiberBundle F' (fun x ↦ V x)]
    [VectorBundle 𝕜 F' (fun x ↦ V x)] [ContMDiffVectorBundle n F' (fun x ↦ V x) IB']
    (hf : IsSmoothEmbedding IB' IB n f)
    (hemb : IsEmbedding
      (fun q : TotalSpace F' (fun x ↦ V x) ↦ (⟨f q.proj, q.2⟩ : TotalSpace F E)))
    (hinc : ContMDiff (IB'.prod 𝓘(𝕜, F')) (IB.prod 𝓘(𝕜, F)) n
      (fun p : TotalSpace F' (fun x ↦ V x) ↦ (⟨f p.proj, p.2⟩ : TotalSpace F E))) :
    IsSmoothEmbedding (IB'.prod 𝓘(𝕜, F')) (IB.prod 𝓘(𝕜, F)) n
      (fun q : TotalSpace F' (fun x ↦ V x) ↦ (⟨f q.proj, q.2⟩ : TotalSpace F E)) :=
  ⟨isImmersion_lift_totalSpace_subbundle hf hinc, hemb⟩

end AlongEmbedding

end SubbundleInclusion

end TauCeti

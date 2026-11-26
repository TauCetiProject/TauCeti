/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.Subbundle
public import TauCeti.Topology.VectorBundle.Quotient
import Mathlib.Geometry.Manifold.VectorBundle.ContMDiffSection
import TauCeti.Geometry.Manifold.ContMDiff.LeftInverse

/-!
# Quotients of vector bundles by subbundles

Let `E` be a `C^n` vector bundle over `B` with finite-dimensional model fibre `F`, over a complete
nontrivially normed field `𝕜`, and let `V` assign to every point `x` a subspace `V x` of the fibre
`E x`, with `C^n` local frames indexed by `ι` near every point
(`TauCeti.HasLocalContMDiffSubbundleFrames`), so that `V` is a `C^n` subbundle of `E`. This file
constructs the quotient bundle `E ⧸ V`, whose fibre at `x` is the quotient space `E x ⧸ V x` with
its quotient topology, as a `C^n` vector bundle with model fibre `κ → 𝕜`, where
`card ι + card κ = dim F`.

A local frame of `E ⧸ V` on a set `U` (`TauCeti.IsQuotientFrameOn V Y U`) is a family of sections
`Y j` of `E` whose classes modulo `V` form a basis of every fibre `E x ⧸ V x`, `x ∈ U`. When `X` is
a local frame of `V` on `U`, this holds exactly when `X` and `Y` together form a frame of `E`
(`TauCeti.IsSubbundleFrameOn.isQuotientFrameOn_iff`), and such completions exist near every point
(`TauCeti.HasLocalContMDiffSubbundleFrames.exists_isQuotientFrameOn`): read the frame of `V` in a
trivialization of `E` and add constant sections spanning a complement in `F`. A frame `Y` of `E ⧸ V`
on an open set gives the pretrivialization `TauCeti.IsQuotientFrameOn.pretrivialization`, sending a
class to its coordinates in the frame. These frames and their pretrivializations need no manifold
structure and are set up in `TauCeti.Topology.VectorBundle.Quotient`.

The substance is that these coordinates are `C^n`. Read in a trivialization of `E` near `y₀`, the
frames `X` and `Y` together form a `C^n` family of invertible operators `𝕜^(ι ⊕ κ) → F`, which has
`C^n` left inverses near `y₀`; the coordinates of the class of `v` in the frame `Y` are the
`κ`-components of the left inverse applied to `v`. Hence the coordinate changes between frames of
`E ⧸ V` are `C^n`, and the quotient map `E → E ⧸ V`, `(x, v) ↦ (x, [v])`, is `C^n`.

The bundle is built with Mathlib's `VectorPrebundle`: its pretrivializations are those of all
`C^n` local frames of `E ⧸ V` on open sets, and the topology on the total space is the one these
pretrivializations generate. On each fibre it induces the quotient topology of `E x ⧸ V x`, because
a linear isomorphism between finite-dimensional spaces is a homeomorphism.

## Main definitions

* `TauCeti.HasLocalContMDiffSubbundleFrames.quotientPrebundle`: the quotient bundle `E ⧸ V`, as a
  vector prebundle with model fibre `κ → 𝕜`.

## Main results

* `TauCeti.HasLocalContMDiffSubbundleFrames.exists_isQuotientFrameOn`: `E ⧸ V` has `C^n` local
  frames near every point.
* `TauCeti.HasLocalContMDiffSubbundleFrames.contMDiffVectorBundle_quotientPrebundle`: `E ⧸ V` is a
  `C^n` vector bundle.
* `trivializationOfMemPretrivializationAtlas_quotientPrebundle_apply`, in the namespace
  `TauCeti.HasLocalContMDiffSubbundleFrames`: the trivializations of `E ⧸ V` send a class to its
  coordinates in the corresponding frame.
* `TauCeti.HasLocalContMDiffSubbundleFrames.contMDiff_totalSpace_mkQ`: the quotient map
  `E → E ⧸ V` is `C^n`.
* `TauCeti.HasLocalContMDiffSubbundleFrames.exists_contMDiffOn_mk_eq`: a `C^n` section of `E ⧸ V`
  is locally the class of a `C^n` section of `E`.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Springer GTM 218 (2013), Chapter 10
  (local frame criteria for vector bundles and subbundles).
-/

public section

noncomputable section

open Set Filter Function Module Bundle Topology
open scoped Manifold ContDiff

namespace TauCeti

section Smooth

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  {EB : Type*} [NormedAddCommGroup EB] [NormedSpace 𝕜 EB]
  {HB : Type*} [TopologicalSpace HB] {IB : ModelWithCorners 𝕜 EB HB}
  {B : Type*} [TopologicalSpace B] [ChartedSpace HB B]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {E : B → Type*} [∀ x, AddCommGroup (E x)] [∀ x, Module 𝕜 (E x)]
  [TopologicalSpace (TotalSpace F E)] [∀ x, TopologicalSpace (E x)] [FiberBundle F E]
  [VectorBundle 𝕜 F E] {n : ℕ∞ω}
  {ι κ : Type*} [Fintype ι] [Fintype κ] {V : Π x, Submodule 𝕜 (E x)}
  {X : ι → Π x, E x} {Y : κ → Π x, E x} {U U' : Set B}

omit [CompleteSpace 𝕜] [ChartedSpace HB B] [Fintype κ] [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [∀ x, TopologicalSpace (E x)] [FiberBundle F E] [VectorBundle 𝕜 F E] in
/-- At a point where `X` frames `V` and `Y` frames `E ⧸ V`, the coordinates of the class of a
vector in the frame `Y` are its coordinates along `Y` in the basis of `E` formed by `X` and `Y`. -/
private theorem basis_equivFun_mk_eq [Fintype κ] (hX : IsSubbundleFrameOn F V X U)
    (hY : IsQuotientFrameOn V Y U') {y : B} (hy : y ∈ U) (hy' : y ∈ U') (d : ι ⊕ κ → 𝕜) :
    (hY.basis hy').equivFun (Submodule.Quotient.mk (∑ k, d k • Sum.elim X Y k y)) =
      fun j ↦ d (Sum.inr j) := by
  rw [← LinearEquiv.eq_symm_apply, hY.basis_equivFun_symm, Submodule.Quotient.eq,
    Fintype.sum_sum_type]
  simp only [Sum.elim_inl, Sum.elim_inr, add_sub_cancel_right]
  exact Submodule.sum_mem _ fun i _ ↦ Submodule.smul_mem _ _ (hX.apply_mem i hy)

variable [ContMDiffVectorBundle n F E IB]

omit [Fintype κ] in
/-- If the sections `X` and `Y` are `C^n` at `y₀` and together, read in the trivialization of `E`
at `y₀`, are bijective on coefficients at `y₀`, then this family of operators has `C^n` left
inverses near `y₀`. -/
private theorem exists_contMDiffAt_leftInverse_trivOperator_sumElim [Fintype κ] {y₀ : B}
    (hX : ∀ i, CMDiffAt n (T% (X i)) y₀) (hY : ∀ j, CMDiffAt n (T% (Y j)) y₀)
    (hbij : Bijective (IsSubbundleFrameOn.trivOperator 𝕜 F (Sum.elim X Y) y₀ y₀)) :
    ∃ L : B → F →L[𝕜] ι ⊕ κ → 𝕜, ContMDiffAt IB 𝓘(𝕜, F →L[𝕜] ι ⊕ κ → 𝕜) n L y₀ ∧
      ∀ᶠ y in 𝓝 y₀,
        LeftInverse (L y) (IsSubbundleFrameOn.trivOperator 𝕜 F (Sum.elim X Y) y₀ y) := by
  let A₀ := (LinearEquiv.ofBijective
    (IsSubbundleFrameOn.trivOperator 𝕜 F (Sum.elim X Y) y₀ y₀ : (ι ⊕ κ → 𝕜) →ₗ[𝕜] F)
    hbij).toContinuousLinearEquiv
  exact (IsSubbundleFrameOn.contMDiffAt_trivOperator (𝕜' := 𝕜) (Sum.forall.mpr ⟨hX, hY⟩)
    (FiberBundle.mem_baseSet_trivializationAt' y₀)).exists_contMDiffAt_leftInverse
    ⟨A₀.symm, fun d ↦ A₀.symm_apply_apply d⟩

omit [Fintype ι] in
/-- Near a point `y₀` where `X` is a `C^n` frame of `V` and `Y` a `C^n` frame of `E ⧸ V`, the
coordinates of a class in the frame `Y` are a `C^n` family of operators applied to a representative
read in the trivialization of `E` at `y₀`. -/
private theorem exists_basis_equivFun_mk_eq [Finite ι] (hX : IsSubbundleFrameOn F V X U)
    (hU : IsOpen U) (hXn : ∀ i, CMDiff[U] n (T% (X i))) (hY : IsQuotientFrameOn V Y U')
    (hU' : IsOpen U') (hYn : ∀ j, CMDiff[U'] n (T% (Y j))) {y₀ : B} (hy₀ : y₀ ∈ U)
    (hy₀' : y₀ ∈ U') :
    ∃ L : B → F →L[𝕜] κ → 𝕜, ContMDiffAt IB 𝓘(𝕜, F →L[𝕜] κ → 𝕜) n L y₀ ∧
      ∀ᶠ y in 𝓝 y₀, ∃ hy : y ∈ U', y ∈ (trivializationAt F E y₀).baseSet ∧
        ∀ v : E y, (hY.basis hy).equivFun (Submodule.Quotient.mk v) =
          L y (trivializationAt F E y₀ ⟨y, v⟩).2 := by
  have := Fintype.ofFinite ι
  have he := FiberBundle.mem_baseSet_trivializationAt' (F := F) (E := E) y₀
  have hb := (hX.mono (inter_subset_left (t := U'))).isQuotientFrameOn_iff.mp
    (hY.mono inter_subset_right)
  -- The frames `X` and `Y` together, read in the trivialization at `y₀`, have left inverses.
  obtain ⟨L, hL, hLinv⟩ := exists_contMDiffAt_leftInverse_trivOperator_sumElim
    (fun i ↦ (hXn i).contMDiffAt (hU.mem_nhds hy₀))
    (fun j ↦ (hYn j).contMDiffAt (hU'.mem_nhds hy₀'))
    ((IsSubbundleFrameOn.linearIndependent_and_span_eq_top_iff_bijective_trivOperator he).mp
      (hb y₀ ⟨hy₀, hy₀'⟩))
  let P : (ι ⊕ κ → 𝕜) →L[𝕜] κ → 𝕜 := .pi fun j ↦ .proj (Sum.inr j)
  refine ⟨fun y ↦ P ∘L L y,
    (ContinuousLinearMap.compL 𝕜 F _ _ P).contDiff.comp_contMDiffAt hL, ?_⟩
  filter_upwards [hLinv, (hU.inter hU').mem_nhds ⟨hy₀, hy₀'⟩,
    (trivializationAt F E y₀).open_baseSet.mem_nhds he] with y hyL hy hye
  refine ⟨hy.2, hye, fun v ↦ ?_⟩
  -- Expand `v` in the basis of `E y` formed by `X` and `Y`.
  let b := Basis.mk (hb y hy).1 (hb y hy).2.ge
  have hv : ∑ k, b.equivFun v k • Sum.elim X Y k y = v := by
    simpa [b] using b.sum_equivFun v
  have hAv : IsSubbundleFrameOn.trivOperator 𝕜 F (Sum.elim X Y) y₀ y (b.equivFun v) =
      (trivializationAt F E y₀ ⟨y, v⟩).2 := by
    rw [IsSubbundleFrameOn.trivOperator_apply hye, hv]
  conv_lhs => rw [← hv]
  rw [basis_equivFun_mk_eq hX hY hy.1 hy.2, ContinuousLinearMap.comp_apply, ← hAv, hyL]
  ext j
  simp only [P, ContinuousLinearMap.pi_apply, ContinuousLinearMap.proj_apply]


omit [Fintype ι] in
/-- The coordinate changes between the pretrivializations of two `C^n` frames of `E ⧸ V` are
`C^n` on the overlap of their domains, provided `V` has `C^n` local frames. -/
private theorem exists_contMDiffOn_coordChange [Finite ι]
    (hV : HasLocalContMDiffSubbundleFrames IB n F ι V)
    (hY : IsQuotientFrameOn V Y U) (hU : IsOpen U) (hYn : ∀ j, CMDiff[U] n (T% (Y j)))
    {Y' : κ → Π x, E x} (hY' : IsQuotientFrameOn V Y' U') (hU' : IsOpen U')
    (hY'n : ∀ j, CMDiff[U'] n (T% (Y' j))) :
    ∃ f : B → (κ → 𝕜) →L[𝕜] κ → 𝕜,
      ContMDiffOn IB 𝓘(𝕜, (κ → 𝕜) →L[𝕜] κ → 𝕜) n f
        ((hY.pretrivialization hU).baseSet ∩ (hY'.pretrivialization hU').baseSet) ∧
      ∀ b ∈ (hY.pretrivialization hU).baseSet ∩ (hY'.pretrivialization hU').baseSet, ∀ c,
        f b c = (hY'.pretrivialization hU' ⟨b, (hY.pretrivialization hU).symm b c⟩).2 := by
  classical
  have := Fintype.ofFinite ι
  simp only [IsQuotientFrameOn.pretrivialization_baseSet]
  let f : B → (κ → 𝕜) →L[𝕜] κ → 𝕜 := fun b ↦
    if hb : b ∈ U ∩ U' then
      LinearMap.toContinuousLinearMap
        ((hY'.basis hb.2).equivFun.toLinearMap ∘ₗ (hY.basis hb.1).equivFun.symm.toLinearMap)
    else 0
  have hf (b : B) (hb : b ∈ U ∩ U') (c : κ → 𝕜) :
      f b c = (hY'.basis hb.2).equivFun ((hY.basis hb.1).equivFun.symm c) := by
    simp only [f, hb, ↓reduceDIte, LinearMap.coe_toContinuousLinearMap', LinearMap.coe_comp,
      LinearEquiv.coe_coe, comp_apply]
  refine ⟨f, fun b₀ hb₀ ↦ ?_, fun b hb c ↦ ?_⟩
  · obtain ⟨W, hW, hb₀W, X, hX, hXn⟩ := hasLocalContMDiffSubbundleFrames_iff.mp hV b₀
    obtain ⟨L, hL, hev⟩ := exists_basis_equivFun_mk_eq hX hW hXn hY' hU' hY'n hb₀W hb₀.2
    have he := FiberBundle.mem_baseSet_trivializationAt' (F := F) (E := E) b₀
    -- Read the frame `Y` in the trivialization of `E` at `b₀`.
    have hT := IsSubbundleFrameOn.contMDiffAt_trivOperator (𝕜' := 𝕜) (X := Y)
      (fun j ↦ (hYn j).contMDiffAt (hU.mem_nhds hb₀.1)) he
    refine ContMDiffAt.contMDiffWithinAt ((hL.clm_comp hT).congr_of_eventuallyEq ?_)
    filter_upwards [hev, (hU.inter hU').mem_nhds hb₀] with b hbev hb
    obtain ⟨hb', hbe, hbL⟩ := hbev
    ext1 c
    rw [hf b hb, hY.basis_equivFun_symm, hbL, ContinuousLinearMap.comp_apply,
      IsSubbundleFrameOn.trivOperator_apply hbe]
  · rw [hY.pretrivialization_symm_apply hU hb.1, hf b hb]
    exact congrArg Prod.snd (hY'.pretrivialization_apply hU' (p := ⟨b, _⟩) hb.2).symm

omit [CompleteSpace 𝕜] [ChartedSpace HB B] [ContMDiffVectorBundle n F E IB] [Fintype κ] in
/-- Over a frame of `E ⧸ V`, the frame pretrivialization restricts on each fibre to a
homeomorphism onto its image, for the quotient topology of the fibre. -/
private theorem isInducing_pretrivialization_comp_mk [Finite κ] [FiniteDimensional 𝕜 F]
    [CompleteSpace 𝕜] (hY : IsQuotientFrameOn V Y U) (hU : IsOpen U) {b : B} (hb : b ∈ U) :
    IsInducing (hY.pretrivialization hU ∘ TotalSpace.mk b) := by
  have := Fintype.ofFinite κ
  let φ := (trivializationAt F E b).continuousLinearEquivAt 𝕜 b
    (FiberBundle.mem_baseSet_trivializationAt' b)
  -- Linear maps out of the fibre `E b ≃L[𝕜] F` are continuous.
  have hcont (g : E b →ₗ[𝕜] κ → 𝕜) : Continuous g := by
    have : (g : E b → κ → 𝕜) = (g ∘ₗ (φ.symm : F →ₗ[𝕜] E b)) ∘ φ := by
      ext v
      simp
    rw [this]
    exact (g ∘ₗ (φ.symm : F →ₗ[𝕜] E b)).continuous_of_finiteDimensional.comp φ.continuous
  let g : (κ → 𝕜) →ₗ[𝕜] E b ⧸ V b := (V b).mkQ ∘ₗ Fintype.linearCombination 𝕜 (Y · b)
  have hg : Continuous g := by
    have : (g : (κ → 𝕜) → E b ⧸ V b) =
        (V b).mkQ ∘ φ.symm ∘ (φ.toLinearMap ∘ₗ Fintype.linearCombination 𝕜 (Y · b)) := by
      ext c
      simp [g]
    rw [this]
    exact (V b).continuous_mkQ.comp (φ.symm.continuous.comp
      (φ.toLinearMap ∘ₗ Fintype.linearCombination 𝕜 (Y · b)).continuous_on_pi)
  have hcoords : Continuous fun q : E b ⧸ V b ↦ (hY.basis hb).equivFun q :=
    (Submodule.isQuotientMap_mkQ (V b)).continuous_iff.mpr <| by
      exact hcont (((hY.basis hb).equivFun : (E b ⧸ V b) →ₗ[𝕜] κ → 𝕜) ∘ₗ (V b).mkQ)
  refine IsInducing.of_comp (g := g ∘ Prod.snd) ?_ (hg.comp continuous_snd) ?_
  · exact (continuous_const.prodMk hcoords).congr fun q ↦
      (hY.pretrivialization_apply hU (p := ⟨b, q⟩) hb).symm
  · have hgc (c : κ → 𝕜) : g c = (hY.basis hb).equivFun.symm c := by
      rw [hY.basis_equivFun_symm hb]
      simp only [g, LinearMap.comp_apply, Fintype.linearCombination_apply, Submodule.mkQ_apply]
    have : (g ∘ Prod.snd) ∘ (hY.pretrivialization hU ∘ TotalSpace.mk b) = id := by
      ext q
      simp only [Function.comp_apply, hY.pretrivialization_apply hU (p := ⟨b, q⟩) hb, id_eq]
      rw [hgc, LinearEquiv.symm_apply_apply]
    rw [this]
    exact IsInducing.id


omit [CompleteSpace 𝕜] in
/-- A frame of `V` at `x₀` can be completed, by `C^n` sections of `E` that are constant in the
trivialization of `E` at `x₀`, to vectors forming a basis of `E x₀`. -/
private theorem exists_contMDiffOn_injective_trivOperator_sumElim [FiniteDimensional 𝕜 F]
    (hX : IsSubbundleFrameOn F V X U) {x₀ : B} (hx₀ : x₀ ∈ U)
    (hκ : Fintype.card ι + Fintype.card κ = finrank 𝕜 F) :
    ∃ Y : κ → Π x, E x, (∀ j, CMDiff[(trivializationAt F E x₀).baseSet] n (T% (Y j))) ∧
      Injective (IsSubbundleFrameOn.trivOperator 𝕜 F (Sum.elim X Y) x₀ x₀) := by
  set e := trivializationAt F E x₀
  have he : x₀ ∈ e.baseSet := FiberBundle.mem_baseSet_trivializationAt' x₀
  let φ := e.continuousLinearEquivAt 𝕜 x₀ he
  -- Complete the frame of `V x₀`, read in `e`, by a basis `c` of a complement in `F`.
  have hXφ : LinearIndependent 𝕜 fun i ↦ φ (X i x₀) :=
    (hX.linearIndependent hx₀).map' (φ : E x₀ →ₗ[𝕜] F) φ.toLinearEquiv.ker
  let W := Submodule.span 𝕜 (range fun i ↦ φ (X i x₀))
  obtain ⟨C, hWC⟩ := W.exists_isCompl
  have hC : finrank 𝕜 C = Fintype.card κ := by
    have := Submodule.finrank_add_eq_of_isCompl hWC
    rw [finrank_span_eq_card hXφ] at this
    omega
  let c : Basis κ 𝕜 C := (Module.finBasisOfFinrankEq 𝕜 C hC).reindex (Fintype.equivFin κ).symm
  let Y : κ → Π x, E x := fun j x ↦ e.symm x (c j)
  refine ⟨Y, fun j ↦ e.contMDiffOn_section_baseSet_iff.mpr <|
    (contMDiffOn_const (c := (c j : F))).congr fun y hy ↦ by simp [Y, e.apply_mk_symm hy], ?_⟩
  -- The two halves of the completed frame span complementary subspaces of `F`.
  have hA : (IsSubbundleFrameOn.trivOperator 𝕜 F (Sum.elim X Y) x₀ x₀ : (ι ⊕ κ → 𝕜) → F) =
      Fintype.linearCombination 𝕜 (Sum.elim (fun i ↦ φ (X i x₀)) fun j ↦ (c j : F)) := by
    ext d
    rw [IsSubbundleFrameOn.trivOperator_apply_eq_linearCombination he,
      Fintype.linearCombination_apply,
      Fintype.linearCombination_apply, map_sum, Fintype.sum_sum_type, Fintype.sum_sum_type]
    simp only [Y, φ, e]
    simp [Trivialization.apply_mk_symm _ (FiberBundle.mem_baseSet_trivializationAt' x₀)]
  rw [hA, ← linearIndependent_iff_injective_fintypeLinearCombination]
  refine hXφ.sum_type (c.linearIndependent.map' C.subtype C.ker_subtype) ?_
  refine hWC.disjoint.mono_right (Submodule.span_le.mpr ?_)
  rintro _ ⟨j, rfl⟩
  exact (c j).property

variable [FiniteDimensional 𝕜 F]

/-- **Quotients by subbundles have local frames.** If `V` has `C^n` local frames of size `card ι`
and the model fibre of `E` has dimension `card ι + card κ`, then every point has an open
neighbourhood carrying a `C^n` local frame of `E ⧸ V` indexed by `κ`. -/
theorem HasLocalContMDiffSubbundleFrames.exists_isQuotientFrameOn
    (hV : HasLocalContMDiffSubbundleFrames IB n F ι V)
    (hκ : Fintype.card ι + Fintype.card κ = finrank 𝕜 F) (x₀ : B) :
    ∃ U : Set B, IsOpen U ∧ x₀ ∈ U ∧
      ∃ Y : κ → Π x, E x, IsQuotientFrameOn V Y U ∧ ∀ j, CMDiff[U] n (T% (Y j)) := by
  obtain ⟨U₀, hU₀, hx₀, X, hX, hXn⟩ := hasLocalContMDiffSubbundleFrames_iff.mp hV x₀
  obtain ⟨Y, hYn, hinj⟩ :=
    exists_contMDiffOn_injective_trivOperator_sumElim (IB := IB) (n := n) hX hx₀ hκ
  set e := trivializationAt F E x₀
  have he : x₀ ∈ e.baseSet := FiberBundle.mem_baseSet_trivializationAt' x₀
  have hrank : finrank 𝕜 (ι ⊕ κ → 𝕜) = finrank 𝕜 F := by
    simp [hκ]
  -- The completed frame read in `e` is invertible at `x₀`, so it has left inverses nearby.
  obtain ⟨L, -, hLinv⟩ := exists_contMDiffAt_leftInverse_trivOperator_sumElim
    (fun i ↦ (hXn i).contMDiffAt (hU₀.mem_nhds hx₀))
    (fun j ↦ (hYn j).contMDiffAt (e.open_baseSet.mem_nhds he))
    ⟨hinj, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hrank).mp hinj⟩
  obtain ⟨t, ht, hto, hx₀t⟩ := mem_nhds_iff.mp hLinv
  exact ⟨t ∩ U₀ ∩ e.baseSet, (hto.inter hU₀).inter e.open_baseSet, ⟨⟨hx₀t, hx₀⟩, he⟩, Y,
    (hX.mono (U' := t ∩ U₀ ∩ e.baseSet) fun y hy ↦ hy.1.2).isQuotientFrameOn_iff.mpr
      fun y hy ↦ IsSubbundleFrameOn.linearIndependent_and_span_eq_top_of_injective_trivOperator
        hy.2 hrank (ht hy.1.1).injective,
    fun j ↦ (hYn j).mono fun y hy ↦ hy.2⟩

namespace HasLocalContMDiffSubbundleFrames

variable (hV : HasLocalContMDiffSubbundleFrames IB n F ι V)
  (hκ : Fintype.card ι + Fintype.card κ = finrank 𝕜 F)

/-- The domain of the `C^n` local frame of `E ⧸ V` chosen near `x`. -/
private def frameDomain (x : B) : Set B :=
  (hV.exists_isQuotientFrameOn hκ x).choose

/-- The `C^n` local frame of `E ⧸ V` chosen near `x`. -/
private def frame (x : B) : κ → Π y, E y :=
  (hV.exists_isQuotientFrameOn hκ x).choose_spec.2.2.choose

private theorem frame_spec (x : B) :
    IsOpen (hV.frameDomain hκ x) ∧ x ∈ hV.frameDomain hκ x ∧
      IsQuotientFrameOn V (hV.frame hκ x) (hV.frameDomain hκ x) ∧
      ∀ j, CMDiff[hV.frameDomain hκ x] n (T% (hV.frame hκ x j)) :=
  have h := (hV.exists_isQuotientFrameOn hκ x).choose_spec
  ⟨h.1, h.2.1, h.2.2.choose_spec⟩

/-- **The quotient bundle `E ⧸ V`.** Let `V` be a family of subspaces of the fibres of a `C^n`
vector bundle `E`, with `C^n` local frames of size `card ι` near every point, and let the model
fibre of `E` have dimension `card ι + card κ`. The quotients `E x ⧸ V x`, each with its quotient
topology, form a vector prebundle with model fibre `κ → 𝕜`, whose pretrivializations are those of
the `C^n` local frames of `E ⧸ V` (`TauCeti.IsQuotientFrameOn.pretrivialization`). With the
total-space topology `(hV.quotientPrebundle hκ).totalSpaceTopology`, it is a `C^n` vector bundle
(`TauCeti.HasLocalContMDiffSubbundleFrames.contMDiffVectorBundle_quotientPrebundle`), and the
quotient map from `E` is `C^n`
(`TauCeti.HasLocalContMDiffSubbundleFrames.contMDiff_totalSpace_mkQ`). -/
def quotientPrebundle : VectorPrebundle 𝕜 (κ → 𝕜) fun x ↦ E x ⧸ V x where
  pretrivializationAtlas :=
    {e | ∃ (U : Set B) (hU : IsOpen U) (Y : κ → Π x, E x) (hY : IsQuotientFrameOn V Y U),
      (∀ j, CMDiff[U] n (T% (Y j))) ∧ hY.pretrivialization hU = e}
  pretrivialization_linear' := by
    rintro _ ⟨U, hU, Y, hY, -, rfl⟩
    exact hY.isLinear_pretrivialization hU
  pretrivializationAt x := (hV.frame_spec hκ x).2.2.1.pretrivialization (hV.frame_spec hκ x).1
  mem_base_pretrivializationAt x :=
    ((hV.frame_spec hκ x).2.2.1.pretrivialization_baseSet _).ge (hV.frame_spec hκ x).2.1
  pretrivialization_mem_atlas x :=
    ⟨_, (hV.frame_spec hκ x).1, _, (hV.frame_spec hκ x).2.2.1, (hV.frame_spec hκ x).2.2.2, rfl⟩
  exists_coordChange := by
    rintro _ ⟨U, hU, Y, hY, hYn, rfl⟩ _ ⟨U', hU', Y', hY', hY'n, rfl⟩
    obtain ⟨f, hf, hfe⟩ := exists_contMDiffOn_coordChange hV hY hU hYn hY' hU' hY'n
    exact ⟨f, hf.continuousOn, hfe⟩
  totalSpaceMk_isInducing x :=
    isInducing_pretrivialization_comp_mk (F := F) (hV.frame_spec hκ x).2.2.1
      (hV.frame_spec hκ x).1 (hV.frame_spec hκ x).2.1

/-- The pretrivializations of the quotient bundle are those of the `C^n` local frames of `E ⧸ V`
on open sets. -/
theorem mem_pretrivializationAtlas_quotientPrebundle_iff
    (e : Pretrivialization (κ → 𝕜) (π (κ → 𝕜) fun x ↦ E x ⧸ V x)) :
    e ∈ (hV.quotientPrebundle hκ).pretrivializationAtlas ↔
      ∃ (U : Set B) (hU : IsOpen U) (Y : κ → Π x, E x) (hY : IsQuotientFrameOn V Y U),
        (∀ j, CMDiff[U] n (T% (Y j))) ∧ hY.pretrivialization hU = e :=
  Iff.rfl

/-- The coordinate changes of the quotient bundle are `C^n`. -/
theorem isContMDiff_quotientPrebundle : (hV.quotientPrebundle hκ).IsContMDiff IB n where
  exists_contMDiffCoordChange := by
    rintro _ ⟨U, hU, Y, hY, hYn, rfl⟩ _ ⟨U', hU', Y', hY', hY'n, rfl⟩
    exact exists_contMDiffOn_coordChange hV hY hU hYn hY' hU' hY'n

/-- **The quotient of a `C^n` vector bundle by a `C^n` subbundle is a `C^n` vector bundle.** -/
theorem contMDiffVectorBundle_quotientPrebundle :
    letI := (hV.quotientPrebundle hκ).totalSpaceTopology
    letI := (hV.quotientPrebundle hκ).toFiberBundle
    letI := (hV.quotientPrebundle hκ).toVectorBundle
    ContMDiffVectorBundle n (κ → 𝕜) (fun x ↦ E x ⧸ V x) IB :=
  have := hV.isContMDiff_quotientPrebundle hκ
  VectorPrebundle.contMDiffVectorBundle IB (hV.quotientPrebundle hκ)

/-- In the quotient bundle, the trivialization given by a local frame `Y` of `E ⧸ V` on an open set
`U` whose pretrivialization lies in the atlas sends a class over a point of `U` to its coordinates
in the frame. -/
theorem trivializationOfMemPretrivializationAtlas_quotientPrebundle_apply
    {Y : κ → Π x, E x} {U : Set B} {hY : IsQuotientFrameOn V Y U} {hU : IsOpen U}
    (he : hY.pretrivialization hU ∈ (hV.quotientPrebundle hκ).pretrivializationAtlas)
    {p : TotalSpace (κ → 𝕜) fun x ↦ E x ⧸ V x} (hp : p.proj ∈ U) :
    letI := (hV.quotientPrebundle hκ).totalSpaceTopology
    (hV.quotientPrebundle hκ).trivializationOfMemPretrivializationAtlas he p =
      (p.proj, (hY.basis hp).equivFun p.snd) :=
  -- The trivialization built from a pretrivialization has the same underlying function.
  hY.pretrivialization_apply hU hp

/-- In the quotient bundle, the trivialization at `x` sends a class over a point of the domain of
the chosen frame to its coordinates in that frame. -/
private theorem trivializationAt_quotientPrebundle_apply {x : B}
    {p : TotalSpace (κ → 𝕜) fun x ↦ E x ⧸ V x} (hp : p.proj ∈ hV.frameDomain hκ x) :
    letI := (hV.quotientPrebundle hκ).totalSpaceTopology
    letI := (hV.quotientPrebundle hκ).toFiberBundle
    trivializationAt (κ → 𝕜) (fun x ↦ E x ⧸ V x) x p =
      (p.proj, ((hV.frame_spec hκ x).2.2.1.basis hp).equivFun p.snd) :=
  hV.trivializationOfMemPretrivializationAtlas_quotientPrebundle_apply hκ
    ((hV.quotientPrebundle hκ).pretrivialization_mem_atlas x) hp

/-- **The quotient map `E → E ⧸ V` is `C^n`.** -/
theorem contMDiff_totalSpace_mkQ :
    letI := (hV.quotientPrebundle hκ).totalSpaceTopology
    letI := (hV.quotientPrebundle hκ).toFiberBundle
    ContMDiff (IB.prod 𝓘(𝕜, F)) (IB.prod 𝓘(𝕜, κ → 𝕜)) n
      (fun p : TotalSpace F E ↦
        (⟨p.proj, Submodule.Quotient.mk p.snd⟩ : TotalSpace (κ → 𝕜) fun x ↦ E x ⧸ V x)) := by
  let := (hV.quotientPrebundle hκ).totalSpaceTopology
  let := (hV.quotientPrebundle hκ).toFiberBundle
  intro p
  have hproj : ContMDiffAt (IB.prod 𝓘(𝕜, F)) IB n (fun q : TotalSpace F E ↦ q.proj) p :=
    (Bundle.contMDiff_proj E).contMDiffAt
  rw [Bundle.contMDiffAt_totalSpace_iff]
  refine ⟨hproj, ?_⟩
  obtain ⟨hU, hpU, hY, hYn⟩ := hV.frame_spec hκ p.proj
  obtain ⟨W, hW, hpW, X, hX, hXn⟩ := hasLocalContMDiffSubbundleFrames_iff.mp hV p.proj
  obtain ⟨L, hL, hev⟩ := exists_basis_equivFun_mk_eq hX hW hXn hY hU hYn hpW hpU
  have hpE := FiberBundle.mem_trivializationAt_proj_source (x := p)
  refine ((hL.comp p hproj).clm_apply
    ((trivializationAt F E p.proj).contMDiffAt hpE).snd).congr_of_eventuallyEq ?_
  filter_upwards [hproj.continuousAt.preimage_mem_nhds hev] with q hq
  obtain ⟨hqU, -, hqL⟩ := hq
  rw [trivializationAt_quotientPrebundle_apply hV hκ hqU]
  exact hqL q.snd

/-- **Local lifts of sections.** A `C^n` section of the quotient bundle `E ⧸ V` on an open set
`W` is, near every point of `W`, the class of a `C^n` section of `E`. -/
theorem exists_contMDiffOn_mk_eq {W : Set B} (hW : IsOpen W) {s : Π x, E x ⧸ V x}
    (hs : letI := (hV.quotientPrebundle hκ).totalSpaceTopology
      letI := (hV.quotientPrebundle hκ).toFiberBundle
      ContMDiffOn IB (IB.prod 𝓘(𝕜, κ → 𝕜)) n
        (fun x ↦ TotalSpace.mk' (κ → 𝕜) (E := fun x ↦ E x ⧸ V x) x (s x)) W)
    {x₀ : B} (hx₀ : x₀ ∈ W) :
    ∃ U : Set B, IsOpen U ∧ x₀ ∈ U ∧ U ⊆ W ∧ ∃ σ : (Π x, E x), CMDiff[U] n (T% σ) ∧
      ∀ x ∈ U, Submodule.Quotient.mk (σ x) = s x := by
  let := (hV.quotientPrebundle hκ).totalSpaceTopology
  let := (hV.quotientPrebundle hκ).toFiberBundle
  have := (hV.quotientPrebundle hκ).toVectorBundle
  have := hV.contMDiffVectorBundle_quotientPrebundle hκ
  obtain ⟨hU, hx₀U, hY, hYn⟩ := hV.frame_spec hκ x₀
  set U := hV.frameDomain hκ x₀
  set Y := hV.frame hκ x₀
  -- The coordinates of `s` in the frame `Y` are `C^n` on `U ∩ W`.
  have hc : ContMDiffOn IB 𝓘(𝕜, κ → 𝕜) n
      (fun x ↦ (trivializationAt (κ → 𝕜) (fun x ↦ E x ⧸ V x) x₀ ⟨x, s x⟩).2) (U ∩ W) :=
    ((trivializationAt (κ → 𝕜) (fun x ↦ E x ⧸ V x) x₀).contMDiffOn_section_iff (hU.inter hW)
      fun x hx ↦ (hY.pretrivialization_baseSet hU).ge hx.1).mp (hs.mono inter_subset_right)
  refine ⟨U ∩ W, hU.inter hW, ⟨hx₀U, hx₀⟩, inter_subset_right,
    fun x ↦ ∑ j, (trivializationAt (κ → 𝕜) (fun x ↦ E x ⧸ V x) x₀ ⟨x, s x⟩).2 j • Y j x,
    ?_, fun x hx ↦ ?_⟩
  · refine ContMDiffOn.sum_section fun j _ ↦ ContMDiffOn.smul_section ?_
      ((hYn j).mono inter_subset_left)
    exact fun x hx ↦ (ContinuousLinearMap.proj j : (κ → 𝕜) →L[𝕜] 𝕜).contDiff.comp_contMDiffWithinAt
      (hc x hx)
  · dsimp only
    rw [trivializationAt_quotientPrebundle_apply hV hκ (p := ⟨x, s x⟩) hx.1,
      ← hY.basis_equivFun_symm hx.1, LinearEquiv.symm_apply_apply]

end HasLocalContMDiffSubbundleFrames

end Smooth

end TauCeti

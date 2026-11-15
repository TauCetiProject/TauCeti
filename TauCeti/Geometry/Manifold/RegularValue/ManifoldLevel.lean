/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.IsManifold.InteriorBoundary
public import TauCeti.Geometry.Manifold.RegularValue.Level
import TauCeti.Geometry.Manifold.Immersion.LocalDiffeomorph
import TauCeti.Geometry.Manifold.Immersion.Basic
import TauCeti.Geometry.Manifold.LocalDiffeomorph.OpenSubset
public import TauCeti.Geometry.Manifold.LocalDiffeomorph.Basic
import TauCeti.Geometry.Manifold.PullbackGroupoid

/-!
# Regular fibres of manifold-valued maps

A regular fibre over an interior value of a `C^m` map, `m ≥ 1`, from a finite-dimensional
boundaryless real manifold to a finite-dimensional real manifold is an embedded submanifold of
the expected dimension. The carrier is the actual subtype
`{x // f x = c}`, with its subspace topology; neither manifold needs to be Hausdorff, and the
fibre may be empty.

`TauCeti.regularFiberChartedSpace` constructs an atlas using the preferred extended target chart.
`TauCeti.RegularFiber.chartedSpaceOfChart` allows any target chart containing the value.
`TauCeti.isManifold_regularFiber`, `TauCeti.isSmoothEmbedding_coe_regularFiber`, and
`TauCeti.range_mfderiv_coe_regularFiber` give its manifold, embedding, and tangent-kernel
properties.
`TauCeti.exists_regularFiber_smoothEmbedding` packages these properties existentially.
The smooth universal property follows from Mathlib's `ContMDiff.iff_comp_isImmersion`
and continuity into a subtype. No global charted-space instance is installed on a fibre or on its
ambient manifold.

The construction uses one extended target chart at `c`. Its open preimage contains the entire
fibre, and the regular level of the coordinate map there is homeomorphic to the original fibre.
The atlas is transported from `TauCeti.regularLevelChartedSpace`; no gluing of local fibre
atlases is needed.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Springer, 2013,
  Corollary 5.14 and Proposition 5.38 (regular level sets and their tangent spaces).
-/

public section

open Function Module Set
open scoped ContDiff Manifold Topology

namespace TauCeti

namespace RegularFiber

variable {E H M F G N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace G]
  {J : ModelWithCorners ℝ F G}
  [TopologicalSpace N] [ChartedSpace G N]
  {f : M → N} {c : N} {m : ℕ∞ω}

/-- The open preimage of the source of a target coordinate chart. -/
private def domain (hf : ContMDiff I J m f) (φ : PartialDiffeomorph J 𝓘(ℝ, F) N F m) :
    TopologicalSpace.Opens M :=
  ⟨f ⁻¹' φ.source, φ.open_source.preimage hf.continuous⟩

private theorem coordinate_eq_iff (hf : ContMDiff I J m f)
    (φ : PartialDiffeomorph J 𝓘(ℝ, F) N F m) (hc : c ∈ φ.source)
    (x : domain hf φ) : φ (f x) = φ c ↔ f x = c :=
  ⟨fun h ↦ φ.toPartialEquiv.injOn x.2 hc h, congrArg φ⟩

/-- The coordinate level in the open preimage is the original fibre, with the same topology. -/
private def levelHomeomorph (hf : ContMDiff I J m f)
    (φ : PartialDiffeomorph J 𝓘(ℝ, F) N F m) (hc : c ∈ φ.source) :
    {x : M // f x = c} ≃ₜ {x : domain hf φ // φ (f x) = φ c} where
  toFun x := ⟨⟨x, by simpa only [domain, TopologicalSpace.Opens.mem_mk,
    mem_preimage, x.2] using hc⟩, congrArg φ x.2⟩
  invFun x := ⟨x.1, (coordinate_eq_iff hf φ hc x.1).1 x.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

private theorem coe_levelHomeomorph (hf : ContMDiff I J m f)
    (φ : PartialDiffeomorph J 𝓘(ℝ, F) N F m) (hc : c ∈ φ.source)
    (x : {x : M // f x = c}) : (levelHomeomorph hf φ hc x).1.1 = x.1 :=
  (rfl)

private theorem contMDiff_coordinate (hf : ContMDiff I J m f)
    (φ : PartialDiffeomorph J 𝓘(ℝ, F) N F m) :
    ContMDiff I 𝓘(ℝ, F) m (fun x : domain hf φ ↦ φ (f x)) :=
  φ.contMDiffOn.comp_contMDiff (hf.comp contMDiff_subtype_val) fun x ↦ x.2

/-- Target coordinates and the open inclusion both have invertible differential, so regularity
is unchanged by passing to the coordinate level. -/
private theorem regularValue_coordinate (hm : 1 ≤ m) (hf : ContMDiff I J m f)
    (φ : PartialDiffeomorph J 𝓘(ℝ, F) N F m) (hc : c ∈ φ.source)
    (hreg : IsRegularValue I J f c) :
    IsRegularValue I 𝓘(ℝ, F) (fun x : domain hf φ ↦ φ (f x)) (φ c) := by
  rw [isRegularValue_iff]
  intro x hx
  have hm0 : m ≠ 0 := ENat.one_le_iff_ne_zero_withTop.mp hm
  have hi := isLocalDiffeomorph_subtype_val (I := I) (n := m) (U := domain hf φ) x
  have hφ := φ.isLocalDiffeomorphAt J 𝓘(ℝ, F) m x.2
  exact IsRegularPoint.comp (isRegularPoint_iff.2 (hφ.isInvertible_mfderiv hm0).surjective)
    ((hreg.isRegularPoint ((coordinate_eq_iff hf φ hc x).1 hx)).comp
      (isRegularPoint_iff.2 (hi.isInvertible_mfderiv hm0).surjective))

variable [I.Boundaryless] [IsManifold I m M]
  [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]

/-- The atlas of a regular fibre transported from its coordinate level in a target chart `φ`
containing the value `c`. The fibre retains its subspace topology, and no global instance is
installed. -/
@[instance_reducible]
noncomputable def chartedSpaceOfChart (hm : 1 ≤ m) (hf : ContMDiff I J m f)
    (φ : PartialDiffeomorph J 𝓘(ℝ, F) N F m) (hc : c ∈ φ.source)
    (hreg : IsRegularValue I J f c) :
    ChartedSpace (Fin (finrank ℝ E - finrank ℝ F) → ℝ) {x : M // f x = c} :=
  let q : domain hf φ → F := fun x ↦ φ (f x)
  let hq : ContMDiff I 𝓘(ℝ, F) m q := contMDiff_coordinate hf φ
  let hqr : IsRegularValue I 𝓘(ℝ, F) q (φ c) := regularValue_coordinate hm hf φ hc hreg
  letI := regularLevelChartedSpace (fun x _ ↦ (hq x).of_le hm) hqr rfl
  (levelHomeomorph hf φ hc).pullbackChartedSpace

private theorem isManifold_and_isSmoothEmbedding_of_chart (hm : 1 ≤ m)
    (hf : ContMDiff I J m f) (φ : PartialDiffeomorph J 𝓘(ℝ, F) N F m) (hc : c ∈ φ.source)
    (hreg : IsRegularValue I J f c) :
    letI := chartedSpaceOfChart hm hf φ hc hreg
    IsManifold 𝓘(ℝ, Fin (finrank ℝ E - finrank ℝ F) → ℝ) m {x : M // f x = c} ∧
    Manifold.IsSmoothEmbedding 𝓘(ℝ, Fin (finrank ℝ E - finrank ℝ F) → ℝ) I m
      (Subtype.val : {x : M // f x = c} → M) := by
  -- The coordinate-level and pullback instances below must match the unfolding of
  -- `chartedSpaceOfChart`; this lets the transported instances prove the stated properties.
  let K := 𝓘(ℝ, Fin (finrank ℝ E - finrank ℝ F) → ℝ)
  let q : domain hf φ → F := fun x ↦ φ (f x)
  have hq : ContMDiff I 𝓘(ℝ, F) m q := contMDiff_coordinate hf φ
  have hqr : IsRegularValue I 𝓘(ℝ, F) q (φ c) := regularValue_coordinate hm hf φ hc hreg
  let := regularLevelChartedSpace (fun x _ ↦ (hq x).of_le hm) hqr rfl
  have := isManifold_regularLevel hm (fun x _ ↦ hq x) hqr rfl
  -- Transfer its atlas, then compose its inclusion with the open inclusion into `M`.
  let e := levelHomeomorph hf φ hc
  let := e.pullbackChartedSpace (H := Fin (finrank ℝ E - finrank ℝ F) → ℝ)
  have := e.pullback_isManifold K m
  refine ⟨inferInstance, ?_⟩
  have hlev := isImmersionOfComplement_coe_regularLevel hm
    (fun x _ ↦ hq x) hqr rfl
  have hpre := isImmersionOfComplement_comp_diffeomorph (e.pullbackDiffeomorph K m) hlev
  rw [Homeomorph.coe_pullbackDiffeomorph] at hpre
  have hpost := isImmersionOfComplement_isLocalDiffeomorphAt_comp
    (fun x ↦ isLocalDiffeomorph_subtype_val (I := I) (n := m)
      (U := domain hf φ) (e x).1) hpre
  have heq : (fun x : {x : M // f x = c} ↦ ((e x).1 : M)) = Subtype.val :=
    funext (coe_levelHomeomorph hf φ hc)
  simp only [comp_def] at hpost
  rw [heq] at hpost
  exact ⟨hpost.isImmersion, Topology.IsEmbedding.subtypeVal⟩

/-- A regular fibre with the atlas constructed in any target chart containing its value is a
`C^m` manifold. -/
theorem isManifold_of_chart (hm : 1 ≤ m) (hf : ContMDiff I J m f)
    (φ : PartialDiffeomorph J 𝓘(ℝ, F) N F m) (hc : c ∈ φ.source)
    (hreg : IsRegularValue I J f c) :
    letI := chartedSpaceOfChart hm hf φ hc hreg
    IsManifold 𝓘(ℝ, Fin (finrank ℝ E - finrank ℝ F) → ℝ) m {x : M // f x = c} :=
  (isManifold_and_isSmoothEmbedding_of_chart hm hf φ hc hreg).1

/-- The inclusion of a regular fibre is a `C^m` smooth embedding for the atlas constructed in
any target chart containing its value. -/
theorem isSmoothEmbedding_coe_of_chart (hm : 1 ≤ m) (hf : ContMDiff I J m f)
    (φ : PartialDiffeomorph J 𝓘(ℝ, F) N F m) (hc : c ∈ φ.source)
    (hreg : IsRegularValue I J f c) :
    letI := chartedSpaceOfChart hm hf φ hc hreg
    Manifold.IsSmoothEmbedding 𝓘(ℝ, Fin (finrank ℝ E - finrank ℝ F) → ℝ) I m
      (Subtype.val : {x : M // f x = c} → M) :=
  (isManifold_and_isSmoothEmbedding_of_chart hm hf φ hc hreg).2

end RegularFiber

variable {E H M F G N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {m : ℕ∞ω} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I m M]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F] [TopologicalSpace G]
  {J : ModelWithCorners ℝ F G}
  [TopologicalSpace N] [ChartedSpace G N] [IsManifold J m N]
  {f : M → N} {c : N}

/-- The atlas on a regular fibre of a `C^m` map, `m ≥ 1`, over an interior value `c`, transported
from the regular level in the preferred extended target chart at `c`. It uses the subspace
topology and is not a global instance. -/
@[instance_reducible]
noncomputable def regularFiberChartedSpace (hm : 1 ≤ m) (hf : ContMDiff I J m f)
    (hc : J.IsInteriorPoint c) (hreg : IsRegularValue I J f c) :
    ChartedSpace (Fin (finrank ℝ E - finrank ℝ F) → ℝ) {x : M // f x = c} :=
  RegularFiber.chartedSpaceOfChart hm hf (extChartPartialDiffeomorph J m c)
    ((mem_extChartPartialDiffeomorph_source J m c).2 hc) hreg

omit [IsManifold I m M] in
/-- The preferred regular-fibre atlas uses the extended target chart at the value. This equation
allows comparisons with atlases constructed in other target charts without unfolding the atlas. -/
theorem regularFiberChartedSpace_eq_chartedSpaceOfChart (hm : 1 ≤ m) (hf : ContMDiff I J m f)
    (hc : J.IsInteriorPoint c) (hreg : IsRegularValue I J f c) :
    regularFiberChartedSpace hm hf hc hreg =
      RegularFiber.chartedSpaceOfChart hm hf (extChartPartialDiffeomorph J m c)
        ((mem_extChartPartialDiffeomorph_source J m c).2 hc) hreg :=
  (rfl)

/-- The regular fibre over an interior value with its preferred atlas is a `C^m` manifold. -/
theorem isManifold_regularFiber (hm : 1 ≤ m) (hf : ContMDiff I J m f)
    (hc : J.IsInteriorPoint c) (hreg : IsRegularValue I J f c) :
    letI := regularFiberChartedSpace hm hf hc hreg
    IsManifold 𝓘(ℝ, Fin (finrank ℝ E - finrank ℝ F) → ℝ) m {x : M // f x = c} :=
  (RegularFiber.isManifold_and_isSmoothEmbedding_of_chart hm hf
    (extChartPartialDiffeomorph J m c)
    ((mem_extChartPartialDiffeomorph_source J m c).2 hc) hreg).1

/-- The inclusion of the regular fibre over an interior value with its preferred atlas is a
`C^m` smooth embedding. -/
theorem isSmoothEmbedding_coe_regularFiber (hm : 1 ≤ m) (hf : ContMDiff I J m f)
    (hc : J.IsInteriorPoint c) (hreg : IsRegularValue I J f c) :
    letI := regularFiberChartedSpace hm hf hc hreg
    Manifold.IsSmoothEmbedding 𝓘(ℝ, Fin (finrank ℝ E - finrank ℝ F) → ℝ) I m
      (Subtype.val : {x : M // f x = c} → M) :=
  (RegularFiber.isManifold_and_isSmoothEmbedding_of_chart hm hf
    (extChartPartialDiffeomorph J m c)
    ((mem_extChartPartialDiffeomorph_source J m c).2 hc) hreg).2

/-- The tangent image of the regular-fibre inclusion is the kernel of the ambient differential. -/
theorem range_mfderiv_coe_regularFiber (hm : 1 ≤ m) (hf : ContMDiff I J m f)
    (hc : J.IsInteriorPoint c) (hreg : IsRegularValue I J f c) :
    letI := regularFiberChartedSpace hm hf hc hreg
    ∀ z : {x : M // f x = c},
      (mfderiv 𝓘(ℝ, Fin (finrank ℝ E - finrank ℝ F) → ℝ) I Subtype.val z).range =
        (mfderiv I J f z.1).ker := by
  let := regularFiberChartedSpace hm hf hc hreg
  have := isManifold_regularFiber hm hf hc hreg
  intro z
  have hdim := (hreg.isRegularPoint z.2).finrank_ker_mfderiv_add_finrank
  refine (hreg.isRegularPoint z.2).range_mfderiv_eq_ker_mfderiv
    (.of_forall fun w : {x : M // f x = c} ↦ w.2)
    ((isSmoothEmbedding_coe_regularFiber hm hf hc hreg).isImmersion.mfderiv_injective
      (ENat.one_le_iff_ne_zero_withTop.mp hm) z) ?_
  rw [finrank_fin_fun]
  omega

/-- **The regular-fibre theorem.** A regular fibre over an interior value of a `C^m` map,
`m ≥ 1`, from a finite-dimensional boundaryless real manifold to a finite-dimensional real
manifold admits a `C^m` manifold structure of dimension `dim M - dim N`, with its subspace
topology, for which the inclusion is a `C^m` smooth embedding and has tangent image `ker df`.
No separation or countability assumptions are needed, and an empty fibre is allowed. -/
theorem exists_regularFiber_smoothEmbedding (hm : 1 ≤ m) (hf : ContMDiff I J m f)
    (hc : J.IsInteriorPoint c) (hreg : IsRegularValue I J f c) :
    ∃ a : ChartedSpace (Fin (finrank ℝ E - finrank ℝ F) → ℝ) {x : M // f x = c},
      letI := a
      IsManifold 𝓘(ℝ, Fin (finrank ℝ E - finrank ℝ F) → ℝ) m {x : M // f x = c} ∧
      Manifold.IsSmoothEmbedding 𝓘(ℝ, Fin (finrank ℝ E - finrank ℝ F) → ℝ) I m
        (Subtype.val : {x : M // f x = c} → M) ∧
      ∀ z : {x : M // f x = c},
        (mfderiv 𝓘(ℝ, Fin (finrank ℝ E - finrank ℝ F) → ℝ) I Subtype.val z).range =
          (mfderiv I J f z.1).ker := by
  exact ⟨regularFiberChartedSpace hm hf hc hreg, isManifold_regularFiber hm hf hc hreg,
    isSmoothEmbedding_coe_regularFiber hm hf hc hreg,
    range_mfderiv_coe_regularFiber hm hf hc hreg⟩

end TauCeti

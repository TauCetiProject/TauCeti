/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Complex.FundamentalClass
public import TauCeti.Geometry.Manifold.VectorBundle.CauchyRiemann.Chart
public import TauCeti.Topology.VectorBundle.Orientation.Complex.EulerClass
public import TauCeti.Topology.VectorBundle.Orientation.SectionIndex.CauchyRiemann

/-!
# The zero count for the kernel of a real Cauchy–Riemann operator on a line bundle

Let `L` be a complex line bundle over a compact connected Riemann surface `X`, smooth as a real
vector bundle, and let `D` be a smooth real Cauchy–Riemann operator on `L`. A `C¹` section `s` with
`D s = 0` which is not identically zero has finitely many zeros, and their number is at most the
first Chern number `c₁(L)[X]`, the Euler class of `L` with its complex orientation
(`TauCeti.complexEulerClass`) evaluated on the fundamental class of `X`
(`TauCeti.IsRealCauchyRiemannOperator.ncard_le_evalFundamentalClass_complexEulerClass`). So a
section in the kernel vanishing at more than `c₁(L)[X]` points vanishes identically
(`TauCeti.IsRealCauchyRiemannOperator.eq_zero_of_evalFundamentalClass_complexEulerClass_lt_ncard`),
and if `c₁(L)[X] < 0` the kernel on `C¹` sections is zero
(`TauCeti.IsRealCauchyRiemannOperator.eq_zero_of_evalFundamentalClass_complexEulerClass_neg`).
This is the injectivity half of the vanishing theorem of McDuff–Salamon, Theorem C.1.10 (iii), in
the closed case.

The proof reads `s` in the charts of a finite bundle atlas, which are preferred charts of `X` and
preferred trivializations of `L`. There `D s = 0` reads `\bar∂ sᵢ = -Zᵢ sᵢ`
(`TauCeti.FiniteBundleAtlas.coord_tangentHom_eq_complexAntilinearPartL_fderiv_add_chartZeroOrder`),
with a bounded zeroth-order term `Zᵢ`
(`TauCeti.FiniteBundleAtlas.exists_norm_chartZeroOrder_apply_le`), so the reading satisfies the
Cauchy–Riemann inequality `‖\bar∂ sᵢ‖ ≤ C ‖sᵢ‖`
(`TauCeti.IsRealCauchyRiemannOperator.norm_conjWirtingerDeriv_coord_le`). The holomorphic charts
carry the canonical local orientation of `X` to that of `ℂ`, and the complex-linear trivializations
read the complex orientation of `L` as that of `ℂ`, so the zero count for sections solving a
Cauchy–Riemann inequality
(`ncard_le_evalFundamentalClass_eulerClass_of_norm_conjWirtingerDeriv_le` in the namespace
`TauCeti.VectorBundleOrientation`)
applies.

## Main results

* `TauCeti.IsRealCauchyRiemannOperator.norm_conjWirtingerDeriv_coord_le`: a section in the kernel
  satisfies a Cauchy–Riemann inequality in each chart of a finite bundle atlas.
* `TauCeti.IsRealCauchyRiemannOperator.ncard_le_evalFundamentalClass_complexEulerClass`: a nonzero
  `C¹` section in the kernel has finitely many zeros, at most `c₁(L)[X]` of them.
* `TauCeti.IsRealCauchyRiemannOperator.eq_zero_of_evalFundamentalClass_complexEulerClass_lt_ncard`
  and `TauCeti.IsRealCauchyRiemannOperator.eq_zero_of_evalFundamentalClass_complexEulerClass_neg`:
  the kernel is detected by values at `c₁(L)[X] + 1` points, and is zero if `c₁(L)[X] < 0`.

## Implementation notes

Kernel elements are assumed `C¹`. For the Sobolev realizations of `D` this needs elliptic
regularity of the kernel, which is not used here.

## References

* D. McDuff, D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition, AMS
  Colloquium Publications 52 (2012), Theorem C.1.10 (iii) and its proof (p. 603).
-/

public section

noncomputable section

open Bundle Module Set Filter Topology
open ContinuousLinearMap (complexAntilinearPartL)
open scoped Manifold ContDiff TauCeti.ComplexManifold

namespace TauCeti

open SmoothAlmostComplexStructure

namespace IsRealCauchyRiemannOperator

variable {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ∞ X] [T2Space X]
  {L : X → Type} [TopologicalSpace (TotalSpace ℂ L)] [∀ x, AddCommGroup (L x)]
  [∀ x, Module ℝ (L x)] [∀ x, Module ℂ (L x)] [∀ x, IsScalarTower ℝ ℂ (L x)]
  [∀ x, TopologicalSpace (L x)] [∀ x, IsTopologicalAddGroup (L x)] [∀ x, ContinuousSMul ℝ (L x)]
  [∀ x, ContinuousSMul ℂ (L x)] [FiberBundle ℂ L] [VectorBundle ℂ ℂ L]

local instance instVectorBundleRealZeroCount : VectorBundle ℝ ℂ L :=
  VectorBundle.restrictScalars ℝ ℂ ℂ L

variable [ContMDiffVectorBundle ∞ ℂ L 𝓘(ℝ, ℂ)]
  {D : (Π x : X, L x) → Π x : X, TangentSpace 𝓘(ℝ, ℂ) x →L[ℝ] L x}
  (hD : IsRealCauchyRiemannOperator ℂ (ofComplexManifold ℂ X) D)
  (hDs : ContMDiffCovariantDerivativeOn ℂ ∞ D univ)

include hD hDs in
/-- **A section in the kernel solves a Cauchy–Riemann inequality in each chart.** In chart `i` of a
finite bundle atlas, the reading `sᵢ` of a `C¹` section `s` with `D s = 0` satisfies
`‖\bar∂ sᵢ‖ ≤ C ‖sᵢ‖` on the chart image, for a constant `C` bounding the zeroth-order term of `D`
in that chart. -/
theorem norm_conjWirtingerDeriv_coord_le (A : FiniteBundleAtlas ℂ X ℂ L) (i : Fin A.n)
    {s : Π x, L x}
    (hs : ContMDiff 𝓘(ℝ, ℂ) (𝓘(ℝ, ℂ).prod 𝓘(ℝ, ℂ)) 1 fun x ↦ TotalSpace.mk' ℂ x (s x))
    (hs0 : D s = 0) :
    ∃ C, ∀ y ∈ A.image i, ‖conjWirtingerDeriv (A.coord i s) y‖ ≤ C * ‖A.coord i s y‖ := by
  obtain ⟨C, hC⟩ := A.exists_norm_chartZeroOrder_apply_le hD hDs i
  refine ⟨max C 0, fun y hy ↦ ?_⟩
  have h := A.coord_tangentHom_eq_complexAntilinearPartL_fderiv_add_chartZeroOrder hD hy
    ((hs _).mdifferentiableAt one_ne_zero)
  -- The reading of the one-form `D s = 0` is zero.
  rw [hs0, FiniteBundleAtlas.coord_tangentHom] at h
  simp only [Pi.zero_apply, ContinuousLinearMap.inCoordinates, ContinuousLinearMap.zero_comp,
    ContinuousLinearMap.comp_zero] at h
  have hbar : complexAntilinearPartL (fderiv ℝ (A.coord i s) y) =
      -A.chartZeroOrder D i y (A.coord i s y) := eq_neg_of_add_eq_zero_left h.symm
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun v ↦ ?_
  rw [conjWirtingerDeriv_apply_eq_complexAntilinearPartL, hbar, _root_.neg_apply,
    norm_neg]
  calc ‖A.chartZeroOrder D i y (A.coord i s y) v‖
      ≤ ‖A.chartZeroOrder D i y (A.coord i s y)‖ * ‖v‖ := ContinuousLinearMap.le_opNorm _ _
    _ ≤ max C 0 * ‖A.coord i s y‖ * ‖v‖ := by
      gcongr
      exact (hC y (subset_closure hy) _).trans (by gcongr; exact le_max_left _ _)

/-- A holomorphic chart carries the canonical local orientation of a Riemann surface at a point of
its source to the local orientation of `ℂ` selected by its standard orientation. -/
private theorem localHomologyMap_complexHomologicalOrientation (c : X) {z : X}
    (hz : z ∈ (chartAt ℂ c).source) :
    localHomologyMap (ModuleCat.of ℤ (ULift.{0} ℤ))
        (⟨fun x : (chartAt ℂ c).source ↦ chartAt ℂ c x - chartAt ℂ c z,
          (chartAt ℂ c).continuousOn.domRestrict.sub continuous_const⟩ :
            C((chartAt ℂ c).source, ℂ)) (S := {⟨z, hz⟩}) (T := {0})
        (by
          rintro x hx
          exact Subtype.ext ((chartAt ℂ c).injOn x.property hz (sub_eq_zero.1 hx))) (1 + 1)
        (((chartAt ℂ c).open_source.isOpenEmbedding_subtypeVal.localOrientationEquiv ⟨z, hz⟩
          (1 + 1)).symm (complexHomologicalOrientation X z)).val =
      (Complex.orientation.localOrientation Complex.finrank_real_complex).val := by
  set φ := chartAt ℂ c
  rw [complexHomologicalOrientation_apply_of_mem_maximalAtlas
    (IsManifold.chart_mem_maximalAtlas (I := 𝓘(ℂ)) (n := ∞) c) hz]
  have hσ : (((ContinuousLinearEquiv.refl ℝ ℂ : ℂ →L[ℝ] ℂ) : C(ℂ, ℂ)).comp
      ((⟨fun y ↦ y - φ z, by fun_prop⟩ : C(ℂ, ℂ)).comp φ.sourceRestrict)) =
      (⟨fun y : φ.source ↦ φ y - φ z,
        φ.continuousOn.domRestrict.sub continuous_const⟩ : C(φ.source, ℂ)) :=
    ContinuousMap.ext fun y ↦ congrArg (fun w ↦ w - φ z) (φ.sourceRestrict_apply y)
  have hφ := φ.localHomologyMap_chart_localOrientationOfOrientedChart hz
    (ContinuousLinearEquiv.refl ℝ ℂ) Complex.orientation
    Complex.finrank_real_complex Complex.finrank_real_complex (by
      rw [hσ]
      exact fun y hy ↦ Subtype.ext (φ.injOn y.property hz (sub_eq_zero.1 hy)))
  simp only [hσ] at hφ
  -- `Orientation.map` uses the underlying linear identity, rather than the continuous structure.
  have hid : (ContinuousLinearEquiv.refl ℝ ℂ).toLinearEquiv = LinearEquiv.refl ℝ ℂ := (rfl)
  simpa only [hid, Orientation.map_refl, Equiv.refl_apply] using hφ

include hD hDs in
/-- Around every point a `C¹` section in the kernel is read, in the preferred chart of `X` and
the preferred trivialization of `L` at some centre `c z`, as a `C¹` function on an open set `Ω z`
satisfying `‖\bar∂ f‖ ≤ C z ‖f‖`. -/
private theorem exists_chart_data [CompactSpace X] {s : Π x, L x}
    (hs : ContMDiff 𝓘(ℝ, ℂ) (𝓘(ℝ, ℂ).prod 𝓘(ℝ, ℂ)) 1 fun x ↦ TotalSpace.mk' ℂ x (s x))
    (hs0 : D s = 0) :
    ∃ (c : X → X) (Ω : X → Set ℂ) (C : X → ℝ), ∀ z, z ∈ (chartAt ℂ (c z)).source ∧
      z ∈ (trivializationAt ℂ L (c z)).baseSet ∧ IsOpen (Ω z) ∧ chartAt ℂ (c z) z ∈ Ω z ∧
      ContDiffOn ℝ 1 (fun y ↦ (trivializationAt ℂ L (c z) (TotalSpace.mk' ℂ
        ((chartAt ℂ (c z)).symm y) (s ((chartAt ℂ (c z)).symm y)))).2) (Ω z) ∧
      ∀ y ∈ Ω z, ‖conjWirtingerDeriv (fun y ↦ (trivializationAt ℂ L (c z) (TotalSpace.mk' ℂ
        ((chartAt ℂ (c z)).symm y) (s ((chartAt ℂ (c z)).symm y)))).2) y‖ ≤
        C z * ‖(trivializationAt ℂ L (c z) (TotalSpace.mk' ℂ
          ((chartAt ℂ (c z)).symm y) (s ((chartAt ℂ (c z)).symm y)))).2‖ := by
  obtain ⟨A⟩ := FiniteBundleAtlas.nonempty (E := ℂ) (M := X) (F := ℂ) (V := L)
  choose i hi using A.exists_mem_dom
  choose C hC using fun j ↦ norm_conjWirtingerDeriv_coord_le hD hDs A j hs hs0
  -- The readings of `s` in the charts of `A`.
  have hc (j : Fin A.n) : (fun y ↦ (trivializationAt ℂ L (A.center j) (TotalSpace.mk' ℂ
      ((chartAt ℂ (A.center j)).symm y) (s ((chartAt ℂ (A.center j)).symm y)))).2) =
        A.coord j s :=
    funext fun y ↦ (A.coord_def j s y).symm
  refine ⟨fun z ↦ A.center (i z), fun z ↦ A.image (i z), fun z ↦ C (i z), fun z ↦
    ⟨A.dom_subset_chart_source _ (hi z), A.dom_subset_baseSet _ (hi z), (A.image _).isOpen,
      A.mem_image.2 ⟨z, hi z, rfl⟩, ?_, ?_⟩⟩
  · rw [hc]
    -- The reading of `s` is `C¹` on the chart image, which lies over the base set.
    refine (A.contDiffOn_coord hs (i z)).mono fun y hy ↦ ?_
    obtain ⟨x, hx, rfl⟩ := A.mem_image.1 hy
    exact ⟨(A.chart _).map_source (A.dom_subset_chart_source _ hx), by
      rw [mem_preimage, (A.chart _).left_inv (A.dom_subset_chart_source _ hx)]
      exact A.dom_subset_baseSet _ hx⟩
  · intro y hy
    have h := hC (i z) y hy
    rw [A.coord_def (i z) s y] at h
    rwa [hc]

omit [IsManifold 𝓘(ℂ, ℂ) ∞ X] [ChartedSpace ℂ X] [T2Space X] [∀ x, IsTopologicalAddGroup (L x)]
  [∀ x, ContinuousSMul ℝ (L x)] [∀ x, ContinuousSMul ℂ (L x)]
  [ContMDiffVectorBundle ∞ ℂ L 𝓘(ℝ, ℂ)] in
/-- The preferred trivializations of `L` read its complex orientation as the standard orientation
of `ℂ`. -/
private theorem mapOrientation_complex_trivializationAt (c : X) {x : X}
    (hx : x ∈ (trivializationAt ℂ L c).baseSet) :
    (trivializationAt ℂ L c).mapOrientation (Fin (1 + 1)) hx
        (VectorBundleOrientation.reindex (finCongr (by rw [finrank_self]))
          (VectorBundleOrientation.complex ℂ L) x) = Complex.orientation :=
  (VectorBundleOrientation.mapOrientation_reindex_complex ℂ L _ _ hx).trans
    reindex_complexOrientation_complex

variable [CompactSpace X]

include hD hDs in
/-- **The zeros of a nonzero section in the kernel are finite in number.** On a compact connected
Riemann surface, a `C¹` section of a complex line bundle in the kernel of a smooth real
Cauchy–Riemann operator, not identically zero, has finitely many zeros. -/
theorem finite_setOf_eq_zero [ConnectedSpace X] {s : Π x, L x}
    (hs : ContMDiff 𝓘(ℝ, ℂ) (𝓘(ℝ, ℂ).prod 𝓘(ℝ, ℂ)) 1 fun x ↦ TotalSpace.mk' ℂ x (s x))
    (hs0 : D s = 0) (hne : ∃ x, s x ≠ 0) : {x | s x = 0}.Finite := by
  obtain ⟨c, Ω, C, h⟩ := exists_chart_data hD hDs hs hs0
  exact finite_setOf_section_eq_zero_of_norm_conjWirtingerDeriv_le (fun z ↦ chartAt ℂ (c z))
    (fun z ↦ trivializationAt ℂ L (c z)) (fun z ↦ (h z).1) (fun z ↦ (h z).2.1) Ω
    (fun z ↦ (h z).2.2.1) (fun z ↦ (h z).2.2.2.1) (fun z ↦ (h z).2.2.2.2.1) (fun z _ ↦ C z)
    (fun z _ _ ↦ ⟨C z, Eventually.of_forall fun _ ↦ le_rfl⟩) (fun z ↦ (h z).2.2.2.2.2) hne

include hD hDs in
/-- **The zero count.** On a compact Riemann surface, a `C¹` section of a complex line bundle `L`
in the kernel of a smooth real Cauchy–Riemann operator, with finitely many zeros, has at most
`c₁(L)[X]` zeros: the Euler class of `L` with its complex orientation, evaluated on the
fundamental class of `X`. -/
theorem ncard_le_evalFundamentalClass_complexEulerClass {s : Π x, L x}
    (hs : ContMDiff 𝓘(ℝ, ℂ) (𝓘(ℝ, ℂ).prod 𝓘(ℝ, ℂ)) 1 fun x ↦ TotalSpace.mk' ℂ x (s x))
    (hs0 : D s = 0) (hZ : {x | s x = 0}.Finite) :
    ({x | s x = 0}.ncard : ℤ) ≤
      ((complexHomologicalOrientation X).evalFundamentalClass Complex.finrank_real_complex
        (ModuleCat.of ℤ (ULift.{0} ℤ)) (ContinuousMap.id X)
        (complexEulerClass ℂ L (r := 0) (finrank_self ℂ))).down := by
  obtain ⟨c, Ω, C, h⟩ := exists_chart_data hD hDs hs hs0
  rw [complexEulerClass_def]
  exact
    VectorBundleOrientation.ncard_le_evalFundamentalClass_eulerClass_of_norm_conjWirtingerDeriv_le
    _ Complex.finrank_real_complex _ hs.continuous (fun z ↦ chartAt ℂ (c z))
    (fun z ↦ trivializationAt ℂ L (c z)) (fun _ ↦ Complex.orientation) (fun z _ ↦ (h z).1) Ω
    (fun z _ ↦ C z) hZ (fun z _ ↦ (h z).2.1)
    (fun z _ ↦ Eventually.of_forall fun x hx ↦ mapOrientation_complex_trivializationAt (c z) hx)
    (fun z _ ↦ localHomologyMap_complexHomologicalOrientation (c z) (h z).1)
    (fun z _ ↦ (h z).2.2.1) (fun z _ ↦ (h z).2.2.2.1) (fun z _ ↦ (h z).2.2.2.2.1)
    (fun z _ _ _ ↦ ⟨C z, Eventually.of_forall fun _ ↦ le_rfl⟩) (fun z _ ↦ (h z).2.2.2.2.2)

include hD hDs in
/-- **A section in the kernel vanishing at more than `c₁(L)[X]` points vanishes identically.** On
a compact connected Riemann surface, a `C¹` section of a complex line bundle `L` in the kernel of a
smooth real Cauchy–Riemann operator which vanishes on a set with more than `c₁(L)[X]` points is
zero. -/
theorem eq_zero_of_evalFundamentalClass_complexEulerClass_lt_ncard [ConnectedSpace X]
    {s : Π x, L x}
    (hs : ContMDiff 𝓘(ℝ, ℂ) (𝓘(ℝ, ℂ).prod 𝓘(ℝ, ℂ)) 1 fun x ↦ TotalSpace.mk' ℂ x (s x))
    (hs0 : D s = 0) {S : Set X} (hS : ∀ x ∈ S, s x = 0)
    (hlt : ((complexHomologicalOrientation X).evalFundamentalClass Complex.finrank_real_complex
        (ModuleCat.of ℤ (ULift.{0} ℤ)) (ContinuousMap.id X)
        (complexEulerClass ℂ L (r := 0) (finrank_self ℂ))).down < S.ncard) :
    s = 0 := by
  by_contra hne
  obtain ⟨x, hx⟩ := Function.ne_iff.1 hne
  have hZ := finite_setOf_eq_zero hD hDs hs hs0 ⟨x, hx⟩
  have hle := ncard_le_evalFundamentalClass_complexEulerClass hD hDs hs hs0 hZ
  have hSZ : S.ncard ≤ {x | s x = 0}.ncard := ncard_le_ncard hS hZ
  omega

include hD hDs in
/-- **Vanishing of the kernel in negative degree.** On a compact connected Riemann surface, if the
first Chern number `c₁(L)[X]` of a complex line bundle `L` is negative, every `C¹` section of `L` in
the kernel of a smooth real Cauchy–Riemann operator is zero. -/
theorem eq_zero_of_evalFundamentalClass_complexEulerClass_neg [ConnectedSpace X]
    (hneg : ((complexHomologicalOrientation X).evalFundamentalClass Complex.finrank_real_complex
        (ModuleCat.of ℤ (ULift.{0} ℤ)) (ContinuousMap.id X)
        (complexEulerClass ℂ L (r := 0) (finrank_self ℂ))).down < 0)
    {s : Π x, L x}
    (hs : ContMDiff 𝓘(ℝ, ℂ) (𝓘(ℝ, ℂ).prod 𝓘(ℝ, ℂ)) 1 fun x ↦ TotalSpace.mk' ℂ x (s x))
    (hs0 : D s = 0) : s = 0 :=
  eq_zero_of_evalFundamentalClass_complexEulerClass_lt_ncard hD hDs hs hs0
    (S := ∅) (fun _ h ↦ h.elim) (by simpa using hneg)

end IsRealCauchyRiemannOperator

end TauCeti

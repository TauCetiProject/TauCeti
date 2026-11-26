/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Sobolev.Pseudoholomorphic
public import TauCeti.Geometry.Manifold.Sobolev.LocalMap.Atlas.Higher
import TauCeti.Analysis.Complex.CauchyRiemann.Weak.Bootstrap

/-!
# Interior regularity of weak pseudoholomorphic maps

Let `X` be a Riemann surface, `M` a manifold modelled on a boundaryless model `I` with
finite-dimensional model vector space `E`, and `J`, `ν` a domain-dependent almost complex
structure on `M` and an inhomogeneous term, both of class `C^ℓ`. A weak pseudoholomorphic map
`u` on an open set `s ⊆ X` (`TauCeti.IsWeakPseudoholomorphicOn J ν p u s`) gains `ℓ`
derivatives: for finite `p > 2` it lies in `W^{k+1,p}_loc` on `s` for every `k ≤ ℓ`, and for every
`p > 2`, including `p = ∞`, it is of class `C^ℓ` on `s`. As a corollary, a `C¹` map that is
pseudoholomorphic for a smooth almost complex structure is smooth. This is the interior case of
McDuff–Salamon, Theorem B.4.1 and Remark B.4.3.

The proof is local. In the preferred charts at `x ∈ X` and `y ∈ M`, the coordinate expression
of `u` solves the planar equation `∂ₛw + J_xy(z, w) ∂ₜw = η_xy(z, w)`, whose coefficients
`ContMDiffAlmostComplexStructureFamily.chartField` and `InhomogeneousTerm.chartTerm` are `C^ℓ`
jointly in `(z, w)` on the product of the chart targets
(`ContMDiffAlmostComplexStructureFamily.contDiffOn_chartField_chartAt`,
`InhomogeneousTerm.contDiffOn_chartTerm_chartAt`) and satisfy `J_xy² = -1` there. The planar
bootstrapping theorems `TauCeti.memWkpLoc_of_isWeakCauchyRiemannOn` and
`TauCeti.contDiffOn_of_isWeakCauchyRiemannOn` then apply in each pair of charts, and testing the
preferred charts suffices for both conclusions
(`TauCeti.memWkpLocMapOn_iff_chartAt_of_two_lt` and `contMDiffOn_iff`).

## Main results

* `TauCeti.IsWeakPseudoholomorphicOn.memWkpLocMapOn_succ`,
  `TauCeti.IsWeakPseudoholomorphic.memWkpLocMap_succ`: for `2 < p < ∞` and `k ≤ ℓ`, a weak
  pseudoholomorphic map is in `W^{k+1,p}_loc`. At `ℓ = 1` this is `W^{2,p}_loc`, hence `C¹`.
* `TauCeti.IsWeakPseudoholomorphicOn.contMDiffOn`, `TauCeti.IsWeakPseudoholomorphic.contMDiff`:
  for every `p > 2`, including `p = ∞`, a weak pseudoholomorphic map is of class `C^ℓ`, and
  smooth when `J` and `ν` are smooth.
* `TauCeti.IsPseudoholomorphicOn.contMDiffOn`, `TauCeti.IsPseudoholomorphic.contMDiff`: a `C¹`
  pseudoholomorphic map for a smooth almost complex structure is smooth.
* `TauCeti.contMDiffOn_of_mfderiv_stdComplexLineImag_eq`,
  `TauCeti.contMDiff_of_mfderiv_stdComplexLineImag_eq`: the same for a map of the plane `ℝ × ℝ`
  solving `∂ₜu = J(u) ∂ₛu`, the form in which bubbles of Floer solutions arise.

## Implementation notes

The Sobolev conclusion needs `p < ∞`: a `W^{1,∞}` solution for a `C¹` structure need not be
`W^{2,∞}` (`TauCeti.not_memWkpLoc_two_top_graph_logLogExample`). The `C^ℓ` conclusion holds for
`p = ∞` as well, since a `W^{1,∞}_loc` solution is a `W^{1,q}_loc` solution for finite `q > 2`.
Boundary regularity, for maps sending the boundary of a bordered surface into a totally real
submanifold, is not treated here.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Appendix B.4 (Theorem B.4.1 and Remark B.4.3).
-/

public section

open Set Filter TopologicalSpace MeasureTheory
open scoped Manifold ContDiff Topology TauCeti.ComplexManifold

noncomputable section

namespace TauCeti

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ∞ X]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] {ℓ : ℕ∞}
  {J : ContMDiffAlmostComplexStructureFamily I M 𝓘(ℝ, ℂ) X ℓ}
  {ν : InhomogeneousTerm ((SmoothAlmostComplexStructure.ofComplexManifold ℂ X).toContMDiff ℓ) J}
  {p : ENNReal} {u : X → M} {s : Set X}

namespace IsWeakPseudoholomorphicOn

omit [FiniteDimensional ℝ E] in
/-- In the preferred charts at `x` and `y`, a weak pseudoholomorphic map on an open set is a
weak solution of the planar equation whose coefficients are `C^ℓ` on the product of the chart
targets and square to `-1` there. This packages the hypotheses of the planar bootstrapping
theorems. -/
private theorem chartAt_data (h : IsWeakPseudoholomorphicOn J ν p u s) (hs : IsOpen s)
    (x : X) (y : M) :
    ∃ Ω : Opens ℂ, (Ω : Set ℂ) =
        (chartAt ℂ x).target ∩ (chartAt ℂ x).symm ⁻¹' (s ∩ u ⁻¹' (chartAt H y).source) ∧
      IsOpen ((chartAt ℂ x).target ×ˢ (extChartAt I y).target) ∧
      (∀ z ∈ Ω, (z, (extChartAt I y ∘ u ∘ (chartAt ℂ x).symm) z) ∈
        (chartAt ℂ x).target ×ˢ (extChartAt I y).target) ∧
      (∀ᵐ z ∂volume.restrict Ω,
        J.chartField (chartAt ℂ x) ((chartAt H y).extendTrans I (Homeomorph.refl E)) z
            ((extChartAt I y ∘ u ∘ (chartAt ℂ x).symm) z) *
          J.chartField (chartAt ℂ x) ((chartAt H y).extendTrans I (Homeomorph.refl E)) z
            ((extChartAt I y ∘ u ∘ (chartAt ℂ x).symm) z) = -1) ∧
      IsWeakCauchyRiemannOn p Ω
        (J.chartField (chartAt ℂ x) ((chartAt H y).extendTrans I (Homeomorph.refl E)))
        (ν.chartTerm (chartAt ℂ x) ((chartAt H y).extendTrans I (Homeomorph.refl E)))
        (extChartAt I y ∘ u ∘ (chartAt ℂ x).symm) := by
  have hΩ : IsOpen
      ((chartAt ℂ x).target ∩ (chartAt ℂ x).symm ⁻¹' (s ∩ u ⁻¹' (chartAt H y).source)) :=
    (chartAt ℂ x).isOpen_inter_preimage_symm
      (h.continuousOn.isOpen_inter_preimage hs (chartAt H y).open_source)
  have huW : ∀ z ∈ (chartAt ℂ x).target ∩ (chartAt ℂ x).symm ⁻¹' (s ∩ u ⁻¹' (chartAt H y).source),
      (z, (extChartAt I y ∘ u ∘ (chartAt ℂ x).symm) z) ∈
        (chartAt ℂ x).target ×ˢ (extChartAt I y).target := fun z hz ↦
    ⟨hz.1, (extChartAt I y).map_source (by rw [extChartAt_source]; exact hz.2.2)⟩
  refine ⟨⟨_, hΩ⟩, rfl, (chartAt ℂ x).open_target.prod (isOpen_extChartAt_target y), huW,
    ae_restrict_of_forall_mem hΩ.measurableSet fun z hz ↦ ?_, ?_⟩
  · ext w
    exact J.chartField_chartAt_apply_apply x y z (huW z hz).2 w
  · have h' := h.isWeakCauchyRiemannOn_chart (IsManifold.chart_mem_maximalAtlas x)
      (IsManifold.chart_mem_maximalAtlas y)
    rwa [OpenPartialHomeomorph.coe_extendTrans_refl] at h'

/-- **Interior elliptic bootstrapping for maps from a Riemann surface** (McDuff–Salamon,
Theorem B.4.1 and Remark B.4.3, interior case). Let `2 < p < ∞` and let `J` and `ν` be of class
`C^ℓ`. A weak pseudoholomorphic map on an open set `s` lies in `W^{k+1,p}_loc` on `s` for every
`k ≤ ℓ`; for finite `ℓ` this is `W^{ℓ+1,p}_loc`. -/
theorem memWkpLocMapOn_succ (h : IsWeakPseudoholomorphicOn J ν p u s) (hs : IsOpen s)
    (hp : 2 < p) (hp' : p ≠ ⊤) {k : ℕ} (hk : (k : ℕ∞) ≤ ℓ) :
    MemWkpLocMapOn I p (k + 1) u s := by
  rw [memWkpLocMapOn_iff_chartAt_of_two_lt hp hp' hs]
  refine ⟨h.continuousOn, fun x y ↦ ?_⟩
  obtain ⟨Ω, hΩ, hW, huW, hJ2, hcr⟩ := h.chartAt_data hs x y
  have hk' : ((k : ℕ∞) : WithTop ℕ∞) ≤ ℓ := by exact_mod_cast hk
  rw [← hΩ]
  exact memWkpLoc_of_isWeakCauchyRiemannOn hp hp' hW
    ((J.contDiffOn_chartField_chartAt x y).of_le hk')
    ((ν.contDiffOn_chartTerm_chartAt x y).of_le hk') huW hJ2 hcr

/-- **Interior regularity of weak pseudoholomorphic maps** (McDuff–Salamon, Remark B.4.3,
interior case). Let `p > 2`, possibly `p = ∞`, and let `J` and `ν` be of class `C^ℓ`, `ℓ ≤ ∞`.
A weak pseudoholomorphic map on an open set `s` is of class `C^ℓ` on `s`; in particular it is
smooth there when `J` and `ν` are smooth. -/
theorem contMDiffOn (h : IsWeakPseudoholomorphicOn J ν p u s) (hs : IsOpen s) (hp : 2 < p) :
    ContMDiffOn 𝓘(ℝ, ℂ) I ℓ u s := by
  have : IsManifold 𝓘(ℝ, ℂ) ℓ X := .of_le (n := ∞) (by exact_mod_cast le_top)
  have : IsManifold I ℓ M := .of_le (n := ∞) (by exact_mod_cast le_top)
  rw [contMDiffOn_iff]
  refine ⟨h.continuousOn, fun x y ↦ ?_⟩
  obtain ⟨Ω, hΩ, hW, huW, hJ2, hcr⟩ := h.chartAt_data hs x y
  have hc := contDiffOn_of_isWeakCauchyRiemannOn hp hW (J.contDiffOn_chartField_chartAt x y)
    (ν.contDiffOn_chartTerm_chartAt x y) huW hJ2 hcr
  rw [hΩ] at hc
  simpa [extChartAt_source] using hc

end IsWeakPseudoholomorphicOn

namespace IsWeakPseudoholomorphic

/-- **Interior elliptic bootstrapping on the whole surface.** For `2 < p < ∞` and `J`, `ν` of
class `C^ℓ`, a weak pseudoholomorphic map lies in `W^{k+1,p}_loc` for every `k ≤ ℓ`. -/
theorem memWkpLocMap_succ (h : IsWeakPseudoholomorphic J ν p u) (hp : 2 < p) (hp' : p ≠ ⊤)
    {k : ℕ} (hk : (k : ℕ∞) ≤ ℓ) : MemWkpLocMap I p (k + 1) u :=
  memWkpLocMapOnGroupoid_univ.1
    ((isWeakPseudoholomorphicOn_univ.2 h).memWkpLocMapOn_succ isOpen_univ hp hp' hk)

/-- **Interior regularity on the whole surface.** For `p > 2`, possibly `p = ∞`, and `J`, `ν` of
class `C^ℓ`, a weak pseudoholomorphic map is of class `C^ℓ`. -/
theorem contMDiff (h : IsWeakPseudoholomorphic J ν p u) (hp : 2 < p) :
    ContMDiff 𝓘(ℝ, ℂ) I ℓ u :=
  contMDiffOn_univ.1 ((isWeakPseudoholomorphicOn_univ.2 h).contMDiffOn isOpen_univ hp)

end IsWeakPseudoholomorphic

/-- **`C¹` pseudoholomorphic maps are smooth** (McDuff–Salamon, Remark B.4.3, interior case).
A map from a Riemann surface that is of class `C¹` and pseudoholomorphic on an open set `s` for a
smooth almost complex structure `J₀` is smooth on `s`. -/
theorem IsPseudoholomorphicOn.contMDiffOn {J₀ : SmoothAlmostComplexStructure I M}
    (h : IsPseudoholomorphicOn (SmoothAlmostComplexStructure.ofComplexManifold ℂ X) J₀ u s)
    (hs : IsOpen s) (hu : ContMDiffOn 𝓘(ℝ, ℂ) I 1 u s) : ContMDiffOn 𝓘(ℝ, ℂ) I ∞ u s :=
  ((isWeakPseudoholomorphicOn_iff_isPseudoholomorphicOn (ℓ := ⊤) (p := 3) J₀ hs hu).2 h).contMDiffOn
    hs (by norm_num)

/-- **`C¹` pseudoholomorphic maps are smooth.** A map from a Riemann surface that is of class
`C¹` and pseudoholomorphic for a smooth almost complex structure `J₀` is smooth. -/
theorem IsPseudoholomorphic.contMDiff {J₀ : SmoothAlmostComplexStructure I M}
    (h : IsPseudoholomorphic (SmoothAlmostComplexStructure.ofComplexManifold ℂ X) J₀ u)
    (hu : ContMDiff 𝓘(ℝ, ℂ) I 1 u) : ContMDiff 𝓘(ℝ, ℂ) I ∞ u :=
  contMDiffOn_univ.1 ((isPseudoholomorphicOn_univ.2 h).contMDiffOn isOpen_univ hu.contMDiffOn)

/-- **`C¹` pseudoholomorphic maps of the plane are smooth.** Let `J₀` be a smooth almost complex
structure on `M`. A map `u : ℝ × ℝ → M` of class `C¹` on an open set `U` which solves the
Cauchy–Riemann equation `∂ₜu = J₀(u) ∂ₛu` on `U` is smooth on `U`. This is
`TauCeti.IsPseudoholomorphicOn.contMDiffOn` for the Riemann surface `ℂ`, read in the real
coordinates `Complex.equivRealProdCLM`. -/
theorem contMDiffOn_of_mfderiv_stdComplexLineImag_eq {J₀ : SmoothAlmostComplexStructure I M}
    {u : ℝ × ℝ → M} {U : Set (ℝ × ℝ)} (hU : IsOpen U) (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u U)
    (hCR : ∀ z ∈ U, mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag =
      J₀ (u z) (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)) :
    ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I ∞ u U := by
  set e : ℂ ≃L[ℝ] ℝ × ℝ := Complex.equivRealProdCLM
  have he : MapsTo e (e ⁻¹' U) U := fun _ hz ↦ hz
  -- Read `u` on the Riemann surface `ℂ`, where it is pseudoholomorphic.
  have hhol : IsPseudoholomorphicOn (SmoothAlmostComplexStructure.ofComplexManifold ℂ ℂ) J₀
      (u ∘ e) (e ⁻¹' U) := by
    refine isPseudoholomorphicOn_iff.2 fun z hz ↦ ?_
    have hdiff : MDifferentiableAt 𝓘(ℝ, ℝ × ℝ) I u (e z) :=
      ((hu _ hz).contMDiffAt (hU.mem_nhds hz)).mdifferentiableAt one_ne_zero
    have hez := isPseudoholomorphic_iff.1 isPseudoholomorphic_equivRealProdCLM z
    exact (((isPseudoholomorphicAt_stdComplexLine_iff J₀ u (e z)).2
      ⟨_, hdiff.hasMFDerivAt, hCR _ hz⟩).comp hez).isPseudoholomorphicWithinAt
  have hsmooth := hhol.contMDiffOn (hU.preimage e.continuous)
    (hu.comp e.contDiff.contMDiff.contMDiffOn he)
  exact (hsmooth.comp e.symm.contDiff.contMDiff.contMDiffOn fun y hy ↦ by simpa using hy).congr
    fun y _ ↦ by simp

/-- **`C¹` pseudoholomorphic planes are smooth.** Let `J₀` be a smooth almost complex structure
on `M`. A `C¹` map `u : ℝ × ℝ → M` solving the Cauchy–Riemann equation `∂ₜu = J₀(u) ∂ₛu` is
smooth. -/
theorem contMDiff_of_mfderiv_stdComplexLineImag_eq {J₀ : SmoothAlmostComplexStructure I M}
    {u : ℝ × ℝ → M} (hu : ContMDiff 𝓘(ℝ, ℝ × ℝ) I 1 u)
    (hCR : ∀ z, mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag =
      J₀ (u z) (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)) :
    ContMDiff 𝓘(ℝ, ℝ × ℝ) I ∞ u :=
  contMDiffOn_univ.1 <|
    contMDiffOn_of_mfderiv_stdComplexLineImag_eq isOpen_univ hu.contMDiffOn fun z _ ↦ hCR z

end TauCeti

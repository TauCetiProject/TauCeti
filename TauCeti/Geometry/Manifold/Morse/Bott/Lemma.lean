/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.Immersion
public import Mathlib.Geometry.Manifold.LocalDiffeomorph
public import TauCeti.Geometry.Manifold.Morse.Bott.Basic
import TauCeti.Analysis.Calculus.Bilinear
import TauCeti.Analysis.Calculus.BumpFunction.Cutoff
import TauCeti.Analysis.Calculus.Morse.Parametric
import TauCeti.Analysis.Calculus.SecondDerivative
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Basic
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Constructions
import TauCeti.Geometry.Manifold.MFDeriv.Chart.Basic
import TauCeti.Topology.Algebra.Module.BilinearForm

/-!
# The Morse–Bott lemma

Let `i : S → M` be a Morse–Bott critical submanifold of a function `f` on a finite-dimensional
boundaryless manifold `M` (`TauCeti.SmoothEmbedding.IsNondegenerateCriticalSubmanifold`): every
point of its image is critical, and the kernel of the critical Hessian there is the tangent space
of the image. The Morse–Bott lemma says that, near each point of the submanifold, `f` is a
nondegenerate quadratic form in the normal directions. Here it is proved in a slice chart: if `i`
is an immersion at `s₀` with complement `F`, so that `M` has coordinates in `E' × F` near `i s₀`
in which `i` is `u ↦ (u, 0)`, there is a smooth chart `Φ` of `M` near `i s₀` with values in
`E' × F`

* in which the points of the submanifold are exactly the points of the zero section, and
* in which, on every fibre, `f` is half its vertical Hessian quadratic form plus its value on the
  zero section: `f (Φ⁻¹ (b, v)) = f (Φ⁻¹ (b, 0)) + (1/2) Q_b (v, v)`, where `Q_b` is the Hessian
  of `v ↦ f (Φ⁻¹ (b, v))` at `0`, an invertible bilinear form

(`TauCeti.SmoothEmbedding.IsNondegenerateCriticalSubmanifold.exists_morseBott_chart`). This is the
converse of the model example `TauCeti.SmoothEmbedding.isNondegenerateCriticalSubmanifold_comp_snd`:
every Morse–Bott critical submanifold is locally the zero section of a family of nondegenerate
quadratic forms. It is the local input for attaching the negative normal disc bundle of a critical
submanifold when a sublevel passes a Morse–Bott critical level.

In the slice coordinates of the immersion, every point `(b, 0)` of the zero section is critical,
so the Hessian of the coordinate expression vanishes on the tangent directions `E' × 0`. Its kernel
has the dimension of the kernel of the critical Hessian, which by the Morse–Bott condition is at
most `dim E'`; so the kernel is exactly `E' × 0` and the vertical Hessian on `0 × F` is invertible.
The parametric Morse lemma for a function defined near the zero section
(`TauCeti.exists_parametric_morse_chart_of_contDiffOn`), whose change of coordinates preserves the
base point `b` and fixes the zero section, then gives the chart.

## Main declarations

* `TauCeti.SmoothEmbedding.IsNondegenerateCriticalSubmanifold.exists_morseBott_chart`: the
  Morse–Bott lemma, as a slice chart in which the function is a fibrewise nondegenerate quadratic
  form.

## References

* R. Bott, *Nondegenerate critical manifolds*, Annals of Mathematics 60 (1954), 248–261.
* A. Banyaga and D. E. Hurtubise, *A proof of the Morse–Bott lemma*, Expositiones Mathematicae 22
  (2004), 365–373.
* R. S. Palais, *Morse theory on Hilbert manifolds*, Topology 2 (1963), 299–340, Section 2, for
  the operator square root proof of the parametric Morse lemma.
-/

public section

open Filter Function Set Topology
open scoped ContDiff Manifold

noncomputable section

namespace TauCeti

namespace SmoothEmbedding

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [I.Boundaryless] [TopologicalSpace M] [ChartedSpace H M]
  {E' H' S : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
  {J : ModelWithCorners ℝ E' H'} [TopologicalSpace S] [ChartedSpace H' S]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {f : M → ℝ} {i : SmoothEmbedding J I ∞ S M} {s₀ : S}

section Slice

variable (hi : Manifold.IsImmersionAtOfComplement F J I ∞ i s₀)
include hi

omit [I.Boundaryless] in
/-- In the slice coordinates of an immersion, the zero section is the image of the immersion. -/
private theorem codChart_extend_symm_equiv_mk_zero {b : E'}
    (hb : b ∈ (hi.domChart.extend J).target) :
    (hi.codChart.extend I).symm (hi.equiv (b, 0)) = i ((hi.domChart.extend J).symm b) := by
  have hs : (hi.domChart.extend J).symm b ∈ hi.domChart.source := by
    simpa only [OpenPartialHomeomorph.extend_source] using (hi.domChart.extend J).map_target hb
  have hx : i ((hi.domChart.extend J).symm b) ∈ (hi.codChart.extend I).source := by
    rw [OpenPartialHomeomorph.extend_source]
    exact hi.source_subset_preimage_source hs
  rw [← (hi.codChart.extend I).left_inv hx]
  exact congrArg _ (hi.writtenInCharts hb).symm

omit [I.Boundaryless] in
/-- In the slice coordinates of an immersion, a point of the immersed manifold in the source of
the domain chart goes to the zero section. -/
private theorem equiv_symm_codChart_extend {s : S} (hs : s ∈ hi.domChart.source) :
    hi.equiv.symm (hi.codChart.extend I (i s)) = (hi.domChart.extend J s, 0) := by
  have hb : hi.domChart.extend J s ∈ (hi.domChart.extend J).target :=
    (hi.domChart.extend J).map_source (by rwa [OpenPartialHomeomorph.extend_source])
  have hw := hi.writtenInCharts hb
  rw [comp_apply, comp_apply, (hi.domChart.extend J).left_inv
    (by rwa [OpenPartialHomeomorph.extend_source])] at hw
  rw [hw, comp_apply, ContinuousLinearEquiv.symm_apply_apply]

/-- In the slice coordinates of an immersion onto critical points, the zero section is critical
for the coordinate expression of the function. -/
private theorem fderiv_comp_equiv_eq_zero (h : i.IsCriticalSubmanifold f)
    {b : E'} (hb : b ∈ (hi.domChart.extend J).target) :
    fderiv ℝ ((f ∘ (hi.codChart.extend I).symm) ∘ hi.equiv) (b, 0) = 0 := by
  have he : hi.codChart ∈ IsManifold.maximalAtlas I 1 M :=
    IsManifold.maximalAtlas_subset_of_le (by simp) hi.codChart_mem_maximalAtlas
  set s := (hi.domChart.extend J).symm b
  have hs : s ∈ hi.domChart.source := by
    simpa only [OpenPartialHomeomorph.extend_source] using (hi.domChart.extend J).map_target hb
  have hx : i s ∈ hi.codChart.source := hi.source_subset_preimage_source hs
  have hL : hi.equiv (b, 0) = hi.codChart.extend I (i s) := (hi.writtenInCharts hb).symm
  rw [ContinuousLinearEquiv.comp_right_fderiv, hL,
    (mvfderiv_eq_zero_iff_fderiv_comp_extend_symm_eq_zero he hx
      ((h.contMDiffAt s).mdifferentiableAt two_ne_zero)).1
      (mem_criticalPoints.1 (h.mem_criticalPoints s)),
    ContinuousLinearMap.zero_comp]

omit [I.Boundaryless] in
/-- The model space of the immersed manifold is finite dimensional when the ambient one is. -/
private theorem finiteDimensional_domain [FiniteDimensional ℝ E] : FiniteDimensional ℝ E' :=
  FiniteDimensional.of_injective ((hi.equiv : E' × F →L[ℝ] E).toLinearMap ∘ₗ LinearMap.inl ℝ E' F)
    (hi.equiv.injective.comp LinearMap.inl_injective)

omit [I.Boundaryless] in
/-- The complement of an immersion is finite dimensional when the ambient model space is. -/
private theorem finiteDimensional_complement [FiniteDimensional ℝ E] : FiniteDimensional ℝ F :=
  FiniteDimensional.of_injective ((hi.equiv : E' × F →L[ℝ] E).toLinearMap ∘ₗ LinearMap.inr ℝ E' F)
    (hi.equiv.injective.comp LinearMap.inr_injective)

/-- **Nondegeneracy of the vertical Hessian.** In the slice coordinates of a Morse–Bott critical
submanifold, the Hessian of the coordinate expression of the function in the normal directions is
nondegenerate along the zero section. -/
private theorem isInvertible_fderiv_fderiv_comp_equiv [FiniteDimensional ℝ E] [J.Boundaryless]
    (h : i.IsNondegenerateCriticalSubmanifold f) {b : E'}
    (hb : b ∈ (hi.domChart.extend J).target) :
    (fderiv ℝ (fderiv ℝ fun v ↦
      ((f ∘ (hi.codChart.extend I).symm) ∘ hi.equiv) (b, v)) 0).IsInvertible := by
  have := finiteDimensional_domain hi
  have := finiteDimensional_complement hi
  set e := hi.codChart
  set L := hi.equiv
  set s := (hi.domChart.extend J).symm b
  set g := (f ∘ (e.extend I).symm) ∘ L
  set D := fderiv ℝ (fderiv ℝ g) (b, 0)
  set K := fderiv ℝ (fderiv ℝ (f ∘ (e.extend I).symm)) (e.extend I (i s))
  have hs : s ∈ hi.domChart.source := by
    simpa only [OpenPartialHomeomorph.extend_source] using (hi.domChart.extend J).map_target hb
  have hx : i s ∈ e.source := hi.source_subset_preimage_source hs
  have he2 : e ∈ IsManifold.maximalAtlas I 2 M :=
    IsManifold.maximalAtlas_subset_of_le (by simp) hi.codChart_mem_maximalAtlas
  have he1 : e ∈ IsManifold.maximalAtlas I 1 M :=
    IsManifold.maximalAtlas_subset_of_le (by simp) hi.codChart_mem_maximalAtlas
  have hLb : L (b, 0) = e.extend I (i s) := (hi.writtenInCharts hb).symm
  have hcrit := mem_criticalPoints.1 (h.mem_criticalPoints s)
  have hK : ContDiffAt ℝ 2 (f ∘ (e.extend I).symm) (L (b, 0)) :=
    hLb ▸ (contMDiffAt_iff_contDiffAt_comp_extend_symm he2 hx).1 (h.contMDiffAt s)
  have hK0 : fderiv ℝ (f ∘ (e.extend I).symm) (L (b, 0)) = 0 :=
    hLb ▸ (mvfderiv_eq_zero_iff_fderiv_comp_extend_symm_eq_zero he1 hx
      ((h.contMDiffAt s).mdifferentiableAt two_ne_zero)).1 hcrit
  have hg : ContDiffAt ℝ 2 g (b, 0) := hK.comp _ L.contDiff.contDiffAt
  -- The Hessian of `g` is the Hessian `K` in the chart, read through `L`.
  have hD (z z' : E' × F) : D z z' = K (L z) (L z') := by
    have := fderiv_fderiv_comp_apply_of_fderiv_eq_zero hK L.contDiff.contDiffAt hK0 z z'
    rwa [L.fderiv, hLb] at this
  -- The critical Hessian is `K` read through the invertible derivative of the chart.
  obtain ⟨T, hT⟩ : (mvfderiv I (e.extend I) (i s)).IsInvertible := by
    -- `mvfderiv` is `mfderiv` followed by the identification `fromTangentSpace` of the tangent
    -- space of `E` with `E`; both factors are invertible.
    unfold mvfderiv
    exact ContinuousLinearMap.IsInvertible.comp
      ⟨NormedSpace.fromTangentSpace (e.extend I (i s)), rfl⟩ (isInvertible_mfderiv_extend he1 hx)
  have hH (v w : TangentSpace I (i s)) : criticalHessian I f (i s) v w = K (T v) (T w) := by
    have := criticalHessian_apply_eq_of_mem_maximalAtlas he2 hx (h.contMDiffAt s) hcrit v w
    rwa [← hT, ContinuousLinearEquiv.coe_coe] at this
  -- The Morse–Bott condition bounds the dimension of the kernel of `D` by `dim E'`.
  have hker : Module.finrank ℝ D.ker ≤ Module.finrank ℝ E' := by
    rw [ContinuousLinearMap.finrank_ker_eq_of_congr L hD,
      ← ContinuousLinearMap.finrank_ker_eq_of_congr (X := E) T hH]
    exact (Submodule.finrank_mono (h.ker_criticalHessian_le s)).trans
      (LinearMap.finrank_range_le _)
  -- The zero section near `b` is critical for `g`, so `D` vanishes on `E' × 0`.
  have hinl (u : E') : D (u, 0) = 0 := by
    have hev : (fun b' ↦ fderiv ℝ g (b', 0)) =ᶠ[𝓝 b] fun _ ↦ 0 := by
      filter_upwards [hi.domChart.isOpen_extend_target.mem_nhds hb] with b' hb'
      exact fderiv_comp_equiv_eq_zero hi h.toIsCriticalSubmanifold hb'
    have hder : HasFDerivAt (fun b' ↦ fderiv ℝ g (b', 0))
        (D.comp (ContinuousLinearMap.inl ℝ E' F)) b :=
      (hg.hasFDerivAt_fderiv le_rfl).comp b (hasFDerivAt_prodMk_left b 0)
    have h0 := hder.fderiv.symm.trans (hev.fderiv_eq.trans (fderiv_const_apply 0))
    simpa using congrArg (fun T ↦ T u) h0
  have hsymm (z z' : E' × F) : D z z' = D z' z :=
    (hg.isSymmSndFDerivAt (by simp)) z z'
  -- The vertical Hessian is the restriction of `D` to `0 × F`.
  convert ContinuousLinearMap.isInvertible_bilinearComp_inr_of_finrank_ker_le hsymm hinl hker
    using 1
  ext w w'
  have hg0 : fderiv ℝ g ((fun v : F ↦ (b, v)) 0) = 0 := fderiv_comp_equiv_eq_zero hi h.1 hb
  have := fderiv_fderiv_comp_apply_of_fderiv_eq_zero (φ := fun v : F ↦ (b, v)) hg
    (contDiffAt_const.prodMk contDiffAt_id) hg0 w w'
  rw [(hasFDerivAt_prodMk_right b (0 : F)).fderiv] at this
  rw [ContinuousLinearMap.bilinearComp_apply]
  exact this

/-- **The Morse–Bott lemma in slice coordinates.** In the slice coordinates of a Morse–Bott
critical submanifold, the coordinate expression of the function has a parametric Morse chart near
the image of `s₀`, which preserves the first coordinate, fixes the zero section, and lies over the
target of the domain chart. -/
private theorem exists_morse_chart_comp_equiv [FiniteDimensional ℝ E] [J.Boundaryless]
    (h : i.IsNondegenerateCriticalSubmanifold f)
    (hf : ∀ᶠ y in 𝓝 (i s₀), ContMDiffAt I 𝓘(ℝ) ∞ f y) :
    ∃ ψ : OpenPartialHomeomorph (E' × F) (E' × F),
      (hi.domChart.extend J s₀, 0) ∈ ψ.source ∧
      (∀ z ∈ ψ.source, z.1 ∈ (hi.domChart.extend J).target) ∧
      (∀ z ∈ ψ.source, (ψ z).1 = z.1) ∧
      (∀ z ∈ ψ.source, (z.1, 0) ∈ ψ.source ∧ ψ (z.1, 0) = (z.1, 0)) ∧
      ContDiffOn ℝ ∞ ψ ψ.source ∧ ContDiffOn ℝ ∞ ψ.symm ψ.target ∧
      (∀ z ∈ ψ.target, f ((hi.codChart.extend I).symm (hi.equiv (ψ.symm z))) =
        f ((hi.codChart.extend I).symm (hi.equiv (z.1, 0))) + 2⁻¹ * fderiv ℝ (fderiv ℝ fun v ↦
          f ((hi.codChart.extend I).symm (hi.equiv (ψ.symm (z.1, v))))) 0 z.2 z.2) ∧
      ∀ z ∈ ψ.target, (fderiv ℝ (fderiv ℝ fun v ↦
        f ((hi.codChart.extend I).symm (hi.equiv (ψ.symm (z.1, v))))) 0).IsInvertible := by
  have := finiteDimensional_domain hi
  have := finiteDimensional_complement hi
  set e := hi.codChart
  set L := hi.equiv
  set T := (hi.domChart.extend J).target
  set g := (f ∘ (e.extend I).symm) ∘ L
  have he : e ∈ IsManifold.maximalAtlas I ∞ M := hi.codChart_mem_maximalAtlas
  have ha : hi.domChart.extend J s₀ ∈ T := (hi.domChart.extend J).map_source
    (by rw [OpenPartialHomeomorph.extend_source]; exact hi.mem_domChart_source)
  obtain ⟨O, hOf, hO, hxO⟩ := mem_nhds_iff.1 hf
  -- The open set of `E' × F` over `T` on which `g` is smooth.
  set W : Set (E' × F) := L ⁻¹' ((e.extend I).target ∩ (e.extend I).symm ⁻¹' O) ∩ T ×ˢ univ
  have hW : IsOpen W :=
    ((e.continuousOn_extend_symm.isOpen_inter_preimage e.isOpen_extend_target hO).preimage
      L.continuous).inter (hi.domChart.isOpen_extend_target.prod isOpen_univ)
  have hLa : L (hi.domChart.extend J s₀, 0) = e.extend I (i s₀) := by
    rw [← equiv_symm_codChart_extend hi hi.mem_domChart_source,
      ContinuousLinearEquiv.apply_symm_apply]
  have hx₀ : i s₀ ∈ (e.extend I).source := by
    rw [OpenPartialHomeomorph.extend_source]; exact hi.mem_codChart_source
  have haW : (hi.domChart.extend J s₀, 0) ∈ W := by
    refine ⟨⟨?_, ?_⟩, ha, mem_univ _⟩ <;> simp only [mem_preimage, hLa]
    · exact (e.extend I).map_source hx₀
    · rw [(e.extend I).left_inv hx₀]; exact hxO
  have hgW : ContDiffOn ℝ ∞ g W := by
    intro z hz
    have hzt : L z ∈ (e.extend I).target := hz.1.1
    have hy : (e.extend I).symm (L z) ∈ e.source := by
      rw [← OpenPartialHomeomorph.extend_source (I := I)]; exact (e.extend I).map_target hzt
    have h := (contMDiffAt_iff_contDiffAt_comp_extend_symm he hy).1 (hOf hz.1.2)
    rw [(e.extend I).right_inv hzt] at h
    exact (h.comp z L.contDiff.contDiffAt).contDiffWithinAt
  have hcrit : ∀ b, (b, 0) ∈ W → fderiv ℝ (fun v ↦ g (b, v)) 0 = 0 := by
    intro b hb
    have hd : DifferentiableAt ℝ g (b, 0) :=
      ((hgW _ hb).contDiffAt (hW.mem_nhds hb)).differentiableAt (by simp)
    rw [fderiv_fun_comp _ hd (differentiableAt_const _ |>.prodMk differentiableAt_id),
      fderiv_comp_equiv_eq_zero hi h.1 hb.2.1, ContinuousLinearMap.zero_comp]
  obtain ⟨ψ, haψ, hψW, hψfst, hψzero, hψ, hψsymm, hψeq, hψinv⟩ :=
    exists_parametric_morse_chart_of_contDiffOn (n := ⊤) hW haW hgW hcrit
      (fun b hb ↦ isInvertible_fderiv_fderiv_comp_equiv hi h hb.2.1) (by simp)
  exact ⟨ψ, haψ, fun z hz ↦ (hψW hz).2.1, hψfst, hψzero, hψ, hψsymm, hψeq, hψinv⟩

end Slice

/-- **The Morse–Bott lemma.** Let `i : S → M` be a Morse–Bott critical submanifold of a function
`f` which is smooth near `i s₀`, on a finite-dimensional boundaryless manifold `M`, and let `F` be
a complement in which `i` is an immersion at `s₀`. Then there is a smooth chart `Φ` of `M` near
`i s₀` with values in `E' × F` which is a slice chart for `i`, sending exactly the points of the
submanifold to the zero section, and in which `f` is a nondegenerate quadratic form on each fibre:
`f (Φ.symm (b, v))` is the value at `(b, 0)` plus half the Hessian of `v ↦ f (Φ.symm (b, v))` at
`0` evaluated on `v`, and that Hessian is invertible. -/
theorem IsNondegenerateCriticalSubmanifold.exists_morseBott_chart [FiniteDimensional ℝ E]
    [J.Boundaryless] (h : i.IsNondegenerateCriticalSubmanifold f)
    (hf : ∀ᶠ y in 𝓝 (i s₀), ContMDiffAt I 𝓘(ℝ) ∞ f y)
    (hi : Manifold.IsImmersionAtOfComplement F J I ∞ i s₀) :
    ∃ Φ : PartialDiffeomorph I 𝓘(ℝ, E' × F) M (E' × F) ∞,
      i s₀ ∈ Φ.source ∧ (∀ x ∈ Φ.source, x ∈ range i ↔ (Φ x).2 = 0) ∧
      (∀ z ∈ Φ.target, (z.1, 0) ∈ Φ.target) ∧
      (∀ z ∈ Φ.target, f (Φ.symm z) = f (Φ.symm (z.1, 0)) +
        2⁻¹ * fderiv ℝ (fderiv ℝ fun v ↦ f (Φ.symm (z.1, v))) 0 z.2 z.2) ∧
      ∀ z ∈ Φ.target, (fderiv ℝ (fderiv ℝ fun v ↦ f (Φ.symm (z.1, v))) 0).IsInvertible := by
  -- The chart `Φ` is the immersion chart `e`, followed by `L.symm` into the slice coordinates and
  -- by the parametric Morse chart `ψ` there, restricted to an open set `Wm` meeting the
  -- submanifold only in the image of the domain chart. The slice property comes from `ψ` fixing
  -- the zero section and preserving the first coordinate, and the normal form and nondegeneracy
  -- are those of `ψ`, read through the formula for `Φ.symm`.
  obtain ⟨ψ, haψ, hψT, hψfst, hψzero, hψ, hψsymm, hψeq, hψinv⟩ :=
    exists_morse_chart_comp_equiv hi h hf
  set e := hi.codChart
  set L := hi.equiv
  have he : e ∈ IsManifold.maximalAtlas I ∞ M := hi.codChart_mem_maximalAtlas
  -- An open set of `M` meeting the submanifold exactly in the image of the domain chart.
  obtain ⟨Wm, hWm, hWmeq⟩ := i.isEmbedding.isInducing.isOpen_iff.1 hi.domChart.open_source
  set Φ := (((e.toPartialDiffeomorphOfMemMaximalAtlas he).trans
    L.symm.toPartialDiffeomorph).restrOpen Wm hWm).trans
      (PartialDiffeomorph.ofOpenPartialHomeomorph ψ hψ hψsymm)
  have hsrc (x : M) : x ∈ Φ.source ↔ x ∈ e.source ∧ x ∈ Wm ∧ L.symm (e.extend I x) ∈ ψ.source := by
    simp [Φ, and_assoc]
  have hΦ (x : M) : Φ x = ψ (L.symm (e.extend I x)) := by
    simp [Φ]
  have htgt (z : E' × F) : z ∈ Φ.target ↔ z ∈ ψ.target ∧ L (ψ.symm z) ∈ (e.extend I).target ∧
      (e.extend I).symm (L (ψ.symm z)) ∈ Wm := by
    simp [Φ, Set.range_eq_univ.1 I.range_eq_univ]
  have hsymm (z : E' × F) : Φ.symm z = (e.extend I).symm (L (ψ.symm z)) := by
    simp [Φ]
  -- The zero section over the target of the domain chart is the submanifold, inside `Wm`.
  have hWm' : ∀ b ∈ (hi.domChart.extend J).target, i ((hi.domChart.extend J).symm b) ∈ Wm := by
    intro b hb
    rw [← mem_preimage, hWmeq, ← OpenPartialHomeomorph.extend_source (I := J)]
    exact (hi.domChart.extend J).map_target hb
  -- The point `(z.1, 0)` below a point `z` of the target of `ψ` is fixed by `ψ`.
  have hψt0 : ∀ z ∈ ψ.target, (z.1, (0 : F)) ∈ ψ.source ∧ (z.1, (0 : F)) ∈ ψ.target ∧
      ψ.symm (z.1, 0) = (z.1, 0) := by
    intro z hz
    have hy := ψ.map_target hz
    have hfst : (ψ.symm z).1 = z.1 := by rw [← hψfst _ hy, ψ.right_inv hz]
    obtain ⟨h0, h0'⟩ := hψzero _ hy
    rw [hfst] at h0 h0'
    have hinv := ψ.left_inv h0
    rw [h0'] at hinv
    exact ⟨h0, h0' ▸ ψ.map_source h0, hinv⟩
  refine ⟨Φ, ?_, fun x hx ↦ ?_, fun z hz ↦ ?_, fun z hz ↦ ?_, fun z hz ↦ ?_⟩
  · have hs₀ : s₀ ∈ i ⁻¹' Wm := by rw [hWmeq]; exact hi.mem_domChart_source
    refine (hsrc _).2 ⟨hi.mem_codChart_source, hs₀, ?_⟩
    rw [equiv_symm_codChart_extend hi hi.mem_domChart_source]
    exact haψ
  · obtain ⟨hxe, hxW, hxψ⟩ := (hsrc x).1 hx
    rw [hΦ]
    constructor
    · rintro ⟨s, rfl⟩
      have hs : s ∈ hi.domChart.source := by rw [← hWmeq]; exact hxW
      rw [equiv_symm_codChart_extend hi hs] at hxψ ⊢
      simpa using congrArg Prod.snd (hψzero _ hxψ).2
    · intro h0
      set y := L.symm (e.extend I x)
      -- `ψ y` lies on the zero section, so `y` does, as `ψ` fixes the zero section.
      have hyeq : y = (y.1, 0) := ψ.injOn hxψ (hψzero y hxψ).1
        ((Prod.ext (hψfst y hxψ) h0 : ψ y = (y.1, 0)).trans (hψzero y hxψ).2.symm)
      refine ⟨(hi.domChart.extend J).symm y.1, ?_⟩
      rw [← codChart_extend_symm_equiv_mk_zero hi (hψT y hxψ), ← hyeq,
        ContinuousLinearEquiv.apply_symm_apply,
        (e.extend I).left_inv (by rwa [OpenPartialHomeomorph.extend_source])]
  · obtain ⟨hzψ, -, -⟩ := (htgt z).1 hz
    obtain ⟨h0s, h0t, h0⟩ := hψt0 z hzψ
    have hb := hψT _ h0s
    refine (htgt _).2 ⟨h0t, ?_, ?_⟩ <;> rw [h0]
    · exact hi.target_subset_preimage_target hb
    · rw [codChart_extend_symm_equiv_mk_zero hi hb]
      exact hWm' _ hb
  · obtain ⟨hzψ, -, -⟩ := (htgt z).1 hz
    simp only [hsymm]
    rw [(hψt0 z hzψ).2.2]
    exact hψeq z hzψ
  · obtain ⟨hzψ, -, -⟩ := (htgt z).1 hz
    simp only [hsymm]
    exact hψinv z hzψ

end SmoothEmbedding

end TauCeti

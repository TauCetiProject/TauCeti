/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.Morse.Bott
public import TauCeti.Geometry.Manifold.Morse.Bott.Basic
import TauCeti.Analysis.Calculus.SecondDerivative
import TauCeti.Geometry.Manifold.MFDeriv.Chart

/-!
# The Morse–Bott lemma on a manifold

Near each point of a Morse–Bott critical submanifold, a function is, in suitable coordinates, its
constant critical value plus a nondegenerate quadratic form in the normal directions. This file
proves this in the slice charts of the submanifold.

Let `i : S → M` be a nondegenerate critical submanifold of `f`
(`TauCeti.SmoothEmbedding.IsNondegenerateCriticalSubmanifold`) and let `h` be immersion data of
`i` at `s` (`Manifold.IsImmersionAtOfComplement`) with complement `F`: charts `φ = h.domChart` of
`S` and `e = h.codChart` of `M` and a linear isomorphism `L = h.equiv : E' × F ≃ E` in which `i`
reads `b ↦ (b, 0)`. The coordinate expression `g = f ∘ e⁻¹ ∘ L` on `E' × F` then has a critical
zero section, and the kernel of its Hessian at `(φ s, 0)` consists of base directions: it contains
them because the zero section is critical, and its dimension is that of the kernel of the critical
Hessian of `f` at `i s`, which for a Morse–Bott submanifold is the dimension of `S`. The Morse–Bott
lemma in product coordinates (`TauCeti.exists_morseBott_chart_of_contDiffOn`) then applies to `g`.

The resulting chart `ψ` changes only the normal coordinate, fixes the zero section, which is
the submanifold itself, and puts `g` in the form
`g z = f (i s) + ½ D²(g (z.1, ·))(0) ((ψ z).2, (ψ z).2)` with invertible vertical Hessians
(`TauCeti.SmoothEmbedding.IsNondegenerateCriticalSubmanifold.exists_morseBott_chart`). In
particular `f` is constant along `i` near `s`.

## Main declarations

* `TauCeti.SmoothEmbedding.IsNondegenerateCriticalSubmanifold.exists_morseBott_chart`: the
  Morse–Bott lemma in a slice chart of a Morse–Bott critical submanifold.

## References

* R. Bott, *Nondegenerate critical manifolds*, Annals of Mathematics 60 (1954), 248–261.
* A. Banyaga and D. E. Hurtubise, *A proof of the Morse–Bott lemma*, Expositiones Mathematicae 22
  (2004), 365–373.
-/

public section

open Filter Function Manifold Set Topology
open scoped ContDiff Manifold

namespace TauCeti

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 2 M]
  {E' H' S : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
  {J : ModelWithCorners ℝ E' H'} [J.Boundaryless] [TopologicalSpace S] [ChartedSpace H' S]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {f : M → ℝ} {n : ℕ∞ω} {k : ℕ∞} {i : SmoothEmbedding J I n S M} {s : S}

namespace SmoothEmbedding.IsNondegenerateCriticalSubmanifold

omit [J.Boundaryless] in
/-- In a chart `e` of `M` and coordinates `L : E' × F ≃ E` in which a point `(a, 0)` of a critical
zero section corresponds to the point `i s` of a Morse–Bott critical submanifold, the kernel of the
Hessian of the coordinate expression of `f` at `(a, 0)` consists of base directions. It contains
them because the zero section is critical, and it has the dimension of `S` because it corresponds
to the kernel of the critical Hessian of `f` at `i s` under the derivative of the chart. -/
private theorem ker_fderiv_fderiv_comp_le_range_inl (hi : i.IsNondegenerateCriticalSubmanifold f)
    (hn : n ≠ 0) {e : OpenPartialHomeomorph M H} (he : e ∈ IsManifold.maximalAtlas I 2 M)
    {L : (E' × F) ≃L[ℝ] E} {a : E'} (hx : i s ∈ e.source) (hxL : e.extend I (i s) = L (a, 0))
    (hcrit : ∀ᶠ b in 𝓝 a, fderiv ℝ (f ∘ (e.extend I).symm ∘ L) (b, 0) = 0) :
    (fderiv ℝ (fderiv ℝ (f ∘ (e.extend I).symm ∘ L)) (a, 0)).ker ≤
      LinearMap.range (LinearMap.inl ℝ E' F) := by
  have he1 : e ∈ IsManifold.maximalAtlas I 1 M :=
    IsManifold.maximalAtlas_subset_of_le (by norm_num) he
  have hfx : ContMDiffAt I 𝓘(ℝ) 2 f (i s) := hi.contMDiffAt s
  have hcritx : mvfderiv I f (i s) = 0 := mem_criticalPoints.mp (hi.mem_criticalPoints s)
  have hQ0 : fderiv ℝ (f ∘ (e.extend I).symm) (L (a, 0)) = 0 := by
    rw [← hxL]
    exact (mvfderiv_eq_zero_iff_fderiv_comp_extend_symm_eq_zero he1 hx
      (hfx.mdifferentiableAt two_ne_zero)).mp hcritx
  have hQ2 : ContDiffAt ℝ 2 (f ∘ (e.extend I).symm) (L (a, 0)) := by
    rw [← hxL]
    exact (contMDiffAt_iff_contDiffAt_comp_extend_symm he hx).mp hfx
  have hga : ContDiffAt ℝ 2 (f ∘ (e.extend I).symm ∘ L) (a, 0) :=
    hQ2.comp (a, 0) L.contDiff.contDiffAt
  -- The Hessian at `(a, 0)` is the critical Hessian at `i s` read through `N = T⁻¹ ∘ L`, where
  -- `T` is the derivative of the chart.
  obtain ⟨T, hT⟩ : (mvfderiv I (e.extend I) (i s)).IsInvertible := by
    unfold mvfderiv
    exact ContinuousLinearMap.IsInvertible.comp
      ⟨NormedSpace.fromTangentSpace (e.extend I (i s)), rfl⟩ (isInvertible_mfderiv_extend he1 hx)
  let N := L.toLinearEquiv.trans T.symm.toLinearEquiv
  -- In the chart, the critical Hessian is the Hessian of `f ∘ (e.extend I).symm` read through `T`.
  have hchart (v w : E) : criticalHessian I f (i s) (T.symm v) (T.symm w) =
      fderiv ℝ (fderiv ℝ (f ∘ (e.extend I).symm)) (L (a, 0)) v w := by
    have h := criticalHessian_apply_eq_of_mem_maximalAtlas he hx hfx hcritx (T.symm v) (T.symm w)
    simpa only [← hT, ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.apply_symm_apply,
      hxL] using h
  -- Composing with the linear map `L` at a critical point composes the Hessian with `L`.
  have hlin (z z' : E' × F) : fderiv ℝ (fderiv ℝ (f ∘ (e.extend I).symm ∘ L)) (a, 0) z z' =
      fderiv ℝ (fderiv ℝ (f ∘ (e.extend I).symm)) (L (a, 0)) (L z) (L z') := by
    have h := fderiv_fderiv_comp_apply_of_fderiv_eq_zero hQ2 L.contDiff.contDiffAt hQ0 z z'
    simp only [L.fderiv, ContinuousLinearEquiv.coe_coe] at h
    exact h
  have hHess (z z' : E' × F) : fderiv ℝ (fderiv ℝ (f ∘ (e.extend I).symm ∘ L)) (a, 0) z z' =
      criticalHessian I f (i s) (N z) (N z') := by
    simp only [N, LinearEquiv.trans_apply, ContinuousLinearEquiv.coe_toLinearEquiv, hlin, hchart]
  have hcomap : (fderiv ℝ (fderiv ℝ (f ∘ (e.extend I).symm ∘ L)) (a, 0)).ker =
      (criticalHessian I f (i s)).ker.comap N.toLinearMap := by
    ext z
    simp only [LinearMap.mem_ker, Submodule.mem_comap, ContinuousLinearMap.coe_coe,
      LinearEquiv.coe_coe]
    constructor
    · refine fun hz ↦ ContinuousLinearMap.ext fun v ↦ ?_
      obtain ⟨z', rfl⟩ := N.surjective v
      have hzz' := congr($hz z')
      rw [hHess] at hzz'
      simpa using hzz'
    · refine fun hz ↦ ContinuousLinearMap.ext fun z' ↦ ?_
      rw [hHess]
      simpa using congr($hz (N z'))
  -- The base directions lie in the kernel, which has the dimension of `S`.
  have hrange : LinearMap.range (LinearMap.inl ℝ E' F) ≤
      (fderiv ℝ (fderiv ℝ (f ∘ (e.extend I).symm ∘ L)) (a, 0)).ker := by
    rintro _ ⟨u, rfl⟩
    exact fderiv_fderiv_apply_inl_eq_zero hga hcrit u
  have : FiniteDimensional ℝ (E' × F) := L.symm.toLinearEquiv.finiteDimensional
  refine (Submodule.eq_of_le_of_finrank_le hrange ?_).ge
  rw [hcomap, Submodule.comap_equiv_eq_map_symm, LinearEquiv.finrank_map_eq,
    hi.ker_criticalHessian hn s, LinearMap.finrank_range_of_inj LinearMap.inl_injective]
  exact (LinearMap.finrank_range_of_inj (i.isImmersion.mfderiv_injective hn s)).le

/-- **The Morse–Bott lemma.** Let `i : S → M` be a Morse–Bott critical submanifold of `f`, with
slice charts `h.domChart` of `S` and `h.codChart` of `M` at `s` and `h.equiv : E' × F ≃ E` in which
`i` reads `b ↦ (b, 0)`, and let `f` be `C^{k+2}` near `i s` with `1 ≤ k` and `k + 2 ≤ n`. Write
`g = f ∘ (h.codChart.extend I).symm ∘ h.equiv`. There is a `C^k` chart `ψ` of `E' × F` with
product source `U ×ˢ V` around `(h.domChart.extend J s, 0)`, inside the chart domains, preserving
the base coordinate and fixing the zero section, such that

* the zero section over `U` is the submanifold: `g` there reads `f ∘ i` in the chart of `S`,
* `f` is constant, equal to `f (i s)`, along the submanifold over `U`,
* the vertical Hessian of `g` at each point of the zero section over `U` is invertible, and
* `g z = f (i s) + ½ D²(g (z.1, ·))(0) ((ψ z).2, (ψ z).2)` on the source of `ψ`. -/
theorem exists_morseBott_chart (hi : i.IsNondegenerateCriticalSubmanifold f)
    (h : IsImmersionAtOfComplement F J I n i s) (hkn : (k : ℕ∞ω) + 2 ≤ n) (hk : k ≠ 0)
    (hf : ∀ᶠ y in 𝓝 (i s), ContMDiffAt I 𝓘(ℝ) (k + 2) f y) :
    ∃ (ψ : OpenPartialHomeomorph (E' × F) (E' × F)) (U : Set E') (V : Set F),
      IsOpen U ∧ IsOpen V ∧ h.domChart.extend J s ∈ U ∧ (0 : F) ∈ V ∧ ψ.source = U ×ˢ V ∧
      U ⊆ (h.domChart.extend J).target ∧
      U ×ˢ V ⊆ h.equiv ⁻¹' (h.codChart.extend I).target ∧
      (∀ b ∈ U, (h.codChart.extend I).symm (h.equiv (b, 0)) = i ((h.domChart.extend J).symm b)) ∧
      (∀ z, (ψ z).1 = z.1) ∧ (∀ b, ψ (b, 0) = (b, 0)) ∧
      (∀ z ∈ ψ.target, (ψ.symm z).1 = z.1) ∧
      ContDiffOn ℝ k ψ ψ.source ∧ ContDiffOn ℝ k ψ.symm ψ.target ∧
      (∀ b ∈ U, f (i ((h.domChart.extend J).symm b)) = f (i s)) ∧
      (∀ b ∈ U, (fderiv ℝ (fderiv ℝ
        (fun v ↦ (f ∘ (h.codChart.extend I).symm ∘ h.equiv) (b, v))) 0).IsInvertible) ∧
      ∀ z ∈ ψ.source,
        (f ∘ (h.codChart.extend I).symm ∘ h.equiv) z = f (i s) + (2 : ℝ)⁻¹ *
          fderiv ℝ (fderiv ℝ (fun v ↦ (f ∘ (h.codChart.extend I).symm ∘ h.equiv) (z.1, v))) 0
            (ψ z).2 (ψ z).2 := by
  set φ := h.domChart.extend J with hφ
  set ξ := h.codChart.extend I with hξ
  set L := h.equiv with hL
  set g := f ∘ ξ.symm ∘ L with hg
  set a := φ s with ha
  have hn : n ≠ 0 := fun h0 ↦ by simp [h0] at hkn
  have hk2 : (2 : ℕ∞ω) ≤ k + 2 := le_add_self
  have he : h.codChart ∈ IsManifold.maximalAtlas I (k + 2) M :=
    IsManifold.maximalAtlas_subset_of_le hkn h.codChart_mem_maximalAtlas
  have he2 : h.codChart ∈ IsManifold.maximalAtlas I 2 M :=
    IsManifold.maximalAtlas_subset_of_le hk2 he
  have he1 : h.codChart ∈ IsManifold.maximalAtlas I 1 M :=
    IsManifold.maximalAtlas_subset_of_le (by norm_num) he2
  have hsφ : s ∈ φ.source := by simpa [hφ] using h.mem_domChart_source
  have haφ : a ∈ φ.target := φ.map_source hsφ
  have hφopen : IsOpen φ.target := h.domChart.isOpen_extend_target
  have hξopen : IsOpen ξ.target := h.codChart.isOpen_extend_target
  -- Points of the zero section over the chart of `S` are the points of the submanifold.
  have hsec {b : E'} (hb : b ∈ φ.target) :
      i (φ.symm b) ∈ h.codChart.source ∧ ξ (i (φ.symm b)) = L (b, 0) ∧
        ξ.symm (L (b, 0)) = i (φ.symm b) ∧ L (b, 0) ∈ ξ.target := by
    have hsrc : φ.symm b ∈ h.domChart.source := by
      simpa [hφ] using φ.map_target hb
    have hy : i (φ.symm b) ∈ h.codChart.source := h.source_subset_preimage_source hsrc
    have hw : ξ (i (φ.symm b)) = L (b, 0) := h.writtenInCharts hb
    have hyξ : i (φ.symm b) ∈ ξ.source := by simpa [hξ] using hy
    refine ⟨hy, hw, ?_, h.target_subset_preimage_target hb⟩
    rw [← hw, ξ.left_inv hyξ]
  have hx := hsec haφ
  rw [ha, φ.left_inv hsφ] at hx
  -- The coordinate expression of `f` in the chart of `M` is `C^{k+2}` near `L (a, 0)`.
  have hQ {y : M} (hy : y ∈ h.codChart.source) (hfy : ContMDiffAt I 𝓘(ℝ) (k + 2) f y) :
      ContDiffAt ℝ (k + 2) (f ∘ ξ.symm) (ξ y) :=
    (contMDiffAt_iff_contDiffAt_comp_extend_symm he hy).mp hfy
  have hcont : ContinuousAt (fun z : E' × F ↦ ξ.symm (L z)) (a, 0) :=
    (h.codChart.continuousOn_extend_symm.continuousAt (hξopen.mem_nhds hx.2.2.2)).comp
      L.continuous.continuousAt
  let W : Set (E' × F) := (φ.target ×ˢ univ) ∩ L ⁻¹' ξ.target ∩
    {z | ContMDiffAt I 𝓘(ℝ) (k + 2) f (ξ.symm (L z))}
  have hW : W ∈ 𝓝 (a, 0) := by
    refine Filter.inter_mem (Filter.inter_mem ((hφopen.prod isOpen_univ).mem_nhds ⟨haφ, trivial⟩)
      ((hξopen.preimage L.continuous).mem_nhds hx.2.2.2)) ?_
    exact hcont.preimage_mem_nhds (by rw [hx.2.2.1]; exact hf)
  have hgW : ContDiffOn ℝ (k + 2) g W := fun z hz ↦ by
    have hz' : ξ.symm (L z) ∈ h.codChart.source := by
      simpa [hξ] using ξ.map_target hz.1.2
    have h1 := hQ hz' hz.2
    rw [ξ.right_inv hz.1.2] at h1
    exact (h1.comp z L.contDiff.contDiffAt).contDiffWithinAt
  -- The zero section consists of critical points of `g`.
  have hcrit_g {b : E'} (hb : b ∈ φ.target) : fderiv ℝ g (b, 0) = 0 := by
    obtain ⟨hy, hw, -, -⟩ := hsec hb
    have hdiff := (hi.contMDiffAt (φ.symm b)).mdifferentiableAt two_ne_zero
    have hzero : fderiv ℝ (f ∘ ξ.symm) (ξ (i (φ.symm b))) = 0 :=
      (mvfderiv_eq_zero_iff_fderiv_comp_extend_symm_eq_zero he1 hy hdiff).mp
        (mem_criticalPoints.mp (hi.mem_criticalPoints (φ.symm b)))
    rw [hg, ← comp_assoc, L.comp_right_fderiv, ← hw, hzero, ContinuousLinearMap.zero_comp]
  have hcrit : ∀ᶠ b in 𝓝 a, fderiv ℝ g (b, 0) = 0 :=
    Filter.mem_of_superset (hφopen.mem_nhds haφ) fun b hb ↦ hcrit_g hb
  have hker := hi.ker_fderiv_fderiv_comp_le_range_inl hn he2 hx.1 hx.2.1 hcrit
  have : FiniteDimensional ℝ (E' × F) := L.symm.toLinearEquiv.finiteDimensional
  have : FiniteDimensional ℝ E' :=
    Module.Finite.of_surjective (LinearMap.fst ℝ E' F) LinearMap.fst_surjective
  have : FiniteDimensional ℝ F :=
    Module.Finite.of_surjective (LinearMap.snd ℝ E' F) LinearMap.snd_surjective
  obtain ⟨ψ, U, V, hU, hV, haU, h0V, hsource, hUVW, hψfst, hψ0, hψsymm, hψ, hψinv, hconst, hinv,
    hψg⟩ := exists_morseBott_chart_of_contDiffOn hW hgW hcrit hker hk
  have hUφ : U ⊆ φ.target := fun b hb ↦ (hUVW (mk_mem_prod hb h0V)).1.1.1
  -- The critical value along the zero section is the value of `f` along the submanifold.
  have hval {b : E'} (hb : b ∈ φ.target) : g (b, 0) = f (i (φ.symm b)) := by
    simp only [hg, comp_apply, (hsec hb).2.2.1]
  have hga0 : g (a, 0) = f (i s) := by
    rw [hval haφ, ha, φ.left_inv hsφ]
  refine ⟨ψ, U, V, hU, hV, haU, h0V, hsource, hUφ, fun z hz ↦ (hUVW hz).1.2,
    fun b hb ↦ (hsec (hUφ hb)).2.2.1, hψfst, hψ0, hψsymm, hψ, hψinv,
    fun b hb ↦ by rw [← hval (hUφ hb), hconst b hb, hga0], hinv, fun z hz ↦ ?_⟩
  rw [hψg z hz, hga0]

end SmoothEmbedding.IsNondegenerateCriticalSubmanifold

end TauCeti

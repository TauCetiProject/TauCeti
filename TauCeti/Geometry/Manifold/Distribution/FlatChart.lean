/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Distribution.Diffeomorph
public import TauCeti.Geometry.Manifold.Distribution.Horizontal
public import TauCeti.Geometry.Manifold.Distribution.Transverse
public import TauCeti.Geometry.Manifold.IsManifold.InteriorChart
public import TauCeti.Geometry.Manifold.LocalDiffeomorph.Basic

import TauCeti.Geometry.Manifold.LocalDiffeomorph.Constructions
import TauCeti.Geometry.Manifold.MFDeriv.NormedSpace
import TauCeti.LinearAlgebra.Projection.ProdEquiv

/-!
# Flat charts of an involutive distribution

The **local Frobenius theorem** on a manifold: an involutive `C^m` distribution `D` of rank `k` on
a manifold modelled on a finite-dimensional real space has a *flat chart* around every interior
point, a chart `e` of the `C^m` maximal atlas in which `D` is constant. That is, the differential of
`I ∘ e` carries the fibre of `D` at every point of the domain onto one fixed `k`-dimensional
subspace `W` of the model space. The slices of `I ∘ e` in the direction of `W` are therefore
integral manifolds of `D`, and these are the plaques from which the leaves of `D` are built.

The manifold is `C^n` with `m + 1 ≤ n`, because reading a vector field in a chart loses one
derivative of the chart's regularity. This covers a `C¹` distribution on a `C²` manifold, the lowest
regularity at which involutivity constrains the distribution. At a boundary point the statement
fails: a chart preserves the boundary, while a distribution may be tangent to the boundary at one
boundary point and transverse to it at nearby ones. The model `I` itself may have a boundary, since
only the base point has to be interior, and on a boundaryless manifold
`BoundarylessManifold.isInteriorPoint` supplies this at every point. No Hausdorff or
second-countability assumption on the manifold is used.

The proof reads `D` near `x` in the chart `TauCeti.extChartPartialDiffeomorph`, followed by a linear
splitting `E ≃ W × T` with `W` the fibre of `D` at `x` read in that chart. The distribution is
transverse to the vertical factor at the base point, so
`TauCeti.IsDistributionFrameOn.exists_openPartialHomeomorph_map_fderiv_eq_ker_snd` applies.

## Main results

* `TauCeti.IsInvolutiveDistribution.exists_flatChart`: the local Frobenius theorem.
* `TauCeti.IsInvolutiveDistribution.exists_flatChart_extend`: flat extended coordinates with
  open source and injective differential.
* `TauCeti.IsInvolutiveDistribution.exists_flatChart_eventually_sub_mem`: a horizontal
  differentiable map stays locally in a single affine slice of a Frobenius chart.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Springer GTM 218 (2013),
  Theorem 19.12 and Proposition 19.16 (local containment in a slice).
* S. Lang, *Fundamentals of Differential Geometry*, Springer GTM 191 (1999), Chapter VI, §1.
-/

public section

noncomputable section

open Set Filter Module
open scoped Topology Manifold ContDiff

namespace TauCeti

universe u

variable {E : Type u} {H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]

section SplitChart

variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] {n : ℕ∞ω}
  (A : P ≃L[ℝ] E) [IsManifold I n M] (x : M)

/-- The partial diffeomorphism from `M` to `P` given by the extended chart at `x` followed by the
inverse of a linear equivalence `A : P ≃ E`. -/
private def splitChart : PartialDiffeomorph I 𝓘(ℝ, P) M P n :=
  (extChartPartialDiffeomorph I n x).trans A.symm.toPartialDiffeomorph

private theorem splitChart_coe : ⇑(splitChart (I := I) (n := n) A x) = A.symm ∘ extChartAt I x := by
  funext y
  simp [splitChart]

private theorem splitChart_source :
    (splitChart (I := I) (n := n) A x).source = (extChartPartialDiffeomorph I n x).source := by
  simp [splitChart]

end SplitChart

section Splitting

variable {W T : Submodule ℝ E} (hT : IsCompl W T)

/-- If `W` is the image of `D x` under the differential of the chart at `x` and `A : W × T ≃ E` is
the splitting along a complement of `W`, then in the split coordinates `D x` is horizontal. -/
private theorem map_mfderiv_splitChart_eq_ker_snd [FiniteDimensional ℝ E] [IsManifold I 1 M]
    {n : ℕ∞ω} [IsManifold I n M] {x : M} {S : Submodule ℝ (TangentSpace I x)}
    (hW : W = S.map (mfderiv I 𝓘(ℝ, E) (extChartAt I x) x).toLinearMap) :
    S.map (mfderiv I 𝓘(ℝ, W × T) (splitChart (I := I) (n := n)
      (Submodule.prodEquivOfIsCompl W T hT).toContinuousLinearEquiv x) x).toLinearMap =
      LinearMap.ker (LinearMap.snd ℝ W T) := by
  let A : (W × T) ≃L[ℝ] E := (Submodule.prodEquivOfIsCompl W T hT).toContinuousLinearEquiv
  have hext : MDifferentiableAt I 𝓘(ℝ, E) (extChartAt I x) x := mdifferentiableAt_extChartAt
    (ChartedSpace.mem_chart_source x)
  have hd : mfderiv I 𝓘(ℝ, W × T) (splitChart (I := I) (n := n) A x) x =
      (A.symm : E →L[ℝ] W × T).comp (mfderiv I 𝓘(ℝ, E) (extChartAt I x) x) := by
    rw [splitChart_coe]
    exact ((A.symm : E →L[ℝ] W × T).hasMFDerivAt.comp x hext.hasMFDerivAt).mfderiv
  rw [hd]
  exact (Submodule.map_comp _ _ S).trans ((congrArg _ hW.symm).trans
    ((Submodule.map_symm_eq_iff _).2 (Submodule.map_ker_snd_prodEquivOfIsCompl W T hT)))

end Splitting

/-- A coordinate change `φ` of `P`, fixing the image of `x` under a partial diffeomorphism `Ψ`,
gives a chart of the maximal atlas of `M` that reads as `A ∘ φ ∘ Ψ`, when `A` carries the image of
`x` to the interior of the range of `I`. -/
private theorem exists_mem_maximalAtlas_eventuallyEq {P : Type*} [NormedAddCommGroup P]
    [NormedSpace ℝ P] (A : P ≃L[ℝ] E) {m n : ℕ∞ω} (hmn : m ≤ n) [IsManifold I n M]
    (Ψ : PartialDiffeomorph I 𝓘(ℝ, P) M P n) {x : M} (hx : x ∈ Ψ.source)
    {φ : OpenPartialHomeomorph P P} (hsrc : Ψ x ∈ φ.source) (hfix : φ (Ψ x) = Ψ x)
    (hφ : ContDiffOn ℝ m φ φ.source) (hφ' : ContDiffOn ℝ m φ.symm φ.target)
    (hint : A (Ψ x) ∈ interior (range I)) :
    ∃ e : OpenPartialHomeomorph M H, e ∈ IsManifold.maximalAtlas I m M ∧ x ∈ e.source ∧
      ∀ y ∈ e.source, y ∈ Ψ.source ∧ Ψ y ∈ φ.source ∧ (I ∘ e) =ᶠ[𝓝 y] fun y' ↦ A (φ (Ψ y')) := by
  have : IsManifold I m M := .of_le hmn
  -- The coordinates `A ∘ φ ∘ Ψ` on `M`, with values in the model vector space.
  let Θ : PartialDiffeomorph I 𝓘(ℝ, E) M E m :=
    ((Ψ.ofLE hmn).trans (PartialDiffeomorph.ofOpenPartialHomeomorph φ hφ hφ')).trans
      A.toPartialDiffeomorph
  have hsource {y : M} : y ∈ Θ.source ↔ y ∈ Ψ.source ∧ Ψ y ∈ φ.source := by
    simp [Θ]
  have hΘ (y : M) : Θ y = A (φ (Ψ y)) := by
    simp [Θ]
  have hmem {y : M} : y ∈ (Θ.toOpenPartialHomeomorph.trans I.interiorChart.symm).source ↔
      y ∈ Θ.source ∧ Θ y ∈ interior (range I) := by
    simp
  refine ⟨Θ.toOpenPartialHomeomorph.trans I.interiorChart.symm,
    OpenPartialHomeomorph.trans_interiorChart_symm_mem_maximalAtlas Θ.contMDiffOn
      Θ.symm.contMDiffOn,
    hmem.2 ⟨hsource.2 ⟨hx, hsrc⟩, ?_⟩,
    fun y hy ↦ ⟨(hsource.1 (hmem.1 hy).1).1, (hsource.1 (hmem.1 hy).1).2, ?_⟩⟩
  · rwa [hΘ, hfix]
  · refine eventually_of_mem (OpenPartialHomeomorph.open_source _ |>.mem_nhds hy) fun y' hy' ↦ ?_
    have h := I.right_inv (interior_subset (hmem.1 hy').2)
    simpa only [Function.comp_apply, OpenPartialHomeomorph.coe_trans,
      ModelWithCorners.interiorChart_coe_symm, PartialDiffeomorph.toFun'_toOpenPartialHomeomorph,
      hΘ] using h

/-- The local Frobenius theorem in the coordinates of a partial diffeomorphism `Ψ` to a product, in
which the involutive distribution `D` is transverse to the vertical factor at `x`. -/
private theorem exists_flat_coordinates {F₁ F₂ : Type u} [NormedAddCommGroup F₁] [NormedSpace ℝ F₁]
    [FiniteDimensional ℝ F₁] [NormedAddCommGroup F₂] [NormedSpace ℝ F₂] [FiniteDimensional ℝ F₂]
    [IsManifold I 1 M] [CompleteSpace E] {m : ℕ∞} {n : ℕ∞ω} (hmn : (m : ℕ∞ω) + 1 + 1 ≤ n)
    [IsManifold I n M] (Ψ : PartialDiffeomorph I 𝓘(ℝ, F₁ × F₂) M (F₁ × F₂) n)
    {D : Π x : M, Submodule ℝ (TangentSpace I x)} (hinv : IsInvolutiveDistribution I D)
    (hD : IsContMDiffDistribution I ((m : ℕ∞ω) + 1) (finrank ℝ F₁) D) {x : M} (hx : x ∈ Ψ.source)
    (hbase : Disjoint ((D x).map (mfderiv I 𝓘(ℝ, F₁ × F₂) Ψ x).toLinearMap)
      (LinearMap.ker (LinearMap.fst ℝ F₁ F₂))) :
    ∃ φ : OpenPartialHomeomorph (F₁ × F₂) (F₁ × F₂), Ψ x ∈ φ.source ∧ φ (Ψ x) = Ψ x ∧
      ContDiffOn ℝ ((m : ℕ∞ω) + 1) φ φ.source ∧ ContDiffOn ℝ ((m : ℕ∞ω) + 1) φ.symm φ.target ∧
      ∀ y ∈ Ψ.source, Ψ y ∈ φ.source →
        ((D y).map (mfderiv I 𝓘(ℝ, F₁ × F₂) Ψ y).toLinearMap).map
          (fderiv ℝ φ (Ψ y) : F₁ × F₂ →ₗ[ℝ] F₁ × F₂) = LinearMap.ker (LinearMap.snd ℝ F₁ F₂) := by
  have hn0 : n ≠ 0 := by
    rintro rfl
    simp at hmn
  have h2n : (2 : ℕ∞ω) ≤ n := by
    refine le_trans ?_ hmn
    calc (2 : ℕ∞ω) = 1 + 1 := by norm_num
      _ ≤ (m : ℕ∞ω) + 1 + 1 := by gcongr; simp
  have h2n' : minSmoothness ℝ 2 ≤ n := by rwa [minSmoothness_of_isRCLikeNormedField]
  have : IsManifold I (minSmoothness ℝ 2) M := .of_le h2n'
  have : CompleteSpace (F₁ × F₂) := FiniteDimensional.complete ℝ _
  let Φ := Ψ.symm
  -- The distribution read in the coordinates of `Ψ`.
  let DP : F₁ × F₂ → Submodule ℝ (F₁ × F₂) := fun q ↦
    (D (Φ q)).comap (mfderivWithin 𝓘(ℝ, F₁ × F₂) I Φ Φ.source q).toLinearMap
  have hDP (y : M) (hy : y ∈ Ψ.source) :
      (D y).map (mfderiv I 𝓘(ℝ, F₁ × F₂) Ψ y).toLinearMap = DP (Ψ y) :=
    Ψ.map_mfderiv_eq_comap_mfderivWithin_symm hn0 D hy
  obtain ⟨U, hU, hxU, X, hX⟩ := isContMDiffDistribution_iff.1 hD x
  have hV : IsOpen (Φ.source ∩ Φ ⁻¹' U) := Φ.toOpenPartialHomeomorph.isOpen_inter_preimage hU
  have ha₀ : Ψ x ∈ Φ.source ∩ Φ ⁻¹' U := by
    refine ⟨Ψ.map_source hx, ?_⟩
    rwa [mem_preimage, show Φ (Ψ x) = x from Ψ.left_inv hx]
  obtain ⟨φ, hsrc, hfix, hφ, hφ', hmap⟩ :=
    IsDistributionFrameOn.exists_openPartialHomeomorph_map_fderiv_eq_ker_snd (D := DP) hV
      (hX.comap_mfderivWithin Φ hmn)
      ((Φ.isInvolutiveDistributionOn_comap_mfderivWithin
        (hinv.isInvolutiveDistributionOn _) h2n').mono inter_subset_left) ha₀ (hDP x hx ▸ hbase)
  exact ⟨φ, hsrc, hfix, hφ, hφ', fun y hy hyφ ↦ by rw [hDP y hy]; exact hmap _ hyφ⟩

/-- **The local Frobenius theorem.** An involutive `C^m` distribution `D` of rank `k`, for `1 ≤ m`,
on a `C^n` manifold with `m + 1 ≤ n`, modelled on a finite-dimensional real space, is constant in a
suitable chart around any interior point `x`: there are a chart `e` of the `C^m` maximal atlas whose
domain contains `x` and a `k`-dimensional subspace `W` of the model space such that the differential
of `I ∘ e` carries `D y` onto `W` at every point `y` of the domain of `e`. On a boundaryless
manifold `BoundarylessManifold.isInteriorPoint` gives the interior hypothesis at every point. -/
theorem IsInvolutiveDistribution.exists_flatChart [FiniteDimensional ℝ E] [IsManifold I 1 M]
    {m : ℕ∞} (hm : 1 ≤ m) {n : ℕ∞ω} (hmn : (m : ℕ∞ω) + 1 ≤ n)
    [IsManifold I n M] {k : ℕ} {D : Π x : M, Submodule ℝ (TangentSpace I x)}
    (hinv : IsInvolutiveDistribution I D) (hD : IsContMDiffDistribution I m k D) {x : M}
    (hx : I.IsInteriorPoint x) :
    ∃ (e : OpenPartialHomeomorph M H) (W : Submodule ℝ E),
      e ∈ IsManifold.maximalAtlas I m M ∧ x ∈ e.source ∧ finrank ℝ W = k ∧
        ∀ y ∈ e.source, (D y).map (mfderiv I 𝓘(ℝ, E) (I ∘ e) y).toLinearMap = W := by
  have : CompleteSpace E := FiniteDimensional.complete ℝ E
  obtain ⟨m', rfl⟩ : ∃ m' : ℕ∞, m = m' + 1 := ⟨m - 1, (tsub_add_cancel_of_le hm).symm⟩
  have hcast : ((m' + 1 : ℕ∞) : ℕ∞ω) = (m' : ℕ∞ω) + 1 := by norm_cast
  rw [hcast] at hmn hD ⊢
  have hn0 : n ≠ 0 := by
    rintro rfl
    simp at hmn
  -- The fibre of `D` at `x` read in the chart, and a linear splitting of the model space along it.
  obtain ⟨W, hW⟩ : ∃ W : Submodule ℝ E,
      W = (D x).map (mfderiv I 𝓘(ℝ, E) (extChartAt I x) x).toLinearMap := ⟨_, rfl⟩
  obtain ⟨T, hT⟩ := W.exists_isCompl
  have hfinrank : finrank ℝ W = k := by
    rw [hW, ← hD.finrank_eq x]
    exact (Submodule.equivMapOfInjective _
      (isInvertible_mfderiv_extChartAt (mem_extChartAt_source x)).injective _).finrank_eq.symm
  subst hfinrank
  let A : (W × T) ≃L[ℝ] E := (Submodule.prodEquivOfIsCompl W T hT).toContinuousLinearEquiv
  let Ψ : PartialDiffeomorph I 𝓘(ℝ, W × T) M (W × T) n := splitChart A x
  have hxΨ : x ∈ Ψ.source := by
    rwa [show Ψ.source = _ from splitChart_source A x, mem_extChartPartialDiffeomorph_source]
  -- At the base point `D` is horizontal, so transverse to the vertical factor.
  have hbase : (D x).map (mfderiv I 𝓘(ℝ, W × T) Ψ x).toLinearMap =
      LinearMap.ker (LinearMap.snd ℝ W T) :=
    map_mfderiv_splitChart_eq_ker_snd hT hW
  have hdisj : Disjoint (LinearMap.ker (LinearMap.snd ℝ W T))
      (LinearMap.ker (LinearMap.fst ℝ W T)) := by
    rw [← LinearMap.range_inl, ← LinearMap.range_inr]
    exact LinearMap.isCompl_range_inl_inr.disjoint
  obtain ⟨φ, hsrc, hfix, hφ, hφ', hmap⟩ :=
    exists_flat_coordinates hmn Ψ hinv hD hxΨ (hbase ▸ hdisj)
  have hint : A (Ψ x) ∈ interior (range I) := by
    have h : extChartAt I x x ∈ interior (range I) := hx
    rw [show (Ψ : M → W × T) = A.symm ∘ extChartAt I x from splitChart_coe A x]
    simpa only [Function.comp_apply, A.apply_symm_apply] using h
  obtain ⟨e, heA, hxe, he⟩ := exists_mem_maximalAtlas_eventuallyEq A (le_self_add.trans hmn) Ψ hxΨ
    hsrc hfix hφ hφ' hint
  refine ⟨e, W, heA, hxe, rfl, fun y hy ↦ ?_⟩
  obtain ⟨hyΨ, hyφ, hev⟩ := he y hy
  have hL := hmap y hyΨ hyφ
  have hφd : DifferentiableAt ℝ φ (Ψ y) :=
    (hφ.contDiffAt (φ.open_source.mem_nhds hyφ)).differentiableAt (by simp)
  -- The differential of `I ∘ e = A ∘ φ ∘ Ψ` near `y`, by the chain rule.
  have hderiv : mfderiv I 𝓘(ℝ, E) (I ∘ e) y =
      (A : W × T →L[ℝ] E).comp ((fderiv ℝ φ (Ψ y)).comp (mfderiv I 𝓘(ℝ, W × T) Ψ y)) := by
    rw [hev.mfderiv_eq]
    have hΨd : MDifferentiableAt I 𝓘(ℝ, W × T) Ψ y := Ψ.mdifferentiableAt hn0 hyΨ
    exact ((A : W × T →L[ℝ] E).hasFDerivAt.comp _ hφd.hasFDerivAt).hasMFDerivAt.comp y
      hΨd.hasMFDerivAt |>.mfderiv
  rw [hderiv]
  exact (Submodule.map_comp _ _ (D y)).trans ((congrArg _ (Submodule.map_comp _ _ (D y))).trans
    ((congrArg _ hL).trans (Submodule.map_ker_snd_prodEquivOfIsCompl W T hT)))


/-- An involutive `C^m` distribution admits extended flat coordinates near each interior point,
for `1 ≤ m` and ambient regularity `n ≥ m + 1`. The coordinate source is open, its differential
is injective there, and it carries the distribution onto a fixed rank-`k` subspace. -/
theorem IsInvolutiveDistribution.exists_flatChart_extend [FiniteDimensional ℝ E]
    [IsManifold I 1 M] {m : ℕ∞} (hm : 1 ≤ m) {n : ℕ∞ω}
    (hmn : (m : ℕ∞ω) + 1 ≤ n) [IsManifold I n M]
    {k : ℕ} {D : Π x : M, Submodule ℝ (TangentSpace I x)}
    (hinv : IsInvolutiveDistribution I D) (hD : IsContMDiffDistribution I m k D)
    {x : M} (hx : I.IsInteriorPoint x) :
    ∃ (Φ : PartialEquiv M E) (W : Submodule ℝ E),
      IsOpen Φ.source ∧ x ∈ Φ.source ∧ finrank ℝ W = k ∧
        ContMDiffOn I 𝓘(ℝ, E) m Φ Φ.source ∧
        (∀ z ∈ Φ.source, (D z).map (mfderiv I 𝓘(ℝ, E) Φ z).toLinearMap = W) ∧
        ∀ z ∈ Φ.source, Function.Injective (mfderiv I 𝓘(ℝ, E) Φ z) := by
  let _ : IsManifold I (m : ℕ∞ω) M := .of_le (le_self_add.trans hmn)
  obtain ⟨e, W, he, hxe, hdim, hflat⟩ := hinv.exists_flatChart hm hmn hD hx
  let Φ := e.extend I
  refine ⟨Φ, W, e.isOpen_extend_source, ?_, hdim, ?_, ?_, ?_⟩
  · simpa only [Φ, e.extend_source] using hxe
  · simpa only [Φ, e.extend_coe, e.extend_source] using e.contMDiffOn_extend he
  · intro z hz
    rw [show (Φ : M → E) = I ∘ e from e.extend_coe]
    exact hflat z (by simpa only [Φ, e.extend_source] using hz)
  · intro z hz
    exact (isInvertible_mfderiv_extend
      (IsManifold.maximalAtlas_subset_of_le
        (show (1 : ℕ∞ω) ≤ m from by exact_mod_cast hm) he)
      (by simpa only [Φ, e.extend_source] using hz)).injective

section Horizontal

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {H' : Type*} [TopologicalSpace H'] {J : ModelWithCorners ℝ F H'}
  {N : Type*} [TopologicalSpace N] [ChartedSpace H' N] [IsManifold J 1 N]
  {D : ∀ z : M, Submodule ℝ (TangentSpace I z)} {f : N → M}

/-- A Frobenius chart near an interior image point of a horizontal differentiable map puts
that map locally in the affine slice parallel to the flattened distribution. -/
theorem IsInvolutiveDistribution.exists_flatChart_eventually_sub_mem [FiniteDimensional ℝ E]
    [IsManifold I 1 M] {m : ℕ∞} (hm : 1 ≤ m) {n : ℕ∞ω}
    (hmn : (m : ℕ∞ω) + 1 ≤ n) [IsManifold I n M]
    (hinv : IsInvolutiveDistribution I D) {k : ℕ} (hD : IsContMDiffDistribution I m k D)
    (hf : IsHorizontalMap J D f) {s : Set N} (hfd : MDifferentiableOn J I f s)
    (hs : IsOpen s) {x : N} (hxs : x ∈ s) (hx : I.IsInteriorPoint (f x)) :
    ∃ (e : OpenPartialHomeomorph M H) (W : Submodule ℝ E),
      e ∈ IsManifold.maximalAtlas I m M ∧ f x ∈ e.source ∧ Module.finrank ℝ W = k ∧
        (∀ z ∈ e.source, (D z).map (mfderiv I 𝓘(ℝ, E) (I ∘ e) z).toLinearMap = W) ∧
        ∀ᶠ y in 𝓝 x, f y ∈ e.source ∧ (I ∘ e) (f y) - (I ∘ e) (f x) ∈ W := by
  obtain ⟨e, W, he, hxsrc, hdim, hflat⟩ := hinv.exists_flatChart hm hmn hD hx
  refine ⟨e, W, he, hxsrc, hdim, hflat, ?_⟩
  have hm0 : (m : ℕ∞ω) ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one (by exact_mod_cast hm))
  have hDp (z : M) (hz : z ∈ e.source) :
      (D z).map (mvfderiv I (I ∘ e) z).toLinearMap ≤ W := by
    rw [(D z).map_mvfderiv_eq_map_mfderiv (I := I) (x := z) (I ∘ e)]
    exact (hflat z hz).le
  have hconst := hf.eventually_sub_mem hfd hs
    ((e.contMDiffOn_extend he).mdifferentiableOn hm0) e.open_source W.closed_of_finiteDimensional
    hDp hxs hxsrc
  have hfc : ContinuousAt f x := hfd.continuousOn.continuousAt (hs.mem_nhds hxs)
  filter_upwards [hconst, hfc (e.open_source.mem_nhds hxsrc)] with y hy hys
  exact ⟨hys, hy⟩

end Horizontal

end TauCeti

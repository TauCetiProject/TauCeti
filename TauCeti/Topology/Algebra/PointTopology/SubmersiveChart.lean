/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Smooth.StandardSmoothOfFree
public import Mathlib.Topology.IsLocalHomeomorph
public import TauCeti.Analysis.MvPolynomial.Jacobian
public import TauCeti.RingTheory.Extension.Presentation.Submersive
public import TauCeti.Topology.Algebra.PointTopology.Basic
public import TauCeti.Topology.Algebra.PointTopology.Localization
public import TauCeti.Topology.Algebra.PointTopology.Presentation
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import TauCeti.Analysis.Calculus.ImplicitFunction.Data
import TauCeti.LinearAlgebra.Matrix.MaximalMinor

/-!
# Local charts on the points of smooth algebras

Let `K` be a complete nontrivially normed field and `P` a submersive presentation of a
`K`-algebra `S`, with finitely many variables `ι`, relations `σ`, and the injective map
`P.map : σ → ι` singling out the variables in which the Jacobian minor is taken. The values of a
point `x : S →ₐ[K] K` at the remaining variables, those outside `Set.range P.map`, are local
coordinates on the space of points with its evaluation topology: the map
`x ↦ (x (P.val i))_{i ∉ range P.map}` is a local homeomorphism into `K` to the power
`ι ∖ range P.map`. These are the smooth local parameters of `S`: by Mathlib's
`Algebra.SubmersivePresentation.basisKaehler`, the differentials of the same generators form a
basis of the Kähler differentials of `S` over `K`.

In the inverse chart the generator values are analytic by the analytic inverse function theorem.
Evaluation at any element of the algebra is a polynomial in those generator values.

The proof applies Mathlib's implicit function theorem, `ImplicitFunctionData`, to the relations
as left function and to the coordinate projection as right function, at the coordinate vector of
the point, through `ImplicitFunctionData.levelSetChart`. The two kernels are complementary
(`Matrix.isCompl_ker_mulVecLin_ker_funLeft`) because the Jacobian minor is invertible at every
point of a submersive presentation
(`Algebra.SubmersivePresentation.isUnit_det_jacobiMatrix_solution`). No hypothesis on the
characteristic of `K` is needed, and the theorem applies over `ℝ`, `ℂ` and every nonarchimedean
local field.

## Main results

* `Algebra.SubmersivePresentation.isLocalHomeomorph_pointCoords`: the coordinates outside
  `Set.range P.map` are a local homeomorphism on the points of a submersive presentation.
* `Algebra.IsStandardSmooth.exists_openPartialHomeomorph_points` and
  `Algebra.Smooth.exists_openPartialHomeomorph_points`: every point of a standard smooth, or
  more generally smooth, `K`-algebra lies in the source of a chart, a homeomorphism from an open
  set of points onto an open subset of some `Kⁿ`. The chart of a standard smooth algebra is
  evaluation at finitely many elements; for a smooth algebra the chart is defined on points `y`
  with `y g` a unit for some `g` with `x g ≠ 0`, and is evaluation at finitely many elements of
  the localization `A[1/g]`.

## References

* B. Conrad, *Weil and Grothendieck approaches to adelic points*, Enseign. Math. (2) 58 (2012),
  §4, p. 11.
* V. Platonov, A. Rapinchuk and I. Rapinchuk, *Algebraic Groups and Number Theory*, vol. 1,
  second edition, §3.1.
-/

public section

open MvPolynomial Topology

namespace Algebra.SubmersivePresentation

open TauCeti TauCeti.PointTopology

section Algebra

variable {K S ι σ : Type*} [CommRing K] [CommRing S] [Algebra K S] [Finite σ]
  (P : SubmersivePresentation K S ι σ)

/-- The coordinates of a point of a submersive presentation at the variables outside the range
of `P.map`. These are the smooth local parameters, and they are local coordinates on the points
(`Algebra.SubmersivePresentation.isLocalHomeomorph_pointCoords`). -/
def pointCoords (x : S →ₐ[K] K) : ↥(Set.range P.map)ᶜ → K :=
  fun i ↦ x (P.val i)

@[simp]
theorem pointCoords_apply (x : S →ₐ[K] K) (i : ↥(Set.range P.map)ᶜ) :
    P.pointCoords x i = x (P.val i) := (rfl)

variable [TopologicalSpace K]

@[continuity, fun_prop]
theorem continuous_pointCoords : Continuous P.pointCoords :=
  continuous_pi fun i ↦ by
    simpa only [pointCoords_apply] using PointTopology.continuous_eval (P.val i)

end Algebra

variable {K S ι σ : Type*} [NontriviallyNormedField K] [CompleteSpace K] [CommRing S]
  [Algebra K S] [Finite ι] [Finite σ] (P : SubmersivePresentation K S ι σ)

/-- The coordinate projection onto the variables outside the range of `P.map`. -/
private noncomputable def coordProj : (ι → K) →L[K] ↥(Set.range P.map)ᶜ → K :=
  ContinuousLinearMap.pi fun i ↦ ContinuousLinearMap.proj i.val

omit [CompleteSpace K] [Finite ι] in
private theorem coordProj_apply (v : ι → K) (i : ↥(Set.range P.map)ᶜ) :
    P.coordProj v i = v i := by
  simp [coordProj]

omit [CompleteSpace K] [Finite ι] in
private theorem toLinearMap_coordProj :
    (P.coordProj : (ι → K) →ₗ[K] ↥(Set.range P.map)ᶜ → K) =
      LinearMap.funLeft K K Subtype.val := by
  ext v i
  simp [coordProj_apply]

section Fintype

variable [Fintype ι] [Fintype σ] [DecidableEq σ] [Fintype ↥(Set.range P.map)ᶜ]

/-- The implicit-function data at the coordinate vector of a point: the relations as left
function and the coordinate projection onto the variables outside `range P.map` as right
function. -/
private noncomputable abbrev implicitData (x : S →ₐ[K] K) :
    ImplicitFunctionData K (ι → K) (σ → K) (↥(Set.range P.map)ᶜ → K) :=
  have hπ := P.toLinearMap_coordProj
  have hJ := fderiv_eval_family P.relation fun i ↦ x (P.val i)
  have hA := P.isUnit_det_jacobiMatrixAt_submatrix x
  { leftFun := fun y j ↦ eval y (P.relation j)
    leftDeriv := fderiv K (fun y j ↦ eval y (P.relation j)) fun i ↦ x (P.val i)
    rightFun := P.coordProj
    rightDeriv := P.coordProj
    pt := fun i ↦ x (P.val i)
    hasStrictFDerivAt_leftFun := (analyticOnNhd_eval_family P.relation _ trivial).hasStrictFDerivAt
    hasStrictFDerivAt_rightFun := P.coordProj.hasStrictFDerivAt
    range_leftDeriv := by
      rw [hJ, LinearMap.range_eq_top, Matrix.coe_mulVecLin]
      exact Matrix.mulVec_surjective_of_isUnit_det_submatrix _ P.map_inj hA
    range_rightDeriv := by
      rw [hπ, LinearMap.range_eq_top]
      exact LinearMap.funLeft_surjective_of_injective K K _ Subtype.val_injective
    isCompl_ker := by
      rw [hJ, hπ]
      exact Matrix.isCompl_ker_mulVecLin_ker_funLeft _ P.map_inj hA }

omit [Finite ι] in
/-- The implicit-function chart parametrizes the generator values analytically. -/
private theorem analyticAt_coe_levelSetChart_symm (x : S →ₐ[K] K)
    (z : ↥(Set.range P.map)ᶜ → K)
    (h : z ∈ ((P.implicitData x).levelSetChart
      (c := 0) (funext (P.eval_relation_eq_zero x))).target) :
    AnalyticAt K (fun w ↦ (((P.implicitData x).levelSetChart
      (c := 0) (funext (P.eval_relation_eq_zero x))).symm w : ι → K)) z := by
  let φ := P.implicitData x
  have hx := funext (P.eval_relation_eq_zero x)
  let e := φ.levelSetChart (c := 0) hx
  have hz : ((0 : σ → K), z) ∈ φ.toOpenPartialHomeomorph.target := by
    simpa only [e, ImplicitFunctionData.levelSetChart_target, Set.mem_preimage] using h
  let y := P.toPresentation.pointsHomeomorphZeroSet.symm (e.symm z)
  have hy : (P.implicitData y).pt = φ.toOpenPartialHomeomorph.symm (0, z) := by
    calc
      (P.implicitData y).pt = (e.symm z : ι → K) := by
        funext i
        exact P.toPresentation.pointsHomeomorphZeroSet_symm_apply_val _ i
      _ = _ := φ.coe_levelSetChart_symm_apply hx h
  obtain ⟨D, hD⟩ := (P.implicitData y).isInvertible_fderiv_prodFun
  have hfun : φ.prodFun = fun v ↦ (fun j ↦ eval v (P.relation j), P.coordProj v) :=
    funext φ.prodFun_apply
  have hfun' : (P.implicitData y).prodFun = φ.prodFun := by
    funext v
    rw [ImplicitFunctionData.prodFun_apply, hfun]
  have ha : AnalyticAt K φ.toOpenPartialHomeomorph (φ.toOpenPartialHomeomorph.symm (0, z)) := by
    rw [ImplicitFunctionData.toOpenPartialHomeomorph_coe, hfun]
    exact (analyticOnNhd_eval_family P.relation _ trivial).prod (P.coordProj.analyticAt _)
  have hInv := φ.toOpenPartialHomeomorph.analyticAt_symm hz ha <| by
    rw [ImplicitFunctionData.toOpenPartialHomeomorph_coe, ← hy]
    rw [hfun'] at hD
    exact hD.symm
  refine (hInv.comp (analyticAt_const.prod analyticAt_id)).congr ?_
  filter_upwards [e.open_target.mem_nhds h] with w hw
  exact (φ.coe_levelSetChart_symm_apply hx hw).symm

end Fintype

/-- The implicit function theorem gives a chart at each point, computed by `pointCoords`,
in which every coordinate evaluation is analytic. -/
private theorem exists_openPartialHomeomorph_pointCoords [Fintype ↥(Set.range P.map)ᶜ]
    (x : S →ₐ[K] K) :
    ∃ e : OpenPartialHomeomorph (S →ₐ[K] K) (↥(Set.range P.map)ᶜ → K),
      x ∈ e.source ∧ (∀ y, e y = P.pointCoords y) ∧
        ∀ a : S, AnalyticOnNhd K (fun z ↦ e.symm z a) e.target := by
  classical
  let := Fintype.ofFinite ι
  let := Fintype.ofFinite σ
  let e := (P.implicitData x).levelSetChart (c := 0) (funext (P.eval_relation_eq_zero x))
  have he := (P.implicitData x).mem_levelSetChart_source (c := 0)
    (funext (P.eval_relation_eq_zero x))
  refine ⟨P.pointsHomeomorphZeroSet.transOpenPartialHomeomorph e, ?_, fun y ↦ ?_, ?_⟩
  · have hx : P.pointsHomeomorphZeroSet x = ⟨_, funext (P.eval_relation_eq_zero x)⟩ :=
      Subtype.ext (P.toPresentation.coe_pointsHomeomorphZeroSet_apply x)
    simpa [hx] using he
  · simp only [Homeomorph.transOpenPartialHomeomorph_apply, Function.comp_apply,
      e, ImplicitFunctionData.levelSetChart_apply]
    ext i
    simp [coordProj_apply]
  · intro a z hz
    obtain ⟨p, rfl⟩ := P.aeval_val_surjective a
    have hz' : z ∈ e.target := by simpa using hz
    have ha := P.analyticAt_coe_levelSetChart_symm x z hz'
    have he (w : ↥(Set.range P.map)ᶜ → K) :
        (P.pointsHomeomorphZeroSet.transOpenPartialHomeomorph e).symm w (aeval P.val p) =
          eval (e.symm w : ι → K) p := by
      simp [MvPolynomial.comp_aeval_apply, MvPolynomial.aeval_eq_eval,
        P.toPresentation.pointsHomeomorphZeroSet_symm_apply_val]
    simp_rw [he]
    exact (AnalyticOnNhd.eval_mvPolynomial p _ trivial).comp ha

/-- **Local charts on the points of a submersive presentation.** The values of a point at the
variables outside the range of `P.map` form a local homeomorphism from the points, with their
evaluation topology, to `K` to the power `ι ∖ range P.map`. -/
theorem isLocalHomeomorph_pointCoords : IsLocalHomeomorph P.pointCoords := by
  let := Fintype.ofFinite ↥(Set.range P.map)ᶜ
  refine IsLocalHomeomorph.mk _ fun x ↦ ?_
  obtain ⟨e, hx, he, -⟩ := P.exists_openPartialHomeomorph_pointCoords x
  exact ⟨e, hx, fun y _ ↦ (he y).symm⟩

end Algebra.SubmersivePresentation

namespace Algebra

open TauCeti.PointTopology

variable {K A : Type*} [NontriviallyNormedField K] [CompleteSpace K] [CommRing A] [Algebra K A]

/-- Every point of a standard smooth `K`-algebra has a chart: an open partial homeomorphism from
the points, with their evaluation topology, to some `Kⁿ`, whose source contains the point, and
which is evaluation at finitely many elements `a i` of `A`. Every coordinate evaluation
pulled back by the inverse chart is analytic on the target. -/
theorem IsStandardSmooth.exists_openPartialHomeomorph_points [IsStandardSmooth K A]
    (x : A →ₐ[K] K) :
    ∃ (n : ℕ) (e : OpenPartialHomeomorph (A →ₐ[K] K) (Fin n → K)) (a : Fin n → A),
      x ∈ e.source ∧ (∀ y i, e y i = y (a i)) ∧
        ∀ b : A, AnalyticOnNhd K (fun z ↦ e.symm z b) e.target := by
  obtain ⟨ι, σ, _, _, ⟨P⟩⟩ := ‹IsStandardSmooth K A›.out
  let := Fintype.ofFinite ↥(Set.range P.map)ᶜ
  obtain ⟨e, hx, he, ha⟩ := P.exists_openPartialHomeomorph_pointCoords x
  let c := Fintype.equivFin ↥(Set.range P.map)ᶜ
  let q := ContinuousLinearEquiv.piCongrLeft K (fun _ : Fin _ ↦ K) c
  refine ⟨_, e.transHomeomorph q.toHomeomorph, fun i ↦ P.val (c.symm i), hx, fun y i ↦ ?_, ?_⟩
  · obtain ⟨i, rfl⟩ := c.surjective i
    simp [OpenPartialHomeomorph.transHomeomorph_apply, q, ContinuousLinearEquiv.piCongrLeft,
      he, SubmersivePresentation.pointCoords_apply]
  · intro b z hz
    have hz' : q.symm z ∈ e.target := by
      simpa only [OpenPartialHomeomorph.transHomeomorph_target, Set.mem_preimage,
        ContinuousLinearEquiv.coe_symm_toHomeomorph] using hz
    simpa only [OpenPartialHomeomorph.transHomeomorph_symm_apply, Function.comp_apply,
      ContinuousLinearEquiv.coe_symm_toHomeomorph] using (ha b _ hz').fun_comp (q.symm.analyticAt z)

/-- **Local charts on the points of a smooth algebra.** Every point `x` of a smooth `K`-algebra
has a chart: an open partial homeomorphism from the points, with their evaluation topology, to
some `Kⁿ`, whose source contains `x`. There is `g : A` with `x g ≠ 0` such that every point of
the source sends `g` to a unit, and the chart is evaluation at finitely many elements `b i` of the
localization `A[1/g]`, through the unique extension of a point to `A[1/g]`.
Every coordinate evaluation on `A` pulled back by the inverse chart is analytic on the target. -/
theorem Smooth.exists_openPartialHomeomorph_points [Smooth K A] (x : A →ₐ[K] K) :
    ∃ (n : ℕ) (e : OpenPartialHomeomorph (A →ₐ[K] K) (Fin n → K)) (g : A)
      (b : Fin n → Localization.Away g), x ∈ e.source ∧ x g ≠ 0 ∧
      e.source ⊆ {y | IsUnit (y g)} ∧
      (∀ (y : Localization.Away g →ₐ[K] K) i,
        e (y.comp (IsScalarTower.toAlgHom K A (Localization.Away g))) i = y (b i)) ∧
      ∀ a : A, AnalyticOnNhd K (fun z ↦ e.symm z a) e.target := by
  obtain ⟨s, hs, hst⟩ := Smooth.exists_span_eq_top_isStandardSmooth K A
  obtain ⟨g, hg, hxg⟩ : ∃ g ∈ s, x g ≠ 0 := by
    by_contra! h
    have hle : Ideal.span s ≤ RingHom.ker x := Ideal.span_le.2 h
    have h1 : (1 : A) ∈ RingHom.ker x := hle (hs ▸ Submodule.mem_top)
    simp at h1
  have := hst g hg
  let j : (Localization.Away g →ₐ[K] K) → A →ₐ[K] K :=
    fun y ↦ y.comp (IsScalarTower.toAlgHom K A (Localization.Away g))
  have hj : IsOpenEmbedding j := isOpenEmbedding_localization g Units.isEmbedding_val₀ <| by
    simpa only [isUnit_iff_ne_zero] using isOpen_ne
  have hrange : Set.range j = {y | IsUnit (y g)} := IsLocalization.Away.range_comp_toAlgHom g
  obtain ⟨y, rfl⟩ : x ∈ Set.range j := hrange ▸ isUnit_iff_ne_zero.2 hxg
  obtain ⟨n, e, b, he, heb, ha⟩ := IsStandardSmooth.exists_openPartialHomeomorph_points y
  refine ⟨n, e.lift_openEmbedding hj, g, b, Set.mem_image_of_mem j he, hxg, ?_, fun z i ↦ ?_, ?_⟩
  · rw [OpenPartialHomeomorph.lift_openEmbedding_source, ← hrange]
    exact Set.image_subset_range j e.source
  · rw [OpenPartialHomeomorph.lift_openEmbedding_apply, heb]
  · intro a z hz
    have hz' : z ∈ e.target := by
      simpa only [OpenPartialHomeomorph.lift_openEmbedding_target] using hz
    simpa only [OpenPartialHomeomorph.lift_openEmbedding_symm, Function.comp_apply, j,
      AlgHom.comp_apply, IsScalarTower.toAlgHom_apply] using
      ha (algebraMap A (Localization.Away g) a) z hz'

end Algebra

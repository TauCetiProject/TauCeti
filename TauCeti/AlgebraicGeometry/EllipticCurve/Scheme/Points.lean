/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
public import TauCeti.AlgebraicGeometry.EllipticCurve.Projective.Chart.Basic
public import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.ProjModel
import Mathlib.AlgebraicGeometry.EllipticCurve.Projective.Point
import TauCeti.AlgebraicGeometry.EllipticCurve.Projective.Nonsingular
-- Proof-only: the body of the zero section `projModelZero` is not exposed.
import all TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.ProjModel

/-!
# Points of the projective Weierstrass model over a field

Let `W` be an elliptic Weierstrass curve over a field `K`. This file identifies the sections of the
structure morphism `projModel W ⟶ Spec K` of the projective Weierstrass model with the points
`W.toAffine.Point` of `W`: the zero section `[0 : 1 : 0]` corresponds to the point at infinity, and
an affine point `(x, y)` to the section through the standard affine chart `D₊(Z)` at which
`X / Z = x` and `Y / Z = y`.

## Main definitions

* `WeierstrassCurve.chartRingEval W h`: evaluation at a solution `(x, y)` of the affine
  Weierstrass equation, the `K`-algebra map `K[X, Y, Z] ⧸ (W, Z - 1) → K` with `X ↦ x`, `Y ↦ y`
  and `Z ↦ 1` on the coordinate ring of the chart `D₊(Z)`.
* `WeierstrassCurve.projModelPointsEquiv W`: the equivalence between the sections of
  `projModel W ⟶ Spec K` and `W.toAffine.Point`.

## Main results

* `WeierstrassCurve.projModelPointsEquiv_projModelZero`: the zero section corresponds to `0`.
* `WeierstrassCurve.projModelPointsEquiv_symm_some`: the affine point `(x, y)` corresponds to
  `Spec` of `chartRingEval` at `(x, y)`, followed by the inclusion of the chart `D₊(Z)`.

## References

* [J. H. Silverman, *The Arithmetic of Elliptic Curves*, III.1][silverman2009]

## Provenance

Adapted from AINTLIB (`github.com/CBirkbeck/AINTLIB`, Apache-2.0) at commit
`c3415f32a313e19ace43e05479aeaa0d56ca287a`, file
`projects/ModularCurves/ModularCurves/EllipticCurve/WeierstrassModel.lean`, declarations
`specPoint_factors_through_chart`, `chartSolutionsEquiv`, `chartHomEquiv`,
`chartPointOfHom_factors_iff`, `projModel_points` and `projModelPointsEquivEll` (with `_zero` and
`_some`). Here the base is the field `K` itself, the model is the `Proj` of
`WeierstrassCurve.Projective.CoordinateRing`, the charts are read through
`WeierstrassCurve.Projective.awayEquivChartRing`, and the comparison goes through Mathlib's
nonsingular projective points `WeierstrassCurve.Projective.Point` and their equivalence with
`W.toAffine.Point`, in place of AINTLIB's split into the chart `D₊(Z)` and the point at infinity.
-/

public section

open CategoryTheory AlgebraicGeometry HomogeneousLocalization MvPolynomial

universe u

namespace WeierstrassCurve

variable {K : Type u} [Field K] (W : WeierstrassCurve K)

/-- Evaluation at a solution `(x, y)` of the affine Weierstrass equation on the coordinate ring
`K[X, Y, Z] ⧸ (W, Z - 1)` of the standard affine chart `D₊(Z)`: the `K`-algebra map with `X ↦ x`,
`Y ↦ y` and `Z ↦ 1`. -/
noncomputable def chartRingEval {x y : K} (h : W.toAffine.Equation x y) :
    W.toProjective.ChartRing 2 →ₐ[K] K :=
  Ideal.Quotient.liftₐ _ (aeval ![x, y, 1]) fun _ hp ↦ RingHom.mem_ker.mp <| Ideal.span_le.mpr
    (by simpa [Set.range_subset_iff, Fin.forall_fin_two, Projective.Equation] using
      (W.toProjective.equation_some x y).mpr h) hp

/-- `chartRingEval` sends the class of a polynomial `p` to its value `p(x, y, 1)`. -/
@[simp]
theorem chartRingEval_mk {x y : K} (h : W.toAffine.Equation x y) (p : MvPolynomial (Fin 3) K) :
    W.chartRingEval h (Ideal.Quotient.mk _ p) = eval ![x, y, 1] p := by
  simp [chartRingEval]

section Chart

-- Evaluation of the homogeneous coordinate ring at a solution `P` of the projective equation.
private noncomputable def evalHom (P : Fin 3 → K) (hP : W.toProjective.Equation P) :
    W.toProjective.CoordinateRing →+* K :=
  Ideal.Quotient.lift _ (eval P) ((RingHom.ker (eval P)).span_singleton_le_iff_mem.mpr hP)

variable {W} {P : Fin 3 → K} (hP : W.toProjective.Equation P) {i : Fin 3}

private theorem evalHom_mk (p : MvPolynomial (Fin 3) K) :
    W.evalHom P hP (Ideal.Quotient.mk _ p) = eval P p := rfl

-- The homomorphism `A_(Xᵢ) →+* K`, `Xⱼ / Xᵢ ↦ Pⱼ / Pᵢ`, of the chart `D₊(Xᵢ)` containing `P`.
private noncomputable def chartHom (hi : P i ≠ 0) :
    Away W.toProjective.grading (W.toProjective.coord i) →+* K :=
  Away.lift _ (W.evalHom P hP) <| by rwa [evalHom_mk, eval_X, isUnit_iff_ne_zero]

-- `chartHom` is a homomorphism over `K`: it is a left inverse of the structure map `K → A_(Xᵢ)`.
private theorem chartHom_comp_algebraMap (hi : P i ≠ 0) :
    (chartHom hP hi).comp ((fromZeroRingHom _ _).comp (algebraMap K (W.toProjective.grading 0))) =
      RingHom.id K :=
  RingHom.ext fun r ↦ (Away.lift_algebraMap _ _ _).trans <| (evalHom_mk hP _).trans (eval_C r)

private theorem chartHom_mk_X (hi : P i ≠ 0) (k : Fin 3) :
    chartHom hP hi ((W.toProjective.awayEquivChartRing i).symm (Ideal.Quotient.mk _ (X k))) =
      P k / P i := by
  simp [chartHom, evalHom_mk, div_eq_mul_inv]

-- The `K`-point of `projModel W` with homogeneous coordinates `P`, read on the chart `D₊(Xᵢ)`.
private noncomputable def chartPoint (hi : P i ≠ 0) : Spec (.of K) ⟶ W.projModel :=
  Spec.map (CommRingCat.ofHom (chartHom hP hi)) ≫
    Proj.awayι W.toProjective.grading (W.toProjective.coord i)
      (W.toProjective.coord_mem_grading i) one_pos

-- The point with coordinates `P` lies on the chart `D₊(Xⱼ)` exactly when `Pⱼ ≠ 0`.
private theorem chartPoint_mem_basicOpen_iff (hi : P i ≠ 0) (x : Spec (.of K)) (j : Fin 3) :
    chartPoint hP hi x ∈ Proj.basicOpen W.toProjective.grading (W.toProjective.coord j) ↔
      P j ≠ 0 := by
  rw [← Scheme.Hom.mem_preimage, chartPoint, Scheme.Hom.comp_preimage,
    Proj.awayι_preimage_basicOpen _ _ one_pos (W.toProjective.coord_mem_grading j) one_pos,
    SpecMap_preimage_basicOpen]
  -- the only prime ideal of `K` is `⊥`
  refine (PrimeSpectrum.mem_basicOpen _ _).trans ?_
  simp [Unique.eq_default x, chartHom, evalHom_mk, hi]

-- A homomorphism `A_(Xᵢ) →+* K` over `K` is, on the chart ring `K[X₀, X₁, X₂] ⧸ (W, Xᵢ - 1)`,
-- evaluation at its values on the fractions `Xⱼ / Xᵢ`.
private theorem comp_awayEquivChartRing_symm_mk
    {α : Away W.toProjective.grading (W.toProjective.coord i) →+* K}
    (hα : α.comp ((fromZeroRingHom _ _).comp (algebraMap K (W.toProjective.grading 0))) =
      RingHom.id K) :
    (α.comp (W.toProjective.awayEquivChartRing i).symm.toRingHom).comp (Ideal.Quotient.mk _) =
      eval fun k ↦ α ((W.toProjective.awayEquivChartRing i).symm (Ideal.Quotient.mk _ (X k))) := by
  refine MvPolynomial.ringHom_ext (fun r ↦ ?_) fun k ↦ by simp
  -- constants: `mk (C r)` is `algebraMap K _ r` (`rfl`), which the chart iso and `hα` send to `r`
  rw [eval_C]
  exact (congrArg α (RingHom.congr_fun
    (W.toProjective.awayEquivChartRing_symm_comp_algebraMap i) r)).trans (RingHom.congr_fun hα r)

-- In the chart ring `K[X₀, X₁, X₂] ⧸ (W, Xᵢ - 1)`, the coordinate `Xᵢ` is `1`.
private theorem chartRing_mk_X_self :
    (Ideal.Quotient.mk _ (X i) : W.toProjective.ChartRing i) = 1 :=
  (Ideal.Quotient.mk_eq_one_iff_sub_mem _).mpr (Ideal.subset_span ⟨1, by simp⟩)

-- A homomorphism `α : A_(Xᵢ) →+* K` over `K` is the `chartHom` of its values `Q` on the fractions
-- `Xⱼ / Xᵢ`, which solve the projective equation with `Qᵢ = 1`.
private theorem exists_eq_chartHom
    {α : Away W.toProjective.grading (W.toProjective.coord i) →+* K}
    (hα : α.comp ((fromZeroRingHom _ _).comp (algebraMap K (W.toProjective.grading 0))) =
      RingHom.id K) {Q : Fin 3 → K}
    (hQ : ∀ k, α ((W.toProjective.awayEquivChartRing i).symm (Ideal.Quotient.mk _ (X k))) = Q k) :
    ∃ (hP : W.toProjective.Equation Q) (hi : Q i ≠ 0), α = chartHom hP hi := by
  have hQi : Q i = 1 := by rw [← hQ, chartRing_mk_X_self, map_one, map_one]
  have hW : (Ideal.Quotient.mk _ W.toProjective.polynomial : W.toProjective.ChartRing i) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span ⟨0, by simp⟩)
  have hP : W.toProjective.Equation Q := by
    rw [Projective.Equation, ← funext hQ, ← RingHom.congr_fun (comp_awayEquivChartRing_symm_mk hα),
      RingHom.comp_apply, hW, map_zero]
  -- two homomorphisms over `K` agreeing on the fractions `Xⱼ / Xᵢ` are equal
  refine ⟨hP, hQi ▸ one_ne_zero, (RingHom.cancel_right
    (W.toProjective.awayEquivChartRing i).symm.surjective).mp <| Ideal.Quotient.ringHom_ext <|
      (comp_awayEquivChartRing_symm_mk hα).trans <| (congrArg eval (funext fun k ↦ ?_)).trans
        (comp_awayEquivChartRing_symm_mk (chartHom_comp_algebraMap hP _)).symm⟩
  rw [hQ, chartHom_mk_X, hQi, div_one]

end Chart

open Classical in
-- The section with homogeneous coordinates `P`, read on any chart `D₊(Xᵢ)` with `Pᵢ ≠ 0`; the zero
-- section when `P` is not a nonzero solution of the projective equation.
private noncomputable def repPoint (P : Fin 3 → K) : Spec (.of K) ⟶ W.projModel :=
  if h : W.toProjective.Equation P ∧ ∃ i, P i ≠ 0 then chartPoint h.1 h.2.choose_spec
  else W.projModelZero

-- The point does not depend on the chart: `D₊(Xᵢ)` and `D₊(Xⱼ)` give the same morphism.
private theorem repPoint_eq {P : Fin 3 → K} (hP : W.toProjective.Equation P) {i : Fin 3}
    (hi : P i ≠ 0) : W.repPoint P = chartPoint hP hi :=
  (dite_eq_left ⟨hP, i, hi⟩).trans (Proj.SpecMap_awayLift_awayι_eq ..)

private theorem repPoint_projModelOver (P : Fin 3 → K) : W.repPoint P ≫ W.projModelOver = 𝟙 _ := by
  simp [repPoint, dite_comp, chartPoint, awayι_projModelOver, ← Spec.map_comp,
    ← CommRingCat.ofHom_comp, chartHom_comp_algebraMap]

-- Rescaling the homogeneous coordinates does not change the point.
private theorem repPoint_smul (P : Fin 3 → K) (u : Kˣ) :
    W.repPoint ((u : K) • P) = W.repPoint P := by
  obtain ⟨hP, i, hi⟩ | h := em (W.toProjective.Equation P ∧ ∃ i, P i ≠ 0)
  · rw [W.repPoint_eq hP hi, W.repPoint_eq ((W.toProjective.equation_smul P u.isUnit).mpr hP)
      (smul_ne_zero u.ne_zero hi), chartPoint, chartPoint, chartHom, chartHom,
      Away.lift_eq_of_forall_mem _ _ u (fun n a ha ↦ ?_) (W.toProjective.coord_mem_grading i)]
    -- a form of degree `n` evaluated at `u • P` is `uⁿ` times its value at `P`
    obtain ⟨p, hp, rfl⟩ := W.toProjective.mem_grading_iff.mp ha
    exact hp.eval_smul P u
  -- neither `u • P` nor `P` is a nonzero solution, so both sides are the zero section
  · simp [repPoint, h, W.toProjective.equation_smul P u.isUnit]

-- The section attached to a nonsingular projective point.
private noncomputable def sectionOfPoint (P : W.toProjective.Point) :
    {g : Spec (CommRingCat.of K) ⟶ W.projModel // g ≫ W.projModelOver = 𝟙 _} :=
  P.point.liftOn (fun Q ↦ ⟨W.repPoint Q, W.repPoint_projModelOver Q⟩) fun _ Q ⟨u, h⟩ ↦
    Subtype.ext <| h ▸ W.repPoint_smul Q u

private theorem sectionOfPoint_mk {Q : Fin 3 → K} (hQ : W.toProjective.NonsingularLift ⟦Q⟧) :
    (W.sectionOfPoint ⟨hQ⟩).1 = W.repPoint Q := by
  rw [sectionOfPoint, Quotient.liftOn_mk]

private theorem exists_ne_zero_of_nonsingular {P : Fin 3 → K} (hP : W.toProjective.Nonsingular P) :
    ∃ i, P i ≠ 0 := by
  by_cases hz : P 2 = 0
  exacts [⟨1, Projective.Y_ne_zero_of_Z_eq_zero hP hz⟩, ⟨2, hz⟩]

private theorem sectionOfPoint_injective : Function.Injective W.sectionOfPoint := by
  rintro @⟨P, hP⟩ @⟨Q, hQ⟩ h
  induction P, Q using Quotient.ind₂ with | _ P Q => ?_
  have hPQ : W.repPoint P = W.repPoint Q :=
    (W.sectionOfPoint_mk hP).symm.trans <| (congrArg Subtype.val h).trans <| W.sectionOfPoint_mk hQ
  rw [Projective.nonsingularLift_iff] at hP hQ
  obtain ⟨i, hi⟩ := W.exists_ne_zero_of_nonsingular hP
  obtain ⟨j, hj⟩ := W.exists_ne_zero_of_nonsingular hQ
  -- the point `P` lies on the chart `D₊(Xⱼ)` of `Q`
  have hPj : P j ≠ 0 := by
    rwa [← chartPoint_mem_basicOpen_iff hP.1 hi default, ← W.repPoint_eq hP.1 hi, hPQ,
      W.repPoint_eq hQ.1 hj, chartPoint_mem_basicOpen_iff]
  -- hence `P`, `Q` give the same `A_(Xⱼ) →+* K`, taking `Xₖ / Xⱼ` to `Pₖ / Pⱼ = Qₖ / Qⱼ`
  rw [W.repPoint_eq hP.1 hPj, W.repPoint_eq hQ.1 hj, chartPoint, chartPoint, cancel_mono,
    Spec.map_inj, CommRingCat.hom_ext_iff, CommRingCat.hom_ofHom, CommRingCat.hom_ofHom] at hPQ
  have hu : (P j / Q j) • Q = P := funext fun k ↦ by
    rw [Pi.smul_apply, smul_eq_mul, div_mul_comm, ← chartHom_mk_X hQ.1 hj, ← hPQ, chartHom_mk_X,
      div_mul_cancel₀ _ hPj]
  exact Projective.Point.ext <| Quotient.sound <|
    hu ▸ Projective.smul_equiv Q (div_ne_zero hPj hj).isUnit

-- A morphism `Spec K ⟶ projModel W` factors through one of the standard charts `D₊(Xᵢ)`.
private theorem exists_spec_map_comp_awayι (g : Spec (CommRingCat.of K) ⟶ W.projModel) :
    ∃ (i : Fin 3) (α : CommRingCat.of (Away W.toProjective.grading (W.toProjective.coord i)) ⟶
      CommRingCat.of K), Spec.map α ≫ Proj.awayι W.toProjective.grading (W.toProjective.coord i)
        (W.toProjective.coord_mem_grading i) one_pos = g := by
  -- the charts `D₊(Xᵢ)` cover `projModel W`, and the image of `g` is a single point
  let 𝒰 := Proj.affineOpenCoverOfIrrelevantLESpan _ _ W.toProjective.coord_mem_grading
    (fun _ ↦ one_pos) W.toProjective.irrelevant_le_span_range_coord
  have h : Set.range g ⊆ Set.range (𝒰.f (𝒰.idx (g default))) :=
    Set.range_subset_iff.mpr fun y ↦ Unique.eq_default y ▸ 𝒰.covers _
  obtain ⟨α, hα⟩ := Spec.map_surjective (IsOpenImmersion.lift _ g h)
  exact ⟨𝒰.idx (g default), α, hα ▸ IsOpenImmersion.lift_fac _ _ h⟩

section Equiv

variable [W.IsElliptic]

private theorem sectionOfPoint_surjective : Function.Surjective W.sectionOfPoint := by
  rintro ⟨g, hg⟩
  obtain ⟨i, α, rfl⟩ := W.exists_spec_map_comp_awayι g
  -- `α` is a homomorphism over `K`
  rw [Category.assoc, awayι_projModelOver, ← Spec.map_comp, Spec.map_eq_id] at hg
  -- its values `Q` on the fractions `Xⱼ / Xᵢ` are homogeneous coordinates of `g`
  obtain ⟨hQ, hQi, hαQ⟩ := exists_eq_chartHom (α := α.hom) (congrArg CommRingCat.Hom.hom hg)
    fun _ ↦ rfl
  refine ⟨⟨(Projective.nonsingularLift_iff _).mpr <| (Projective.equation_iff_nonsingular_of_ne_zero
    fun h ↦ hQi (congrFun h i)).mp hQ⟩,
    Subtype.ext <| (W.sectionOfPoint_mk _).trans <| (W.repPoint_eq hQ hQi).trans ?_⟩
  rw [chartPoint, ← hαQ, CommRingCat.ofHom_hom]

private theorem sectionOfPoint_bijective : Function.Bijective W.sectionOfPoint :=
  ⟨W.sectionOfPoint_injective, W.sectionOfPoint_surjective⟩

open Classical in
/-- Over a field `K`, the sections of the structure morphism `projModel W ⟶ Spec K` of the
projective Weierstrass model of an elliptic Weierstrass curve `W` correspond to the points
`W.toAffine.Point`: the zero section `[0 : 1 : 0]` corresponds to `0`
(`projModelPointsEquiv_projModelZero`), and the section through the chart `D₊(Z)` at which
`X / Z = x` and `Y / Z = y` corresponds to the affine point `(x, y)`
(`projModelPointsEquiv_symm_some`). -/
noncomputable def projModelPointsEquiv :
    {g : Spec (CommRingCat.of K) ⟶ projModel W //
      g ≫ projModelOver W = 𝟙 (Spec (CommRingCat.of K))} ≃ W.toAffine.Point :=
  -- sections ≃ nonsingular projective points (every solution is nonsingular as `W` is elliptic)
  (Equiv.ofBijective _ W.sectionOfPoint_bijective).symm.trans
    (Projective.Point.toAffineAddEquiv W.toProjective).toEquiv

/-- The zero section `[0 : 1 : 0]` of the projective model corresponds to the point at
infinity. -/
@[simp]
theorem projModelPointsEquiv_projModelZero :
    W.projModelPointsEquiv ⟨W.projModelZero, W.projModelZero_projModelOver⟩ = 0 := by
  have h : W.sectionOfPoint 0 = ⟨W.projModelZero, W.projModelZero_projModelOver⟩ := by
    refine Subtype.ext ?_
    rw [Projective.Point.zero_def, sectionOfPoint_mk,
      W.repPoint_eq W.toProjective.equation_zero (i := 1) (by simp)]
    simp only [chartPoint, chartHom, projModelZero, awayYEvalZero]
    -- both sides are `Spec` of evaluation at `[0 : 1 : 0]` on the chart `D₊(Y)`
    congr 4
    exact Ideal.Quotient.ringHom_ext <| RingHom.ext fun p ↦ (W.toProjective.evalZero_mk p).symm
  simp [projModelPointsEquiv, ← h, Projective.Point.toAffineLift_zero]

/-- The affine point `(x, y)` corresponds to the section through the chart `D₊(Z)` at which
`X / Z = x` and `Y / Z = y`: `Spec` of the evaluation `chartRingEval` at `(x, y)` on
`K[X, Y, Z] ⧸ (W, Z - 1)`, read on `A_(Z)` through `awayEquivChartRing`, followed by the
inclusion of `D₊(Z)`. -/
theorem projModelPointsEquiv_symm_some {x y : K} (h : W.toAffine.Nonsingular x y) :
    (W.projModelPointsEquiv.symm (.some x y h)).1 =
      Spec.map (CommRingCat.ofHom ((W.chartRingEval h.1 : W.toProjective.ChartRing 2 →+* K).comp
        (W.toProjective.awayEquivChartRing 2 : _ →+* _))) ≫
        Proj.awayι W.toProjective.grading (W.toProjective.coord 2)
          (W.toProjective.coord_mem_grading 2) one_pos := by
  classical
  -- the section of `[x : y : 1]`, read on the chart `D₊(Z)`
  rw [projModelPointsEquiv, Equiv.symm_trans_apply, Equiv.symm_symm, Equiv.ofBijective_apply,
    AddEquiv.toEquiv_eq_coe, AddEquiv.coe_toEquiv_symm,
    Projective.Point.toAffineAddEquiv_symm_apply, Projective.Point.fromAffine_some,
    sectionOfPoint_mk]
  obtain ⟨hP, hz, hψ⟩ := exists_eq_chartHom
    (α := (W.chartRingEval h.1 : W.toProjective.ChartRing 2 →+* K).comp
      (W.toProjective.awayEquivChartRing 2).toRingHom) (Q := ![x, y, 1])
    -- `chartRingEval` composed with the chart isomorphism is a homomorphism over `K`
    (by simp [RingHom.ext_iff, ← W.toProjective.awayEquivChartRing_symm_comp_algebraMap])
    -- both send `Xₖ / Z` to the `k`-th coordinate of `[x : y : 1]`
    fun k ↦ by simp
  rw [W.repPoint_eq hP hz, chartPoint, ← hψ, RingEquiv.toRingHom_eq_coe]

end Equiv

end WeierstrassCurve

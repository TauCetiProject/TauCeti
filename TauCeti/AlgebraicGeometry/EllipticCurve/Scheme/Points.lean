/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
public import TauCeti.AlgebraicGeometry.EllipticCurve.Projective.Unimodular
public import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.Chart
-- Proof-only: the body of the zero section `projModelZero` is not exposed.
import all TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.ProjModel

/-!
# Points of the projective Weierstrass model

Let `W` be a Weierstrass curve over a commutative ring `R`, let `g : R →+* S` be a ring
homomorphism and let `P` be a solution of the projective Weierstrass equation of `W.map g` with a
unit coordinate `Pᵢ`. Then `P` gives an `S`-point of the projective Weierstrass model
`projModel W`, through the standard affine chart `D₊(Xᵢ)` at which `Xₖ / Xᵢ = Pₖ / Pᵢ`, lying over
`Spec g`.

Over a local ring `R`, this file identifies the sections of the structure morphism
`projModel W ⟶ Spec R` of the projective Weierstrass model with the projective point classes
`[X : Y : Z]` of solutions of the projective Weierstrass equation with unimodular coordinates
(`WeierstrassCurve.Projective.UnimodularLift`), that is, with one coordinate a unit. No
ellipticity is needed. A section factors through the standard affine chart `D₊(Xᵢ)` containing the
image of the closed point, and its homogeneous coordinates are its values on the fractions
`Xⱼ / Xᵢ`. The zero section `[0 : 1 : 0]` corresponds to the class of `(0, 1, 0)`, and a solution
`(x, y)` of the affine equation to the section through the chart `D₊(Z)` at which `X / Z = x` and
`Y / Z = y`.

When `R = K` is a field and `W` is elliptic, the unimodular classes are Mathlib's nonsingular
projective points, so the sections are identified with the points `W.toAffine.Point` of `W`, the
zero section corresponding to the point at infinity.

## Main definitions

* `WeierstrassCurve.projModelPoint W g hP hi`: the point `Spec S ⟶ projModel W` with homogeneous
  coordinates `P`, through the chart `D₊(Xᵢ)`.
* `WeierstrassCurve.chartRingEval W h`: evaluation at a solution `(x, y)` of the affine
  Weierstrass equation, the `R`-algebra map `R[X, Y, Z] ⧸ (W, Z - 1) → R` with `X ↦ x`, `Y ↦ y`
  and `Z ↦ 1` on the coordinate ring of the chart `D₊(Z)`.
* `WeierstrassCurve.projModelPointsEquivUnimodular W`: over a local ring, the equivalence between
  the sections of `projModel W ⟶ Spec R` and the unimodular projective point classes.
* `WeierstrassCurve.projModelPointsEquiv W`: over a field, for elliptic `W`, the equivalence
  between the sections of `projModel W ⟶ Spec K` and `W.toAffine.Point`.

## Main results

* `WeierstrassCurve.projModelPoint_projModelOver`: the point with homogeneous coordinates `P` lies
  over `Spec g`.
* `WeierstrassCurve.projModelPoint_eq_of_isUnit` and `WeierstrassCurve.projModelPoint_smul`: the
  point does not depend on the chart used to define it, nor on rescaling `P` by a unit.
* `WeierstrassCurve.projModelPoint_mem_basicOpen_iff`: the point lies on the chart `D₊(Xⱼ)` over a
  prime `x` of `S` exactly when `Pⱼ ∉ x`.
* `WeierstrassCurve.projModelPoint_eq_projModelPoint_iff`: two such points are equal exactly when
  they lie over the same ring homomorphism and their homogeneous coordinates differ by a unit.
* `WeierstrassCurve.SpecMap_projModelPoint`: the point is natural in the ring `S`.
* `WeierstrassCurve.chartι_eq_projModelPoint`: the chart `D₊(Xᵢ)` is the point with homogeneous
  coordinates the universal point of the chart ring.
* `WeierstrassCurve.projModelPointsEquivUnimodular_projModelZero`: the zero section corresponds to
  the class of `(0, 1, 0)`.
* `WeierstrassCurve.projModelPointsEquivUnimodular_symm_mk`: the class of a representative `P`
  with unit coordinate `Pᵢ` corresponds to the section through the chart `D₊(Xᵢ)` at which
  `Xₖ / Xᵢ = Pₖ / Pᵢ`.
* `WeierstrassCurve.projModelPointsEquivUnimodular_symm_mk_some`: the class of `(x, y, 1)`
  corresponds to `Spec` of `chartRingEval` at `(x, y)`, followed by the inclusion of the chart
  `D₊(Z)`.
* `WeierstrassCurve.projModelPointsEquiv_projModelZero`: the zero section corresponds to `0`.
* `WeierstrassCurve.projModelPointsEquiv_symm_some`: the affine point `(x, y)` corresponds to
  `Spec` of `chartRingEval` at `(x, y)`, followed by the inclusion of the chart `D₊(Z)`.

## References

* [J. H. Silverman, *The Arithmetic of Elliptic Curves*, III.1][silverman2009]
* N. M. Katz and B. Mazur, *Arithmetic Moduli of Elliptic Curves*, 2.2.

## Provenance

Adapted from AINTLIB (`github.com/CBirkbeck/AINTLIB`, Apache-2.0) at commit
`c3415f32a313e19ace43e05479aeaa0d56ca287a`, file
`projects/ModularCurves/ModularCurves/EllipticCurve/WeierstrassModel.lean`, declarations
`specPoint_factors_through_chart`, `chartSolutionsEquiv`, `chartHomEquiv`,
`chartPointOfHom_factors_iff`, `projModel_points` and `projModelPointsEquivEll` (with `_zero` and
`_some`). Here the chart arguments are carried out over a local ring `R` with unit coordinates in
place of nonzero ones, the model is the `Proj` of `WeierstrassCurve.Projective.CoordinateRing`, the
charts are read through `WeierstrassCurve.Projective.awayEquivChartRing`, and the field statement is
deduced through Mathlib's nonsingular projective points `WeierstrassCurve.Projective.Point` and
their equivalence with `W.toAffine.Point`, in place of AINTLIB's split into the chart `D₊(Z)` and
the point at infinity. The point `projModelPoint` of a solution with a unit coordinate over an
arbitrary ring homomorphism `g : R →+* S` corresponds to AINTLIB's `chartHomOfTriple` (file
`AdditionChartHom.lean`) followed by the chart inclusion; here it evaluates the homogeneous
coordinate ring at `P` in place of the source's dehomogenised chart ring.
-/

public section

open CategoryTheory AlgebraicGeometry HomogeneousLocalization MvPolynomial IsLocalRing

universe u

namespace WeierstrassCurve

section CommRing

variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

/-- Evaluation at a solution `(x, y)` of the affine Weierstrass equation on the coordinate ring
`R[X, Y, Z] ⧸ (W, Z - 1)` of the standard affine chart `D₊(Z)`: the `R`-algebra map with `X ↦ x`,
`Y ↦ y` and `Z ↦ 1`. -/
noncomputable def chartRingEval {x y : R} (h : W.toAffine.Equation x y) :
    W.toProjective.ChartRing 2 →ₐ[R] R :=
  Ideal.Quotient.liftₐ _ (aeval ![x, y, 1]) fun _ hp ↦ RingHom.mem_ker.mp <| Ideal.span_le.mpr
    (by simpa [Set.range_subset_iff, Fin.forall_fin_two, Projective.Equation] using
      (W.toProjective.equation_some x y).mpr h) hp

/-- `chartRingEval` sends the class of a polynomial `p` to its value `p(x, y, 1)`. -/
@[simp]
theorem chartRingEval_mk {x y : R} (h : W.toAffine.Equation x y) (p : MvPolynomial (Fin 3) R) :
    W.chartRingEval h (Ideal.Quotient.mk _ p) = eval ![x, y, 1] p := by
  simp [chartRingEval]

section Chart

variable {S : Type u} [CommRing S] (g : R →+* S) {P : Fin 3 → S}
  (hP : (W.toProjective.map g).Equation P) {i : Fin 3}

/-- The **point of the projective model with homogeneous coordinates `P`**. For a ring
homomorphism `g : R →+* S` and a solution `P` of the projective Weierstrass equation of `W.map g`
whose coordinate `Pᵢ` is a unit, this is the morphism `Spec S ⟶ projModel W` through the standard
affine chart `D₊(Xᵢ)` at which `Xₖ / Xᵢ = Pₖ / Pᵢ`: `Spec` of `Projective.awayEvalHom`, followed by
the inclusion of `D₊(Xᵢ)`. It lies over `Spec g` (`projModelPoint_projModelOver`). -/
noncomputable def projModelPoint (hi : IsUnit (P i)) : Spec (.of S) ⟶ W.projModel :=
  Spec.map (CommRingCat.ofHom (W.toProjective.awayEvalHom g hP hi)) ≫
    Proj.awayι W.toProjective.grading (W.toProjective.coord i)
      (W.toProjective.coord_mem_grading i) one_pos

/-- The point `projModelPoint W g hP hi` of the projective model lies over the morphism
`Spec S ⟶ Spec R` induced by `g`. -/
@[reassoc (attr := simp)]
theorem projModelPoint_projModelOver (hi : IsUnit (P i)) :
    W.projModelPoint g hP hi ≫ W.projModelOver = Spec.map (CommRingCat.ofHom g) := by
  rw [projModelPoint, Category.assoc, awayι_projModelOver, ← Spec.map_comp,
    ← CommRingCat.ofHom_comp, Projective.awayEvalHom_comp_algebraMap]

variable {W} {g} {hP}

/-- The point `projModelPoint W g hP hi` does not depend on the unit coordinate `Pᵢ` through whose
chart it is defined. -/
theorem projModelPoint_eq_of_isUnit {j : Fin 3} (hi : IsUnit (P i)) (hj : IsUnit (P j)) :
    W.projModelPoint g hP hi = W.projModelPoint g hP hj := by
  rw [projModelPoint, projModelPoint, Projective.awayEvalHom_def, Projective.awayEvalHom_def]
  exact Proj.SpecMap_awayLift_awayι_eq ..

/-- Rescaling the homogeneous coordinates by a unit `u` does not change the point
`projModelPoint W g hP hi`. -/
theorem projModelPoint_smul (u : Sˣ) (hi : IsUnit (P i)) :
    W.projModelPoint g (((W.toProjective.map g).equation_smul P u.isUnit).mpr hP)
      (u.isUnit.mul hi) = W.projModelPoint g hP hi := by
  rw [projModelPoint, projModelPoint, Projective.awayEvalHom_def, Projective.awayEvalHom_def,
    Away.lift_eq_of_forall_mem _ _ u (fun n a ha ↦ ?_) (W.toProjective.coord_mem_grading i)]
  -- a form of degree `n` evaluated at `u • P` is `uⁿ` times its value at `P`
  obtain ⟨p, hp, rfl⟩ := W.toProjective.mem_grading_iff.mp ha
  simp only [Projective.evalHom_mk, Pi.smul_def, smul_eq_mul]
  exact hp.eval₂_const_mul g P u

/-- The point `projModelPoint W g hP hi` is natural in the ring `S`: composing it with `Spec ψ`
for a ring homomorphism `ψ : S →+* T` gives the point with homogeneous coordinates `ψ ∘ P`, along
`ψ.comp g`. -/
@[reassoc (attr := simp)]
theorem SpecMap_projModelPoint {T : Type u} [CommRing T] (ψ : S →+* T) (hi : IsUnit (P i)) :
    Spec.map (CommRingCat.ofHom ψ) ≫ W.projModelPoint g hP hi =
      W.projModelPoint (ψ.comp g) (P := ψ ∘ P)
        (by simpa only [WeierstrassCurve.map_map] using hP.map ψ) (hi.map ψ) := by
  rw [projModelPoint, projModelPoint, ← Spec.map_comp_assoc, ← CommRingCat.ofHom_comp,
    Projective.awayEvalHom_def, Projective.awayEvalHom_def,
    RingHom.comp_homogeneousLocalizationAwayLift]
  -- `ψ` composed with evaluation at `P` is evaluation at `ψ ∘ P`
  refine congrArg (fun f ↦ Spec.map (CommRingCat.ofHom f) ≫ _)
    (Away.lift_eq_of_forall_mem _ _ 1 (fun n a ha ↦ ?_) (W.toProjective.coord_mem_grading i) _ _)
  obtain ⟨p, -, rfl⟩ := W.toProjective.mem_grading_iff.mp ha
  simp [Projective.evalHom_mk, MvPolynomial.eval₂_comp_left]

/-- The point `projModelPoint W g hP hi` with homogeneous coordinates `P` sends a point `x` of
`Spec S` into the standard chart `D₊(Xⱼ)` exactly when the coordinate `Pⱼ` does not lie in the
prime ideal `x`. -/
theorem projModelPoint_mem_basicOpen_iff (hi : IsUnit (P i)) (x : Spec (.of S)) (j : Fin 3) :
    W.projModelPoint g hP hi x ∈ Proj.basicOpen W.toProjective.grading (W.toProjective.coord j) ↔
      P j ∉ x.asIdeal := by
  rw [← Scheme.Hom.mem_preimage, projModelPoint, Scheme.Hom.comp_preimage,
    Proj.awayι_preimage_basicOpen _ _ one_pos (W.toProjective.coord_mem_grading j) one_pos,
    SpecMap_preimage_basicOpen]
  refine (PrimeSpectrum.mem_basicOpen _ _).trans ?_
  simp [Ideal.mul_unit_mem_iff_mem _ (Units.isUnit _)]

-- Equal points lie on the same charts: if the point with coordinates `P` equals the point with
-- coordinates `Q` and `Qⱼ` is a unit, then so is `Pⱼ`.
private theorem isUnit_of_projModelPoint_eq {g' : R →+* S} {Q : Fin 3 → S}
    {hQ : (W.toProjective.map g').Equation Q} {j : Fin 3} {hi : IsUnit (P i)} {hj : IsUnit (Q j)}
    (h : W.projModelPoint g hP hi = W.projModelPoint g' hQ hj) : IsUnit (P j) := by
  -- otherwise `Pⱼ` lies in a maximal ideal `m`, whose point of `Spec S` is on `D₊(Xⱼ)` for `Q`
  by_contra hPj
  obtain ⟨m, hm, hPm⟩ := exists_max_ideal_of_mem_nonunits (mem_nonunits_iff.mpr hPj)
  have hmem := (projModelPoint_mem_basicOpen_iff (hP := hQ) hj
    (⟨m, hm.isPrime⟩ : PrimeSpectrum S) j).mpr (Ideal.notMem_of_isUnit _ hj)
  rw [← h] at hmem
  exact (projModelPoint_mem_basicOpen_iff hi _ j).mp hmem hPm

/-- Two points of the projective model, with homogeneous coordinates `P` along `g` and `Q` along
`g'`, are equal exactly when `g = g'` and `P` is a unit multiple of `Q`. -/
theorem projModelPoint_eq_projModelPoint_iff {g' : R →+* S} {Q : Fin 3 → S}
    {hQ : (W.toProjective.map g').Equation Q} {j : Fin 3} {hi : IsUnit (P i)} {hj : IsUnit (Q j)} :
    W.projModelPoint g hP hi = W.projModelPoint g' hQ hj ↔ g = g' ∧ ∃ u : Sˣ, P = u • Q := by
  refine ⟨fun h ↦ ?_, ?_⟩
  · -- both points lie over `Spec g = Spec g'`
    obtain rfl : g = g' := by
      simpa [Spec.map_inj, CommRingCat.hom_ext_iff] using congrArg (· ≫ W.projModelOver) h
    -- the first point lies on the chart `D₊(Xⱼ)` of the second, so `Pⱼ` is a unit
    have hPj := isUnit_of_projModelPoint_eq h
    -- on that chart, both points send `Xₖ / Xⱼ` to `Pₖ / Pⱼ = Qₖ / Qⱼ`
    rw [projModelPoint_eq_of_isUnit hi hPj, projModelPoint, projModelPoint, cancel_mono,
      Spec.map_inj, CommRingCat.hom_ext_iff, CommRingCat.hom_ofHom, CommRingCat.hom_ofHom] at h
    refine ⟨rfl, hPj.unit * hj.unit⁻¹, funext fun k ↦ ?_⟩
    simpa [Units.smul_def, Units.mul_inv_eq_iff_eq_mul, mul_comm, mul_left_comm] using
      RingHom.congr_fun h ((W.toProjective.awayEquivChartRing j).symm (Ideal.Quotient.mk _ (X k)))
  · rintro ⟨rfl, u, rfl⟩
    exact (projModelPoint_smul (hP := hQ) u (by simpa [Units.smul_def] using hi)).trans
      (projModelPoint_eq_of_isUnit _ _)

variable (W) in
/-- The standard affine chart `D₊(Xᵢ)` of the projective model is the point with homogeneous
coordinates the universal point `chartPoint i` of the chart ring `R[X₀, X₁, X₂] ⧸ (W, Xᵢ - 1)`. -/
theorem chartι_eq_projModelPoint (i : Fin 3) :
    W.chartι i = W.projModelPoint (algebraMap R _)
      (by simpa only [Projective.baseChange, WeierstrassCurve.baseChange] using
        W.toProjective.equation_chartPoint i)
      (W.toProjective.chartPoint_self i ▸ isUnit_one) := by
  rw [chartι_def, projModelPoint]
  congr 2
  ext z
  obtain ⟨n, a, ha, rfl⟩ := Away.mk_surjective _ (W.toProjective.coord_mem_grading i) z
  obtain ⟨p, hp, rfl⟩ := W.toProjective.mem_grading_iff.mp ha
  -- the unit coordinate is `1`, and evaluation at the classes of the variables is the quotient map
  have hu : (W.toProjective.chartPoint_self i ▸ isUnit_one :
      IsUnit (W.toProjective.chartPoint i i)).unit = 1 :=
    Units.ext (W.toProjective.chartPoint_self i)
  simp only [CommRingCat.hom_ofHom, RingEquiv.coe_toRingHom, Projective.awayEquivChartRing_mk,
    Projective.awayEvalHom_mk, Projective.evalHom_mk, hu, one_pow, inv_one, Units.val_one, mul_one]
  rw [← aeval_def, ← Ideal.Quotient.mkₐ_eq_mk R, aeval_unique (Ideal.Quotient.mkₐ R _)]
  exact congrArg (aeval · p) (funext fun k ↦ (W.toProjective.chartPoint_apply i k).symm)

-- A solution of the equation of `W` solves the equation of `W.map (RingHom.id R)`, which is `W`
-- only up to unfolding `WeierstrassCurve.map`: `hP` itself is accepted by `awayEvalHom` and
-- `projModelPoint`, but the rewrite and `simp` lemmas about them then fail to match.
private theorem equation_map_id {P : Fin 3 → R} (hP : W.toProjective.Equation P) :
    (W.toProjective.map (RingHom.id R)).Equation P :=
  hP

-- `awayEvalHom` sends the fraction `Xₖ / Xᵢ` to `Pₖ / Pᵢ`.
private theorem awayEvalHom_mk_X {P : Fin 3 → R} (hP : W.toProjective.Equation P)
    (hi : IsUnit (P i)) (k : Fin 3) :
    W.toProjective.awayEvalHom (RingHom.id R) (equation_map_id hP) hi
        ((W.toProjective.awayEquivChartRing i).symm (Ideal.Quotient.mk _ (X k))) =
      P k * ↑hi.unit⁻¹ := by
  simp

-- A homomorphism `A_(Xᵢ) →+* R` over `R` is, on the chart ring `R[X₀, X₁, X₂] ⧸ (W, Xᵢ - 1)`,
-- evaluation at its values on the fractions `Xⱼ / Xᵢ`.
private theorem comp_awayEquivChartRing_symm_mk
    {α : Away W.toProjective.grading (W.toProjective.coord i) →+* R}
    (hα : α.comp ((fromZeroRingHom _ _).comp (algebraMap R (W.toProjective.grading 0))) =
      RingHom.id R) :
    (α.comp (W.toProjective.awayEquivChartRing i).symm.toRingHom).comp (Ideal.Quotient.mk _) =
      eval fun k ↦ α ((W.toProjective.awayEquivChartRing i).symm (Ideal.Quotient.mk _ (X k))) := by
  refine MvPolynomial.ringHom_ext (fun r ↦ ?_) fun k ↦ by simp
  -- constants: `mk (C r)` is `algebraMap R _ r` (`rfl`), which the chart iso and `hα` send to `r`
  rw [eval_C]
  exact (congrArg α (RingHom.congr_fun
    (W.toProjective.awayEquivChartRing_symm_comp_algebraMap i) r)).trans (RingHom.congr_fun hα r)

-- A homomorphism `α : A_(Xᵢ) →+* R` over `R` is the `awayEvalHom` of its values `Q` on the
-- fractions `Xⱼ / Xᵢ`, which solve the projective equation with `Qᵢ = 1`.
private theorem exists_eq_awayEvalHom
    {α : Away W.toProjective.grading (W.toProjective.coord i) →+* R}
    (hα : α.comp ((fromZeroRingHom _ _).comp (algebraMap R (W.toProjective.grading 0))) =
      RingHom.id R) {Q : Fin 3 → R}
    (hQ : ∀ k, α ((W.toProjective.awayEquivChartRing i).symm (Ideal.Quotient.mk _ (X k))) = Q k) :
    ∃ (hP : W.toProjective.Equation Q) (hi : IsUnit (Q i)),
      α = W.toProjective.awayEvalHom (RingHom.id R) (equation_map_id hP) hi := by
  have hQi : Q i = 1 := by rw [← hQ, Projective.chartRing_mk_X_self, map_one, map_one]
  have hW : (Ideal.Quotient.mk _ W.toProjective.polynomial : W.toProjective.ChartRing i) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span ⟨0, by simp⟩)
  have hP : W.toProjective.Equation Q := by
    rw [Projective.Equation, ← funext hQ, ← RingHom.congr_fun (comp_awayEquivChartRing_symm_mk hα),
      RingHom.comp_apply, hW, map_zero]
  have hi : IsUnit (Q i) := hQi ▸ isUnit_one
  -- two homomorphisms over `R` agreeing on the fractions `Xⱼ / Xᵢ` are equal
  refine ⟨hP, hi, (RingHom.cancel_right
    (W.toProjective.awayEquivChartRing i).symm.surjective).mp <| Ideal.Quotient.ringHom_ext <|
      (comp_awayEquivChartRing_symm_mk hα).trans <| (congrArg eval (funext fun k ↦ ?_)).trans
        (comp_awayEquivChartRing_symm_mk (W.toProjective.awayEvalHom_comp_algebraMap _ _ hi)).symm⟩
  rw [hQ, awayEvalHom_mk_X hP, Units.eq_mul_inv_iff_mul_eq, IsUnit.unit_spec, hQi, mul_one]

end Chart

open Classical in
-- The section with homogeneous coordinates `P`, read on any chart `D₊(Xᵢ)` with `Pᵢ` a unit; the
-- zero section when `P` is not a solution of the projective equation with a unit coordinate.
private noncomputable def repPoint (P : Fin 3 → R) : Spec (.of R) ⟶ W.projModel :=
  if h : W.toProjective.Equation P ∧ ∃ i, IsUnit (P i) then
    W.projModelPoint (RingHom.id R) (equation_map_id h.1) h.2.choose_spec
  else W.projModelZero

-- The point does not depend on the chart: `D₊(Xᵢ)` and `D₊(Xⱼ)` give the same morphism.
private theorem repPoint_eq {P : Fin 3 → R} (hP : W.toProjective.Equation P) {i : Fin 3}
    (hi : IsUnit (P i)) : W.repPoint P = W.projModelPoint (RingHom.id R) (equation_map_id hP) hi :=
  (dite_eq_left ⟨hP, i, hi⟩).trans (projModelPoint_eq_of_isUnit _ _)

private theorem repPoint_projModelOver (P : Fin 3 → R) : W.repPoint P ≫ W.projModelOver = 𝟙 _ := by
  simp [repPoint, dite_comp]

-- Rescaling the homogeneous coordinates does not change the point.
private theorem repPoint_smul (P : Fin 3 → R) (u : Rˣ) :
    W.repPoint ((u : R) • P) = W.repPoint P := by
  have hunit (i : Fin 3) : IsUnit (((u : R) • P) i) ↔ IsUnit (P i) := by
    rw [Pi.smul_apply, smul_eq_mul, Units.isUnit_units_mul]
  obtain ⟨hP, i, hi⟩ | h := em (W.toProjective.Equation P ∧ ∃ i, IsUnit (P i))
  · rw [W.repPoint_eq hP hi, W.repPoint_eq ((W.toProjective.equation_smul P u.isUnit).mpr hP)
      ((hunit i).mpr hi)]
    exact projModelPoint_smul u hi
  -- neither `u • P` nor `P` is a solution with a unit coordinate: both are the zero section
  · simp [repPoint, h, W.toProjective.equation_smul P u.isUnit]

-- The section attached to a unimodular projective point class.
private noncomputable def sectionOfClass
    (P : {P : Projective.PointClass R // W.toProjective.UnimodularLift P}) :
    {g : Spec (CommRingCat.of R) ⟶ W.projModel // g ≫ W.projModelOver = 𝟙 _} :=
  P.1.liftOn (fun Q ↦ ⟨W.repPoint Q, W.repPoint_projModelOver Q⟩) fun _ Q ⟨u, h⟩ ↦
    Subtype.ext <| h ▸ W.repPoint_smul Q u

private theorem sectionOfClass_mk {Q : Fin 3 → R}
    (hQ : W.toProjective.UnimodularLift ⟦Q⟧) : (W.sectionOfClass ⟨⟦Q⟧, hQ⟩).1 = W.repPoint Q := by
  rw [sectionOfClass, Quotient.liftOn_mk]

-- A representative of a unimodular class over a local ring has a unit coordinate.
private theorem exists_isUnit_of_unimodularLift [IsLocalRing R] {P : Fin 3 → R}
    (hP : W.toProjective.UnimodularLift ⟦P⟧) :
    W.toProjective.Equation P ∧ ∃ i, IsUnit (P i) :=
  ((Projective.unimodularLift_iff P).mp hP).imp_right
    TauCeti.Module.isUnimodular_iff_exists_isUnit.mp

private theorem sectionOfClass_injective [IsLocalRing R] : Function.Injective W.sectionOfClass := by
  rintro ⟨P, hP⟩ ⟨Q, hQ⟩ h
  induction P, Q using Quotient.ind₂ with | _ P Q => ?_
  rw [Subtype.ext_iff, sectionOfClass_mk, sectionOfClass_mk] at h
  obtain ⟨hP, i, hi⟩ := W.exists_isUnit_of_unimodularLift hP
  obtain ⟨hQ, j, hj⟩ := W.exists_isUnit_of_unimodularLift hQ
  -- equal points have proportional homogeneous coordinates
  rw [W.repPoint_eq hP hi, W.repPoint_eq hQ hj, projModelPoint_eq_projModelPoint_iff] at h
  obtain ⟨-, u, hu⟩ := h
  exact Subtype.ext <| Quotient.sound ⟨u, hu.symm⟩

-- Over a local ring, a morphism `Spec R ⟶ projModel W` factors through one of the standard charts
-- `D₊(Xᵢ)`: the chart containing the image of the closed point contains the whole image.
private theorem exists_spec_map_comp_awayι [IsLocalRing R]
    (g : Spec (CommRingCat.of R) ⟶ W.projModel) :
    ∃ (i : Fin 3) (α : CommRingCat.of (Away W.toProjective.grading (W.toProjective.coord i)) ⟶
      CommRingCat.of R), Spec.map α ≫ Proj.awayι W.toProjective.grading (W.toProjective.coord i)
        (W.toProjective.coord_mem_grading i) one_pos = g := by
  let 𝒰 := Proj.affineOpenCoverOfIrrelevantLESpan _ _ W.toProjective.coord_mem_grading
    (fun _ ↦ one_pos) W.toProjective.irrelevant_le_span_range_coord
  have h : Set.range g ⊆ Set.range (𝒰.f (𝒰.idx (g (closedPoint R)))) := by
    have htop := Scheme.preimage_eq_top_of_closedPoint_mem g
      (U := (𝒰.f (𝒰.idx (g (closedPoint R)))).opensRange) (𝒰.covers _)
    rintro _ ⟨y, rfl⟩
    exact (htop.ge trivial : y ∈ g ⁻¹ᵁ _)
  obtain ⟨α, hα⟩ := Spec.map_surjective (IsOpenImmersion.lift _ g h)
  exact ⟨𝒰.idx (g (closedPoint R)), α, hα ▸ IsOpenImmersion.lift_fac _ _ h⟩


private theorem sectionOfClass_surjective [IsLocalRing R] :
    Function.Surjective W.sectionOfClass := by
  rintro ⟨g, hg⟩
  obtain ⟨i, α, rfl⟩ := W.exists_spec_map_comp_awayι g
  -- `α` is a homomorphism over `R`
  rw [Category.assoc, awayι_projModelOver, ← Spec.map_comp, Spec.map_eq_id] at hg
  -- its values `Q` on the fractions `Xⱼ / Xᵢ` are homogeneous coordinates of `g`
  set Q : Fin 3 → R :=
    fun k ↦ α.hom ((W.toProjective.awayEquivChartRing i).symm (Ideal.Quotient.mk _ (X k)))
  obtain ⟨hQ, hi, hαQ⟩ := exists_eq_awayEvalHom (α := α.hom) (Q := Q)
    (congrArg CommRingCat.Hom.hom hg) fun _ ↦ rfl
  refine ⟨⟨⟦Q⟧, (Projective.unimodularLift_iff _).mpr
      ⟨hQ, TauCeti.Module.isUnimodular_of_isUnit_apply hi⟩⟩,
    Subtype.ext <| (W.sectionOfClass_mk _).trans <| (W.repPoint_eq hQ hi).trans ?_⟩
  rw [projModelPoint, ← hαQ, CommRingCat.ofHom_hom]

private theorem sectionOfClass_bijective [IsLocalRing R] : Function.Bijective W.sectionOfClass :=
  ⟨W.sectionOfClass_injective, W.sectionOfClass_surjective⟩

variable [IsLocalRing R]

/-- Over a local ring `R`, the sections of the structure morphism `projModel W ⟶ Spec R` of the
projective Weierstrass model correspond to the projective point classes `[X : Y : Z]` of solutions
of the projective Weierstrass equation with unimodular coordinates, that is, with one coordinate a
unit. The class of a representative `P` with unit coordinate `Pᵢ` corresponds to the section
through the chart `D₊(Xᵢ)` at which `Xₖ / Xᵢ = Pₖ / Pᵢ` (`projModelPointsEquivUnimodular_symm_mk`).
The zero section `[0 : 1 : 0]` corresponds to the class of `(0, 1, 0)`
(`projModelPointsEquivUnimodular_projModelZero`), and the section through the chart `D₊(Z)` at which
`X / Z = x` and `Y / Z = y` to the class of `(x, y, 1)`
(`projModelPointsEquivUnimodular_symm_mk_some`). No ellipticity is assumed. -/
noncomputable def projModelPointsEquivUnimodular :
    {g : Spec (CommRingCat.of R) ⟶ projModel W //
      g ≫ projModelOver W = 𝟙 (Spec (CommRingCat.of R))} ≃
      {P : Projective.PointClass R // W.toProjective.UnimodularLift P} :=
  (Equiv.ofBijective _ W.sectionOfClass_bijective).symm

/-- The zero section `[0 : 1 : 0]` of the projective model corresponds to the class of
`(0, 1, 0)`. -/
@[simp]
theorem projModelPointsEquivUnimodular_projModelZero :
    W.projModelPointsEquivUnimodular ⟨W.projModelZero, W.projModelZero_projModelOver⟩ =
      ⟨⟦![0, 1, 0]⟧, W.toProjective.unimodularLift_zero⟩ := by
  rw [projModelPointsEquivUnimodular, Equiv.symm_apply_eq]
  refine Subtype.ext ?_
  rw [Equiv.ofBijective_apply, sectionOfClass_mk,
    W.repPoint_eq W.toProjective.equation_zero (i := 1) (by simp)]
  simp only [projModelPoint, projModelZero, awayYEvalZero]
  -- both sides are `Spec` of a homomorphism `A_(Y) → R` followed by the inclusion of `D₊(Y)`
  rw [cancel_mono, Spec.map_inj, CommRingCat.hom_ext_iff, CommRingCat.hom_ofHom,
    CommRingCat.hom_ofHom]
  -- both homomorphisms are induced by evaluation at `[0 : 1 : 0]`
  refine Eq.trans ?_ (Projective.awayEvalHom_def ..).symm
  refine Away.lift_eq_of_forall_mem _ _ 1 (fun n a ha ↦ ?_) (W.toProjective.coord_mem_grading 1) _ _
  obtain ⟨p, -, rfl⟩ := W.toProjective.mem_grading_iff.mp ha
  simp [eval₂_id]

/-- The class of a unimodular representative `P` with unit coordinate `Pᵢ` corresponds to the
section through the chart `D₊(Xᵢ)` at which `Xₖ / Xᵢ = Pₖ / Pᵢ`: `Spec` of any `R`-algebra map
`α : R[X₀, X₁, X₂] ⧸ (W, Xᵢ - 1) → R` with `α(Xₖ) = Pₖ / Pᵢ`, read on `A_(Xᵢ)` through
`awayEquivChartRing`, followed by the inclusion of `D₊(Xᵢ)`. -/
theorem projModelPointsEquivUnimodular_symm_mk {P : Fin 3 → R}
    (hP : W.toProjective.UnimodularLift ⟦P⟧) {i : Fin 3} (hi : IsUnit (P i))
    (α : W.toProjective.ChartRing i →ₐ[R] R)
    (hα : ∀ k, α (Ideal.Quotient.mk _ (X k)) = P k * ↑hi.unit⁻¹) :
    (W.projModelPointsEquivUnimodular.symm ⟨⟦P⟧, hP⟩).1 =
      Spec.map (CommRingCat.ofHom ((α : W.toProjective.ChartRing i →+* R).comp
        (W.toProjective.awayEquivChartRing i : _ →+* _))) ≫
        Proj.awayι W.toProjective.grading (W.toProjective.coord i)
          (W.toProjective.coord_mem_grading i) one_pos := by
  rw [projModelPointsEquivUnimodular, Equiv.symm_symm, Equiv.ofBijective_apply, sectionOfClass_mk]
  -- `α` sends `Xₖ / Xᵢ` to the `k`-th coordinate of the rescaled representative `Pᵢ⁻¹ • P`
  obtain ⟨hQ, hQi, hψ⟩ := exists_eq_awayEvalHom
    (α := (α : W.toProjective.ChartRing i →+* R).comp
      (W.toProjective.awayEquivChartRing i).toRingHom) (Q := ((hi.unit⁻¹ : Rˣ) : R) • P)
    (by simp [RingHom.ext_iff, ← W.toProjective.awayEquivChartRing_symm_comp_algebraMap])
    fun k ↦ by simpa [mul_comm] using hα k
  rw [← W.repPoint_smul P hi.unit⁻¹, W.repPoint_eq hQ hQi, projModelPoint, ← hψ,
    RingEquiv.toRingHom_eq_coe]

/-- The class of `(x, y, 1)` corresponds to the section through the chart `D₊(Z)` at which
`X / Z = x` and `Y / Z = y`: `Spec` of the evaluation `chartRingEval` at `(x, y)` on
`R[X, Y, Z] ⧸ (W, Z - 1)`, read on `A_(Z)` through `awayEquivChartRing`, followed by the
inclusion of `D₊(Z)`. -/
theorem projModelPointsEquivUnimodular_symm_mk_some {x y : R} (h : W.toAffine.Equation x y) :
    (W.projModelPointsEquivUnimodular.symm
        ⟨⟦![x, y, 1]⟧, (W.toProjective.unimodularLift_some x y).mpr h⟩).1 =
      Spec.map (CommRingCat.ofHom ((W.chartRingEval h : W.toProjective.ChartRing 2 →+* R).comp
        (W.toProjective.awayEquivChartRing 2 : _ →+* _))) ≫
        Proj.awayι W.toProjective.grading (W.toProjective.coord 2)
          (W.toProjective.coord_mem_grading 2) one_pos := by
  rw [projModelPointsEquivUnimodular, Equiv.symm_symm, Equiv.ofBijective_apply, sectionOfClass_mk]
  obtain ⟨hP, hz, hψ⟩ := exists_eq_awayEvalHom
    (α := (W.chartRingEval h : W.toProjective.ChartRing 2 →+* R).comp
      (W.toProjective.awayEquivChartRing 2).toRingHom) (Q := ![x, y, 1])
    -- `chartRingEval` composed with the chart isomorphism is a homomorphism over `R`
    (by simp [RingHom.ext_iff, ← W.toProjective.awayEquivChartRing_symm_comp_algebraMap])
    -- both send `Xₖ / Z` to the `k`-th coordinate of `[x : y : 1]`
    fun k ↦ by simp
  rw [W.repPoint_eq hP hz, projModelPoint, ← hψ, RingEquiv.toRingHom_eq_coe]

end CommRing

section Field

variable {K : Type u} [Field K] (W : WeierstrassCurve K) [W.IsElliptic]

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
  -- unimodular classes are nonsingular projective points, as `W` is elliptic
  W.projModelPointsEquivUnimodular.trans <|
    (Projective.Point.equivUnimodularLift W.toProjective).symm.trans
      (Projective.Point.toAffineAddEquiv W.toProjective).toEquiv

/-- The zero section `[0 : 1 : 0]` of the projective model corresponds to the point at
infinity. -/
@[simp]
theorem projModelPointsEquiv_projModelZero :
    W.projModelPointsEquiv ⟨W.projModelZero, W.projModelZero_projModelOver⟩ = 0 := by
  have h : (Projective.Point.equivUnimodularLift W.toProjective).symm
      ⟨⟦![0, 1, 0]⟧, W.toProjective.unimodularLift_zero⟩ = 0 :=
    Projective.Point.ext <| by
      rw [Projective.Point.equivUnimodularLift_symm_point, Projective.Point.zero_def]
  simp [projModelPointsEquiv, h, Projective.Point.toAffineLift_zero]

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
  have hP : Projective.Point.equivUnimodularLift W.toProjective
      ((Projective.Point.toAffineAddEquiv W.toProjective).symm (.some x y h)) =
        ⟨⟦![x, y, 1]⟧, (W.toProjective.unimodularLift_some x y).mpr h.1⟩ :=
    Subtype.ext <| by
      rw [Projective.Point.coe_equivUnimodularLift, Projective.Point.toAffineAddEquiv_symm_apply,
        Projective.Point.fromAffine_some]
  rw [← projModelPointsEquivUnimodular_symm_mk_some, ← hP]
  simp only [projModelPointsEquiv, Equiv.symm_trans_apply, Equiv.symm_symm,
    AddEquiv.toEquiv_eq_coe, AddEquiv.coe_toEquiv_symm]

end Field

end WeierstrassCurve

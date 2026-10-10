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
`Spec g`. When `S` is a local ring, every `S`-point of `projModel W` lying over `Spec g` arises in
this way.

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
* `WeierstrassCurve.projModelPoint_map`: `Proj.map F` of a graded ring homomorphism `F` of
  homogeneous coordinate rings carries the point with homogeneous coordinates `P'` to the point
  with homogeneous coordinates `P`, when the value of `F a` at `P'` is `cⁿ` times the value of `a`
  at `P` for a unit `c` and every homogeneous `a` of degree `n`.
* `WeierstrassCurve.chartι_eq_projModelPoint`: the chart `D₊(Xᵢ)` is the point with homogeneous
  coordinates the universal point of the chart ring.
* `WeierstrassCurve.projModelPoint_eqToHom`: an equality of Weierstrass curves identifies the
  points with the same homogeneous coordinates.
* `WeierstrassCurve.projModelPoint_projModelVariableChangeIso_hom`: the isomorphism
  `projModel (C • W) ≅ projModel W` induced by a change of variables `C` sends the point with
  homogeneous coordinates `P` to the point with homogeneous coordinates `(C.map g).toMatrix *ᵥ P`.
* `WeierstrassCurve.projModelPointsEquivUnimodular_projModelZero`: the zero section corresponds to
  the class of `(0, 1, 0)`.
* `WeierstrassCurve.projModelPointsEquivUnimodular_projModelPoint`: the section with homogeneous
  coordinates `P` corresponds to the class of `P`.
* `WeierstrassCurve.projModelPointsEquivUnimodular_symm_mk`: the class of a representative `P`
  with unit coordinate `Pᵢ` corresponds to the section through the chart `D₊(Xᵢ)` at which
  `Xₖ / Xᵢ = Pₖ / Pᵢ`.
* `WeierstrassCurve.projModelPointsEquivUnimodular_symm_mk_some`: the class of `(x, y, 1)`
  corresponds to `Spec` of `chartRingEval` at `(x, y)`, followed by the inclusion of the chart
  `D₊(Z)`.
* `WeierstrassCurve.SpecMap_chartι`: a point `Spec α` of the chart `D₊(Xᵢ)` is the point with
  homogeneous coordinates the image under `α` of the universal point of the chart ring.
* `WeierstrassCurve.exists_eq_projModelPoint`: a point of the projective model with values in a
  local ring `S`, lying over `Spec g`, is the point with homogeneous coordinates `P`, for some
  solution `P` of the projective Weierstrass equation of `W.map g` with a unit coordinate.
* `WeierstrassCurve.exists_ringHom_eq_projModelPoint`: a point of the projective model with values
  in a local ring `S` is the point with homogeneous coordinates `P`, for some ring homomorphism
  `g : R →+* S` and some solution `P` of the projective Weierstrass equation of `W.map g` with a
  unit coordinate.
* `WeierstrassCurve.exists_eq_projModelPoint_of_forall_mem_basicOpen`: a point of the projective
  model with values in a commutative ring `S`, lying over `Spec g`, all of whose values lie on the
  chart `D₊(Xᵢ)`, is the point with homogeneous coordinates `Q`, for some solution `Q` of the
  projective Weierstrass equation of `W.map g` with `Qᵢ = 1`.
* `WeierstrassCurve.SpecMap_projModelZero`: the zero section, restricted along `Spec g`, is the
  point with homogeneous coordinates `(0, 1, 0)`.
* `WeierstrassCurve.projModelPointsEquiv_projModelZero`: the zero section corresponds to `0`.
* `WeierstrassCurve.projModelPointsEquiv_symm_some`: the affine point `(x, y)` corresponds to
  `Spec` of `chartRingEval` at `(x, y)`, followed by the inclusion of the chart `D₊(Z)`.
* `WeierstrassCurve.projModelPointsEquiv_projModelPoint`: the section with homogeneous coordinates
  `P` corresponds to the point `WeierstrassCurve.Projective.Point.toAffine W P`.

## References

* [J. H. Silverman, *The Arithmetic of Elliptic Curves*, III.1][silverman2009]
* N. M. Katz and B. Mazur, *Arithmetic Moduli of Elliptic Curves*, 2.2.

## Provenance

`SpecMap_chartι` is adapted from AINTLIB (`github.com/CBirkbeck/AINTLIB`, Apache-2.0) at commit
`c3415f32a313e19ace43e05479aeaa0d56ca287a`, file
`projects/ModularCurves/ModularCurves/EllipticCurve/AdditionSpecPoints.lean`: it corresponds to
`chartPointTriple` with `ChartPointTriple.equation`, `ChartPointTriple.self_eq_one` and
`ChartPointTriple.eq_chartHom` (stated with `chartAwayHomOfTriple`, file `AdditionChartHom.lean`).
There a ring homomorphism out of the chart ring `A_(Xₖ)`, compatible with the `R`-algebra
structures, is the chart homomorphism `chartAwayHomOfTriple` of its own coordinate triple; here the
statement is an equality of points of the projective model, for any ring homomorphism out of
`ChartRing i`. `exists_eq_projModelPoint` is not stated in the source, which factors a point with
values in a field through a chart (`specPoint_factors_through_chart`, file
`WeierstrassModel.lean`) and reads off that the chart homomorphism is compatible with the
`R`-algebra structures (`chartHom_compat_of_specPoint`, file `AdditionSpecPoints.lean`); here the
point has values in any local ring `S`, over any ring homomorphism `g : R →+* S`.

`SpecMap_projModelZero` corresponds to AINTLIB's `projModelFromOfGlobalSections_zero_one_zero`
(file `WeierstrassModelCoordinateTransition.lean`), which rests, as here, on the equality of
evaluation homomorphisms `projModelEval_zero_one_zero` (file `WeierstrassModelCoordinates.lean`):
evaluation at `(0, 1, 0)` along a ring homomorphism `f` is `f` after the evaluation defining the
zero section. There, for a Weierstrass curve over the ring of global sections of a scheme `X`, the
morphism from `X` with homogeneous coordinates `(0, 1, 0)`, built by `Proj.fromOfGlobalSections`,
is the zero section preceded by `X ⟶ Spec Γ(X, ⊤)`; here the zero section restricted along any ring
homomorphism `g : R →+* S` is the point `projModelPoint` with homogeneous coordinates `(0, 1, 0)`,
along `g`. `exists_ringHom_eq_projModelPoint` is not stated in AINTLIB, whose computations on
points with values in a field `K` take `K` with the algebra structure for which the composite of
the point with the structure morphism is `Spec` of the structure homomorphism
(`structure_eq_specMap`, file `GroupLawAxioms.lean`).
`exists_eq_projModelPoint_of_forall_mem_basicOpen` corresponds to AINTLIB's `chartHomEquiv` (file
`WeierstrassModel.lean`), which identifies the points over the base, with values in a commutative
`R`-algebra, that factor through the chart `D₊(Xᵢ)` with the ring homomorphisms out of `A_(Xᵢ)`
compatible with the `R`-algebra structures; here the factorisation is deduced from the values of
the point lying on the chart, and the point is given by homogeneous coordinates.

Adapted from AINTLIB (`github.com/CBirkbeck/AINTLIB`, Apache-2.0) at commit
`c3415f32a313e19ace43e05479aeaa0d56ca287a`, file
`projects/ModularCurves/ModularCurves/EllipticCurve/WeierstrassModel.lean`, declarations
`specPoint_factors_through_chart`, `chartSolutionsEquiv`, `chartHomEquiv`,
`chartPointOfHom_factors_iff`, `projModel_points` and `projModelPointsEquivEll` (with `_zero` and
`_some`), and file `AdditionSpecPoints.lean`, declaration `Dictionary.eq_toAffine`, as
`projModelPointsEquiv_projModelPoint`. Here the chart arguments are carried out over a local ring
`R` with unit coordinates in place of nonzero ones, the model is the `Proj` of
`WeierstrassCurve.Projective.CoordinateRing`, the charts are read through
`WeierstrassCurve.Projective.awayEquivChartRing`, and the field statement is deduced through
Mathlib's nonsingular projective points `WeierstrassCurve.Projective.Point` and their equivalence
with `W.toAffine.Point`, in place of AINTLIB's split into the chart `D₊(Z)` and the point at
infinity. The point `projModelPoint` of a solution with a unit coordinate over an arbitrary ring
homomorphism `g : R →+* S` corresponds to AINTLIB's `chartHomOfTriple` (file
`AdditionChartHom.lean`) followed by the chart inclusion; here it evaluates the homogeneous
coordinate ring at `P` in place of the source's dehomogenised chart ring. `projModelPoint_map` is
not taken from AINTLIB; it is the analogue for `projModelPoint` of `projModelZero_map`. AINTLIB
states the corresponding fact for the morphisms built by `Proj.fromOfGlobalSections`
(`Proj.fromOfGlobalSections_map`, file `ForMathlib/ProjFromGlobalSectionsMap.lean`).
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

/-- Let `F` be a graded ring homomorphism from the homogeneous coordinate ring of `W` over `R` to
that of `W'` over `R'`. If, for a unit `c` of `S` and every homogeneous `a` of degree `n`, the value
of `F a` at `P'` along `g'` is `cⁿ` times the value of `a` at `P` along `g`, then `Proj.map F`
carries the point of `projModel W'` with homogeneous coordinates `P'` to the point of `projModel W`
with homogeneous coordinates `P`. -/
@[reassoc]
theorem projModelPoint_map {R' : Type u} [CommRing R'] {W' : WeierstrassCurve R'}
    (F : W.toProjective.grading →+*ᵍ W'.toProjective.grading)
    (hF : HomogeneousIdeal.irrelevant W'.toProjective.grading ≤
      (HomogeneousIdeal.irrelevant W.toProjective.grading).map F)
    {g' : R' →+* S} {P' : Fin 3 → S} {hP' : (W'.toProjective.map g').Equation P'} (c : Sˣ)
    (h : ∀ n, ∀ a ∈ W.toProjective.grading n,
      W'.toProjective.evalHom g' hP' (F a) = c ^ n * W.toProjective.evalHom g hP a)
    {j : Fin 3} (hj : IsUnit (P' j)) (hi : IsUnit (P i)) :
    W'.projModelPoint g' hP' hj ≫ Proj.map F hF = W.projModelPoint g hP hi := by
  have hXi := W.toProjective.coord_mem_grading i
  -- the point of `projModel W'` may be read on the chart away from the image of `Xᵢ`
  have hFi : IsUnit (W'.toProjective.evalHom g' hP' (F (W.toProjective.coord i))) := by
    rw [h 1 _ hXi, pow_one, Projective.evalHom_mk, eval₂_X]
    exact c.isUnit.mul hi
  rw [projModelPoint, projModelPoint, Projective.awayEvalHom_def, Projective.awayEvalHom_def,
    Proj.SpecMap_awayLift_awayι_eq _ _ one_pos (GradedFunLike.map_mem F hXi) one_pos _ hFi,
    Category.assoc, Proj.awayι_comp_map _ _ one_pos _ hXi, ← Spec.map_comp_assoc,
    ← CommRingCat.ofHom_comp, Away.lift_comp_map]
  -- the two evaluations agree on fractions of degree zero, where the powers of `c` cancel
  congr 3
  exact Away.lift_eq_of_forall_mem _ _ c h hXi _ _

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
  obtain ⟨p, _, rfl⟩ := W.toProjective.mem_grading_iff.mp ha
  -- the unit coordinate is `1`, and evaluation at the classes of the variables is the quotient map
  have hu : (W.toProjective.chartPoint_self i ▸ isUnit_one :
      IsUnit (W.toProjective.chartPoint i i)).unit = 1 :=
    Units.ext (W.toProjective.chartPoint_self i)
  simp only [CommRingCat.hom_ofHom, RingEquiv.coe_toRingHom, Projective.awayEquivChartRing_mk,
    Projective.awayEvalHom_mk, Projective.evalHom_mk, hu, one_pow, inv_one, Units.val_one, mul_one]
  rw [← aeval_def, ← Ideal.Quotient.mkₐ_eq_mk R, aeval_unique (Ideal.Quotient.mkₐ R _)]
  exact congrArg (aeval · p) (funext fun k ↦ (W.toProjective.chartPoint_apply i k).symm)

/-- Transport of points along an equality of Weierstrass curves: the point of `projModel W₁` with
homogeneous coordinates `P`, followed by the identification of `projModel W₁` with `projModel W₂`
induced by `h : W₁ = W₂`, is the point of `projModel W₂` with the same coordinates. -/
@[reassoc]
theorem projModelPoint_eqToHom {W₁ W₂ : WeierstrassCurve R} (h : W₁ = W₂)
    {hP : (W₁.toProjective.map g).Equation P} (hi : IsUnit (P i)) :
    W₁.projModelPoint g hP hi ≫ eqToHom (congrArg projModel h) =
      W₂.projModelPoint g (h ▸ hP) hi := by
  subst h
  simp

open Matrix in
/-- The isomorphism `projModel (C • W) ≅ projModel W` induced by a change of variables `C` sends
the point `projModelPoint (C • W) g hP hi` with homogeneous coordinates `P` to the point with
homogeneous coordinates `(C.map g).toMatrix *ᵥ P = [u²P₀ + rP₂ : u²sP₀ + u³P₁ + tP₂ : P₂]`
(with `u, r, s, t` mapped along `g`), defined through any chart `D₊(Xⱼ)` on which that
coordinate is a unit. -/
@[reassoc]
theorem projModelPoint_projModelVariableChangeIso_hom {C : VariableChange R}
    {hP : ((C • W).toProjective.map g).Equation P} (hi : IsUnit (P i)) {j : Fin 3}
    (hj : IsUnit (((C.map g).toMatrix *ᵥ P) j)) :
    (C • W).projModelPoint g hP hi ≫ (W.projModelVariableChangeIso C).hom =
      W.projModelPoint g ((Projective.equation_variableChange (W.map g) (C.map g) P).mp
        (by simpa only [map_variableChange] using hP)) hj := by
  set hQ := (Projective.equation_variableChange (W.map g) (C.map g) P).mp
    (by simpa only [map_variableChange] using hP)
  -- evaluating at `P` after the change of variables is evaluating at `(C.map g).toMatrix *ᵥ P`
  have hF : ((C • W).toProjective.evalHom g hP).comp (variableChangeGradedHom W C).toRingHom =
      W.toProjective.evalHom g hQ := by
    refine Projective.eq_evalHom _ _ _ (RingHom.ext fun r ↦ ?_) (funext fun k ↦ ?_)
    · simpa [variableChangeGradedHom_apply] using
        RingHom.congr_fun ((C • W).toProjective.evalHom_comp_algebraMap g hP) r
    · simp [variableChangeGradedHom_apply, Projective.coord, mulVec, dotProduct]
  -- the image of `Xⱼ` under the change of variables takes the unit value `Qⱼ` at `P`
  have hFj : IsUnit ((C • W).toProjective.evalHom g hP
      (variableChangeGradedHom W C (W.toProjective.coord j))) := by
    rwa [← GradedRingHom.coe_toRingHom, ← RingHom.comp_apply, hF, Projective.evalHom_mk, eval₂_X]
  -- read the point on the chart cut out by the image of `Xⱼ`, which the isomorphism carries
  -- into `D₊(Xⱼ)`
  rw [projModelPoint, projModelPoint, projModelVariableChangeIso, Proj.mapIso_hom,
    Projective.awayEvalHom_def, Projective.awayEvalHom_def, Proj.SpecMap_awayLift_awayι_eq _ _
      one_pos (GradedFunLike.map_mem _ (W.toProjective.coord_mem_grading j)) one_pos _ hFj,
    Category.assoc, Proj.awayι_comp_map _ _ one_pos _ (W.toProjective.coord_mem_grading j)]
  simp [← Spec.map_comp_assoc, ← CommRingCat.ofHom_comp, hF]

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

-- Over a local ring `S`, a morphism `Spec S ⟶ projModel W` factors through one of the standard
-- charts `D₊(Xᵢ)`: the chart containing the image of the closed point contains the whole image.
private theorem exists_spec_map_comp_awayι {S : Type u} [CommRing S] [IsLocalRing S]
    (x : Spec (CommRingCat.of S) ⟶ W.projModel) :
    ∃ (i : Fin 3) (α : CommRingCat.of (Away W.toProjective.grading (W.toProjective.coord i)) ⟶
      CommRingCat.of S), Spec.map α ≫ Proj.awayι W.toProjective.grading (W.toProjective.coord i)
        (W.toProjective.coord_mem_grading i) one_pos = x := by
  let 𝒰 := Proj.affineOpenCoverOfIrrelevantLESpan _ _ W.toProjective.coord_mem_grading
    (fun _ ↦ one_pos) W.toProjective.irrelevant_le_span_range_coord
  have h : Set.range x ⊆ Set.range (𝒰.f (𝒰.idx (x (closedPoint S)))) := by
    have htop := Scheme.preimage_eq_top_of_closedPoint_mem x
      (U := (𝒰.f (𝒰.idx (x (closedPoint S)))).opensRange) (𝒰.covers _)
    rintro _ ⟨y, rfl⟩
    exact (htop.ge trivial : y ∈ x ⁻¹ᵁ _)
  obtain ⟨α, hα⟩ := Spec.map_surjective (IsOpenImmersion.lift _ x h)
  exact ⟨𝒰.idx (x (closedPoint S)), α, hα ▸ IsOpenImmersion.lift_fac _ _ h⟩

/-- A point `Spec α` of the standard affine chart `D₊(Xᵢ)` of the projective model is the point
with homogeneous coordinates the image under `α` of the universal point `chartPoint i` of the chart
ring, along the composite `R → ChartRing i → A`. The case `α = 𝟙` gives
`chartι_eq_projModelPoint`. -/
theorem SpecMap_chartι {A : CommRingCat.{u}} {i : Fin 3}
    (α : CommRingCat.of (W.toProjective.ChartRing i) ⟶ A) :
    Spec.map α ≫ W.chartι i =
      W.projModelPoint (α.hom.comp (algebraMap R _)) (P := α.hom ∘ W.toProjective.chartPoint i)
        (by simpa only [Projective.baseChange, WeierstrassCurve.baseChange,
          WeierstrassCurve.map_map] using (W.toProjective.equation_chartPoint i).map α.hom) (i := i)
        (by simpa only [Function.comp_apply, W.toProjective.chartPoint_self i, map_one] using
          isUnit_one) := by
  rw [W.chartι_eq_projModelPoint i]
  exact SpecMap_projModelPoint α.hom _

/-- A point of the projective Weierstrass model with values in a local ring is given by
homogeneous coordinates: for a local ring `S`, a ring homomorphism `g : R →+* S` and
`x : Spec S ⟶ projModel W` over `Spec g`, `x` is the point with homogeneous coordinates `P` for
some solution `P` of the projective Weierstrass equation of `W.map g` with a unit coordinate.
Such a `P` is unique up to a unit (`projModelPoint_eq_projModelPoint_iff`). For a point with no
`g` given, see `exists_ringHom_eq_projModelPoint`. For a ring `S` that is not local, a point all
of whose values lie on the chart `D₊(Xᵢ)` is described by
`exists_eq_projModelPoint_of_forall_mem_basicOpen`, and a point `Spec α` of that chart by
`SpecMap_chartι`. -/
theorem exists_eq_projModelPoint {S : Type u} [CommRing S] [IsLocalRing S] {g : R →+* S}
    {x : Spec (.of S) ⟶ W.projModel} (hx : x ≫ W.projModelOver = Spec.map (CommRingCat.ofHom g)) :
    ∃ (P : Fin 3 → S) (hP : (W.toProjective.map g).Equation P) (i : Fin 3) (hi : IsUnit (P i)),
      x = W.projModelPoint g hP hi := by
  obtain ⟨i, α, rfl⟩ := W.exists_spec_map_comp_awayι x
  -- through the isomorphism `awayEquivChartRing`, `α` is a homomorphism `β` out of the chart ring
  obtain ⟨β, rfl⟩ : ∃ β : CommRingCat.of (W.toProjective.ChartRing i) ⟶ CommRingCat.of S,
      α = CommRingCat.ofHom (W.toProjective.awayEquivChartRing i : _ →+* _) ≫ β :=
    ⟨_, ((W.toProjective.awayEquivChartRing i).toCommRingCatIso.hom_inv_id_assoc α).symm⟩
  -- so the point is `Spec β` followed by the chart `D₊(Xᵢ)`
  rw [Spec.map_comp_assoc, ← chartι_def, W.SpecMap_chartι] at hx ⊢
  -- the point lies over `Spec g` and over `Spec` of the composite `R → ChartRing i → S`
  obtain rfl : β.hom.comp (algebraMap R _) = g := by
    simpa only [projModelPoint_projModelOver, Spec.map_inj, CommRingCat.hom_ext_iff,
      CommRingCat.hom_ofHom] using hx
  exact ⟨_, _, i, _, rfl⟩

/-- A point of the projective Weierstrass model with values in a local ring is given by
homogeneous coordinates, along some ring homomorphism: for a local ring `S` and
`x : Spec S ⟶ projModel W`, there are a ring homomorphism `g : R →+* S` and a solution `P` of the
projective Weierstrass equation of `W.map g` with a unit coordinate such that `x` is the point
with homogeneous coordinates `P`. Such a `g` is unique, and `P` is unique up to a unit
(`projModelPoint_eq_projModelPoint_iff`). For a point lying over a given `g`, see
`exists_eq_projModelPoint`. -/
theorem exists_ringHom_eq_projModelPoint {S : Type u} [CommRing S] [IsLocalRing S]
    (x : Spec (.of S) ⟶ W.projModel) :
    ∃ (g : R →+* S) (P : Fin 3 → S) (hP : (W.toProjective.map g).Equation P) (i : Fin 3)
      (hi : IsUnit (P i)), x = W.projModelPoint g hP hi := by
  -- `x` lies over `Spec φ` for a ring homomorphism `φ`
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (x ≫ W.projModelOver)
  exact ⟨φ.hom, W.exists_eq_projModelPoint (by rw [← hφ, CommRingCat.ofHom_hom])⟩

/-- A point of the projective Weierstrass model with values in a commutative ring `S`, lying over
`Spec g` for a ring homomorphism `g : R →+* S`, all of whose values lie on the standard affine
chart `D₊(Xᵢ)`, is the point with homogeneous coordinates `Q`, along `g`, for some solution `Q` of
the projective Weierstrass equation of `W.map g` whose `i`-th coordinate is `1`. Such a `Q` is
unique (`projModelPoint_eq_projModelPoint_iff`). For a local ring `S`, the hypothesis holds for
some `i`; see `exists_eq_projModelPoint`. -/
theorem exists_eq_projModelPoint_of_forall_mem_basicOpen {S : Type u} [CommRing S] {g : R →+* S}
    {x : Spec (.of S) ⟶ W.projModel} (hx : x ≫ W.projModelOver = Spec.map (CommRingCat.ofHom g))
    {i : Fin 3} (hxi : ∀ s, x s ∈ Proj.basicOpen W.toProjective.grading (W.toProjective.coord i)) :
    ∃ (Q : Fin 3 → S) (hQ : (W.toProjective.map g).Equation Q) (hQi : Q i = 1),
      x = W.projModelPoint g hQ (i := i) (by simpa only [hQi] using isUnit_one) := by
  -- `x` is `Spec α` followed by the chart, for a homomorphism `α` out of the chart ring
  have hrange : Set.range x ⊆ Set.range (W.chartι i) := by
    simpa only [← Scheme.Hom.coe_opensRange, W.opensRange_chartι i, Set.range_subset_iff,
      SetLike.mem_coe] using hxi
  obtain ⟨α, hα⟩ := Spec.map_surjective (IsOpenImmersion.lift (W.chartι i) x hrange)
  have hfac := IsOpenImmersion.lift_fac (W.chartι i) x hrange
  rw [← hα, W.SpecMap_chartι] at hfac
  -- it lies over `Spec g` and over `Spec` of the composite `R → ChartRing i → S`
  obtain rfl : α.hom.comp (algebraMap R _) = g := by
    simpa only [projModelPoint_projModelOver, hx, Spec.map_inj, CommRingCat.hom_ext_iff,
      CommRingCat.hom_ofHom] using congrArg (· ≫ W.projModelOver) hfac
  exact ⟨_, _, by rw [Function.comp_apply, Projective.chartPoint_self, map_one], hfac.symm⟩

/-- The zero section `[0 : 1 : 0]` of the projective model, restricted along `Spec g` for a ring
homomorphism `g : R →+* S`, is the point with homogeneous coordinates `(0, 1, 0)`, along `g`. The
case `g = RingHom.id R` describes the zero section itself. -/
@[reassoc (attr := simp)]
theorem SpecMap_projModelZero {S : Type u} [CommRing S] (g : R →+* S) :
    Spec.map (CommRingCat.ofHom g) ≫ W.projModelZero =
      W.projModelPoint g (W.toProjective.map g).equation_zero (i := 1)
        (by simpa only [Matrix.cons_val_one, Matrix.cons_val_zero] using isUnit_one) := by
  -- evaluating at `[0 : 1 : 0]` and then applying `g` is evaluating at `(0, 1, 0)` along `g`
  have h : g.comp W.toProjective.evalZero.toRingHom =
      W.toProjective.evalHom g (W.toProjective.map g).equation_zero := by
    refine RingHom.ext fun a ↦ ?_
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective a
    rw [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Projective.evalZero_mk,
      Projective.evalHom_mk, eval₂_comp, Projective.comp_fin3, map_zero, map_one]
  -- both sides are `Spec` of a homomorphism `A_(Y) → S` induced by evaluation at `[0 : 1 : 0]`,
  -- followed by the inclusion of `D₊(Y)`
  simp only [projModelZero, projModelPoint, ← Spec.map_comp_assoc, ← CommRingCat.ofHom_comp,
    awayYEvalZero, Projective.awayEvalHom_def, RingHom.comp_homogeneousLocalizationAwayLift, h]

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
      ⟨hQ, hi.isUnimodular_pi⟩⟩,
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
  -- the zero section is the point with homogeneous coordinates `(0, 1, 0)`
  rw [Equiv.ofBijective_apply, sectionOfClass_mk,
    W.repPoint_eq W.toProjective.equation_zero (i := 1) (by simp),
    ← W.SpecMap_projModelZero (RingHom.id R), CommRingCat.ofHom_id, Spec.map_id, Category.id_comp]

/-- The section `projModelPoint W (RingHom.id R) hP hi` with homogeneous coordinates `P`, a
solution of the projective Weierstrass equation with a unit coordinate `Pᵢ`, corresponds to the
class of `P`. -/
@[simp]
theorem projModelPointsEquivUnimodular_projModelPoint {P : Fin 3 → R}
    (hP : (W.toProjective.map (RingHom.id R)).Equation P) {i : Fin 3} (hi : IsUnit (P i)) :
    (W.projModelPointsEquivUnimodular ⟨W.projModelPoint (RingHom.id R) hP hi, by simp⟩ :
      Projective.PointClass R) = ⟦P⟧ := by
  have hE : W.toProjective.Equation P := by simpa only [WeierstrassCurve.map_id] using hP
  have hU : W.toProjective.UnimodularLift ⟦P⟧ := (Projective.unimodularLift_iff P).mpr
    ⟨hE, hi.isUnimodular_pi⟩
  -- the section attached to the class of `P` is the point with homogeneous coordinates `P`
  refine congrArg Subtype.val ((Equiv.symm_apply_eq _).mpr (Subtype.ext ?_) :
    W.projModelPointsEquivUnimodular ⟨_, _⟩ = ⟨⟦P⟧, hU⟩)
  rw [Equiv.ofBijective_apply, sectionOfClass_mk, W.repPoint_eq hE hi]

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

/-- For a solution `P` of the projective Weierstrass equation with a unit coordinate `Pᵢ`, the
section `projModelPoint W (RingHom.id K) hP hi` with homogeneous coordinates `P` corresponds to the
point `WeierstrassCurve.Projective.Point.toAffine W P` of `W`: the point at infinity if `P₂ = 0`,
and the affine point `(P₀ / P₂, P₁ / P₂)` otherwise. Unlike `projModelPointsEquiv_symm_some`, which
describes the section of an affine point through the chart `D₊(Z)`, it applies to a section read
through any chart `D₊(Xᵢ)`. -/
@[simp]
theorem projModelPointsEquiv_projModelPoint {P : Fin 3 → K}
    (hP : (W.toProjective.map (RingHom.id K)).Equation P) {i : Fin 3} (hi : IsUnit (P i)) :
    W.projModelPointsEquiv ⟨W.projModelPoint (RingHom.id K) hP hi, by simp⟩ =
      Projective.Point.toAffine W.toProjective P := by
  classical
  -- the section corresponds to the unimodular class of `P`, which is the nonsingular point `⟦P⟧`
  have hNS : W.toProjective.NonsingularLift ⟦P⟧ :=
    Projective.unimodularLift_iff_nonsingularLift.mp <| (Projective.unimodularLift_iff P).mpr
      ⟨by simpa only [WeierstrassCurve.map_id] using hP,
        hi.isUnimodular_pi⟩
  have h : (Projective.Point.equivUnimodularLift W.toProjective).symm
      (W.projModelPointsEquivUnimodular ⟨W.projModelPoint (RingHom.id K) hP hi, by simp⟩) =
        ⟨hNS⟩ :=
    Projective.Point.ext <| by
      rw [Projective.Point.equivUnimodularLift_symm_point,
        projModelPointsEquivUnimodular_projModelPoint]
  rw [projModelPointsEquiv, Equiv.trans_apply, Equiv.trans_apply, h, AddEquiv.toEquiv_eq_coe,
    AddEquiv.coe_toEquiv, Projective.Point.toAffineAddEquiv_apply, Projective.Point.toAffineLift_eq]

end Field

end WeierstrassCurve

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.Points

/-!
# The zero section of the projective Weierstrass model and the affine chart `D₊(Z)`

Let `W` be a Weierstrass curve over a commutative ring `R`. The image of the zero section
`[0 : 1 : 0]` of the projective Weierstrass model `projModel W` is the complement of the standard
affine chart `D₊(Z)`.

It follows that, under a morphism `f : projModel W ⟶ projModel W'` between the projective models
of two Weierstrass curves over `R` that carries the zero section to the zero section, the preimage
of the chart `D₊(Z)` of `W'` is contained in the chart `D₊(Z)` of `W`, and is equal to it when `f`
is injective on points, for instance an isomorphism. If `f` is injective on points and moreover a
morphism over `Spec R`, it sends a point with homogeneous coordinates `[X : Y : Z]`, `Z` a unit,
with values in any commutative ring, to a point with homogeneous coordinates `[X' : Y' : 1]`.

The zero section has homogeneous coordinates `(0, 1, 0)`, so it misses `D₊(Z)`. Conversely, the
residue-field point at a point `p` off `D₊(Z)` has homogeneous coordinates `P` with `P₂ = 0`; the
projective Weierstrass equation then reads `P₀³ = 0`, so `P` is a unit multiple of `(0, 1, 0)` and
the residue-field point factors through the zero section.

## Main results

* `WeierstrassCurve.projModelZero_mem_basicOpen_iff`: the zero section lies on the chart
  `D₊(Xⱼ)` exactly when `j = 1`.
* `WeierstrassCurve.mem_range_projModelZero_iff` and `WeierstrassCurve.range_projModelZero`: the
  image of the zero section is the complement of the chart `D₊(Z)`.
* `WeierstrassCurve.isClosedImmersion_projModelZero`: the zero section is a closed immersion.
* `WeierstrassCurve.preimage_basicOpen_coord_two_le`: under a morphism of projective Weierstrass
  models that carries the zero section to the zero section, the preimage of the chart `D₊(Z)` is
  contained in the chart `D₊(Z)`.
* `WeierstrassCurve.preimage_basicOpen_coord_two`: if the morphism is injective on points, the
  preimage of the chart `D₊(Z)` is the chart `D₊(Z)`.
* `WeierstrassCurve.exists_projModelPoint_comp_eq_projModelPoint`: if it is moreover a morphism
  over the base, it sends a point with homogeneous coordinates `P`, `P₂` a unit, to a point with
  homogeneous coordinates `Q`, `Q₂ = 1`.

## References

* [J. H. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.1.

## Provenance

Adapted from AINTLIB (`github.com/CBirkbeck/AINTLIB`, Apache-2.0) at commit
`c3415f32a313e19ace43e05479aeaa0d56ca287a`, directory
`projects/ModularCurves/ModularCurves/EllipticCurve/`. `mem_range_projModelZero_iff` combines
`mem_range_zero_of_not_mem_zChart` and `not_mem_zChart_of_mem_range_zero` (file
`ModelVariableChange.lean`), which rest on `specPoint_eq_zero_of_not_inZ` and
`projModelZero_not_preimage_zChart` (file `WeierstrassModel.lean`); `range_projModelZero`
corresponds to `sectionAway_projModelZero_eq_zChart` (file `PoleSheafAwayModel.lean`), which states
that the open complement of the zero section is the chart `D₊(Z)`. The source shows that a point
with values in a field which does not factor through the chart `D₊(Z)` is the zero section by a
case analysis on the chart through which it factors, solving the dehomogenised equation there
(`eq_infPoint_of_not_inZ`), and that the zero section misses `D₊(Z)` by computing the preimage of
`D₊(Z)` under it. Here both directions are read off the homogeneous coordinates of a point
(`projModelPoint_mem_basicOpen_iff`), with Mathlib's
`WeierstrassCurve.Projective.X_eq_zero_of_Z_eq_zero` for the equation;
`projModelZero_mem_basicOpen_iff` states the first for all three charts.

`preimage_basicOpen_coord_two` corresponds to `pointedIso_preimage_zChart` (file
`ModelVariableChange.lean`) and, for the complement of a section of a separated morphism, to
`preimage_sectionAway_eq_of_pointedIso` (file `PoleSheafAwayModel.lean`), both stated there for an
isomorphism; here the inclusion `preimage_basicOpen_coord_two_le` is stated for every morphism
carrying the zero section to the zero section, and the equality for the ones that are injective
on points.

`exists_projModelPoint_comp_eq_projModelPoint` corresponds to `ZChart.mem_specPointPointedIso`
(file `projects/ModularCurves/ModularCurves/ModularCurve/YOneAtlasClassify.lean`): under an
isomorphism over the base that carries the zero section to the zero section, the image of a point
with values in a commutative algebra over the base ring that factors through the chart `D₊(Z)`
factors through the chart `D₊(Z)`. The source deduces this from the square
`ZChart.PointedIso.spec_map_awayι` (same file), which presents the isomorphism on the chart as
`Spec` of its action on the sections of the structure sheaf over `D₊(Z)` (`pointedIsoΓ`, file
`ModelVariableChange.lean`). Here the values of the image point lie on the chart by
`preimage_basicOpen_coord_two`, for a morphism that is injective on points and a point along any
ring homomorphism `g : R →+* S`, and the statement is in homogeneous coordinates
(`exists_eq_projModelPoint_of_forall_mem_basicOpen`).
-/

public section

open CategoryTheory AlgebraicGeometry

universe u

namespace WeierstrassCurve

variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

-- A point of the projective model with values in a field, one of whose values is off the chart
-- `D₊(Z)`, is the zero section along a ring homomorphism.
private theorem exists_eq_SpecMap_comp_projModelZero {K : Type u} [Field K]
    (x : Spec (.of K) ⟶ W.projModel) {s : Spec (.of K)}
    (hs : x s ∉ Proj.basicOpen W.toProjective.grading (W.toProjective.coord 2)) :
    ∃ g : R →+* K, x = Spec.map (CommRingCat.ofHom g) ≫ W.projModelZero := by
  obtain ⟨g, P, hP, i, hi, rfl⟩ := W.exists_ringHom_eq_projModelPoint x
  -- the third homogeneous coordinate lies in a prime ideal of the field `K`, so it vanishes
  have hPz : P 2 = 0 := by
    rwa [projModelPoint_mem_basicOpen_iff, not_not,
      Ideal.eq_bot_of_prime s.asIdeal (h := s.isPrime), Ideal.mem_bot] at hs
  -- by the projective Weierstrass equation, so does the first: `P` is `P 1` times `(0, 1, 0)`
  have hPx : P 0 = 0 := Projective.X_eq_zero_of_Z_eq_zero hP hPz
  -- and `P 1` is nonzero, since one coordinate of `P` is a unit
  have hPy : P 1 ≠ 0 := fun h ↦ hi.ne_zero (by fin_cases i <;> assumption)
  refine ⟨g, ?_⟩
  rw [W.SpecMap_projModelZero g, projModelPoint_eq_projModelPoint_iff]
  exact ⟨rfl, Units.mk0 _ hPy, funext fun k ↦ by fin_cases k <;> simp [hPx, hPz]⟩

/-- The zero section `[0 : 1 : 0]` of the projective Weierstrass model lies on the standard chart
`D₊(Xⱼ)` exactly when `j = 1`: it lies on `D₊(Y)` and misses `D₊(X)` and `D₊(Z)`. -/
theorem projModelZero_mem_basicOpen_iff (q : Spec (.of R)) (j : Fin 3) :
    W.projModelZero q ∈ Proj.basicOpen W.toProjective.grading (W.toProjective.coord j) ↔
      j = 1 := by
  -- the zero section has homogeneous coordinates `(0, 1, 0)`; `0` lies in every prime, `1` in none
  rw [W.projModelZero_eq_projModelPoint, projModelPoint_mem_basicOpen_iff]
  fin_cases j <;> simp [q.isPrime.one_notMem]

/-- A point of the projective Weierstrass model lies on the zero section `[0 : 1 : 0]` exactly
when it does not lie on the standard affine chart `D₊(Z)`. -/
theorem mem_range_projModelZero_iff (p : W.projModel) :
    p ∈ Set.range W.projModelZero ↔
      p ∉ Proj.basicOpen W.toProjective.grading (W.toProjective.coord 2) := by
  refine ⟨?_, fun hp ↦ ?_⟩
  · -- the zero section lies on the chart `D₊(Y)` only
    rintro ⟨q, rfl⟩
    simp only [W.projModelZero_mem_basicOpen_iff, Fin.reduceEq, not_false_eq_true]
  · -- the residue-field point at `p` is the zero section along a ring homomorphism `g`
    obtain ⟨g, hg⟩ := W.exists_eq_SpecMap_comp_projModelZero (K := W.projModel.residueField p)
      (W.projModel.fromSpecResidueField p) (s := default)
      (by rwa [Scheme.fromSpecResidueField_apply])
    refine ⟨Spec.map (CommRingCat.ofHom g) default, ?_⟩
    rw [← Scheme.Hom.comp_apply, ← hg, Scheme.fromSpecResidueField_apply]

/-- The image of the zero section `[0 : 1 : 0]` of the projective Weierstrass model is the
complement of the standard affine chart `D₊(Z)`. -/
@[simp]
theorem range_projModelZero :
    Set.range W.projModelZero =
      (Proj.basicOpen W.toProjective.grading (W.toProjective.coord 2) : Set W.projModel)ᶜ :=
  Set.ext W.mem_range_projModelZero_iff

/-- The zero section of the projective Weierstrass model is a closed immersion, as is every
section of a separated morphism. -/
instance isClosedImmersion_projModelZero : IsClosedImmersion W.projModelZero := by
  have : IsClosedImmersion (W.projModelZero ≫ W.projModelOver) := by
    rw [W.projModelZero_projModelOver]
    infer_instance
  exact IsClosedImmersion.of_comp W.projModelZero W.projModelOver

variable {W} {W' : WeierstrassCurve R}

/-- Under a morphism `f : projModel W ⟶ projModel W'` of projective Weierstrass models that
carries the zero section to the zero section, the preimage of the standard affine chart `D₊(Z)` of
`W'` is contained in the standard affine chart `D₊(Z)` of `W`. -/
theorem preimage_basicOpen_coord_two_le {f : W.projModel ⟶ W'.projModel}
    (hf : W.projModelZero ≫ f = W'.projModelZero) :
    f ⁻¹ᵁ Proj.basicOpen W'.toProjective.grading (W'.toProjective.coord 2) ≤
      Proj.basicOpen W.toProjective.grading (W.toProjective.coord 2) := by
  intro p
  -- contrapositive: if `p` lies on the zero section of `W`, then `f p` lies on that of `W'`
  contrapose
  rw [← mem_range_projModelZero_iff, Scheme.Hom.mem_preimage, ← mem_range_projModelZero_iff]
  rintro ⟨q, rfl⟩
  exact ⟨q, by rw [← hf, Scheme.Hom.comp_apply]⟩

/-- Under a morphism `f : projModel W ⟶ projModel W'` of projective Weierstrass models that
carries the zero section to the zero section and is injective on points, for instance an
isomorphism, the preimage of the standard affine chart `D₊(Z)` of `W'` is the standard affine
chart `D₊(Z)` of `W`. -/
theorem preimage_basicOpen_coord_two {f : W.projModel ⟶ W'.projModel}
    (hf : W.projModelZero ≫ f = W'.projModelZero) (hinj : Function.Injective f) :
    f ⁻¹ᵁ Proj.basicOpen W'.toProjective.grading (W'.toProjective.coord 2) =
      Proj.basicOpen W.toProjective.grading (W.toProjective.coord 2) := by
  refine le_antisymm (preimage_basicOpen_coord_two_le hf) fun p ↦ ?_
  -- contrapositive: if `f p` lies on the zero section of `W'`, then `p` lies on that of `W`
  contrapose
  rw [Scheme.Hom.mem_preimage, ← mem_range_projModelZero_iff, ← mem_range_projModelZero_iff]
  rintro ⟨q, hq⟩
  exact ⟨q, hinj <| by rwa [← hf, Scheme.Hom.comp_apply] at hq⟩

/-- Let `f : projModel W ⟶ projModel W'` be a morphism of projective Weierstrass models over
`Spec R` that carries the zero section to the zero section and is injective on points, for
instance an isomorphism. For a ring homomorphism `g : R →+* S` and a solution `P` of the projective
Weierstrass equation of `W.map g` whose third coordinate is a unit, `f` sends the point with
homogeneous coordinates `P` to the point with homogeneous coordinates `Q`, along `g`, for some
solution `Q` of the projective Weierstrass equation of `W'.map g` whose third coordinate is `1`.
Such a `Q` is unique (`projModelPoint_eq_projModelPoint_iff_of_apply_eq`). -/
theorem exists_projModelPoint_comp_eq_projModelPoint {f : W.projModel ⟶ W'.projModel}
    (hf : W.projModelZero ≫ f = W'.projModelZero) (hinj : Function.Injective f)
    (hfo : f ≫ W'.projModelOver = W.projModelOver) {S : Type u} [CommRing S] {g : R →+* S}
    {P : Fin 3 → S} (hP : (W.toProjective.map g).Equation P) (h2 : IsUnit (P 2)) :
    ∃ (Q : Fin 3 → S) (hQ : (W'.toProjective.map g).Equation Q) (hQ2 : Q 2 = 1),
      W.projModelPoint g hP h2 ≫ f =
        W'.projModelPoint g hQ (i := 2) (by simpa only [hQ2] using isUnit_one) := by
  refine W'.exists_eq_projModelPoint_of_forall_mem_basicOpen
    (by rw [Category.assoc, hfo, projModelPoint_projModelOver]) fun x ↦ ?_
  -- the composite sends `x` into the chart `D₊(Z)` of `W'`, as the unit `P 2` is not in `x`
  rw [Scheme.Hom.comp_apply, ← Scheme.Hom.mem_preimage, preimage_basicOpen_coord_two hf hinj,
    projModelPoint_mem_basicOpen_iff]
  exact fun hx ↦ x.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ hx h2)

end WeierstrassCurve

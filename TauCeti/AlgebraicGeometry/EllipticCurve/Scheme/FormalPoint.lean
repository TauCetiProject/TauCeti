/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.FormalGroup.WExpansion
public import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.Points
import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.ZeroSection
import TauCeti.RingTheory.PowerSeries.SubstInv
import TauCeti.RingTheory.Spectrum.Prime.PowerSeries

/-!
# The formal point of the projective Weierstrass model along the zero section

Let `W` be a Weierstrass curve over a commutative ring `R`. On the standard affine chart `D₊(Y)`
of the projective Weierstrass model `projModel W`, the functions `z = -X / Y` and `w = -Z / Y`
vanish on the zero section `[0 : 1 : 0]`, and the Weierstrass equation reads

`w = z ^ 3 + a₁ z w + a₂ z ^ 2 w + a₃ w ^ 2 + a₄ z w ^ 2 + a₆ w ^ 3`.

It has a unique solution `w(z)` in `R⟦z⟧` with zero constant coefficient, the `w`-expansion
`formalW W`, so that `z` is a formal parameter of `projModel W` along the zero section. This file
defines the corresponding point `[z : -1 : w(z)]` of `projModel W` with values in `R⟦z⟧`, the
**formal point**, and shows that every point of `projModel W` with values in `R⟦z⟧`, lying over
`Spec R`, that restricts to the zero section at `z = 0` is the formal point reparametrised by a
substitution `z ↦ s(z)`, that is, the point `[s : -1 : w(s)]` for a power series `s` with zero
constant coefficient. In the statements, `z` is the variable `X` of `R⟦X⟧`.

Let `x` be such a point. The zero section lies on the chart `D₊(Y)`, so the preimage of `D₊(Y)`
under `x` is an open subset of `Spec R⟦z⟧` containing the locus `z = 0`. As `z` lies in the
Jacobson radical of `R⟦z⟧`, every nonempty closed subset of `Spec R⟦z⟧` meets the locus `z = 0`, so
this open subset is all of `Spec R⟦z⟧`, although `R⟦z⟧` need not be a local ring. Hence `x` factors
through `D₊(Y)` and is the point `[s : -1 : t]` for power series `s` and `t`, which have zero
constant coefficient because `x` restricts to `[0 : 1 : 0]` at `z = 0`. The projective Weierstrass
equation at `[s : -1 : t]` is the `w`-equation at the parameter `s`, whose only solution with zero
constant coefficient is `t = w(s)`.

It follows that a morphism `f : projModel W ⟶ projModel W'` over `Spec R` that carries the zero
section to the zero section sends the formal point of `W` to the formal point of `W'`
reparametrised by a substitution `z ↦ s(z)`: the image is a point of `projModel W'` with values in
`R⟦z⟧` that restricts to the zero section at `z = 0`. If `f` is an isomorphism, the power series
`s` of `f` and `s'` of its inverse satisfy `s'(s) = z`, so `s` is `z` times a unit of `R⟦z⟧`.

When `R` is complete for the adic topology of an ideal `I` and `t` lies in `I`, the point of `W`
over a field containing `R` that `WeierstrassCurve.formalPoint` (file
`FormalGroup/Point/Basic.lean`) attaches to `t`, namely `(t / w(t), -1 / w(t))` for `t ≠ 0` and the
point at infinity for `t = 0`, has homogeneous coordinates `[t : -1 : w(t)]`: the coordinates of
the formal point evaluated at `z = t`. The two constructions are not compared in this file.

## Main definitions

* `WeierstrassCurve.projModelFormalPoint W`: the formal point `[X : -1 : w(X)]` of `projModel W`,
  with values in `R⟦X⟧`.

## Main results

* `WeierstrassCurve.Projective.equation_neg_one_iff_wEquation`: the projective Weierstrass
  equation at `[q : -1 : v]` is the `w`-equation at the parameter `q`.
* `WeierstrassCurve.projModelFormalPoint_projModelOver`: the formal point lies over
  `Spec R⟦X⟧ ⟶ Spec R`.
* `WeierstrassCurve.SpecMap_constantCoeff_projModelFormalPoint`: the formal point restricts to the
  zero section at `X = 0`.
* `WeierstrassCurve.SpecMap_substAlgHom_projModelFormalPoint`: the formal point reparametrised by
  `X ↦ s` is the point `[s : -1 : w(s)]`.
* `WeierstrassCurve.SpecMap_constantCoeff_comp_eq_projModelZero_iff`: a point of `projModel W`
  with values in `R⟦X⟧`, lying over `Spec R`, restricts to the zero section at `X = 0` exactly
  when it is the point `[s : -1 : w(s)]` for a power series `s` with zero constant coefficient.
* `WeierstrassCurve.exists_projModelFormalPoint_comp_eq`: a morphism of projective Weierstrass
  models over `Spec R` that carries the zero section to the zero section sends the formal point
  to the point `[s : -1 : w'(s)]`, for a power series `s` with zero constant coefficient.
* `WeierstrassCurve.exists_unit_projModelFormalPoint_comp_eq`: for an isomorphism, `s` is `X`
  times a unit of `R⟦X⟧`.

## References

* [J. H. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], IV.1.

## Provenance

Not adapted from AINTLIB (`github.com/CBirkbeck/AINTLIB`, Apache-2.0) at commit
`c3415f32a313e19ace43e05479aeaa0d56ca287a`, directory
`projects/ModularCurves/ModularCurves/EllipticCurve/`, which has no formal point and does not use
the `w`-expansion. The source proves the corresponding step of the classification of the
isomorphisms of projective Weierstrass models that preserve the zero section by transporting a
pole-order filtration through charts (`pointedIsoCoordEquiv_filtration`, file
`ModelVariableChange.lean`).
-/

public section

open CategoryTheory AlgebraicGeometry PowerSeries

universe u

namespace WeierstrassCurve

variable {R : Type u} [CommRing R]

/-- For `q` and `v` in a commutative `R`-algebra, the projective Weierstrass equation at
`[q : -1 : v]` is equivalent to the `w`-equation
`v = q ^ 3 + a₁ q v + a₂ q ^ 2 v + a₃ v ^ 2 + a₄ q v ^ 2 + a₆ v ^ 3` (`wEquationRHS`).
`wEquation_of_equation` is the implication from left to right for a solution `(x, y)` of the
affine Weierstrass equation over a field with `y ≠ 0`, where
`[x : y : 1] = [-x / y : -1 : -1 / y]`. -/
theorem Projective.equation_neg_one_iff_wEquation (W' : Projective R) {S : Type*} [CommRing S]
    [Algebra R S] (q v : S) :
    (W'.map (algebraMap R S)).Equation ![q, -1, v] ↔ v = wEquationRHS W' q v := by
  rw [Projective.equation_iff, wEquationRHS_def]
  simp only [Matrix.cons_val, map_a₁, map_a₂, map_a₃, map_a₄, map_a₆]
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩ <;> linear_combination h

variable (W : WeierstrassCurve R)

/-- The **formal point** `[X : -1 : w(X)]` of the projective Weierstrass model along the zero
section: the point of `projModel W` with values in the power series ring `R⟦X⟧` whose homogeneous
coordinates are `(X, -1, w(X))`, where `w` is the `w`-expansion `formalW W`. It restricts to the
zero section at `X = 0` (`SpecMap_constantCoeff_projModelFormalPoint`). Rewrite with
`projModelFormalPoint_def` rather than unfolding this definition. -/
noncomputable def projModelFormalPoint : Spec (.of R⟦X⟧) ⟶ W.projModel :=
  W.projModelPoint (algebraMap R R⟦X⟧) (P := ![X, -1, W.formalW])
    ((W.toProjective.equation_neg_one_iff_wEquation X W.formalW).mpr W.formalW_wEquation) (i := 1)
    (by simpa only [Matrix.cons_val_one, Matrix.cons_val_zero] using isUnit_neg_one)

/-- The formal point is the point of the projective model with homogeneous coordinates
`(X, -1, w(X))`, along `algebraMap R R⟦X⟧`. -/
theorem projModelFormalPoint_def : W.projModelFormalPoint =
    W.projModelPoint (algebraMap R R⟦X⟧) (P := ![X, -1, W.formalW])
      ((W.toProjective.equation_neg_one_iff_wEquation X W.formalW).mpr W.formalW_wEquation) (i := 1)
      (by simpa only [Matrix.cons_val_one, Matrix.cons_val_zero] using isUnit_neg_one) := (rfl)

/-- The formal point lies over the morphism `Spec R⟦X⟧ ⟶ Spec R` induced by
`algebraMap R R⟦X⟧`. -/
@[reassoc (attr := simp)]
theorem projModelFormalPoint_projModelOver : W.projModelFormalPoint ≫ W.projModelOver =
    Spec.map (CommRingCat.ofHom (algebraMap R R⟦X⟧)) := by
  rw [projModelFormalPoint_def, projModelPoint_projModelOver]

-- The point `[s : -1 : t]` with values in `R⟦X⟧` restricts to the zero section at `X = 0` exactly
-- when `s` and `t` have zero constant coefficient.
private theorem SpecMap_constantCoeff_projModelPoint_eq_projModelZero_iff {s t : R⟦X⟧}
    (h : (W.toProjective.map (algebraMap R R⟦X⟧)).Equation ![s, -1, t]) :
    Spec.map (CommRingCat.ofHom (constantCoeff (R := R))) ≫
        W.projModelPoint (algebraMap R R⟦X⟧) h (i := 1)
          (by simpa only [Matrix.cons_val_one, Matrix.cons_val_zero] using isUnit_neg_one) =
      W.projModelZero ↔ constantCoeff s = 0 ∧ constantCoeff t = 0 := by
  -- at `X = 0` the point is `[s(0) : -1 : t(0)]`, along the identity of `R`
  rw [SpecMap_projModelPoint, projModelZero_eq_projModelPoint, projModelPoint_eq_projModelPoint_iff,
    and_iff_right (by rw [algebraMap_eq, constantCoeff_comp_C])]
  refine ⟨fun ⟨u, hu⟩ ↦ ⟨?_, ?_⟩, fun ⟨hs, ht⟩ ↦ ⟨-1, funext fun k ↦ ?_⟩⟩
  · simpa only [Function.comp_apply, Matrix.cons_val, Pi.smul_apply, smul_zero] using congrFun hu 0
  · simpa only [Function.comp_apply, Matrix.cons_val, Pi.smul_apply, smul_zero] using congrFun hu 2
  · fin_cases k <;> simp [hs, ht]

/-- The formal point `[X : -1 : w(X)]` restricts to the zero section `[0 : 1 : 0]` at `X = 0`:
its composite with `Spec` of `constantCoeff : R⟦X⟧ →+* R` is the zero section. -/
@[reassoc (attr := simp)]
theorem SpecMap_constantCoeff_projModelFormalPoint :
    Spec.map (CommRingCat.ofHom (constantCoeff (R := R))) ≫ W.projModelFormalPoint =
      W.projModelZero := by
  rw [projModelFormalPoint_def, SpecMap_constantCoeff_projModelPoint_eq_projModelZero_iff]
  exact ⟨constantCoeff_X, W.constantCoeff_formalW⟩

/-- The formal point reparametrised by a substitution `X ↦ s`, for a power series `s` that can be
substituted, is the point of the projective model with homogeneous coordinates `(s, -1, w(s))`. The
reparametrised point is its composite with `Spec` of `substAlgHom hs : R⟦X⟧ →ₐ[R] R⟦X⟧`. -/
@[reassoc]
theorem SpecMap_substAlgHom_projModelFormalPoint {s : R⟦X⟧} (hs : HasSubst s) :
    Spec.map (CommRingCat.ofHom (substAlgHom hs).toRingHom) ≫ W.projModelFormalPoint =
      W.projModelPoint (algebraMap R R⟦X⟧) (P := ![s, -1, W.formalW.subst s])
        ((W.toProjective.equation_neg_one_iff_wEquation s (W.formalW.subst s)).mpr
          (W.subst_formalW_wEquation hs)) (i := 1)
        (by simpa only [Matrix.cons_val_one, Matrix.cons_val_zero] using isUnit_neg_one) := by
  rw [projModelFormalPoint_def, SpecMap_projModelPoint, projModelPoint_eq_projModelPoint_iff]
  refine ⟨by rw [AlgHom.toRingHom_eq_coe, AlgHom.comp_algebraMap], 1, funext fun k ↦ ?_⟩
  fin_cases k <;> simp [substAlgHom_X hs, ← coe_substAlgHom hs]

-- If the formal point is the point `[s' : -1 : t']` reparametrised by `X ↦ s`, then `s'(s) = X`.
private theorem subst_eq_X_of_projModelFormalPoint_eq {s s' t' : R⟦X⟧} (hs : HasSubst s)
    {h : (W.toProjective.map (algebraMap R R⟦X⟧)).Equation ![s', -1, t']}
    (he : W.projModelFormalPoint = Spec.map (CommRingCat.ofHom (substAlgHom hs).toRingHom) ≫
      W.projModelPoint (algebraMap R R⟦X⟧) h (i := 1)
        (by simpa only [Matrix.cons_val_one, Matrix.cons_val_zero] using isUnit_neg_one)) :
    s'.subst s = X := by
  -- the coordinates `(X, -1, w(X))` and `(s'(s), -1, t'(s))` agree at `Y`, so they are equal
  rw [projModelFormalPoint_def, SpecMap_projModelPoint,
    projModelPoint_eq_projModelPoint_iff_of_apply_eq
      (by simp only [Function.comp_apply, Matrix.cons_val, RingHom.map_neg, RingHom.map_one])] at he
  simpa only [Function.comp_apply, Matrix.cons_val, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
    coe_substAlgHom hs] using (congrFun he.2 0).symm

-- An open subset of `Spec R⟦X⟧` contains the image of `Spec R` under `Spec` of
-- `constantCoeff : R⟦X⟧ →+* R`, the locus `X = 0`, exactly when it is all of `Spec R⟦X⟧`.
private theorem range_SpecMap_constantCoeff_subset_iff_eq_top {U : (Spec (.of R⟦X⟧)).Opens} :
    Set.range (Spec.map (CommRingCat.ofHom (constantCoeff (R := R)))) ⊆ U ↔ U = ⊤ :=
  -- the points of `Spec` of a ring are those of its prime spectrum (`Spec_carrier`), on which
  -- `Spec.map` is `PrimeSpectrum.comap` (`Spec.map_apply`), both by definition, so this is
  -- `PowerSeries.range_comap_constantCoeff_subset_iff_eq_top` for the open subset `U`; no lemma
  -- carries an open subset across this identification, and Mathlib crosses it by a term in the
  -- same way, in `Scheme.preimage_eq_top_of_closedPoint_mem`
  range_comap_constantCoeff_subset_iff_eq_top

-- A point of the projective model with values in `R⟦X⟧` that restricts to the zero section at
-- `X = 0` has all its values on the chart `D₊(Y)`.
private theorem mem_basicOpen_coord_one_of_SpecMap_constantCoeff_comp_eq
    {x : Spec (.of R⟦X⟧) ⟶ W.projModel}
    (hx0 : Spec.map (CommRingCat.ofHom (constantCoeff (R := R))) ≫ x = W.projModelZero)
    (p : Spec (.of R⟦X⟧)) :
    x p ∈ Proj.basicOpen W.toProjective.grading (W.toProjective.coord 1) := by
  -- the zero section lies on `D₊(Y)`, so the preimage of `D₊(Y)` is an open subset of
  -- `Spec R⟦X⟧` containing the locus `X = 0`, hence all of `Spec R⟦X⟧`
  have htop : x ⁻¹ᵁ Proj.basicOpen W.toProjective.grading (W.toProjective.coord 1) = ⊤ :=
    range_SpecMap_constantCoeff_subset_iff_eq_top.mp <| Set.range_subset_iff.mpr fun q ↦ by
      rw [SetLike.mem_coe, Scheme.Hom.mem_preimage, ← Scheme.Hom.comp_apply, hx0,
        projModelZero_mem_basicOpen_iff]
  rw [← Scheme.Hom.mem_preimage, htop]
  exact TopologicalSpace.Opens.mem_top p

-- A point of the projective model over `Spec g` all of whose values lie on the chart `D₊(Y)` is
-- the point `[a : -1 : b]` for some `a` and `b`.
private theorem exists_eq_projModelPoint_neg_one {S : Type u} [CommRing S] {g : R →+* S}
    {x : Spec (.of S) ⟶ W.projModel} (hx : x ≫ W.projModelOver = Spec.map (CommRingCat.ofHom g))
    (hx1 : ∀ p, x p ∈ Proj.basicOpen W.toProjective.grading (W.toProjective.coord 1)) :
    ∃ (a b : S) (h : (W.toProjective.map g).Equation ![a, -1, b]),
      x = W.projModelPoint g h (i := 1)
        (by simpa only [Matrix.cons_val_one, Matrix.cons_val_zero] using isUnit_neg_one) := by
  obtain ⟨Q, hQ, hQ1, rfl⟩ := W.exists_eq_projModelPoint_of_forall_mem_basicOpen hx hx1
  -- rescale `Q = [Q₀ : 1 : Q₂]` by the unit `-1`
  have hQs : Q = (-1 : Sˣ) • ![-Q 0, -1, -Q 2] := by
    funext k
    fin_cases k <;> simp [hQ1]
  refine ⟨-Q 0, -Q 2, (Projective.equation_smul _ (-1 : Sˣ).isUnit).mp ?_,
    projModelPoint_eq_projModelPoint_iff.mpr ⟨rfl, -1, hQs⟩⟩
  rwa [← Units.smul_def, ← hQs]

/-- A point `x` of the projective Weierstrass model with values in `R⟦X⟧`, lying over `Spec R`,
restricts to the zero section at `X = 0` exactly when it is the point `[s : -1 : w(s)]` for a
power series `s` with zero constant coefficient, that is, the formal point reparametrised by
`X ↦ s` (`SpecMap_substAlgHom_projModelFormalPoint`). Such an `s` is unique
(`projModelPoint_eq_projModelPoint_iff_of_apply_eq`). -/
theorem SpecMap_constantCoeff_comp_eq_projModelZero_iff {x : Spec (.of R⟦X⟧) ⟶ W.projModel}
    (hx : x ≫ W.projModelOver = Spec.map (CommRingCat.ofHom (algebraMap R R⟦X⟧))) :
    Spec.map (CommRingCat.ofHom (constantCoeff (R := R))) ≫ x = W.projModelZero ↔
      ∃ (s : R⟦X⟧) (_ : constantCoeff s = 0)
        (h : (W.toProjective.map (algebraMap R R⟦X⟧)).Equation ![s, -1, W.formalW.subst s]),
        x = W.projModelPoint (algebraMap R R⟦X⟧) h (i := 1)
          (by simpa only [Matrix.cons_val_one, Matrix.cons_val_zero] using isUnit_neg_one) := by
  refine ⟨fun hx0 ↦ ?_, ?_⟩
  · -- `x` is the point `[s : -1 : t]`, and `s` and `t` have zero constant coefficient
    obtain ⟨s, t, h, rfl⟩ := W.exists_eq_projModelPoint_neg_one hx
      (W.mem_basicOpen_coord_one_of_SpecMap_constantCoeff_comp_eq hx0)
    obtain ⟨hs, ht⟩ := (W.SpecMap_constantCoeff_projModelPoint_eq_projModelZero_iff h).mp hx0
    -- `t` solves the `w`-equation at the parameter `s`, so `t = w(s)`
    obtain rfl := W.eq_subst_formalW_of_wEquation hs ht
      ((W.toProjective.equation_neg_one_iff_wEquation s t).mp h)
    exact ⟨s, hs, h, rfl⟩
  · rintro ⟨s, hs, h, rfl⟩
    exact (W.SpecMap_constantCoeff_projModelPoint_eq_projModelZero_iff h).mpr
      ⟨hs, (constantCoeff_eq _).trans (constantCoeff_subst_eq_zero
        ((constantCoeff_eq s).symm.trans hs) _ W.constantCoeff_formalW)⟩

variable {W} {W' : WeierstrassCurve R}

/-- A morphism `f : projModel W ⟶ projModel W'` of projective Weierstrass models over `Spec R`
that carries the zero section to the zero section sends the formal point `[X : -1 : w(X)]` of `W`
to the point `[s : -1 : w'(s)]` of `W'`, for a power series `s` with zero constant coefficient,
where `w'` is the `w`-expansion of `W'`; that is, to the formal point of `W'` reparametrised by
`X ↦ s` (`SpecMap_substAlgHom_projModelFormalPoint`). If `f` is an isomorphism, `s` is `X` times a
unit of `R⟦X⟧` (`exists_unit_projModelFormalPoint_comp_eq`). -/
theorem exists_projModelFormalPoint_comp_eq {f : W.projModel ⟶ W'.projModel}
    (hf : W.projModelZero ≫ f = W'.projModelZero) (hfo : f ≫ W'.projModelOver = W.projModelOver) :
    ∃ (s : R⟦X⟧) (_ : constantCoeff s = 0)
      (h : (W'.toProjective.map (algebraMap R R⟦X⟧)).Equation ![s, -1, W'.formalW.subst s]),
      W.projModelFormalPoint ≫ f = W'.projModelPoint (algebraMap R R⟦X⟧) h (i := 1)
        (by simpa only [Matrix.cons_val_one, Matrix.cons_val_zero] using isUnit_neg_one) :=
  (W'.SpecMap_constantCoeff_comp_eq_projModelZero_iff
    (by rw [Category.assoc, hfo, projModelFormalPoint_projModelOver])).mp
    (by rw [SpecMap_constantCoeff_projModelFormalPoint_assoc, hf])

/-- An isomorphism `e : projModel W ≅ projModel W'` of projective Weierstrass models over `Spec R`
that carries the zero section to the zero section sends the formal point `[X : -1 : w(X)]` of `W`
to the point `[s : -1 : w'(s)]` of `W'` with `s = X * v` for a unit `v` of `R⟦X⟧`, where `w'` is
the `w`-expansion of `W'`. For a morphism that need not be an isomorphism, see
`exists_projModelFormalPoint_comp_eq`. -/
theorem exists_unit_projModelFormalPoint_comp_eq (e : W.projModel ≅ W'.projModel)
    (hz : W.projModelZero ≫ e.hom = W'.projModelZero)
    (ho : e.hom ≫ W'.projModelOver = W.projModelOver) :
    ∃ (v : R⟦X⟧ˣ) (h : (W'.toProjective.map (algebraMap R R⟦X⟧)).Equation
        ![X * (v : R⟦X⟧), -1, W'.formalW.subst (X * (v : R⟦X⟧))]),
      W.projModelFormalPoint ≫ e.hom = W'.projModelPoint (algebraMap R R⟦X⟧) h (i := 1)
        (by simpa only [Matrix.cons_val_one, Matrix.cons_val_zero] using isUnit_neg_one) := by
  -- `e` and its inverse send the formal points to `[s : -1 : w'(s)]` and `[s' : -1 : w(s')]`
  obtain ⟨s, hs, hE, hse⟩ := exists_projModelFormalPoint_comp_eq hz ho
  obtain ⟨s', -, hE', hse'⟩ := exists_projModelFormalPoint_comp_eq (f := e.inv)
    (e.comp_inv_eq.mpr hz.symm) (e.inv_comp_eq.mpr ho.symm)
  have ha : HasSubst s := .of_constantCoeff_zero' hs
  -- so the formal point of `W` is `[s' : -1 : w(s')]` reparametrised by `X ↦ s`, and `s'(s) = X`
  have hX : s'.subst s = X := W.subst_eq_X_of_projModelFormalPoint_eq ha (h := hE') <| by
    rw [← hse', SpecMap_substAlgHom_projModelFormalPoint_assoc W' ha, e.eq_comp_inv, hse]
  obtain ⟨v, rfl⟩ := exists_unit_eq_X_mul_of_subst_eq_X hs hX
  exact ⟨v, hE, hse⟩

end WeierstrassCurve

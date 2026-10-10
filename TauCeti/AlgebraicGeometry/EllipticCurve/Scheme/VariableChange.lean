/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.ProjModel
import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.CoordinateRing.LaurentExpansion
import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.CoordinateRing.VariableChange
import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.Eval
import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.Chart
import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.Points
import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.ZeroSection
import TauCeti.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant

/-!
# Pointed isomorphisms of projective Weierstrass models are changes of variables

Let `W` be a Weierstrass curve over a commutative ring `R`. A change of variables
`C = (u, r, s, t)` induces the isomorphism
`projModelVariableChangeIso W C : projModel (C • W) ≅ projModel W`,
`[X : Y : Z] ↦ [u²X + rZ : u²sX + u³Y + tZ : Z]`, of projective Weierstrass models, over `Spec R`
and carrying the zero section to the zero section. This file shows that these are all such
isomorphisms, and that each comes from only one change of variables: every isomorphism
`projModel W ≅ projModel W'` over `Spec R` that carries the zero section to the zero section is
induced by a unique change of variables `C` with `C • W' = W`. In particular, among the changes of
variables fixing `W`, only the identity induces the identity of `projModel W`. No hypothesis on
`W`, on `W'` or on `R` is needed; in particular the base may be nonreduced.

**Uniqueness.** Two changes of variables are compared on the tautological point `[x : y : 1]` of
`C • W`, whose coordinates lie in the affine coordinate ring `R[x, y] ⧸ ((C • W)(x, y))`. The
isomorphisms induced by `C` and `C'` send it to the points `[u²x + r : u²sx + u³y + t : 1]` and
`[u'²x + r' : u'²s'x + u'³y + t' : 1]`, and `x`, `y` and `1` are linearly independent over `R`.

**Existence.** Let `e : projModel W ≅ projModel W'` be an isomorphism over `Spec R` carrying the
zero section to the zero section. Since the zero section is the complement of the chart `D₊(Z)`,
`e` sends the tautological point `[x : y : 1]` of `W` to a point `[X' : Y' : 1]` with `X'` and
`Y'` in the affine coordinate ring `R[W]`. The pole orders of `X'` and `Y'` at infinity are read
on the formal neighbourhood of the zero section. Its formal point `[-z : 1 : -w(z)]`, with values
in `R⟦z⟧` and `w(z) = z³ + ⋯` the `w`-expansion of `W`, specializes to the zero section, so its
image under `e` lies on the open chart `D₊(Y)` of `W'`. By uniqueness of the solution of the
`w`-equation, the image is the formal point of `W'` at a parameter `b(z)` with `b(0) = 0`. The
same holds for the inverse of `e`, and composing the two substitutions gives `z`, so `b = z c(z)`
with `c` a unit. Over the Laurent series `R⸨z⸩`, the tautological point is the formal point,
through the Laurent expansion `R[W] → R⸨z⸩` at infinity (`WeierstrassCurve.laurentExpansion`).
Comparing the two descriptions of its image shows that `X'` has a pole of order exactly `2`, with
unit leading coefficient, and `Y'` a pole of order at most `3`. So `X' = αx + β` and
`Y' = γy + δx + ε` with `α` a unit
(`WeierstrassCurve.exists_eq_of_coeff_laurentExpansion_eq_zero_of_lt_neg_two`), and then
`(X', Y')` is `(u²x + r, u³y + u²sx + t)` for a change of variables `C` with `C • W' = W`
(`WeierstrassCurve.Affine.CoordinateRing.exists_variableChange_of_equation`). The isomorphisms `e`
and the one induced by `C` agree on the tautological point, hence on the scheme-theoretically
dense chart `D₊(Z)`, hence everywhere, as the target is separated over `Spec R`.

The behaviour at the zero section cannot be dropped: an isomorphism of affine coordinate rings
need not come from a change of variables. Over `R = k[ε] ⧸ (ε²)` with `k` a field of
characteristic different from `2`, the derivation
`∂ = (2y + a₁x + a₃) ∂/∂x + (3x² + 2a₂x + a₄ - a₁y) ∂/∂y` of `R[W]` gives the automorphism
`g ↦ g + εx ∂g`, which sends `x` to `x + εx(2y + a₁x + a₃)`. Its `xy` coefficient `2ε` is
nonzero, so this is not of the shape `u²x + r`.

## Main results

* `WeierstrassCurve.existsUnique_eq_eqToHom_comp_projModelVariableChangeIso_hom`: an
  isomorphism of projective Weierstrass models over the base that carries the zero section to the
  zero section is induced by a unique change of variables.
* `WeierstrassCurve.projModelVariableChangeIso_hom_inj`: for `C • W = C' • W`, the isomorphisms
  induced by `C` and `C'` agree exactly when `C = C'`.
* `WeierstrassCurve.eqToHom_comp_projModelVariableChangeIso_hom_inj`: for `C • W = W'` and
  `C' • W = W'`, the morphisms `projModel W' ⟶ projModel W` induced by `C` and `C'` agree exactly
  when `C = C'`.
* `WeierstrassCurve.eqToHom_comp_projModelVariableChangeIso_hom_eq_id_iff`: for `C • W = W`, the
  endomorphism of `projModel W` induced by `C` is the identity exactly when `C = 1`.

## References

* [J. H. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.1 (the change of
  variables), III.3.1(b) (the classification over a field) and IV.1 (the expansions at the zero
  section in the parameter `z = -x / y`).
* N. M. Katz and B. Mazur, *Arithmetic Moduli of Elliptic Curves*, 2.2.

## Provenance

The statement of `projModelVariableChangeIso_hom_inj` is that of AINTLIB
(`github.com/CBirkbeck/AINTLIB`, Apache-2.0) at commit
`c3415f32a313e19ace43e05479aeaa0d56ca287a`, file
`projects/ModularCurves/ModularCurves/EllipticCurve/ComparisonInjective.lean`, declaration
`projModelVCIso_injective'`, stated here as an equivalence. The proof is not the source's. The
source transports each isomorphism to an isomorphism of affine coordinate rings
(`pointedIsoCoordEquiv`, computed for a change of variables by `bridge_coordX` and
`bridge_coordY`), and treats the zero ring separately. Here both isomorphisms are evaluated on one
point of the projective model, by `projModelPoint_projModelVariableChangeIso_hom`, with no case
distinction. What is kept from the source is the last step: the coefficients are read off the
linear independence of `x`, `y` and `1` over `R` (the source's `coordXY_ext`), and `u` and `s` are
recovered by cancelling the unit `u²`, here in
`WeierstrassCurve.VariableChange.toMatrix_injective`. The other two statements are not stated in
the source, which derives them where it uses them (`transVC_unique` and `transVC_self` in
`InvariantDifferential.lean`).

The existence statement and its proof through the formal point and the Laurent expansion at
infinity are not taken from the source, which derives the classification from an isomorphism of
affine coordinate rings preserving their filtration by pole order (see the provenance note of
`TauCeti/AlgebraicGeometry/EllipticCurve/Affine/CoordinateRing/VariableChange.lean`).
-/

public section

open CategoryTheory

universe u

namespace WeierstrassCurve

variable {R : Type u} [CommRing R] {W : WeierstrassCurve R}

open Matrix in
-- If the isomorphisms induced by `C` and `C'` agree, through the identification of
-- `projModel (C • W)` with `projModel (C' • W)`, then the matrices of `C` and `C'`, mapped along a
-- ring homomorphism `g : R →+* S`, take the same value at the homogeneous coordinates `P` of every
-- `S`-point of `projModel (C • W)` over `g` whose third coordinate is a unit.
private theorem toMatrix_map_mulVec_eq {C C' : VariableChange R} (h : C • W = C' • W)
    (hC : (W.projModelVariableChangeIso C).hom =
      eqToHom (congrArg projModel h) ≫ (W.projModelVariableChangeIso C').hom) {S : Type u}
    [CommRing S] {g : R →+* S} {P : Fin 3 → S} (hP : ((C • W).toProjective.map g).Equation P)
    (hi : IsUnit (P 2)) : (C.map g).toMatrix *ᵥ P = (C'.map g).toMatrix *ᵥ P := by
  -- a change of variables fixes the third homogeneous coordinate
  have hZ (D : VariableChange R) : ((D.map g).toMatrix *ᵥ P) 2 = P 2 :=
    (D.map g).toMatrix_mulVec_two P
  have hj (D : VariableChange R) : IsUnit (((D.map g).toMatrix *ᵥ P) 2) := by rwa [hZ D]
  -- both isomorphisms send the point with coordinates `P` to the same point of `projModel W`
  have key := projModelPoint_projModelVariableChangeIso_hom (hP := hP) hi (hj C)
  rw [hC, projModelPoint_eqToHom_assoc h hi,
    projModelPoint_projModelVariableChangeIso_hom hi (hj C'),
    projModelPoint_eq_projModelPoint_iff] at key
  obtain ⟨-, l, hl⟩ := key
  -- the two triples of coordinates are proportional, with the same unit third coordinate
  exact ((Projective.equiv_iff_eq_of_Z_eq' ((hZ C').trans (hZ C).symm)
    (hj C).mem_nonZeroDivisors).mp ⟨l, hl.symm⟩).symm

/-- A change of variables is determined by the isomorphism of projective Weierstrass models it
induces. For changes of variables `C` and `C'` with `C • W = C' • W`, the isomorphisms
`projModel (C • W) ≅ projModel W` and `projModel (C' • W) ≅ projModel W` induced by `C` and `C'`
agree, through the identification of `projModel (C • W)` with `projModel (C' • W)`, exactly when
`C = C'`. -/
@[simp]
theorem projModelVariableChangeIso_hom_inj {C C' : VariableChange R} (h : C • W = C' • W) :
    (W.projModelVariableChangeIso C).hom =
      eqToHom (congrArg projModel h) ≫ (W.projModelVariableChangeIso C').hom ↔ C = C' := by
  refine ⟨fun hC ↦ ?_, by rintro rfl; rw [eqToHom_refl, Category.id_comp]⟩
  -- `C` and `C'` act in the same way on the tautological point `[x : y : 1]` of `C • W`, with
  -- coordinates in the affine coordinate ring
  have hM := toMatrix_map_mulVec_eq h hC (g := algebraMap R (C • W).toAffine.CoordinateRing)
    (P := ![AdjoinRoot.of _ Polynomial.X, AdjoinRoot.root _, 1])
    ((Projective.equation_some _ _).mpr (by
      simpa only [AlgHom.id_apply, Affine.baseChange, WeierstrassCurve.baseChange] using
        Affine.CoordinateRing.equation_of_algHom (AlgHom.id R (C • W).toAffine.CoordinateRing)))
    (by simpa only [Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons] using isUnit_one)
  -- `x`, `y` and `1` are linearly independent over `R`, so the matrices of `C` and `C'` have the
  -- same rows
  refine VariableChange.toMatrix_injective (Matrix.ext fun i ↦
    (Affine.CoordinateRing.linearIndependent_X_root_one (C • W).toAffine).eq_coords_of_eq ?_)
  simpa only [Algebra.smul_def, Matrix.mulVec, dotProduct, VariableChange.toMatrix_map,
    Matrix.map_apply] using congrFun hM i

/-- A change of variables carrying `W` to `W'` is determined by the isomorphism
`projModel W' ≅ projModel W` it induces. For changes of variables `C` and `C'` with `C • W = W'`
and `C' • W = W'`, the isomorphisms induced by `C` and `C'`, read as morphisms
`projModel W' ⟶ projModel W` through the identifications of `projModel W'` with
`projModel (C • W)` and with `projModel (C' • W)`, agree exactly when `C = C'`. -/
@[simp]
theorem eqToHom_comp_projModelVariableChangeIso_hom_inj {W' : WeierstrassCurve R}
    {C C' : VariableChange R} (hC : C • W = W') (hC' : C' • W = W') :
    eqToHom (congrArg projModel hC.symm) ≫ (W.projModelVariableChangeIso C).hom =
      eqToHom (congrArg projModel hC'.symm) ≫ (W.projModelVariableChangeIso C').hom ↔ C = C' := by
  subst hC
  rw [eqToHom_refl, Category.id_comp, projModelVariableChangeIso_hom_inj hC'.symm]

/-- Among the changes of variables fixing `W`, only the identity induces the identity of the
projective Weierstrass model. For a change of variables `C` with `C • W = W`, the isomorphism
induced by `C`, read as an endomorphism of `projModel W` through the identification of
`projModel W` with `projModel (C • W)`, is the identity exactly when `C = 1`. The implication from
`C = 1` follows from `projModelVariableChangeIso_one`. -/
@[simp]
theorem eqToHom_comp_projModelVariableChangeIso_hom_eq_id_iff {C : VariableChange R}
    (h : C • W = W) :
    eqToHom (congrArg projModel h.symm) ≫ (W.projModelVariableChangeIso C).hom = 𝟙 W.projModel ↔
      C = 1 := by
  rw [← eqToHom_comp_projModelVariableChangeIso_hom_inj h (one_smul _ W),
    projModelVariableChangeIso_one, eqToIso.hom, eqToHom_trans, eqToHom_refl]

/-! ### Existence: a pointed isomorphism is a change of variables -/

section Existence

open AlgebraicGeometry PowerSeries

open scoped LaurentSeries

variable {W' : WeierstrassCurve R}

-- With second coordinate `1`, the projective Weierstrass equation at `(q, 1, v)` is the
-- `w`-equation `-v = w(-q)` at the parameter `-q`: the coordinates at the zero section are
-- `z = -X / Y` and `w = -Z / Y`.
private theorem equation_iff_wEquationRHS {A : Type u} [CommRing A] [Algebra R A] {q v : A} :
    (W.toProjective.map (algebraMap R A)).Equation ![q, 1, v] ↔
      -v = wEquationRHS W (-q) (-v) := by
  rw [Projective.equation_iff, wEquationRHS_def]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons, map_a₁, map_a₂, map_a₃, map_a₄, map_a₆]
  constructor <;> intro h <;> linear_combination -h

-- The second coordinate of `(q, 1, v)` is a unit. Stated on its own so that the proof keeps the
-- type `IsUnit (![q, 1, v] 1)` under which the points below are formed and rewritten.
private theorem isUnit_vecCons_one {A : Type*} [CommRing A] (q v : A) : IsUnit (![q, 1, v] 1) := by
  simp

-- The homogeneous coordinates `(-z, 1, -w(z))` over `R⟦X⟧` solve the Weierstrass equation.
private theorem equation_zeroFormalPoint :
    (W.toProjective.map (algebraMap R R⟦X⟧)).Equation ![-X, 1, -formalW W] := by
  rw [equation_iff_wEquationRHS, neg_neg, neg_neg]
  exact formalW_wEquation W

variable (W) in
-- The formal point at the zero section: the point `[-z : 1 : -w(z)]` of the projective model
-- with values in `R⟦X⟧`, through the chart `D₊(Y)`.
private noncomputable def zeroFormalPoint : Spec (.of R⟦X⟧) ⟶ W.projModel :=
  W.projModelPoint (algebraMap R R⟦X⟧) equation_zeroFormalPoint (isUnit_vecCons_one _ _)

-- The formal point at a parameter `b` with `b(0) = 0`, obtained by substituting `b` for `z`, is
-- the point `[-b : 1 : -w(b)]`.
private theorem SpecMap_substAlgHom_zeroFormalPoint {b : R⟦X⟧} (hb : HasSubst b) :
    Spec.map (CommRingCat.ofHom (substAlgHom hb : R⟦X⟧ →ₐ[R] R⟦X⟧).toRingHom) ≫
        W.zeroFormalPoint =
      W.projModelPoint (algebraMap R R⟦X⟧) (P := ![-b, 1, -subst b (formalW W)])
        (by rw [equation_iff_wEquationRHS, neg_neg, neg_neg]
            exact subst_formalW_wEquation W hb) (isUnit_vecCons_one _ _) := by
  rw [zeroFormalPoint, SpecMap_projModelPoint, projModelPoint_eq_projModelPoint_iff]
  refine ⟨RingHom.ext (substAlgHom hb).commutes, 1, funext fun k ↦ ?_⟩
  fin_cases k <;> simp [substAlgHom_X, ← coe_substAlgHom hb]

-- The formal point reduces to the zero section modulo `z`.
private theorem SpecMap_constantCoeff_zeroFormalPoint :
    Spec.map (CommRingCat.ofHom (constantCoeff (R := R))) ≫ W.zeroFormalPoint =
      W.projModelZero := by
  rw [← Category.id_comp W.projModelZero, ← Spec.map_id, ← CommRingCat.ofHom_id,
    SpecMap_projModelZero, zeroFormalPoint, SpecMap_projModelPoint,
    projModelPoint_eq_projModelPoint_iff]
  refine ⟨constantCoeff_comp_C, 1, funext fun k ↦ ?_⟩
  fin_cases k <;> simp [constantCoeff_formalW]

-- Every point of `Spec R⟦X⟧` specializes to a point at which the formal point passes through the
-- zero section, since `z` lies in every maximal ideal of `R⟦X⟧`. So under a morphism that carries
-- the zero section to the zero section, the image of the formal point lies on the chart `D₊(Y)`,
-- an open neighbourhood of the zero section.
private theorem zeroFormalPoint_comp_mem_basicOpen_one {f : W.projModel ⟶ W'.projModel}
    (hf : W.projModelZero ≫ f = W'.projModelZero) (s : Spec (.of R⟦X⟧)) :
    (W.zeroFormalPoint ≫ f) s ∈
      Proj.basicOpen W'.toProjective.grading (W'.toProjective.coord 1) := by
  obtain ⟨m, hm, hsm⟩ := s.asIdeal.exists_le_maximal s.isPrime.ne_top
  -- `z` lies in the maximal ideal `m`: otherwise `m` contains `1 - az`, a unit
  have hX : (X : R⟦X⟧) ∈ m := by
    by_contra hX
    obtain ⟨a, i, hi, hai⟩ := hm.exists_inv hX
    refine hm.ne_top (m.eq_top_of_isUnit_mem hi (isUnit_iff_constantCoeff.mpr ?_))
    have := congrArg constantCoeff hai
    simp only [map_add, map_mul, constantCoeff_X, mul_zero, zero_add, map_one] at this
    exact this ▸ isUnit_one
  let t : Spec (.of R⟦X⟧) := ⟨m, hm.isPrime⟩
  -- at `t` the formal point is off the chart `D₊(Z)`, since `w(z)` lies in `m`
  have ht : W.zeroFormalPoint t ∈ Set.range W.projModelZero := by
    rw [mem_range_projModelZero_iff, zeroFormalPoint, projModelPoint_mem_basicOpen_iff]
    have hw : formalW W ∈ m := by
      rw [formalW_eq_X_pow_mul_formalU]
      exact m.mul_mem_right _ (m.pow_mem_of_mem hX 3 (by norm_num))
    simpa using hw
  obtain ⟨q, hq⟩ := ht
  have hmem : (W.zeroFormalPoint ≫ f) t ∈
      Proj.basicOpen W'.toProjective.grading (W'.toProjective.coord 1) := by
    rw [Scheme.Hom.comp_apply, ← hq, ← Scheme.Hom.comp_apply, hf]
    exact (W'.projModelZero_mem_basicOpen_iff q 1).mpr rfl
  exact (((PrimeSpectrum.le_iff_specializes s t).mp hsm).map
    (W.zeroFormalPoint ≫ f).continuous).mem_open (Proj.basicOpen _ _).isOpen hmem

-- Under a morphism over the base that carries the zero section to the zero section, the formal
-- point at the zero section goes to the formal point at some parameter `b` with `b(0) = 0`.
private theorem exists_zeroFormalPoint_comp_eq {f : W.projModel ⟶ W'.projModel}
    (hf : W.projModelZero ≫ f = W'.projModelZero) (hfo : f ≫ W'.projModelOver = W.projModelOver) :
    ∃ (b : R⟦X⟧) (hb : constantCoeff b = 0), W.zeroFormalPoint ≫ f =
      Spec.map (CommRingCat.ofHom (substAlgHom (HasSubst.of_constantCoeff_zero' hb) :
        R⟦X⟧ →ₐ[R] R⟦X⟧).toRingHom) ≫ W'.zeroFormalPoint := by
  -- the image lies on the chart `D₊(Y)`, so it has homogeneous coordinates `(Q₀, 1, Q₂)`
  obtain ⟨Q, hQ, hQ1, hx⟩ := W'.exists_eq_projModelPoint_of_forall_mem_basicOpen
    (x := W.zeroFormalPoint ≫ f) (g := algebraMap R R⟦X⟧)
    (by rw [Category.assoc, hfo, zeroFormalPoint, projModelPoint_projModelOver]) (i := 1)
    (zeroFormalPoint_comp_mem_basicOpen_one hf)
  have hQ' : Q = ![Q 0, 1, Q 2] := funext fun k ↦ by fin_cases k <;> simp [hQ1]
  -- modulo `z`, the image is the zero section `(0, 1, 0)`
  have h0 : Spec.map (CommRingCat.ofHom (constantCoeff (R := R))) ≫ W.zeroFormalPoint ≫ f =
      Spec.map (CommRingCat.ofHom (RingHom.id R)) ≫ W'.projModelZero := by
    rw [← Category.assoc, SpecMap_constantCoeff_zeroFormalPoint, hf, CommRingCat.ofHom_id,
      Spec.map_id, Category.id_comp]
  rw [hx, SpecMap_projModelPoint, SpecMap_projModelZero, projModelPoint_eq_projModelPoint_iff]
    at h0
  obtain ⟨-, u, hu⟩ := h0
  have hc : ∀ k, constantCoeff (Q k) = (u : R) * ![0, 1, 0] k := fun k ↦ congrFun hu k
  have hu1 : (u : R) = 1 := by simpa [hQ1] using (hc 1).symm
  have hc0 : constantCoeff (Q 0) = 0 := by simpa using hc 0
  have hc2 : constantCoeff (Q 2) = 0 := by simpa using hc 2
  -- the third coordinate is `-w(-Q₀)`, by uniqueness of the solution of the `w`-equation
  have hb : constantCoeff (-Q 0) = 0 := by rw [map_neg, hc0, neg_zero]
  have hw : -Q 2 = subst (-Q 0) (formalW W') := by
    refine eq_subst_formalW_of_wEquation W' hb (by rw [map_neg, hc2, neg_zero]) ?_
    rw [hQ'] at hQ
    exact equation_iff_wEquationRHS.mp hQ
  refine ⟨-Q 0, hb, ?_⟩
  rw [SpecMap_substAlgHom_zeroFormalPoint, hx, projModelPoint_eq_projModelPoint_iff]
  refine ⟨rfl, 1, funext fun k ↦ ?_⟩
  fin_cases k <;> simp [hQ1, ← hw]

-- An `R`-algebra endomorphism `ψ` of `R⟦X⟧` fixing the formal point fixes `z`.
private theorem eq_X_of_SpecMap_zeroFormalPoint {ψ : R⟦X⟧ →ₐ[R] R⟦X⟧}
    (h : Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ W.zeroFormalPoint = W.zeroFormalPoint) :
    ψ X = X := by
  rw [zeroFormalPoint, SpecMap_projModelPoint, projModelPoint_eq_projModelPoint_iff] at h
  obtain ⟨-, u, hu⟩ := h
  -- the second coordinates show `u = 1`, and then the first ones show `ψ(-z) = -z`
  have h1 : (u : R⟦X⟧) = 1 := by simpa [Units.smul_def] using (congrFun hu 1).symm
  simpa [Units.smul_def, h1] using congrFun hu 0

-- Under a pointed isomorphism over the base, the formal point at the zero section goes to the
-- formal point at a parameter `z c(z)` with `c` a unit: the parameter `b` of the image, and the
-- parameter `b'` of the image under the inverse, satisfy `b(b'(z)) = z`.
private theorem exists_isUnit_zeroFormalPoint_comp_eq (e : W.projModel ≅ W'.projModel)
    (he : e.hom ≫ W'.projModelOver = W.projModelOver)
    (h0 : W.projModelZero ≫ e.hom = W'.projModelZero) :
    ∃ (c : R⟦X⟧) (hc : constantCoeff (X * c) = 0), IsUnit c ∧ W.zeroFormalPoint ≫ e.hom =
      Spec.map (CommRingCat.ofHom (substAlgHom (HasSubst.of_constantCoeff_zero' hc) :
        R⟦X⟧ →ₐ[R] R⟦X⟧).toRingHom) ≫ W'.zeroFormalPoint := by
  obtain ⟨b, hb, hfb⟩ := exists_zeroFormalPoint_comp_eq h0 he
  obtain ⟨b', hb', hgb⟩ := exists_zeroFormalPoint_comp_eq (f := e.inv)
    (by rw [← h0, Category.assoc, e.hom_inv_id, Category.comp_id])
    (by rw [← he, e.inv_hom_id_assoc])
  obtain ⟨c, rfl⟩ := X_dvd_iff.mpr hb
  obtain ⟨c', rfl⟩ := X_dvd_iff.mpr hb'
  refine ⟨c, hb, ?_, hfb⟩
  -- the composite of the two substitutions fixes the formal point, hence fixes `z`
  set σ := (substAlgHom (HasSubst.of_constantCoeff_zero' hb) : R⟦X⟧ →ₐ[R] R⟦X⟧)
  set σ' := (substAlgHom (HasSubst.of_constantCoeff_zero' hb') : R⟦X⟧ →ₐ[R] R⟦X⟧)
  have h : Spec.map (CommRingCat.ofHom (σ.comp σ').toRingHom) ≫ W.zeroFormalPoint =
      W.zeroFormalPoint := by
    rw [AlgHom.toRingHom_eq_coe] at hfb hgb
    rw [AlgHom.toRingHom_eq_coe, AlgHom.comp_toRingHom, CommRingCat.ofHom_comp, Spec.map_comp,
      Category.assoc, ← hgb,
      ← Category.assoc, ← hfb, Category.assoc, e.hom_inv_id, Category.comp_id]
  have hX := eq_X_of_SpecMap_zeroFormalPoint h
  rw [AlgHom.comp_apply, substAlgHom_X, map_mul, substAlgHom_X, mul_assoc] at hX
  exact .of_mul_eq_one _ (X_mul_cancel (hX.trans (mul_one X).symm))

-- The third coordinate of `(q, v, 1)` is a unit, stated on its own for the same reason.
private theorem isUnit_vecCons_two {A : Type*} [CommRing A] (q v : A) : IsUnit (![q, v, 1] 2) := by
  simp

-- The coordinate functions `(x, y, 1)` over the affine coordinate ring solve the Weierstrass
-- equation.
private theorem equation_tautologicalPoint :
    (W.toProjective.map (algebraMap R W.toAffine.CoordinateRing)).Equation
      ![AdjoinRoot.of W.toAffine.polynomial Polynomial.X, AdjoinRoot.root W.toAffine.polynomial,
        1] :=
  (Projective.equation_some _ _).mpr (Affine.CoordinateRing.equation_X_root W.toAffine)

variable (W) in
-- The tautological point `[x : y : 1]` of the projective model, with values in the affine
-- coordinate ring.
private noncomputable def tautologicalPoint : Spec (.of W.toAffine.CoordinateRing) ⟶ W.projModel :=
  W.projModelPoint (algebraMap R _) equation_tautologicalPoint (isUnit_vecCons_two _ _)

-- The chart `D₊(Z)` factors through the tautological point.
private theorem exists_SpecMap_comp_tautologicalPoint_eq_chartι :
    ∃ k : W.toAffine.CoordinateRing →ₐ[R] W.toProjective.ChartRing 2,
      Spec.map (CommRingCat.ofHom k.toRingHom) ≫ W.tautologicalPoint = W.chartι 2 := by
  -- the universal point of the chart is `(X / Z, Y / Z, 1)`
  have hP : W.toProjective.chartPoint 2 = ![W.toProjective.chartPoint 2 0,
      W.toProjective.chartPoint 2 1, 1] := funext fun k ↦ by
    fin_cases k <;> simp
  have hE := W.toProjective.equation_chartPoint 2
  rw [hP] at hE
  refine ⟨Affine.CoordinateRing.evalAlgHom ((Projective.equation_some _ _).mp hE), ?_⟩
  rw [tautologicalPoint, SpecMap_projModelPoint, chartι_eq_projModelPoint,
    projModelPoint_eq_projModelPoint_iff]
  refine ⟨RingHom.ext (Affine.CoordinateRing.evalAlgHom _).commutes, 1, funext fun k ↦ ?_⟩
  fin_cases k <;> simp

-- Expanded in Laurent series at the point at infinity, the tautological point `[x : y : 1]` is
-- the formal point `[-z : 1 : -w(z)]`: its coordinates are `y` times those of the formal point.
private theorem SpecMap_laurentExpansion_tautologicalPoint :
    Spec.map (CommRingCat.ofHom (W.laurentExpansion : W.toAffine.CoordinateRing →+* R⸨X⸩)) ≫
        W.tautologicalPoint =
      Spec.map (CommRingCat.ofHom (HahnSeries.ofPowerSeries ℤ R)) ≫ W.zeroFormalPoint := by
  have hy := W.laurentExpansion_root_mul_formalW
  have hx := W.laurentExpansion_of_X_eq_neg_X_mul_laurentExpansion_root
  rw [tautologicalPoint, zeroFormalPoint, SpecMap_projModelPoint, SpecMap_projModelPoint,
    projModelPoint_eq_projModelPoint_iff]
  refine ⟨(W.laurentExpansion.comp_algebraMap).trans rfl,
    (IsUnit.of_mul_eq_one (-HahnSeries.ofPowerSeries ℤ R (formalW W))
      (by rw [mul_neg, hy, neg_neg])).unit, funext fun k ↦ ?_⟩
  fin_cases k
  · simp [-laurentExpansion_of_X, -laurentExpansion_root, Units.smul_def, hx]
    ring
  · simp
  · simp [-laurentExpansion_root, Units.smul_def, hy]

open HahnSeries in
-- Under a pointed isomorphism over the base, the image `[X' : Y' : 1]` of the tautological point
-- has Laurent expansions `X' = z⁻² F(z)` and `Y' = z⁻³ G(z)` at the point at infinity, with `F`
-- and `G` power series and `F(0)` a unit. The formal point goes to the formal point at
-- `b = z c(z)`, `c` a unit, and `-w'(b) = z³ E(z)` with `E` a unit; comparing the two
-- expansions of the image gives `Y' = 1 / (z³ E)` and `X' = -b Y'`.
private theorem exists_laurentExpansion_eq_of_iso (e : W.projModel ≅ W'.projModel)
    (he : e.hom ≫ W'.projModelOver = W.projModelOver)
    (h0 : W.projModelZero ≫ e.hom = W'.projModelZero) {Q : Fin 3 → W.toAffine.CoordinateRing}
    (hQ : (W'.toProjective.map (algebraMap R _)).Equation Q) (hQ2 : Q 2 = 1) {hQ2' : IsUnit (Q 2)}
    (hτ : W.tautologicalPoint ≫ e.hom = W'.projModelPoint _ hQ hQ2') :
    ∃ F G : R⟦X⟧, IsUnit (constantCoeff F) ∧
      W.laurentExpansion (Q 0) = single (-2) 1 * ofPowerSeries ℤ R F ∧
      W.laurentExpansion (Q 1) = single (-3) 1 * ofPowerSeries ℤ R G := by
  obtain ⟨c, hc0, hc, hfc⟩ := exists_isUnit_zeroFormalPoint_comp_eq e he h0
  set σ := (substAlgHom (HasSubst.of_constantCoeff_zero' hc0) : R⟦X⟧ →ₐ[R] R⟦X⟧)
  -- `-w'(z c(z)) = z³ E(z)` with `E` a unit
  set E : R⟦X⟧ := -(c ^ 3 * σ (formalU W'))
  have hwE : -subst (X * c) (formalW W') = X ^ 3 * E := by
    rw [← coe_substAlgHom (HasSubst.of_constantCoeff_zero' hc0), formalW_eq_X_pow_mul_formalU,
      map_mul, map_pow, substAlgHom_X]
    ring
  have hE : IsUnit E := by
    refine isUnit_iff_constantCoeff.mpr ?_
    have hU : constantCoeff (σ (formalU W')) = 1 := by
      rw [coe_substAlgHom]
      exact (constantCoeff_subst_of_constantCoeff_zero hc0 _).trans (by simp)
    simpa [E, hU] using (isUnit_iff_constantCoeff.mp hc).pow 3 |>.neg
  obtain ⟨Eu, hEu⟩ := hE
  -- comparing the two expansions of the image of the tautological point
  have key := congrArg (Spec.map (CommRingCat.ofHom
    (W.laurentExpansion : W.toAffine.CoordinateRing →+* R⸨X⸩)) ≫ ·) hτ
  rw [← Category.assoc, SpecMap_laurentExpansion_tautologicalPoint, Category.assoc, hfc,
    SpecMap_substAlgHom_zeroFormalPoint, SpecMap_projModelPoint, SpecMap_projModelPoint,
    projModelPoint_eq_projModelPoint_iff] at key
  obtain ⟨-, v, hv⟩ := key
  have h0' := congrFun hv 0
  have h1 := congrFun hv 1
  have h2 := congrFun hv 2
  simp only [Function.comp_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons, Units.smul_def, Pi.smul_apply, smul_eq_mul, hQ2, map_one,
    mul_one, RingHom.coe_coe] at h0' h1 h2
  rw [hwE, ← hEu] at h2
  -- `z⁻³ E⁻¹` is inverse to `v = z³ E`
  set Y : R⸨X⸩ := single (-3) 1 * ofPowerSeries ℤ R ↑Eu⁻¹ with hY_def
  have hYv : Y * v = 1 := by
    rw [← h2, map_mul, map_pow, ofPowerSeries_X, single_pow, mul_mul_mul_comm, single_mul_single,
      ← map_mul, Units.inv_mul]
    simp
  have hY : W.laurentExpansion (Q 1) = Y := by
    calc W.laurentExpansion (Q 1) = Y * v * W.laurentExpansion (Q 1) := by rw [hYv, one_mul]
      _ = Y := by rw [mul_assoc, ← h1, mul_one]
  refine ⟨↑Eu⁻¹ * -c, ↑Eu⁻¹, ?_, ?_, hY⟩
  · rw [map_mul, map_neg]
    exact (Eu⁻¹.isUnit.map constantCoeff).mul (isUnit_iff_constantCoeff.mp hc).neg
  · calc W.laurentExpansion (Q 0) = Y * v * W.laurentExpansion (Q 0) := by rw [hYv, one_mul]
      _ = Y * ofPowerSeries ℤ R (-(X * c)) := by rw [mul_assoc, ← h0']
      _ = single (-2) 1 * ofPowerSeries ℤ R (↑Eu⁻¹ * -c) := by
        -- split `z⁻²` as `z⁻³ * z` to match `Y * X`
        have h23 : (-2 : ℤ) = -3 + 1 := by norm_num
        rw [mul_neg, map_neg, map_mul, ofPowerSeries_X, mul_neg, map_neg, map_mul, h23,
          ← one_mul (1 : R), ← single_mul_single, hY_def, one_mul]
        ring

open HahnSeries in
/-- **Every pointed isomorphism of projective Weierstrass models is a change of variables.** Let
`W` and `W'` be Weierstrass curves over a commutative ring `R`, and let
`e : projModel W ≅ projModel W'` be an isomorphism over `Spec R` that carries the zero section to
the zero section. Then there is a unique change of variables `C` with `C • W' = W` such that `e` is
the isomorphism `projModel W ≅ projModel (C • W') ≅ projModel W'` induced by `C`. No hypothesis on
`W`, on `W'` or on `R` is needed. -/
theorem existsUnique_eq_eqToHom_comp_projModelVariableChangeIso_hom
    (e : W.projModel ≅ W'.projModel) (he : e.hom ≫ W'.projModelOver = W.projModelOver)
    (h0 : W.projModelZero ≫ e.hom = W'.projModelZero) :
    ∃! C : VariableChange R, ∃ h : C • W' = W,
      e.hom = eqToHom (congrArg projModel h.symm) ≫ (W'.projModelVariableChangeIso C).hom := by
  refine existsUnique_of_exists_of_unique ?_ fun C C' ⟨h, hC⟩ ⟨h', hC'⟩ ↦
    (eqToHom_comp_projModelVariableChangeIso_hom_inj h h').mp (hC.symm.trans hC')
  -- the image `[X' : Y' : 1]` of the tautological point `[x : y : 1]`
  obtain ⟨Q, hQ, hQ2, hτ⟩ := exists_projModelPoint_comp_eq_projModelPoint h0
    (fun a b hab ↦ e.hom.homeomorph.injective hab) he equation_tautologicalPoint
    (isUnit_vecCons_two _ _)
  obtain ⟨F, G, hF, hX', hY'⟩ := exists_laurentExpansion_eq_of_iso e he h0 hQ hQ2 hτ
  -- `X'` has a pole of order `2` and `Y'` a pole of order at most `3` at infinity
  have hcoeff (H : R⟦X⟧) {k m : ℤ} (hm : m < k) :
      (single k (1 : R) * ofPowerSeries ℤ R H).coeff m = 0 := by
    rw [coeff_single_mul, PowerSeries.coeff_coe]
    have hmk : m - k < 0 := by omega
    simp [hmk]
  obtain ⟨β, hβ⟩ := W.exists_eq_of_coeff_laurentExpansion_eq_zero_of_lt_neg_two
    (g := Q 0) fun m hm ↦ hX' ▸ hcoeff F hm
  obtain ⟨δ, ε, hδε⟩ := W.exists_eq_of_coeff_laurentExpansion_eq_zero_of_lt_neg_three
    (g := Q 1) fun m hm ↦ hY' ▸ hcoeff G hm
  set α := (W.laurentExpansion (Q 0)).coeff (-2)
  set γ := -(W.laurentExpansion (Q 1)).coeff (-3)
  have hα : IsUnit α := by
    simpa [α, hX', coeff_single_mul, PowerSeries.coeff_coe] using hF
  -- `(X', Y') = (αx + β, γy + δx + ε)` is a point of `W'`, so it comes from a change of variables
  have hQ' : Q = ![Q 0, Q 1, 1] := funext fun k ↦ by fin_cases k <;> simp [hQ2]
  have hEq := (Projective.equation_some _ _).mp (hQ' ▸ hQ)
  rw [hβ, hδε] at hEq
  obtain ⟨C, hC, hu2, hu3, hr, hs, ht⟩ := Affine.CoordinateRing.exists_variableChange_of_equation hα
    hEq
  refine ⟨C, hC, ?_⟩
  -- the two isomorphisms agree on the scheme-theoretically dense chart `D₊(Z)`, through which the
  -- chart factors through the tautological point
  obtain ⟨k, hk⟩ := W.exists_SpecMap_comp_tautologicalPoint_eq_chartι
  refine TauCeti.ext_of_isSchemeTheoreticallyDominant (W.chartι 2) W'.projModelOver ?_ ?_
  · rw [he, Category.assoc, projModelVariableChangeIso_hom_projModelOver]
    subst hC
    simp
  · rw [← hk, Category.assoc, Category.assoc, tautologicalPoint, hτ,
      projModelPoint_eqToHom_assoc hC.symm,
      projModelPoint_projModelVariableChangeIso_hom (j := 2) _
        (by rw [VariableChange.toMatrix_mulVec_two]; exact isUnit_vecCons_two _ _)]
    congr 1
    rw [projModelPoint_eq_projModelPoint_iff]
    refine ⟨rfl, 1, funext fun i ↦ ?_⟩
    fin_cases i
    · simp [hβ, ← hu2, ← hr, VariableChange.toMatrix_def]
      ring
    · simp [hδε, ← hu3, ← hs, ← ht, VariableChange.toMatrix_def]
      ring
    · simp [hQ2, VariableChange.toMatrix_def]

end Existence

end WeierstrassCurve

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.CoordinateRing.VariableChange
public import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.Point.VariableChange
public import TauCeti.AlgebraicGeometry.EllipticCurve.Aut
public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.Hom.Basic
public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.Neg
public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.TautologicalPoint
-- Proof-only: a degree-one isogeny has an inverse, and pullbacks give `x` a pole at infinity.
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.Factorisation
-- Proof-only: integral closedness of the coordinate ring of an elliptic curve.
import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.CoordinateRing
-- Proof-only: the functions of pole order at most three on the affine curve.
import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.FunctionField.InfinityPlace.PoleOrder
-- Proof-only: the equation satisfied by the images of the coordinate functions.
import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.Eval
-- Proof-only: triviality on `F` of a valuation restricted along a pullback.
import TauCeti.RingTheory.Valuation.IsTrivialOn
-- Proof-only: a unit of the endomorphism monoid has degree one.
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.Units

/-!
# Isomorphisms of elliptic curves are changes of variables

A change of variables `C = (u, r, s, t)` carries a Weierstrass curve `W₁` to `W₂ = C • W₁`, and
the substitution `x₁ = u²x₂ + r`, `y₁ = u³y₂ + u²sx₂ + t` identifies their coordinate rings
(`WeierstrassCurve.Affine.CoordinateRing.variableChangeEquiv`). Read contravariantly, this is a
coordinate pullback `R(W₂) → K(W₁)`, and it maps the point at infinity to the point at infinity
because every function on `W₁` is already a pullback. So a change of variables is an isogeny
`W₁ ⟶ W₂` of degree one, and changes of variables compose as their isogenies do.

Conversely, between elliptic curves every isogeny of degree one comes from a change of variables
(Silverman III.3.1(b)). Such an isogeny `φ` has an inverse, and both pull coordinate rings back
into coordinate rings, the coordinate rings being integrally closed. Comparing pole orders at
infinity in both directions, `φ` pulls `x₂` back to a function of pole order two and `y₂` to one
of pole order at most three. On the affine curve those are `αx₁ + β` with `α ≠ 0` and
`γy₁ + δx₁ + ε` (`WeierstrassCurve.Affine.exists_eq_of_val_lt_val_mk_Y` and
`WeierstrassCurve.Affine.exists_eq_of_val_le_val_mk_Y`), and a substitution of that shape
satisfying the equation of `W₂` is a change of variables
(`WeierstrassCurve.Affine.CoordinateRing.exists_variableChange_of_equation`).

For a curve `W` the changes of variables fixing `W` form `W.autGroup`, the stabiliser of `W` in
`VariableChange F`. Their isogenies are automorphisms of `W` fixing the point at infinity, units
of the endomorphism monoid `Hom W W`, and for an elliptic curve every such unit arises from exactly
one of them: `W.autGroup ≃* (Hom W W)ˣ`.

## Main definitions

* `TauCeti.Isogeny.variableChangeIsogeny`: the isogeny `W₁ ⟶ W₂` of a change of variables `C`
  with `C • W₁ = W₂`.
* `TauCeti.Isogeny.Hom.autGroupToUnits`: the homomorphism `W.autGroup →* (Hom W W)ˣ`.
* `TauCeti.Isogeny.Hom.autGroupEquivUnits`: for an elliptic curve, the isomorphism
  `W.autGroup ≃* (Hom W W)ˣ`.

## Main results

* `TauCeti.Isogeny.variableChangeIsogeny_comp` and `TauCeti.Isogeny.variableChangeIsogeny_one`:
  the isogenies of changes of variables compose as the changes of variables multiply.
* `TauCeti.Isogeny.degree_variableChangeIsogeny`: they have degree one.
* `TauCeti.Isogeny.tautologicalPoint_variableChangePullback`: the tautological point of a change of
  variables is the generic point moved by `WeierstrassCurve.pointEquivVariableChange`.
* `TauCeti.Isogeny.variableChangeIsogeny_inj`: a change of variables is determined by its isogeny.
* `TauCeti.Isogeny.variableChangeIsogeny_negVariableChange`: the change of variables `[-1]` gives
  the negation isogeny.
* `TauCeti.Isogeny.exists_algebraMap_eq_pullback_of_degree_eq_one`: an isogeny of degree one out
  of a curve with integrally closed coordinate ring (for instance an elliptic curve) pulls the
  coordinate ring back into the coordinate ring.
* `TauCeti.Isogeny.exists_variableChangeIsogeny_eq_of_degree_eq_one`: **an isogeny of degree one
  between elliptic curves is the isogeny of a change of variables.**
* `TauCeti.Isogeny.Hom.autGroupToUnits_injective` and
  `TauCeti.Isogeny.Hom.autGroupToUnits_surjective`.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.1, III.3.1 and III.10.
-/

public section

open WeierstrassCurve WeierstrassCurve.Affine.CoordinateRing

namespace TauCeti

variable {F : Type*} [Field F] {W₁ W₂ W₃ : WeierstrassCurve.Affine F} (C C' : VariableChange F)

namespace Isogeny

/-- The coordinate pullback of a change of variables `C` with `C • W₁ = W₂`: a function on `W₂`
is pulled back along the substitution `x₂ = u⁻²(x₁ - r)`, `y₂ = u⁻³(y₁ - s(x₁ - r) - t)`, the
inverse of the isomorphism of coordinate rings `variableChangeEquiv C h : R(W₁) ≃ R(W₂)`. -/
noncomputable def variableChangePullback (h : C • W₁ = W₂) : CoordinatePullback W₁ W₂ :=
  (IsScalarTower.toAlgHom F W₁.CoordinateRing W₁.FunctionField).comp
    ((variableChangeEquiv C h).symm : W₂.CoordinateRing →ₐ[F] W₁.CoordinateRing)

/-- The pullback of a change of variables is the inverse isomorphism of coordinate rings, read in
the function field. -/
@[simp]
theorem variableChangePullback_apply (h : C • W₁ = W₂) (z : W₂.CoordinateRing) :
    variableChangePullback C h z =
      algebraMap W₁.CoordinateRing W₁.FunctionField ((variableChangeEquiv C h).symm z) :=
  (rfl)

/-- **A change of variables maps the point at infinity to itself**: every function on `W₁` is
already the pullback of a function on `W₂`. -/
theorem mapsInfinity_variableChangePullback (h : C • W₁ = W₂) :
    (variableChangePullback C h).MapsInfinity :=
  CoordinatePullback.mapsInfinity_of_pow _ Nat.one_pos fun z =>
    ⟨variableChangeEquiv C h z, by simp⟩

/-- **The isomorphism `W₁ ⟶ W₂` of a change of variables** `C` with `C • W₁ = W₂`, as an
isogeny. -/
noncomputable def variableChangeIsogeny (h : C • W₁ = W₂) : Isogeny W₁ W₂ where
  pullback := variableChangePullback C h
  mapsInfinity := mapsInfinity_variableChangePullback C h

@[simp]
theorem variableChangeIsogeny_pullback (h : C • W₁ = W₂) :
    (variableChangeIsogeny C h).pullback = variableChangePullback C h :=
  (rfl)

open _root_.WeierstrassCurve.Affine in
/-- **The tautological point of a change of variables**: the coordinate pullback of `C` cuts out the
generic point of `W` moved to `C • W` by the inverse of `pointEquivVariableChange`, the point with
coordinates `(u⁻²(x - r), u⁻³(y - s(x - r) - t))`. -/
@[simp]
theorem tautologicalPoint_variableChangePullback [W₁.IsElliptic] :
    (variableChangePullback C (rfl : C • W₁ = C • W₁)).tautologicalPoint =
      (W₁.pointEquivVariableChange W₁.FunctionField C).symm (genericPoint W₁) := by
  have hinv : (C.baseChange W₁.FunctionField)⁻¹ = C⁻¹.baseChange W₁.FunctionField :=
    (map_inv (VariableChange.mapHom (algebraMap F W₁.FunctionField)) C).symm
  rw [← Point.some_coords (CoordinatePullback.tautologicalPoint_ne_zero _), genericPoint_eq_some,
    pointEquivVariableChange_symm_some]
  simp only [Point.some.injEq, CoordinatePullback.xCoord_tautologicalPoint,
    CoordinatePullback.yCoord_tautologicalPoint, variableChangePullback_apply,
    variableChangeEquiv_symm_of_X, variableChangeEquiv_symm_root]
  rw [hinv]
  simp only [VariableChange.baseChange, VariableChange.map_u, VariableChange.map_r,
    VariableChange.map_s, VariableChange.map_t, Units.coe_map, MonoidHom.coe_ofClass, map_add,
    map_mul, map_pow, ← IsScalarTower.algebraMap_apply, genericX_def, genericY_def,
    CoordinateRing.mk, AdjoinRoot.mk_C, AdjoinRoot.mk_X, and_self]

/-- **The isogenies of changes of variables compose as the changes of variables multiply.** -/
@[simp]
theorem variableChangeIsogeny_comp (h : C • W₁ = W₂) (h' : C' • W₂ = W₃) :
    (variableChangeIsogeny C' h').comp (variableChangeIsogeny C h) =
      variableChangeIsogeny (C' * C) (by rw [mul_smul, h, h']) := by
  refine Isogeny.ext (AlgHom.ext fun z => ?_)
  rw [comp_pullback, AlgHom.comp_apply, variableChangeIsogeny_pullback,
    variableChangePullback_apply, fieldPullback_algebraMap, variableChangeIsogeny_pullback,
    variableChangePullback_apply, variableChangeIsogeny_pullback, variableChangePullback_apply,
    ← variableChangeEquiv_trans C' C h' h, AlgEquiv.symm_trans_apply]

/-- **The identity change of variables gives the identity isogeny.** -/
@[simp]
theorem variableChangeIsogeny_one (h : (1 : VariableChange F) • W₁ = W₁) :
    variableChangeIsogeny 1 h = id W₁ := by
  refine Isogeny.ext (AlgHom.ext fun z => ?_)
  simp

/-- The isogeny of `C⁻¹` is a left inverse of that of `C`. -/
theorem variableChangeIsogeny_inv_comp (h : C • W₁ = W₂) (h' : C⁻¹ • W₂ = W₁) :
    (variableChangeIsogeny C⁻¹ h').comp (variableChangeIsogeny C h) = id W₁ := by
  rw [variableChangeIsogeny_comp C C⁻¹ h h']
  convert variableChangeIsogeny_one (one_smul _ W₁) using 2
  exact inv_mul_cancel C

/-- **The isogeny of a change of variables has degree one**: it is an isomorphism, with inverse
the isogeny of the inverse change of variables. -/
@[simp]
theorem degree_variableChangeIsogeny (h : C • W₁ = W₂) :
    (variableChangeIsogeny C h).degree = 1 :=
  (degree_eq_one_of_comp_eq_id
    (variableChangeIsogeny_inv_comp C h (by rw [← h, inv_smul_smul]))).2

/-- **A change of variables is determined by its isogeny.** -/
theorem variableChangeIsogeny_inj (h : C • W₁ = W₂) (h' : C' • W₁ = W₂) :
    variableChangeIsogeny C h = variableChangeIsogeny C' h' ↔ C = C' := by
  refine ⟨fun he => ?_, fun hC => by subst hC; rfl⟩
  rw [← variableChangeEquiv_inj C C' h h', ← AlgEquiv.symm_symm (variableChangeEquiv C h),
    ← AlgEquiv.symm_symm (variableChangeEquiv C' h')]
  congr 1
  ext z
  exact IsFractionRing.injective W₁.CoordinateRing W₁.FunctionField
    (by simpa using congrArg (fun φ : Isogeny W₁ W₂ => φ.pullback z) he)

/-- **The change of variables `[-1]` gives the negation isogeny**: `negVariableChange` is the
substitution `(x, y) ↦ (x, -y - a₁x - a₃)`, whose pullback is the conjugation of the coordinate
ring. -/
@[simp]
theorem variableChangeIsogeny_negVariableChange (h : W₁.negVariableChange • W₁ = W₁) :
    variableChangeIsogeny W₁.negVariableChange h = negIsogeny W₁ := by
  refine Isogeny.ext (Affine.CoordinateRing.algHom_ext ?_ ?_)
  · simp [variableChangeEquiv_symm_of_X, conj_mk_C]
  · simp [variableChangeEquiv_symm_root, conj_mk_Y, Affine.negPolynomial,
      IsScalarTower.algebraMap_apply F (Polynomial F) W₁.CoordinateRing]
    ring

/-! ### Every isomorphism is a change of variables -/

section Converse

open Polynomial _root_.WeierstrassCurve.Affine

/-- Along an isogeny whose composite with `ψ` is the identity, a function that is the pullback
along `ψ` of `w` pulls back to `w`. -/
private theorem pullback_eq_of_comp_eq_id {φ : Isogeny W₁ W₂} {ψ : Isogeny W₂ W₁}
    (hψφ : ψ.comp φ = id W₁) {w : W₁.CoordinateRing} {a : W₂.CoordinateRing}
    (ha : algebraMap W₂.CoordinateRing W₂.FunctionField a = ψ.pullback w) :
    φ.pullback a = algebraMap W₁.CoordinateRing W₁.FunctionField w := by
  rw [← fieldPullback_algebraMap, ha, ← AlgHom.comp_apply, ← comp_pullback, hψφ, id_pullback,
    CoordinatePullback.id_apply]

/-- The place at infinity of `W₁`, restricted along an isogeny, gives `x₂` a pole. -/
private theorem one_lt_comap_infinityPlace_X (φ : Isogeny W₁ W₂) :
    1 < (W₁.infinityPlace.comap φ.fieldPullback.toRingHom)
      (algebraMap F[X] W₂.FunctionField Polynomial.X) := by
  rw [IsScalarTower.algebraMap_apply F[X] W₂.CoordinateRing, comap_fieldPullback_apply_algebraMap]
  exact one_lt_infinityPlace_pullback_X φ

/-- The coordinate function `x`, in the two forms the pole-order lemmas and the coordinate ring
use. -/
private theorem algebraMap_X (W : WeierstrassCurve.Affine F) :
    algebraMap F[X] W.FunctionField Polynomial.X =
      algebraMap W.CoordinateRing W.FunctionField (AdjoinRoot.of W.polynomial Polynomial.X) := by
  rw [IsScalarTower.algebraMap_apply F[X] W.CoordinateRing, AdjoinRoot.algebraMap_eq]

/-- **An isogeny of degree one out of a curve with integrally closed coordinate ring pulls the
coordinate ring back into the coordinate ring**: the pullback of a function on the affine curve
`W₂` is a function on the affine curve `W₁`. This applies to elliptic `W₁`, by
`WeierstrassCurve.Affine.isIntegrallyClosed_coordinateRing`. -/
theorem exists_algebraMap_eq_pullback_of_degree_eq_one [IsIntegrallyClosed W₁.CoordinateRing]
    (φ : Isogeny W₁ W₂) (hφ : φ.degree = 1)
    (z : W₂.CoordinateRing) :
    ∃ w : W₁.CoordinateRing, algebraMap W₁.CoordinateRing W₁.FunctionField w = φ.pullback z := by
  -- The inverse `ψ` maps infinity to infinity, so `z` is integral over `R(W₁)` acting through
  -- `ψ`. Carried across `φ`, which undoes `ψ`, this makes `φ z` integral over `R(W₁)`, and that
  -- ring is integrally closed.
  obtain ⟨ψ, hψφ, -⟩ := exists_comp_eq_id_and_comp_eq_id_of_degree_eq_one φ hφ
  -- `φ ∘ ψ`, read on functions, is the inclusion of `R(W₁)` in its function field
  have hcomp : φ.fieldPullback.toRingHom.comp ψ.pullback.toRingHom =
      algebraMap W₁.CoordinateRing W₁.FunctionField := RingHom.ext fun w => by
    simpa using congrArg (fun χ : Isogeny W₁ W₁ => χ.pullback w) hψφ
  obtain ⟨p, hp, hpz⟩ := (CoordinatePullback.mapsInfinity_iff _).mp ψ.mapsInfinity z
  have hint : IsIntegral W₁.CoordinateRing (φ.pullback z) := by
    refine ⟨p, hp, ?_⟩
    rw [RingHom.algebraMap_toAlgebra] at hpz
    have h := congrArg φ.fieldPullback.toRingHom hpz
    rwa [Polynomial.hom_eval₂, map_zero, hcomp, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
      fieldPullback_algebraMap] at h
  exact IsIntegrallyClosed.isIntegral_iff.mp hint

variable [W₁.IsElliptic] [W₂.IsElliptic]

/-- A degree-one isogeny pulls `x` back to `αx + β` with `α ≠ 0`. The pullback `f` of `x₂` lies in
the coordinate ring and has a pole at infinity, so its pole has order at least two; conversely `x₁`
is the pullback of a function `a` with a pole, whose pole is at least that of `x₂`. So `f` has a
pole of order exactly two. -/
private theorem exists_pullback_X_eq_of_degree_eq_one (φ : Isogeny W₁ W₂) (hφ : φ.degree = 1) :
    ∃ α β : F, α ≠ 0 ∧ φ.pullback (AdjoinRoot.of W₂.polynomial Polynomial.X) =
      algebraMap W₁.CoordinateRing W₁.FunctionField (algebraMap F W₁.CoordinateRing α *
        AdjoinRoot.of W₁.polynomial Polynomial.X + algebraMap F W₁.CoordinateRing β) := by
  set v₂ := W₁.infinityPlace.comap φ.fieldPullback.toRingHom
  have hv (w : W₂.CoordinateRing) :
      v₂ (algebraMap W₂.CoordinateRing W₂.FunctionField w) = W₁.infinityPlace (φ.pullback w) :=
    comap_fieldPullback_apply_algebraMap φ _ w
  have := W₁.isIntegrallyClosed_coordinateRing
  have := W₂.isIntegrallyClosed_coordinateRing
  have hx₁ := one_lt_infinityPlace_X W₁
  obtain ⟨f, hf⟩ := exists_algebraMap_eq_pullback_of_degree_eq_one φ hφ
    (AdjoinRoot.of W₂.polynomial Polynomial.X)
  obtain ⟨ψ, hψφ, -⟩ := exists_comp_eq_id_and_comp_eq_id_of_degree_eq_one φ hφ
  obtain ⟨a, ha⟩ := exists_algebraMap_eq_pullback_of_degree_eq_one ψ
    (degree_eq_one_of_comp_eq_id hψφ).1 (AdjoinRoot.of W₁.polynomial Polynomial.X)
  have ha' := pullback_eq_of_comp_eq_id hψφ ha
  have hf₁ : 1 < W₁.infinityPlace (algebraMap _ _ f) := by
    rw [hf, ← hv, ← algebraMap_X]
    exact one_lt_comap_infinityPlace_X φ
  -- the pole of `f` is at most that of `x₁`, the pullback of `a`
  have hfx : W₁.infinityPlace (algebraMap _ _ f) ≤
      W₁.infinityPlace (algebraMap W₁.CoordinateRing W₁.FunctionField
        (AdjoinRoot.of W₁.polynomial Polynomial.X)) := by
    have h := val_X_le_of_one_lt v₂ (one_lt_comap_infinityPlace_X φ) (z := a)
      (by rw [hv, ha', ← algebraMap_X]; exact hx₁)
    rwa [algebraMap_X, hv, hv, ha', ← hf] at h
  obtain ⟨α, β, hfαβ⟩ := exists_eq_of_val_lt_val_mk_Y _ hx₁ (z := f)
    (hfx.trans_lt (by rw [← algebraMap_X]; exact val_X_lt_val_mk_Y _ hx₁))
  -- `α ≠ 0`, since `f` is not constant
  refine ⟨α, β, fun hα => ?_, by rw [← hf, hfαβ]⟩
  rw [hfαβ, hα, map_zero, zero_mul, zero_add, ← IsScalarTower.algebraMap_apply] at hf₁
  exact hf₁.not_ge (Valuation.IsTrivialOn.valuation_algebraMap_le_one _ β)

/-- A degree-one isogeny pulls `y` back to `γy + δx + ε`. The pullback `g` of `y₂` lies in the
coordinate ring; `y₁` is the pullback of a function `b`, and if the pole of `b` were less than that
of `y₂`, then `b` would be `α'x₂ + β'` and `y₁` a combination of `x₁` and `1`. So the pole of `g`
is at most that of `y₁`. -/
private theorem exists_pullback_root_eq_of_degree_eq_one (φ : Isogeny W₁ W₂) (hφ : φ.degree = 1) :
    ∃ γ δ ε : F, φ.pullback (AdjoinRoot.root W₂.polynomial) =
      algebraMap W₁.CoordinateRing W₁.FunctionField (algebraMap F W₁.CoordinateRing γ *
        AdjoinRoot.root W₁.polynomial + algebraMap F W₁.CoordinateRing δ *
          AdjoinRoot.of W₁.polynomial Polynomial.X + algebraMap F W₁.CoordinateRing ε) := by
  set v₂ := W₁.infinityPlace.comap φ.fieldPullback.toRingHom
  have hv (w : W₂.CoordinateRing) :
      v₂ (algebraMap W₂.CoordinateRing W₂.FunctionField w) = W₁.infinityPlace (φ.pullback w) :=
    comap_fieldPullback_apply_algebraMap φ _ w
  have := W₁.isIntegrallyClosed_coordinateRing
  have := W₂.isIntegrallyClosed_coordinateRing
  obtain ⟨g, hg⟩ := exists_algebraMap_eq_pullback_of_degree_eq_one φ hφ
    (AdjoinRoot.root W₂.polynomial)
  obtain ⟨ψ, hψφ, -⟩ := exists_comp_eq_id_and_comp_eq_id_of_degree_eq_one φ hφ
  obtain ⟨b, hb⟩ := exists_algebraMap_eq_pullback_of_degree_eq_one ψ
    (degree_eq_one_of_comp_eq_id hψφ).1 (AdjoinRoot.root W₁.polynomial)
  have hb' := pullback_eq_of_comp_eq_id hψφ hb
  have hgy : W₁.infinityPlace (algebraMap _ _ g) ≤ W₁.infinityPlace
      (algebraMap W₁.CoordinateRing W₁.FunctionField (AdjoinRoot.root W₁.polynomial)) := by
    by_contra hlt
    rw [not_le, hg, ← hv, ← hb', ← hv, ← AdjoinRoot.mk_X] at hlt
    obtain ⟨α', β', rfl⟩ :=
      exists_eq_of_val_lt_val_mk_Y v₂ (one_lt_comap_infinityPlace_X φ) (z := b) hlt
    obtain ⟨α, β, -, hX⟩ := exists_pullback_X_eq_of_degree_eq_one φ hφ
    -- then `y₁ = α'(αx₁ + β) + β'` in `R(W₁)`
    have hyb : AdjoinRoot.root W₁.polynomial = algebraMap F W₁.CoordinateRing (α' * α) *
        AdjoinRoot.of W₁.polynomial Polynomial.X +
          algebraMap F W₁.CoordinateRing (α' * β + β') := by
      apply IsFractionRing.injective W₁.CoordinateRing W₁.FunctionField
      rw [← hb', map_add, map_mul, AlgHom.commutes, AlgHom.commutes, hX]
      simp only [map_add, map_mul, ← IsScalarTower.algebraMap_apply]
      ring
    -- which contradicts the linear independence of `x₁`, `y₁` and `1`
    have hli := Fintype.linearIndependent_iff.mp
      (CoordinateRing.linearIndependent_X_root_one (W := W₁)) ![α' * α, -1, α' * β + β'] (by
        rw [Fin.sum_univ_three]
        simp only [Matrix.cons_val, Algebra.smul_def, mul_one, map_neg, map_one]
        rw [hyb]
        ring)
    exact absurd (hli 1) (by simp)
  obtain ⟨δ, ε, γ, hgγ⟩ := exists_eq_of_val_le_val_mk_Y _ (one_lt_infinityPlace_X W₁) (z := g)
    (by rwa [AdjoinRoot.mk_X])
  exact ⟨γ, δ, ε, by rw [← hg, hgγ]⟩

/-- **An isogeny of degree one between elliptic curves is a change of variables** (Silverman
III.3.1(b)): there is a change of variables `C` with `C • W₁ = W₂` whose isogeny is `φ`. -/
theorem exists_variableChangeIsogeny_eq_of_degree_eq_one (φ : Isogeny W₁ W₂)
    (hφ : φ.degree = 1) :
    ∃ (C : VariableChange F) (h : C • W₁ = W₂), variableChangeIsogeny C h = φ := by
  obtain ⟨α, β, hα, hX⟩ := exists_pullback_X_eq_of_degree_eq_one φ hφ
  obtain ⟨γ, δ, ε, hY⟩ := exists_pullback_root_eq_of_degree_eq_one φ hφ
  -- the substituted pair satisfies the equation of `W₂` over `R(W₁)`, read in `K(W₁)`
  have heq : (W₂⁄W₁.CoordinateRing).toAffine.Equation
      (algebraMap F W₁.CoordinateRing α * AdjoinRoot.of W₁.polynomial Polynomial.X
        + algebraMap F W₁.CoordinateRing β)
      (algebraMap F W₁.CoordinateRing γ * AdjoinRoot.root W₁.polynomial
        + algebraMap F W₁.CoordinateRing δ * AdjoinRoot.of W₁.polynomial Polynomial.X
        + algebraMap F W₁.CoordinateRing ε) := by
    have h := CoordinateRing.equation_of_algHom φ.pullback
    rw [hX, hY] at h
    refine (map_equation (W := (W₂⁄W₁.CoordinateRing).toAffine)
      (IsFractionRing.injective W₁.CoordinateRing W₁.FunctionField) _ _).mp ?_
    convert h using 2
    exact WeierstrassCurve.map_baseChange (W := W₂)
      (IsScalarTower.toAlgHom F W₁.CoordinateRing W₁.FunctionField)
  obtain ⟨D, hD, hu2, hu3, hr, hs, ht⟩ :=
    exists_variableChange_of_equation (isUnit_iff_ne_zero.mpr hα) heq
  -- `φ` is the isogeny of `D⁻¹`, whose pullback is the substitution of `D`
  have h : D⁻¹ • W₁ = W₂ := by rw [← hD, inv_smul_smul]
  have he : (variableChangeEquiv D⁻¹ h).symm = variableChangeEquiv D hD := by
    rw [variableChangeEquiv_symm D⁻¹ h (by rwa [inv_inv]), variableChangeEquiv_inj]
    exact inv_inv D
  refine ⟨D⁻¹, h, Isogeny.ext (CoordinateRing.algHom_ext ?_ ?_)⟩
  · rw [variableChangeIsogeny_pullback, variableChangePullback_apply, he,
      variableChangeEquiv_of_X, hX, ← hu2, ← hr, map_pow]
  · rw [variableChangeIsogeny_pullback, variableChangePullback_apply, he,
      variableChangeEquiv_root, hY, ← hu3, ← hs, ← ht, map_mul, map_pow, map_pow]

end Converse

namespace Hom

variable (W : WeierstrassCurve.Affine F)

/-- **The automorphisms of `W` given by changes of variables.** A change of variables `C` fixing
`W` is sent to the isogeny `variableChangeIsogeny C : W ⟶ W`, an automorphism of `W` fixing the
point at infinity, hence a unit of the endomorphism monoid. -/
noncomputable def autGroupToUnits : W.autGroup →* (Hom W W)ˣ :=
  MonoidHom.toHomUnits
    { toFun := fun C => ofIsogeny (variableChangeIsogeny C (MulAction.mem_stabilizer_iff.mp C.2))
      map_one' := by
        simp only [OneMemClass.coe_one, variableChangeIsogeny_one, one_def, id_def]
      map_mul' := fun C C' => by
        simp only [Subgroup.coe_mul, mul_def, ofIsogeny_comp_ofIsogeny,
          variableChangeIsogeny_comp] }

/-- The automorphism of `W` attached to a change of variables `C` fixing `W` is the isogeny of
`C`. -/
@[simp]
theorem coe_autGroupToUnits (C : W.autGroup) :
    (autGroupToUnits W C : Hom W W) =
      ofIsogeny (variableChangeIsogeny C (MulAction.mem_stabilizer_iff.mp C.2)) :=
  (rfl)

/-- **Distinct changes of variables fixing `W` give distinct automorphisms of `W`.** -/
theorem autGroupToUnits_injective : Function.Injective (autGroupToUnits W) := fun C C' hC => by
  have h := congr(($hC : Hom W W))
  rw [coe_autGroupToUnits, coe_autGroupToUnits, ofIsogeny_injective.eq_iff,
    variableChangeIsogeny_inj] at h
  exact Subtype.ext h

/-- **Every automorphism of an elliptic curve fixing the point at infinity is a change of
variables**: the homomorphism `autGroupToUnits` is onto. -/
theorem autGroupToUnits_surjective [W.IsElliptic] : Function.Surjective (autGroupToUnits W) :=
  fun U => by
  obtain ⟨φ, hφ⟩ := (U : Hom W W).eq_zero_or_exists_ofIsogeny.resolve_left U.ne_zero
  have hdeg : φ.degree = 1 := by rw [← degree_ofIsogeny, ← hφ]; exact degree_coe_units U
  obtain ⟨C, h, rfl⟩ := exists_variableChangeIsogeny_eq_of_degree_eq_one φ hdeg
  exact ⟨⟨C, MulAction.mem_stabilizer_iff.mpr h⟩, Units.ext (by rw [coe_autGroupToUnits, hφ])⟩

/-- **The automorphism group of an elliptic curve** (Silverman III.10): the changes of variables
fixing `W`, its stabiliser `W.autGroup` in `VariableChange F`, are exactly the automorphisms of
`W` fixing the point at infinity, the units of the endomorphism monoid `Hom W W`. -/
noncomputable def autGroupEquivUnits [W.IsElliptic] : W.autGroup ≃* (Hom W W)ˣ :=
  MulEquiv.ofBijective (autGroupToUnits W)
    ⟨autGroupToUnits_injective W, autGroupToUnits_surjective W⟩

@[simp]
theorem autGroupEquivUnits_apply [W.IsElliptic] (C : W.autGroup) :
    autGroupEquivUnits W C = autGroupToUnits W C :=
  (rfl)

end Hom

end Isogeny

end TauCeti

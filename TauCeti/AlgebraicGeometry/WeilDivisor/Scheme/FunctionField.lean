/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Scheme.Place.Proper
public import TauCeti.AlgebraicGeometry.WeilDivisor.Scheme.Degree
public import TauCeti.AlgebraicGeometry.WeilDivisor.Scheme.Place
public import TauCeti.AlgebraicGeometry.WeilDivisor.Scheme.Principal
public import TauCeti.FieldTheory.FunctionField.Divisor.Principal

/-!
# Divisors on a proper curve and divisors of its function field

Let `X` be a separated integral curve over a field `k`. If every codimension-one local ring is a
discrete valuation ring and the structure morphism satisfies the existence part of the valuative
criterion, codimension-one points of `X` are equivalent to normalized places of `k(X)`. Reindexing
finite formal sums along this equivalence identifies scheme-theoretic Weil divisors with divisors
of the function field.

This file records the characteristic properties of that identification. It preserves point
divisors, coefficientwise order and effectivity, the residue-degree-weighted degree, and principal
divisors. Consequently it also preserves linear equivalence. These comparisons allow the
scheme-theoretic divisor and principal-parts constructions to use the function-field divisor API.

## Main declarations

* `SchemeWeilDivisor.equivFunctionFieldDivisor`: the additive equivalence between divisors on
  `X` and divisors of `k(X)`;
* `SchemeWeilDivisor.degree_equivFunctionFieldDivisor`: compatibility with divisor degree;
* `SchemeWeilDivisor.equivFunctionFieldDivisor_principalDivisor`: compatibility with principal
  divisors;
* `SchemeWeilDivisor.linearlyEquivalent_equivFunctionFieldDivisor_iff`: compatibility with
  linear equivalence.

## References

* R. Hartshorne, *Algebraic Geometry*, Chapter I, Section 6, and Chapter II, Section 6.
* H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., GTM 254, Springer, 2009,
  Section I.4.
-/

public section

open Order _root_.AlgebraicGeometry

namespace TauCeti.AlgebraicGeometry

universe u

noncomputable section

namespace SchemeWeilDivisor

variable {k : Type u} [Field k] {X : Scheme.{u}} [IsIntegral X] [X.Over (Spec (.of k))]
  [∀ x : CodimensionOnePoint X, IsDiscreteValuationRing (X.presheaf.stalk (x : X))]
  [X.IsSeparated]

/-- Reindex scheme-theoretic Weil divisors along the equivalence between codimension-one points
and normalized places of the function field. -/
def equivFunctionFieldDivisor
    (hex : ValuativeCriterion.Existence (X ↘ Spec (.of k)))
    (hdim : ∀ x : X, coheight x ≤ 1) :
    SchemeWeilDivisor X ≃+ Divisor k X.functionField :=
  Finsupp.domCongr (CodimensionOnePoint.equivPlace hex hdim)

/-- The coefficient after reindexing is the coefficient at the corresponding codimension-one
point. -/
@[simp]
theorem coeff_equivFunctionFieldDivisor
    (hex : ValuativeCriterion.Existence (X ↘ Spec (.of k)))
    (hdim : ∀ x : X, coheight x ≤ 1) (D : SchemeWeilDivisor X)
    (P : Place k X.functionField) :
    WeilDivisor.coeff (equivFunctionFieldDivisor hex hdim D) P =
      WeilDivisor.coeff D ((CodimensionOnePoint.equivPlace hex hdim).symm P) :=
  by
    simp only [equivFunctionFieldDivisor, Finsupp.domCongr_apply, WeilDivisor.coeff,
      Finsupp.equivMapDomain_apply]

/-- The coefficient at the place attached to `x` is the coefficient at `x`. -/
@[simp]
theorem coeff_equivFunctionFieldDivisor_toPlace
    (hex : ValuativeCriterion.Existence (X ↘ Spec (.of k)))
    (hdim : ∀ x : X, coheight x ≤ 1) (D : SchemeWeilDivisor X)
    (x : CodimensionOnePoint X) :
    WeilDivisor.coeff (equivFunctionFieldDivisor hex hdim D)
        (X.toPlace (k := k) (x : X)) = WeilDivisor.coeff D x := by
  have hx : CodimensionOnePoint.equivPlace (k := k) hex hdim x =
      X.toPlace (k := k) (x : X) :=
    CodimensionOnePoint.equivPlace_apply (k := k) hex hdim x
  rw [coeff_equivFunctionFieldDivisor, ← hx,
    (CodimensionOnePoint.equivPlace hex hdim).symm_apply_apply]

/-- Reindexing sends the prime divisor at a codimension-one point to the divisor of its place. -/
@[simp]
theorem equivFunctionFieldDivisor_ofPoint
    (hex : ValuativeCriterion.Existence (X ↘ Spec (.of k)))
    (hdim : ∀ x : X, coheight x ≤ 1) (x : CodimensionOnePoint X) :
    equivFunctionFieldDivisor hex hdim (WeilDivisor.ofPoint x) =
      WeilDivisor.ofPoint (X.toPlace (k := k) (x : X)) := by
  have hx : CodimensionOnePoint.equivPlace (k := k) hex hdim x =
      X.toPlace (k := k) (x : X) :=
    CodimensionOnePoint.equivPlace_apply (k := k) hex hdim x
  apply WeilDivisor.ext
  intro P
  rw [coeff_equivFunctionFieldDivisor, ← hx]
  by_cases hP : (CodimensionOnePoint.equivPlace hex hdim).symm P = x
  · have hP' : P = CodimensionOnePoint.equivPlace hex hdim x := by
      rw [← (CodimensionOnePoint.equivPlace hex hdim).apply_symm_apply P, hP]
    subst P
    rw [(CodimensionOnePoint.equivPlace hex hdim).symm_apply_apply,
      WeilDivisor.coeff_ofPoint_self, WeilDivisor.coeff_ofPoint_self]
  · have hP' : P ≠ CodimensionOnePoint.equivPlace hex hdim x := by
      intro h
      apply hP
      rw [h, (CodimensionOnePoint.equivPlace hex hdim).symm_apply_apply]
    rw [WeilDivisor.coeff_ofPoint_of_ne hP, WeilDivisor.coeff_ofPoint_of_ne hP']

/-- The divisor equivalence is the formal pushforward along the point-to-place map. -/
theorem equivFunctionFieldDivisor_apply
    (hex : ValuativeCriterion.Existence (X ↘ Spec (.of k)))
    (hdim : ∀ x : X, coheight x ≤ 1) (D : SchemeWeilDivisor X) :
    equivFunctionFieldDivisor hex hdim D =
      WeilDivisor.pushforward (fun x : CodimensionOnePoint X ↦
        X.toPlace (k := k) (x : X)) D := by
  rw [equivFunctionFieldDivisor, Finsupp.domCongr_apply,
    Finsupp.equivMapDomain_eq_mapDomain, WeilDivisor.pushforward_apply]
  congr 2
  funext x
  exact CodimensionOnePoint.equivPlace_apply hex hdim x

/-- Reindexing along the point-to-place equivalence preserves coefficientwise inequalities. -/
@[simp]
theorem equivFunctionFieldDivisor_le_iff
    (hex : ValuativeCriterion.Existence (X ↘ Spec (.of k)))
    (hdim : ∀ x : X, coheight x ≤ 1) {D E : SchemeWeilDivisor X} :
    equivFunctionFieldDivisor hex hdim D ≤ equivFunctionFieldDivisor hex hdim E ↔ D ≤ E := by
  simp only [WeilDivisor.le_iff, coeff_equivFunctionFieldDivisor]
  exact (CodimensionOnePoint.equivPlace hex hdim).symm.forall_congr
    (fun _ ↦ Iff.rfl)

/-- Reindexing along the point-to-place equivalence preserves effectivity. -/
@[simp]
theorem isEffective_equivFunctionFieldDivisor_iff
    (hex : ValuativeCriterion.Existence (X ↘ Spec (.of k)))
    (hdim : ∀ x : X, coheight x ≤ 1) {D : SchemeWeilDivisor X} :
    WeilDivisor.IsEffective (equivFunctionFieldDivisor hex hdim D) ↔
      WeilDivisor.IsEffective D := by
  rw [WeilDivisor.isEffective_iff_zero_le, WeilDivisor.isEffective_iff_zero_le,
    ← map_zero (equivFunctionFieldDivisor hex hdim), equivFunctionFieldDivisor_le_iff]

/-- The function-field degree of a reindexed divisor is its scheme-theoretic relative degree. -/
@[simp]
theorem degree_equivFunctionFieldDivisor
    (hex : ValuativeCriterion.Existence (X ↘ Spec (.of k)))
    (hdim : ∀ x : X, coheight x ≤ 1) (D : SchemeWeilDivisor X) :
    Divisor.degree (equivFunctionFieldDivisor hex hdim D) =
      relativeDegree (X ↘ Spec (.of k)) D := by
  induction D using Finsupp.induction with
  | zero => simp
  | single_add x n D hx hn ih =>
      have hsingle :
          Divisor.degree (equivFunctionFieldDivisor hex hdim (Finsupp.single x n)) =
            relativeDegree (X ↘ Spec (.of k)) (Finsupp.single x n) := by
        rw [WeilDivisor.single_eq_zsmul_ofPoint, map_zsmul, map_zsmul,
          map_zsmul, equivFunctionFieldDivisor_ofPoint, Divisor.degree_ofPoint,
          relativeDegree_ofPoint]
        congr 1
        exact_mod_cast X.toPlace_degree_eq_residueDegree (k := k) (x : X)
      calc
        Divisor.degree
              (equivFunctionFieldDivisor hex hdim (Finsupp.single x n + D)) =
            Divisor.degree (equivFunctionFieldDivisor hex hdim (Finsupp.single x n)) +
              Divisor.degree (equivFunctionFieldDivisor hex hdim D) := by rw [map_add, map_add]
        _ = relativeDegree (X ↘ Spec (.of k)) (Finsupp.single x n) +
              relativeDegree (X ↘ Spec (.of k)) D := by rw [hsingle, ih]
        _ = relativeDegree (X ↘ Spec (.of k)) (Finsupp.single x n + D) :=
          (map_add _ _ _).symm

variable [IsNoetherian X]

/-- The point-to-place divisor equivalence intertwines the two order systems. -/
theorem equivFunctionFieldDivisor_principalHom
    (hex : ValuativeCriterion.Existence (X ↘ Spec (.of k)))
    (hdim : ∀ x : X, coheight x ≤ 1) (hF : IsFunctionField k X.functionField) :
    (equivFunctionFieldDivisor hex hdim).toAddMonoidHom.comp
        (WeilDivisor.OrderSystem.ofScheme X).principalHom =
      (Place.orderSystem hF).principalHom := by
  apply AddMonoidHom.ext
  intro g
  apply WeilDivisor.ext
  intro P
  obtain ⟨x, hx⟩ := (CodimensionOnePoint.equivPlace hex hdim).surjective P
  have he : CodimensionOnePoint.equivPlace (k := k) hex hdim x =
      X.toPlace (k := k) (x : X) :=
    CodimensionOnePoint.equivPlace_apply (k := k) hex hdim x
  simp only [AddMonoidHom.comp_apply, AddEquiv.coe_toAddMonoidHom,
    WeilDivisor.OrderSystem.principalHom_apply]
  subst P
  rw [he, coeff_equivFunctionFieldDivisor_toPlace,
    WeilDivisor.OrderSystem.coeff_principalDivisor,
    WeilDivisor.OrderSystem.coeff_principalDivisor,
    WeilDivisor.OrderSystem.ofScheme_ord, ← ofMul_toMul g,
    Place.orderSystem_ord, orderAt_apply]
  rw [toMul_ofMul]
  exact (CodimensionOnePoint.toPlace_ord (k := k) x
    ((Additive.toMul g : X.functionFieldˣ) : X.functionField)).symm

/-- Scheme-theoretic principal divisors become the corresponding function-field principal
divisors under the point-to-place equivalence. -/
@[simp]
theorem equivFunctionFieldDivisor_principalDivisor
    (hex : ValuativeCriterion.Existence (X ↘ Spec (.of k)))
    (hdim : ∀ x : X, coheight x ≤ 1) (hF : IsFunctionField k X.functionField)
    (g : Additive X.functionFieldˣ) :
    equivFunctionFieldDivisor hex hdim
        ((WeilDivisor.OrderSystem.ofScheme X).principalDivisor g) =
      (Place.orderSystem hF).principalDivisor g := by
  -- Expose only the application of the `toAddMonoidHom` wrapper so that the homomorphism
  -- comparison above rewrites the two principal-divisor maps.
  change (equivFunctionFieldDivisor hex hdim).toAddMonoidHom
      ((WeilDivisor.OrderSystem.ofScheme X).principalDivisor g) = _
  rw [← WeilDivisor.OrderSystem.principalHom_apply,
    ← WeilDivisor.OrderSystem.principalHom_apply, ← AddMonoidHom.comp_apply,
    equivFunctionFieldDivisor_principalHom]

/-- Linear equivalence of scheme divisors is exactly linear equivalence of the corresponding
function-field divisors. -/
@[simp]
theorem linearlyEquivalent_equivFunctionFieldDivisor_iff
    (hex : ValuativeCriterion.Existence (X ↘ Spec (.of k)))
    (hdim : ∀ x : X, coheight x ≤ 1) (hF : IsFunctionField k X.functionField)
    {D E : SchemeWeilDivisor X} :
    (Place.orderSystem hF).LinearlyEquivalent
        (equivFunctionFieldDivisor hex hdim D)
        (equivFunctionFieldDivisor hex hdim E) ↔
      (WeilDivisor.OrderSystem.ofScheme X).LinearlyEquivalent D E := by
  rw [WeilDivisor.OrderSystem.linearlyEquivalent_iff_exists_principalDivisor,
    WeilDivisor.OrderSystem.linearlyEquivalent_iff_exists_principalDivisor]
  constructor
  · rintro ⟨g, hg⟩
    refine ⟨g, (equivFunctionFieldDivisor hex hdim).injective ?_⟩
    rw [map_sub, equivFunctionFieldDivisor_principalDivisor]
    exact hg
  · rintro ⟨g, hg⟩
    refine ⟨g, ?_⟩
    rw [← equivFunctionFieldDivisor_principalDivisor, ← map_sub, hg]

end SchemeWeilDivisor

end

end TauCeti.AlgebraicGeometry

/-
Copyright (c) 2026 Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.RepresentationTheory.FiniteIndex

/-!
# Restricting to a finite-index subgroup and coming back

Let `S` be a subgroup of finite index in a group `G`. Coinduction from `S` to `G` is right adjoint
to restriction (`Rep.resCoindAdjunction`), and, because the index is finite, also left adjoint to
it (`Rep.coindResAdjunction`). For a `G`-representation `A` this gives two maps

`A ⟶ Coind_S^G(Res_S A) ⟶ A`,

the unit of the first adjunction, `a ↦ (g ↦ g • a)`, and the counit of the second, the *trace*
`f ↦ ∑ g⁻¹ • f g` over representatives `g` of the right cosets of `S`. Their composite is
multiplication by the index `[G : S]`. This is the identity behind the normalization
`cor ∘ res = [G : S]` of group-cohomological corestriction.

## Main results

* `Subgroup.coindResAdjunction_counit_app_hom_apply`: the trace sums `g⁻¹ • f g` over the
  chosen representatives `g` of the right cosets of `S`.
* `TauCeti.Rep.resCoindAdjunction_unit_app_comp_coindResAdjunction_counit_app`: the composite of
  the unit and the trace is `[G : S] • 𝟙 A`.

## References

* K. S. Brown, *Cohomology of Groups*, Graduate Texts in Mathematics 87, Springer (1982),
  Chapter III, §9.
-/

public section

open CategoryTheory

namespace Subgroup

open Rep

universe u

variable {k G : Type u} [CommRing k] [Group G] (S : Subgroup G) [S.FiniteIndex]

attribute [local instance] Subgroup.fintypeQuotientOfFiniteIndex

open Classical in
/-- **The trace as a sum over right cosets.** For a finite-index subgroup `S ≤ G`, the counit
`Coind_S^G(Res_S A) ⟶ A` of coinduction–restriction sends `f` to `∑ g⁻¹ • f g`, the sum over the
representatives `g = q.out` of the right cosets `q = S g`. -/
theorem coindResAdjunction_counit_app_hom_apply (A : Rep.{u} k G)
    (f : coind S.subtype (res S.subtype A)) :
    ((coindResAdjunction.{u, u, u} k S).counit.app A).hom f =
      ∑ q : Quotient (QuotientGroup.rightRel S), A.ρ (q.out)⁻¹ (f.1 q.out) := by
  -- The trace evaluated on a class `⟦g ⊗ b⟧` is `g⁻¹ • b`.
  have hcounit (g : G) (b : A) : ((indResAdjunction k S.subtype).counit.app A).hom
      (Representation.IndV.mk S.subtype (res S.subtype A).ρ g b) = A.ρ g⁻¹ b := by
    simp [indResAdjunction, indResHomEquiv]
  have h : (indCoindIso (res S.subtype A)).inv.hom f = coindToInd (res S.subtype A) f :=
    LinearMap.congr_fun (indCoindIso_inv_hom_toLinearMap (res S.subtype A)) _
  rw [coindResAdjunction_counit_app, Rep.hom_comp, Representation.IntertwiningMap.comp_apply, h,
    coindToInd_apply, map_sum]
  refine Finset.sum_congr rfl fun q _ => ?_
  conv_lhs => rw [← Quotient.out_eq q]
  rw [Quotient.liftOn_mk, hcounit]

end Subgroup

namespace TauCeti.Rep

open _root_.Rep

universe u

variable {k G : Type u} [CommRing k] [Group G] (S : Subgroup G) [S.FiniteIndex]

attribute [local instance] Subgroup.fintypeQuotientOfFiniteIndex

open Classical in
/-- **Unit followed by trace is the index.** For a finite-index subgroup `S ≤ G`, the unit
`A ⟶ Coind_S^G(Res_S A)` of restriction–coinduction followed by the counit
`Coind_S^G(Res_S A) ⟶ A` of coinduction–restriction is multiplication by `[G : S]`. -/
theorem resCoindAdjunction_unit_app_comp_coindResAdjunction_counit_app
    (A : Rep.{u} k G) :
    (resCoindAdjunction k S.subtype).unit.app A ≫ (coindResAdjunction.{u, u, u} k S).counit.app A =
      S.index • 𝟙 A := by
  rw [← Nat.cast_smul_eq_nsmul k]
  refine Rep.hom_ext (Representation.IntertwiningMap.ext (LinearMap.ext fun a => ?_))
  simp only [Representation.IntertwiningMap.toLinearMap_apply, coindResAdjunction_counit_app,
    Rep.hom_comp, Representation.IntertwiningMap.comp_apply]
  have h : (Hom.hom (indCoindIso (res S.subtype A)).inv)
      ((Hom.hom ((resCoindAdjunction k S.subtype).unit.app A)) a) =
      coindToInd (res S.subtype A) ((Hom.hom ((resCoindAdjunction k S.subtype).unit.app A)) a) :=
    LinearMap.congr_fun (indCoindIso_inv_hom_toLinearMap (res S.subtype A)) _
  -- The trace evaluated on a class `⟦g ⊗ b⟧` is `g⁻¹ • b`; the unit evaluated at `g` is `g • a`.
  have hcounit (g : G) (b : A) : ((indResAdjunction k S.subtype).counit.app A).hom
      (Representation.IndV.mk S.subtype (res S.subtype A).ρ g b) = A.ρ g⁻¹ b := by
    simp [indResAdjunction, indResHomEquiv]
  have hunit (g : G) : (((resCoindAdjunction k S.subtype).unit.app A).hom a).1 g = A.ρ g a := rfl
  rw [h, coindToInd_apply, map_sum]
  refine (Finset.sum_congr rfl (g := fun _ => a) fun q _ => ?_).trans ?_
  · induction q using Quotient.inductionOn with
    | h g =>
      rw [Quotient.liftOn_mk, hcounit, hunit, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel,
        map_one, Module.End.one_apply]
  · rw [Finset.sum_const, Finset.card_univ, QuotientGroup.card_quotient_rightRel, Rep.smul_hom,
      Representation.IntertwiningMap.smul_apply, Subgroup.index_eq_card, Nat.card_eq_fintype_card,
      Nat.cast_smul_eq_nsmul]
    -- `a` lives in `(𝟭 _).obj A`, so `Rep.hom_id` does not match syntactically; the identity
    -- morphism acts as the identity by definition.
    rfl

end TauCeti.Rep

/-
Copyright (c) 2026 Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.RepresentationTheory.FiniteIndex
public import TauCeti.RepresentationTheory.RelativeNorm

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

Because the index is finite, induction `Ind_S^G` is identified with coinduction
(`Rep.indCoindIso`), and the same identity holds for the unit `A ⟶ Ind_S^G(Res_S A)` of
restriction–induction followed by the counit `Ind_S^G(Res_S A) ⟶ A` of induction–restriction. That
form is behind the normalization of the transfer in group homology.

## Main results

* `Subgroup.coindResAdjunction_counit_app_hom_apply`: the trace sums `g⁻¹ • f g` over the
  chosen representatives `g` of the right cosets of `S`.
* `TauCeti.Rep.resCoindAdjunction_unit_app_comp_coindResAdjunction_counit_app`: the composite of
  the unit and the trace is `[G : S] • 𝟙 A`.
* `TauCeti.Rep.resIndAdjunction_unit_app_comp_indResAdjunction_counit_app`: the same identity
  with coinduction replaced by induction, through Mathlib's identification `Rep.indCoindIso`.
* `Rep.coinvariantsMk_coindToInd_unit`: in the `G`-coinvariants of `Ind_S^G(Res_S A)`, the
  unit `A ⟶ Ind_S^G(Res_S A)` sends `a` to the class of `1 ⊗ ∑_{q ∈ G ⧸ S} q⁻¹ • a`, the relative
  transfer `Representation.relTransfer`.

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

open Classical in
/-- **Unit followed by counit is the index, for induction.** For a finite-index subgroup `S ≤ G`,
the unit `A ⟶ Ind_S^G(Res_S A)` of restriction–induction followed by the counit
`Ind_S^G(Res_S A) ⟶ A` of induction–restriction is multiplication by `[G : S]`. -/
@[reassoc]
theorem resIndAdjunction_unit_app_comp_indResAdjunction_counit_app (A : Rep.{u} k G) :
    (resIndAdjunction.{u, u, u} k S).unit.app A ≫ (indResAdjunction k S.subtype).counit.app A =
      S.index • 𝟙 A := by
  rw [resIndAdjunction_unit_app, Category.assoc, ← coindResAdjunction_counit_app]
  exact resCoindAdjunction_unit_app_comp_coindResAdjunction_counit_app S A

end TauCeti.Rep

/-! ### The unit of restriction–induction in coinvariants -/

namespace Rep

variable {k G : Type u} [CommRing k] [Group G]

attribute [local instance] Subgroup.fintypeQuotientOfFiniteIndex

-- In the `G`-coinvariants of an induced representation `Ind_S^G A`, the class of `⟦h ⊗ a⟧` does
-- not depend on `h ∈ G`: the element is `h⁻¹` acting on `⟦1 ⊗ a⟧`.
private theorem coinvariantsMk_indVMk (S : Subgroup G) (A : Rep k S) (h : G) (a : A.V) :
    Representation.Coinvariants.mk (Representation.ind S.subtype A.ρ)
        (Representation.IndV.mk S.subtype A.ρ h a) =
      Representation.Coinvariants.mk (Representation.ind S.subtype A.ρ)
        (Representation.IndV.mk S.subtype A.ρ 1 a) := by
  have hmk : Representation.IndV.mk S.subtype A.ρ h a =
      Representation.ind S.subtype A.ρ h⁻¹ (Representation.IndV.mk S.subtype A.ρ 1 a) := by
    rw [Representation.ind_mk, one_mul, inv_inv]
  rw [hmk, Representation.Coinvariants.mk_self_apply]

-- In the `G`-coinvariants of an induced representation `Ind_S^G A`, acting by `s ∈ S` on the
-- second factor of `⟦1 ⊗ a⟧` does not change its class: `⟦1 ⊗ s • a⟧ = ⟦s⁻¹ ⊗ a⟧` in `Ind_S^G A`,
-- and `coinvariantsMk_indVMk` removes the `s⁻¹`.
private theorem coinvariantsMk_indVMk_one_apply (S : Subgroup G) (A : Rep k S) (s : S) (a : A.V) :
    Representation.Coinvariants.mk (Representation.ind S.subtype A.ρ)
        (Representation.IndV.mk S.subtype A.ρ 1 (A.ρ s a)) =
      Representation.Coinvariants.mk (Representation.ind S.subtype A.ρ)
        (Representation.IndV.mk S.subtype A.ρ 1 a) := by
  have hbal : Representation.IndV.mk S.subtype A.ρ 1 (A.ρ s a) =
      Representation.IndV.mk S.subtype A.ρ (s⁻¹ : S) a := by
    -- `IndV.mk S.subtype A.ρ h a` is the class of `single h 1 ⊗ₜ a` in the coinvariants of the
    -- tensor product, where `mk_tmul_inv` moves `s⁻¹` from the left factor to the right one.
    simpa only [LinearMap.coe_comp, Function.comp_apply, TensorProduct.mk_apply,
      InvMemClass.coe_inv, inv_inv, MonoidHom.coe_comp, Subgroup.coe_subtype,
      Representation.ofMulAction_single, smul_eq_mul, mul_one] using
      Representation.Coinvariants.mk_tmul_inv ((Representation.leftRegular k G).comp S.subtype)
        A.ρ (MonoidAlgebra.single 1 1) a s⁻¹
  rw [hbal, coinvariantsMk_indVMk]

open scoped Classical in
/-- **The unit of `Res ⊣ Ind`, read in coinvariants, is the relative transfer.** For a
finite-index subgroup `S ≤ G`, the unit `M ⟶ Ind_S^G Res_S M` sends `m` to `∑ᵢ ⟦gᵢ ⊗ gᵢ • m⟧` over
right coset representatives `gᵢ`; in the `G`-coinvariants of `Ind_S^G Res_S M` this is the class
of `⟦1 ⊗ ∑_{q ∈ G ⧸ S} q⁻¹ • m⟧`. The right coset `S g` is matched with the left coset `g⁻¹ S`,
and each summand depends only on its coset. -/
theorem coinvariantsMk_coindToInd_unit (M : Rep k G) (S : Subgroup G) [S.FiniteIndex]
    (m : M.V) :
    Representation.Coinvariants.mk (Representation.ind S.subtype (res S.subtype M).ρ)
        (coindToInd (res S.subtype M) (((resCoindAdjunction k S.subtype).unit.app M).hom m)) =
      Representation.Coinvariants.mk (Representation.ind S.subtype (res S.subtype M).ρ)
        (Representation.IndV.mk S.subtype (res S.subtype M).ρ 1
          (Representation.relTransfer M.ρ S m)) := by
  rw [coindToInd_apply, map_sum, Representation.relTransfer_apply, map_sum, map_sum]
  refine Fintype.sum_equiv (QuotientGroup.quotientRightRelEquivQuotientLeftRel S) _ _
    fun c => ?_
  induction c using Quotient.inductionOn with
  | h g =>
    set q : G ⧸ S := QuotientGroup.quotientRightRelEquivQuotientLeftRel S (Quotient.mk _ g)
      with hq
    have hq' : q = ((g⁻¹ : G) : G ⧸ S) := rfl
    have hs : (q.out : G)⁻¹ * g⁻¹ ∈ S := QuotientGroup.eq.mp (q.out_eq'.trans hq')
    have hg : (q.out : G)⁻¹ = ((⟨_, hs⟩ : S) : G) * g := by simp
    have h1 := coinvariantsMk_indVMk S (res S.subtype M) g (M.ρ g m)
    have h2 := coinvariantsMk_indVMk_one_apply S (res S.subtype M) ⟨_, hs⟩ (M.ρ g m)
    rw [hg, map_mul, Module.End.mul_apply]
    exact h1.trans h2.symm

end Rep

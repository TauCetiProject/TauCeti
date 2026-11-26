/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.LocalCoefficient.QuotientCovering.Coordinates
public import TauCeti.AlgebraicTopology.LocalCoefficient.Sign.Permutation
public import TauCeti.Topology.Covering.Quotient

/-!
# The sign representation of a double cover and its sign local system

Let `p : E ⟶ B` be the quotient covering map of an action of `ℤˣ = {1, -1}`, in the sense of
Mathlib's `IsQuotientCoveringMap`, so that `p` is a double cover whose fibres are the pairs
`{e, -1 • e}`, and let `σ` be the involution `e ↦ -1 • e`. Over a commutative ring `k` there are two
natural rank-one local systems on `B` attached to it:

* the local system associated to the sign representation of `ℤˣ` on `k`, `u ↦ (r ↦ u • r)`
  (`IsQuotientCoveringMap.associatedLocalSystem`), whose fibre over `x` is the coinvariants
  `(k ⊗ k[p⁻¹ x])_{ℤˣ}`, so that `a ⊗ [-1 • e]` and `-a ⊗ [e]` have the same class;
* the sign local system of `σ` (`IsCoveringMap.signLocalSystem`), whose fibre over `x` is the module
  of functions on `p⁻¹ x` changing sign under `σ`.

They are isomorphic (`IsQuotientCoveringMap.associatedLocalSystemSignIso`): the class of `a ⊗ r[e]`
goes to the function taking the value `r * a` at `e` and `-(r * a)` at `-1 • e`. In the coordinates
given by a sheet `e`, evaluation at `e` on the sign local system and the identification of the
coinvariants with `k` on the associated one, the isomorphism is the identity of `k`
(`IsQuotientCoveringMap.associatedLocalSystemIsoOfSheetCoordinates`); both coordinates change sign
when `e` is replaced by `-1 • e` and both are carried along by transport.

So for the orientation double cover of a real vector bundle, whose sign local system is the
orientation local system, the orientation-twisted chains of the base are the coinvariants of the
chains of the cover tensored with the sign representation; this is in
`TauCeti.Topology.VectorBundle.Orientation.Cover.SignRepresentation`.

The spaces may lie in any universe `u`. Associated local systems need the acting group in that
universe, so the sign representation is one of the copy `ULift ℤˣ` of `ℤˣ`, acting on `E` and on
`k` through `ULift.down` (`IsQuotientCoveringMap.ulift`).

## Main definitions

* `IsQuotientCoveringMap.associatedLocalSystemSignIso`: the local system associated to the sign
  representation of `ℤˣ` is the sign local system of the involution `e ↦ -1 • e`.

## References

* A. Hatcher, *Algebraic Topology*, Section 3.H.
* K. S. Brown, *Cohomology of Groups*, Springer, 1982, Sections II.4 and III.1.
-/

public section

noncomputable section

open CategoryTheory TauCeti

universe u

namespace IsQuotientCoveringMap

variable {E B : TopCat.{u}} {p : E ⟶ B} [MulAction ℤˣ E] (hG : IsQuotientCoveringMap p ℤˣ)
  (k : Type u) [CommRing k] {σ : C(E, E)} (hσ : ∀ e, σ e = (-1 : ℤˣ) • e)

include hG hσ

/-- A function on a fibre changing sign under `e ↦ -1 • e` is equivariant for the sign
representation: its value at `u • e` is `u` times its value at `e`. -/
theorem apply_smul_of_mem_signFiber {x : FundamentalGroupoid B} (u : ℤˣ) (e : p ⁻¹' {x.as})
    {f : p ⁻¹' {x.as} → k}
    (hf : f ∈ signFiber k σ (hG.comp_eq_of_forall_eq_neg_one_smul hσ) x.as) :
    letI := hG.mulActionFiber x.as
    f (u • e) = u • f e := by
  let := hG.mulActionFiber x.as
  rcases Int.units_eq_one_or u with rfl | rfl
  · rw [one_smul, one_smul]
  · have he : (-1 : ℤˣ) • e =
        Function.fiberMap σ (hG.comp_eq_of_forall_eq_neg_one_smul hσ) x.as e :=
      Subtype.ext ((hσ e).symm.trans (Function.fiberMap_apply_coe _ _ _ e).symm)
    rw [he, mem_signFiber_iff.1 hf, Units.neg_smul, one_smul]

/-- The sheet coordinates of the sign local system: evaluation at the sheet. -/
private abbrev signCoordinates {x : FundamentalGroupoid B} (e : p ⁻¹' {x.as}) :
    (hG.isCoveringMap.signLocalSystem k σ (hG.comp_eq_of_forall_eq_neg_one_smul hσ)).obj x ≅
      ModuleCat.of k (Rep.ofDistribMulAction k (ULift.{u} ℤˣ) k) :=
  (hG.isCoveringMap.signLocalSystemObjEquiv σ (hG.comp_eq_of_forall_eq_neg_one_smul hσ) x ≪≫ₗ
    signFiberEquiv (hG.ne_self_of_forall_eq_neg_one_smul hσ)
      (hG.eq_or_eq_of_forall_eq_neg_one_smul hσ) e).toModuleIso

/-- The sheet coordinate of a function changing sign under `σ` is its value at the sheet. -/
private lemma signCoordinates_hom_apply {x : FundamentalGroupoid B} (e : p ⁻¹' {x.as})
    (f : (hG.isCoveringMap.signLocalSystem k σ (hG.comp_eq_of_forall_eq_neg_one_smul hσ)).obj x) :
    (hG.signCoordinates k hσ e).hom.hom f =
      (hG.isCoveringMap.signLocalSystemObjEquiv σ _ x f : p ⁻¹' {x.as} → k) e :=
  signFiberEquiv_apply (R := k) _ _ e _

/-- Moving the sheet from `e` to `u • e` multiplies the evaluation by the sign `u`. -/
private lemma signCoordinates_smul {x : FundamentalGroupoid B} (e : p ⁻¹' {x.as})
    (u : ULift.{u} ℤˣ) :
    letI := hG.ulift.mulActionFiber x.as
    (hG.signCoordinates k hσ (u • e)).hom =
      (hG.signCoordinates k hσ e).hom ≫
        ModuleCat.ofHom ((Rep.ofDistribMulAction k (ULift.{u} ℤˣ) k).ρ u) := by
  let := hG.mulActionFiber x.as
  refine ModuleCat.hom_ext (LinearMap.ext fun f ↦ ?_)
  rw [ModuleCat.hom_comp, LinearMap.comp_apply, signCoordinates_hom_apply, ModuleCat.hom_ofHom,
    signCoordinates_hom_apply, Rep.ofDistribMulAction_ρ_apply_apply]
  -- `ULift ℤˣ` acts on the fibre and on `k` through `ULift.down`.
  exact hG.apply_smul_of_mem_signFiber k hσ u.down e
    (hG.isCoveringMap.signLocalSystemObjEquiv σ _ x f).property

/-- Transport in the sign local system is the identity in the coordinates given by a sheet and by
the endpoint of its lift. -/
private lemma signCoordinates_map {x y : FundamentalGroupoid B} (γ : x ⟶ y) (e : p ⁻¹' {x.as}) :
    (hG.isCoveringMap.signLocalSystem k σ (hG.comp_eq_of_forall_eq_neg_one_smul hσ)).map γ ≫
        (hG.signCoordinates k hσ (hG.isCoveringMap.monodromy γ e)).hom =
      (hG.signCoordinates k hσ e).hom :=
  ModuleCat.hom_ext (LinearMap.ext fun f ↦ by
    rw [ModuleCat.hom_comp, LinearMap.comp_apply, signCoordinates_hom_apply,
      signCoordinates_hom_apply]
    exact hG.isCoveringMap.signLocalSystemObjEquiv_map_apply_monodromy σ _ γ f e)

/-- **The local system of the sign representation is the sign local system.** For a quotient cover
by `ℤˣ` and the involution `σ = (-1 • ·)`, the local system associated to the sign representation
of `ℤˣ` on `k` is the sign local system of `σ`: the class of `a ⊗ r[e]` goes to the function
changing sign under `σ` whose value at `e` is `r * a`
(`associatedLocalSystemSignIso_hom_app_coinvariantsTensorMk`). -/
def associatedLocalSystemSignIso :
    hG.ulift.associatedLocalSystem k (Rep.ofDistribMulAction k (ULift.{u} ℤˣ) k) ≅
      hG.isCoveringMap.signLocalSystem k σ (hG.comp_eq_of_forall_eq_neg_one_smul hσ) :=
  hG.ulift.associatedLocalSystemIsoOfSheetCoordinates k (hG.signCoordinates k hσ)
    (hG.signCoordinates_smul k hσ) (hG.signCoordinates_map k hσ)

/-- The identification of the local system of the sign representation with the sign local system
sends the class of `a ⊗ r[e]` to the function whose value at `e` is `r * a`. -/
-- Not a simp lemma: `simp` unfolds `Rep.coinvariantsTensorMk` on the left-hand side first.
lemma associatedLocalSystemSignIso_hom_app_coinvariantsTensorMk {x : FundamentalGroupoid B}
    (e : p ⁻¹' {x.as}) (a r : k) :
    (hG.isCoveringMap.signLocalSystemObjEquiv σ (hG.comp_eq_of_forall_eq_neg_one_smul hσ) x
        (((hG.associatedLocalSystemSignIso k hσ).hom.app x).hom
          (Rep.coinvariantsTensorMk (Rep.ofDistribMulAction k (ULift.{u} ℤˣ) k)
            (Rep.of (hG.ulift.fiberRepresentation k x.as)) a (Finsupp.single e r))) :
          p ⁻¹' {x.as} → k)
        e =
      r * a := by
  have h := hG.ulift.associatedLocalSystemIsoOfSheetCoordinates_hom_app_coinvariantsTensorMk k
    (hG.signCoordinates k hσ) (hG.signCoordinates_smul k hσ) (hG.signCoordinates_map k hσ) e a r
  -- Evaluating at `e` the function with coordinate `r • a` at `e` gives `r • a`.
  rw [← hG.signCoordinates_hom_apply k hσ e, associatedLocalSystemSignIso, h,
    ← ModuleCat.comp_apply, Iso.inv_hom_id, ModuleCat.id_apply]
  -- The sign representation is `k` as a `k`-module, so its scalar action is multiplication.
  rfl

/-- The identification of the local system of the sign representation with the sign local system
sends the class of `a ⊗ f`, for a formal sum `f` of sheets over the point, to `a` times the
antisymmetrization `e ↦ f e - f (σ e)` of `f` (`IsCoveringMap.permutationLocalSystemToSignApp`). -/
-- Not a simp lemma: `simp` unfolds `Rep.coinvariantsTensorMk` on the left-hand side first.
lemma associatedLocalSystemSignIso_hom_app_coinvariantsTensorMk_eq_smul
    {x : FundamentalGroupoid B} (a : k) (f : p ⁻¹' {x.as} →₀ k) :
    ((hG.associatedLocalSystemSignIso k hσ).hom.app x).hom
        (Rep.coinvariantsTensorMk (Rep.ofDistribMulAction k (ULift.{u} ℤˣ) k)
          (Rep.of (hG.ulift.fiberRepresentation k x.as)) a f) =
      a • hG.isCoveringMap.permutationLocalSystemToSignApp k
        (hG.comp_eq_of_forall_eq_neg_one_smul hσ) (involutive_of_forall_eq_neg_one_smul hσ) x
          f := by
  induction f using Finsupp.induction_linear with
  | zero =>
    rw [map_zero, map_zero, smul_zero]
    exact map_zero _
  | add f g hf hg =>
    rw [map_add, map_add, smul_add, ← hf, ← hg]
    exact map_add _ _ _
  | single e r =>
    -- Both sides change sign under `σ`, so they agree once they agree at the sheet `e`.
    refine (hG.isCoveringMap.signLocalSystemObjEquiv σ _ x).injective
      ((signFiberEquiv (hG.ne_self_of_forall_eq_neg_one_smul hσ)
        (hG.eq_or_eq_of_forall_eq_neg_one_smul hσ) e).injective ?_)
    have he : Function.fiberMap σ (hG.comp_eq_of_forall_eq_neg_one_smul hσ) x.as e ≠ e :=
      fun h ↦ hG.ne_self_of_forall_eq_neg_one_smul hσ e
        ((Function.fiberMap_apply_coe σ _ x.as e).symm.trans (congrArg Subtype.val h))
    rw [signFiberEquiv_apply, signFiberEquiv_apply,
      associatedLocalSystemSignIso_hom_app_coinvariantsTensorMk, map_smul, Submodule.coe_smul,
      Pi.smul_apply, IsCoveringMap.signLocalSystemObjEquiv_permutationLocalSystemToSignApp_apply,
      Finsupp.single_eq_same, Finsupp.single_eq_of_ne he, sub_zero, smul_eq_mul, mul_comm]

/-- The inverse identification of the sign local system with the local system of the sign
representation sends a function changing sign under `σ` to the class of `f e ⊗ [e]`, for any sheet
`e` over the point. -/
-- Not a simp lemma: the sheet `e` occurs only on the right-hand side.
lemma associatedLocalSystemSignIso_inv_app_apply {x : FundamentalGroupoid B}
    (e : p ⁻¹' {x.as})
    (f : (hG.isCoveringMap.signLocalSystem k σ (hG.comp_eq_of_forall_eq_neg_one_smul hσ)).obj x) :
    ((hG.associatedLocalSystemSignIso k hσ).inv.app x).hom f =
      Rep.coinvariantsTensorMk (Rep.ofDistribMulAction k (ULift.{u} ℤˣ) k)
        (Rep.of (hG.ulift.fiberRepresentation k x.as))
        ((hG.isCoveringMap.signLocalSystemObjEquiv σ _ x f : p ⁻¹' {x.as} → k) e)
        (Finsupp.single e 1) := by
  -- Read `f` through its coordinate in the sheet `e`, where the inverse is the inverse fibre
  -- identification of the associated local system.
  have h := hG.ulift.associatedLocalSystemIsoOfSheetCoordinates_comp_inv_app k
    (hG.signCoordinates k hσ)
    (hG.signCoordinates_smul k hσ) (hG.signCoordinates_map k hσ) e
  calc ((hG.associatedLocalSystemSignIso k hσ).inv.app x).hom f
      = ((hG.signCoordinates k hσ e).inv ≫ (hG.associatedLocalSystemSignIso k hσ).inv.app x).hom
          ((hG.signCoordinates k hσ e).hom.hom f) := by
        rw [ModuleCat.comp_apply, ← ModuleCat.comp_apply (hG.signCoordinates k hσ e).hom,
          Iso.hom_inv_id, ModuleCat.id_apply]
    _ = _ := by
        rw [associatedLocalSystemSignIso, h, signCoordinates_hom_apply]
        exact hG.ulift.associatedLocalSystemFiberIso_inv_apply k
          (Rep.ofDistribMulAction k (ULift.{u} ℤˣ) k) e _

end IsQuotientCoveringMap

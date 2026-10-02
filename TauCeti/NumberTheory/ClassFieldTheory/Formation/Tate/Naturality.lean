/-
Copyright (c) 2026 Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.NumberTheory.ClassFieldTheory.Formation.Tate.Theorem
public import TauCeti.NumberTheory.ClassFieldTheory.Formation.Tate.TrivialRestrictionTrans
public import TauCeti.RepresentationTheory.Homological.TateCohomology.Cup.Functoriality
public import TauCeti.RepresentationTheory.Homological.TateCohomology.Cup.Restriction.Nonnegative

/-!
# Restriction of the Tate isomorphism of a class formation

Restriction to an intermediate ground field preserves cup product with a degree-two class.
Since the fundamental class restricts to the fundamental class of the smaller layer, the Tate
isomorphism commutes with restriction in every integer degree. In degree minus two this is the
square relating inclusion of ground levels to transfer of abelianized Galois groups.

The range comparisons identify a layer's Galois group with its image in the larger group. The
restriction maps defined branchwise by degree agree with generic Tate restriction through these
comparisons, so the cup-product restriction law applies to the existing finite-layer maps.

## References

* E. Artin and J. Tate, *Class Field Theory*, Chapter XIV, §4, Theorem 1 and §5.
* J.-P. Serre, *Local Fields*, Chapter XI, §3.
-/

public noncomputable section

open CategoryTheory MonoidalCategory Rep

namespace TauCeti.ClassFieldTheory

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [TotallyDisconnectedSpace G]

namespace LayerRestriction

variable {small big : NormalLayer G}

attribute [local instance] instFintypeRange Subgroup.fintypeOfFinite

/-- Layer Tate restriction is generic subgroup restriction followed by the inverse range
comparison, in every degree. -/
theorem tateRes_eq_res (T : LayerRestriction small big) (F : Formation G) (r : ℤ) :
    T.tateRes F r = TauCeti.TateCohomology.res (big.rep F) T.galHom.range r ≫
      (T.tateRangeIso F r).inv := by
  cases r with
  | ofNat n =>
    cases n with
    | zero => simp
    | succ n =>
      simp only [Int.ofNat_eq_natCast]
      let A := big.rep F
      let B := small.rep F
      let C := Rep.res T.galHom.range.subtype A
      let j := (TateCohomology.isoGroupCohomology (n + 1)).app B
      let k := (TateCohomology.isoGroupCohomology (n + 1)).app C
      let f := groupCohomology.map
        ((MonoidHom.ofInjective T.galHom_injective).symm : T.galHom.range →* small.Gal)
        (Representation.IsIntertwiningMap.ofRes (T.isIntertwiningMap_repIso_range F)) (n + 1)
      have hm : (T.tateRangeIso F ((n + 1 : ℕ) : ℤ)).hom ≫ k.hom = j.hom ≫ f := by
        rw [tateRangeIso_hom]
        exact TauCeti.TateCohomology.map_comp_isoGroupCohomology_hom
          (T.isIntertwiningMap_repIso_range F) (n + 1)
      have hr : TauCeti.TateCohomology.res A T.galHom.range ((n + 1 : ℕ) : ℤ) =
          TauCeti.TateCohomology.posRes A T.galHom.range n := by
        simpa only [Int.natCast_add, Int.cast_ofNat_Int] using
          TauCeti.TateCohomology.res_ofNat_succ A T.galHom.range n
      have ht := T.tateRes_comp_tateHIsoH_hom F (n + 1)
      rw [NormalLayer.tateHIsoH_def, NormalLayer.tateHIsoH_def] at ht
      have hg : T.cohomologyRes F (n + 1) ≫ f =
          groupCohomology.map T.galHom.range.subtype (𝟙 C) (n + 1) := by
        rw [cohomologyRes_def, ← groupCohomology.map_comp]
        refine groupCohomology.map_congr ?_ ?_ (n + 1)
        · ext γ
          exact congrArg Subtype.val
            ((MonoidHom.ofInjective T.galHom_injective).apply_symm_apply γ)
        · ext x
          simp only [Representation.IsIntertwiningMap.ofRes_hom_toLinearMap,
            Rep.hom_comp, Representation.IntertwiningMap.comp_toLinearMap,
            resMap_hom_toLinearMap, LinearMap.comp_apply]
          -- `equivOfIso` has the linear map of the isomorphism as its forward map.
          simp only [Representation.equivOfIso, res_obj_ρ,
            Representation.IntertwiningMap.coe_toLinearMap, LinearMap.coe_mk, AddHom.coe_mk,
            Iso.inv_hom_id_apply, SetLike.coe_eq_coe]
          exact (Rep.id_apply (A := C) x).symm
      rw [Iso.eq_comp_inv]
      ext x
      apply k.toLinearEquiv.injective
      -- Evaluate the comparison squares: categorical rewrites cannot cross the semireducible
      -- `groupCohomology.functor` carrier in their intermediate terms.
      exact (ConcreteCategory.congr_hom hm _).trans
        ((congrArg f (ConcreteCategory.congr_hom ht x)).trans
          ((ConcreteCategory.congr_hom hg _).trans
            ((ConcreteCategory.congr_hom
              (TauCeti.TateCohomology.posRes_comp_isoGroupCohomology_hom A
                T.galHom.range n) x).symm.trans
                  (congrArg k.hom (ConcreteCategory.congr_hom hr x).symm))))
  | negSucc n => cases n <;> simp

/-- Restriction with trivial integral coefficients is generic subgroup restriction followed by
its inverse range comparison. -/
theorem trivialTateRes_eq_res (T : LayerRestriction small big) (r : ℤ) :
    T.trivialTateRes r =
      TauCeti.TateCohomology.res (Rep.trivial ℤ big.Gal ℤ) T.galHom.range r ≫
        (T.trivialTateRangeIso r).inv := by
  cases r with
  | ofNat n =>
    cases n with
    | zero => simp
    | succ n =>
      simp only [Int.ofNat_eq_natCast]
      let A := Rep.trivial ℤ big.Gal ℤ
      let C := Rep.res T.galHom.range.subtype A
      let k := (TateCohomology.isoGroupCohomology (n + 1)).app C
      have hr : TauCeti.TateCohomology.res A T.galHom.range ((n + 1 : ℕ) : ℤ) =
          TauCeti.TateCohomology.posRes A T.galHom.range n := by
        simpa only [Int.natCast_add, Int.cast_ofNat_Int] using
          TauCeti.TateCohomology.res_ofNat_succ A T.galHom.range n
      rw [Iso.eq_comp_inv]
      ext x
      apply k.toLinearEquiv.injective
      -- Evaluation avoids the semireducible functor carrier, as in the coefficient square above.
      exact (ConcreteCategory.congr_hom
        (T.trivialTateRes_comp_isoGroupCohomology_hom (n + 1)) x).trans
          ((ConcreteCategory.congr_hom
            (TauCeti.TateCohomology.posRes_comp_isoGroupCohomology_hom A
              T.galHom.range n) x).symm.trans
                (congrArg k.hom (ConcreteCategory.congr_hom hr x).symm))
  | negSucc n => cases n <;> simp

-- The range comparison preserves the tensor product and its left unitor.
private theorem tateRangeIso_hom_cupClass (T : LayerRestriction small big) (F : Formation G)
    (u : small.H F 2) (r : ℤ) (x : small.TrivialTateH r) :
    (T.tateRangeIso F (r + 2)).hom (cupClass F small u r x) =
      (tateCohomologyFunctor (r + 2)).map
        (Rep.resMap T.galHom.range.subtype (λ_ (big.rep F)).hom)
        (TauCeti.TateCohomology.cup
          (Rep.res T.galHom.range.subtype (Rep.trivial ℤ big.Gal ℤ))
          (Rep.res T.galHom.range.subtype (big.rep F)) r 2 (r + 2) rfl
          ((T.trivialTateRangeIso r).hom x)
          ((T.tateRangeIso F 2).hom ((small.tateHIsoH F 2).inv u))) := by
  have hφ := T.isIntertwiningMap_repIso_range F
  have h₀ := T.isIntertwiningMap_trivial_range
  have hl := TauCeti.TateCohomology.tateCohomologyFunctor_map_comp_map (h₀.tensor hφ) hφ
    (λ_ (small.rep F)).hom (Rep.resMap T.galHom.range.subtype (λ_ (big.rep F)).hom)
    (TensorProduct.ext' fun n c ↦ by
      -- Restriction preserves tensor carriers, but the two representations are not syntactically
      -- equal. Presenting the unitors as tensor linear maps lets their application lemmas fire.
      change (Representation.equivOfIso (T.repIso F)).toLinearEquiv
          (TensorProduct.lid ℤ (small.rep F).V (n ⊗ₜ[ℤ] c)) =
        TensorProduct.lid ℤ (big.rep F).V
          (n ⊗ₜ[ℤ] (Representation.equivOfIso (T.repIso F)).toLinearEquiv c)
      simp) (r + 2)
  rw [cupClass_apply, tateRangeIso_hom, ← ModuleCat.comp_apply, hl, ModuleCat.comp_apply,
    trivialTateRangeIso_hom, tateRangeIso_hom]
  exact congrArg _ (TauCeti.TateCohomology.map_cup h₀ hφ r 2 (r + 2) rfl x _)

/-- Restricting cup product with a degree-two layer class gives cup product of the restricted
classes, in every integer degree. -/
@[simp]
theorem cupClass_res (T : LayerRestriction small big) (F : Formation G) (u : big.H F 2)
    (r : ℤ) (x : big.TrivialTateH r) :
    T.tateRes F (r + 2) (cupClass F big u r x) =
      cupClass F small (T.cohomologyRes F 2 u) r (T.trivialTateRes r x) := by
  have hu : T.tateRes F 2 ((big.tateHIsoH F 2).inv u) =
      (small.tateHIsoH F 2).inv (T.cohomologyRes F 2 u) := by
    apply (small.tateHIsoH F 2).toLinearEquiv.injective
    exact (ConcreteCategory.congr_hom (T.tateRes_comp_tateHIsoH_hom F 2) _).trans
      ((congrArg (T.cohomologyRes F 2) ((big.tateHIsoH F 2).inv_hom_id_apply u)).trans
        ((small.tateHIsoH F 2).inv_hom_id_apply _).symm)
  apply (ConcreteCategory.bijective_of_isIso (T.tateRangeIso F (r + 2)).hom).injective
  rw [tateRangeIso_hom_cupClass, ← hu]
  simp only [tateRes_eq_res, trivialTateRes_eq_res, ModuleCat.comp_apply,
    Iso.inv_hom_id_apply]
  rw [cupClass_apply]
  have hnat := TauCeti.TateCohomology.res_natural (λ_ (big.rep F)).hom T.galHom.range (r + 2)
  have hcup := TauCeti.TateCohomology.cup_res_of_nonneg_right
    (Rep.trivial ℤ big.Gal ℤ) (big.rep F) T.galHom.range (by omega) rfl x
      ((big.tateHIsoH F 2).inv u)
  exact (ConcreteCategory.congr_hom hnat _).trans (congrArg _ hcup)

end LayerRestriction

namespace ClassFormation

variable {F : Formation G} {small big : NormalLayer G}

/-- The Tate isomorphism of a class formation commutes with restriction to an intermediate
ground field, in every integer degree. -/
theorem tateIso_res (cf : ClassFormation F) (T : LayerRestriction small big) (r : ℤ)
    (x : big.TrivialTateH r) :
    T.tateRes F (r + 2) (cf.tateIso big r x) =
      cf.tateIso small r (T.trivialTateRes r x) := by
  simp [tateIso_apply]

/-- The restriction square for the Tate isomorphism composes along a tower of ground fields. -/
theorem tateIso_res_trans (cf : ClassFormation F) {a b c : NormalLayer G}
    (T : LayerRestriction a b) (T' : LayerRestriction b c) (r : ℤ)
    (x : c.TrivialTateH r) :
    (T.trans T').tateRes F (r + 2) (cf.tateIso c r x) =
      cf.tateIso a r (T.trivialTateRes r (T'.trivialTateRes r x)) := by
  rw [cf.tateIso_res, LayerRestriction.trivialTateRes_trans, ModuleCat.comp_apply]

end ClassFormation

end TauCeti.ClassFieldTheory

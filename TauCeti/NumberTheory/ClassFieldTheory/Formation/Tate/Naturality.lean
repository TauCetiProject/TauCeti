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
-- Not `@[simp]`: the existing cup-product rules already prove this, so `simpNF` rejects it.
theorem tateIso_res (cf : ClassFormation F) (T : LayerRestriction small big) (r : ℤ)
    (x : big.TrivialTateH r) :
    T.tateRes F (r + 2) (cf.tateIso big r x) =
      cf.tateIso small r (T.trivialTateRes r x) := by
  simp [tateIso_apply]

/-- The Tate isomorphism commutes with iterated restriction along a tower of ground fields. -/
theorem tateIso_res_trans (cf : ClassFormation F) {a b c : NormalLayer G}
    (T : LayerRestriction a b) (T' : LayerRestriction b c) (r : ℤ)
    (x : c.TrivialTateH r) :
    T.tateRes F (r + 2) (T'.tateRes F (r + 2) (cf.tateIso c r x)) =
      cf.tateIso a r (T.trivialTateRes r (T'.trivialTateRes r x)) := by
  simpa only [T.tateRes_trans T' F (r + 2), T.trivialTateRes_trans T' r,
    ModuleCat.comp_apply] using cf.tateIso_res (T.trans T') r x

end ClassFormation

end TauCeti.ClassFieldTheory

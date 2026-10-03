/-
Copyright (c) 2026 Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import TauCeti.NumberTheory.ClassFieldTheory.Formation.Tate.Theorem
public import TauCeti.RepresentationTheory.Homological.TateCohomology.Cup.ChangeOfGroup

/-!
# Inflation and the Tate isomorphism of a class formation

A refinement `LayerRefinement old new` enlarges the top field of a finite normal layer from `K` to
`L` over the same ground field `F`. Inflation of positive-degree Tate cohomology along it, with
formation coefficients (`LayerRefinement.tateInfl`) and with trivial integral coefficients
(`LayerRefinement.trivialTateInfl`), is change of group along the quotient map of Galois groups
`Gal(L/F) → Gal(K/F)` (`LayerRefinement.tateInfl_eq_posMap`,
`LayerRefinement.trivialTateInfl_eq_posMap`). Since change of group preserves the Tate cup product,
inflating cup product with a degree-two class is cup product of the inflated classes
(`LayerRefinement.cupClass_infl`).

For a class formation the fundamental class does not inflate to the fundamental class:
`inf u_{K/F} = [L : K] • u_{L/F}` (`ClassFormation.fundamentalClass_infl`). Hence Tate's
isomorphism `H^r(Gal(K/F), ℤ) ≃ H^{r+2}(Gal(K/F), A^{V})` satisfies the scaled inflation formula

`inf (x ∪ u_{K/F}) = [L : K] • (inf x ∪ u_{L/F})`

in every positive degree `r` (`ClassFormation.tateIso_infl`). Inflation is not defined in Tate
degrees at most zero, so the formula has no counterpart there. The restriction and corestriction
squares of `ClassFormation.tateIso_res` and `ClassFormation.tateIso_cor` commute without a factor;
the inflation square differs from them exactly by the relative degree.

## Main statements

* `TauCeti.ClassFieldTheory.LayerRefinement.cupClass_infl`: inflation preserves cup product with a
  degree-two class.
* `TauCeti.ClassFieldTheory.ClassFormation.tateIso_infl`: the scaled inflation formula for the
  Tate isomorphism.

## References

* E. Artin and J. Tate, *Class Field Theory*, Chapter XIV, §§1–4.
* J.-P. Serre, *Local Fields*, Chapter XI, §§1–3.
-/

public noncomputable section

open CategoryTheory MonoidalCategory Rep

namespace TauCeti.ClassFieldTheory

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [TotallyDisconnectedSpace G]

namespace LayerRefinement

variable {old new : NormalLayer G}

/-- Inflation of positive-degree Tate cohomology along a refinement is the change of group along
the quotient map of Galois groups and the inclusion of coefficient modules. -/
theorem tateInfl_eq_posMap (T : LayerRefinement old new) (F : Formation G) (r : ℕ) [NeZero r] :
    T.tateInfl F r = TateCohomology.posMap T.galHom (T.repHom F) r := by
  rw [tateInfl_def, cohomologyInfl_def, TateCohomology.posMap_def, NormalLayer.tateHIsoH_def,
    NormalLayer.tateHIsoH_def]
  rfl

/-- Inflation of positive-degree Tate cohomology with trivial integral coefficients is the change
of group along the quotient map of Galois groups. -/
theorem trivialTateInfl_eq_posMap (T : LayerRefinement old new) (r : ℕ) [NeZero r] :
    T.trivialTateInfl r = TateCohomology.posMap T.galHom T.trivialRepHom r := by
  rw [trivialTateInfl_def, trivialCohomologyInfl_def, TateCohomology.posMap_def,
    NormalLayer.trivialTateHIsoH_def, NormalLayer.trivialTateHIsoH_def]
  rfl

-- Degree-two Tate inflation is ordinary inflation, read through `tateHIsoH`.
private theorem tateInfl_tateHIsoH_inv (T : LayerRefinement old new) (F : Formation G)
    (u : old.H F 2) :
    T.tateInfl F 2 ((old.tateHIsoH F 2).inv u) =
      (new.tateHIsoH F 2).inv (T.cohomologyInfl F 2 u) := by
  rw [tateInfl_def, ModuleCat.comp_apply, Iso.inv_hom_id_apply, ModuleCat.comp_apply]

-- Along a refinement, the left unitor `ℤ ⊗ A^V ≅ A^V` and the inclusion `A^V ⊆ A^{V'}` commute.
private theorem resMap_leftUnitor_comp_repHom (T : LayerRefinement old new) (F : Formation G) :
    (Rep.resFunctor T.galHom).map (λ_ (old.rep F)).hom ≫ T.repHom F =
      (T.trivialRepHom ⊗ₘ T.repHom F :
        Rep.res T.galHom (Rep.trivial ℤ old.Gal ℤ) ⊗ Rep.res T.galHom (old.rep F) ⟶ _) ≫
        (λ_ (new.rep F)).hom := by
  ext t
  induction t using TensorProduct.inductionOn with
  | add a b ha hb => simp only [map_add, Submodule.coe_add, ha, hb]
  | tmul n c =>
    -- The source of `f ⊗ g` is the tensor product of the restrictions, which is the restriction of
    -- the tensor product only after unfolding, so its value on a pure tensor is stated explicitly.
    change _ = ((λ_ (new.rep F)).hom.hom (T.trivialRepHom.hom n ⊗ₜ[ℤ] (T.repHom F).hom c) :
      F.toRep.V)
    simpa using congrArg (· • (c : F.toRep.V)) (T.trivialRepHom_hom_apply n).symm


/-- Inflating cup product with a degree-two class gives cup product of the inflated classes, in
every positive degree. -/
theorem cupClass_infl (T : LayerRefinement old new) (F : Formation G) (u : old.H F 2) (r : ℕ)
    [NeZero r] (x : old.TrivialTateH r) :
    T.tateInfl F (r + 2) (cupClass F old u r x) =
      cupClass F new (T.cohomologyInfl F 2 u) r (T.trivialTateInfl r x) := by
  have hdeg : (r : ℤ) + ((2 : ℕ) : ℤ) = ((r + 2 : ℕ) : ℤ) := by push_cast; rfl
  let w := TateCohomology.cup (Rep.trivial ℤ old.Gal ℤ) (old.rep F) r 2 (r + 2 : ℕ) hdeg x
    ((old.tateHIsoH F 2).inv u)
  rw [tateInfl_eq_posMap, trivialTateInfl_eq_posMap, cupClass_apply, cupClass_apply,
    ← tateInfl_tateHIsoH_inv, tateInfl_eq_posMap]
  refine (congr($(TateCohomology.map_comp_posMap T.galHom (λ_ (old.rep F)).hom (T.repHom F)
    (r + 2)) w)).trans ?_
  rw [resMap_leftUnitor_comp_repHom]
  refine (congr($(TateCohomology.posMap_comp_map T.galHom (M := Rep.trivial ℤ old.Gal ℤ ⊗ old.rep F)
    (T.trivialRepHom ⊗ₘ T.repHom F :
      Rep.res T.galHom (Rep.trivial ℤ old.Gal ℤ) ⊗ Rep.res T.galHom (old.rep F) ⟶ _)
    (λ_ (new.rep F)).hom (r + 2)) w)).symm.trans ?_
  rw [ModuleCat.comp_apply]
  exact congrArg _ (TateCohomology.cup_posMap T.galHom _ _ T.trivialRepHom (T.repHom F) r 2
    (r + 2) hdeg x _)

end LayerRefinement

namespace ClassFormation

variable {F : Formation G} {old new : NormalLayer G}

/-- **The scaled inflation formula for the Tate isomorphism.** Under a refinement of the top field
from `K` to `L`, inflating `x ∪ u_{K/F}` gives `[L : K]` times the cup product of the inflation of
`x` with `u_{L/F}`, in every positive degree. Unlike restriction and corestriction, the inflation
square commutes only up to the relative degree, because `inf u_{K/F} = [L : K] • u_{L/F}`. -/
theorem tateIso_infl (cf : ClassFormation F) (T : LayerRefinement old new) (r : ℕ) [NeZero r]
    (x : old.TrivialTateH r) :
    T.tateInfl F (r + 2) (cf.tateIso old r x) =
      T.relativeDegree • cf.tateIso new r (T.trivialTateInfl r x) := by
  rw [tateIso_apply, tateIso_apply, cupFundamentalClass_apply, cupFundamentalClass_apply,
    LayerRefinement.cupClass_infl, cf.fundamentalClass_infl]
  exact congrArg (· (T.trivialTateInfl r x))
    ((AddMonoidHom.mk' (fun u ↦ cupClass F new u r) fun u v ↦ cupClass_add F new u v r).map_nsmul
      _ _)

end ClassFormation

end TauCeti.ClassFieldTheory

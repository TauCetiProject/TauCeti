/-
Copyright (c) 2026 Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import TauCeti.NumberTheory.ClassFieldTheory.Formation.Character
public import TauCeti.NumberTheory.ClassFieldTheory.Formation.GaloisMaps
public import TauCeti.NumberTheory.ClassFieldTheory.Formation.Tate.Theorem
public import TauCeti.RepresentationTheory.Homological.TateCohomology.Cup.ChangeOfGroup

/-!
# Inflation, the Tate isomorphism and character classes of a class formation

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

The classes through which Artin and Tate characterize the Artin map behave without such a factor.
A character `χ` of `Gal(K/F)^ab` inflates to the character `χ ∘ π` of `Gal(L/F)^ab`, where
`π : Gal(L/F)^ab → Gal(K/F)^ab` is the quotient map, and inflation carries the connecting class
`δχ ∈ H²(Gal(K/F), ℤ)` to `δ(χ ∘ π)` (`LayerRefinement.trivialTateInfl_characterConnectingClass`).
Cup product with the degree-zero class of `a ∈ A^U` is induced by the coefficient map `n ↦ n • a`,
which inflation does not see, so inflation carries the Artin character cup `a₀ ∪ δχ` of `K/F` to
that of `L/F` (`LayerRefinement.cohomologyInfl_artinCharacterCup`). Since inflation preserves
invariants, `inv_{L/F}(a₀ ∪ δ(χ ∘ π)) = inv_{K/F}(a₀ ∪ δχ)`
(`ClassFormation.inv_artinCharacterCup_comp_quotientHom`). By the character formula of Artin and
Tate, `χ(artinMap a) = inv(a₀ ∪ δχ)`, this is the statement that the Artin maps of `K/F` and `L/F`
are compatible with the quotient map `π`.

## Main statements

* `TauCeti.ClassFieldTheory.LayerRefinement.cupClass_infl`: inflation preserves cup product with a
  degree-two class.
* `TauCeti.ClassFieldTheory.ClassFormation.tateIso_infl`: the scaled inflation formula for the
  Tate isomorphism.
* `TauCeti.ClassFieldTheory.LayerRefinement.trivialTateInfl_characterConnectingClass`: inflation
  of the connecting class of a character is the connecting class of the inflated character.
* `TauCeti.ClassFieldTheory.LayerRefinement.cohomologyInfl_artinCharacterCup`: inflation of the
  Artin character cup is the Artin character cup of the inflated character.
* `TauCeti.ClassFieldTheory.ClassFormation.inv_artinCharacterCup_comp_quotientHom`: the invariant
  of the Artin character cup does not change under inflation.

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

-- `dsimp% only [Nat.cast_ofNat]` on the left-hand side, as for
-- `ClassFormation.tateHIsoH_hom_tateFundamentalClass`: `simp` first normalises the degree
-- `((2 : ℕ) : ℤ)` of `trivialTateInfl` to `2`.
/-- **Inflation of the connecting class of a character.** Inflating `δχ ∈ H²(Gal(K/F), ℤ)` to the
refinement `L/F` gives the connecting class of the inflated character `χ ∘ π`, where
`π : Gal(L/F)^ab → Gal(K/F)^ab` is the quotient map. -/
@[simp]
theorem trivialTateInfl_characterConnectingClass (T : LayerRefinement old new)
    (χ : Additive (Abelianization old.Gal) →+ AddCircle (1 : ℚ)) :
    (dsimp% only [Nat.cast_ofNat] (T.trivialTateInfl 2 (old.characterConnectingClass χ))) =
      new.characterConnectingClass (χ.comp T.quotientHom) := by
  rw [trivialTateInfl_eq_posMap, NormalLayer.characterConnectingClass_def,
    NormalLayer.characterConnectingClass_def]
  refine (TateCohomology.posMap_characterConnectingClass T.galHom T.trivialRepHom
    T.trivialRepHom_hom_apply χ).trans (congrArg _ (congrArg χ.comp ?_))
  ext x
  simp

/-- **Inflation of the Artin character cup.** Inflating the class `a₀ ∪ δχ ∈ H²(Gal(K/F), A^V)`
of `a ∈ A^U` and a character `χ` of `Gal(K/F)^ab` to the refinement `L/F` gives the class
`a₀ ∪ δ(χ ∘ π) ∈ H²(Gal(L/F), A^{V'})` of the same element `a` of the common ground level and the
inflated character. -/
@[simp]
theorem cohomologyInfl_artinCharacterCup (T : LayerRefinement old new) (F : Formation G)
    (a : F.level old.ground) (χ : Additive (Abelianization old.Gal) →+ AddCircle (1 : ℚ)) :
    T.cohomologyInfl F 2 (old.artinCharacterCup F a χ) =
      new.artinCharacterCup F (T.groundEquiv F a) (χ.comp T.quotientHom) := by
  obtain ⟨x, rfl⟩ := (old.groundLevelEquiv F).surjective a
  obtain ⟨x', hx'⟩ :=
    (new.groundLevelEquiv F).surjective (T.groundEquiv F (old.groundLevelEquiv F x))
  rw [← hx', NormalLayer.artinCharacterCup_groundLevelEquiv,
    NormalLayer.artinCharacterCup_groundLevelEquiv, ← T.trivialTateInfl_characterConnectingClass]
  -- Both cups are induced by the coefficient maps `n ↦ n • a`, which commute with inflation.
  have hg : (Rep.resFunctor T.galHom).map
      (Rep.tensorInvariant (Rep.trivial ℤ old.Gal ℤ) x ≫ (β_ _ (old.rep F)).hom ≫
        (ρ_ (old.rep F)).hom) ≫ T.repHom F =
      T.trivialRepHom ≫ Rep.tensorInvariant (Rep.trivial ℤ new.Gal ℤ) x' ≫
        (β_ _ (new.rep F)).hom ≫ (ρ_ (new.rep F)).hom := by
    have hx : ((x' : F.level new.top) : F.toRep.V) = ((x : F.level old.top) : F.toRep.V) := by
      simpa using congrArg Subtype.val hx'
    refine Rep.hom_ext (Representation.IntertwiningMap.ext (LinearMap.ext fun n ↦ ?_))
    apply Subtype.ext
    have h₁ := congrArg Subtype.val
      (TauCeti.Rep.tensorInvariant_braiding_rightUnitor_hom_apply (M := old.rep F) x n)
    have h₂ := congrArg Subtype.val
      (TauCeti.Rep.tensorInvariant_braiding_rightUnitor_hom_apply (M := new.rep F) x' n)
    simp only [Representation.IntertwiningMap.coe_toLinearMap, Rep.hom_comp,
      Representation.IntertwiningMap.comp_apply]
    rw [repHom_hom_apply_coe, trivialRepHom_hom_apply]
    refine h₁.trans (Eq.trans ?_ h₂.symm)
    simp [hx]
  have e := congr($(T.tateInfl_comp_tateHIsoH_hom F 2) ((tateCohomologyFunctor 2).map
      (Rep.tensorInvariant (Rep.trivial ℤ old.Gal ℤ) x ≫ (β_ _ (old.rep F)).hom ≫
        (ρ_ (old.rep F)).hom) (old.characterConnectingClass χ)))
  simp only [ModuleCat.comp_apply] at e
  rw [← e]
  refine congrArg _ ?_
  rw [tateInfl_eq_posMap, trivialTateInfl_eq_posMap]
  refine (congr($(TateCohomology.map_comp_posMap T.galHom _ (T.repHom F) 2) _)).trans ?_
  rw [hg]
  exact (congr($(TateCohomology.posMap_comp_map T.galHom T.trivialRepHom _ 2) _)).symm

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

/-- **The invariant of the Artin character cup is unchanged by inflation.** For `a ∈ A^U` and a
character `χ` of `Gal(K/F)^ab`, the invariant over the refinement `L/F` of `a₀ ∪ δ(χ ∘ π)` is the
invariant over `K/F` of `a₀ ∪ δχ`, where `π : Gal(L/F)^ab → Gal(K/F)^ab` is the quotient map. -/
@[simp]
theorem inv_artinCharacterCup_comp_quotientHom (cf : ClassFormation F) (T : LayerRefinement old new)
    (a : F.level old.ground) (χ : Additive (Abelianization old.Gal) →+ AddCircle (1 : ℚ)) :
    cf.inv new (new.artinCharacterCup F (T.groundEquiv F a) (χ.comp T.quotientHom)) =
      cf.inv old (old.artinCharacterCup F a χ) := by
  rw [← LayerRefinement.cohomologyInfl_artinCharacterCup, cf.inv_infl]

end ClassFormation

end TauCeti.ClassFieldTheory

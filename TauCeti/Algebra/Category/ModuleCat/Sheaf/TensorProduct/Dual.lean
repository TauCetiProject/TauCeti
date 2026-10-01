/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Products
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free
public import TauCeti.Algebra.Category.ModuleCat.Sheaf.Biproducts
public import TauCeti.Algebra.Category.ModuleCat.Sheaf.TensorProduct.Closed
public import TauCeti.CategoryTheory.Monoidal.Rigid.Biproduct
public import TauCeti.CategoryTheory.Monoidal.Rigid.Closed

/-!
# Finite free sheaves of modules are self-dual

Let `R` be a sheaf of commutative rings on a small site. In the symmetric monoidal category of
sheaves of `R`-modules, the free sheaf `free I` on a finite type `I` is dualizable, with dual
`free I` itself. Writing `eᵢ = ιFree i` for the basis sections, the evaluation
`free I ⊗ free I ⟶ R` sends `eᵢ ⊗ eⱼ` to `δᵢⱼ`, and the coevaluation `R ⟶ free I ⊗ free I` sends
`1` to `∑ i, eᵢ ⊗ eᵢ`.

The pairing is obtained from `TauCeti.ExactPairing.biproduct`: `free I` is the biproduct of `I`
copies of the unit `R` (`TauCeti.SheafOfModules.biproductIsoFree`), and the unit is canonically
self-dual. Since evaluation at an object `W` preserves products, the biproduct decomposition also
computes the sections of `free I` over `W`: they are the `I`-tuples of sections of `R` over `W`
(`TauCeti.SheafOfModules.evaluationFreeIso`).
Finite free sheaves are the local models of finite locally free sheaves, so this is the local
input for showing that finite locally free sheaves are dualizable.

Combining the pairing with the closed structure of sheaves of modules identifies the internal Hom
out of `free I` with tensoring by `free I`, and in particular the dual sheaf
`𝓗om(free I, 𝒪)` with `free I` itself. Its basis sections are the dual basis: paired against the
basis sections of `free I` they give `δᵢⱼ`.

## Main declarations

* `TauCeti.SheafOfModules.biproductIsoFree`: the free sheaf on a finite type is the biproduct of
  copies of the unit;
* `TauCeti.SheafOfModules.evaluationFreeIso`: the sections of `free I` over `W` are the `I`-tuples
  of sections of `R` over `W`;
* `TauCeti.SheafOfModules.exactPairingFree`: the exact pairing between `free I` and itself;
* `TauCeti.SheafOfModules.ιFree_tensorHom_ιFree_evaluation`,
  `TauCeti.SheafOfModules.ιFree_tensorHom_ιFree_evaluation_of_ne` and
  `TauCeti.SheafOfModules.coevaluation_free`: its evaluation and coevaluation on basis sections;
* `TauCeti.SheafOfModules.ihomFreeIso` and `TauCeti.SheafOfModules.dualFreeIso`: the internal Hom
  out of `free I`, and the dual sheaf of `free I`;
* `TauCeti.SheafOfModules.dualFreeι`: the basis sections of the dual sheaf;
* `TauCeti.SheafOfModules.ιFree_tensorHom_dualFreeι_comp_ev` and its `_of_ne` variant: the
  dual basis;
* `SheafOfModules.dual` and `SheafOfModules.dualIso`: the internal-Hom dual and its action on
  isomorphisms;
* `SheafOfModules.isIso_evaluation_dual_of_iso_freePUnit`: evaluation against the dual is an
  isomorphism for a sheaf isomorphic to the standard free rank-one sheaf.
-/

public section

open CategoryTheory Limits MonoidalCategory MonoidalClosed

namespace TauCeti

universe u

noncomputable section

variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat.{u})]
variable [HasWeakSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]

namespace SheafOfModules

open _root_.SheafOfModules

variable {R : Sheaf J CommRingCat.{u}} (I : Type u) [Finite I]

/-- The free sheaf of modules on a finite type `I` is the biproduct of `I` copies of the unit. -/
def biproductIsoFree :
    ⨁ (fun _ : I ↦ 𝟙_ (SheafOfModules.{u} (ringCatSheaf R))) ≅ free (R := ringCatSheaf R) I :=
  (biproduct.isColimit _).coconePointUniqueUpToIso (isColimitFreeCofan I)

variable {I}

/-- `biproductIsoFree` sends the `i`-th summand to the `i`-th basis section. -/
@[reassoc (attr := simp)]
theorem biproduct_ι_biproductIsoFree_hom (i : I) :
    biproduct.ι (fun _ : I ↦ unit (ringCatSheaf R)) i ≫
      (biproductIsoFree (R := R) I).hom = ιFree i :=
  (biproduct.isColimit _).comp_coconePointUniqueUpToIso_hom (isColimitFreeCofan I) ⟨i⟩

/-- The inverse of `biproductIsoFree` sends the `i`-th basis section to the `i`-th summand. -/
@[reassoc (attr := simp)]
theorem ιFree_biproductIsoFree_inv (i : I) :
    ιFree i ≫ (biproductIsoFree (R := R) I).inv =
      biproduct.ι (fun _ : I ↦ 𝟙_ (SheafOfModules.{u} (ringCatSheaf R))) i :=
  (biproduct.isColimit _).comp_coconePointUniqueUpToIso_inv (isColimitFreeCofan I) ⟨i⟩

variable (I)

/-- The sections over `W` of the free sheaf of modules on a finite type `I` are the `I`-indexed
tuples of sections of the sheaf of rings over `W`: `free I` is the product of `I` copies of the
unit, and evaluation at `W` preserves products. -/
def evaluationFreeIso (W : Cᵒᵖ) :
    (evaluation (ringCatSheaf R) W).obj (free I) ≅
      ModuleCat.of ((ringCatSheaf R).obj.obj W) (I → (ringCatSheaf R).obj.obj W) :=
  (evaluation (ringCatSheaf R) W).mapIso
      ((biproductIsoFree (R := R) I).symm ≪≫ biproduct.isoProduct _) ≪≫
    PreservesProduct.iso (evaluation (ringCatSheaf R) W) _ ≪≫ ModuleCat.piIsoPi _

/-- The `i`-th coordinate of a section of `free I` under `evaluationFreeIso` is its image under
the `i`-th projection `free I ⟶ R` of the biproduct decomposition of `free I`. -/
@[reassoc (attr := simp)]
theorem evaluationFreeIso_hom_comp_proj (W : Cᵒᵖ) (i : I) :
    (evaluationFreeIso (R := R) I W).hom ≫ ModuleCat.ofHom (LinearMap.proj i) =
      (evaluation (ringCatSheaf R) W).map
        ((biproductIsoFree (R := R) I).inv ≫ biproduct.π _ i) := by
  -- The last factor of `evaluationFreeIso` lands in the module of `I`-tuples of sections of the
  -- unit over `W`, which is the module of `I`-tuples of sections of `R` only after unfolding
  -- `evaluation`; the composite is therefore spelled out in the former form before simplifying.
  change ((evaluation (ringCatSheaf R) W).map
      ((biproductIsoFree (R := R) I).inv ≫ (biproduct.isoProduct _).hom) ≫
    (PreservesProduct.iso (evaluation (ringCatSheaf R) W) _).hom ≫
    (ModuleCat.piIsoPi fun _ : I ↦ (evaluation (ringCatSheaf R) W).obj (𝟙_ _)).hom) ≫
      ModuleCat.ofHom (LinearMap.proj i) = _
  simp

variable {I}

variable (I) in
/-- The free sheaf of modules on a finite type is self-dual: the evaluation pairs the basis
sections `ιFree i` and `ιFree j` to `δᵢⱼ`, and the coevaluation is `∑ i, ιFree i ⊗ ιFree i`. -/
instance exactPairingFree :
    ExactPairing (free (R := ringCatSheaf R) I) (free (R := ringCatSheaf R) I) :=
  have := Fintype.ofFinite I
  exactPairingCongr (biproductIsoFree I).symm (biproductIsoFree I).symm

/-- The evaluation of `free I` is the evaluation of the biproduct of copies of the unit,
transported along `biproductIsoFree`. -/
private theorem evaluation_free_eq :
    ε_ (free (R := ringCatSheaf R) I) (free I) =
      ((biproductIsoFree I).inv ⊗ₘ (biproductIsoFree I).inv) ≫
        ε_ (⨁ fun _ : I ↦ 𝟙_ (SheafOfModules.{u} (ringCatSheaf R))) (⨁ fun _ ↦ 𝟙_ _) := by
  -- The evaluation of `exactPairingCongr` whiskers the evaluation of the biproduct pairing by
  -- the two isomorphisms, one on each side.
  rw [tensorHom_def', Category.assoc]
  rfl

/-- The coevaluation of `free I` is the coevaluation of the biproduct of copies of the unit,
transported along `biproductIsoFree`. -/
private theorem coevaluation_free_eq :
    η_ (free (R := ringCatSheaf R) I) (free I) =
      η_ (⨁ fun _ : I ↦ 𝟙_ (SheafOfModules.{u} (ringCatSheaf R))) (⨁ fun _ ↦ 𝟙_ _) ≫
        ((biproductIsoFree I).hom ⊗ₘ (biproductIsoFree I).hom) := by
  -- The coevaluation of `exactPairingCongr` whiskers the coevaluation of the biproduct pairing
  -- by the inverses of the two isomorphisms.
  rw [tensorHom_def', ← Category.assoc]
  rfl

/-- The evaluation of the free sheaf on a finite type pairs each basis section with itself to
`1`. -/
@[reassoc (attr := simp)]
theorem ιFree_tensorHom_ιFree_evaluation (i : I) :
    (ιFree i ⊗ₘ ιFree i) ≫ ε_ (free (R := ringCatSheaf R) I) (free I) =
      (ρ_ (𝟙_ (SheafOfModules.{u} (ringCatSheaf R)))).hom := by
  rw [evaluation_free_eq, tensorHom_comp_tensorHom_assoc, ιFree_biproductIsoFree_inv,
    ExactPairing.biproduct_ι_tensorHom_biproduct_ι_evaluation, ExactPairing.unit_evaluation]

/-- The evaluation of the free sheaf on a finite type pairs distinct basis sections to `0`. -/
@[reassoc (attr := simp)]
theorem ιFree_tensorHom_ιFree_evaluation_of_ne {i j : I} (h : i ≠ j) :
    (ιFree i ⊗ₘ ιFree j) ≫ ε_ (free (R := ringCatSheaf R) I) (free I) = 0 := by
  rw [evaluation_free_eq, tensorHom_comp_tensorHom_assoc, ιFree_biproductIsoFree_inv,
    ιFree_biproductIsoFree_inv, ExactPairing.biproduct_ι_tensorHom_biproduct_ι_evaluation_of_ne h]

/-- The coevaluation of the free sheaf on a finite type is the sum of the tensor squares of the
basis sections. -/
theorem coevaluation_free [Fintype I] :
    η_ (free (R := ringCatSheaf R) I) (free I) =
      ∑ i, (ρ_ (𝟙_ (SheafOfModules.{u} (ringCatSheaf R)))).inv ≫ (ιFree i ⊗ₘ ιFree i) := by
  rw [coevaluation_free_eq, ExactPairing.biproduct_coevaluation, Preadditive.sum_comp]
  simp only [ExactPairing.unit_coevaluation, Category.assoc, tensorHom_comp_tensorHom]
  simp only [tensorUnit_eq, biproduct_ι_biproductIsoFree_hom]

variable (I)

/-- The internal Hom out of a finite free sheaf of modules is tensoring with that sheaf, since
the free sheaf is its own dual. -/
def ihomFreeIso (M : SheafOfModules.{u} (ringCatSheaf R)) :
    (ihom (free (R := ringCatSheaf R) I)).obj M ≅ free (R := ringCatSheaf R) I ⊗ M :=
  (ihomIsoTensorLeft (free I) (free I)).app M

/-- The dual of a finite free sheaf of modules, that is, the internal Hom into the structure
sheaf, is free on the same index type. It is `TauCeti.SheafOfModules.ihomFreeIso` at the
structure sheaf, followed by the right unitor. -/
def dualFreeIso :
    (ihom (free (R := ringCatSheaf R) I)).obj (𝟙_ (SheafOfModules.{u} (ringCatSheaf R))) ≅
      free (R := ringCatSheaf R) I :=
  ihomUnitIso (free I) (free I)

variable {I}

/-- The `i`-th basis section of the dual of `free I`, obtained by transporting the corresponding
basis section along `TauCeti.SheafOfModules.dualFreeIso`. -/
def dualFreeι (i : I) :
    𝟙_ (SheafOfModules.{u} (ringCatSheaf R)) ⟶
      (ihom (free (R := ringCatSheaf R) I)).obj
        (𝟙_ (SheafOfModules.{u} (ringCatSheaf R))) :=
  ιFree i ≫ (dualFreeIso (R := R) I).inv

/-- Transporting a dual basis section back along `TauCeti.SheafOfModules.dualFreeIso` recovers
the corresponding basis section of the free sheaf. -/
@[reassoc (attr := simp)]
theorem dualFreeι_comp_dualFreeIso_hom (i : I) :
    dualFreeι (R := R) i ≫ (dualFreeIso (R := R) I).hom = ιFree i := by
  rw [dualFreeι, Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- The basis sections of the dual sheaf are the dual basis: the `i`-th one evaluates on the
`i`-th basis section of `free I` to `1`. -/
@[reassoc, simp]
theorem ιFree_tensorHom_dualFreeι_comp_ev (i : I) :
    ((ιFree i ⊗ₘ dualFreeι (R := R) i) :
      unit (ringCatSheaf R) ⊗ unit (ringCatSheaf R) ⟶
        free (R := ringCatSheaf R) I ⊗
        (PresheafOfModules.sheafification (𝟙 (ringCatSheaf R).obj)).obj
          ((ihom (free (R := ringCatSheaf R) I).val).obj (unit (ringCatSheaf R)).val)) ≫
      (ihom.ev (free (R := ringCatSheaf R) I)).app
        (unit (ringCatSheaf R)) =
      (ρ_ (𝟙_ (SheafOfModules.{u} (ringCatSheaf R)))).hom := by
  simpa only [dualFreeι, dualFreeIso, tensorUnit_eq, SheafOfModules.ihom_obj] using
    (tensorHom_ihomUnitIso_inv_comp_ev (D := free I) (Y := free I) (ιFree i) (ιFree i)).trans
      (ιFree_tensorHom_ιFree_evaluation (R := R) i)

/-- The basis sections of the dual sheaf are the dual basis: the `j`-th one evaluates on the
`i`-th basis section of `free I` to `0` when `i ≠ j`. -/
@[reassoc, simp]
theorem ιFree_tensorHom_dualFreeι_comp_ev_of_ne {i j : I} (h : i ≠ j) :
    ((ιFree i ⊗ₘ dualFreeι (R := R) j) :
      unit (ringCatSheaf R) ⊗ unit (ringCatSheaf R) ⟶
        free (R := ringCatSheaf R) I ⊗
        (PresheafOfModules.sheafification (𝟙 (ringCatSheaf R).obj)).obj
          ((ihom (free (R := ringCatSheaf R) I).val).obj (unit (ringCatSheaf R)).val)) ≫
      (ihom.ev (free (R := ringCatSheaf R) I)).app
        (unit (ringCatSheaf R)) = 0 := by
  simpa only [dualFreeι, dualFreeIso, tensorUnit_eq, SheafOfModules.ihom_obj] using
    (tensorHom_ihomUnitIso_inv_comp_ev (D := free I) (Y := free I) (ιFree i) (ιFree j)).trans
      (ιFree_tensorHom_ιFree_evaluation_of_ne (R := R) h)

/-- The internal-Hom dual of a sheaf of modules. -/
abbrev _root_.SheafOfModules.dual
    (M : _root_.SheafOfModules.{u} (ringCatSheaf R)) :
    _root_.SheafOfModules.{u} (ringCatSheaf R) :=
  (ihom M).obj (unit (ringCatSheaf R))

/-- An isomorphism of sheaves induces an isomorphism of their duals. -/
def _root_.SheafOfModules.dualIso {M N : _root_.SheafOfModules.{u} (ringCatSheaf R)}
    (e : M ≅ N) : M.dual ≅ N.dual := by
  have hpre : IsIso (pre e.inv) := by
    unfold pre
    infer_instance
  exact asIso ((pre e.inv).app (unit (ringCatSheaf R)))

private lemma ιFree_pUnit_eq_sigma_ι :
    ιFree (R := ringCatSheaf R) PUnit.unit =
      Sigma.ι (fun _ : PUnit.{u + 1} ↦ unit (ringCatSheaf R)) PUnit.unit :=
  rfl

/-- Evaluation of the standard free rank-one sheaf against its dual is an isomorphism. -/
instance _root_.SheafOfModules.isIso_evaluation_dual_freePUnit :
    IsIso ((ihom.ev (free (R := ringCatSheaf R) PUnit)).app
      (unit (ringCatSheaf R))) := by
  let ι := ιFree (R := ringCatSheaf R) PUnit.unit
  have : IsIso ι := by
    dsimp only [ι]
    rw [ιFree_pUnit_eq_sigma_ι, ← coproductUniqueIso_inv
      (fun _ : PUnit.{u + 1} ↦ unit (ringCatSheaf R))]
    exact Iso.isIso_inv _
  let ιdual := dualFreeι (R := R) PUnit.unit
  have : IsIso ιdual := by
    exact IsIso.of_isIso_fac_right (dualFreeι_comp_dualFreeIso_hom (R := R) PUnit.unit)
  have : IsIso (ι ⊗ₘ ιdual) := inferInstance
  have hevaluation := ιFree_tensorHom_dualFreeι_comp_ev (R := R) PUnit.unit
  have : IsIso ((ι ⊗ₘ ιdual) ≫
      (ihom.ev (free (R := ringCatSheaf R) PUnit)).app (unit (ringCatSheaf R))) :=
    hevaluation ▸ inferInstance
  exact IsIso.of_isIso_comp_left (ι ⊗ₘ ιdual)
    ((ihom.ev (free (R := ringCatSheaf R) PUnit)).app (unit (ringCatSheaf R)))

/-- Evaluation against the dual is an isomorphism for a sheaf isomorphic to the standard free
rank-one sheaf. -/
theorem _root_.SheafOfModules.isIso_evaluation_dual_of_iso_freePUnit
    (M : _root_.SheafOfModules.{u} (ringCatSheaf R))
    (e : free (R := ringCatSheaf R) PUnit ≅ M) :
    IsIso ((ihom.ev M).app (unit (ringCatSheaf R))) := by
  have h := id_tensor_pre_app_comp_ev e.hom (unit (ringCatSheaf R))
  have hpre : IsIso (pre e.hom) := by
    unfold pre
    infer_instance
  have : IsIso ((pre e.hom).app (unit (ringCatSheaf R))) :=
    (NatTrans.isIso_iff_isIso_app (pre e.hom)).1 hpre _
  have : IsIso (free (R := ringCatSheaf R) PUnit ◁
      (pre e.hom).app (unit (ringCatSheaf R)) ≫
        (ihom.ev (free (R := ringCatSheaf R) PUnit)).app (unit (ringCatSheaf R))) :=
    inferInstance
  have : IsIso (e.hom ▷ M.dual ≫
      (ihom.ev M).app (unit (ringCatSheaf R))) := h ▸ inferInstance
  exact IsIso.of_isIso_comp_left (e.hom ▷ M.dual)
    ((ihom.ev M).app (unit (ringCatSheaf R)))

end SheafOfModules

end

end TauCeti

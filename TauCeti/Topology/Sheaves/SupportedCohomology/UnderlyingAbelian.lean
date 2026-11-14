/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Sites.SheafCohomology.UnderlyingAbelian
public import TauCeti.Topology.Sheaves.Flasque.Module
import Mathlib.Algebra.FiveLemma

/-!
# Cohomology with supports of a sheaf of modules and of its underlying abelian sheaf

Let `R` be a commutative ring and `F` a sheaf of `R`-modules on a topological space `X`. Its
cohomology with supports in a closed subset `S` can be computed in sheaves of `R`-modules, as
`H_Sⁿ(W, F) = Extⁿ(Q_S(W), F)` (`CategoryTheory.Sheaf.supportedModuleH`), or in abelian sheaves,
as the cohomology with supports of the underlying abelian sheaf of `F`
(`CategoryTheory.Sheaf.supportedH`). This file proves that the two agree.

More generally, for an inclusion of opens `i : U ⟶ V` the comparison
`Extⁿ(R_{V,U}, F) ⟶ Hⁿ(V, U; F)` of `TauCeti.CategoryTheory.relativeExtToForget` is bijective in
every degree (`TauCeti.CategoryTheory.relativeExtToForget_bijective`). In degree zero both sides
are the sections over `V` restricting to zero on `U`. In higher degrees one shifts dimension
along `0 ⟶ F ⟶ I ⟶ I / F ⟶ 0` with `I` an injective sheaf of `R`-modules: `I` has no higher `Ext`
in sheaves of `R`-modules, and its underlying abelian sheaf is flasque, so it has no higher
relative cohomology either; the comparison commutes with the connecting maps, and the five lemma
concludes. The induction follows Mathlib's
`CategoryTheory.Functor.mapExt_bijective_of_preservesInjectiveObjects`, which treats a fully
faithful exact functor preserving injectives.

For cohomology with supports this gives an additive equivalence from `H_Sⁿ(W, F)` computed with
module coefficients to `H_Sⁿ(W, F)` computed with the underlying abelian sheaf
(`CategoryTheory.Sheaf.supportedModuleHAddEquiv`). It is the identity on supported sections in
degree zero, and it is compatible with restriction to smaller opens, with morphisms of coefficient
sheaves and with the connecting maps of short exact sequences of coefficients. As presheaves,
`W ↦ H_Sⁿ(W, F)` computed with module coefficients has underlying presheaf of abelian groups
`W ↦ H_Sⁿ(W, F)` computed with abelian coefficients
(`CategoryTheory.Sheaf.supportedModuleHPresheafForgetIso`). This is how statements about the
abelian theory, such as support truncation, transfer to sheaves of modules.

## Main declarations

* `TauCeti.CategoryTheory.relativeExtToForget_bijective`: the relative comparison is bijective;
* `CategoryTheory.Sheaf.supportedModuleHAddEquiv`: `H_Sⁿ(W, F)` computed with module coefficients
  is additively equivalent to `H_Sⁿ(W, F)` computed with the underlying abelian sheaf;
* `CategoryTheory.Sheaf.supportedModuleHAddEquiv_supportedModuleHPresheaf_map`,
  `CategoryTheory.Sheaf.supportedModuleHAddEquiv_comp`: compatibility with restriction and with
  `Ext` classes between coefficient sheaves;
* `CategoryTheory.Sheaf.supportedModuleHPresheafForgetIso`: the isomorphism of presheaves of
  abelian groups.

## References

* A. Grothendieck, *Sur quelques points d'algèbre homologique*, Tôhoku Math. J. 9 (1957), §3.
* A. Grothendieck, *Local cohomology*, Lecture Notes in Mathematics 41, §1.
* M. Kashiwara and P. Schapira, *Sheaves on Manifolds*, §2.6.
-/

public section

open CategoryTheory Limits Opposite TopologicalSpace Abelian

universe u

namespace TauCeti.CategoryTheory

variable {X : TopCat.{u}} (R : Type u) [CommRing R]

attribute [local instance] Ext.subsingleton_of_injective in
/-- For an inclusion of opens `i : U ⟶ V`, the comparison `Extⁿ(R_{V,U}, F) ⟶ Hⁿ(V, U; F)`
between the relative cohomology of a sheaf of `R`-modules and that of its underlying abelian sheaf
is bijective in every degree. -/
theorem relativeExtToForget_bijective {U V : Opens X} (i : U ⟶ V)
    (F : Sheaf (Opens.grothendieckTopology X) (ModuleCat.{u} R)) (n : ℕ) :
    Function.Bijective (relativeExtToForget.{u, u} _ R i F n) := by
  induction n generalizing F with
  | zero => exact relativeExtToForget_zero_bijective _ R i F
  | succ n hn =>
    -- shift dimension along `0 ⟶ F ⟶ I ⟶ I / F ⟶ 0` with `I` injective
    let Φ := sheafCompose (Opens.grothendieckTopology X) (forget₂ (ModuleCat.{u} R) AddCommGrpCat)
    let S := TauCeti.injectiveCokernelSequence F
    have hS : S.ShortExact := TauCeti.injectiveCokernelSequence_shortExact F
    have hS' : (S.map Φ).ShortExact := Sheaf.shortExact_map_sheafCompose_forget₂_moduleCat hS
    -- the underlying abelian sheaf of `I` is flasque
    have : TopCat.Presheaf.IsFlasque (S.map Φ).X₂.obj := by
      rw [ShortComplex.map_X₂, sheafCompose_obj_obj]
      infer_instance
    exact AddMonoidHom.bijective_of_surjective_of_bijective_of_right_exact _ _ _ _
      (relativeExtToForget _ R i S.X₂ n) (relativeExtToForget _ R i S.X₃ n)
      (relativeExtToForget _ R i S.X₁ (n + 1))
      (AddMonoidHom.ext fun x ↦ by
        simp only [AddMonoidHom.coe_comp, Function.comp_apply, AddCommGrpCat.hom_ofHom,
          AddMonoidHom.flip_apply, Ext.bilinearComp_apply_apply, relativeExtToForget_comp,
          Ext.mapExactFunctor_mk₀, ShortComplex.map_g, Φ])
      (AddMonoidHom.ext fun x ↦ by
        simp only [AddMonoidHom.coe_comp, Function.comp_apply, AddCommGrpCat.hom_ofHom,
          AddMonoidHom.flip_apply, Ext.bilinearComp_apply_apply, relativeExtToForget_comp,
          Ext.mapExactFunctor_extClass _ hS])
      ((ShortComplex.ab_exact_iff_function_exact _).mp
        (Ext.covariant_sequence_exact₃' _ hS n (n + 1) rfl))
      ((ShortComplex.ab_exact_iff_function_exact _).mp
        (Ext.covariant_sequence_exact₃' _ hS' n (n + 1) rfl))
      (hn _).surjective (hn _)
      (fun x₁ ↦ Ext.covariant_sequence_exact₁ _ hS x₁ (Subsingleton.elim _ _) rfl)
      (fun y₁ ↦ Ext.covariant_sequence_exact₁ _ hS' y₁ (Subsingleton.elim _ _) rfl)

end TauCeti.CategoryTheory

namespace CategoryTheory.Sheaf

open TauCeti.CategoryTheory

variable {X : TopCat.{u}} {R : Type u} [CommRing R]
  (F : Sheaf (Opens.grothendieckTopology X) (ModuleCat.{u} R))

noncomputable section

/-- Cohomology with supports in `S` of a sheaf of `R`-modules `F`, computed with module
coefficients, is additively equivalent to the cohomology with supports in `S` of the underlying
abelian sheaf of `F`. -/
def supportedModuleHAddEquiv (S : Closeds X) (W : Opens X) (n : ℕ) :
    F.supportedModuleH S W n ≃+
      ((sheafCompose _ (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u})).obj F).supportedH S W n :=
  AddEquiv.ofBijective (relativeExtToForget _ R (S.complInclusion W) F n)
    (relativeExtToForget_bijective R (S.complInclusion W) F n)

lemma supportedModuleHAddEquiv_apply (S : Closeds X) (W : Opens X) {n : ℕ}
    (x : F.supportedModuleH S W n) :
    F.supportedModuleHAddEquiv S W n x = relativeExtToForget _ R (S.complInclusion W) F n x :=
  (rfl)

/-- In degree zero, the equivalence `supportedModuleHAddEquiv` is the identity on the sections of
`F` supported in `S`. -/
lemma coe_supportedHZeroEquiv_supportedModuleHAddEquiv (S : Closeds X) (W : Opens X)
    (x : F.supportedModuleH S W 0) :
    ((((sheafCompose _ (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u})).obj F).supportedHZeroEquiv S
        W (F.supportedModuleHAddEquiv S W 0 x)).1 : F.obj.obj (op W)) =
      (F.supportedModuleHZeroEquiv S W x).1 := by
  rw [coe_supportedHZeroEquiv_apply, coe_supportedModuleHZeroEquiv_apply]
  exact coe_relativeH'_zeroEquiv_relativeExtToForget _ R (S.complInclusion W) F x

/-- The equivalence `supportedModuleHAddEquiv` commutes with restriction to smaller opens. -/
lemma supportedModuleHAddEquiv_supportedModuleHPresheaf_map (S : Closeds X) {n : ℕ}
    {W W' : (Opens X)ᵒᵖ} (h : W ⟶ W') (x : F.supportedModuleH S W.unop n) :
    F.supportedModuleHAddEquiv S W'.unop n ((F.supportedModuleHPresheaf S n).map h x) =
      ((sheafCompose _ (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u})).obj F).supportedHRestrict S
        (leOfHom h.unop) n (F.supportedModuleHAddEquiv S W.unop n x) := by
  rw [supportedHRestrict_apply, relativeH'.map_apply]
  exact relativeExtToForget_mk₀_relativeFreeModuleYonedaSheafMap_comp _ R
    (S.complInclusion W'.unop) (S.complInclusion W.unop) _ h.unop rfl F x

/-- The equivalence `supportedModuleHAddEquiv` is natural in the coefficients: it carries the
Yoneda product with an `Ext` class between sheaves of `R`-modules, such as a morphism of sheaves or
the connecting class of a short exact sequence, to the Yoneda product with the underlying `Ext`
class of abelian sheaves. -/
lemma supportedModuleHAddEquiv_comp {G : Sheaf (Opens.grothendieckTopology X) (ModuleCat.{u} R)}
    (S : Closeds X) (W : Opens X) {m n k : ℕ} (x : F.supportedModuleH S W m) (α : Ext F G n)
    (h : m + n = k) :
    G.supportedModuleHAddEquiv S W k (x.comp α h) =
      (F.supportedModuleHAddEquiv S W m x).comp
        (α.mapExactFunctor (sheafCompose _ (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}))) h :=
  relativeExtToForget_comp _ R _ x α h

/-- The presheaf `W ↦ H_Sⁿ(W, F)` of a sheaf of `R`-modules, viewed as a presheaf of abelian
groups, is isomorphic to the presheaf `W ↦ H_Sⁿ(W, F)` of its underlying abelian sheaf. -/
def supportedModuleHPresheafForgetIso (S : Closeds X) (n : ℕ) :
    F.supportedModuleHPresheaf S n ⋙ forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u} ≅
      ((sheafCompose _ (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u})).obj F).supportedHPresheaf
        S n :=
  NatIso.ofComponents (fun W ↦ (F.supportedModuleHAddEquiv S W.unop n).toAddCommGrpIso)
    fun {W W'} h ↦ by
      ext x
      exact F.supportedModuleHAddEquiv_supportedModuleHPresheaf_map S h x

@[simp↓]
lemma supportedModuleHPresheafForgetIso_hom_app_apply (S : Closeds X) (n : ℕ) (W : (Opens X)ᵒᵖ)
    (x : F.supportedModuleH S W.unop n) :
    (F.supportedModuleHPresheafForgetIso S n).hom.app W x =
      F.supportedModuleHAddEquiv S W.unop n x :=
  (rfl)

@[simp↓]
lemma supportedModuleHPresheafForgetIso_inv_app_apply (S : Closeds X) (n : ℕ) (W : (Opens X)ᵒᵖ)
    (x : ((sheafCompose _ (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u})).obj F).supportedH S
      W.unop n) :
    (F.supportedModuleHPresheafForgetIso S n).inv.app W x =
      (F.supportedModuleHAddEquiv S W.unop n).symm x :=
  (rfl)

end

end CategoryTheory.Sheaf

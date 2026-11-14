/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Sheaves.Flasque.Module
public import TauCeti.Topology.Sheaves.SupportedCohomology.Sections
import TauCeti.Algebra.Homology.ShortComplex.FunctorCategory
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-!
# The coefficient sequence for module-valued supported cohomology

For an `Ext` class `α : Extⁿ(F, G)` between sheaves of `R`-modules, the Yoneda
product defines a morphism `H_Sᵐ(-, F) ⟶ H_Sᵐ⁺ⁿ(-, G)` of supported cohomology
presheaves (`CategoryTheory.Sheaf.supportedModuleHPresheafPostcomp`), compatible
with open restriction, composition of `Ext` classes, and enlarging the closed
support. For `α = Ext.mk₀ f` this recovers functoriality in the coefficient
sheaf, and for the extension class of a short exact sequence it gives the
connecting morphism (`CategoryTheory.Sheaf.supportedModuleHPresheafδ`).

These maps commute with morphisms of short exact sequences and give an exact
coefficient sequence. A flasque middle term makes the positive-degree connecting
maps dimension-shift isomorphisms and all connecting maps epimorphisms; a
flasque kernel makes the positive-degree quotient maps isomorphisms. Read
through the identification of degree-zero supported cohomology with supported
sections, the degree-zero connecting map `Γ_S(-, F₃) ⟶ H_S¹(-, F₁)` is exact
after `Γ_S(-, F₂) ⟶ Γ_S(-, F₃)`, and surjective when the middle term is flasque.

Sheafification of this sequence is treated in
`TauCeti.Topology.Sheaves.LocalCohomology.LongExactSequence`.

## References

* A. Grothendieck, *Local cohomology*, Lecture Notes in Mathematics 41, §1.
* M. Kashiwara and P. Schapira, *Sheaves on Manifolds*, §2.6.
-/

public section

open CategoryTheory Limits Opposite TopologicalSpace Abelian

universe u

namespace CategoryTheory.Sheaf

variable {X : TopCat.{u}} {R : Type u} [CommRing R] (S : Closeds X)
  {T T' : ShortComplex (Sheaf (Opens.grothendieckTopology X) (ModuleCat.{u} R))}

noncomputable section

/-- The morphism of presheaves `H_Sᵐ(-, F) ⟶ H_Sᵏ(-, G)` given by the Yoneda
product with an `Ext` class `α : Extⁿ(F, G)`, where `m + n = k`. For
`α = Ext.mk₀ f` this is the map induced by a morphism of sheaves `f : F ⟶ G`,
and for the extension class of a short exact sequence it is the connecting
morphism `CategoryTheory.Sheaf.supportedModuleHPresheafδ`. -/
def supportedModuleHPresheafPostcomp
    {F G : Sheaf (Opens.grothendieckTopology X) (ModuleCat.{u} R)} {m n k : ℕ}
    (α : Ext.{u} F G n) (hk : m + n = k) :
    F.supportedModuleHPresheaf S m ⟶ G.supportedModuleHPresheaf S k where
  app W := ModuleCat.ofHom (Ext.postcompOfLinear α R
    ((S.supportedFreeModuleSheafFunctor R).obj W.unop) hk)
  naturality W W' f := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    -- Normalize the source before introducing a class, so rewriting sees Ext
    -- rather than the opaque presheaf object's carrier.
    change ∀ x : F.supportedModuleH S W.unop m,
      ((Ext.mk₀ ((S.supportedFreeModuleSheafFunctor R).map f.unop)).comp x
          (zero_add m)).comp α hk =
        (Ext.mk₀ ((S.supportedFreeModuleSheafFunctor R).map f.unop)).comp
          (x.comp α hk) (zero_add k)
    intro x
    exact Ext.comp_assoc _ x α (zero_add m) hk (by omega)

/-- Evaluating `CategoryTheory.Sheaf.supportedModuleHPresheafPostcomp` on an open `W` computes the
Yoneda product with `α`. -/
@[simp]
lemma supportedModuleHPresheafPostcomp_app_apply
    {F G : Sheaf (Opens.grothendieckTopology X) (ModuleCat.{u} R)} {m n k : ℕ}
    (α : Ext.{u} F G n) (hk : m + n = k) (W : (Opens X)ᵒᵖ)
    (x : F.supportedModuleH S W.unop m) :
    (supportedModuleHPresheafPostcomp S α hk).app W x = x.comp α hk :=
  (rfl)

/-- Yoneda postcomposition with the zero `Ext` class is the zero morphism of presheaves. -/
@[simp]
lemma supportedModuleHPresheafPostcomp_zero
    (F G : Sheaf (Opens.grothendieckTopology X) (ModuleCat.{u} R)) {m n k : ℕ}
    (hk : m + n = k) :
    supportedModuleHPresheafPostcomp S (0 : Ext.{u} F G n) hk = 0 := by
  apply NatTrans.ext
  funext W
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  -- Normalize the domain before introducing a class so `Ext.comp_zero` applies directly.
  change ∀ x : F.supportedModuleH S W.unop m, x.comp (0 : Ext.{u} F G n) hk = 0
  intro x
  exact Ext.comp_zero x _ _ _ hk

/-- For a degree-zero class `Ext.mk₀ f`, Yoneda postcomposition is the map of
supported cohomology presheaves induced by `f`. -/
lemma supportedModuleHPresheafPostcomp_mk₀
    {F G : Sheaf (Opens.grothendieckTopology X) (ModuleCat.{u} R)} (f : F ⟶ G) (n : ℕ) :
    supportedModuleHPresheafPostcomp S (Ext.mk₀ f) (add_zero n) =
      (supportedModuleHPresheafFunctor S n).map f := by
  apply NatTrans.ext
  funext W
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  -- Normalize the domain so both sides evaluate on a supported Ext class.
  change ∀ x : F.supportedModuleH S W.unop n,
    (supportedModuleHPresheafPostcomp S (Ext.mk₀ f) (add_zero n)).app W x =
      ((supportedModuleHPresheafFunctor S n).map f).app W x
  intro x
  rfl

/-- The Yoneda product with the identity class `Ext.mk₀ (𝟙 F)` is the identity
of `H_Sⁿ(-, F)`. -/
@[simp]
lemma supportedModuleHPresheafPostcomp_mk₀_id
    (F : Sheaf (Opens.grothendieckTopology X) (ModuleCat.{u} R)) (n : ℕ) :
    supportedModuleHPresheafPostcomp S (Ext.mk₀ (𝟙 F)) (add_zero n) = 𝟙 _ := by
  apply NatTrans.ext
  funext W
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  -- Normalize the domain before introducing a supported Ext class.
  change ∀ x : F.supportedModuleH S W.unop n, x.comp (Ext.mk₀ (𝟙 F)) (add_zero n) = x
  intro x
  exact Ext.comp_mk₀_id x

/-- Successive Yoneda products with `α : Extⁿ(F, G)` and `β : Extⁿ'(G, H)` agree
with the Yoneda product with `α.comp β : Extᵖ(F, H)`, where `n + n' = p`. -/
@[reassoc]
lemma supportedModuleHPresheafPostcomp_comp
    {F G H : Sheaf (Opens.grothendieckTopology X) (ModuleCat.{u} R)} {m n n' k l p : ℕ}
    (α : Ext.{u} F G n) (β : Ext.{u} G H n') (hk : m + n = k) (hl : k + n' = l)
    (hp : n + n' = p) :
    supportedModuleHPresheafPostcomp S α hk ≫ supportedModuleHPresheafPostcomp S β hl =
      supportedModuleHPresheafPostcomp S (α.comp β hp) (by omega) := by
  apply NatTrans.ext
  funext W
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  -- Normalize the domain before introducing a supported Ext class.
  change ∀ x : F.supportedModuleH S W.unop m,
    (x.comp α hk).comp β hl = x.comp (α.comp β hp) (by omega)
  intro x
  exact Ext.comp_assoc x α β hk hp (by omega)

variable {S} in
/-- Enlarging the support from `Z` to `S` commutes with Yoneda postcomposition. -/
@[reassoc]
lemma supportedModuleHPresheafMap_supportedModuleHPresheafPostcomp {Z : Closeds X}
    (hZS : Z ≤ S) {F G : Sheaf (Opens.grothendieckTopology X) (ModuleCat.{u} R)}
    {m n k : ℕ} (α : Ext.{u} F G n) (hk : m + n = k) :
    F.supportedModuleHPresheafMap hZS m ≫ supportedModuleHPresheafPostcomp S α hk =
      supportedModuleHPresheafPostcomp Z α hk ≫ G.supportedModuleHPresheafMap hZS k := by
  refine NatTrans.ext (funext fun W ↦ ?_)
  rw [NatTrans.comp_app, NatTrans.comp_app]
  refine ConcreteCategory.hom_ext _ _ fun x ↦ ?_
  refine (ConcreteCategory.comp_apply _ _ x).trans ?_
  refine ((congrArg ((supportedModuleHPresheafPostcomp S α hk).app W)
    (F.supportedModuleHPresheafMap_app_apply hZS m W x)).trans
    (supportedModuleHPresheafPostcomp_app_apply S α hk W _)).trans ?_
  refine (Ext.comp_assoc _ x α (zero_add m) hk (by omega)).trans ?_
  exact ((ConcreteCategory.comp_apply _ _ x).trans
    ((congrArg ((G.supportedModuleHPresheafMap hZS k).app W)
      (supportedModuleHPresheafPostcomp_app_apply Z α hk W x)).trans
      (G.supportedModuleHPresheafMap_app_apply hZS k W _))).symm

variable {S} in
/-- Enlarging the support from `Z` to `S` is natural in the coefficient sheaf. -/
@[reassoc]
lemma supportedModuleHPresheafMap_naturality {Z : Closeds X} (hZS : Z ≤ S)
    {F G : Sheaf (Opens.grothendieckTopology X) (ModuleCat.{u} R)} (f : F ⟶ G) (n : ℕ) :
    F.supportedModuleHPresheafMap hZS n ≫ (supportedModuleHPresheafFunctor S n).map f =
      (supportedModuleHPresheafFunctor Z n).map f ≫ G.supportedModuleHPresheafMap hZS n :=
  (congrArg (F.supportedModuleHPresheafMap hZS n ≫ ·)
    (supportedModuleHPresheafPostcomp_mk₀ S f n).symm).trans
    ((supportedModuleHPresheafMap_supportedModuleHPresheafPostcomp hZS (Ext.mk₀ f)
      (add_zero n)).trans
      (congrArg (· ≫ G.supportedModuleHPresheafMap hZS n)
        (supportedModuleHPresheafPostcomp_mk₀ Z f n)))

/-- If the Yoneda products `H_Sᵐ(W, F) ⟶ H_Sᵏ(W, G)` with `α` are bijective for
every open `W`, then `CategoryTheory.Sheaf.supportedModuleHPresheafPostcomp` is
an isomorphism of presheaves. -/
theorem isIso_supportedModuleHPresheafPostcomp
    {F G : Sheaf (Opens.grothendieckTopology X) (ModuleCat.{u} R)} {m n k : ℕ}
    (α : Ext.{u} F G n) (hk : m + n = k)
    (h : ∀ W : Opens X, Function.Bijective
      (α.postcomp ((S.supportedFreeModuleSheafFunctor R).obj W) hk)) :
    IsIso (supportedModuleHPresheafPostcomp S α hk) := by
  have (W : (Opens X)ᵒᵖ) : IsIso ((supportedModuleHPresheafPostcomp S α hk).app W) := by
    rw [ConcreteCategory.isIso_iff_bijective,
      funext (supportedModuleHPresheafPostcomp_app_apply S α hk W)]
    exact h W.unop
  exact NatIso.isIso_of_isIso_app _

/-- An isomorphism of sheaves `f : F ⟶ G` induces an isomorphism of presheaves
`H_Sⁿ(-, F) ≅ H_Sⁿ(-, G)`. -/
instance isIso_supportedModuleHPresheafPostcomp_mk₀
    {F G : Sheaf (Opens.grothendieckTopology X) (ModuleCat.{u} R)} (f : F ⟶ G) [IsIso f]
    (n : ℕ) :
    IsIso (supportedModuleHPresheafPostcomp S (Ext.mk₀ f) (add_zero n)) :=
  isIso_supportedModuleHPresheafPostcomp S _ _ fun _ ↦
    Function.bijective_iff_has_inverse.2 ⟨(Ext.mk₀ (inv f)).postcomp _ (add_zero n),
      fun x ↦ by simp, fun x ↦ by simp⟩

/-- If `F₂` is flasque, the connecting morphism `H_Sᵃ⁺¹(-, F₃) ⟶ H_Sᵏ(-, F₁)`,
for `k = a + 2`, is an isomorphism of presheaves. -/
theorem isIso_supportedModuleHPresheafPostcomp_extClass (hT : T.ShortExact)
    [TopCat.Presheaf.IsFlasque T.X₂.obj] {a k : ℕ} (hk : a + 1 + 1 = k) :
    IsIso (supportedModuleHPresheafPostcomp S hT.extClass hk) :=
  isIso_supportedModuleHPresheafPostcomp S _ _ fun W ↦ by
    subst hk
    exact hT.extClass_postcomp_bijective _ rfl inferInstance inferInstance

/-- If `F₁` is flasque, postcomposing with `Ext.mk₀ T.g` in positive degrees is
an isomorphism of supported cohomology presheaves. -/
theorem isIso_supportedModuleHPresheafPostcomp_mk₀_g (hT : T.ShortExact)
    [TopCat.Presheaf.IsFlasque T.X₁.obj] (n : ℕ) :
    IsIso (supportedModuleHPresheafPostcomp S (Ext.mk₀ T.g) (add_zero (n + 1))) :=
  isIso_supportedModuleHPresheafPostcomp S _ _ fun _ ↦
    ⟨(injective_iff_map_eq_zero _).2 fun x hx ↦ by
        obtain ⟨z, rfl⟩ := Ext.covariant_sequence_exact₂ _ hT x hx
        rw [Subsingleton.elim z 0, Ext.zero_comp],
      fun x ↦ Ext.covariant_sequence_exact₃ _ hT x rfl (Subsingleton.elim _ _)⟩

/-- If `F₁` is flasque, the morphism `H_Sⁿ⁺¹(-, F₂) ⟶ H_Sⁿ⁺¹(-, F₃)` induced by
`F₂ ⟶ F₃` is an isomorphism of presheaves. -/
theorem isIso_supportedModuleHPresheafFunctor_map_g_succ (hT : T.ShortExact)
    [TopCat.Presheaf.IsFlasque T.X₁.obj] (n : ℕ) :
    IsIso ((supportedModuleHPresheafFunctor S (n + 1)).map T.g) := by
  have := isIso_supportedModuleHPresheafPostcomp_mk₀_g S hT n
  rwa [supportedModuleHPresheafPostcomp_mk₀] at this

/-- The connecting morphism of supported cohomology presheaves for a short exact
sequence of coefficient sheaves, given by its Yoneda extension class. -/
def supportedModuleHPresheafδ (hT : T.ShortExact) (n : ℕ) :
    T.X₃.supportedModuleHPresheaf S n ⟶ T.X₁.supportedModuleHPresheaf S (n + 1) :=
  supportedModuleHPresheafPostcomp S hT.extClass rfl

@[simp]
lemma supportedModuleHPresheafδ_app_apply (hT : T.ShortExact) (n : ℕ)
    (W : (Opens X)ᵒᵖ) (x : T.X₃.supportedModuleH S W.unop n) :
    (supportedModuleHPresheafδ S hT n).app W x = x.comp hT.extClass rfl :=
  (rfl)

variable {S} in
/-- Enlarging the support from `Z` to `S` commutes with the connecting morphisms
of a short exact sequence of coefficients. -/
@[reassoc]
lemma supportedModuleHPresheafMap_δ {Z : Closeds X} (hZS : Z ≤ S) (hT : T.ShortExact) (n : ℕ) :
    T.X₃.supportedModuleHPresheafMap hZS n ≫ supportedModuleHPresheafδ S hT n =
      supportedModuleHPresheafδ Z hT n ≫ T.X₁.supportedModuleHPresheafMap hZS (n + 1) :=
  supportedModuleHPresheafMap_supportedModuleHPresheafPostcomp hZS hT.extClass rfl

/-- The connecting morphism is natural in short exact sequences of coefficients. -/
@[reassoc]
lemma supportedModuleHPresheafδ_naturality (hT : T.ShortExact) (hT' : T'.ShortExact)
    (f : T ⟶ T') (n : ℕ) :
    (supportedModuleHPresheafFunctor S n).map f.τ₃ ≫ supportedModuleHPresheafδ S hT' n =
      supportedModuleHPresheafδ S hT n ≫
        (supportedModuleHPresheafFunctor S (n + 1)).map f.τ₁ := by
  apply NatTrans.ext
  funext W
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  -- Normalize the domain before introducing its Ext class, as in the definition.
  change ∀ x : T.X₃.supportedModuleH S W.unop n,
    (x.comp (Ext.mk₀ f.τ₃) (add_zero n)).comp hT'.extClass rfl =
      (x.comp hT.extClass rfl).comp (Ext.mk₀ f.τ₁) (add_zero (n + 1))
  intro x
  exact (Ext.comp_assoc_of_second_deg_zero x _ _ rfl).trans
    ((congrArg (fun a : Ext.{u} T.X₃ T'.X₁ 1 ↦ x.comp a rfl)
      (hT.extClass_naturality hT' f).symm).trans
        (Ext.comp_assoc_of_third_deg_zero x _ _ rfl).symm)

@[simp, reassoc]
lemma supportedModuleHPresheafFunctor_map_g_δ (hT : T.ShortExact) (n : ℕ) :
    (supportedModuleHPresheafFunctor S n).map T.g ≫ supportedModuleHPresheafδ S hT n = 0 := by
  apply NatTrans.ext
  funext W
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  -- Expose the Ext domain before introducing a section of the composite functor.
  change ∀ x : T.X₂.supportedModuleH S W.unop n,
    (x.comp (Ext.mk₀ T.g) (add_zero n)).comp hT.extClass rfl = 0
  intro x
  exact (Ext.comp_assoc_of_second_deg_zero x _ _ rfl).trans
    ((congrArg (fun a : Ext.{u} T.X₂ T.X₁ 1 ↦ x.comp a rfl) hT.comp_extClass).trans
      (Ext.comp_zero x _ _ _ rfl))

@[simp, reassoc]
lemma supportedModuleHPresheafδ_map_f (hT : T.ShortExact) (n : ℕ) :
    supportedModuleHPresheafδ S hT n ≫
      (supportedModuleHPresheafFunctor S (n + 1)).map T.f = 0 := by
  apply NatTrans.ext
  funext W
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  -- Expose the Ext domain before introducing a section of the composite functor.
  change ∀ x : T.X₃.supportedModuleH S W.unop n,
    (x.comp hT.extClass rfl).comp (Ext.mk₀ T.f) (add_zero (n + 1)) = 0
  intro x
  exact (Ext.comp_assoc_of_third_deg_zero x _ _ rfl).trans
    ((congrArg (fun a : Ext.{u} T.X₃ T.X₂ 1 ↦ x.comp a rfl) hT.extClass_comp).trans
      (Ext.comp_zero x _ _ _ rfl))

/-- The coefficient sequence is exact at the middle supported cohomology presheaf. -/
theorem exact_map_supportedModuleHPresheafFunctor (hT : T.ShortExact) (n : ℕ) :
    (T.map (supportedModuleHPresheafFunctor S n)).Exact := by
  rw [ShortComplex.exact_iff_evaluation]
  intro W
  rw [ShortComplex.moduleCat_exact_iff]
  exact fun x hx ↦ Ext.covariant_sequence_exact₂ _ hT x hx

/-- The coefficient sequence is exact immediately before its connecting map. -/
theorem exact_supportedModuleHPresheafFunctor_map_g_δ (hT : T.ShortExact) (n : ℕ) :
    (ShortComplex.mk ((supportedModuleHPresheafFunctor S n).map T.g)
      (supportedModuleHPresheafδ S hT n)
      (supportedModuleHPresheafFunctor_map_g_δ S hT n)).Exact := by
  rw [ShortComplex.exact_iff_evaluation]
  intro W
  rw [ShortComplex.moduleCat_exact_iff]
  exact fun x hx ↦ Ext.covariant_sequence_exact₃ _ hT x rfl hx

/-- The coefficient sequence is exact immediately after its connecting map. -/
theorem exact_supportedModuleHPresheafδ_map_f (hT : T.ShortExact) (n : ℕ) :
    (ShortComplex.mk (supportedModuleHPresheafδ S hT n)
      ((supportedModuleHPresheafFunctor S (n + 1)).map T.f)
      (supportedModuleHPresheafδ_map_f S hT n)).Exact := by
  rw [ShortComplex.exact_iff_evaluation]
  intro W
  rw [ShortComplex.moduleCat_exact_iff]
  exact fun x hx ↦ Ext.covariant_sequence_exact₁ _ hT x hx rfl

/-- A flasque middle term makes the positive-degree connecting morphism an
isomorphism of supported cohomology presheaves. -/
instance isIso_supportedModuleHPresheafδ_succ (hT : T.ShortExact)
    [TopCat.Presheaf.IsFlasque T.X₂.obj] (n : ℕ) :
    IsIso (supportedModuleHPresheafδ S hT (n + 1)) :=
  isIso_supportedModuleHPresheafPostcomp_extClass S hT rfl

/-- The degree-zero connecting morphism `Γ_S(-, F₃) ⟶ H_S¹(-, F₁)` of a short exact sequence
`0 ⟶ F₁ ⟶ F₂ ⟶ F₃ ⟶ 0`, read through the identification of degree-zero supported cohomology
with supported sections. -/
def supportedModuleHPresheafδZero (hT : T.ShortExact) :
    (T.X₃.supportedSubmoduleSheaf S).obj ⟶ T.X₁.supportedModuleHPresheaf S 1 :=
  (T.X₃.supportedModuleHPresheafZeroIso S).inv ≫ supportedModuleHPresheafδ S hT 0

/-- The degree-zero connecting morphism sends a supported section to the Yoneda product of its
degree-zero class with the extension class. -/
lemma supportedModuleHPresheafδZero_app_apply (hT : T.ShortExact) (W : (Opens X)ᵒᵖ)
    (s : T.X₃.supportedSubmodule S W.unop) :
    (supportedModuleHPresheafδZero S hT).app W s =
      ((T.X₃.supportedModuleHZeroEquiv S W.unop).symm s).comp hT.extClass (zero_add 1) :=
  (supportedModuleHPresheafδ_app_apply S hT 0 W _).trans <|
    congrArg (Ext.comp · hT.extClass _)
      (supportedModuleHPresheafZeroIso_inv_app_apply S T.X₃ W s)

/-- Under `CategoryTheory.Sheaf.supportedModuleHZeroEquiv`, the image of a supported section of
`F₂` in `F₃` corresponds to the image of its class. -/
private lemma supportedModuleHZeroEquiv_symm_map_g (W : (Opens X)ᵒᵖ)
    (s : T.X₂.supportedSubmodule S W.unop) :
    (T.X₃.supportedModuleHZeroEquiv S W.unop).symm
        (((supportedSubmoduleFunctor S).map T.g).hom.app W s) =
      ((T.X₂.supportedModuleHZeroEquiv S W.unop).symm s).comp (Ext.mk₀ T.g) (add_zero 0) := by
  refine (LinearEquiv.symm_apply_eq _).2 (Subtype.ext ?_)
  rw [coe_supportedModuleHZeroEquiv_naturality_right, LinearEquiv.apply_symm_apply]
  exact coe_supportedSubmoduleFunctor_map_hom_app_apply S T.g W s

/-- The degree-zero connecting morphism vanishes on the supported sections coming from `F₂`. -/
@[reassoc (attr := simp)]
lemma supportedSubmoduleFunctor_map_g_hom_supportedModuleHPresheafδZero (hT : T.ShortExact) :
    ((supportedSubmoduleFunctor S).map T.g).hom ≫ supportedModuleHPresheafδZero S hT = 0 := by
  ext W s
  refine (supportedModuleHPresheafδZero_app_apply S hT W _).trans <|
    (congrArg (fun z ↦ z.comp hT.extClass (zero_add 1))
      (supportedModuleHZeroEquiv_symm_map_g S W s)).trans ?_
  rw [Ext.comp_assoc_of_second_deg_zero, hT.comp_extClass, Ext.comp_zero]
  rfl

/-- The sequence `Γ_S(W, F₂) ⟶ Γ_S(W, F₃) ⟶ H_S¹(W, F₁)` of a short exact sequence
`0 ⟶ F₁ ⟶ F₂ ⟶ F₃ ⟶ 0` is exact. -/
theorem exact_supportedModuleHPresheafδZero_app (hT : T.ShortExact) (W : (Opens X)ᵒᵖ) :
    (ShortComplex.mk (((supportedSubmoduleFunctor S).map T.g).hom.app W)
      ((supportedModuleHPresheafδZero S hT).app W) (by
        rw [← NatTrans.comp_app, supportedSubmoduleFunctor_map_g_hom_supportedModuleHPresheafδZero,
          NatTrans.app_zero])).Exact := by
  refine (ShortComplex.moduleCat_exact_iff _).2 fun s hs ↦ ?_
  obtain ⟨z, hz⟩ := Ext.covariant_sequence_exact₃ _ hT _ (zero_add 1)
    ((supportedModuleHPresheafδZero_app_apply S hT W s).symm.trans hs)
  refine ⟨T.X₂.supportedModuleHZeroEquiv S W.unop z, ?_⟩
  apply (T.X₃.supportedModuleHZeroEquiv S W.unop).symm.injective
  refine (supportedModuleHZeroEquiv_symm_map_g S W _).trans ?_
  rw [LinearEquiv.symm_apply_apply]
  exact hz

/-- A flasque middle term makes the degree-zero connecting morphism
`Γ_S(W, F₃) ⟶ H_S¹(W, F₁)` surjective. -/
instance epi_supportedModuleHPresheafδZero_app (hT : T.ShortExact)
    [TopCat.Presheaf.IsFlasque T.X₂.obj] (W : (Opens X)ᵒᵖ) :
    Epi ((supportedModuleHPresheafδZero S hT).app W) := by
  refine (ModuleCat.epi_iff_surjective _).2 fun c ↦ ?_
  obtain ⟨y, rfl⟩ := Ext.covariant_sequence_exact₁ _ hT c
    ((subsingleton_supportedModuleH_succ_of_isFlasque T.X₂ S W.unop 0).elim _ _) (zero_add 1)
  refine ⟨T.X₃.supportedModuleHZeroEquiv S W.unop y, ?_⟩
  exact (supportedModuleHPresheafδZero_app_apply S hT W _).trans
    (by rw [LinearEquiv.symm_apply_apply])

/-- A flasque middle term makes the connecting morphism
`H_Sⁿ(-, F₃) ⟶ H_Sⁿ⁺¹(-, F₁)` an epimorphism of presheaves in every degree `n`. -/
instance epi_supportedModuleHPresheafδ (hT : T.ShortExact)
    [TopCat.Presheaf.IsFlasque T.X₂.obj] (n : ℕ) :
    Epi (supportedModuleHPresheafδ S hT n) := by
  rcases n with _ | n
  · have : Epi ((T.X₃.supportedModuleHPresheafZeroIso S).hom ≫
        supportedModuleHPresheafδZero S hT) := by
      have : Epi (supportedModuleHPresheafδZero S hT) := NatTrans.epi_of_epi_app _
      exact epi_comp _ _
    rwa [supportedModuleHPresheafδZero, Iso.hom_inv_id_assoc] at this
  · infer_instance

end

end CategoryTheory.Sheaf

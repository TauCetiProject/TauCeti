/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Sheaves.LocalCohomology.LongExactSequence
import Mathlib.Topology.Sheaves.LocallySurjective
import TauCeti.Topology.Sheaves.Stalks

/-!
# Support truncation and the edge comparison for module coefficients

Let `R` be a commutative ring, `F` a sheaf of `R`-modules on a topological space `X` and `S` a
closed subset. This file relates the cohomology `H_Sⁿ(W, F)` with supports in `S` to the local
cohomology sheaves `𝓗_Sⁿ(F)` when the latter vanish below some degree, keeping the `R`-module
structures throughout. The same statements for sheaves of abelian groups are in
`TauCeti.Topology.Sheaves.LocalCohomology.Basic`.

*Support truncation* says that if `𝓗_S^q(F) = 0` for all `q < n`, then `H_S^q(W, F) = 0` for all
`q < n` and every open `W`. The *edge comparison* says that under the same hypothesis the presheaf
`W ↦ H_Sⁿ(W, F)` is already a sheaf, so the sheafification map is an `R`-linear isomorphism
`H_Sⁿ(W, F) ≃ₗ[R] 𝓗_Sⁿ(F)(W)`, and that for every closed `Z ≤ S` it restricts to an isomorphism
`H_Zⁿ(W, F) ≃ₗ[R] Γ_Z(W, 𝓗_Sⁿ(F))` onto the sections supported in `Z`. For a real-analytic manifold
`M` of dimension `n` in a complexification `X`, where purity gives `𝓗_M^q(𝓞_X) = 0` for `q < n`,
these identify the complex vector space of sections of `𝓗_Mⁿ(𝓞_X)` over `W` with `H_Mⁿ(W, 𝓞_X)`.

Both results are proved by dimension shifting along an embedding `F ⟶ I` into an injective sheaf,
for the more general statements in which `Γ_S(F)` is only assumed flasque and `𝓗_S^q(F) = 0` for
`0 < q < n`. If `𝓗_S¹(F) = 0`, the supported-section functor keeps `0 ⟶ F ⟶ I ⟶ I / F ⟶ 0` short
exact, because a section of `I / F` supported in `S` lifts locally; so `Γ_S(I / F)` is flasque as
a quotient of the flasque sheaf `Γ_S(I)` by `Γ_S(F)`, and the connecting maps
`H_S^q(-, I / F) ⟶ H_S^{q+1}(-, F)` are isomorphisms for `q > 0`. In degree one, for `Γ_S(F)`
flasque, the degree-zero connecting maps identify `H_S¹(-, F)` with the cokernel sheaf of
`Γ_S(I) ⟶ Γ_S(I / F)`, whose sections are computed objectwise.

## Main declarations

* `CategoryTheory.Sheaf.shortExact_map_supportedSubmoduleFunctor`: `Γ_S` preserves a short exact
  sequence `0 ⟶ F₁ ⟶ F₂ ⟶ F₃ ⟶ 0` with `𝓗_S¹(F₁) = 0`;
* `CategoryTheory.Sheaf.subsingleton_supportedModuleH_of_isZero_supportedModuleHSheaf`: support
  truncation;
* `CategoryTheory.Sheaf.isSheaf_supportedModuleHPresheaf_of_isZero_supportedModuleHSheaf`: if
  `𝓗_S^q(F) = 0` for `q < n`, the presheaf `W ↦ H_Sⁿ(W, F)` is a sheaf;
* `CategoryTheory.Sheaf.supportedModuleHSectionsEquiv`: under the same hypothesis,
  `H_Sⁿ(W, F) ≃ₗ[R] 𝓗_Sⁿ(F)(W)`, given by the sheafification map;
* `CategoryTheory.Sheaf.supportedModuleHEdgeEquiv`: the degenerate edge comparison
  `H_Zⁿ(W, F) ≃ₗ[R] Γ_Z(W, 𝓗_Sⁿ(F))` for closed `Z ≤ S`.

## References

* A. Grothendieck, *Local cohomology*, Lecture Notes in Mathematics 41, §1.
* M. Kashiwara and P. Schapira, *Sheaves on Manifolds*, §2.6.
-/

public section

open CategoryTheory Limits Opposite TopologicalSpace Abelian

universe u

namespace CategoryTheory.Sheaf

variable {X : TopCat.{u}} {R : Type u} [CommRing R]
  (F : Sheaf (Opens.grothendieckTopology X) (ModuleCat.{u} R)) (S : Closeds X)

noncomputable section

/-- If the local cohomology sheaf `𝓗_Sⁿ(F)` vanishes, then every class in `H_Sⁿ(W, F)` vanishes
locally: each point `x ∈ W` has an open neighbourhood `V ≤ W` on which the class restricts to
zero. -/
theorem exists_supportedModuleHPresheaf_map_eq_zero_of_isZero_supportedModuleHSheaf {n : ℕ}
    (h : IsZero (F.supportedModuleHSheaf S n)) {W : Opens X} (c : F.supportedModuleH S W n)
    {x : X} (hx : x ∈ W) :
    ∃ (V : Opens X) (hVW : V ≤ W), x ∈ V ∧
      (F.supportedModuleHPresheaf S n).map (homOfLE hVW).op c = 0 :=
  (TopCat.Presheaf.isZero_presheafToSheaf_obj_iff_moduleCat _).1 h x W c hx

/-- If the local cohomology sheaf `𝓗_S⁰(F)` vanishes, so does the presheaf of sections of `F`
supported in `S`. -/
theorem isZero_supportedSubmoduleSheaf_obj (h : IsZero (F.supportedModuleHSheaf S 0)) :
    IsZero (F.supportedSubmoduleSheaf S).obj :=
  (sheafToPresheaf _ _).map_isZero (h.of_iso (F.supportedModuleHSheafZeroIso S).symm)

/-- If the local cohomology sheaf `𝓗_S⁰(F)` vanishes, then the presheaf of sections of `F`
supported in `S` is flasque, being zero. -/
theorem isFlasque_supportedSubmoduleSheaf_obj_of_isZero (h : IsZero (F.supportedModuleHSheaf S 0)) :
    TopCat.Presheaf.IsFlasque (F.supportedSubmoduleSheaf S).obj :=
  TopCat.Presheaf.IsFlasque.of_isZero (F.isZero_supportedSubmoduleSheaf_obj S h)

section truncation

variable {T : ShortComplex (Sheaf (Opens.grothendieckTopology X) (ModuleCat.{u} R))}

/-- The Yoneda product with the extension class of a short exact sequence commutes with
restriction of supported cohomology classes. -/
private lemma supportedModuleHPresheaf_map_comp_extClass (hT : T.ShortExact) {n : ℕ}
    {W W' : (Opens X)ᵒᵖ} (f : W ⟶ W') (c : T.X₃.supportedModuleH S W.unop n) :
    (((T.X₃.supportedModuleHPresheaf S n).map f c : T.X₃.supportedModuleH S W'.unop n).comp
        hT.extClass rfl : T.X₁.supportedModuleH S W'.unop (n + 1)) =
      (T.X₁.supportedModuleHPresheaf S (n + 1)).map f (c.comp hT.extClass rfl) :=
  Ext.comp_assoc _ c hT.extClass (zero_add n) rfl (by omega)

/-- If the middle term of a short exact sequence is flasque, the Yoneda product with its extension
class is bijective on supported cohomology in positive degrees. -/
private lemma bijective_comp_extClass_succ (hT : T.ShortExact) [TopCat.Presheaf.IsFlasque T.X₂.obj]
    (W : Opens X) (n : ℕ) :
    Function.Bijective (fun c : T.X₃.supportedModuleH S W (n + 1) ↦
      (c.comp hT.extClass rfl : T.X₁.supportedModuleH S W (n + 2))) :=
  have := isIso_supportedModuleHPresheafδ_succ S hT n
  have e : (fun c : T.X₃.supportedModuleH S W (n + 1) ↦
      (c.comp hT.extClass rfl : T.X₁.supportedModuleH S W (n + 2))) =
      (supportedModuleHPresheafδ S hT (n + 1)).app (op W) :=
    funext fun c ↦ (supportedModuleHPresheafδ_app_apply S hT (n + 1) (op W) c).symm
  e ▸ (ConcreteCategory.isIso_iff_bijective _).1 inferInstance

/-- If `0 ⟶ F₁ ⟶ F₂ ⟶ F₃ ⟶ 0` is short exact and the local cohomology sheaf `𝓗_S¹(F₁)` vanishes,
then `Γ_S(F₂) ⟶ Γ_S(F₃)` is an epimorphism: a section of `F₃` supported in `S` lifts locally to a
section of `F₂` supported in `S`. -/
theorem epi_supportedSubmoduleFunctor_map_g (hT : T.ShortExact)
    (h : IsZero (T.X₁.supportedModuleHSheaf S 1)) :
    Epi ((supportedSubmoduleFunctor S).map T.g) := by
  refine (TopCat.Sheaf.isLocallySurjective_iff_epi _).1 ?_
  rw [TopCat.Presheaf.isLocallySurjective_iff]
  intro W s x hx
  -- the class `y` of `s` in `H_S⁰(W, F₃)` has image in `H_S¹(W, F₁)` vanishing near `x`
  obtain ⟨y, rfl⟩ := (T.X₃.supportedModuleHZeroEquiv S W).surjective s
  obtain ⟨V, hVW, hxV, hV⟩ :=
    T.X₁.exists_supportedModuleHPresheaf_map_eq_zero_of_isZero_supportedModuleHSheaf S h
      (y.comp hT.extClass rfl) hx
  rw [← supportedModuleHPresheaf_map_comp_extClass S hT] at hV
  -- so near `x` the class `y` comes from a section of `F₂` supported in `S`
  obtain ⟨z, hz⟩ := Ext.covariant_sequence_exact₃ _ hT _ rfl hV
  refine ⟨V, hVW, ⟨T.X₂.supportedModuleHZeroEquiv S V z, Subtype.ext ?_⟩, hxV⟩
  rw [coe_supportedSubmoduleFunctor_map_hom_app_apply,
    ← coe_supportedModuleHZeroEquiv_naturality_right, hz, coe_supportedModuleHZeroEquiv_map]
  rfl

/-- If `0 ⟶ F₁ ⟶ F₂ ⟶ F₃ ⟶ 0` is short exact and the local cohomology sheaf `𝓗_S¹(F₁)` vanishes,
then `0 ⟶ Γ_S(F₁) ⟶ Γ_S(F₂) ⟶ Γ_S(F₃) ⟶ 0` is short exact. -/
theorem shortExact_map_supportedSubmoduleFunctor (hT : T.ShortExact)
    (h : IsZero (T.X₁.supportedModuleHSheaf S 1)) :
    (T.map (supportedSubmoduleFunctor S)).ShortExact :=
  have := hT.mono_f
  { exact := exact_map_supportedSubmoduleFunctor S hT.exact
    mono_f := mono_supportedSubmoduleFunctor_map S T.f
    epi_g := epi_supportedSubmoduleFunctor_map_g S hT h }

/-- If `0 ⟶ F₁ ⟶ F₂ ⟶ F₃ ⟶ 0` is short exact with `F₂` flasque and `𝓗_Sⁿ⁺²(F₁) = 0`, then
`𝓗_Sⁿ⁺¹(F₃) = 0`. -/
theorem isZero_supportedModuleHSheaf_X₃_of_shortExact (hT : T.ShortExact)
    [TopCat.Presheaf.IsFlasque T.X₂.obj] {n : ℕ}
    (h : IsZero (T.X₁.supportedModuleHSheaf S (n + 2))) :
    IsZero (T.X₃.supportedModuleHSheaf S (n + 1)) := by
  refine (TopCat.Presheaf.isZero_presheafToSheaf_obj_iff_moduleCat _).2 fun x W c hx ↦ ?_
  obtain ⟨V, hVW, hxV, hV⟩ :=
    T.X₁.exists_supportedModuleHPresheaf_map_eq_zero_of_isZero_supportedModuleHSheaf S h
      (Ext.comp (c : T.X₃.supportedModuleH S W (n + 1)) hT.extClass rfl) hx
  -- the connecting map commutes with restriction to `V`, where it is injective
  refine ⟨V, hVW, hxV, (bijective_comp_extClass_succ S hT V n).1 ?_⟩
  exact ((supportedModuleHPresheaf_map_comp_extClass S hT _ _).trans hV).trans
    (Ext.zero_comp _ _ _ _ _).symm

/-- If `0 ⟶ F₁ ⟶ F₂ ⟶ F₃ ⟶ 0` is short exact with `F₂` flasque, `Γ_S(F₁)` flasque and
`𝓗_S¹(F₁) = 0`, then `H_S¹(W, F₁) = 0` for every open `W`. This is the base step of
`CategoryTheory.Sheaf.subsingleton_supportedModuleH_succ_of_isZero_supportedModuleHSheaf_succ`,
which states the conclusion without the auxiliary short exact sequence. -/
private theorem subsingleton_supportedModuleH_one_of_shortExact (hT : T.ShortExact)
    [TopCat.Presheaf.IsFlasque T.X₂.obj]
    [TopCat.Presheaf.IsFlasque (T.X₁.supportedSubmoduleSheaf S).obj]
    (h : IsZero (T.X₁.supportedModuleHSheaf S 1)) (W : Opens X) :
    Subsingleton (T.X₁.supportedModuleH S W 1) := by
  refine subsingleton_of_forall_eq 0 fun x ↦ ?_
  -- `x` is the connecting image of a class `y` in `H_S⁰(W, F₃)`, which comes from `H_S⁰(W, F₂)`
  -- because `Γ_S(F₂) ⟶ Γ_S(F₃)` is surjective on sections, `Γ_S(F₁)` being flasque
  obtain ⟨y, rfl⟩ := Ext.covariant_sequence_exact₁ _ hT x
    ((subsingleton_supportedModuleH_succ_of_isFlasque T.X₂ S W 0).elim _ _) (zero_add 1)
  have hΓ := shortExact_map_supportedSubmoduleFunctor S hT h
  have : TopCat.Presheaf.IsFlasque (T.map (supportedSubmoduleFunctor S)).X₁.obj := ‹_›
  obtain ⟨t, ht⟩ := hΓ.surjective_app_of_isFlasque (op W) (T.X₃.supportedModuleHZeroEquiv S W y)
  obtain ⟨z, rfl⟩ := (T.X₂.supportedModuleHZeroEquiv S W).surjective t
  have hy : z.comp (Ext.mk₀ T.g) (add_zero 0) = y :=
    (T.X₃.supportedModuleHZeroEquiv S W).injective <| Subtype.ext <|
      (coe_supportedModuleHZeroEquiv_naturality_right S W T.g z).trans <|
        (coe_supportedSubmoduleFunctor_map_hom_app_apply S T.g (op W) _).symm.trans
          (congrArg Subtype.val ht)
  rw [← hy, Ext.comp_assoc_of_second_deg_zero, hT.comp_extClass, Ext.comp_zero]

/-- The dimension-shifting form of support truncation: if `Γ_S(F)` is flasque and the local
cohomology sheaves `𝓗_S^{q+1}(F)` vanish for `q < n`, then `H_S^{q+1}(W, F) = 0` for every
`q < n` and every open `W`. -/
theorem subsingleton_supportedModuleH_succ_of_isZero_supportedModuleHSheaf_succ
    [TopCat.Presheaf.IsFlasque (F.supportedSubmoduleSheaf S).obj] {n : ℕ}
    (h : ∀ q < n, IsZero (F.supportedModuleHSheaf S (q + 1))) {q : ℕ} (hq : q < n)
    (W : Opens X) : Subsingleton (F.supportedModuleH S W (q + 1)) := by
  induction n generalizing F q with
  | zero => omega
  | succ n ih =>
    -- embed `F` into an injective sheaf `F₂ = I(F)` with quotient `F₃`
    let T := TauCeti.injectiveCokernelSequence F
    have hT : T.ShortExact := TauCeti.injectiveCokernelSequence_shortExact F
    have h₁ : IsZero (T.X₁.supportedModuleHSheaf S 1) := h 0 (by omega)
    have : TopCat.Presheaf.IsFlasque T.X₂.obj := isFlasque_of_injective_moduleCat _
    -- `Γ_S(F₃)` is flasque, as the quotient of the flasque sheaf `Γ_S(F₂)` by `Γ_S(F)`
    have hΓ := shortExact_map_supportedSubmoduleFunctor S hT h₁
    have : TopCat.Presheaf.IsFlasque (T.map (supportedSubmoduleFunctor S)).X₁.obj := ‹_›
    have : TopCat.Presheaf.IsFlasque (T.map (supportedSubmoduleFunctor S)).X₂.obj :=
      isFlasque_supportedSubmoduleSheaf T.X₂ S
    have : TopCat.Presheaf.IsFlasque (T.X₃.supportedSubmoduleSheaf S).obj :=
      hΓ.isFlasque_X₃_of_isFlasque
    rcases q with _ | q
    · exact subsingleton_supportedModuleH_one_of_shortExact S hT h₁ W
    · have := ih T.X₃ (fun q hq ↦ isZero_supportedModuleHSheaf_X₃_of_shortExact S hT
        (h (q + 1) (by omega))) (q := q) (by omega)
      exact (bijective_comp_extClass_succ S hT W q).2.subsingleton

/-- **Support truncation.** If the local cohomology sheaves `𝓗_S^q(F)` vanish for all `q < n`,
then the cohomology modules `H_S^q(W, F)` with supports in `S` vanish for all `q < n` and every
open `W`. -/
theorem subsingleton_supportedModuleH_of_isZero_supportedModuleHSheaf {n : ℕ}
    (h : ∀ q < n, IsZero (F.supportedModuleHSheaf S q)) {q : ℕ} (hq : q < n) (W : Opens X) :
    Subsingleton (F.supportedModuleH S W q) := by
  rcases q with _ | q
  · have : Subsingleton (F.supportedSubmodule S W) := ModuleCat.subsingleton_of_isZero
      ((F.isZero_supportedSubmoduleSheaf_obj S (h 0 (by omega))).obj (op W))
    exact (F.supportedModuleHZeroEquiv S W).injective.subsingleton
  · have := F.isFlasque_supportedSubmoduleSheaf_obj_of_isZero S (h 0 (by omega))
    exact F.subsingleton_supportedModuleH_succ_of_isZero_supportedModuleHSheaf_succ S
      (fun q hq ↦ h (q + 1) (by omega)) (by omega : q < n - 1) W

end truncation

section edge

variable {T : ShortComplex (Sheaf (Opens.grothendieckTopology X) (ModuleCat.{u} R))}

/-- The degree-zero connecting maps `Γ_S(W, F₃) ⟶ H_S¹(W, F₁)` of a short exact sequence
`0 ⟶ F₁ ⟶ F₂ ⟶ F₃ ⟶ 0`, as a morphism of presheaves. -/
private abbrev supportedModuleHPresheafδZero (hT : T.ShortExact) :
    (T.X₃.supportedSubmoduleSheaf S).obj ⟶ T.X₁.supportedModuleHPresheaf S 1 :=
  (T.X₃.supportedModuleHPresheafZeroIso S).inv ≫ supportedModuleHPresheafδ S hT 0

private lemma supportedModuleHPresheafδZero_app_apply (hT : T.ShortExact) (W : (Opens X)ᵒᵖ)
    (s : T.X₃.supportedSubmodule S W.unop) :
    (supportedModuleHPresheafδZero S hT).app W s =
      ((T.X₃.supportedModuleHZeroEquiv S W.unop).symm s).comp hT.extClass (zero_add 1) :=
  (supportedModuleHPresheafδ_app_apply S hT 0 W _).trans <| congrArg (Ext.comp · hT.extClass _) <|
    (LinearEquiv.eq_symm_apply _).2 <| Subtype.ext <|
      (coe_supportedModuleHPresheafZeroIso_hom_app_apply S T.X₃ W _).symm.trans <|
        congrArg Subtype.val (ConcreteCategory.congr_hom
          ((T.X₃.supportedModuleHPresheafZeroIso S).inv_hom_id_app W) s)

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

/-- The short complex `Γ_S(W, F₂) ⟶ Γ_S(W, F₃) ⟶ H_S¹(W, F₁)` of a short exact sequence
`0 ⟶ F₁ ⟶ F₂ ⟶ F₃ ⟶ 0`. -/
private abbrev supportedModuleHδZeroComplex (hT : T.ShortExact) (W : Opens X) :
    ShortComplex (ModuleCat.{u} R) :=
  ShortComplex.mk ((T.map (supportedSubmoduleFunctor S)).g.hom.app (op W))
    ((supportedModuleHPresheafδZero S hT).app (op W)) <| by
      ext s
      refine (supportedModuleHPresheafδZero_app_apply S hT (op W) _).trans <|
        (congrArg (fun z ↦ z.comp hT.extClass (zero_add 1))
          (supportedModuleHZeroEquiv_symm_map_g S (op W) s)).trans ?_
      rw [Ext.comp_assoc_of_second_deg_zero, hT.comp_extClass, Ext.comp_zero]
      rfl

/-- If `F₂` is flasque, the degree-zero connecting map `Γ_S(W, F₃) ⟶ H_S¹(W, F₁)` is surjective
with kernel the image of `Γ_S(W, F₂)`. -/
private lemma exact_supportedModuleHδZeroComplex (hT : T.ShortExact)
    [TopCat.Presheaf.IsFlasque T.X₂.obj] (W : Opens X) :
    (supportedModuleHδZeroComplex S hT W).Exact ∧ Epi (supportedModuleHδZeroComplex S hT W).g := by
  refine ⟨(ShortComplex.moduleCat_exact_iff _).2 fun s hs ↦ ?_,
    (ModuleCat.epi_iff_surjective _).2 fun c ↦ ?_⟩
  · obtain ⟨z, hz⟩ := Ext.covariant_sequence_exact₃ _ hT _ (zero_add 1)
      ((supportedModuleHPresheafδZero_app_apply S hT (op W) s).symm.trans hs)
    refine ⟨T.X₂.supportedModuleHZeroEquiv S W z, ?_⟩
    apply (T.X₃.supportedModuleHZeroEquiv S W).symm.injective
    refine (supportedModuleHZeroEquiv_symm_map_g S (op W) _).trans ?_
    rw [LinearEquiv.symm_apply_apply]
    exact hz
  · obtain ⟨y, rfl⟩ := Ext.covariant_sequence_exact₁ _ hT c
      ((subsingleton_supportedModuleH_succ_of_isFlasque T.X₂ S W 0).elim _ _) (zero_add 1)
    refine ⟨T.X₃.supportedModuleHZeroEquiv S W y, ?_⟩
    exact (supportedModuleHPresheafδZero_app_apply S hT (op W) _).trans
      (by rw [LinearEquiv.symm_apply_apply])

/-- If `F₂` is flasque, `H_S¹(W, F₁)` is the cokernel of `Γ_S(W, F₂) ⟶ Γ_S(W, F₃)`, through the
degree-zero connecting map. -/
private def isColimitSupportedModuleHδZero (hT : T.ShortExact)
    [TopCat.Presheaf.IsFlasque T.X₂.obj] (W : Opens X) :
    IsColimit (CokernelCofork.ofπ _ (supportedModuleHδZeroComplex S hT W).zero) :=
  have := (exact_supportedModuleHδZeroComplex S hT W).2
  (exact_supportedModuleHδZeroComplex S hT W).1.gIsCokernel

/-- If `F₂` and `Γ_S(F₁)` are flasque, the sections over `W` of the cokernel sheaf of
`Γ_S(F₂) ⟶ Γ_S(F₃)` are the cokernel of `Γ_S(W, F₂) ⟶ Γ_S(W, F₃)`. -/
private def isColimitCokernelπApp (hT : T.ShortExact) [TopCat.Presheaf.IsFlasque T.X₂.obj]
    [TopCat.Presheaf.IsFlasque (T.X₁.supportedSubmoduleSheaf S).obj] (W : Opens X) :
    IsColimit (CokernelCofork.ofπ (f := (T.map (supportedSubmoduleFunctor S)).g.hom.app (op W))
      ((cokernel.π (T.map (supportedSubmoduleFunctor S)).g).hom.app (op W))
      (by simp [← NatTrans.comp_app, ← ObjectProperty.FullSubcategory.comp_hom])) :=
  have := hT.mono_f
  have : Mono (T.map (supportedSubmoduleFunctor S)).f := mono_supportedSubmoduleFunctor_map S T.f
  have hT' := exact_map_supportedSubmoduleFunctor S hT.exact
  have : TopCat.Presheaf.IsFlasque (T.map (supportedSubmoduleFunctor S)).X₁.obj := ‹_›
  have : TopCat.Presheaf.IsFlasque (T.map (supportedSubmoduleFunctor S)).X₂.obj :=
    isFlasque_supportedSubmoduleSheaf T.X₂ S
  have : Epi ((cokernel.π (T.map (supportedSubmoduleFunctor S)).g).hom.app (op W)) :=
    (ModuleCat.epi_iff_surjective _).2 (hT'.surjective_cokernel_π_app_of_isFlasque (op W))
  have hex : (ShortComplex.mk ((T.map (supportedSubmoduleFunctor S)).g.hom.app (op W))
      ((cokernel.π (T.map (supportedSubmoduleFunctor S)).g).hom.app (op W))
      (by simp [← NatTrans.comp_app, ← ObjectProperty.FullSubcategory.comp_hom])).Exact :=
    (ShortComplex.moduleCat_exact_iff _).2 fun c hc ↦
      (hT'.exact_cokernel_π_app_of_isFlasque (op W) c).1 hc
  hex.gIsCokernel

/-- If `0 ⟶ F₁ ⟶ F₂ ⟶ F₃ ⟶ 0` is short exact with `F₂` and `Γ_S(F₁)` flasque, `H_S¹(W, F₁)` is
the module of sections over `W` of the cokernel of `Γ_S(F₂) ⟶ Γ_S(F₃)`. -/
private def supportedModuleHOneIsoCokernel (hT : T.ShortExact)
    [TopCat.Presheaf.IsFlasque T.X₂.obj]
    [TopCat.Presheaf.IsFlasque (T.X₁.supportedSubmoduleSheaf S).obj] (W : Opens X) :
    (T.X₁.supportedModuleHPresheaf S 1).obj (op W) ≅
      (cokernel (T.map (supportedSubmoduleFunctor S)).g).obj.obj (op W) :=
  IsColimit.coconePointUniqueUpToIso (isColimitSupportedModuleHδZero S hT W)
    (isColimitCokernelπApp S hT W)

@[reassoc]
private lemma supportedModuleHPresheafδZero_supportedModuleHOneIsoCokernel (hT : T.ShortExact)
    [TopCat.Presheaf.IsFlasque T.X₂.obj]
    [TopCat.Presheaf.IsFlasque (T.X₁.supportedSubmoduleSheaf S).obj] (W : Opens X) :
    (supportedModuleHPresheafδZero S hT).app (op W) ≫ (supportedModuleHOneIsoCokernel S hT W).hom =
      (cokernel.π (T.map (supportedSubmoduleFunctor S)).g).hom.app (op W) :=
  IsColimit.comp_coconePointUniqueUpToIso_hom (isColimitSupportedModuleHδZero S hT W)
    (isColimitCokernelπApp S hT W) WalkingParallelPair.one

/-- If `0 ⟶ F₁ ⟶ F₂ ⟶ F₃ ⟶ 0` is short exact with `F₂` and `Γ_S(F₁)` flasque, the presheaf
`W ↦ H_S¹(W, F₁)` is isomorphic to the cokernel of `Γ_S(F₂) ⟶ Γ_S(F₃)` in sheaves. -/
private def supportedModuleHPresheafOneIsoCokernel (hT : T.ShortExact)
    [TopCat.Presheaf.IsFlasque T.X₂.obj]
    [TopCat.Presheaf.IsFlasque (T.X₁.supportedSubmoduleSheaf S).obj] :
    T.X₁.supportedModuleHPresheaf S 1 ≅ (cokernel (T.map (supportedSubmoduleFunctor S)).g).obj :=
  NatIso.ofComponents (fun W ↦ supportedModuleHOneIsoCokernel S hT W.unop) fun {W W'} f ↦ by
    -- both composites agree after precomposing with the epimorphism `Γ_S(W, F₃) ⟶ H_S¹(W, F₁)`
    have := (exact_supportedModuleHδZeroComplex S hT W.unop).2
    rw [← cancel_epi ((supportedModuleHPresheafδZero S hT).app W), ← NatTrans.naturality_assoc,
      supportedModuleHPresheafδZero_supportedModuleHOneIsoCokernel,
      supportedModuleHPresheafδZero_supportedModuleHOneIsoCokernel_assoc]
    exact (cokernel.π (T.map (supportedSubmoduleFunctor S)).g).hom.naturality f

/-- If `0 ⟶ F₁ ⟶ F₂ ⟶ F₃ ⟶ 0` is short exact with `F₂` and `Γ_S(F₁)` flasque, the presheaf
`W ↦ H_S¹(W, F₁)` is a sheaf: it is isomorphic to the cokernel of `Γ_S(F₂) ⟶ Γ_S(F₃)` in
sheaves. This is the base step of
`CategoryTheory.Sheaf.isSheaf_supportedModuleHPresheaf_succ_of_isZero_supportedModuleHSheaf_succ`,
which states the conclusion without the auxiliary short exact sequence. -/
private theorem isSheaf_supportedModuleHPresheaf_one_of_shortExact (hT : T.ShortExact)
    [TopCat.Presheaf.IsFlasque T.X₂.obj]
    [TopCat.Presheaf.IsFlasque (T.X₁.supportedSubmoduleSheaf S).obj] :
    (T.X₁.supportedModuleHPresheaf S 1).IsSheaf :=
  (Presheaf.isSheaf_of_iso_iff (supportedModuleHPresheafOneIsoCokernel S hT)).2
    (cokernel (T.map (supportedSubmoduleFunctor S)).g).property

/-- The dimension-shifting form of the edge comparison: if `Γ_S(F)` is flasque and the local
cohomology sheaves `𝓗_S^{q+1}(F)` vanish for `q < n`, then the presheaf `W ↦ H_Sⁿ⁺¹(W, F)` is a
sheaf. -/
theorem isSheaf_supportedModuleHPresheaf_succ_of_isZero_supportedModuleHSheaf_succ
    [TopCat.Presheaf.IsFlasque (F.supportedSubmoduleSheaf S).obj] {n : ℕ}
    (h : ∀ q < n, IsZero (F.supportedModuleHSheaf S (q + 1))) :
    (F.supportedModuleHPresheaf S (n + 1)).IsSheaf := by
  induction n generalizing F with
  | zero =>
    have : TopCat.Presheaf.IsFlasque (TauCeti.injectiveCokernelSequence F).X₂.obj :=
      isFlasque_of_injective_moduleCat _
    exact isSheaf_supportedModuleHPresheaf_one_of_shortExact
      (T := TauCeti.injectiveCokernelSequence F) S (TauCeti.injectiveCokernelSequence_shortExact F)
  | succ n ih =>
    -- embed `F` into an injective sheaf `F₂ = I(F)` with quotient `F₃`
    let T := TauCeti.injectiveCokernelSequence F
    have hT : T.ShortExact := TauCeti.injectiveCokernelSequence_shortExact F
    have : TopCat.Presheaf.IsFlasque T.X₂.obj := isFlasque_of_injective_moduleCat _
    -- `Γ_S(F₃)` is flasque, as the quotient of the flasque sheaf `Γ_S(F₂)` by `Γ_S(F)`
    have hΓ := shortExact_map_supportedSubmoduleFunctor S hT (h 0 (by omega))
    have : TopCat.Presheaf.IsFlasque (T.map (supportedSubmoduleFunctor S)).X₁.obj := ‹_›
    have : TopCat.Presheaf.IsFlasque (T.map (supportedSubmoduleFunctor S)).X₂.obj :=
      isFlasque_supportedSubmoduleSheaf T.X₂ S
    have : TopCat.Presheaf.IsFlasque (T.X₃.supportedSubmoduleSheaf S).obj :=
      hΓ.isFlasque_X₃_of_isFlasque
    -- and `H_Sⁿ⁺¹(-, F₃) ≅ H_Sⁿ⁺²(-, F)` by the connecting isomorphism
    have := isIso_supportedModuleHPresheafδ_succ S hT n
    exact (Presheaf.isSheaf_of_iso_iff (asIso (supportedModuleHPresheafδ S hT (n + 1)))).1
      (ih T.X₃ fun q hq ↦ isZero_supportedModuleHSheaf_X₃_of_shortExact S hT (h (q + 1) (by omega)))

/-- If the local cohomology sheaves `𝓗_S^q(F)` vanish for all `q < n`, then the presheaf
`W ↦ H_Sⁿ(W, F)` of cohomology with supports in `S` is already a sheaf. -/
theorem isSheaf_supportedModuleHPresheaf_of_isZero_supportedModuleHSheaf {n : ℕ}
    (h : ∀ q < n, IsZero (F.supportedModuleHSheaf S q)) :
    (F.supportedModuleHPresheaf S n).IsSheaf := by
  rcases n with _ | n
  · exact F.isSheaf_supportedModuleHPresheaf_zero S
  · have := F.isFlasque_supportedSubmoduleSheaf_obj_of_isZero S (h 0 (by omega))
    exact F.isSheaf_supportedModuleHPresheaf_succ_of_isZero_supportedModuleHSheaf_succ S
      fun q hq ↦ h (q + 1) (by omega)

variable {n : ℕ}

/-- **Edge comparison.** If the local cohomology sheaves `𝓗_S^q(F)` vanish for all `q < n`, the
sheafification map identifies `H_Sⁿ(W, F)` with the sections of `𝓗_Sⁿ(F)` over `W`. -/
def supportedModuleHSectionsEquiv (h : ∀ q < n, IsZero (F.supportedModuleHSheaf S q))
    (W : Opens X) :
    F.supportedModuleH S W n ≃ₗ[R] (F.supportedModuleHSheaf S n).obj.obj (op W) :=
  have := isIso_toSheafify _
    (F.isSheaf_supportedModuleHPresheaf_of_isZero_supportedModuleHSheaf S h)
  (asIso ((toSheafify _ (F.supportedModuleHPresheaf S n)).app (op W))).toLinearEquiv

/-- The edge comparison `H_Sⁿ(W, F) ≃ₗ[R] 𝓗_Sⁿ(F)(W)` is the sheafification map. -/
@[simp]
lemma supportedModuleHSectionsEquiv_apply (h : ∀ q < n, IsZero (F.supportedModuleHSheaf S q))
    (W : Opens X) (x : F.supportedModuleH S W n) :
    F.supportedModuleHSectionsEquiv S h W x =
      (toSheafify (Opens.grothendieckTopology X) (F.supportedModuleHPresheaf S n)).app (op W) x :=
  (rfl)

/-- The edge comparison `H_Sⁿ(W, F) ≃ₗ[R] 𝓗_Sⁿ(F)(W)` is compatible with restriction to a smaller
open `W' ≤ W`. -/
lemma supportedModuleHSectionsEquiv_map (h : ∀ q < n, IsZero (F.supportedModuleHSheaf S q))
    {W' W : Opens X} (hW : W' ≤ W) (x : F.supportedModuleH S W n) :
    F.supportedModuleHSectionsEquiv S h W'
        ((F.supportedModuleHPresheaf S n).map (homOfLE hW).op x) =
      (F.supportedModuleHSheaf S n).obj.map (homOfLE hW).op
        (F.supportedModuleHSectionsEquiv S h W x) :=
  congr($((toSheafify _ (F.supportedModuleHPresheaf S n)).naturality (homOfLE hW).op) x)

variable {S} {Z : Closeds X}

/-- If the local cohomology sheaves `𝓗_S^q(F)` vanish for all `q < n`, then enlarging the
support `H_Zⁿ(W, F) ⟶ H_Sⁿ(W, F)` is injective for every closed `Z ≤ S`. -/
theorem supportedModuleHPresheafMap_app_injective_of_isZero_supportedModuleHSheaf
    (h : ∀ q < n, IsZero (F.supportedModuleHSheaf S q)) (hZS : Z ≤ S) (W : Opens X) :
    Function.Injective ((F.supportedModuleHPresheafMap hZS n).app (op W)) := by
  rcases n with _ | m
  · -- in degree zero, enlarging the support is the inclusion `Γ_Z(W, F) ≤ Γ_S(W, F)`
    intro x y hxy
    refine (F.supportedModuleHZeroEquiv Z W).injective (Subtype.ext ?_)
    exact (F.coe_supportedModuleHZeroEquiv_supportedModuleHPresheafMap_app hZS W x).symm.trans
      ((congrArg (fun z ↦ (F.supportedModuleHZeroEquiv S W z : F.obj.obj (op W))) hxy).trans
        (F.coe_supportedModuleHZeroEquiv_supportedModuleHPresheafMap_app hZS W y))
  · -- the kernel is the image of `H_Sᵐ(W ∖ Z, F)`, which vanishes by support truncation
    refine (injective_iff_map_eq_zero _).2 fun x hx ↦ ?_
    obtain ⟨y, rfl⟩ :=
      (F.exact_supportedModuleHδ_supportedModuleHPresheafMap_app hZS W (add_comm 1 m) x).1 hx
    have := F.subsingleton_supportedModuleH_of_isZero_supportedModuleHSheaf S h
      (Nat.lt_succ_self m) (W ⊓ Z.compl)
    rw [Subsingleton.elim y 0]
    exact map_zero _

/-- **Degenerate edge comparison.** If the local cohomology sheaves `𝓗_S^q(F)` vanish for all
`q < n`, then for every closed `Z ≤ S` the cohomology `H_Zⁿ(W, F)` with supports in `Z` is the
module `Γ_Z(W, 𝓗_Sⁿ(F))` of sections of `𝓗_Sⁿ(F)` over `W` supported in `Z`, through enlarging
the support to `S` and the sheafification map. -/
def supportedModuleHEdgeEquiv (h : ∀ q < n, IsZero (F.supportedModuleHSheaf S q)) (hZS : Z ≤ S)
    (W : Opens X) :
    F.supportedModuleH Z W n ≃ₗ[R] (F.supportedModuleHSheaf S n).supportedSubmodule Z W :=
  LinearEquiv.ofBijective
    (((F.supportedModuleHSectionsEquiv S h W).toLinearMap.comp
      ((F.supportedModuleHPresheafMap hZS n).app (op W)).hom).codRestrict _ fun x ↦ by
        -- the restriction to `W ∖ Z` of a class with supports in `Z` vanishes
        rw [mem_supportedSubmodule_iff]
        refine (F.supportedModuleHSectionsEquiv_map S h inf_le_left _).symm.trans ?_
        exact (congrArg _ ((F.exact_supportedModuleHPresheafMap_app_supportedModuleHPresheaf_map
          hZS W n).apply_apply_eq_zero x)).trans (map_zero _))
    ⟨fun x y hxy ↦ F.supportedModuleHPresheafMap_app_injective_of_isZero_supportedModuleHSheaf
      h hZS W ((F.supportedModuleHSectionsEquiv S h W).injective (congrArg Subtype.val hxy)),
      fun s ↦ by
        obtain ⟨y, hy⟩ := (F.supportedModuleHSectionsEquiv S h W).surjective s
        -- a class with supports in `S` comes from `Z` if it restricts to zero on `W ∖ Z`
        obtain ⟨x, rfl⟩ :=
          (F.exact_supportedModuleHPresheafMap_app_supportedModuleHPresheaf_map hZS W n y).1 <|
            (F.supportedModuleHSectionsEquiv S h _).injective <| by
              rw [supportedModuleHSectionsEquiv_map, hy]
              exact ((mem_supportedSubmodule_iff _).1 s.2).trans (map_zero _).symm
        exact ⟨x, Subtype.ext hy⟩⟩

/-- The degenerate edge comparison enlarges the support from `Z` to `S` and then applies the
sheafification map. -/
@[simp]
lemma coe_supportedModuleHEdgeEquiv_apply (h : ∀ q < n, IsZero (F.supportedModuleHSheaf S q))
    (hZS : Z ≤ S) (W : Opens X) (x : F.supportedModuleH Z W n) :
    (F.supportedModuleHEdgeEquiv h hZS W x : (F.supportedModuleHSheaf S n).obj.obj (op W)) =
      F.supportedModuleHSectionsEquiv S h W ((F.supportedModuleHPresheafMap hZS n).app (op W) x) :=
  (rfl)

/-- The degenerate edge comparison `H_Zⁿ(W, F) ≃ₗ[R] Γ_Z(W, 𝓗_Sⁿ(F))` is compatible with
restriction to a smaller open `W' ≤ W`. -/
lemma coe_supportedModuleHEdgeEquiv_map (h : ∀ q < n, IsZero (F.supportedModuleHSheaf S q))
    (hZS : Z ≤ S) {W' W : Opens X} (hW : W' ≤ W) (x : F.supportedModuleH Z W n) :
    (F.supportedModuleHEdgeEquiv h hZS W'
        ((F.supportedModuleHPresheaf Z n).map (homOfLE hW).op x) :
        (F.supportedModuleHSheaf S n).obj.obj (op W')) =
      (F.supportedModuleHSheaf S n).obj.map (homOfLE hW).op
        (F.supportedModuleHEdgeEquiv h hZS W x) :=
  (F.coe_supportedModuleHEdgeEquiv_apply h hZS W' _).trans <|
    (congrArg (F.supportedModuleHSectionsEquiv S h W')
      congr($((F.supportedModuleHPresheafMap hZS n).naturality (homOfLE hW).op) x)).trans
        (F.supportedModuleHSectionsEquiv_map S h hW _)

end edge

end

end CategoryTheory.Sheaf

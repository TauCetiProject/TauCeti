/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Sheaves.LocalCohomology.LongExactSequence

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
exact (`CategoryTheory.Sheaf.shortExact_map_supportedSubmoduleFunctor`); so `Γ_S(I / F)` is
flasque as a quotient of the flasque sheaf `Γ_S(I)` by `Γ_S(F)`, and the connecting maps
`H_S^q(-, I / F) ⟶ H_S^{q+1}(-, F)` are isomorphisms for `q > 0`. In degree one, for `Γ_S(F)`
flasque, the degree-zero connecting maps identify `H_S¹(-, F)` with the cokernel sheaf of
`Γ_S(I) ⟶ Γ_S(I / F)`, whose sections are computed objectwise.

## Main declarations

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

section truncation

variable {T : ShortComplex (Sheaf (Opens.grothendieckTopology X) (ModuleCat.{u} R))}

/-- If `0 ⟶ F₁ ⟶ F₂ ⟶ F₃ ⟶ 0` is short exact with `F₂` flasque, `Γ_S(F₁)` flasque and
`𝓗_S¹(F₁) = 0`, then `H_S¹(W, F₁) = 0` for every open `W`. This is the base step of
`CategoryTheory.Sheaf.subsingleton_supportedModuleH_succ_of_isZero_supportedModuleHSheaf_succ`,
which states the conclusion without the auxiliary short exact sequence. -/
private theorem subsingleton_supportedModuleH_one_of_shortExact (hT : T.ShortExact)
    [TopCat.Presheaf.IsFlasque T.X₂.obj]
    [TopCat.Presheaf.IsFlasque (T.X₁.supportedSubmoduleSheaf S).obj]
    (h : IsZero (T.X₁.supportedModuleHSheaf S 1)) (W : Opens X) :
    Subsingleton (T.X₁.supportedModuleH S W 1) := by
  refine subsingleton_of_forall_eq 0 fun c ↦ ?_
  -- `c` is the connecting image of a section of `F₃` supported in `S`, which comes from `F₂`
  -- because `Γ_S(F₂) ⟶ Γ_S(F₃)` is surjective on sections, `Γ_S(F₁)` being flasque
  obtain ⟨s, rfl⟩ := (ModuleCat.epi_iff_surjective _).1
    (epi_supportedModuleHPresheafδZero_app S hT (op W)) c
  have hΓ := shortExact_map_supportedSubmoduleFunctor S hT h
  have : TopCat.Presheaf.IsFlasque (T.map (supportedSubmoduleFunctor S)).X₁.obj := ‹_›
  obtain ⟨t, rfl⟩ := hΓ.surjective_app_of_isFlasque (op W) s
  exact ConcreteCategory.congr_hom (NatTrans.congr_app
    (supportedSubmoduleFunctor_map_g_hom_supportedModuleHPresheafδZero S hT) (op W)) t

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
    · have hsub := ih T.X₃ (fun q hq ↦ isZero_supportedModuleHSheaf_X₃_of_shortExact S hT
        (h (q + 1) (by omega))) (q := q) (by omega)
      have := isIso_supportedModuleHPresheafδ_succ S hT q
      exact ((asIso (supportedModuleHPresheafδ S hT (q + 1))).app (op W)).toLinearEquiv.toEquiv
        |>.subsingleton_congr.mp hsub

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

/-- If `F₂` is flasque, `H_S¹(W, F₁)` is the cokernel of `Γ_S(W, F₂) ⟶ Γ_S(W, F₃)`, through the
degree-zero connecting map. -/
private def isColimitSupportedModuleHδZero (hT : T.ShortExact)
    [TopCat.Presheaf.IsFlasque T.X₂.obj] (W : Opens X) :
    IsColimit (CokernelCofork.ofπ (f := ((supportedSubmoduleFunctor S).map T.g).hom.app (op W))
      ((supportedModuleHPresheafδZero S hT).app (op W)) (by
        rw [← NatTrans.comp_app, supportedSubmoduleFunctor_map_g_hom_supportedModuleHPresheafδZero,
          NatTrans.app_zero])) :=
  (exact_supportedModuleHPresheafδZero_app S hT (op W)).gIsCokernel

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

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Sheaves.LocalCohomology.LongExactSequence
import Mathlib.CategoryTheory.Abelian.DiagramLemmas.Four
import TauCeti.Topology.Sheaves.SupportedCohomology.Composition

/-!
# Support truncation and the edge comparison for module coefficients

Let `R` be a commutative ring, `F` a sheaf of `R`-modules on a topological space `X` and `S` a
closed subset. This file relates the cohomology `H_Sⁿ(W, F)` with supports in `S` to the local
cohomology sheaves `𝓗_Sⁿ(F)` when the latter vanish below some degree or outside a single degree,
keeping the `R`-module structures throughout. The same statements for sheaves of abelian groups are
in `TauCeti.Topology.Sheaves.LocalCohomology.Basic`.

*Support truncation* says that if `𝓗_S^q(F) = 0` for all `q < n`, then `H_Z^q(W, F) = 0` for all
`q < n`, every closed `Z ≤ S`, and every open `W`. The *edge comparison* says that under the same
hypothesis the presheaf `W ↦ H_Sⁿ(W, F)` is already a sheaf, so the sheafification map is an
`R`-linear isomorphism `H_Sⁿ(W, F) ≃ₗ[R] 𝓗_Sⁿ(F)(W)`, and that for every closed `Z ≤ S` it
restricts to an isomorphism `H_Zⁿ(W, F) ≃ₗ[R] Γ_Z(W, 𝓗_Sⁿ(F))` onto the sections supported in `Z`.
When moreover `𝓗_S^q(F) = 0` for all `q ≠ n`, the *degenerate edge comparison* identifies
`H_Z^{n+j}(-, F)` with `H_Z^j(-, 𝓗_Sⁿ(F))` in every degree `j`, both as presheaves of `R`-modules
and after sheafification; in particular, if `𝓗_Sⁿ(F)` is flasque, `H_Z^k(W, F) = 0` for all
`k ≠ n`. For a real-analytic manifold `M` of dimension `n` in a complexification `X`, where purity
gives `𝓗_M^q(𝓞_X) = 0` for `q ≠ n`, these identify the complex vector space of sections of
`𝓗_Mⁿ(𝓞_X)` over `W` supported in `Z ≤ M` with `H_Zⁿ(W, 𝓞_X)` and reduce the flasqueness of
`𝓗_Mⁿ(𝓞_X)` to the vanishing of `H_Z^{n+1}(W, 𝓞_X)`.

The proofs proceed by dimension shifting along an embedding `F ⟶ I` into an injective sheaf, for
the more general statements in which `Γ_S(F)` is only assumed flasque and `𝓗_S^q(F)` vanishes in
the relevant positive degrees. If `𝓗_S¹(F) = 0`, the supported-section functor keeps
`0 ⟶ F ⟶ I ⟶ I / F ⟶ 0` short exact
(`CategoryTheory.Sheaf.shortExact_map_supportedSubmoduleFunctor`); so `Γ_S(I / F)` is flasque as a
quotient of the flasque sheaf `Γ_S(I)` by `Γ_S(F)`, and the connecting maps
`H_S^q(-, I / F) ⟶ H_S^{q+1}(-, F)` are isomorphisms for `q > 0`. In degree one, for `Γ_S(F)`
flasque, the degree-zero connecting maps identify `H_S¹(-, F)` and `𝓗_S¹(F)` with the cokernel
sheaf of `Γ_S(I) ⟶ Γ_S(I / F)`, whose sections are computed objectwise and whose kernel image is
flasque.

## Main declarations

* `CategoryTheory.Sheaf.subsingleton_supportedModuleH_of_isZero_supportedModuleHSheaf` and
  `CategoryTheory.Sheaf.subsingleton_supportedModuleH_of_isZero_supportedModuleHSheaf_of_le`:
  support truncation on `S` and on any closed `Z ≤ S`;
* `CategoryTheory.Sheaf.isSheaf_supportedModuleHPresheaf_of_isZero_supportedModuleHSheaf`: if
  `𝓗_S^q(F) = 0` for `q < n`, the presheaf `W ↦ H_Sⁿ(W, F)` is a sheaf;
* `CategoryTheory.Sheaf.supportedModuleHSectionsEquiv`: under the same hypothesis,
  `H_Sⁿ(W, F) ≃ₗ[R] 𝓗_Sⁿ(F)(W)`, given by the sheafification map;
* `CategoryTheory.Sheaf.supportedModuleHEdgeEquiv` and
  `CategoryTheory.Sheaf.supportedModuleHEdgePresheafIso`: the degree-zero degenerate edge
  comparison `H_Zⁿ(W, F) ≃ₗ[R] Γ_Z(W, 𝓗_Sⁿ(F))` for closed `Z ≤ S`;
* `CategoryTheory.Sheaf.isIso_supportedModuleHPresheafFunctor_map_supportedSubmoduleι`: when
  `𝓗_S^q(F) = 0` for `q > 0`, the inclusion `Γ_S(F) ⟶ F` induces `H_Z^j(-, Γ_S(F)) ≅ H_Z^j(-, F)`
  for closed `Z ≤ S`;
* `CategoryTheory.Sheaf.supportedModuleHPresheafEdgeIso`,
  `CategoryTheory.Sheaf.supportedModuleHHigherEdgeEquiv` and
  `CategoryTheory.Sheaf.supportedModuleHSheafEdgeIso`: when `𝓗_S^q(F) = 0` for `q ≠ n` and
  `Z ≤ S`, the degenerate edge comparison `H_Z^{n+j}(-, F) ≅ H_Z^j(-, 𝓗_Sⁿ(F))` on presheaves,
  sections, and local cohomology sheaves;
* `CategoryTheory.Sheaf.subsingleton_supportedModuleH_of_ne_of_isFlasque` and
  `CategoryTheory.Sheaf.isZero_supportedModuleHSheaf_of_ne_of_isFlasque`: vanishing of
  `H_Z^k(W, F)` and `𝓗_Z^k(F)` for `k ≠ n` when `𝓗_Sⁿ(F)` is also flasque.

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

/-- If `0 ⟶ F₁ ⟶ F₂ ⟶ F₃ ⟶ 0` is short exact with `F₂` and `Γ_S(F₁)` flasque, the local
cohomology sheaf `𝓗_S¹(F₁)` is the cokernel of `Γ_S(F₂) ⟶ Γ_S(F₃)`. -/
private def supportedModuleHSheafOneIsoCokernel (hT : T.ShortExact)
    [TopCat.Presheaf.IsFlasque T.X₂.obj]
    [TopCat.Presheaf.IsFlasque (T.X₁.supportedSubmoduleSheaf S).obj] :
    T.X₁.supportedModuleHSheaf S 1 ≅ cokernel (T.map (supportedSubmoduleFunctor S)).g :=
  (presheafToSheaf _ _).mapIso (supportedModuleHPresheafOneIsoCokernel S hT) ≪≫
    (sheafificationIso _).symm

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

/-- **Support truncation for closed subsets.** If the local cohomology sheaves `𝓗_S^q(F)` vanish
for all `q < n`, then for every closed `Z ≤ S` the cohomology modules `H_Z^q(W, F)` with supports
in `Z` vanish for all `q < n` and every open `W`. -/
theorem subsingleton_supportedModuleH_of_isZero_supportedModuleHSheaf_of_le
    (h : ∀ q < n, IsZero (F.supportedModuleHSheaf S q)) (hZS : Z ≤ S) {q : ℕ} (hq : q < n)
    (W : Opens X) : Subsingleton (F.supportedModuleH Z W q) := by
  have : Subsingleton ((F.supportedModuleHPresheaf S q).obj (op W)) :=
    F.subsingleton_supportedModuleH_of_isZero_supportedModuleHSheaf S h hq W
  exact (F.supportedModuleHPresheafMap_app_injective_of_isZero_supportedModuleHSheaf
    (fun i hi ↦ h i (hi.trans hq)) hZS W).subsingleton

/-- If the local cohomology sheaves `𝓗_S^q(F)` vanish for all `q < n`, then `𝓗_Z^q(F) = 0` for
all `q < n` and every closed `Z ≤ S`. -/
theorem isZero_supportedModuleHSheaf_of_isZero_supportedModuleHSheaf_of_le
    (h : ∀ q < n, IsZero (F.supportedModuleHSheaf S q)) (hZS : Z ≤ S) {q : ℕ} (hq : q < n) :
    IsZero (F.supportedModuleHSheaf Z q) := by
  apply Functor.map_isZero
  refine (Functor.isZero_iff _).2 fun W ↦ ?_
  rw [F.supportedModuleHPresheaf_obj]
  have := F.subsingleton_supportedModuleH_of_isZero_supportedModuleHSheaf_of_le h hZS hq W.unop
  exact ModuleCat.isZero_iff_subsingleton.2 inferInstance

/-- **Degenerate edge comparison on presheaves in degree zero.** If the local cohomology sheaves
`𝓗_S^q(F)` vanish for all `q < n`, then for every closed `Z ≤ S` the presheaf `W ↦ H_Zⁿ(W, F)` is
isomorphic to the presheaf `W ↦ Γ_Z(W, 𝓗_Sⁿ(F))` of sections of `𝓗_Sⁿ(F)` supported in `Z`, via
`CategoryTheory.Sheaf.supportedModuleHEdgeEquiv`. -/
def supportedModuleHEdgePresheafIso (h : ∀ q < n, IsZero (F.supportedModuleHSheaf S q))
    (hZS : Z ≤ S) :
    F.supportedModuleHPresheaf Z n ≅
      ((F.supportedModuleHSheaf S n).supportedSubmoduleSheaf Z).obj :=
  NatIso.ofComponents (fun W ↦ (F.supportedModuleHEdgeEquiv h hZS W.unop).toModuleIso) fun f ↦ by
    ext x
    exact Subtype.ext (F.coe_supportedModuleHEdgeEquiv_map h hZS (leOfHom f.unop) x)

/-- On sections over `W`, `CategoryTheory.Sheaf.supportedModuleHEdgePresheafIso` acts by
`CategoryTheory.Sheaf.supportedModuleHEdgeEquiv`. -/
@[simp]
lemma supportedModuleHEdgePresheafIso_hom_app_apply
    (h : ∀ q < n, IsZero (F.supportedModuleHSheaf S q)) (hZS : Z ≤ S) (W : (Opens X)ᵒᵖ)
    (x : F.supportedModuleH Z W.unop n) :
    (F.supportedModuleHEdgePresheafIso h hZS).hom.app W x =
      F.supportedModuleHEdgeEquiv h hZS W.unop x :=
  (rfl)

/-- On supported sections over `W`, the inverse of
`CategoryTheory.Sheaf.supportedModuleHEdgePresheafIso` acts by the inverse of
`CategoryTheory.Sheaf.supportedModuleHEdgeEquiv`. -/
@[simp]
lemma supportedModuleHEdgePresheafIso_inv_app_apply
    (h : ∀ q < n, IsZero (F.supportedModuleHSheaf S q)) (hZS : Z ≤ S) (W : (Opens X)ᵒᵖ)
    (s : (F.supportedModuleHSheaf S n).supportedSubmodule Z W.unop) :
    (F.supportedModuleHEdgePresheafIso h hZS).inv.app W s =
      (F.supportedModuleHEdgeEquiv h hZS W.unop).symm s :=
  (rfl)

/-- If the local cohomology sheaves `𝓗_S^q(F)` vanish for all `q < n`, then for every closed
`Z ≤ S` the presheaf `W ↦ H_Zⁿ(W, F)` of cohomology with supports in `Z` is already a sheaf. -/
theorem isSheaf_supportedModuleHPresheaf_of_isZero_supportedModuleHSheaf_of_le
    (h : ∀ q < n, IsZero (F.supportedModuleHSheaf S q)) (hZS : Z ≤ S) :
    (F.supportedModuleHPresheaf Z n).IsSheaf :=
  (Presheaf.isSheaf_of_iso_iff (F.supportedModuleHEdgePresheafIso h hZS)).2
    ((F.supportedModuleHSheaf S n).supportedSubmoduleSheaf Z).property

end edge

section higherEdge

variable {S} {Z : Closeds X}

/-- **Degenerate edge comparison for `n = 0`.** If the local cohomology sheaves `𝓗_S^q(F)`
vanish for all `q > 0`, then for every closed `Z ≤ S` the inclusion `Γ_S(F) ⟶ F` induces an
isomorphism of presheaves `H_Z^j(-, Γ_S(F)) ≅ H_Z^j(-, F)` in every degree `j`. -/
theorem isIso_supportedModuleHPresheafFunctor_map_supportedSubmoduleι
    (h : ∀ q, IsZero (F.supportedModuleHSheaf S (q + 1))) (hZS : Z ≤ S) (j : ℕ) :
    IsIso ((supportedModuleHPresheafFunctor Z j).map (F.supportedSubmoduleι S)) := by
  induction j generalizing F with
  | zero =>
    have hg₁ : IsIso (((supportedSubmoduleFunctor Z).map (F.supportedSubmoduleι S)).hom) :=
      (ObjectProperty.isIso_hom_iff _).2 (F.isIso_supportedSubmoduleFunctor_map_ι hZS)
    have hfac : (supportedModuleHPresheafFunctor Z 0).map (F.supportedSubmoduleι S) =
        ((F.supportedSubmoduleSheaf S).supportedModuleHPresheafZeroIso Z).hom ≫
          ((supportedSubmoduleFunctor Z).map (F.supportedSubmoduleι S)).hom ≫
          (F.supportedModuleHPresheafZeroIso Z).inv :=
      ((Category.comp_id _).symm.trans
        (congrArg _ (F.supportedModuleHPresheafZeroIso Z).hom_inv_id.symm)).trans <|
        (Category.assoc _ _ _).symm.trans <|
          (congrArg (· ≫ (F.supportedModuleHPresheafZeroIso Z).inv)
            (supportedModuleHPresheafZeroIso_hom_naturality Z (F.supportedSubmoduleι S))).trans
            (Category.assoc _ _ _)
    exact hfac ▸ IsIso.comp_isIso' (Iso.isIso_hom _) (IsIso.comp_isIso' hg₁ (Iso.isIso_inv _))
  | succ j ih =>
    -- embed `F` into an injective sheaf `F₂ = I(F)` with quotient `F₃`; as `𝓗_S¹(F) = 0`,
    -- applying `Γ_S` gives a short exact sequence `Γ_S(T)`
    let T := TauCeti.injectiveCokernelSequence F
    have hT : T.ShortExact := TauCeti.injectiveCokernelSequence_shortExact F
    have : TopCat.Presheaf.IsFlasque T.X₂.obj := isFlasque_of_injective_moduleCat _
    let T' := T.map (supportedSubmoduleFunctor S)
    have hT' : T'.ShortExact := shortExact_map_supportedSubmoduleFunctor S hT (h 0)
    have : TopCat.Presheaf.IsFlasque T'.X₂.obj := isFlasque_supportedSubmoduleSheaf T.X₂ S
    -- the inclusions `Γ_S(Fᵢ) ⟶ Fᵢ` form a morphism of short exact sequences `Γ_S(T) ⟶ T`
    let φ : T' ⟶ T :=
      { τ₁ := T.X₁.supportedSubmoduleι S
        τ₂ := T.X₂.supportedSubmoduleι S
        τ₃ := T.X₃.supportedSubmoduleι S
        comm₁₂ := (supportedSubmoduleFunctor_map_ι S T.f).symm
        comm₂₃ := (supportedSubmoduleFunctor_map_ι S T.g).symm }
    have ih₂ := ih T.X₂ fun q ↦ isZero_supportedModuleHSheaf_succ_of_isFlasque S T.X₂ q
    have ih₃ := ih T.X₃ fun q ↦ isZero_supportedModuleHSheaf_X₃_of_shortExact S hT (h (q + 1))
    -- compare the exact segments `H_Z^j(-, X₂) ⟶ H_Z^j(-, X₃) ⟶ H_Z^{j+1}(-, X₁)`
    let R₁ := ShortComplex.mk ((supportedModuleHPresheafFunctor Z j).map T'.g)
      (supportedModuleHPresheafδ Z hT' j) (supportedModuleHPresheafFunctor_map_g_δ Z hT' j)
    let R₂ := ShortComplex.mk ((supportedModuleHPresheafFunctor Z j).map T.g)
      (supportedModuleHPresheafδ Z hT j) (supportedModuleHPresheafFunctor_map_g_δ Z hT j)
    let ψ : R₁ ⟶ R₂ :=
      { τ₁ := (supportedModuleHPresheafFunctor Z j).map φ.τ₂
        τ₂ := (supportedModuleHPresheafFunctor Z j).map φ.τ₃
        τ₃ := (supportedModuleHPresheafFunctor Z (j + 1)).map φ.τ₁
        comm₁₂ := (Functor.map_comp _ _ _).symm.trans <|
          (congrArg ((supportedModuleHPresheafFunctor Z j).map) φ.comm₂₃).trans
            (Functor.map_comp _ _ _)
        comm₂₃ := supportedModuleHPresheafδ_naturality Z hT' hT φ j }
    have : Epi R₁.g := epi_supportedModuleHPresheafδ Z hT' j
    have : Epi R₂.g := epi_supportedModuleHPresheafδ Z hT j
    have : Epi ψ.τ₁ := by dsimp [ψ, φ]; infer_instance
    have : Mono ψ.τ₂ := by dsimp [ψ, φ]; infer_instance
    have : Epi ψ.τ₂ := by dsimp [ψ, φ]; infer_instance
    have : Mono ψ.τ₃ := ShortComplex.mono_of_epi_of_epi_of_mono ψ
      (exact_supportedModuleHPresheafFunctor_map_g_δ Z hT j) inferInstance inferInstance
      inferInstance
    have : Epi (R₁.g ≫ ψ.τ₃) := ψ.comm₂₃ ▸ epi_comp ψ.τ₂ R₂.g
    have : Epi ψ.τ₃ := epi_of_epi R₁.g ψ.τ₃
    exact isIso_of_mono_of_epi ψ.τ₃

/-- If the local cohomology sheaves `𝓗_S^q(F)` vanish for all `q > 0`, then for every closed
`Z ≤ S` the inclusion `Γ_S(F) ⟶ F` induces bijections `H_Z^j(W, Γ_S(F)) ⟶ H_Z^j(W, F)` in every
degree `j`. -/
theorem bijective_postcomp_mk₀_supportedSubmoduleι
    (h : ∀ q, IsZero (F.supportedModuleHSheaf S (q + 1))) (hZS : Z ≤ S) (W : Opens X) (j : ℕ) :
    Function.Bijective ((Ext.mk₀ (F.supportedSubmoduleι S)).postcomp _ (add_zero j) :
      (F.supportedSubmoduleSheaf S).supportedModuleH Z W j → F.supportedModuleH Z W j) := by
  have : IsIso (supportedModuleHPresheafPostcomp Z (Ext.mk₀ (F.supportedSubmoduleι S))
      (add_zero j)) := by
    rw [supportedModuleHPresheafPostcomp_mk₀]
    exact F.isIso_supportedModuleHPresheafFunctor_map_supportedSubmoduleι h hZS j
  have hbij := (ConcreteCategory.isIso_iff_bijective
    ((supportedModuleHPresheafPostcomp Z (Ext.mk₀ (F.supportedSubmoduleι S)) (add_zero j)).app
      (op W))).1 inferInstance
  rwa [funext (supportedModuleHPresheafPostcomp_app_apply Z _ _ (op W))] at hbij

/-- If the local cohomology sheaves `𝓗_S^q(F)` vanish for all `q > 0`, then for every closed
`Z ≤ S` the inclusion `Γ_S(F) ⟶ F` induces an isomorphism `𝓗_Z^j(Γ_S(F)) ≅ 𝓗_Z^j(F)` in every
degree `j`. -/
theorem isIso_supportedModuleHSheafFunctor_map_supportedSubmoduleι
    (h : ∀ q, IsZero (F.supportedModuleHSheaf S (q + 1))) (hZS : Z ≤ S) (j : ℕ) :
    IsIso ((supportedModuleHSheafFunctor Z j).map (F.supportedSubmoduleι S)) := by
  have := F.isIso_supportedModuleHPresheafFunctor_map_supportedSubmoduleι h hZS j
  exact (presheafToSheaf _ _).map_isIso
    ((supportedModuleHPresheafFunctor Z j).map (F.supportedSubmoduleι S))

/-- The base case `n = 1` of the degenerate edge comparison in positive degrees, for `Γ_S(F)`
flasque and `𝓗_S^q(F) = 0` for `q ≥ 2`: `H_Z^k(-, F) ≅ H_Z^{j+1}(-, 𝓗_S¹(F))` for `k = j + 2`. -/
private def supportedModuleHPresheafEdgeIsoOne
    [TopCat.Presheaf.IsFlasque (F.supportedSubmoduleSheaf S).obj]
    (h : ∀ q, IsZero (F.supportedModuleHSheaf S (q + 2))) (hZS : Z ≤ S) {j k : ℕ}
    (hk : j + 1 + 1 = k) :
    F.supportedModuleHPresheaf Z k ≅
      (F.supportedModuleHSheaf S 1).supportedModuleHPresheaf Z (j + 1) :=
  -- embed `F` into an injective sheaf `F₂` with quotient `F₃`
  let T := TauCeti.injectiveCokernelSequence F
  have hT : T.ShortExact := TauCeti.injectiveCokernelSequence_shortExact F
  have : TopCat.Presheaf.IsFlasque T.X₂.obj := isFlasque_of_injective_moduleCat _
  -- `H_Z^{j+1}(-, F₃) ≅ H_Z^{j+2}(-, F)` by the connecting morphism
  have := isIso_supportedModuleHPresheafPostcomp_extClass Z hT hk
  -- `H_Z^{j+1}(-, Γ_S(F₃)) ≅ H_Z^{j+1}(-, F₃)`, since `𝓗_S^q(F₃) = 0` for `q > 0`
  have : IsIso (supportedModuleHPresheafPostcomp Z (Ext.mk₀ (T.X₃.supportedSubmoduleι S))
      (add_zero (j + 1))) := by
    rw [supportedModuleHPresheafPostcomp_mk₀]
    exact T.X₃.isIso_supportedModuleHPresheafFunctor_map_supportedSubmoduleι
      (fun q ↦ isZero_supportedModuleHSheaf_X₃_of_shortExact S hT (h q)) hZS (j + 1)
  -- `Γ_S(F₃) ⟶ coker(Γ_S(F₂) ⟶ Γ_S(F₃))` has flasque kernel, the image of `Γ_S(F₂)`
  let E := T.map (supportedSubmoduleFunctor S)
  have := hT.mono_f
  have hE : E.Exact := exact_map_supportedSubmoduleFunctor S hT.exact
  have : Mono E.f := mono_supportedSubmoduleFunctor_map S T.f
  have : TopCat.Presheaf.IsFlasque E.X₁.obj := ‹_›
  have : TopCat.Presheaf.IsFlasque E.X₂.obj := isFlasque_supportedSubmoduleSheaf T.X₂ S
  have : TopCat.Presheaf.IsFlasque (Limits.image E.g).obj :=
    hE.shortExact_factorThruImage.isFlasque_X₃_of_isFlasque
  have := isIso_supportedModuleHPresheafPostcomp_mk₀_g Z
    (ShortComplex.shortExact_image_ι_cokernel_π E.g) j
  (asIso (supportedModuleHPresheafPostcomp Z hT.extClass hk)).symm ≪≫
    (asIso (supportedModuleHPresheafPostcomp Z (Ext.mk₀ (T.X₃.supportedSubmoduleι S))
      (add_zero (j + 1)))).symm ≪≫
    asIso (supportedModuleHPresheafPostcomp Z (Ext.mk₀ (cokernel.π E.g)) (add_zero (j + 1))) ≪≫
    asIso (supportedModuleHPresheafPostcomp Z
      (Ext.mk₀ (supportedModuleHSheafOneIsoCokernel S hT).symm.hom) (add_zero (j + 1)))

/-- The dimension-shifting form of the degenerate edge comparison in positive degrees: if `Γ_S(F)`
is flasque and `𝓗_S^{q+1}(F) = 0` for `q ≠ m`, then `H_Z^k(-, F) ≅ H_Z^{j+1}(-, 𝓗_S^{m+1}(F))`
for `k = m + 1 + (j + 1)`. -/
private def supportedModuleHPresheafEdgeIsoSucc (hZS : Z ≤ S) :
    ∀ (F : Sheaf (Opens.grothendieckTopology X) (ModuleCat.{u} R)) (m : ℕ)
      [TopCat.Presheaf.IsFlasque (F.supportedSubmoduleSheaf S).obj]
      (_ : ∀ q ≠ m, IsZero (F.supportedModuleHSheaf S (q + 1))) {j k : ℕ}
      (_ : m + 1 + (j + 1) = k),
      F.supportedModuleHPresheaf Z k ≅
        (F.supportedModuleHSheaf S (m + 1)).supportedModuleHPresheaf Z (j + 1)
  | F, 0, _, h, _, _, hk =>
    supportedModuleHPresheafEdgeIsoOne F (fun q ↦ h (q + 1) (by omega)) hZS (by omega)
  | F, m + 1, _, h, j, k, hk =>
    -- embed `F` into an injective sheaf `F₂` with quotient `F₃`
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
    -- `H_Z^{k-1}(-, F₃) ≅ H_Z^k(-, F)` and `𝓗_S^{m+1}(F₃) ≅ 𝓗_S^{m+2}(F)` by the connecting
    -- morphisms
    have := isIso_supportedModuleHPresheafPostcomp_extClass Z hT
      (show m + 1 + j + 1 + 1 = k by omega)
    (asIso (supportedModuleHPresheafPostcomp Z hT.extClass
        (show m + 1 + j + 1 + 1 = k by omega))).symm ≪≫
      supportedModuleHPresheafEdgeIsoSucc hZS T.X₃ m
        (fun q hq ↦ isZero_supportedModuleHSheaf_X₃_of_shortExact S hT (h (q + 1) (by omega)))
        (k := m + 1 + j + 1) (by omega) ≪≫
      asIso (supportedModuleHPresheafPostcomp Z
        (Ext.mk₀ (supportedModuleHSheafδ S hT (m + 1))) (add_zero (j + 1)))

/-- The degenerate edge comparison for `n = 0` in positive degrees: if `𝓗_S^q(F) = 0` for `q > 0`,
then `H_Z^k(-, F) ≅ H_Z^{j+1}(-, 𝓗_S⁰(F))` for `k = j + 1`, through `H_Z^{j+1}(-, Γ_S(F))` and
`𝓗_S⁰(F) ≅ Γ_S(F)`. -/
private def supportedModuleHPresheafEdgeIsoOfIsZeroSucc
    (h : ∀ q, IsZero (F.supportedModuleHSheaf S (q + 1))) (hZS : Z ≤ S) {j k : ℕ}
    (hk : j + 1 = k) :
    F.supportedModuleHPresheaf Z k ≅
      (F.supportedModuleHSheaf S 0).supportedModuleHPresheaf Z (j + 1) :=
  have : IsIso (supportedModuleHPresheafPostcomp Z (Ext.mk₀ (F.supportedSubmoduleι S))
      (show j + 1 + 0 = k by omega)) := by
    subst hk
    rw [supportedModuleHPresheafPostcomp_mk₀]
    exact F.isIso_supportedModuleHPresheafFunctor_map_supportedSubmoduleι h hZS (j + 1)
  (asIso (supportedModuleHPresheafPostcomp Z (Ext.mk₀ (F.supportedSubmoduleι S))
      (show j + 1 + 0 = k by omega))).symm ≪≫
    asIso (supportedModuleHPresheafPostcomp Z (Ext.mk₀ (F.supportedModuleHSheafZeroIso S).symm.hom)
      (add_zero (j + 1)))

variable {n : ℕ}

/-- The degenerate edge comparison in degree zero, `H_Zⁿ(-, F) ≅ H_Z⁰(-, 𝓗_Sⁿ(F))`, as an
isomorphism of presheaves: `CategoryTheory.Sheaf.supportedModuleHEdgePresheafIso` followed by the
inverse of `CategoryTheory.Sheaf.supportedModuleHPresheafZeroIso`. -/
private def supportedModuleHPresheafEdgeIsoZero
    (h : ∀ q < n, IsZero (F.supportedModuleHSheaf S q)) (hZS : Z ≤ S) :
    F.supportedModuleHPresheaf Z n ≅ (F.supportedModuleHSheaf S n).supportedModuleHPresheaf Z 0 :=
  F.supportedModuleHEdgePresheafIso h hZS ≪≫
    ((F.supportedModuleHSheaf S n).supportedModuleHPresheafZeroIso Z).symm

/-- **Degenerate edge comparison.** If the local cohomology sheaves `𝓗_S^q(F)` vanish for all
`q ≠ n`, then for every closed `Z ≤ S` and every `j` the presheaf `W ↦ H_Z^{n+j}(W, F)` of
cohomology with supports in `Z` is isomorphic as a presheaf of `R`-modules to
`W ↦ H_Z^j(W, 𝓗_Sⁿ(F))`. The degree is written `k` with `n + j = k`.

In degree `j = 0` this is `CategoryTheory.Sheaf.supportedModuleHEdgeEquiv`
(`CategoryTheory.Sheaf.supportedModuleHZeroEquiv_supportedModuleHPresheafEdgeIso_hom_app`). -/
def supportedModuleHPresheafEdgeIso (h : ∀ q ≠ n, IsZero (F.supportedModuleHSheaf S q))
    (hZS : Z ≤ S) {j k : ℕ} (hk : n + j = k) :
    F.supportedModuleHPresheaf Z k ≅ (F.supportedModuleHSheaf S n).supportedModuleHPresheaf Z j :=
  match n, j, h, hk with
  | n, 0, h, hk => eqToIso (congrArg (F.supportedModuleHPresheaf Z) hk.symm) ≪≫
      supportedModuleHPresheafEdgeIsoZero (n := n) F (fun q hq ↦ h q hq.ne) hZS
  | 0, j + 1, h, hk =>
    supportedModuleHPresheafEdgeIsoOfIsZeroSucc F (fun q ↦ h (q + 1) (by omega)) hZS (by omega)
  | m + 1, j + 1, h, hk =>
    have := F.isFlasque_supportedSubmoduleSheaf_obj_of_isZero S (h 0 (by omega))
    supportedModuleHPresheafEdgeIsoSucc hZS F m (fun q hq ↦ h (q + 1) (by omega)) hk

/-- In degree zero, the degenerate edge comparison `H_Zⁿ(W, F) ≅ H_Z⁰(W, 𝓗_Sⁿ(F))` is
`CategoryTheory.Sheaf.supportedModuleHEdgeEquiv`, through
`H_Z⁰(W, 𝓗_Sⁿ(F)) ≃ₗ[R] Γ_Z(W, 𝓗_Sⁿ(F))`. -/
@[simp]
lemma supportedModuleHZeroEquiv_supportedModuleHPresheafEdgeIso_hom_app
    (h : ∀ q ≠ n, IsZero (F.supportedModuleHSheaf S q)) (hZS : Z ≤ S) (W : Opens X)
    (x : F.supportedModuleH Z W n) :
    (F.supportedModuleHSheaf S n).supportedModuleHZeroEquiv Z W
        ((F.supportedModuleHPresheafEdgeIso h hZS (add_zero n)).hom.app (op W) x) =
      F.supportedModuleHEdgeEquiv (fun q hq ↦ h q hq.ne) hZS W x := by
  simp only [supportedModuleHPresheafEdgeIso, supportedModuleHPresheafEdgeIsoZero, eqToIso_refl,
    Iso.refl_trans, Iso.trans_hom, Iso.symm_hom]
  refine (congrArg ((F.supportedModuleHSheaf S n).supportedModuleHZeroEquiv Z W) ?_).trans
    (LinearEquiv.apply_symm_apply _ _)
  exact (supportedModuleHPresheafZeroIso_inv_app_apply Z (F.supportedModuleHSheaf S n) (op W)
    _).trans (congrArg _ (F.supportedModuleHEdgePresheafIso_hom_app_apply
      (fun q hq ↦ h q hq.ne) hZS (op W) x))

/-- **Degenerate edge comparison on sections.** If the local cohomology sheaves `𝓗_S^q(F)` vanish
for all `q ≠ n`, then for every closed `Z ≤ S`, open `W`, and degree `j` (with `n + j = k`),
`H_Z^k(W, F)` is `R`-linearly equivalent to `H_Z^j(W, 𝓗_Sⁿ(F))`. -/
def supportedModuleHHigherEdgeEquiv (h : ∀ q ≠ n, IsZero (F.supportedModuleHSheaf S q))
    (hZS : Z ≤ S) (W : Opens X) {j k : ℕ} (hk : n + j = k) :
    F.supportedModuleH Z W k ≃ₗ[R] (F.supportedModuleHSheaf S n).supportedModuleH Z W j :=
  ((F.supportedModuleHPresheafEdgeIso h hZS hk).app (op W)).toLinearEquiv

/-- Evaluating `CategoryTheory.Sheaf.supportedModuleHHigherEdgeEquiv` applies the forward direction
of `CategoryTheory.Sheaf.supportedModuleHPresheafEdgeIso` on `W`. -/
@[simp]
lemma supportedModuleHHigherEdgeEquiv_apply (h : ∀ q ≠ n, IsZero (F.supportedModuleHSheaf S q))
    (hZS : Z ≤ S) (W : Opens X) {j k : ℕ} (hk : n + j = k) (x : F.supportedModuleH Z W k) :
    F.supportedModuleHHigherEdgeEquiv h hZS W hk x =
      (F.supportedModuleHPresheafEdgeIso h hZS hk).hom.app (op W) x :=
  (rfl)

/-- Evaluating the inverse of `CategoryTheory.Sheaf.supportedModuleHHigherEdgeEquiv` applies the
inverse of `CategoryTheory.Sheaf.supportedModuleHPresheafEdgeIso` on `W`. -/
@[simp]
lemma supportedModuleHHigherEdgeEquiv_symm_apply
    (h : ∀ q ≠ n, IsZero (F.supportedModuleHSheaf S q)) (hZS : Z ≤ S) (W : Opens X) {j k : ℕ}
    (hk : n + j = k) (y : (F.supportedModuleHSheaf S n).supportedModuleH Z W j) :
    (F.supportedModuleHHigherEdgeEquiv h hZS W hk).symm y =
      (F.supportedModuleHPresheafEdgeIso h hZS hk).inv.app (op W) y :=
  (rfl)

/-- The degenerate edge comparison `H_Z^{n+j}(W, F) ≃ₗ[R] H_Z^j(W, 𝓗_Sⁿ(F))` is compatible with
restriction to a smaller open `W' ≤ W`. -/
lemma supportedModuleHHigherEdgeEquiv_map (h : ∀ q ≠ n, IsZero (F.supportedModuleHSheaf S q))
    (hZS : Z ≤ S) {W' W : Opens X} (hW : W' ≤ W) {j k : ℕ} (hk : n + j = k)
    (x : F.supportedModuleH Z W k) :
    F.supportedModuleHHigherEdgeEquiv h hZS W' hk
        ((F.supportedModuleHPresheaf Z k).map (homOfLE hW).op x) =
      ((F.supportedModuleHSheaf S n).supportedModuleHPresheaf Z j).map (homOfLE hW).op
        (F.supportedModuleHHigherEdgeEquiv h hZS W hk x) :=
  congr($((F.supportedModuleHPresheafEdgeIso h hZS hk).hom.naturality (homOfLE hW).op) x)

/-- In degree `j = 0`, `CategoryTheory.Sheaf.supportedModuleHHigherEdgeEquiv` agrees with
`CategoryTheory.Sheaf.supportedModuleHEdgeEquiv` through `supportedModuleHZeroEquiv`. -/
lemma supportedModuleHZeroEquiv_supportedModuleHHigherEdgeEquiv
    (h : ∀ q ≠ n, IsZero (F.supportedModuleHSheaf S q)) (hZS : Z ≤ S) (W : Opens X)
    (x : F.supportedModuleH Z W n) :
    (F.supportedModuleHSheaf S n).supportedModuleHZeroEquiv Z W
        (F.supportedModuleHHigherEdgeEquiv h hZS W (add_zero n) x) =
      F.supportedModuleHEdgeEquiv (fun q hq ↦ h q hq.ne) hZS W x := by
  simp

/-- **Degenerate edge comparison for local cohomology sheaves.** If the local cohomology sheaves
`𝓗_S^q(F)` vanish for all `q ≠ n`, then for every closed `Z ≤ S` and every `j` (with `n + j = k`),
`𝓗_Z^k(F) ≅ 𝓗_Z^j(𝓗_Sⁿ(F))` as sheaves of `R`-modules. -/
def supportedModuleHSheafEdgeIso (h : ∀ q ≠ n, IsZero (F.supportedModuleHSheaf S q)) (hZS : Z ≤ S)
    {j k : ℕ} (hk : n + j = k) :
    F.supportedModuleHSheaf Z k ≅ (F.supportedModuleHSheaf S n).supportedModuleHSheaf Z j :=
  (presheafToSheaf _ _).mapIso (F.supportedModuleHPresheafEdgeIso h hZS hk)

/-- The sheaf-level degenerate edge comparison is induced by the presheaf comparison through
sheafification. -/
@[reassoc (attr := simp)]
lemma toSheafify_supportedModuleHSheafEdgeIso_hom
    (h : ∀ q ≠ n, IsZero (F.supportedModuleHSheaf S q)) (hZS : Z ≤ S) {j k : ℕ}
    (hk : n + j = k) :
    toSheafify (Opens.grothendieckTopology X) (F.supportedModuleHPresheaf Z k) ≫
        (F.supportedModuleHSheafEdgeIso h hZS hk).hom.hom =
      (F.supportedModuleHPresheafEdgeIso h hZS hk).hom ≫
        toSheafify (Opens.grothendieckTopology X)
          ((F.supportedModuleHSheaf S n).supportedModuleHPresheaf Z j) :=
  (toSheafify_naturality _ _).symm

/-- The inverse of the sheaf-level degenerate edge comparison is induced by the inverse presheaf
comparison through sheafification. -/
@[reassoc (attr := simp)]
lemma toSheafify_supportedModuleHSheafEdgeIso_inv
    (h : ∀ q ≠ n, IsZero (F.supportedModuleHSheaf S q)) (hZS : Z ≤ S) {j k : ℕ}
    (hk : n + j = k) :
    toSheafify (Opens.grothendieckTopology X)
        ((F.supportedModuleHSheaf S n).supportedModuleHPresheaf Z j) ≫
        (F.supportedModuleHSheafEdgeIso h hZS hk).inv.hom =
      (F.supportedModuleHPresheafEdgeIso h hZS hk).inv ≫
        toSheafify (Opens.grothendieckTopology X) (F.supportedModuleHPresheaf Z k) :=
  (toSheafify_naturality _ _).symm

/-- If the local cohomology sheaves `𝓗_S^q(F)` vanish for all `q ≠ n` and `𝓗_Sⁿ(F)` is flasque,
then `H_Z^k(W, F) = 0` for all `k ≠ n`, every closed `Z ≤ S`, and every open `W`. -/
theorem subsingleton_supportedModuleH_of_ne_of_isFlasque
    (h : ∀ q ≠ n, IsZero (F.supportedModuleHSheaf S q))
    [TopCat.Presheaf.IsFlasque (F.supportedModuleHSheaf S n).obj] (hZS : Z ≤ S) {k : ℕ}
    (hk : k ≠ n) (W : Opens X) : Subsingleton (F.supportedModuleH Z W k) := by
  rcases lt_or_gt_of_ne hk with hkn | hkn
  · exact F.subsingleton_supportedModuleH_of_isZero_supportedModuleHSheaf_of_le
      (fun q hq ↦ h q hq.ne) hZS hkn W
  · exact (F.supportedModuleHHigherEdgeEquiv h hZS W
      (show n + (k - n - 1 + 1) = k by omega)).injective.subsingleton

/-- If the local cohomology sheaves `𝓗_S^q(F)` vanish for all `q ≠ n` and `𝓗_Sⁿ(F)` is flasque,
then `𝓗_Z^k(F) = 0` for all `k ≠ n` and every closed `Z ≤ S`. -/
theorem isZero_supportedModuleHSheaf_of_ne_of_isFlasque
    (h : ∀ q ≠ n, IsZero (F.supportedModuleHSheaf S q))
    [TopCat.Presheaf.IsFlasque (F.supportedModuleHSheaf S n).obj] (hZS : Z ≤ S) {k : ℕ}
    (hk : k ≠ n) : IsZero (F.supportedModuleHSheaf Z k) := by
  apply Functor.map_isZero
  refine (Functor.isZero_iff _).2 fun W ↦ ?_
  rw [F.supportedModuleHPresheaf_obj]
  have := F.subsingleton_supportedModuleH_of_ne_of_isFlasque h hZS hk W.unop
  exact ModuleCat.isZero_iff_subsingleton.2 inferInstance

end higherEdge

end

end CategoryTheory.Sheaf

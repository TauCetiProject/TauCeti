/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.MorphismProperty.IsInvertedBy
public import TauCeti.Topology.Category.TopCat.Pullback
public import TauCeti.Topology.Category.TopCat.WeakEquivalence
public import TauCeti.Topology.Homotopy.SerreFibration.Connected

import Mathlib.Topology.Subpath
import TauCeti.Topology.Homotopy.Contractible
import TauCeti.Topology.Homotopy.Path
import TauCeti.Topology.UnitInterval.Contractible

/-!
# Path transport on fibres of a Serre fibration

Let `p : E ⟶ B` be a Serre fibration (`TauCeti.TopCat.serreFibrations`), and let
`F : TopCat.{u} ⥤ C` be any functor that inverts weak homotopy equivalences
(`TauCeti.TopCat.weakEquivalences.IsInvertedBy F`), such as singular homology or cohomology with
arbitrary coefficients. Over a contractible base `B`, every fibre inclusion `p.fiberι b` is a weak
homotopy equivalence (`TauCeti.TopCat.isWeakHomotopyEquivalence_fiberι_of_contractibleSpace`), so
`F.map (p.fiberι b)` is an isomorphism (`TauCeti.TopCat.isIso_map_fiberι_of_contractibleSpace`).

Pulling `p` back along a path `γ : Path b₀ b₁` in an arbitrary base `B` to the contractible
interval `TopCat.of (ULift unitInterval)` therefore produces a canonical path transport isomorphism
`F.obj (p.fiber b₀) ≅ F.obj (p.fiber b₁)` (`TauCeti.TopCat.fiberIsoOfPath`). It commutes with the
fibre inclusions into `E` (`fiberIsoOfPath_hom_comp_map_fiberι`), reduces to the zig-zag of fibre
inclusions over a contractible base (`fiberIsoOfPath_eq_of_contractibleSpace`), is natural in maps
of Serre fibrations (`fiberIsoOfPath_naturality`), base change (`fiberIsoOfPath_pullbackFst`), and
natural transformations `F ⟶ G` (`fiberIsoOfPath_hom_comp_app`), and depends only on the endpoint-
fixing homotopy class of `γ` (`fiberIsoOfPath_refl`, `fiberIsoOfPath_symm`,
`fiberIsoOfPath_trans`, `fiberIsoOfPath_congr`).

## Main declarations

* `TauCeti.TopCat.isIso_map_fiberι_of_contractibleSpace`: over a contractible base, a functor
  inverting weak homotopy equivalences sends every fibre inclusion of a Serre fibration to an
  isomorphism.
* `TauCeti.TopCat.fiberIsoOfPath`: path transport isomorphism
  `F.obj (p.fiber b₀) ≅ F.obj (p.fiber b₁)` induced by a path `γ : Path b₀ b₁`.
* `TauCeti.TopCat.fiberIsoOfPath_eq_of_contractibleSpace`,
  `TauCeti.TopCat.fiberIsoOfPath_pullbackFst`, `TauCeti.TopCat.fiberIsoOfPath_naturality`, and
  `TauCeti.TopCat.fiberIsoOfPath_hom_comp_app`: characterization over contractible bases, base
  change compatibility, and naturality.
* `TauCeti.TopCat.fiberIsoOfPath_refl`, `TauCeti.TopCat.fiberIsoOfPath_symm`,
  `TauCeti.TopCat.fiberIsoOfPath_trans`, and `TauCeti.TopCat.fiberIsoOfPath_congr`: groupoid
  functoriality and homotopy invariance in the path `γ`.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 4.2, Theorem 4.41.
* G. W. Whitehead, *Elements of Homotopy Theory*, GTM 61, Springer, 1978, Chapter IV.8.
-/

public section

open CategoryTheory CategoryTheory.Limits
open scoped Topology

universe u v w

namespace TauCeti.TopCat

variable {C : Type v} [Category.{w} C] {F : _root_.TopCat.{u} ⥤ C}
  {E B : _root_.TopCat.{u}} {p : E ⟶ B}

/-- Over a contractible base, any functor inverting weak homotopy equivalences sends every fibre
inclusion of a Serre fibration to an isomorphism. -/
theorem isIso_map_fiberι_of_contractibleSpace (hF : weakEquivalences.{u}.IsInvertedBy F)
    (hp : serreFibrations p) [ContractibleSpace B] (b : B) :
    IsIso (F.map (p.fiberι b)) :=
  hF _ ((mem_weakEquivalences_iff _).2 (isWeakHomotopyEquivalence_fiberι_of_contractibleSpace hp b))

/-- A path `γ : Path b₀ b₁` in `B` viewed as a `TopCat.{u}` morphism from `ULift unitInterval`. -/
private def pathToTopCatHom {b₀ b₁ : B} (γ : Path b₀ b₁) :
    _root_.TopCat.of (ULift.{u} unitInterval) ⟶ B :=
  _root_.TopCat.ofHom ⟨fun t ↦ γ t.down, γ.continuous.comp continuous_uliftDown⟩

@[simp]
private lemma pathToTopCatHom_apply {b₀ b₁ : B} (γ : Path b₀ b₁)
    (t : _root_.TopCat.of (ULift.{u} unitInterval)) :
    pathToTopCatHom γ t = γ t.down :=
  rfl

private lemma pathToTopCatHom_zero {b₀ b₁ : B} (γ : Path b₀ b₁) :
    pathToTopCatHom γ (ULift.up (0 : unitInterval)) = b₀ :=
  γ.source

private lemma pathToTopCatHom_one {b₀ b₁ : B} (γ : Path b₀ b₁) :
    pathToTopCatHom γ (ULift.up (1 : unitInterval)) = b₁ :=
  γ.target

/-- The canonical path from `ULift.up 0` to `ULift.up 1` in `ULift unitInterval`. -/
private def uliftUnitIntervalPath :
    Path (ULift.up (0 : unitInterval)) (ULift.up (1 : unitInterval)) :=
  Path.id.map continuous_uliftUp

/-- **Path transport on fibres of a Serre fibration.** Given a functor `F : TopCat.{u} ⥤ C` that
inverts weak homotopy equivalences and a Serre fibration `p : E ⟶ B`, a path `γ : Path b₀ b₁`
induces a canonical isomorphism `F.obj (p.fiber b₀) ≅ F.obj (p.fiber b₁)` by pulling `p` back to
the contractible interval `ULift unitInterval` and inverting the induced maps of the endpoint fibre
inclusions. -/
noncomputable def fiberIsoOfPath (hF : weakEquivalences.{u}.IsInvertedBy F)
    (hp : serreFibrations p) {b₀ b₁ : B} (γ : Path b₀ b₁) :
    F.obj (p.fiber b₀) ≅ F.obj (p.fiber b₁) :=
  let g := pathToTopCatHom γ
  let p' := _root_.TopCat.pullbackFst g p
  have hp' : serreFibrations p' := mem_serreFibrations_pullbackFst hp g
  have := isIso_map_fiberι_of_contractibleSpace hF hp' (ULift.up (0 : unitInterval))
  have := isIso_map_fiberι_of_contractibleSpace hF hp' (ULift.up (1 : unitInterval))
  F.mapIso (eqToIso (congrArg p.fiber (pathToTopCatHom_zero γ).symm) ≪≫
      (p.fiberPullbackFstIso g (ULift.up (0 : unitInterval))).symm) ≪≫
    asIso (F.map (p'.fiberι (ULift.up (0 : unitInterval)))) ≪≫
    (asIso (F.map (p'.fiberι (ULift.up (1 : unitInterval))))).symm ≪≫
    F.mapIso (p.fiberPullbackFstIso g (ULift.up (1 : unitInterval)) ≪≫
      eqToIso (congrArg p.fiber (pathToTopCatHom_one γ)))

variable (hF : weakEquivalences.{u}.IsInvertedBy F) (hp : serreFibrations p)

/-- Explicit unfolding of `(fiberIsoOfPath hF hp γ).hom` into its four composable factors. -/
private lemma fiberIsoOfPath_hom {b₀ b₁ : B} (γ : Path b₀ b₁) :
    have := isIso_map_fiberι_of_contractibleSpace hF
      (mem_serreFibrations_pullbackFst hp (pathToTopCatHom γ)) (ULift.up (1 : unitInterval))
    (fiberIsoOfPath hF hp γ).hom =
      F.map (eqToHom (congrArg p.fiber (pathToTopCatHom_zero γ).symm) ≫
          (p.fiberPullbackFstIso (pathToTopCatHom γ) (ULift.up (0 : unitInterval))).inv) ≫
        F.map ((_root_.TopCat.pullbackFst (pathToTopCatHom γ) p).fiberι
          (ULift.up (0 : unitInterval))) ≫
        inv (F.map ((_root_.TopCat.pullbackFst (pathToTopCatHom γ) p).fiberι
          (ULift.up (1 : unitInterval)))) ≫
        F.map ((p.fiberPullbackFstIso (pathToTopCatHom γ) (ULift.up (1 : unitInterval))).hom ≫
          eqToHom (congrArg p.fiber (pathToTopCatHom_one γ))) := by
  simp [fiberIsoOfPath]

/-- Path transport along `γ : Path b₀ b₁` commutes with the maps induced by the fibre inclusions
`p.fiber b₀ ⟶ E` and `p.fiber b₁ ⟶ E`. -/
@[reassoc (attr := simp)]
theorem fiberIsoOfPath_hom_comp_map_fiberι {b₀ b₁ : B} (γ : Path b₀ b₁) :
    (fiberIsoOfPath hF hp γ).hom ≫ F.map (p.fiberι b₁) = F.map (p.fiberι b₀) := by
  let g := pathToTopCatHom γ
  let p' := _root_.TopCat.pullbackFst g p
  have hp' : serreFibrations p' := mem_serreFibrations_pullbackFst hp g
  let t₀ : _root_.TopCat.of (ULift.{u} unitInterval) := ULift.up (0 : unitInterval)
  let t₁ : _root_.TopCat.of (ULift.{u} unitInterval) := ULift.up (1 : unitInterval)
  have := isIso_map_fiberι_of_contractibleSpace hF hp' t₁
  have h1 : F.map ((p.fiberPullbackFstIso g t₁).hom ≫
      eqToHom (congrArg p.fiber (pathToTopCatHom_one γ))) ≫ F.map (p.fiberι b₁) =
        F.map (p'.fiberι t₁) ≫ F.map (_root_.TopCat.pullbackSnd g p) := by
    rw [← F.map_comp, ← F.map_comp]
    congr 1
    simp only [Category.assoc, p.eqToHom_fiber_comp_fiberι (pathToTopCatHom_one γ), g, p', t₁,
      p.fiberPullbackFstIso_hom_comp_fiberι]
  have h0 : F.map (eqToHom (congrArg p.fiber (pathToTopCatHom_zero γ).symm) ≫
      (p.fiberPullbackFstIso g t₀).inv) ≫ F.map (p'.fiberι t₀) ≫
        F.map (_root_.TopCat.pullbackSnd g p) = F.map (p.fiberι b₀) := by
    rw [← F.map_comp, ← F.map_comp]
    congr 1
    simp only [Category.assoc, g, p', t₀, ← p.fiberPullbackFstIso_hom_comp_fiberι,
      Iso.inv_hom_id_assoc, p.eqToHom_fiber_comp_fiberι (pathToTopCatHom_zero γ).symm]
  rw [fiberIsoOfPath_hom]
  dsimp only [g, p', t₀, t₁] at h1 h0
  simp only [Category.assoc, h1, IsIso.inv_hom_id_assoc, h0]

/-- The inverse of `fiberIsoOfPath` commutes with the maps induced by the fibre inclusions
`p.fiber b₁ ⟶ E` and `p.fiber b₀ ⟶ E`. -/
@[reassoc (attr := simp)]
theorem fiberIsoOfPath_inv_comp_map_fiberι {b₀ b₁ : B} (γ : Path b₀ b₁) :
    (fiberIsoOfPath hF hp γ).inv ≫ F.map (p.fiberι b₀) = F.map (p.fiberι b₁) :=
  (Iso.inv_comp_eq _).2 (fiberIsoOfPath_hom_comp_map_fiberι hF hp γ).symm

/-- Over a contractible base, path transport along any path `γ : Path b₀ b₁` equals
`F.map (p.fiberι b₀)` followed by `(F.map (p.fiberι b₁))⁻¹`, and in particular depends only on the
endpoints `b₀` and `b₁`. -/
theorem fiberIsoOfPath_eq_of_contractibleSpace [ContractibleSpace B] {b₀ b₁ : B} (γ : Path b₀ b₁) :
    have := isIso_map_fiberι_of_contractibleSpace hF hp b₀
    have := isIso_map_fiberι_of_contractibleSpace hF hp b₁
    fiberIsoOfPath hF hp γ =
      asIso (F.map (p.fiberι b₀)) ≪≫ (asIso (F.map (p.fiberι b₁))).symm := by
  have := isIso_map_fiberι_of_contractibleSpace hF hp b₀
  have := isIso_map_fiberι_of_contractibleSpace hF hp b₁
  apply Iso.ext
  refine (cancel_mono (F.map (p.fiberι b₁))).1 ?_
  rw [fiberIsoOfPath_hom_comp_map_fiberι]
  simp

omit hp in
/-- Naturality of the fibre-inclusion zig-zag `F.map (p₁.fiberι t₀) ≫ inv (F.map (p₁.fiberι t₁))`
along a commutative square between Serre fibrations over contractible bases. -/
private lemma fiberι_zigzag_naturality {E₁ B₁ E₂ B₂ : _root_.TopCat.{u}}
    {p₁ : E₁ ⟶ B₁} {p₂ : E₂ ⟶ B₂} (hp₁ : serreFibrations p₁) (hp₂ : serreFibrations p₂)
    [ContractibleSpace B₁] [ContractibleSpace B₂]
    {f : E₁ ⟶ E₂} {g : B₁ ⟶ B₂} (sq : CommSq f p₁ p₂ g) (t₀ t₁ : B₁) :
    have := isIso_map_fiberι_of_contractibleSpace hF hp₁ t₁
    have := isIso_map_fiberι_of_contractibleSpace hF hp₂ (g t₁)
    F.map (p₁.fiberι t₀) ≫ inv (F.map (p₁.fiberι t₁)) ≫ F.map (sq.fiberMap t₁) =
      F.map (sq.fiberMap t₀) ≫ F.map (p₂.fiberι (g t₀)) ≫ inv (F.map (p₂.fiberι (g t₁))) := by
  have := isIso_map_fiberι_of_contractibleSpace hF hp₁ t₁
  have := isIso_map_fiberι_of_contractibleSpace hF hp₂ (g t₁)
  have hfib (t : B₁) : F.map (sq.fiberMap t) ≫ F.map (p₂.fiberι (g t)) =
      F.map (p₁.fiberι t) ≫ F.map f := by
    rw [← F.map_comp, ← F.map_comp, sq.fiberMap_comp_fiberι]
  refine (cancel_mono (F.map (p₂.fiberι (g t₁)))).1 ?_
  simp [hfib t₀, hfib t₁]

/-- General naturality of `fiberIsoOfPath` along a morphism of Serre fibrations
`sq : CommSq f p p' g` and paths `γ` in `B`, `γ'` in `B'` satisfying `g (γ t) = γ' t`. -/
private lemma fiberIsoOfPath_naturality_of_forall {E' B' : _root_.TopCat.{u}} {p' : E' ⟶ B'}
    (hp' : serreFibrations p') {f : E ⟶ E'} {g : B ⟶ B'} (sq : CommSq f p p' g)
    {b₀ b₁ : B} (γ : Path b₀ b₁) {b₀' b₁' : B'} (γ' : Path b₀' b₁')
    (hb₀ : g b₀ = b₀') (hb₁ : g b₁ = b₁') (hγ : ∀ t, g (γ t) = γ' t) :
    (fiberIsoOfPath hF hp γ).hom ≫
        F.map (sq.fiberMap b₁ ≫ eqToHom (congrArg p'.fiber hb₁)) =
      F.map (sq.fiberMap b₀ ≫ eqToHom (congrArg p'.fiber hb₀)) ≫
        (fiberIsoOfPath hF hp' γ').hom := by
  -- Pull both fibrations back to the interval `I` and lift the square to a map `Φ` over `I`.
  let I := _root_.TopCat.of (ULift.{u} unitInterval)
  let ι := pathToTopCatHom γ
  let ι' := pathToTopCatHom γ'
  let p_γ := _root_.TopCat.pullbackFst ι p
  let p'_γ' := _root_.TopCat.pullbackFst ι' p'
  have hp_γ : serreFibrations p_γ := mem_serreFibrations_pullbackFst hp ι
  have hp'_γ' : serreFibrations p'_γ' := mem_serreFibrations_pullbackFst hp' ι'
  have hι : ι ≫ g = ι' := _root_.TopCat.ext fun t ↦ hγ t.down
  have hp_γ_cond : p_γ ≫ ι = _root_.TopCat.pullbackSnd ι p ≫ p :=
    (_root_.TopCat.pullbackCone ι p).condition
  have hcond : p_γ ≫ ι' = (_root_.TopCat.pullbackSnd ι p ≫ f) ≫ p' := by
    simp only [← hι, reassoc_of% hp_γ_cond, Category.assoc, sq.w]
  let Φ : _root_.TopCat.of { q : I × E // ι q.1 = p q.2 } ⟶
      _root_.TopCat.of { q : I × E' // ι' q.1 = p' q.2 } :=
    (_root_.TopCat.pullbackConeIsLimit ι' p').lift
      (PullbackCone.mk p_γ (_root_.TopCat.pullbackSnd ι p ≫ f) hcond)
  have hΦ_fst : Φ ≫ p'_γ' = p_γ :=
    PullbackCone.IsLimit.lift_fst (_root_.TopCat.pullbackConeIsLimit ι' p') _ _ hcond
  have hΦ_snd : Φ ≫ _root_.TopCat.pullbackSnd ι' p' = _root_.TopCat.pullbackSnd ι p ≫ f :=
    PullbackCone.IsLimit.lift_snd (_root_.TopCat.pullbackConeIsLimit ι' p') _ _ hcond
  have sqΦ : CommSq Φ p_γ p'_γ' (𝟙 I) := ⟨hΦ_fst.trans (Category.comp_id p_γ).symm⟩
  let Φ_fiber (t : I) : p_γ.fiber t ⟶ p'_γ'.fiber t := sqΦ.fiberMap t
  have hΦ_fiber (t : I) : Φ_fiber t ≫ p'_γ'.fiberι t = p_γ.fiberι t ≫ Φ :=
    sqΦ.fiberMap_comp_fiberι t
  -- Compare `Φ_fiber` with `sq.fiberMap` at either endpoint by post-composing with `p'.fiberι`.
  have hcohere {t : I} {b : B} {b' : B'} (ht : ι t = b) (ht' : ι' t = b') (hb : g b = b') :
      (p.fiberPullbackFstIso ι t).hom ≫ eqToHom (congrArg p.fiber ht) ≫
          sq.fiberMap b ≫ eqToHom (congrArg p'.fiber hb) =
        Φ_fiber t ≫ (p'.fiberPullbackFstIso ι' t).hom ≫ eqToHom (congrArg p'.fiber ht') := by
    refine (cancel_mono (p'.fiberι b')).1 ?_
    simp only [Category.assoc, p'.eqToHom_fiber_comp_fiberι hb, p'.eqToHom_fiber_comp_fiberι ht',
      sq.fiberMap_comp_fiberι, p.eqToHom_fiber_comp_fiberι_assoc ht,
      p.fiberPullbackFstIso_hom_comp_fiberι_assoc ι t,
      p'.fiberPullbackFstIso_hom_comp_fiberι ι' t, p_γ, p'_γ', reassoc_of% hΦ_fiber, hΦ_snd]
  let t₀ : I := ULift.up (0 : unitInterval)
  let t₁ : I := ULift.up (1 : unitInterval)
  have h0F :
      F.map (eqToHom (congrArg p.fiber (pathToTopCatHom_zero γ).symm) ≫
          (p.fiberPullbackFstIso ι t₀).inv) ≫ F.map (Φ_fiber t₀) =
        F.map (sq.fiberMap b₀ ≫ eqToHom (congrArg p'.fiber hb₀)) ≫
          F.map (eqToHom (congrArg p'.fiber (pathToTopCatHom_zero γ').symm) ≫
            (p'.fiberPullbackFstIso ι' t₀).inv) := by
    rw [← F.map_comp, ← F.map_comp]
    congr 1
    refine (cancel_mono ((p'.fiberPullbackFstIso ι' t₀).hom ≫
      eqToHom (congrArg p'.fiber (pathToTopCatHom_zero γ')))).1 ?_
    have hc := hcohere (pathToTopCatHom_zero γ) (pathToTopCatHom_zero γ') hb₀
    simp only [Category.assoc, t₀, ι, ι', ← hc, Iso.inv_hom_id_assoc, eqToHom_trans,
      eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
  have h1F :
      F.map ((p.fiberPullbackFstIso ι t₁).hom ≫
          eqToHom (congrArg p.fiber (pathToTopCatHom_one γ))) ≫
          F.map (sq.fiberMap b₁ ≫ eqToHom (congrArg p'.fiber hb₁)) =
        F.map (Φ_fiber t₁) ≫
          F.map ((p'.fiberPullbackFstIso ι' t₁).hom ≫
            eqToHom (congrArg p'.fiber (pathToTopCatHom_one γ'))) := by
    rw [← F.map_comp, ← F.map_comp]
    congr 1
    simpa only [Category.assoc] using
      hcohere (pathToTopCatHom_one γ) (pathToTopCatHom_one γ') hb₁
  have := isIso_map_fiberι_of_contractibleSpace hF hp_γ t₁
  have := isIso_map_fiberι_of_contractibleSpace hF hp'_γ' t₁
  have hmid :
      F.map (p_γ.fiberι t₀) ≫ inv (F.map (p_γ.fiberι t₁)) ≫ F.map (Φ_fiber t₁) =
        F.map (Φ_fiber t₀) ≫ F.map (p'_γ'.fiberι t₀) ≫ inv (F.map (p'_γ'.fiberι t₁)) :=
    fiberι_zigzag_naturality hF hp_γ hp'_γ' sqΦ t₀ t₁
  rw [fiberIsoOfPath_hom, fiberIsoOfPath_hom]
  dsimp only [ι, ι', p_γ, p'_γ', t₀, t₁] at h0F h1F hmid
  simp only [Category.assoc, h1F, reassoc_of% hmid, reassoc_of% h0F]

/-- Naturality of `fiberIsoOfPath` in maps of Serre fibrations: a commutative square
`sq : CommSq f p p' g` intertwines path transport along `γ` for `p` with path transport along
`γ.map g.hom.continuous` for `p'`. -/
@[reassoc]
theorem fiberIsoOfPath_naturality {E' B' : _root_.TopCat.{u}} {p' : E' ⟶ B'}
    (hp' : serreFibrations p') {f : E ⟶ E'} {g : B ⟶ B'} (sq : CommSq f p p' g)
    {b₀ b₁ : B} (γ : Path b₀ b₁) :
    (fiberIsoOfPath hF hp γ).hom ≫ F.map (sq.fiberMap b₁) =
      F.map (sq.fiberMap b₀) ≫ (fiberIsoOfPath hF hp' (γ.map g.hom.continuous)).hom := by
  simpa using fiberIsoOfPath_naturality_of_forall hF hp hp' sq γ (γ.map g.hom.continuous)
    rfl rfl fun _ ↦ rfl

/-- Base change compatibility of `fiberIsoOfPath` along a morphism `f : B' ⟶ B`: if a path `γ'` in
`B'` lifts `γ` in `B` along `f`, then path transport along `γ` for `p` is conjugate via
`p.fiberPullbackFstIso f` to path transport along `γ'` for `TopCat.pullbackFst f p`. -/
theorem fiberIsoOfPath_pullbackFst {B' : _root_.TopCat.{u}} (f : B' ⟶ B)
    {x₀ x₁ : B'} (γ' : Path x₀ x₁) {b₀ b₁ : B} (γ : Path b₀ b₁)
    (hb₀ : f x₀ = b₀) (hb₁ : f x₁ = b₁) (hγ : ∀ t, f (γ' t) = γ t) :
    fiberIsoOfPath hF hp γ =
      F.mapIso (eqToIso (congrArg p.fiber hb₀.symm) ≪≫ (p.fiberPullbackFstIso f x₀).symm) ≪≫
        fiberIsoOfPath hF (mem_serreFibrations_pullbackFst hp f) γ' ≪≫
        F.mapIso (p.fiberPullbackFstIso f x₁ ≪≫ eqToIso (congrArg p.fiber hb₁)) := by
  have sq : CommSq (_root_.TopCat.pullbackSnd f p) (_root_.TopCat.pullbackFst f p) p f :=
    ⟨(_root_.TopCat.pullbackCone f p).condition.symm⟩
  have hsq (x : B') : sq.fiberMap x = (p.fiberPullbackFstIso f x).hom := by
    refine (cancel_mono (p.fiberι (f x))).1 ?_
    simp
  have hnat := fiberIsoOfPath_naturality_of_forall hF (mem_serreFibrations_pullbackFst hp f) hp
    sq γ' γ hb₀ hb₁ hγ
  simp only [hsq] at hnat
  apply Iso.ext
  simp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, eqToIso.hom]
  rw [hnat, ← F.map_comp_assoc]
  simp

/-- Naturality of `fiberIsoOfPath` in natural transformations between functors inverting weak
homotopy equivalences. -/
@[reassoc]
theorem fiberIsoOfPath_hom_comp_app {G : _root_.TopCat.{u} ⥤ C}
    (hG : weakEquivalences.{u}.IsInvertedBy G) (α : F ⟶ G) {b₀ b₁ : B} (γ : Path b₀ b₁) :
    (fiberIsoOfPath hF hp γ).hom ≫ α.app (p.fiber b₁) =
      α.app (p.fiber b₀) ≫ (fiberIsoOfPath hG hp γ).hom := by
  let g := pathToTopCatHom γ
  let p' := _root_.TopCat.pullbackFst g p
  have hp' : serreFibrations p' := mem_serreFibrations_pullbackFst hp g
  let t₁ : _root_.TopCat.of (ULift.{u} unitInterval) := ULift.up (1 : unitInterval)
  have := isIso_map_fiberι_of_contractibleSpace hF hp' t₁
  have := isIso_map_fiberι_of_contractibleSpace hG hp' t₁
  have hinv :
      inv (F.map (p'.fiberι t₁)) ≫ α.app (p'.fiber t₁) =
        α.app _ ≫ inv (G.map (p'.fiberι t₁)) := by
    rw [IsIso.inv_comp_eq]
    simp [α.naturality_assoc]
  rw [fiberIsoOfPath_hom, fiberIsoOfPath_hom]
  dsimp only [g, p', t₁] at hinv
  simp only [Category.assoc, α.naturality, α.naturality_assoc, reassoc_of% hinv]

/-- If `γ` lifts along `f : B' ⟶ B` from a contractible space `B'` to a path `γ'` from `x₀` to
`x₁`, then path transport along `γ` factors through the endpoint fibre inclusions of the pullback
fibration over `B'`. -/
private lemma fiberIsoOfPath_of_contractibleSpace_lift {B' : _root_.TopCat.{u}}
    [ContractibleSpace B'] (f : B' ⟶ B) {x₀ x₁ : B'} (γ' : Path x₀ x₁) {b₀ b₁ : B}
    (γ : Path b₀ b₁) (hb₀ : f x₀ = b₀) (hb₁ : f x₁ = b₁) (hγ : ∀ t, f (γ' t) = γ t) :
    have := isIso_map_fiberι_of_contractibleSpace hF (mem_serreFibrations_pullbackFst hp f) x₀
    have := isIso_map_fiberι_of_contractibleSpace hF (mem_serreFibrations_pullbackFst hp f) x₁
    fiberIsoOfPath hF hp γ =
      F.mapIso (eqToIso (congrArg p.fiber hb₀.symm) ≪≫ (p.fiberPullbackFstIso f x₀).symm) ≪≫
        asIso (F.map ((_root_.TopCat.pullbackFst f p).fiberι x₀)) ≪≫
        (asIso (F.map ((_root_.TopCat.pullbackFst f p).fiberι x₁))).symm ≪≫
        F.mapIso (p.fiberPullbackFstIso f x₁ ≪≫ eqToIso (congrArg p.fiber hb₁)) := by
  have := isIso_map_fiberι_of_contractibleSpace hF (mem_serreFibrations_pullbackFst hp f) x₀
  have := isIso_map_fiberι_of_contractibleSpace hF (mem_serreFibrations_pullbackFst hp f) x₁
  rw [fiberIsoOfPath_pullbackFst hF hp f γ' γ hb₀ hb₁ hγ,
    fiberIsoOfPath_eq_of_contractibleSpace hF (mem_serreFibrations_pullbackFst hp f) γ']
  simp [Iso.trans_assoc]

/-- Path transport along the constant path `Path.refl b` is the identity isomorphism. -/
@[simp]
theorem fiberIsoOfPath_refl (b : B) :
    fiberIsoOfPath hF hp (Path.refl b) = Iso.refl _ := by
  let f : _root_.TopCat.of PUnit.{u + 1} ⟶ B := _root_.TopCat.ofHom (ContinuousMap.const _ b)
  rw [fiberIsoOfPath_of_contractibleSpace_lift hF hp f (Path.refl PUnit.unit) (Path.refl b)
    rfl rfl fun _ ↦ rfl]
  ext
  simp

/-- Path transport along the reversed path `γ.symm` is the inverse isomorphism. -/
@[simp]
theorem fiberIsoOfPath_symm {b₀ b₁ : B} (γ : Path b₀ b₁) :
    fiberIsoOfPath hF hp γ.symm = (fiberIsoOfPath hF hp γ).symm := by
  let f := pathToTopCatHom γ
  rw [fiberIsoOfPath_of_contractibleSpace_lift hF hp f uliftUnitIntervalPath γ
      γ.source γ.target fun _ ↦ rfl,
    fiberIsoOfPath_of_contractibleSpace_lift hF hp f uliftUnitIntervalPath.symm γ.symm
      γ.target γ.source fun _ ↦ rfl]
  ext
  simp

/-- Path transport along a concatenation `γ.trans δ` is the composition of the path transport
isomorphisms along `γ` and `δ`. -/
@[simp]
theorem fiberIsoOfPath_trans {b₀ b₁ b₂ : B} (γ : Path b₀ b₁) (δ : Path b₁ b₂) :
    fiberIsoOfPath hF hp (γ.trans δ) =
      fiberIsoOfPath hF hp γ ≪≫ fiberIsoOfPath hF hp δ := by
  let f := pathToTopCatHom (γ.trans δ)
  let m : unitInterval := ⟨1 / 2, by constructor <;> norm_num⟩
  let ι₁ := (Path.id.subpath 0 m).map continuous_uliftUp
  let ι₂ := (Path.id.subpath m 1).map continuous_uliftUp
  -- Evaluate `γ.trans δ` on the midpoint and on each half-interval subpath.
  have hm : f (ULift.up m) = b₁ :=
    (Path.trans_apply_of_eq_two_mul γ δ (u := m) (v := 1) (by simp [m])).trans γ.target
  have hι₁ (t : unitInterval) : f (ι₁ t) = γ t :=
    Path.trans_apply_of_eq_two_mul γ δ (v := t)
      (by simp [ι₁, Path.subpath, Set.Icc.convexComb, m]; ring)
  have hι₂ (t : unitInterval) : f (ι₂ t) = δ t :=
    Path.trans_apply_of_eq_two_mul_sub_one γ δ (v := t)
      (by simp [ι₂, Path.subpath, Set.Icc.convexComb, m]; ring)
  rw [fiberIsoOfPath_of_contractibleSpace_lift hF hp f uliftUnitIntervalPath (γ.trans δ)
      (γ.trans δ).source (γ.trans δ).target (fun _ ↦ rfl),
    fiberIsoOfPath_of_contractibleSpace_lift hF hp f ι₁ γ (γ.trans δ).source hm hι₁,
    fiberIsoOfPath_of_contractibleSpace_lift hF hp f ι₂ δ hm (γ.trans δ).target hι₂]
  ext
  simp
  rfl

/-- Homotopic paths with fixed endpoints induce the same path transport isomorphism. -/
theorem fiberIsoOfPath_congr {b₀ b₁ : B} {γ₀ γ₁ : Path b₀ b₁} (h : γ₀.Homotopic γ₁) :
    fiberIsoOfPath hF hp γ₀ = fiberIsoOfPath hF hp γ₁ := by
  obtain ⟨H⟩ := h
  let f : _root_.TopCat.of (ULift.{u} (unitInterval × unitInterval)) ⟶ B :=
    _root_.TopCat.ofHom ⟨fun x ↦ H x.down, H.continuous.comp continuous_uliftDown⟩
  -- Pull `p` back to the contractible square `I × I`; the four edges lift `γ₀`, `refl b₁`,
  -- `refl b₀`, and `γ₁`.
  let α₀ := ((Path.refl (0 : unitInterval)).prod Path.id).map continuous_uliftUp
  let α₁ := ((Path.refl (1 : unitInterval)).prod Path.id).map continuous_uliftUp
  let c₀ := (Path.id.prod (Path.refl (0 : unitInterval))).map continuous_uliftUp
  let c₁ := (Path.id.prod (Path.refl (1 : unitInterval))).map continuous_uliftUp
  have hsq :
      fiberIsoOfPath hF hp γ₀ ≪≫ fiberIsoOfPath hF hp (Path.refl b₁) =
        fiberIsoOfPath hF hp (Path.refl b₀) ≪≫ fiberIsoOfPath hF hp γ₁ := by
    rw [fiberIsoOfPath_of_contractibleSpace_lift hF hp f α₀ γ₀
        ((H.apply_zero 0).trans γ₀.source) ((H.apply_zero 1).trans γ₀.target)
        (fun t ↦ H.apply_zero t),
      fiberIsoOfPath_of_contractibleSpace_lift hF hp f c₁ (Path.refl b₁)
        ((H.apply_zero 1).trans γ₀.target) ((H.apply_one 1).trans γ₁.target)
        (fun s ↦ (H.prop' s 1 (Or.inr rfl)).trans γ₀.target),
      fiberIsoOfPath_of_contractibleSpace_lift hF hp f c₀ (Path.refl b₀)
        ((H.apply_zero 0).trans γ₀.source) ((H.apply_one 0).trans γ₁.source)
        (fun s ↦ (H.prop' s 0 (Or.inl rfl)).trans γ₀.source),
      fiberIsoOfPath_of_contractibleSpace_lift hF hp f α₁ γ₁
        ((H.apply_one 0).trans γ₁.source) ((H.apply_one 1).trans γ₁.target)
        (fun t ↦ H.apply_one t)]
    ext
    simp
  simpa using hsq

end TauCeti.TopCat

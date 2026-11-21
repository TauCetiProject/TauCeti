/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.MorphismProperty.IsInvertedBy
public import TauCeti.Topology.Category.TopCat.Pullback
public import TauCeti.Topology.Category.TopCat.WeakEquivalence
public import TauCeti.Topology.Homotopy.SerreFibration.WeakHomotopyEquivalence
public import TauCeti.Topology.Homotopy.TopCat.Path

import TauCeti.Topology.Homotopy.Contractible

/-!
# Path transport on fibres of a Serre fibration

Let `p : E ⟶ B` be a Serre fibration (`TauCeti.TopCat.serreFibrations`), and let
`F : TopCat.{u} ⥤ C` be any functor that inverts weak homotopy equivalences
(`TauCeti.TopCat.weakEquivalences.IsInvertedBy F`), such as singular homology or cohomology with
arbitrary coefficients. Over a contractible base `B`, every fibre inclusion `p.fiberι b` is a weak
homotopy equivalence (`TauCeti.TopCat.isWeakHomotopyEquivalence_fiberι_of_contractibleSpace`), so
`F.map (p.fiberι b)` is an isomorphism (`TauCeti.TopCat.isIso_map_fiberι_of_contractibleSpace`).

More generally, for any map `g : K ⟶ B` from a contractible parameter space `K` and points
`k₀, k₁ : K` over `b₀, b₁ : B`, the fibre inclusions `p.pullbackFiberι g` into the base change
of `p` along `g` are weak homotopy equivalences
(`TauCeti.TopCat.isWeakHomotopyEquivalence_pullbackFiberι`), so `F` sends them to isomorphisms
(`TauCeti.TopCat.isIso_map_pullbackFiberι`). Composing the forward isomorphism at `k₀` with the
inverse isomorphism at `k₁` yields a transport isomorphism
`F.obj (p.fiber b₀) ≅ F.obj (p.fiber b₁)` (`TauCeti.TopCat.pullbackFiberIso`). This transport is
transitive (`pullbackFiberIso_trans`), trivial along paths in `K` on which `g` is constant
(`pullbackFiberIso_eq_refl`), natural in maps of parameter spaces (`pullbackFiberIso_comp_left`),
maps of Serre fibrations (`pullbackFiberIso_naturality`), and natural transformations
(`pullbackFiberIso_hom_comp_app`).

Specializing `pullbackFiberIso` to the interval morphism `(TopCat.pathEquiv.symm γ).hom` of a path
`γ : Path b₀ b₁` produces path transport `F.obj (p.fiber b₀) ≅ F.obj (p.fiber b₁)`
(`TauCeti.TopCat.fiberIsoOfPath`). It commutes with the fibre inclusions into `E`
(`fiberIsoOfPath_hom_comp_map_fiberι`), reduces to the zig-zag of fibre inclusions over a
contractible base (`fiberIsoOfPath_eq_of_contractibleSpace`), is natural in maps of Serre
fibrations (`fiberIsoOfPath_naturality`), base change (`fiberIsoOfPath_pullbackFst`), and natural
transformations `F ⟶ G` (`fiberIsoOfPath_hom_comp_app`), and depends only on the endpoint-fixing
homotopy class of `γ` (`fiberIsoOfPath_refl`, `fiberIsoOfPath_symm`, `fiberIsoOfPath_trans`,
`fiberIsoOfPath_congr`).

## Main declarations

* `TauCeti.TopCat.isIso_map_fiberι_of_contractibleSpace`: over a contractible base, a functor
  inverting weak homotopy equivalences sends every fibre inclusion of a Serre fibration to an
  isomorphism.
* `TauCeti.TopCat.isIso_map_pullbackFiberι`: a functor inverting weak homotopy equivalences sends
  every fibre inclusion into a base change over a contractible space to an isomorphism.
* `TauCeti.TopCat.pullbackFiberIso`: transport isomorphism `F.obj (p.fiber b₀) ≅ F.obj (p.fiber b₁)`
  over a contractible parameter space.
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
open scoped Topology unitInterval ContinuousMap

universe u v w

namespace TauCeti.TopCat

variable {C : Type v} [Category.{w} C] {F : _root_.TopCat.{u} ⥤ C}
  {E B : _root_.TopCat.{u}} {p : E ⟶ B}

/-- Any functor inverting weak homotopy equivalences maps freely homotopic continuous maps to equal
morphisms. -/
private theorem map_eq_of_homotopy (hF : weakEquivalences.{u}.IsInvertedBy F)
    {X Y : _root_.TopCat.{u}} {f₀ f₁ : X ⟶ Y} (H : ContinuousMap.Homotopy f₀.hom f₁.hom) :
    F.map f₀ = F.map f₁ := by
  let IX := _root_.TopCat.of (_root_.TopCat.I.{u} × X)
  let snd : IX ⟶ X := _root_.TopCat.ofHom ContinuousMap.snd
  let i₀ : X ⟶ IX := _root_.TopCat.ofHom ⟨fun x ↦ (0, x), by fun_prop⟩
  let i₁ : X ⟶ IX := _root_.TopCat.ofHom ⟨fun x ↦ (1, x), by fun_prop⟩
  let Hmap : IX ⟶ Y :=
    _root_.TopCat.ofHom ⟨fun q ↦ H (_root_.TopCat.I.homeomorph q.1, q.2), by fun_prop⟩
  let e : (_root_.TopCat.I.{u} × X) ≃ₕ X :=
    { toFun := ContinuousMap.snd
      invFun := i₀.hom
      left_inv := Nonempty.intro
        { toContinuousMap :=
            ⟨fun q ↦ (_root_.TopCat.I.homeomorph.symm (q.1 * _root_.TopCat.I.homeomorph q.2.1),
              q.2.2), by fun_prop⟩
          map_zero_left q := by
            simp [i₀, _root_.TopCat.I.homeomorph.symm_apply_eq, _root_.TopCat.I.homeomorph_zero]
          map_one_left q := by simp }
      right_inv := ContinuousMap.Homotopic.refl _ }
  have hsnd : IsIso (F.map snd) :=
    hF _ ((mem_weakEquivalences_iff _).2 e.isWeakHomotopyEquivalence)
  have hi : F.map i₀ = F.map i₁ := by
    refine (cancel_mono (F.map snd)).1 ?_
    rw [← F.map_comp, ← F.map_comp]
    have h₀ : i₀ ≫ snd = 𝟙 X := rfl
    have h₁ : i₁ ≫ snd = 𝟙 X := rfl
    rw [h₀, h₁]
  have hf₀ : i₀ ≫ Hmap = f₀ := by
    ext x
    exact H.apply_zero x
  have hf₁ : i₁ ≫ Hmap = f₁ := by
    ext x
    exact H.apply_one x
  rw [← hf₀, ← hf₁, F.map_comp, F.map_comp, hi]

/-- Over a contractible base, any functor inverting weak homotopy equivalences sends every fibre
inclusion of a Serre fibration to an isomorphism. -/
theorem isIso_map_fiberι_of_contractibleSpace (hF : weakEquivalences.{u}.IsInvertedBy F)
    (hp : serreFibrations p) [ContractibleSpace B] (b : B) :
    IsIso (F.map (p.fiberι b)) :=
  hF _ ((mem_weakEquivalences_iff _).2 (isWeakHomotopyEquivalence_fiberι_of_contractibleSpace hp b))

/-- Over a contractible parameter space `K`, any functor inverting weak homotopy equivalences sends
the fibre inclusions `p.pullbackFiberι g h` into the base change of a Serre fibration along
`g : K ⟶ B` to isomorphisms. -/
theorem isIso_map_pullbackFiberι (hF : weakEquivalences.{u}.IsInvertedBy F)
    (hp : serreFibrations p) {K : _root_.TopCat.{u}} [ContractibleSpace K]
    (g : K ⟶ B) {k : K} {b : B} (h : g k = b) :
    IsIso (F.map (p.pullbackFiberι g h)) :=
  hF _ ((mem_weakEquivalences_iff _).2 (isWeakHomotopyEquivalence_pullbackFiberι hp g h))

section Pullback

variable (hF : weakEquivalences.{u}.IsInvertedBy F) (hp : serreFibrations p)
  {K : _root_.TopCat.{u}} [ContractibleSpace K]

/-- **Transport over a contractible parameter space.** For a Serre fibration `p`, a functor
`F : TopCat.{u} ⥤ C` inverting weak homotopy equivalences, a map `g : K ⟶ B` from a contractible
space, and points `k₀, k₁ : K` over `b₀, b₁ : B`, the isomorphism
`F.obj (p.fiber b₀) ≅ F.obj (p.fiber b₁)` obtained by composing `F.map (p.pullbackFiberι g h₀)`
with `(F.map (p.pullbackFiberι g h₁))⁻¹`. -/
noncomputable def pullbackFiberIso (g : K ⟶ B) {k₀ k₁ : K} {b₀ b₁ : B}
    (h₀ : g k₀ = b₀) (h₁ : g k₁ = b₁) :
    F.obj (p.fiber b₀) ≅ F.obj (p.fiber b₁) :=
  have := isIso_map_pullbackFiberι hF hp g h₀
  have := isIso_map_pullbackFiberι hF hp g h₁
  asIso (F.map (p.pullbackFiberι g h₀)) ≪≫ (asIso (F.map (p.pullbackFiberι g h₁))).symm

/-- Transport over a contractible parameter space followed by the fibre inclusion at the end point
equals the fibre inclusion at the starting point. -/
@[reassoc (attr := simp)]
theorem pullbackFiberIso_hom_comp_map_pullbackFiberι (g : K ⟶ B) {k₀ k₁ : K} {b₀ b₁ : B}
    (h₀ : g k₀ = b₀) (h₁ : g k₁ = b₁) :
    (pullbackFiberIso hF hp g h₀ h₁).hom ≫ F.map (p.pullbackFiberι g h₁) =
      F.map (p.pullbackFiberι g h₀) := by
  have := isIso_map_pullbackFiberι hF hp g h₁
  simp [pullbackFiberIso]

/-- The inverse of `pullbackFiberIso` followed by the fibre inclusion at the starting point equals
the fibre inclusion at the end point. -/
@[reassoc (attr := simp)]
theorem pullbackFiberIso_inv_comp_map_pullbackFiberι (g : K ⟶ B) {k₀ k₁ : K} {b₀ b₁ : B}
    (h₀ : g k₀ = b₀) (h₁ : g k₁ = b₁) :
    (pullbackFiberIso hF hp g h₀ h₁).inv ≫ F.map (p.pullbackFiberι g h₀) =
      F.map (p.pullbackFiberι g h₁) :=
  (Iso.inv_comp_eq _).2 (pullbackFiberIso_hom_comp_map_pullbackFiberι hF hp g h₀ h₁).symm

/-- **Characterization of transport over a contractible parameter space.** A morphism equals
`(pullbackFiberIso hF hp g h₀ h₁).hom` if and only if postcomposing with the fibre inclusion at the
end point gives the fibre inclusion at the starting point. -/
theorem eq_pullbackFiberIso_hom_iff (g : K ⟶ B) {k₀ k₁ : K} {b₀ b₁ : B}
    (h₀ : g k₀ = b₀) (h₁ : g k₁ = b₁) (f : F.obj (p.fiber b₀) ⟶ F.obj (p.fiber b₁)) :
    f = (pullbackFiberIso hF hp g h₀ h₁).hom ↔
      f ≫ F.map (p.pullbackFiberι g h₁) = F.map (p.pullbackFiberι g h₀) := by
  have := isIso_map_pullbackFiberι hF hp g h₁
  rw [← cancel_mono (F.map (p.pullbackFiberι g h₁)),
    pullbackFiberIso_hom_comp_map_pullbackFiberι]

/-- Transport from a point of a contractible parameter space to itself is the identity
isomorphism. -/
@[simp]
theorem pullbackFiberIso_self (g : K ⟶ B) {k : K} {b : B} (h : g k = b) :
    pullbackFiberIso hF hp g h h = Iso.refl _ :=
  Iso.ext ((eq_pullbackFiberIso_hom_iff hF hp g h h _).2 (Category.id_comp _)).symm

/-- Swapping the two points of a contractible parameter space inverts `pullbackFiberIso`. -/
theorem pullbackFiberIso_symm (g : K ⟶ B) {k₀ k₁ : K} {b₀ b₁ : B}
    (h₀ : g k₀ = b₀) (h₁ : g k₁ = b₁) :
    pullbackFiberIso hF hp g h₁ h₀ = (pullbackFiberIso hF hp g h₀ h₁).symm :=
  Iso.ext ((eq_pullbackFiberIso_hom_iff hF hp g h₁ h₀ _).2
    (pullbackFiberIso_inv_comp_map_pullbackFiberι hF hp g h₀ h₁)).symm

/-- **Transitivity of transport over a contractible parameter space.** -/
@[simp]
theorem pullbackFiberIso_trans (g : K ⟶ B) {k₀ k₁ k₂ : K} {b₀ b₁ b₂ : B}
    (h₀ : g k₀ = b₀) (h₁ : g k₁ = b₁) (h₂ : g k₂ = b₂) :
    pullbackFiberIso hF hp g h₀ h₁ ≪≫ pullbackFiberIso hF hp g h₁ h₂ =
      pullbackFiberIso hF hp g h₀ h₂ :=
  Iso.ext ((eq_pullbackFiberIso_hom_iff hF hp g h₀ h₂ _).2 (by simp))

/-- **Transport along a path in `K` on which `g` is constant is the identity.** If `γ : Path k₀ k₁`
in `K` is mapped constantly to `b` by `g`, the endpoint fibre inclusions into the base change are
homotopic, so `pullbackFiberIso` is `Iso.refl _`. -/
theorem pullbackFiberIso_eq_refl (g : K ⟶ B) {k₀ k₁ : K} {b : B}
    (γ : Path k₀ k₁) (hγ : ∀ t, g (γ t) = b) (h₀ : g k₀ = b) (h₁ : g k₁ = b) :
    pullbackFiberIso hF hp g h₀ h₁ = Iso.refl _ := by
  refine Iso.ext ((eq_pullbackFiberIso_hom_iff hF hp g h₀ h₁ _).2 ?_).symm
  let H : ContinuousMap.Homotopy (p.pullbackFiberι g h₁).hom (p.pullbackFiberι g h₀).hom :=
    { toFun x := ⟨(γ (unitInterval.symm x.1), x.2.val),
        (hγ _).trans (x.2.property : p x.2.val = b).symm⟩
      continuous_toFun := by fun_prop
      map_zero_left x := Subtype.ext (by rw [_root_.TopCat.Hom.coe_pullbackFiberι_apply]; simp)
      map_one_left x := Subtype.ext (by rw [_root_.TopCat.Hom.coe_pullbackFiberι_apply]; simp) }
  rw [Iso.refl_hom, Category.id_comp]
  exact map_eq_of_homotopy hF H

/-- **Naturality of `pullbackFiberIso` in maps of Serre fibrations.** -/
@[reassoc]
theorem pullbackFiberIso_naturality {E' B' K' : _root_.TopCat.{u}} {p' : E' ⟶ B'}
    [ContractibleSpace K'] {f : E ⟶ E'} {g_B : B ⟶ B'} (sq : CommSq f p p' g_B)
    (hp' : serreFibrations p') (g : K ⟶ B) (g' : K' ⟶ B') (φ : K ⟶ K')
    (hφ : φ ≫ g' = g ≫ g_B) {k₀ k₁ : K} {b₀ b₁ : B} (h₀ : g k₀ = b₀) (h₁ : g k₁ = b₁)
    (h₀' : g' (φ k₀) = g_B b₀) (h₁' : g' (φ k₁) = g_B b₁) :
    (pullbackFiberIso hF hp g h₀ h₁).hom ≫ F.map (sq.fiberMap b₁) =
      F.map (sq.fiberMap b₀) ≫ (pullbackFiberIso hF hp' g' h₀' h₁').hom := by
  have := isIso_map_pullbackFiberι hF hp' g' h₁'
  have hm {k : K} {b : B} (h : g k = b) (h' : g' (φ k) = g_B b) :
      F.map (sq.fiberMap b) ≫ F.map (p'.pullbackFiberι g' h') =
        F.map (p.pullbackFiberι g h) ≫ F.map (sq.pullbackMapOfCompEq φ hφ) := by
    rw [← F.map_comp, ← F.map_comp, sq.pullbackFiberι_comp_pullbackMapOfCompEq]
  refine (cancel_mono (F.map (p'.pullbackFiberι g' h₁'))).1 ?_
  simp only [Category.assoc, hm h₁ h₁', hm h₀ h₀',
    pullbackFiberIso_hom_comp_map_pullbackFiberι,
    pullbackFiberIso_hom_comp_map_pullbackFiberι_assoc]

/-- **Naturality of `pullbackFiberIso` in maps of parameter spaces.** If `φ : K' ⟶ K` satisfies
`φ ≫ g = g'`, transport along `g'` from `k₀` to `k₁` equals transport along `g` from `φ k₀` to
`φ k₁`. -/
theorem pullbackFiberIso_comp_left {K' : _root_.TopCat.{u}} [ContractibleSpace K']
    (g : K ⟶ B) (g' : K' ⟶ B) (φ : K' ⟶ K) (hφ : φ ≫ g = g')
    {k₀ k₁ : K'} {k₀' k₁' : K} (hk₀ : φ k₀ = k₀') (hk₁ : φ k₁ = k₁') {b₀ b₁ : B}
    (h₀ : g' k₀ = b₀) (h₁ : g' k₁ = b₁) (h₀' : g k₀' = b₀) (h₁' : g k₁' = b₁) :
    pullbackFiberIso hF hp g' h₀ h₁ = pullbackFiberIso hF hp g h₀' h₁' := by
  subst hφ hk₀ hk₁
  exact Iso.ext <| by
    simpa using pullbackFiberIso_naturality hF hp (CommSq.mk (by simp : 𝟙 E ≫ p = p ≫ 𝟙 B))
      hp (φ ≫ g) g φ (Category.comp_id _).symm h₀ h₁ h₀' h₁'

/-- **Naturality of `pullbackFiberIso` in natural transformations** between functors inverting weak
homotopy equivalences. -/
@[reassoc]
theorem pullbackFiberIso_hom_comp_app {G : _root_.TopCat.{u} ⥤ C}
    (hG : weakEquivalences.{u}.IsInvertedBy G) (α : F ⟶ G) (g : K ⟶ B) {k₀ k₁ : K}
    {b₀ b₁ : B} (h₀ : g k₀ = b₀) (h₁ : g k₁ = b₁) :
    (pullbackFiberIso hF hp g h₀ h₁).hom ≫ α.app (p.fiber b₁) =
      α.app (p.fiber b₀) ≫ (pullbackFiberIso hG hp g h₀ h₁).hom := by
  have := isIso_map_pullbackFiberι hF hp g h₁
  have := isIso_map_pullbackFiberι hG hp g h₁
  refine (cancel_mono (G.map (p.pullbackFiberι g h₁))).1 ?_
  simp only [Category.assoc, pullbackFiberIso_hom_comp_map_pullbackFiberι, ← α.naturality,
    pullbackFiberIso_hom_comp_map_pullbackFiberι_assoc]

end Pullback

section Path

/-- **Path transport on fibres of a Serre fibration.** Given a functor `F : TopCat.{u} ⥤ C` that
inverts weak homotopy equivalences and a Serre fibration `p : E ⟶ B`, a path `γ : Path b₀ b₁`
induces a canonical isomorphism `F.obj (p.fiber b₀) ≅ F.obj (p.fiber b₁)` by pulling `p` back to
the contractible interval `TopCat.I` along `(TopCat.pathEquiv.symm γ).hom` and inverting the
induced maps of the endpoint fibre inclusions. -/
@[expose] noncomputable def fiberIsoOfPath (hF : weakEquivalences.{u}.IsInvertedBy F)
    (hp : serreFibrations p) {b₀ b₁ : B} (γ : Path b₀ b₁) :
    F.obj (p.fiber b₀) ≅ F.obj (p.fiber b₁) :=
  pullbackFiberIso hF hp (_root_.TopCat.pathEquiv.symm γ).hom (k₀ := 0) (k₁ := 1)
    (_root_.TopCat.pathEquiv.symm γ).hom₀ (_root_.TopCat.pathEquiv.symm γ).hom₁

variable (hF : weakEquivalences.{u}.IsInvertedBy F) (hp : serreFibrations p)

/-- Path transport along `γ` is transport over `TopCat.I` along `(TopCat.pathEquiv.symm γ).hom`
from `0` to `1`. -/
theorem fiberIsoOfPath_eq_pullbackFiberIso {b₀ b₁ : B} (γ : Path b₀ b₁) :
    fiberIsoOfPath hF hp γ =
      pullbackFiberIso hF hp (_root_.TopCat.pathEquiv.symm γ).hom (k₀ := 0) (k₁ := 1)
        (_root_.TopCat.pathEquiv.symm γ).hom₀ (_root_.TopCat.pathEquiv.symm γ).hom₁ :=
  rfl

/-- Path transport along `γ : Path b₀ b₁` followed by the fibre inclusion at `1` into the base
change along `γ` equals the fibre inclusion at `0`. -/
@[reassoc (attr := simp)]
theorem fiberIsoOfPath_hom_comp_map_pullbackFiberι {b₀ b₁ : B} (γ : Path b₀ b₁) :
    (fiberIsoOfPath hF hp γ).hom ≫
        F.map (p.pullbackFiberι (_root_.TopCat.pathEquiv.symm γ).hom (k := 1)
          (_root_.TopCat.pathEquiv.symm γ).hom₁) =
      F.map (p.pullbackFiberι (_root_.TopCat.pathEquiv.symm γ).hom (k := 0)
        (_root_.TopCat.pathEquiv.symm γ).hom₀) :=
  pullbackFiberIso_hom_comp_map_pullbackFiberι hF hp _ _ _

/-- The inverse of `fiberIsoOfPath` followed by the fibre inclusion at `0` into the base change
along `γ` equals the fibre inclusion at `1`. -/
@[reassoc (attr := simp)]
theorem fiberIsoOfPath_inv_comp_map_pullbackFiberι {b₀ b₁ : B} (γ : Path b₀ b₁) :
    (fiberIsoOfPath hF hp γ).inv ≫
        F.map (p.pullbackFiberι (_root_.TopCat.pathEquiv.symm γ).hom (k := 0)
          (_root_.TopCat.pathEquiv.symm γ).hom₀) =
      F.map (p.pullbackFiberι (_root_.TopCat.pathEquiv.symm γ).hom (k := 1)
        (_root_.TopCat.pathEquiv.symm γ).hom₁) :=
  pullbackFiberIso_inv_comp_map_pullbackFiberι hF hp _ _ _

/-- **Characterization of path transport.** A morphism equals `(fiberIsoOfPath hF hp γ).hom` if and
only if postcomposing with the fibre inclusion at `1` into the base change along `γ` gives the
fibre inclusion at `0`. -/
theorem eq_fiberIsoOfPath_hom_iff {b₀ b₁ : B} (γ : Path b₀ b₁)
    (f : F.obj (p.fiber b₀) ⟶ F.obj (p.fiber b₁)) :
    f = (fiberIsoOfPath hF hp γ).hom ↔
      f ≫ F.map (p.pullbackFiberι (_root_.TopCat.pathEquiv.symm γ).hom (k := 1)
          (_root_.TopCat.pathEquiv.symm γ).hom₁) =
        F.map (p.pullbackFiberι (_root_.TopCat.pathEquiv.symm γ).hom (k := 0)
          (_root_.TopCat.pathEquiv.symm γ).hom₀) :=
  eq_pullbackFiberIso_hom_iff hF hp _ _ _ f

/-- Path transport along `γ : Path b₀ b₁` commutes with the maps induced by the fibre inclusions
`p.fiber b₀ ⟶ E` and `p.fiber b₁ ⟶ E`. -/
@[reassoc (attr := simp)]
theorem fiberIsoOfPath_hom_comp_map_fiberι {b₀ b₁ : B} (γ : Path b₀ b₁) :
    (fiberIsoOfPath hF hp γ).hom ≫ F.map (p.fiberι b₁) = F.map (p.fiberι b₀) := by
  let g := (_root_.TopCat.pathEquiv.symm γ).hom
  rw [← p.pullbackFiberι_comp_pullbackSnd g (_root_.TopCat.pathEquiv.symm γ).hom₁, F.map_comp,
    fiberIsoOfPath_hom_comp_map_pullbackFiberι_assoc, ← F.map_comp,
    p.pullbackFiberι_comp_pullbackSnd]

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

/-- Naturality of `fiberIsoOfPath` in maps of Serre fibrations: a commutative square
`sq : CommSq f p p' g` intertwines path transport along `γ` for `p` with path transport along
`γ.map g.hom.continuous` for `p'`. -/
@[reassoc]
theorem fiberIsoOfPath_naturality {E' B' : _root_.TopCat.{u}} {p' : E' ⟶ B'}
    (hp' : serreFibrations p') {f : E ⟶ E'} {g : B ⟶ B'} (sq : CommSq f p p' g)
    {b₀ b₁ : B} (γ : Path b₀ b₁) :
    (fiberIsoOfPath hF hp γ).hom ≫ F.map (sq.fiberMap b₁) =
      F.map (sq.fiberMap b₀) ≫ (fiberIsoOfPath hF hp' (γ.map g.hom.continuous)).hom :=
  pullbackFiberIso_naturality hF hp sq hp' (_root_.TopCat.pathEquiv.symm γ).hom
    (_root_.TopCat.pathEquiv.symm (γ.map g.hom.continuous)).hom (𝟙 _)
    (by rw [Category.id_comp, _root_.TopCat.pathEquiv_symm_map_hom])
    (_root_.TopCat.pathEquiv.symm γ).hom₀ (_root_.TopCat.pathEquiv.symm γ).hom₁
    (by simp) (by simp)

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
  subst hb₀ hb₁
  have sq : CommSq (_root_.TopCat.pullbackSnd f p) (_root_.TopCat.pullbackFst f p) p f :=
    ⟨(_root_.TopCat.pullbackCone f p).condition.symm⟩
  have hsq (x : B') : sq.fiberMap x = (p.fiberPullbackFstIso f x).hom :=
    sq.fiberMap_pullbackSnd x
  have hφ : 𝟙 _root_.TopCat.I.{u} ≫ (_root_.TopCat.pathEquiv.symm γ).hom =
      (_root_.TopCat.pathEquiv.symm γ').hom ≫ f :=
    _root_.TopCat.ext fun t ↦ (hγ (_root_.TopCat.I.homeomorph t)).symm
  have hnat := pullbackFiberIso_naturality hF (mem_serreFibrations_pullbackFst hp f) sq hp
    (_root_.TopCat.pathEquiv.symm γ').hom (_root_.TopCat.pathEquiv.symm γ).hom (𝟙 _) hφ
    (_root_.TopCat.pathEquiv.symm γ').hom₀ (_root_.TopCat.pathEquiv.symm γ').hom₁
    (by simp) (by simp)
  simp only [hsq] at hnat
  apply Iso.ext
  simp only [fiberIsoOfPath_eq_pullbackFiberIso, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom,
    eqToIso.hom, eqToHom_refl, Category.id_comp, Category.comp_id]
  rw [hnat, ← F.map_comp_assoc]
  simp

/-- Naturality of `fiberIsoOfPath` in natural transformations between functors inverting weak
homotopy equivalences. -/
@[reassoc]
theorem fiberIsoOfPath_hom_comp_app {G : _root_.TopCat.{u} ⥤ C}
    (hG : weakEquivalences.{u}.IsInvertedBy G) (α : F ⟶ G) {b₀ b₁ : B} (γ : Path b₀ b₁) :
    (fiberIsoOfPath hF hp γ).hom ≫ α.app (p.fiber b₁) =
      α.app (p.fiber b₀) ≫ (fiberIsoOfPath hG hp γ).hom :=
  pullbackFiberIso_hom_comp_app hF hp hG α (_root_.TopCat.pathEquiv.symm γ).hom _ _

/-- Path transport along the constant path `Path.refl b` is the identity isomorphism. -/
@[simp]
theorem fiberIsoOfPath_refl (b : B) :
    fiberIsoOfPath hF hp (Path.refl b) = Iso.refl _ :=
  pullbackFiberIso_eq_refl hF hp (_root_.TopCat.pathEquiv.symm (Path.refl b)).hom
    ⟨⟨fun t ↦ _root_.TopCat.I.homeomorph.symm t, by fun_prop⟩,
      _root_.TopCat.I.homeomorph.symm_apply_eq.2 _root_.TopCat.I.homeomorph_zero.symm,
      _root_.TopCat.I.homeomorph.symm_apply_eq.2 _root_.TopCat.I.homeomorph_one.symm⟩
    (fun _ ↦ by rw [_root_.TopCat.pathEquiv_symm_hom_apply, Path.refl_apply]) _ _

/-- Path transport along the reversed path `γ.symm` is the inverse isomorphism. -/
@[simp]
theorem fiberIsoOfPath_symm {b₀ b₁ : B} (γ : Path b₀ b₁) :
    fiberIsoOfPath hF hp γ.symm = (fiberIsoOfPath hF hp γ).symm := by
  let rev : _root_.TopCat.I.{u} ⟶ _root_.TopCat.I.{u} :=
    _root_.TopCat.ofHom
      ⟨fun t ↦ _root_.TopCat.I.homeomorph.symm (unitInterval.symm (_root_.TopCat.I.homeomorph t)),
        by fun_prop⟩
  have hrev : rev ≫ (_root_.TopCat.pathEquiv.symm γ).hom =
      (_root_.TopCat.pathEquiv.symm γ.symm).hom := by
    ext t
    simp [rev, Path.symm_apply]
  have h0 : rev 0 = 1 :=
    _root_.TopCat.I.homeomorph.injective (Subtype.ext (by
      simp [rev, _root_.TopCat.I.homeomorph_zero, _root_.TopCat.I.homeomorph_one]))
  have h1 : rev 1 = 0 :=
    _root_.TopCat.I.homeomorph.injective (Subtype.ext (by
      simp [rev, _root_.TopCat.I.homeomorph_zero, _root_.TopCat.I.homeomorph_one]))
  rw [fiberIsoOfPath_eq_pullbackFiberIso, fiberIsoOfPath_eq_pullbackFiberIso,
    pullbackFiberIso_comp_left hF hp (_root_.TopCat.pathEquiv.symm γ).hom _ rev hrev h0 h1
      (_root_.TopCat.pathEquiv.symm γ.symm).hom₀ (_root_.TopCat.pathEquiv.symm γ.symm).hom₁
      (_root_.TopCat.pathEquiv.symm γ).hom₁ (_root_.TopCat.pathEquiv.symm γ).hom₀,
    pullbackFiberIso_symm]

/-- Path transport along a concatenation `γ.trans δ` is the composition of the path transport
isomorphisms along `γ` and `δ`. -/
@[simp]
theorem fiberIsoOfPath_trans {b₀ b₁ b₂ : B} (γ : Path b₀ b₁) (δ : Path b₁ b₂) :
    fiberIsoOfPath hF hp (γ.trans δ) =
      fiberIsoOfPath hF hp γ ≪≫ fiberIsoOfPath hF hp δ := by
  rw [fiberIsoOfPath_eq_pullbackFiberIso, fiberIsoOfPath_eq_pullbackFiberIso,
    fiberIsoOfPath_eq_pullbackFiberIso,
    ← pullbackFiberIso_trans hF hp (_root_.TopCat.pathEquiv.symm (γ.trans δ)).hom
      (_root_.TopCat.pathEquiv.symm (γ.trans δ)).hom₀
      (_root_.TopCat.pathEquiv_symm_trans_hom_midpoint γ δ)
      (_root_.TopCat.pathEquiv.symm (γ.trans δ)).hom₁,
    pullbackFiberIso_comp_left hF hp _ _ _root_.TopCat.I.firstHalf
      (_root_.TopCat.firstHalf_comp_pathEquiv_symm_trans_hom γ δ)
      _root_.TopCat.I.firstHalf_zero _root_.TopCat.I.firstHalf_one
      (_root_.TopCat.pathEquiv.symm γ).hom₀ (_root_.TopCat.pathEquiv.symm γ).hom₁
      (_root_.TopCat.pathEquiv.symm (γ.trans δ)).hom₀
      (_root_.TopCat.pathEquiv_symm_trans_hom_midpoint γ δ),
    pullbackFiberIso_comp_left hF hp _ _ _root_.TopCat.I.secondHalf
      (_root_.TopCat.secondHalf_comp_pathEquiv_symm_trans_hom γ δ)
      _root_.TopCat.I.secondHalf_zero _root_.TopCat.I.secondHalf_one
      (_root_.TopCat.pathEquiv.symm δ).hom₀ (_root_.TopCat.pathEquiv.symm δ).hom₁
      (_root_.TopCat.pathEquiv_symm_trans_hom_midpoint γ δ)
      (_root_.TopCat.pathEquiv.symm (γ.trans δ)).hom₁]

/-- Homotopic paths with fixed endpoints induce the same path transport isomorphism. -/
theorem fiberIsoOfPath_congr {b₀ b₁ : B} {γ₀ γ₁ : Path b₀ b₁} (h : γ₀.Homotopic γ₁) :
    fiberIsoOfPath hF hp γ₀ = fiberIsoOfPath hF hp γ₁ := by
  obtain ⟨H⟩ := h
  let g : _root_.TopCat.of (ULift.{u} (unitInterval × unitInterval)) ⟶ B :=
    _root_.TopCat.ofHom (H.toContinuousMap.comp ⟨ULift.down, continuous_uliftDown⟩)
  let φ (s : unitInterval) :
      _root_.TopCat.I.{u} ⟶ _root_.TopCat.of (ULift.{u} (unitInterval × unitInterval)) :=
    _root_.TopCat.ofHom ⟨fun t ↦ ULift.up (s, _root_.TopCat.I.homeomorph t), by fun_prop⟩
  let edge (t : unitInterval) :
      Path (ULift.up ((0 : unitInterval), t)) (ULift.up ((1 : unitInterval), t)) :=
    ⟨⟨fun s ↦ ULift.up (s, t), by fun_prop⟩, rfl, rfl⟩
  have hl : fiberIsoOfPath hF hp γ₀ = pullbackFiberIso hF hp g
      (k₀ := ULift.up (0, 0)) (k₁ := ULift.up (0, 1)) (H.source 0) (H.target 0) :=
    pullbackFiberIso_comp_left hF hp g _ (φ 0)
      (by ext t; simp [g, φ]) (by simp [φ]) (by simp [φ]) _ _ _ _
  have hr : fiberIsoOfPath hF hp γ₁ = pullbackFiberIso hF hp g
      (k₀ := ULift.up (1, 0)) (k₁ := ULift.up (1, 1)) (H.source 1) (H.target 1) :=
    pullbackFiberIso_comp_left hF hp g _ (φ 1)
      (by ext t; simp [g, φ]) (by simp [φ]) (by simp [φ]) _ _ _ _
  have hb := pullbackFiberIso_eq_refl hF hp g (edge 0) (fun s ↦ H.source s) (H.source 0)
    (H.source 1)
  have ht := pullbackFiberIso_eq_refl hF hp g (edge 1) (fun s ↦ H.target s) (H.target 0)
    (H.target 1)
  rw [hl, hr, ← Iso.trans_refl (pullbackFiberIso hF hp g _ (H.target 0)), ← ht,
    pullbackFiberIso_trans,
    ← pullbackFiberIso_trans hF hp g _ (H.source 1), hb, Iso.refl_trans]

end Path

end TauCeti.TopCat

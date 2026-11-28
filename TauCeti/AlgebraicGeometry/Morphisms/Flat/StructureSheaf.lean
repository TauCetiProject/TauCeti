/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import TauCeti.AlgebraicGeometry.RationalPoint.Basic
public import TauCeti.AlgebraicGeometry.Geometrically.GlobalSections
import TauCeti.AlgebraicGeometry.AffineScheme.Basic

/-!
# The pushforward of the structure sheaf under flat base change

A morphism of schemes `f : X ⟶ S` satisfies `f_* 𝒪_X = 𝒪_S` when every map
`f.app V : Γ(S, V) ⟶ Γ(X, f⁻¹ V)` is an isomorphism; it suffices to ask this for affine `V`. This
file shows that for a quasi-compact quasi-separated `f` this condition is stable under flat base
change: for every flat `g : T ⟶ S`, the projection `p : T ×_S X ⟶ T` again satisfies
`p_* 𝒪_{T ×_S X} = 𝒪_T`. On an
affine open `U` of `T` lying over an affine open `V` of `S`, the sections of `T ×_S X` over
`p⁻¹ U` are `Γ(X, f⁻¹ V) ⊗_{Γ(S, V)} Γ(T, U)` (Mathlib's
`AlgebraicGeometry.isIso_pushoutSection_of_isQuasiSeparated_of_flat_right`), which is `Γ(T, U)`
when `Γ(S, V) ⟶ Γ(X, f⁻¹ V)` is an isomorphism. Such opens form a basis of `T`, and a morphism of
sheaves that is an isomorphism on a basis is an isomorphism.

Over an affine base `Y` only the global sections are needed: if `X` is quasi-compact and
quasi-separated and `Γ(Y, 𝒪) ≅ Γ(X, 𝒪)`, then `f_* 𝒪_X = 𝒪_Y`, because over a basic open `D(r)`
both rings of sections are localizations away from `r`. So every flat base change `T ×_Y X ⟶ T`
induces an isomorphism on global sections. In particular, every flat base change of
`X ⟶ Spec Γ(X, 𝒪)` induces an isomorphism on global sections. When its target is affine, this
base change is the absolute affinization of its source.

Over a field every base change is flat, so a quasi-compact quasi-separated scheme `X` over a field
`K` with `Γ(X, 𝒪_X) = K` satisfies `p_* 𝒪_{X_T} = 𝒪_T` for *every* scheme `T` over `K`. This holds
for a proper (more generally, universally closed and quasi-separated) integral scheme with a
`K`-rational point, whose global functions are constant
(`TauCeti.AlgebraicGeometry.appTop_bijective_of_section`). It is the hypothesis "`f_* 𝒪_X = 𝒪`
universally" under which line bundles rigidified along a section of `X` have no automorphisms
other than the identity, after every base change.

The same universal equality holds for every universally closed quasi-separated geometrically
reduced and geometrically connected scheme over a field, including reducible curves. No rational
point is needed in this version.

## Main results

* `AlgebraicGeometry.Scheme.Hom.isIso_app_of_isBasis`: a morphism of schemes induces
  isomorphisms on the sections over all opens once it does so over a basis of opens.
* `TauCeti.AlgebraicGeometry.isIso_app_pullback_fst_of_flat` and
  `TauCeti.AlgebraicGeometry.isIso_app_pullback_snd_of_flat`: `f_* 𝒪_X = 𝒪_S` is stable under
  flat base change for quasi-compact quasi-separated `f`.
* `AlgebraicGeometry.Scheme.Hom.isIso_app_of_isIso_appTop_of_isAffine`: over an affine target,
  `f_* 𝒪_X = 𝒪_Y` for quasi-compact quasi-separated `X` as soon as `Γ(Y, 𝒪) ≅ Γ(X, 𝒪)`.
* `TauCeti.AlgebraicGeometry.isIso_appTop_of_isPullback_of_flat`: over an affine base, an
  isomorphism `Γ(Y, 𝒪) ≅ Γ(X, 𝒪)` for quasi-compact quasi-separated `X` survives flat base change.
* `TauCeti.AlgebraicGeometry.isIso_app_pullback_fst_of_isIso_appTop`: over a field, a
  quasi-compact quasi-separated scheme with constant global functions satisfies
  `p_* 𝒪_{X_T} = 𝒪_T` after every base change.
* `TauCeti.AlgebraicGeometry.isIso_app_pullback_fst_of_section`: the same for a universally
  closed quasi-separated integral scheme with a rational point, such as a proper one.
* `TauCeti.AlgebraicGeometry.appTop_eq_of_comp_snd_eq`: for `X` quasi-compact and
  quasi-separated over a field `K` with constant global functions, a regular function on
  `X ×_K T` takes equal values at any two points with the same image in `T`.
* `AlgebraicGeometry.Scheme.Hom.isIso_app_of_universallyClosed_of_geometricallyIntegral`: over a
  field, a universally closed geometrically integral morphism satisfies `f_* 𝒪_X = 𝒪_{Spec K}`
  without requiring quasi-separatedness or a rational point.
* `isIso_app_pullback_fst_of_geometricallyReduced_of_geometricallyConnected`: the same universal
  base-change equality for a universally closed quasi-separated geometrically reduced and
  geometrically connected scheme over a field, without a rational point or irreducibility.

## References

* [The Stacks Project, Lemma 30.5.2](https://stacks.math.columbia.edu/tag/02KH), flat base change.
* S. Bosch, W. Lütkebohmert, M. Raynaud, *Néron Models*, Section 8.1.
-/

public section

open CategoryTheory Limits TopologicalSpace Opposite

namespace AlgebraicGeometry

universe u

/-- A morphism of schemes `p : Y ⟶ X` induces isomorphisms `Γ(X, U) ≅ Γ(Y, p⁻¹ U)` for all opens
`U` once it does so for the opens of a basis of `X`. -/
theorem Scheme.Hom.isIso_app_of_isBasis {X Y : Scheme.{u}} (p : Y ⟶ X) {ι : Type*}
    {B : ι → X.Opens} (hB : Opens.IsBasis (Set.range B)) (h : ∀ i, IsIso (p.app (B i)))
    (U : X.Opens) : IsIso (p.app U) := by
  let φ : X.sheaf ⟶ (TopCat.Sheaf.pushforward _ p.base).obj Y.sheaf := ObjectProperty.homMk p.c
  have : IsIso φ := TopCat.Sheaf.isIso_iff_isIso_basis hB h
  have : IsIso ((TopCat.Sheaf.forget _ _).map φ) := Functor.map_isIso _ _
  exact NatIso.isIso_app_of_isIso ((TopCat.Sheaf.forget _ _).map φ) (op U)

/-- A morphism of schemes into a scheme with at most one point induces isomorphisms on the
sections over all opens once it induces one on global sections. -/
theorem Scheme.Hom.isIso_app_of_isIso_appTop {X Y : Scheme.{u}} [Subsingleton X] (p : Y ⟶ X)
    [IsIso p.appTop] (U : X.Opens) : IsIso (p.app U) := by
  refine p.isIso_app_of_isBasis (B := fun _ : Unit ↦ ⊤) ?_ (fun _ ↦ ‹_›) U
  refine Opens.isBasis_iff_nbhd.mpr fun {V x} hx ↦ ⟨⊤, ⟨(), rfl⟩, trivial, fun y _ ↦ ?_⟩
  rwa [Subsingleton.elim y x]

/-- A morphism from a quasi-compact quasi-separated scheme to an affine scheme which induces an
isomorphism on global sections induces isomorphisms on the sections over all opens: `f_* 𝒪_X = 𝒪_Y`.
For instance this applies to `X ⟶ Spec Γ(X, ⊤)`. -/
theorem Scheme.Hom.isIso_app_of_isIso_appTop_of_isAffine {X Y : Scheme.{u}} [IsAffine Y]
    [CompactSpace X] [QuasiSeparatedSpace X] (f : X ⟶ Y) [IsIso f.appTop] (U : Y.Opens) :
    IsIso (f.app U) := by
  refine f.isIso_app_of_isBasis (B := Y.basicOpen) (isBasis_basicOpen Y) (fun r ↦ ?_) U
  -- Over `D(r)` both rings of sections are localizations away from `r`, by the qcqs lemma.
  have := isLocalization_basicOpen_of_qcqs (X := Y) isCompact_univ isQuasiSeparated_univ r
  have := isLocalization_basicOpen_of_qcqs (X := X) isCompact_univ isQuasiSeparated_univ
    (f.appTop r)
  have e := Scheme.preimage_basicOpen_top f r
  -- This square is the one in the proof of Mathlib's `Scheme.isPullback_toSpecΓ_toSpecΓ`.
  have hpush : IsPushout f.appTop (Y.presheaf.map (homOfLE le_top).op)
      (X.presheaf.map (homOfLE le_top).op) (f.appLE (Y.basicOpen r) (X.basicOpen (f.appTop r))
        e.ge) := by
    refine CommRingCat.isPushout_of_isLocalization f.appTop.hom
      (f.appLE (Y.basicOpen r) (X.basicOpen (f.appTop r)) e.ge).hom ?_ (.powers r)
    -- The algebra maps of the two localizations are restrictions of sections; `change` exposes
    -- the compatibility as an equation of composites in `CommRingCat`, which is the naturality
    -- of `appLE`. The final `rfl` unfolds the abbreviation `appTop = app ⊤`.
    change CommRingCat.Hom.hom (Y.presheaf.map _ ≫ f.appLE _ _ _) =
      CommRingCat.Hom.hom (f.appTop ≫ X.presheaf.map _)
    rw [f.map_appLE, Scheme.Hom.appLE]
    rfl
  have happLE := hpush.isIso_inr_of_isIso
  -- The basic open `X_{f^* r}` is the preimage of `D(r)`, so `appLE` is `app` followed by an
  -- isomorphism.
  have : IsIso (X.presheaf.map (homOfLE e.ge).op) := by
    have : IsIso (homOfLE e.ge) := ⟨homOfLE e.le, Subsingleton.elim _ _, Subsingleton.elim _ _⟩
    infer_instance
  rw [Scheme.Hom.appLE] at happLE
  exact IsIso.of_isIso_comp_right _ (X.presheaf.map (homOfLE e.ge).op)

end AlgebraicGeometry

namespace TauCeti

namespace AlgebraicGeometry

open _root_.AlgebraicGeometry

universe u

variable {S X T : Scheme.{u}} (f : X ⟶ S) (g : T ⟶ S)

/-- **Flat base change for `f_* 𝒪_X = 𝒪_S`.** If `f : X ⟶ S` is quasi-compact and
quasi-separated and induces isomorphisms `Γ(S, V) ≅ Γ(X, f⁻¹ V)` for all affine opens `V`, then
for every flat `g : T ⟶ S` the projection `T ×_S X ⟶ T` induces isomorphisms on the sections over
all opens of `T`. -/
theorem isIso_app_pullback_fst_of_flat [QuasiCompact f] [QuasiSeparated f] [Flat g]
    (hf : ∀ V : S.affineOpens, IsIso (f.app V)) (U : T.Opens) :
    IsIso ((pullback.fst g f).app U) := by
  -- The affine opens of `T` lying over an affine open of `S` form a basis of `T`.
  let ι := {UV : T.affineOpens × S.affineOpens // (UV.1 : T.Opens) ≤ g ⁻¹ᵁ UV.2}
  refine (pullback.fst g f).isIso_app_of_isBasis (B := fun i : ι ↦ i.val.1)
    g.isBasis_range_affineOpens_le_preimage (fun i ↦ ?_) U
  · obtain ⟨⟨⟨U', hU'⟩, ⟨V, hV⟩⟩, hUV⟩ := i
    -- Over `U'` the sections of the fibre product are `Γ(X, f⁻¹ V) ⊗_{Γ(S, V)} Γ(T, U')`.
    have H := (IsPullback.of_hasPullback g f).flip
    have hUY : pullback.fst g f ⁻¹ᵁ U' =
        pullback.snd g f ⁻¹ᵁ (f ⁻¹ᵁ V) ⊓ pullback.fst g f ⁻¹ᵁ U' := by
      refine (inf_eq_right.mpr ?_).symm
      rw [← Scheme.Hom.comp_preimage, ← pullback.condition, Scheme.Hom.comp_preimage]
      exact (pullback.fst g f).preimage_mono hUV
    have := isIso_pushoutSection_of_isQuasiSeparated_of_flat_right H hUV le_rfl hUY hV hU'
      (f.isCompact_preimage hV.isCompact) (f.isQuasiSeparated_preimage hV.isQuasiSeparated)
    have hpush := (isIso_pushoutSection_iff H hUV le_rfl hUY).mp this
    have : IsIso (f.appLE V (f ⁻¹ᵁ V) le_rfl) := by
      rw [Scheme.Hom.appLE_eq_app]
      exact hf ⟨V, hV⟩
    have := hpush.isIso_inr_of_isIso
    rwa [Scheme.Hom.appLE_eq_app] at this

/-- **Flat base change for `f_* 𝒪_X = 𝒪_S`, second projection.** If `f : X ⟶ S` is quasi-compact
and quasi-separated and induces isomorphisms `Γ(S, V) ≅ Γ(X, f⁻¹ V)` on all affine opens `V` of
`S`, then for every flat `g : T ⟶ S` the second projection `X ×_S T ⟶ T` induces isomorphisms on
the sections over all opens of `T`. -/
theorem isIso_app_pullback_snd_of_flat [QuasiCompact f] [QuasiSeparated f] [Flat g]
    (hf : ∀ V : S.affineOpens, IsIso (f.app V)) (U : T.Opens) :
    IsIso ((pullback.snd f g).app U) := by
  have hsymm : pullback.snd f g = (pullbackSymmetry f g).hom ≫ pullback.fst g f := by simp
  rw [hsymm, Scheme.Hom.comp_app]
  exact (isIso_app_pullback_fst_of_flat f g hf U).comp_isIso'
    ((pullbackSymmetry f g).hom.isIso_app _ fun x _ ↦ ⟨(pullbackSymmetry f g).inv x, by simp⟩)

/-- **Flat base change for `Γ(Y, 𝒪) = Γ(X, 𝒪)`.** Let `f : X ⟶ Y` be a morphism from a
quasi-compact quasi-separated scheme to an affine scheme which induces an isomorphism on global
sections, for instance `X ⟶ Spec Γ(X, ⊤)`. Then every base change of `f` along a flat morphism
`g : T ⟶ Y` again induces an isomorphism on global sections. -/
theorem isIso_appTop_of_isPullback_of_flat {P Y : Scheme.{u}} {f : X ⟶ Y} {g : T ⟶ Y}
    {f' : P ⟶ T} {g' : P ⟶ X} (H : IsPullback g' f' f g) [IsAffine Y] [CompactSpace X]
    [QuasiSeparatedSpace X] [Flat g] [IsIso f.appTop] : IsIso f'.appTop := by
  have h₁ := isIso_app_pullback_snd_of_flat f g
    (fun V ↦ f.isIso_app_of_isIso_appTop_of_isAffine V) ⊤
  have h₂ : IsIso H.isoPullback.hom.appTop := inferInstanceAs (IsIso (H.isoPullback.hom.app ⊤))
  rw [← H.isoPullback_hom_snd, Scheme.Hom.comp_appTop]
  exact h₁.comp_isIso' h₂

variable {K : Type u} [Field K]

/-- **`f_* 𝒪_X = 𝒪` universally over a field.** If `X` is quasi-compact and quasi-separated over a
field `K` and its global functions are the constants, then for every scheme `T` over `K` the
projection `T ×_K X ⟶ T` induces isomorphisms on the sections over all opens of `T`. -/
theorem isIso_app_pullback_fst_of_isIso_appTop (f : X ⟶ Spec (.of K)) [QuasiCompact f]
    [QuasiSeparated f] [IsIso f.appTop] (g : T ⟶ Spec (.of K)) (U : T.Opens) :
    IsIso ((pullback.fst g f).app U) :=
  isIso_app_pullback_fst_of_flat f g (fun V ↦ f.isIso_app_of_isIso_appTop V) U

/-- **`f_* 𝒪_X = 𝒪` universally for a proper integral scheme with a rational point.** If `X` is
integral, universally closed and quasi-separated over a field `K` (for instance proper) and has a
`K`-rational point, then for every scheme `T` over `K` the projection `T ×_K X ⟶ T` induces
isomorphisms on the sections over all opens of `T`. -/
theorem isIso_app_pullback_fst_of_section (f : X ⟶ Spec (.of K)) [IsIntegral X]
    [UniversallyClosed f] [QuasiSeparated f] {s : Spec (.of K) ⟶ X}
    (hs : s ≫ f = 𝟙 (Spec (.of K))) (g : T ⟶ Spec (.of K)) (U : T.Opens) :
    IsIso ((pullback.fst g f).app U) :=
  have : IsIso f.appTop :=
    (ConcreteCategory.isIso_iff_bijective _).mpr (appTop_bijective_of_section hs)
  isIso_app_pullback_fst_of_isIso_appTop f g U

/-- **Regular functions on a base change are constant along the fibres.** Let `X` be quasi-compact
and quasi-separated over a field `K` with constant global functions, and `T` a scheme over `K`.
A regular function `φ` on `X ×_K T` takes equal values at any two points `u`, `v` of `X ×_K T`
with the same image in `T`: their pullbacks `u^*φ` and `v^*φ` agree. -/
theorem appTop_eq_of_comp_snd_eq {Y : Scheme.{u}} (f : X ⟶ Spec (.of K)) [QuasiCompact f]
    [QuasiSeparated f] [IsIso f.appTop] (g : T ⟶ Spec (.of K)) {u v : Y ⟶ pullback f g}
    (h : u ≫ pullback.snd f g = v ≫ pullback.snd f g) (φ : Γ(pullback f g, ⊤)) :
    u.appTop φ = v.appTop φ := by
  have : IsIso (pullback.snd f g).appTop :=
    isIso_app_pullback_snd_of_flat f g (fun V ↦ f.isIso_app_of_isIso_appTop V) ⊤
  -- `φ` is the pullback of a function `c` on `T`, and `u^*φ = (u ≫ pr₂)^*c = (v ≫ pr₂)^*c`.
  obtain ⟨c, rfl⟩ := (ConcreteCategory.bijective_of_isIso (pullback.snd f g).appTop).2 φ
  have hc := congrArg (fun w : Y ⟶ T ↦ w.appTop c) h
  simpa only [Scheme.Hom.comp_appTop, CommRingCat.comp_apply] using hc

end AlgebraicGeometry

end TauCeti

namespace AlgebraicGeometry.Scheme.Hom

universe u

variable {K : Type u} [Field K] {X T : Scheme.{u}}

/-- A universally closed geometrically integral morphism `f : X ⟶ Spec K` over a field `K` induces
isomorphisms `Γ(Spec K, V) ≅ Γ(X, f⁻¹ V)` on the sections over all opens `V` of `Spec K`, without
requiring quasi-separatedness or a `K`-rational point of `X`. -/
theorem isIso_app_of_universallyClosed_of_geometricallyIntegral
    (f : X ⟶ Spec (.of K)) [UniversallyClosed f] [GeometricallyIntegral f]
    (V : (Spec (.of K)).Opens) :
    IsIso (f.app V) := by
  let _ : X.Over (Spec (.of K)) := ⟨f⟩
  have : UniversallyClosed (X ↘ Spec (.of K)) := inferInstanceAs (UniversallyClosed f)
  have : GeometricallyIntegral (X ↘ Spec (.of K)) := inferInstanceAs (GeometricallyIntegral f)
  have h : Function.Bijective (⇑(ConcreteCategory.hom f.appTop) ∘
      ⇑(ConcreteCategory.hom (Scheme.ΓSpecIso (.of K)).inv)) := by
    convert X.baseRingToGlobalSections_bijective_of_geometricallyIntegral K using 1
    ext c
    exact (Modules.baseRingToGlobalSections_apply K X c).symm
  have : IsIso f.appTop := (ConcreteCategory.isIso_iff_bijective _).mpr
    ((Function.Bijective.of_comp_iff _
      (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of K)).inv)).mp h)
  exact f.isIso_app_of_isIso_appTop V

/-- **Universal structure-sheaf equality for geometrically reduced connected schemes.** A
universally closed quasi-separated geometrically reduced and geometrically connected scheme over
a field satisfies `p_* 𝒪 = 𝒪` after base change by any scheme over that field. In particular the
scheme is allowed to be reducible, and it need not have a rational point. -/
theorem isIso_app_pullback_fst_of_geometricallyReduced_of_geometricallyConnected
    (f : X ⟶ Spec (.of K)) [UniversallyClosed f] [QuasiSeparated f]
    [GeometricallyReduced f] [GeometricallyConnected f]
    (g : T ⟶ Spec (.of K)) (U : T.Opens) :
    IsIso ((pullback.fst g f).app U) := by
  let _ : X.Over (Spec (.of K)) := ⟨f⟩
  have : UniversallyClosed (X ↘ Spec (.of K)) := inferInstanceAs (UniversallyClosed f)
  have : QuasiSeparated (X ↘ Spec (.of K)) := inferInstanceAs (QuasiSeparated f)
  have : GeometricallyReduced (X ↘ Spec (.of K)) := inferInstanceAs (GeometricallyReduced f)
  have : GeometricallyConnected (X ↘ Spec (.of K)) := inferInstanceAs (GeometricallyConnected f)
  have : IsIso f.appTop := (ConcreteCategory.isIso_iff_bijective _).mpr
    (X.appTop_bijective_of_geometricallyReduced_of_geometricallyConnected K)
  exact TauCeti.AlgebraicGeometry.isIso_app_pullback_fst_of_isIso_appTop f g U

end AlgebraicGeometry.Scheme.Hom

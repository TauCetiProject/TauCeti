/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import TauCeti.AlgebraicGeometry.RationalPoint.Basic

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

Over a field every base change is flat, so a quasi-compact quasi-separated scheme `X` over a field
`K` with `Γ(X, 𝒪_X) = K` satisfies `p_* 𝒪_{X_T} = 𝒪_T` for *every* scheme `T` over `K`. This holds
for a proper (more generally, universally closed and quasi-separated) integral scheme with a
`K`-rational point, whose global functions are constant
(`TauCeti.AlgebraicGeometry.appTop_bijective_of_section`). It is the hypothesis "`f_* 𝒪_X = 𝒪`
universally" under which line bundles rigidified along a section of `X` have no automorphisms
other than the identity, after every base change.

## Main results

* `AlgebraicGeometry.Scheme.Hom.isIso_app_of_isBasis`: a morphism of schemes induces
  isomorphisms on the sections over all opens once it does so over a basis of opens.
* `TauCeti.AlgebraicGeometry.isIso_app_pullback_fst_of_flat`: `f_* 𝒪_X = 𝒪_S` is stable under
  flat base change for quasi-compact quasi-separated `f`.
* `TauCeti.AlgebraicGeometry.isIso_app_pullback_fst_of_isIso_appTop`: over a field, a
  quasi-compact quasi-separated scheme with constant global functions satisfies
  `p_* 𝒪_{X_T} = 𝒪_T` after every base change.
* `TauCeti.AlgebraicGeometry.isIso_app_pullback_fst_of_section`: the same for a universally
  closed quasi-separated integral scheme with a rational point, such as a proper one.

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
  refine (pullback.fst g f).isIso_app_of_isBasis (B := fun i : ι ↦ i.1.1) ?_ (fun i ↦ ?_) U
  · refine Opens.isBasis_iff_nbhd.mpr fun {W x} hx ↦ ?_
    obtain ⟨_, ⟨V, hV, rfl⟩, hxV, -⟩ :=
      S.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (g x)) isOpen_univ
    obtain ⟨_, ⟨U', hU', rfl⟩, hxU', hU'W⟩ :=
      T.isBasis_affineOpens.exists_subset_of_mem_open (⟨hx, hxV⟩ : x ∈ W ⊓ g ⁻¹ᵁ V)
        (W ⊓ g ⁻¹ᵁ V).isOpen
    exact ⟨U', ⟨⟨(⟨U', hU'⟩, ⟨V, hV⟩), fun y hy ↦ (hU'W hy).2⟩, rfl⟩, hxU',
      fun y hy ↦ (hU'W hy).1⟩
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

end AlgebraicGeometry

end TauCeti

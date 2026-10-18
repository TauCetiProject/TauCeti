/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.ExteriorPower
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Category.ModuleCat.EpiMono

/-!
# Exterior powers and restriction of scalars

Restriction of scalars has a natural exterior-power comparison, sending a wedge over the
source ring to the same wedge over the target ring. It is an isomorphism when the coefficient
map is bijective, though not for an arbitrary ring map. This gives exterior-power restriction
isomorphisms for module presheaves and sheaves. The construction uses Mathlib's
`ModuleCat.exteriorPower.desc` and supplies the sectionwise maps
for exterior powers of pushforwards of module presheaves.
-/

public section

open CategoryTheory

namespace TauCeti.ModuleCat

universe u v w

noncomputable section

variable {S : Type u} {R : Type v} [CommRing S] [CommRing R] (f : S →+* R)

private def restrictScalarsExteriorPowerApp (n : ℕ) (M : ModuleCat.{max u v w} R) :
    ((ModuleCat.restrictScalars f).obj M).exteriorPower n ⟶
      (ModuleCat.restrictScalars f).obj (M.exteriorPower n) :=
  ModuleCat.exteriorPower.desc
    { toFun m := ModuleCat.exteriorPower.mk (M := M) m
      map_update_add' m i a b :=
        (ModuleCat.exteriorPower.mk (M := M)).map_update_add m i a b
      map_update_smul' m i r a :=
        (ModuleCat.exteriorPower.mk (M := M)).map_update_smul m i (f r) a
      map_eq_zero_of_eq' m _ _ h hij :=
        (ModuleCat.exteriorPower.mk (M := M)).map_eq_zero_of_eq m h hij }

private lemma restrictScalarsExteriorPowerApp_mk (n : ℕ)
    (M : ModuleCat.{max u v w} R) (m : Fin n → (ModuleCat.restrictScalars f).obj M) :
    restrictScalarsExteriorPowerApp f n M (ModuleCat.exteriorPower.mk m) =
      ModuleCat.exteriorPower.mk (M := M) m :=
  ModuleCat.exteriorPower.desc_mk _ _

/-- Restriction of scalars carries the natural exterior-power comparison, changing the
coefficient ring of a wedge without changing its factors. -/
def restrictScalarsExteriorPowerComparison (n : ℕ) :
    ModuleCat.restrictScalars.{max u v w} f ⋙ ModuleCat.exteriorPower.functor S n ⟶
      ModuleCat.exteriorPower.functor R n ⋙ ModuleCat.restrictScalars f where
  app := restrictScalarsExteriorPowerApp f n
  naturality {M N} φ := by
    dsimp only [Functor.comp_obj, Functor.comp_map, ModuleCat.exteriorPower.functor]
    apply ModuleCat.exteriorPower.hom_ext
    apply ModuleCat.AlternatingMap.ext
    intro m
    simp only [ModuleCat.AlternatingMap.postcomp_apply, ModuleCat.comp_apply,
      ModuleCat.restrictScalars.map_apply, ModuleCat.exteriorPower.map_mk,
      restrictScalarsExteriorPowerApp_mk, Function.comp_def]
    -- Restriction of scalars gives the concrete-category coercions different bundled objects
    -- with the same carriers, preventing `simp` from matching these two wedge formulas.
    exact (restrictScalarsExteriorPowerApp_mk f n N (φ ∘ m)).trans
      (ModuleCat.exteriorPower.map_mk φ m).symm

/-- The restriction-of-scalars comparison preserves the factors of a decomposable wedge. -/
-- Explicit objects keep the coercion to a function in simp normal form.
@[simp]
theorem restrictScalarsExteriorPowerComparison_app_mk (n : ℕ)
    (M : ModuleCat.{max u v w} R) (m : Fin n → (ModuleCat.restrictScalars f).obj M) :
    (ConcreteCategory.hom
      (X := (ModuleCat.exteriorPower.functor S n).obj ((ModuleCat.restrictScalars f).obj M))
      (Y := (ModuleCat.restrictScalars f).obj ((ModuleCat.exteriorPower.functor R n).obj M))
      ((restrictScalarsExteriorPowerComparison f n).app M))
      (ModuleCat.exteriorPower.mk m) = ModuleCat.exteriorPower.mk (M := M) m :=
  restrictScalarsExteriorPowerApp_mk f n M m

-- The reverse wedge map, with the target action transported by the inverse ring map.
private def restrictScalarsExteriorPowerInvAux (e : S ≃+* R) (n : ℕ)
    (M : ModuleCat.{max u v w} R) :
    M.exteriorPower n ⟶ (ModuleCat.restrictScalars e.symm.toRingHom).obj
      (((ModuleCat.restrictScalars e.toRingHom).obj M).exteriorPower n) := by
  let N := (ModuleCat.restrictScalars e.toRingHom).obj M
  let P := (ModuleCat.restrictScalars e.symm.toRingHom).obj (N.exteriorPower n)
  let a : M.AlternatingMap P n :=
    { toFun m := ModuleCat.exteriorPower.mk (M := N) m
      map_update_add' m i a b := (ModuleCat.exteriorPower.mk (M := N)).map_update_add m i a b
      map_update_smul' m i r a := by
        -- The action of `e.symm r` on `N` is the original action of `r` on `M`.
        have hr : e (e.symm r) = r := e.apply_symm_apply r
        have hw := (ModuleCat.exteriorPower.mk (M := N)).map_update_smul m i (e.symm r) a
        -- Expose only the transported action on each wedge factor, not on the exterior power.
        change ModuleCat.exteriorPower.mk (M := N) (Function.update m i (e (e.symm r) • a)) =
          e.symm r • ModuleCat.exteriorPower.mk (M := N) (Function.update m i a) at hw
        rw [hr] at hw
        exact hw
      map_eq_zero_of_eq' m _ _ h hij :=
        (ModuleCat.exteriorPower.mk (M := N)).map_eq_zero_of_eq m h hij }
  exact ModuleCat.exteriorPower.desc a

private lemma restrictScalarsExteriorPowerInvAux_mk (e : S ≃+* R) (n : ℕ)
    (M : ModuleCat.{max u v w} R) (m : Fin n → M) :
    restrictScalarsExteriorPowerInvAux e n M (ModuleCat.exteriorPower.mk m) =
      ModuleCat.exteriorPower.mk (M := (ModuleCat.restrictScalars e.toRingHom).obj M) m :=
  ModuleCat.exteriorPower.desc_mk _ m

private def restrictScalarsExteriorPowerInv (e : S ≃+* R) (n : ℕ)
    (M : ModuleCat.{max u v w} R) :
    (ModuleCat.restrictScalars e.toRingHom).obj (M.exteriorPower n) ⟶
      ((ModuleCat.restrictScalars e.toRingHom).obj M).exteriorPower n :=
  (ModuleCat.restrictScalars e.toRingHom).map (restrictScalarsExteriorPowerInvAux e n M) ≫
    (ModuleCat.restrictScalarsEquivalenceOfRingEquiv e).counitIso.hom.app _

private lemma restrictScalarsExteriorPowerInv_mk (e : S ≃+* R) (n : ℕ)
    (M : ModuleCat.{max u v w} R) (m : Fin n → M) :
    restrictScalarsExteriorPowerInv e n M (ModuleCat.exteriorPower.mk m) =
      ModuleCat.exteriorPower.mk (M := (ModuleCat.restrictScalars e.toRingHom).obj M) m :=
  restrictScalarsExteriorPowerInvAux_mk e n M m

private lemma restrictScalarsExteriorPowerComparison_comp_inv
    (e : S ≃+* R) (n : ℕ) (M : ModuleCat.{max u v w} R) :
    (restrictScalarsExteriorPowerComparison e.toRingHom n).app M ≫
      restrictScalarsExteriorPowerInv e n M = 𝟙 _ := by
  apply ModuleCat.hom_ext
  apply _root_.exteriorPower.linearMap_ext
  apply _root_.AlternatingMap.ext
  intro m
  exact (congrArg (restrictScalarsExteriorPowerInv e n M)
    (restrictScalarsExteriorPowerComparison_app_mk e.toRingHom n M m)).trans
      (restrictScalarsExteriorPowerInv_mk e n M m)

private lemma restrictScalarsExteriorPowerComparison_inv_apply
    (e : S ≃+* R) (n : ℕ) (M : ModuleCat.{max u v w} R) (x : M.exteriorPower n) :
    ((restrictScalarsExteriorPowerComparison e.toRingHom n).app M)
      (restrictScalarsExteriorPowerInvAux e n M x) = x := by
  let N := (ModuleCat.restrictScalars e.toRingHom).obj M
  let P := (ModuleCat.restrictScalars e.symm.toRingHom).obj (N.exteriorPower n)
  let h : M.exteriorPower n ⟶ P := restrictScalarsExteriorPowerInvAux e n M
  have hh (m : Fin n → M) : h (ModuleCat.exteriorPower.mk m) =
      ModuleCat.exteriorPower.mk (M := N) m := restrictScalarsExteriorPowerInvAux_mk e n M m
  let c : N.exteriorPower n ⟶ (ModuleCat.restrictScalars e.toRingHom).obj (M.exteriorPower n) :=
    (restrictScalarsExteriorPowerComparison e.toRingHom n).app M
  let c' : P ⟶ M.exteriorPower n :=
    (ModuleCat.restrictScalars e.symm.toRingHom).map c ≫
      (ModuleCat.restrictScalarsEquivalenceOfRingEquiv e).unitIso.inv.app _
  have hc (m : Fin n → M) : c (ModuleCat.exteriorPower.mk (M := N) m) =
      ModuleCat.exteriorPower.mk (M := M) m :=
    restrictScalarsExteriorPowerComparison_app_mk e.toRingHom n M m
  have hc' (x : P) : c' x = c x := rfl
  have hright : h ≫ c' = 𝟙 _ := by
    apply ModuleCat.hom_ext
    apply _root_.exteriorPower.linearMap_ext
    apply _root_.AlternatingMap.ext
    intro m
    exact (congrArg c' (hh m)).trans
      ((hc' (ModuleCat.exteriorPower.mk (M := N) m)).trans (hc m))
  exact (hc' (h x)).symm.trans (ConcreteCategory.congr_hom hright x)

private lemma restrictScalarsExteriorPowerComparison_injective
    (e : S ≃+* R) (n : ℕ) (M : ModuleCat.{max u v w} R) :
    Function.Injective ((restrictScalarsExteriorPowerComparison e.toRingHom n).app M) := by
  let N := (ModuleCat.restrictScalars e.toRingHom).obj M
  let c : N.exteriorPower n ⟶ (ModuleCat.restrictScalars e.toRingHom).obj (M.exteriorPower n) :=
    (restrictScalarsExteriorPowerComparison e.toRingHom n).app M
  have hleft : c ≫ restrictScalarsExteriorPowerInv e n M = 𝟙 (N.exteriorPower n) :=
    restrictScalarsExteriorPowerComparison_comp_inv e n M
  have : Mono c := mono_of_mono_fac hleft
  exact (ModuleCat.mono_iff_injective c).mp inferInstance

private lemma restrictScalarsExteriorPowerComparison_surjective
    (e : S ≃+* R) (n : ℕ) (M : ModuleCat.{max u v w} R) :
    Function.Surjective ((restrictScalarsExteriorPowerComparison e.toRingHom n).app M) :=
  fun x ↦ ⟨restrictScalarsExteriorPowerInvAux e n M x,
    restrictScalarsExteriorPowerComparison_inv_apply e n M x⟩

/-- Restriction along an isomorphism of coefficient rings preserves exterior powers. -/
theorem isIso_restrictScalarsExteriorPowerComparison_app_of_bijective
    (hf : Function.Bijective f) (n : ℕ) (M : ModuleCat.{max u v w} R) :
    IsIso ((restrictScalarsExteriorPowerComparison f n).app M) :=
  (ConcreteCategory.isIso_iff_bijective _).mpr
    ⟨restrictScalarsExteriorPowerComparison_injective (RingEquiv.ofBijective f hf) n M,
      restrictScalarsExteriorPowerComparison_surjective (RingEquiv.ofBijective f hf) n M⟩

end

end TauCeti.ModuleCat

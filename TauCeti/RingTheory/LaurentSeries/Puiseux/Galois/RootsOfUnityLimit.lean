/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.LaurentSeries.Puiseux.Galois.Limit
public import TauCeti.RingTheory.RootsOfUnity.TateModule.Limit

/-!
# The Galois limit as the profinite limit of roots of unity

The finite ramified levels of the Puiseux field are cofinal among its finite Galois
intermediate fields. Their Kummer coordinates therefore identify Mathlib's Galois-limit
object with the inverse limit of the finite discrete groups of roots of unity.

This file supplies the categorical comparison in `ProfiniteGrp`. The cone has Mathlib's
Galois limit as its vertex; its leg at `n` is restriction to level `n` followed by the
Kummer character. It is a limit cone, so every compatible family of continuous maps to
these discrete root groups factors uniquely through the Galois limit. The resulting
isomorphism to the explicit roots-of-unity limit is characterized by these same legs.

The proof reuses the cofinal-level comparison `limitEquivTateModule` and the universal
property `PrimeToPTateModule.rootsOfUnityConeIsLimit`; no choice of primitive roots,
algebraic closedness, or topology on the coefficient field is needed.
-/

public section

noncomputable section

open CategoryTheory CategoryTheory.Limits IntermediateField InfiniteGalois Opposite
open scoped LaurentSeries

namespace TauCeti.puiseuxField

variable (K : Type*) [Field K] [∀ n : ℕ+, HasEnoughRootsOfUnity K n]

/-- The cone of Kummer characters on Mathlib's Galois limit, with finite discrete
root-of-unity groups as its targets. -/
-- Expose the vertex: the projection and universal-property statements use Mathlib's
-- concrete Galois-limit carrier.
@[expose]
def galoisRootsOfUnityCone : Cone (PrimeToPTateModule.rootsOfUnityDiagram 1 K) :=
  (PrimeToPTateModule.rootsOfUnityCone 1 K).extend
    (ProfiniteGrp.ContinuousMulEquiv.toProfiniteGrpIso (limitEquivTateModule K)).hom

/-- The cone vertex is Mathlib's limit over all finite Galois intermediate fields. -/
@[simp]
theorem galoisRootsOfUnityCone_pt :
    (galoisRootsOfUnityCone K).pt =
      ProfiniteGrp.limit (asProfiniteGaloisGroupFunctor K⸨X⸩ (puiseuxField K)) := (rfl)

/-- The cone legs are the Tate-module projections after the cofinal-level comparison. -/
@[simp]
theorem galoisRootsOfUnityCone_π_app_eq_proj (n : (PrimeToPTateModule.Index 1)ᵒᵖ)
    (g : ProfiniteGrp.limit (asProfiniteGaloisGroupFunctor K⸨X⸩ (puiseuxField K))) :
    dsimp% only [Functor.comp_obj, Functor.const_obj_obj]
    ((galoisRootsOfUnityCone K).π.app n).hom g =
      PrimeToPTateModule.proj n.unop.order (limitEquivTateModule K g) := (rfl)

/-- Each cone leg is the Kummer character of the corresponding finite-level component. -/
@[simp]
theorem galoisRootsOfUnityCone_π_app_apply (n : ℕ+)
    (g : (galoisRootsOfUnityCone K).pt) :
    dsimp% only [Functor.comp_obj, Functor.const_obj_obj]
    ((galoisRootsOfUnityCone K).π.app (op ⟨⟨n, n.ne_zero, Nat.coprime_one_right _⟩⟩)).hom g =
      levelGalEquivRootsOfUnity K n (proj (levelFiniteGalois K n) g) := by
  exact (galoisRootsOfUnityCone_π_app_eq_proj K _ g).trans (proj_limitEquivTateModule g n)

/-- Restricting a Galois automorphism and then taking Kummer coordinates gives the
legs of the roots-of-unity cone. -/
theorem galoisRootsOfUnityCone_π_continuousMulEquivToLimit (n : ℕ+)
    (σ : Gal(puiseuxField K/K⸨X⸩)) :
    ((galoisRootsOfUnityCone K).π.app (op ⟨⟨n, n.ne_zero, Nat.coprime_one_right _⟩⟩)).hom
        (continuousMulEquivToLimit K⸨X⸩ (puiseuxField K) σ) =
      levelGalEquivRootsOfUnity K n (AlgEquiv.restrictNormalHom (level K n) σ) := by
  exact (galoisRootsOfUnityCone_π_app_eq_proj K _ _).trans
    ((congrArg (PrimeToPTateModule.proj _) <|
      limitEquivTateModule_continuousMulEquivToLimit σ).trans (proj_galEquivTateModule σ n))

/-- Mathlib's Galois limit is the inverse limit of the finite discrete root groups:
every compatible cone of continuous homomorphisms factors uniquely through its
finite-level Kummer characters. -/
def galoisRootsOfUnityConeIsLimit : IsLimit (galoisRootsOfUnityCone K) := by
  unfold galoisRootsOfUnityCone
  exact IsLimit.extendIso _ (PrimeToPTateModule.rootsOfUnityConeIsLimit 1 K)

/-- The categorical cofinal-limit comparison from all finite Galois intermediate
fields to the finite discrete groups of roots of unity. -/
def galoisLimitRootsOfUnityIso :
    ProfiniteGrp.limit (asProfiniteGaloisGroupFunctor K⸨X⸩ (puiseuxField K)) ≅
      ProfiniteGrp.limit (PrimeToPTateModule.rootsOfUnityDiagram 1 K) :=
  (galoisRootsOfUnityConeIsLimit K).conePointUniqueUpToIso
    (ProfiniteGrp.limitConeIsLimit _)

/-- The comparison is characterized by restriction to the levels and their Kummer
characters. -/
@[simp]
theorem galoisLimitRootsOfUnityIso_hom_proj (n : ℕ+)
    (g : (galoisRootsOfUnityCone K).pt) :
    dsimp% only [Functor.comp_obj, Functor.const_obj_obj]
    ((galoisLimitRootsOfUnityIso K).hom.hom g).val
        (op ⟨⟨n, n.ne_zero, Nat.coprime_one_right _⟩⟩) =
      levelGalEquivRootsOfUnity K n (proj (levelFiniteGalois K n) g) := by
  have h := congrArg (fun f ↦ f.hom g)
    ((galoisRootsOfUnityConeIsLimit K).conePointUniqueUpToIso_hom_comp
      (ProfiniteGrp.limitConeIsLimit _) (op ⟨⟨n, n.ne_zero, Nat.coprime_one_right _⟩⟩))
  exact h.trans (galoisRootsOfUnityCone_π_app_apply K n g)

/-- The inverse comparison recovers the finite-level Kummer character from the
corresponding root-of-unity coordinate. -/
@[simp]
theorem galoisLimitRootsOfUnityIso_inv_proj (n : ℕ+)
    (x : ProfiniteGrp.limit (PrimeToPTateModule.rootsOfUnityDiagram 1 K)) :
    dsimp% only [Functor.comp_obj, Functor.const_obj_obj]
    levelGalEquivRootsOfUnity K n
        (proj (levelFiniteGalois K n) ((galoisLimitRootsOfUnityIso K).inv.hom x)) =
      x.val (op ⟨⟨n, n.ne_zero, Nat.coprime_one_right _⟩⟩) := by
  have h := congrArg (fun f ↦ f.hom x)
    ((galoisRootsOfUnityConeIsLimit K).conePointUniqueUpToIso_inv_comp
      (ProfiniteGrp.limitConeIsLimit _) (op ⟨⟨n, n.ne_zero, Nat.coprime_one_right _⟩⟩))
  exact (galoisRootsOfUnityCone_π_app_apply K n _).symm.trans h

end TauCeti.puiseuxField

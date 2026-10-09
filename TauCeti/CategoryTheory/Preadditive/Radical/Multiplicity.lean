/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Preadditive.Radical.Basic
public import TauCeti.CategoryTheory.Linear.Biproduct
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.LinearAlgebra.Quotient.Defs
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.LinearAlgebra.Quotient.Basic

/-!
# Krull–Schmidt multiplicities through the radical

In a linear category over a division ring `k`, the quotient `(X ⟶ Y) / rad(X, Y)` of a morphism
space by the radical is a `k`-vector space. When `Y` has a local endomorphism ring, the morphisms
outside the radical are exactly the split epimorphisms `X ⟶ Y`
(`TauCeti.mem_jacobsonRadical_iff_not_isSplitEpi`), so the quotient is nonzero exactly when `Y` is
a retract of `X`. This file proves the properties of its dimension which make it a coordinate on a
split Grothendieck group, detecting `Y` among indecomposable objects:

* it is additive in `X` on binary biproducts, when the two morphism spaces are finite-dimensional;
* it is invariant under isomorphisms of `X` and of `Y`;
* it vanishes when `X` and `Y` are non-isomorphic objects with local endomorphism rings;
* it is positive when `X = Y` has a local, finite-dimensional endomorphism ring;
* it is additive on finite biproducts in either argument, assuming finite-dimensional quotients;
* reversing the arguments preserves the dimension when one has a local endomorphism ring
  and the other has a finite decomposition into objects with local endomorphism rings.

These are the facts behind linear independence of the classes of pairwise non-isomorphic
indecomposable objects in a Krull–Schmidt category; no Krull–Schmidt decomposition of an arbitrary
object is needed to use them.

## Main results

* `TauCeti.finrank_quotient_jacobsonRadicalSubmodule_biprod`: additivity on binary biproducts in
  the source.
* `TauCeti.finrank_quotient_jacobsonRadicalSubmodule_congr`: invariance under isomorphisms.
* `TauCeti.finrank_quotient_jacobsonRadicalSubmodule_eq_zero`: vanishing between non-isomorphic
  objects with local endomorphism rings.
* `TauCeti.finrank_quotient_jacobsonRadicalSubmodule_self_pos`: positivity on an object with a
  local, finite-dimensional endomorphism ring.

## References

* M. Auslander, I. Reiten and S. O. Smalø, *Representation Theory of Artin Algebras*, Chapter V,
  Section 7, for the radical of a category.
* H. Krause, "Krull–Schmidt categories and projective covers", *Expositiones Mathematicae* **33**
  (2015), 535–549, for Krull–Schmidt categories and their radical.
-/

public section

namespace TauCeti

open CategoryTheory CategoryTheory.Limits

universe v u

variable {C : Type u} [Category.{v} C] [Preadditive C] (k : Type*) [DivisionRing k] [Linear k C]

/-- **Morphisms out of a biproduct, modulo the radical, split as a product**: the dimension of
`(X₁ ⊞ X₂ ⟶ Y) / rad` is the sum of the dimensions of `(X₁ ⟶ Y) / rad` and `(X₂ ⟶ Y) / rad`.
Restricting along the two inclusions is onto the product of the two quotients, and its kernel is
the radical, which is a two-sided ideal. -/
theorem finrank_quotient_jacobsonRadicalSubmodule_biprod (X₁ X₂ Y : C) [HasBinaryBiproduct X₁ X₂]
    [FiniteDimensional k (X₁ ⟶ Y)] [FiniteDimensional k (X₂ ⟶ Y)] :
    Module.finrank k ((X₁ ⊞ X₂ ⟶ Y) ⧸ jacobsonRadicalSubmodule k (X₁ ⊞ X₂) Y) =
      Module.finrank k ((X₁ ⟶ Y) ⧸ jacobsonRadicalSubmodule k X₁ Y) +
        Module.finrank k ((X₂ ⟶ Y) ⧸ jacobsonRadicalSubmodule k X₂ Y) := by
  let φ : (X₁ ⊞ X₂ ⟶ Y) →ₗ[k] ((X₁ ⟶ Y) ⧸ jacobsonRadicalSubmodule k X₁ Y) ×
      ((X₂ ⟶ Y) ⧸ jacobsonRadicalSubmodule k X₂ Y) :=
    ((jacobsonRadicalSubmodule k X₁ Y).mkQ ∘ₗ Linear.leftComp k Y biprod.inl).prod
      ((jacobsonRadicalSubmodule k X₂ Y).mkQ ∘ₗ Linear.leftComp k Y biprod.inr)
  have hφ : Function.Surjective φ := by
    rintro ⟨q₁, q₂⟩
    obtain ⟨a, rfl⟩ := (jacobsonRadicalSubmodule k X₁ Y).mkQ_surjective q₁
    obtain ⟨b, rfl⟩ := (jacobsonRadicalSubmodule k X₂ Y).mkQ_surjective q₂
    exact ⟨biprod.desc a b, by simp [φ]⟩
  have hker : LinearMap.ker φ = jacobsonRadicalSubmodule k (X₁ ⊞ X₂) Y := by
    ext f
    simp only [φ, LinearMap.ker_prod, Submodule.mem_inf, LinearMap.mem_ker, LinearMap.coe_comp,
      Function.comp_apply, Linear.leftComp_apply, Submodule.mkQ_apply,
      Submodule.Quotient.mk_eq_zero, mem_jacobsonRadicalSubmodule]
    refine ⟨fun ⟨h₁, h₂⟩ ↦ ?_, fun hf ↦
      ⟨comp_mem_jacobsonRadical_left _ hf, comp_mem_jacobsonRadical_left _ hf⟩⟩
    -- A morphism out of the biproduct is the sum of its restrictions, projected back.
    have hf : f = biprod.fst ≫ biprod.inl ≫ f + biprod.snd ≫ biprod.inr ≫ f := by
      rw [← Category.assoc, ← Category.assoc, ← Preadditive.add_comp, biprod.total,
        Category.id_comp]
    rw [hf]
    exact add_mem (comp_mem_jacobsonRadical_left _ h₁) (comp_mem_jacobsonRadical_left _ h₂)
  rw [← Module.finrank_prod]
  exact ((Submodule.quotEquivOfEq _ _ hker.symm).trans
    (φ.quotKerEquivOfSurjective hφ)).finrank_eq

/-- **The dimension modulo the radical is invariant under isomorphisms** of the source and of
the target, conjugation by the two isomorphisms carrying the radical onto the radical. -/
theorem finrank_quotient_jacobsonRadicalSubmodule_congr {X X' Y Y' : C} (e : X ≅ X')
    (e' : Y ≅ Y') :
    Module.finrank k ((X ⟶ Y) ⧸ jacobsonRadicalSubmodule k X Y) =
      Module.finrank k ((X' ⟶ Y') ⧸ jacobsonRadicalSubmodule k X' Y') :=
  (Submodule.Quotient.equiv _ _ (Linear.homCongr k e e')
    (jacobsonRadicalSubmodule_map_homCongr k e e')).finrank_eq

/-- **Between non-isomorphic objects with local endomorphism rings nothing survives modulo the
radical**: every morphism is radical (`TauCeti.jacobsonRadical_eq_top`). -/
theorem finrank_quotient_jacobsonRadicalSubmodule_eq_zero {X Y : C} [IsLocalRing (End X)]
    [IsLocalRing (End Y)] (h : IsEmpty (X ≅ Y)) :
    Module.finrank k ((X ⟶ Y) ⧸ jacobsonRadicalSubmodule k X Y) = 0 := by
  have htop : jacobsonRadicalSubmodule k X Y = ⊤ := by
    refine Submodule.eq_top_iff'.2 fun f ↦ ?_
    rw [mem_jacobsonRadicalSubmodule, jacobsonRadical_eq_top h]
    exact AddSubgroup.mem_top f
  have : Subsingleton ((X ⟶ Y) ⧸ jacobsonRadicalSubmodule k X Y) :=
    Submodule.Quotient.subsingleton_iff.2 htop
  exact Module.finrank_zero_of_subsingleton

/-- **An object with a local, finite-dimensional endomorphism ring survives modulo the radical**:
the identity is invertible, hence not radical, so `(X ⟶ X) / rad(X, X)` is nonzero. -/
theorem finrank_quotient_jacobsonRadicalSubmodule_self_pos (X : C) [IsLocalRing (End X)]
    [FiniteDimensional k (X ⟶ X)] :
    0 < Module.finrank k ((X ⟶ X) ⧸ jacobsonRadicalSubmodule k X X) := by
  refine Module.finrank_pos_iff_exists_ne_zero.2 ⟨Submodule.Quotient.mk (𝟙 X), ?_⟩
  rw [Ne, Submodule.Quotient.mk_eq_zero, mem_jacobsonRadicalSubmodule,
    mem_jacobsonRadical_iff_not_isIso, not_not]
  infer_instance

/-- Morphisms from a finite biproduct, modulo the radical, have dimension equal to the sum
of the corresponding dimensions for its summands. -/
theorem finrank_quotient_jacobsonRadicalSubmodule_biproduct {J : Type*} [Fintype J]
    (P : J → C) [HasBiproduct P] (Y : C)
    [∀ j, FiniteDimensional k ((P j ⟶ Y) ⧸ jacobsonRadicalSubmodule k (P j) Y)] :
    Module.finrank k ((⨁ P ⟶ Y) ⧸ jacobsonRadicalSubmodule k (⨁ P) Y) =
      ∑ j, Module.finrank k ((P j ⟶ Y) ⧸ jacobsonRadicalSubmodule k (P j) Y) := by
  classical
  let φ := (LinearMap.piMap fun j ↦ (jacobsonRadicalSubmodule k (P j) Y).mkQ) ∘ₗ
    (homBiproductLinearEquiv k P Y).toLinearMap
  have hsurj : Function.Surjective φ :=
    (Function.Surjective.piMap (fun j ↦
      (jacobsonRadicalSubmodule k (P j) Y).mkQ_surjective)).comp
      (homBiproductLinearEquiv k P Y).surjective
  have hker : LinearMap.ker φ = jacobsonRadicalSubmodule k (⨁ P) Y := by
    ext f
    simp only [LinearMap.mem_ker, φ, LinearMap.comp_apply, LinearEquiv.coe_toLinearMap,
      LinearMap.coe_piMap, Pi.map_apply, Submodule.mkQ_apply, funext_iff, Pi.zero_apply,
      Submodule.Quotient.mk_eq_zero, homBiproductLinearEquiv_apply,
      mem_jacobsonRadicalSubmodule]
    constructor
    · intro hf
      have heq : f = ∑ j, biproduct.π P j ≫ biproduct.ι P j ≫ f := by
        simp only [← Category.assoc, ← Preadditive.sum_comp, biproduct.total, Category.id_comp]
      rw [heq]
      exact (jacobsonRadical (⨁ P) Y).sum_mem fun j _ ↦
        comp_mem_jacobsonRadical_left _ (hf j)
    · intro hf j
      exact comp_mem_jacobsonRadical_left _ hf
  exact ((Submodule.quotEquivOfEq _ _ hker.symm).trans
    (φ.quotKerEquivOfSurjective hsurj)).finrank_eq.trans (Module.finrank_pi_fintype k)

/-- Morphisms into a finite biproduct, modulo the radical, have dimension equal to the sum
of the corresponding dimensions for its summands. -/
theorem finrank_quotient_jacobsonRadicalSubmodule_biproduct_right {J : Type*} [Fintype J]
    (P : J → C) [HasBiproduct P] (Y : C)
    [∀ j, FiniteDimensional k ((Y ⟶ P j) ⧸ jacobsonRadicalSubmodule k Y (P j))] :
    Module.finrank k ((Y ⟶ ⨁ P) ⧸ jacobsonRadicalSubmodule k Y (⨁ P)) =
      ∑ j, Module.finrank k ((Y ⟶ P j) ⧸ jacobsonRadicalSubmodule k Y (P j)) := by
  classical
  let φ := (LinearMap.piMap fun j ↦ (jacobsonRadicalSubmodule k Y (P j)).mkQ) ∘ₗ
    (biproductHomLinearEquiv k P Y).toLinearMap
  have hsurj : Function.Surjective φ :=
    (Function.Surjective.piMap (fun j ↦
      (jacobsonRadicalSubmodule k Y (P j)).mkQ_surjective)).comp
      (biproductHomLinearEquiv k P Y).surjective
  have hker : LinearMap.ker φ = jacobsonRadicalSubmodule k Y (⨁ P) := by
    ext f
    simp only [LinearMap.mem_ker, φ, LinearMap.comp_apply, LinearEquiv.coe_toLinearMap,
      LinearMap.coe_piMap, Pi.map_apply, Submodule.mkQ_apply, funext_iff, Pi.zero_apply,
      Submodule.Quotient.mk_eq_zero, biproductHomLinearEquiv_apply,
      mem_jacobsonRadicalSubmodule]
    constructor
    · intro hf
      have heq : f = ∑ j, (f ≫ biproduct.π P j) ≫ biproduct.ι P j := by
        simp only [Category.assoc, ← Preadditive.comp_sum, biproduct.total, Category.comp_id]
      rw [heq]
      exact (jacobsonRadical Y (⨁ P)).sum_mem fun j _ ↦
        comp_mem_jacobsonRadical_right (hf j) _
    · intro hf j
      exact comp_mem_jacobsonRadical_right hf _
  exact ((Submodule.quotEquivOfEq _ _ hker.symm).trans
    (φ.quotKerEquivOfSurjective hsurj)).finrank_eq.trans (Module.finrank_pi_fintype k)

/-- Between objects with local endomorphism rings, reversing source and target preserves
the dimension of the morphism space modulo the radical. -/
theorem finrank_quotient_jacobsonRadicalSubmodule_symm {X Y : C}
    [IsLocalRing (End X)] [IsLocalRing (End Y)] :
    Module.finrank k ((X ⟶ Y) ⧸ jacobsonRadicalSubmodule k X Y) =
      Module.finrank k ((Y ⟶ X) ⧸ jacobsonRadicalSubmodule k Y X) := by
  classical
  by_cases h : Nonempty (X ≅ Y)
  · obtain ⟨e⟩ := h
    exact finrank_quotient_jacobsonRadicalSubmodule_congr k e e.symm
  · have hXY : IsEmpty (X ≅ Y) := ⟨fun e ↦ h ⟨e⟩⟩
    have hYX : IsEmpty (Y ≅ X) := ⟨fun e ↦ h ⟨e.symm⟩⟩
    rw [finrank_quotient_jacobsonRadicalSubmodule_eq_zero k hXY,
      finrank_quotient_jacobsonRadicalSubmodule_eq_zero k hYX]

/-- Reversing source and target preserves dimension modulo the radical when one object has a
local endomorphism ring and the other is a finite biproduct of objects with local endomorphism
rings. -/
theorem finrank_quotient_jacobsonRadicalSubmodule_symm_of_iso_biproduct {J : Type*} [Finite J]
    {X Y : C} [IsLocalRing (End X)] (P : J → C) [HasBiproduct P]
    [∀ j, IsLocalRing (End (P j))]
    [∀ j, FiniteDimensional k ((P j ⟶ X) ⧸ jacobsonRadicalSubmodule k (P j) X)]
    [∀ j, FiniteDimensional k ((X ⟶ P j) ⧸ jacobsonRadicalSubmodule k X (P j))]
    (e : Y ≅ ⨁ P) :
    Module.finrank k ((X ⟶ Y) ⧸ jacobsonRadicalSubmodule k X Y) =
      Module.finrank k ((Y ⟶ X) ⧸ jacobsonRadicalSubmodule k Y X) := by
  let := Fintype.ofFinite J
  rw [finrank_quotient_jacobsonRadicalSubmodule_congr k (Iso.refl X) e,
    finrank_quotient_jacobsonRadicalSubmodule_congr k e (Iso.refl X),
    finrank_quotient_jacobsonRadicalSubmodule_biproduct_right,
    finrank_quotient_jacobsonRadicalSubmodule_biproduct]
  exact Finset.sum_congr rfl fun j _ ↦ finrank_quotient_jacobsonRadicalSubmodule_symm k

end TauCeti

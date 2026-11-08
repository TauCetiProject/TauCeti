/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Preadditive.Biproducts
public import TauCeti.Algebra.Category.FiniteHopfModuleCat.Basic

/-!
# Zero object and biproducts of finite-dimensional algebra modules

The category `FiniteHopfModuleCat k H` of `H`-modules finite-dimensional over `k` has a zero
object, the zero module, and binary biproducts: the biproduct of `M` and `N` is the product
module `M × N`, with the coordinate projections and inclusions. Both constructions only need
`H` to be a `k`-algebra.

These are the additive structures on which split Grothendieck groups `TauCeti.SplitK0` of the
category, such as representation rings of Hopf algebras, are built.

## Main declarations

* `HasZeroObject (TauCeti.FiniteHopfModuleCat k H)` and
  `HasBinaryBiproducts (TauCeti.FiniteHopfModuleCat k H)`.
* `TauCeti.FiniteHopfModuleCat.biprodIsoProd`: the chosen biproduct `M ⊞ N` is isomorphic to the
  product module `M × N`.

The construction follows Mathlib's `ModuleCat.biprodIsoProd`.
-/

public noncomputable section

open CategoryTheory Limits

namespace TauCeti.FiniteHopfModuleCat

universe u v

variable {k : Type u} [Field k] {H : Type v} [Ring H] [Algebra k H]

/-- A finite-dimensional module with at most one element is a zero object. -/
theorem isZero_of_subsingleton (M : FiniteHopfModuleCat k H) [Subsingleton M] : IsZero M :=
  (IsZero.iff_id_eq_zero M).2 (hom_ext (LinearMap.ext fun _ => Subsingleton.elim _ _))

instance : HasZeroObject (FiniteHopfModuleCat k H) :=
  (isZero_of_subsingleton (of (k := k) (H := H) PUnit)).hasZeroObject

variable (M N : FiniteHopfModuleCat k H)

/-- The product module `M × N`, as a bicone over `M` and `N` with the coordinate projections and
inclusions. -/
def prodBicone : BinaryBicone M N where
  pt := of (M × N)
  fst := ObjectProperty.homMk (ModuleCat.ofHom (LinearMap.fst H M N))
  snd := ObjectProperty.homMk (ModuleCat.ofHom (LinearMap.snd H M N))
  inl := ObjectProperty.homMk (ModuleCat.ofHom (LinearMap.inl H M N))
  inr := ObjectProperty.homMk (ModuleCat.ofHom (LinearMap.inr H M N))
  inl_fst := by ext; rfl
  inl_snd := by ext; rfl
  inr_fst := by ext; rfl
  inr_snd := by ext; rfl

/-- The product module is a biproduct. -/
def prodBiconeIsBilimit : (prodBicone M N).IsBilimit :=
  -- The sum of the two idempotents `fst ≫ inl` and `snd ≫ inr` sends `(m, n)` to
  -- `(m + 0, 0 + n)`.
  isBinaryBilimitOfTotal _ (by ext ⟨m, n⟩; exact Prod.ext (add_zero m) (zero_add n))

instance : HasBinaryBiproducts (FiniteHopfModuleCat k H) where
  has_binary_biproduct M N := HasBinaryBiproduct.mk ⟨_, prodBiconeIsBilimit M N⟩

/-- The chosen biproduct `M ⊞ N` is isomorphic to the product module `M × N`. -/
def biprodIsoProd : M ⊞ N ≅ of (M × N) :=
  (biprod.uniqueUpToIso M N (prodBiconeIsBilimit M N)).symm

/-- Under `biprodIsoProd`, the first biproduct projection is the first coordinate projection. -/
@[simp]
theorem biprodIsoProd_inv_comp_fst :
    (biprodIsoProd M N).inv ≫ biprod.fst =
      ObjectProperty.homMk (ModuleCat.ofHom (LinearMap.fst H M N)) :=
  biprod.lift_fst _ _

/-- Under `biprodIsoProd`, the second biproduct projection is the second coordinate projection. -/
@[simp]
theorem biprodIsoProd_inv_comp_snd :
    (biprodIsoProd M N).inv ≫ biprod.snd =
      ObjectProperty.homMk (ModuleCat.ofHom (LinearMap.snd H M N)) :=
  biprod.lift_snd _ _

end TauCeti.FiniteHopfModuleCat

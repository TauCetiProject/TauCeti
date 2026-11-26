/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Homotopy.Equiv
public import TauCeti.Topology.Category.CompactlyGenerated.Coreflection

/-!
# Preservation of homotopies by the `CompactlyGenerated` coreflector

Because `unitInterval` is locally compact, Hausdorff, and `0`-small, the coreflector
`TopCat.toCompactlyGenerated.{u}` commutes with the cylinder `unitInterval × -` up to
identity-on-points homeomorphism (`TopCat.toCompactlyGeneratedProdLeftHomeomorph`). Consequently,
`ContinuousMap.toCompactlyGenerated` preserves homotopies, relative homotopies, and homotopy
equivalences across arbitrary universes without separation hypotheses.

## Main declarations

* `ContinuousMap.Homotopy.toCompactlyGenerated`: sends a homotopy `f₀ ≃ f₁` to a homotopy
  `k(f₀) ≃ k(f₁)`.
* `ContinuousMap.HomotopyRel.toCompactlyGenerated`: sends a homotopy relative to `S` to a relative
  homotopy `k(f₀) ≃ k(f₁)`.
* `ContinuousMap.Homotopic.toCompactlyGenerated` and
  `ContinuousMap.HomotopicRel.toCompactlyGenerated`: preserve the (relative) homotopy relations.
* `ContinuousMap.HomotopyEquiv.toCompactlyGenerated`: sends a homotopy equivalence `X ≃ₕ Y` to a
  homotopy equivalence `kX ≃ₕ kY`.

## References

* N. E. Steenrod, *A convenient category of topological spaces*, Michigan Math. J. 14 (1967),
  133–152.
* R. M. Vogt, *Convenient categories of topological spaces for homotopy theory*, Arch. Math.
  (Basel) 22 (1971), 545–555.
-/

public section

noncomputable section

universe u v₁ v₂

namespace ContinuousMap

section ToCompactlyGenerated

variable {X : Type v₁} {Y : Type v₂} [TopologicalSpace X] [TopologicalSpace Y]

/-- Because `unitInterval` is locally compact, Hausdorff, and `0`-small, `k` commutes with the
cylinder `unitInterval × -` and therefore carries homotopies `f₀ ≃ f₁` to homotopies
`k(f₀) ≃ k(f₁)`. -/
@[expose]
def Homotopy.toCompactlyGenerated {f₀ f₁ : C(X, Y)} (F : f₀.Homotopy f₁) :
    f₀.toCompactlyGenerated.{u}.Homotopy f₁.toCompactlyGenerated.{u} where
  toContinuousMap := F.toContinuousMap.toCompactlyGenerated.{u}.comp
    (TopCat.toCompactlyGeneratedProdLeftHomeomorph.{u} unitInterval X).symm
  map_zero_left := F.map_zero_left
  map_one_left := F.map_one_left

@[simp]
theorem Homotopy.toCompactlyGenerated_apply {f₀ f₁ : C(X, Y)} (F : f₀.Homotopy f₁)
    (p : unitInterval × TopCat.toCompactlyGenerated.{u, v₁}.obj (TopCat.of X)) :
    F.toCompactlyGenerated.{u} p = F p := rfl

/-- `k` carries homotopies relative to a subset `S : Set X` to homotopies relative to `S`. -/
@[expose]
def HomotopyRel.toCompactlyGenerated {f₀ f₁ : C(X, Y)} {S : Set X} (F : f₀.HomotopyRel f₁ S) :
    f₀.toCompactlyGenerated.{u}.HomotopyRel f₁.toCompactlyGenerated.{u} S :=
  ⟨F.toHomotopy.toCompactlyGenerated.{u}, F.prop⟩

@[simp]
theorem HomotopyRel.toCompactlyGenerated_apply {f₀ f₁ : C(X, Y)} {S : Set X}
    (F : f₀.HomotopyRel f₁ S)
    (p : unitInterval × TopCat.toCompactlyGenerated.{u, v₁}.obj (TopCat.of X)) :
    F.toCompactlyGenerated.{u} p = F p := rfl

/-- `k` preserves the homotopy relation between continuous maps. -/
theorem Homotopic.toCompactlyGenerated {f₀ f₁ : C(X, Y)} (h : f₀.Homotopic f₁) :
    f₀.toCompactlyGenerated.{u}.Homotopic f₁.toCompactlyGenerated.{u} :=
  h.map Homotopy.toCompactlyGenerated.{u}

/-- `k` preserves homotopy relative to a subset `S : Set X`. -/
theorem HomotopicRel.toCompactlyGenerated {f₀ f₁ : C(X, Y)} {S : Set X}
    (h : f₀.HomotopicRel f₁ S) :
    f₀.toCompactlyGenerated.{u}.HomotopicRel f₁.toCompactlyGenerated.{u} S :=
  h.map HomotopyRel.toCompactlyGenerated.{u}

/-- `k` preserves homotopy equivalences across arbitrary universes without separation hypotheses. -/
@[expose]
def HomotopyEquiv.toCompactlyGenerated (e : X ≃ₕ Y) :
    TopCat.toCompactlyGenerated.{u, v₁}.obj (TopCat.of X) ≃ₕ
      TopCat.toCompactlyGenerated.{u, v₂}.obj (TopCat.of Y) where
  toFun := e.toFun.toCompactlyGenerated.{u}
  invFun := e.invFun.toCompactlyGenerated.{u}
  left_inv := e.left_inv.toCompactlyGenerated.{u}
  right_inv := e.right_inv.toCompactlyGenerated.{u}

@[simp]
theorem HomotopyEquiv.toCompactlyGenerated_apply (e : X ≃ₕ Y)
    (x : TopCat.toCompactlyGenerated.{u, v₁}.obj (TopCat.of X)) :
    e.toCompactlyGenerated.{u} x = e x := rfl

@[simp]
theorem HomotopyEquiv.toCompactlyGenerated_symm_apply (e : X ≃ₕ Y)
    (y : TopCat.toCompactlyGenerated.{u, v₂}.obj (TopCat.of Y)) :
    (e.toCompactlyGenerated.{u}).symm y = e.symm y := rfl

end ToCompactlyGenerated

end ContinuousMap

end

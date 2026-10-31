/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RepresentationTheory.Coinvariants

/-!
# Change of groups on tensor coinvariants

Let `f : G →* H` be a group homomorphism and `φ : A ⟶ Res(f)(B)` a compatible map of coefficient
representations. A morphism `v : X ⟶ Res(f)(Y)` of `G`-representations induces the linear map
`MonoidHom.coinvariantsTensorMap f φ v : (A ⊗ X)_G ⟶ (B ⊗ Y)_H` on Mathlib's tensor coinvariants,
which sends the class of `a ⊗ x` to the class of `φ a ⊗ v x`. It is natural in `X` and `Y`.

This is the degreewise construction underlying change of groups on the tensor coinvariants of
complexes, `MonoidHom.coinvariantsTensorChainMap`.

## Main definitions

* `MonoidHom.coinvariantsTensorMap`: the map `(A ⊗ X)_G ⟶ (B ⊗ Y)_H` induced by `f`, `φ`
  and `v`.

## Main results

* `MonoidHom.coinvariantsTensorMap_mk`: its value on a tensor class.
* `MonoidHom.coinvariantsTensorMap_naturality`: naturality in the representations.

## References

* K. S. Brown, *Cohomology of Groups*, GTM 87, Springer, 1982, Chapter III, §8.

The tensor coinvariants functor `Rep.coinvariantsTensor` is Mathlib's construction by Amelia
Livingston.
-/

public section

noncomputable section

open CategoryTheory Rep Representation

universe u

namespace MonoidHom

variable {k G H : Type u} [CommRing k] [Group G] [Group H] {A : Rep.{u} k G} {B : Rep.{u} k H}
  (f : G →* H) (φ : A ⟶ res f B)

/-- **Change of groups on tensor coinvariants.** For `f : G →* H`, a compatible coefficient map
`φ : A ⟶ Res(f)(B)` and a morphism `v : X ⟶ Res(f)(Y)`, this is the map `(A ⊗ X)_G ⟶ (B ⊗ Y)_H`
sending the class of `a ⊗ x` to the class of `φ a ⊗ v x`. -/
def coinvariantsTensorMap {X : Rep.{u} k G} {Y : Rep.{u} k H} (v : X ⟶ res f Y) :
    ((coinvariantsTensor k G).obj A).obj X ⟶ ((coinvariantsTensor k H).obj B).obj Y :=
  ModuleCat.ofHom <| Coinvariants.lift _
    ((Coinvariants.mk _).comp (TensorProduct.map φ.hom.toLinearMap v.hom.toLinearMap))
    fun g ↦ TensorProduct.ext' fun a x ↦ by
      have h₁ := Rep.hom_comm_apply φ g a
      have h₂ := Rep.hom_comm_apply v g x
      -- The tensor representations are presented through the monoidal structure of `Rep`.
      -- State them as `Representation.tprod`, so that the tensor computation applies.
      change Coinvariants.mk (B.ρ.tprod Y.ρ) (TensorProduct.map φ.hom.toLinearMap
          v.hom.toLinearMap (A.ρ.tprod X.ρ g (a ⊗ₜ x))) =
        Coinvariants.mk (B.ρ.tprod Y.ρ)
          (TensorProduct.map φ.hom.toLinearMap v.hom.toLinearMap (a ⊗ₜ x))
      rw [tprod_apply, TensorProduct.map_tmul, TensorProduct.map_tmul, TensorProduct.map_tmul]
      simp only [IntertwiningMap.toLinearMap_apply, h₁, h₂]
      exact Coinvariants.mk_self_apply (B.ρ.tprod Y.ρ) (f g) (φ.hom a ⊗ₜ[k] v.hom x)

/-- The map sends the class of `a ⊗ x` to the class of `φ a ⊗ v x`. -/
-- Match before simplification changes the presentation of the tensor carrier.
@[simp↓]
theorem coinvariantsTensorMap_mk {X : Rep.{u} k G} {Y : Rep.{u} k H} (v : X ⟶ res f Y)
    (a : A) (x : X) :
    (f.coinvariantsTensorMap φ v).hom (coinvariantsTensorMk A X a x) =
      coinvariantsTensorMk B Y (φ.hom a) (v.hom x) :=
  (rfl)

/-- The map is natural in the representations. -/
theorem coinvariantsTensorMap_naturality {X X' : Rep.{u} k G} {Y Y' : Rep.{u} k H}
    (v : X ⟶ res f Y) (v' : X' ⟶ res f Y') (s : X ⟶ X') (t : Y ⟶ Y')
    (h : v ≫ (resFunctor f).map t = s ≫ v') :
    ((coinvariantsTensor k G).obj A).map s ≫ f.coinvariantsTensorMap φ v' =
      f.coinvariantsTensorMap φ v ≫ ((coinvariantsTensor k H).obj B).map t := by
  refine coinvariantsTensor_hom_ext (LinearMap.ext₂ fun a x ↦ ?_)
  have hx : v'.hom (s.hom x) = t.hom (v.hom x) := (congrArg (fun w ↦ w.hom x) h).symm
  -- The functor `(coinvariantsTensor k G).obj A` acts on a tensor class through the
  -- second factor; this holds by definition of the tensor product of morphisms.
  change (f.coinvariantsTensorMap φ v').hom (coinvariantsTensorMk A X' a (s.hom x)) =
    (((coinvariantsTensor k H).obj B).map t).hom (coinvariantsTensorMk B Y (φ.hom a) (v.hom x))
  rw [coinvariantsTensorMap_mk, hx]
  rfl

end MonoidHom

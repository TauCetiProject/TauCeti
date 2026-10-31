/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RepresentationTheory.Coinvariants

/-!
# Change of groups on tensor coinvariants, and maps out of tensor coinvariants

Let `f : G →* H` be a group homomorphism and `φ : A ⟶ Res(f)(B)` a compatible map of coefficient
representations. A morphism `v : X ⟶ Res(f)(Y)` of `G`-representations induces the linear map
`MonoidHom.coinvariantsTensorMap f φ v : (A ⊗ X)_G ⟶ (B ⊗ Y)_H` on Mathlib's tensor coinvariants,
which sends the class of `a ⊗ x` to the class of `φ a ⊗ v x`. It is natural in `X` and `Y`.

This is the degreewise construction underlying change of groups on the tensor coinvariants of
complexes, `MonoidHom.coinvariantsTensorChainMap`.

For a `k`-module `N`, a `k`-linear map `X_G ⟶ N` out of the coinvariants is the same as a
morphism of representations `X ⟶ N` to the trivial representation (`Rep.coinvariantsAdjunction`);
`Rep.coinvariantsHomLinearEquiv` is the `k`-linear form of this bijection, for representations of
any monoid. For a representation `A` of a group, a morphism of representations `A ⊗ X ⟶ N` is in
turn the same as a morphism `X ⟶ Homₖ(A, N)` into the internal hom
(`Rep.MonoidalClosed.linearHomEquiv`). The composite `k`-linear equivalence is
`Rep.coinvariantsTensorHomLinearEquiv`; it sends `f` to `x ↦ (a ↦ f ⟦a ⊗ x⟧)` and is natural in
`X`.

## Main definitions

* `MonoidHom.coinvariantsTensorMap`: the map `(A ⊗ X)_G ⟶ (B ⊗ Y)_H` induced by `f`, `φ`
  and `v`.
* `Rep.coinvariantsHomLinearEquiv`: `Hom(X_G, N) ≃ₗ[k] Hom_G(X, N)`.
* `Rep.coinvariantsTensorHomLinearEquiv`: `Hom((A ⊗ X)_G, N) ≃ₗ[k] Hom_G(X, Homₖ(A, N))`.

## Main results

* `MonoidHom.coinvariantsTensorMap_mk`: its value on a tensor class.
* `MonoidHom.coinvariantsTensorMap_naturality`: naturality in the representations.
* `Rep.coinvariantsTensorHomLinearEquiv_comp`: naturality of
  `Rep.coinvariantsTensorHomLinearEquiv` in the representation.

## References

* K. S. Brown, *Cohomology of Groups*, GTM 87, Springer, 1982, Chapter III, §8 and Section III.2.

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

namespace Rep

open MonoidalCategory

section Monoid

variable {k G : Type u} [CommRing k] [Monoid G] (N : Type u) [AddCommGroup N] [Module k N]

/-- **Maps out of coinvariants are invariant maps**: the bijection of the adjunction
`Rep.coinvariantsAdjunction` between `k`-linear maps `X_G ⟶ N` and morphisms of representations
`X ⟶ N` to the trivial representation is `k`-linear. -/
def coinvariantsHomLinearEquiv (X : Rep.{u} k G) :
    ((coinvariantsFunctor k G).obj X ⟶ ModuleCat.of k N) ≃ₗ[k] (X ⟶ Rep.trivial k G N) :=
  { (coinvariantsAdjunction k G).homEquiv X (ModuleCat.of k N) with
    map_add' _ _ := by ext; simp [Rep.add_hom, Adjunction.homEquiv_unit]
    map_smul' _ _ := by ext; simp [Rep.smul_hom, Adjunction.homEquiv_unit] }

/-- The invariant map corresponding to `f : X_G ⟶ N` is `f` composed with the projection to the
coinvariants. -/
@[simp]
theorem coinvariantsHomLinearEquiv_apply_hom_apply {X : Rep.{u} k G}
    (f : (coinvariantsFunctor k G).obj X ⟶ ModuleCat.of k N) (x : X) :
    (coinvariantsHomLinearEquiv N X f).hom x = f (Representation.Coinvariants.mk X.ρ x) :=
  (rfl)

/-- The map out of the coinvariants corresponding to `φ : X ⟶ N` sends the class of `x` to
`φ x`. -/
-- Match before simplification changes the presentation of the coinvariants carrier.
@[simp↓]
theorem coinvariantsHomLinearEquiv_symm_apply_mk {X : Rep.{u} k G} (φ : X ⟶ Rep.trivial k G N)
    (x : X) :
    (coinvariantsHomLinearEquiv N X).symm φ (Representation.Coinvariants.mk X.ρ x) = φ.hom x := by
  have h := coinvariantsHomLinearEquiv_apply_hom_apply N ((coinvariantsHomLinearEquiv N X).symm φ) x
  rw [LinearEquiv.apply_symm_apply] at h
  exact h.symm

end Monoid

section Group

variable {k G : Type u} [CommRing k] [Group G] (A : Rep.{u} k G) (N : Type u) [AddCommGroup N]
  [Module k N]

/-- **Maps out of tensor coinvariants are morphisms into the internal hom**: for representations
`A` and `X` of `G` and a `k`-module `N`, the `k`-linear maps `(A ⊗ X)_G ⟶ N` correspond
`k`-linearly to the morphisms of representations `X ⟶ Homₖ(A, N)`, where `N` carries the trivial
action. The map `f` corresponds to `x ↦ (a ↦ f ⟦a ⊗ x⟧)`
(`Rep.coinvariantsTensorHomLinearEquiv_apply_hom_apply_apply`). -/
def coinvariantsTensorHomLinearEquiv (X : Rep.{u} k G) :
    (((coinvariantsTensor k G).obj A).obj X ⟶ ModuleCat.of k N) ≃ₗ[k]
      (X ⟶ (Rep.ihom A).obj (Rep.trivial k G N)) :=
  coinvariantsHomLinearEquiv N (A ⊗ X) ≪≫ₗ MonoidalClosed.linearHomEquiv A X (Rep.trivial k G N)

variable {A N}

/-- The morphism corresponding to a map `f : (A ⊗ X)_G ⟶ N` sends `x` to `a ↦ f ⟦a ⊗ x⟧`. -/
-- Match before simplification changes the presentation of the tensor carrier.
@[simp↓]
theorem coinvariantsTensorHomLinearEquiv_apply_hom_apply_apply {X : Rep.{u} k G}
    (f : ((coinvariantsTensor k G).obj A).obj X ⟶ ModuleCat.of k N) (x : X) (a : A) :
    -- The carrier of `Homₖ(A, N)` is `A →ₗ[k] N` only up to unfolding, so the coercion is named.
    DFunLike.coe (F := A →ₗ[k] N) ((coinvariantsTensorHomLinearEquiv A N X f).hom x) a =
      f (coinvariantsTensorMk A X a x) :=
  (rfl)

/-- The map corresponding to a morphism `φ : X ⟶ Homₖ(A, N)` sends `⟦a ⊗ x⟧` to `φ x a`. -/
-- Match before simplification changes the presentation of the tensor carrier.
@[simp↓]
theorem coinvariantsTensorHomLinearEquiv_symm_apply_coinvariantsTensorMk {X : Rep.{u} k G}
    (φ : X ⟶ (Rep.ihom A).obj (Rep.trivial k G N)) (a : A) (x : X) :
    (coinvariantsTensorHomLinearEquiv A N X).symm φ (coinvariantsTensorMk A X a x) =
      DFunLike.coe (F := A →ₗ[k] N) (φ.hom x) a := by
  have h := coinvariantsTensorHomLinearEquiv_apply_hom_apply_apply
    ((coinvariantsTensorHomLinearEquiv A N X).symm φ) x a
  rw [LinearEquiv.apply_symm_apply] at h
  exact h.symm

/-- **The correspondence is natural in the representation**: precomposing a map out of
`(A ⊗ X')_G` with the map induced by `g : X ⟶ X'` corresponds to precomposing with `g`. -/
theorem coinvariantsTensorHomLinearEquiv_comp {X X' : Rep.{u} k G} (g : X ⟶ X')
    (f : ((coinvariantsTensor k G).obj A).obj X' ⟶ ModuleCat.of k N) :
    coinvariantsTensorHomLinearEquiv A N X (((coinvariantsTensor k G).obj A).map g ≫ f) =
      g ≫ coinvariantsTensorHomLinearEquiv A N X' f := by
  -- `(A ⊗ -)_G` sends `g` to the map of coinvariants induced by `A ◁ g`, so this is the
  -- naturality of the hom-equivalences of the coinvariants and internal-hom adjunctions.
  change (ihom.adjunction A).homEquiv _ _ ((coinvariantsAdjunction k G).homEquiv _ _
    ((coinvariantsFunctor k G).map ((tensorLeft A).map g) ≫ f)) =
      g ≫ (ihom.adjunction A).homEquiv _ _ ((coinvariantsAdjunction k G).homEquiv _ _ f)
  rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_left]

end Group

end Rep

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.Weight.Torus
public import TauCeti.Algebra.AlgebraicGroup.SplitTorus.LinearMap

/-!
# Weight tori along maps of character lattices

Let `wt : Fin N → κ → ℤ` be a family of weights of the split torus `𝔾ₘ^κ` and let
`f : (κ → ℤ) →ₗ[ℤ] (κ' → ℤ)` be a map of character lattices. Pushing every weight forward along
`f` gives a weight family of `𝔾ₘ^κ'`, and its weight torus is the weight torus of `wt` precomposed
with the split-torus morphism `𝔾ₘ^κ' → 𝔾ₘ^κ` dual to `f`:

```text
weightTorus (f ∘ wt) = SplitTorus.ofLinearMap f ≫ weightTorus wt.
```

On coordinate Hopf algebras the dual morphism is the group-algebra map of `f`, which is injective
when `f` is. In that case the two weight-torus coordinate maps have the same kernel: the two
parametrized tori cut out the same closed subscheme of `GL_N`, even though the parametrization by
`f ∘ wt` has a nontrivial kernel whenever `f` is not surjective. For example, the adjoint torus of
`A₁` has weights `α, 0, -α`, that is `1, 0, -1` in root-lattice coordinates; read in the weight
lattice, where `α = 2ϖ`, they give the parametrization `s ↦ diag(s², 1, s⁻²)`, whose kernel is
`μ₂`, and which has the same image as `s ↦ diag(s, 1, s⁻¹)`.

## Main results

* `TauCeti.GeneralLinear.weightCharacterMap_linearMap`: pushing the weights forward along `f`
  composes the character-lattice map with `f`.
* `TauCeti.GeneralLinear.weightTorusCoordinateMap_linearMap` and
  `TauCeti.GeneralLinear.weightTorus_linearMap`: the corresponding factorizations of the coordinate
  morphism and of the represented weight torus;
  `TauCeti.GeneralLinear.hom_weightTorusCoordinateMap_linearMap` is the bialgebra form of the
  first.
* `TauCeti.GeneralLinear.ker_weightTorusCoordinateMap_linearMap`: for injective `f` the two
  coordinate maps have the same kernel.

## References

* J. S. Milne, *Algebraic Groups* (2017), §12.
-/

public section

open CategoryTheory

namespace TauCeti.GeneralLinear

universe u

variable {R κ κ' : Type u} [CommRing R] [Finite κ] [Finite κ'] {N : ℕ}

/-- **Pushing the weights forward along a map of character lattices composes the weight
character-lattice map with it.** -/
theorem weightCharacterMap_linearMap (f : (κ → ℤ) →ₗ[ℤ] (κ' → ℤ)) (wt : Fin N → κ → ℤ) :
    weightCharacterMap (fun i => f (wt i)) =
      (SplitTorus.characterMapOfLinearMap f).comp (weightCharacterMap wt) := by
  ext ⟨i⟩ j
  have hwt :
      Finsupp.linearEquivFunOnFinite ℤ ℤ κ (Finsupp.equivFunOnFinite.symm (wt i)) = wt i := by
    ext; simp
  simp [hwt]

/-- **Pushing the weights forward along `f` composes the underlying bialgebra morphism of the
weight-torus coordinate map with the group-algebra map of `f`.** -/
theorem hom_weightTorusCoordinateMap_linearMap (f : (κ → ℤ) →ₗ[ℤ] (κ' → ℤ))
    (wt : Fin N → κ → ℤ) :
    (weightTorusCoordinateMap (R := R) fun i => f (wt i)).hom =
      (MonoidAlgebra.mapDomainBialgHom R (SplitTorus.characterMapOfLinearMap f)).comp
        (weightTorusCoordinateMap (R := R) wt).hom := by
  apply coordinateHopfAlgebra_bialgHom_ext R N
  intro i j
  rw [BialgHom.comp_apply, weightTorusCoordinateMap_X, weightTorusCoordinateMap_X]
  split_ifs
  · have hi := weightCharacterMap_ofAdd_single (fun i => f (wt i)) i
    rw [weightCharacterMap_linearMap, MonoidHom.comp_apply, weightCharacterMap_ofAdd_single] at hi
    rw [MonoidAlgebra.mapDomainBialgHom_single, hi]
  · simp

/-- **The weight-torus coordinate map of the pushed-forward weights** is the weight-torus coordinate
map of the original weights followed by the group-algebra map of `f`. -/
theorem weightTorusCoordinateMap_linearMap (f : (κ → ℤ) →ₗ[ℤ] (κ' → ℤ)) (wt : Fin N → κ → ℤ) :
    weightTorusCoordinateMap (R := R) (fun i => f (wt i)) =
      weightTorusCoordinateMap (R := R) wt ≫
        (DiagonalizableGroup.coordinateMap R (SplitTorus.characterGroupMapOfLinearMap f)).hom := by
  apply _root_.CommHopfAlgCat.hom_ext
  rw [_root_.CommHopfAlgCat.hom_comp, hom_weightTorusCoordinateMap_linearMap,
    ← SplitTorus.hom_hom_characterGroupMapOfLinearMap,
    ← DiagonalizableGroup.toBialgHom_coordinateMap]

/-- **The weight torus of the pushed-forward weights** is the weight torus of the original weights
precomposed with the split-torus morphism dual to `f`. -/
theorem weightTorus_linearMap (f : (κ → ℤ) →ₗ[ℤ] (κ' → ℤ)) (wt : Fin N → κ → ℤ) :
    weightTorus (R := R) (fun i => f (wt i)) = SplitTorus.ofLinearMap R f ≫ weightTorus wt := by
  rw [weightTorus_def, weightTorus_def, SplitTorus.ofLinearMap_def,
    DiagonalizableGroup.groupSchemeMap_def, weightTorusCoordinateMap_linearMap, op_comp,
    Functor.map_comp]
  simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]

/-- **Pushing the weights forward along an injective map of character lattices does not change the
kernel of the weight-torus coordinate map.** The group-algebra map of an injective map of character
lattices is injective. Hence both weight families cut out the same closed subscheme of `GL_N`. -/
theorem ker_weightTorusCoordinateMap_linearMap {f : (κ → ℤ) →ₗ[ℤ] (κ' → ℤ)}
    (hf : Function.Injective f) (wt : Fin N → κ → ℤ) :
    RingHom.ker (weightTorusCoordinateMap (R := R) fun i => f (wt i)).hom.toAlgHom.toRingHom =
      RingHom.ker (weightTorusCoordinateMap (R := R) wt).hom.toAlgHom.toRingHom := by
  rw [hom_weightTorusCoordinateMap_linearMap]
  exact RingHom.ker_comp_of_injective (weightTorusCoordinateMap (R := R) wt).hom.toAlgHom.toRingHom
    (f := (MonoidAlgebra.mapDomainBialgHom R
      (SplitTorus.characterMapOfLinearMap f)).toAlgHom.toRingHom)
    (MonoidAlgebra.mapDomain_injective (SplitTorus.characterMapOfLinearMap_injective hf))

end TauCeti.GeneralLinear

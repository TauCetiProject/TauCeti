/-
Copyright (c) 2026 Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.RepresentationTheory.Homological.Resolution
public import Mathlib.CategoryTheory.Preadditive.Projective.Resolution
public import Mathlib.RepresentationTheory.Coinduced

/-!
# The bar resolution along a group homomorphism

Let `f : H →* G` be a homomorphism of groups. The bar resolution `Rep.barComplex k H` of the
trivial representation `k` of `H` maps to the restriction along `f` of the bar resolution of `G`:
in degree `n` a basis element `(h₁, …, hₙ)` is sent to `(f h₁, …, f hₙ)`. This file constructs
that chain map, `TauCeti.Rep.barComplex.resChainMap`, and checks that it lies over the identity of
`k` when `f` is the inclusion of a subgroup, so that it is a morphism of projective resolutions of
`k` over the subgroup.

To make the last statement checkable, the file also computes the augmentations of Mathlib's
standard and bar resolutions on basis elements: both send a basis element with coefficient `r` to
`r`. On the way it records the value of the comparison `Rep.diagonalSuccIsoFree` between the bar
and standard resolutions on basis elements, `(g, (g₁, …, gₙ)) ↦ g • (1, g₁, g₁g₂, …, g₁⋯gₙ)`.

The chain map is what identifies Mathlib's Shapiro isomorphism `groupCohomology.coindIso`, which is
defined through `Ext`, with an explicit map on inhomogeneous cochains.

## Main definitions

* `TauCeti.Rep.barComplex.resHom`: the degree-`n` component `k[Hⁿ] ⊗ k[H] ⟶ k[Gⁿ] ⊗ k[G]`.
* `TauCeti.Rep.barComplex.resChainMap`: the chain map from the bar resolution of `H` to the
  restriction of the bar resolution of `G`.

## Main results

* `TauCeti.Rep.diagonalSuccIsoFree_inv_hom_single`: the comparison between the bar and standard
  resolutions on basis elements.
* `TauCeti.Rep.standardResolution_π_f_zero_single` and
  `TauCeti.Rep.barResolution_π_f_zero_single`: the augmentations on basis elements.
* `TauCeti.Rep.barComplex.resChainMap_f_zero_comp_π`: for a subgroup, the chain map lies over the
  identity of `k`.

## References

* K. S. Brown, *Cohomology of Groups*, Graduate Texts in Mathematics 87, Springer (1982),
  Chapter I, §5 (the bar resolution) and Chapter III, §8 (change of groups).
-/

public section

open CategoryTheory Finsupp

namespace TauCeti.Rep

open _root_.Rep

universe u

variable {k G H : Type u} [CommRing k] [Group G] [Group H]

/-- The comparison `Rep.diagonalSuccIsoFree` between the bar and standard resolutions sends the
basis element `(g₁, …, gₘ)` with coefficient `r • g` to `g • (1, g₁, g₁g₂, …, g₁⋯gₘ)` with
coefficient `r`. -/
theorem diagonalSuccIsoFree_inv_hom_single (m : ℕ) (x : Fin m → G) (g : G) (r : k) :
    (diagonalSuccIsoFree k G m).inv.hom (single x (MonoidAlgebra.single g r)) =
      MonoidAlgebra.single (g • Fin.partialProd x) r := by
  simp only [diagonalSuccIsoFree, diagonalSuccIsoTensorTrivial, Iso.trans_inv, Rep.hom_comp,
    Representation.IntertwiningMap.comp_apply]
  have h : (leftRegularTensorTrivialIsoFree k G (Fin m → G)).inv.hom (single x (.single g r)) =
      .single g 1 ⊗ₜ[k] .single x r :=
    Representation.leftRegularTensorTrivialIsoFree_symm_apply_single_single x g r
  rw [h]
  refine ((congrArg (Representation.linearizeMap (Action.diagonalSuccIsoTensorTrivial G m).inv)
      (Representation.LinearizeMonoidal.μ_apply_single_single (k := k)
        (X := Action.leftRegular G) (Y := Action.trivial G (Fin m → G)) g x 1 r)).trans
    (Representation.linearizeMap_single (k := k)
      (Action.diagonalSuccIsoTensorTrivial G m).inv (g, x) ((1 : k) * r))).trans ?_
  rw [one_mul, Action.diagonalSuccIsoTensorTrivial_inv_hom_apply]

/-- The augmentation of the standard resolution sends a basis element with coefficient `r` to
`r`. -/
theorem standardResolution_π_f_zero_single (y : Fin 1 → G) (r : k) :
    ((standardResolution k G).π.f 0).hom (MonoidAlgebra.single y r) = r :=
  (congrArg (fun φ : (standardComplex k G).X 0 ⟶ trivial k G k => φ.hom (MonoidAlgebra.single y r))
    (ChainComplex.toSingle₀Equiv_symm_apply_f_zero (C := standardComplex k G)
      (X := trivial k G k) (standardComplex.ε k G) (standardComplex.d_comp_ε k G))).trans
    ((linearCombination_single k (v := fun _ : Fin 1 → G => (1 : k)) r y).trans (mul_one r))

/-- The augmentation of the bar resolution sends a basis element with coefficient `r` to `r`. -/
theorem barResolution_π_f_zero_single (x : Fin 0 → G) (g : G) (r : k) :
    ((barResolution k G).π.f 0).hom (single x (MonoidAlgebra.single g r)) = r :=
  (congrArg ((standardResolution k G).π.f 0).hom
    (diagonalSuccIsoFree_inv_hom_single (k := k) 0 x g r)).trans
    (standardResolution_π_f_zero_single _ r)

namespace barComplex

open _root_.Rep.barComplex

/-- The degree-`n` component of the map from the bar resolution of `H` to the restriction along
`f : H →* G` of the bar resolution of `G`: it sends the basis element `(h₁, …, hₙ)` to
`(f h₁, …, f hₙ)`. -/
noncomputable def resHom (f : H →* G) (n : ℕ) :
    free k H (Fin n → H) ⟶ res f (free k G (Fin n → G)) :=
  freeLift k H (res f (free k G (Fin n → G))) fun x => single (f ∘ x) (MonoidAlgebra.single 1 1)

/-- `resHom f n` applies `f` to the tuple and to the group coefficient of a basis element. -/
@[simp]
theorem resHom_single (f : H →* G) (n : ℕ) (x : Fin n → H) (h : H) (r : k) :
    (resHom f n).hom (single x (MonoidAlgebra.single h r)) =
      single (f ∘ x) (MonoidAlgebra.single (f h) r) := by
  simp [resHom]

/-- The components `resHom f n` commute with the bar differentials. -/
theorem d_comp_resHom (f : H →* G) (n : ℕ) :
    d k H n ≫ resHom f n = resHom f (n + 1) ≫ (resFunctor f).map (d k G n) := by
  refine free_ext _ _ _ _ _ fun x => ?_
  simp only [Rep.hom_comp, Representation.IntertwiningMap.comp_apply]
  rw [d_single, resHom_single, map_add, map_sum, resHom_single, resMap_hom_apply, map_one,
    d_single]
  refine congrArg _ (Finset.sum_congr rfl fun j _ => ?_)
  rw [resHom_single, map_one, Fin.comp_contractNth _ _ (map_mul f)]

/-- **The bar resolution along a group homomorphism.** The chain map from the bar resolution of
`H` to the restriction along `f : H →* G` of the bar resolution of `G`, sending `(h₁, …, hₙ)` to
`(f h₁, …, f hₙ)` in every degree. -/
noncomputable def resChainMap (f : H →* G) :
    barComplex k H ⟶ ((resFunctor f).mapHomologicalComplex _).obj (barComplex k G) where
  f n := resHom f n
  comm' i j (h : j + 1 = i) := by
    subst h
    simpa [d_def] using (d_comp_resHom (k := k) f j).symm

/-- The components of `resChainMap f` are the maps `resHom f n`. -/
@[simp]
theorem resChainMap_f (f : H →* G) (n : ℕ) : (resChainMap (k := k) f).f n = resHom f n := (rfl)

/-- **For a subgroup, the bar resolution along the inclusion lies over the identity of `k`**: it is
a morphism from the bar resolution of `S` to the restriction of the bar resolution of `G`, both
viewed as projective resolutions of the trivial representation of `S`. -/
theorem resChainMap_f_zero_comp_π (S : Subgroup G) : (resChainMap (k := k) S.subtype).f 0 ≫
    ((resFunctor S.subtype).mapProjectiveResolution (barResolution k G)).π.f 0 =
      (barResolution k S).π.f 0 := by
  refine free_ext _ _ _ _ _ fun x => ?_
  have h₁ : ((resChainMap (k := k) S.subtype).f 0).hom (single x (MonoidAlgebra.single 1 1)) =
      single (S.subtype ∘ x) (MonoidAlgebra.single 1 1) := resHom_single _ _ _ _ _
  -- The augmentation of the restricted resolution is that of `G` followed by the canonical
  -- identifications of the single complex, which are the identity on underlying modules.
  have h₂ : (((resFunctor S.subtype).mapProjectiveResolution (barResolution k G)).π.f 0).hom
      (single (S.subtype ∘ x) (MonoidAlgebra.single 1 1)) = (1 : k) :=
    barResolution_π_f_zero_single (k := k) (S.subtype ∘ x) (1 : G) 1
  exact (congrArg _ h₁).trans (h₂.trans (barResolution_π_f_zero_single (k := k) x (1 : S) 1).symm)

end barComplex

end TauCeti.Rep

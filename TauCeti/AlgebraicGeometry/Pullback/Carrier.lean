/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.PullbackCarrier
public import Mathlib.RingTheory.IntegralClosure.IsIntegral.Defs

import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.RingTheory.RingHom.Integral

/-!
# Underlying sets and residue fields of fibre products

In any cartesian square of schemes, the topological image of either projection is the preimage of
the image of the opposite morphism (`AlgebraicGeometry.Scheme.Pullback.range_fst_of_isPullback`
and `AlgebraicGeometry.Scheme.Pullback.range_snd_of_isPullback`), extending Mathlib's
`range_fst` and `range_snd` from chosen pullbacks to arbitrary cartesian squares. If moreover the
second projection is injective on points, the fibre of the first projection over a point `x` has
the same cardinality as the fibre of the opposite map over the image of `x`
(`AlgebraicGeometry.Scheme.natCard_preimage_fst_singleton_of_isPullback`), as for the inverse
image of a closed subscheme.

Let `t` be a point of `X ×_S Y` lying over `x ∈ X`, `y ∈ Y` and `s ∈ S`. Mathlib's
`AlgebraicGeometry.Scheme.Pullback.ofPointTensor` is the canonical map
`κ(x) ⊗[κ(s)] κ(y) ⟶ κ(t)`. In general `κ(t)` is only the fraction field of the image of this
map. If `κ(x)` is integral over `κ(s)`, for instance if `X → S` is finite, or unramified and
locally of finite type, then the map is surjective. So `κ(t)` is then generated as a ring by the
images of `κ(x)` and `κ(y)`. The proof uses that `κ(x) ⊗[κ(s)] κ(y)` is integral over the field
`κ(y)`, so all of its primes are maximal.

For a base change of a finite étale cover, this shows that each residue field of the base change
is a quotient of a base change of a residue field of the cover, as used in the proof of Stacks,
Lemma 58.31.1 (0EYD).

## Main results

* `AlgebraicGeometry.Scheme.Pullback.range_fst_of_isPullback` and
  `AlgebraicGeometry.Scheme.Pullback.range_snd_of_isPullback`: the topological range of a
  projection in a cartesian square of schemes is the preimage of the opposite morphism's range.
* `AlgebraicGeometry.Scheme.natCard_preimage_fst_singleton_of_isPullback`: if the second
  projection of a pullback square is injective, the fibres of the first projection have the same
  cardinality as the corresponding fibres of the opposite map.
* `AlgebraicGeometry.Scheme.Pullback.ofPointTensor_surjective`: `κ(x) ⊗[κ(s)] κ(y) ⟶ κ(t)` is
  surjective when `κ(x)` is integral over `κ(s)`.
* `AlgebraicGeometry.Scheme.Pullback.closure_range_residueFieldMap_eq_top`: in that case `κ(t)`
  is generated as a ring by the images of `κ(x)` and `κ(y)`.
* `AlgebraicGeometry.Scheme.Pullback.surjective_liftEquiv_residueFieldMap`: consequently, for
  rings `K ⟶ K'` such that `κ(t)` is a `K'`-algebra containing the image of `κ(y)`, the induced
  map `K' ⊗[K] κ(x) ⟶ κ(t)` is surjective.
-/

public section

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme.Pullback

universe u

/-- In a cartesian square of schemes, the range of the first projection is the preimage of the
range of the opposite morphism. -/
theorem range_fst_of_isPullback {P X Y S : Scheme.{u}} {fst : P ⟶ X} {snd : P ⟶ Y}
    {f : X ⟶ S} {g : Y ⟶ S} (h : IsPullback fst snd f g) :
    Set.range fst = f ⁻¹' Set.range g := by
  rw [← h.isoPullback_hom_fst, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp,
    Set.range_eq_univ.mpr h.isoPullback.hom.surjective, Set.image_univ, range_fst]

/-- In a cartesian square of schemes, the range of the second projection is the preimage of the
range of the opposite morphism. -/
theorem range_snd_of_isPullback {P X Y S : Scheme.{u}} {fst : P ⟶ X} {snd : P ⟶ Y}
    {f : X ⟶ S} {g : Y ⟶ S} (h : IsPullback fst snd f g) :
    Set.range snd = g ⁻¹' Set.range f :=
  range_fst_of_isPullback h.flip

variable {X Y S : Scheme.{u}} {f : X ⟶ S} {g : Y ⟶ S}

/-- If `t` is a point of `X ×_S Y` over `x ∈ X` and `κ(x)` is integral over `κ(f x)`, then the
canonical map `κ(x) ⊗[κ(s)] κ(y) ⟶ κ(t)` is surjective. -/
theorem ofPointTensor_surjective (t : ↑(pullback f g))
    (h : (f.residueFieldMap (pullback.fst f g t)).hom.IsIntegral) :
    Function.Surjective (ofPointTensor t) := by
  -- At every point `p` of `Spec (κ(x) ⊗[κ(s)] κ(y))` the residue field `κ(p)` is a quotient of
  -- the tensor product, as `p` is maximal, and it factors through `κ` of the image point.
  have key (T : Triplet f g) (hT : T.tensorInr.hom.IsIntegral) (p : Spec T.tensor) :
      Function.Surjective (ofPointTensor (T.SpecTensorTo p)) := by
    have := p.isPrime
    have hp : p.asIdeal.IsMaximal := by
      refine Ideal.isMaximal_of_isIntegral_of_isMaximal_comap _ hT p.asIdeal ?_
      rw [Ideal.eq_bot_of_prime (Ideal.comap _ p.asIdeal)]
      exact Ideal.bot_isMaximal
    have e := T.Spec_ofPointTensor_SpecTensorTo p
    rw [← Spec.map_residueFieldIso_inv_eq_fromSpecResidueField, ← Spec.map_comp, ← Spec.map_comp,
      ← Spec.map_comp, Spec.map_inj] at e
    intro z
    obtain ⟨w₀, hw₀⟩ := (ConcreteCategory.bijective_of_isIso
      (Spec.residueFieldIso T.tensor p).inv).2 (T.SpecTensorTo.residueFieldMap p z)
    obtain ⟨w, rfl⟩ := p.asIdeal.algebraMap_residueField_surjective w₀
    refine ⟨(Triplet.tensorCongr (T.ofPoint_SpecTensorTo p).symm).hom w,
      (T.SpecTensorTo.residueFieldMap p).hom.injective ?_⟩
    rw [← hw₀]
    exact congr($e w)
  -- Integrality is stable under cobase change, so `κ(y) ⟶ κ(x) ⊗[κ(s)] κ(y)` is integral.
  have : (RingHom.toMorphismProperty RingHom.IsIntegral).IsStableUnderCobaseChange :=
    RingHom.isStableUnderCobaseChange_toMorphismProperty_iff.mpr
      RingHom.isIntegral_isStableUnderBaseChange
  have := key (Triplet.ofPoint t) (MorphismProperty.pushout_inr
    (P := RingHom.toMorphismProperty RingHom.IsIntegral) _ _ (RingHom.IsIntegral.trans _ _
      (RingHom.isIntegral_of_surjective _ fun x ↦ ⟨x, rfl⟩) h)) (SpecOfPoint t)
  rwa [SpecTensorTo_SpecOfPoint] at this

/-- If `t` is a point of `X ×_S Y` over `x ∈ X` and `y ∈ Y`, and `κ(x)` is integral over
`κ(f x)`, then the residue field `κ(t)` is generated as a ring by the images of `κ(x)` and
`κ(y)`. -/
theorem closure_range_residueFieldMap_eq_top (t : ↑(pullback f g))
    (h : (f.residueFieldMap (pullback.fst f g t)).hom.IsIntegral) :
    Subring.closure (Set.range ((pullback.fst f g).residueFieldMap t) ∪
      Set.range ((pullback.snd f g).residueFieldMap t)) = ⊤ := by
  -- `κ(x) ⊗[κ(s)] κ(y)` is generated by the images of `κ(x)` and `κ(y)`, and `ofPointTensor t`
  -- is surjective and maps these images to those of the two residue field maps.
  have H : Subring.closure (Set.range (Triplet.ofPoint t).tensorInl.hom ∪
      Set.range (Triplet.ofPoint t).tensorInr.hom) = ⊤ :=
    CommRingCat.closure_range_union_range_eq_top_of_isPushout (.of_hasPushout _ _)
  have h₁ : (Triplet.ofPoint t).tensorInl ≫ ofPointTensor t =
      (pullback.fst f g).residueFieldMap t :=
    pushout.inl_desc _ _ _
  have h₂ : (Triplet.ofPoint t).tensorInr ≫ ofPointTensor t =
      (pullback.snd f g).residueFieldMap t :=
    pushout.inr_desc _ _ _
  rw [← (RingHom.range_eq_top (f := (ofPointTensor t).hom)).mpr (ofPointTensor_surjective t h),
    RingHom.range_eq_map, ← H, RingHom.map_closure, Set.image_union, ← Set.range_comp,
    ← Set.range_comp, ← RingHom.coe_comp, ← RingHom.coe_comp, ← CommRingCat.hom_comp,
    ← CommRingCat.hom_comp, h₁, h₂]
  -- `ConcreteCategory.hom` and `CommRingCat.Hom.hom` agree definitionally.
  rfl

/-- Let `t` be a point of `X ×_S Y` over `x ∈ X`, with `κ(x)` integral over `κ(f x)`, let `K ⟶ K'`
be rings, and let `ψ : κ(x) → κ(t)` be the residue field map of the first projection, as an
algebra map over `K`. If `κ(t)` is a `K'`-algebra, compatibly with `K`, and every element in the
image of the residue field map of the second projection comes from `K'`, then the induced
`K'`-algebra map `K' ⊗[K] κ(x) → κ(t)` is surjective. -/
theorem surjective_liftEquiv_residueFieldMap (t : ↑(pullback f g))
    (h : (f.residueFieldMap (pullback.fst f g t)).hom.IsIntegral) {K K' : Type*} [CommRing K]
    [CommRing K'] [Algebra K K'] [Algebra K ((pullback f g).residueField t)]
    [Algebra K' ((pullback f g).residueField t)]
    [IsScalarTower K K' ((pullback f g).residueField t)]
    [Algebra K (X.residueField (pullback.fst f g t))]
    (ψ : X.residueField (pullback.fst f g t) →ₐ[K] (pullback f g).residueField t)
    (hψ : ∀ l, ψ l = (pullback.fst f g).residueFieldMap t l)
    (hK' : ∀ z ∈ Set.range ((pullback.snd f g).residueFieldMap t),
      z ∈ Set.range (algebraMap K' ((pullback f g).residueField t))) :
    Function.Surjective (AlgHom.liftEquiv K K' _ _ ψ) := by
  set R := (AlgHom.liftEquiv K K' _ _ ψ).range
  have h₁ (l : X.residueField (pullback.fst f g t)) :
      (pullback.fst f g).residueFieldMap t l ∈ R :=
    (AlgHom.mem_range _).mpr ⟨1 ⊗ₜ l, by rw [AlgHom.liftEquiv_tmul, one_smul, hψ]⟩
  have h₂ (z : Y.residueField (pullback.snd f g t)) :
      (pullback.snd f g).residueFieldMap t z ∈ R := by
    obtain ⟨k, hk⟩ := hK' _ ⟨z, rfl⟩
    refine (AlgHom.mem_range _).mpr ⟨k ⊗ₜ 1, ?_⟩
    exact (AlgHom.liftEquiv_tmul _ _ _).trans <| ((congrArg (k • ·) (map_one ψ)).trans
      (Algebra.algebraMap_eq_smul_one k).symm).trans hk
  have hle := (Subring.closure_le (t := R.toSubring)).mpr
    (Set.union_subset (Set.range_subset_iff.mpr h₁) (Set.range_subset_iff.mpr h₂))
  rw [closure_range_residueFieldMap_eq_top t h] at hle
  exact fun z ↦ (AlgHom.mem_range _).mp (hle (Subring.mem_top z))

end AlgebraicGeometry.Scheme.Pullback

namespace AlgebraicGeometry.Scheme

universe u

variable {P X Y S : Scheme.{u}} {fst : P ⟶ X} {snd : P ⟶ Y} {f : X ⟶ S} {g : Y ⟶ S}

/-- In a pullback square of schemes whose second projection `snd` is injective, the fibre of `fst`
over `x` has the same cardinality as the fibre of `g` over `f x`: `snd` maps the first injectively
onto the second (Mathlib's `Scheme.image_preimage_eq_of_isPullback`). -/
theorem natCard_preimage_fst_singleton_of_isPullback (H : IsPullback fst snd f g)
    (hsnd : Function.Injective snd) (x : X) :
    Nat.card (fst ⁻¹' {x}) = Nat.card (g ⁻¹' {f x}) := by
  rw [← Nat.card_image_of_injective hsnd, Scheme.image_preimage_eq_of_isPullback H,
    Set.image_singleton]

end AlgebraicGeometry.Scheme

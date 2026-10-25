/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import TauCeti.RingTheory.Smooth.SeparablePoint

/-!
# Smooth schemes over a field have points over finite separable extensions

Let `X` be a nonempty scheme smooth over a field `k`. Then `X` has a point with values in a
finite separable extension `K` of `k`: a morphism `Spec K ⟶ X` over `k`. Equivalently, the base
change of `X` to `K` has a `K`-rational point. No perfectness hypothesis on `k` is needed, so
this applies for instance to smooth curves over the fraction field of a discrete valuation ring.

The point is a closed point of a nonempty affine open `U` of `X`: the ring `Γ(X, U)` is a nonzero
smooth `k`-algebra, so it has a maximal ideal with finite separable residue field
(`Algebra.Smooth.exists_isMaximal_isSeparable`).

## Main results

* `AlgebraicGeometry.Smooth.exists_finite_isSeparable_comp_eq`: a nonempty scheme smooth over a
  field `k` has a point with values in a finite separable extension of `k`.

## References

* [The Stacks Project, Tag 056U](https://stacks.math.columbia.edu/tag/056U)
-/

public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- A nonempty scheme smooth over a field `k` has a point with values in a finite separable
extension `K` of `k`, that is, a morphism `Spec K ⟶ X` over `Spec k`. -/
theorem Smooth.exists_finite_isSeparable_comp_eq {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [Smooth f] [Nonempty X] :
    ∃ (K : Type u) (_ : Field K) (_ : Algebra k K), Module.Finite k K ∧
      Algebra.IsSeparable k K ∧
      ∃ g : Spec (.of K) ⟶ X, g ≫ f = Spec.map (CommRingCat.ofHom (algebraMap k K)) := by
  obtain ⟨x⟩ := ‹Nonempty X›
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  have : Nonempty U := ⟨⟨x, hxU⟩⟩
  -- The ring of sections over a nonempty affine open `U` is a nonzero smooth `k`-algebra.
  let φ : k →+* Γ(X, U) :=
    (f.appLE ⊤ U le_top).hom.comp (Scheme.ΓSpecIso (.of k)).inv.hom
  have hφ : φ.Smooth :=
    (RingHom.Smooth.of_bijective
      (Scheme.ΓSpecIso (.of k)).commRingCatIsoToRingEquiv.symm.bijective).comp
      (HasRingHomProperty.appLE @Smooth f ‹_› ⟨⊤, isAffineOpen_top _⟩ ⟨U, hU⟩ le_top)
  algebraize [φ]
  obtain ⟨m, hm, hfin, hsep⟩ := Algebra.Smooth.exists_isMaximal_isSeparable k Γ(X, U)
  let := Ideal.Quotient.field m
  refine ⟨Γ(X, U) ⧸ m, inferInstance, inferInstance, hfin, hsep,
    Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk m)) ≫ hU.fromSpec, ?_⟩
  -- The point is the closed point `m` of `Spec Γ(X, U) ≅ U`, and `Spec Γ(X, U) ⟶ Spec k` is induced
  -- by `φ`.
  rw [Category.assoc, ← IsAffineOpen.SpecMap_appLE_fromSpec f (isAffineOpen_top _) hU le_top,
    IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv, ← Spec.map_comp, ← Spec.map_comp]
  -- Both ring maps `k → Γ(X, U) ⧸ m` are `Ideal.Quotient.mk m ∘ φ`, by definition of the algebra
  -- structures.
  rfl

end AlgebraicGeometry

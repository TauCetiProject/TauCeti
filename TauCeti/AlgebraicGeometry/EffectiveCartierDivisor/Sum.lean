/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EffectiveCartierDivisor.Relative
import Mathlib.AlgebraicGeometry.Morphisms.RingHomProperties

/-!
# Sums of relative effective Cartier divisors

The sum of effective Cartier divisors is represented by the product of their ideal sheaves.
On a flat scheme over a base, sums of relative effective Cartier divisors are again relative
effective Cartier. In particular, the multiples of a section divisor on a smooth relative curve
remain relative effective Cartier, even when the sections coincide or the base is nonreduced.
The absolute closure results `TauCeti.isEffectiveCartier_mul`, `TauCeti.isEffectiveCartier_pow`,
and `TauCeti.isEffectiveCartier_prod` are provided by
`TauCeti.AlgebraicGeometry.EffectiveCartierDivisor.Basic`. This module proves their relative
counterparts: `TauCeti.isRelativeEffectiveCartier_mul` gives binary sums,
`TauCeti.isRelativeEffectiveCartier_pow` gives multiples, and
`TauCeti.isRelativeEffectiveCartier_prod` gives finite sums.

## References

* Stacks Project, *Divisors*, Effective Cartier divisors and Relative effective Cartier divisors.
* N. M. Katz and B. Mazur, *Arithmetic Moduli of Elliptic Curves*, §1.1.
-/

public section

open CategoryTheory Limits

universe u

namespace TauCeti

open AlgebraicGeometry AlgebraicGeometry.Scheme.IdealSheafData

variable {X S : Scheme.{u}}

/-- On a flat ambient scheme, the sum of two relative effective Cartier divisors is relative
effective Cartier. No disjointness, reducedness, or noetherian hypothesis is needed. -/
theorem isRelativeEffectiveCartier_mul {I J : X.IdealSheafData} {f : X ⟶ S} [Flat f]
    (hI : I.IsRelativeEffectiveCartier f) (hJ : J.IsRelativeEffectiveCartier f) :
    (I * J).IsRelativeEffectiveCartier f := by
  refine (isRelativeEffectiveCartier_iff _ _).mpr
    ⟨isEffectiveCartier_mul hI.isEffectiveCartier hJ.isEffectiveCartier, ?_⟩
  let _ := hI.flat
  let _ := hJ.flat
  -- Specify the ring property because the general locality instances do not infer it here.
  let : IsZariskiLocalAtSource (@Flat.{u}) :=
    HasRingHomProperty.instIsZariskiLocalAtSource (Q := @RingHom.Flat)
  let : IsZariskiLocalAtTarget (@Flat.{u}) :=
    HasRingHomProperty.instIsZariskiLocalAtTarget (@Flat.{u}) (Q := @RingHom.Flat)
  let : MorphismProperty.RespectsRight (@Flat.{u}) (@IsOpenImmersion.{u}) :=
    MorphismProperty.Respects.toRespectsRight
  -- Flatness is local around each point of the sum divisor, on both source and base.
  apply (IsZariskiLocalAtSource.iff_exists_resLE (P := @Flat.{u})).mpr
  intro x
  obtain ⟨_, ⟨W, hW, rfl⟩, hxW, -⟩ := S.isBasis_affineOpens.exists_subset_of_mem_open
    (Set.mem_univ (f ((I * J).subschemeι x))) isOpen_univ
  replace hW : IsAffineOpen W := hW
  obtain ⟨U, hUW, hxU, a, ha, hIa⟩ :=
    hI.isEffectiveCartier.exists_eq_span_singleton_le (f ⁻¹ᵁ W) hxW
  obtain ⟨V, hVU, hxV, b, hb, hJb⟩ :=
    hJ.isEffectiveCartier.exists_eq_span_singleton_le U.1 hxU
  have hVW : V.1 ≤ f ⁻¹ᵁ W := hVU.trans hUW
  let a' := X.presheaf.map (homOfLE hVU).op a
  have ha' : IsSMulRegular Γ(X, V) a' := U.2.isSMulRegular_map hVU ha
  have hIa' : I.ideal V = Ideal.span {a'} := by
    rw [← I.map_ideal hVU, hIa, Ideal.map_span, Set.image_singleton]
    rfl
  refine ⟨W, (I * J).subschemeι ⁻¹ᵁ V.1, hxV,
    (Scheme.Hom.preimage_mono _ hVW).trans_eq rfl, ?_⟩
  rw [flat_resLE_subschemeι_iff hW V hVW]
  let _ : Algebra Γ(S, W) Γ(X, V) := (f.appLE W V hVW).hom.toAlgebra
  have : Module.Flat Γ(S, W) Γ(X, V) := f.flat_appLE hW V.2 hVW
  -- The two quotient algebras are flat over the same affine base; apply the product criterion.
  have hflatI := I.flat_appLE_comp_ofHom_quotient_mk f hW V hVW
  have hflatJ := J.flat_appLE_comp_ofHom_quotient_mk f hW V hVW
  rw [hIa'] at hflatI
  rw [hJb] at hflatJ
  have hmap (c : Γ(X, V)) :
      algebraMap Γ(S, W) (Γ(X, V) ⧸ Ideal.span {c}) =
        (f.appLE W V hVW ≫ CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {c}))).hom := by
    rw [IsScalarTower.algebraMap_eq Γ(S, W) Γ(X, V), Ideal.Quotient.algebraMap_eq,
      RingHom.algebraMap_toAlgebra, CommRingCat.hom_comp, CommRingCat.hom_ofHom]
  have : Module.Flat Γ(S, W) (Γ(X, V) ⧸ Ideal.span {a'}) := by
    rw [← RingHom.flat_algebraMap_iff, hmap]
    exact hflatI
  have : Module.Flat Γ(S, W) (Γ(X, V) ⧸ Ideal.span {b}) := by
    rw [← RingHom.flat_algebraMap_iff, hmap]
    exact hflatJ
  have hflat := flat_quotient_span_singleton_mul (R := Γ(S, W)) ha' hb
  rw [← RingHom.flat_algebraMap_iff, hmap] at hflat
  have hIJ : (I * J).ideal V = Ideal.span {a' * b} := by
    simp only [ideal_mul, Pi.mul_apply, hIa', hJb, Ideal.span_singleton_mul_span_singleton]
  rw [hIJ]
  exact hflat

/-- Every nonnegative multiple of a relative effective Cartier divisor on a flat ambient scheme
is relative effective Cartier. This includes the empty divisor for multiplicity zero. -/
theorem isRelativeEffectiveCartier_pow {I : X.IdealSheafData} {f : X ⟶ S} [Flat f]
    (hI : I.IsRelativeEffectiveCartier f) (n : ℕ) :
    (I ^ n).IsRelativeEffectiveCartier f := by
  induction n with
  | zero => simp
  | succ n hn => simpa only [pow_succ] using isRelativeEffectiveCartier_mul hn hI

/-- A finite sum of relative effective Cartier divisors on a flat ambient scheme is relative
effective Cartier, with no restriction on intersections between the summands. -/
theorem isRelativeEffectiveCartier_prod {ι : Type*} {s : Finset ι} {I : ι → X.IdealSheafData}
    {f : X ⟶ S} [Flat f] (hI : ∀ i ∈ s, (I i).IsRelativeEffectiveCartier f) :
    (∏ i ∈ s, I i).IsRelativeEffectiveCartier f := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi hs =>
    rw [Finset.prod_insert hi]
    exact isRelativeEffectiveCartier_mul (hI i (Finset.mem_insert_self i s))
      (hs fun j hj ↦ hI j (Finset.mem_insert_of_mem hj))

end TauCeti

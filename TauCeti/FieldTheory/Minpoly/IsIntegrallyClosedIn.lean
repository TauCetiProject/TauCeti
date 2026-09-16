/-
Copyright (c) 2026 Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.LinearDisjoint
public import Mathlib.FieldTheory.PrimitiveElement
public import Mathlib.RingTheory.Polynomial.IsIntegral

/-!
# Minimal polynomials over a relatively algebraically closed base field

Let `F / k` be a field extension in which `k` is relatively algebraically closed, that is,
`IsIntegrallyClosedIn k F` — equivalently `algebraicClosure k F = ⊥` — and let `E` be a further
commutative `F`-algebra.  An element `x` of `E` algebraic over `k` then has the same minimal
polynomial over `F` as over `k`: the coefficients of `minpoly F x` are integral over `k`, because
that polynomial divides the monic polynomial `(minpoly k x).map (algebraMap k F)`, and relative
algebraic closedness puts them back into `k`.

Consequently, for `E` a field, `F⟮x⟯ / F` and `k⟮x⟯ / k` have the same degree.  This is the
mechanism behind the degree behaviour of a constant field extension: adjoining constants to `F`
costs exactly what adjoining them to `k` costs. More strongly, every finite separable extension
of `k` inside `E` is linearly disjoint from `F`, so a family of constants linearly independent
over `k` stays linearly independent over `F`.

## Main results

* `TauCeti.minpoly.map_algebraMap_of_isIntegrallyClosedIn`: `minpoly F x` is the image of
  `minpoly k x`.
* `TauCeti.IntermediateField.finrank_adjoin_simple_eq_finrank_adjoin_simple_of_isIntegrallyClosedIn`
  : `[F⟮x⟯ : F] = [k⟮x⟯ : k]`.
* `TauCeti.linearDisjoint_fieldRange_of_isIntegrallyClosedIn`: a finite separable extension of
  `k` inside a common overfield is linearly disjoint from `F`.
* `TauCeti.linearIndependent_algebraMap_of_isIntegrallyClosedIn`: linear independence in that
  extension persists after extending scalars from `k` to `F`.

## References

* H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., GTM 254, Springer, 2009,
  Section III.6.  This is the field theory behind the persistence of linear independence under a
  constant field extension (Proposition 3.6.1(b)); it is stated here for an arbitrary extension
  `F / k` with `k` relatively algebraically closed, with no function field involved.
-/

public section

open IntermediateField Polynomial

namespace TauCeti

universe u v w

variable {k : Type u} {F : Type v} {E : Type w} [Field k] [Field F] [Algebra k F]

section CommRing

variable [CommRing E] [Algebra k E] [Algebra F E] [IsScalarTower k F E]

/-- If `k` is relatively algebraically closed in `F`, then an element of an extension of `F` that
is algebraic over `k` has the same minimal polynomial over `F` as over `k`.

Without the hypothesis only the divisibility `minpoly F x ∣ (minpoly k x).map (algebraMap k F)`
holds; the content is that the coefficients of the left-hand factor, being integral over `k` and
lying in `F`, are constants. -/
theorem minpoly.map_algebraMap_of_isIntegrallyClosedIn (hex : IsIntegrallyClosedIn k F) {x : E}
    (hx : IsIntegral k x) : (minpoly k x).map (algebraMap k F) = minpoly F x := by
  -- make the exactness hypothesis available to instance search
  have := hex
  -- the coefficients of `minpoly F x` are integral over `k`, hence constants
  refine minpoly.map_algebraMap hx ((Polynomial.lifts_iff_coeff_lifts _).2 fun n ↦
    IsIntegrallyClosedIn.isIntegral_iff.1 ?_)
  exact Polynomial.isIntegral_coeff_of_dvd _ _ (minpoly.monic hx) (minpoly.monic hx.tower_top)
    (minpoly.dvd_map_of_isScalarTower k F x) n

end CommRing

section Field

variable [Field E] [Algebra k E] [Algebra F E] [IsScalarTower k F E]

/-- If `k` is relatively algebraically closed in `F`, then adjoining an element algebraic over `k`
to `F` raises the degree by exactly as much as adjoining it to `k` does. -/
theorem IntermediateField.finrank_adjoin_simple_eq_finrank_adjoin_simple_of_isIntegrallyClosedIn
    (hex : IsIntegrallyClosedIn k F) {x : E} (hx : IsIntegral k x) :
    Module.finrank F F⟮x⟯ = Module.finrank k k⟮x⟯ := by
  rw [adjoin.finrank hx.tower_top, adjoin.finrank hx,
    ← minpoly.map_algebraMap_of_isIntegrallyClosedIn hex hx,
    Polynomial.natDegree_map_eq_of_injective (algebraMap k F).injective]

/-! ### Linear disjointness from a finite separable extension -/

variable {k' : Type*} [Field k'] [Algebra k k'] [Algebra k' E]
variable [IsScalarTower k k' E]

/-- A finite separable extension of a relatively algebraically closed field `k` is linearly
disjoint from `F` inside any common overfield `E`.

This is the field-theoretic content of Stichtenoth, Proposition 3.6.1(b), for finite constant
extensions. Exactness of `k` in `F` keeps the minimal polynomial of a primitive element
irreducible after extending scalars to `F`; its powers therefore remain a basis-sized linearly
independent family. -/
theorem linearDisjoint_fieldRange_of_isIntegrallyClosedIn
    (hex : IsIntegrallyClosedIn k F) [FiniteDimensional k k'] [Algebra.IsSeparable k k'] :
    (IsScalarTower.toAlgHom k k' E).fieldRange.LinearDisjoint F := by
  let pb : PowerBasis k k' := Field.powerBasisOfFiniteOfSeparable k k'
  let e : k' ≃ₐ[k] (IsScalarTower.toAlgHom k k' E).fieldRange :=
    (IsScalarTower.toAlgHom k k' E).equivFieldRange
  let x : E := algebraMap k' E pb.gen
  have hx : IsIntegral k x :=
    pb.isIntegral_gen.map (IsScalarTower.toAlgHom k k' E)
  have hminpoly : minpoly k x = minpoly k pb.gen :=
    minpoly.algebraMap_eq (algebraMap k' E).injective pb.gen
  have hdegree : (minpoly F x).natDegree = pb.dim := by
    rw [← minpoly.map_algebraMap_of_isIntegrallyClosedIn hex hx,
      Polynomial.natDegree_map_eq_of_injective (algebraMap k F).injective, hminpoly,
      pb.natDegree_minpoly]
  let b : Module.Basis (Fin (minpoly F x).natDegree) k
      (IsScalarTower.toAlgHom k k' E).fieldRange :=
    (pb.basis.map e.toLinearEquiv).reindex (finCongr hdegree.symm)
  refine IntermediateField.LinearDisjoint.of_basis_left b ?_
  simpa [b, e, x, PowerBasis.coe_basis, Function.comp_def, Module.Basis.reindex_apply] using
    (linearIndependent_pow (K := F) x)

/-- A linearly independent family in a finite separable extension of a relatively algebraically
closed field `k` remains linearly independent after extending scalars to `F` inside a common
overfield.

For an algebraic function field and a finite separable constant extension, this is Stichtenoth,
Proposition 3.6.1(b). -/
theorem linearIndependent_algebraMap_of_isIntegrallyClosedIn
    (hex : IsIntegrallyClosedIn k F) [FiniteDimensional k k'] [Algebra.IsSeparable k k']
    {ι : Type*} {v : ι → k'} (hv : LinearIndependent k v) :
    LinearIndependent F (algebraMap k' E ∘ v) := by
  let e : k' ≃ₐ[k] (IsScalarTower.toAlgHom k k' E).fieldRange :=
    (IsScalarTower.toAlgHom k k' E).equivFieldRange
  have he : LinearIndependent k (e ∘ v) := hv.map' e.toLinearMap e.toLinearEquiv.ker
  have h := (linearDisjoint_fieldRange_of_isIntegrallyClosedIn hex).linearIndependent_left he
  simpa [e, Function.comp_def] using h

end Field

end TauCeti

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.FunctionField.Place.Extension.Unramified
public import TauCeti.FieldTheory.FunctionField.Place.RatFunc.Basic
import TauCeti.FieldTheory.FunctionField.Place.Extension.Equiv
import TauCeti.FieldTheory.FunctionField.Place.Extension.Existence
import TauCeti.FieldTheory.RatFunc.Transcendental

/-!
# Algebraic Belyi pairs

A *Belyi map* is a finite map from a curve to the projective line that is unramified outside
`t = 0`, `t = 1` and `t = ∞`. In the language of function fields, over a field `k` of
characteristic zero, an **algebraic Belyi pair** is a function field `F / k` with exact constant
field `k`, together with a finite embedding `k(t) ↪ F` of the rational function field, such that
every place of `F` lying over a place of `k(t)` other than the three marked places `t = 0`,
`t = 1` and `t = ∞` has ramification index `1`. The embedding is recorded as an
`Algebra (RatFunc k) F` structure, with `F` finite over `RatFunc k`; the degree of the Belyi map is
`Module.finrank (RatFunc k) F`.

The three marked places are the finite places of the monic irreducibles `t` and `t - 1`, and the
place at infinity (`TauCeti.Place.zeroOneInfty`). The definition asks only that the branch locus
be *contained* in them: a Belyi map need not ramify over all three points.

In characteristic zero the extension `F / k(t)` is automatically separable, and so are the
residue field extensions at all places. Hence `F` is an algebraic Belyi pair exactly when every
place of `k(t)` outside the three marked places is unramified in `F` in Stichtenoth's sense
(`TauCeti.isAlgebraicBelyiPair_iff`). Characteristic zero is also what makes the standard
examples behave: in characteristic `p` the map `t ↦ t ^ p` is inseparable, and `4t(1 - t)` is
constant in characteristic `2`.

The rational function field itself, with the identity embedding, is the Belyi pair of degree
one (`TauCeti.isAlgebraicBelyiPair_ratFunc`). Being a Belyi pair is invariant under
isomorphisms over `k(t)`, and more generally under a commutative square of isomorphisms whose
automorphism of `k(t)` permutes the three marked places
(`TauCeti.IsAlgebraicBelyiPair.of_equiv_equiv`); the six automorphisms permuting them are in
`TauCeti.FieldTheory.FunctionField.Belyi.BranchPoints`. Radical examples
`y ^ n = c t ^ a (t - 1) ^ b`, among them the power maps, are in
`TauCeti.FieldTheory.FunctionField.Belyi.Radical`.

## Main definitions

* `TauCeti.Place.zeroOneInfty`: the places `t = 0`, `t = 1` and `t = ∞` of `k(t)`, and
  `TauCeti.Place.markedPlace`, the same places numbered `0`, `1` and `2`.
* `TauCeti.IsAlgebraicBelyiPair`: `F / k(t)` is an algebraic Belyi pair.

## Main results

* `TauCeti.isAlgebraicBelyiPair_iff`: the characterization by unramified places.
* `TauCeti.isAlgebraicBelyiPair_ratFunc`: `k(t)` over itself is an algebraic Belyi pair.
* `TauCeti.IsAlgebraicBelyiPair.of_equiv_equiv` and `TauCeti.IsAlgebraicBelyiPair.of_algEquiv`:
  transport along isomorphisms.

## References

* E. Girondo and G. González-Diez, *Introduction to Compact Riemann Surfaces and Dessins
  d'Enfants*, LMS Student Texts 79, Cambridge University Press, 2012, Chapter 3.
* H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., GTM 254, Springer, 2009,
  Definitions 3.1.5 and 3.1.13.
-/

public section

open Polynomial

namespace TauCeti

namespace Place

variable (k : Type*) [Field k]

/-- The **three marked places** of the rational function field `k(t)`: the places `t = 0` and
`t = 1` of the monic irreducibles `t` and `t - 1`, and the place `t = ∞` at infinity. A Belyi map
is unramified over every other place. -/
noncomputable def zeroOneInfty : Set (Place k (RatFunc k)) :=
  {adicOfIrreducible (irreducible_X (R := k)), adicOfIrreducible (irreducible_X_sub_C (1 : k)),
    infty k}

variable {k}

theorem mem_zeroOneInfty_iff {P : Place k (RatFunc k)} :
    P ∈ zeroOneInfty k ↔ P = adicOfIrreducible (irreducible_X (R := k)) ∨
      P = adicOfIrreducible (irreducible_X_sub_C (1 : k)) ∨ P = infty k :=
  Iff.rfl

@[simp]
theorem adicOfIrreducible_X_mem_zeroOneInfty :
    adicOfIrreducible (irreducible_X (R := k)) ∈ zeroOneInfty k :=
  Or.inl rfl

@[simp]
theorem adicOfIrreducible_X_sub_one_mem_zeroOneInfty :
    adicOfIrreducible (irreducible_X_sub_C (1 : k)) ∈ zeroOneInfty k :=
  Or.inr (Or.inl rfl)

@[simp]
theorem infty_mem_zeroOneInfty : infty k ∈ zeroOneInfty k :=
  Or.inr (Or.inr rfl)

variable (k) in
/-- The three marked places `t = 0`, `t = 1` and `t = ∞` of `k(t)`, numbered `0`, `1` and `2`:
the numbering of the branch points used for permutation triples. -/
noncomputable def markedPlace : Fin 3 → Place k (RatFunc k) :=
  ![adicOfIrreducible (irreducible_X (R := k)), adicOfIrreducible (irreducible_X_sub_C (1 : k)),
    infty k]

@[simp]
theorem markedPlace_zero : markedPlace k 0 = adicOfIrreducible (irreducible_X (R := k)) :=
  (rfl)

@[simp]
theorem markedPlace_one : markedPlace k 1 = adicOfIrreducible (irreducible_X_sub_C (1 : k)) :=
  (rfl)

@[simp]
theorem markedPlace_two : markedPlace k 2 = infty k :=
  (rfl)

variable (k) in
/-- The numbered marked places are exactly the three marked places. -/
theorem range_markedPlace : Set.range (markedPlace k) = zeroOneInfty k := by
  ext P
  simp [mem_zeroOneInfty_iff, Fin.exists_fin_succ, eq_comm]

end Place

/-- An **algebraic Belyi pair** over a field `k` of characteristic zero: a function field `F / k`
with exact constant field `k`, finite over the rational function field `k(t)` through the given
`Algebra (RatFunc k) F` structure, in which every place lying over a place of `k(t)` other than
`t = 0`, `t = 1` and `t = ∞` has ramification index `1`.

The branch locus is only required to be contained in the three marked places. The base field is
pinned to characteristic zero, where `F / k(t)` is automatically separable; in characteristic `p`
the power map `t ↦ t ^ p` is inseparable and `4t(1 - t)` is constant in characteristic `2`. -/
structure IsAlgebraicBelyiPair (k F : Type*) [Field k] [CharZero k] [Field F] [Algebra k F]
    [Algebra (RatFunc k) F] [IsScalarTower k (RatFunc k) F] [FiniteDimensional (RatFunc k) F] :
    Prop where
  /-- The constant field of `F` is exactly `k`. -/
  isIntegrallyClosedIn : IsIntegrallyClosedIn k F
  /-- Every place of `F` over a place of `k(t)` other than `0`, `1`, `∞` is unramified. -/
  ramificationIdx_eq_one {P : Place k F} :
    P.restrict k (RatFunc k) ∉ Place.zeroOneInfty k → Place.ramificationIdx (RatFunc k) P = 1

variable {k F : Type*} [Field k] [CharZero k] [Field F] [Algebra k F] [Algebra (RatFunc k) F]
  [IsScalarTower k (RatFunc k) F] [FiniteDimensional (RatFunc k) F]

/-- **An algebraic Belyi pair is a function field unramified outside `0`, `1` and `∞`**: `F` is
an algebraic Belyi pair exactly when its constant field is `k` and every place of `k(t)` other
than the three marked places is unramified in `F`. In characteristic zero the residue field
extensions are separable, so being unramified is just having ramification index `1` at every
place above, of which there is at least one. -/
theorem isAlgebraicBelyiPair_iff :
    IsAlgebraicBelyiPair k F ↔ IsIntegrallyClosedIn k F ∧
      ∀ P ∉ Place.zeroOneInfty k, P.IsUnramified (k' := k) (F' := F) := by
  -- In characteristic zero the residue fields have characteristic zero, hence are perfect.
  have hsep (P' : Place k F) :
      Algebra.IsSeparable (P'.restrict k (RatFunc k)).ResidueField P'.ResidueField :=
    have : CharZero (P'.restrict k (RatFunc k)).ResidueField :=
      charZero_of_injective_algebraMap (algebraMap k _).injective
    inferInstance
  refine ⟨fun h ↦ ⟨h.isIntegrallyClosedIn, fun P hP ↦ (Place.isUnramified_iff P).mpr ⟨?_,
    fun P' hP' ↦ ⟨h.ramificationIdx_eq_one (hP' ▸ hP), hsep P'⟩⟩⟩,
    fun ⟨hex, h⟩ ↦ ⟨hex, fun hP ↦ (h _ hP).ramificationIdx_eq_one rfl⟩⟩
  exact Place.restrict_surjective_of_finiteDimensional (IsFunctionField.ratFunc k)
    (isFunctionField_iff_functionField.mpr inferInstance) P

variable {F' : Type*} [Field F'] [Algebra k F'] [Algebra (RatFunc k) F']
  [IsScalarTower k (RatFunc k) F'] [FiniteDimensional (RatFunc k) F']

/-- **Transport of Belyi pairs along a commutative square of isomorphisms.** Let
`σ : k(t) ≃ₐ[k] k(t)` carry the three marked places into themselves, and let `e : F ≃ₐ[k] F'`
restrict to `σ` on `k(t)`. If `F` is an algebraic Belyi pair then so is `F'`.

For `F' = F` as fields, this changes the Belyi function `t` of `F` into its image under an
automorphism of `k(t)`; see `TauCeti.IsAlgebraicBelyiPair.of_branchPointAut`. -/
theorem IsAlgebraicBelyiPair.of_equiv_equiv (h : IsAlgebraicBelyiPair k F)
    (σ : RatFunc k ≃ₐ[k] RatFunc k)
    (hσ : Set.MapsTo (Place.map σ) (Place.zeroOneInfty k) (Place.zeroOneInfty k))
    (e : F ≃ₐ[k] F') (he : ∀ x, e (algebraMap (RatFunc k) F x) = algebraMap (RatFunc k) F' (σ x)) :
    IsAlgebraicBelyiPair k F' where
  isIntegrallyClosedIn := by
    have := h.isIntegrallyClosedIn
    refine isIntegrallyClosedIn_iff.mpr ⟨(algebraMap k F').injective, fun {x} hx ↦ ?_⟩
    obtain ⟨c, hc⟩ := IsIntegrallyClosedIn.algebraMap_eq_of_integral (hx.map (e.symm : F' →ₐ[k] F))
    exact ⟨c, by rw [← e.commutes, hc]; exact e.apply_symm_apply x⟩
  ramificationIdx_eq_one {P'} hP' := by
    obtain ⟨Q, rfl⟩ : ∃ Q : Place k F, Q.map e = P' := ⟨P'.map e.symm, Place.map_map_symm e P'⟩
    rw [Place.ramificationIdx_map e σ.toRingEquiv he]
    refine h.ramificationIdx_eq_one fun hQ ↦ hP' ?_
    rw [Place.restrict_map e σ he]
    exact hσ hQ

/-- **Being an algebraic Belyi pair is invariant under isomorphism over `k(t)`.** -/
theorem IsAlgebraicBelyiPair.of_algEquiv (h : IsAlgebraicBelyiPair k F)
    (e : F ≃ₐ[RatFunc k] F') : IsAlgebraicBelyiPair k F' :=
  h.of_equiv_equiv AlgEquiv.refl (fun P hP ↦ by rwa [Place.map_refl]) (e.restrictScalars k)
    e.commutes

variable (k) in
/-- **The trivial Belyi pair**: the rational function field `k(t)` over itself, the Belyi map of
degree one, is an algebraic Belyi pair. -/
theorem isAlgebraicBelyiPair_ratFunc : IsAlgebraicBelyiPair k (RatFunc k) where
  isIntegrallyClosedIn := isIntegrallyClosedIn_ratFunc
  ramificationIdx_eq_one {P} _ := Place.ramificationIdx_self P

end TauCeti

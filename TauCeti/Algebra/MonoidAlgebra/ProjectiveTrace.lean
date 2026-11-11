/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.Projective
public import Mathlib.LinearAlgebra.Trace
public import Mathlib.RepresentationTheory.Basic
public import Mathlib.RingTheory.LocalRing.Basic
import TauCeti.Algebra.Module.Projective.Trans
import TauCeti.Algebra.MonoidAlgebra.CosetBasis
import TauCeti.Algebra.MonoidAlgebra.LocalRing
import TauCeti.Algebra.MonoidAlgebra.MapDomain
import TauCeti.Algebra.MonoidAlgebra.Trace
import TauCeti.GroupTheory.OrderOfElement.PPart
import TauCeti.LinearAlgebra.End.Basic
import TauCeti.LinearAlgebra.Matrix.FiniteOrder
import TauCeti.RingTheory.LocalRing.Basic
import TauCeti.RingTheory.LocalRing.Module

/-!
# Characters of projective modules vanish at `p`-singular elements

Let `A` be a commutative local ring in which the prime `p` is not a unit (for instance `ℤ_p`, or a
field of characteristic `p`), let `G` be a finite group and let `X` be a finitely generated
projective `A[G]`-module. Then every element `g ∈ G` whose order is divisible by `p` acts on `X`
with trace zero.

The proof restricts `X` to the group algebra `A[Q]` of the `p`-part `Q = ⟨q⟩` of `⟨g⟩`, where
`g = s * q` with `q ≠ 1` of `p`-power order and `s` of order `m` prime to `p`, both powers of `g`.
The ring `A[Q]` is local, and `A[G]` is free over it, so `X` is a free `A[Q]`-module of finite
rank. The element `s` commutes with `Q`, so it acts `A[Q]`-linearly, with `s ^ m = 1`; as `m` is a
unit in `A`, its `A[Q]`-trace is a constant `c ∈ A`. Then `g` acts as the scalar `q` times `s`,
and the `A`-trace is the algebra trace `Tr_{A[Q]/A}(q * c) = c * |Q| * [q = 1] = 0`.

With `A = ℤ_p` this is the vanishing of the characters of projective `ℤ_p[G]`-modules away from the
`p`-regular elements, one of the inputs to Swan's theorem that a finitely generated projective
`ℤ_p[G]`-module is determined by its rationalization (NSW (5.6.10)(ii)).

## Main results

* `TauCeti.trace_ofModule'_eq_zero_of_dvd_orderOf`: the trace of `g` on a finitely generated
  projective `A[G]`-module vanishes when `p` divides the order of `g`.

## References

* J.-P. Serre, *Linear Representations of Finite Groups*, Part III (Brauer theory: projective
  `A[G]`-modules and their characters).
* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, second edition,
  Proposition (5.6.10).
-/

public section

namespace TauCeti

open _root_.MonoidAlgebra

variable {A : Type*} [CommRing A] [IsLocalRing A] {p : ℕ} [Fact p.Prime] {G : Type*} [Group G]
  [Finite G] (X : Type*) [AddCommMonoid X] [Module A X] [Module (MonoidAlgebra A G) X]
  [IsScalarTower A (MonoidAlgebra A G) X] [Module.Finite (MonoidAlgebra A G) X]
  [Module.Projective (MonoidAlgebra A G) X]

/-- **Characters of projective modules vanish at `p`-singular elements.** Let `A` be a local ring
in which the prime `p` is not a unit and `G` a finite group. If `p` divides the order of `g ∈ G`,
then `g` acts with trace zero on every finitely generated projective `A[G]`-module. -/
theorem trace_ofModule'_eq_zero_of_dvd_orderOf (hp : ¬IsUnit (p : A)) {g : G}
    (hg : p ∣ orderOf g) : LinearMap.trace A X (Representation.ofModule' X g) = 0 := by
  -- Write `g = s * q`, restrict `X` to a free module over the local ring `A[Q]`, `Q = ⟨q⟩`, on
  -- which `s` acts linearly with `s ^ m = 1`, and compute the trace of `g = q • s` along
  -- `A[Q] / A` with `LinearMap.trace_restrictScalars_smul_of_pow_eq_one`.
  classical
  let s := pFreePart p g
  let q := pPart p g
  have hmul : s * q = g := pFreePart_mul_pPart p g
  have hsq : Commute s q := commute_pFreePart_pPart p g
  have hq1 : q ≠ 1 := pPart_ne_one_of_dvd_orderOf Fact.out (orderOf_pos g).ne' hg
  have hQ : IsPGroup p (Subgroup.zpowers q) :=
    isPGroup_zpowers_pPart Fact.out (orderOf_pos g).ne'
  have hpm : ¬p ∣ orderOf s := not_dvd_orderOf_pFreePart Fact.out (orderOf_pos g).ne'
  rw [← hmul]
  -- Restrict `X` to the local group algebra `A[Q]` of `Q = ⟨q⟩`.
  let Q := Subgroup.zpowers q
  -- The commutative group structure of `Q`, with the same underlying monoid as its subgroup one.
  let _ : CommGroup Q := { (inferInstance : Group Q) with mul_comm := fun a b ↦ mul_comm' a b }
  let φ : MonoidAlgebra A Q →ₐ[A] MonoidAlgebra A G := mapDomainAlgHom A A Q.subtype
  let _ : Module (MonoidAlgebra A Q) (MonoidAlgebra A G) := (mapDomainRingHom A Q.subtype).toModule
  let _ : Module (MonoidAlgebra A Q) X := .compHom X (mapDomainRingHom A Q.subtype)
  have : IsScalarTower (MonoidAlgebra A Q) (MonoidAlgebra A G) X :=
    ⟨fun r y x ↦ mul_smul (φ r) y x⟩
  have : IsScalarTower (MonoidAlgebra A Q) (MonoidAlgebra A G) (MonoidAlgebra A G) :=
    ⟨fun r y z ↦ mul_assoc (φ r) y z⟩
  have : IsScalarTower A (MonoidAlgebra A Q) X :=
    ⟨fun a r x ↦ (congrArg (· • x) (map_smul φ a r)).trans (smul_assoc a (φ r) x)⟩
  let b := TauCeti.MonoidAlgebra.basisCosets A Q.subtype Q.subtype_injective
  have : Module.Free (MonoidAlgebra A Q) (MonoidAlgebra A G) := .of_basis b
  have : Module.Finite (MonoidAlgebra A Q) (MonoidAlgebra A G) := .of_basis b
  have : Module.Finite (MonoidAlgebra A Q) X := .trans (MonoidAlgebra A G) X
  have : Module.Projective (MonoidAlgebra A Q) X := .trans (MonoidAlgebra A G) X
  have : IsLocalRing (MonoidAlgebra A Q) := TauCeti.MonoidAlgebra.isLocalRing_of_isPGroup hp hQ
  have : IsLocalHom (MonoidAlgebra.lift A A Q 1) :=
    TauCeti.MonoidAlgebra.isLocalHom_lift_one_of_isPGroup hp hQ
  have : Module.Free (MonoidAlgebra A Q) X := Module.free_of_projective_of_isLocalRing
  -- The element `s` commutes with `Q`, so it acts `A[Q]`-linearly.
  let S := Q.subtype.singleSMulLinearMap (R := A)
    (by rintro ⟨_, j, rfl⟩; exact (hsq.zpow_right j).symm) X fun _ _ ↦ rfl
  have hS : S ^ orderOf s = 1 :=
    Module.End.pow_eq_one_of_apply_eq_smul S (MonoidHom.singleSMulLinearMap_apply _ _ _ _)
      (by rw [single_pow, one_pow, pow_orderOf_eq_one, one_def])
  -- The element `g = s * q` acts as the scalar `q ∈ A[Q]` times `S`.
  let q' : Q := ⟨q, Subgroup.mem_zpowers q⟩
  have hg' : Representation.ofModule' X (s * q) =
      ((single q' (1 : A) : MonoidAlgebra A Q) • S).restrictScalars A := by
    ext x
    -- Unfold the `A[Q]`-action on `X`: it is the `A[G]`-action through `φ`.
    change (single (s * q) (1 : A) : MonoidAlgebra A G) • x = φ (single q' (1 : A)) • S x
    rw [show S x = _ from MonoidHom.singleSMulLinearMap_apply _ _ _ _ x, ← mul_smul]
    simp [φ, q', single_mul_single, hsq.eq]
  have hm : IsUnit (orderOf s : A) :=
    (Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd Fact.out).mpr hpm)).isUnit_natCast hp
  have : Fintype Q := Fintype.ofFinite Q
  rw [hg', LinearMap.trace_restrictScalars_smul_of_pow_eq_one S (MonoidAlgebra.lift A A Q 1) hm hS,
    Algebra.trace_eq_matrix_trace (MonoidAlgebra.basis Q A), trace_leftMulMatrix]
  simp [Ne.symm (show q' ≠ 1 from fun h ↦ hq1 (congrArg Subtype.val h))]

end TauCeti

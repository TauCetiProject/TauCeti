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
import Mathlib.RingTheory.LocalRing.Module
import TauCeti.Algebra.Module.Projective.Trans
import TauCeti.Algebra.MonoidAlgebra.CosetBasis
import TauCeti.Algebra.MonoidAlgebra.LocalRing
import TauCeti.Algebra.MonoidAlgebra.Trace
import TauCeti.GroupTheory.OrderOfElement.PPart
import TauCeti.LinearAlgebra.Matrix.FiniteOrder
import TauCeti.RingTheory.LocalRing.Basic

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

/-- Every element `g` of a finite group whose order is divisible by `p` is a product `s * q` of
commuting elements, where `q ≠ 1` generates a `p`-group and the order of `s` is prime to `p`. -/
private theorem exists_commute_mul_eq_of_dvd_orderOf {p : ℕ} (hp : p.Prime) {G : Type*} [Group G]
    [Finite G] {g : G} (hg : p ∣ orderOf g) :
    ∃ s q : G, s * q = g ∧ Commute s q ∧ q ≠ 1 ∧ IsPGroup p (Subgroup.zpowers q) ∧
      ¬p ∣ orderOf s :=
  ⟨pFreePart p g, pPart p g, pFreePart_mul_pPart p g, commute_pFreePart_pPart p g,
    pPart_ne_one_of_dvd_orderOf hp (orderOf_pos g).ne' hg,
    isPGroup_zpowers_pPart hp (orderOf_pos g).ne', not_dvd_orderOf_pFreePart hp (orderOf_pos g).ne'⟩

/-- An element `s` commuting with the image of a monoid homomorphism `ι : Q →* G` commutes with the
image of every element of `A[Q]` in `A[G]`. -/
theorem mapDomainAlgHom_mul_single_comm {A : Type*} [CommSemiring A] {Q G : Type*} [Monoid Q]
    [Monoid G] (ι : Q →* G) {s : G} (hs : ∀ c, Commute s (ι c)) (r : MonoidAlgebra A Q) :
    mapDomainAlgHom A A ι r * single s 1 = single s 1 * mapDomainAlgHom A A ι r := by
  induction r using MonoidAlgebra.induction_linear with
  | zero => simp
  | add x y hx hy => rw [map_add, add_mul, mul_add, hx, hy]
  | single c a => simp [single_mul_single, (hs c).eq]

/-- If the `A[Q]`-module structure on `X` is the `A[G]`-action through `ι`, then the action of
`single s 1` for `s` commuting with the image of `ι` is `A[Q]`-linear. -/
theorem exists_linearMap_apply_eq_single_smul {A : Type*} [CommSemiring A] {Q G : Type*}
    [Monoid Q] [Monoid G] (ι : Q →* G) {s : G} (hs : ∀ c, Commute s (ι c)) (X : Type*)
    [AddCommMonoid X] [Module (MonoidAlgebra A G) X] [Module (MonoidAlgebra A Q) X]
    (hact : ∀ (r : MonoidAlgebra A Q) (x : X), r • x = mapDomainAlgHom A A ι r • x) :
    ∃ S : X →ₗ[MonoidAlgebra A Q] X, ∀ x, S x = (single s (1 : A) : MonoidAlgebra A G) • x :=
  ⟨{ toFun := fun x ↦ (single s (1 : A) : MonoidAlgebra A G) • x
     map_add' := smul_add _
     map_smul' := fun r x ↦ by
       rw [RingHom.id_apply, hact, hact, ← mul_smul, ← mul_smul,
         mapDomainAlgHom_mul_single_comm ι hs] }, fun _ ↦ rfl⟩

/-- The `k`-th power of an endomorphism acting as `single s 1` acts as `single (s ^ k) 1`. -/
theorem pow_apply_eq_single_pow_smul {A : Type*} [CommSemiring A] {G : Type*} [Monoid G]
    {R X : Type*} [Semiring R] [AddCommMonoid X] [Module R X] [Module (MonoidAlgebra A G) X]
    {s : G} (S : Module.End R X)
    (hS : ∀ x, S x = (single s (1 : A) : MonoidAlgebra A G) • x) (k : ℕ) (x : X) :
    (S ^ k) x = (single (s ^ k) (1 : A) : MonoidAlgebra A G) • x := by
  induction k with
  | zero => simp [← one_def]
  | succ k ih =>
    rw [pow_succ', mul_apply_eq_comp, ih, hS, pow_succ']
    exact (mul_smul _ _ x).symm.trans (by rw [single_mul_single, one_mul])

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
  obtain ⟨s, q, hmul, hsq, hq1, hQ, hpm⟩ := exists_commute_mul_eq_of_dvd_orderOf Fact.out hg
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
  have : Module.Projective (MonoidAlgebra A Q) X := .trans (S := MonoidAlgebra A G)
  have : IsLocalRing (MonoidAlgebra A Q) := TauCeti.MonoidAlgebra.isLocalRing_of_isPGroup hp hQ
  have : IsLocalHom (MonoidAlgebra.lift A A Q 1) :=
    TauCeti.MonoidAlgebra.isLocalHom_lift_one_of_isPGroup hp hQ
  -- `X` is a module over the ring `A[Q]`, so it carries the additive group structure that
  -- `Module.free_of_flat_of_isLocalRing` asks for.
  have : Module.Free (MonoidAlgebra A Q) X :=
    let _ := Module.addCommMonoidToAddCommGroup (MonoidAlgebra A Q) (M := X)
    Module.free_of_flat_of_isLocalRing
  -- The element `s` commutes with `Q`, so it acts `A[Q]`-linearly.
  have hcomm : ∀ c : Q, Commute s (Q.subtype c) := by
    rintro ⟨_, j, rfl⟩
    exact hsq.zpow_right j
  obtain ⟨S, hSapply⟩ := exists_linearMap_apply_eq_single_smul (A := A) Q.subtype hcomm X
    fun _ _ ↦ rfl
  have hS : S ^ orderOf s = 1 := LinearMap.ext fun x ↦ by
    rw [pow_apply_eq_single_pow_smul S hSapply, pow_orderOf_eq_one s, ← one_def, one_smul,
      one_apply_eq_self]
  -- The element `g = s * q` acts as the scalar `q ∈ A[Q]` times `S`.
  let q' : Q := ⟨q, Subgroup.mem_zpowers q⟩
  have hg' : Representation.ofModule' X (s * q) =
      ((single q' (1 : A) : MonoidAlgebra A Q) • S).restrictScalars A := by
    ext x
    -- Unfold both constructed actions; the `A[Q]`-action on `X` is the `A[G]`-action through `φ`.
    change (single (s * q) (1 : A) : MonoidAlgebra A G) • x =
      (single q' (1 : A) : MonoidAlgebra A Q) • S x
    rw [hSapply]
    change _ = φ (single q' (1 : A)) • (single s (1 : A) : MonoidAlgebra A G) • x
    rw [← mul_smul]
    simp [φ, q', single_mul_single, hsq.eq]
  have hm : IsUnit (orderOf s : A) :=
    (Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd Fact.out).mpr hpm)).isUnit_natCast hp
  have hq' : q' ≠ 1 := fun h ↦ hq1 (congrArg Subtype.val h)
  have : Fintype Q := Fintype.ofFinite Q
  rw [hg', LinearMap.trace_restrictScalars_smul_of_pow_eq_one S (MonoidAlgebra.lift A A Q 1) hm hS,
    Algebra.trace_eq_matrix_trace (MonoidAlgebra.basis Q A), trace_leftMulMatrix]
  simp [hq'.symm]

end TauCeti

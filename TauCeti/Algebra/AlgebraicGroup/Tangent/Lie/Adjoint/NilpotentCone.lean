/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Representation.Comodule.Dual
public import TauCeti.Algebra.AlgebraicGroup.Representation.Fixed
public import TauCeti.Algebra.AlgebraicGroup.Representation.Orbit.Invariants
public import TauCeti.Algebra.AlgebraicGroup.Tangent.FiniteType
public import TauCeti.Algebra.AlgebraicGroup.Tangent.Lie.Adjoint.BasePoints
public import TauCeti.Algebra.AlgebraicGroup.Tangent.Lie.Adjoint.Differential
public import TauCeti.Algebra.AlgebraicGroup.Representation.ComoduleAlgebra
public import TauCeti.Algebra.Lie.AdjointAction.InvariantZeroLocus
public import TauCeti.Algebra.Lie.TracePowerPolynomial
public import TauCeti.Algebra.Lie.Reductive.InvariantZeroLocus
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import TauCeti.Algebra.AlgebraicGroup.Tangent.Lie.Adjoint.Fixed
import TauCeti.Algebra.Lie.Basic
import TauCeti.Algebra.Polynomial.Degree.Map

/-!
# The nilpotent cone of an affine group

Let `G = Spec H` be an affine group over a field `k` with finite-dimensional Lie algebra `𝔤`,
modelled as the dual of the augmentation cotangent space. The polynomial functions on `𝔤` are the
symmetric algebra `O(𝔤) = Sym(𝔤*)`, and `G` acts on them through the contragredient of the adjoint
representation (`TauCeti.adjointPolynomialComoduleAlgebra`). The invariant functions
`O(𝔤)^G` (`TauCeti.adjointInvariantPolynomials`) form the coordinate ring of the adjoint
quotient `χ : 𝔤 → 𝔤 // G`. The **nilpotent cone** is the scheme-theoretic zero fibre `χ⁻¹(0)`:
its ideal (`TauCeti.nilpotentConeIdeal`) is generated in `O(𝔤)` by the invariant functions
vanishing at the origin, that is, it is the ideal `Subalgebra.symmetricAlgebraHilbertIdeal` of the
coinvariants of the comodule `𝔤*`. It is a homogeneous ideal, so the cone is stable under scaling,
and it is a subcomodule, so the cone is stable under the adjoint action of `G`
(`TauCeti.nilpotentConeSubcomodule`). The quotient ring is the full coordinate ring of the zero
fibre; no reduction is taken.

Adjoint-invariant polynomials are constant on rational adjoint orbits and, for a finite-type group
over an algebraically closed field, across the closure order on `TauCeti.Comodule.VectorOrbit k H 𝔤`
(`TauCeti.lift_eval_basePointsRepresentation_of_mem_adjointInvariantPolynomials`,
`TauCeti.lift_eval_eq_of_mk_le_mk_of_mem_adjointInvariantPolynomials`), so the nilpotent cone is
closed under orbit specialization (`TauCeti.nilpotentConeIdeal_le_ker_lift_eval_of_mk_le_mk`), and
its rational orbits (`TauCeti.nilpotentConeOrbits`) form a downward-closed set
(`TauCeti.mem_nilpotentConeOrbits_of_le`). Similarly, the predicate
`TauCeti.Comodule.VectorOrbit.IsNilpotentAd` of `ad`-nilpotent rational adjoint orbits is downward
closed in the closure order (`TauCeti.Comodule.VectorOrbit.IsNilpotentAd.of_le`) without any
characteristic, connectedness, or Killing hypothesis, and the `k`-rational vectors
`{y : 𝔤 | mk y ≤ O}` whose orbit lies below an `ad`-nilpotent orbit `O` decompose into `O` together
with the union of all strictly smaller `ad`-nilpotent orbits
(`TauCeti.Comodule.VectorOrbit.setOf_mk_le_eq_union_biUnion_of_isNilpotentAd`).

The infinitesimal adjoint action of `x ∈ 𝔤` on `O(𝔤)` is the coadjoint action of `x` by
derivations (`TauCeti.differential_adjointPolynomialComoduleAlgebra`), so every group invariant is
a Lie invariant `S(𝔤*)^𝔤`. For a connected group over an algebraically closed field of
characteristic zero, a vector is fixed by the group exactly when the Lie algebra kills it, and the
two rings of invariants coincide (`TauCeti.adjointInvariantPolynomials_eq_lieInvariants`). When
the Killing form of `𝔤` is nondegenerate, the Lie-invariant functions of positive degree cut out the
`ad`-nilpotent elements (`TauCeti.isNilpotent_ad_iff_forall_lift_eval_eq_zero`). Hence the
`k`-points of the nilpotent cone are exactly the `ad`-nilpotent elements of `𝔤`
(`TauCeti.nilpotentConeIdeal_le_ker_lift_eval_iff`), and `TauCeti.nilpotentConeOrbits` coincides
with `{O | O.IsNilpotentAd}` (`TauCeti.nilpotentConeOrbits_eq_setOf_isNilpotentAd`). Each inclusion
holds under weaker hypotheses: `ad`-nilpotent elements lie on the cone for every group with
nondegenerate Killing form in characteristic zero, and points of the cone are `ad`-nilpotent for
every connected group over an algebraically closed field of characteristic zero.

When `𝔤` is only reductive, `𝔤 = Z(𝔤) ⊕ ⁅𝔤, 𝔤⁆`, the linear functions vanishing on `⁅𝔤, 𝔤⁆` are
invariants of degree one, and the cone is cut out inside `⁅𝔤, 𝔤⁆`: its `k`-points are the
`ad`-nilpotent elements of the derived ideal
(`TauCeti.nilpotentConeIdeal_le_ker_lift_eval_iff_mem_derivedSeries_and_isNilpotent_ad`). These
have zero central coordinate (`TauCeti.nilpotentConeIdeal_le_ker_lift_eval_add_iff`), whereas
the `ad`-nilpotent elements of `𝔤` form the larger set `Z(𝔤) × 𝒩(⁅𝔤, 𝔤⁆)`
(`TauCeti.isNilpotent_ad_iff_exists_mem_center_add_nilpotentConeIdeal_le_ker_lift_eval`), and at
the orbit level `{O // O.IsNilpotentAd}` splits canonically as
`LieAlgebra.center k 𝔤 × nilpotentConeOrbits k H` (`TauCeti.centerProdNilpotentConeOrbitsEquiv`).

The cone is not reduced in general, so the statement about `k`-points does not by itself say
anything about points with values in a nonreduced ring. For a connected affine group of finite
type over an algebraically closed field of characteristic zero, the trace-power polynomials
`x ↦ tr (ρ_M(x) ^ m)` of positive degree of a `d`-dimensional module `M` over `𝔤` lie in the ideal
of the cone. Over the coordinate ring of the cone, which is a `ℚ`-algebra, Newton's identities
then make the characteristic polynomial of the matrix `A` of the universal element acting on `M`
equal to `T ^ d`, and the Cayley–Hamilton theorem gives `A ^ d = 0` there. So every point of the
cone, with values in any semiring, acts on `M` by a matrix with `d`-th power zero.

The characteristic coefficients of `A` are Lie invariants as well, and all but the leading one
vanish at the origin, so they lie in the ideal of the cone directly, without Newton's identities.
Hence at every point of the cone with values in any commutative ring, not only a `ℚ`-algebra, the
matrix of the point acting on `M` has characteristic polynomial `T ^ d`.

## Main declarations

* `TauCeti.adjointPolynomialComoduleAlgebra`: the action of `G` on the polynomial functions on `𝔤`,
  with coaction on linear functions `TauCeti.adjointPolynomialComoduleAlgebra_coact_ι`.
* `TauCeti.adjointInvariantPolynomials`: the invariant polynomial functions `O(𝔤)^G`.
* `TauCeti.adjointInvariantPolynomials_le_lieInvariants` and
  `TauCeti.adjointInvariantPolynomials_eq_lieInvariants`: they are Lie invariants, and for
  connected `G` over an algebraically closed field of characteristic zero they are all of them.
* `TauCeti.nilpotentConeIdeal`: the ideal of the zero fibre of the adjoint quotient.
* `TauCeti.mem_adjointInvariantPolynomials_iff_mem_coinvariants` and
  `TauCeti.nilpotentConeIdeal_eq_symmetricAlgebraHilbertIdeal`: the invariants and the ideal of
  the cone, in terms of the coinvariants of the symmetric algebra of the comodule `𝔤*`.
* `TauCeti.nilpotentConeIdeal_isHomogeneous` and `TauCeti.nilpotentConeSubcomodule`: it is
  stable under scaling and under the adjoint action.
* `TauCeti.lift_eval_basePointsRepresentation_of_mem_adjointInvariantPolynomials`,
  `TauCeti.lift_eval_eq_of_mk_le_mk_of_mem_adjointInvariantPolynomials`, and
  `TauCeti.nilpotentConeIdeal_le_ker_lift_eval_of_mk_le_mk`: invariance of adjoint-invariant
  polynomials and stability of the nilpotent cone along the adjoint orbit closure order.
* `TauCeti.nilpotentConeIdeal_le_ker_lift_eval_basePointsRepresentation_iff`: the `k`-points of
  the nilpotent cone are stable under the adjoint action of rational points.
* `TauCeti.nilpotentConeOrbits`, `TauCeti.mem_nilpotentConeOrbits_of_le`, and
  `TauCeti.centerProdNilpotentConeOrbitsEquiv`: rational adjoint orbits in the nilpotent cone,
  their downward closure, and the product comparison
  `Z(𝔤) × nilpotentConeOrbits ≃ {O // O.IsNilpotentAd}` for connected groups with reductive Lie
  algebra.
* `TauCeti.Comodule.VectorOrbit.IsNilpotentAd`, `TauCeti.Comodule.VectorOrbit.IsNilpotentAd.of_le`,
  and `TauCeti.Comodule.VectorOrbit.setOf_mk_le_eq_union_biUnion_of_isNilpotentAd`: `ad`-nilpotent
  rational adjoint orbits, downward closure in the closure order, and decomposition of the
  `k`-rational vectors `{y : 𝔤 | mk y ≤ O}` whose orbit lies in the closure of an `ad`-nilpotent
  orbit `O`.
* `TauCeti.nilpotentConeIdeal_le_ker_lift_eval_iff`: its `k`-points are the `ad`-nilpotent
  elements, with the two inclusions `TauCeti.nilpotentConeIdeal_le_ker_lift_eval_of_isNilpotent`
  and `TauCeti.isNilpotent_ad_of_nilpotentConeIdeal_le_ker_lift_eval`. More generally, points of
  the cone act nilpotently on every finite-dimensional module
  (`TauCeti.isNilpotent_toEnd_of_nilpotentConeIdeal_le_ker_lift_eval`).
* `TauCeti.ι_mem_nilpotentConeIdeal`: for a connected group, the linear functions vanishing on
  `⁅𝔤, 𝔤⁆` lie in the ideal of the cone, so the cone lies in the derived ideal `⁅𝔤, 𝔤⁆`, and so do
  its `k`-points (`TauCeti.mem_derivedSeries_of_nilpotentConeIdeal_le_ker_lift_eval`). When `𝔤` is
  reductive this kills the central coordinates.
* `TauCeti.nilpotentConeIdeal_le_ker_iff`: for a connected group, a ring homomorphism kills the
  ideal of the cone exactly when it kills the Lie invariants of positive degree; in particular the
  `k`-points of the cone are the common zeros of these invariants.
* `TauCeti.nilpotentConeIdeal_le_ker_lift_eval_iff_mem_derivedSeries_and_isNilpotent_ad`: for a
  connected group with reductive Lie algebra, the `k`-points of the cone are the `ad`-nilpotent
  elements of the derived ideal. In the coordinates `𝔤 = Z(𝔤) ⊕ ⁅𝔤, 𝔤⁆` the point `z + y` lies on
  the cone exactly when `z = 0` and `ad y` is nilpotent
  (`TauCeti.nilpotentConeIdeal_le_ker_lift_eval_add_iff`), while the `ad`-nilpotent elements are
  the sums of an arbitrary central element and a point of the cone
  (`TauCeti.isNilpotent_ad_iff_exists_mem_center_add_nilpotentConeIdeal_le_ker_lift_eval`).
* `Module.Basis.genericActionMatrix_pow_card_apply_mem_nilpotentConeIdeal`: for a connected
  affine group of finite type over an algebraically closed field of characteristic zero, the
  universal element of the cone acts nilpotently with a uniform bound. In a basis of size `d` of a
  module `M` over the Lie algebra, the `d`-th power of the generic action matrix vanishes in the
  coordinate ring of the cone, because the trace-power polynomials of positive degree lie in its
  ideal (`TauCeti.tracePowerPolynomial_mem_nilpotentConeIdeal`). Consequently every point of the
  cone, with values in any semiring, acts on `M` by a matrix whose `d`-th power vanishes
  (`TauCeti.map_genericActionMatrix_pow_card_eq_zero_of_nilpotentConeIdeal_le_ker`).
* `TauCeti.charpoly_map_genericActionMatrix_eq_X_pow_of_nilpotentConeIdeal_le_ker`: for a
  connected group, at every point of the cone with values in a commutative ring the generic action
  matrix of a module of rank `d` over the Lie algebra has characteristic polynomial `X ^ d`.

## References

* B. Kostant, *Lie group representations on polynomial rings*, Amer. J. Math. 85 (1963),
  327–404.
* D. H. Collingwood and W. M. McGovern, *Nilpotent Orbits in Semisimple Lie Algebras*, Van
  Nostrand Reinhold, 1993, §1.3, §3.2, and §6.2.
* J. S. Milne, *Algebraic Groups* (2017), Chapter 10.
-/

public section

open scoped TensorProduct

namespace TauCeti

universe u v

attribute [local instance] Derivation.adjointComodule

section Basic

variable (k : Type u) [Field k] (H : Type u) [CommRing H] [HopfAlgebra k H]
  [Module.Finite k (Bialgebra.CotangentSpace k H)]

local notation "𝔤" => Module.Dual k (Bialgebra.CotangentSpace k H)

/-- The polynomial functions `Sym(𝔤*)` on the Lie algebra `𝔤` of `Spec H`, as a comodule algebra:
`Spec H` acts on them through the contragredient of the adjoint representation.

This is not a global instance; select it explicitly or as a local instance. -/
@[implicit_reducible]
noncomputable def adjointPolynomialComoduleAlgebra :
    ComoduleAlgebra k H (SymmetricAlgebra k (Module.Dual k 𝔤)) :=
  letI := Comodule.dual k H 𝔤
  ComoduleAlgebra.symmetricAlgebra k H (Module.Dual k 𝔤)

attribute [local instance] adjointPolynomialComoduleAlgebra

/-- The coaction on a linear function on the Lie algebra, viewed as a polynomial function, is its
coaction `TauCeti.Comodule.dualCoact` under the contragredient of the adjoint representation. -/
theorem adjointPolynomialComoduleAlgebra_coact_ι (φ : Module.Dual k 𝔤) :
    Comodule.coact (R := k) (C := H) (SymmetricAlgebra.ι k (Module.Dual k 𝔤) φ) =
      (SymmetricAlgebra.ι k (Module.Dual k 𝔤)).rTensor H
        (Comodule.dualCoact (R := k) (H := H) (M := 𝔤) φ) := by
  let := Comodule.dual k H 𝔤
  rw [ComoduleAlgebra.symmetricAlgebra_coact, AlgHom.toLinearMap_apply,
    Comodule.symmetricAlgebraCoact_ι, Comodule.dual_coact]

/-- The polynomial functions on the Lie algebra which are invariant under the adjoint action: the
coordinate ring of the adjoint quotient `𝔤 // G`. -/
noncomputable def adjointInvariantPolynomials :
    Subalgebra k (SymmetricAlgebra k (Module.Dual k 𝔤)) :=
  ComoduleAlgebra.coinvariants k H (SymmetricAlgebra k (Module.Dual k 𝔤))

variable {k H}

/-- A polynomial function on the Lie algebra is invariant when its coaction is trivial. -/
@[simp]
theorem mem_adjointInvariantPolynomials {p : SymmetricAlgebra k (Module.Dual k 𝔤)} :
    p ∈ adjointInvariantPolynomials k H ↔
      Comodule.coact (R := k) (C := H) p = p ⊗ₜ[k] (1 : H) :=
  ComoduleAlgebra.mem_coinvariants

/-- **The infinitesimal action on polynomial functions.** A tangent vector `d` at the identity acts
on the polynomial functions on `𝔤` by the coadjoint derivation of the corresponding element of
`𝔤`. -/
theorem differential_adjointPolynomialComoduleAlgebra
    (d : Derivation k H (Bialgebra.CounitAlgebra k H k))
    (p : SymmetricAlgebra k (Module.Dual k 𝔤)) :
    Comodule.differential (R := k) (H := H) d p =
      SymmetricAlgebra.lieModuleDerivation k 𝔤 (Module.Dual k 𝔤)
        ((Derivation.cotangentDualLieEquiv (R := k) (H := H)).symm d) p := by
  let := Comodule.dual k H 𝔤
  have h : Comodule.differential (R := k) (H := H) (M := Module.Dual k 𝔤) d =
      LieModule.toEnd k 𝔤 (Module.Dual k 𝔤)
        ((Derivation.cotangentDualLieEquiv (R := k) (H := H)).symm d) := by
    ext φ x
    rw [Comodule.differential_dual_apply, Derivation.differential_adjointComodule,
      LieModule.toEnd_apply_apply, Module.Dual.lie_apply]
  rw [ComoduleAlgebra.differential_symmetricAlgebra, h,
    SymmetricAlgebra.lieModuleDerivation_apply, Derivation.coeFn_coe]

/-- Invariant polynomial functions on the Lie algebra are killed by the coadjoint action of the Lie
algebra. No connectedness or characteristic assumption is needed. -/
theorem adjointInvariantPolynomials_le_lieInvariants :
    adjointInvariantPolynomials k H ≤ SymmetricAlgebra.lieInvariants k 𝔤 (Module.Dual k 𝔤) :=
  fun p hp ↦ SymmetricAlgebra.mem_lieInvariants.mpr fun x ↦ by
    have h := Comodule.differential_eq_zero_of_coact_eq_tmul_one
      (mem_adjointInvariantPolynomials.mp hp)
      (Derivation.cotangentDualLieEquiv (R := k) (H := H) x)
    rwa [differential_adjointPolynomialComoduleAlgebra, LieEquiv.symm_apply_apply] at h

variable (k H) in
/-- **The ideal of the nilpotent cone.** The ideal of `O(𝔤)` generated by the invariant polynomial
functions vanishing at the origin: the ideal of the scheme-theoretic zero fibre of the adjoint
quotient map `𝔤 → 𝔤 // G`. It is the ideal `Subalgebra.symmetricAlgebraHilbertIdeal` of the
coinvariants of the comodule `𝔤*`. -/
noncomputable def nilpotentConeIdeal : Ideal (SymmetricAlgebra k (Module.Dual k 𝔤)) :=
  (adjointInvariantPolynomials k H).symmetricAlgebraHilbertIdeal

/-- An invariant polynomial function vanishing at the origin lies in the ideal of the nilpotent
cone. -/
theorem mem_nilpotentConeIdeal_of_mem_adjointInvariantPolynomials
    {p : SymmetricAlgebra k (Module.Dual k 𝔤)} (hp : p ∈ adjointInvariantPolynomials k H)
    (hp₀ : SymmetricAlgebra.algebraMapInv p = 0) : p ∈ nilpotentConeIdeal k H :=
  Subalgebra.mem_symmetricAlgebraHilbertIdeal_of_mem hp hp₀

/-- **The universal property of the ideal of the nilpotent cone.** An ideal contains it exactly
when it contains every invariant polynomial function vanishing at the origin. -/
theorem nilpotentConeIdeal_le_iff {I : Ideal (SymmetricAlgebra k (Module.Dual k 𝔤))} :
    nilpotentConeIdeal k H ≤ I ↔
      ∀ p ∈ adjointInvariantPolynomials k H, SymmetricAlgebra.algebraMapInv p = 0 → p ∈ I :=
  Subalgebra.symmetricAlgebraHilbertIdeal_le_iff

/-- The origin lies on the nilpotent cone: its ideal is contained in the augmentation ideal. -/
theorem nilpotentConeIdeal_le_ker_algebraMapInv :
    nilpotentConeIdeal k H ≤
      RingHom.ker (SymmetricAlgebra.algebraMapInv :
        SymmetricAlgebra k (Module.Dual k 𝔤) →ₐ[k] k) :=
  nilpotentConeIdeal_le_iff.mpr fun _ _ hp₀ ↦ hp₀

/-- **The nilpotent cone is a cone.** Its ideal is homogeneous: it is generated by the homogeneous
components of positive degree of the invariant polynomial functions, which are again invariant. -/
theorem nilpotentConeIdeal_isHomogeneous :
    (nilpotentConeIdeal k H).IsHomogeneous
      (SymmetricAlgebra.homogeneousSubmodule k (Module.Dual k 𝔤)) :=
  let _ : Comodule k H (Module.Dual k 𝔤) := Comodule.dual k H 𝔤
  Subalgebra.isHomogeneous_symmetricAlgebraHilbertIdeal fun n _ hp ↦
    ComoduleAlgebra.decompose_mem_coinvariants_symmetricAlgebra hp n

/-- **The nilpotent cone is stable under the adjoint action.** The coaction carries its ideal into
the ideal it generates in `O(𝔤) ⊗ H`, since it is generated by invariants. -/
theorem coact_mem_map_includeLeft_nilpotentConeIdeal {p : SymmetricAlgebra k (Module.Dual k 𝔤)}
    (hp : p ∈ nilpotentConeIdeal k H) :
    Comodule.coact (R := k) (C := H) p ∈
      (nilpotentConeIdeal k H).map (Algebra.TensorProduct.includeLeft (R := k) (S := k)
        (A := SymmetricAlgebra k (Module.Dual k 𝔤)) (B := H)) :=
  ComoduleAlgebra.coact_mem_map_includeLeft_symmetricAlgebraHilbertIdeal hp

variable (k H) in
/-- The ideal of the nilpotent cone, as a subcomodule of the polynomial functions on the Lie
algebra: the adjoint action of `G` on `O(𝔤)` restricts to it, and so descends to the coordinate
ring of the cone. -/
noncomputable def nilpotentConeSubcomodule :
    Subcomodule k H (SymmetricAlgebra k (Module.Dual k 𝔤)) :=
  ComoduleAlgebra.spanSubcomodule (S := {p | p ∈ adjointInvariantPolynomials k H ∧
    SymmetricAlgebra.algebraMapInv p = 0}) fun _ ↦ And.left

/-- Membership in the subcomodule of the nilpotent cone is membership in its ideal. -/
@[simp]
theorem mem_nilpotentConeSubcomodule {p : SymmetricAlgebra k (Module.Dual k 𝔤)} :
    p ∈ nilpotentConeSubcomodule k H ↔ p ∈ nilpotentConeIdeal k H :=
  (ComoduleAlgebra.mem_spanSubcomodule _).trans <| by
    rw [nilpotentConeIdeal, Subalgebra.symmetricAlgebraHilbertIdeal_def]

/-- **Nilpotent elements lie on the nilpotent cone.** Over a field of characteristic zero, if the
Killing form of the Lie algebra is nondegenerate, then evaluation at an `ad`-nilpotent element kills
the ideal of the nilpotent cone. -/
theorem nilpotentConeIdeal_le_ker_lift_eval_of_isNilpotent [CharZero k]
    [LieAlgebra.IsKilling k 𝔤] {x : 𝔤} (hx : IsNilpotent (LieAlgebra.ad k 𝔤 x)) :
    nilpotentConeIdeal k H ≤ RingHom.ker (SymmetricAlgebra.lift (Module.Dual.eval k 𝔤 x)) :=
  nilpotentConeIdeal_le_iff.mpr fun p hp hp₀ ↦
    isNilpotent_ad_iff_forall_lift_eval_eq_zero.mp hx p
      (adjointInvariantPolynomials_le_lieInvariants hp) hp₀

/-- **Adjoint-invariant polynomials are preserved by rational group points.** -/
theorem lift_eval_basePointsRepresentation_of_mem_adjointInvariantPolynomials
    (g : WithConv (H →ₐ[k] k)) (x : 𝔤) {p : SymmetricAlgebra k (Module.Dual k 𝔤)}
    (hp : p ∈ adjointInvariantPolynomials k H) :
    SymmetricAlgebra.lift (Module.Dual.eval k 𝔤 (Comodule.basePointsRepresentation 𝔤 g x)) p =
      SymmetricAlgebra.lift (Module.Dual.eval k 𝔤 x) p := by
  let _ := Comodule.dual k H 𝔤
  exact Comodule.lift_eval_basePointsRepresentation_of_mem_coinvariants x g hp

/-- **The nilpotent cone is stable under rational group points.** An element lies on the
nilpotent cone exactly when its image under the adjoint action of a rational point does. -/
@[simp]
theorem nilpotentConeIdeal_le_ker_lift_eval_basePointsRepresentation_iff
    (g : WithConv (H →ₐ[k] k)) (x : 𝔤) :
    nilpotentConeIdeal k H ≤ RingHom.ker
        (SymmetricAlgebra.lift (Module.Dual.eval k 𝔤 (Comodule.basePointsRepresentation 𝔤 g x))) ↔
      nilpotentConeIdeal k H ≤ RingHom.ker (SymmetricAlgebra.lift (Module.Dual.eval k 𝔤 x)) := by
  simp only [nilpotentConeIdeal_le_iff, RingHom.mem_ker]
  exact forall₂_congr fun p hp ↦ by
    rw [lift_eval_basePointsRepresentation_of_mem_adjointInvariantPolynomials g x hp]

/-- **Adjoint-invariant polynomials are constant on adjoint orbit closures.** -/
theorem lift_eval_eq_of_mk_le_mk_of_mem_adjointInvariantPolynomials [IsAlgClosed k]
    [Algebra.FiniteType k H] {x y : 𝔤}
    (h : (Comodule.VectorOrbit.mk y : Comodule.VectorOrbit k H 𝔤) ≤ Comodule.VectorOrbit.mk x)
    {p : SymmetricAlgebra k (Module.Dual k 𝔤)} (hp : p ∈ adjointInvariantPolynomials k H) :
    SymmetricAlgebra.lift (Module.Dual.eval k 𝔤 y) p =
      SymmetricAlgebra.lift (Module.Dual.eval k 𝔤 x) p := by
  let _ := Comodule.dual k H 𝔤
  exact Comodule.VectorOrbit.lift_eval_eq_of_mk_le_mk_of_mem_coinvariants h hp

/-- **The nilpotent cone is closed under adjoint orbit specialization.** If the adjoint orbit of `y`
lies below that of `x` in the closure order and `x` lies on the nilpotent cone, so does `y`. -/
theorem nilpotentConeIdeal_le_ker_lift_eval_of_mk_le_mk [IsAlgClosed k] [Algebra.FiniteType k H]
    {x y : 𝔤}
    (h : (Comodule.VectorOrbit.mk y : Comodule.VectorOrbit k H 𝔤) ≤ Comodule.VectorOrbit.mk x)
    (hx : nilpotentConeIdeal k H ≤ RingHom.ker (SymmetricAlgebra.lift (Module.Dual.eval k 𝔤 x))) :
    nilpotentConeIdeal k H ≤ RingHom.ker (SymmetricAlgebra.lift (Module.Dual.eval k 𝔤 y)) :=
  nilpotentConeIdeal_le_iff.mpr fun p hp hp₀ ↦ by
    rw [RingHom.mem_ker, lift_eval_eq_of_mk_le_mk_of_mem_adjointInvariantPolynomials h hp]
    exact nilpotentConeIdeal_le_iff.mp hx p hp hp₀

end Basic

section Coinvariants

variable {k : Type u} [Field k] {H : Type u} [CommRing H] [HopfAlgebra k H]
  [Module.Finite k (Bialgebra.CotangentSpace k H)]

local notation "𝔤" => Module.Dual k (Bialgebra.CotangentSpace k H)

attribute [local instance] ComoduleAlgebra.symmetricAlgebra

/-- The invariant polynomial functions on the Lie algebra are the coinvariants of the symmetric
algebra of the contragredient of the adjoint comodule. -/
theorem mem_adjointInvariantPolynomials_iff_mem_coinvariants
    {p : SymmetricAlgebra k (Module.Dual k 𝔤)} :
    letI := Comodule.dual k H 𝔤
    p ∈ adjointInvariantPolynomials k H ↔
      p ∈ ComoduleAlgebra.coinvariants k H (SymmetricAlgebra k (Module.Dual k 𝔤)) := by
  let := Comodule.dual k H 𝔤
  -- Both coactions are algebra maps extending the contragredient coaction on generators.
  have h : (letI := adjointPolynomialComoduleAlgebra k H
      ComoduleAlgebra.coactAlgHom k H (SymmetricAlgebra k (Module.Dual k 𝔤))) =
      Comodule.symmetricAlgebraCoact k H (Module.Dual k 𝔤) := by
    let := adjointPolynomialComoduleAlgebra k H
    refine SymmetricAlgebra.algHom_ext (LinearMap.ext fun φ ↦ ?_)
    simp only [LinearMap.coe_comp, LinearMap.coe_ofClass, Function.comp_apply,
      ComoduleAlgebra.coactAlgHom_apply, adjointPolynomialComoduleAlgebra_coact_ι,
      Comodule.symmetricAlgebraCoact_ι, Comodule.dual_coact]
  have hp : (letI := adjointPolynomialComoduleAlgebra k H
      Comodule.coact (R := k) (C := H) p) = Comodule.symmetricAlgebraCoact k H _ p := by
    let := adjointPolynomialComoduleAlgebra k H
    rw [← ComoduleAlgebra.coactAlgHom_apply, h]
  rw [mem_adjointInvariantPolynomials, hp, ComoduleAlgebra.mem_coinvariants,
    ComoduleAlgebra.symmetricAlgebra_coact, AlgHom.toLinearMap_apply]

/-- The ideal of the adjoint nilpotent cone is the ideal generated by the coinvariants of the
symmetric algebra of the contragredient of the adjoint comodule vanishing at the origin. -/
theorem nilpotentConeIdeal_eq_symmetricAlgebraHilbertIdeal :
    letI := Comodule.dual k H 𝔤
    nilpotentConeIdeal k H = (ComoduleAlgebra.coinvariants k H
      (SymmetricAlgebra k (Module.Dual k 𝔤))).symmetricAlgebraHilbertIdeal := by
  let := Comodule.dual k H 𝔤
  refine le_antisymm (nilpotentConeIdeal_le_iff.mpr fun p hp hp₀ ↦ ?_)
    (Subalgebra.symmetricAlgebraHilbertIdeal_le_iff.mpr fun p hp hp₀ ↦ ?_)
  · exact Subalgebra.mem_symmetricAlgebraHilbertIdeal_of_mem
      (mem_adjointInvariantPolynomials_iff_mem_coinvariants.mp hp) hp₀
  · exact mem_nilpotentConeIdeal_of_mem_adjointInvariantPolynomials
      (mem_adjointInvariantPolynomials_iff_mem_coinvariants.mpr hp) hp₀

end Coinvariants

section Connected

variable {k : Type u} [Field k] [CharZero k] [IsAlgClosed k]
  {H : FiniteTypeCommHopfAlgCat.{u, u} k} [ConnectedSpace (PrimeSpectrum H)]

attribute [local instance] adjointPolynomialComoduleAlgebra

local notation "𝔤" => Module.Dual k (Bialgebra.CotangentSpace k H)

/-- **Group and Lie invariants coincide.** For a connected affine group over an algebraically
closed field of characteristic zero, a polynomial function on the Lie algebra is invariant under
the adjoint action exactly when it is killed by the coadjoint action of the Lie algebra. -/
theorem adjointInvariantPolynomials_eq_lieInvariants :
    adjointInvariantPolynomials k H = SymmetricAlgebra.lieInvariants k 𝔤 (Module.Dual k 𝔤) :=
  le_antisymm adjointInvariantPolynomials_le_lieInvariants fun p hp ↦
    mem_adjointInvariantPolynomials.mpr <|
    (Comodule.coact_eq_tmul_one_iff_forall_differential_eq_zero p).mpr fun d ↦ by
      rw [differential_adjointPolynomialComoduleAlgebra]
      exact SymmetricAlgebra.mem_lieInvariants.mp hp _

/-- **Points of the nilpotent cone are the common zeros of the Lie invariants.** For a connected
affine group over an algebraically closed field of characteristic zero, a ring homomorphism `f`
out of the polynomial functions on the Lie algebra kills the ideal of the nilpotent cone exactly
when it kills every polynomial function that is killed by the coadjoint action and vanishes at the
origin. For `f` the evaluation at an element `x` of the Lie algebra, this says that `x` lies on the
cone exactly when it is a common zero of these invariants. -/
theorem nilpotentConeIdeal_le_ker_iff {S F : Type*} [Semiring S]
    [FunLike F (SymmetricAlgebra k (Module.Dual k 𝔤)) S]
    [RingHomClass F (SymmetricAlgebra k (Module.Dual k 𝔤)) S] {f : F} :
    nilpotentConeIdeal k H ≤ RingHom.ker f ↔
      ∀ p ∈ SymmetricAlgebra.lieInvariants k 𝔤 (Module.Dual k 𝔤),
        SymmetricAlgebra.algebraMapInv p = 0 → f p = 0 := by
  simp only [nilpotentConeIdeal_le_iff, adjointInvariantPolynomials_eq_lieInvariants,
    RingHom.mem_ker]

/-- **The nilpotent cone lies in the derived ideal.** For a connected affine group over an
algebraically closed field of characteristic zero, a linear function on the Lie algebra vanishing on
all brackets, that is on the derived ideal `⁅𝔤, 𝔤⁆`, lies in the ideal of the nilpotent cone. So the
cone is a closed subscheme of the linear subspace `⁅𝔤, 𝔤⁆`. Only when `𝔤` is reductive does this
say that the cone has zero central coordinate
(`TauCeti.nilpotentConeIdeal_le_ker_lift_eval_add_iff`). -/
theorem ι_mem_nilpotentConeIdeal {φ : Module.Dual k 𝔤} (hφ : ∀ x y : 𝔤, φ ⁅x, y⁆ = 0) :
    _root_.SymmetricAlgebra.ι k (Module.Dual k 𝔤) φ ∈ nilpotentConeIdeal k H := by
  refine mem_nilpotentConeIdeal_of_mem_adjointInvariantPolynomials ?_
    (SymmetricAlgebra.algebraMapInv_ι φ)
  rw [adjointInvariantPolynomials_eq_lieInvariants]
  exact SymmetricAlgebra.ι_mem_lieInvariants_iff_apply_lie_eq_zero.mpr hφ

/-- **Points of the nilpotent cone lie in the derived ideal.** For a connected affine group over an
algebraically closed field of characteristic zero, if evaluation at an element `x` of the Lie
algebra kills the ideal of the nilpotent cone, then `x ∈ ⁅𝔤, 𝔤⁆`. -/
theorem mem_derivedSeries_of_nilpotentConeIdeal_le_ker_lift_eval {x : 𝔤}
    (hx : nilpotentConeIdeal k H ≤ RingHom.ker (SymmetricAlgebra.lift (Module.Dual.eval k 𝔤 x))) :
    x ∈ LieAlgebra.derivedSeries k 𝔤 1 :=
  mem_derivedSeries_of_forall_lift_eval_eq_zero (nilpotentConeIdeal_le_ker_iff.mp hx)

/-- **Points of the nilpotent cone act nilpotently.** For a connected affine group over an
algebraically closed field of characteristic zero, if evaluation at an element `x` of the Lie
algebra kills the ideal of the nilpotent cone, then `x` acts nilpotently on every
finite-dimensional module over the Lie algebra. -/
theorem isNilpotent_toEnd_of_nilpotentConeIdeal_le_ker_lift_eval (M : Type*) [AddCommGroup M]
    [Module k M] [FiniteDimensional k M] [LieRingModule 𝔤 M] [LieModule k 𝔤 M] {x : 𝔤}
    (hx : nilpotentConeIdeal k H ≤ RingHom.ker (SymmetricAlgebra.lift (Module.Dual.eval k 𝔤 x))) :
    IsNilpotent (LieModule.toEnd k 𝔤 M x) :=
  isNilpotent_toEnd_of_forall_lift_eval_eq_zero M (nilpotentConeIdeal_le_ker_iff.mp hx)

/-- **Points of the nilpotent cone are nilpotent.** For a connected affine group over an
algebraically closed field of characteristic zero, if evaluation at an element `x` of the Lie
algebra kills the ideal of the nilpotent cone, then `ad x` is nilpotent. -/
theorem isNilpotent_ad_of_nilpotentConeIdeal_le_ker_lift_eval {x : 𝔤}
    (hx : nilpotentConeIdeal k H ≤ RingHom.ker (SymmetricAlgebra.lift (Module.Dual.eval k 𝔤 x))) :
    IsNilpotent (LieAlgebra.ad k 𝔤 x) :=
  isNilpotent_toEnd_of_nilpotentConeIdeal_le_ker_lift_eval 𝔤 hx

/-- **The rational points of the nilpotent cone.** For a connected affine group over an
algebraically closed field of characteristic zero whose Lie algebra has nondegenerate Killing form,
an element `x` of the Lie algebra lies on the nilpotent cone, that is evaluation at `x` kills its
ideal, exactly when `ad x` is nilpotent. -/
theorem nilpotentConeIdeal_le_ker_lift_eval_iff [LieAlgebra.IsKilling k 𝔤] {x : 𝔤} :
    nilpotentConeIdeal k H ≤ RingHom.ker (SymmetricAlgebra.lift (Module.Dual.eval k 𝔤 x)) ↔
      IsNilpotent (LieAlgebra.ad k 𝔤 x) :=
  ⟨isNilpotent_ad_of_nilpotentConeIdeal_le_ker_lift_eval,
    nilpotentConeIdeal_le_ker_lift_eval_of_isNilpotent⟩

/-- **The rational points of the nilpotent cone of a group with reductive Lie algebra.** For a
connected affine group over an algebraically closed field of characteristic zero whose Lie algebra
is reductive, an element `x` of the Lie algebra lies on the nilpotent cone, that is evaluation at
`x` kills its ideal, exactly when `x` lies in the derived ideal `⁅𝔤, 𝔤⁆` and `ad x` is nilpotent.

The invariant linear functions are those vanishing on `⁅𝔤, 𝔤⁆`, so the cone has zero central
coordinate: unlike the set of `ad`-nilpotent elements, it contains no nonzero central element
(`TauCeti.nilpotentConeIdeal_le_ker_lift_eval_add_iff`). -/
theorem nilpotentConeIdeal_le_ker_lift_eval_iff_mem_derivedSeries_and_isNilpotent_ad
    [LieAlgebra.HasCentralRadical k 𝔤] {x : 𝔤} :
    nilpotentConeIdeal k H ≤ RingHom.ker (SymmetricAlgebra.lift (Module.Dual.eval k 𝔤 x)) ↔
      x ∈ LieAlgebra.derivedSeries k 𝔤 1 ∧ IsNilpotent (LieAlgebra.ad k 𝔤 x) := by
  rw [nilpotentConeIdeal_le_ker_iff,
    mem_derivedSeries_and_isNilpotent_ad_iff_forall_lift_eval_eq_zero]

/-- **The nilpotent cone of a group with reductive Lie algebra has zero central coordinate.** For a
connected affine group over an algebraically closed field of characteristic zero whose Lie algebra
`𝔤` is reductive, let `z` be central and `y ∈ ⁅𝔤, 𝔤⁆`. Then `z + y` lies on the nilpotent cone
exactly when the central coordinate `z` is zero and `ad y` is nilpotent. -/
theorem nilpotentConeIdeal_le_ker_lift_eval_add_iff [LieAlgebra.HasCentralRadical k 𝔤] {z y : 𝔤}
    (hz : z ∈ LieAlgebra.center k 𝔤) (hy : y ∈ LieAlgebra.derivedSeries k 𝔤 1) :
    nilpotentConeIdeal k H ≤ RingHom.ker (SymmetricAlgebra.lift (Module.Dual.eval k 𝔤 (z + y))) ↔
      z = 0 ∧ IsNilpotent (LieAlgebra.ad k 𝔤 y) := by
  rw [nilpotentConeIdeal_le_ker_iff, forall_lift_eval_add_eq_zero_iff hz hy]

/-- **The `ad`-nilpotent elements of a group with reductive Lie algebra.** For a connected affine
group over an algebraically closed field of characteristic zero whose Lie algebra `𝔤` is reductive,
`ad x` is nilpotent exactly when `x = z + y` with `z` central and `y` on the nilpotent cone. So the
`ad`-nilpotent locus `Z(𝔤) × 𝒩(⁅𝔤, 𝔤⁆)` is larger than the cone as soon as `𝔤` has nonzero
centre. -/
theorem isNilpotent_ad_iff_exists_mem_center_add_nilpotentConeIdeal_le_ker_lift_eval
    [LieAlgebra.HasCentralRadical k 𝔤] {x : 𝔤} :
    IsNilpotent (LieAlgebra.ad k 𝔤 x) ↔
      ∃ z ∈ LieAlgebra.center k 𝔤, ∃ y : 𝔤,
        nilpotentConeIdeal k H ≤ RingHom.ker (SymmetricAlgebra.lift (Module.Dual.eval k 𝔤 y)) ∧
          z + y = x := by
  rw [isNilpotent_ad_iff_exists_mem_center_add]
  simp only [nilpotentConeIdeal_le_ker_lift_eval_iff_mem_derivedSeries_and_isNilpotent_ad,
    and_assoc]

section GenericActionMatrix

/-- For a connected affine group of finite type over an algebraically closed field of
characteristic zero, the trace-power polynomials `x ↦ tr (ρ_M(x) ^ m)` of positive degree of every
finite-dimensional module `M` over its Lie algebra lie in the ideal of the nilpotent cone. -/
theorem tracePowerPolynomial_mem_nilpotentConeIdeal {M : Type*} [AddCommGroup M] [Module k M]
    [FiniteDimensional k M] [LieRingModule 𝔤 M] [LieModule k 𝔤 M] {m : ℕ} (hm : 0 < m) :
    tracePowerPolynomial k 𝔤 M m ∈ nilpotentConeIdeal k H := by
  refine mem_nilpotentConeIdeal_of_mem_adjointInvariantPolynomials
    (by rw [adjointInvariantPolynomials_eq_lieInvariants]
        exact tracePowerPolynomial_mem_lieInvariants m) ?_
  -- a homogeneous element of positive degree lies in the irrelevant ideal
  exact SymmetricAlgebra.mem_irrelevant_iff_algebraMapInv_eq_zero.mp <|
    HomogeneousIdeal.mem_irrelevant_of_mem _ hm
      (tracePowerPolynomial_mem_homogeneousSubmodule (R := k) (L := 𝔤) (M := M) m)

variable {M : Type*} [AddCommGroup M] [Module k M]
  [LieRingModule (Module.Dual k (Bialgebra.CotangentSpace k H)) M]
  [LieModule k (Module.Dual k (Bialgebra.CotangentSpace k H)) M]
  {κ : Type*} [Fintype κ] [DecidableEq κ]

/-- **The universal element of the nilpotent cone is nilpotent.** For a connected affine group of
finite type over an algebraically closed field of characteristic zero and a basis `c` of size `d`
of a module `M` over its Lie algebra, every entry of the `d`-th power of the generic action matrix
lies in the ideal of the nilpotent cone. That is, `A ^ d = 0` in the coordinate ring of the cone,
where `A` is the matrix of the universal element of the cone acting on `M`. -/
theorem _root_.Module.Basis.genericActionMatrix_pow_card_apply_mem_nilpotentConeIdeal
    (c : Module.Basis κ k M) (p q : κ) :
    (genericActionMatrix k 𝔤 c ^ Fintype.card κ) p q ∈ nilpotentConeIdeal k H := by
  have := Module.Finite.of_basis c
  let I := nilpotentConeIdeal k H
  -- the coordinate ring of the cone is a vector space over a field of characteristic zero
  have := HasUniqueDiv.of_isTorsionFree k (SymmetricAlgebra k (Module.Dual k 𝔤) ⧸ I)
  have h := map_genericActionMatrix_pow_card_eq_zero (Ideal.Quotient.mk I) c
    fun j hj _ ↦ Ideal.Quotient.eq_zero_iff_mem.mpr (tracePowerPolynomial_mem_nilpotentConeIdeal hj)
  have hpq := congrFun₂ h p q
  rw [← Matrix.map_pow, Matrix.map_apply, Matrix.zero_apply] at hpq
  exact Ideal.Quotient.eq_zero_iff_mem.mp hpq

/-- **Points of the nilpotent cone act nilpotently, with a uniform bound.** For a connected affine
group of finite type over an algebraically closed field of characteristic zero, let
`φ : O(𝔤) → B` be a point of the nilpotent cone with values in any semiring, possibly nonreduced:
a ring homomorphism killing the ideal of the cone. Let `A` be the generic action matrix of a module
`M` over the Lie algebra in a basis of size `d`. Then the matrix `φ A` of the point acting on `M`
satisfies `(φ A) ^ d = 0`. -/
theorem map_genericActionMatrix_pow_card_eq_zero_of_nilpotentConeIdeal_le_ker {B F : Type*}
    [Semiring B] [FunLike F (SymmetricAlgebra k (Module.Dual k 𝔤)) B]
    [RingHomClass F (SymmetricAlgebra k (Module.Dual k 𝔤)) B] (φ : F)
    (hφ : nilpotentConeIdeal k H ≤ RingHom.ker φ) (c : Module.Basis κ k M) :
    (genericActionMatrix k 𝔤 c).map φ ^ Fintype.card κ = 0 := by
  ext p q
  rw [← RingHom.coe_coe φ, ← Matrix.map_pow, Matrix.map_apply, Matrix.zero_apply]
  exact hφ (c.genericActionMatrix_pow_card_apply_mem_nilpotentConeIdeal p q)

/-- **The characteristic polynomial of a module on the nilpotent cone.** For a connected affine
group over an algebraically closed field of characteristic zero, let `M` be a Lie module over its
Lie algebra with a basis `c` of size `N`. At every point of the nilpotent cone with values in a
commutative ring, that is after applying any ring homomorphism `f` killing the ideal of the cone,
the generic action matrix of `M` has characteristic polynomial `X ^ N`: its other characteristic
coefficients are invariant polynomial functions vanishing at the origin. -/
theorem charpoly_map_genericActionMatrix_eq_X_pow_of_nilpotentConeIdeal_le_ker {B : Type*}
    [CommRing B] {f : SymmetricAlgebra k (Module.Dual k 𝔤) →+* B}
    (hf : nilpotentConeIdeal k H ≤ RingHom.ker f) (c : Module.Basis κ k M) :
    ((genericActionMatrix k 𝔤 c).map f).charpoly = Polynomial.X ^ Fintype.card κ := by
  set A := genericActionMatrix k 𝔤 c
  have hcoeff (i : ℕ) (hi : i < Fintype.card κ) : f (A.charpoly.coeff i) = 0 := by
    refine hf (mem_nilpotentConeIdeal_of_mem_adjointInvariantPolynomials ?_
      (algebraMapInv_charpoly_coeff_genericActionMatrix_of_lt k 𝔤 c hi))
    rw [adjointInvariantPolynomials_eq_lieInvariants]
    exact charpoly_coeff_genericActionMatrix_mem_lieInvariants k 𝔤 c i
  rw [Matrix.charpoly_map, ← Matrix.charpoly_natDegree_eq_dim A]
  exact (Matrix.charpoly_monic A).map_eq_X_pow_of_map_coeff_eq_zero fun i hi ↦
    hcoeff i (A.charpoly_natDegree_eq_dim ▸ hi)

end GenericActionMatrix

end Connected

namespace Comodule.VectorOrbit

section Predicate

variable {k : Type u} {H : Type v} [Field k] [CommRing H] [HopfAlgebra k H]
  [Module.Finite k (Bialgebra.CotangentSpace k H)]

local notation "𝔤" => Module.Dual k (Bialgebra.CotangentSpace k H)

/-- A rational adjoint orbit is **nilpotent** when its elements act nilpotently under `ad`. -/
def IsNilpotentAd (O : VectorOrbit k H 𝔤) : Prop :=
  O.lift (fun x ↦ IsNilpotent (LieAlgebra.ad k 𝔤 x)) fun g x ↦ by
    rw [← Derivation.basePointsAdjointLieEquiv_apply]
    exact propext ((Derivation.basePointsAdjointLieEquiv g).isNilpotent_ad_apply_iff x)

/-- The orbit of `x ∈ 𝔤` is nilpotent precisely when `ad x` is nilpotent. -/
@[simp]
theorem isNilpotentAd_mk_iff {x : 𝔤} :
    (mk x : VectorOrbit k H 𝔤).IsNilpotentAd ↔ IsNilpotent (LieAlgebra.ad k 𝔤 x) := by
  rw [IsNilpotentAd, lift_mk]

/-- The zero adjoint orbit is nilpotent. -/
theorem isNilpotentAd_mk_zero : (mk (0 : 𝔤) : VectorOrbit k H 𝔤).IsNilpotentAd := by
  simp

end Predicate

section Closure

variable {k H : Type u} [Field k] [IsAlgClosed k] [CommRing H] [HopfAlgebra k H]
  [Algebra.FiniteType k H]

local notation "𝔤" => Module.Dual k (Bialgebra.CotangentSpace k H)

/-- **Nilpotent orbits are downward closed in the closure order.** For any finite-type affine group
over an algebraically closed field, any rational adjoint orbit in the closure of a nilpotent orbit
is again nilpotent. -/
theorem IsNilpotentAd.of_le {O O' : VectorOrbit k H 𝔤} (hle : O' ≤ O)
    (hO : O.IsNilpotentAd) : O'.IsNilpotentAd := by
  classical
  induction O using VectorOrbit.ind with | h x =>
  induction O' using VectorOrbit.ind with | h y =>
  rw [isNilpotentAd_mk_iff] at hO ⊢
  obtain ⟨n, hn⟩ := hO
  refine ⟨n, ?_⟩
  let c := Module.Free.chooseBasis k 𝔤
  have hmat (z : 𝔤) :
      LinearMap.toMatrix c c (LieAlgebra.ad k 𝔤 z ^ n) =
        (genericActionMatrix k 𝔤 c ^ n).map (SymmetricAlgebra.lift (Module.Dual.eval k 𝔤 z)) := by
    rw [← LinearMap.toMatrix_pow, ← AlgHom.mapMatrix_apply, map_pow, AlgHom.mapMatrix_apply,
      map_lift_eval_genericActionMatrix]
    rfl
  apply (LinearMap.toMatrix c c).injective
  rw [map_zero, hmat y]
  ext p q
  rw [Matrix.map_apply, Matrix.zero_apply]
  refine lift_eval_eq_zero_of_mk_le_mk_of_forall_lift_eval_basePointsRepresentation_eq_zero hle
    fun g ↦ ?_
  have hgn : (LieAlgebra.ad k 𝔤 (basePointsRepresentation 𝔤 g x)) ^ n = 0 := by
    ext z
    rw [LinearMap.zero_apply, ← Derivation.basePointsAdjointLieEquiv_apply]
    have hmap := LieHom.map_ad_pow (Derivation.basePointsAdjointLieEquiv g).toLieHom x n
      ((Derivation.basePointsAdjointLieEquiv g).symm z)
    rw [LieEquiv.coe_toLieHom, LieEquiv.apply_symm_apply] at hmap
    rw [← hmap, hn, LinearMap.zero_apply, map_zero]
  have h0 := congrArg (fun M ↦ M p q) (hmat (basePointsRepresentation 𝔤 g x))
  rw [hgn, map_zero, Matrix.zero_apply, Matrix.map_apply] at h0
  exact h0.symm

/-- **Decomposition of the `k`-rational vectors below a nilpotent orbit.** The `k`-rational vectors
`{y : 𝔤 | mk y ≤ O}` whose orbit lies in the closure of a nilpotent orbit `O` decompose into `O`
together with the union of all strictly smaller nilpotent orbits. -/
theorem setOf_mk_le_eq_union_biUnion_of_isNilpotentAd {O : VectorOrbit k H 𝔤}
    (hO : O.IsNilpotentAd) :
    {y : 𝔤 | (mk y : VectorOrbit k H 𝔤) ≤ O} =
      {y : 𝔤 | mk y = O} ∪
        ⋃ O' ∈ {O' : VectorOrbit k H 𝔤 | O'.IsNilpotentAd ∧ O' < O},
          {y : 𝔤 | mk y = O'} := by
  ext y
  simp only [Set.mem_ofPred_eq, Set.mem_union, Set.mem_iUnion, exists_prop]
  refine ⟨fun hle ↦ ?_, ?_⟩
  · rcases eq_or_lt_of_le hle with rfl | hlt
    · exact Or.inl rfl
    · exact Or.inr ⟨mk y, ⟨hO.of_le hle, hlt⟩, rfl⟩
  · rintro (rfl | ⟨_, ⟨-, hlt⟩, rfl⟩)
    · exact le_rfl
    · exact hlt.le

end Closure

section Subsingleton

variable {k : Type u} {H : Type v} [Field k] [CommRing H] [HopfAlgebra k H]
  [Module.Finite k (Bialgebra.CotangentSpace k H)]

local notation "𝔤" => Module.Dual k (Bialgebra.CotangentSpace k H)

/-- In a trivial (rank-zero) Lie algebra, the zero orbit is the sole `ad`-nilpotent orbit. -/
theorem setOf_isNilpotentAd_eq_singleton_of_subsingleton [Subsingleton 𝔤] :
    {O : VectorOrbit k H 𝔤 | O.IsNilpotentAd} = {mk (0 : 𝔤)} := by
  ext O
  induction O using VectorOrbit.ind with | h x =>
  simp [Subsingleton.elim x 0]

end Subsingleton

end Comodule.VectorOrbit

section NilpotentConeOrbits

section General

variable (k H : Type u) [Field k] [CommRing H] [HopfAlgebra k H]
  [Module.Finite k (Bialgebra.CotangentSpace k H)]

attribute [local instance] Derivation.adjointComodule

local notation "𝔤" => Module.Dual k (Bialgebra.CotangentSpace k H)

/-- **Rational adjoint orbits in the nilpotent cone** of `G = Spec H`: the `G(k)`-orbits of vectors
`x ∈ 𝔤` on which `TauCeti.nilpotentConeIdeal k H` vanishes. Unlike
`Comodule.VectorOrbit.IsNilpotentAd`, this excludes nonzero central orbits when `𝔤` is reductive
with nontrivial centre. -/
def nilpotentConeOrbits : Set (Comodule.VectorOrbit k H 𝔤) :=
  {O | O.lift
    (fun x ↦ nilpotentConeIdeal k H ≤
      RingHom.ker (_root_.SymmetricAlgebra.lift (Module.Dual.eval k 𝔤 x)))
    fun g x ↦ propext (nilpotentConeIdeal_le_ker_lift_eval_basePointsRepresentation_iff g x)}

variable {k H}

/-- The orbit of `x ∈ 𝔤` belongs to `nilpotentConeOrbits` precisely when evaluation at `x`
annihilates `nilpotentConeIdeal k H`. -/
@[simp]
theorem mk_mem_nilpotentConeOrbits_iff {x : 𝔤} :
    (Comodule.VectorOrbit.mk x : Comodule.VectorOrbit k H 𝔤) ∈ nilpotentConeOrbits k H ↔
      nilpotentConeIdeal k H ≤
        RingHom.ker (_root_.SymmetricAlgebra.lift (Module.Dual.eval k 𝔤 x)) := by
  simp [nilpotentConeOrbits]

/-- The zero orbit lies in `nilpotentConeOrbits`. -/
theorem mk_zero_mem_nilpotentConeOrbits :
    (Comodule.VectorOrbit.mk (0 : 𝔤) : Comodule.VectorOrbit k H 𝔤) ∈ nilpotentConeOrbits k H := by
  rw [mk_mem_nilpotentConeOrbits_iff]
  have heq : _root_.SymmetricAlgebra.lift (Module.Dual.eval k 𝔤 (0 : 𝔤)) =
      SymmetricAlgebra.algebraMapInv :=
    _root_.SymmetricAlgebra.algHom_ext <| LinearMap.ext fun φ ↦ by
      simp [SymmetricAlgebra.algebraMapInv_ι]
  rw [heq]
  exact nilpotentConeIdeal_le_ker_algebraMapInv

/-- In a trivial (rank-zero) Lie algebra, the zero orbit is the sole orbit in the nilpotent cone. -/
theorem nilpotentConeOrbits_eq_singleton_of_subsingleton [Subsingleton 𝔤] :
    nilpotentConeOrbits k H = {Comodule.VectorOrbit.mk (0 : 𝔤)} := by
  ext O
  induction O using Comodule.VectorOrbit.ind with | h x =>
  rw [Subsingleton.elim x 0]
  exact ⟨fun _ ↦ rfl, fun _ ↦ mk_zero_mem_nilpotentConeOrbits⟩

/-- In characteristic zero, when the Killing form is nondegenerate, every `ad`-nilpotent orbit lies
in `nilpotentConeOrbits` (without connectedness or algebraic closure). -/
theorem mem_nilpotentConeOrbits_of_isNilpotentAd [CharZero k] [LieAlgebra.IsKilling k 𝔤]
    {O : Comodule.VectorOrbit k H 𝔤} (hO : O.IsNilpotentAd) :
    O ∈ nilpotentConeOrbits k H := by
  induction O using Comodule.VectorOrbit.ind with | h x =>
  rw [mk_mem_nilpotentConeOrbits_iff]
  exact nilpotentConeIdeal_le_ker_lift_eval_of_isNilpotent
    (Comodule.VectorOrbit.isNilpotentAd_mk_iff.mp hO)

end General

section Closure

variable {k H : Type u} [Field k] [IsAlgClosed k] [CommRing H] [HopfAlgebra k H]
  [Algebra.FiniteType k H]

attribute [local instance] Derivation.adjointComodule

local notation "𝔤" => Module.Dual k (Bialgebra.CotangentSpace k H)

/-- **Orbits in the nilpotent cone are downward closed in the closure order.** -/
theorem mem_nilpotentConeOrbits_of_le {O O' : Comodule.VectorOrbit k H 𝔤}
    (hle : O' ≤ O) (hO : O ∈ nilpotentConeOrbits k H) :
    O' ∈ nilpotentConeOrbits k H := by
  induction O using Comodule.VectorOrbit.ind with | h x =>
  induction O' using Comodule.VectorOrbit.ind with | h y =>
  rw [mk_mem_nilpotentConeOrbits_iff] at hO ⊢
  exact nilpotentConeIdeal_le_ker_lift_eval_of_mk_le_mk hle hO

/-- **Decomposition of the `k`-rational vectors below an orbit in the nilpotent cone.** -/
theorem setOf_mk_le_eq_union_biUnion_of_mem_nilpotentConeOrbits {O : Comodule.VectorOrbit k H 𝔤}
    (hO : O ∈ nilpotentConeOrbits k H) :
    {y : 𝔤 | (Comodule.VectorOrbit.mk y : Comodule.VectorOrbit k H 𝔤) ≤ O} =
      {y : 𝔤 | Comodule.VectorOrbit.mk y = O} ∪
        ⋃ O' ∈ {O' : Comodule.VectorOrbit k H 𝔤 | O' ∈ nilpotentConeOrbits k H ∧ O' < O},
          {y : 𝔤 | Comodule.VectorOrbit.mk y = O'} := by
  ext y
  simp only [Set.mem_ofPred_eq, Set.mem_union, Set.mem_iUnion, exists_prop]
  refine ⟨fun hle ↦ ?_, ?_⟩
  · rcases eq_or_lt_of_le hle with rfl | hlt
    · exact Or.inl rfl
    · exact Or.inr ⟨Comodule.VectorOrbit.mk y, ⟨mem_nilpotentConeOrbits_of_le hle hO, hlt⟩, rfl⟩
  · rintro (rfl | ⟨_, ⟨-, hlt⟩, rfl⟩)
    · exact le_rfl
    · exact hlt.le

end Closure

section ConnectedOrbits

variable {k H : Type u} [Field k] [CharZero k] [IsAlgClosed k] [CommRing H] [HopfAlgebra k H]
  [Algebra.FiniteType k H] [ConnectedSpace (PrimeSpectrum H)]

attribute [local instance] Derivation.adjointComodule

local notation "𝔤" => Module.Dual k (Bialgebra.CotangentSpace k H)

/-- For a connected group over an algebraically closed field of characteristic zero, every orbit in
`nilpotentConeOrbits` is `ad`-nilpotent. -/
theorem isNilpotentAd_of_mem_nilpotentConeOrbits {O : Comodule.VectorOrbit k H 𝔤}
    (hO : O ∈ nilpotentConeOrbits k H) : O.IsNilpotentAd := by
  induction O using Comodule.VectorOrbit.ind with | h x =>
  rw [mk_mem_nilpotentConeOrbits_iff] at hO
  exact Comodule.VectorOrbit.isNilpotentAd_mk_iff.mpr <|
    isNilpotent_ad_of_nilpotentConeIdeal_le_ker_lift_eval (H := FiniteTypeCommHopfAlgCat.of k H) hO

/-- For a connected group with Killing tangent Lie algebra, `nilpotentConeOrbits` coincides with
`IsNilpotentAd`. -/
@[simp]
theorem mem_nilpotentConeOrbits_iff_isNilpotentAd [LieAlgebra.IsKilling k 𝔤]
    {O : Comodule.VectorOrbit k H 𝔤} :
    O ∈ nilpotentConeOrbits k H ↔ O.IsNilpotentAd :=
  ⟨isNilpotentAd_of_mem_nilpotentConeOrbits, mem_nilpotentConeOrbits_of_isNilpotentAd⟩

/-- Set-level equality `nilpotentConeOrbits k H = {O | O.IsNilpotentAd}` for connected groups with
Killing tangent Lie algebra. -/
theorem nilpotentConeOrbits_eq_setOf_isNilpotentAd [LieAlgebra.IsKilling k 𝔤] :
    nilpotentConeOrbits k H = {O : Comodule.VectorOrbit k H 𝔤 | O.IsNilpotentAd} :=
  Set.ext fun _ ↦ mem_nilpotentConeOrbits_iff_isNilpotentAd

/-- **Reductive nilpotent-cone orbit criterion.** For a connected group with reductive tangent Lie
algebra, the orbit of `x ∈ 𝔤` lies in `nilpotentConeOrbits` iff `x ∈ ⁅𝔤, 𝔤⁆` and `ad x` is
nilpotent. -/
theorem mk_mem_nilpotentConeOrbits_iff_mem_derivedSeries_and_isNilpotent_ad
    [LieAlgebra.HasCentralRadical k 𝔤] {x : 𝔤} :
    (Comodule.VectorOrbit.mk x : Comodule.VectorOrbit k H 𝔤) ∈ nilpotentConeOrbits k H ↔
      x ∈ LieAlgebra.derivedSeries k 𝔤 1 ∧ IsNilpotent (LieAlgebra.ad k 𝔤 x) := by
  rw [mk_mem_nilpotentConeOrbits_iff]
  exact nilpotentConeIdeal_le_ker_lift_eval_iff_mem_derivedSeries_and_isNilpotent_ad
    (H := FiniteTypeCommHopfAlgCat.of k H)

/-- Every rational point of a connected group in characteristic zero fixes the centre `Z(𝔤)`
pointwise under the adjoint representation. -/
theorem basePointsRepresentation_eq_self_of_mem_center
    {z : 𝔤} (hz : z ∈ LieAlgebra.center k 𝔤) (g : WithConv (H →ₐ[k] k)) :
    Comodule.basePointsRepresentation 𝔤 g z = z := by
  rw [Comodule.basePointsRepresentation_apply,
    FiniteTypeCommHopfAlgCat.endOfPoint_tmul_of_mem_center (FiniteTypeCommHopfAlgCat.of k H) z hz
      g.ofConv 1,
    TensorProduct.lid_tmul, one_smul]

/-- Auxiliary map translating an orbit in `nilpotentConeOrbits` by a central element `z ∈ Z(𝔤)`. -/
private noncomputable def centerAddNilpotentConeOrbit
    (z : LieAlgebra.center k 𝔤) (O : Comodule.VectorOrbit k H 𝔤) : Comodule.VectorOrbit k H 𝔤 :=
  O.lift (fun y ↦ Comodule.VectorOrbit.mk ((z : 𝔤) + y)) fun g y ↦
    Comodule.VectorOrbit.mk_eq_mk_iff.mpr ⟨g⁻¹, by
      rw [map_add, basePointsRepresentation_eq_self_of_mem_center z.property,
        Representation.inv_self_apply]⟩

@[simp]
private theorem centerAddNilpotentConeOrbit_mk (z : LieAlgebra.center k 𝔤) (y : 𝔤) :
    centerAddNilpotentConeOrbit (k := k) (H := H) z (Comodule.VectorOrbit.mk y) =
      Comodule.VectorOrbit.mk ((z : 𝔤) + y) :=
  Comodule.VectorOrbit.lift_mk _ _ y

/-- **Decomposition of `ad`-nilpotent orbits for a reductive tangent Lie algebra.** For a connected
affine group in characteristic zero over an algebraically closed field with `𝔤` reductive, adding a
central element to a nilpotent-cone orbit gives a bijection
`Z(𝔤) × nilpotentConeOrbits k H ≃ {O : VectorOrbit k H 𝔤 // O.IsNilpotentAd}`. -/
noncomputable def centerProdNilpotentConeOrbitsEquiv [LieAlgebra.HasCentralRadical k 𝔤] :
    LieAlgebra.center k 𝔤 × nilpotentConeOrbits k H ≃
      {O : Comodule.VectorOrbit k H 𝔤 // O.IsNilpotentAd} :=
  Equiv.ofBijective
    (fun p ↦ ⟨centerAddNilpotentConeOrbit p.fst p.snd.val, by
      rcases p with ⟨z, ⟨O, hO⟩⟩
      induction O using Comodule.VectorOrbit.ind with | h y =>
      rw [centerAddNilpotentConeOrbit_mk, Comodule.VectorOrbit.isNilpotentAd_mk_iff,
        LieAlgebra.isNilpotent_ad_add_iff_of_mem_center_left z.property]
      exact Comodule.VectorOrbit.isNilpotentAd_mk_iff.mp
        (isNilpotentAd_of_mem_nilpotentConeOrbits hO)⟩)
    ⟨by
      rintro ⟨z₁, ⟨O₁, hO₁⟩⟩ ⟨z₂, ⟨O₂, hO₂⟩⟩ heq
      induction O₁ using Comodule.VectorOrbit.ind with | h y₁ =>
      induction O₂ using Comodule.VectorOrbit.ind with | h y₂ =>
      have heq' : (Comodule.VectorOrbit.mk ((z₁ : 𝔤) + y₁) : Comodule.VectorOrbit k H 𝔤) =
          Comodule.VectorOrbit.mk ((z₂ : 𝔤) + y₂) := by
        simpa only [centerAddNilpotentConeOrbit_mk] using congrArg Subtype.val heq
      obtain ⟨g, hg⟩ := Comodule.VectorOrbit.mk_eq_mk_iff.mp heq'
      rw [map_add, basePointsRepresentation_eq_self_of_mem_center z₁.property] at hg
      have hy₁ := (mk_mem_nilpotentConeOrbits_iff_mem_derivedSeries_and_isNilpotent_ad.mp hO₁).left
      have hy₂ := (mk_mem_nilpotentConeOrbits_iff_mem_derivedSeries_and_isNilpotent_ad.mp hO₂).left
      have hgy₁ : Comodule.basePointsRepresentation 𝔤 g y₁ ∈ LieAlgebra.derivedSeries k 𝔤 1 := by
        rw [← Derivation.basePointsAdjointLieEquiv_apply,
          ← LieIdeal.derivedSeries_map_eq 1 (Derivation.basePointsAdjointLieEquiv g).surjective]
        exact LieIdeal.mem_map hy₁
      have hz_eq : z₁ = z₂ := by
        have hsub : (z₁ : 𝔤) - z₂ = y₂ - Comodule.basePointsRepresentation 𝔤 g y₁ :=
          sub_eq_sub_iff_add_eq_add.mpr (hg.trans (add_comm _ _))
        have hmem : (z₁ : 𝔤) - z₂ ∈
            (LieAlgebra.center k 𝔤 ⊓ LieAlgebra.derivedSeries k 𝔤 1 : LieIdeal k 𝔤) :=
          ⟨sub_mem z₁.property z₂.property, hsub.symm ▸ sub_mem hy₂ hgy₁⟩
        rw [center_inf_derivedSeries_eq_bot k 𝔤, LieSubmodule.mem_bot, sub_eq_zero] at hmem
        exact Subtype.ext hmem
      subst hz_eq
      exact Prod.ext rfl (Subtype.ext <|
        Comodule.VectorOrbit.mk_eq_mk_iff.mpr ⟨g, add_left_cancel hg⟩),
     by
      rintro ⟨O, hO⟩
      induction O using Comodule.VectorOrbit.ind with | h x =>
      obtain ⟨z, hz, y, hy, hzy⟩ :=
        (isNilpotent_ad_iff_exists_mem_center_add_nilpotentConeIdeal_le_ker_lift_eval
          (H := FiniteTypeCommHopfAlgCat.of k H)).mp
          (Comodule.VectorOrbit.isNilpotentAd_mk_iff.mp hO)
      exact ⟨(⟨z, hz⟩, ⟨Comodule.VectorOrbit.mk y, mk_mem_nilpotentConeOrbits_iff.mpr hy⟩),
        Subtype.ext <| by dsimp only; rw [centerAddNilpotentConeOrbit_mk, hzy]⟩⟩

/-- On `(z, mk y)`, `centerProdNilpotentConeOrbitsEquiv` sends the pair to `mk (z + y)`. -/
@[simp]
theorem coe_centerProdNilpotentConeOrbitsEquiv_mk [LieAlgebra.HasCentralRadical k 𝔤]
    (z : LieAlgebra.center k 𝔤) {y : 𝔤}
    (hy : (Comodule.VectorOrbit.mk y : Comodule.VectorOrbit k H 𝔤) ∈ nilpotentConeOrbits k H) :
    (centerProdNilpotentConeOrbitsEquiv (k := k) (H := H) (z, ⟨Comodule.VectorOrbit.mk y, hy⟩) :
        Comodule.VectorOrbit k H 𝔤) =
      Comodule.VectorOrbit.mk ((z : 𝔤) + y) := by
  simp [centerProdNilpotentConeOrbitsEquiv, Equiv.ofBijective]

end ConnectedOrbits

end NilpotentConeOrbits

end TauCeti

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Representation.Comodule.Dual
public import TauCeti.Algebra.AlgebraicGroup.Representation.Fixed
public import TauCeti.Algebra.AlgebraicGroup.Tangent.FiniteType
public import TauCeti.Algebra.AlgebraicGroup.Tangent.Lie.Adjoint.Differential
public import TauCeti.Algebra.AlgebraicGroup.Representation.ComoduleAlgebra
public import TauCeti.Algebra.Lie.AdjointAction.InvariantZeroLocus
public import TauCeti.Algebra.Lie.TracePowerPolynomial
public import TauCeti.Algebra.Lie.Reductive.InvariantZeroLocus

/-!
# The nilpotent cone of an affine group

Let `G = Spec H` be an affine group over a field `k` with finite-dimensional Lie algebra `𝔤`,
modelled as the dual of the augmentation cotangent space. The polynomial functions on `𝔤` are the
symmetric algebra `O(𝔤) = Sym(𝔤*)`, and `G` acts on them through the contragredient of the adjoint
representation (`TauCeti.adjointPolynomialComoduleAlgebra`). The invariant functions
`O(𝔤)^G` (`TauCeti.adjointInvariantPolynomials`) form the coordinate ring of the adjoint
quotient `χ : 𝔤 → 𝔤 // G`. The **nilpotent cone** is the scheme-theoretic zero fibre `χ⁻¹(0)`:
its ideal (`TauCeti.nilpotentConeIdeal`) is generated in `O(𝔤)` by the invariant functions
vanishing at the origin. It is a homogeneous ideal, so the cone is stable under scaling, and it is
a subcomodule, so the cone is stable under the adjoint action of `G`
(`TauCeti.nilpotentConeSubcomodule`). The quotient ring is the full coordinate ring of the zero
fibre; no reduction is taken.

The infinitesimal adjoint action of `x ∈ 𝔤` on `O(𝔤)` is the coadjoint action of `x` by
derivations (`TauCeti.differential_adjointPolynomialComoduleAlgebra`), so every group invariant is
a Lie invariant `S(𝔤*)^𝔤`. For a connected group over an algebraically closed field of
characteristic zero, a vector is fixed by the group exactly when the Lie algebra kills it, and the
two rings of invariants coincide (`TauCeti.adjointInvariantPolynomials_eq_lieInvariants`). When
the Killing form of `𝔤` is nondegenerate, the Lie-invariant functions of positive degree cut out the
`ad`-nilpotent elements (`TauCeti.isNilpotent_ad_iff_forall_lift_eval_eq_zero`). Hence the
`k`-points of the nilpotent cone are exactly the `ad`-nilpotent elements of `𝔤`
(`TauCeti.nilpotentConeIdeal_le_ker_lift_eval_iff`). Each inclusion holds under weaker hypotheses:
`ad`-nilpotent elements lie on the cone for every group with nondegenerate Killing form in
characteristic zero, and points of the cone are `ad`-nilpotent for every connected group over an
algebraically closed field of characteristic zero.

When `𝔤` is only reductive, `𝔤 = Z(𝔤) ⊕ ⁅𝔤, 𝔤⁆`, the linear functions vanishing on `⁅𝔤, 𝔤⁆` are
invariants of degree one, and the cone is cut out inside `⁅𝔤, 𝔤⁆`: its `k`-points are the
`ad`-nilpotent elements of the derived ideal
(`TauCeti.nilpotentConeIdeal_le_ker_lift_eval_iff_mem_derivedSeries_and_isNilpotent_ad`). These
have zero central coordinate (`TauCeti.nilpotentConeIdeal_le_ker_lift_eval_add_iff`), whereas
the `ad`-nilpotent elements of `𝔤` form the larger set `Z(𝔤) × 𝒩(⁅𝔤, 𝔤⁆)`: they are the sums of a
central element and a point of the cone
(`TauCeti.isNilpotent_ad_iff_exists_mem_center_add_nilpotentConeIdeal_le_ker_lift_eval`).

## Main declarations

* `TauCeti.adjointPolynomialComoduleAlgebra`: the action of `G` on the polynomial functions on `𝔤`,
  with coaction on linear functions `TauCeti.adjointPolynomialComoduleAlgebra_coact_ι`.
* `TauCeti.adjointInvariantPolynomials`: the invariant polynomial functions `O(𝔤)^G`.
* `TauCeti.adjointInvariantPolynomials_le_lieInvariants` and
  `TauCeti.adjointInvariantPolynomials_eq_lieInvariants`: they are Lie invariants, and for
  connected `G` over an algebraically closed field of characteristic zero they are all of them.
* `TauCeti.nilpotentConeIdeal`: the ideal of the zero fibre of the adjoint quotient.
* `TauCeti.nilpotentConeIdeal_isHomogeneous` and `TauCeti.nilpotentConeSubcomodule`: it is
  stable under scaling and under the adjoint action.
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

## References

* B. Kostant, *Lie group representations on polynomial rings*, Amer. J. Math. 85 (1963),
  327–404.
* D. H. Collingwood and W. M. McGovern, *Nilpotent Orbits in Semisimple Lie Algebras*, Van
  Nostrand Reinhold, 1993, §1.3 and §3.2.
* J. S. Milne, *Algebraic Groups* (2017), Chapter 10.
-/

public section

open scoped TensorProduct

namespace TauCeti

universe u

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
quotient map `𝔤 → 𝔤 // G`. -/
noncomputable def nilpotentConeIdeal : Ideal (SymmetricAlgebra k (Module.Dual k 𝔤)) :=
  Ideal.span {p | p ∈ adjointInvariantPolynomials k H ∧ SymmetricAlgebra.algebraMapInv p = 0}

/-- An invariant polynomial function vanishing at the origin lies in the ideal of the nilpotent
cone. -/
theorem mem_nilpotentConeIdeal_of_mem_adjointInvariantPolynomials
    {p : SymmetricAlgebra k (Module.Dual k 𝔤)} (hp : p ∈ adjointInvariantPolynomials k H)
    (hp₀ : SymmetricAlgebra.algebraMapInv p = 0) : p ∈ nilpotentConeIdeal k H :=
  Ideal.subset_span ⟨hp, hp₀⟩

/-- **The universal property of the ideal of the nilpotent cone.** An ideal contains it exactly
when it contains every invariant polynomial function vanishing at the origin. -/
theorem nilpotentConeIdeal_le_iff {I : Ideal (SymmetricAlgebra k (Module.Dual k 𝔤))} :
    nilpotentConeIdeal k H ≤ I ↔
      ∀ p ∈ adjointInvariantPolynomials k H, SymmetricAlgebra.algebraMapInv p = 0 → p ∈ I := by
  rw [nilpotentConeIdeal, Ideal.span_le]
  exact ⟨fun h p hp hp₀ ↦ h ⟨hp, hp₀⟩, fun h p hp ↦ h p hp.1 hp.2⟩

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
      (SymmetricAlgebra.homogeneousSubmodule k (Module.Dual k 𝔤)) := by
  classical
  let _ : Comodule k H (Module.Dual k 𝔤) := Comodule.dual k H 𝔤
  let 𝒜 := SymmetricAlgebra.homogeneousSubmodule k (Module.Dual k 𝔤)
  rw [Ideal.IsHomogeneous.iff_eq]
  refine le_antisymm (Ideal.toIdeal_homogeneousCore_le _ _)
    (nilpotentConeIdeal_le_iff.mpr fun p hp hp₀ ↦ ?_)
  rw [← DirectSum.sum_support_decompose 𝒜 p]
  refine Ideal.sum_mem _ fun n _ ↦
    Ideal.mem_homogeneousCore_of_homogeneous_of_mem (𝒜 := 𝒜) ⟨n, SetLike.coe_mem _⟩ ?_
  refine mem_nilpotentConeIdeal_of_mem_adjointInvariantPolynomials
    (ComoduleAlgebra.decompose_mem_coinvariants_symmetricAlgebra hp n) ?_
  -- The augmentation ideal is the irrelevant ideal, which is homogeneous.
  have h := (HomogeneousIdeal.irrelevant 𝒜).isHomogeneous n
    (show p ∈ (HomogeneousIdeal.irrelevant 𝒜).toIdeal by
      rw [SymmetricAlgebra.toIdeal_irrelevant_eq_ker_algebraMapInv]
      exact hp₀)
  rwa [SymmetricAlgebra.toIdeal_irrelevant_eq_ker_algebraMapInv] at h

/-- **The nilpotent cone is stable under the adjoint action.** The coaction carries its ideal into
the ideal it generates in `O(𝔤) ⊗ H`, since it is generated by invariants. -/
theorem coact_mem_map_includeLeft_nilpotentConeIdeal {p : SymmetricAlgebra k (Module.Dual k 𝔤)}
    (hp : p ∈ nilpotentConeIdeal k H) :
    Comodule.coact (R := k) (C := H) p ∈
      (nilpotentConeIdeal k H).map (Algebra.TensorProduct.includeLeft (R := k) (S := k)
        (A := SymmetricAlgebra k (Module.Dual k 𝔤)) (B := H)) :=
  ComoduleAlgebra.coact_mem_map_includeLeft_span (fun _ ↦ And.left) hp

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
  ComoduleAlgebra.mem_spanSubcomodule _

/-- **Nilpotent elements lie on the nilpotent cone.** Over a field of characteristic zero, if the
Killing form of the Lie algebra is nondegenerate, then evaluation at an `ad`-nilpotent element kills
the ideal of the nilpotent cone. -/
theorem nilpotentConeIdeal_le_ker_lift_eval_of_isNilpotent [CharZero k]
    [LieAlgebra.IsKilling k 𝔤] {x : 𝔤} (hx : IsNilpotent (LieAlgebra.ad k 𝔤 x)) :
    nilpotentConeIdeal k H ≤ RingHom.ker (SymmetricAlgebra.lift (Module.Dual.eval k 𝔤 x)) :=
  nilpotentConeIdeal_le_iff.mpr fun p hp hp₀ ↦
    isNilpotent_ad_iff_forall_lift_eval_eq_zero.mp hx p
      (adjointInvariantPolynomials_le_lieInvariants hp) hp₀

end Basic

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

end Connected

end TauCeti

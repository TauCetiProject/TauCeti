/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.LocalCoefficient.QuotientCovering.Sign
public import TauCeti.AlgebraicTopology.Singular.Twisted.GroupHomology
public import TauCeti.Topology.VectorBundle.Orientation.Cover.Quotient
public import TauCeti.Topology.VectorBundle.Orientation.LocalSystem

/-!
# The orientation local system as the local system of the sign representation

Let `E → B` be a real vector bundle of rank `card ι`, and `B'` its orientation double cover, the
quotient of a free action of `ℤˣ` whose element `-1` reverses orientations
(`TauCeti.VectorBundleOrientationCover.isQuotientCoveringMap_proj`). For a commutative ring `k`,
the orientation local system `o(E)` (`TauCeti.VectorBundleOrientationCover.signLocalSystem`) is the
sign local system of the deck involution, and so it is the local system on `B` associated to the
sign representation of `ℤˣ` on `k`
(`TauCeti.VectorBundleOrientationCover.associatedLocalSystemSignIso`): the class of `a ⊗ r[o]`, for
an orientation `o` of a fibre `E_b`, is the element of `o(E)_b` whose value at `o` is `r * a`.

Consequently the chains of `B` with coefficients in `o(E)` are the coinvariants of the chains of the
orientation cover tensored with the sign representation,

`(k_sign ⊗ C(B'; k))_{ℤˣ} ≅ C(B; o(E))`

(`TauCeti.VectorBundleOrientationCover.coinvariantsTensorSingularChainsRepIsoTwisted`). This holds
over every commutative ring, `ℤ` included, with no orientation of `E`. It describes the
orientation-twisted homology of the base, which is the target of the Thom isomorphism
`H_{p + r}(E, E₀; k) ≅ H_p(B; o(E))` of a possibly non-orientable bundle of rank `r`, through
equivariant chain complexes over the orientation cover, on which the pulled-back bundle is
oriented. Over a ring in which `2` is invertible the twisted homology of `B` is also the part of
the homology of `B'` on which the deck involution acts by `-1`
(`IsCoveringMap.signHomologyLinearEquiv`); the coinvariant description needs no such hypothesis.

## Main definitions

* `TauCeti.VectorBundleOrientationCover.projectionHom`: the projection of the orientation double
  cover as a morphism of topological spaces.
* `TauCeti.VectorBundleOrientationCover.associatedLocalSystemSignIso`: the local system associated
  to the sign representation of `ℤˣ` is the orientation local system.
* `TauCeti.VectorBundleOrientationCover.coinvariantsTensorSingularChainsRepIsoTwisted`: the chains
  of the base twisted by the orientation local system are the sign coinvariants of the chains of
  the orientation cover.

## References

* J. W. Milnor, J. D. Stasheff, *Characteristic Classes*, Annals of Mathematics Studies 76,
  Princeton (1974), §12 (the orientation double cover and twisted coefficients).
* A. Hatcher, *Algebraic Topology*, Section 3.H (local coefficients and the orientation double
  cover).
* K. S. Brown, *Cohomology of Groups*, Springer, 1982, Sections II.4 and III.1.
-/

public section

noncomputable section

open Bundle CategoryTheory Module TauCeti.LocalCoefficientSystem

namespace TauCeti.VectorBundleOrientationCover

variable {B : Type} [TopologicalSpace B] {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {E : B → Type} [TopologicalSpace (TotalSpace F E)] [∀ b, AddCommMonoid (E b)]
  [∀ b, Module ℝ (E b)] [∀ b, TopologicalSpace (E b)] [FiberBundle F E] [VectorBundle ℝ F E]
  {ι : Type} [Fintype ι] [FiniteDimensional ℝ F] (hι : Fintype.card ι = finrank ℝ F)
  (k : Type) [CommRing k]

variable (F E ι) in
/-- The projection of the orientation double cover, as a morphism of topological spaces. -/
abbrev projectionHom : TopCat.of (VectorBundleOrientationCover F E ι) ⟶ TopCat.of B :=
  TopCat.ofHom projection

variable (F E) in
include hι in
/-- The orientation double cover is the quotient of the action of `ℤˣ`
(`isQuotientCoveringMap_proj`), read on `projectionHom`. -/
theorem isQuotientCoveringMap_projectionHom :
    IsQuotientCoveringMap (projectionHom F E ι) ℤˣ :=
  isQuotientCoveringMap_proj hι

/-- **The orientation local system is the local system of the sign representation.** The local
system on `B` associated to the sign representation of `ℤˣ` on `k`, through the orientation double
cover, is the orientation local system `o(E)`: the class of `a ⊗ r[o]`, for an orientation `o` of a
fibre, goes to the element of `o(E)` whose value at `o` is `r * a`
(`associatedLocalSystemSignIso_hom_app_coinvariantsTensorMk`). -/
def associatedLocalSystemSignIso :
    (isQuotientCoveringMap_projectionHom F E hι).associatedLocalSystem k
        (Rep.ofDistribMulAction k ℤˣ k) ≅
      signLocalSystem F E k hι :=
  (isQuotientCoveringMap_projectionHom F E hι).associatedLocalSystemSignIso k
    fun p ↦ (neg_one_smul_eq_deck p).symm

/-- The identification of the local system of the sign representation with the orientation local
system sends the class of `a ⊗ r[o]` to the element whose value at the orientation `o` is
`r * a`. -/
-- Not a simp lemma: `simp` unfolds `Rep.coinvariantsTensorMk` on the left-hand side first.
lemma associatedLocalSystemSignIso_hom_app_coinvariantsTensorMk
    {x : FundamentalGroupoid (TopCat.of B)} (o : projectionHom F E ι ⁻¹' {x.as}) (a r : k) :
    (signLocalSystemObjEquiv hι x (((associatedLocalSystemSignIso hι k).hom.app x).hom
        (Rep.coinvariantsTensorMk (Rep.ofDistribMulAction k ℤˣ k)
          (Rep.of ((isQuotientCoveringMap_projectionHom F E hι).fiberRepresentation k x.as)) a
          (Finsupp.single o r))) : _ → k) o =
      r * a := by
  -- `o(E)` is the sign local system of the deck involution by definition.
  rw [← signLocalSystemObjEquiv_eqToIso_signLocalSystem_def_hom_app]
  exact IsQuotientCoveringMap.associatedLocalSystemSignIso_hom_app_coinvariantsTensorMk
    (isQuotientCoveringMap_projectionHom F E hι) k
    (σ := (deck (F := F) (E := E) (ι := ι) : C(_, _))) (fun p ↦ (neg_one_smul_eq_deck p).symm) o a r

/-- The inverse identification of the orientation local system with the local system of the sign
representation sends `f` to the class of `f o ⊗ [o]`, for any orientation `o` of the fibre. -/
@[simp]
lemma associatedLocalSystemSignIso_inv_app_apply {x : FundamentalGroupoid (TopCat.of B)}
    (o : projectionHom F E ι ⁻¹' {x.as}) (f : (signLocalSystem F E k hι).obj x) :
    ((associatedLocalSystemSignIso hι k).inv.app x).hom f =
      Rep.coinvariantsTensorMk (Rep.ofDistribMulAction k ℤˣ k)
        (Rep.of ((isQuotientCoveringMap_projectionHom F E hι).fiberRepresentation k x.as))
        ((signLocalSystemObjEquiv hι x f : _ → k) o) (Finsupp.single o 1) := by
  -- `o(E)` is the sign local system of the deck involution by definition.
  rw [← signLocalSystemObjEquiv_eqToIso_signLocalSystem_def_hom_app]
  exact (isQuotientCoveringMap_projectionHom F E hι).associatedLocalSystemSignIso_inv_app_apply k
    (σ := (deck (F := F) (E := E) (ι := ι) : C(_, _))) (fun p ↦ (neg_one_smul_eq_deck p).symm) o
    ((eqToIso (signLocalSystem_def hι)).hom.app x f)

/-- **Orientation-twisted chains of the base are sign coinvariants of the chains of the orientation
cover.** For a commutative ring `k`, the chains of `B` with coefficients in the orientation local
system `o(E)` are the coinvariants `(k_sign ⊗ C(B'; k))_{ℤˣ}` of the singular chains of the
orientation double cover `B'`, tensored with the sign representation. The class of `a ⊗ τ` goes to
the simplex `p ∘ τ` with the coefficient of `o(E)` whose value at the initial orientation of `τ` is
`a`. -/
def coinvariantsTensorSingularChainsRepIsoTwisted :
    haveI := (isQuotientCoveringMap_projectionHom F E hι).toContinuousConstSMul
    (singularChainsRep k (TopCat.of (VectorBundleOrientationCover F E ι)) ℤˣ).coinvariantsTensorObj
        (Rep.ofDistribMulAction k ℤˣ k) ≅
      twistedChainComplex (signLocalSystem F E k hι) :=
  (isQuotientCoveringMap_projectionHom F E hι).coinvariantsTensorSingularChainsRepIsoTwisted k _ ≪≫
    twistedChainComplexCoefficientIso (associatedLocalSystemSignIso hι k)

end TauCeti.VectorBundleOrientationCover

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

open Bundle CategoryTheory Module Simplicial TauCeti.LocalCoefficientSystem

namespace TauCeti.VectorBundleOrientationCover

variable {B : Type} [TopologicalSpace B] {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {E : B → Type} [TopologicalSpace (TotalSpace F E)] [∀ b, AddCommMonoid (E b)]
  [∀ b, Module ℝ (E b)] [∀ b, TopologicalSpace (E b)] [FiberBundle F E] [VectorBundle ℝ F E]
  {ι : Type} [Fintype ι] [FiniteDimensional ℝ F] (hι : Fintype.card ι = finrank ℝ F)
  (k : Type) [CommRing k]

/-- **The orientation local system is the local system of the sign representation.** The local
system on `B` associated to the sign representation of `ℤˣ` on `k`, through the orientation double
cover, is the orientation local system `o(E)`: the class of `a ⊗ r[o]`, for an orientation `o` of a
fibre, goes to the element of `o(E)` whose value at `o` is `r * a`
(`associatedLocalSystemSignIso_hom_app_coinvariantsTensorMk`). -/
def associatedLocalSystemSignIso :
    IsQuotientCoveringMap.associatedLocalSystem
        (E := TopCat.of (VectorBundleOrientationCover F E ι)) (p := TopCat.ofHom projection)
        (isQuotientCoveringMap_proj hι) k (Rep.ofDistribMulAction k ℤˣ k) ≅
      signLocalSystem F E k hι :=
  IsQuotientCoveringMap.associatedLocalSystemSignIso
    (E := TopCat.of (VectorBundleOrientationCover F E ι)) (p := TopCat.ofHom projection)
    (isQuotientCoveringMap_proj hι) k fun p ↦ (neg_one_smul_eq_deck p).symm

/-- The identification of the local system of the sign representation with the orientation local
system sends the class of `a ⊗ r[o]` to the element whose value at the orientation `o` is
`r * a`. -/
-- Not a simp lemma: `simp` unfolds `Rep.coinvariantsTensorMk` on the left-hand side first.
lemma associatedLocalSystemSignIso_hom_app_coinvariantsTensorMk
    {x : FundamentalGroupoid (TopCat.of B)}
    (o : (TopCat.ofHom (projection (F := F) (E := E) (ι := ι))) ⁻¹' {x.as}) (a r : k) :
    (signLocalSystemObjEquiv hι x (((associatedLocalSystemSignIso hι k).hom.app x).hom
        (Rep.coinvariantsTensorMk (Rep.ofDistribMulAction k ℤˣ k)
          (Rep.of (IsQuotientCoveringMap.fiberRepresentation
            (E := TopCat.of (VectorBundleOrientationCover F E ι)) (p := TopCat.ofHom projection)
            (isQuotientCoveringMap_proj hι) k x.as)) a
          (Finsupp.single o r))) : _ → k) o =
      r * a := by
  -- `o(E)` is the sign local system of the deck involution by definition.
  rw [← signLocalSystemObjEquiv_eqToIso_signLocalSystem_def_hom_app]
  exact IsQuotientCoveringMap.associatedLocalSystemSignIso_hom_app_coinvariantsTensorMk
    (E := TopCat.of (VectorBundleOrientationCover F E ι)) (p := TopCat.ofHom projection)
    (isQuotientCoveringMap_proj hι) k
    (σ := (deck (F := F) (E := E) (ι := ι) : C(_, _))) (fun p ↦ (neg_one_smul_eq_deck p).symm) o a r

/-- The identification of the local system of the sign representation with the orientation local
system sends the class of `a ⊗ f`, for a formal sum `f` of orientations of the fibre, to `a` times
the function `o ↦ f o - f (-o)` on the orientations of the fibre. -/
-- Not a simp lemma: `simp` unfolds `Rep.coinvariantsTensorMk` on the left-hand side first.
lemma signLocalSystemObjEquiv_associatedLocalSystemSignIso_hom_app_apply
    {x : FundamentalGroupoid (TopCat.of B)} (a : k)
    (f : (TopCat.ofHom (projection (F := F) (E := E) (ι := ι))) ⁻¹' {x.as} →₀ k)
    (o : (TopCat.ofHom (projection (F := F) (E := E) (ι := ι))) ⁻¹' {x.as}) :
    (signLocalSystemObjEquiv hι x (((associatedLocalSystemSignIso hι k).hom.app x).hom
        (Rep.coinvariantsTensorMk (Rep.ofDistribMulAction k ℤˣ k)
          (Rep.of (IsQuotientCoveringMap.fiberRepresentation
            (E := TopCat.of (VectorBundleOrientationCover F E ι)) (p := TopCat.ofHom projection)
            (isQuotientCoveringMap_proj hι) k x.as)) a f)) : _ → k) o =
      a * (f o - f (Function.fiberMap deck (funext proj_deck) x.as o)) := by
  -- `o(E)` is the sign local system of the deck involution by definition.
  rw [← signLocalSystemObjEquiv_eqToIso_signLocalSystem_def_hom_app]
  refine (congrArg (fun w ↦ ((isCoveringMap_proj (F := F) (E := E) hι).signLocalSystemObjEquiv _
      proj_comp_deck x w : _ → k) o)
    (IsQuotientCoveringMap.associatedLocalSystemSignIso_hom_app_coinvariantsTensorMk_eq_smul
      (E := TopCat.of (VectorBundleOrientationCover F E ι)) (p := TopCat.ofHom projection)
      (isQuotientCoveringMap_proj hι) k
      (σ := (deck (F := F) (E := E) (ι := ι) : C(_, _))) (fun p ↦ (neg_one_smul_eq_deck p).symm)
      a f)).trans ?_
  rw [map_smul, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul]
  -- The fibres of `proj` and of the projection as a morphism of spaces are the same sets.
  exact congrArg (a * ·) ((isQuotientCoveringMap_proj (F := F) (E := E) hι).isCoveringMap
    |>.signLocalSystemObjEquiv_permutationLocalSystemToSignApp_apply k _ _ x f o)

/-- The inverse identification of the orientation local system with the local system of the sign
representation sends `f` to the class of `f o ⊗ [o]`, for any orientation `o` of the fibre. -/
-- Not a simp lemma: the orientation `o` occurs only on the right-hand side.
lemma associatedLocalSystemSignIso_inv_app_apply {x : FundamentalGroupoid (TopCat.of B)}
    (o : (TopCat.ofHom (projection (F := F) (E := E) (ι := ι))) ⁻¹' {x.as})
    (f : (signLocalSystem F E k hι).obj x) :
    ((associatedLocalSystemSignIso hι k).inv.app x).hom f =
      Rep.coinvariantsTensorMk (Rep.ofDistribMulAction k ℤˣ k)
        (Rep.of (IsQuotientCoveringMap.fiberRepresentation
          (E := TopCat.of (VectorBundleOrientationCover F E ι)) (p := TopCat.ofHom projection)
          (isQuotientCoveringMap_proj hι) k x.as))
        ((signLocalSystemObjEquiv hι x f : _ → k) o) (Finsupp.single o 1) := by
  -- `o(E)` is the sign local system of the deck involution by definition.
  rw [← signLocalSystemObjEquiv_eqToIso_signLocalSystem_def_hom_app]
  exact IsQuotientCoveringMap.associatedLocalSystemSignIso_inv_app_apply
    (E := TopCat.of (VectorBundleOrientationCover F E ι)) (p := TopCat.ofHom projection)
    (isQuotientCoveringMap_proj hι) k
    (σ := (deck (F := F) (E := E) (ι := ι) : C(_, _))) (fun p ↦ (neg_one_smul_eq_deck p).symm) o
    ((eqToIso (signLocalSystem_def hι)).hom.app x f)

/-- **Orientation-twisted chains of the base are sign coinvariants of the chains of the orientation
cover.** For a commutative ring `k`, the chains of `B` with coefficients in the orientation local
system `o(E)` are the coinvariants `(k_sign ⊗ C(B'; k))_{ℤˣ}` of the singular chains of the
orientation double cover `B'`, tensored with the sign representation. The class of `a ⊗ τ` goes to
the simplex `p ∘ τ` with the coefficient of `o(E)` whose value at the initial orientation of `τ` is
`a` (`coinvariantsTensorSingularChainsRepIsoTwisted_hom_f_mk`). -/
def coinvariantsTensorSingularChainsRepIsoTwisted :
    (singularChainsRep k (TopCat.of (VectorBundleOrientationCover F E ι)) ℤˣ).coinvariantsTensorObj
        (Rep.ofDistribMulAction k ℤˣ k) ≅
      twistedChainComplex (signLocalSystem F E k hι) :=
  IsQuotientCoveringMap.coinvariantsTensorSingularChainsRepIsoTwisted
      (E := TopCat.of (VectorBundleOrientationCover F E ι)) (p := TopCat.ofHom projection)
      (isQuotientCoveringMap_proj hι) k _ ≪≫
    twistedChainComplexCoefficientIso (associatedLocalSystemSignIso hι k)

/-- The identification of the sign coinvariants of the chains of the orientation cover with the
orientation-twisted chains of the base sends the class of `a ⊗ τ` to the simplex `p ∘ τ` with the
coefficient of `o(E)` whose value at the initial orientation of `τ` is `a`. -/
theorem coinvariantsTensorSingularChainsRepIsoTwisted_hom_f_mk (n : ℕ) (a : k)
    (τ : (TopCat.toSSet.obj (TopCat.of (VectorBundleOrientationCover F E ι))) _⦋n⦌) :
    ((coinvariantsTensorSingularChainsRepIsoTwisted hι k).hom.f n).hom
        (Rep.coinvariantsTensorMk (Rep.ofDistribMulAction k ℤˣ k)
          (Rep.of (singularChainsRepresentation k
            (TopCat.of (VectorBundleOrientationCover F E ι)) ℤˣ n)) a (simplexChain τ 1)) =
      (ιTwistedChainComplex (signLocalSystem F E k hι) n
        ((TopCat.toSSet.map (TopCat.ofHom projection)).app _ τ)).hom
          ((signLocalSystemObjEquiv hι _).symm
            ((signFiberEquiv deck_ne_self (fun _ _ h ↦ eq_or_eq_deck hι h)
              (initialSheet τ)).symm a)) := by
  rw [coinvariantsTensorSingularChainsRepIsoTwisted, Iso.trans_hom, HomologicalComplex.comp_f,
    twistedChainComplexCoefficientIso_hom, ModuleCat.hom_comp]
  refine (LinearMap.comp_apply _ _ _).trans ?_
  -- The comparison of the quotient cover, then the change of coefficients on the summand of
  -- `p ∘ τ`.
  refine (congrArg
    ((twistedChainComplexCoefficientMap (associatedLocalSystemSignIso hι k).hom).f n).hom
    (IsQuotientCoveringMap.coinvariantsTensorSingularChainsRepIsoTwisted_hom_f_mk
      (E := TopCat.of (VectorBundleOrientationCover F E ι)) (p := TopCat.ofHom projection)
      (isQuotientCoveringMap_proj hι) k n a τ)).trans ?_
  refine (twistedChainComplexCoefficientMap_f_ι_apply _ n _ _).trans ?_
  refine congrArg (ιTwistedChainComplex (signLocalSystem F E k hι) n _).hom
    ((signLocalSystemObjEquiv hι _).injective ?_)
  rw [LinearEquiv.apply_symm_apply]
  refine (signFiberEquiv deck_ne_self (fun _ _ h ↦ eq_or_eq_deck hι h)
    (initialSheet τ)).injective ?_
  rw [LinearEquiv.apply_symm_apply, signFiberEquiv_apply]
  -- The summand of `p ∘ τ` carries the permutation representation of the fibre over its initial
  -- vertex.
  exact (associatedLocalSystemSignIso_hom_app_coinvariantsTensorMk hι k (initialSheet τ) a 1).trans
    (one_mul a)

end TauCeti.VectorBundleOrientationCover

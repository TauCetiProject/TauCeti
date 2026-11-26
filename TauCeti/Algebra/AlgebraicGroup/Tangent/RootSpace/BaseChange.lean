/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Tangent.RootSpace
public import TauCeti.Algebra.AlgebraicGroup.Tangent.Representation.BaseChange
public import TauCeti.Algebra.AlgebraicGroup.DiagonalizableGroup.Weight.BaseChange
public import TauCeti.Algebra.AlgebraicGroup.SplitTorus.Maximal
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
import Mathlib.LinearAlgebra.TensorProduct.Decomposition

/-!
# Base change of adjoint weight spaces and roots

Let `G = Spec H` be an affine group over `R` with finite projective cotangent space, let
`π : H → R[M]` be the coordinate morphism of a homomorphism `D(M) → G`, and let `S` be a
commutative `R`-algebra. Base change gives `G_S = Spec (S ⊗[R] H)` and a homomorphism
`πS : S ⊗[R] H → S[M]` agreeing with `π` on `1 ⊗ h`. The Lie algebra of `G_S` is the scalar
extension of that of `G` (`Derivation.cotangentDualBaseChangeEquiv`), compatibly with the
adjoint representations (`Derivation.map_coact_cotangentDualBaseChangeEquiv`).

This file deduces that **the adjoint weight spaces and the roots commute with base change**:

* every weight space `𝔤_{S,α}` of `G_S` is the image of the base change of `𝔤_α`, with no flatness
  assumption;
* `S ⊗[R] 𝔤_α ≃ₗ[S] 𝔤_{S,α}`, again without flatness since `𝔤_α` is a direct summand, so a free
  root space keeps its rank;
* when `R → S` is injective, for instance faithfully flat, `G_S` and `G` have the same nontrivial
  adjoint weights: the Lie algebra is projective, so its scalar extension along `R → S` is
  injective.

For a chosen split maximal torus `T` (`TauCeti.SplitMaximalTorus`) and its base change
`T.baseChange S` these specialize to the root spaces and the roots of the split pair `(G, T)`:
`TauCeti.SplitMaximalTorus.adjointWeightSpace_baseChange` and
`TauCeti.SplitMaximalTorus.nontrivialAdjointWeights_baseChange`.

## Main results

* `Derivation.adjointWeightSpace_baseChange`: `𝔤_{S,α}` is the image of `(𝔤_α).baseChange S`.
* `Derivation.adjointWeightSpaceBaseChangeEquiv`: the linear equivalence
  `S ⊗[R] 𝔤_α ≃ₗ[S] 𝔤_{S,α}`.
* `Derivation.finrank_adjointWeightSpace_baseChange`: a free weight space keeps its rank.
* `Derivation.nontrivialAdjointWeights_baseChange`: along an injective map `R → S`, the nontrivial
  adjoint weights are unchanged.
* `TauCeti.SplitMaximalTorus.adjointWeightSpace_baseChange`,
  `TauCeti.SplitMaximalTorus.finrank_adjointWeightSpace_baseChange` and
  `TauCeti.SplitMaximalTorus.nontrivialAdjointWeights_baseChange`: the root spaces, their
  dimensions and the roots of a chosen split maximal torus commute with base change.

## References

* J. S. Milne, *Algebraic Groups* (2017), §21.a (the roots of a split reductive group).
-/

public section

open scoped TensorProduct

namespace Derivation

open TauCeti

universe u v

variable {R S : Type u} {H : Type v} [CommRing R] [CommRing S] [Algebra R S] [CommRing H]
  [HopfAlgebra R H]
  [Module.Finite R (Bialgebra.CotangentSpace R H)]
  [Module.Projective R (Bialgebra.CotangentSpace R H)]
  [Module.Finite S (Bialgebra.CotangentSpace S (S ⊗[R] H))]
  [Module.Projective S (Bialgebra.CotangentSpace S (S ⊗[R] H))]
variable {M : Type*} [CommGroup M]

/-- **Adjoint weight spaces commute with base change.** If `πS : S ⊗[R] H → S[M]` agrees with
`π : H → R[M]` on `1 ⊗ h`, then the `α`-weight space of the Lie algebra of `Spec (S ⊗[R] H)` is
the image of the base change of the `α`-weight space of the Lie algebra of `Spec H`.

No flatness of `S` over `R` is assumed. -/
theorem adjointWeightSpace_baseChange (π : H →ₐc[R] MonoidAlgebra R M)
    (πS : S ⊗[R] H →ₐc[S] MonoidAlgebra S M)
    (hπ : ∀ h, πS (1 ⊗ₜ h) = MonoidAlgebra.mapAlgHom M (Algebra.ofId R S) (π h)) (α : M) :
    adjointWeightSpace πS α =
      ((adjointWeightSpace π α).baseChange S).map
        (cotangentDualBaseChangeEquiv R S H).toLinearMap := by
  let _ := adjointComodule (R := R) (H := H)
  let _ := adjointComodule (R := S) (H := S ⊗[R] H)
  let _ := Comodule.baseChange (R := R) (H := H)
    (M := Module.Dual R (Bialgebra.CotangentSpace R H)) S
  -- The comparison of Lie algebras is a comodule morphism, so it pulls weight spaces back.
  let e : Comodule.Hom S (S ⊗[R] H) (S ⊗[R] Module.Dual R (Bialgebra.CotangentSpace R H))
      (Module.Dual S (Bialgebra.CotangentSpace S (S ⊗[R] H))) :=
    { toLinearMap := (cotangentDualBaseChangeEquiv R S H).toLinearMap
      map_coact := map_coact_cotangentDualBaseChangeEquiv }
  have hcomap := DiagonalizableGroup.weightSpace_eq_comap_of_injective πS.toCoalgHom e
    (cotangentDualBaseChangeEquiv R S H).injective α
  rw [DiagonalizableGroup.weightSpace_baseChange (Module.Dual R (Bialgebra.CotangentSpace R H))
    π.toCoalgHom πS.toCoalgHom hπ α] at hcomap
  rw [adjointWeightSpace_eq_weightSpace, adjointWeightSpace_eq_weightSpace, hcomap]
  exact (Submodule.map_comap_eq_of_surjective (cotangentDualBaseChangeEquiv R S H).surjective
    _).symm

/-- The scalar extension of the adjoint weight space `𝔤_α` is the adjoint weight space of the
base change, through the comparison of Lie algebras. No flatness is needed, since `𝔤_α` is a
direct summand of the Lie algebra. -/
noncomputable def adjointWeightSpaceBaseChangeEquiv (π : H →ₐc[R] MonoidAlgebra R M)
    (πS : S ⊗[R] H →ₐc[S] MonoidAlgebra S M)
    (hπ : ∀ h, πS (1 ⊗ₜ h) = MonoidAlgebra.mapAlgHom M (Algebra.ofId R S) (π h)) (α : M) :
    S ⊗[R] adjointWeightSpace π α ≃ₗ[S] adjointWeightSpace πS α :=
  (LinearEquiv.ofBijective ((adjointWeightSpace π α).toBaseChange S) <| by
    classical
    exact DirectSum.IsInternal.toBaseChange_bijective _ (isInternal_adjointWeightSpace π) α).trans
    (((cotangentDualBaseChangeEquiv R S H).submoduleMap _).trans
      (LinearEquiv.ofEq _ _ (adjointWeightSpace_baseChange π πS hπ α).symm))

/-- The equivalence `S ⊗[R] 𝔤_α ≃ₗ[S] 𝔤_{S,α}` is the comparison of Lie algebras. -/
@[simp]
theorem coe_adjointWeightSpaceBaseChangeEquiv_tmul (π : H →ₐc[R] MonoidAlgebra R M)
    (πS : S ⊗[R] H →ₐc[S] MonoidAlgebra S M)
    (hπ : ∀ h, πS (1 ⊗ₜ h) = MonoidAlgebra.mapAlgHom M (Algebra.ofId R S) (π h)) (α : M)
    (s : S) (x : adjointWeightSpace π α) :
    (adjointWeightSpaceBaseChangeEquiv π πS hπ α (s ⊗ₜ x) :
        Module.Dual S (Bialgebra.CotangentSpace S (S ⊗[R] H))) =
      cotangentDualBaseChangeEquiv R S H (s ⊗ₜ (x : Module.Dual R
        (Bialgebra.CotangentSpace R H))) := by
  simp only [adjointWeightSpaceBaseChangeEquiv, LinearEquiv.trans_apply,
    LinearEquiv.coe_ofEq_apply, LinearEquiv.submoduleMap_apply]
  rw [LinearEquiv.ofBijective_apply, Submodule.coe_toBaseChange_tmul]

/-- **A free adjoint weight space keeps its rank under base change** to a nontrivial ring. In
particular the dimension of a root space does not change under extension of the base field. -/
theorem finrank_adjointWeightSpace_baseChange [Nontrivial S]
    (π : H →ₐc[R] MonoidAlgebra R M) (πS : S ⊗[R] H →ₐc[S] MonoidAlgebra S M)
    (hπ : ∀ h, πS (1 ⊗ₜ h) = MonoidAlgebra.mapAlgHom M (Algebra.ofId R S) (π h)) (α : M)
    [Module.Free R (adjointWeightSpace π α)] :
    Module.finrank S (adjointWeightSpace πS α) = Module.finrank R (adjointWeightSpace π α) := by
  have : Nontrivial R := (algebraMap R S).domain_nontrivial
  rw [← (adjointWeightSpaceBaseChangeEquiv π πS hπ α).finrank_eq, Module.finrank_baseChange]


section FaithfulSMul

variable [FaithfulSMul R S]

/-- Along an injective scalar map `R → S`, for instance a faithfully flat one, an adjoint weight
space vanishes after base change exactly when the original one does. -/
theorem adjointWeightSpace_baseChange_eq_bot_iff (π : H →ₐc[R] MonoidAlgebra R M)
    (πS : S ⊗[R] H →ₐc[S] MonoidAlgebra S M)
    (hπ : ∀ h, πS (1 ⊗ₜ h) = MonoidAlgebra.mapAlgHom M (Algebra.ofId R S) (π h)) (α : M) :
    adjointWeightSpace πS α = ⊥ ↔ adjointWeightSpace π α = ⊥ := by
  -- The Lie algebra is projective, hence flat, so `x ↦ 1 ⊗ x` is injective along `R → S`.
  rw [adjointWeightSpace_baseChange π πS hπ α,
    Submodule.map_eq_bot_iff (e := cotangentDualBaseChangeEquiv R S H), ← le_bot_iff,
    Submodule.baseChange_le_iff_le_comap, Submodule.restrictScalars_bot, ← LinearMap.ker,
    LinearMap.ker_eq_bot.mpr (Module.Flat.tensorProduct_mk_injective R
      (Module.Dual R (Bialgebra.CotangentSpace R H)) S), le_bot_iff]

/-- **The nontrivial adjoint weights are invariant under base change along an injective scalar
map**, in particular under every faithfully flat base change, every field extension and the map
from `ℤ` to a ring of characteristic zero. For a split maximal torus of a reductive group these
are the roots. -/
theorem nontrivialAdjointWeights_baseChange (π : H →ₐc[R] MonoidAlgebra R M)
    (πS : S ⊗[R] H →ₐc[S] MonoidAlgebra S M)
    (hπ : ∀ h, πS (1 ⊗ₜ h) = MonoidAlgebra.mapAlgHom M (Algebra.ofId R S) (π h)) :
    nontrivialAdjointWeights πS = nontrivialAdjointWeights π := by
  ext α
  simp only [mem_nontrivialAdjointWeights, ne_eq,
    adjointWeightSpace_baseChange_eq_bot_iff π πS hπ α]

end FaithfulSMul

end Derivation

namespace TauCeti.SplitMaximalTorus

universe u

variable {R : Type u} [CommRing R] {H : CommHopfAlgCat.{u} R} [Algebra.FiniteType R H] {r : ℕ}
variable (S : Type u) [CommRing S] [Algebra R S]

variable [Module.Finite R (Bialgebra.CotangentSpace R H)]
  [Module.Projective R (Bialgebra.CotangentSpace R H)]
  [Module.Finite S (Bialgebra.CotangentSpace S (S ⊗[R] H))]
  [Module.Projective S (Bialgebra.CotangentSpace S (S ⊗[R] H))]

/-- **The root spaces of a chosen split maximal torus commute with base change**: each weight space
of the base-changed torus on the Lie algebra of the base-changed group is the image of the base
change of the corresponding weight space. -/
theorem adjointWeightSpace_baseChange (T : SplitMaximalTorus R H r)
    (α : SplitTorus.characterGroup (ULift.{u} (Fin r))) :
    Derivation.adjointWeightSpace (T.baseChange S).coordinateMap.hom α =
      ((Derivation.adjointWeightSpace T.coordinateMap.hom α).baseChange S).map
        (Derivation.cotangentDualBaseChangeEquiv R S H).toLinearMap :=
  Derivation.adjointWeightSpace_baseChange _ _ (baseChange_coordinateMap_hom_one_tmul S T) α

/-- **The roots of a chosen split maximal torus are invariant under base change along an injective
scalar map**, in particular under every faithfully flat base change, every field extension and the
map from `ℤ` to a ring of characteristic zero. -/
theorem nontrivialAdjointWeights_baseChange [FaithfulSMul R S]
    (T : SplitMaximalTorus R H r) :
    Derivation.nontrivialAdjointWeights (T.baseChange S).coordinateMap.hom =
      Derivation.nontrivialAdjointWeights T.coordinateMap.hom :=
  Derivation.nontrivialAdjointWeights_baseChange _ _ (baseChange_coordinateMap_hom_one_tmul S T)

/-- **The dimension of a free root space of a chosen split maximal torus is unchanged by base
change** to a nontrivial ring, in particular by every field extension. -/
theorem finrank_adjointWeightSpace_baseChange [Nontrivial S]
    (T : SplitMaximalTorus R H r) (α : SplitTorus.characterGroup (ULift.{u} (Fin r)))
    [Module.Free R (Derivation.adjointWeightSpace T.coordinateMap.hom α)] :
    Module.finrank S (Derivation.adjointWeightSpace (T.baseChange S).coordinateMap.hom α) =
      Module.finrank R (Derivation.adjointWeightSpace T.coordinateMap.hom α) :=
  Derivation.finrank_adjointWeightSpace_baseChange _ _
    (baseChange_coordinateMap_hom_one_tmul S T) α

end TauCeti.SplitMaximalTorus

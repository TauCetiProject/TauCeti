/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.DiagonalizableGroup.Normalizer.Weight
public import TauCeti.Algebra.AlgebraicGroup.DiagonalizableGroup.Normalizer.Character
public import TauCeti.Algebra.AlgebraicGroup.Tangent.Lie.Adjoint.Cotangent
public import TauCeti.Algebra.AlgebraicGroup.Tangent.Equivariance

/-!
# Weight spaces of the adjoint representation

Let `G = Spec H` be an affine group scheme over `R` whose augmentation cotangent space is finite
projective, so that its Lie algebra is the single `R`-module
`Module.Dual R (Bialgebra.CotangentSpace R H)` carrying the adjoint comodule of
`TauCeti.Algebra.AlgebraicGroup.Tangent.Representation`. Let `π : H →ₐc[R] R[M]` be a morphism of
coordinate bialgebras, that is, a homomorphism `D(M) → G` of affine group schemes out of the
diagonalizable group on a commutative group `M` written multiplicatively.

Restricting the adjoint representation along `π` decomposes the Lie algebra into weight
submodules, indexed by `M`. This file names them: `adjointWeightSpace π α` is the `α`-weight
submodule `𝔤_α`, `nontrivialAdjointWeights π` is the set of nontrivial characters whose weight
submodule is nonzero, and the Lie algebra is spanned by `𝔤_1` together with the `𝔤_α` for
`α ∈ nontrivialAdjointWeights π`. A point of `D(M)` acts on `𝔤_α` by the value of `α` at that
point, and the Lie bracket sends `𝔤_α × 𝔤_β` into `𝔤_{αβ}`.

Nothing here asserts that `π` is a closed immersion, that `D(M)` is a torus, let alone a maximal
one, or that `G` is reductive. When `π` does exhibit a split maximal torus `T` in a reductive `G`,
`nontrivialAdjointWeights π` is the set of roots of the split pair `(G, T)`. The character and
cocharacter lattices of the root datum `(X*(T), Φ, X_*(T), Φ^∨)`, with their pairing, are in
`TauCeti.Algebra.AlgebraicGroup.Cocharacter`; this file supplies the weight decomposition from
which `Φ` is read off.

## Main definitions

* `Derivation.adjointWeightSpace`: the `α`-weight submodule `𝔤_α` of the Lie algebra of
  `G` under a homomorphism from a diagonalizable group.
* `Derivation.nontrivialAdjointWeights`: the nontrivial characters whose adjoint weight
  submodule is nonzero.

## Main results

* `Derivation.isInternal_adjointWeightSpace`: **the Lie algebra of `G` is the internal
  direct sum of its weight submodules.**
* `Derivation.adjointWeightSpace_mapDomainBialgHom_comp`: restricting along `D(N) → D(M)` for
  `q : M →* N`, the `n`-weight space is the sum of the `m`-weight spaces with `q m = n`.
* `Derivation.sup_iSup_adjointWeightSpace_eq_top`: the trivial weight submodule together
  with the submodules indexed by `nontrivialAdjointWeights π` exhaust the Lie algebra.
* `Derivation.finite_nontrivialAdjointWeights`: **the set of nontrivial adjoint weights is
  finite.**
* `Derivation.endOfPoint_tmul_of_mem_adjointWeightSpace`: a point of `D(M)` acts on the
  `α`-weight submodule by the value of `α` at that point.
* `Derivation.mem_adjointWeightSpace_iff_universalPointAction`: weight-space membership can be
  tested using the universal point of `D(M)`.
* `Derivation.lie_mem_adjointWeightSpace_mul`: the adjoint weight decomposition is a Lie
  grading: `[𝔤_α, 𝔤_β] ⊆ 𝔤_{αβ}`.
* `Derivation.image_nontrivialAdjointWeights`: inverse conjugation by a normalizing rational
  point permutes the nontrivial adjoint weights, hence the roots of a split reductive pair.
* `Derivation.image_nontrivialAdjointWeights_normalizerCharacterHom`: the actual character
  action of the scheme normalizer preserves the nontrivial adjoint weights.
* `Derivation.dualCotangentMap_mem_adjointWeightSpace_iff`: the differential of a closed
  immersion `Spec L → Spec H` detects the adjoint weight spaces of a diagonalizable subgroup of
  `Spec L`.
* `BialgHom.dualCotangentMap_mem_adjointWeightSpace_iff_of_injective`: more generally, an
  injective differential detects these weight spaces.
* `BialgHom.map_dualCotangentMap_adjointWeightSpace_of_bijective` and
  `BialgHom.adjointWeightSpaceEquivOfBijective`: a bijective differential identifies
  corresponding weight spaces over a commutative base ring.
* `Derivation.map_dualCotangentMap_adjointWeightSpace` and `Derivation.adjointWeightSpaceEquiv`:
  the differential of an isomorphism carries each weight space onto the corresponding weight
  space for the transported diagonalizable subgroup.
* `Derivation.adjointWeightSpace_comp_bialgEquiv_eq_bot_iff_of_characterEquiv`: a weight space
  vanishes exactly when its transport along a bialgebra equivalence does, for a character group
  in any universe.

## References

* J. S. Milne, *Algebraic Groups* (2017), §21.1 (the roots of a split reductive group).
* W. C. Waterhouse, *Introduction to Affine Group Schemes*, §3.2.
* B. Conrad, *Reductive Group Schemes* (SGA3 exposition), §3.2.
-/

public section

open CategoryTheory WithConv
open scoped DirectSum TensorProduct

namespace Derivation

open TauCeti

attribute [local instance] Classical.decEq
attribute [local instance] adjointComodule

universe u v w

variable {R : Type u} {H : Type v} [CommRing R] [CommRing H] [HopfAlgebra R H]
variable [Module.Finite R (Bialgebra.CotangentSpace R H)]
variable [Module.Projective R (Bialgebra.CotangentSpace R H)]
variable {M : Type w} [CommGroup M]

/-- The `α`-weight submodule `𝔤_α` of the Lie algebra of `G = Spec H` under a homomorphism
`D(M) → G` with coordinate morphism `π`: the part of the Lie algebra on which `D(M)` acts through
the character `α`. -/
noncomputable def adjointWeightSpace (π : H →ₐc[R] MonoidAlgebra R M) (α : M) :
    Submodule R (Module.Dual R (Bialgebra.CotangentSpace R H)) :=
  letI : Comodule R H (Module.Dual R (Bialgebra.CotangentSpace R H)) :=
    adjointComodule (R := R) (H := H)
  DiagonalizableGroup.weightSpace (Module.Dual R (Bialgebra.CotangentSpace R H))
    (π : H →ₗc[R] MonoidAlgebra R M) α

/-- Membership in the `α`-weight submodule, in terms of the adjoint coaction: pushing the adjoint
coaction of `x` through `π` must give `x ⊗ α`. -/
@[simp]
theorem mem_adjointWeightSpace {π : H →ₐc[R] MonoidAlgebra R M} {α : M}
    {x : Module.Dual R (Bialgebra.CotangentSpace R H)} :
    x ∈ adjointWeightSpace π α ↔
      TensorProduct.map LinearMap.id (π : H →ₗc[R] MonoidAlgebra R M).toLinearMap
          (Comodule.coact (R := R) (C := H)
            (M := Module.Dual R (Bialgebra.CotangentSpace R H)) x) =
        x ⊗ₜ[R] MonoidAlgebra.single α (1 : R) :=
  letI : Comodule R H (Module.Dual R (Bialgebra.CotangentSpace R H)) :=
    adjointComodule (R := R) (H := H)
  DiagonalizableGroup.mem_weightSpace

/-- Relabelling the character group by an equivalence preserves each adjoint weight space. -/
theorem adjointWeightSpace_domCongr {N : Type*} [CommGroup N] (e : M ≃* N)
    (π : H →ₐc[R] MonoidAlgebra R M) (α : M) :
    adjointWeightSpace ((MonoidAlgebra.domCongrBialgEquiv R R e).toBialgHom.comp π) (e α) =
      adjointWeightSpace π α := by
  ext x
  rw [mem_adjointWeightSpace, mem_adjointWeightSpace]
  let V := Module.Dual R (Bialgebra.CotangentSpace R H)
  let E := MonoidAlgebra.domCongrBialgEquiv R R e
  let T := TensorProduct.congr (LinearEquiv.refl R V) E.toAlgEquiv.toLinearEquiv
  have hcomp (z : V ⊗[R] H) :
      T (TensorProduct.map LinearMap.id (π : H →ₗc[R] MonoidAlgebra R M).toLinearMap z) =
      TensorProduct.map LinearMap.id
        (E.toBialgHom.comp π : H →ₗc[R] MonoidAlgebra R N).toLinearMap z := by
    -- TensorProduct.congr acts by the tensor map of the underlying linear equivalences.
    change TensorProduct.map LinearMap.id E.toAlgEquiv.toLinearMap
      (TensorProduct.map LinearMap.id (π : H →ₗc[R] MonoidAlgebra R M).toLinearMap z) = _
    rw [TensorProduct.map_map]
    rfl
  have hsingle : T (x ⊗ₜ[R] MonoidAlgebra.single α 1) =
      x ⊗ₜ[R] MonoidAlgebra.single (e α) 1 := by
    rw [TensorProduct.congr_tmul, LinearEquiv.refl_apply]
    congr 1
    simp only [E, MonoidAlgebra.domCongrBialgEquiv]
    exact MonoidAlgebra.domCongr_single (R := R) (A := R) e α 1
  rw [← hcomp, ← hsingle]
  exact T.injective.eq_iff

/-- **Pushing the characters forward along a homomorphism `q : M →* N` collects adjoint weight
spaces.** The `n`-weight space for `D(N) → D(M) → G` is the sum of the `m`-weight spaces for
`D(M) → G` over the characters `m` with `q m = n`. -/
theorem adjointWeightSpace_mapDomainBialgHom_comp {N : Type*} [CommGroup N]
    (π : H →ₐc[R] MonoidAlgebra R M) (q : M →* N) (n : N) :
    adjointWeightSpace ((MonoidAlgebra.mapDomainBialgHom R q).comp π) n =
      ⨆ m ∈ q ⁻¹' {n}, adjointWeightSpace π m := by
  simp only [adjointWeightSpace, BialgHom.comp_toCoalgHom]
  exact DiagonalizableGroup.weightSpace_mapDomainBialgHom_comp _ (π : H →ₗc[R] MonoidAlgebra R M)
    q n

/-- Membership in an adjoint weight space can be tested on the universal point of the
diagonalizable group. The universal point acts on a weight vector of weight `alpha` by the
group-algebra basis element `[alpha]`.

This is the converse to `endOfPoint_tmul_of_mem_adjointWeightSpace` at the universal point. -/
theorem mem_adjointWeightSpace_iff_universalPointAction
    {R H : Type u} [CommRing R] [CommRing H] [HopfAlgebra R H]
    [Module.Finite R (Bialgebra.CotangentSpace R H)]
    [Module.Projective R (Bialgebra.CotangentSpace R H)]
    {M : Type u} [CommGroup M]
    (pi : H →ₐc[R] MonoidAlgebra R M) (alpha : M)
    (x : Module.Dual R (Bialgebra.CotangentSpace R H)) :
    x ∈ adjointWeightSpace pi alpha ↔
      (adjointAction (CommAlgCat.of R (MonoidAlgebra R M))
          (toConv (pi : H →ₐ[R] MonoidAlgebra R M))).val (1 ⊗ₜ[R] x) =
        MonoidAlgebra.single alpha (1 : R) ⊗ₜ[R] x := by
  let V := Module.Dual R (Bialgebra.CotangentSpace R H)
  let U := ULift.{u} H
  let K := MonoidAlgebra R M
  let phi : U →ₐ[R] K :=
    (pi : H →ₐ[R] K).comp (ULift.algEquiv (R := R) : U ≃ₐ[R] H).toAlgHom
  let g : HopfAlgebra.points (H := H) (CommAlgCat.of R U) :=
    toConv (ULift.algEquiv (R := R) : U ≃ₐ[R] H).symm.toAlgHom
  have hmapPoint : HopfAlgebra.mapPoints (H := H) (CommAlgCat.ofHom phi) g =
      toConv (pi : H →ₐ[R] K) := by
    rw [HopfAlgebra.mapPoints_apply]
    apply WithConv.ofConv_injective
    ext h
    rfl
  have hnatural :=
    (adjointPointRepresentation (R := R) (H := H)).action_mapPoints_one_tmul
      (CommAlgCat.ofHom phi) g x
  rw [adjointPointRepresentation_action, hmapPoint] at hnatural
  have hcore :
      TensorProduct.comm R V K
          (TensorProduct.map LinearMap.id (pi : H →ₗc[R] K).toLinearMap
            ((adjointComodule (R := R) (H := H)).coact x)) =
        (adjointAction (CommAlgCat.of R K) (toConv (pi : H →ₐ[R] K))).val
          (1 ⊗ₜ[R] x) := by
    rw [adjointComodule_coact_apply]
    rw [hnatural]
    let z :=
      (((adjointPointRepresentation (R := R) (H := H)).action
        (CommAlgCat.of R U) g).val (1 ⊗ₜ[R] x))
    -- Naturality is expressed through bundled scalar extension, while the coaction side uses
    -- tensor maps. Neither wrapper exposes a theorem for its underlying linear map, so unfold
    -- those wrappers definitionally before proving the resulting tensor identity.
    change
      TensorProduct.comm R V K
          (TensorProduct.map LinearMap.id (pi : H →ₗc[R] K).toLinearMap
            (TensorProduct.comm R H V
              (TensorProduct.map
                (ULift.algEquiv (R := R) : U ≃ₐ[R] H).toLinearMap LinearMap.id z))) =
        GeneralLinear.scalarExtensionMap (V := V) (CommAlgCat.ofHom phi) z
    induction z using TensorProduct.inductionOn with
    | add a b ha hb => simpa only [map_add] using congrArg₂ (fun p q ↦ p + q) ha hb
    | tmul a y =>
        simp only [TensorProduct.map_tmul, LinearMap.id_apply, TensorProduct.comm_tmul]
        rw [GeneralLinear.scalarExtensionMap_tmul]
        rfl
  rw [mem_adjointWeightSpace]
  constructor
  · intro hx
    rw [← hcore, hx, TensorProduct.comm_tmul]
  · intro hx
    apply (TensorProduct.comm R V K).injective
    rw [hcore, hx, TensorProduct.comm_tmul]

/-- **The Lie algebra of `G` is the internal direct sum of its weight submodules under a
homomorphism from a diagonalizable group.** -/
theorem isInternal_adjointWeightSpace (π : H →ₐc[R] MonoidAlgebra R M) :
    DirectSum.IsInternal (adjointWeightSpace π) :=
  letI : Comodule R H (Module.Dual R (Bialgebra.CotangentSpace R H)) :=
    adjointComodule (R := R) (H := H)
  DiagonalizableGroup.isInternal_weightSpace (Module.Dual R (Bialgebra.CotangentSpace R H))
    (π : H →ₗc[R] MonoidAlgebra R M)

/-- The nontrivial characters of `D(M)` whose adjoint weight submodule in the Lie algebra of `G`
is nonzero. When `π` exhibits a split maximal torus `T` in a reductive `G`, these are the roots of
the split pair `(G, T)`. -/
def nontrivialAdjointWeights (π : H →ₐc[R] MonoidAlgebra R M) : Set M :=
  {α | α ≠ 1 ∧ adjointWeightSpace π α ≠ ⊥}

@[simp]
theorem mem_nontrivialAdjointWeights {π : H →ₐc[R] MonoidAlgebra R M} {α : M} :
    α ∈ nontrivialAdjointWeights π ↔ α ≠ 1 ∧ adjointWeightSpace π α ≠ ⊥ :=
  Iff.rfl

/-- Adjoint action by a normalizing rational point carries each adjoint weight space onto the
weight space indexed by pullback along inverse conjugation. -/
theorem map_adjointWeightSpace_basePointsRepresentation
    (π : H →ₐc[R] MonoidAlgebra R M) (g : WithConv (H →ₐ[R] R)) (w : M ≃* M)
    (hg : π.toAlgHom.comp (HopfAlgebra.pointConjugationAlgHom g⁻¹) =
      (MonoidAlgebra.domCongr R R w).toAlgHom.comp π.toAlgHom) (α : M) :
    (adjointWeightSpace π α).map
        (Comodule.basePointsRepresentation (H := H)
          (Module.Dual R (Bialgebra.CotangentSpace R H)) g) =
      adjointWeightSpace π (w α) := by
  unfold adjointWeightSpace
  exact DiagonalizableGroup.map_weightSpace_basePointsRepresentation π g w hg α

/-- Inverse conjugation by a normalizing rational point preserves membership in the set of
nontrivial adjoint weights. For a split reductive pair these are the roots. -/
theorem mem_nontrivialAdjointWeights_apply_iff
    (π : H →ₐc[R] MonoidAlgebra R M) (g : WithConv (H →ₐ[R] R)) (w : M ≃* M)
    (hg : π.toAlgHom.comp (HopfAlgebra.pointConjugationAlgHom g⁻¹) =
      (MonoidAlgebra.domCongr R R w).toAlgHom.comp π.toAlgHom) (α : M) :
    w α ∈ nontrivialAdjointWeights π ↔ α ∈ nontrivialAdjointWeights π := by
  rw [mem_nontrivialAdjointWeights, mem_nontrivialAdjointWeights]
  have hbot : adjointWeightSpace π (w α) ≠ ⊥ ↔ adjointWeightSpace π α ≠ ⊥ := by
    unfold adjointWeightSpace
    exact DiagonalizableGroup.weightSpace_apply_ne_bot_iff π g w hg α
  exact and_congr (not_congr w.map_eq_one_iff) hbot

/-- The character automorphism induced by inverse conjugation by a normalizing rational point
permutes the nontrivial adjoint weights. This supplies the preservation of roots needed for
the normalizer action of a split reductive pair. -/
theorem image_nontrivialAdjointWeights
    (π : H →ₐc[R] MonoidAlgebra R M) (g : WithConv (H →ₐ[R] R)) (w : M ≃* M)
    (hg : π.toAlgHom.comp (HopfAlgebra.pointConjugationAlgHom g⁻¹) =
      (MonoidAlgebra.domCongr R R w).toAlgHom.comp π.toAlgHom) :
    w '' nontrivialAdjointWeights π = nontrivialAdjointWeights π := by
  apply (Set.eq_preimage_iff_image_eq w.bijective).mp
  exact Set.ext fun α ↦ (mem_nontrivialAdjointWeights_apply_iff π g w hg α).symm

/-- The induced character action of the scheme normalizer permutes the nontrivial adjoint
weights. For a split reductive pair, this is its action on the roots. -/
theorem image_nontrivialAdjointWeights_normalizerCharacterHom
    [ConnectedSpace (PrimeSpectrum R)]
    (π : H →ₐc[R] MonoidAlgebra R M) (hπ : Function.Surjective π)
    (g : π.normalizerPoints hπ) :
    π.normalizerCharacterHom hπ g '' nontrivialAdjointWeights π =
      nontrivialAdjointWeights π :=
  image_nontrivialAdjointWeights π g (π.normalizerCharacterHom hπ g)
    (π.normalizerCharacterHom_comp hπ g)

/-- Off the nontrivial adjoint weights and the trivial character the weight submodule vanishes. -/
theorem adjointWeightSpace_eq_bot_of_notMem_nontrivialAdjointWeights
    {π : H →ₐc[R] MonoidAlgebra R M} {α : M} (hα : α ≠ 1)
    (h : α ∉ nontrivialAdjointWeights π) : adjointWeightSpace π α = ⊥ := by
  by_contra hbot
  exact h ⟨hα, hbot⟩

/-- **The set of nontrivial adjoint weights is finite.** The Lie algebra is finitely generated, so
only finitely many weight submodules are nonzero. -/
theorem finite_nontrivialAdjointWeights (π : H →ₐc[R] MonoidAlgebra R M) :
    (nontrivialAdjointWeights π).Finite :=
  letI : Comodule R H (Module.Dual R (Bialgebra.CotangentSpace R H)) :=
    adjointComodule (R := R) (H := H)
  Set.Finite.subset
    (DiagonalizableGroup.finite_setOf_weightSpace_ne_bot
      (Module.Dual R (Bialgebra.CotangentSpace R H)) (π : H →ₗc[R] MonoidAlgebra R M))
    fun _ hα => hα.2

/-- **The Lie algebra is spanned by the trivial weight submodule together with the submodules
indexed by the nontrivial adjoint weights.** -/
theorem sup_iSup_adjointWeightSpace_eq_top (π : H →ₐc[R] MonoidAlgebra R M) :
    (adjointWeightSpace π 1 ⊔
      ⨆ α ∈ nontrivialAdjointWeights π, adjointWeightSpace π α) = ⊤ := by
  refine top_unique ?_
  rw [← (isInternal_adjointWeightSpace π).submodule_iSup_eq_top]
  refine iSup_le fun α => ?_
  by_cases hα : α = 1
  · subst hα
    exact le_sup_left
  · by_cases hbot : adjointWeightSpace π α = ⊥
    · rw [hbot]
      exact bot_le
    · exact le_sup_of_le_right
        (le_iSup₂ (f := fun β (_ : β ∈ nontrivialAdjointWeights π) => adjointWeightSpace π β)
          α ⟨hα, hbot⟩)

/-- **A point of `D(M)` acts on the `α`-weight submodule `𝔤_α` by the value of the character
`α` at that point.** -/
theorem endOfPoint_tmul_of_mem_adjointWeightSpace {A : Type*} [CommSemiring A] [Algebra R A]
    (π : H →ₐc[R] MonoidAlgebra R M) (f : MonoidAlgebra R M →ₐ[R] A) (a : A) {α : M}
    {x : Module.Dual R (Bialgebra.CotangentSpace R H)} (hx : x ∈ adjointWeightSpace π α) :
    Comodule.endOfPoint (Module.Dual R (Bialgebra.CotangentSpace R H))
        (f.comp (π : H →ₐ[R] MonoidAlgebra R M)) (a ⊗ₜ[R] x) =
      (a * f (MonoidAlgebra.single α (1 : R))) ⊗ₜ[R] x :=
  letI : Comodule R H (Module.Dual R (Bialgebra.CotangentSpace R H)) :=
    adjointComodule (R := R) (H := H)
  DiagonalizableGroup.endOfPoint_tmul_of_mem_weightSpace
    (Module.Dual R (Bialgebra.CotangentSpace R H)) π f a hx

private theorem map_universalAdjointAction_eq_single_of_mem_adjointWeightSpace
    {π : H →ₐc[R] MonoidAlgebra R M} {α : M}
    {x : Module.Dual R (Bialgebra.CotangentSpace R H)}
    (hx : x ∈ adjointWeightSpace π α) :
    TensorProduct.map
        ((π : H →ₗc[R] MonoidAlgebra R M).toLinearMap ∘ₗ
          (ULift.algEquiv (R := R) : ULift.{max u v} H ≃ₐ[R] H).toLinearMap)
        LinearMap.id
        ((adjointAction (CommAlgCat.of R (ULift.{max u v} H))
          (WithConv.toConv (ULift.algEquiv (R := R)).symm.toAlgHom)).val
            (1 ⊗ₜ[R] x)) =
      MonoidAlgebra.single α 1 ⊗ₜ[R] x := by
  let : Comodule R H (Module.Dual R (Bialgebra.CotangentSpace R H)) :=
    adjointComodule (R := R) (H := H)
  have h := endOfPoint_tmul_of_mem_adjointWeightSpace π
    (AlgHom.id R (MonoidAlgebra R M)) 1 hx
  rw [Comodule.endOfPoint_tmul] at h
  simp only [one_smul] at h
  rw [adjointComodule_coact_apply, adjointPointRepresentation_action] at h
  rw [LinearMap.lTensor_def, ← TensorProduct.map_comm] at h
  simp only [AlgHom.id_comp, AlgHom.id_apply, one_mul, TensorProduct.comm_comm,
    TensorProduct.map_map, LinearMap.comp_id] at h
  have hπ : (π : H →ₐ[R] MonoidAlgebra R M).toLinearMap =
      (π : H →ₗc[R] MonoidAlgebra R M).toLinearMap := by
    rw [CoalgHom.toLinearMap_eq_ofClass]
    exact BialgHom.toAlgHom_toLinearMap π
  rw [hπ] at h
  exact h

/-- **The bracket of an `α`-weight vector and a `β`-weight vector has weight `α * β`.**

For a split pair this is the root-space grading relation
`[𝔤_α, 𝔤_β] ⊆ 𝔤_{αβ}` (with characters written multiplicatively). -/
theorem lie_mem_adjointWeightSpace_mul {π : H →ₐc[R] MonoidAlgebra R M} {α β : M}
    {x y : Module.Dual R (Bialgebra.CotangentSpace R H)}
    (hx : x ∈ adjointWeightSpace π α) (hy : y ∈ adjointWeightSpace π β) :
    ⁅x, y⁆ ∈ adjointWeightSpace π (α * β) := by
  rw [mem_adjointWeightSpace]
  let U := ULift.{max u v} H
  let A := CommAlgCat.of R U
  let g : HopfAlgebra.points (H := H) A :=
    WithConv.toConv (ULift.algEquiv (R := R)).symm.toAlgHom
  let q : U →ₐ[R] MonoidAlgebra R M :=
    (π : H →ₐ[R] MonoidAlgebra R M).comp
      (ULift.algEquiv (R := R) : U ≃ₐ[R] H).toAlgHom
  have hπ : (π : H →ₐ[R] MonoidAlgebra R M).toLinearMap =
      (π : H →ₗc[R] MonoidAlgebra R M).toLinearMap := by
    rw [CoalgHom.toLinearMap_eq_ofClass]
    exact BialgHom.toAlgHom_toLinearMap π
  have hq : q.toLinearMap =
      ((π : H →ₗc[R] MonoidAlgebra R M).toLinearMap ∘ₗ
        (ULift.algEquiv (R := R) : U ≃ₐ[R] H).toLinearMap) := by
    -- Unfold `q`: `AlgHom.comp` has no theorem exposing its underlying linear map.
    change
      ((π : H →ₐ[R] MonoidAlgebra R M).toLinearMap ∘ₗ
          (ULift.algEquiv (R := R) : U ≃ₐ[R] H).toLinearMap) = _
    rw [hπ]
  have hx' :
      TensorProduct.map q.toLinearMap LinearMap.id
          ((adjointAction A g).val (1 ⊗ₜ[R] x)) =
        MonoidAlgebra.single α 1 ⊗ₜ[R] x := by
    rw [hq]
    exact map_universalAdjointAction_eq_single_of_mem_adjointWeightSpace hx
  have hy' :
      TensorProduct.map q.toLinearMap LinearMap.id
          ((adjointAction A g).val (1 ⊗ₜ[R] y)) =
        MonoidAlgebra.single β 1 ⊗ₜ[R] y := by
    rw [hq]
    exact map_universalAdjointAction_eq_single_of_mem_adjointWeightSpace hy
  have hbracket := adjointAction_bracket A g (1 ⊗ₜ[R] x) (1 ⊗ₜ[R] y)
  have hmapped := congrArg
    (LieAlgebra.ExtendScalars.map q
      (LieHom.id : Module.Dual R (Bialgebra.CotangentSpace R H) →ₗ⁅R⁆
        Module.Dual R (Bialgebra.CotangentSpace R H))) hbracket
  rw [LieHom.map_lie] at hmapped
  simp only [LieAlgebra.ExtendScalars.bracket_tmul, one_mul] at hmapped
  -- `ExtendScalars.map` exposes this tensor map only through its `LieHom` coercion.
  change
    TensorProduct.map q.toLinearMap LinearMap.id
        ((adjointAction A g).val (1 ⊗ₜ[R] ⁅x, y⁆)) =
      ⁅TensorProduct.map q.toLinearMap LinearMap.id
          ((adjointAction A g).val (1 ⊗ₜ[R] x)),
        TensorProduct.map q.toLinearMap LinearMap.id
          ((adjointAction A g).val (1 ⊗ₜ[R] y))⁆ at hmapped
  rw [hx', hy'] at hmapped
  simp only [LieAlgebra.ExtendScalars.bracket_tmul,
    MonoidAlgebra.single_mul_single, one_mul] at hmapped
  rw [adjointComodule_coact_apply, adjointPointRepresentation_action]
  apply (TensorProduct.comm R (Module.Dual R (Bialgebra.CotangentSpace R H))
    (MonoidAlgebra R M)).injective
  rw [← TensorProduct.map_comm]
  simp only [TensorProduct.comm_comm, TensorProduct.map_map,
    LinearMap.comp_id, TensorProduct.comm_tmul]
  rw [hq] at hmapped
  exact hmapped

section Transport

/-! ### Transport along homomorphisms with injective or bijective differential -/

variable {R H L M : Type u} [CommRing R] [CommRing H] [CommRing L] [HopfAlgebra R H]
  [HopfAlgebra R L] [CommGroup M]

-- Identify the linear map underlying `ofBijective` through its public application lemma.
private lemma ofBijective_dualCotangentMap_toLinearMap (φ : H →ₐc[R] L)
    (hφ : Function.Bijective (dualCotangentMap φ)) :
    (LinearEquiv.ofBijective (dualCotangentMap φ) hφ).toLinearMap = dualCotangentMap φ :=
  LinearMap.ext fun _ ↦ LinearEquiv.ofBijective_apply ..

variable [Module.Finite R (Bialgebra.CotangentSpace R H)]
  [Module.Projective R (Bialgebra.CotangentSpace R H)]
  [Module.Finite R (Bialgebra.CotangentSpace R L)]
  [Module.Projective R (Bialgebra.CotangentSpace R L)]

/-- The differential of a group homomorphism carries an adjoint weight vector to a vector
of the same weight, after restricting along the same diagonalizable group in the source. -/
theorem _root_.BialgHom.dualCotangentMap_mem_adjointWeightSpace (φ : H →ₐc[R] L)
    (π : L →ₐc[R] MonoidAlgebra R M) (α : M)
    {y : Module.Dual R (Bialgebra.CotangentSpace R L)}
    (hy : y ∈ adjointWeightSpace π α) :
    dualCotangentMap φ y ∈ adjointWeightSpace (π.comp φ) α := by
  let A := CommAlgCat.of R (MonoidAlgebra R M)
  have h := congrArg ((dualCotangentMap φ).lTensor A)
    ((mem_adjointWeightSpace_iff_universalPointAction π α y).mp hy)
  rw [BialgHom.lTensor_dualCotangentMap_adjointAction, LinearMap.lTensor_tmul,
    LinearMap.lTensor_tmul] at h
  apply (mem_adjointWeightSpace_iff_universalPointAction (π.comp φ) α _).mpr
  simpa only [BialgHom.mapDomain_apply, BialgHom.comp_toAlgHom, A] using h

/-- A homomorphism with injective differential detects adjoint weights for any homomorphism
from a diagonalizable group into its source. No injectivity of the coordinate map is needed. -/
theorem _root_.BialgHom.dualCotangentMap_mem_adjointWeightSpace_iff_of_injective (φ : H →ₐc[R] L)
    (hφ : Function.Injective (dualCotangentMap φ))
    (π : L →ₐc[R] MonoidAlgebra R M) (α : M)
    (y : Module.Dual R (Bialgebra.CotangentSpace R L)) :
    dualCotangentMap φ y ∈ adjointWeightSpace (π.comp φ) α ↔ y ∈ adjointWeightSpace π α := by
  refine ⟨?_, φ.dualCotangentMap_mem_adjointWeightSpace π α⟩
  intro hy
  let A := CommAlgCat.of R (MonoidAlgebra R M)
  have hinj := Module.Flat.lTensor_preserves_injective_linearMap (M := A)
    (dualCotangentMap φ) hφ
  apply (mem_adjointWeightSpace_iff_universalPointAction π α y).mpr
  apply hinj
  rw [BialgHom.lTensor_dualCotangentMap_adjointAction]
  simpa [A] using
    (mem_adjointWeightSpace_iff_universalPointAction (π.comp φ) α _).mp hy

/-- **The differential of a closed immersion detects adjoint weight spaces.** Let
`φ : H →ₐc[R] L` be surjective, so that it represents a closed immersion `Spec L → Spec H`, and let
`π` represent a homomorphism `D(M) → Spec L`. A tangent vector of `Spec L` has weight `α` exactly
when its image under the differential of `φ` has weight `α` for the composite `D(M) → Spec H`. -/
theorem dualCotangentMap_mem_adjointWeightSpace_iff (φ : H →ₐc[R] L)
    (hφ : Function.Surjective φ) (π : L →ₐc[R] MonoidAlgebra R M) (α : M)
    (y : Module.Dual R (Bialgebra.CotangentSpace R L)) :
    dualCotangentMap φ y ∈ adjointWeightSpace (π.comp φ) α ↔ y ∈ adjointWeightSpace π α :=
  φ.dualCotangentMap_mem_adjointWeightSpace_iff_of_injective
    (φ.dualCotangentMap_injective_of_surjective hφ) π α y

/-- A bijective differential carries each adjoint weight space onto the weight space of the
same character for the composite diagonalizable-group homomorphism. -/
theorem _root_.BialgHom.map_dualCotangentMap_adjointWeightSpace_of_bijective (φ : H →ₐc[R] L)
    (hφ : Function.Bijective (dualCotangentMap φ))
    (π : L →ₐc[R] MonoidAlgebra R M) (α : M) :
    (adjointWeightSpace π α).map (dualCotangentMap φ) = adjointWeightSpace (π.comp φ) α := by
  ext x
  obtain ⟨y, rfl⟩ := hφ.surjective x
  rw [← ofBijective_dualCotangentMap_toLinearMap φ hφ,
    Submodule.mem_map_equiv, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
  exact (φ.dualCotangentMap_mem_adjointWeightSpace_iff_of_injective hφ.injective π α y).symm

/-- A bijective differential preserves nontrivial adjoint weights, indexed by the characters
of the same diagonalizable group in its source. -/
theorem _root_.BialgHom.nontrivialAdjointWeights_comp_of_bijective (φ : H →ₐc[R] L)
    (hφ : Function.Bijective (dualCotangentMap φ)) (π : L →ₐc[R] MonoidAlgebra R M) :
    nontrivialAdjointWeights (π.comp φ) = nontrivialAdjointWeights π := by
  ext α
  rw [mem_nontrivialAdjointWeights, mem_nontrivialAdjointWeights,
    ← φ.map_dualCotangentMap_adjointWeightSpace_of_bijective hφ,
    ← ofBijective_dualCotangentMap_toLinearMap φ hφ]
  exact and_congr_right' (not_congr Submodule.map_eq_bot_iff)

/-- A bijective differential restricts to a linear equivalence of corresponding adjoint
weight spaces. -/
noncomputable def _root_.BialgHom.adjointWeightSpaceEquivOfBijective (φ : H →ₐc[R] L)
    (hφ : Function.Bijective (dualCotangentMap φ)) (π : L →ₐc[R] MonoidAlgebra R M) (α : M) :
    adjointWeightSpace π α ≃ₗ[R] adjointWeightSpace (π.comp φ) α :=
  ((LinearEquiv.ofBijective (dualCotangentMap φ) hφ).submoduleMap
    (adjointWeightSpace π α)).trans
      (LinearEquiv.ofEq _ _ (by
        rw [ofBijective_dualCotangentMap_toLinearMap φ hφ]
        exact φ.map_dualCotangentMap_adjointWeightSpace_of_bijective hφ π α))

/-- The restricted equivalence acts by the differential on weight vectors. -/
@[simp]
theorem _root_.BialgHom.coe_adjointWeightSpaceEquivOfBijective_apply (φ : H →ₐc[R] L)
    (hφ : Function.Bijective (dualCotangentMap φ)) (π : L →ₐc[R] MonoidAlgebra R M)
    (α : M) (y : adjointWeightSpace π α) :
    (φ.adjointWeightSpaceEquivOfBijective hφ π α y :
        Module.Dual R (Bialgebra.CotangentSpace R H)) = dualCotangentMap φ y := by
  rw [BialgHom.adjointWeightSpaceEquivOfBijective, LinearEquiv.trans_apply,
    LinearEquiv.coe_ofEq_apply, LinearEquiv.submoduleMap_apply, LinearEquiv.ofBijective_apply]

/-- The differential of a bialgebra equivalence carries each adjoint weight space onto the
weight space of the same character for the transported diagonalizable subgroup. -/
theorem map_dualCotangentMap_adjointWeightSpace (e : H ≃ₐc[R] L)
    (π : L →ₐc[R] MonoidAlgebra R M) (α : M) :
    (adjointWeightSpace π α).map (dualCotangentMap (e : H →ₐc[R] L)) =
      adjointWeightSpace (π.comp (e : H →ₐc[R] L)) α :=
  BialgHom.map_dualCotangentMap_adjointWeightSpace_of_bijective _
    e.dualCotangentMap_bijective π α

/-- Transport along a bialgebra equivalence preserves the nontrivial adjoint weights. -/
@[simp]
theorem nontrivialAdjointWeights_comp_bialgEquiv (e : H ≃ₐc[R] L)
    (π : L →ₐc[R] MonoidAlgebra R M) :
    nontrivialAdjointWeights (π.comp (e : H →ₐc[R] L)) = nontrivialAdjointWeights π :=
  BialgHom.nontrivialAdjointWeights_comp_of_bijective _
    e.dualCotangentMap_bijective π

/-- The differential of a bialgebra equivalence, restricted to an adjoint weight space. -/
noncomputable def adjointWeightSpaceEquiv (e : H ≃ₐc[R] L) (π : L →ₐc[R] MonoidAlgebra R M)
    (α : M) :
    adjointWeightSpace π α ≃ₗ[R] adjointWeightSpace (π.comp (e : H →ₐc[R] L)) α :=
  BialgHom.adjointWeightSpaceEquivOfBijective _
    e.dualCotangentMap_bijective π α

/-- The weight-space equivalence is the differential of the bialgebra equivalence. -/
@[simp]
theorem coe_adjointWeightSpaceEquiv_apply (e : H ≃ₐc[R] L) (π : L →ₐc[R] MonoidAlgebra R M)
    (α : M) (y : adjointWeightSpace π α) :
    (adjointWeightSpaceEquiv e π α y : Module.Dual R (Bialgebra.CotangentSpace R H)) =
      dualCotangentMap (e : H →ₐc[R] L) y := by
  exact BialgHom.coe_adjointWeightSpaceEquivOfBijective_apply _ _ π α y

end Transport

/-- A character equivalence into the coefficient-ring universe lets the differential of a
closed immersion detect adjoint weights without restricting the original character universe. -/
theorem dualCotangentMap_mem_adjointWeightSpace_iff_of_characterEquiv
    {R H L N : Type u} {M : Type v} [CommRing R] [CommRing H] [CommRing L]
    [HopfAlgebra R H] [HopfAlgebra R L] [CommGroup M] [CommGroup N]
    [Module.Finite R (Bialgebra.CotangentSpace R H)]
    [Module.Projective R (Bialgebra.CotangentSpace R H)]
    [Module.Finite R (Bialgebra.CotangentSpace R L)]
    [Module.Projective R (Bialgebra.CotangentSpace R L)]
    (e : M ≃* N) (φ : H →ₐc[R] L) (hφ : Function.Surjective φ)
    (π : L →ₐc[R] MonoidAlgebra R M) (α : M)
    (x : Module.Dual R (Bialgebra.CotangentSpace R L)) :
    dualCotangentMap φ x ∈ adjointWeightSpace (π.comp φ) α ↔
      x ∈ adjointWeightSpace π α := by
  rw [← adjointWeightSpace_domCongr e π α,
    ← adjointWeightSpace_domCongr e (π.comp φ) α, ← BialgHom.comp_assoc]
  exact dualCotangentMap_mem_adjointWeightSpace_iff φ hφ _ _ x

/-- An adjoint weight space vanishes exactly when the weight space of the same character for the
diagonalizable subgroup transported along a bialgebra equivalence vanishes. As in
`dualCotangentMap_mem_adjointWeightSpace_iff_of_characterEquiv`, a character equivalence into the
coefficient-ring universe lets the character group lie in any universe. -/
theorem adjointWeightSpace_comp_bialgEquiv_eq_bot_iff_of_characterEquiv
    {R H L N : Type u} {M : Type v} [CommRing R] [CommRing H] [CommRing L]
    [HopfAlgebra R H] [HopfAlgebra R L] [CommGroup M] [CommGroup N]
    [Module.Finite R (Bialgebra.CotangentSpace R H)]
    [Module.Projective R (Bialgebra.CotangentSpace R H)]
    [Module.Finite R (Bialgebra.CotangentSpace R L)]
    [Module.Projective R (Bialgebra.CotangentSpace R L)]
    (eM : M ≃* N) (e : H ≃ₐc[R] L) (π : L →ₐc[R] MonoidAlgebra R M) (α : M) :
    adjointWeightSpace (π.comp (e : H →ₐc[R] L)) α = ⊥ ↔ adjointWeightSpace π α = ⊥ := by
  have hmem (x : Module.Dual R (Bialgebra.CotangentSpace R L)) :
      dualCotangentEquiv e x ∈ adjointWeightSpace (π.comp (e : H →ₐc[R] L)) α ↔
        x ∈ adjointWeightSpace π α := by
    rw [dualCotangentEquiv_apply]
    exact dualCotangentMap_mem_adjointWeightSpace_iff_of_characterEquiv eM
      (e : H →ₐc[R] L) e.surjective π α x
  simp only [Submodule.eq_bot_iff]
  constructor
  · intro h x hx
    exact (dualCotangentEquiv e).map_eq_zero_iff.mp (h _ ((hmem x).mpr hx))
  · intro h y hy
    obtain ⟨x, rfl⟩ := (dualCotangentEquiv e).surjective y
    rw [h x ((hmem x).mp hy), map_zero]

end Derivation

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Algebra.Equiv
public import TauCeti.NumberTheory.NumberField.Global.Approximation.Weak
public import TauCeti.NumberTheory.NumberField.LocalGlobal.Completion
public import TauCeti.RingTheory.DedekindDomain.AdicValuation.LocalDegree
public import TauCeti.RingTheory.DedekindDomain.AdicValuation.Semilocal
public import TauCeti.RingTheory.DedekindDomain.PrimesAbove
public import TauCeti.RingTheory.Ideal.PrimesOver

/-!
# Topological and number-field aspects of the semi-local decomposition

Let `L/K` be an extension of number fields and `v` a finite place of `K`. Every finite place `w`
of `L` above `v` gives a completion `L_w`, which is a `K_v`-algebra through the canonical
completion map `completionAlgHom v w`. The algebraic semi-local decomposition
`K_v ⊗[K] L ≃ₐ[K_v] ∏_{w ∣ v} L_w`
(`IsDedekindDomain.HeightOneSpectrum.adicCompletionSemilocalEquiv`) and the degree identity
`∑_{w ∣ v} [L_w : K_v] = [L : K]`
(`IsDedekindDomain.HeightOneSpectrum.sum_finrank_adicCompletion_of_finite`) are proved for general
Dedekind domains in `TauCeti.RingTheory.DedekindDomain.AdicValuation.Semilocal`.

This file supplies the number-field weak-approximation density result above `v`, the extension of
embeddings into `K_v`-domains, and the topological enhancement of the semi-local isomorphism when
`K_v ⊗[K] L` carries its `K_v`-module topology.

## Main definitions

* `TauCeti.semilocalContinuousEquiv`: the semi-local decomposition as a continuous algebra
  equivalence when the tensor product carries its module topology over `K_v`.

## Main results

* `TauCeti.denseRange_algebraMap_pi_liesOver`: `L` is dense in `∏_{w ∣ v} L_w`.
* `TauCeti.exists_algHom_adicCompletion_eq`: a `K`-algebra map from `L` to a `K_v`-algebra that
  is a domain extends to the completion `L_w` at some place `w` above `v`.

## Topology

Both sides of the semi-local decomposition are finite-dimensional `K_v`-vector spaces. Each
carries its canonical `K_v`-module topology, which on `∏_{w ∣ v} L_w` is the product topology,
and `K_v`-linear maps between such spaces are continuous. So when `K_v ⊗[K] L` carries its module
topology, `v.adicCompletionSemilocalEquiv K (𝒪 L) L` is a homeomorphism. This placewise
identification of topological rings is the finite-place input for identifying the finite adeles of
`L` with the scalar extension of the finite adeles of `K` to `L`.

## Provenance

The continuous equivalence and its companion formulas follow the archimedean analogue
`TauCeti.GlobalNumberFields.infiniteSemilocalContinuousEquiv` in
`TauCeti.NumberTheory.NumberField.Global.Places.Semilocal`.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter II, Proposition (8.3).
-/

public section
noncomputable section

open IsDedekindDomain NumberField Module
open scoped TensorProduct NumberField AdicCompletionExtension Valued

namespace TauCeti

open IsDedekindDomain.HeightOneSpectrum

local notation "𝒪" => _root_.NumberField.RingOfIntegers

variable {K : Type*} [Field K] [NumberField K] (L : Type*) [Field L] [NumberField L] [Algebra K L]
  (v : HeightOneSpectrum (𝒪 K))

omit [NumberField K] in
/-- **Weak approximation above `v`.** The diagonal image of `L` is dense in the product of the
completions of `L` at the places above `v`. -/
theorem denseRange_algebraMap_pi_liesOver :
    DenseRange fun (x : L) (w : {w : HeightOneSpectrum (𝒪 L) // w.asIdeal.LiesOver v.asIdeal}) ↦
      algebraMap L (w.val.adicCompletion L) x := by
  let S := ((Set.finite_coe_iff
    (s := {w : HeightOneSpectrum (𝒪 L) | w.asIdeal.LiesOver v.asIdeal})).mp
      (finite_liesOver (𝒪 L) v)).toFinset
  have hS {w : HeightOneSpectrum (𝒪 L)} : w ∈ S ↔ w.asIdeal.LiesOver v.asIdeal :=
    Set.Finite.mem_toFinset _
  let e : {w : HeightOneSpectrum (𝒪 L) // w ∈ S} ≃
      {w : HeightOneSpectrum (𝒪 L) // w.asIdeal.LiesOver v.asIdeal} :=
    Equiv.subtypeEquivRight fun w ↦ hS (w := w)
  -- Weak approximation is stated for the places of a `Finset`, together with a (here empty)
  -- family of infinite places; reindex its product along `S ↔ {w ∣ v}`.
  let Φ : (((w : {w // w ∈ S}) → w.val.adicCompletion L) ×
      ((u : {u : InfinitePlace L // u ∈ (∅ : Finset (InfinitePlace L))}) → u.val.Completion)) ≃ₜ
      ((w : {w : HeightOneSpectrum (𝒪 L) // w.asIdeal.LiesOver v.asIdeal}) →
        w.val.adicCompletion L) :=
    (Homeomorph.prodUnique _ _).trans
      (Homeomorph.piCongrLeft
        (Y := fun w : {w : HeightOneSpectrum (𝒪 L) // w.asIdeal.LiesOver v.asIdeal} ↦
          w.val.adicCompletion L) e)
  exact Φ.surjective.denseRange.comp
    (TauCeti.GlobalNumberFields.weakApproximation_denseRange S ∅) Φ.continuous

attribute [local instance] Fintype.ofFinite in
/-- **An embedding of `L` into a `K_v`-domain extends to a completion of `L` above `v`.** For a
domain `M` that is a `K_v`-algebra, every `K`-algebra map `φ : L → M` is the restriction to `L` of
a `K_v`-algebra map `L_w → M` from the completion of `L` at some place `w` above `v`. Indeed `φ`
induces a `K_v`-algebra map `K_v ⊗[K] L ≃ ∏_{w ∣ v} L_w → M`, and a ring homomorphism from a
finite product of rings to a domain factors through one of the factors. -/
theorem exists_algHom_adicCompletion_eq {M : Type*} [CommRing M] [IsDomain M] [Algebra K M]
    [Algebra (v.adicCompletion K) M] [IsScalarTower K (v.adicCompletion K) M] (φ : L →ₐ[K] M) :
    ∃ (w : HeightOneSpectrum (𝒪 L)) (_ : w.asIdeal.LiesOver v.asIdeal)
      (φ' : w.adicCompletion L →ₐ[v.adicCompletion K] M),
      ∀ x : L, φ x = φ' (algebraMap L (w.adicCompletion L) x) := by
  classical
  -- The `K_v`-algebra map `∏_{w ∣ v} L_w ≃ K_v ⊗[K] L → M` induced by `φ`.
  let f := (Algebra.TensorProduct.lift (Algebra.ofId (v.adicCompletion K) M) φ
    fun _ _ ↦ .all _ _).comp (v.adicCompletionSemilocalEquiv K (𝒪 L) L).symm.toAlgHom
  -- It kills one of the idempotents `e i = 1 - [i]`, whose product vanishes.
  let e (i : {w : HeightOneSpectrum (𝒪 L) // w.asIdeal.LiesOver v.asIdeal}) :
      (w : {w : HeightOneSpectrum (𝒪 L) // w.asIdeal.LiesOver v.asIdeal}) →
        w.val.adicCompletion L := Function.update 1 i 0
  have he (i) : e i + Pi.single i 1 = 1 := funext fun j ↦ by
    by_cases h : j = i
    · subst h
      simp [e]
    · simp [e, h]
  obtain ⟨i, hi⟩ : ∃ i, f (e i) = 0 := by
    have H : ∏ i, e i = 0 := funext fun j ↦ by
      rw [Finset.prod_apply, Pi.zero_apply]
      exact Finset.prod_eq_zero (Finset.mem_univ j) (by simp [e])
    have := congrArg f H
    rw [map_prod, map_zero] at this
    simpa using Finset.prod_eq_zero_iff.1 this
  have hi1 : f (Pi.single i 1) = 1 := by
    have := congrArg f (he i)
    rwa [map_add, hi, zero_add, map_one] at this
  -- So `f` factors through the factor `L_i`.
  have hf (x) : f x = f (Pi.single i (x i)) := by
    have hx : x * Pi.single i 1 = Pi.single i (x i) := funext fun j ↦ by
      by_cases h : j = i
      · subst h
        simp
      · simp [h]
    rw [← hx, map_mul, hi1, mul_one]
  let φ' : i.val.adicCompletion L →ₐ[v.adicCompletion K] M :=
    AlgHom.ofLinearMap (f.toLinearMap.comp (LinearMap.single (v.adicCompletion K)
      (fun w : {w : HeightOneSpectrum (𝒪 L) // w.asIdeal.LiesOver v.asIdeal} ↦
        w.val.adicCompletion L) i)) hi1
      (fun x y ↦ by simp [Pi.single_mul])
  refine ⟨i.val, i.property, φ', fun x ↦ ?_⟩
  have : φ x = f (fun w ↦ algebraMap L (w.val.adicCompletion L) x) := by
    simp [f, v.adicCompletionSemilocalEquiv_symm_algebraMap (K := K) (B := 𝒪 L) (L := L) x]
  rw [this, hf]
  rfl

variable [TopologicalSpace (v.adicCompletion K ⊗[K] L)]
  [IsModuleTopology (v.adicCompletion K) (v.adicCompletion K ⊗[K] L)]

/-- The semi-local decomposition is topological when the tensor product carries the module
topology over `K_v`. Both the comparison and its inverse are continuous. -/
def semilocalContinuousEquiv :
    v.adicCompletion K ⊗[K] L ≃A[v.adicCompletion K]
      ((w : {w : HeightOneSpectrum (𝒪 L) // w.asIdeal.LiesOver v.asIdeal}) →
        w.val.adicCompletion L) where
  toAlgEquiv := v.adicCompletionSemilocalEquiv K (𝒪 L) L
  continuous_toFun := IsModuleTopology.continuous_of_linearMap
    (v.adicCompletionSemilocalEquiv K (𝒪 L) L).toLinearMap
  continuous_invFun := by
    let := IsModuleTopology.toContinuousAdd (v.adicCompletion K)
      (v.adicCompletion K ⊗[K] L)
    let := isModuleTopologyOfFiniteDimensional (𝕜 := v.adicCompletion K)
      (E := (w : {w : HeightOneSpectrum (𝒪 L) // w.asIdeal.LiesOver v.asIdeal}) →
        w.val.adicCompletion L)
    exact IsModuleTopology.continuous_of_linearMap
      (v.adicCompletionSemilocalEquiv K (𝒪 L) L).symm.toLinearMap

/-- Forgetting continuity recovers the algebraic semi-local decomposition. -/
@[simp]
theorem semilocalContinuousEquiv_toAlgEquiv :
    (semilocalContinuousEquiv L v).toAlgEquiv = v.adicCompletionSemilocalEquiv K (𝒪 L) L :=
  (rfl)

variable {L v}

/-- The continuous semi-local comparison has the prescribed formula on pure tensors. -/
@[simp]
theorem semilocalContinuousEquiv_tmul (a : v.adicCompletion K) (x : L)
    (w : {w : HeightOneSpectrum (𝒪 L) // w.asIdeal.LiesOver v.asIdeal}) :
    semilocalContinuousEquiv L v (a ⊗ₜ x) w =
      algebraMap (v.adicCompletion K) (w.val.adicCompletion L) a *
        algebraMap L (w.val.adicCompletion L) x := by
  rw [← ContinuousAlgEquiv.coe_toAlgEquiv, semilocalContinuousEquiv_toAlgEquiv]
  exact v.adicCompletionSemilocalEquiv_tmul a x w

/-- The inverse continuous comparison sends a diagonal field element to `1 ⊗ x`. -/
@[simp]
theorem semilocalContinuousEquiv_symm_algebraMap (x : L) :
    (semilocalContinuousEquiv L v).symm
      (fun w : {w : HeightOneSpectrum (𝒪 L) // w.asIdeal.LiesOver v.asIdeal} ↦
        algebraMap L (w.val.adicCompletion L) x) = 1 ⊗ₜ[K] x := by
  rw [← ContinuousAlgEquiv.coe_toAlgEquiv, ContinuousAlgEquiv.symm_toAlgEquiv,
    semilocalContinuousEquiv_toAlgEquiv]
  exact v.adicCompletionSemilocalEquiv_symm_algebraMap x

end TauCeti

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.MultiplicativeGroup.Topology
public import TauCeti.NumberTheory.NumberField.Global.AdelicPoints.Basic
import TauCeti.NumberTheory.NumberField.FinitePlace.Basic
import TauCeti.NumberTheory.NumberField.Global.Ideles.Basic

/-!
# Examples of adelic points of affine groups

* For the multiplicative group `H = K[T;T⁻¹]` over a number field `K`, evaluation at `T` is an
  injective map from `G(𝔸_K)` to `𝔸_K`, but it is not an embedding: the point topology on
  `G(𝔸_K)` is the idele topology, and inversion is not continuous for the subspace topology of
  `𝔸_K` on the ideles.
* For the trivial coordinate Hopf algebra `H = K`, the adelic points form a subsingleton.
-/

public section

open NumberField IsDedekindDomain TauCeti
open scoped LaurentPolynomial

variable (K : Type*) [Field K] [NumberField K]

-- Evaluation at `T` is injective on the adelic points of `𝔾ₘ`; through `pointsMulEquiv` they are
-- the ideles as a group.
example : Function.Injective
    fun x : AdelicPoints (𝓞 K) K K[T;T⁻¹] ↦ x.ofConv (LaurentPolynomial.T 1) := by
  intro x y hxy
  apply MultiplicativeGroup.pointsMulEquiv.injective
  exact Units.ext (by simpa using hxy)

-- It is not a topological embedding: `G(𝔸_K)` carries the idele topology, which is strictly
-- finer than the subspace topology from `𝔸_K`.
example : ¬Topology.IsEmbedding
    fun x : AdelicPoints (𝓞 K) K K[T;T⁻¹] ↦ x.ofConv (LaurentPolynomial.T 1) := by
  intro h
  apply IdeleGroup.not_isEmbedding_val (𝓞 K) K
  let e := MultiplicativeGroup.pointsContinuousMulEquiv K (AdeleRing (𝓞 K) K)
  have he : (Units.val : (AdeleRing (𝓞 K) K)ˣ → AdeleRing (𝓞 K) K) =
      (fun x : AdelicPoints (𝓞 K) K K[T;T⁻¹] ↦ x.ofConv (LaurentPolynomial.T 1)) ∘ e.symm := by
    funext u
    simp [e, MultiplicativeGroup.pointsMulEquiv_symm_apply]
  rw [he]
  exact h.comp e.symm.toHomeomorph.isEmbedding

-- The adelic points of the trivial group `Spec K` form a subsingleton.
example (R : Type*) [CommRing R] [IsDedekindDomain R] [Algebra R K] [IsFractionRing R K] :
    Subsingleton (AdelicPoints R K K) :=
  (WithConv.equiv _).subsingleton

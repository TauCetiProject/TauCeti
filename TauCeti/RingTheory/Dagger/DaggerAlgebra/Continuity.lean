/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Algebra.Equiv
public import TauCeti.RingTheory.Dagger.Continuity
public import TauCeti.RingTheory.Dagger.DaggerAlgebra.ResidueNorm

import TauCeti.RingTheory.Dagger.NoetherNormalization
import TauCeti.RingTheory.Dagger.Noetherian
import TauCeti.RingTheory.Dagger.QuotientCompletion
import TauCeti.RingTheory.Huber.Normed
import TauCeti.RingTheory.Huber.OpenIdeal

/-!
# Automatic continuity, completion functoriality, and canonical topology of dagger algebras

Let `K` be a complete ultrametric normed field and `A`, `B` be `K`-dagger algebras.

First, over any complete ultrametric field `K`, two `K`-algebra homomorphisms
`K⟨X⟩† → A` from a Monsky–Washnitzer algebra into a `K`-dagger algebra agree as soon as they agree
on the variables `Xᵢ` (`TauCeti.Dagger.washnitzerAlgebra.algHom_ext_of_isDaggerAlgebra`), with no
continuity or reducedness hypothesis.

Over a nontrivially normed `K`, the completion map `τ : A → Â` of `TauCeti.Dagger.toCompletion`
satisfies the universal property for `K`-affinoid targets: every `K`-algebra homomorphism
`φ : A → C` into a `K`-affinoid algebra extends uniquely to a `K`-algebra homomorphism
`Â → C` (`TauCeti.Dagger.completionLift`), with no continuity or norm assumed on `C` or `φ`.
Whenever `C` carries a complete ultrametric `K`-algebra norm, both the extension and `φ` itself
are automatically continuous (`TauCeti.Dagger.continuous_completionLift`,
`TauCeti.Dagger.continuous_algHom_of_isAffinoidAlgebra`), and `φ` preserves power-bounded elements.

Applying the universal property to `B → B̂` makes completion a functor on dagger algebras: every
`K`-algebra homomorphism `φ : A → B` induces a unique `K`-algebra homomorphism `φ̂ : Â → B̂`
compatible with the completion maps (`TauCeti.Dagger.completionMap`), and `φ̂` is automatically
continuous (`TauCeti.Dagger.continuous_completionMap`). Since `τ_B : B → B̂` is an isometry for the
residue norm on `B`, it follows that every `K`-algebra homomorphism `φ : A → B` between dagger
algebras is automatically continuous for their residue norm topologies
(`TauCeti.Dagger.continuous_algHom`), and every `K`-algebra isomorphism is a homeomorphism
(`TauCeti.Dagger.toContinuousAlgEquiv`).

Consequently, the residue norm topology and the completion of a dagger algebra are independent of
the chosen presentation up to canonical continuous `K`-algebra isomorphism:
* every surjective presentation `π : W_σ ↠ A` is an open quotient map onto `A` with its residue
  norm topology (`TauCeti.Dagger.isOpenQuotientMap_of_surjective_washnitzerAlgebra`) and induces a
  homeomorphism `W_σ ⧸ ker π ≃A[K] A` (`TauCeti.Dagger.quotientKerContinuousAlgEquiv`);
* any two presentations `W_σ ↠ C` and `W_τ ↠ C` give homeomorphic residue algebras
  (`TauCeti.Dagger.presentationContinuousAlgEquiv`);
* for any presentation `π : W_σ ↠ A`, the affinoid quotient `T_σ ⧸ (ker π) T_σ` is canonically
  isomorphic as a topological `K`-algebra to `completion K A`
  (`TauCeti.Dagger.presentationCompletionContinuousAlgEquiv`);
* in particular, `completion K (washnitzerAlgebra σ K) ≃A[K] T_σ` compatibly with `W_σ ⊆ T_σ`
  (`TauCeti.Dagger.completionWashnitzerContinuousAlgEquiv`).

## Main definitions

* `TauCeti.Dagger.completionLift`: the unique `K`-algebra extension `Â →ₐ[K] C` of a `K`-algebra
  homomorphism `A →ₐ[K] C` into an affinoid algebra.
* `TauCeti.Dagger.completionMap`: functoriality of completion on morphisms of dagger algebras.
* `TauCeti.Dagger.completionContinuousAlgEquiv`: continuous isomorphism `Â ≃A[K] B̂` induced by an
  algebra isomorphism `A ≃ₐ[K] B` of dagger algebras.
* `TauCeti.Dagger.toContinuousAlgEquiv`: every algebra isomorphism between dagger algebras is a
  homeomorphism for their residue norm topologies.
* `TauCeti.Dagger.quotientKerContinuousAlgEquiv` and
  `TauCeti.Dagger.presentationContinuousAlgEquiv`: presentation-independence of the residue norm
  topology.
* `TauCeti.Dagger.presentationCompletionContinuousAlgEquiv` and
  `TauCeti.Dagger.completionWashnitzerContinuousAlgEquiv`: presentation-independence of the
  completion and identification of the completion of `W_σ` with `T_σ`.

## Main results

* `TauCeti.Dagger.washnitzerAlgebra.algHom_ext_of_isDaggerAlgebra`: homomorphisms `W_σ →ₐ[K] A`
  into a dagger algebra are determined by their values on the variables.
* `TauCeti.Dagger.completionLift_unique`, `TauCeti.Dagger.existsUnique_algHom_comp_toCompletion`,
  `TauCeti.Dagger.completionMap_id`, `TauCeti.Dagger.completionMap_comp`: universal property and
  functoriality of completion.
* `TauCeti.Dagger.continuous_algHom` and `TauCeti.Dagger.isPowerBounded_map`: automatic continuity
  and preservation of power-boundedness for arbitrary morphisms of dagger algebras.
* `TauCeti.Dagger.isOpenQuotientMap_of_surjective_washnitzerAlgebra`: every presentation
  `W_σ ↠ A` is an open quotient map.

## References

* E. Grosse-Klönne, *Rigid analytic spaces with overconvergent structure sheaf*,
  J. reine angew. Math. 519 (2000), §1, Proposition 1.6 (2) and Theorem 1.7 (1).
-/

public section

namespace TauCeti.Dagger

open _root_.MvPowerSeries

section Extensionality

variable {K σ : Type*} [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [Finite σ]

/-- **Homomorphisms from `W` into a dagger algebra are determined by the variables.** Two
`K`-algebra homomorphisms `K⟨X⟩† → A` into a `K`-dagger algebra agreeing on every variable `Xᵢ` are
equal, with no continuity, norm, or reducedness hypothesis. -/
theorem washnitzerAlgebra.algHom_ext_of_isDaggerAlgebra {A : Type*} [CommRing A] [Algebra K A]
    [IsDaggerAlgebra K A] {φ ψ : washnitzerAlgebra σ K →ₐ[K] A}
    (h : ∀ i, φ (washnitzerAlgebra.X σ K i) = ψ (washnitzerAlgebra.X σ K i)) : φ = ψ :=
  have := IsDaggerAlgebra.isNoetherianRing (K := K) (A := A)
  washnitzerAlgebra.algHom_ext_of_isIntegral_quotient (fun m _ ↦
    have := IsDaggerAlgebra.finite_quotient_of_isMaximal K m
    Algebra.IsIntegral.of_finite K _) h

end Extensionality

section CompletionUniversal

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A : Type*} [CommRing A] [Algebra K A] [IsDaggerAlgebra K A]

/-- **Universal property of the completion of a dagger algebra.** Every `K`-algebra homomorphism
`φ : A → C` from a `K`-dagger algebra into a `K`-affinoid algebra extends uniquely to a `K`-algebra
homomorphism `Â → C` along `τ : A → Â`. No norm or continuity is assumed on `C` or `φ`. -/
noncomputable def completionLift {C : Type*} [CommRing C] [Algebra K C]
    (hC : IsAffinoidAlgebra K C) (φ : A →ₐ[K] C) : completion K A →ₐ[K] C :=
  washnitzerAlgebra.quotientToTateLift hC (φ.comp (residueAlgEquiv K A).symm.toAlgHom)

/-- `completionLift hC φ` extends `φ` on every element of `A`. -/
@[simp]
theorem completionLift_toCompletion {C : Type*} [CommRing C] [Algebra K C]
    (hC : IsAffinoidAlgebra K C) (φ : A →ₐ[K] C) (a : A) :
    completionLift hC φ (toCompletion K A a) = φ a := by
  obtain ⟨f, rfl⟩ := presentation_surjective K A a
  rw [completionLift, toCompletion_presentation, washnitzerAlgebra.quotientToTateLift_mk,
    AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, ← residueAlgEquiv_presentation,
    AlgEquiv.symm_apply_apply]

/-- `completionLift hC φ` restricts to `φ` along `toCompletion K A`. -/
@[simp]
theorem completionLift_comp_toCompletion {C : Type*} [CommRing C] [Algebra K C]
    (hC : IsAffinoidAlgebra K C) (φ : A →ₐ[K] C) :
    (completionLift hC φ).comp (toCompletion K A) = φ :=
  AlgHom.ext (completionLift_toCompletion hC φ)

/-- **Uniqueness of the completion extension.** Any `K`-algebra homomorphism `Â → C` into an
affinoid algebra restricting to `φ` on `A` equals `completionLift hC φ`. No continuity is assumed
on `Φ` or `φ`. -/
theorem completionLift_unique {C : Type*} [CommRing C] [Algebra K C]
    (hC : IsAffinoidAlgebra K C) {φ : A →ₐ[K] C} {Φ : completion K A →ₐ[K] C}
    (hΦ : Φ.comp (toCompletion K A) = φ) : Φ = completionLift hC φ := by
  refine washnitzerAlgebra.quotientToTateLift_unique hC (AlgHom.ext fun x ↦ ?_)
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [AlgHom.comp_apply, Ideal.quotient_map_mkₐ, Ideal.Quotient.mkₐ_eq_mk,
    ← toCompletion_presentation, ← AlgHom.comp_apply, hΦ, AlgHom.comp_apply,
    AlgEquiv.coe_toAlgHom, ← residueAlgEquiv_presentation, AlgEquiv.symm_apply_apply]

/-- **Universal property of `A → Â` for affinoid targets.** Every `K`-algebra homomorphism
`A → C` into a `K`-affinoid algebra extends uniquely to `Â → C`. -/
theorem existsUnique_algHom_comp_toCompletion {C : Type*} [CommRing C] [Algebra K C]
    (hC : IsAffinoidAlgebra K C) (φ : A →ₐ[K] C) :
    ∃! Φ : completion K A →ₐ[K] C, Φ.comp (toCompletion K A) = φ :=
  ⟨completionLift hC φ, completionLift_comp_toCompletion hC φ,
    fun _ hΦ ↦ completionLift_unique hC hΦ⟩

/-- Extending `toCompletion K A` itself yields the identity on `completion K A`. -/
@[simp]
theorem completionLift_toCompletion_id :
    completionLift isAffinoidAlgebra_completion (toCompletion K A) =
      AlgHom.id K (completion K A) := by
  symm
  exact completionLift_unique isAffinoidAlgebra_completion (AlgHom.id_comp _)

/-- Naturality of `completionLift` with respect to algebra homomorphisms of affinoid targets. -/
theorem completionLift_comp {C D : Type*} [CommRing C] [Algebra K C] [CommRing D] [Algebra K D]
    (hC : IsAffinoidAlgebra K C) (hD : IsAffinoidAlgebra K D) (θ : C →ₐ[K] D) (φ : A →ₐ[K] C) :
    completionLift hD (θ.comp φ) = θ.comp (completionLift hC φ) :=
  (completionLift_unique hD (by rw [AlgHom.comp_assoc, completionLift_comp_toCompletion])).symm

section NormedAffinoidTarget

variable {C : Type*} [NormedCommRing C] [NormedAlgebra K C] [IsUltrametricDist C] [CompleteSpace C]

/-- The completion extension `completionLift hC φ` is continuous for every complete ultrametric
algebra norm on the affinoid target `C`. -/
theorem continuous_completionLift (hC : IsAffinoidAlgebra K C) (φ : A →ₐ[K] C) :
    Continuous (completionLift hC φ) :=
  washnitzerAlgebra.continuous_quotientToTateLift hC _

/-- **Automatic continuity of dagger-to-affinoid homomorphisms.** Every `K`-algebra homomorphism
`A → C` from a dagger algebra into a completely normed affinoid algebra is continuous for the
residue norm on `A`. -/
theorem continuous_algHom_of_isAffinoidAlgebra (hC : IsAffinoidAlgebra K C) (φ : A →ₐ[K] C) :
    letI := residueNormedCommRing K A
    Continuous φ :=
  letI := residueNormedCommRing K A
  by
    rw [← completionLift_comp_toCompletion hC φ]
    exact (continuous_completionLift hC φ).comp (isometry_toCompletion K A).continuous

/-- Every `K`-algebra homomorphism `A → C` from a dagger algebra into a completely normed affinoid
algebra preserves power-bounded elements. -/
theorem isPowerBounded_map_of_isAffinoidAlgebra (hC : IsAffinoidAlgebra K C) (φ : A →ₐ[K] C)
    {a : A} :
    letI := residueNormedCommRing K A
    Huber.IsPowerBounded a → Huber.IsPowerBounded (φ a) :=
  letI := residueNormedCommRing K A
  letI := residueNormedAlgebra K A
  have := isUltrametricDist_residueNormedCommRing K A
  have := Huber.IsTateRing.of_normedAlgebra K A
  have := Huber.IsTateRing.of_normedAlgebra K C
  fun ha ↦ ha.map_of_isTateRing (f := (φ : A →+* C))
    (continuous_algHom_of_isAffinoidAlgebra hC φ).continuousAt

end NormedAffinoidTarget

end CompletionUniversal

section Functoriality

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A B C : Type*} [CommRing A] [Algebra K A] [IsDaggerAlgebra K A]
  [CommRing B] [Algebra K B] [IsDaggerAlgebra K B]
  [CommRing C] [Algebra K C] [IsDaggerAlgebra K C]

/-- **Functoriality of completion** (Grosse-Klönne, Theorem 1.7 (1)). Every `K`-algebra
homomorphism `φ : A → B` of dagger algebras extends uniquely to a `K`-algebra homomorphism
`φ̂ : Â → B̂` of their completions. -/
noncomputable def completionMap (φ : A →ₐ[K] B) : completion K A →ₐ[K] completion K B :=
  completionLift isAffinoidAlgebra_completion ((toCompletion K B).comp φ)

/-- `completionMap φ` commutes with the completion maps on elements of `A`. -/
@[simp]
theorem completionMap_toCompletion (φ : A →ₐ[K] B) (a : A) :
    completionMap φ (toCompletion K A a) = toCompletion K B (φ a) :=
  completionLift_toCompletion isAffinoidAlgebra_completion _ a

/-- `completionMap φ` satisfies `φ̂ ∘ τ_A = τ_B ∘ φ`. -/
@[simp]
theorem completionMap_comp_toCompletion (φ : A →ₐ[K] B) :
    (completionMap φ).comp (toCompletion K A) = (toCompletion K B).comp φ :=
  completionLift_comp_toCompletion isAffinoidAlgebra_completion _

/-- **Uniqueness of the induced map on completions.** Any `K`-algebra homomorphism `Â → B̂`
compatible with `φ : A → B` along the completion maps equals `completionMap φ`. -/
theorem completionMap_unique {φ : A →ₐ[K] B} {Φ : completion K A →ₐ[K] completion K B}
    (hΦ : Φ.comp (toCompletion K A) = (toCompletion K B).comp φ) : Φ = completionMap φ :=
  completionLift_unique isAffinoidAlgebra_completion hΦ

/-- The induced map `completionMap φ : Â → B̂` on completions is automatically continuous. -/
theorem continuous_completionMap (φ : A →ₐ[K] B) : Continuous (completionMap φ) :=
  continuous_completionLift (K := K) (C := completion K B) isAffinoidAlgebra_completion _

/-- Completion sends the identity morphism to the identity on `Â`. -/
@[simp]
theorem completionMap_id : completionMap (AlgHom.id K A) = AlgHom.id K (completion K A) :=
  (completionMap_unique (by simp)).symm

/-- Completion preserves composition of dagger algebra morphisms. -/
theorem completionMap_comp (ψ : B →ₐ[K] C) (φ : A →ₐ[K] B) :
    completionMap (ψ.comp φ) = (completionMap ψ).comp (completionMap φ) :=
  (completionMap_unique (by
    rw [AlgHom.comp_assoc, completionMap_comp_toCompletion, ← AlgHom.comp_assoc,
      completionMap_comp_toCompletion, AlgHom.comp_assoc])).symm

/-- Extending along a dagger morphism followed by an affinoid map agrees with precomposing with
`completionMap`. -/
theorem completionLift_comp_completionMap {D : Type*} [CommRing D] [Algebra K D]
    (hD : IsAffinoidAlgebra K D) (ψ : B →ₐ[K] D) (φ : A →ₐ[K] B) :
    (completionLift hD ψ).comp (completionMap φ) = completionLift hD (ψ.comp φ) :=
  completionLift_unique hD (by
    rw [AlgHom.comp_assoc, completionMap_comp_toCompletion, ← AlgHom.comp_assoc,
      completionLift_comp_toCompletion])

/-- An algebra isomorphism `A ≃ₐ[K] B` of dagger algebras induces a continuous algebra isomorphism
`Â ≃A[K] B̂` of their completions. -/
noncomputable def completionContinuousAlgEquiv (e : A ≃ₐ[K] B) :
    completion K A ≃A[K] completion K B where
  toAlgEquiv := AlgEquiv.ofAlgHom (completionMap e.toAlgHom) (completionMap e.symm.toAlgHom)
    (by rw [← completionMap_comp, AlgEquiv.comp_symm, completionMap_id])
    (by rw [← completionMap_comp, AlgEquiv.symm_comp, completionMap_id])
  continuous_toFun := continuous_completionMap e.toAlgHom
  continuous_invFun := continuous_completionMap e.symm.toAlgHom

/-- The underlying algebra homomorphism of `completionContinuousAlgEquiv e` is
`completionMap e.toAlgHom`. -/
@[simp]
theorem toAlgHom_completionContinuousAlgEquiv (e : A ≃ₐ[K] B) :
    (completionContinuousAlgEquiv e).toAlgHom = completionMap e.toAlgHom :=
  (rfl)

/-- `completionContinuousAlgEquiv e` commutes with the completion maps. -/
@[simp]
theorem completionContinuousAlgEquiv_toCompletion (e : A ≃ₐ[K] B) (a : A) :
    completionContinuousAlgEquiv e (toCompletion K A a) = toCompletion K B (e a) :=
  completionMap_toCompletion e.toAlgHom a

/-- `completionContinuousAlgEquiv` commutes with taking inverses. -/
@[simp]
theorem completionContinuousAlgEquiv_symm (e : A ≃ₐ[K] B) :
    (completionContinuousAlgEquiv e).symm = completionContinuousAlgEquiv e.symm :=
  ContinuousAlgEquiv.ext rfl

/-- `completionContinuousAlgEquiv` sends the identity equivalence to the identity. -/
@[simp]
theorem completionContinuousAlgEquiv_refl :
    completionContinuousAlgEquiv (AlgEquiv.refl (R := K) (A₁ := A)) =
      ContinuousAlgEquiv.refl (R := K) (A := completion K A) :=
  ContinuousAlgEquiv.toAlgEquiv_injective <| AlgEquiv.coe_toAlgHom_injective completionMap_id

/-- `completionContinuousAlgEquiv` preserves composition of algebra isomorphisms. -/
theorem completionContinuousAlgEquiv_trans (e₁ : A ≃ₐ[K] B) (e₂ : B ≃ₐ[K] C) :
    completionContinuousAlgEquiv (e₁.trans e₂) =
      (completionContinuousAlgEquiv e₁).trans (completionContinuousAlgEquiv e₂) :=
  ContinuousAlgEquiv.toAlgEquiv_injective <| AlgEquiv.coe_toAlgHom_injective <|
    completionMap_comp e₂.toAlgHom e₁.toAlgHom

end Functoriality

section AutomaticContinuity

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A B : Type*} [CommRing A] [Algebra K A] [IsDaggerAlgebra K A]
  [CommRing B] [Algebra K B] [IsDaggerAlgebra K B]

/-- **Automatic continuity for dagger algebras** (Grosse-Klönne, Proposition 1.6 (2)). Every
`K`-algebra homomorphism `φ : A → B` between `K`-dagger algebras is continuous for their residue
norm topologies, with no continuity hypothesis. -/
theorem continuous_algHom (φ : A →ₐ[K] B) :
    letI := residueNormedCommRing K A
    letI := residueNormedCommRing K B
    Continuous φ :=
  letI := residueNormedCommRing K A
  letI := residueNormedCommRing K B
  (isometry_toCompletion K B).comp_continuous_iff.mp <| by
    have h := continuous_algHom_of_isAffinoidAlgebra (K := K) (C := completion K B)
      isAffinoidAlgebra_completion ((toCompletion K B).comp φ)
    simpa only [AlgHom.coe_comp] using h

/-- Every `K`-algebra homomorphism between dagger algebras preserves power-bounded elements for
their residue norm topologies. -/
theorem isPowerBounded_map (φ : A →ₐ[K] B) {a : A} :
    letI := residueNormedCommRing K A
    letI := residueNormedCommRing K B
    Huber.IsPowerBounded a → Huber.IsPowerBounded (φ a) :=
  letI := residueNormedCommRing K A
  letI := residueNormedAlgebra K A
  letI := residueNormedCommRing K B
  letI := residueNormedAlgebra K B
  have := isUltrametricDist_residueNormedCommRing K A
  have := isUltrametricDist_residueNormedCommRing K B
  have := Huber.IsTateRing.of_normedAlgebra K A
  have := Huber.IsTateRing.of_normedAlgebra K B
  fun ha ↦ ha.map_of_isTateRing (f := (φ : A →+* B)) (continuous_algHom φ).continuousAt

/-- Every `K`-algebra isomorphism between dagger algebras is a homeomorphism for their residue
norm topologies. -/
noncomputable def toContinuousAlgEquiv (e : A ≃ₐ[K] B) :
    letI := residueNormedCommRing K A
    letI := residueNormedCommRing K B
    A ≃A[K] B :=
  letI := residueNormedCommRing K A
  letI := residueNormedCommRing K B
  { e with
    continuous_toFun := continuous_algHom e.toAlgHom
    continuous_invFun := continuous_algHom e.symm.toAlgHom }

/-- The homeomorphism attached to an algebra isomorphism has the same underlying function. -/
@[simp]
theorem coe_toContinuousAlgEquiv (e : A ≃ₐ[K] B) :
    letI := residueNormedCommRing K A
    letI := residueNormedCommRing K B
    ⇑(toContinuousAlgEquiv e) = e :=
  (rfl)

/-- The homeomorphism attached to an algebra isomorphism has that isomorphism as its underlying
algebra isomorphism. -/
@[simp]
theorem toAlgEquiv_toContinuousAlgEquiv (e : A ≃ₐ[K] B) :
    letI := residueNormedCommRing K A
    letI := residueNormedCommRing K B
    (toContinuousAlgEquiv e).toAlgEquiv = e :=
  (rfl)

end AutomaticContinuity

section PresentationIndependence

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]

local notation "Tate " σ:max => IsRestricted.subring (R := K) (fun _ : σ ↦ (1 : ℝ))

/-- Every `K`-algebra homomorphism `W_σ → A` from a Monsky–Washnitzer algebra into a dagger
algebra is continuous for the unit Gauss norm on `W_σ` and the residue norm on `A`. -/
theorem continuous_algHom_of_washnitzerAlgebra {σ : Type*} [Finite σ]
    {A : Type*} [CommRing A] [Algebra K A] [IsDaggerAlgebra K A]
    (π : washnitzerAlgebra σ K →ₐ[K] A) :
    letI := residueNormedCommRing K A
    Continuous π :=
  letI := residueNormedCommRing K A
  (isometry_toCompletion K A).comp_continuous_iff.mp <| by
    have h := washnitzerAlgebra.continuous_algHom_of_isAffinoidAlgebra
      (K := K) (C := completion K A) isAffinoidAlgebra_completion ((toCompletion K A).comp π)
    simpa only [AlgHom.coe_comp] using h

/-- For every surjective presentation `π : W_σ ↠ A` of a dagger algebra, the algebraic first
isomorphism theorem `W_σ ⧸ ker π ≃ A` is a homeomorphism between the residue Gauss norm on
`W_σ ⧸ ker π` and the canonical residue norm on `A`. -/
noncomputable def quotientKerContinuousAlgEquiv {σ : Type*} [Finite σ]
    {A : Type*} [CommRing A] [Algebra K A] [IsDaggerAlgebra K A]
    (π : washnitzerAlgebra σ K →ₐ[K] A) (hπ : Function.Surjective π) :
    letI := residueNormedCommRing K A
    (washnitzerAlgebra σ K ⧸ RingHom.ker π) ≃A[K] A :=
  letI := residueNormedCommRing K A
  { toAlgEquiv := Ideal.quotientKerAlgEquivOfSurjective hπ
    continuous_toFun := by
      have h : Continuous (Ideal.quotientKerAlgEquivOfSurjective hπ) :=
        (isometry_toCompletion K A).comp_continuous_iff.mp <| by
          have h' := washnitzerAlgebra.continuous_quotient_algHom_of_isAffinoidAlgebra
            (K := K) (C := completion K A) isAffinoidAlgebra_completion
            ((toCompletion K A).comp (Ideal.quotientKerAlgEquivOfSurjective hπ).toAlgHom)
          simpa only [AlgHom.coe_comp, AlgEquiv.coe_toAlgHom] using h'
      exact h
    continuous_invFun := by
      have h : Continuous (Ideal.quotientKerAlgEquivOfSurjective hπ).symm :=
        (Ideal.isometry_quotientMap_toTate (RingHom.ker π)).comp_continuous_iff.mp <| by
          let C := Tate σ ⧸ (RingHom.ker π).map (washnitzerAlgebra.toTate σ K)
          have h' := continuous_algHom_of_isAffinoidAlgebra (K := K) (C := C)
            ((isAffinoidAlgebra_tate (K := K) (σ := σ)).quotient _)
            ((Ideal.quotientMapₐ _ (washnitzerAlgebra.toTate σ K) Ideal.le_comap_map).comp
              (Ideal.quotientKerAlgEquivOfSurjective hπ).symm.toAlgHom)
          simpa only [AlgHom.coe_comp, AlgEquiv.coe_toAlgHom] using h'
      exact h }

/-- The homeomorphism `quotientKerContinuousAlgEquiv π hπ` sends the class of `f` to `π f`. -/
@[simp]
theorem quotientKerContinuousAlgEquiv_mk {σ : Type*} [Finite σ]
    {A : Type*} [CommRing A] [Algebra K A] [IsDaggerAlgebra K A]
    (π : washnitzerAlgebra σ K →ₐ[K] A) (hπ : Function.Surjective π) (f : washnitzerAlgebra σ K) :
    letI := residueNormedCommRing K A
    quotientKerContinuousAlgEquiv π hπ (Ideal.Quotient.mk _ f) = π f :=
  Ideal.quotientKerAlgEquivOfSurjective_mk hπ f

/-- The underlying algebra isomorphism of `quotientKerContinuousAlgEquiv π hπ` is the algebraic
first isomorphism theorem. -/
@[simp]
theorem toAlgEquiv_quotientKerContinuousAlgEquiv {σ : Type*} [Finite σ]
    {A : Type*} [CommRing A] [Algebra K A] [IsDaggerAlgebra K A]
    (π : washnitzerAlgebra σ K →ₐ[K] A) (hπ : Function.Surjective π) :
    letI := residueNormedCommRing K A
    (quotientKerContinuousAlgEquiv π hπ).toAlgEquiv = Ideal.quotientKerAlgEquivOfSurjective hπ :=
  (rfl)

/-- Every surjective Monsky–Washnitzer presentation `π : W_σ ↠ A` of a dagger algebra is an open
quotient map onto `A` with its canonical residue norm topology. -/
theorem isOpenQuotientMap_of_surjective_washnitzerAlgebra {σ : Type*} [Finite σ]
    {A : Type*} [CommRing A] [Algebra K A] [IsDaggerAlgebra K A]
    (π : washnitzerAlgebra σ K →ₐ[K] A) (hπ : Function.Surjective π) :
    letI := residueNormedCommRing K A
    IsOpenQuotientMap π :=
  letI := residueNormedCommRing K A
  by
    have hcomp : ⇑π = ⇑(quotientKerContinuousAlgEquiv π hπ).toHomeomorph ∘ ⇑(RingHom.ker π).mkQ :=
      funext fun f ↦ (quotientKerContinuousAlgEquiv_mk π hπ f).symm
    rw [hcomp]
    exact (quotientKerContinuousAlgEquiv π hπ).toHomeomorph.isOpenQuotientMap.comp
      (RingHom.ker π).isOpenQuotientMap_mkQ

/-- **Independence of presentation for the residue norm topology** (Grosse-Klönne, Proposition
1.6 (2)). Any two Monsky–Washnitzer presentations `W_σ ↠ C` and `W_τ ↠ C` of the same `K`-algebra
give homeomorphic residue algebras for their quotient Gauss norms. -/
noncomputable def presentationContinuousAlgEquiv {σ τ : Type*} [Finite σ] [Finite τ]
    {C : Type*} [CommRing C] [Algebra K C]
    (π₁ : washnitzerAlgebra σ K →ₐ[K] C) (hπ₁ : Function.Surjective π₁)
    (π₂ : washnitzerAlgebra τ K →ₐ[K] C) (hπ₂ : Function.Surjective π₂) :
    (washnitzerAlgebra σ K ⧸ RingHom.ker π₁) ≃A[K]
      (washnitzerAlgebra τ K ⧸ RingHom.ker π₂) :=
  let e := (Ideal.quotientKerAlgEquivOfSurjective hπ₁).trans
    (Ideal.quotientKerAlgEquivOfSurjective hπ₂).symm
  { e with
    continuous_toFun := washnitzerAlgebra.continuous_quotient_algHom e.toAlgHom
    continuous_invFun := washnitzerAlgebra.continuous_quotient_algHom e.symm.toAlgHom }

/-- The underlying algebra isomorphism of `presentationContinuousAlgEquiv` is the canonical
comparison between the two presentation quotients. -/
@[simp]
theorem toAlgEquiv_presentationContinuousAlgEquiv {σ τ : Type*} [Finite σ] [Finite τ]
    {C : Type*} [CommRing C] [Algebra K C]
    (π₁ : washnitzerAlgebra σ K →ₐ[K] C) (hπ₁ : Function.Surjective π₁)
    (π₂ : washnitzerAlgebra τ K →ₐ[K] C) (hπ₂ : Function.Surjective π₂) :
    (presentationContinuousAlgEquiv π₁ hπ₁ π₂ hπ₂).toAlgEquiv =
      (Ideal.quotientKerAlgEquivOfSurjective hπ₁).trans
        (Ideal.quotientKerAlgEquivOfSurjective hπ₂).symm :=
  (rfl)

/-- The presentation comparison is characterized by compatibility with both presentations. -/
@[simp]
theorem kerLiftAlg_presentationContinuousAlgEquiv {σ τ : Type*} [Finite σ] [Finite τ]
    {C : Type*} [CommRing C] [Algebra K C]
    (π₁ : washnitzerAlgebra σ K →ₐ[K] C) (hπ₁ : Function.Surjective π₁)
    (π₂ : washnitzerAlgebra τ K →ₐ[K] C) (hπ₂ : Function.Surjective π₂)
    (x : washnitzerAlgebra σ K ⧸ RingHom.ker π₁) :
    Ideal.kerLiftAlg π₂ (presentationContinuousAlgEquiv π₁ hπ₁ π₂ hπ₂ x) =
      Ideal.kerLiftAlg π₁ x := by
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective x
  obtain ⟨g, hg⟩ := hπ₂ (π₁ f)
  have h : ⇑(presentationContinuousAlgEquiv π₁ hπ₁ π₂ hπ₂) =
      ⇑((Ideal.quotientKerAlgEquivOfSurjective hπ₁).trans
        (Ideal.quotientKerAlgEquivOfSurjective hπ₂).symm) := rfl
  simp [h, ← hg]

/-- **Independence of presentation for the completion.** For any surjective presentation
`π : W_σ ↠ A` of a dagger algebra, the affinoid quotient `T_σ ⧸ (ker π) T_σ` is canonically
isomorphic as a topological `K`-algebra to `completion K A`, compatibly with `π` and `toCompletion`.
-/
noncomputable def presentationCompletionContinuousAlgEquiv {σ : Type*} [Finite σ]
    {A : Type*} [CommRing A] [Algebra K A] [IsDaggerAlgebra K A]
    (π : washnitzerAlgebra σ K →ₐ[K] A) (hπ : Function.Surjective π) :
    (Tate σ ⧸ (RingHom.ker π).map (washnitzerAlgebra.toTate σ K)) ≃A[K] completion K A :=
  let toFun : (Tate σ ⧸ (RingHom.ker π).map (washnitzerAlgebra.toTate σ K)) →ₐ[K]
      completion K A :=
    washnitzerAlgebra.quotientToTateLift isAffinoidAlgebra_completion
      ((toCompletion K A).comp (Ideal.quotientKerAlgEquivOfSurjective hπ).toAlgHom)
  let invFun : completion K A →ₐ[K]
      (Tate σ ⧸ (RingHom.ker π).map (washnitzerAlgebra.toTate σ K)) :=
    completionLift ((isAffinoidAlgebra_tate (K := K) (σ := σ)).quotient _)
      ((Ideal.quotientMapₐ _ (washnitzerAlgebra.toTate σ K) Ideal.le_comap_map).comp
        (Ideal.quotientKerAlgEquivOfSurjective hπ).symm.toAlgHom)
  { toAlgEquiv := AlgEquiv.ofAlgHom toFun invFun
      (by
        rw [← completionLift_toCompletion_id]
        exact completionLift_unique isAffinoidAlgebra_completion (AlgHom.ext fun a ↦ by
          obtain ⟨f, rfl⟩ := hπ a
          simp [toFun, invFun, Ideal.quotient_map_mkₐ]))
      (by
        rw [← washnitzerAlgebra.quotientToTateLift_quotientMap_id]
        exact washnitzerAlgebra.quotientToTateLift_unique
          ((isAffinoidAlgebra_tate (K := K) (σ := σ)).quotient _) (AlgHom.ext fun x ↦ by
            obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective x
            simp [toFun, invFun, Ideal.quotient_map_mkₐ]))
    continuous_toFun :=
      washnitzerAlgebra.continuous_quotientToTateLift (K := K) (C := completion K A)
        isAffinoidAlgebra_completion _
    continuous_invFun :=
      continuous_completionLift (K := K)
        (C := Tate σ ⧸ (RingHom.ker π).map (washnitzerAlgebra.toTate σ K))
        ((isAffinoidAlgebra_tate (K := K) (σ := σ)).quotient _) _ }

/-- `presentationCompletionContinuousAlgEquiv π hπ` sends the class of `toTate f` to
`toCompletion K A (π f)`. -/
@[simp]
theorem presentationCompletionContinuousAlgEquiv_mk {σ : Type*} [Finite σ]
    {A : Type*} [CommRing A] [Algebra K A] [IsDaggerAlgebra K A]
    (π : washnitzerAlgebra σ K →ₐ[K] A) (hπ : Function.Surjective π) (f : washnitzerAlgebra σ K) :
    presentationCompletionContinuousAlgEquiv π hπ
      (Ideal.Quotient.mk _ (washnitzerAlgebra.toTate σ K f)) = toCompletion K A (π f) := by
  have h : ⇑(presentationCompletionContinuousAlgEquiv π hπ) =
      washnitzerAlgebra.quotientToTateLift isAffinoidAlgebra_completion
        ((toCompletion K A).comp (Ideal.quotientKerAlgEquivOfSurjective hπ).toAlgHom) := rfl
  rw [h, washnitzerAlgebra.quotientToTateLift_mk, AlgHom.comp_apply, AlgEquiv.coe_toAlgHom,
    Ideal.quotientKerAlgEquivOfSurjective_mk]

/-- The inverse of `presentationCompletionContinuousAlgEquiv π hπ` sends `toCompletion K A (π f)`
to the class of `toTate f`. -/
@[simp]
theorem presentationCompletionContinuousAlgEquiv_symm_toCompletion {σ : Type*} [Finite σ]
    {A : Type*} [CommRing A] [Algebra K A] [IsDaggerAlgebra K A]
    (π : washnitzerAlgebra σ K →ₐ[K] A) (hπ : Function.Surjective π) (f : washnitzerAlgebra σ K) :
    (presentationCompletionContinuousAlgEquiv π hπ).symm (toCompletion K A (π f)) =
      Ideal.Quotient.mk _ (washnitzerAlgebra.toTate σ K f) :=
  (presentationCompletionContinuousAlgEquiv π hπ).symm_apply_eq.mpr
    (presentationCompletionContinuousAlgEquiv_mk π hπ f).symm

end PresentationIndependence

section CompletionWashnitzer

/-- **The completion of the Monsky–Washnitzer algebra is the Tate algebra.** For every finite
variable type `σ`, `completion K (washnitzerAlgebra σ K)` is canonically isomorphic as a
topological `K`-algebra to `T_σ = K⟨X⟩`, compatibly with `W_σ ⊆ T_σ`. -/
noncomputable def completionWashnitzerContinuousAlgEquiv (σ K : Type*)
    [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K] [Finite σ] :
    completion K (washnitzerAlgebra σ K) ≃A[K]
      IsRestricted.subring (R := K) (fun _ : σ ↦ (1 : ℝ)) :=
  let toFun := completionLift (isAffinoidAlgebra_tate (K := K) (σ := σ))
    (washnitzerAlgebra.toTate σ K)
  let invFun := washnitzerAlgebra.toTateLift isAffinoidAlgebra_completion
    (toCompletion K (washnitzerAlgebra σ K))
  { toAlgEquiv := AlgEquiv.ofAlgHom toFun invFun
      (by
        rw [← washnitzerAlgebra.toTateLift_toTate_id]
        exact washnitzerAlgebra.toTateLift_unique (isAffinoidAlgebra_tate (K := K) (σ := σ))
          (AlgHom.ext fun f ↦ by simp [toFun, invFun]))
      (by
        rw [← completionLift_toCompletion_id]
        exact completionLift_unique isAffinoidAlgebra_completion
          (AlgHom.ext fun f ↦ by simp [toFun, invFun]))
    continuous_toFun :=
      continuous_completionLift (K := K)
        (C := IsRestricted.subring (R := K) (fun _ : σ ↦ (1 : ℝ)))
        (isAffinoidAlgebra_tate (K := K) (σ := σ)) _
    continuous_invFun :=
      washnitzerAlgebra.continuous_toTateLift (K := K)
        (C := completion K (washnitzerAlgebra σ K)) isAffinoidAlgebra_completion _ }

/-- `completionWashnitzerContinuousAlgEquiv` intertwines `toCompletion` with `toTate`. -/
@[simp]
theorem completionWashnitzerContinuousAlgEquiv_toCompletion {σ K : Type*}
    [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K] [Finite σ]
    (f : washnitzerAlgebra σ K) :
    completionWashnitzerContinuousAlgEquiv σ K (toCompletion K (washnitzerAlgebra σ K) f) =
      washnitzerAlgebra.toTate σ K f := by
  dsimp [completionWashnitzerContinuousAlgEquiv]
  exact completionLift_toCompletion (isAffinoidAlgebra_tate (K := K) (σ := σ)) _ f

/-- The inverse of `completionWashnitzerContinuousAlgEquiv` sends `toTate f` to `toCompletion f`. -/
@[simp]
theorem completionWashnitzerContinuousAlgEquiv_symm_toTate {σ K : Type*}
    [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K] [Finite σ]
    (f : washnitzerAlgebra σ K) :
    (completionWashnitzerContinuousAlgEquiv σ K).symm (washnitzerAlgebra.toTate σ K f) =
      toCompletion K (washnitzerAlgebra σ K) f :=
  (completionWashnitzerContinuousAlgEquiv σ K).symm_apply_eq.mpr
    (completionWashnitzerContinuousAlgEquiv_toCompletion f).symm

end CompletionWashnitzer

section Examples

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]

-- Edge case: the completion of the zero dagger algebra `W_1 ⧸ ⊤` is trivial, so `completionMap`
-- into it vanishes identically.
example (φ : K →ₐ[K] (washnitzerAlgebra (Fin 1) K ⧸ (⊤ : Ideal (washnitzerAlgebra (Fin 1) K))))
    (x : completion K K) : completionMap φ x = 0 := by
  let A0 := washnitzerAlgebra (Fin 1) K ⧸ (⊤ : Ideal (washnitzerAlgebra (Fin 1) K))
  have htop : (RingHom.ker (presentation K A0)).map (washnitzerAlgebra.toTate _ K) = ⊤ := by
    have : Subsingleton A0 := inferInstance
    have hker : RingHom.ker (presentation K A0) = ⊤ :=
      eq_top_iff.mpr fun f _ ↦ RingHom.mem_ker.mpr (Subsingleton.elim _ _)
    rw [hker, Ideal.map_top]
  have : Subsingleton (completion K A0) := Ideal.Quotient.subsingleton_iff.mpr htop
  exact Subsingleton.elim _ _

-- Compatibility with the variables: `completionWashnitzerContinuousAlgEquiv` sends each
-- completed coordinate `Xᵢ` to the corresponding Tate variable `Xᵢ`.
example (n : ℕ) (i : Fin n) :
    completionWashnitzerContinuousAlgEquiv (Fin n) K
      (toCompletion K (washnitzerAlgebra (Fin n) K) (washnitzerAlgebra.X (Fin n) K i)) =
        ⟨_root_.MvPowerSeries.X i, isRestricted_X _ i⟩ := by
  rw [completionWashnitzerContinuousAlgEquiv_toCompletion]
  exact Subtype.ext (by simp)

-- Nonreduced quotient: the presentation completion of `W_1 ⧸ (X²)` keeps the nilpotent generator
-- nonzero with square zero.
example :
    let W := washnitzerAlgebra (Fin 1) K
    let I : Ideal W := Ideal.span {washnitzerAlgebra.X (Fin 1) K 0 ^ 2}
    let π : W →ₐ[K] (W ⧸ I) := Ideal.Quotient.mkₐ K I
    let x := toCompletion K (W ⧸ I) (π (washnitzerAlgebra.X (Fin 1) K 0))
    x ≠ 0 ∧ x ^ 2 = 0 := by
  intro W I π x
  constructor
  · intro hx
    have hmk := congrArg
      (presentationCompletionContinuousAlgEquiv π (Ideal.Quotient.mkₐ_surjective K I)).symm hx
    rw [presentationCompletionContinuousAlgEquiv_symm_toCompletion, map_zero] at hmk
    have hm := Ideal.Quotient.eq_zero_iff_mem.mp hmk
    have hker : RingHom.ker π = I := Ideal.mk_ker
    rw [hker, Ideal.map_span, Set.image_singleton, map_pow] at hm
    have hd : (washnitzerAlgebra.toTate (Fin 1) K (washnitzerAlgebra.X (Fin 1) K 0)) ^ 2 ∣
        washnitzerAlgebra.toTate (Fin 1) K (washnitzerAlgebra.X (Fin 1) K 0) :=
      Ideal.mem_span_singleton.mp hm
    have hdiv : (_root_.MvPowerSeries.X 0 : MvPowerSeries (Fin 1) K) ^ 2 ∣
        _root_.MvPowerSeries.X 0 := by
      have h := map_dvd (IsRestricted.subring
        (R := K) (fun _ : Fin 1 ↦ (1 : ℝ))).subtype hd
      simpa only [map_pow, Subring.subtype_apply, washnitzerAlgebra.coe_toTate,
        washnitzerAlgebra.coe_X] using h
    have hc := X_pow_dvd_iff.mp hdiv (Finsupp.single 0 1) (by simp)
    simp [coeff_X] at hc
  · dsimp only [x]
    rw [← map_pow, ← map_pow]
    have hzero : π (washnitzerAlgebra.X (Fin 1) K 0 ^ 2) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span rfl)
    rw [hzero, map_zero]

end Examples

end TauCeti.Dagger

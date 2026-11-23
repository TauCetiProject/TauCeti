/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Affinoid.QuotientNorm
public import TauCeti.RingTheory.Dagger.DaggerAlgebra.Completion
public import TauCeti.RingTheory.Dagger.SupSeminorm

import TauCeti.RingTheory.Dagger.DaggerAlgebra.FaithfullyFlat
import TauCeti.RingTheory.Dagger.TateLift

/-!
# Universal property and functoriality of the completion of a dagger algebra

Let `K` be a complete nontrivially normed ultrametric field and `A` a `K`-dagger algebra, with
completion map `τ : A → Â = completion K A`. Although `Â` is constructed from the chosen minimal
presentation `W_n ↠ A` as `T_n ⧸ I T_n`, it is characterized up to unique `K`-algebra isomorphism
under `A` by a purely algebraic universal property: `τ : A → Â` is initial among `K`-algebra
homomorphisms from `A` into `K`-affinoid algebras, with no continuity or norm assumed on the
target.

Both existence and uniqueness specialize the Monsky–Washnitzer quotient extension
`TauCeti.Dagger.washnitzerAlgebra.liftToTateQuotient` and extensionality theorem
`TauCeti.Dagger.washnitzerAlgebra.tateQuotient_algHom_ext_of_isAffinoidAlgebra` (established in
`TauCeti.RingTheory.Dagger.TateLift`) to the minimal presentation `presentation K A : W_n ↠ A`.

Specializing `S` to the completion `B̂` of a second dagger algebra `B` makes `A ↦ Â` a functor
(`AlgHom.daggerCompletionMap`) sending `K`-algebra isomorphisms to topological `K`-algebra
isomorphisms (`AlgEquiv.daggerCompletionContinuousAlgEquiv`). Applying the universal
property in both directions identifies `Â` with `T_σ ⧸ (ker π) T_σ` for every presentation
`π : W_σ ↠ A` (`AlgHom.daggerPresentationCompletionContinuousAlgEquiv`), and in particular
identifies the completion of `W_σ` with `T_σ`
(`TauCeti.Dagger.washnitzerAlgebra.completionContinuousAlgEquiv`).

## Main definitions

* `TauCeti.Dagger.completionLift`, `TauCeti.Dagger.completionLiftEquiv`: the universal extension
  `(completion K A →ₐ[K] S) ≃ (A →ₐ[K] S)` for an affinoid algebra `S`.
* `AlgHom.daggerCompletionMap`: the completion `completion K A →ₐ[K] completion K B` of a
  morphism `A →ₐ[K] B` of dagger algebras, together with
  `AlgEquiv.daggerCompletionAlgEquiv` and
  `AlgEquiv.daggerCompletionContinuousAlgEquiv`: the induced algebraic and topological
  isomorphisms for `A ≃ₐ[K] B`.
* `AlgHom.daggerPresentationCompletionContinuousAlgEquiv`: comparison of `completion K A` with
  `T_σ ⧸ (ker π) T_σ` for an arbitrary presentation `π : W_σ ↠ A`.
* `TauCeti.Dagger.washnitzerAlgebra.completionContinuousAlgEquiv`: the topological `K`-algebra
  isomorphism `completion K (washnitzerAlgebra σ K) ≃A[K] T_σ`.

## Main results

* `TauCeti.Dagger.completion_algHom_ext_of_isAffinoidAlgebra` and
  `TauCeti.Dagger.existsUnique_algHom_completion`: every `K`-algebra map `A →ₐ[K] S` into an
  affinoid algebra factors uniquely through `toCompletion K A`.
* `TauCeti.Dagger.completion_algHom_ext`, `AlgHom.daggerCompletionMap_unique`,
  `AlgHom.daggerCompletionMap_id`, `AlgHom.daggerCompletionMap_comp`,
  `AlgHom.continuous_daggerCompletionMap`: uniqueness, functoriality, and continuity of
  `AlgHom.daggerCompletionMap`.
* `TauCeti.Dagger.supSeminorm_toCompletion`, `AlgHom.supSeminorm_map_le_of_isDaggerAlgebra`,
  `TauCeti.Dagger.IsDaggerAlgebra.supSeminorm_eq_zero_iff`,
  `TauCeti.Dagger.IsDaggerAlgebra.isReduced_iff_supSeminorm_eq_zero`: the completion map preserves
  `supSeminorm`, morphisms of dagger algebras contract it, and its kernel is the nilradical.

## References

* E. Grosse-Klönne, *Rigid analytic spaces with overconvergent structure sheaf*,
  J. reine angew. Math. 519 (2000), §1.2 and Theorem 1.7 (1).
* [Bosch, Güntzer, Remmert, *Non-Archimedean Analysis*][bosch-guntzer-remmert], §6.1.3.

The extension and uniqueness arguments adapt the restricted-series universal property in
`TauCeti.RingTheory.Affinoid.Restricted` and automatic continuity in
`TauCeti.RingTheory.Affinoid.Continuity` and `TauCeti.RingTheory.Affinoid.QuotientNorm` to
Monsky–Washnitzer presentations via `TauCeti.RingTheory.Dagger.TateLift`.
-/

public section

namespace TauCeti.Dagger

open _root_.MvPowerSeries

section CompletionLift

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A S : Type*} [CommRing A] [Algebra K A] [IsDaggerAlgebra K A]
  [CommRing S] [Algebra K S]

/-- Two `K`-algebra homomorphisms out of `completion K A` into an affinoid algebra that agree on
`toCompletion K A` are equal. No continuity or norm on `S` is assumed. -/
theorem completion_algHom_ext_of_isAffinoidAlgebra (hS : IsAffinoidAlgebra K S)
    {Φ₁ Φ₂ : completion K A →ₐ[K] S}
    (h : ∀ a, Φ₁ (toCompletion K A a) = Φ₂ (toCompletion K A a)) : Φ₁ = Φ₂ :=
  washnitzerAlgebra.tateQuotient_algHom_ext_of_isAffinoidAlgebra hS fun f ↦ by
    simpa only [← toCompletion_presentation] using h (presentation K A f)

/-- **Universal extension to the completion.** Every `K`-algebra homomorphism `φ : A →ₐ[K] S` from
a dagger algebra into an affinoid algebra extends across `toCompletion K A : A →ₐ[K] completion K A`
to a `K`-algebra homomorphism `completion K A →ₐ[K] S`. -/
noncomputable def completionLift (hS : IsAffinoidAlgebra K S) (φ : A →ₐ[K] S) :
    completion K A →ₐ[K] S :=
  washnitzerAlgebra.liftToTateQuotient hS (RingHom.ker (presentation K A))
    (φ.comp (presentation K A)) fun _ hf ↦ by simp [RingHom.mem_ker.mp hf]

/-- `completionLift` extends `φ` on every element of `A`. -/
@[simp]
theorem completionLift_toCompletion (hS : IsAffinoidAlgebra K S) (φ : A →ₐ[K] S) (a : A) :
    completionLift hS φ (toCompletion K A a) = φ a := by
  obtain ⟨f, rfl⟩ := presentation_surjective K A a
  simp [completionLift]

/-- Precomposing `completionLift` with `toCompletion` recovers `φ`. -/
@[simp]
theorem completionLift_comp_toCompletion (hS : IsAffinoidAlgebra K S) (φ : A →ₐ[K] S) :
    (completionLift hS φ).comp (toCompletion K A) = φ :=
  AlgHom.ext (completionLift_toCompletion hS φ)

/-- **Universal property of the completion of a dagger algebra.** For every `K`-affinoid algebra `S`
and `K`-algebra homomorphism `φ : A →ₐ[K] S`, there is a unique `K`-algebra homomorphism
`Φ : completion K A →ₐ[K] S` with `Φ ∘ toCompletion K A = φ`. -/
theorem existsUnique_algHom_completion (hS : IsAffinoidAlgebra K S) (φ : A →ₐ[K] S) :
    ∃! Φ : completion K A →ₐ[K] S, Φ.comp (toCompletion K A) = φ :=
  ⟨completionLift hS φ, completionLift_comp_toCompletion hS φ, fun _ hΦ ↦
    completion_algHom_ext_of_isAffinoidAlgebra hS fun a ↦ by
      rw [← AlgHom.comp_apply, hΦ, completionLift_toCompletion]⟩

/-- Precomposition with `toCompletion K A` identifies `K`-algebra homomorphisms
`completion K A →ₐ[K] S` into an affinoid algebra with `K`-algebra homomorphisms `A →ₐ[K] S`. -/
noncomputable def completionLiftEquiv (hS : IsAffinoidAlgebra K S) :
    (completion K A →ₐ[K] S) ≃ (A →ₐ[K] S) where
  toFun Φ := Φ.comp (toCompletion K A)
  invFun := completionLift hS
  left_inv Φ := completion_algHom_ext_of_isAffinoidAlgebra hS
    (completionLift_toCompletion hS (Φ.comp (toCompletion K A)))
  right_inv := completionLift_comp_toCompletion hS

/-- Applying `completionLiftEquiv` precomposes with `toCompletion K A`. -/
@[simp]
theorem completionLiftEquiv_apply (hS : IsAffinoidAlgebra K S) (Φ : completion K A →ₐ[K] S) :
    completionLiftEquiv hS Φ = Φ.comp (toCompletion K A) := (rfl)

/-- The inverse of `completionLiftEquiv` is `completionLift`. -/
@[simp]
theorem completionLiftEquiv_symm_apply (hS : IsAffinoidAlgebra K S) (φ : A →ₐ[K] S) :
    (completionLiftEquiv hS).symm φ = completionLift hS φ := (rfl)

end CompletionLift

section CompletionExt

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A B : Type*} [CommRing A] [Algebra K A] [IsDaggerAlgebra K A]
  [CommRing B] [Algebra K B] [IsDaggerAlgebra K B]

/-- Two `K`-algebra homomorphisms between completions of dagger algebras that agree on `A` are
equal. -/
theorem completion_algHom_ext {Φ₁ Φ₂ : completion K A →ₐ[K] completion K B}
    (h : ∀ a, Φ₁ (toCompletion K A a) = Φ₂ (toCompletion K A a)) : Φ₁ = Φ₂ :=
  completion_algHom_ext_of_isAffinoidAlgebra isAffinoidAlgebra_completion h

end CompletionExt

end TauCeti.Dagger

namespace AlgHom

open TauCeti TauCeti.Dagger

section DaggerCompletion

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A B C : Type*} [CommRing A] [Algebra K A] [IsDaggerAlgebra K A]
  [CommRing B] [Algebra K B] [IsDaggerAlgebra K B]
  [CommRing C] [Algebra K C] [IsDaggerAlgebra K C]

/-- **Functoriality of dagger completion.** Every `K`-algebra homomorphism `φ : A →ₐ[K] B` of
dagger algebras extends uniquely to a `K`-algebra homomorphism
`φ̂ : completion K A →ₐ[K] completion K B` compatible with `toCompletion`. -/
noncomputable def daggerCompletionMap (φ : A →ₐ[K] B) : completion K A →ₐ[K] completion K B :=
  completionLift isAffinoidAlgebra_completion ((toCompletion K B).comp φ)

/-- `φ.daggerCompletionMap` commutes with `toCompletion` on elements. -/
@[simp]
theorem daggerCompletionMap_toCompletion (φ : A →ₐ[K] B) (a : A) :
    φ.daggerCompletionMap (toCompletion K A a) = toCompletion K B (φ a) :=
  completionLift_toCompletion isAffinoidAlgebra_completion _ a

/-- `φ.daggerCompletionMap` intertwines the completion maps. -/
@[simp]
theorem daggerCompletionMap_comp_toCompletion (φ : A →ₐ[K] B) :
    φ.daggerCompletionMap.comp (toCompletion K A) = (toCompletion K B).comp φ :=
  completionLift_comp_toCompletion isAffinoidAlgebra_completion _

/-- `φ.daggerCompletionMap` is the unique `K`-algebra homomorphism `Â →ₐ[K] B̂` intertwining `φ`
with `toCompletion`. -/
theorem daggerCompletionMap_unique {φ : A →ₐ[K] B} {Φ : completion K A →ₐ[K] completion K B}
    (h : Φ.comp (toCompletion K A) = (toCompletion K B).comp φ) : Φ = φ.daggerCompletionMap :=
  completion_algHom_ext fun a ↦ by
    rw [← AlgHom.comp_apply, h, AlgHom.comp_apply, daggerCompletionMap_toCompletion]

/-- The induced map between dagger completions is continuous for their quotient Gauss norms. -/
theorem continuous_daggerCompletionMap (φ : A →ₐ[K] B) : Continuous φ.daggerCompletionMap :=
  have := (isAffinoidAlgebra_completion (K := K) (A := A)).isNoetherianRing
  IsAffinoidAlgebra.continuous_algHom (K := K) (A := completion K B) (B := completion K A)
    isAffinoidAlgebra_completion φ.daggerCompletionMap

/-- `daggerCompletionMap` sends the identity homomorphism to the identity homomorphism. -/
@[simp]
theorem daggerCompletionMap_id :
    (AlgHom.id K A).daggerCompletionMap = AlgHom.id K (completion K A) :=
  completion_algHom_ext fun a ↦ by simp

/-- `daggerCompletionMap` respects composition of `K`-algebra homomorphisms. -/
@[simp]
theorem daggerCompletionMap_comp (ψ : B →ₐ[K] C) (φ : A →ₐ[K] B) :
    (ψ.comp φ).daggerCompletionMap = ψ.daggerCompletionMap.comp φ.daggerCompletionMap :=
  completion_algHom_ext fun a ↦ by simp

end DaggerCompletion

end AlgHom

namespace AlgEquiv

open TauCeti TauCeti.Dagger

section DaggerCompletion

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A B C : Type*} [CommRing A] [Algebra K A] [IsDaggerAlgebra K A]
  [CommRing B] [Algebra K B] [IsDaggerAlgebra K B]
  [CommRing C] [Algebra K C] [IsDaggerAlgebra K C]

/-- A `K`-algebra isomorphism of dagger algebras induces a `K`-algebra isomorphism of their
completions. -/
noncomputable def daggerCompletionAlgEquiv (e : A ≃ₐ[K] B) :
    completion K A ≃ₐ[K] completion K B :=
  AlgEquiv.ofAlgHom e.toAlgHom.daggerCompletionMap e.symm.toAlgHom.daggerCompletionMap
    (completion_algHom_ext fun b ↦ by simp)
    (completion_algHom_ext fun a ↦ by simp)

/-- The underlying `AlgHom` of `e.daggerCompletionAlgEquiv` is `e.toAlgHom.daggerCompletionMap`. -/
@[simp]
theorem toAlgHom_daggerCompletionAlgEquiv (e : A ≃ₐ[K] B) :
    e.daggerCompletionAlgEquiv.toAlgHom = e.toAlgHom.daggerCompletionMap := (rfl)

/-- Applying `e.daggerCompletionAlgEquiv` evaluates `e.toAlgHom.daggerCompletionMap`. -/
@[simp]
theorem daggerCompletionAlgEquiv_apply (e : A ≃ₐ[K] B) (x : completion K A) :
    e.daggerCompletionAlgEquiv x = e.toAlgHom.daggerCompletionMap x := (rfl)

/-- `daggerCompletionAlgEquiv` commutes with `.symm`. -/
@[simp]
theorem daggerCompletionAlgEquiv_symm (e : A ≃ₐ[K] B) :
    e.daggerCompletionAlgEquiv.symm = e.symm.daggerCompletionAlgEquiv := (rfl)

/-- `daggerCompletionAlgEquiv` sends `AlgEquiv.refl` to `AlgEquiv.refl`. -/
@[simp]
theorem daggerCompletionAlgEquiv_refl :
    (AlgEquiv.refl : A ≃ₐ[K] A).daggerCompletionAlgEquiv = AlgEquiv.refl := by
  ext x
  simp

/-- `daggerCompletionAlgEquiv` respects composition of `K`-algebra isomorphisms. -/
@[simp]
theorem daggerCompletionAlgEquiv_trans (e₁ : A ≃ₐ[K] B) (e₂ : B ≃ₐ[K] C) :
    (e₁.trans e₂).daggerCompletionAlgEquiv =
      e₁.daggerCompletionAlgEquiv.trans e₂.daggerCompletionAlgEquiv := by
  ext x
  have h : (e₁.trans e₂).toAlgHom = e₂.toAlgHom.comp e₁.toAlgHom := rfl
  simp [h]

/-- A `K`-algebra isomorphism of dagger algebras induces a topological `K`-algebra isomorphism of
their completions. -/
noncomputable def daggerCompletionContinuousAlgEquiv (e : A ≃ₐ[K] B) :
    completion K A ≃A[K] completion K B :=
  IsAffinoidAlgebra.toContinuousAlgEquiv (K := K) (A := completion K A) (B := completion K B)
    isAffinoidAlgebra_completion e.daggerCompletionAlgEquiv

/-- The underlying `AlgEquiv` of `e.daggerCompletionContinuousAlgEquiv` is
`e.daggerCompletionAlgEquiv`. -/
@[simp]
theorem toAlgEquiv_daggerCompletionContinuousAlgEquiv (e : A ≃ₐ[K] B) :
    e.daggerCompletionContinuousAlgEquiv.toAlgEquiv = e.daggerCompletionAlgEquiv := by
  simp [daggerCompletionContinuousAlgEquiv]

/-- Applying `e.daggerCompletionContinuousAlgEquiv` evaluates `e.toAlgHom.daggerCompletionMap`. -/
@[simp]
theorem daggerCompletionContinuousAlgEquiv_apply (e : A ≃ₐ[K] B) (x : completion K A) :
    e.daggerCompletionContinuousAlgEquiv x = e.toAlgHom.daggerCompletionMap x := by
  simp [daggerCompletionContinuousAlgEquiv]

/-- `e.daggerCompletionContinuousAlgEquiv` commutes with `toCompletion`. -/
theorem daggerCompletionContinuousAlgEquiv_toCompletion (e : A ≃ₐ[K] B) (a : A) :
    e.daggerCompletionContinuousAlgEquiv (toCompletion K A a) = toCompletion K B (e a) := by
  simp

/-- `daggerCompletionContinuousAlgEquiv` commutes with `.symm`. -/
@[simp]
theorem daggerCompletionContinuousAlgEquiv_symm (e : A ≃ₐ[K] B) :
    e.daggerCompletionContinuousAlgEquiv.symm = e.symm.daggerCompletionContinuousAlgEquiv := by
  ext x
  refine e.daggerCompletionContinuousAlgEquiv.symm_apply_eq.mpr ?_
  have h : e.toAlgHom.daggerCompletionMap (e.symm.toAlgHom.daggerCompletionMap x) = x := by
    simp [← AlgHom.comp_apply, ← AlgHom.daggerCompletionMap_comp]
  simpa using h.symm

/-- `daggerCompletionContinuousAlgEquiv` sends `AlgEquiv.refl` to `ContinuousAlgEquiv.refl`. -/
@[simp]
theorem daggerCompletionContinuousAlgEquiv_refl :
    (AlgEquiv.refl : A ≃ₐ[K] A).daggerCompletionContinuousAlgEquiv =
      ContinuousAlgEquiv.refl K (completion K A) := by
  ext x
  simp

/-- `daggerCompletionContinuousAlgEquiv` respects composition of `K`-algebra isomorphisms. -/
@[simp]
theorem daggerCompletionContinuousAlgEquiv_trans (e₁ : A ≃ₐ[K] B) (e₂ : B ≃ₐ[K] C) :
    (e₁.trans e₂).daggerCompletionContinuousAlgEquiv =
      e₁.daggerCompletionContinuousAlgEquiv.trans e₂.daggerCompletionContinuousAlgEquiv := by
  ext x
  have h : (e₁.trans e₂).toAlgHom = e₂.toAlgHom.comp e₁.toAlgHom := rfl
  simp [h]

end DaggerCompletion

end AlgEquiv

namespace AlgHom

open TauCeti TauCeti.Dagger _root_.MvPowerSeries

section PresentationComparison

variable {K σ : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  [_root_.Finite σ] {A : Type*} [CommRing A] [Algebra K A] [IsDaggerAlgebra K A]

local notation "T " α:max => IsRestricted.subring (R := K) (fun _ : α ↦ (1 : ℝ))

/-- The canonical `K`-algebra map `A → T_σ ⧸ (ker π) T_σ` attached to an arbitrary surjective
presentation `π : W_σ ↠ A`. -/
private noncomputable def toPresentationCompletion (π : washnitzerAlgebra σ K →ₐ[K] A)
    (hπ : Function.Surjective π) :
    A →ₐ[K] T σ ⧸ (RingHom.ker π).map (washnitzerAlgebra.toTate σ K) :=
  (Ideal.quotientMapₐ _ (washnitzerAlgebra.toTate σ K) Ideal.le_comap_map).comp
    (Ideal.quotientKerAlgEquivOfSurjective hπ).symm.toAlgHom

omit [CompleteSpace K] [_root_.Finite σ] [IsDaggerAlgebra K A] in
@[simp]
private theorem toPresentationCompletion_apply (π : washnitzerAlgebra σ K →ₐ[K] A)
    (hπ : Function.Surjective π) (f : washnitzerAlgebra σ K) :
    toPresentationCompletion π hπ (π f) =
      Ideal.Quotient.mk _ (washnitzerAlgebra.toTate σ K f) := by
  simp [toPresentationCompletion]

/-- The forward map `completion K A →ₐ[K] T_σ ⧸ (ker π) T_σ` induced by `completionLift`. -/
private noncomputable def presentationCompletionFwd
    (π : washnitzerAlgebra σ K →ₐ[K] A) (hπ : Function.Surjective π) :
    completion K A →ₐ[K] T σ ⧸ (RingHom.ker π).map (washnitzerAlgebra.toTate σ K) :=
  completionLift (isAffinoidAlgebra_tate.quotient _) (toPresentationCompletion π hπ)

/-- The backward map `(T_σ ⧸ (ker π) T_σ) →ₐ[K] completion K A` induced by `liftToTateQuotient`. -/
private noncomputable def presentationCompletionBwd
    (π : washnitzerAlgebra σ K →ₐ[K] A) :
    (T σ ⧸ (RingHom.ker π).map (washnitzerAlgebra.toTate σ K)) →ₐ[K] completion K A :=
  washnitzerAlgebra.liftToTateQuotient isAffinoidAlgebra_completion (RingHom.ker π)
    ((toCompletion K A).comp π) fun _ hf ↦ by simp [RingHom.mem_ker.mp hf]

private theorem presentationCompletionBwd_comp_fwd
    (π : washnitzerAlgebra σ K →ₐ[K] A) (hπ : Function.Surjective π) :
    (presentationCompletionBwd π).comp (presentationCompletionFwd π hπ) =
      AlgHom.id K (completion K A) :=
  completion_algHom_ext fun a ↦ by
    obtain ⟨f, rfl⟩ := hπ a
    simp [presentationCompletionFwd, presentationCompletionBwd]

private theorem presentationCompletionFwd_comp_bwd
    (π : washnitzerAlgebra σ K →ₐ[K] A) (hπ : Function.Surjective π) :
    (presentationCompletionFwd π hπ).comp (presentationCompletionBwd π) = AlgHom.id K _ :=
  washnitzerAlgebra.tateQuotient_algHom_ext_of_isAffinoidAlgebra
    (isAffinoidAlgebra_tate.quotient _) fun f ↦ by
      simp [presentationCompletionFwd, presentationCompletionBwd]

/-- **Presentation independence of the completion.** For any surjective presentation
`π : W_σ →ₐ[K] A` of a dagger algebra, `completion K A` is canonically topologically isomorphic as
a `K`-algebra to `T_σ ⧸ (ker π) T_σ` under `A`. -/
noncomputable def daggerPresentationCompletionContinuousAlgEquiv
    (π : washnitzerAlgebra σ K →ₐ[K] A) (hπ : Function.Surjective π) :
    completion K A ≃A[K] T σ ⧸ (RingHom.ker π).map (washnitzerAlgebra.toTate σ K) :=
  IsAffinoidAlgebra.toContinuousAlgEquiv (K := K) (A := completion K A)
    (B := T σ ⧸ (RingHom.ker π).map (washnitzerAlgebra.toTate σ K))
    (isAffinoidAlgebra_tate.quotient _)
    (AlgEquiv.ofAlgHom (presentationCompletionFwd π hπ) (presentationCompletionBwd π)
      (presentationCompletionFwd_comp_bwd π hπ) (presentationCompletionBwd_comp_fwd π hπ))

/-- `π.daggerPresentationCompletionContinuousAlgEquiv hπ` sends `toCompletion K A (π f)` to the
class of `toTate σ K f`. -/
@[simp]
theorem daggerPresentationCompletionContinuousAlgEquiv_toCompletion
    (π : washnitzerAlgebra σ K →ₐ[K] A) (hπ : Function.Surjective π)
    (f : washnitzerAlgebra σ K) :
    π.daggerPresentationCompletionContinuousAlgEquiv hπ (toCompletion K A (π f)) =
      Ideal.Quotient.mk _ (washnitzerAlgebra.toTate σ K f) := by
  rw [daggerPresentationCompletionContinuousAlgEquiv, IsAffinoidAlgebra.coe_toContinuousAlgEquiv,
    AlgEquiv.ofAlgHom_apply]
  exact (completionLift_toCompletion _ _ (π f)).trans (toPresentationCompletion_apply π hπ f)

/-- The inverse of `π.daggerPresentationCompletionContinuousAlgEquiv hπ` sends the class of
`toTate σ K f` to `toCompletion K A (π f)`. -/
@[simp]
theorem daggerPresentationCompletionContinuousAlgEquiv_symm_mk_toTate
    (π : washnitzerAlgebra σ K →ₐ[K] A) (hπ : Function.Surjective π)
    (f : washnitzerAlgebra σ K) :
    (π.daggerPresentationCompletionContinuousAlgEquiv hπ).symm
      (Ideal.Quotient.mk _ (washnitzerAlgebra.toTate σ K f)) =
      toCompletion K A (π f) :=
  (π.daggerPresentationCompletionContinuousAlgEquiv hπ).symm_apply_eq.mpr
    (π.daggerPresentationCompletionContinuousAlgEquiv_toCompletion hπ f).symm

end PresentationComparison

end AlgHom

namespace TauCeti.Dagger

open _root_.MvPowerSeries

namespace washnitzerAlgebra

variable {σ K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]

local notation "T" => IsRestricted.subring (R := K) (fun _ : σ ↦ (1 : ℝ))

private theorem ker_id_map_toTate_eq_bot :
    (RingHom.ker (AlgHom.id K (washnitzerAlgebra σ K))).map (toTate σ K) = ⊥ := by
  rw [eq_bot_iff, Ideal.map_le_iff_le_comap]
  intro f hf
  rw [RingHom.mem_ker, AlgHom.id_apply] at hf
  simp [hf]

variable [CompleteSpace K] [Finite σ]

variable (σ K) in
/-- **The completion of the Monsky–Washnitzer algebra is the Tate algebra.** The completion
`completion K (washnitzerAlgebra σ K)` is canonically topologically isomorphic as a `K`-algebra to
`T_σ = K⟨X⟩`, compatibly with `toCompletion` and `toTate`. -/
noncomputable def completionContinuousAlgEquiv :
    completion K (washnitzerAlgebra σ K) ≃A[K] T :=
  ((AlgHom.id K (washnitzerAlgebra σ K)).daggerPresentationCompletionContinuousAlgEquiv
    Function.surjective_id).trans <|
    IsAffinoidAlgebra.toContinuousAlgEquiv (K := K)
      (A := T ⧸ (RingHom.ker (AlgHom.id K (washnitzerAlgebra σ K))).map (toTate σ K))
      (B := T) isAffinoidAlgebra_tate <|
      (Ideal.quotientEquivAlgOfEq K ker_id_map_toTate_eq_bot).trans (AlgEquiv.quotientBot K T)

/-- The completion comparison on `W_σ` intertwines `toCompletion` with `toTate`. -/
@[simp]
theorem completionContinuousAlgEquiv_toCompletion (f : washnitzerAlgebra σ K) :
    completionContinuousAlgEquiv σ K (toCompletion K (washnitzerAlgebra σ K) f) =
      toTate σ K f := by
  have hf := AlgHom.daggerPresentationCompletionContinuousAlgEquiv_toCompletion
    (AlgHom.id K (washnitzerAlgebra σ K)) Function.surjective_id f
  rw [AlgHom.id_apply] at hf
  rw [completionContinuousAlgEquiv, ContinuousAlgEquiv.trans_apply, hf,
    IsAffinoidAlgebra.coe_toContinuousAlgEquiv, AlgEquiv.trans_apply,
    Ideal.quotientEquivAlgOfEq_mk, AlgEquiv.quotientBot_mk]

/-- The inverse completion comparison on `W_σ` sends `toTate σ K f` to `toCompletion K W_σ f`. -/
@[simp]
theorem completionContinuousAlgEquiv_symm_toTate (f : washnitzerAlgebra σ K) :
    (completionContinuousAlgEquiv σ K).symm (toTate σ K f) =
      toCompletion K (washnitzerAlgebra σ K) f :=
  (completionContinuousAlgEquiv σ K).symm_apply_eq.mpr
    (completionContinuousAlgEquiv_toCompletion f).symm

/-- On coordinate variables, `completionContinuousAlgEquiv` sends `toCompletion (Xᵢ)` to `Xᵢ`. -/
theorem completionContinuousAlgEquiv_X (i : σ) :
    completionContinuousAlgEquiv σ K (toCompletion K (washnitzerAlgebra σ K) (X σ K i)) =
      ⟨_root_.MvPowerSeries.X i, isRestricted_X _ i⟩ := by
  simp

end washnitzerAlgebra

section SupSeminorm

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A : Type*} [CommRing A] [Algebra K A] [IsDaggerAlgebra K A]

/-- **The completion map preserves the supremum seminorm**, since contraction along `toCompletion`
is a bijection of classical points preserving residue fields. -/
@[simp]
theorem supSeminorm_toCompletion (a : A) :
    supSeminorm K (toCompletion K A a) = supSeminorm K a := by
  rw [supSeminorm_eq_iSup, supSeminorm_eq_iSup]
  simp_rw [← (isAffinoidAlgebra_completion (K := K) (A := A)).pointNorm_maximalSpectrumComap
    (toCompletion K A)]
  exact (maximalSpectrumComap_toCompletion_bijective (K := K) (A := A)).surjective.iSup_comp
    (pointNorm K · a)

namespace IsDaggerAlgebra

/-- **The kernel of the supremum seminorm on a dagger algebra is the nilradical**: `|a|sup = 0`
if and only if `a` is nilpotent, since `toCompletion` is injective and preserves `supSeminorm`. -/
theorem supSeminorm_eq_zero_iff {a : A} : supSeminorm K a = 0 ↔ IsNilpotent a := by
  rw [← supSeminorm_toCompletion (K := K) (A := A),
    (isAffinoidAlgebra_completion (K := K) (A := A)).supSeminorm_eq_zero_iff]
  exact ⟨fun ⟨n, hn⟩ ↦ ⟨n, toCompletion_injective (K := K) (A := A)
    (by rw [map_pow, hn, map_zero])⟩, fun ha ↦ ha.map (toCompletion K A)⟩

/-- **The supremum seminorm is a norm precisely on reduced dagger algebras**, in every
characteristic. -/
theorem isReduced_iff_supSeminorm_eq_zero :
    IsReduced A ↔ ∀ a : A, supSeminorm K a = 0 → a = 0 := by
  simp_rw [supSeminorm_eq_zero_iff, isReduced_iff]

end IsDaggerAlgebra

end SupSeminorm

end TauCeti.Dagger

namespace AlgHom

open TauCeti TauCeti.Dagger

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A B : Type*} [CommRing A] [Algebra K A] [IsDaggerAlgebra K A]
  [CommRing B] [Algebra K B] [IsDaggerAlgebra K B]

/-- **Morphisms of dagger algebras contract the supremum seminorm**: `|φ a|sup ≤ |a|sup`. -/
theorem supSeminorm_map_le_of_isDaggerAlgebra (φ : A →ₐ[K] B) (a : A) :
    supSeminorm K (φ a) ≤ supSeminorm K a := by
  rw [← supSeminorm_toCompletion (K := K) (A := B), ← φ.daggerCompletionMap_toCompletion,
    ← supSeminorm_toCompletion (K := K) (A := A)]
  exact (isAffinoidAlgebra_completion (K := K) (A := A)).supSeminorm_map_le
    (isAffinoidAlgebra_completion (K := K) (A := B)) φ.daggerCompletionMap _

end AlgHom

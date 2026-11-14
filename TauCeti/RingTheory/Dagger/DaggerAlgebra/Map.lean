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
(`TauCeti.Dagger.completionMap`) sending `K`-algebra isomorphisms to topological `K`-algebra
isomorphisms (`TauCeti.Dagger.completionContinuousAlgEquivOfAlgEquiv`). Applying the universal
property in both directions identifies `Â` with `T_σ ⧸ (ker π) T_σ` for every presentation
`π : W_σ ↠ A` (`TauCeti.Dagger.presentationCompletionContinuousAlgEquiv`), and in particular
identifies the completion of `W_σ` with `T_σ`
(`TauCeti.Dagger.washnitzerAlgebra.completionContinuousAlgEquiv`).

## Main definitions

* `TauCeti.Dagger.completionLift`, `TauCeti.Dagger.completionLiftEquiv`: the universal extension
  `(completion K A →ₐ[K] S) ≃ (A →ₐ[K] S)` for an affinoid algebra `S`.
* `TauCeti.Dagger.completionMap`: the completion `completion K A →ₐ[K] completion K B` of a
  morphism `A →ₐ[K] B` of dagger algebras, together with
  `TauCeti.Dagger.completionAlgEquivOfAlgEquiv` and
  `TauCeti.Dagger.completionContinuousAlgEquivOfAlgEquiv`: the induced algebraic and topological
  isomorphisms for `A ≃ₐ[K] B`.
* `TauCeti.Dagger.presentationCompletionContinuousAlgEquiv`: comparison of `completion K A` with
  `T_σ ⧸ (ker π) T_σ` for an arbitrary presentation `π : W_σ ↠ A`.
* `TauCeti.Dagger.washnitzerAlgebra.completionContinuousAlgEquiv`: the topological `K`-algebra
  isomorphism `completion K (washnitzerAlgebra σ K) ≃A[K] T_σ`.

## Main results

* `TauCeti.Dagger.washnitzerAlgebra.algHom_ext_of_isDaggerAlgebra`: `K`-algebra maps out of `W_σ`
  into a dagger algebra are determined by the coordinate variables.
* `TauCeti.Dagger.completion_algHom_ext_of_isAffinoidAlgebra` and
  `TauCeti.Dagger.existsUnique_algHom_completion`: every `K`-algebra map `A →ₐ[K] S` into an
  affinoid algebra factors uniquely through `toCompletion K A`.
* `TauCeti.Dagger.completion_algHom_ext`, `TauCeti.Dagger.completionMap_unique`,
  `TauCeti.Dagger.completionMap_id`, `TauCeti.Dagger.completionMap_comp`,
  `TauCeti.Dagger.continuous_completionMap`: uniqueness, functoriality, and continuity of
  `completionMap`.
* `TauCeti.Dagger.supSeminorm_toCompletion`, `TauCeti.Dagger.IsDaggerAlgebra.supSeminorm_map_le`,
  `TauCeti.Dagger.IsDaggerAlgebra.supSeminorm_algEquiv`,
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

section AlgHomExt

namespace washnitzerAlgebra

variable {K σ : Type*} [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [Finite σ]

/-- **`K`-algebra homomorphisms from `W_σ` into a dagger algebra are determined by the
variables**, with no continuity assumed. -/
theorem algHom_ext_of_isDaggerAlgebra {R : Type*} [CommRing R] [Algebra K R]
    [IsDaggerAlgebra K R] {φ ψ : washnitzerAlgebra σ K →ₐ[K] R}
    (h : ∀ i, φ (X σ K i) = ψ (X σ K i)) : φ = ψ := by
  have := IsDaggerAlgebra.isNoetherianRing (K := K) (A := R)
  refine algHom_ext_of_isNoetherianRing (fun m hm k ↦ ?_) h
  have : m.radical.IsMaximal := (Ideal.IsMaximal.isPrime hm).radical.symm ▸ hm
  exact IsDaggerAlgebra.finite_quotient_pow_of_isMaximal_radical K m k

end washnitzerAlgebra

end AlgHomExt

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

section Functoriality

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A B C : Type*} [CommRing A] [Algebra K A] [IsDaggerAlgebra K A]
  [CommRing B] [Algebra K B] [IsDaggerAlgebra K B]
  [CommRing C] [Algebra K C] [IsDaggerAlgebra K C]

/-- Two `K`-algebra homomorphisms between completions of dagger algebras that agree on `A` are
equal. -/
theorem completion_algHom_ext {Φ₁ Φ₂ : completion K A →ₐ[K] completion K B}
    (h : ∀ a, Φ₁ (toCompletion K A a) = Φ₂ (toCompletion K A a)) : Φ₁ = Φ₂ :=
  completion_algHom_ext_of_isAffinoidAlgebra isAffinoidAlgebra_completion h

/-- **Functoriality of dagger completion.** Every `K`-algebra homomorphism `φ : A →ₐ[K] B` of
dagger algebras extends uniquely to a `K`-algebra homomorphism
`φ̂ : completion K A →ₐ[K] completion K B` compatible with `toCompletion`. -/
noncomputable def completionMap (φ : A →ₐ[K] B) : completion K A →ₐ[K] completion K B :=
  completionLift isAffinoidAlgebra_completion ((toCompletion K B).comp φ)

/-- `completionMap φ` commutes with `toCompletion` on elements. -/
@[simp]
theorem completionMap_toCompletion (φ : A →ₐ[K] B) (a : A) :
    completionMap φ (toCompletion K A a) = toCompletion K B (φ a) :=
  completionLift_toCompletion isAffinoidAlgebra_completion _ a

/-- `completionMap φ` intertwines the completion maps. -/
@[simp]
theorem completionMap_comp_toCompletion (φ : A →ₐ[K] B) :
    (completionMap φ).comp (toCompletion K A) = (toCompletion K B).comp φ :=
  completionLift_comp_toCompletion isAffinoidAlgebra_completion _

/-- `completionMap φ` is the unique `K`-algebra homomorphism `Â →ₐ[K] B̂` intertwining `φ` with
`toCompletion`. -/
theorem completionMap_unique {φ : A →ₐ[K] B} {Φ : completion K A →ₐ[K] completion K B}
    (h : Φ.comp (toCompletion K A) = (toCompletion K B).comp φ) : Φ = completionMap φ :=
  completion_algHom_ext fun a ↦ by
    rw [← AlgHom.comp_apply, h, AlgHom.comp_apply, completionMap_toCompletion]

/-- The induced map between completions is continuous for their quotient Gauss norms. -/
theorem continuous_completionMap (φ : A →ₐ[K] B) : Continuous (completionMap φ) :=
  have := (isAffinoidAlgebra_completion (K := K) (A := A)).isNoetherianRing
  IsAffinoidAlgebra.continuous_algHom (K := K) (A := completion K B) (B := completion K A)
    isAffinoidAlgebra_completion (completionMap φ)

/-- `completionMap` sends the identity homomorphism to the identity homomorphism. -/
@[simp]
theorem completionMap_id :
    completionMap (AlgHom.id K A) = AlgHom.id K (completion K A) :=
  completion_algHom_ext fun a ↦ by simp

/-- `completionMap` respects composition of `K`-algebra homomorphisms. -/
@[simp]
theorem completionMap_comp (ψ : B →ₐ[K] C) (φ : A →ₐ[K] B) :
    completionMap (ψ.comp φ) = (completionMap ψ).comp (completionMap φ) :=
  completion_algHom_ext fun a ↦ by simp

/-- A `K`-algebra isomorphism of dagger algebras induces a `K`-algebra isomorphism of their
completions. -/
noncomputable def completionAlgEquivOfAlgEquiv (e : A ≃ₐ[K] B) :
    completion K A ≃ₐ[K] completion K B :=
  AlgEquiv.ofAlgHom (completionMap e.toAlgHom) (completionMap e.symm.toAlgHom)
    (completion_algHom_ext fun b ↦ by simp)
    (completion_algHom_ext fun a ↦ by simp)

/-- The underlying `AlgHom` of `completionAlgEquivOfAlgEquiv e` is `completionMap e.toAlgHom`. -/
@[simp]
theorem toAlgHom_completionAlgEquivOfAlgEquiv (e : A ≃ₐ[K] B) :
    (completionAlgEquivOfAlgEquiv e).toAlgHom = completionMap e.toAlgHom := (rfl)

/-- Applying `completionAlgEquivOfAlgEquiv e` evaluates `completionMap e.toAlgHom`. -/
@[simp]
theorem completionAlgEquivOfAlgEquiv_apply (e : A ≃ₐ[K] B) (x : completion K A) :
    completionAlgEquivOfAlgEquiv e x = completionMap e.toAlgHom x := (rfl)

/-- `completionAlgEquivOfAlgEquiv` commutes with `.symm`. -/
@[simp]
theorem completionAlgEquivOfAlgEquiv_symm (e : A ≃ₐ[K] B) :
    (completionAlgEquivOfAlgEquiv e).symm = completionAlgEquivOfAlgEquiv e.symm := (rfl)

/-- A `K`-algebra isomorphism of dagger algebras induces a topological `K`-algebra isomorphism of
their completions. -/
noncomputable def completionContinuousAlgEquivOfAlgEquiv (e : A ≃ₐ[K] B) :
    completion K A ≃A[K] completion K B :=
  IsAffinoidAlgebra.toContinuousAlgEquiv (K := K) (A := completion K A) (B := completion K B)
    isAffinoidAlgebra_completion (completionAlgEquivOfAlgEquiv e)

/-- The underlying `AlgEquiv` of `completionContinuousAlgEquivOfAlgEquiv e` is
`completionAlgEquivOfAlgEquiv e`. -/
@[simp]
theorem toAlgEquiv_completionContinuousAlgEquivOfAlgEquiv (e : A ≃ₐ[K] B) :
    (completionContinuousAlgEquivOfAlgEquiv e).toAlgEquiv = completionAlgEquivOfAlgEquiv e := by
  simp [completionContinuousAlgEquivOfAlgEquiv]

/-- Applying `completionContinuousAlgEquivOfAlgEquiv e` evaluates `completionMap e.toAlgHom`. -/
@[simp]
theorem completionContinuousAlgEquivOfAlgEquiv_apply (e : A ≃ₐ[K] B) (x : completion K A) :
    completionContinuousAlgEquivOfAlgEquiv e x = completionMap e.toAlgHom x := by
  simp [completionContinuousAlgEquivOfAlgEquiv]

/-- `completionContinuousAlgEquivOfAlgEquiv e` commutes with `toCompletion`. -/
theorem completionContinuousAlgEquivOfAlgEquiv_toCompletion (e : A ≃ₐ[K] B) (a : A) :
    completionContinuousAlgEquivOfAlgEquiv e (toCompletion K A a) = toCompletion K B (e a) := by
  simp

/-- `completionContinuousAlgEquivOfAlgEquiv` commutes with `.symm`. -/
@[simp]
theorem completionContinuousAlgEquivOfAlgEquiv_symm (e : A ≃ₐ[K] B) :
    (completionContinuousAlgEquivOfAlgEquiv e).symm =
      completionContinuousAlgEquivOfAlgEquiv e.symm := by
  ext x
  refine (completionContinuousAlgEquivOfAlgEquiv e).symm_apply_eq.mpr ?_
  have h : completionMap e.toAlgHom (completionMap e.symm.toAlgHom x) = x := by
    simp [← AlgHom.comp_apply, ← completionMap_comp]
  simpa using h.symm

/-- `completionContinuousAlgEquivOfAlgEquiv` sends `AlgEquiv.refl` to `ContinuousAlgEquiv.refl`. -/
@[simp]
theorem completionContinuousAlgEquivOfAlgEquiv_refl :
    completionContinuousAlgEquivOfAlgEquiv (AlgEquiv.refl : A ≃ₐ[K] A) =
      ContinuousAlgEquiv.refl K (completion K A) := by
  ext x
  simp

/-- `completionContinuousAlgEquivOfAlgEquiv` respects composition of `K`-algebra isomorphisms. -/
@[simp]
theorem completionContinuousAlgEquivOfAlgEquiv_trans (e₁ : A ≃ₐ[K] B) (e₂ : B ≃ₐ[K] C) :
    completionContinuousAlgEquivOfAlgEquiv (e₁.trans e₂) =
      (completionContinuousAlgEquivOfAlgEquiv e₁).trans
        (completionContinuousAlgEquivOfAlgEquiv e₂) := by
  ext x
  have h : (e₁.trans e₂).toAlgHom = e₂.toAlgHom.comp e₁.toAlgHom := rfl
  simp [h]

end Functoriality

section PresentationComparison

section ArbitraryPresentation

variable {K σ : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  [Finite σ] {A : Type*} [CommRing A] [Algebra K A] [IsDaggerAlgebra K A]

local notation "T " α:max => IsRestricted.subring (R := K) (fun _ : α ↦ (1 : ℝ))

/-- The canonical `K`-algebra map `A → T_σ ⧸ (ker π) T_σ` attached to an arbitrary surjective
presentation `π : W_σ ↠ A`. -/
private noncomputable def toPresentationCompletion (π : washnitzerAlgebra σ K →ₐ[K] A)
    (hπ : Function.Surjective π) :
    A →ₐ[K] T σ ⧸ (RingHom.ker π).map (washnitzerAlgebra.toTate σ K) :=
  (Ideal.quotientMapₐ _ (washnitzerAlgebra.toTate σ K) Ideal.le_comap_map).comp
    (Ideal.quotientKerAlgEquivOfSurjective hπ).symm.toAlgHom

omit [CompleteSpace K] [Finite σ] [IsDaggerAlgebra K A] in
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
noncomputable def presentationCompletionContinuousAlgEquiv
    (π : washnitzerAlgebra σ K →ₐ[K] A) (hπ : Function.Surjective π) :
    completion K A ≃A[K] T σ ⧸ (RingHom.ker π).map (washnitzerAlgebra.toTate σ K) :=
  IsAffinoidAlgebra.toContinuousAlgEquiv (K := K) (A := completion K A)
    (B := T σ ⧸ (RingHom.ker π).map (washnitzerAlgebra.toTate σ K))
    (isAffinoidAlgebra_tate.quotient _)
    (AlgEquiv.ofAlgHom (presentationCompletionFwd π hπ) (presentationCompletionBwd π)
      (presentationCompletionFwd_comp_bwd π hπ) (presentationCompletionBwd_comp_fwd π hπ))

/-- `presentationCompletionContinuousAlgEquiv` sends `toCompletion K A (π f)` to the class of
`toTate σ K f`. -/
@[simp]
theorem presentationCompletionContinuousAlgEquiv_toCompletion
    (π : washnitzerAlgebra σ K →ₐ[K] A) (hπ : Function.Surjective π)
    (f : washnitzerAlgebra σ K) :
    presentationCompletionContinuousAlgEquiv π hπ (toCompletion K A (π f)) =
      Ideal.Quotient.mk _ (washnitzerAlgebra.toTate σ K f) := by
  change (IsAffinoidAlgebra.toContinuousAlgEquiv _ _) (toCompletion K A (π f)) = _
  rw [IsAffinoidAlgebra.coe_toContinuousAlgEquiv, AlgEquiv.ofAlgHom_apply]
  exact (completionLift_toCompletion _ _ (π f)).trans (toPresentationCompletion_apply π hπ f)

/-- The inverse of `presentationCompletionContinuousAlgEquiv` sends the class of `toTate σ K f` to
`toCompletion K A (π f)`. -/
@[simp]
theorem presentationCompletionContinuousAlgEquiv_symm_mk_toTate
    (π : washnitzerAlgebra σ K →ₐ[K] A) (hπ : Function.Surjective π)
    (f : washnitzerAlgebra σ K) :
    (presentationCompletionContinuousAlgEquiv π hπ).symm
      (Ideal.Quotient.mk _ (washnitzerAlgebra.toTate σ K f)) =
      toCompletion K A (π f) :=
  (presentationCompletionContinuousAlgEquiv π hπ).symm_apply_eq.mpr
    (presentationCompletionContinuousAlgEquiv_toCompletion π hπ f).symm

end ArbitraryPresentation

namespace washnitzerAlgebra

variable {σ K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  [Finite σ]

local notation "T" => IsRestricted.subring (R := K) (fun _ : σ ↦ (1 : ℝ))

section Helpers

variable (σ K)

/-- The forward map `completion K (washnitzerAlgebra σ K) →ₐ[K] T_σ` induced by `completionLift`. -/
private noncomputable def completionFwd :
    completion K (washnitzerAlgebra σ K) →ₐ[K] T :=
  completionLift isAffinoidAlgebra_tate (toTate σ K)

/-- The backward map `T_σ →ₐ[K] completion K (washnitzerAlgebra σ K)` induced by `liftToTate`. -/
private noncomputable def completionBwd :
    T →ₐ[K] completion K (washnitzerAlgebra σ K) :=
  liftToTate isAffinoidAlgebra_completion (toCompletion K (washnitzerAlgebra σ K))

private theorem completionBwd_comp_fwd :
    (completionBwd σ K).comp (completionFwd σ K) = AlgHom.id K _ :=
  completion_algHom_ext fun f ↦ by simp [completionFwd, completionBwd]

private theorem completionFwd_comp_bwd :
    (completionFwd σ K).comp (completionBwd σ K) = AlgHom.id K _ :=
  tate_algHom_ext_of_isAffinoidAlgebra isAffinoidAlgebra_tate fun f ↦ by
    simp [completionFwd, completionBwd]

end Helpers

variable (σ K) in
/-- **The completion of the Monsky–Washnitzer algebra is the Tate algebra.** The completion
`completion K (washnitzerAlgebra σ K)` is canonically topologically isomorphic as a `K`-algebra to
`T_σ = K⟨X⟩`, compatibly with `toCompletion` and `toTate`. -/
noncomputable def completionContinuousAlgEquiv :
    completion K (washnitzerAlgebra σ K) ≃A[K] T :=
  IsAffinoidAlgebra.toContinuousAlgEquiv (K := K)
    (A := completion K (washnitzerAlgebra σ K)) (B := T) isAffinoidAlgebra_tate
    (AlgEquiv.ofAlgHom (completionFwd σ K) (completionBwd σ K)
      (completionFwd_comp_bwd σ K) (completionBwd_comp_fwd σ K))

/-- The completion comparison on `W_σ` intertwines `toCompletion` with `toTate`. -/
@[simp]
theorem completionContinuousAlgEquiv_toCompletion (f : washnitzerAlgebra σ K) :
    completionContinuousAlgEquiv σ K (toCompletion K (washnitzerAlgebra σ K) f) =
      toTate σ K f := by
  change (IsAffinoidAlgebra.toContinuousAlgEquiv _ _) _ = _
  rw [IsAffinoidAlgebra.coe_toContinuousAlgEquiv, AlgEquiv.ofAlgHom_apply]
  exact completionLift_toCompletion isAffinoidAlgebra_tate (toTate σ K) f

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

end PresentationComparison

section SupSeminorm

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A B : Type*} [CommRing A] [Algebra K A] [IsDaggerAlgebra K A]
  [CommRing B] [Algebra K B] [IsDaggerAlgebra K B]

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

/-- **Morphisms of dagger algebras contract the supremum seminorm**: `|φ a|sup ≤ |a|sup`. -/
theorem supSeminorm_map_le (φ : A →ₐ[K] B) (a : A) :
    supSeminorm K (φ a) ≤ supSeminorm K a := by
  rw [← supSeminorm_toCompletion (K := K) (A := B), ← completionMap_toCompletion,
    ← supSeminorm_toCompletion (K := K) (A := A)]
  exact (isAffinoidAlgebra_completion (K := K) (A := A)).supSeminorm_map_le
    (isAffinoidAlgebra_completion (K := K) (A := B)) (completionMap φ) _

/-- Algebra isomorphisms of dagger algebras preserve the supremum seminorm. -/
@[simp]
theorem supSeminorm_algEquiv (e : A ≃ₐ[K] B) (a : A) :
    supSeminorm K (e a) = supSeminorm K a :=
  le_antisymm (supSeminorm_map_le e.toAlgHom a)
    (by simpa using supSeminorm_map_le e.symm.toAlgHom (e a))

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

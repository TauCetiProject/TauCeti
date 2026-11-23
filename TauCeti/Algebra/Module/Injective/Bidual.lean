/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.Algebra.Module.Injective
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.LinearAlgebra.LeftExact
public import Mathlib.RingTheory.Finiteness.Cardinality
public import TauCeti.Algebra.Module.Injective.Hom
public import TauCeti.LinearAlgebra.Dual.Lemmas

/-!
# Evaluation into a double Hom

For an injective module `E`, surjectivity of the evaluation map into the double `E`-dual
passes to quotients. If every endomorphism of `E` is scalar, evaluation is surjective for
finite free modules, and hence for every finitely generated module. Together with a
cogenerator condition, this gives biduality without requiring the original module to be
projective. The principal application is Matlis duality over a complete local ring.

Injectivity of evaluation also descends along a presentation: if `N → P → M → 0` is exact,
evaluation is surjective for `N` and injective for `P`, then it is injective for `M`. For a
self-injective ring `R`, taking `E = R` and a finite free presentation shows that every finitely
presented `R`-module is reflexive, although it need not be projective: `ℤ/2` over `ℤ/4` is an
example. Over a Noetherian self-injective ring this applies to every finitely generated module.
This is the biduality on which duality with finite self-injective coefficients such as `ℤ/ℓⁿ`
rests.

The argument uses Mathlib's `LinearEquiv.piRing` to identify the dual of a finite free
module, and `Module.Injective.extension_property` to dualize an injection.

## Main results

* `TauCeti.surjective_applyₗ_of_finite_of_end_eq_smul`: evaluation into the double `E`-dual of a
  finitely generated module is surjective when `E` is injective with only scalar endomorphisms.
* `Function.Exact.injective_applyₗ`: injectivity of evaluation descends along a presentation.
* `Module.IsReflexive.of_injective_of_finitePresentation`: over a self-injective ring every
  finitely presented module is reflexive.
* `Module.IsReflexive.of_injective_of_finite`: over a Noetherian self-injective ring every finitely
  generated module is reflexive.

## References

* The Stacks Project, Proposition 47.7.8, Matlis duality, Tag 08Z9.
* [SGA 4, Exposé XVIII], 3.2.6, for biduality of finite modules over a self-injective coefficient
  ring.
-/

public section

noncomputable section

universe u v w z

namespace LinearMap

variable {R : Type u} [CommRing R] {E : Type v} [AddCommGroup E] [Module R E]
  {M : Type w} [AddCommGroup M] [Module R M]
  {N : Type z} [AddCommGroup N] [Module R N]

/-- Surjectivity of evaluation into the double dual with injective coefficients passes to
quotients. -/
theorem surjective_applyₗ_of_surjective [Small.{v} R] [Module.Injective R E]
    (f : M →ₗ[R] N) (hf : Function.Surjective f)
    (hM : Function.Surjective (applyₗ : M →ₗ[R] (M →ₗ[R] E) →ₗ[R] E)) :
    Function.Surjective (applyₗ : N →ₗ[R] (N →ₗ[R] E) →ₗ[R] E) := by
  intro φ
  obtain ⟨ψ, hψ⟩ := Module.Injective.extension_property R E _ _ (f.lcomp R E)
    (lcomp_injective_of_surjective f hf) φ
  obtain ⟨m, hm⟩ := hM ψ
  refine ⟨f m, LinearMap.ext fun g ↦ ?_⟩
  have h := LinearMap.congr_fun hψ g
  simpa [← hm] using h

end LinearMap

namespace Function.Exact

open LinearMap

variable {R : Type u} [CommRing R] {E : Type v} [AddCommGroup E] [Module R E]
  {N P M : Type*} [AddCommGroup N] [Module R N] [AddCommGroup P] [Module R P]
  [AddCommGroup M] [Module R M]

/-- Injectivity of evaluation into the double `E`-dual descends along a presentation: for
`E` injective and an exact sequence `N → P → M → 0`, if evaluation is surjective for `N` and
injective for `P`, then it is injective for `M`. -/
theorem injective_applyₗ [Small.{v} R] [Module.Injective R E]
    {f : N →ₗ[R] P} {g : P →ₗ[R] M} (hfg : Function.Exact f g) (hg : Function.Surjective g)
    (hN : Function.Surjective (applyₗ : N →ₗ[R] (N →ₗ[R] E) →ₗ[R] E))
    (hP : Function.Injective (applyₗ : P →ₗ[R] (P →ₗ[R] E) →ₗ[R] E)) :
    Function.Injective (applyₗ : M →ₗ[R] (M →ₗ[R] E) →ₗ[R] E) := by
  refine (injective_iff_map_eq_zero _).2 fun m hm ↦ ?_
  obtain ⟨p, rfl⟩ := hg m
  -- a functional on `P` killing the image of `f` factors through `g`, so it kills `p`
  have hle : ker (f.lcomp R E) ≤ ker (applyₗ p : (P →ₗ[R] E) →ₗ[R] E) := fun ψ hψ ↦ by
    obtain ⟨χ, rfl⟩ := (exact_lcomp_of_exact_of_surjective E hfg hg ψ).1 hψ
    simpa using LinearMap.congr_fun hm χ
  -- so `ψ ∘ f ↦ ψ p` extends to a functional on `N →ₗ[R] E`
  obtain ⟨Ψ, hΨ⟩ := (exists_comp_eq_iff_ker_le (f.lcomp R E) (applyₗ p)).2 hle
  -- which is evaluation at some `n`, so `p` and `f n` agree on every functional
  obtain ⟨n, rfl⟩ := hN Ψ
  have hpn : p = f n := hP <| LinearMap.ext fun ψ ↦ by
    simpa using (LinearMap.congr_fun hΨ ψ).symm
  rw [hpn, hfg.apply_apply_eq_zero]

end Function.Exact

namespace TauCeti

open LinearMap

section Semiring

variable {R : Type u} [CommSemiring R] {E : Type v} [AddCommMonoid E] [Module R E]

/-- If every endomorphism of `E` is scalar, evaluation into the double `E`-dual of a finite
free module is surjective. -/
theorem surjective_applyₗ_pi_of_end_eq_smul
    (hE : ∀ f : Module.End R E, ∃ r : R, f = r • LinearMap.id)
    (ι : Type*) [Finite ι] :
    Function.Surjective (applyₗ : (ι → R) →ₗ[R] ((ι → R) →ₗ[R] E) →ₗ[R] E) := by
  classical
  let := Fintype.ofFinite ι
  intro φ
  let e := LinearEquiv.piRing R E ι R
  let ψ := φ.comp e.symm.toLinearMap
  choose r hr using fun i ↦ hE (ψ.comp (LinearMap.single R (fun _ : ι ↦ E) i))
  refine ⟨r, LinearMap.ext fun f ↦ ?_⟩
  have hψ : ψ (e f) = ∑ i, r i • e f i := by
    conv_lhs => rw [← Finset.univ_sum_single (e f), map_sum]
    exact Finset.sum_congr rfl fun i _ ↦ LinearMap.congr_fun (hr i) (e f i)
  have hf : f r = ∑ i, r i • e f i := by
    simpa only [e, LinearEquiv.piRing_symm_apply] using
      congrArg (fun g : (ι → R) →ₗ[R] E ↦ g r) (e.symm_apply_apply f).symm
  simpa only [LinearMap.applyₗ_apply_apply] using
    hf.trans (by simpa [ψ] using hψ.symm)

end Semiring

variable {R : Type u} [CommRing R] {E : Type v} [AddCommGroup E] [Module R E]

/-- If `E` is injective and every endomorphism of `E` is scalar, every finitely generated
module maps surjectively onto its double `E`-dual by evaluation. -/
theorem surjective_applyₗ_of_finite_of_end_eq_smul [Small.{v} R] [Module.Injective R E]
    (hE : ∀ f : Module.End R E, ∃ r : R, f = r • LinearMap.id)
    (M : Type w) [AddCommGroup M] [Module R M] [Module.Finite R M] :
    Function.Surjective (applyₗ : M →ₗ[R] (M →ₗ[R] E) →ₗ[R] E) := by
  obtain ⟨n, f, hf⟩ := Module.Finite.exists_fin' R M
  exact f.surjective_applyₗ_of_surjective hf (surjective_applyₗ_pi_of_end_eq_smul hE (Fin n))

end TauCeti

namespace Module

open LinearMap

variable (R : Type u) [CommRing R]

/-- **Biduality over a self-injective ring**: every finitely presented module over a
self-injective commutative ring is reflexive. Projectivity is not needed. Over a Noetherian ring
every finitely generated module is finitely presented, see `IsReflexive.of_injective_of_finite`. -/
instance (priority := 900) IsReflexive.of_injective_of_finitePresentation [Module.Injective R R]
    (M : Type*) [AddCommGroup M] [Module R M] [Module.FinitePresentation R M] :
    IsReflexive R M := by
  have hR (f : Module.End R R) : ∃ r : R, f = r • LinearMap.id :=
    ⟨f 1, LinearMap.ext_ring (by simp)⟩
  obtain ⟨n, m, g, f, hg, hfg⟩ := FinitePresentation.exists_fin' R M
  refine ⟨⟨?_, ?_⟩⟩
  · rw [Dual.eval_eq_applyₗ]
    exact hfg.injective_applyₗ hg (TauCeti.surjective_applyₗ_pi_of_end_eq_smul hR _)
      (by simpa only [Dual.eval_eq_applyₗ] using eval_apply_injective R (V := Fin n → R))
  · rw [Dual.eval_eq_applyₗ]
    exact TauCeti.surjective_applyₗ_of_finite_of_end_eq_smul hR M

/-- **Biduality over a Noetherian self-injective ring**: every finitely generated module is
reflexive, so evaluation into its double dual is bijective (`Module.bijective_dual_eval`). -/
instance (priority := 900) IsReflexive.of_injective_of_finite [IsNoetherianRing R]
    [Module.Injective R R] (M : Type*) [AddCommGroup M] [Module R M] [Module.Finite R M] :
    IsReflexive R M :=
  have := finitePresentation_of_finite R M
  .of_injective_of_finitePresentation R M

end Module

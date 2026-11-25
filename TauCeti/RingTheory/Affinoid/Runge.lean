/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Affinoid.Subdomain.Laurent
public import TauCeti.RingTheory.Affinoid.Subdomain.Preimage

import TauCeti.RingTheory.Affinoid.QuotientNorm
import TauCeti.RingTheory.Affinoid.Restricted.Perturbation

/-!
# Runge immersions of affinoid spaces

A `K`-algebra map `φ : A → B` of affinoid algebras is a *Runge immersion*
(`TauCeti.IsRungeImmersion`) if `Sp B → Sp A` is a closed immersion into a Weierstrass domain
`W = {x ∈ Sp A : |f₁(x)|, …, |fₖ(x)| ≤ 1}` followed by the inclusion of `W`: the map `φ` factors
as a map `A → A⟨f⟩` representing `W` as an affinoid subdomain, followed by a surjection
`A⟨f⟩ → B`. The definition is algebraic, with no norm chosen on `A`, `B` or `A⟨f⟩`, like the
affinoid subdomains `TauCeti.IsAffinoidSubdomainMap` it is built from.

For complete ultrametric algebra norms on `A` and `B` there are two equivalent descriptions.

* `φ` is a Runge immersion if and only if some `φ f₁, …, φ fₖ` form a system of affinoid
  generators of `B` over `A`: they are power-bounded and the extension `A⟨X₁, …, Xₖ⟩ → B` of `φ`
  sending `Xᵢ` to `φ fᵢ` is surjective.
* `φ` is a Runge immersion if and only if its image is dense in `B`. The image of `A` is dense in a
  Weierstrass domain because polynomials are dense in restricted series; conversely, affinoid
  generators of `B` over `A` can be approximated by elements of the image of `A`, and they stay
  generators (`TauCeti.IsAffinoidAlgebra.exists_surjective_restrictedLift_of_denseRange`).

Closed immersions and inclusions of Weierstrass domains are Runge immersions. The density
criterion shows that Runge immersions compose. They are stable under base change along a
pushout of affinoid algebras, so restricting a Runge immersion `Sp B → Sp A` over an affinoid
subdomain `U ⊆ Sp A` gives a Runge immersion into `U`. The Gerritzen–Grauert theorem asserts that
every locally closed immersion becomes a Runge immersion over the members of a finite rational
covering of the target.

## Main definitions

* `TauCeti.IsRungeImmersion φ`: `φ : A → B` is a Runge immersion.

## Main results

* `TauCeti.isRungeImmersion_of_surjective`: closed immersions are Runge immersions.
* `TauCeti.IsAffinoidSubdomainMap.isRungeImmersion`: inclusions of Weierstrass domains are Runge
  immersions.
* `TauCeti.isRungeImmersion_iff_exists_surjective_restrictedLift`: Runge immersions are the maps
  whose image contains a system of affinoid generators.
* `TauCeti.isRungeImmersion_iff_denseRange`: Runge immersions are the maps with dense image.
* `TauCeti.IsRungeImmersion.comp`: Runge immersions compose.
* `TauCeti.IsRungeImmersion.baseChange`: Runge immersions are stable under affinoid pushouts.
* `TauCeti.IsRungeImmersion.exists_preimage`: the restriction of a Runge immersion over an
  affinoid subdomain of the target is a Runge immersion.

## References

* S. Bosch, *Lectures on Formal and Rigid Geometry*, Lecture Notes in Math. 2105, Springer,
  2014, §4.2, Definition 5, Remark 6 and Proposition 7.
-/

public section

namespace TauCeti

open _root_.MvPowerSeries TauCeti.MvPowerSeries

universe u v

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]

section Definition

variable {A : Type u} [CommRing A] [Algebra K A] {B : Type*} [CommRing B] [Algebra K B]

/-- **Runge immersions.** The `K`-algebra map `φ : A → B` is a Runge immersion if it factors as a
map `ι : A → W` representing a Weierstrass domain `{x ∈ Sp A : |f₁(x)|, …, |fₖ(x)| ≤ 1}` as an
affinoid subdomain, followed by a surjection `W → B`: geometrically, `Sp B → Sp A` is a closed
immersion into a Weierstrass domain followed by its inclusion. -/
def IsRungeImmersion (φ : A →ₐ[K] B) : Prop :=
  ∃ (k : ℕ) (f : Fin k → A) (W : Type u) (_ : CommRing W) (_ : Algebra K W) (ι : A →ₐ[K] W)
    (π : W →ₐ[K] B), IsAffinoidSubdomainMap ι (laurentDomain K f ![]) ∧
      Function.Surjective π ∧ π.comp ι = φ

/-- Unfolding lemma for `TauCeti.IsRungeImmersion`. -/
theorem isRungeImmersion_iff {φ : A →ₐ[K] B} :
    IsRungeImmersion φ ↔ ∃ (k : ℕ) (f : Fin k → A) (W : Type u) (_ : CommRing W)
      (_ : Algebra K W) (ι : A →ₐ[K] W) (π : W →ₐ[K] B),
      IsAffinoidSubdomainMap ι (laurentDomain K f ![]) ∧ Function.Surjective π ∧ π.comp ι = φ :=
  Iff.rfl

/-- The target of a Runge immersion is affinoid, being a quotient of an affinoid algebra. -/
theorem IsRungeImmersion.isAffinoidAlgebra {φ : A →ₐ[K] B} (h : IsRungeImmersion φ) :
    IsAffinoidAlgebra K B :=
  let ⟨_, _, _, _, _, _, π, hι, hπ, _⟩ := h
  hι.isAffinoidAlgebra.of_surjective π hπ

/-- **Inclusions of Weierstrass domains are Runge immersions.** -/
theorem IsAffinoidSubdomainMap.isRungeImmersion {W : Type u} [CommRing W] [Algebra K W]
    {ι : A →ₐ[K] W} {k : ℕ} {f : Fin k → A} (h : IsAffinoidSubdomainMap ι (laurentDomain K f ![])) :
    IsRungeImmersion ι :=
  ⟨k, f, W, _, _, ι, AlgHom.id K W, h, Function.surjective_id, AlgHom.id_comp ι⟩

/-- **Closed immersions are Runge immersions**, into the Weierstrass domain `Sp A` defined by no
inequalities. -/
theorem isRungeImmersion_of_surjective (hA : IsAffinoidAlgebra K A) {φ : A →ₐ[K] B}
    (hφ : Function.Surjective φ) : IsRungeImmersion φ := by
  have hW : laurentDomain K (![] : Fin 0 → A) ![] = Set.univ := by
    ext x
    simp
  exact ⟨0, ![], A, _, _, AlgHom.id K A, φ, hW ▸ IsAffinoidSubdomainMap.id hA, hφ,
    AlgHom.comp_id φ⟩

end Definition

section Normed

variable {A : Type u} [NormedCommRing A] [NormedAlgebra K A] [IsUltrametricDist A] [CompleteSpace A]
  (hA : IsAffinoidAlgebra K A)

variable {B : Type*} [NormedCommRing B] [NormedAlgebra K B] [IsUltrametricDist B] [CompleteSpace B]
  (hB : IsAffinoidAlgebra K B)

include hA hB in
/-- **Runge immersions are the maps whose image contains affinoid generators** (Bosch §4.2,
Remark 6). For affinoid algebras with complete ultrametric algebra norms, `φ : A → B` is a Runge
immersion if and only if for some `f₁, …, fₖ ∈ A` the images `φ fᵢ` are power-bounded and the
extension `A⟨X₁, …, Xₖ⟩ → B` of `φ` sending `Xᵢ` to `φ fᵢ` is surjective. -/
theorem isRungeImmersion_iff_exists_surjective_restrictedLift {φ : A →ₐ[K] B} :
    IsRungeImmersion φ ↔ ∃ (k : ℕ) (f : Fin k → A) (hf : ∀ i, Huber.IsPowerBounded (φ (f i))),
      Function.Surjective (hA.restrictedLift hB φ hf) := by
  refine ⟨fun ⟨k, f, W, _, _, ι, π, hι, hπ, hπι⟩ ↦ ?_, fun ⟨k, f, hf, hsurj⟩ ↦ ?_⟩
  · -- `φ` sends `Sp B` into the Weierstrass domain, so the `φ fᵢ` are power-bounded.
    have hW := hι.isAffinoidAlgebra
    have hf : ∀ i, Huber.IsPowerBounded (φ (f i)) := by
      refine ((hB.range_maximalSpectrumComap_subset_laurentDomain_iff φ
        (g := (![] : Fin 0 → A))).mp ?_).1
      rw [← hπι, IsAffinoidAlgebra.maximalSpectrumComap_comp hW hB, Set.range_comp]
      exact (Set.image_subset_range _ _).trans hι.range_maximalSpectrumComap_subset
    let := hW.residueNormedCommRing
    let := hW.residueNormedAlgebra
    have := hW.isUltrametricDist_residueNormedCommRing
    have := hW.completeSpace_residueNormedCommRing
    have hfι : ∀ i, Huber.IsPowerBounded (ι (f i)) :=
      ((hW.range_maximalSpectrumComap_subset_laurentDomain_iff ι
        (g := (![] : Fin 0 → A))).mp hι.range_maximalSpectrumComap_subset).1
    -- The generators of `B` are the images of the generators `ι fᵢ` of `W`.
    have hcomp : hA.restrictedLift hB φ hf = π.comp (hA.restrictedLift hW ι hfι) :=
      hA.algHom_ext_isRestricted_subring hB (fun a ↦ by simp [← hπι])
        fun i ↦ by simp [← hπι]
    exact ⟨k, f, hf, hcomp ▸ hπ.comp (hι.surjective_restrictedLift hA hfι)⟩
  · -- Factor `φ` through the Weierstrass fraction algebra `A⟨f⟩`, whose quotient map is
    -- `A⟨X⟩ → A⟨f⟩` (the indexing type `Fin (k + 0)` is `Fin k`).
    let π := LaurentFraction.lift (g := (![] : Fin 0 → A)) hA hB φ hf (b := ![])
      (fun j ↦ j.elim0) fun j ↦ j.elim0
    have hX (i : Fin k) : Ideal.Quotient.mk (laurentFractionIdeal f (![] : Fin 0 → A))
        ⟨X i, isRestricted_X _ i⟩ = algebraMap A _ (f i) :=
      LaurentFraction.mk_X_castAdd i
    have hcomp : hA.restrictedLift hB φ hf =
        π.comp (Ideal.Quotient.mkₐ K (laurentFractionIdeal f (![] : Fin 0 → A))) :=
      hA.algHom_ext_isRestricted_subring hB
        (fun a ↦ by
          rw [IsAffinoidAlgebra.restrictedLift_algebraMap, AlgHom.comp_apply,
            Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.mk_algebraMap]
          exact (LaurentFraction.lift_algebraMap hA hB φ hf _ _ a).symm)
        fun i ↦ by
          rw [IsAffinoidAlgebra.restrictedLift_X, AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk, hX]
          exact (LaurentFraction.lift_algebraMap hA hB φ hf _ _ (f i)).symm
    refine ⟨k, f, _, _, _, _, π, LaurentFraction.isAffinoidSubdomainMap hA, fun b ↦ ?_,
      AlgHom.ext fun a ↦ LaurentFraction.lift_algebraMap hA hB φ hf _ _ a⟩
    obtain ⟨t, rfl⟩ := hsurj b
    exact ⟨Ideal.Quotient.mk _ t, by rw [hcomp, AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk]⟩

include hA hB in
/-- **Runge immersions are the maps with dense image** (Bosch §4.2, Remark 6). For affinoid
algebras with complete ultrametric algebra norms, `φ : A → B` is a Runge immersion if and only if
its image is dense in `B`. -/
theorem isRungeImmersion_iff_denseRange {φ : A →ₐ[K] B} :
    IsRungeImmersion φ ↔ DenseRange φ := by
  rw [isRungeImmersion_iff_exists_surjective_restrictedLift hA hB]
  refine ⟨fun ⟨k, f, hf, hsurj⟩ ↦ ?_, hA.exists_surjective_restrictedLift_of_denseRange hB⟩
  have := (hA.isRestricted_subring (τ := Fin k)).isNoetherianRing
  -- The images of polynomials are dense, and they are values of `φ`.
  refine (hsurj.denseRange.comp denseRange_polynomialToRestricted
    (hB.continuous_algHom _)).mono ?_
  rintro _ ⟨p, rfl⟩
  refine ⟨MvPolynomial.eval f p, ?_⟩
  -- `φ (p(f)) = p(φ f)`, with the coefficients of `p` mapped by `φ`.
  have h := MvPolynomial.eval₂_comp_left (φ : A →+* B) (RingHom.id A) f p
  rw [RingHom.comp_id] at h
  rw [Function.comp_apply, IsAffinoidAlgebra.restrictedLift_polynomialToRestricted]
  exact h

end Normed

section Composition

variable {A : Type u} [CommRing A] [Algebra K A] {B : Type v} [CommRing B] [Algebra K B]
  {C : Type*} [CommRing C] [Algebra K C]

/-- **Runge immersions compose** (Bosch §4.2, Proposition 7). -/
theorem IsRungeImmersion.comp (hA : IsAffinoidAlgebra K A) {φ : A →ₐ[K] B} {ψ : B →ₐ[K] C}
    (hψ : IsRungeImmersion ψ) (hφ : IsRungeImmersion φ) : IsRungeImmersion (ψ.comp φ) := by
  have hB := hφ.isAffinoidAlgebra
  have hC := hψ.isAffinoidAlgebra
  let := hA.residueNormedCommRing
  let := hA.residueNormedAlgebra
  have := hA.isUltrametricDist_residueNormedCommRing
  have := hA.completeSpace_residueNormedCommRing
  let := hB.residueNormedCommRing
  let := hB.residueNormedAlgebra
  have := hB.isUltrametricDist_residueNormedCommRing
  have := hB.completeSpace_residueNormedCommRing
  let := hC.residueNormedCommRing
  let := hC.residueNormedAlgebra
  have := hC.isUltrametricDist_residueNormedCommRing
  have := hC.completeSpace_residueNormedCommRing
  have := hB.isNoetherianRing
  rw [isRungeImmersion_iff_denseRange hB hC] at hψ
  rw [isRungeImmersion_iff_denseRange hA hB] at hφ
  rw [isRungeImmersion_iff_denseRange hA hC, AlgHom.coe_comp]
  exact hψ.comp hφ (hC.continuous_algHom ψ)

end Composition

section BaseChangeNormed

variable {A B C D : Type u} [NormedCommRing A] [NormedAlgebra K A] [IsUltrametricDist A]
  [CompleteSpace A] [NormedCommRing B] [NormedAlgebra K B] [IsUltrametricDist B] [CompleteSpace B]
  [NormedCommRing C] [NormedAlgebra K C] [IsUltrametricDist C] [CompleteSpace C]
  [NormedCommRing D] [NormedAlgebra K D] [IsUltrametricDist D] [CompleteSpace D]
  (hA : IsAffinoidAlgebra K A) (hB : IsAffinoidAlgebra K B) (hC : IsAffinoidAlgebra K C)
  (hD : IsAffinoidAlgebra K D) {ψ : A →ₐ[K] C} {φ : A →ₐ[K] B} {χ : B →ₐ[K] D} {θ : C →ₐ[K] D}

include hA hB hC hD in
/-- Affinoid generators `ψ fᵢ` of `C` over `A` give affinoid generators `χ (φ fᵢ)` of a pushout
`D` of `B` and `C` over `A`. The quotient `Q = B⟨X⟩ ⧸ ker Λ'` of the extension
`Λ' : B⟨X⟩ → D` receives compatible maps from `B` and `C`, hence a map `D → Q`, which `Λ'`
lifts back to the identity of `D`. -/
private theorem surjective_restrictedLift_of_pushout (hsq : χ.comp φ = θ.comp ψ)
    (hpush : ∀ {E : Type u} [CommRing E] [Algebra K E], IsAffinoidAlgebra K E →
      ∀ (β : B →ₐ[K] E) (γ : C →ₐ[K] E), β.comp φ = γ.comp ψ →
        ∃! δ : D →ₐ[K] E, δ.comp χ = β ∧ δ.comp θ = γ)
    {k : ℕ} {f : Fin k → A} (hf : ∀ i, Huber.IsPowerBounded (ψ (f i)))
    (hΛ : Function.Surjective (hA.restrictedLift hC ψ hf))
    (hg : ∀ i, Huber.IsPowerBounded (χ (φ (f i)))) :
    Function.Surjective (hB.restrictedLift hD χ hg) := by
  have := (hA.isRestricted_subring (τ := Fin k)).isNoetherianRing
  set Λ := hA.restrictedLift hC ψ hf
  set Λ' := hB.restrictedLift hD χ hg
  -- `j : A⟨X⟩ → B⟨X⟩` applies `φ` to coefficients, and `Λ' ∘ j = θ ∘ Λ`.
  have hTB := hB.isRestricted_subring (τ := Fin k)
  let j := hA.restrictedLift hTB
    ((IsScalarTower.toAlgHom K B (IsRestricted.subring (R := B) (fun _ : Fin k ↦ 1))).comp φ)
    (b := fun i ↦ ⟨X i, isRestricted_X _ i⟩) isPowerBounded_X
  have hj : Λ'.comp j = θ.comp Λ := hA.algHom_ext_isRestricted_subring hD
    (fun a ↦ by simpa [j, Λ, Λ'] using AlgHom.congr_fun hsq a)
    fun i ↦ by simpa [j, Λ, Λ'] using AlgHom.congr_fun hsq (f i)
  -- Maps from `B` and `C` into `Q = B⟨X⟩ ⧸ ker Λ'`, agreeing on `A`.
  let β := (Ideal.Quotient.mkₐ K (RingHom.ker Λ')).comp
    (IsScalarTower.toAlgHom K B (IsRestricted.subring (R := B) (fun _ : Fin k ↦ 1)))
  have hker : RingHom.ker Λ.toRingHom ≤
      RingHom.ker ((Ideal.Quotient.mkₐ K (RingHom.ker Λ')).comp j).toRingHom := fun x hx ↦ by
    rw [RingHom.mem_ker, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom] at hx ⊢
    rw [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem,
      RingHom.mem_ker, ← AlgHom.comp_apply, hj, AlgHom.comp_apply, hx, map_zero]
  let γ := Λ.liftOfSurjective hΛ _ hker
  have hγ (t) : γ (Λ t) = Ideal.Quotient.mk (RingHom.ker Λ') (j t) :=
    AlgHom.liftOfSurjective_apply _ hΛ _ hker t
  have hβγ : β.comp φ = γ.comp ψ := AlgHom.ext fun a ↦ by
    simp only [AlgHom.comp_apply]
    rw [← hA.restrictedLift_algebraMap hC ψ hf a, hγ]
    simp [β, j]
  -- `ker Λ'`-lifting `δ` back to `D` is the identity, by the uniqueness in the pushout.
  obtain ⟨δ, ⟨hδχ, hδθ⟩, -⟩ := hpush (hTB.quotient (RingHom.ker Λ')) β γ hβγ
  have hid : (Ideal.kerLiftAlg Λ').comp δ = AlgHom.id K D := by
    refine (hpush hD χ θ hsq).unique ⟨?_, ?_⟩ ⟨AlgHom.id_comp χ, AlgHom.id_comp θ⟩
    · rw [AlgHom.comp_assoc, hδχ]
      exact AlgHom.ext fun b ↦ by
        simp only [AlgHom.comp_apply, β, Ideal.Quotient.mkₐ_eq_mk, IsScalarTower.coe_toAlgHom',
          Ideal.kerLiftAlg_mk, Λ', IsAffinoidAlgebra.restrictedLift_algebraMap]
    · rw [AlgHom.comp_assoc, hδθ]
      refine AlgHom.ext fun c ↦ ?_
      obtain ⟨t, rfl⟩ := hΛ c
      simp only [AlgHom.comp_apply, hγ, Ideal.kerLiftAlg_mk]
      exact AlgHom.congr_fun hj t
  intro d
  obtain ⟨t, ht⟩ := Ideal.Quotient.mk_surjective (δ d)
  refine ⟨t, ?_⟩
  rw [← Ideal.kerLiftAlg_mk, ht]
  exact AlgHom.congr_fun hid d

include hA hB hC hD in
/-- `IsRungeImmersion.baseChange` for affinoid algebras with complete ultrametric algebra norms. -/
private theorem IsRungeImmersion.baseChange_of_normed (hψ : IsRungeImmersion ψ)
    (hsq : χ.comp φ = θ.comp ψ)
    (hpush : ∀ {E : Type u} [CommRing E] [Algebra K E], IsAffinoidAlgebra K E →
      ∀ (β : B →ₐ[K] E) (γ : C →ₐ[K] E), β.comp φ = γ.comp ψ →
        ∃! δ : D →ₐ[K] E, δ.comp χ = β ∧ δ.comp θ = γ) :
    IsRungeImmersion χ := by
  obtain ⟨k, f, hf, hΛ⟩ := (isRungeImmersion_iff_exists_surjective_restrictedLift hA hC).mp hψ
  have := hC.isNoetherianRing
  -- The images `χ (φ fᵢ) = θ (ψ fᵢ)` are power-bounded, and they generate `D` over `B`.
  have hg (i : Fin k) : Huber.IsPowerBounded (χ (φ (f i))) := by
    have := hD.isPowerBounded_map θ (hf i)
    rwa [← AlgHom.comp_apply, ← hsq, AlgHom.comp_apply] at this
  exact (isRungeImmersion_iff_exists_surjective_restrictedLift hB hD).mpr
    ⟨k, φ ∘ f, hg, surjective_restrictedLift_of_pushout hA hB hC hD hsq hpush hf hΛ hg⟩

end BaseChangeNormed

section BaseChange

variable {A B C D : Type u} [CommRing A] [Algebra K A] [CommRing B] [Algebra K B]
  [CommRing C] [Algebra K C] [CommRing D] [Algebra K D]

/-- **Runge immersions are stable under affinoid base change.** Let `ψ : A → C` be a Runge
immersion, `φ : A → B` a map of affinoid algebras, and `χ ∘ φ = θ ∘ ψ` a commutative square with
`D` affinoid which is a pushout for maps into affinoid algebras: two maps `β : B → E` and
`γ : C → E` into an affinoid algebra with `β ∘ φ = γ ∘ ψ` factor through exactly one map
`D → E`. Then `χ : B → D` is a Runge immersion. -/
theorem IsRungeImmersion.baseChange (hA : IsAffinoidAlgebra K A) (hB : IsAffinoidAlgebra K B)
    (hD : IsAffinoidAlgebra K D) {ψ : A →ₐ[K] C} (hψ : IsRungeImmersion ψ) {φ : A →ₐ[K] B}
    {χ : B →ₐ[K] D} {θ : C →ₐ[K] D} (hsq : χ.comp φ = θ.comp ψ)
    (hpush : ∀ {E : Type u} [CommRing E] [Algebra K E], IsAffinoidAlgebra K E →
      ∀ (β : B →ₐ[K] E) (γ : C →ₐ[K] E), β.comp φ = γ.comp ψ →
        ∃! δ : D →ₐ[K] E, δ.comp χ = β ∧ δ.comp θ = γ) :
    IsRungeImmersion χ := by
  have hC := hψ.isAffinoidAlgebra
  let := hA.residueNormedCommRing
  let := hA.residueNormedAlgebra
  have := hA.isUltrametricDist_residueNormedCommRing
  have := hA.completeSpace_residueNormedCommRing
  let := hB.residueNormedCommRing
  let := hB.residueNormedAlgebra
  have := hB.isUltrametricDist_residueNormedCommRing
  have := hB.completeSpace_residueNormedCommRing
  let := hC.residueNormedCommRing
  let := hC.residueNormedAlgebra
  have := hC.isUltrametricDist_residueNormedCommRing
  have := hC.completeSpace_residueNormedCommRing
  let := hD.residueNormedCommRing
  let := hD.residueNormedAlgebra
  have := hD.isUltrametricDist_residueNormedCommRing
  have := hD.completeSpace_residueNormedCommRing
  exact hψ.baseChange_of_normed hA hB hC hD hsq hpush

/-- **Restricting a Runge immersion over an affinoid subdomain** (Bosch §4.2, Proposition 7).
Let `ψ : A → C` be a Runge immersion and let `φ : A → B` represent an affinoid subdomain
`U ⊆ Sp A`. Then some `θ : C → D` represents the inverse image of `U` in `Sp C`, and the induced
map `χ : B → D`, with `χ ∘ φ = θ ∘ ψ`, is a Runge immersion: `Sp D → U` is a Runge immersion. -/
theorem IsRungeImmersion.exists_preimage (hA : IsAffinoidAlgebra K A) {ψ : A →ₐ[K] C}
    (hψ : IsRungeImmersion ψ) {φ : A →ₐ[K] B} {U : Set (MaximalSpectrum A)}
    (h : IsAffinoidSubdomainMap φ U) :
    ∃ (D : Type u) (_ : CommRing D) (_ : Algebra K D) (θ : C →ₐ[K] D) (χ : B →ₐ[K] D),
      IsAffinoidSubdomainMap θ (hψ.isAffinoidAlgebra.maximalSpectrumComap ψ ⁻¹' U) ∧
        χ.comp φ = θ.comp ψ ∧ IsRungeImmersion χ := by
  have hC := hψ.isAffinoidAlgebra
  obtain ⟨D, _, _, θ, hθ⟩ := h.exists_preimage hA hC ψ
  have hD := hθ.isAffinoidAlgebra
  -- The classical points of `D` lie over `U`, so `θ ∘ ψ` factors through `φ`.
  have hU : Set.range (hD.maximalSpectrumComap (θ.comp ψ)) ⊆ U := by
    rw [IsAffinoidAlgebra.maximalSpectrumComap_comp hC hD, Set.range_comp]
    exact Set.image_subset_iff.mpr hθ.range_maximalSpectrumComap_subset
  let χ := h.lift hD (θ.comp ψ) hU
  have hsq : χ.comp φ = θ.comp ψ := h.lift_comp hD _ hU
  -- The square is a pushout: a map out of `C` whose composite with `ψ` factors through `φ` has
  -- its classical points over `U`, so it factors through `θ`.
  refine ⟨D, _, _, θ, χ, hθ, hsq, hψ.baseChange hA h.isAffinoidAlgebra hD hsq ?_⟩
  intro E _ _ hE β γ hβγ
  have hγU : Set.range (hE.maximalSpectrumComap γ) ⊆ hC.maximalSpectrumComap ψ ⁻¹' U := by
    rw [← Set.image_subset_iff, ← Set.range_comp,
      ← IsAffinoidAlgebra.maximalSpectrumComap_comp hC hE, ← hβγ]
    exact h.range_maximalSpectrumComap_comp_subset hE β
  refine ⟨hθ.lift hE γ hγU, ⟨h.algHom_ext hE ?_, hθ.lift_comp hE γ hγU⟩,
    fun δ ⟨_, hδθ⟩ ↦ hθ.eq_lift hE γ hγU hδθ⟩
  rw [AlgHom.comp_assoc, hsq, ← AlgHom.comp_assoc, hθ.lift_comp, hβγ]

end BaseChange

end TauCeti

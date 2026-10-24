/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Affinoid.Basic
public import Mathlib.RingTheory.Finiteness.Defs

import TauCeti.RingTheory.MvPowerSeries.TateAlgebra.Distinguished
import TauCeti.RingTheory.PowerSeries.Weierstrass.Quotient

/-!
# Noether normalisation of affinoid algebras

Every nonzero affinoid algebra over a complete ultrametric field admits a finite injective
algebra map from a Tate algebra. No reducedness, characteristic, or nontrivial valuation
assumption is needed.

The argument follows Bosch–Güntzer–Remmert, *Non-Archimedean Analysis*, §6.1.2. Its
distinguished-variable induction adapts the central construction in
`TauCeti.MvPowerSeries.finite_quotient_of_isMaximal`: a nonzero relation becomes distinguished
after a change of variables, so Weierstrass division makes the algebra finite over the image of
a Tate algebra with one fewer variable. Applying induction to that image retains nilpotents.
-/

public section

namespace TauCeti

open _root_.MvPowerSeries

universe u v w

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]

local notation "Tate " σ:max => IsRestricted.subring (R := K) (fun _ : σ ↦ 1)

/-- Removing a distinguished variable gives a finite map from a smaller Tate algebra. -/
private theorem exists_finite_map_of_not_injective {σ : Type*} [Finite σ]
    {A : Type*} [CommRing A] [Algebra K A] (π : Tate (Option σ) →ₐ[K] A)
    (hπ : Function.Surjective π) (hne : ¬ Function.Injective π) :
    ∃ γ : Tate σ →ₐ[K] A, γ.Finite := by
  obtain ⟨f, hf, hf0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
    (mt (RingHom.injective_iff_ker_eq_bot (f := π.toRingHom)).mpr hne)
  obtain ⟨e, s, hd, hu⟩ := MvPowerSeries.exists_algEquiv_isDistinguished_isUnit f hf0
  let R := Tate σ
  let S := PowerSeries.IsRestricted.subring (R := R) 1
  let _ : Algebra K S := ((algebraMap R S).comp (algebraMap K R)).toAlgebra
  have : IsScalarTower K R S := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  let Φ : Tate (Option σ) ≃ₐ[K] S :=
    e.trans (AlgEquiv.ofRingEquiv (f := Huber.restrictedOptionEquiv)
      Huber.restrictedOptionEquiv_algebraMap)
  let ψ := π.comp Φ.symm.toAlgHom
  let I : Ideal S := Ideal.span {Φ f}
  have hI : I ≤ RingHom.ker ψ := by
    rw [Ideal.span_le, Set.singleton_subset_iff]
    exact RingHom.mem_ker.mpr (by simpa [ψ] using (RingHom.mem_ker.mp hf))
  let q : S ⧸ I →ₐ[K] A := Ideal.Quotient.liftₐ I ψ (fun a ha ↦ RingHom.mem_ker.mp (hI ha))
  have hqmk (x : S) : q (Ideal.Quotient.mk I x) = ψ x :=
    DFunLike.congr_fun (Ideal.Quotient.liftₐ_comp I ψ
      (fun a ha ↦ RingHom.mem_ker.mp (hI ha))) x
  have hq : Function.Surjective q := by
    intro a
    obtain ⟨g, rfl⟩ := hπ a
    exact ⟨Ideal.Quotient.mk I (Φ g), (hqmk _).trans (by simp [ψ])⟩
  have : Module.Finite R (S ⧸ I) := hd.finite_quotient zero_lt_one hu
  let γ : R →ₐ[K] A := ψ.comp (IsScalarTower.toAlgHom K R S)
  refine ⟨γ, ?_⟩
  have hcoeff : (algebraMap R (S ⧸ I)).Finite := by
    rw [RingHom.finite_algebraMap]
    infer_instance
  have hfin := (RingHom.Finite.of_surjective q.toRingHom hq).comp hcoeff
  have hcomp : q.toRingHom.comp (algebraMap R (S ⧸ I)) = γ.toRingHom := by
    ext x
    rw [RingHom.comp_apply, ← Ideal.Quotient.mk_algebraMap]
    exact hqmk _
  exact (congrArg RingHom.Finite hcomp).mp hfin

omit [CompleteSpace K] in
/-- A bijective Tate presentation already supplies a normalisation. -/
private theorem exists_finite_injective_of_bijective {σ : Type*} [Finite σ]
    {A : Type*} [CommRing A] [Algebra K A] (π : Tate σ →ₐ[K] A)
    (hπ : Function.Bijective π) :
    ∃ (n : ℕ) (g : Tate (Fin n) →ₐ[K] A), Function.Injective g ∧ g.Finite := by
  let := Fintype.ofFinite σ
  let r : Tate (Fin (Fintype.card σ)) ≃ₐ[K] Tate σ :=
    IsRestricted.renameAlgEquiv (Fintype.equivFin σ).symm fun _ ↦ 1
  exact ⟨_, π.comp r.toAlgHom, hπ.1.comp r.injective,
    AlgHom.Finite.of_surjective _ (hπ.2.comp r.surjective)⟩

/-- Normalisation for an arbitrary finite-variable Tate presentation. -/
private theorem exists_finite_injective_of_surjective {σ : Type v} [Finite σ]
    {A : Type w} [CommRing A] [Algebra K A] [Nontrivial A]
    (π : Tate σ →ₐ[K] A) (hπ : Function.Surjective π) :
    ∃ (n : ℕ) (g : Tate (Fin n) →ₐ[K] A), Function.Injective g ∧ g.Finite := by
  suffices H : ∀ (B : Type w) [CommRing B] [Algebra K B] [Nontrivial B]
      (π : Tate σ →ₐ[K] B), Function.Surjective π →
      ∃ (n : ℕ) (g : Tate (Fin n) →ₐ[K] B), Function.Injective g ∧ g.Finite by
    exact H A π hπ
  refine Finite.induction_empty_option
    (P := fun σ ↦ ∀ (A : Type w) [CommRing A] [Algebra K A] [Nontrivial A]
      (π : Tate σ →ₐ[K] A), Function.Surjective π →
      ∃ (n : ℕ) (g : Tate (Fin n) →ₐ[K] A), Function.Injective g ∧ g.Finite)
    (fun {α β} e ih A _ _ _ π hπ ↦ ?_) (fun A _ _ _ π hπ ↦ ?_)
    (fun ih A _ _ _ π hπ ↦ ?_) σ
  · let r : Tate α ≃ₐ[K] Tate β := IsRestricted.renameAlgEquiv e fun _ ↦ 1
    exact ih A (π.comp r.toAlgHom) (hπ.comp r.surjective)
  · apply exists_finite_injective_of_bijective π ⟨?_, hπ⟩
    intro a b hab
    obtain ⟨x, rfl⟩ := algebraMap_isRestrictedSubring_surjective (R := K) a
    obtain ⟨y, rfl⟩ := algebraMap_isRestrictedSubring_surjective (R := K) b
    rw [π.commutes, π.commutes] at hab
    rw [(FaithfulSMul.algebraMap_injective K A) hab]
  · by_cases h : Function.Injective π
    · exact exists_finite_injective_of_bijective π ⟨h, hπ⟩
    · obtain ⟨γ, hγ⟩ := exists_finite_map_of_not_injective π hπ h
      obtain ⟨n, g, hg, hgf⟩ := ih γ.range γ.rangeRestrict γ.rangeRestrict_surjective
      have hval : γ.range.val.Finite := by
        apply AlgHom.Finite.of_comp_finite (f := γ.rangeRestrict)
        rw [AlgHom.val_comp_rangeRestrict]
        exact hγ
      exact ⟨n, γ.range.val.comp g, Subtype.val_injective.comp hg, hval.comp hgf⟩

/-- **Affinoid Noether normalisation.** Every nonzero affinoid algebra over a complete
ultrametric field is finite over an injectively embedded finite-variable Tate algebra.
Finiteness uses the algebra structure induced by the displayed map. -/
theorem IsAffinoidAlgebra.exists_finite_injective {A : Type*} [CommRing A] [Algebra K A]
    [Nontrivial A] (hA : IsAffinoidAlgebra K A) :
    ∃ (n : ℕ) (g : Tate (Fin n) →ₐ[K] A), Function.Injective g ∧ g.Finite := by
  obtain ⟨n, π, hπ⟩ := (isAffinoidAlgebra_iff K A).mp hA
  exact exists_finite_injective_of_surjective π hπ

end TauCeti

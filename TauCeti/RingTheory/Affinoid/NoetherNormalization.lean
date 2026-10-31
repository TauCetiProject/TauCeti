/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Affinoid.Basic
public import Mathlib.RingTheory.Finiteness.Defs
public import TauCeti.Analysis.Normed.Ring.Ultra

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

The changes of variables are isometries of Gauss norms, so for a presentation
`π : K⟨X₁, …, Xₙ⟩ → A` the normalisation can be chosen of the form `π ∘ ι` for a Gauss-norm
preserving map `ι : K⟨Y₁, …, Y_d⟩ → K⟨X₁, …, Xₙ⟩` (`AlgHom.exists_norm_eq_finite_injective_comp`).
In particular it sends the Gauss unit ball into the image under `π` of the Gauss unit ball
(`AlgHom.exists_finite_injective_map_unitClosedBall_le`). This compatibility relates the
supremum seminorm of `A` to integrality over the presentation ring `π(K⟨X₁, …, Xₙ⟩°)`, and lets
coefficients over `K⟨Y₁, …, Y_d⟩` be lifted along `π` without increasing their Gauss norms.
-/

public section

namespace TauCeti

open _root_.MvPowerSeries

universe u v w

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]

local notation "Tate " σ:max => IsRestricted.subring (R := K) (fun _ : σ ↦ 1)

/-- Removing a distinguished variable gives a finite map from a smaller Tate algebra, through a
norm-preserving map of Tate algebras. -/
private theorem exists_finite_map_of_not_injective {σ : Type*} [Finite σ]
    {A : Type*} [CommRing A] [Algebra K A] (π : Tate (Option σ) →ₐ[K] A)
    (hπ : Function.Surjective π) (hne : ¬ Function.Injective π) :
    ∃ ι : Tate σ →ₐ[K] Tate (Option σ), (∀ y, ‖ι y‖ = ‖y‖) ∧ (π.comp ι).Finite := by
  obtain ⟨f, hf, hf0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
    (mt (RingHom.injective_iff_ker_eq_bot (f := π.toRingHom)).mpr hne)
  obtain ⟨α, hα, s, hd, hu⟩ :=
    MvPowerSeries.exists_restrictedTriangularEquiv_isDistinguished_isUnit f hf0
  let e := MvPowerSeries.restrictedTriangularEquiv (R := K) α hα
  let R := Tate σ
  let S := PowerSeries.IsRestricted.subring (R := R) 1
  let Φ : Tate (Option σ) ≃ₐ[K] S := e.trans restrictedOptionEquiv
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
  let ι : R →ₐ[K] Tate (Option σ) := Φ.symm.toAlgHom.comp (IsScalarTower.toAlgHom K R S)
  -- The change of variables `Φ` preserves Gauss norms.
  have hΦ (z : Tate (Option σ)) : ‖Φ z‖ = ‖z‖ :=
    (MvPowerSeries.norm_restrictedOptionEquiv (e z)).trans
      (MvPowerSeries.norm_restrictedTriangularEquiv ..)
  refine ⟨ι, fun y ↦ ?_, ?_⟩
  · -- `ι y` unfolds to `Φ.symm (algebraMap R S y)`.
    rw [← hΦ]
    exact (congrArg norm (Φ.apply_symm_apply _)).trans
      (MvPowerSeries.norm_algebraMap_isRestrictedSubring y)
  have hcoeff : (algebraMap R (S ⧸ I)).Finite := by
    rw [RingHom.finite_algebraMap]
    infer_instance
  have hfin := (RingHom.Finite.of_surjective q.toRingHom hq).comp hcoeff
  have hcomp : q.toRingHom.comp (algebraMap R (S ⧸ I)) = (π.comp ι).toRingHom := by
    ext x
    rw [RingHom.comp_apply, ← Ideal.Quotient.mk_algebraMap]
    exact (hqmk _).trans (by simp [ψ, ι])
  exact (congrArg RingHom.Finite hcomp).mp hfin

omit [CompleteSpace K] in
/-- A bijective Tate presentation already supplies a normalisation, after renaming the
variables. -/
private theorem exists_finite_injective_of_bijective {σ : Type*} [Finite σ]
    {A : Type*} [CommRing A] [Algebra K A] (π : Tate σ →ₐ[K] A)
    (hπ : Function.Bijective π) :
    ∃ (n : ℕ) (ι : Tate (Fin n) →ₐ[K] Tate σ), (∀ x, ‖ι x‖ = ‖x‖) ∧
      Function.Injective (π.comp ι) ∧ (π.comp ι).Finite := by
  let := Fintype.ofFinite σ
  let r : Tate (Fin (Fintype.card σ)) ≃ₐ[K] Tate σ :=
    IsRestricted.renameAlgEquiv (Fintype.equivFin σ).symm fun _ ↦ 1
  exact ⟨_, r.toAlgHom,
    IsRestricted.norm_renameAlgEquiv (Fintype.equivFin σ).symm (fun _ ↦ (1 : ℝ)),
    hπ.1.comp r.injective, AlgHom.Finite.of_surjective _ (hπ.2.comp r.surjective)⟩

/-- Normalisation for an arbitrary finite-variable Tate presentation `π`, through a
norm-preserving map of Tate algebras. -/
private theorem exists_finite_injective_of_surjective {σ : Type v} [Finite σ]
    {A : Type w} [CommRing A] [Algebra K A] [Nontrivial A]
    (π : Tate σ →ₐ[K] A) (hπ : Function.Surjective π) :
    ∃ (n : ℕ) (ι : Tate (Fin n) →ₐ[K] Tate σ), (∀ x, ‖ι x‖ = ‖x‖) ∧
      Function.Injective (π.comp ι) ∧ (π.comp ι).Finite := by
  suffices H : ∀ (B : Type w) [CommRing B] [Algebra K B] [Nontrivial B]
      (π : Tate σ →ₐ[K] B), Function.Surjective π →
      ∃ (n : ℕ) (ι : Tate (Fin n) →ₐ[K] Tate σ), (∀ x, ‖ι x‖ = ‖x‖) ∧
        Function.Injective (π.comp ι) ∧ (π.comp ι).Finite by
    exact H A π hπ
  refine Finite.induction_empty_option
    (P := fun σ ↦ ∀ (A : Type w) [CommRing A] [Algebra K A] [Nontrivial A]
      (π : Tate σ →ₐ[K] A), Function.Surjective π →
      ∃ (n : ℕ) (ι : Tate (Fin n) →ₐ[K] Tate σ), (∀ x, ‖ι x‖ = ‖x‖) ∧
        Function.Injective (π.comp ι) ∧ (π.comp ι).Finite)
    (fun {α β} e ih A _ _ _ π hπ ↦ ?_) (fun A _ _ _ π hπ ↦ ?_)
    (fun ih A _ _ _ π hπ ↦ ?_) σ
  · let r : Tate α ≃ₐ[K] Tate β := IsRestricted.renameAlgEquiv e fun _ ↦ 1
    obtain ⟨n, ι, hι, hg, hgf⟩ := ih A (π.comp r.toAlgHom) (hπ.comp r.surjective)
    exact ⟨n, r.toAlgHom.comp ι, fun x ↦
      (IsRestricted.norm_renameAlgEquiv e (fun _ ↦ (1 : ℝ)) (ι x)).trans (hι x), hg, hgf⟩
  · apply exists_finite_injective_of_bijective π ⟨?_, hπ⟩
    intro a b hab
    obtain ⟨x, rfl⟩ := algebraMap_isRestrictedSubring_surjective (R := K) a
    obtain ⟨y, rfl⟩ := algebraMap_isRestrictedSubring_surjective (R := K) b
    rw [π.commutes, π.commutes] at hab
    rw [(FaithfulSMul.algebraMap_injective K A) hab]
  · by_cases h : Function.Injective π
    · exact exists_finite_injective_of_bijective π ⟨h, hπ⟩
    · obtain ⟨ι₁, hι₁, hγ⟩ := exists_finite_map_of_not_injective π hπ h
      let γ := π.comp ι₁
      obtain ⟨n, ι₂, hι₂, hg, hgf⟩ :=
        ih γ.range γ.rangeRestrict γ.rangeRestrict_surjective
      have hval : γ.range.val.Finite := by
        apply AlgHom.Finite.of_comp_finite (f := γ.rangeRestrict)
        rw [AlgHom.val_comp_rangeRestrict]
        exact hγ
      have hcomp : π.comp (ι₁.comp ι₂) = γ.range.val.comp (γ.rangeRestrict.comp ι₂) := by
        rw [← AlgHom.comp_assoc _ γ.rangeRestrict, AlgHom.val_comp_rangeRestrict, AlgHom.comp_assoc]
      refine ⟨n, ι₁.comp ι₂, fun x ↦ (hι₁ (ι₂ x)).trans (hι₂ x), ?_, ?_⟩
      · rw [hcomp]
        exact Subtype.val_injective.comp hg
      · rw [hcomp]
        exact hval.comp hgf

/-- **Affinoid Noether normalisation.** Every nonzero affinoid algebra over a complete
ultrametric field is finite over an injectively embedded finite-variable Tate algebra.
Finiteness uses the algebra structure induced by the displayed map. -/
theorem IsAffinoidAlgebra.exists_finite_injective {A : Type*} [CommRing A] [Algebra K A]
    [Nontrivial A] (hA : IsAffinoidAlgebra K A) :
    ∃ (n : ℕ) (g : Tate (Fin n) →ₐ[K] A), Function.Injective g ∧ g.Finite := by
  obtain ⟨n, π, hπ⟩ := (isAffinoidAlgebra_iff K A).mp hA
  obtain ⟨d, ι, -, hg, hgf⟩ := exists_finite_injective_of_surjective π hπ
  exact ⟨d, π.comp ι, hg, hgf⟩

end TauCeti

/-- **Affinoid Noether normalisation through a presentation.** For a Tate presentation `π` of a
nonzero algebra there is a map `ι : K⟨Y₁, …, Y_d⟩ → K⟨X₁, …, Xₙ⟩` of Tate algebras, preserving
Gauss norms, such that `π ∘ ι` is finite and injective. -/
theorem AlgHom.exists_norm_eq_finite_injective_comp {K : Type*} [NormedField K]
    [IsUltrametricDist K] [CompleteSpace K] {σ : Type*} [_root_.Finite σ] {A : Type*} [CommRing A]
    [Algebra K A] [Nontrivial A]
    (π : MvPowerSeries.IsRestricted.subring (R := K) (fun _ : σ ↦ 1) →ₐ[K] A)
    (hπ : Function.Surjective π) :
    ∃ (n : ℕ) (ι : MvPowerSeries.IsRestricted.subring (R := K) (fun _ : Fin n ↦ 1) →ₐ[K]
        MvPowerSeries.IsRestricted.subring (R := K) (fun _ : σ ↦ 1)),
      (∀ x, ‖ι x‖ = ‖x‖) ∧ Function.Injective (π.comp ι) ∧ (π.comp ι).Finite :=
  TauCeti.exists_finite_injective_of_surjective π hπ

/-- **Affinoid Noether normalisation adapted to a presentation.** For a Tate presentation `π` of
a nonzero algebra, a finite injective map `g` from a Tate algebra can be chosen to send the
Gauss unit ball into the image under `π` of the Gauss unit ball. -/
theorem AlgHom.exists_finite_injective_map_unitClosedBall_le {K : Type*} [NormedField K]
    [IsUltrametricDist K] [CompleteSpace K] {σ : Type*} [_root_.Finite σ] {A : Type*} [CommRing A]
    [Algebra K A] [Nontrivial A]
    (π : MvPowerSeries.IsRestricted.subring (R := K) (fun _ : σ ↦ 1) →ₐ[K] A)
    (hπ : Function.Surjective π) :
    ∃ (n : ℕ) (g : MvPowerSeries.IsRestricted.subring (R := K) (fun _ : Fin n ↦ 1) →ₐ[K] A),
      Function.Injective g ∧ g.Finite ∧
        (Subring.unitClosedBall _).map g.toRingHom ≤
          (Subring.unitClosedBall _).map π.toRingHom := by
  obtain ⟨n, ι, hι, hg, hgf⟩ := π.exists_norm_eq_finite_injective_comp hπ
  refine ⟨n, π.comp ι, hg, hgf, ?_⟩
  rintro _ ⟨x, hx, rfl⟩
  exact ⟨ι x, Subring.mem_unitClosedBall.mpr ((hι x).trans_le (Subring.mem_unitClosedBall.mp hx)),
    rfl⟩

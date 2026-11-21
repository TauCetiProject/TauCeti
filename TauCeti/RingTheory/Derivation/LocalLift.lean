/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Derivation.Localization
public import TauCeti.RingTheory.Kaehler.Conormal
import Mathlib.Algebra.Module.FinitePresentation
import Mathlib.LinearAlgebra.Basis.VectorSpace

/-!
# Lifting local residue functionals to global derivations

Let `A` be a local localization of a `k`-algebra `R` at a submonoid `S`, with residue field `κ`.
When `Ω[R⁄k]` is finitely generated and projective over `R`, any `κ`-linear functional
`φ : κ ⊗[A] Ω[A⁄k] →ₗ[κ] κ` lifts via `Ω[R⁄k] →ₗ[R] A` (using projectivity of `Ω[R⁄k]`) and
denominator clearing (`Module.FinitePresentation.exists_lift_of_isLocalizedModule`) to a global
`k`-derivation `δ` of `R` and a denominator `s ∈ S` whose localization agrees modulo `𝔪_A` with
`s • φ ∘ (1 ⊗ d)`.

When `κ` is formally smooth over `k`, the tensors `1 ⊗ d(t j)` of a minimal generating set `t` of
`𝔪_A` are `κ`-linearly independent (`KaehlerDifferential.linearIndependent_tmul_D`). Dualizing
produces, for each coordinate `i`, a global derivation `δ` and denominator `s ∈ S` sending `t j` to
`s · δ_{ij}` modulo `𝔪_A`.

## Main results

* `Derivation.exists_derivation_residue_eq`: lifts a `κ`-linear functional on `κ ⊗[A] Ω[A⁄k]` to
  a global derivation of `R` up to a unit denominator `s ∈ S`;
* `Derivation.exists_dual_derivation`: constructs global derivations dual modulo `𝔪_A` to a
  minimal generating set of `𝔪_A`.
-/

public section

open IsLocalRing KaehlerDifferential TensorProduct

namespace Derivation

/-- Given a `κ`-linear functional `φ : κ ⊗[A] Ω[A⁄k] →ₗ[κ] κ` on a local localization `A` of a
`k`-algebra `R` with finitely generated projective `Ω[R⁄k]`, there exist `s ∈ S` and a global
`k`-derivation `δ : Derivation k R R` whose localization `D : Derivation k A A` satisfies
`residue A (D x) = residue A (algebraMap R A s) * φ (1 ⊗ d x)` for all `x : A`. -/
theorem exists_derivation_residue_eq {k R A : Type*} [CommRing k] [CommRing R] [CommRing A]
    [Algebra k R] [Algebra R A] [Algebra k A] [IsScalarTower k R A]
    [Module.Projective R Ω[R⁄k]] [Module.Finite R Ω[R⁄k]]
    (S : Submonoid R) [IsLocalization S A] [IsLocalRing A]
    (φ : ResidueField A ⊗[A] Ω[A⁄k] →ₗ[ResidueField A] ResidueField A) :
    ∃ (s : S) (δ : Derivation k R R),
      ∀ x : A,
        residue A ((((Algebra.linearMap R A).compDer δ).extendOfIsLocalization S) x) =
          residue A (algebraMap R A s) *
            φ ((1 : ResidueField A) ⊗ₜ[A] KaehlerDifferential.D k A x) := by
  set κ := ResidueField A
  have : Module.FinitePresentation R Ω[R⁄k] := Module.finitePresentation_of_projective R Ω[R⁄k]
  let f : Ω[R⁄k] →ₗ[R] κ :=
    ((φ.restrictScalars A).comp (TensorProduct.mk A κ Ω[A⁄k] 1)).restrictScalars R ∘ₗ
      KaehlerDifferential.map k k R A
  have hsurj : Function.Surjective (IsScalarTower.toAlgHom R A κ).toLinearMap :=
    fun y ↦ by simpa [κ, ResidueField.algebraMap_eq] using residue_surjective (R := A) y
  obtain ⟨fA, hfA⟩ :=
    Module.projective_lifting_property (IsScalarTower.toAlgHom R A κ).toLinearMap f hsurj
  obtain ⟨g, s, hg⟩ :=
    Module.FinitePresentation.exists_lift_of_isLocalizedModule S (Algebra.linearMap R A) fA
  let δ : Derivation k R R := g.compDer (KaehlerDifferential.D k R)
  let Dloc : Derivation k A A := ((Algebra.linearMap R A).compDer δ).extendOfIsLocalization S
  refine ⟨s, δ, fun x ↦ congrFun (IsLocalization.eq_of_leibniz (A := R) (T := A) (N := κ) S
    (δ₁ := fun x ↦ residue A (Dloc x))
    (δ₂ := fun x ↦ residue A (algebraMap R A s) * φ ((1 : κ) ⊗ₜ[A] KaehlerDifferential.D k A x))
    (fun x y ↦ by
      rw [Dloc.leibniz, map_add, smul_eq_mul, smul_eq_mul, map_mul, map_mul,
        Algebra.smul_def, Algebra.smul_def, ResidueField.algebraMap_eq])
    (fun x y ↦ by
      rw [(KaehlerDifferential.D k A).leibniz, TensorProduct.tmul_add, map_add, mul_add,
        TensorProduct.tmul_smul, TensorProduct.tmul_smul,
        ← algebraMap_smul κ x, ← algebraMap_smul κ y, φ.map_smul, φ.map_smul,
        smul_eq_mul, smul_eq_mul, Algebra.smul_def, Algebra.smul_def]
      ring)
    fun r ↦ ?_) x⟩
  have hfAr : residue A (fA (KaehlerDifferential.D k R r)) = f (KaehlerDifferential.D k R r) := by
    have h := LinearMap.congr_fun hfA (KaehlerDifferential.D k R r)
    simpa [κ, ResidueField.algebraMap_eq] using h
  have hgr : algebraMap R A (δ r) = algebraMap R A s * fA (KaehlerDifferential.D k R r) := by
    simpa [δ, Submonoid.smul_def, Algebra.smul_def] using
      LinearMap.congr_fun hg (KaehlerDifferential.D k R r)
  have hloc : Dloc (algebraMap R A r) = algebraMap R A (δ r) := by simp [Dloc]
  rw [hloc, hgr, map_mul, hfAr]
  dsimp only [f]
  rw [LinearMap.comp_apply, KaehlerDifferential.map_D]
  simp

/-- For a minimal system of generators `t : Fin r → A` of the maximal ideal of a local localization
`A` of `R` (with `Ω[R⁄k]` finite projective and `κ` formally smooth over `k`), each coordinate `i`
admits a global derivation `δ` and a denominator `s ∈ S` such that the localization `D` of `δ`
sends `t j` to `s · δ_{ij}` modulo `𝔪_A`. -/
theorem exists_dual_derivation {k R A : Type*} [CommRing k] [CommRing R] [CommRing A]
    [Algebra k R] [Algebra R A] [Algebra k A] [IsScalarTower k R A]
    [Module.Projective R Ω[R⁄k]] [Module.Finite R Ω[R⁄k]]
    (S : Submonoid R) [IsLocalization S A] [IsLocalRing A]
    [Algebra.FormallySmooth k (ResidueField A)]
    {r : ℕ} {t : Fin r → A} (ht : Ideal.span (Set.range t) = maximalIdeal A)
    (hr : (maximalIdeal A).spanFinrank = r) (i : Fin r) :
    ∃ (s : S) (δ : Derivation k R R),
      ∀ j : Fin r,
        residue A ((((Algebra.linearMap R A).compDer δ).extendOfIsLocalization S) (t j)) =
          if j = i then residue A (algebraMap R A s) else 0 := by
  classical
  let b := Module.Basis.span (linearIndependent_tmul_D (k := k) ht hr)
  obtain ⟨φ, hφ⟩ := (b.coord i).exists_extend
  obtain ⟨s, δ, hδ⟩ := exists_derivation_residue_eq (k := k) S φ
  refine ⟨s, δ, fun j ↦ ?_⟩
  have hbj : φ (b j) = if j = i then 1 else 0 := by
    have := LinearMap.congr_fun hφ (b j)
    simpa [Finsupp.single_apply] using this
  have hval : (b j : ResidueField A ⊗[A] Ω[A⁄k]) =
      (1 : ResidueField A) ⊗ₜ[A] KaehlerDifferential.D k A (t j) := by
    simp [b, Module.Basis.span_apply]
  rw [hδ (t j), ← hval, hbj]
  split_ifs <;> simp

end Derivation

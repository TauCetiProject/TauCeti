/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Smooth.Basic
public import TauCeti.RingTheory.Ideal.FixedPoints

/-!
# Smoothness of tame fixed-point quotients

Let `A` be a formally smooth (resp. smooth) commutative `R`-algebra equipped with an action of a
group `Γ` by `R`-algebra endomorphisms `ρ : Γ → F`, such that the order `Nat.card Γ` is a unit in
`R`. Edixhoven's tame fixed-point theorem states that the fixed-point quotient
`A ⧸ TauCeti.fixedPointsIdeal ρ` is again formally smooth (resp. smooth) over `R`.

Note that `[Finite Γ]` is not needed as a separate hypothesis: when `R` is nontrivial, invertibility
of `(Nat.card Γ : R)` implies `Nat.card Γ ≠ 0` and hence `Finite Γ`; when `R` is subsingleton,
every `R`-algebra is subsingleton and therefore smooth.

The proof of formal smoothness follows Edixhoven's averaging argument: given an infinitesimal
lifting problem into a square-zero thickening `B ↠ B ⧸ J`, one lifts the `Γ`-invariant map
`A →ₐ[R] B ⧸ J` to an arbitrary `h₀ : A →ₐ[R] B` using formal smoothness of `A`, and replaces
`h₀` by its `Γ`-average `a ↦ |Γ|⁻¹ • ∑ γ, h₀ (ρ γ a)`. Because the differences
`d_γ a = h₀ (ρ γ a) - h₀ a` lie in the square-zero ideal `J`, each `d_γ` is a derivation along
`h₀`, so the average `h₀ + |Γ|⁻¹ • ∑ γ, d_γ` remains an `R`-algebra homomorphism, still lifts the
given map modulo `J`, and is `Γ`-invariant; it therefore factors through the fixed-point quotient.

## Main results

* `Algebra.FormallySmooth.quotient_fixedPointsIdeal`: formal smoothness of the fixed-point
  quotient of a formally smooth algebra under a group action of invertible order.
* `Algebra.Smooth.quotient_fixedPointsIdeal`: smoothness of the fixed-point quotient of a smooth
  algebra under a group action of invertible order.

## References

* B. Edixhoven, *Néron models and tame ramification*, Compositio Math. 81 (1992), Proposition 3.4,
  pp. 294–295.
-/

public section

namespace Algebra

section Helpers

private theorem smooth_of_subsingleton {R A : Type*} [CommRing R] [Subsingleton R]
    [CommRing A] [Algebra R A] : Smooth R A := by
  have : Subsingleton A := Module.subsingleton R A
  let e : R ≃ₐ[R] A :=
    { Algebra.ofId R A with
      invFun := fun _ ↦ 0
      left_inv := fun _ ↦ Subsingleton.elim _ _
      right_inv := fun _ ↦ Subsingleton.elim _ _ }
  have : Smooth R R := ⟨inferInstance, FinitePresentation.self R⟩
  exact Smooth.of_equiv e

private theorem finite_of_isUnit_natCard {R Γ : Type*} [CommRing R] [Nontrivial R]
    (hΓ : IsUnit (Nat.card Γ : R)) : Finite Γ := by
  refine Nat.finite_of_card_ne_zero fun h0 ↦ ?_
  rw [h0, Nat.cast_zero] at hΓ
  exact not_isUnit_zero hΓ

/-- Given a lift `h₀ : A →ₐ[R] B` of a `Γ`-invariant homomorphism modulo a square-zero ideal `J`,
averaging `h₀ ∘ ρ γ` over `Γ` produces a `Γ`-invariant algebra homomorphism lifting the same map. -/
private noncomputable def averageLift {R A B Γ F : Type*} [CommRing R] [CommRing A] [Algebra R A]
    [CommRing B] [Algebra R B] [Fintype Γ] [FunLike F A A] [AlgHomClass F R A A]
    (ρ : Γ → F) (J : Ideal B) (hJ : J ^ 2 = ⊥) (u : Rˣ)
    (h₀ : A →ₐ[R] B) (hdiff : ∀ γ a, h₀ (ρ γ a) - h₀ a ∈ J) : A →ₐ[R] B :=
  let d : Γ → A → B := fun γ a ↦ h₀ (ρ γ a) - h₀ a
  let δ : A → B := fun a ↦ (↑u⁻¹ : R) • ∑ γ : Γ, d γ a
  have hδ_mem : ∀ a, δ a ∈ J := fun a ↦ by
    dsimp only [δ]
    rw [Algebra.smul_def]
    exact Ideal.mul_mem_left J _ (Submodule.sum_mem J fun γ _ ↦ hdiff γ a)
  have hsq : ∀ {x y : B}, x ∈ J → y ∈ J → x * y = 0 := fun hx hy ↦
    Ideal.mem_bot.mp (hJ ▸ (pow_two J ▸ Ideal.mul_mem_mul hx hy))
  have hd_mul : ∀ γ a b, d γ (a * b) = h₀ a * d γ b + d γ a * h₀ b := fun γ a b ↦ by
    have hzero : d γ a * d γ b = 0 := hsq (hdiff γ a) (hdiff γ b)
    calc
      d γ (a * b) = h₀ (ρ γ a) * h₀ (ρ γ b) - h₀ a * h₀ b := by simp [d]
      _ = (h₀ a + d γ a) * (h₀ b + d γ b) - h₀ a * h₀ b := by simp [d]
      _ = h₀ a * d γ b + d γ a * h₀ b + d γ a * d γ b := by ring
      _ = h₀ a * d γ b + d γ a * h₀ b := by rw [hzero, add_zero]
  have hδ_mul : ∀ a b, δ (a * b) = h₀ a * δ b + δ a * h₀ b := fun a b ↦ by
    simp only [δ, hd_mul, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul,
      smul_add, smul_mul_assoc, mul_smul_comm]
  { toFun := fun a ↦ h₀ a + δ a
    map_one' := by
      have h1 : δ 1 = 0 := by simp [δ, d]
      rw [h1, add_zero, map_one]
    map_mul' := fun a b ↦ by
      have hzero : δ a * δ b = 0 := hsq (hδ_mem a) (hδ_mem b)
      calc
        h₀ (a * b) + δ (a * b) = h₀ a * h₀ b + (h₀ a * δ b + δ a * h₀ b) := by
          rw [map_mul, hδ_mul]
        _ = (h₀ a + δ a) * (h₀ b + δ b) - δ a * δ b := by ring
        _ = (h₀ a + δ a) * (h₀ b + δ b) := by rw [hzero, sub_zero]
    map_zero' := by
      have h0 : δ 0 = 0 := by simp [δ, d]
      rw [h0, add_zero, map_zero]
    map_add' := fun a b ↦ by
      have hadd : δ (a + b) = δ a + δ b := by
        simp only [δ, d, map_add]
        have hsub : ∀ γ : Γ, h₀ (ρ γ a) + h₀ (ρ γ b) - (h₀ a + h₀ b) =
            (h₀ (ρ γ a) - h₀ a) + (h₀ (ρ γ b) - h₀ b) := fun _ ↦ by ring
        simp_rw [hsub, Finset.sum_add_distrib, smul_add]
      rw [map_add, hadd]
      ring
    commutes' := fun r ↦ by
      have hr : δ (algebraMap R A r) = 0 := by
        simp [δ, d, AlgHomClass.commutes]
      rw [hr, add_zero, AlgHom.commutes] }

private theorem averageLift_apply_eq_sum {R A B Γ F : Type*} [CommRing R] [CommRing A]
    [Algebra R A] [CommRing B] [Algebra R B] [Fintype Γ] [FunLike F A A]
    [AlgHomClass F R A A] (ρ : Γ → F) (J : Ideal B) (hJ : J ^ 2 = ⊥) (u : Rˣ)
    (hu : (u : R) = Fintype.card Γ) (h₀ : A →ₐ[R] B) (hdiff : ∀ γ a, h₀ (ρ γ a) - h₀ a ∈ J)
    (a : A) :
    averageLift ρ J hJ u h₀ hdiff a = (↑u⁻¹ : R) • ∑ γ : Γ, h₀ (ρ γ a) := by
  have hcard : (↑u⁻¹ : R) • ((Fintype.card Γ : R) • h₀ a) = h₀ a := by
    rw [← mul_smul, ← hu, Units.inv_mul, one_smul]
  simp only [averageLift, AlgHom.coe_mk, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk,
    Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, ← Nat.cast_smul_eq_nsmul R,
    smul_sub, hcard, add_sub_cancel]

private theorem mk_averageLift {R A B Γ F : Type*} [CommRing R] [CommRing A] [Algebra R A]
    [CommRing B] [Algebra R B] [Fintype Γ] [FunLike F A A] [AlgHomClass F R A A]
    (ρ : Γ → F) (J : Ideal B) (hJ : J ^ 2 = ⊥) (u : Rˣ)
    (h₀ : A →ₐ[R] B) (hdiff : ∀ γ a, h₀ (ρ γ a) - h₀ a ∈ J) (a : A) :
    Ideal.Quotient.mkₐ R J (averageLift ρ J hJ u h₀ hdiff a) =
      Ideal.Quotient.mkₐ R J (h₀ a) := by
  have hmem : (↑u⁻¹ : R) • ∑ γ : Γ, (h₀ (ρ γ a) - h₀ a) ∈ J := by
    rw [Algebra.smul_def]
    exact Ideal.mul_mem_left J _ (Submodule.sum_mem J fun γ _ ↦ hdiff γ a)
  have hzero : Ideal.Quotient.mkₐ R J ((↑u⁻¹ : R) • ∑ γ : Γ, (h₀ (ρ γ a) - h₀ a)) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr hmem
  simp only [averageLift, AlgHom.coe_mk, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk,
    map_add, hzero, add_zero]

end Helpers

namespace FormallySmooth

/-- **Edixhoven's tame fixed-point theorem (formal smoothness).** Let `A` be a formally smooth
commutative `R`-algebra and let a group `Γ` act on `A` by `R`-algebra endomorphisms `ρ` with
`ρ (γ * τ) a = ρ γ (ρ τ a)`. If `Nat.card Γ` is a unit in `R`, then the fixed-point quotient
`A ⧸ TauCeti.fixedPointsIdeal ρ` is formally smooth over `R`. -/
theorem quotient_fixedPointsIdeal {R A Γ F : Type*} [CommRing R] [CommRing A] [Algebra R A]
    [FormallySmooth R A] [Group Γ] [FunLike F A A] [AlgHomClass F R A A]
    (ρ : Γ → F) (hρ : ∀ γ τ a, ρ (γ * τ) a = ρ γ (ρ τ a))
    (hΓ : IsUnit (Nat.card Γ : R)) :
    FormallySmooth R (A ⧸ TauCeti.fixedPointsIdeal ρ) := by
  rcases subsingleton_or_nontrivial R with hsub | hnt
  · exact (smooth_of_subsingleton (R := R) (A := A ⧸ TauCeti.fixedPointsIdeal ρ)).formallySmooth
  · have : Finite Γ := finite_of_isUnit_natCard hΓ
    let _ : Fintype Γ := Fintype.ofFinite Γ
    obtain ⟨u, hu⟩ := hΓ
    rw [Nat.card_eq_fintype_card] at hu
    refine of_comp_surjective fun B _ _ J hJ g₀ ↦ ?_
    let g : A →ₐ[R] B ⧸ J := g₀.comp (Ideal.Quotient.mkₐ R (TauCeti.fixedPointsIdeal ρ))
    have hg : ∀ γ a, g (ρ γ a) = g a := by
      simpa only [TauCeti.quotientFixedPointsAlgHomEquiv_apply] using
        (TauCeti.quotientFixedPointsAlgHomEquiv ρ g₀).2
    obtain ⟨h₀, hh₀⟩ := comp_surjective R A J hJ g
    have hdiff : ∀ γ a, h₀ (ρ γ a) - h₀ a ∈ J := fun γ a ↦ by
      rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub]
      have h1 : Ideal.Quotient.mk J (h₀ (ρ γ a)) = g (ρ γ a) := AlgHom.congr_fun hh₀ (ρ γ a)
      have h2 : Ideal.Quotient.mk J (h₀ a) = g a := AlgHom.congr_fun hh₀ a
      rw [h1, h2, hg γ a, sub_self]
    let h : A →ₐ[R] B := averageLift ρ J hJ u h₀ hdiff
    have hinv : ∀ τ a, h (ρ τ a) = h a := fun τ a ↦ by
      rw [averageLift_apply_eq_sum (hu := hu), averageLift_apply_eq_sum (hu := hu)]
      congr 1
      have hcomp : ∀ γ : Γ, h₀ (ρ γ (ρ τ a)) = h₀ (ρ (γ * τ) a) := fun γ ↦ by rw [hρ γ τ a]
      simp_rw [hcomp]
      exact Equiv.sum_comp (Equiv.mulRight τ) (fun γ ↦ h₀ (ρ γ a))
    refine ⟨(TauCeti.quotientFixedPointsAlgHomEquiv ρ).symm ⟨h, hinv⟩, ?_⟩
    ext x
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [AlgHom.comp_apply, TauCeti.quotientFixedPointsAlgHomEquiv_symm_apply_mk,
      mk_averageLift, ← AlgHom.comp_apply, hh₀]
    rfl

end FormallySmooth

namespace Smooth

/-- **Edixhoven's tame fixed-point theorem.** Let `A` be a smooth commutative `R`-algebra and let
a group `Γ` act on `A` by `R`-algebra endomorphisms `ρ` with `ρ (γ * τ) a = ρ γ (ρ τ a)`. If
`Nat.card Γ` is a unit in `R`, then the fixed-point quotient `A ⧸ TauCeti.fixedPointsIdeal ρ` is
smooth over `R`. -/
theorem quotient_fixedPointsIdeal {R A Γ F : Type*} [CommRing R] [CommRing A] [Algebra R A]
    [Smooth R A] [Group Γ] [FunLike F A A] [AlgHomClass F R A A]
    (ρ : Γ → F) (hρ : ∀ γ τ a, ρ (γ * τ) a = ρ γ (ρ τ a))
    (hΓ : IsUnit (Nat.card Γ : R)) :
    Smooth R (A ⧸ TauCeti.fixedPointsIdeal ρ) := by
  rcases subsingleton_or_nontrivial R with hsub | hnt
  · exact smooth_of_subsingleton
  · have : Finite Γ := finite_of_isUnit_natCard hΓ
    exact ⟨FormallySmooth.quotient_fixedPointsIdeal ρ hρ hΓ,
      TauCeti.finitePresentation_quotient_fixedPointsIdeal (R := R) ρ⟩

end Smooth

end Algebra

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Kaehler.Conormal
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.MvPolynomial.Basic
public import Mathlib.Algebra.Polynomial.AlgebraMap

/-!
# Checks: the conormal map at a rational point needs no Noetherian hypothesis

Tau Ceti's `KaehlerDifferential.kerCotangentToTensor_bijective_of_formallyEtale` identifies the
conormal module `I/I²` of a surjection `P → S` onto a formally étale `k`-algebra with
`S ⊗[P] Ω[P⁄k]`, with no Noetherian hypothesis on `P`. At a `k`-rational point it identifies the
cotangent space `𝔪/𝔪²` of the local ring with the fibre `κ ⊗[R] Ω[R⁄k]` of the differentials:

* for a `k`-algebra `A` with a `k`-point `φ : A →ₐ[k] k`, the local ring `R = A_𝔭` at
  `𝔭 = ker φ` has residue field `k` (`bijective_algebraMap_residueField`), so its conormal map
  `𝔪/𝔪² → κ ⊗[R] Ω[R⁄k]` is bijective (`bijective_kerCotangentToTensor_residueField`), and it
  sends the class of `a ∈ 𝔭` to `1 ⊗ da` (`kerCotangentToTensor_toCotangent_algebraMap`);
* for `R = k`, both sides are zero (`subsingleton_cotangent_self`,
  `subsingleton_tensor_self`);
* for `R = k[x]_(x)` the class of `x`, which spans `𝔪/𝔪²`, maps to `1 ⊗ dx`
  (`polynomial_span_toCotangent_X`, `polynomial_kerCotangentToTensor_X`);
* for the non-Noetherian `R = k[x₀, x₁, …]` localized at `(x₀, x₁, …)` the conormal map is still
  bijective (`mvPolynomial_bijective_kerCotangentToTensor`), sending the class of `xᵢ` to
  `1 ⊗ dxᵢ` (`mvPolynomial_kerCotangentToTensor_X`).

The Stacks Project, Lemma 10.140.4 (Tag 00TU), states injectivity for Noetherian rings only.
-/

public section

noncomputable section

open KaehlerDifferential IsLocalRing TensorProduct

namespace TauCeti.ConormalRationalPointExample

variable {k : Type*} [Field k]

section RationalPoint

variable {A : Type*} [CommRing A] [Algebra k A] (φ : A →ₐ[k] k)

/-- The prime ideal `𝔭 = ker φ` of a `k`-point `φ` of `A`. -/
abbrev pointIdeal : Ideal A :=
  RingHom.ker (φ : A →+* k)

/-- The kernel of a `k`-point is prime. -/
instance isPrime_pointIdeal : (pointIdeal φ).IsPrime :=
  RingHom.ker_isPrime _

/-- The local ring `A_𝔭` at the `k`-point `φ`. -/
abbrev LocalRingAt : Type _ :=
  Localization.AtPrime (pointIdeal φ)

/-- The residue map of `A_𝔭` on `a ∈ A` is the value `φ a`. -/
theorem residue_algebraMap (a : A) :
    residue (LocalRingAt φ) (algebraMap A (LocalRingAt φ) a) =
      algebraMap k (ResidueField (LocalRingAt φ)) (φ a) := by
  have h : algebraMap A (LocalRingAt φ) a - algebraMap k (LocalRingAt φ) (φ a) ∈
      maximalIdeal (LocalRingAt φ) := by
    rw [IsScalarTower.algebraMap_apply k A (LocalRingAt φ), ← map_sub,
      ← Localization.AtPrime.map_eq_maximalIdeal]
    exact Ideal.mem_map_of_mem _ (by simp [RingHom.mem_ker])
  rw [← sub_eq_zero, IsScalarTower.algebraMap_apply k (LocalRingAt φ) (ResidueField _),
    ResidueField.algebraMap_eq, ← map_sub, residue_eq_zero_iff]
  exact h

/-- **The residue field of `A_𝔭` is `k`.** -/
theorem bijective_algebraMap_residueField :
    Function.Bijective (algebraMap k (ResidueField (LocalRingAt φ))) := by
  refine ⟨(algebraMap k _).injective, fun y ↦ ?_⟩
  obtain ⟨z, rfl⟩ := residue_surjective y
  obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective (pointIdeal φ).primeCompl z
  dsimp only
  have hs : φ s ≠ 0 := s.property
  refine ⟨φ a / φ s, ?_⟩
  rw [map_div₀, div_eq_iff ((map_ne_zero _).mpr hs), ← residue_algebraMap φ s,
    ← residue_algebraMap φ a, ← map_mul, IsLocalization.mk'_spec]

/-- The residue field of `A_𝔭` is formally étale over `k`. -/
instance formallyEtale_residueField : Algebra.FormallyEtale k (ResidueField (LocalRingAt φ)) :=
  .of_equiv (AlgEquiv.ofBijective (Algebra.ofId k _) (bijective_algebraMap_residueField φ))

/-- **The conormal map at a rational point is bijective.** For the local ring `R = A_𝔭` at a
`k`-point, `𝔪/𝔪² → κ ⊗[R] Ω[R⁄k]` is bijective, with no Noetherian hypothesis on `A`. -/
theorem bijective_kerCotangentToTensor_residueField :
    Function.Bijective
      (kerCotangentToTensor k (LocalRingAt φ) (ResidueField (LocalRingAt φ))) :=
  kerCotangentToTensor_bijective_of_formallyEtale residue_surjective

/-- `𝔪 = 𝔭 A_𝔭`: an element of `𝔭` lies in the kernel of the residue map. -/
theorem algebraMap_mem_ker {a : A} (ha : a ∈ pointIdeal φ) :
    algebraMap A (LocalRingAt φ) a ∈
      RingHom.ker (algebraMap (LocalRingAt φ) (ResidueField (LocalRingAt φ))) := by
  have h : φ a = 0 := RingHom.mem_ker.mp ha
  rw [RingHom.mem_ker, ResidueField.algebraMap_eq, residue_algebraMap, h, map_zero]

/-- The conormal map sends the class of `a ∈ 𝔭` to `1 ⊗ da`. -/
theorem kerCotangentToTensor_toCotangent_algebraMap {a : A} (ha : a ∈ pointIdeal φ) :
    kerCotangentToTensor k (LocalRingAt φ) (ResidueField (LocalRingAt φ))
        ((RingHom.ker _).toCotangent ⟨_, algebraMap_mem_ker φ ha⟩) =
      1 ⊗ₜ D k (LocalRingAt φ) (algebraMap A (LocalRingAt φ) a) :=
  kerCotangentToTensor_toCotangent _ _ _ _

end RationalPoint

section Field

/-- For `R = k` the conormal module is zero. -/
theorem subsingleton_cotangent_self :
    Subsingleton (RingHom.ker (algebraMap k (ResidueField k))).Cotangent := by
  have h (x : RingHom.ker (algebraMap k (ResidueField k))) : x = 0 :=
    Subtype.ext ((map_eq_zero_iff _ (algebraMap k _).injective).mp (RingHom.mem_ker.mp x.property))
  refine ⟨fun x y ↦ ?_⟩
  obtain ⟨x, rfl⟩ := Ideal.toCotangent_surjective _ x
  obtain ⟨y, rfl⟩ := Ideal.toCotangent_surjective _ y
  rw [h x, h y]

/-- For `R = k` the fibre of the differentials is zero. -/
theorem subsingleton_tensor_self : Subsingleton (ResidueField k ⊗[k] Ω[k⁄k]) :=
  inferInstance

end Field

section Polynomial

open Polynomial

/-- The `k`-point `x ↦ 0` of `k[x]`. -/
abbrev evalZero : k[X] →ₐ[k] k :=
  Polynomial.aeval 0

/-- `x` lies in the kernel of `x ↦ 0`. -/
theorem X_mem_pointIdeal : (X : k[X]) ∈ pointIdeal (evalZero (k := k)) := by
  simp [RingHom.mem_ker]

/-- For `R = k[x]_(x)`, the conormal map sends the class of `x` to `1 ⊗ dx`. -/
theorem polynomial_kerCotangentToTensor_X :
    kerCotangentToTensor k (LocalRingAt (evalZero (k := k)))
        (ResidueField (LocalRingAt (evalZero (k := k))))
        ((RingHom.ker _).toCotangent ⟨_, algebraMap_mem_ker _ X_mem_pointIdeal⟩) =
      1 ⊗ₜ D k _ (algebraMap k[X] (LocalRingAt (evalZero (k := k))) X) :=
  kerCotangentToTensor_toCotangent_algebraMap _ X_mem_pointIdeal

/-- For `R = k[x]_(x)`, the class of `x` spans `𝔪/𝔪²`. -/
theorem polynomial_span_toCotangent_X :
    Submodule.span (LocalRingAt (evalZero (k := k)))
        {(RingHom.ker (algebraMap _ (ResidueField (LocalRingAt (evalZero (k := k)))))).toCotangent
          ⟨_, algebraMap_mem_ker _ X_mem_pointIdeal⟩} = ⊤ := by
  have hI : pointIdeal (evalZero (k := k)) = Ideal.span {X} := by
    change RingHom.ker (evalRingHom (0 : k)) = _
    rw [ker_evalRingHom, map_zero, sub_zero]
  have hle : Ideal.map (algebraMap k[X] (LocalRingAt (evalZero (k := k))))
      (pointIdeal evalZero) ≤ Ideal.span {algebraMap k[X] _ X} := by
    rw [Ideal.map_le_iff_le_comap]
    intro a ha
    rw [hI, Ideal.mem_span_singleton'] at ha
    obtain ⟨b, rfl⟩ := ha
    rw [Ideal.mem_comap, map_mul]
    exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)
  refine eq_top_iff.mpr fun c _ ↦ ?_
  obtain ⟨c, rfl⟩ := Ideal.toCotangent_surjective _ c
  have hc : (c : LocalRingAt (evalZero (k := k))) ∈ maximalIdeal _ := by
    rw [← residue_eq_zero_iff, ← ResidueField.algebraMap_eq]
    exact c.property
  rw [← Localization.AtPrime.map_eq_maximalIdeal] at hc
  have hc := hle hc
  rw [Ideal.mem_span_singleton'] at hc
  obtain ⟨r, hr⟩ := hc
  have hcr : c = r • ⟨_, algebraMap_mem_ker _ X_mem_pointIdeal⟩ :=
    Subtype.ext (by rw [Submodule.coe_smul, smul_eq_mul]; exact hr.symm)
  rw [hcr, map_smul]
  exact Submodule.smul_mem _ _ (Submodule.subset_span rfl)

end Polynomial

section MvPolynomial

/-- The `k`-point `0` of `k[x₀, x₁, …]`. -/
abbrev mvEvalZero : MvPolynomial ℕ k →ₐ[k] k :=
  MvPolynomial.aeval 0

/-- Each `xᵢ` lies in the kernel of the point `0`. -/
theorem mvPolynomial_X_mem_pointIdeal (i : ℕ) :
    MvPolynomial.X i ∈ pointIdeal (mvEvalZero (k := k)) := by
  simp [RingHom.mem_ker]

/-- For `R = k[x₀, x₁, …]` localized at `(x₀, x₁, …)`, which is not Noetherian, the conormal map is
bijective. -/
theorem mvPolynomial_bijective_kerCotangentToTensor :
    Function.Bijective (kerCotangentToTensor k (LocalRingAt (mvEvalZero (k := k)))
      (ResidueField (LocalRingAt (mvEvalZero (k := k))))) :=
  bijective_kerCotangentToTensor_residueField _

/-- For `R = k[x₀, x₁, …]` localized at `(x₀, x₁, …)`, the conormal map sends the class of `xᵢ`
to `1 ⊗ dxᵢ`. -/
theorem mvPolynomial_kerCotangentToTensor_X (i : ℕ) :
    kerCotangentToTensor k (LocalRingAt (mvEvalZero (k := k)))
        (ResidueField (LocalRingAt (mvEvalZero (k := k))))
        ((RingHom.ker _).toCotangent ⟨_, algebraMap_mem_ker _ (mvPolynomial_X_mem_pointIdeal i)⟩) =
      1 ⊗ₜ D k _ (algebraMap (MvPolynomial ℕ k) (LocalRingAt (mvEvalZero (k := k)))
        (MvPolynomial.X i)) :=
  kerCotangentToTensor_toCotangent_algebraMap _ (mvPolynomial_X_mem_pointIdeal i)

end MvPolynomial

end TauCeti.ConormalRationalPointExample

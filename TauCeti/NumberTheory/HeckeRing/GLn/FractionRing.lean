/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.RingTheory.Ideal.Quotient.HasFiniteQuotients.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public import TauCeti.NumberTheory.HeckeRing.Associativity

import Mathlib.Tactic.Group
import TauCeti.GroupTheory.Commensurable
import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Map
import TauCeti.RingTheory.Localization.IntegerMultiple

/-!
# The Hecke pair `(GL_n(K), GL_n(R))` for the fraction field `K` of `R`

Let `R` be a domain with fraction field `K`. The integral points `GL_ι(R)` form a subgroup of
`GL_ι(K)` (`HeckeRing.GLn.integralGL R K ι`), the image of `Matrix.GeneralLinearGroup.map`.
When every quotient of `R` by a nonzero ideal is finite (`Ring.HasFiniteQuotients R`), as for the
valuation ring of a nonarchimedean local field, **every element of `GL_ι(K)` commensurates
`GL_ι(R)`** (`HeckeRing.GLn.commensurator_integralGL_eq_top`), so `(⊤, GL_ι(R))` is a Hecke pair
and `𝕋 ⊤ (integralGL R K ι) S` is the local Hecke ring `H(GL_ι(K), GL_ι(R))` over any coefficient
semiring `S`. For a nonarchimedean local field `L` with valuation ring `O_L` this is the spherical
Hecke ring `H(GL_n(L), GL_n(O_L))`. The cases `ℤ ⊂ ℚ` and `ℤ_p ⊂ ℚ_p`,
`HeckeRing.GLn.commensurator_GLnZ_eq_top` and `HeckeRing.GLn.commensurator_glPadicInt_eq_top`,
are derived from this one.

The proof is the usual congruence argument. For `g ∈ GL_ι(K)` clear denominators, `b g = A` and
`c g⁻¹ = B` with `A`, `B` integral and `b, c ∈ R` nonzero. If `γ ∈ GL_ι(R)` is congruent to `1`
modulo `b c`, say `γ = 1 + b c C`, then `g⁻¹ γ g = 1 + B C A` is integral with unit determinant,
so it lies in `GL_ι(R)`. The congruence subgroup of level `b c` is the kernel of reduction to the
finite group `GL_ι(R ⧸ (b c))`, so it has finite index in `GL_ι(R)`, and it lies in
`g GL_ι(R) g⁻¹`. By `Subgroup.Commensurable.commensurator_eq_top_iff` this suffices.

## Main definitions

* `HeckeRing.GLn.integralGL R K ι`: the subgroup `GL_ι(R)` of `GL_ι(K)`.

## Main results

* `HeckeRing.GLn.mem_integralGL_iff`: `g ∈ GL_ι(R)` exactly when `g` is the image of an integral
  matrix with unit determinant.
* `HeckeRing.GLn.inv_mul_map_mul_mem_integralGL_of_map_eq`: a conjugate `g⁻¹ γ g` of
  `γ ∈ GL_ι(R)` with integral entries lies in `GL_ι(R)`, since its determinant is that of `γ`
  (`HeckeRing.GLn.det_inv_mul_map_mul`).
* `HeckeRing.GLn.commensurator_integralGL_eq_top`: the commensurator of `GL_ι(R)` in `GL_ι(K)` is
  the whole group.
* the `IsHeckeTriple` instance for `(⊤, GL_ι(R))`.

## References

* [G. Shimura, *Introduction to the arithmetic theory of automorphic functions*][shimura1971],
  §3.1.
* I. G. Macdonald, *Spherical Functions on a Group of p-adic Type*, Ramanujan Institute (1971),
  Chapter V.
-/

public section

open Matrix Subgroup Subgroup.Commensurable
open scoped Pointwise

namespace HeckeRing.GLn

variable (R K : Type*) [CommRing R] [Field K] [Algebra R K] (ι : Type*) [Fintype ι]
  [DecidableEq ι]

/-- The integral points `GL_ι(R)` inside `GL_ι(K)`: the image of the entrywise map
`GL_ι(R) → GL_ι(K)`. For the valuation ring `R` of a nonarchimedean local field `K` this is the
maximal compact subgroup `GL_ι(O_K)` that defines the spherical Hecke ring. It is the subgroup
used by the Cartan decomposition `TauCeti.existsUnique_monotone_mem_doubleCoset_diagGL_zpow`. -/
abbrev integralGL : Subgroup (GL ι K) :=
  (GeneralLinearGroup.map (n := ι) (algebraMap R K)).range

variable {R K ι}

/-- An invertible matrix over `K` lies in `GL_ι(R)` exactly when it is the image of a matrix over
`R` whose determinant is a unit of `R`. -/
theorem mem_integralGL_iff {g : GL ι K} :
    g ∈ integralGL R K ι ↔
      ∃ A : Matrix ι ι R, IsUnit A.det ∧ A.map (algebraMap R K) = g := by
  constructor
  · rintro ⟨k, rfl⟩
    exact ⟨k, isUnits_det_units k, rfl⟩
  · rintro ⟨A, hA, hAg⟩
    exact ⟨GeneralLinearGroup.mk'' A hA, Units.ext hAg⟩

/-- When `R → K` is injective, an invertible matrix over `K` whose determinant is the image of a
unit of `R` lies in `GL_ι(R)` as soon as its entries lie in `R`. -/
theorem mem_integralGL_of_map_eq (hinj : Function.Injective (algebraMap R K)) {g : GL ι K}
    {A : Matrix ι ι R} (hA : A.map (algebraMap R K) = g) {u : Rˣ}
    (hdet : (g : Matrix ι ι K).det = algebraMap R K u) : g ∈ integralGL R K ι := by
  refine mem_integralGL_iff.mpr ⟨A, ?_, hA⟩
  have h : algebraMap R K A.det = algebraMap R K u := by
    rw [RingHom.map_det, RingHom.mapMatrix_apply, hA, hdet]
  rw [hinj h]
  exact u.isUnit

/-- The determinant of an element of `GL_ι(R)` is the image of a unit of `R`. -/
theorem exists_det_eq_algebraMap_of_mem_integralGL {g : GL ι K} (hg : g ∈ integralGL R K ι) :
    ∃ u : Rˣ, (g : Matrix ι ι K).det = algebraMap R K u := by
  obtain ⟨k, rfl⟩ := hg
  refine ⟨GeneralLinearGroup.det k, ?_⟩
  rw [GeneralLinearGroup.val_det_apply, RingHom.map_det, GeneralLinearGroup.val_map_apply,
    RingHom.mapMatrix_apply]

/-- The determinant of a conjugate `g⁻¹ γ g` of an element `γ` of `GL_ι(R)` by `g ∈ GL_ι(K)` is
the image of the determinant of `γ`. -/
theorem det_inv_mul_map_mul (g : GL ι K) (γ : GL ι R) :
    ((g⁻¹ * GeneralLinearGroup.map (algebraMap R K) γ * g : GL ι K) : Matrix ι ι K).det =
      algebraMap R K (GeneralLinearGroup.det γ : R) := by
  rw [← GeneralLinearGroup.val_det_apply, map_mul, map_mul, mul_right_comm, map_inv,
    inv_mul_cancel, one_mul, GeneralLinearGroup.val_det_apply, GeneralLinearGroup.val_map_apply,
    GeneralLinearGroup.val_det_apply, RingHom.map_det, RingHom.mapMatrix_apply]

/-- When `R → K` is injective, a conjugate `g⁻¹ γ g` of an element `γ` of `GL_ι(R)` lies in
`GL_ι(R)` as soon as its entries lie in `R`. -/
theorem inv_mul_map_mul_mem_integralGL_of_map_eq (hinj : Function.Injective (algebraMap R K))
    {g : GL ι K} {γ : GL ι R} {A : Matrix ι ι R}
    (hA : A.map (algebraMap R K) = ↑(g⁻¹ * GeneralLinearGroup.map (algebraMap R K) γ * g)) :
    g⁻¹ * GeneralLinearGroup.map (algebraMap R K) γ * g ∈ integralGL R K ι :=
  mem_integralGL_of_map_eq hinj hA (det_inv_mul_map_mul g γ)

section Commensurator

variable [IsFractionRing R K]

/-- **The conjugation step.** If `b g` and `c g⁻¹` are integral and `γ ∈ GL_ι(R)` is congruent to
`1` modulo `b c`, then `g⁻¹ γ g` lies in `GL_ι(R)`. -/
private theorem inv_mul_map_mul_mem_integralGL {g : GL ι K} {b c : R} {A B : Matrix ι ι R}
    (hA : A.map (algebraMap R K) = b • (g : Matrix ι ι K))
    (hB : B.map (algebraMap R K) = c • (↑g⁻¹ : Matrix ι ι K)) {γ : GL ι R}
    (hγ : γ ∈ (GeneralLinearGroup.map (n := ι) (Ideal.Quotient.mk (Ideal.span {b * c}))).ker) :
    g⁻¹ * GeneralLinearGroup.map (algebraMap R K) γ * g ∈ integralGL R K ι := by
  -- the entries of `γ - 1` are multiples of `b c`
  have hent (i j : ι) : ∃ x : R, (γ : Matrix ι ι R) i j = (1 : Matrix ι ι R) i j + b * c * x := by
    have h := congrArg (fun x : GL ι (R ⧸ Ideal.span {b * c}) ↦
      (x : Matrix ι ι (R ⧸ Ideal.span {b * c})) i j) (MonoidHom.mem_ker.mp hγ)
    simp only [GeneralLinearGroup.val_map_apply, map_apply, Units.val_one] at h
    have h1 : (1 : Matrix ι ι (R ⧸ Ideal.span {b * c})) i j =
        Ideal.Quotient.mk _ ((1 : Matrix ι ι R) i j) := by
      by_cases hij : i = j <;> simp [Matrix.one_apply, hij]
    rw [h1, Ideal.Quotient.eq] at h
    obtain ⟨x, hx⟩ := Ideal.mem_span_singleton'.mp h
    exact ⟨x, by linear_combination hx.symm⟩
  choose C hC using hent
  have hγC : (γ : Matrix ι ι R) = 1 + (b * c) • Matrix.of C := by
    ext i j
    simp [hC]
  -- `g⁻¹ γ g = g⁻¹ (1 + b c C) g = 1 + (c g⁻¹) C (b g) = 1 + B C A`
  refine inv_mul_map_mul_mem_integralGL_of_map_eq (IsFractionRing.injective R K)
    (A := 1 + B * Matrix.of C * A) ?_
  have hg : (↑g⁻¹ : Matrix ι ι K) * g = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  rw [← RingHom.mapMatrix_apply, map_add, map_one, map_mul, map_mul]
  simp only [RingHom.mapMatrix_apply]
  rw [hA, hB, Units.val_mul, Units.val_mul, GeneralLinearGroup.val_map_apply, hγC,
    Matrix.map_add _ (map_add _), Matrix.map_one _ (map_zero _) (map_one _),
    Matrix.map_smul _ _ fun a ↦ by rw [smul_eq_mul, map_mul, Algebra.smul_def], mul_add, add_mul,
    Matrix.mul_one, hg]
  simp only [smul_mul_assoc, mul_smul_comm, smul_smul, Matrix.mul_assoc]

variable [Ring.HasFiniteQuotients R]

/-- **Every element of `GL_ι(K)` commensurates `GL_ι(R)`.** For `g ∈ GL_ι(K)`, a congruence
subgroup of `GL_ι(R)`, of finite index since `R` has finite quotients, lies in `g GL_ι(R) g⁻¹`. -/
theorem commensurator_integralGL_eq_top : commensurator (integralGL R K ι) = ⊤ := by
  have : IsDomain R := Function.Injective.isDomain _ (IsFractionRing.injective R K)
  refine commensurator_eq_top_iff.mpr fun g ↦ ?_
  obtain ⟨⟨b, hb⟩, A, hA⟩ :=
    TauCeti.IsLocalization.exists_matrix_map_eq_smul (nonZeroDivisors R) (g : Matrix ι ι K)
  obtain ⟨⟨c, hc⟩, B, hB⟩ :=
    TauCeti.IsLocalization.exists_matrix_map_eq_smul (nonZeroDivisors R) (↑g⁻¹ : Matrix ι ι K)
  set φ := GeneralLinearGroup.map (n := ι) (algebraMap R K)
  set N := (GeneralLinearGroup.map (n := ι) (Ideal.Quotient.mk (Ideal.span {b * c}))).ker
  have hφ : Function.Injective φ :=
    GeneralLinearGroup.map_injective (IsFractionRing.injective R K)
  -- the congruence subgroup of level `b c` has finite index in `GL_ι(R)`
  have : Finite (R ⧸ Ideal.span {b * c}) := Ring.HasFiniteQuotients.finiteQuotient (by
    rw [ne_eq, Ideal.span_singleton_eq_bot]
    exact mul_ne_zero (nonZeroDivisors.ne_zero hb) (nonZeroDivisors.ne_zero hc))
  have hN : (N.map φ).IsFiniteRelIndex (integralGL R K ι) := by
    rw [isFiniteRelIndex_iff_relIndex_ne_zero, integralGL, MonoidHom.range_eq_map,
      relIndex_map_map_of_injective _ _ hφ, relIndex_top_right]
    exact (finiteIndex_ker _).index_ne_zero
  refine isFiniteRelIndex_of_le_left (integralGL R K ι) (H := N.map φ) ?_
  -- and it lies in `g GL_ι(R) g⁻¹`
  rintro _ ⟨γ, hγ, rfl⟩
  rw [mem_pointwise_smul_iff_inv_smul_mem, MulAut.smul_def, MulAut.conj_inv_apply]
  exact inv_mul_map_mul_mem_integralGL hA hB hγ

/-- The local Hecke pair `(GL_ι(K), GL_ι(R))`. -/
instance instIsHeckeTripleTopIntegralGL :
    IsHeckeTriple (⊤ : Submonoid (GL ι K)) (integralGL R K ι) (integralGL R K ι) :=
  IsHeckeTriple.of_diagonal le_top (by rw [commensurator_integralGL_eq_top]; exact le_top)

end Commensurator

end HeckeRing.GLn

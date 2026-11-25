/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Charpoly.BaseChange
public import TauCeti.RingTheory.Iwasawa.Elementary
public import TauCeti.RingTheory.Iwasawa.LambdaInvariant

import Mathlib.NumberTheory.Padics.PadicIntegers
import TauCeti.Algebra.Module.Torsion.Localization
import TauCeti.Algebra.Polynomial.Degree.Operations
import TauCeti.LinearAlgebra.Charpoly.Pi
import TauCeti.RingTheory.Polynomial.Distinguished
import TauCeti.RingTheory.Polynomial.Eisenstein.DiscreteValuationRing
import TauCeti.RingTheory.PowerSeries.Weierstrass.Charpoly
import TauCeti.RingTheory.RegularLocalRing.PowerSeries

/-!
# The generic fiber of an Iwasawa module

Let `O` be a discrete valuation ring with fraction field `K`, complete for its maximal ideal, and
let `M` be a finitely generated torsion module over `Λ = O⟦X⟧`. Then `K ⊗[O] M` is a
finite-dimensional `K`-vector space, and multiplication by `X` on `M` induces an endomorphism of it.
This file shows that the characteristic polynomial of that endomorphism is the characteristic
polynomial `F_M` of `M` (`TauCeti.Iwasawa.charPoly`), and hence that the `λ`-invariant of `M` is
the dimension of `K ⊗[O] M`. In this form `F_M` and `λ(M)` are read off the action of `X` alone,
with no reference to the characteristic divisor.

Base change to `K` forgets everything that a power of a uniformiser `ϖ` kills. A pseudo-null
`Λ`-module is killed by a power of the maximal ideal `(ϖ, X)` of `Λ`, so a pseudo-isomorphism
becomes an isomorphism after base change to `K`. By the structure theorem
(`TauCeti.Iwasawa.exists_isPseudoIsomorphism_elementary`), this reduces the computation to an
elementary module. Its free part vanishes because `M` is torsion, and its vertical factors
`Λ ⧸ (ϖ ^ mᵢ)` die over `K`. Each horizontal factor `Λ ⧸ (Fⱼ ^ nⱼ)` is free over `O` of rank
`nⱼ deg Fⱼ`, and `X` acts on it with characteristic polynomial `Fⱼ ^ nⱼ`
(`PowerSeries.IsWeierstrassFactorizationAt.charpoly_lmul_mk_X`).

## Main results

* `TauCeti.Iwasawa.IsPseudoNull.isTorsion_of_isScalarTower`: a pseudo-null `O⟦X⟧`-module is torsion
  over `O`.
* `TauCeti.Iwasawa.IsPseudoIsomorphism.baseChange_bijective`: a pseudo-isomorphism of
  `O⟦X⟧`-modules becomes bijective after base change to `K`.
* `TauCeti.Iwasawa.finite_tensorProduct_of_isTorsion`: `K ⊗[O] M` is finite-dimensional.
* `TauCeti.Iwasawa.map_charPoly_eq_charpoly`: `F_M` is the characteristic polynomial of `X` on
  `K ⊗[O] M`.
* `TauCeti.Iwasawa.lambdaInvariant_eq_finrank`: `λ(M) = dim_K (K ⊗[O] M)`.

## References

* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, second edition, (5.3.9)
  and Remark 3 following it.
* L. Washington, *Introduction to Cyclotomic Fields*, second edition, GTM 83, §13.2.
-/

public section

open IsLocalRing PowerSeries TensorProduct
open scoped Polynomial PowerSeries

namespace TauCeti.Iwasawa

/-- In the vertical factor `O⟦X⟧ ⧸ (ϖ ^ m)`, multiplication by `ϖ ^ m` is zero. -/
private theorem pow_smul_quotient_span_C_pow {O : Type*} [CommRing O] (ϖ : O) (m : ℕ)
    (q : O⟦X⟧ ⧸ Ideal.span {C (ϖ ^ m)}) : ϖ ^ m • q = 0 := by
  induction q using Submodule.Quotient.induction_on with | _ p
  rw [← algebraMap_smul O⟦X⟧, algebraMap_eq, ← Submodule.Quotient.mk_smul,
    Submodule.Quotient.mk_eq_zero, smul_eq_mul]
  exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)

/-- A product with a free factor `Fin r → A` over a nontrivial ring is torsion only when `r = 0`.
This removes the free part of an elementary module. -/
private theorem eq_zero_of_isTorsion_prod {A P : Type*} [CommRing A] [Nontrivial A]
    [AddCommGroup P] [Module A P] {r : ℕ} (h : Module.IsTorsion A ((Fin r → A) × P)) : r = 0 := by
  by_contra hr
  let i : Fin r := ⟨0, Nat.pos_of_ne_zero hr⟩
  obtain ⟨c, hc⟩ := h (x := (Pi.single i 1, 0))
  exact nonZeroDivisors.coe_ne_zero c
    (by simpa [Submonoid.smul_def] using congr_fun (congrArg Prod.fst hc) i)

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (K : Type*) [Field K]
  [Algebra O K] [IsFractionRing O K] {M N : Type*} [AddCommGroup M] [Module O⟦X⟧ M] [Module O M]
  [IsScalarTower O O⟦X⟧ M] [AddCommGroup N] [Module O⟦X⟧ N] [Module O N] [IsScalarTower O O⟦X⟧ N]

/-- Over a discrete valuation ring `O`, a pseudo-null `O⟦X⟧`-module is torsion over `O`: since
`O⟦X⟧` is a two-dimensional local ring, a power of its maximal ideal kills the module, and that
power contains a power of a uniformiser of `O`. -/
theorem IsPseudoNull.isTorsion_of_isScalarTower (h : IsPseudoNull O⟦X⟧ M) :
    Module.IsTorsion O M := by
  have := h.finite
  obtain ⟨k, hk⟩ := (isPseudoNull_iff_exists_pow_le_annihilator
    TauCeti.PowerSeries.ringKrullDim_of_isDiscreteValuationRing).mp h
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  -- The constant `ϖ` is not a unit of `O⟦X⟧`, so it lies in the maximal ideal.
  have hC : C ϖ ∈ maximalIdeal O⟦X⟧ := fun hu ↦
    hϖ.not_isUnit (by simpa using hu.map (constantCoeff (R := O)))
  intro x
  refine ⟨⟨ϖ ^ k, pow_mem (mem_nonZeroDivisors_of_ne_zero hϖ.ne_zero) k⟩, ?_⟩
  rw [Submonoid.mk_smul, ← algebraMap_smul O⟦X⟧, algebraMap_eq, map_pow]
  exact Module.mem_annihilator.mp (hk (Ideal.pow_mem_pow hC k)) x

/-- Over a discrete valuation ring `O` with fraction field `K`, a pseudo-isomorphism of
`O⟦X⟧`-modules becomes bijective after base change to `K`: its kernel and cokernel are
pseudo-null, hence torsion over `O`. -/
theorem IsPseudoIsomorphism.baseChange_bijective {f : M →ₗ[O⟦X⟧] N}
    (hf : IsPseudoIsomorphism f) : Function.Bijective ((f.restrictScalars O).baseChange K) := by
  refine ((f.restrictScalars O).baseChange_bijective_iff_isTorsion K).mpr ⟨?_, fun y ↦ ?_⟩
  · rw [LinearMap.ker_restrictScalars]
    exact hf.isPseudoNull_ker.isTorsion_of_isScalarTower
  · induction y using Submodule.Quotient.induction_on with | _ n
    obtain ⟨a, ha⟩ := hf.isPseudoNull_coker.isTorsion_of_isScalarTower
      (x := Submodule.Quotient.mk (p := LinearMap.range f) n)
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at ha
    exact ⟨a, by rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]; exact ha⟩

variable [IsAdicComplete (maximalIdeal O) O]

/-- A finitely generated torsion `O⟦X⟧`-module `M` maps to a finite product of horizontal factors
`O⟦X⟧ ⧸ (Fⱼ ^ nⱼ)`, with each `Fⱼ` distinguished and `F_M = ∏ Fⱼ ^ nⱼ`, by a map that becomes
bijective after base change to `K`. -/
private theorem exists_bijective_baseChange_pi (hM : Module.IsTorsion O⟦X⟧ M)
    [Module.Finite O⟦X⟧ M] :
    ∃ (b : ℕ) (F : Fin b → O[X]) (n : Fin b → ℕ),
      (∀ j, (F j).IsDistinguishedAt (maximalIdeal O)) ∧ charPoly O M = ∏ j, F j ^ n j ∧
        ∃ g : M →ₗ[O⟦X⟧] ∀ j, O⟦X⟧ ⧸ Ideal.span {((F j ^ n j : O[X]) : O⟦X⟧)},
          Function.Bijective ((g.restrictScalars O).baseChange K) := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  obtain ⟨r, a, b, m, F, n, -, hFn, f, hf⟩ := exists_isPseudoIsomorphism_elementary (M := M) hϖ
  -- The elementary module is torsion, so it has no free part.
  obtain rfl : r = 0 := eq_zero_of_isTorsion_prod (hf.isTorsion_iff.mp hM)
  refine ⟨b, F, n, fun j ↦ (hFn j).1, hf.charPoly_eq_prod hϖ (fun j ↦ (hFn j).1)
    (fun j ↦ (hFn j).2.1), (LinearMap.snd _ _ _ ∘ₗ LinearMap.snd _ _ _) ∘ₗ f, ?_⟩
  rw [LinearMap.restrictScalars_comp, LinearMap.baseChange_comp, LinearMap.coe_comp]
  refine Function.Bijective.comp ?_ (hf.baseChange_bijective K)
  -- The projection onto the horizontal factors is surjective, and `ϖ ^ (∑ mᵢ)` kills its kernel.
  refine (LinearMap.baseChange_bijective_iff_isTorsion _ K).mpr ⟨fun x ↦ ?_, fun y ↦ ?_⟩
  · have hx : (x : Elementary O ϖ 0 m F n).2.2 = 0 := by simpa using x.property
    refine ⟨⟨ϖ ^ ∑ i, m i, pow_mem (mem_nonZeroDivisors_of_ne_zero hϖ.ne_zero) _⟩, ?_⟩
    rw [Submonoid.mk_smul]
    refine Subtype.ext (Prod.ext (Subsingleton.elim _ _) (Prod.ext (funext fun i ↦ ?_) ?_))
    · obtain ⟨c, hc⟩ := pow_dvd_pow ϖ (Finset.single_le_sum (fun _ _ ↦ Nat.zero_le _)
        (Finset.mem_univ i) : m i ≤ ∑ i, m i)
      rw [Submodule.coe_smul]
      simp [hc, mul_comm _ c, mul_smul, pow_smul_quotient_span_C_pow]
    · rw [Submodule.coe_smul]
      simp [hx]
  · induction y using Submodule.Quotient.induction_on with | _ h
    refine ⟨1, ?_⟩
    rw [one_smul, Submodule.Quotient.mk_eq_zero]
    exact LinearMap.mem_range.mpr ⟨(0, 0, h), by simp⟩

/-- **The generic fiber of a torsion Iwasawa module is finite-dimensional.** Over a complete
discrete valuation ring `O` with fraction field `K`, for a finitely generated torsion
`O⟦X⟧`-module `M`, the `K`-vector space `K ⊗[O] M` is finite-dimensional. -/
theorem finite_tensorProduct_of_isTorsion (hM : Module.IsTorsion O⟦X⟧ M)
    [Module.Finite O⟦X⟧ M] : Module.Finite K (K ⊗[O] M) := by
  obtain ⟨b, F, n, hF, -, g, hg⟩ := exists_bijective_baseChange_pi K hM
  have (j : Fin b) := ((hF j).pow (n j)).isWeierstrassFactorizationAt.finite_quotient
  exact .equiv (LinearEquiv.ofBijective _ hg).symm

/-- **The characteristic polynomial of an Iwasawa module as a characteristic polynomial.** Over a
complete discrete valuation ring `O` with fraction field `K`, let `M` be a finitely generated
torsion `O⟦X⟧`-module. The characteristic polynomial `F_M` of `M`, mapped to `K`, is the
characteristic polynomial of multiplication by `X` on the finite-dimensional `K`-vector space
`K ⊗[O] M` (see `finite_tensorProduct_of_isTorsion`). -/
theorem map_charPoly_eq_charpoly (hM : Module.IsTorsion O⟦X⟧ M) [Module.Finite O⟦X⟧ M]
    [Module.Finite K (K ⊗[O] M)] :
    (charPoly O M).map (algebraMap O K) =
      ((Algebra.lsmul O O M (X : O⟦X⟧)).baseChange K).charpoly := by
  obtain ⟨b, F, n, hF, hchar, g, hg⟩ := exists_bijective_baseChange_pi K hM
  have hW (j : Fin b) := ((hF j).pow (n j)).isWeierstrassFactorizationAt
  have (j : Fin b) := (hW j).free_quotient
  have (j : Fin b) := (hW j).finite_quotient
  let e := LinearEquiv.ofBijective _ hg
  -- The isomorphism `e` intertwines multiplication by `X` on both sides.
  have hconj : e.conj ((Algebra.lsmul O O M (X : O⟦X⟧)).baseChange K) =
      (Algebra.lsmul O O _ (X : O⟦X⟧)).baseChange K := by
    have hcomm : g.restrictScalars O ∘ₗ Algebra.lsmul O O M (X : O⟦X⟧) =
        Algebra.lsmul O O _ (X : O⟦X⟧) ∘ₗ g.restrictScalars O :=
      LinearMap.ext fun x ↦ g.map_smul X x
    refine LinearMap.ext fun y ↦ ?_
    obtain ⟨y, rfl⟩ := e.surjective y
    rw [LinearEquiv.conj_apply_apply, LinearEquiv.symm_apply_apply]
    have h := LinearMap.congr_fun (congrArg (LinearMap.baseChange K) hcomm) y
    rwa [LinearMap.baseChange_comp, LinearMap.baseChange_comp] at h
  -- Multiplication by `X` on the product acts coordinatewise, by `Fⱼ ^ nⱼ` on each factor.
  have hpi : Algebra.lsmul O O (∀ j, O⟦X⟧ ⧸ Ideal.span {((F j ^ n j : O[X]) : O⟦X⟧)}) (X : O⟦X⟧) =
      LinearMap.piMap fun j ↦ Algebra.lmul O _ (Ideal.Quotient.mk _ X) := by
    refine LinearMap.ext fun x ↦ funext fun j ↦ ?_
    obtain ⟨q, hq⟩ := Ideal.Quotient.mk_surjective (x j)
    -- The quotient map is an `O⟦X⟧`-algebra map, so it commutes with multiplication by `X`.
    simpa [← hq, ← map_mul] using (map_smul (Ideal.Quotient.mkₐ O⟦X⟧ _) (X : O⟦X⟧) q).symm
  rw [← e.charpoly_conj, hconj, LinearMap.charpoly_baseChange, hpi, LinearMap.charpoly_piMap, hchar]
  simp only [fun j ↦ (hW j).charpoly_lmul_mk_X]

/-- **The `λ`-invariant is a dimension.** Over a complete discrete valuation ring `O` with fraction
field `K`, the `λ`-invariant of a finitely generated torsion `O⟦X⟧`-module `M` is the dimension of
the `K`-vector space `K ⊗[O] M`. -/
theorem lambdaInvariant_eq_finrank (hM : Module.IsTorsion O⟦X⟧ M) [Module.Finite O⟦X⟧ M] :
    lambdaInvariant O M = Module.finrank K (K ⊗[O] M) := by
  have := finite_tensorProduct_of_isTorsion K hM
  rw [lambdaInvariant_def, ← monic_charPoly.natDegree_map (algebraMap O K),
    map_charPoly_eq_charpoly K hM, LinearMap.charpoly_natDegree]

-- Over `ℚ_p`, the generic fiber of `ℤ_p⟦T⟧ ⧸ (T² + pT + p)`, cut out by an Eisenstein polynomial,
-- has dimension `2 = λ`.
example (p : ℕ) [Fact p.Prime] :
    let F : ℤ_[p][X] := .X ^ 2 + .C (p : ℤ_[p]) * .X + .C (p : ℤ_[p])
    Module.finrank ℚ_[p] (ℚ_[p] ⊗[ℤ_[p]] (ℤ_[p]⟦X⟧ ⧸ Ideal.span {(F : ℤ_[p]⟦X⟧)})) = 2 := by
  intro F
  have hp : (p : ℤ_[p]) ∈ maximalIdeal ℤ_[p] := by
    rw [PadicInt.maximalIdeal_eq_span_p]
    exact Ideal.mem_span_singleton_self _
  have hE : F.IsEisensteinAt (maximalIdeal ℤ_[p]) :=
    TauCeti.isEisensteinAt_X_pow_add_C_mul_X_add_C_of_irreducible hp PadicInt.irreducible_p le_rfl
  have hdeg : F.natDegree = 2 := Polynomial.natDegree_X_pow_add_C_mul_X_add_C _ _ le_rfl
  have hmon : F.Monic := by
    rw [Polynomial.Monic, Polynomial.leadingCoeff, hdeg]
    simp [F]
  have hF : F.IsDistinguishedAt (maximalIdeal ℤ_[p]) := ⟨hE.isWeaklyEisensteinAt, hmon⟩
  have hirr : Irreducible F := hE.irreducible (maximalIdeal.isMaximal _).isPrime hmon.isPrimitive
    (by rw [hdeg]; norm_num)
  have hM := Ideal.isTorsion_quotient_of_mem (Ideal.mem_span_singleton_self (F : ℤ_[p]⟦X⟧))
    (mem_nonZeroDivisors_of_ne_zero (Polynomial.coe_eq_zero_iff.not.mpr hmon.ne_zero))
  have h := lambdaInvariant_quotient_span_pow hF hirr 1
  rw [pow_one, one_mul, hdeg] at h
  rw [← lambdaInvariant_eq_finrank ℚ_[p] hM, h]

end TauCeti.Iwasawa

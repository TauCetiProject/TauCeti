/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.MvPolynomial.HasseDeriv.Taylor
public import Mathlib.LinearAlgebra.Matrix.Defs
public import TauCeti.Data.Finsupp.Weight
public import Mathlib.RingTheory.MvPolynomial.Ideal
public import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.LinearAlgebra.Dimension.RankNullity

/-!
# Samuel jet matrices

The degree-`k` jet of a polynomial at `a` consists of its Taylor coefficients of total degree
at most `k`. For generators `f i`, the Samuel matrix has these exponents as rows and pairs
`(i, β)` as columns. Its column holds the truncated coefficients of `X^β * taylor a (f i)`,
where `X` denotes the centered Taylor variables, rather than just the jet of `f i`. These extra
columns retain all polynomial multiples of the generators.

The column space is the image of the entire ideal in the space of jets. In particular, both
its rank and its ideals of minors are independent of the generating family. For finite variable
and generator types, this provides finite determinantal equations for jet rank conditions. Hasse
derivatives give the entries without a characteristic restriction; in characteristic zero these
are normalized ordinary derivatives.

The construction follows Bierstone–Milman, *Canonical desingularization in characteristic zero
by blowing up the maximum strata of a local invariant* (1997), Definition 7.10 and (7.12).
-/

public section

variable {σ R ι : Type*}

namespace MvPolynomial

section Semiring

variable [CommSemiring R]

/-- The coefficients of total degree at most `k`, as a linear map. -/
noncomputable def jetCoeffs (k : ℕ) :
    MvPolynomial σ R →ₗ[R] ({d : σ →₀ ℕ // d.degree ≤ k} → R) :=
  LinearMap.pi fun d ↦ lcoeff R d.val

/-- Each coordinate of the truncated coefficient vector is the corresponding coefficient. -/
@[simp]
theorem jetCoeffs_apply (k : ℕ) (p : MvPolynomial σ R)
    (d : {d : σ →₀ ℕ // d.degree ≤ k}) : jetCoeffs k p d = p.coeff d.val := (rfl)

/-- Vanishing of the degree-`k` coefficient vector is membership in the `(k+1)`-st power
of the coordinate ideal. Thus these coefficient vectors are genuine truncated jets. -/
@[simp]
theorem jetCoeffs_eq_zero_iff (k : ℕ) (p : MvPolynomial σ R) :
    jetCoeffs k p = 0 ↔ p ∈ idealOfVars σ R ^ (k + 1) := by
  rw [mem_pow_idealOfVars_iff']
  simp only [funext_iff, jetCoeffs_apply, Pi.zero_apply, Subtype.forall]
  exact forall_congr' fun d ↦ by rw [Nat.lt_succ_iff]

/-- The Samuel jet matrix: column `(i, β)` holds the truncated coefficients of
`X^β * taylor a (f i)`, where `X` denotes the centered Taylor variables. -/
noncomputable def samuelJetMatrix (f : ι → MvPolynomial σ R) (a : σ → R) (k : ℕ) :
    Matrix {d : σ →₀ ℕ // d.degree ≤ k} (ι × {d : σ →₀ ℕ // d.degree ≤ k}) R :=
  fun α iβ ↦ (monomial iβ.2.val 1 * taylor a (f iβ.1)).coeff α.val

/-- An entry of the Samuel matrix is the shifted, normalized derivative of a generator.
The entry is zero unless the column exponent is componentwise at most the row exponent. -/
theorem samuelJetMatrix_apply (f : ι → MvPolynomial σ R) (a : σ → R) (k : ℕ)
    (α : {d : σ →₀ ℕ // d.degree ≤ k}) (iβ : ι × {d : σ →₀ ℕ // d.degree ≤ k}) :
    samuelJetMatrix f a k α iβ =
      if iβ.2.val ≤ α.val then eval a (hasseDeriv (α.val - iβ.2.val) (f iβ.1)) else 0 := by
  classical
  simp [samuelJetMatrix, coeff_monomial_mul', coeff_taylor]

/-- Monomial multiples of degree greater than `k` have zero degree-`k` jet. -/
theorem jetCoeffs_monomial_mul_eq_zero {k : ℕ} {β : σ →₀ ℕ} (hβ : k < β.degree)
    (p : MvPolynomial σ R) : jetCoeffs k (monomial β 1 * p) = 0 := by
  classical
  ext α
  have h : ¬ β ≤ α.val := fun h ↦ (not_le_of_gt hβ) ((Finsupp.degree_mono h).trans α.property)
  simp [coeff_monomial_mul', h]

/-- Every truncated coefficient vector is the jet of a polynomial. -/
theorem jetCoeffs_surjective [Finite σ] (k : ℕ) :
    Function.Surjective (jetCoeffs (σ := σ) (R := R) k) := by
  classical
  let := Fintype.ofFinite {d : σ →₀ ℕ // d.degree ≤ k}
  intro v
  refine ⟨∑ β, monomial β.val (v β), ?_⟩
  ext α
  simp [← Subtype.ext_iff]

end Semiring

end MvPolynomial

namespace Ideal

open MvPolynomial

section Semiring

variable [CommSemiring R]

/-- The image of an ideal in degree-`k` Taylor jets at `a`. -/
noncomputable def jetImage (I : Ideal (MvPolynomial σ R)) (a : σ → R) (k : ℕ) :
    Submodule R ({d : σ →₀ ℕ // d.degree ≤ k} → R) :=
  ((I.map (taylor a)).restrictScalars R).map (jetCoeffs k)

/-- Membership in the jet image means being the low-degree coefficient vector of a polynomial
in the Taylor-transformed ideal. -/
theorem mem_jetImage_iff (I : Ideal (MvPolynomial σ R)) (a : σ → R) (k : ℕ)
    (v : {d : σ →₀ ℕ // d.degree ≤ k} → R) :
    v ∈ jetImage I a k ↔ ∃ p ∈ I.map (taylor a), jetCoeffs k p = v := (Iff.rfl)

/-- The zero ideal has zero jet image. -/
@[simp]
theorem jetImage_bot (a : σ → R) (k : ℕ) : jetImage (⊥ : Ideal (MvPolynomial σ R)) a k = ⊥ := by
  simp [jetImage]

/-- The unit ideal fills the space of jets. -/
@[simp]
theorem jetImage_top [Finite σ] (a : σ → R) (k : ℕ) :
    jetImage (⊤ : Ideal (MvPolynomial σ R)) a k = ⊤ := by
  simp [jetImage, Ideal.map_top, LinearMap.range_eq_top.mpr (jetCoeffs_surjective k)]

end Semiring

section Ring

variable [CommRing R] [Finite σ]

/-- Jets identify the quotient by an ideal and the `(k+1)`-st coordinate-ideal power
with the quotient of the jet space by the ideal's image, in Taylor coordinates. -/
noncomputable def jetQuotientEquiv (I : Ideal (MvPolynomial σ R)) (a : σ → R) (k : ℕ) :
    (MvPolynomial σ R ⧸
      ((I.map (taylor a) ⊔ idealOfVars σ R ^ (k + 1)).restrictScalars R)) ≃ₗ[R]
      (({d : σ →₀ ℕ // d.degree ≤ k} → R) ⧸ jetImage I a k) := by
  let q := (jetImage I a k).mkQ.comp (jetCoeffs k)
  have hker : LinearMap.ker q =
      ((I.map (taylor a) ⊔ idealOfVars σ R ^ (k + 1)).restrictScalars R) := by
    have hc : LinearMap.ker (jetCoeffs (σ := σ) (R := R) k) =
        (idealOfVars σ R ^ (k + 1)).restrictScalars R := by
      ext p
      exact jetCoeffs_eq_zero_iff k p
    rw [LinearMap.ker_comp, Submodule.ker_mkQ, jetImage, Submodule.comap_map_eq, hc,
      Submodule.restrictScalars_sup]
  exact (Submodule.quotEquivOfEq _ _ hker.symm).trans
    (q.quotKerEquivOfSurjective ((Submodule.mkQ_surjective _).comp (jetCoeffs_surjective k)))

/-- On representatives, the jet quotient comparison takes the low-degree coefficients. -/
@[simp]
theorem jetQuotientEquiv_mk (I : Ideal (MvPolynomial σ R)) (a : σ → R) (k : ℕ)
    (p : MvPolynomial σ R) :
    jetQuotientEquiv I a k (Submodule.Quotient.mk p) =
      Submodule.Quotient.mk (jetCoeffs k p) := by
  simp [jetQuotientEquiv, Submodule.quotEquivOfEq_mk]

end Ring

/-- The colength of an ideal in truncated Taylor coordinates plus the dimension of its jet
image is the number of monomials of total degree at most `k`. -/
theorem finrank_jetQuotient_add_finrank_jetImage {K : Type*} [Field K] [Finite σ]
    (I : Ideal (MvPolynomial σ K)) (a : σ → K) (k : ℕ) :
    Module.finrank K (MvPolynomial σ K ⧸
      ((I.map (taylor a) ⊔ idealOfVars σ K ^ (k + 1)).restrictScalars K)) +
      Module.finrank K (jetImage I a k) =
        Nat.card {d : σ →₀ ℕ // d.degree ≤ k} := by
  classical
  let := Fintype.ofFinite {d : σ →₀ ℕ // d.degree ≤ k}
  rw [(jetQuotientEquiv I a k).finrank_eq, Submodule.finrank_quotient_add_finrank]
  simp

end Ideal

namespace MvPolynomial

open Ideal

section Semiring

variable [CommSemiring R]

private theorem jetCoeffs_mul_generator_mem (f : ι → MvPolynomial σ R) (a : σ → R) (k : ℕ)
    (i : ι) (p : MvPolynomial σ R) :
    jetCoeffs k (p * taylor a (f i)) ∈
      Submodule.span R (Set.range (samuelJetMatrix f a k).col) := by
  classical
  nth_rw 1 [p.as_sum]
  rw [Finset.sum_mul, map_sum]
  apply Submodule.sum_mem
  intro β _
  have hm : jetCoeffs k (monomial β 1 * taylor a (f i)) ∈
      Submodule.span R (Set.range (samuelJetMatrix f a k).col) := by
    by_cases h : β.degree ≤ k
    · exact Submodule.subset_span ⟨(i, ⟨β, h⟩), rfl⟩
    · rw [jetCoeffs_monomial_mul_eq_zero (Nat.lt_of_not_ge h)]
      exact Submodule.zero_mem _
  have heq : monomial β (p.coeff β) * taylor a (f i) =
      p.coeff β • (monomial β 1 * taylor a (f i)) := by
    simp [← smul_mul_assoc, smul_monomial]
  rw [heq, map_smul]
  exact Submodule.smul_mem _ _ hm

/-- The column space of the Samuel matrix is exactly the image of the generated ideal in jets.
In particular, arbitrary polynomial multipliers are already accounted for by columns of degree
at most `k`. -/
theorem span_cols_samuelJetMatrix (f : ι → MvPolynomial σ R) (a : σ → R) (k : ℕ) :
    Submodule.span R (Set.range (samuelJetMatrix f a k).col) =
      jetImage (Ideal.span (Set.range f)) a k := by
  classical
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨⟨i, β⟩, rfl⟩
    apply (mem_jetImage_iff _ _ _ _).mpr
    refine ⟨monomial β.val 1 * taylor a (f i), ?_, rfl⟩
    exact Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem _ (Ideal.subset_span ⟨i, rfl⟩))
  · intro v hv
    obtain ⟨p, hp, rfl⟩ := (mem_jetImage_iff _ _ _ _).mp hv
    rw [Ideal.map_span, ← Set.range_comp] at hp
    obtain ⟨c, rfl⟩ := Finsupp.mem_ideal_span_range_iff_exists_finsupp.mp hp
    rw [Finsupp.sum, map_sum]
    exact Submodule.sum_mem _ fun i _ ↦ jetCoeffs_mul_generator_mem f a k i (c i)

/-- Changing generators does not change the column space of a Samuel matrix. -/
theorem span_cols_samuelJetMatrix_eq {κ : Type*}
    (f : ι → MvPolynomial σ R) (g : κ → MvPolynomial σ R)
    (h : Ideal.span (Set.range f) = Ideal.span (Set.range g)) (a : σ → R) (k : ℕ) :
    Submodule.span R (Set.range (samuelJetMatrix f a k).col) =
      Submodule.span R (Set.range (samuelJetMatrix g a k).col) := by
  rw [span_cols_samuelJetMatrix, span_cols_samuelJetMatrix, h]

end Semiring

/-! The first derivative distinguishes the double zero at `0` from the simple zero at `1` of
`X²(X-1)`, although both zero-jets vanish. -/

example : samuelJetMatrix (fun _ : Unit ↦ (X (0 : Fin 1) ^ 2 * (X 0 - 1) :
    MvPolynomial (Fin 1) ℚ)) (fun _ ↦ 0) 1
    ⟨Finsupp.single 0 1, by simp⟩ ((), ⟨0, by simp⟩) = 0 := by
  simp only [samuelJetMatrix, monomial_zero', C_1, one_mul, coeff_single_one_taylor]
  simp

example : samuelJetMatrix (fun _ : Unit ↦ (X (0 : Fin 1) ^ 2 * (X 0 - 1) :
    MvPolynomial (Fin 1) ℚ)) (fun _ ↦ 1) 1
    ⟨Finsupp.single 0 1, by simp⟩ ((), ⟨0, by simp⟩) = 1 := by
  simp only [samuelJetMatrix, monomial_zero', C_1, one_mul, coeff_single_one_taylor]
  simp

end MvPolynomial

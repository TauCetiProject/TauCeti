/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.MvPolynomial.PolynomialSpace
import TauCeti.Algebra.MvPolynomial.PDeriv
import TauCeti.RingTheory.MvPolynomial.PoincareLemma

/-!
# The Poincaré lemma on Euclidean polynomial spaces

`TauCeti.polynomialsDegLE ι m` is the space of real functions on `EuclideanSpace ℝ ι` represented
by formal polynomials of total degree at most `m`. Building on the analytic calculus, open-set
rigidity, and derivative identities in `TauCeti.Analysis.MvPolynomial.PolynomialSpace` and formal
derivative extensionality (`MvPolynomial.pderiv.ext`) in `TauCeti.Algebra.MvPolynomial.PDeriv`,
this file transports the formal polynomial Poincaré lemma (`MvPolynomial.exists_pderiv_eq`) to
functions in `polynomialsDegLE`:

A finite family `p : ι → EuclideanSpace ℝ ι → ℝ` in `polynomialsDegLE ι m` whose coordinate
derivatives satisfy `fderiv ℝ (p i) x (single j 1) = fderiv ℝ (p j) x (single i 1)` is the
coordinate gradient of a polynomial function `q ∈ polynomialsDegLE ι (m + 1)`, uniquely
determined after prescribing `q 0`.

## Main results

* `TauCeti.exists_mem_polynomialsDegLE_fderiv_single_eq`,
  `TauCeti.existsUnique_mem_polynomialsDegLE_fderiv_single_eq`,
  `TauCeti.exists_mem_polynomialsDegLE_gradient_eq`: the Euclidean polynomial Poincaré lemma with
  degree control.

## References

* S. C. Brenner, L. R. Scott, *The Mathematical Theory of Finite Element Methods*, 3rd ed.,
  Springer (2008), §4.3.
-/

public section

noncomputable section

namespace TauCeti

open MvPolynomial
open scoped Gradient

/-! ### The polynomial Poincaré lemma on Euclidean space -/

section Poincare

/-- **Polynomial Poincaré lemma on `EuclideanSpace ℝ ι`.** If `p : ι → EuclideanSpace ℝ ι → ℝ` is
a family of polynomial functions of total degree at most `m` whose coordinate partial derivatives
commute, then there exists `q ∈ polynomialsDegLE ι (m + 1)` whose coordinate partial derivatives
are the `p i`. -/
theorem exists_mem_polynomialsDegLE_fderiv_single_eq {ι : Type*} [Finite ι] [DecidableEq ι]
    {m : ℕ} {p : ι → EuclideanSpace ℝ ι → ℝ} (hp : ∀ i, p i ∈ polynomialsDegLE ι m)
    (hclosed : ∀ i j x, fderiv ℝ (p i) x (EuclideanSpace.single j 1) =
      fderiv ℝ (p j) x (EuclideanSpace.single i 1)) :
    ∃ q ∈ polynomialsDegLE ι (m + 1),
      ∀ i x, fderiv ℝ q x (EuclideanSpace.single i 1) = p i x := by
  choose P hPdeg hPeval using fun i ↦ (mem_polynomialsDegLE_iff ι).mp (hp i)
  have hPmem : ∀ i, P i ∈ restrictTotalDegree ι ℝ m := fun i ↦
    (mem_restrictTotalDegree ι m (P i)).mpr (hPdeg i)
  have hPclosed : ∀ i j, pderiv j (P i) = pderiv i (P j) := by
    intro i j
    apply polynomialEvalₗ_injective ι
    ext x
    simpa only [← MvPolynomial.fderiv_polynomialEvalₗ_single, hPeval] using hclosed i j x
  obtain ⟨Q, hQdeg, hQp⟩ := exists_pderiv_eq P hPmem hPclosed
  refine ⟨polynomialEvalₗ ι Q, ?_, fun i x ↦ ?_⟩
  · rw [polynomialEvalₗ_mem_polynomialsDegLE_iff]
    exact (mem_restrictTotalDegree ι (m + 1) Q).mp hQdeg
  · rw [Q.fderiv_polynomialEvalₗ_single, hQp i, hPeval i]

/-- A closed family in `polynomialsDegLE ι m` admits a unique potential in
`polynomialsDegLE ι (m + 1)` with any prescribed value at `0`. -/
theorem existsUnique_mem_polynomialsDegLE_fderiv_single_eq {ι : Type*} [Finite ι] [DecidableEq ι]
    {m : ℕ} {p : ι → EuclideanSpace ℝ ι → ℝ} (hp : ∀ i, p i ∈ polynomialsDegLE ι m)
    (hclosed : ∀ i j x, fderiv ℝ (p i) x (EuclideanSpace.single j 1) =
      fderiv ℝ (p j) x (EuclideanSpace.single i 1)) (c : ℝ) :
    ∃! q : EuclideanSpace ℝ ι → ℝ,
      q ∈ polynomialsDegLE ι (m + 1) ∧
        (∀ i x, fderiv ℝ q x (EuclideanSpace.single i 1) = p i x) ∧ q 0 = c := by
  let := Fintype.ofFinite ι
  obtain ⟨q₀, hq₀deg, hq₀f⟩ := exists_mem_polynomialsDegLE_fderiv_single_eq hp hclosed
  set q : EuclideanSpace ℝ ι → ℝ := fun x ↦ q₀ x + (c - q₀ 0)
  have hqdeg : q ∈ polynomialsDegLE ι (m + 1) :=
    Submodule.add_mem _ hq₀deg (const_mem_polynomialsDegLE ι (m + 1) (c - q₀ 0))
  have hqf : ∀ i x, fderiv ℝ q x (EuclideanSpace.single i 1) = p i x := fun i x ↦ by
    simp [q, fderiv_add_const, hq₀f i x]
  have hq0 : q 0 = c := by simp [q]
  refine ⟨q, ⟨hqdeg, hqf, hq0⟩, ?_⟩
  rintro q' ⟨hq'deg, hq'f, hq'0⟩
  obtain ⟨Q, -, hQ⟩ := (mem_polynomialsDegLE_iff ι).mp hqdeg
  obtain ⟨Q', -, hQ'⟩ := (mem_polynomialsDegLE_iff ι).mp hq'deg
  rw [← hQ', ← hQ]
  congr 1
  apply pderiv.ext
  · intro i
    apply polynomialEvalₗ_injective ι
    ext x
    simpa only [← MvPolynomial.fderiv_polynomialEvalₗ_single, hQ, hQ', hqf i x] using hq'f i x
  · have h0 : polynomialEvalₗ ι Q' 0 = polynomialEvalₗ ι Q 0 := by rw [hQ', hQ, hq'0, hq0]
    simpa only [polynomialEvalₗ_apply, PiLp.zero_apply, ← Pi.zero_def, eval_zero] using h0

/-- Full Euclidean form of `exists_mem_polynomialsDegLE_fderiv_single_eq`, recording both the
directional Fréchet derivative and the gradient expansion of the potential `q`. -/
theorem exists_mem_polynomialsDegLE_gradient_eq {ι : Type*} [Fintype ι] [DecidableEq ι] {m : ℕ}
    {p : ι → EuclideanSpace ℝ ι → ℝ} (hp : ∀ i, p i ∈ polynomialsDegLE ι m)
    (hclosed : ∀ i j x, fderiv ℝ (p i) x (EuclideanSpace.single j 1) =
      fderiv ℝ (p j) x (EuclideanSpace.single i 1)) :
    ∃ q ∈ polynomialsDegLE ι (m + 1),
      (∀ i x, fderiv ℝ q x (EuclideanSpace.single i 1) = p i x) ∧
      (∀ x v, fderiv ℝ q x v = ∑ i, p i x * v i) ∧
      (∀ x, ∇ q x = ∑ i, p i x • EuclideanSpace.single i 1) := by
  obtain ⟨q, hqdeg, hqf⟩ := exists_mem_polynomialsDegLE_fderiv_single_eq hp hclosed
  obtain ⟨Q, -, rfl⟩ := (mem_polynomialsDegLE_iff ι).mp hqdeg
  have hQp : ∀ i x, polynomialEvalₗ ι (pderiv i Q) x = p i x := fun i x ↦ by
    rw [← Q.fderiv_polynomialEvalₗ_single, hqf i x]
  refine ⟨polynomialEvalₗ ι Q, hqdeg, hqf, fun x v ↦ ?_, fun x ↦ ?_⟩
  · simp_rw [Q.fderiv_polynomialEvalₗ_apply, hQp]
  · simp_rw [Q.gradient_polynomialEvalₗ, hQp]

end Poincare

end TauCeti

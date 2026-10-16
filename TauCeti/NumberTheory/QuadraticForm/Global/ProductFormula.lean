/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.QuadraticForm.Global.CohomologicalSymbol
public import TauCeti.NumberTheory.QuadraticForm.Global.FormInvariants
public import TauCeti.NumberTheory.QuadraticForm.Global.HilbertSymbol
import TauCeti.NumberTheory.ClassFieldTheory.Global.Hilbert.Reciprocity

/-!
# The product formula for the norm-equation Hilbert symbol and for the Hasse invariant

For `a, b ∈ Kˣ` in a number field `K`, Hilbert's product formula says that the norm-equation
Hilbert symbols `(a_v, b_v)_v ∈ {±1}` multiply to `1` over all the places `v` of `K`: the finite
places, read in the completions `K_v`, and the real places, read in `ℝ`. The complex places
contribute nothing, because every element of `ℂ` is a square.

Hilbert's reciprocity law in its cohomological form is the vanishing of the sum of the local
invariants of `(a) ∪ (b)` in `ZMod 2`, and the product of the norm-equation symbols over the
finite and real places is the sign of that sum
(`TauCeti.finprod_hilbertSymbol_mul_prod_hilbertSymbol_eq_hilbertSign`). This file transports the
cases of the cohomological law that are proved, so the multiplicative formula holds

* whenever some square root of `b` lies in a cyclotomic extension of `K`;
* in particular whenever `b` is rational;
* for all `a, b ∈ ℚˣ`, where it reads `∏_ℓ (a, b)_ℓ · (a, b)_∞ = 1` over the primes `ℓ` and the
  real place, with the symbols computed in `ℚ_ℓ` and in `ℝ`.

Multiplying the product formula over the pairs of coefficients of a diagonalization
`Q ≅ ⟨a₁, …, aₙ⟩` gives the product formula for the Hasse invariant of a regular form `Q`: the
product of its finite Hasse signs and of its real Hasse signs is `1`. With the other conditions
already checked in `QuadraticForm.isAdmissible_globalInvariants_iff`, the system of local
invariants of `Q` is then admissible when `Q` has positive rank. This holds whenever `Q` has a
diagonalization with rational coefficients, and so for every regular form over `ℚ`.

## Main results

* `TauCeti.finprod_hilbertSymbol_mul_prod_hilbertSymbol_eq_one_of_mem_adjoin`: the product
  formula when a square root of `b` lies in a cyclotomic extension of `K`.
* `TauCeti.finprod_hilbertSymbol_mul_prod_hilbertSymbol_eq_one_of_coe_eq_ratCast`: the product
  formula for a rational `b`.
* `TauCeti.finprod_hilbertSymbol_padic_mul_hilbertSymbol_real_eq_one`: the product formula over
  `ℚ`, with the local symbols in `ℚ_ℓ` and `ℝ`.
* `QuadraticForm.globalInvariants_hasseProduct_eq_one_of_coe_eq_ratCast` and
  `QuadraticForm.isAdmissible_globalInvariants_of_coe_eq_ratCast`: the Hasse product formula, and
  admissibility of the system of local invariants, for a form with a rational diagonalization.
* `QuadraticForm.globalInvariants_hasseProduct_eq_one_rat` and
  `QuadraticForm.isAdmissible_globalInvariants_rat`: the same for every regular form over `ℚ`.

## References

* J.-P. Serre, *A Course in Arithmetic*, Springer (1973), Chapter III, §2, Theorem 3, and
  Chapter IV, §3.1, condition (1) for the Hasse invariants of a form over `ℚ`.
* O. T. O'Meara, *Introduction to Quadratic Forms*, Springer (1963), 71:18, and 72:1 for the
  conditions satisfied by the local invariants of a global form.
-/

public section

noncomputable section

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField

namespace TauCeti

variable {K : Type} [Field K] [NumberField K]

open scoped Classical in
/-- **Hilbert's product formula for a cyclotomic radicand.** For `a, b ∈ Kˣ`, if some square root
of `b` in `Kˢ` lies in the cyclotomic extension `K(μ_m)` for some `m ≠ 0`, then the product of the
norm-equation Hilbert symbols `(a_v, b_v)_v` over the finite places and of the real Hilbert
symbols `(a_w, b_w)_w` over the real places of `K` is `1`. -/
theorem finprod_hilbertSymbol_mul_prod_hilbertSymbol_eq_one_of_mem_adjoin (a b : Kˣ)
    {s : SeparableClosure K} (hs : s ^ 2 = algebraMap K (SeparableClosure K) b) {m : ℕ}
    (hm : m ≠ 0)
    (hsm : s ∈ IntermediateField.adjoin K {x : SeparableClosure K | x ^ m = 1}) :
    (∏ᶠ v : HeightOneSpectrum (𝓞 K),
        hilbertSymbol (v.unitAtFinitePlace a) (v.unitAtFinitePlace b)) *
      ∏ w : {w : InfinitePlace K // w.IsReal},
        hilbertSymbol (unitAtRealPlace w a) (unitAtRealPlace w b) = 1 := by
  rw [finprod_hilbertSymbol_mul_prod_hilbertSymbol_eq_hilbertSign,
    ClassFieldTheory.hilbertProductFormula_of_mem_adjoin a b hs hm hsm, hilbertSign_zero]

open scoped Classical in
/-- **Hilbert's product formula for a rational radicand.** For `a, b ∈ Kˣ` with `b` rational, the
product of the norm-equation Hilbert symbols `(a_v, b_v)_v` over the finite places and of the real
Hilbert symbols `(a_w, b_w)_w` over the real places of `K` is `1`. -/
theorem finprod_hilbertSymbol_mul_prod_hilbertSymbol_eq_one_of_coe_eq_ratCast (a b : Kˣ) {q : ℚ}
    (hb : (b : K) = q) :
    (∏ᶠ v : HeightOneSpectrum (𝓞 K),
        hilbertSymbol (v.unitAtFinitePlace a) (v.unitAtFinitePlace b)) *
      ∏ w : {w : InfinitePlace K // w.IsReal},
        hilbertSymbol (unitAtRealPlace w a) (unitAtRealPlace w b) = 1 := by
  rw [finprod_hilbertSymbol_mul_prod_hilbertSymbol_eq_hilbertSign,
    ClassFieldTheory.hilbertProductFormula_of_coe_eq_ratCast a b hb, hilbertSign_zero]

/-- **Hilbert's product formula over `ℚ`.** For `a, b ∈ ℚˣ`, the product over the primes `ℓ` of the
Hilbert symbols `(a, b)_ℓ` computed in `ℚ_ℓ`, times the Hilbert symbol `(a, b)_∞` computed in `ℝ`,
is `1`. -/
theorem finprod_hilbertSymbol_padic_mul_hilbertSymbol_real_eq_one (a b : ℚˣ) :
    (∏ᶠ ℓ : Nat.Primes, hilbertSymbol (Units.map (algebraMap ℚ ℚ_[ℓ]).toMonoidHom a)
        (Units.map (algebraMap ℚ ℚ_[ℓ]).toMonoidHom b)) *
      hilbertSymbol (Units.map (algebraMap ℚ ℝ).toMonoidHom a)
        (Units.map (algebraMap ℚ ℝ).toMonoidHom b) = 1 := by
  classical
  -- The unique real place of `ℚ` is the inclusion `ℚ → ℝ`.
  have hreal (x : ℚˣ) (w : {w : InfinitePlace ℚ // w.IsReal}) :
      unitAtRealPlace w x = Units.map (algebraMap ℚ ℝ).toMonoidHom x := by
    ext
    simp [eq_ratCast]
  have h := finprod_hilbertSymbol_mul_prod_hilbertSymbol_eq_one_of_coe_eq_ratCast a b
    (Rat.cast_id (b : ℚ)).symm
  rwa [Fintype.prod_subsingleton _ ⟨Rat.infinitePlace, Rat.isReal_infinitePlace⟩, hreal, hreal,
    ← finprod_comp_equiv (Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).symm,
    finprod_congr fun ℓ ↦ hilbertSymbol_unitAtFinitePlace_rat ℓ a b] at h

end TauCeti

namespace QuadraticForm

open Finset

variable {K : Type} [Field K] [NumberField K]
variable {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
variable (Q : _root_.QuadraticForm K V) (hQ : Q.Nondegenerate)

/-- **The Hasse product formula for a form with rational coefficients.** If a regular form `Q`
over a number field `K` is isometric to `⟨a₁, …, aₙ⟩` with every `aᵢ` rational, the product of the
finite Hasse signs and the real Hasse signs of `Q` is `1`. -/
theorem globalInvariants_hasseProduct_eq_one_of_coe_eq_ratCast {n : ℕ} {a : Fin n → Kˣ}
    (h : Q.Equivalent (QuadraticMap.weightedSumSquares K fun i => (a i : K)))
    {q : Fin n → ℚ} (hq : ∀ i, (a i : K) = q i) :
    (Q.globalInvariants hQ).hasseProduct = 1 := by
  rw [Q.globalInvariants_hasseProduct_eq_prod hQ h]
  exact prod_eq_one fun i _ => prod_eq_one fun j _ =>
    TauCeti.finprod_hilbertSymbol_mul_prod_hilbertSymbol_eq_one_of_coe_eq_ratCast _ _ (hq j)

/-- **The local invariants of a form with rational coefficients are admissible.** If a regular
form `Q` of positive rank over a number field `K` is isometric to `⟨a₁, …, aₙ⟩` with every `aᵢ`
rational, its system of local invariants is admissible. -/
theorem isAdmissible_globalInvariants_of_coe_eq_ratCast (hn : 1 ≤ Module.finrank K V) {n : ℕ}
    {a : Fin n → Kˣ} (h : Q.Equivalent (QuadraticMap.weightedSumSquares K fun i => (a i : K)))
    {q : Fin n → ℚ} (hq : ∀ i, (a i : K) = q i) :
    (Q.globalInvariants hQ).IsAdmissible :=
  (Q.isAdmissible_globalInvariants_iff hQ).mpr
    ⟨hn, Q.globalInvariants_hasseProduct_eq_one_of_coe_eq_ratCast hQ h hq⟩

variable {V : Type*} [AddCommGroup V] [Module ℚ V] [FiniteDimensional ℚ V]
variable (Q : _root_.QuadraticForm ℚ V) (hQ : Q.Nondegenerate)

/-- **The Hasse product formula over `ℚ`.** For every regular form `Q` over `ℚ`, the product of
the Hasse signs of `Q` at the primes and of its Hasse sign at the real place is `1`. -/
theorem globalInvariants_hasseProduct_eq_one_rat : (Q.globalInvariants hQ).hasseProduct = 1 := by
  obtain ⟨a, h⟩ := Q.equivalent_weightedSumSquares_units_of_nondegenerate'
    (QuadraticMap.nondegenerate_associated_iff.mpr hQ).1
  rw [QuadraticMap.weightedSumSquares_units] at h
  exact Q.globalInvariants_hasseProduct_eq_one_of_coe_eq_ratCast hQ h fun i => (Rat.cast_id _).symm

/-- **The local invariants of a form over `ℚ` are admissible.** The system of local invariants of
every regular form of positive rank over `ℚ` is admissible. -/
theorem isAdmissible_globalInvariants_rat (hn : 1 ≤ Module.finrank ℚ V) :
    (Q.globalInvariants hQ).IsAdmissible :=
  (Q.isAdmissible_globalInvariants_iff hQ).mpr ⟨hn, Q.globalInvariants_hasseProduct_eq_one_rat hQ⟩

end QuadraticForm

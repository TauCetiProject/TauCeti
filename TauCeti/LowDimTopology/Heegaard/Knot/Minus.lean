/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Module.GradedModule.Homology
public import TauCeti.LowDimTopology.Heegaard.Grading
public import TauCeti.LowDimTopology.Heegaard.Knot.Differential
public import TauCeti.LowDimTopology.Heegaard.Knot.EulerCharacteristic

import TauCeti.Algebra.MvPolynomial.AevalConstX

/-!
# The minus knot Floer complex `CFK⁻` of a doubly pointed Heegaard diagram

Let `(Σ, α, β, w, z)` be a doubly pointed Heegaard diagram of a knot, recorded by region incidence
data `H : TauCeti.HeegaardRegionSystem` in which two basepoints `w` and `z` are singled out. Its
full knot Floer complex over `𝔽₂[U, V]` (`TauCeti.HeegaardRegionSystem.knotDifferential`) counts
the nonnegative domains `D` of Maslov index one with weight `U ^ n_w(D) V ^ n_z(D)`. Setting
`V = 0` keeps the domains with `n_z(D) = 0`, weighted by `U ^ n_w(D)`: this is the minus knot
Floer complex `CFK⁻`, a free `𝔽₂[U]`-module on the generators, whose homology `HFK⁻` is the
module from which the concordance invariant `τ` is read
(`TauCeti.LowDimTopology.Heegaard.Knot.Tau`). It is the doubly pointed analogue of the unblocked
grid complex `GC⁻`, in which the variables of the `O`-markings are kept and the `X`-markings are
blocked.

* The **minus knot coefficient** `H.knotMinusCoefficient χ w z x y : (ZMod 2)[X]` is the knot
  coefficient evaluated at `U = X`, `V = 0`. When finitely many domains are counted, it is the sum
  of `U ^ n_w(D)` over the counted domains from `x` to `y` with `n_z(D) = 0`
  (`knotMinusCoefficient_eq_sum`), and its coefficient of `U ^ k` is the number of them with
  `n_w(D) = k`, modulo two (`coeff_knotMinusCoefficient`).
* The **minus knot differential** `H.knotMinusDifferential χ w z` is the `𝔽₂[U]`-linear
  endomorphism of the free `𝔽₂[U]`-module on the generators with these coefficients. Evaluating
  `V = 0` on chains intertwines it with the full knot differential
  (`mapRange_aeval_X_zero_knotDifferential`), so it squares to zero as soon as the full knot
  differential does (`knotMinusDifferential_comp_self_eq_zero`). Setting further `U = 0` gives the
  hat knot Floer differential (`mapRange_constantCoeff_knotMinusDifferential`).

**Gradings.** For a knot grading `(M, A)` (`TauCeti.HeegaardRegionSystem.IsKnotGrading`), the
chain `U ^ k x` has Alexander grading `A(x) - k` (`knotMinusAlexanderGrading`). A term `U ^ k y` of
the differential of `x` comes from a domain `D` from `x` to `y` with `n_w(D) = k`, `n_z(D) = 0` and
`μ(D) = 1`, so that `A(x) = A(y) - k` and `M(x) = M(y) - 2 k + 1`
(`IsKnotGrading.alexander_eq_sub_of_coeff_knotMinusCoefficient_ne_zero` and
`IsKnotGrading.maslov_eq_sub_add_one_of_coeff_knotMinusCoefficient_ne_zero`): the differential
preserves the Alexander grading and lowers the Maslov grading `M(x) - 2 k` of `U ^ k x` by one.
Hence the minus knot differential is homogeneous of degree `0` for the Alexander grading
(`IsKnotGrading.isHomogeneous_knotMinusDifferential_alexander`), on which `U` acts with degree
`-1`. When the differential squares to zero, its homology `HFK⁻` (`knotMinusHomology`), a module
over `𝔽₂[U]`, inherits the Alexander grading
(`IsKnotGrading.knotMinusHomologyAlexanderGrading`), and `U` still lowers it by one
(`IsKnotGrading.X_smul_mem_knotMinusHomologyAlexanderGrading_piece`); shifting `A` by a constant
shifts this grading (`IsKnotGrading.knotMinusHomologyAlexanderGrading_add_const`). A nonzero chain
of Alexander degree `a` involves a generator `x` with `a ≤ A(x)`
(`exists_le_of_mem_knotMinusAlexanderPiece`), which bounds the degrees of `HFK⁻` from above.

As for the other differentials of `TauCeti.HeegaardRegionSystem`, these are counts of domains rather
than of holomorphic disks; they agree with the holomorphic counts only for diagrams in which each
counted domain carries exactly one holomorphic disk modulo translation, and neither that condition
nor `∂ ∘ ∂ = 0` is formalized here. The results about homology carry `∂ ∘ ∂ = 0` as a hypothesis.

## Main definitions

* `TauCeti.HeegaardRegionSystem.knotMinusCoefficient`: the knot coefficient at `U = X`, `V = 0`.
* `TauCeti.HeegaardRegionSystem.knotMinusDifferential`: the differential of `CFK⁻`.
* `TauCeti.HeegaardRegionSystem.knotMinusAlexanderGrading`: the Alexander grading of `CFK⁻`, in
  which `U ^ k x` has degree `A(x) - k`, an instance of
  `TauCeti.HeegaardRegionSystem.monomialGrading`.
* `TauCeti.HeegaardRegionSystem.knotMinusHomology`: the homology `HFK⁻`.
* `TauCeti.HeegaardRegionSystem.IsKnotGrading.knotMinusHomologyAlexanderGrading`: its Alexander
  grading.

## Main results

* `TauCeti.HeegaardRegionSystem.coeff_knotMinusCoefficient`: the coefficients count the domains
  with `n_z = 0` by their multiplicity at `w`.
* `TauCeti.HeegaardRegionSystem.mapRange_aeval_X_zero_knotDifferential` and
  `TauCeti.HeegaardRegionSystem.knotMinusDifferential_comp_self_eq_zero`: `CFK⁻` is the
  specialization `V = 0` of the full knot complex.
* `TauCeti.HeegaardRegionSystem.mapRange_constantCoeff_knotMinusDifferential`: setting `U = 0`
  gives the hat knot Floer differential.
* In the namespace `TauCeti.HeegaardRegionSystem.IsKnotGrading`,
  `alexander_eq_sub_of_coeff_knotMinusCoefficient_ne_zero` and
  `maslov_eq_sub_add_one_of_coeff_knotMinusCoefficient_ne_zero`: the differential preserves the
  Alexander grading and lowers the Maslov grading by one.
* `TauCeti.HeegaardRegionSystem.IsKnotGrading.isHomogeneous_knotMinusDifferential_alexander`: the
  differential has Alexander degree `0`.
* `TauCeti.HeegaardRegionSystem.IsKnotGrading.X_smul_mem_knotMinusHomologyAlexanderGrading_piece`:
  `U` lowers the Alexander grading of `HFK⁻` by one.
* `TauCeti.HeegaardRegionSystem.IsKnotGrading.knotMinusHomologyAlexanderGrading_add_const`:
  shifting the Alexander grading by `a` shifts the grading of `HFK⁻` by `a`.

## References

* P. Ozsváth and Z. Szabó, *Holomorphic disks and knot invariants*, Adv. Math. **186** (2004),
  [arXiv:math/0209056](https://arxiv.org/abs/math/0209056), §3 (the complexes `CFK^∞` and their
  subquotients, the gradings and the action of `U`).
* P. Ozsváth, A. Stipsicz and Z. Szabó, *Grid Homology for Knots and Links*, AMS Mathematical
  Surveys and Monographs 208, 2015, Chapters 4 and 6 (the minus version `GC⁻` with the
  `X`-markings blocked, and `U` of Alexander degree `-1`).
-/

public section

open Polynomial

namespace TauCeti

namespace HeegaardRegionSystem

universe u v w

variable {n : ℕ} {Point : Type u} {Region : Type v} {Basepoint : Type w}
  {H : HeegaardRegionSystem n Point Region Basepoint}

section ChainGrading

variable (H) (A : H.Generator → ℤ)

/-- The degree-`a` piece of `CFK⁻` for an Alexander grading `A` of the generators: the span of the
chains `U ^ k x` with `A(x) - k = a`. -/
noncomputable def knotMinusAlexanderPiece (a : ℤ) :
    Submodule (ZMod 2) (H.Generator →₀ (ZMod 2)[X]) :=
  H.monomialGradedPiece (fun x k => A x - k) a

/-- The Alexander grading of `CFK⁻` by an Alexander grading `A` of the generators, in which
`U ^ k x` has degree `A(x) - k`. -/
noncomputable def knotMinusAlexanderGrading :
    InternalGrading (ZMod 2) (H.Generator →₀ (ZMod 2)[X]) ℤ :=
  H.monomialGrading fun x k => A x - k

variable {H A}

@[simp]
theorem knotMinusAlexanderGrading_piece :
    (H.knotMinusAlexanderGrading A).piece = H.knotMinusAlexanderPiece A :=
  monomialGrading_piece

/-- A chain of `CFK⁻` has Alexander degree `a` exactly when each of its terms `U ^ k x` has
`A(x) - k = a`. -/
@[simp]
theorem mem_knotMinusAlexanderPiece_iff {a : ℤ} {c : H.Generator →₀ (ZMod 2)[X]} :
    c ∈ H.knotMinusAlexanderPiece A a ↔ ∀ x (k : ℕ), (c x).coeff k ≠ 0 → A x - k = a :=
  mem_monomialGradedPiece_iff

/-- The chain `U ^ k x` of `CFK⁻` has Alexander degree `A(x) - k`. -/
theorem single_X_pow_mem_knotMinusAlexanderPiece (x : H.Generator) (k : ℕ) :
    Finsupp.single x (X ^ k : (ZMod 2)[X]) ∈ H.knotMinusAlexanderPiece A (A x - k) :=
  single_X_pow_mem_monomialGradedPiece x k

/-- **`U` lowers the Alexander grading of `CFK⁻` by one.** -/
theorem X_smul_mem_knotMinusAlexanderPiece {a : ℤ} {c : H.Generator →₀ (ZMod 2)[X]}
    (hc : c ∈ H.knotMinusAlexanderPiece A a) :
    (X : (ZMod 2)[X]) • c ∈ H.knotMinusAlexanderPiece A (a - 1) :=
  X_smul_mem_monomialGradedPiece (fun x k => by push_cast; ring) hc

/-- A nonzero chain of `CFK⁻` of Alexander degree `a` has a generator `x` with `a ≤ A(x)`: the
powers of `U` only lower the degree. -/
theorem exists_le_of_mem_knotMinusAlexanderPiece {a : ℤ} {c : H.Generator →₀ (ZMod 2)[X]}
    (hc : c ∈ H.knotMinusAlexanderPiece A a) (hc0 : c ≠ 0) : ∃ x, a ≤ A x := by
  obtain ⟨x, hx⟩ := Finsupp.ne_iff.mp hc0
  obtain ⟨k, hk⟩ := (support_nonempty (p := c x)).mpr (by simpa using hx)
  refine ⟨x, ?_⟩
  rw [← mem_knotMinusAlexanderPiece_iff.mp hc x k (mem_support_iff.mp hk)]
  omega

end ChainGrading

variable [Fintype Point] [DecidableEq Region] [Fintype Region]

section Coefficient

variable (H) in
/-- The coefficient of the generator `y` in the minus knot Floer differential of the generator `x`:
the knot coefficient `∑ U ^ n_w(D) V ^ n_z(D)` (`TauCeti.HeegaardRegionSystem.knotCoefficient`)
evaluated at `U = X` and `V = 0`. When the set `H.minusDomains χ x y` of nonnegative domains of
Maslov index one from `x` to `y` is finite, this is the sum of `X ^ n_w(D)` over those domains `D`
with `n_z(D) = 0` (`knotMinusCoefficient_eq_sum`); for an infinite set it is `0`
(`knotMinusCoefficient_eq_zero_of_infinite`). -/
noncomputable def knotMinusCoefficient (χ : Region → ℤ) (w z : Basepoint) (x y : H.Generator) :
    (ZMod 2)[X] :=
  MvPolynomial.aeval ![(X : (ZMod 2)[X]), 0] (H.knotCoefficient χ w z x y)

variable {χ : Region → ℤ} {w z : Basepoint} {x y : H.Generator}

theorem knotMinusCoefficient_def : H.knotMinusCoefficient χ w z x y =
    MvPolynomial.aeval ![(X : (ZMod 2)[X]), 0] (H.knotCoefficient χ w z x y) :=
  (rfl)

/-- When infinitely many domains are counted, the minus knot coefficient is `0`. -/
theorem knotMinusCoefficient_eq_zero_of_infinite (h : (H.minusDomains χ x y).Infinite) :
    H.knotMinusCoefficient χ w z x y = 0 := by
  rw [knotMinusCoefficient_def, knotCoefficient_eq_zero_of_infinite h, map_zero]

/-- The minus knot coefficient vanishes when no domain is counted. -/
theorem knotMinusCoefficient_eq_zero_of_minusDomains_eq_empty (h : H.minusDomains χ x y = ∅) :
    H.knotMinusCoefficient χ w z x y = 0 := by
  rw [knotMinusCoefficient_def, knotCoefficient_eq_zero_of_minusDomains_eq_empty h, map_zero]

/-- When finitely many domains are counted, the minus knot coefficient is the sum of
`X ^ n_w(D)` over the counted domains `D` from `x` to `y` with `n_z(D) = 0`. -/
theorem knotMinusCoefficient_eq_sum (hfin : (H.minusDomains χ x y).Finite) :
    H.knotMinusCoefficient χ w z x y =
      ∑ D ∈ hfin.toFinset with D (H.basepoint z) = 0, X ^ (D (H.basepoint w)).toNat := by
  rw [knotMinusCoefficient_def, knotCoefficient_eq_sum hfin, map_sum, Finset.sum_filter]
  refine Finset.sum_congr rfl fun D hD => ?_
  have hz := basepoint_nonneg_of_mem_minusDomains (hfin.mem_toFinset.mp hD) z
  simp only [map_mul, map_pow, MvPolynomial.aeval_X, Matrix.cons_val_zero, Matrix.cons_val_one]
  split_ifs with h
  · simp [h]
  · rw [zero_pow (by omega), mul_zero]

/-- The coefficient of `X ^ k` in the minus knot coefficient from `x` to `y` is the number, modulo
two, of counted domains from `x` to `y` with multiplicity `k` at `w` and `0` at `z`. -/
theorem coeff_knotMinusCoefficient (hfin : (H.minusDomains χ x y).Finite) (k : ℕ) :
    (H.knotMinusCoefficient χ w z x y).coeff k =
      {D ∈ H.minusDomains χ x y | D (H.basepoint w) = k ∧ D (H.basepoint z) = 0}.ncard := by
  classical
  rw [knotMinusCoefficient_eq_sum hfin, finsetSum_coeff]
  simp only [coeff_X_pow, Finset.sum_boole, Finset.filter_filter]
  rw [← Set.ncard_coe_finset]
  congr 2
  ext D
  simp only [Finset.coe_filter, Set.Finite.mem_toFinset, Set.mem_ofPred_eq]
  refine and_congr_right fun hD => ?_
  have hw := basepoint_nonneg_of_mem_minusDomains hD w
  omega

/-- A nonzero coefficient of `X ^ k` in the minus knot coefficient from `x` to `y` comes from a
counted domain from `x` to `y` with multiplicity `k` at `w` and `0` at `z`. -/
theorem exists_mem_minusDomains_of_coeff_knotMinusCoefficient_ne_zero {k : ℕ}
    (h : (H.knotMinusCoefficient χ w z x y).coeff k ≠ 0) :
    ∃ D ∈ H.minusDomains χ x y, D (H.basepoint w) = k ∧ D (H.basepoint z) = 0 := by
  by_cases hfin : (H.minusDomains χ x y).Finite
  · rw [coeff_knotMinusCoefficient hfin] at h
    obtain ⟨D, hD, hDw, hDz⟩ :=
      Set.nonempty_of_ncard_ne_zero fun h0 => h (by rw [h0, Nat.cast_zero])
    exact ⟨D, hD, hDw, hDz⟩
  · rw [knotMinusCoefficient_eq_zero_of_infinite hfin] at h
    exact absurd (coeff_zero k) h

/-- **Setting `U = 0` gives the hat knot Floer coefficient.** When finitely many domains are
counted, the constant coefficient of the minus knot coefficient is the hat coefficient of the
diagram pointed at `w` and `z` alone, which counts the domains avoiding both basepoints. -/
theorem constantCoeff_knotMinusCoefficient (hfin : (H.minusDomains χ x y).Finite) :
    constantCoeff (H.knotMinusCoefficient χ w z x y) =
      (H.withBasepoints ![H.basepoint w, H.basepoint z]).hatCoefficient χ x y := by
  -- Both sides are ring homomorphisms of the knot coefficient that kill `U` and `V`.
  have hcomp : (constantCoeff : (ZMod 2)[X] →+* ZMod 2).comp
      (MvPolynomial.aeval ![(X : (ZMod 2)[X]), 0]).toRingHom = MvPolynomial.constantCoeff := by
    refine MvPolynomial.ringHom_ext (fun r => ?_) fun i => ?_
    · simp
    · fin_cases i <;> simp
  rw [← constantCoeff_knotCoefficient hfin, knotMinusCoefficient_def]
  simpa using RingHom.congr_fun hcomp (H.knotCoefficient χ w z x y)

end Coefficient

section Grading

variable {χ : Region → ℤ} {w z : Basepoint} {x y : H.Generator} {M A : H.Generator → ℤ}

namespace IsKnotGrading

/-- **The minus knot differential preserves the Alexander grading.** If the minus knot coefficient
from `x` to `y` has a nonzero coefficient of `U ^ k`, then `A(x) = A(y) - k`, the Alexander grading
of `U ^ k y`. -/
theorem alexander_eq_sub_of_coeff_knotMinusCoefficient_ne_zero (h : H.IsKnotGrading χ w z M A)
    {k : ℕ} (hc : (H.knotMinusCoefficient χ w z x y).coeff k ≠ 0) : A x = A y - k := by
  obtain ⟨D, hD, hw, hz⟩ := exists_mem_minusDomains_of_coeff_knotMinusCoefficient_ne_zero hc
  have hA := h.alexander_sub_alexander (mem_minusDomains_iff.mp hD).1
  omega

/-- **The minus knot differential lowers the Maslov grading by one.** If the minus knot coefficient
from `x` to `y` has a nonzero coefficient of `U ^ k`, then `M(x) = M(y) - 2 k + 1`, one more than
the Maslov grading of `U ^ k y`. -/
theorem maslov_eq_sub_add_one_of_coeff_knotMinusCoefficient_ne_zero
    (h : H.IsKnotGrading χ w z M A) {k : ℕ} (hc : (H.knotMinusCoefficient χ w z x y).coeff k ≠ 0) :
    M x = M y - 2 * k + 1 := by
  obtain ⟨D, hD, hw, -⟩ := exists_mem_minusDomains_of_coeff_knotMinusCoefficient_ne_zero hc
  obtain ⟨hD, -, hμ⟩ := mem_minusDomains_iff.mp hD
  have hM := h.maslov_sub_maslov hD
  rw [hμ, hw] at hM
  have hM' : M x - M y = 1 - 2 * k := by exact_mod_cast hM
  omega

end IsKnotGrading

end Grading

section Differential

variable (H) in
/-- The minus knot Floer differential of a doubly pointed Heegaard diagram with region Euler
characteristics `χ`: the `(ZMod 2)[X]`-linear endomorphism of the free `(ZMod 2)[X]`-module on the
generators whose coefficient from `x` to `y` is the sum of `U ^ n_w(D)`, with `U = X`, over the
nonnegative domains `D` of Maslov index one from `x` to `y` with `n_z(D) = 0`
(`TauCeti.HeegaardRegionSystem.knotMinusCoefficient`). It is the full knot differential at `V = 0`
(`mapRange_aeval_X_zero_knotDifferential`). -/
noncomputable def knotMinusDifferential (χ : Region → ℤ) (w z : Basepoint) :
    (H.Generator →₀ (ZMod 2)[X]) →ₗ[(ZMod 2)[X]] H.Generator →₀ (ZMod 2)[X] :=
  Finsupp.linearCombination (ZMod 2)[X] fun x =>
    Finsupp.equivFunOnFinite.symm (H.knotMinusCoefficient χ w z x)

variable {χ : Region → ℤ} {w z : Basepoint}

/-- The matrix coefficients of the minus knot differential are the polynomials
`TauCeti.HeegaardRegionSystem.knotMinusCoefficient`. -/
@[simp]
theorem knotMinusDifferential_single_apply (x y : H.Generator) (a : (ZMod 2)[X]) :
    H.knotMinusDifferential χ w z (Finsupp.single x a) y = a * H.knotMinusCoefficient χ w z x y :=
  Finsupp.linearCombination_equivFunOnFinite_symm_single_apply _ x y a

/-- The coefficient of `y` in the minus knot differential of a chain `c`. -/
theorem knotMinusDifferential_apply (c : H.Generator →₀ (ZMod 2)[X]) (y : H.Generator) :
    H.knotMinusDifferential χ w z c y = c.sum fun x a => a * H.knotMinusCoefficient χ w z x y :=
  Finsupp.linearCombination_equivFunOnFinite_symm_apply _ c y

/-- The minus knot differential vanishes exactly when all of its coefficients vanish. -/
theorem knotMinusDifferential_eq_zero_iff :
    H.knotMinusDifferential χ w z = 0 ↔ ∀ x y, H.knotMinusCoefficient χ w z x y = 0 :=
  Finsupp.linearCombination_equivFunOnFinite_symm_eq_zero_iff

/-- **Setting `V = 0` gives the minus knot differential.** Evaluating `U = X` and `V = 0` in the
coefficients of a chain intertwines the full knot differential with the minus knot
differential. -/
theorem mapRange_aeval_X_zero_knotDifferential
    (c : H.Generator →₀ MvPolynomial (Fin 2) (ZMod 2)) :
    Finsupp.mapRange (MvPolynomial.aeval ![(X : (ZMod 2)[X]), 0]) (map_zero _)
        (H.knotDifferential χ w z c) =
      H.knotMinusDifferential χ w z
        (Finsupp.mapRange (MvPolynomial.aeval ![(X : (ZMod 2)[X]), 0]) (map_zero _) c) := by
  ext y
  rw [← fullDifferential_withBasepoints_eq_knotDifferential, mapRange_fullDifferential_apply,
    knotMinusDifferential_apply]
  simp only [fullCoefficient_withBasepoints_eq_knotCoefficient, knotMinusCoefficient_def]

/-- **`CFK⁻` squares to zero when the full knot complex does.** If the full knot differential
over `𝔽₂[U, V]` squares to zero, so does its specialization `V = 0`, the minus knot
differential. -/
theorem knotMinusDifferential_comp_self_eq_zero
    (hd : H.knotDifferential χ w z ∘ₗ H.knotDifferential χ w z = 0) :
    H.knotMinusDifferential χ w z ∘ₗ H.knotMinusDifferential χ w z = 0 := by
  refine LinearMap.ext fun c => ?_
  -- Every chain over `𝔽₂[U]` is the image of a chain over `𝔽₂[U, V]`.
  obtain ⟨c, rfl⟩ := Finsupp.mapRange_surjective _ (map_zero _)
    (MvPolynomial.aeval_surjective_of_eq_X (f := ![(X : (ZMod 2)[X]), 0]) (i := 0) rfl) c
  rw [LinearMap.comp_apply, ← mapRange_aeval_X_zero_knotDifferential,
    ← mapRange_aeval_X_zero_knotDifferential, ← LinearMap.comp_apply, hd, LinearMap.zero_apply,
    Finsupp.mapRange_zero, LinearMap.zero_apply]

/-- **Setting `U = 0` gives the hat knot Floer differential.** When the counts are finite, taking
constant coefficients of a chain intertwines the minus knot differential with the hat
differential of the diagram pointed at `w` and `z` alone. -/
theorem mapRange_constantCoeff_knotMinusDifferential (hfin : ∀ x y, (H.minusDomains χ x y).Finite)
    (c : H.Generator →₀ (ZMod 2)[X]) :
    Finsupp.mapRange constantCoeff (map_zero _) (H.knotMinusDifferential χ w z c) =
      (H.withBasepoints ![H.basepoint w, H.basepoint z]).hatDifferential χ
        (Finsupp.mapRange constantCoeff (map_zero _) c) := by
  ext y
  rw [Finsupp.mapRange_apply, knotMinusDifferential_apply, hatDifferential_apply,
    Finsupp.sum_mapRange_index fun _ => zero_mul _, map_finsuppSum]
  refine Finsupp.sum_congr fun x _ => ?_
  rw [map_mul, constantCoeff_knotMinusCoefficient (hfin x y)]

end Differential

section DifferentialGrading

variable {χ : Region → ℤ} {w z : Basepoint} {M A : H.Generator → ℤ}

namespace IsKnotGrading

/-- **The minus knot differential has Alexander degree `0`** for the Alexander component of a knot
grading. -/
theorem isHomogeneous_knotMinusDifferential_alexander (h : H.IsKnotGrading χ w z M A) :
    LinearMap.IsHomogeneous (H.knotMinusDifferential χ w z) (H.knotMinusAlexanderPiece A)
      (H.knotMinusAlexanderPiece A) 0 := by
  unfold knotMinusAlexanderPiece
  refine isHomogeneous_monomialGradedPiece _ knotMinusDifferential_single_apply
    fun x y k j hj => ?_
  have := h.alexander_eq_sub_of_coeff_knotMinusCoefficient_ne_zero hj
  push_cast
  omega

end IsKnotGrading

end DifferentialGrading

section Homology

variable (H) in
/-- The **minus knot Floer homology** `HFK⁻ = ker ∂⁻ ⧸ im ∂⁻` of a doubly pointed diagram whose
minus knot differential `∂⁻`, for the region Euler characteristics `χ`, squares to zero: a module
over `(ZMod 2)[X]`, with `X` acting as `U`. -/
abbrev knotMinusHomology (χ : Region → ℤ) (w z : Basepoint)
    (hd : H.knotMinusDifferential χ w z ∘ₗ H.knotMinusDifferential χ w z = 0) : Type _ :=
  (H.knotMinusDifferential χ w z).homology hd

variable {χ : Region → ℤ} {w z : Basepoint} {M A : H.Generator → ℤ}
  {hd : H.knotMinusDifferential χ w z ∘ₗ H.knotMinusDifferential χ w z = 0}

namespace IsKnotGrading

variable (hd) in
/-- The **Alexander grading of `HFK⁻`** for the Alexander component `A` of a knot grading: the
piece of degree `a` consists of the classes of cycles of Alexander degree `a`, in which `U ^ k x`
has degree `A(x) - k`. -/
noncomputable def knotMinusHomologyAlexanderGrading (h : H.IsKnotGrading χ w z M A) :
    InternalGrading (ZMod 2) (H.knotMinusHomology χ w z hd) ℤ :=
  (H.knotMinusAlexanderGrading A).homology
    (knotMinusAlexanderGrading_piece ▸ h.isHomogeneous_knotMinusDifferential_alexander) hd

/-- A class of `HFK⁻` has Alexander degree `a` exactly when it is the class of a cycle all of whose
terms `U ^ k x` have `A(x) - k = a`. -/
theorem mem_knotMinusHomologyAlexanderGrading_piece_iff (h : H.IsKnotGrading χ w z M A) {a : ℤ}
    {y : H.knotMinusHomology χ w z hd} :
    y ∈ (h.knotMinusHomologyAlexanderGrading hd).piece a ↔
      ∃ c : LinearMap.ker (H.knotMinusDifferential χ w z),
        (c : H.Generator →₀ (ZMod 2)[X]) ∈ H.knotMinusAlexanderPiece A a ∧
          (H.knotMinusDifferential χ w z).homologyπ hd c = y := by
  rw [knotMinusHomologyAlexanderGrading, InternalGrading.mem_homology_piece_iff,
    knotMinusAlexanderGrading_piece]

/-- **`U` lowers the Alexander grading of `HFK⁻` by one.** -/
theorem X_smul_mem_knotMinusHomologyAlexanderGrading_piece (h : H.IsKnotGrading χ w z M A)
    {a : ℤ} {y : H.knotMinusHomology χ w z hd}
    (hy : y ∈ (h.knotMinusHomologyAlexanderGrading hd).piece a) :
    (X : (ZMod 2)[X]) • y ∈ (h.knotMinusHomologyAlexanderGrading hd).piece (a - 1) := by
  rw [sub_eq_add_neg]
  refine InternalGrading.smul_mem_homology_piece _ _ _ (fun _ _ hc => ?_) hy
  rw [knotMinusAlexanderGrading_piece] at hc ⊢
  simpa [sub_eq_add_neg] using X_smul_mem_knotMinusAlexanderPiece hc

/-- **Shifting the Alexander grading by `a` shifts the grading of `HFK⁻` by `a`**: the Alexander
grading of `HFK⁻` for `A + a` is the shift by `-a` of the one for `A`, whose degree-`p` piece is
the degree-`(p - a)` piece. -/
theorem knotMinusHomologyAlexanderGrading_add_const (h : H.IsKnotGrading χ w z M A) (m a : ℤ) :
    (h.add_const m a).knotMinusHomologyAlexanderGrading hd =
      (h.knotMinusHomologyAlexanderGrading hd).shift (-a) := by
  refine InternalGrading.ext fun p => Submodule.ext fun y => ?_
  have hpiece (c : H.Generator →₀ (ZMod 2)[X]) :
      c ∈ H.knotMinusAlexanderPiece (fun x => A x + a) p ↔
        c ∈ H.knotMinusAlexanderPiece A (p + -a) := by
    simp only [mem_knotMinusAlexanderPiece_iff]
    exact forall₃_congr fun x k _ => by omega
  rw [InternalGrading.shift_piece, mem_knotMinusHomologyAlexanderGrading_piece_iff,
    mem_knotMinusHomologyAlexanderGrading_piece_iff]
  simp only [hpiece]

end IsKnotGrading

end Homology

end HeegaardRegionSystem

end TauCeti

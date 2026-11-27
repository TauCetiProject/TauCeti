/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.ModuleCat.Exact
public import TauCeti.LinearAlgebra.Charpoly.Degree
public import TauCeti.LinearAlgebra.Charpoly.Quotient
public import TauCeti.LinearAlgebra.Matrix.Charpoly.Zeta
public import TauCeti.LinearAlgebra.Trace.Exact
import TauCeti.Algebra.Polynomial.Reverse

/-!
# The Hopf trace formula and its determinant form

Let `φ : K ⟶ K` be a chain endomorphism of a complex of vector spaces over a field `k`. In each
degree `n`, write `Bₙ = im (K.X p ⟶ K.X n)` for the boundaries, with `p = c.prev n`, and
`Zₙ = ker (K.X n ⟶ K.X m)` for the kernel of the outgoing differential, with `m = c.next n`. The
two short exact sequences

```text
0 → Zₙ → K.X n → Bₘ → 0      and      0 → Bₙ → Zₙ → Hₙ(K) → 0
```

are respected by `φ`, and the trace is additive along short exact sequences. When `K.X n` is
finite-dimensional this gives

```text
tr (φₙ) = tr (Hₙ(φ)) + tr (φ | Bₙ) + tr (φ | Bₘ)
```

(`HomologicalComplex.trace_f_eq_trace_homologyMap_add`), where `φ | B` is the restriction
`HomologicalComplex.Hom.boundaryMap` of `φ` to the boundaries.

For a chain complex indexed by `ℕ`, with differentials `Kₙ₊₁ ⟶ Kₙ`, the alternating sum of these
identities telescopes: up to degree `n` the alternating sums of the traces of `φ` on the terms and
on the homology differ by `(-1)ⁿ tr (φ | Bₙ)`
(`ChainComplex.sum_range_trace_f_eq_sum_range_trace_homologyMap_add`). If the differential
`Kₙ₊₁ ⟶ Kₙ` vanishes, for instance if `Kₙ₊₁ = 0`, this last term vanishes and we obtain the
**Hopf trace formula**

```text
∑ᵢ₌₀ⁿ (-1)ⁱ tr (φᵢ) = ∑ᵢ₌₀ⁿ (-1)ⁱ tr (Hᵢ(φ))
```

(`ChainComplex.sum_range_trace_f_eq_sum_range_trace_homologyMap`). Applied to the simplicial or
cellular chains of a finite complex and a chain map inducing a given map on homology, the right
side is the Lefschetz number of that map; this is how the Lefschetz fixed point theorem computes
the Lefschetz number from a chain-level trace. For `φ = 𝟙 K` the traces are dimensions and the
formula is the Euler–Poincaré formula
`ChainComplex.sum_range_finrank_X_eq_sum_range_finrank_homology`.

**The determinant form.** The characteristic polynomial `χ` is multiplicative along short exact
sequences (`LinearMap.charpoly_eq_mul_of_exact`), so the same two sequences give, in every
characteristic,

```text
χ(φₙ) = χ(Hₙ(φ)) · χ(φ | Bₙ) · χ(φ | Bₘ)
```

(`HomologicalComplex.charpoly_f_eq_charpoly_homologyMap_mul`). For a chain complex indexed by `ℕ`
with finite-dimensional terms, the alternating products of these identities telescope
(`ChainComplex.prod_charpoly_f_mul_prod_charpoly_homologyMap_mul`), and when `Kₙ₊₁ ⟶ Kₙ` vanishes

```text
∏ᵢ₌₀ⁿ χ(φᵢ) ^ (-1) ^ i = ∏ᵢ₌₀ⁿ χ(Hᵢ(φ)) ^ (-1) ^ i,
```

stated without inverses (`ChainComplex.prod_charpoly_f_mul_prod_charpoly_homologyMap`). Reversing
the polynomials gives the same identity for the determinants `det (1 - X φ)`
(`ChainComplex.prod_reverse_charpoly_f_mul_prod_reverse_charpoly_homologyMap`): the alternating
product of the `det (1 - X φᵢ)` over the chain groups, the form in which a chain map enters the
torsion of a mapping torus, agrees with the product over the homology. Together with the
trace–determinant formula on the homology (`LinearMap.subst_exp_mul_prod_even_eq_prod_odd`),
this computes the homological zeta function `exp (∑ⱼ L j Xʲ / j)` of the action of `φ` on homology
from the chain map alone (`ChainComplex.subst_exp_mul_prod_even_eq_prod_odd`).

## References

* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, Section 2.C, proof of
  Theorem 2C.3 (the Hopf trace formula), pp. 180–181.
-/

public section

open CategoryTheory LinearMap

universe u v

namespace HomologicalComplex

variable {k : Type u} [Field k] {ι : Type*} {c : ComplexShape ι}
  {K : HomologicalComplex (ModuleCat.{v} k) c}

/-- The trace of `φ` on `K.X n` is its trace on the kernel `Zₙ` of the differential `K.d n m` plus
its trace on the image `Bₘ` of that differential. -/
private theorem trace_f_eq_trace_restrict_ker_add (φ : K ⟶ K) (n m : ι)
    [Module.Finite k (K.X n)] :
    trace k (K.X n) (φ.f n).hom = trace k (ker (K.d n m).hom)
      ((φ.f n).hom.restrict (φ.d_apply_eq_zero_of_d_apply_eq_zero n m)) +
        trace k _ (φ.boundaryMap n m) := by
  refine trace_eq_add_of_exact (ker (K.d n m).hom).injective_subtype
    (K.d n m).hom.surjective_rangeRestrict ?_ (LinearMap.ext fun _ ↦ rfl)
    (LinearMap.ext fun x ↦ Subtype.ext (by simp [Hom.comm_apply]))
  rw [LinearMap.exact_iff, ker_rangeRestrict, Submodule.range_subtype]

/-- The trace of `φ` on the kernel `Zₙ` of the differential `K.d n m` is its trace on the image
`Bₙ` of the incoming differential `K.d p n` plus the trace of `Hₙ(φ)`. -/
private theorem trace_restrict_ker_eq_trace_boundaryMap_add (φ : K ⟶ K) {p n m : ι}
    (hp : c.prev n = p) (hm : c.next n = m) [Module.Finite k (K.X n)] :
    trace k (ker (K.d n m).hom)
        ((φ.f n).hom.restrict (φ.d_apply_eq_zero_of_d_apply_eq_zero n m)) =
      trace k _ (φ.boundaryMap p n) + trace k (K.homology n) (homologyMap φ n).hom := by
  refine trace_eq_add_of_exact (Submodule.inclusion_injective _)
    (K.moduleCatKerHomologyClass_surjective hm) (K.exact_inclusion_moduleCatKerHomologyClass hm hp)
    (LinearMap.ext fun x ↦ Subtype.ext (φ.coe_boundaryMap p n x).symm)
    (LinearMap.ext fun z ↦ (homologyMap_moduleCatKerHomologyClass hm φ z).symm)

/-- The trace of a chain endomorphism `φ` on a finite-dimensional term `K.X n` is the sum of its
trace on the homology `Hₙ(K)`, its trace on the boundaries `Bₙ = im (K.X p ⟶ K.X n)` and its
trace on the boundaries `Bₘ = im (K.X n ⟶ K.X m)`, where `p = c.prev n` and `m = c.next n`. -/
theorem trace_f_eq_trace_homologyMap_add (φ : K ⟶ K) {p n m : ι} (hp : c.prev n = p)
    (hm : c.next n = m) [Module.Finite k (K.X n)] :
    trace k (K.X n) (φ.f n).hom = trace k (K.homology n) (homologyMap φ n).hom +
      trace k _ (φ.boundaryMap p n) + trace k _ (φ.boundaryMap n m) := by
  rw [trace_f_eq_trace_restrict_ker_add φ n m, trace_restrict_ker_eq_trace_boundaryMap_add φ hp hm,
    add_comm (trace k _ (φ.boundaryMap p n))]

end HomologicalComplex

namespace ChainComplex

open HomologicalComplex (homologyMap)

variable {k : Type u} [Field k] {K : ChainComplex (ModuleCat.{v} k) ℕ} (φ : K ⟶ K)

/-- In degree `0`, every element is a cycle, so `tr (φ₀) = tr (H₀(φ)) + tr (φ | im (K₁ ⟶ K₀))`. -/
theorem trace_f_zero [Module.Finite k (K.X 0)] :
    trace k (K.X 0) (φ.f 0).hom = trace k (K.homology 0) (homologyMap φ 0).hom +
      trace k _ (φ.boundaryMap 1 0) := by
  rw [HomologicalComplex.trace_f_eq_trace_homologyMap_add φ (p := 1) (by simp)
    ChainComplex.next_nat_zero, φ.boundaryMap_eq_zero (K.shape 0 0 (by simp)), map_zero,
    add_zero]

/-- In degree `n + 1`, `tr (φₙ₊₁) = tr (Hₙ₊₁(φ)) + tr (φ | im (Kₙ₊₂ ⟶ Kₙ₊₁)) +
tr (φ | im (Kₙ₊₁ ⟶ Kₙ))`. -/
theorem trace_f_succ (n : ℕ) [Module.Finite k (K.X (n + 1))] :
    trace k (K.X (n + 1)) (φ.f (n + 1)).hom =
      trace k (K.homology (n + 1)) (homologyMap φ (n + 1)).hom +
        trace k _ (φ.boundaryMap (n + 2) (n + 1)) + trace k _ (φ.boundaryMap (n + 1) n) :=
  HomologicalComplex.trace_f_eq_trace_homologyMap_add φ (by simp) (ChainComplex.next_nat_succ n)

/-- If the terms of `K` through degree `n` are finite-dimensional, the alternating sums up to
degree `n` of the traces of a chain endomorphism `φ` on the terms and on the homology of `K`
differ by the trace of `φ` on the boundaries `im (Kₙ₊₁ ⟶ Kₙ)` in degree `n`, with sign
`(-1)ⁿ`. -/
theorem sum_range_trace_f_eq_sum_range_trace_homologyMap_add (n : ℕ)
    (hfinite : ∀ i ≤ n, Module.Finite k (K.X i)) :
    ∑ i ∈ Finset.range (n + 1), (-1 : k) ^ i * trace k (K.X i) (φ.f i).hom =
      ∑ i ∈ Finset.range (n + 1), (-1 : k) ^ i * trace k (K.homology i) (homologyMap φ i).hom +
        (-1 : k) ^ n * trace k _ (φ.boundaryMap (n + 1) n) := by
  induction n with
  | zero =>
    let _ := hfinite 0 le_rfl
    simp [trace_f_zero]
  | succ n ih =>
    let _ := hfinite (n + 1) le_rfl
    rw [Finset.sum_range_succ, ih (fun i hi ↦ hfinite i (hi.trans n.le_succ)),
      Finset.sum_range_succ _ (n + 1), trace_f_succ]
    ring

/-- **The Hopf trace formula.** If the terms of `K` through degree `n` are finite-dimensional and
the differential `Kₙ₊₁ ⟶ Kₙ` vanishes, then the alternating sums up to degree `n` of the traces
of a chain endomorphism `φ` on the terms and on the homology of `K` agree. -/
theorem sum_range_trace_f_eq_sum_range_trace_homologyMap {n : ℕ}
    (hfinite : ∀ i ≤ n, Module.Finite k (K.X i)) (hn : K.d (n + 1) n = 0) :
    ∑ i ∈ Finset.range (n + 1), (-1 : k) ^ i * trace k (K.X i) (φ.f i).hom =
      ∑ i ∈ Finset.range (n + 1), (-1 : k) ^ i * trace k (K.homology i) (homologyMap φ i).hom := by
  rw [sum_range_trace_f_eq_sum_range_trace_homologyMap_add φ n hfinite, φ.boundaryMap_eq_zero hn,
    map_zero, mul_zero, add_zero]

end ChainComplex

/-! ### The determinant form -/

namespace HomologicalComplex

open Polynomial

variable {k : Type u} [Field k] {ι : Type*} {c : ComplexShape ι}
  {K : HomologicalComplex (ModuleCat.{v} k) c}

/-- The characteristic polynomial of `φ` on `K.X n` is the product of those on the kernel `Zₙ` of
the differential `K.d n m` and on its image `Bₘ`. -/
private theorem charpoly_f_eq_charpoly_restrict_ker_mul (φ : K ⟶ K) (n m : ι)
    [Module.Finite k (K.X n)] :
    (φ.f n).hom.charpoly = ((φ.f n).hom.restrict (p := ker (K.d n m).hom)
      (q := ker (K.d n m).hom) (φ.d_apply_eq_zero_of_d_apply_eq_zero n m)).charpoly *
        (φ.boundaryMap n m).charpoly := by
  refine charpoly_eq_mul_of_exact (ker (K.d n m).hom).injective_subtype
    (K.d n m).hom.surjective_rangeRestrict ?_ (LinearMap.ext fun _ ↦ rfl)
    (LinearMap.ext fun x ↦ Subtype.ext (by simp [Hom.comm_apply]))
  rw [LinearMap.exact_iff, ker_rangeRestrict, Submodule.range_subtype]

/-- The characteristic polynomial of `φ` on the kernel `Zₙ` of the differential `K.d n m` is the
product of those on the image `Bₙ` of the incoming differential `K.d p n` and of `Hₙ(φ)`. -/
private theorem charpoly_restrict_ker_eq_charpoly_boundaryMap_mul (φ : K ⟶ K) {p n m : ι}
    (hp : c.prev n = p) (hm : c.next n = m) [Module.Finite k (K.X n)] :
    ((φ.f n).hom.restrict (p := ker (K.d n m).hom) (q := ker (K.d n m).hom)
      (φ.d_apply_eq_zero_of_d_apply_eq_zero n m)).charpoly =
        (φ.boundaryMap p n).charpoly * (homologyMap φ n).hom.charpoly :=
  charpoly_eq_mul_of_exact (Submodule.inclusion_injective _)
    (K.moduleCatKerHomologyClass_surjective hm) (K.exact_inclusion_moduleCatKerHomologyClass hm hp)
    (LinearMap.ext fun x ↦ Subtype.ext (φ.coe_boundaryMap p n x).symm)
    (LinearMap.ext fun z ↦ (homologyMap_moduleCatKerHomologyClass hm φ z).symm)

/-- The characteristic polynomial of a chain endomorphism `φ` on a finite-dimensional term
`K.X n` is the product of those of `φ` on the homology `Hₙ(K)`, on the boundaries
`Bₙ = im (K.X p ⟶ K.X n)` and on the boundaries `Bₘ = im (K.X n ⟶ K.X m)`, where `p = c.prev n`
and `m = c.next n`. -/
theorem charpoly_f_eq_charpoly_homologyMap_mul (φ : K ⟶ K) {p n m : ι} (hp : c.prev n = p)
    (hm : c.next n = m) [Module.Finite k (K.X n)] :
    (φ.f n).hom.charpoly = (homologyMap φ n).hom.charpoly * (φ.boundaryMap p n).charpoly *
      (φ.boundaryMap n m).charpoly := by
  rw [charpoly_f_eq_charpoly_restrict_ker_mul φ n m,
    charpoly_restrict_ker_eq_charpoly_boundaryMap_mul φ hp hm,
    mul_comm (φ.boundaryMap p n).charpoly]

/-- The characteristic polynomial of `φ` on the boundaries `im (K.X i ⟶ K.X j)` is one when the
differential `K.d i j` vanishes. -/
theorem Hom.charpoly_boundaryMap_eq_one (φ : K ⟶ K) {i j : ι} [Module.Finite k (K.X j)]
    (h : K.d i j = 0) : (φ.boundaryMap i j).charpoly = 1 := by
  have : Subsingleton (LinearMap.range (K.d i j).hom) := by
    rw [h, ModuleCat.hom_zero, LinearMap.range_zero]
    infer_instance
  exact charpoly_eq_one_of_subsingleton _

end HomologicalComplex

namespace ChainComplex

open HomologicalComplex (homologyMap)
open Polynomial

variable {k : Type u} [Field k] {K : ChainComplex (ModuleCat.{v} k) ℕ} (φ : K ⟶ K)

/-- In degree `0`, every element is a cycle, so the characteristic polynomial of `φ₀` is the
product of those of `H₀(φ)` and of `φ | im (K₁ ⟶ K₀)`. -/
theorem charpoly_f_zero [Module.Finite k (K.X 0)] :
    (φ.f 0).hom.charpoly =
      (homologyMap φ 0).hom.charpoly * (φ.boundaryMap 1 0).charpoly := by
  rw [HomologicalComplex.charpoly_f_eq_charpoly_homologyMap_mul φ (p := 1) (by simp)
    ChainComplex.next_nat_zero, φ.charpoly_boundaryMap_eq_one (K.shape 0 0 (by simp)), mul_one]

/-- In degree `n + 1`, the characteristic polynomial of `φₙ₊₁` is the product of those of
`Hₙ₊₁(φ)`, of `φ | im (Kₙ₊₂ ⟶ Kₙ₊₁)` and of `φ | im (Kₙ₊₁ ⟶ Kₙ)`. -/
theorem charpoly_f_succ (n : ℕ) [Module.Finite k (K.X (n + 1))] :
    (φ.f (n + 1)).hom.charpoly = (homologyMap φ (n + 1)).hom.charpoly *
      (φ.boundaryMap (n + 2) (n + 1)).charpoly * (φ.boundaryMap (n + 1) n).charpoly :=
  HomologicalComplex.charpoly_f_eq_charpoly_homologyMap_mul φ (by simp)
    (ChainComplex.next_nat_succ n)

variable [∀ i, Module.Finite k (K.X i)]

/-- Up to degree `n`, the product of the characteristic polynomials of a chain endomorphism `φ`
on the terms of even degree and on the homology in odd degree, and the product of those on the
terms of odd degree and on the homology in even degree, agree up to the characteristic polynomial
of `φ` on the boundaries `im (Kₙ₊₁ ⟶ Kₙ)`: this factor multiplies the second product when `n` is
even and the first when `n` is odd. -/
theorem prod_charpoly_f_mul_prod_charpoly_homologyMap_mul (n : ℕ) :
    (∏ i ∈ Finset.range (n + 1) with Even i, (φ.f i).hom.charpoly) *
        (∏ i ∈ Finset.range (n + 1) with Odd i, (homologyMap φ i).hom.charpoly) *
        (if Even n then 1 else (φ.boundaryMap (n + 1) n).charpoly) =
      (∏ i ∈ Finset.range (n + 1) with Odd i, (φ.f i).hom.charpoly) *
        (∏ i ∈ Finset.range (n + 1) with Even i, (homologyMap φ i).hom.charpoly) *
        (if Even n then (φ.boundaryMap (n + 1) n).charpoly else 1) := by
  simp only [Finset.prod_filter]
  induction n with
  | zero => simp [charpoly_f_zero]
  | succ n ih =>
    rw [Finset.prod_range_succ _ (n + 1), Finset.prod_range_succ _ (n + 1),
      Finset.prod_range_succ _ (n + 1), Finset.prod_range_succ _ (n + 1), charpoly_f_succ]
    by_cases hn : Even n <;>
      simp only [hn, Nat.even_add_one, ← Nat.not_even_iff_odd, not_true_eq_false,
        not_false_eq_true, ↓reduceIte, mul_one] at ih ⊢ <;>
      linear_combination (homologyMap φ (n + 1)).hom.charpoly *
        (φ.boundaryMap (n + 2) (n + 1)).charpoly * ih

/-- **The Hopf trace formula, determinant form.** If the terms of `K` are finite-dimensional and
the differential `Kₙ₊₁ ⟶ Kₙ` vanishes, then up to degree `n` the alternating products of the
characteristic polynomials of a chain endomorphism `φ` on the terms and on the homology of `K`
agree: `∏ᵢ χ(φᵢ) ^ (-1) ^ i = ∏ᵢ χ(Hᵢ(φ)) ^ (-1) ^ i`, stated without inverses. -/
theorem prod_charpoly_f_mul_prod_charpoly_homologyMap {n : ℕ} (hn : K.d (n + 1) n = 0) :
    (∏ i ∈ Finset.range (n + 1) with Even i, (φ.f i).hom.charpoly) *
        ∏ i ∈ Finset.range (n + 1) with Odd i, (homologyMap φ i).hom.charpoly =
      (∏ i ∈ Finset.range (n + 1) with Odd i, (φ.f i).hom.charpoly) *
        ∏ i ∈ Finset.range (n + 1) with Even i, (homologyMap φ i).hom.charpoly := by
  simpa only [φ.charpoly_boundaryMap_eq_one hn, ite_self, mul_one] using
    prod_charpoly_f_mul_prod_charpoly_homologyMap_mul φ n

/-- **The Hopf trace formula, in the form `det (1 - X φ)`.** If the terms of `K` are
finite-dimensional and the differential `Kₙ₊₁ ⟶ Kₙ` vanishes, then up to degree `n` the
alternating products of the polynomials `det (1 - X φ)` of a chain endomorphism `φ` on the terms
and on the homology of `K` agree, stated without inverses. -/
theorem prod_reverse_charpoly_f_mul_prod_reverse_charpoly_homologyMap {n : ℕ}
    (hn : K.d (n + 1) n = 0) :
    (∏ i ∈ Finset.range (n + 1) with Even i, (φ.f i).hom.charpoly.reverse) *
        ∏ i ∈ Finset.range (n + 1) with Odd i, (homologyMap φ i).hom.charpoly.reverse =
      (∏ i ∈ Finset.range (n + 1) with Odd i, (φ.f i).hom.charpoly.reverse) *
        ∏ i ∈ Finset.range (n + 1) with Even i, (homologyMap φ i).hom.charpoly.reverse := by
  simpa only [reverse_mul_of_domain, reverse_prod_of_domain] using
    congrArg reverse (prod_charpoly_f_mul_prod_charpoly_homologyMap φ hn)

open PowerSeries in
/-- **The homological zeta function from the chains.** Let the terms of `K` be finite-dimensional
over a field of characteristic zero, and let the differential `Kₙ₊₁ ⟶ Kₙ` vanish. Let
`L j = ∑ᵢ (-1) ^ i tr (Hᵢ(φ) ^ j)`, the sum over the degrees `i ≤ n`, be the Lefschetz numbers of
the action of a chain endomorphism `φ` on the homology of `K`. Then `exp (∑ⱼ L j Xʲ / j)` is the
alternating product `∏ᵢ det (1 - X φᵢ) ^ (-1) ^ (i + 1)` over the terms of `K`, stated without
inverses: multiplied by the factors of even degree it is the product of the factors of odd
degree. -/
theorem subst_exp_mul_prod_even_eq_prod_odd [Algebra ℚ k] {n : ℕ} (hn : K.d (n + 1) n = 0) :
    (exp k).subst (PowerSeries.mk fun j ↦ (j : ℚ)⁻¹ • ∑ i ∈ Finset.range (n + 1),
        (-1) ^ i * trace k (K.homology i) ((homologyMap φ i).hom ^ j)) *
        ∏ i ∈ Finset.range (n + 1) with Even i, ((φ.f i).hom.charpoly.reverse : k⟦X⟧) =
      ∏ i ∈ Finset.range (n + 1) with Odd i, ((φ.f i).hom.charpoly.reverse : k⟦X⟧) := by
  set E := (exp k).subst (PowerSeries.mk fun j ↦ (j : ℚ)⁻¹ • ∑ i ∈ Finset.range (n + 1),
    (-1) ^ i * trace k (K.homology i) ((homologyMap φ i).hom ^ j))
  set B := ∏ i ∈ Finset.range (n + 1) with Odd i, ((φ.f i).hom.charpoly.reverse : k⟦X⟧)
  set B' := ∏ i ∈ Finset.range (n + 1) with Odd i, ((homologyMap φ i).hom.charpoly.reverse : k⟦X⟧)
  -- the trace–determinant formula on the homology
  have hH : E * ∏ i ∈ Finset.range (n + 1) with Even i,
      ((homologyMap φ i).hom.charpoly.reverse : k⟦X⟧) = B' :=
    LinearMap.subst_exp_mul_prod_even_eq_prod_odd _ fun i ↦ (homologyMap φ i).hom
  -- the determinant form of the Hopf trace formula, read in `k⟦X⟧`
  have hC := congrArg (Polynomial.coeToPowerSeries.ringHom (R := k))
    (prod_reverse_charpoly_f_mul_prod_reverse_charpoly_homologyMap φ hn)
  simp only [map_mul, map_prod, Polynomial.coeToPowerSeries.ringHom_apply] at hC
  -- `B'` has constant coefficient one, so it can be cancelled.
  have hB' : B' ≠ 0 := ne_zero_of_map (f := PowerSeries.constantCoeff (R := k))
    ((LinearMap.constantCoeff_prod_coe_reverse_charpoly _ fun i ↦ (homologyMap φ i).hom).trans_ne
      one_ne_zero)
  refine mul_right_cancel₀ hB' ?_
  linear_combination E * hC + B * hH

end ChainComplex

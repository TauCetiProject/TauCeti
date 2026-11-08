/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.ModuleCat.Basic
public import TauCeti.LinearAlgebra.Trace.Exact

/-!
# The Hopf trace formula

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

/-- A chain endomorphism maps the kernel of the differential `K.d n m` into itself. -/
private theorem mapsTo_ker_d (φ : K ⟶ K) (n m : ι) :
    ∀ x ∈ ker (K.d n m).hom, (φ.f n).hom x ∈ ker (K.d n m).hom :=
  φ.d_apply_eq_zero_of_d_apply_eq_zero n m

/-- The trace of `φ` on `K.X n` is its trace on the kernel `Zₙ` of the differential `K.d n m` plus
its trace on the image `Bₘ` of that differential. -/
private theorem trace_f_eq_trace_restrict_ker_add (φ : K ⟶ K) (n m : ι)
    [Module.Finite k (K.X n)] :
    trace k (K.X n) (φ.f n).hom = trace k _ ((φ.f n).hom.restrict (mapsTo_ker_d φ n m)) +
      trace k _ (φ.boundaryMap n m) := by
  refine trace_eq_add_of_exact (ker (K.d n m).hom).injective_subtype
    (K.d n m).hom.surjective_rangeRestrict ?_ (LinearMap.ext fun _ ↦ by simp)
    (LinearMap.ext fun x ↦ Subtype.ext (by simp [Hom.comm_apply]))
  rw [LinearMap.exact_iff, ker_rangeRestrict, Submodule.range_subtype]

/-- The trace of `φ` on the kernel `Zₙ` of the differential `K.d n m` is its trace on the image
`Bₙ` of the incoming differential `K.d p n` plus the trace of `Hₙ(φ)`. -/
private theorem trace_restrict_ker_eq_trace_boundaryMap_add (φ : K ⟶ K) {p n m : ι}
    (hp : c.prev n = p) (hm : c.next n = m) [Module.Finite k (K.X n)] :
    trace k _ ((φ.f n).hom.restrict (mapsTo_ker_d φ n m)) =
      trace k _ (φ.boundaryMap p n) + trace k (K.homology n) (homologyMap φ n).hom := by
  refine trace_eq_add_of_exact (Submodule.inclusion_injective _)
    (K.moduleCatKerHomologyClass_surjective hm) (K.exact_inclusion_moduleCatKerHomologyClass hm hp)
    (LinearMap.ext fun _ ↦ Subtype.ext (by simp))
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

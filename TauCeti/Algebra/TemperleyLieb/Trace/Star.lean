/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.TemperleyLieb.MarkovTrace
public import TauCeti.Algebra.TemperleyLieb.Star
public import TauCeti.Algebra.TemperleyLieb.Trace.Radical
public import TauCeti.RingTheory.Ideal.Quotient.Star
public import TauCeti.RingTheory.TraceFunctional.Star
import Mathlib.Algebra.Star.LinearMap

/-!
# Hermitian Markov trace forms

At a self-adjoint loop parameter, every bounded-level or all-level Markov trace preserves the
analytic adjoint. Thus its sesquilinear trace form `H(x, y) = tr (star x * y)` is Hermitian, and
strand inclusion scales this form by the loop parameter. This holds over any commutative star
semiring, without positivity or invertibility assumptions on the parameter.

Over a commutative star ring, the adjoint identity makes every Markov trace radical star-stable
(`TauCeti.TemperleyLieb.IsMarkovTrace.isStar_traceRadical`), so the trace-radical quotients are
star algebras and the induced strand maps preserve the involution
(`TauCeti.TemperleyLieb.IsMarkovTrace.quotientStrandIncl_star`). Positivity and the identification
of the radical with the zero-length vectors are proved in
`TauCeti.Algebra.TemperleyLieb.Trace.Positive`.

## References

* D. Penneys, *Unitary Quantum Symmetries Lite*, Chapter 4, Sections 4.3–4.5.
* V. F. R. Jones, *Index for subfactors*, Invent. Math. 72 (1983), 1–25.
-/

public section

namespace TauCeti.TemperleyLieb

section Semiring

variable {R : Type*} [CommSemiring R] [StarRing R] {δ : R} [hδ : Fact (IsSelfAdjoint δ)]

namespace IsMarkovTraceUpTo

variable {N : ℕ} {tr : ∀ n, n ≤ N → TemperleyLieb R δ n →ₗ[R] R}

/-- At a self-adjoint loop parameter, every bounded-level Markov trace preserves the analytic
adjoint. -/
@[simp]
theorem map_star (htr : IsMarkovTraceUpTo R δ N tr) {n : ℕ} (hn : n ≤ N)
    (x : TemperleyLieb R δ n) :
    tr n hn (star x) = star (tr n hn x) := by
  let tr' (m : ℕ) (hm : m ≤ N) := (star (WithConv.toConv (tr m hm))).ofConv
  have happly (m : ℕ) (hm : m ≤ N) (y : TemperleyLieb R δ m) :
      tr' m hm y = star (tr m hm (star y)) := by
    simp [tr']
  have htr' : IsMarkovTraceUpTo R δ N tr' := by
    constructor
    · intro m hm
      simp [happly, htr.map_one, hδ.out.star_eq]
    · intro m hm y z
      simp only [happly, star_mul, htr.map_mul_comm m hm (star z)]
    · intro m hm y
      simp only [happly, ← strandIncl_star, htr.map_strandIncl, star_mul, hδ.out.star_eq,
        mul_comm]
    · intro m hm y
      simp only [happly, star_mul, star_e, ← strandIncl_star,
        htr.map_mul_comm (m + 2) hm (e δ (Fin.last m)), htr.map_strandIncl_mul_e_last]
  have heq := LinearMap.congr_fun (congrFun₂ (htr.unique htr') n hn) (star x)
  simpa only [happly, star_star] using heq

/-- The sesquilinear form of a bounded-level Markov trace is Hermitian. -/
theorem traceSesqForm_isSymm (htr : IsMarkovTraceUpTo R δ N tr) {n : ℕ} (hn : n ≤ N) :
    (tr n hn).traceSesqForm.IsSymm :=
  (tr n hn).traceSesqForm_isSymm (htr.map_star hn)

/-- Adding a strand scales the Hermitian trace form of a bounded-level Markov trace by `δ`. -/
theorem traceSesqForm_strandIncl (htr : IsMarkovTraceUpTo R δ N tr) {n : ℕ} (hn : n + 2 ≤ N)
    (x y : TemperleyLieb R δ (n + 1)) :
    (tr (n + 2) hn).traceSesqForm (strandIncl x) (strandIncl y) =
      δ * (tr (n + 1) (Nat.le_of_succ_le hn)).traceSesqForm x y := by
  simp only [LinearMap.traceSesqForm_apply, ← strandIncl_star, ← map_mul,
    htr.map_strandIncl]

end IsMarkovTraceUpTo

namespace IsMarkovTrace

variable {tr : ∀ n : ℕ, TemperleyLieb R δ n →ₗ[R] R}

/-- At a self-adjoint loop parameter, every Markov trace preserves the analytic adjoint.
In particular, over `ℂ` with real loop parameter, the adjoint conjugates the trace. -/
@[simp]
theorem map_star (htr : IsMarkovTrace R δ tr) (n : ℕ) (x : TemperleyLieb R δ n) :
    tr n (star x) = star (tr n x) :=
  (htr.isMarkovTraceUpTo n).map_star le_rfl x

/-- The sesquilinear form of a Markov trace is Hermitian. -/
theorem traceSesqForm_isSymm (htr : IsMarkovTrace R δ tr) (n : ℕ) :
    (tr n).traceSesqForm.IsSymm :=
  (htr.isMarkovTraceUpTo n).traceSesqForm_isSymm le_rfl

/-- Adding a strand scales the Hermitian trace form by the loop parameter. -/
theorem traceSesqForm_strandIncl (htr : IsMarkovTrace R δ tr) {n : ℕ}
    (x y : TemperleyLieb R δ (n + 1)) :
    (tr (n + 2)).traceSesqForm (strandIncl x) (strandIncl y) =
      δ * (tr (n + 1)).traceSesqForm x y :=
  (htr.isMarkovTraceUpTo (n + 2)).traceSesqForm_strandIncl le_rfl x y

end IsMarkovTrace

end Semiring

section Ring

variable {R : Type*} [CommRing R] [StarRing R] {δ : R} [Fact (IsSelfAdjoint δ)]

namespace IsMarkovTraceUpTo

variable {N : ℕ} {tr : ∀ n, n ≤ N → TemperleyLieb R δ n →ₗ[R] R}

/-- At a self-adjoint loop parameter, the trace radical of a bounded-level Markov trace at level
`n ≤ N` is stable under the analytic adjoint. -/
theorem isStar_traceRadical (htr : IsMarkovTraceUpTo R δ N tr) {n : ℕ} (hn : n ≤ N) :
    ((tr n hn).traceRadical (htr.map_mul_comm n hn)).IsStar where
  star_mem ha :=
    ((tr n hn).star_mem_traceRadical_iff (htr.map_mul_comm n hn) (htr.map_star hn)).mpr ha

end IsMarkovTraceUpTo

namespace IsMarkovTrace

variable {tr : ∀ n : ℕ, TemperleyLieb R δ n →ₗ[R] R}

/-- At a self-adjoint loop parameter, the trace radical of a Markov trace is stable under the
analytic adjoint. Install with `have := htr.isStar_traceRadical n` (in proofs) or
`letI := htr.isStar_traceRadical n` (in data) to equip the trace-radical quotient with its induced
`StarRing` structure. -/
theorem isStar_traceRadical (htr : IsMarkovTrace R δ tr) (n : ℕ) :
    ((tr n).traceRadical (htr.map_mul_comm n)).IsStar :=
  (htr.isMarkovTraceUpTo n).isStar_traceRadical le_rfl

/-- The strand map between trace-radical quotients preserves the induced involution. -/
@[simp]
theorem quotientStrandIncl_star (htr : IsMarkovTrace R δ tr) (n : ℕ)
    [((tr (n + 1)).traceRadical (htr.map_mul_comm (n + 1))).IsStar]
    [((tr (n + 2)).traceRadical (htr.map_mul_comm (n + 2))).IsStar]
    (q : TemperleyLieb R δ (n + 1) ⧸ (tr (n + 1)).traceRadical (htr.map_mul_comm (n + 1))) :
    htr.quotientStrandIncl n (star q) = star (htr.quotientStrandIncl n q) := by
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective q
  simp only [Ideal.Quotient.star_mk, htr.quotientStrandIncl_mk, strandIncl_star]

end IsMarkovTrace

/-- The spin-model Markov trace preserves the analytic adjoint, even when its unit parameter
is not self-adjoint: only the loop parameter must be self-adjoint. -/
@[simp]
theorem markovTrace_star (q : Rˣ) (h : δ = -((q : R) + ((q⁻¹ : Rˣ) : R))) {n : ℕ}
    (x : TemperleyLieb R δ n) : markovTrace q h (star x) = star (markovTrace q h x) :=
  (isMarkovTrace_markovTrace q h).map_star n x

end Ring

end TauCeti.TemperleyLieb

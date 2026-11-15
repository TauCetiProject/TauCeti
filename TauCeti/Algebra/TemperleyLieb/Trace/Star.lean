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

At a self-adjoint loop parameter, every Markov trace preserves the analytic adjoint. Thus its
sesquilinear trace form `H(x, y) = tr (star x * y)` is Hermitian, and strand inclusion scales
this form by the loop parameter. This holds over any commutative star semiring, without positivity
or invertibility assumptions on the parameter.

Over a commutative star ring, the adjoint identity shows that the trace radical is star-stable
(`TauCeti.TemperleyLieb.IsMarkovTrace.isStar_traceRadical`) and is precisely the kernel of the
Hermitian form (`LinearMap.ker_traceSesqForm`), while the quotient strand inclusions preserve the
induced involution (`TauCeti.TemperleyLieb.IsMarkovTrace.quotientStrandInclStarAlgHom`). Positivity
and the identification of that kernel with the zero-length vectors are treated in
`TauCeti.Algebra.TemperleyLieb.Trace.Positive`.

## References

* D. Penneys, *Unitary Quantum Symmetries Lite*, Chapter 4, Sections 4.3–4.5.
* V. F. R. Jones, *Index for subfactors*, Invent. Math. 72 (1983), 1–25.
-/

public section

namespace TauCeti.TemperleyLieb

section Semiring

variable {R : Type*} [CommSemiring R] [StarRing R] {δ : R} [hδ : Fact (IsSelfAdjoint δ)]
  {tr : ∀ n : ℕ, TemperleyLieb R δ n →ₗ[R] R}

namespace IsMarkovTrace

/-- At a self-adjoint loop parameter, every Markov trace preserves the analytic adjoint.
In particular, over `ℂ` with real loop parameter, the adjoint conjugates the trace. -/
@[simp]
theorem map_star (htr : IsMarkovTrace R δ tr) (n : ℕ) (x : TemperleyLieb R δ n) :
    tr n (star x) = star (tr n x) := by
  -- Conjugating both the input and output gives another Markov family, so Markov uniqueness
  -- yields the adjoint identity.
  let tr' (n : ℕ) := (star (WithConv.toConv (tr n))).ofConv
  have happly (n : ℕ) (x : TemperleyLieb R δ n) : tr' n x = star (tr n (star x)) := by
    simp [tr']
  have htr' : IsMarkovTrace R δ tr' := by
    constructor
    · intro n
      simp [happly, htr.map_one, hδ.out.star_eq]
    · intro n x y
      simp only [happly, star_mul, htr.map_mul_comm n (star y)]
    · intro n x
      simp only [happly, ← strandIncl_star, htr.map_strandIncl, star_mul, hδ.out.star_eq,
        mul_comm]
    · intro n x
      simp only [happly, star_mul, star_e, ← strandIncl_star,
        htr.map_mul_comm (n + 2) (e δ (Fin.last n)), htr.map_strandIncl_mul_e_last]
  have heq := LinearMap.congr_fun (congrFun (htr.unique htr') n) (star x)
  simpa only [happly, star_star] using heq

/-- The sesquilinear form of a Markov trace is Hermitian. -/
theorem traceSesqForm_isSymm (htr : IsMarkovTrace R δ tr) (n : ℕ) :
    (tr n).traceSesqForm.IsSymm :=
  (tr n).traceSesqForm_isSymm (htr.map_star n)

/-- Adding a strand scales the Hermitian trace form by the loop parameter. -/
theorem traceSesqForm_strandIncl (htr : IsMarkovTrace R δ tr) {n : ℕ}
    (x y : TemperleyLieb R δ (n + 1)) :
    (tr (n + 2)).traceSesqForm (strandIncl x) (strandIncl y) =
      δ * (tr (n + 1)).traceSesqForm x y := by
  simp only [LinearMap.traceSesqForm_apply, ← strandIncl_star, ← map_mul,
    htr.map_strandIncl]

end IsMarkovTrace

end Semiring

variable {R : Type*} [CommRing R] [StarRing R] {δ : R} [Fact (IsSelfAdjoint δ)]

namespace IsMarkovTrace

/-- At a self-adjoint loop parameter, the trace radical of any Markov trace is closed under the
analytic adjoint. Install with `haveI := htr.isStar_traceRadical` to endow every trace-radical
quotient in the tower with its `StarRing` and `StarModule` structures. -/
theorem isStar_traceRadical {tr : ∀ n : ℕ, TemperleyLieb R δ n →ₗ[R] R}
    (htr : IsMarkovTrace R δ tr) (n : ℕ) :
    ((tr n).traceRadical (htr.map_mul_comm n)).IsStar where
  star_mem ha := ((tr n).star_mem_traceRadical_iff (htr.map_mul_comm n) (htr.map_star n)).mpr ha

section Quotient

variable {tr : ∀ n : ℕ, TemperleyLieb R δ n →ₗ[R] R}

/-- The strand map between trace-radical quotients commutes with the quotient involution. -/
@[simp]
theorem quotientStrandIncl_star (htr : IsMarkovTrace R δ tr) (n : ℕ)
    [((tr (n + 1)).traceRadical (htr.map_mul_comm (n + 1))).IsStar]
    [((tr (n + 2)).traceRadical (htr.map_mul_comm (n + 2))).IsStar]
    (x : TemperleyLieb R δ (n + 1) ⧸ (tr (n + 1)).traceRadical (htr.map_mul_comm (n + 1))) :
    htr.quotientStrandIncl n (star x) = star (htr.quotientStrandIncl n x) := by
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  simp only [Ideal.Quotient.star_mk, htr.quotientStrandIncl_mk, strandIncl_star]

/-- The injective strand inclusion between trace-radical quotients as a `⋆`-algebra
homomorphism. -/
def quotientStrandInclStarAlgHom (htr : IsMarkovTrace R δ tr) (n : ℕ)
    [((tr (n + 1)).traceRadical (htr.map_mul_comm (n + 1))).IsStar]
    [((tr (n + 2)).traceRadical (htr.map_mul_comm (n + 2))).IsStar] :
    TemperleyLieb R δ (n + 1) ⧸ (tr (n + 1)).traceRadical (htr.map_mul_comm (n + 1)) →⋆ₐ[R]
      TemperleyLieb R δ (n + 2) ⧸ (tr (n + 2)).traceRadical (htr.map_mul_comm (n + 2)) :=
  { htr.quotientStrandIncl n with map_star' := htr.quotientStrandIncl_star n }

/-- Forgetting `star` preservation recovers
`TauCeti.TemperleyLieb.IsMarkovTrace.quotientStrandIncl`. -/
@[simp]
theorem toAlgHom_quotientStrandInclStarAlgHom (htr : IsMarkovTrace R δ tr) (n : ℕ)
    [((tr (n + 1)).traceRadical (htr.map_mul_comm (n + 1))).IsStar]
    [((tr (n + 2)).traceRadical (htr.map_mul_comm (n + 2))).IsStar] :
    (htr.quotientStrandInclStarAlgHom n).toAlgHom = htr.quotientStrandIncl n :=
  (rfl)

/-- Coercing `quotientStrandInclStarAlgHom` to a function recovers `quotientStrandIncl`. -/
@[simp]
theorem coe_quotientStrandInclStarAlgHom (htr : IsMarkovTrace R δ tr) (n : ℕ)
    [((tr (n + 1)).traceRadical (htr.map_mul_comm (n + 1))).IsStar]
    [((tr (n + 2)).traceRadical (htr.map_mul_comm (n + 2))).IsStar] :
    ⇑(htr.quotientStrandInclStarAlgHom n) = htr.quotientStrandIncl n :=
  (rfl)

/-- Applying `quotientStrandInclStarAlgHom` to a quotient class includes its representative. -/
theorem quotientStrandInclStarAlgHom_mk (htr : IsMarkovTrace R δ tr) (n : ℕ)
    [((tr (n + 1)).traceRadical (htr.map_mul_comm (n + 1))).IsStar]
    [((tr (n + 2)).traceRadical (htr.map_mul_comm (n + 2))).IsStar]
    (x : TemperleyLieb R δ (n + 1)) :
    htr.quotientStrandInclStarAlgHom n
      (Ideal.Quotient.mk ((tr (n + 1)).traceRadical (htr.map_mul_comm (n + 1))) x) =
        Ideal.Quotient.mk ((tr (n + 2)).traceRadical (htr.map_mul_comm (n + 2)))
          (strandIncl x) :=
  htr.quotientStrandIncl_mk n x

/-- The `⋆`-algebra strand inclusion between trace-radical quotients is injective. -/
theorem quotientStrandInclStarAlgHom_injective (htr : IsMarkovTrace R δ tr) (n : ℕ)
    [((tr (n + 1)).traceRadical (htr.map_mul_comm (n + 1))).IsStar]
    [((tr (n + 2)).traceRadical (htr.map_mul_comm (n + 2))).IsStar] :
    Function.Injective (htr.quotientStrandInclStarAlgHom n) :=
  htr.quotientStrandIncl_injective n

end Quotient

end IsMarkovTrace

/-- The spin-model Markov trace preserves the analytic adjoint, even when its unit parameter
is not self-adjoint: only the loop parameter must be self-adjoint. -/
@[simp]
theorem markovTrace_star (q : Rˣ) (h : δ = -((q : R) + ((q⁻¹ : Rˣ) : R))) {n : ℕ}
    (x : TemperleyLieb R δ n) : markovTrace q h (star x) = star (markovTrace q h x) :=
  (isMarkovTrace_markovTrace q h).map_star n x

end TauCeti.TemperleyLieb

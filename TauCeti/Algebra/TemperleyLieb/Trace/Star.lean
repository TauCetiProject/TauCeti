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

Together with `LinearMap.star_mem_traceRadical_iff` and `LinearMap.ker_traceSesqForm`, the adjoint
identity shows that the trace radical is star-stable (`IsMarkovTrace.instIsStarTraceRadical`) and
is precisely the kernel of the Hermitian form, so strand inclusion induces `⋆`-algebra
homomorphisms `IsMarkovTrace.quotientStrandStarAlgHom` between the algebraic trace quotients
at every level `n ≥ 0` without hypotheses on `δ` (injective at every successor level, and at
level `0` whenever multiplication by `δ` is injective). Positivity and the identification of that
kernel with the zero-length vectors are separate questions.

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

/-- At a self-adjoint loop parameter, the trace radical of a Markov trace is star-stable. -/
theorem IsMarkovTrace.isStar_traceRadical {tr : ∀ n : ℕ, TemperleyLieb R δ n →ₗ[R] R}
    (htr : IsMarkovTrace R δ tr) (n : ℕ) :
    ((tr n).traceRadical (htr.map_mul_comm n)).IsStar :=
  ⟨fun ha ↦ ((tr n).star_mem_traceRadical_iff (htr.map_mul_comm n) (htr.map_star n)).mpr ha⟩

namespace IsMarkovTrace

variable {tr : ∀ n : ℕ, TemperleyLieb R δ n →ₗ[R] R} (htr : IsMarkovTrace R δ tr)

instance instIsStarTraceRadical (n : ℕ) : (htr.traceRadical n).IsStar :=
  htr.isStar_traceRadical n

/-- Unital `⋆`-algebra strand inclusion `htr.Quotient n →⋆ₐ[R] htr.Quotient (n + 1)` (`n ≥ 0`). -/
def quotientStrandStarAlgHom (n : ℕ) :
    htr.Quotient n →⋆ₐ[R] htr.Quotient (n + 1) :=
  { Ideal.quotientMapₐ (htr.traceRadical (n + 1)) (strandInclAll n)
      (htr.traceRadical_le_comap_strandInclAll n) with
    map_star' x := by
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
      simp only [AlgHom.toFun_eq_coe, Ideal.Quotient.star_mk, Ideal.quotient_map_mkₐ,
        strandInclAll_star, Ideal.Quotient.mkₐ_eq_mk] }

/-- `quotientStrandStarAlgHom` acts on representatives by `strandInclAll`. -/
@[simp]
theorem quotientStrandStarAlgHom_mk (n : ℕ) (x : TemperleyLieb R δ n) :
    htr.quotientStrandStarAlgHom n (Ideal.Quotient.mk (htr.traceRadical n) x) =
      Ideal.Quotient.mk (htr.traceRadical (n + 1)) (strandInclAll n x) :=
  Ideal.quotient_map_mkₐ _ _ _

/-- The `⋆`-algebra strand map between trace-radical quotients is injective at every successor
level, and at level `0` whenever multiplication by `δ` is injective. -/
theorem quotientStrandStarAlgHom_injective (n : ℕ)
    (hδ : n = 0 → Function.Injective (δ * ·)) :
    Function.Injective (htr.quotientStrandStarAlgHom n) :=
  Ideal.quotientMap_injective' (H := htr.traceRadical_le_comap_strandInclAll n)
    (htr.comap_traceRadical_strandInclAll n hδ).le

/-- The algebraic quotient trace scales by `δ` along `quotientStrandStarAlgHom`. -/
@[simp]
theorem quotientTrace_quotientStrandStarAlgHom (n : ℕ) (x : htr.Quotient n) :
    (tr (n + 1)).quotientTrace (htr.map_mul_comm (n + 1)) (htr.quotientStrandStarAlgHom n x) =
      δ * (tr n).quotientTrace (htr.map_mul_comm n) x := by
  obtain ⟨_, rfl⟩ := Ideal.Quotient.mk_surjective x; rw [htr.quotientStrandStarAlgHom_mk]
  exact (LinearMap.quotientTrace_mk _ _ _).trans <| (htr.map_strandInclAll n _).trans <|
    congrArg (δ * ·) (LinearMap.quotientTrace_mk _ _ _).symm

end IsMarkovTrace

/-- The spin-model Markov trace preserves the analytic adjoint, even when its unit parameter
is not self-adjoint: only the loop parameter must be self-adjoint. -/
@[simp]
theorem markovTrace_star (q : Rˣ) (h : δ = -((q : R) + ((q⁻¹ : Rˣ) : R))) {n : ℕ}
    (x : TemperleyLieb R δ n) : markovTrace q h (star x) = star (markovTrace q h x) :=
  (isMarkovTrace_markovTrace q h).map_star n x

/-- At a self-adjoint loop parameter, the trace radical of the spin-model Markov trace is
star-stable. -/
instance instIsStarTraceRadicalMarkovTrace (q : Rˣ) (h : δ = -((q : R) + ((q⁻¹ : Rˣ) : R)))
    (n : ℕ) :
    ((markovTrace (n := n) q h).traceRadical (markovTrace_mul_comm q h)).IsStar :=
  (isMarkovTrace_markovTrace q h).isStar_traceRadical n

end TauCeti.TemperleyLieb

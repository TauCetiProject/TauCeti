/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.TypeAHeckeAlgebra.Basis
public import TauCeti.Algebra.TypeAHeckeAlgebra.MarkovTrace
public import TauCeti.RingTheory.TraceFunctional.Radical

/-!
# Finite trace radicals of Hecke traces

Restrict a tracial functional on the infinite Hecke algebra to the independently presented
finite algebra through `TypeAHeckeAlgebra.toInfinite`. Its multiplication pairing has a two-sided
radical `finiteRadical`. Membership can be checked against the standard basis `T_w`
(`TypeAHeckeAlgebra.basisTw`). The quotient functional `finiteQuotientTrace` is tracial and
algebraically nondegenerate, and is normalized for a Markov trace; this makes no positivity
assertion.

Under a tower map, the preimage of the later radical is contained in the earlier radical.
Trace compatibility alone gives only this inclusion. For a Markov trace the two radicals
correspond exactly: an element of the finite radical pairs to zero with the whole infinite
algebra (`IsMarkovTrace.finiteRadical_eq_comap_traceRadical`), because the Markov rule
`τ (x * (a * T n * b)) = z * τ (x * (a * b))` propagates the vanishing along the decomposition
`Hₙ₊₂ = Hₙ₊₁ + Hₙ₊₁ Tₙ Hₙ₊₁`. Hence the finite radical is the preimage of the next one
(`IsMarkovTrace.comap_finiteRadical_strandIncl`), and the tower maps descend to injective
algebra maps of the quotients (`finiteQuotientStrandIncl`) compatible with the quotient traces.
At the two scalar-character parameters, the finite radicals are exactly the kernels of the
corresponding characters.

## References

* V. F. R. Jones, *Hecke algebra representations of braid groups and link polynomials*,
  Ann. of Math. 126 (1987), 335–388, Section 5.
-/

public section

namespace TauCeti.InfiniteTypeAHeckeAlgebra

open TypeAHeckeAlgebra

variable {R : Type*} [CommRing R] {q : Rˣ} {z : R}
  {τ : InfiniteTypeAHeckeAlgebra R q →ₗ[R] R}

/-- The two-sided trace radical on the finite `n`-strand presentation. -/
def finiteRadical (hτ : ∀ x y, τ (x * y) = τ (y * x)) (n : ℕ) :
    Ideal (TypeAHeckeAlgebra R q n) :=
  (τ ∘ₗ (toInfinite R q n).toLinearMap).traceRadical
    (τ.comp_algHom_mul_comm hτ (toInfinite R q n))

/-- Identify the finite radical with the general trace radical. -/
theorem finiteRadical_def (hτ : ∀ x y, τ (x * y) = τ (y * x)) (n : ℕ) :
    finiteRadical hτ n = (τ ∘ₗ (toInfinite R q n).toLinearMap).traceRadical
      (τ.comp_algHom_mul_comm hτ (toInfinite R q n)) := (rfl)

/-- An element belongs to the finite radical exactly when it pairs to zero with all elements
of that finite presentation, not with all elements of the infinite algebra. -/
@[simp]
theorem mem_finiteRadical (hτ : ∀ x y, τ (x * y) = τ (y * x)) {n : ℕ}
    {x : TypeAHeckeAlgebra R q n} :
    x ∈ finiteRadical hτ n ↔ ∀ y, τ (toInfinite R q n (x * y)) = 0 := by
  simp only [finiteRadical_def, LinearMap.mem_traceRadical, LinearMap.comp_apply,
    AlgHom.toLinearMap_apply]

instance (hτ : ∀ x y, τ (x * y) = τ (y * x)) (n : ℕ) :
    (finiteRadical hτ n).IsTwoSided :=
  inferInstanceAs ((τ ∘ₗ (toInfinite R q n).toLinearMap).traceRadical _).IsTwoSided

/-- It suffices to test the finite trace pairing on the standard basis `T_w`. -/
theorem mem_finiteRadical_iff_Tw (hτ : ∀ x y, τ (x * y) = τ (y * x)) {n : ℕ}
    {W : Type*} [Group W] (cs : CoxeterSystem (CoxeterMatrix.A (n - 1)) W)
    {x : TypeAHeckeAlgebra R q n} :
    x ∈ finiteRadical hτ n ↔ ∀ w, τ (toInfinite R q n (x * Tw q cs w)) = 0 := by
  simpa only [finiteRadical_def, LinearMap.comp_apply, AlgHom.toLinearMap_apply,
    coe_basisTw] using
    (τ ∘ₗ (toInfinite R q n).toLinearMap).mem_traceRadical_iff_basis
      (τ.comp_algHom_mul_comm hτ (toInfinite R q n)) (basisTw q cs) (x := x)

/-- Pulling back a later finite radical along a tower map lands in the earlier radical. -/
theorem comap_finiteRadical_strandIncl_le (hτ : ∀ x y, τ (x * y) = τ (y * x)) (n : ℕ) :
    Ideal.comap (strandIncl R q n) (finiteRadical hτ (n + 1)) ≤ finiteRadical hτ n := by
  rw [finiteRadical_def, finiteRadical_def]
  exact LinearMap.comap_traceRadical_le _ _ (strandIncl R q n)
    (LinearMap.ext fun x ↦ by simp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply,
      toInfinite_strandIncl])

/-- The tracial functional induced on the finite trace-radical quotient. -/
def finiteQuotientTrace (hτ : ∀ x y, τ (x * y) = τ (y * x)) (n : ℕ) :
    TypeAHeckeAlgebra R q n ⧸ finiteRadical hτ n →ₗ[R] R :=
  (τ ∘ₗ (toInfinite R q n).toLinearMap).quotientTrace
    (τ.comp_algHom_mul_comm hτ (toInfinite R q n))

/-- The finite quotient trace agrees with the original trace on representatives. -/
@[simp]
theorem finiteQuotientTrace_mk (hτ : ∀ x y, τ (x * y) = τ (y * x)) (n : ℕ)
    (x : TypeAHeckeAlgebra R q n) :
    finiteQuotientTrace hτ n (Ideal.Quotient.mk (finiteRadical hτ n) x) =
      τ (toInfinite R q n x) := by
  calc
    _ = (τ ∘ₗ (toInfinite R q n).toLinearMap) x :=
      (τ ∘ₗ (toInfinite R q n).toLinearMap).quotientTrace_mk
        (τ.comp_algHom_mul_comm hτ (toInfinite R q n)) x
    _ = _ := by rw [LinearMap.comp_apply, AlgHom.toLinearMap_apply]

/-- The finite quotient preserves the value at the identity. -/
@[simp]
theorem finiteQuotientTrace_one (hτ : ∀ x y, τ (x * y) = τ (y * x)) (n : ℕ) :
    finiteQuotientTrace hτ n 1 = τ 1 := by
  simpa only [map_one] using finiteQuotientTrace_mk hτ n 1

/-- The finite quotient of a Markov trace is normalized. -/
theorem IsMarkovTrace.finiteQuotientTrace_one (hτ : IsMarkovTrace z τ) (n : ℕ) :
    finiteQuotientTrace hτ.map_mul_comm n 1 = 1 := by
  rw [InfiniteTypeAHeckeAlgebra.finiteQuotientTrace_one, hτ.map_one]

/-- The finite quotient functional is tracial. -/
theorem finiteQuotientTrace_mul_comm (hτ : ∀ x y, τ (x * y) = τ (y * x)) (n : ℕ)
    (x y : TypeAHeckeAlgebra R q n ⧸ finiteRadical hτ n) :
    finiteQuotientTrace hτ n (x * y) = finiteQuotientTrace hτ n (y * x) := by
  exact (τ ∘ₗ (toInfinite R q n).toLinearMap).quotientTrace_mul_comm
    (τ.comp_algHom_mul_comm hτ (toInfinite R q n)) x y

/-- The finite quotient multiplication pairing is algebraically nondegenerate. -/
theorem finiteQuotientTrace_nondegenerate (hτ : ∀ x y, τ (x * y) = τ (y * x)) (n : ℕ)
    (x : TypeAHeckeAlgebra R q n ⧸ finiteRadical hτ n)
    (hx : ∀ y, finiteQuotientTrace hτ n (x * y) = 0) : x = 0 := by
  exact (τ ∘ₗ (toInfinite R q n).toLinearMap).quotientTrace_nondegenerate
    (τ.comp_algHom_mul_comm hτ (toInfinite R q n)) x hx

/-- For a Markov trace, an element of the stage of the first `n` strands that pairs to zero with
that stage lies in the trace radical: it pairs to zero with the whole infinite algebra. -/
theorem IsMarkovTrace.mem_traceRadical_of_mem_stage (hτ : IsMarkovTrace z τ) {n : ℕ}
    {x : InfiniteTypeAHeckeAlgebra R q} (hx : x ∈ stage R q n)
    (h : ∀ y ∈ stage R q n, τ (x * y) = 0) : x ∈ τ.traceRadical hτ.map_mul_comm := by
  -- Propagate the vanishing from each stage `m ≥ n` to the next.
  have key : ∀ m, n ≤ m → ∀ y ∈ stage R q m, τ (x * y) = 0 := by
    intro m hm
    induction m, hm using Nat.le_induction with
    | base => exact h
    | succ m hnm ih =>
      rcases m with _ | m
      · rwa [stage_eq_bot_of_le_one le_rfl, ← stage_eq_bot_of_le_one (R := R) (q := q)
          (n := 0) zero_le_one]
      · have hP := toSubmodule_stage_add_two_le_iff
          (P := LinearMap.ker (τ ∘ₗ LinearMap.mulLeft R x)) (n := m)
        refine fun y hy ↦ hP.2 ⟨fun y hy ↦ ih y hy, fun a ha b hb ↦ ?_⟩ hy
        rw [LinearMap.mem_ker, LinearMap.comp_apply, LinearMap.mulLeft_apply, ← mul_assoc,
          ← mul_assoc, hτ.map_mul_T_mul (mul_mem (stage_mono hnm hx) ha) hb,
          hτ.map_mul_comm, mul_assoc, ih _ (mul_mem ha hb), mul_zero]
  refine (LinearMap.mem_traceRadical _ _).2 fun y ↦ ?_
  obtain ⟨m, hy⟩ := exists_mem_stage y
  exact key (max n m) (le_max_left n m) y (stage_mono (le_max_right n m) hy)

/-- For a Markov trace, the finite radical is the preimage of the trace radical of the infinite
algebra. For an arbitrary tracial functional only the inclusion `⊇` holds. -/
theorem IsMarkovTrace.finiteRadical_eq_comap_traceRadical (hτ : IsMarkovTrace z τ) (n : ℕ) :
    finiteRadical hτ.map_mul_comm n =
      Ideal.comap (toInfinite R q n) (τ.traceRadical hτ.map_mul_comm) := by
  refine le_antisymm (fun x hx ↦ ?_) ?_
  · rw [mem_finiteRadical] at hx
    refine Ideal.mem_comap.2 <| hτ.mem_traceRadical_of_mem_stage
      (range_toInfinite (R := R) (q := q) (n := n) ▸ AlgHom.mem_range_self _ x) fun y hy ↦ ?_
    rw [← range_toInfinite] at hy
    obtain ⟨y, rfl⟩ := (AlgHom.mem_range _).1 hy
    rw [← map_mul]
    exact hx y
  · rw [finiteRadical_def]
    exact LinearMap.comap_traceRadical_le _ hτ.map_mul_comm (toInfinite R q n) rfl

/-- For a Markov trace, the finite radical is exactly the preimage of the next finite radical
under the tower map. -/
theorem IsMarkovTrace.comap_finiteRadical_strandIncl (hτ : IsMarkovTrace z τ) (n : ℕ) :
    Ideal.comap (strandIncl R q n) (finiteRadical hτ.map_mul_comm (n + 1)) =
      finiteRadical hτ.map_mul_comm n := by
  ext x
  rw [hτ.finiteRadical_eq_comap_traceRadical, hτ.finiteRadical_eq_comap_traceRadical,
    Ideal.mem_comap, Ideal.mem_comap, Ideal.mem_comap, toInfinite_strandIncl]

/-- For a Markov trace, the tower map descends to an algebra map of the finite trace-radical
quotients. It is injective (`finiteQuotientStrandIncl_injective`) and preserves the quotient
traces (`finiteQuotientTrace_finiteQuotientStrandIncl`). -/
def finiteQuotientStrandIncl (hτ : IsMarkovTrace z τ) (n : ℕ) :
    TypeAHeckeAlgebra R q n ⧸ finiteRadical hτ.map_mul_comm n →ₐ[R]
      TypeAHeckeAlgebra R q (n + 1) ⧸ finiteRadical hτ.map_mul_comm (n + 1) :=
  Ideal.quotientMapₐ _ (strandIncl R q n) (hτ.comap_finiteRadical_strandIncl n).ge

/-- The descended tower map sends the class of `x` to the class of its image under the tower
map. -/
@[simp]
theorem finiteQuotientStrandIncl_mk (hτ : IsMarkovTrace z τ) (n : ℕ)
    (x : TypeAHeckeAlgebra R q n) :
    finiteQuotientStrandIncl hτ n (Ideal.Quotient.mk _ x) =
      Ideal.Quotient.mk _ (strandIncl R q n x) := (rfl)

/-- The descended tower map of a Markov trace is injective. -/
theorem finiteQuotientStrandIncl_injective (hτ : IsMarkovTrace z τ) (n : ℕ) :
    Function.Injective (finiteQuotientStrandIncl hτ n) :=
  Ideal.quotientMap_injective' (H := (hτ.comap_finiteRadical_strandIncl n).ge)
    (hτ.comap_finiteRadical_strandIncl n).le

/-- The descended tower map preserves the quotient traces. -/
@[simp]
theorem finiteQuotientTrace_finiteQuotientStrandIncl (hτ : IsMarkovTrace z τ) (n : ℕ)
    (x : TypeAHeckeAlgebra R q n ⧸ finiteRadical hτ.map_mul_comm n) :
    finiteQuotientTrace hτ.map_mul_comm (n + 1) (finiteQuotientStrandIncl hτ n x) =
      finiteQuotientTrace hτ.map_mul_comm n x := by
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [finiteQuotientStrandIncl_mk, finiteQuotientTrace_mk, finiteQuotientTrace_mk,
    toInfinite_strandIncl]

/-- At the index-character parameter, the finite radical is the kernel of that character
pulled back to the finite presentation. -/
theorem finiteRadical_indexCharacter (n : ℕ) :
    finiteRadical (isMarkovTrace_indexCharacter (R := R) (q := q)).map_mul_comm n =
      RingHom.ker ((indexCharacter R q).comp (toInfinite R q n)) := by
  rw [finiteRadical_def]
  exact AlgHom.traceRadical_eq_ker ((indexCharacter R q).comp (toInfinite R q n))

/-- At the sign-character parameter, the finite radical is the kernel of that character
pulled back to the finite presentation. -/
theorem finiteRadical_signCharacter (n : ℕ) :
    finiteRadical (isMarkovTrace_signCharacter (R := R) (q := q)).map_mul_comm n =
      RingHom.ker ((signCharacter R q).comp (toInfinite R q n)) := by
  rw [finiteRadical_def]
  exact AlgHom.traceRadical_eq_ker ((signCharacter R q).comp (toInfinite R q n))

end TauCeti.InfiniteTypeAHeckeAlgebra

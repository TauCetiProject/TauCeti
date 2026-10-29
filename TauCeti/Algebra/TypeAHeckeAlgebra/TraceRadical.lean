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
# Finite trace radicals of Hecke Markov traces

Restrict a Markov trace on the infinite Hecke algebra to the independently presented finite
algebra through `TypeAHeckeAlgebra.toInfinite`. Its multiplication pairing has a two-sided
radical `IsMarkovTrace.finiteRadical`. Membership can be checked against the PBW basis.
The quotient functional supplied by `LinearMap.traceRadicalQuotient` is normalized, tracial
and algebraically nondegenerate; this makes no positivity assertion.

Under a tower map, the preimage of the later radical is contained in the earlier radical.
The opposite inclusion, needed to induce forward maps of these quotients, is not asserted
here: trace compatibility alone would not imply it. At the two scalar-character parameters,
the finite radicals are exactly the kernels of the corresponding characters.

## References

* V. F. R. Jones, *Hecke algebra representations of braid groups and link polynomials*,
  Ann. of Math. 126 (1987), 335–388, Section 5.
-/

public section

namespace TauCeti.InfiniteTypeAHeckeAlgebra

open TypeAHeckeAlgebra

variable {R : Type*} [CommRing R] {q : Rˣ} {z : R}
  {τ : InfiniteTypeAHeckeAlgebra R q →ₗ[R] R}

namespace IsMarkovTrace

/-- The two-sided trace radical on the finite `n`-strand presentation. -/
def finiteRadical (hτ : IsMarkovTrace z τ) (n : ℕ) : Ideal (TypeAHeckeAlgebra R q n) :=
  (τ ∘ₗ (toInfinite R q n).toLinearMap).traceRadical
    (fun x y ↦ by simp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply,
      map_mul, hτ.map_mul_comm])

/-- Identify the finite radical with the general trace radical, allowing the generic quotient
functional and its nondegeneracy theorem to be used on this finite presentation. -/
theorem finiteRadical_def (hτ : IsMarkovTrace z τ) (n : ℕ) :
    hτ.finiteRadical n = (τ ∘ₗ (toInfinite R q n).toLinearMap).traceRadical
      (fun x y ↦ by simp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply,
        map_mul, hτ.map_mul_comm]) := (rfl)

/-- An element belongs to the finite radical exactly when it pairs to zero with all elements
of that finite presentation, not with all elements of the infinite algebra. -/
@[simp]
theorem mem_finiteRadical (hτ : IsMarkovTrace z τ) {n : ℕ}
    {x : TypeAHeckeAlgebra R q n} :
    x ∈ hτ.finiteRadical n ↔ ∀ y, τ (toInfinite R q n (x * y)) = 0 := by
  rw [finiteRadical, LinearMap.mem_traceRadical]
  rfl

instance (hτ : IsMarkovTrace z τ) (n : ℕ) : (hτ.finiteRadical n).IsTwoSided :=
  inferInstanceAs ((τ ∘ₗ (toInfinite R q n).toLinearMap).traceRadical _).IsTwoSided

/-- It suffices to test the finite trace pairing on the PBW basis. -/
theorem mem_finiteRadical_iff_Tw (hτ : IsMarkovTrace z τ) {n : ℕ}
    {W : Type*} [Group W] (cs : CoxeterSystem (CoxeterMatrix.A (n - 1)) W)
    {x : TypeAHeckeAlgebra R q n} :
    x ∈ hτ.finiteRadical n ↔ ∀ w, τ (toInfinite R q n (x * Tw q cs w)) = 0 := by
  rw [mem_finiteRadical]
  refine ⟨fun hx w ↦ hx _, fun hx y ↦ ?_⟩
  let f := τ ∘ₗ (toInfinite R q n).toLinearMap ∘ₗ LinearMap.mulLeft R x
  have hf : f = 0 := (basisTw q cs).ext fun w ↦ by simpa [f] using hx w
  exact LinearMap.congr_fun hf y

/-- Pulling back a later finite radical along a tower map lands in the earlier radical. -/
theorem comap_finiteRadical_strandIncl_le (hτ : IsMarkovTrace z τ) (n : ℕ) :
    Ideal.comap (strandIncl R q n) (hτ.finiteRadical (n + 1)) ≤ hτ.finiteRadical n := by
  intro x hx
  rw [mem_finiteRadical]
  rw [Ideal.mem_comap, mem_finiteRadical] at hx
  intro y
  simpa only [← map_mul, toInfinite_strandIncl] using hx (strandIncl R q n y)

end IsMarkovTrace

/-- At the index-character parameter, the finite radical is the kernel of that character
pulled back to the finite presentation. -/
theorem finiteRadical_indexCharacter (n : ℕ) :
    (isMarkovTrace_indexCharacter (R := R) (q := q)).finiteRadical n =
      RingHom.ker ((indexCharacter R q).comp (toInfinite R q n)) := by
  rw [IsMarkovTrace.finiteRadical]
  exact AlgHom.traceRadical_eq_ker ((indexCharacter R q).comp (toInfinite R q n))

/-- At the sign-character parameter, the finite radical is the kernel of that character
pulled back to the finite presentation. -/
theorem finiteRadical_signCharacter (n : ℕ) :
    (isMarkovTrace_signCharacter (R := R) (q := q)).finiteRadical n =
      RingHom.ker ((signCharacter R q).comp (toInfinite R q n)) := by
  rw [IsMarkovTrace.finiteRadical]
  exact AlgHom.traceRadical_eq_ker ((signCharacter R q).comp (toInfinite R q n))

end TauCeti.InfiniteTypeAHeckeAlgebra

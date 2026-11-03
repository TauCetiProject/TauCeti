/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ClassFieldTheory.ClassFields.RayClassField
public import TauCeti.NumberTheory.NumberField.Global.RayClass.Integral

/-!
# Splitting of primes in ray class fields

For a prime ideal away from a modulus, its residue degree in the ray class field is the order
of its ray class. Consequently the number of primes above it, multiplied by that order, is the
order of the ray class group. Complete splitting is equivalent to having a generator congruent
to one modulo the finite part and positive at the prescribed real places.

At the trivial modulus this gives the classical splitting criterion for the Hilbert class
field: a prime splits completely exactly when it is principal. In the narrow Hilbert class
field the generator must instead be totally positive. These criteria are stated for arbitrary
nonzero prime ideals.

## Main results

* `TauCeti.ClassFieldTheory.orderOf_idealClass_eq_inertiaDeg`: ray-class order is residue degree.
* `TauCeti.ClassFieldTheory.ncard_primesOver_rayClassField_mul_orderOf_idealClass`: the
  decomposition law in ray-class coordinates.
* `TauCeti.ClassFieldTheory.ncard_primesOver_rayClassField_eq_finrank_iff`: the generator
  criterion for complete splitting in a ray class field.
* `TauCeti.ClassFieldTheory.ncard_primesOver_hilbertClassField_eq_finrank_iff`: complete
  splitting in the Hilbert class field is equivalent to principality.
* `TauCeti.ClassFieldTheory.ncard_primesOver_narrowHilbertClassField_eq_finrank_iff`: the
  analogous criterion with a totally positive generator.

## References

* J. S. Milne, *Class Field Theory*, v4.03, Chapter V, §3.
* J. Neukirch, *Algebraic Number Theory*, Chapter VI, §6.
-/

public noncomputable section

open NumberField TauCeti.GlobalNumberFields
open scoped nonZeroDivisors

namespace TauCeti.ClassFieldTheory

variable {K : Type} [Field K] [NumberField K]

/-- **The residue degree in a ray class field is the order of the ray class**: for a prime
`𝔭` away from `𝔪` and a prime `Q` of the ray class field above it, `f(Q / 𝔭)` is the order of
`[𝔭]` in the ray class group. -/
theorem orderOf_idealClass_eq_inertiaDeg (𝔪 : Modulus K) (J : integralIdealsPrimeTo 𝔪)
    [(J : Ideal (𝓞 K)).IsMaximal] (Q : Ideal (𝓞 (rayClassField 𝔪))) [Q.IsPrime]
    [Q.LiesOver (J : Ideal (𝓞 K))] :
    orderOf (idealClass 𝔪 J) = Q.inertiaDeg (𝓞 K) := by
  rw [← (rayClassArtinEquiv 𝔪).orderOf_eq, rayClassArtinEquiv_apply,
    orderOf_rayClassArtinMap_idealClass _ J Q]

/-- **Prime decomposition in the ray class field**: the number of primes above `𝔭`, multiplied
by the order of its ray class, is the order of the ray class group. -/
theorem ncard_primesOver_rayClassField_mul_orderOf_idealClass (𝔪 : Modulus K)
    (J : integralIdealsPrimeTo 𝔪) [(J : Ideal (𝓞 K)).IsMaximal] :
    ((J : Ideal (𝓞 K)).primesOver (𝓞 (rayClassField 𝔪))).ncard *
        orderOf (idealClass 𝔪 J) = Nat.card (RayClassGroup 𝔪) := by
  rw [← (rayClassArtinEquiv 𝔪).orderOf_eq, rayClassArtinEquiv_apply,
    ncard_primesOver_mul_orderOf_rayClassArtinMap_idealClass, finrank_rayClassField]

/-- **Complete splitting in a ray class field**: a prime away from `𝔪` has as many primes
above it as the extension degree exactly when it has an integral generator congruent to one
modulo the finite part of `𝔪` and positive at every real place in the infinite part. -/
theorem ncard_primesOver_rayClassField_eq_finrank_iff (𝔪 : Modulus K)
    (J : integralIdealsPrimeTo 𝔪) [(J : Ideal (𝓞 K)).IsMaximal] :
    ((J : Ideal (𝓞 K)).primesOver (𝓞 (rayClassField 𝔪))).ncard =
        Module.finrank K (rayClassField 𝔪) ↔
      ∃ α : 𝓞 K, α - 1 ∈ 𝔪.finitePart ∧
        (∀ w ∈ 𝔪.infinitePart,
          0 < InfinitePlace.embedding_of_isReal w.2 (algebraMap (𝓞 K) K α)) ∧
        (J : Ideal (𝓞 K)) = Ideal.span {α} := by
  rw [ncard_primesOver_eq_finrank_iff_rayClassArtinMap_idealClass_eq_one
      (isAdmissibleModulus_rayClassField 𝔪),
    ← rayClassArtinEquiv_apply, MulEquiv.map_eq_one_iff,
    idealClass_eq_one_iff_exists_generator]

/-- **A prime splits completely in the Hilbert class field exactly when it is principal.**
The prime is an arbitrary nonzero prime of `𝓞 K`; no auxiliary congruence condition is needed. -/
theorem ncard_primesOver_hilbertClassField_eq_finrank_iff (K : Type) [Field K] [NumberField K]
    (p : Ideal (𝓞 K)) [p.IsPrime] (hp : p ≠ ⊥) :
    (p.primesOver (𝓞 (hilbertClassField K))).ncard =
        Module.finrank K (hilbertClassField K) ↔
      ∃ α : 𝓞 K, p = Ideal.span {α} := by
  let J : integralIdealsPrimeTo (Modulus.one K) := ⟨p, by
    rw [Modulus.mem_integralIdealsPrimeTo, Modulus.isCoprimeTo_iff]
    exact ⟨hp, by simp⟩⟩
  have : (J : Ideal (𝓞 K)).IsMaximal := (inferInstance : p.IsPrime).isMaximal hp
  simpa only [Modulus.one_finitePart, Submodule.mem_top, Modulus.one_infinitePart,
    Finset.notMem_empty, IsEmpty.forall_iff, implies_true, true_and] using
    ncard_primesOver_rayClassField_eq_finrank_iff (Modulus.one K) J

/-- **Complete splitting in the narrow Hilbert class field**: a nonzero prime splits completely
exactly when it has an integral generator positive at every real place of `K`. -/
theorem ncard_primesOver_narrowHilbertClassField_eq_finrank_iff (K : Type) [Field K]
    [NumberField K] (p : Ideal (𝓞 K)) [p.IsPrime] (hp : p ≠ ⊥) :
    (p.primesOver (𝓞 (narrowHilbertClassField K))).ncard =
        Module.finrank K (narrowHilbertClassField K) ↔
      ∃ α : 𝓞 K, (∀ w : {w : InfinitePlace K // w.IsReal},
        0 < InfinitePlace.embedding_of_isReal w.2 (algebraMap (𝓞 K) K α)) ∧
        p = Ideal.span {α} := by
  let J : integralIdealsPrimeTo (narrowModulus K) := ⟨p, by
    rw [Modulus.mem_integralIdealsPrimeTo, Modulus.isCoprimeTo_iff,
      narrowModulus_support]
    exact ⟨hp, by simp⟩⟩
  have : (J : Ideal (𝓞 K)).IsMaximal := (inferInstance : p.IsPrime).isMaximal hp
  simpa only [narrowModulus_finitePart, Submodule.mem_top, mem_narrowModulus_infinitePart,
    forall_const, true_and] using
    ncard_primesOver_rayClassField_eq_finrank_iff (narrowModulus K) J

end TauCeti.ClassFieldTheory

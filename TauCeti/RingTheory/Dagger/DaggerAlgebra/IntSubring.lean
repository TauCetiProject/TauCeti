/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Dagger.DaggerAlgebra.Map
public import TauCeti.RingTheory.Dagger.IntegralWashnitzer.Basic

import TauCeti.RingTheory.Affinoid.PowerBounded

/-!
# The integral subring of a dagger algebra

Let `K` be a complete nontrivially normed ultrametric field and `A` a `K`-dagger algebra, with
completion map `τ : A → Â` into its affinoid completion `Â = T_n ⧸ I T_n`. The *integral subring*

```text
A^int = τ⁻¹(Â°) = {a ∈ A | |a|sup ≤ 1}
```

is the unit ball of the supremum seminorm of `A`. Since `τ` preserves the supremum seminorm
(`TauCeti.Dagger.supSeminorm_toCompletion`) and the power-bounded elements of an affinoid algebra
are those of supremum seminorm at most one, it is also the preimage of the power-bounded subring
`Â°` of `Â`. It is the integral model of `A` from which the reduction of a dagger algebra of
Monsky–Washnitzer type is formed, and it plays for `A` the role that `Â°` plays for `Â`.

Because a morphism of dagger algebras contracts the supremum seminorm, every `K`-algebra
homomorphism `A → B` maps `A^int` into `B^int`, with no continuity hypothesis. For the
Monsky–Washnitzer algebra `W = K⟨X⟩†` itself, the supremum seminorm is the Gauss norm, so `W^int` is
the integral Monsky–Washnitzer algebra `K°⟨X⟩†` of overconvergent series with coefficients in `K°`,
which is also the ring of power-bounded elements of `W`. Elements of supremum seminorm `< 1` lie in
the Jacobson radical of `A^int`: if `|a|sup < 1` then `1 - a` is a unit of `A` whose inverse again
has supremum seminorm at most one.

## Main definitions

* `TauCeti.Dagger.intSubring K A`: the integral subring `A^int = {a | |a|sup ≤ 1}` of a dagger
  algebra.

## Main results

* `TauCeti.Dagger.mem_intSubring_iff_supSeminorm_le_one`: `a ∈ A^int` iff `|a|sup ≤ 1`, and
  `TauCeti.Dagger.mem_intSubring_iff_isPowerBounded_toCompletion`: `A^int = τ⁻¹(Â°)`.
* `TauCeti.Dagger.algebraMap_mem_intSubring_iff`: a scalar lies in `A^int` iff it lies in `K°`
  (for `A ≠ 0`), and `TauCeti.Dagger.mem_intSubring_of_isNilpotent`: nilpotents lie in `A^int`.
* `AlgHom.map_mem_intSubring`, `AlgEquiv.map_intSubring`: functoriality of `A^int` along
  arbitrary morphisms of dagger algebras.
* `TauCeti.Dagger.washnitzerAlgebra.mem_intSubring_iff_norm_le_one`,
  `TauCeti.Dagger.intWashnitzerAlgebra.range_toWashnitzerAlgebra`: `W^int` is the Gauss unit ball
  `K°⟨X⟩†`, and `TauCeti.Dagger.washnitzerAlgebra.intSubring_eq_powerBoundedSubring`: it is the ring
  of power-bounded elements of `W`.
* `TauCeti.Dagger.intSubring.isUnit_one_sub_of_supSeminorm_lt_one`,
  `TauCeti.Dagger.intSubring.mem_jacobson_of_supSeminorm_lt_one`: elements of supremum seminorm
  `< 1` lie in the Jacobson radical of `A^int`.

That `A^int` is also the ring of power-bounded elements of `A` for its canonical residue-norm
topology is `TauCeti.Dagger.mem_intSubring_iff_isPowerBounded`, proved alongside the other
topological statements in `TauCeti.RingTheory.Dagger.DaggerAlgebra.Continuity`.

## References

* E. Grosse-Klönne, *Rigid analytic spaces with overconvergent structure sheaf*,
  J. reine angew. Math. 519 (2000), §1.2.
* K. Kedlaya, *Finiteness of rigid cohomology with coefficients*, Duke Math. J. 134 (2006),
  §3.2.
-/

public section

namespace TauCeti.Dagger

open _root_.MvPowerSeries

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A : Type*} [CommRing A] [Algebra K A] [IsDaggerAlgebra K A]

variable (K A) in
/-- The **integral subring** `A^int = {a ∈ A | |a|sup ≤ 1}` of a dagger algebra `A`: the unit ball
of the supremum seminorm. Equivalently (`mem_intSubring_iff_isPowerBounded_toCompletion`) it is
the preimage `τ⁻¹(Â°)` of the power-bounded elements of the affinoid completion `Â`. -/
noncomputable def intSubring : Subring A where
  carrier := {a | supSeminorm K a ≤ 1}
  mul_mem' {a b} ha hb := (IsDaggerAlgebra.supSeminorm_mul_le a b).trans <|
    (mul_le_mul ha hb (supSeminorm_nonneg b) zero_le_one).trans_eq (mul_one 1)
  one_mem' := supSeminorm_le zero_le_one fun _ ↦ pointNorm_one.le
  add_mem' ha hb := (IsDaggerAlgebra.supSeminorm_add_le _ _).trans (max_le ha hb)
  zero_mem' := supSeminorm_zero.trans_le zero_le_one
  neg_mem' ha := (supSeminorm_neg _).trans_le ha

/-- **The integral subring is the unit ball of the supremum seminorm**: `a ∈ A^int` iff
`|a|sup ≤ 1`. -/
@[simp]
theorem mem_intSubring_iff_supSeminorm_le_one {a : A} :
    a ∈ intSubring K A ↔ supSeminorm K a ≤ 1 :=
  Iff.rfl

/-- **`A^int = τ⁻¹(Â°)`**: an element of a dagger algebra lies in the integral subring iff its
image in the affinoid completion `Â` is power-bounded. -/
theorem mem_intSubring_iff_isPowerBounded_toCompletion {a : A} :
    a ∈ intSubring K A ↔ Huber.IsPowerBounded (toCompletion K A a) := by
  rw [mem_intSubring_iff_supSeminorm_le_one, IsAffinoidAlgebra.isPowerBounded_iff_supSeminorm_le_one
    (K := K) (A := completion K A) isAffinoidAlgebra_completion, supSeminorm_toCompletion]

/-- A scalar of norm at most one lies in the integral subring. -/
theorem algebraMap_mem_intSubring {c : K} (hc : ‖c‖ ≤ 1) : algebraMap K A c ∈ intSubring K A := by
  refine mem_intSubring_iff_supSeminorm_le_one.mpr ?_
  cases subsingleton_or_nontrivial A
  · rw [supSeminorm_eq_zero_of_subsingleton]
    exact zero_le_one
  · rwa [supSeminorm_algebraMap]

/-- In a nonzero dagger algebra, a scalar lies in the integral subring iff it has norm at most
one. -/
theorem algebraMap_mem_intSubring_iff [Nontrivial A] {c : K} :
    algebraMap K A c ∈ intSubring K A ↔ ‖c‖ ≤ 1 := by
  rw [mem_intSubring_iff_supSeminorm_le_one, supSeminorm_algebraMap]

/-- Nilpotent elements of a dagger algebra lie in its integral subring, since their supremum
seminorm vanishes. -/
theorem mem_intSubring_of_isNilpotent {a : A} (ha : IsNilpotent a) : a ∈ intSubring K A := by
  rw [mem_intSubring_iff_supSeminorm_le_one, IsDaggerAlgebra.supSeminorm_eq_zero_iff.mpr ha]
  exact zero_le_one

/-- **Inverting `1 - a` in the integral subring.** If `|a|sup < 1`, then `1 - a` is a unit of
`A^int`: at every classical point `|1 - a| = 1`, so the inverse of `1 - a` in `A` again has supremum
seminorm at most one. -/
theorem intSubring.isUnit_one_sub_of_supSeminorm_lt_one {a : intSubring K A}
    (ha : supSeminorm K (a : A) < 1) : IsUnit (1 - a) := by
  have hA := isAffinoidAlgebra_completion (K := K) (A := A)
  obtain ⟨u, hu⟩ := IsDaggerAlgebra.isUnit_one_sub_of_supSeminorm_lt_one ha
  have hinv : ((u⁻¹ : Aˣ) : A) ∈ intSubring K A := by
    -- By the ultrametric inequality, `|1 - a| = 1` at every classical point of `Â`.
    have h1 : ∀ x, 1 ≤ pointNorm K x (toCompletion K A u) := fun x ↦ by
      have hax : pointNorm K x (toCompletion K A a) < 1 :=
        (hA.pointNorm_le_supSeminorm x _).trans_lt (by rwa [supSeminorm_toCompletion])
      have h := hA.pointNorm_add_le x (toCompletion K A u) (toCompletion K A a)
      rw [← map_add, hu, sub_add_cancel, map_one, pointNorm_one] at h
      rw [hu]
      exact (le_max_iff.mp h).resolve_right hax.not_ge
    have hτ : toCompletion K A ((u⁻¹ : Aˣ) : A) = Ring.inverse (toCompletion K A u) :=
      (Ring.inverse_unit (Units.map (toCompletion K A : A →* completion K A) u)).symm
    rw [mem_intSubring_iff_isPowerBounded_toCompletion, hτ]
    exact (IsAffinoidAlgebra.isUnit_and_isPowerBounded_inverse_iff (K := K)
      (A := completion K A) hA |>.mpr h1).2
  refine isUnit_iff_exists_inv.mpr ⟨⟨_, hinv⟩, Subtype.ext ?_⟩
  simp [← hu]

/-- **Elements of supremum seminorm `< 1` lie in the Jacobson radical of the integral
subring.** -/
theorem intSubring.mem_jacobson_of_supSeminorm_lt_one {a : intSubring K A}
    (ha : supSeminorm K (a : A) < 1) : a ∈ Ring.jacobson (intSubring K A) := by
  refine Ring.mem_jacobson_iff.mpr fun y ↦ ?_
  have h : supSeminorm K ((-(a * y) : intSubring K A) : A) < 1 := by
    rw [Subring.coe_neg, supSeminorm_neg, Subring.coe_mul]
    refine (IsDaggerAlgebra.supSeminorm_mul_le _ _).trans_lt ?_
    exact (mul_le_of_le_one_right (supSeminorm_nonneg _)
      (mem_intSubring_iff_supSeminorm_le_one.mp y.property)).trans_lt ha
  simpa [add_comm] using intSubring.isUnit_one_sub_of_supSeminorm_lt_one h

namespace washnitzerAlgebra

variable {σ : Type*} [Finite σ]

/-- **The integral subring of `W = K⟨X⟩†` is its Gauss unit ball**, since on `W` the supremum
seminorm is the Gauss norm. -/
theorem mem_intSubring_iff_norm_le_one {f : washnitzerAlgebra σ K} :
    f ∈ intSubring K (washnitzerAlgebra σ K) ↔ ‖f‖ ≤ 1 := by
  rw [mem_intSubring_iff_supSeminorm_le_one, supSeminorm_eq_norm]

/-- The integral subring of `W = K⟨X⟩†` is the ring of power-bounded elements of `W` for the Gauss
norm. -/
theorem intSubring_eq_powerBoundedSubring :
    intSubring K (washnitzerAlgebra σ K) = Huber.powerBoundedSubring (washnitzerAlgebra σ K) := by
  ext f
  rw [mem_intSubring_iff_supSeminorm_le_one, Huber.mem_powerBoundedSubring,
    isPowerBounded_iff_supSeminorm_le_one]

end washnitzerAlgebra

/-- **`W^int = K°⟨X⟩†`.** The integral subring of the Monsky–Washnitzer algebra `W = K⟨X⟩†` is the
integral Monsky–Washnitzer algebra of overconvergent series with coefficients in `K°`. -/
theorem intWashnitzerAlgebra.range_toWashnitzerAlgebra {σ : Type*} [Finite σ] :
    (intWashnitzerAlgebra.toWashnitzerAlgebra σ K).range =
      intSubring K (washnitzerAlgebra σ K) := by
  ext f
  rw [RingHom.mem_range, washnitzerAlgebra.mem_intSubring_iff_norm_le_one,
    ← mem_intWashnitzerAlgebra_iff_norm_le_one]
  refine ⟨?_, fun hf ↦ ⟨⟨f, hf⟩, toWashnitzerAlgebra_mk f hf⟩⟩
  rintro ⟨g, rfl⟩
  simp

end TauCeti.Dagger

namespace AlgHom

open TauCeti TauCeti.Dagger

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A B : Type*} [CommRing A] [Algebra K A] [IsDaggerAlgebra K A]
  [CommRing B] [Algebra K B] [IsDaggerAlgebra K B]

/-- **Morphisms of dagger algebras preserve integral subrings**: every `K`-algebra homomorphism
`φ : A → B` of dagger algebras maps `A^int` into `B^int`. -/
theorem map_mem_intSubring (φ : A →ₐ[K] B) {a : A} (ha : a ∈ intSubring K A) :
    φ a ∈ intSubring K B := by
  rw [mem_intSubring_iff_supSeminorm_le_one] at ha ⊢
  exact (φ.supSeminorm_map_le_of_isDaggerAlgebra a).trans ha

end AlgHom

namespace AlgEquiv

open TauCeti TauCeti.Dagger

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A B : Type*} [CommRing A] [Algebra K A] [IsDaggerAlgebra K A]
  [CommRing B] [Algebra K B] [IsDaggerAlgebra K B]

/-- An isomorphism of dagger algebras carries the integral subring onto the integral subring. -/
theorem map_intSubring (e : A ≃ₐ[K] B) : (intSubring K A).map (e : A →+* B) = intSubring K B :=
  le_antisymm (Subring.map_le_iff_le_comap.mpr fun _ ha ↦ e.toAlgHom.map_mem_intSubring ha)
    fun b hb ↦ ⟨e.symm b, e.symm.toAlgHom.map_mem_intSubring hb, e.apply_symm_apply b⟩

end AlgEquiv

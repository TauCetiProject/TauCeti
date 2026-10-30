/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Algebra.SeparatingIdeal.Primitive
public import TauCeti.Analysis.Normed.Ring.Primitive
public import TauCeti.Topology.Algebra.Module.Baire

/-!
# Separating ideals modulo the radical

Let `J` be a separating ideal of a unital complex Banach algebra `B`. Only finitely many
primitive ideals of `B` fail to contain `J`, and each of them has a finite-dimensional
quotient. Since the radical of `B` is the intersection of its primitive ideals, `J` embeds
modulo `J ∩ rad B` into the finite product of these quotients. Hence `J ∩ rad B` has finite
codimension in `J`, and in a semisimple Banach algebra every separating ideal is
finite-dimensional. This is the finiteness half of the structure theorem for separating ideals,
on which the automatic continuity of surjective homomorphisms onto, and of derivations on,
semisimple Banach algebras rests.

The finiteness is proved by contradiction. An infinite family of primitive ideals not containing
`J` contains a sequence `P 0, P 1, …` in which no ideal contains an earlier one: an increasing
chain is ruled out because `B ⧸ P 0` is finite-dimensional. Using that primitive ideals are
prime and closed, and the Baire category theorem in the Banach space `P n`, one chooses
`b n ∈ P n` so that each product `b 0 ⋯ b (n - 1)` lies outside every `P m` with `m ≥ n`. The
left nest `closure (b 0 ⋯ b (n - 1) J)` of `J` then strictly decreases: its `n + 1`-st term lies
in `P n` and its `n`-th term does not.

## Main results

* `Submodule.IsSeparatingIdeal.finite_setOf_isPrimitive_and_not_le`: a separating ideal is
  contained in all but finitely many primitive ideals.
* `Submodule.IsSeparatingIdeal.finiteDimensional_quotient_comap_jacobson`: a separating ideal
  `J` is finite-dimensional modulo `J ∩ rad B`.
* `Submodule.IsSeparatingIdeal.finiteDimensional_of_jacobson_eq_bot`: every separating ideal of
  a semisimple unital complex Banach algebra is finite-dimensional.

## References

* H. G. Dales, *Banach Algebras and Automatic Continuity*, §5.2: the structure of separating
  ideals.
* A. M. Sinclair, *Automatic Continuity of Linear Operators*, London Math. Soc. Lecture Note
  Series 21.
-/

public section

open Filter

namespace Submodule.IsSeparatingIdeal

variable {B : Type*} [NormedRing B] [NormedAlgebra ℂ B] [CompleteSpace B] {J : Submodule ℂ B}

/-- There is no sequence of primitive ideals `P n`, none containing the separating ideal `J`,
in which no ideal contains an earlier one. -/
private theorem false_of_forall_not_le (hJ : J.IsSeparatingIdeal) (P : ℕ → Ideal B)
    (hP : ∀ n, (P n).IsPrimitive) (hJP : ∀ n, ¬ J ≤ (P n).restrictScalars ℂ)
    (hPP : ∀ m n, m < n → ¬ P m ≤ P n) : False := by
  -- Given `c` outside every `P m` with `m ≥ n`, Baire category in the Banach space `P n` gives
  -- `b ∈ P n` with `c * b` outside every `P m` with `m > n`.
  have step (n : ℕ) (c : B) (hc : ∀ m, n ≤ m → c ∉ P m) :
      ∃ b ∈ P n, ∀ m, n < m → c * b ∉ P m := by
    let K : Submodule ℂ B := (P n).restrictScalars ℂ
    have : CompleteSpace K := (hP n).isClosed.completeSpace_coe
    let F : ℕ → Submodule ℂ K := fun k ↦
      ((P (n + k + 1)).restrictScalars ℂ).comap (LinearMap.mulLeft ℂ c ∘ₗ K.subtype)
    have hFc (k : ℕ) : IsClosed (F k : Set K) :=
      (hP _).isClosed.preimage (continuous_const.mul continuous_subtype_val)
    -- `F k = ⊤` would force `P n ≤ P (n + k + 1)`, as `P (n + k + 1)` is prime.
    have hFt (k : ℕ) : F k ≠ ⊤ := by
      intro htop
      refine hPP n (n + k + 1) (by omega) fun x hx ↦ ?_
      refine ((hP _).mem_or_mem_of_forall_mul_mul_mem fun r ↦ ?_).resolve_left (hc _ (by omega))
      have : (⟨r * x, (P n).mul_mem_left r hx⟩ : K) ∈ F k := htop ▸ Submodule.mem_top
      simpa [F, K, mul_assoc] using this
    obtain ⟨x, hx⟩ := Submodule.exists_forall_notMem_of_isClosed F hFc hFt
    refine ⟨x, x.2, fun m hm ↦ ?_⟩
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_lt hm
    simpa [F, K] using hx k
  choose g hgP hg using step
  -- The partial products `C n = b 0 ⋯ b (n - 1)` lie outside every `P m` with `m ≥ n`.
  let C : (n : ℕ) → {c : B // ∀ m, n ≤ m → c ∉ P m} := fun n ↦
    Nat.rec ⟨1, fun m _ h ↦ (hP m).ne_top ((P m).eq_top_of_isUnit_mem h isUnit_one)⟩
      (fun n c ↦ ⟨c.1 * g n c.1 c.2, hg n c.1 c.2⟩) n
  let b : ℕ → B := fun n ↦ g n (C n).1 (C n).2
  have hprod (n : ℕ) (y : B) :
      ((List.range n).map fun i ↦ LinearMap.mulLeft ℂ (b i)).prod y = (C n).1 * y := by
    induction n generalizing y with
    | zero => simp [C]
    | succ n ih => simp [List.range_succ, ih, b, C, mul_assoc]
  let W : ℕ → Submodule ℂ B := fun n ↦
    (J.map ((List.range n).map fun i ↦ LinearMap.mulLeft ℂ (b i)).prod).topologicalClosure
  -- `W (n + 1)` lies in the closed two-sided ideal `P n`, because `b n ∈ P n`.
  have hle (n : ℕ) : W (n + 1) ≤ (P n).restrictScalars ℂ := by
    have := (hP n).isTwoSided
    refine Submodule.topologicalClosure_minimal _ ?_ (hP n).isClosed
    rintro _ ⟨y, -, rfl⟩
    rw [hprod]
    exact (P n).mul_mem_right y ((P n).mul_mem_left _ (hgP n _ _))
  -- `W n` does not: as `P n` is prime and `J ⊄ P n`, some `C n * j` with `j ∈ J` avoids `P n`.
  have hnle (n : ℕ) : ¬ W n ≤ (P n).restrictScalars ℂ := by
    obtain ⟨j, hj, hjP⟩ := IsConcreteLE.not_le_iff_exists.mp (hJP n)
    intro h
    refine ((hP n).mem_or_mem_of_forall_mul_mul_mem (a := (C n).1) (b := j) fun r ↦ ?_).elim
      ((C n).2 n le_rfl) hjP
    rw [mul_assoc, ← hprod]
    exact h (Submodule.le_topologicalClosure _ (Submodule.mem_map_of_mem (hJ.mul_mem_left r hj)))
  obtain ⟨N, hN⟩ := eventuallyConst_atTop_nat.1 (hJ.eventuallyConst_left b)
  have hWN : W (N + 1) = W N := hN N le_rfl
  exact hnle N (hWN ▸ hle N)

/-- **A separating ideal lies in all but finitely many primitive ideals.** For a separating
ideal `J` of a unital complex Banach algebra `B`, only finitely many primitive ideals of `B` do
not contain `J`. -/
theorem finite_setOf_isPrimitive_and_not_le (hJ : J.IsSeparatingIdeal) :
    {P : Ideal B | P.IsPrimitive ∧ ¬ J ≤ P.restrictScalars ℂ}.Finite := by
  by_contra hinf
  let e := Set.Infinite.natEmbedding _ hinf
  -- Pass to a subsequence that is either an increasing chain or has no inclusions forwards.
  obtain ⟨g, hg⟩ := exists_increasing_or_nonincreasing_subseq (fun P Q : Ideal B ↦ P ≤ Q)
    fun n ↦ (e n : Ideal B)
  let P : ℕ → Ideal B := fun n ↦ e (g n)
  have hP (n : ℕ) : (P n).IsPrimitive := (e (g n)).2.1
  have hJP (n : ℕ) : ¬ J ≤ (P n).restrictScalars ℂ := (e (g n)).2.2
  rcases hg with hg | hg
  · -- An increasing chain above `P 0` stabilizes, since `B ⧸ P 0` is finite-dimensional.
    have := finiteDimensional_quotient_of_isPrimitive hJ (hP 0) (hJP 0)
    have : IsNoetherian B (B ⧸ P 0) := isNoetherian_of_tower ℂ inferInstance
    have hmono : Monotone P := fun m n hmn ↦ hmn.eq_or_lt.elim (fun h ↦ h ▸ le_rfl) (hg m n)
    let f : ℕ →o Submodule B (B ⧸ P 0) :=
      ⟨fun n ↦ Submodule.map (P 0).mkQ (P n), fun m n hmn ↦ Submodule.map_mono (hmono hmn)⟩
    obtain ⟨N, hN⟩ := monotone_stabilizes_iff_noetherian.mpr this f
    have h : Submodule.map (P 0).mkQ (P N) = Submodule.map (P 0).mkQ (P (N + 1)) :=
      hN (N + 1) N.le_succ
    replace h := congrArg (Submodule.comap (P 0).mkQ) h
    rw [Submodule.comap_map_mkQ, Submodule.comap_map_mkQ, sup_of_le_right (hmono N.zero_le),
      sup_of_le_right (hmono (N + 1).zero_le)] at h
    exact N.succ_ne_self (g.injective (e.injective (Subtype.ext h.symm)))
  · exact false_of_forall_not_le hJ P hP hJP hg

/-- **A separating ideal is finite-dimensional modulo the radical.** For a separating ideal `J`
of a unital complex Banach algebra `B`, the quotient of `J` by `J ∩ rad B` is finite-dimensional
over `ℂ`. -/
theorem finiteDimensional_quotient_comap_jacobson (hJ : J.IsSeparatingIdeal) :
    FiniteDimensional ℂ (J ⧸ ((Ring.jacobson B).restrictScalars ℂ).comap J.subtype) := by
  let S := {P : Ideal B | P.IsPrimitive ∧ ¬ J ≤ P.restrictScalars ℂ}
  have := hJ.finite_setOf_isPrimitive_and_not_le.to_subtype
  have (P : S) : FiniteDimensional ℂ (B ⧸ (P : Ideal B)) :=
    finiteDimensional_quotient_of_isPrimitive hJ P.2.1 P.2.2
  -- `J` maps to the finite product of the quotients `B ⧸ P` with kernel `J ∩ rad B`.
  let φ : J →ₗ[ℂ] (P : S) → B ⧸ (P : Ideal B) :=
    LinearMap.pi fun P ↦ ((P : Ideal B).mkQ.restrictScalars ℂ) ∘ₗ J.subtype
  have hker : LinearMap.ker φ = ((Ring.jacobson B).restrictScalars ℂ).comap J.subtype := by
    ext x
    rw [LinearMap.mem_ker, Submodule.mem_comap, Submodule.restrictScalars_mem,
      Submodule.subtype_apply, TauCeti.Ring.mem_jacobson_iff_forall_mem_isPrimitive, funext_iff]
    constructor
    · intro h P hP
      by_cases hJP : J ≤ P.restrictScalars ℂ
      · exact hJP x.2
      · simpa [φ, Submodule.Quotient.mk_eq_zero] using h ⟨P, hP, hJP⟩
    · intro h P
      simpa [φ, Submodule.Quotient.mk_eq_zero] using h P P.2.1
  rw [← hker]
  exact Module.Finite.equiv φ.quotKerEquivRange.symm

/-- **Separating ideals of semisimple Banach algebras are finite-dimensional.** If `B` is a
unital complex Banach algebra with zero Jacobson radical, every separating ideal of `B` is
finite-dimensional over `ℂ`. -/
theorem finiteDimensional_of_jacobson_eq_bot (hJ : J.IsSeparatingIdeal)
    (hB : Ring.jacobson B = ⊥) : FiniteDimensional ℂ J := by
  have := hJ.finiteDimensional_quotient_comap_jacobson
  rw [hB, Submodule.restrictScalars_bot, Submodule.comap_bot, Submodule.ker_subtype] at this
  exact Module.Finite.equiv (Submodule.quotEquivOfEqBot ⊥ rfl)

end Submodule.IsSeparatingIdeal

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.DiophantineApproximation.Subspace.Rank
public import TauCeti.NumberTheory.NumberField.CanonicalEmbedding.SmallInteger

/-!
# Successive minima concentrated at one infinite place

Let `K` be a number field of degree `d`, and let `x 0, …, x (n - 1)` be vectors of `ι → K`
realizing the successive minima `μ 0 ≤ … ≤ μ (n - 1)` over `K` of an approximation domain
`approxDomain S₀ L c Q`, so that `v (L v i (x l)) ≤ μ l · Q ^ c v i` at every infinite place `v`.
The minimum `μ l` enters this bound at every infinite place at once. Multiplying `x l` by a
nonzero algebraic integer `a l`, chosen by Minkowski's theorem for one scalar
(`TauCeti.NumberField.exists_ne_zero_forall_infinitePlace_mul_le`), moves it to a single infinite
place `w₀`: afterwards the bound is a constant times `Q ^ c v i` at every infinite place `v ≠ w₀`,
and a constant times `μ l ^ (d / mult w₀) · Q ^ c w₀ i` at `w₀`. The product of the local bounds
over the infinite places, counted with multiplicity, is unchanged up to the constant, because
`(μ l ^ (d / mult w₀)) ^ mult w₀ = μ l ^ d`.

The scaled vectors stay in the lattice `approxModule S₀ L c Q`, since it is an `𝓞 K`-module, and
they stay linearly independent, with their first `finrank K V(Q)` members still spanning the span
`V(Q)` of the domain. The constant is `unitConst K ^ (1 / d)`, which depends only on `K`.

With the minima at `w₀` alone, Evertse's lemma (`NumberField.exists_evertse`) applied to the
scaled family needs non-constant weights `μ` only at `w₀`. At the other places all weights are
equal, so the permutation it returns there does not matter.

## Main results

* `TauCeti.NumberField.exists_ne_zero_forall_apply_smul_le`: one vector bounded at every infinite
  place by `t` times given bounds has a nonzero algebraic-integer multiple whose bounds carry
  `t` at `w₀` alone, as `t ^ (d / mult w₀)`.
* `TauCeti.NumberField.exists_balance`: for forms independent at the infinite places and at `S₀`,
  an approximation domain of positive level has `card ι` `K`-linearly independent vectors in its
  lattice `approxModule S₀ L c Q`, whose first `finrank K V(Q)` members span the domain, with the
  successive minima concentrated at `w₀`.

## References

* J.-H. Evertse and H. P. Schlickewei, *A quantitative version of the absolute subspace theorem*,
  J. reine angew. Math. 548 (2002), 21–127, §9.
* E. Bombieri and W. Gubler, *Heights in Diophantine Geometry*, Cambridge University Press (2006),
  7.5.30–7.5.32.
-/

public section

open Module NumberField NumberField.InfinitePlace NumberField.mixedEmbedding Set
open scoped Pointwise

namespace TauCeti.NumberField

variable {K : Type*} [Field K] [NumberField K]

/-- **Concentrating the size of one vector at an infinite place** (after Evertse–Schlickewei
2002, §9): if forms `L v i` on a `K`-vector space have `v (L v i x) ≤ t · b v i` at every infinite
place `v`, with `t > 0`, then some nonzero algebraic integer `a` has
`v (L v i (a • x)) ≤ C · b v i` at every infinite place `v ≠ w₀` and
`w₀ (L w₀ i (a • x)) ≤ C · t ^ (d / mult w₀) · b w₀ i`, where `d = [K : ℚ]` and
`C = unitConst K ^ (1 / d)`. -/
theorem exists_ne_zero_forall_apply_smul_le {V κ : Type*} [AddCommGroup V] [Module K V]
    (w₀ : InfinitePlace K) {L : InfinitePlace K → κ → Dual K V} {b : InfinitePlace K → κ → ℝ}
    {t : ℝ} (ht : 0 < t) {x : V}
    (hx : ∀ (v : InfinitePlace K) (i : κ), v (L v i x) ≤ t * b v i) :
    ∃ a : 𝓞 K, a ≠ 0 ∧
      (∀ v : InfinitePlace K, v ≠ w₀ → ∀ i : κ,
        v (L v i ((a : K) • x)) ≤ unitConst K ^ ((finrank ℚ K : ℝ)⁻¹) * b v i) ∧
      ∀ i : κ, w₀ (L w₀ i ((a : K) • x)) ≤
        unitConst K ^ ((finrank ℚ K : ℝ)⁻¹) * t ^ ((finrank ℚ K : ℝ) / mult w₀) * b w₀ i := by
  obtain ⟨a, ha, hne, h₀⟩ := exists_ne_zero_forall_infinitePlace_mul_le w₀ ht
  -- The bounds `b v i` are nonnegative, since they bound absolute values from above.
  have hb (v : InfinitePlace K) (i : κ) : 0 ≤ b v i :=
    nonneg_of_mul_nonneg_right ((v.val.nonneg _).trans (hx v i)) ht
  -- At every infinite place, `v (L v i (a • x)) ≤ (v a · t) · b v i`.
  have hsmul (v : InfinitePlace K) (i : κ) :
      v (L v i ((a : K) • x)) ≤ v (a : K) * t * b v i := by
    rw [map_smul, smul_eq_mul, map_mul, mul_assoc]
    exact mul_le_mul_of_nonneg_left (hx v i) (v.val.nonneg _)
  refine ⟨a, ha, fun v hv i ↦ ?_, fun i ↦ ?_⟩
  · exact (hsmul v i).trans (mul_le_mul_of_nonneg_right (hne v hv) (hb v i))
  · exact (hsmul w₀ i).trans (mul_le_mul_of_nonneg_right h₀ (hb w₀ i))

variable {ι : Type*} [Fintype ι]

/-- **The successive minima of an approximation domain, concentrated at one infinite place**
(after Evertse–Schlickewei 2002, §9). Let `μ l` be the successive minima over `K` of
`approxDomain S₀ L c Q`, for forms independent at every infinite place and at `S₀` and a level
`Q > 0`, and let `w₀` be an infinite place. Then there are `card ι` linearly independent vectors
`y l` of the lattice `approxModule S₀ L c Q`, whose first `finrank K V(Q)` members span
`V(Q) = approxSpan S₀ L c Q`, with `v (L v i (y l)) ≤ C · Q ^ c v i` at every infinite place
`v ≠ w₀` and `w₀ (L w₀ i (y l)) ≤ C · μ l ^ (d / mult w₀) · Q ^ c w₀ i`, where `d = [K : ℚ]` and
`C = unitConst K ^ (1 / d)` depends only on `K`. -/
theorem exists_balance {S₀ : Finset (FinitePlace K)} {L : AbsoluteValue K ℝ → ι → Dual K (ι → K)}
    (hLInf : ∀ v : InfinitePlace K, LinearIndependent K (L v.val))
    (hLFin : ∀ v ∈ S₀, LinearIndependent K (L v.val)) (c : AbsoluteValue K ℝ → ι → ℝ) {Q : ℝ}
    (hQ : 0 < Q) (w₀ : InfinitePlace K) :
    ∃ y : Fin (Fintype.card ι) → ι → K, LinearIndependent K y ∧
      approxSpan S₀ L c Q =
        Submodule.span K (y '' {l | l.val < finrank K (approxSpan S₀ L c Q)}) ∧
      ∀ l, y l ∈ approxModule S₀ L c Q ∧
        (∀ v : InfinitePlace K, v ≠ w₀ → ∀ i : ι,
          v (L v.val i (y l)) ≤ unitConst K ^ ((finrank ℚ K : ℝ)⁻¹) * Q ^ c v.val i) ∧
        ∀ i : ι, w₀ (L w₀.val i (y l)) ≤ unitConst K ^ ((finrank ℚ K : ℝ)⁻¹) *
          (approxModule S₀ L c Q).successiveMinimum (approxBody L c Q) l ^
            ((finrank ℚ K : ℝ) / mult w₀) * Q ^ c w₀.val i := by
  let _ := discreteTopology_mixedImage_approxModule hLFin c Q
  let _ := isZLattice_mixedImage_approxModule hLFin c hQ.ne'
  set Λ := approxModule S₀ L c Q
  set μ := Λ.successiveMinimum (approxBody L c Q)
  obtain ⟨B, hcoe, hB, -⟩ := exists_convexBody_approxSpan (S₀ := S₀) hLInf c hQ
  -- A family realizing the successive minima, each of which is positive.
  obtain ⟨x, hx, hxB⟩ := Λ.exists_linearIndependent_mem_smul_successiveMinimum hB
  have hμ (l : Fin (Fintype.card ι)) : 0 < μ l := by
    have h := Λ.successiveMinimum_pos hB l.isLt
    rwa [hcoe] at h
  rw [hcoe] at hxB
  -- Membership in `μ l • approxBody L c Q`, read at the infinite places.
  have hxL (l : Fin (Fintype.card ι)) (v : InfinitePlace K) (i : ι) :
      v (L v.val i (x l)) ≤ μ l * Q ^ c v.val i := by
    have h := (hxB l).2
    rw [Set.mem_smul_set_iff_inv_smul_mem₀ (hμ l).ne'] at h
    have h' := (mem_approxBody.1 h) v i
    simp only [Pi.smul_apply, mul_smul_comm, ← Finset.smul_sum, normAtPlace_smul,
      sum_mixedEmbedding_mul_mixedEmbedding, normAtPlace_apply, abs_inv, abs_of_pos (hμ l)] at h'
    exact (inv_mul_le_iff₀ (hμ l)).1 h'
  choose a ha hne h₀ using fun l ↦
    exists_ne_zero_forall_apply_smul_le w₀ (L := fun v ↦ L v.val) (b := fun v i ↦ Q ^ c v.val i)
      (hμ l) (hxL l)
  -- The scaling factors, as units of `K`.
  let u : Fin (Fintype.card ι) → Kˣ := fun l ↦ Units.mk0 (a l : K) (by simpa using ha l)
  have hu (l : Fin (Fintype.card ι)) : (a l : K) • x l = u l • x l := (Units.smul_mk0 _ _).symm
  refine ⟨fun l ↦ (a l : K) • x l, ?_, ?_, fun l ↦ ⟨?_, hne l, h₀ l⟩⟩
  · simp_rw [hu]
    exact hx.units_smul u
  · refine (approxSpan_eq_span_image hLInf hLFin c hQ hx (fun l ↦ (hxB l).1)
      fun l ↦ (hxB l).2).trans (le_antisymm ?_ ?_) <;>
      refine Submodule.span_le.2 ?_ <;> rintro _ ⟨l, hl, rfl⟩
    · rw [← inv_smul_smul (u l) (x l), ← hu]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨l, hl, rfl⟩)
    · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨l, hl, rfl⟩)
  · beta_reduce
    rw [RingOfIntegers.coe_eq_algebraMap, algebraMap_smul]
    exact Λ.smul_mem _ (hxB l).1

end TauCeti.NumberField

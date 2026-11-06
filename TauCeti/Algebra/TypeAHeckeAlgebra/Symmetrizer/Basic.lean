/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.TypeAHeckeAlgebra.Parabolic.Basic
public import TauCeti.Algebra.Ring.QuadraticPow

/-!
# Parabolic q-symmetrizers

For a standard parabolic subgroup `W_J`, define the weighted sum
`C_J(a) = ∑ w ∈ W_J, a ^ length w • T_w`. If `a² = (q - q⁻¹)a + 1`, every generator
indexed by `J` acts on this sum on either side by `a`. The choices `a = q` and
`a = -q⁻¹` give the row symmetrizer and column antisymmetrizer, respectively. These are the
parabolic sums used to construct Hecke permutation modules and Specht modules.

The identity coefficient is always `1`, even when the parameter is a root of unity. The sum
is a quasi-idempotent with scalar `∑ w ∈ W_J, a ^ (2 * length w)`. Dividing by this scalar
produces an idempotent only when it is a unit; no division is made in the definition.
Only the parabolic subgroup being summed over needs to be finite.

## References

* R. Dipper and G. James, *Representations of Hecke algebras of general linear groups*,
  Proc. London Math. Soc. (3) 52 (1986), 20–52, Section 3.
* A. Mathas, *Iwahori–Hecke algebras and Schur algebras of the symmetric group*,
  University Lecture Series 15, AMS (1999), Chapter 3.
-/

public section

namespace TauCeti.TypeAHeckeAlgebra

open CoxeterSystem

variable {R : Type*} [CommRing R] {q : Rˣ} {n : ℕ}
variable {W : Type*} [Group W] (cs : CoxeterSystem (CoxeterMatrix.A (n - 1)) W)
variable (J : Set (Fin (n - 1))) [Finite (cs.parabolic J)]

/-- The parabolic weighted sum `C_J(a) = ∑ w ∈ W_J, a ^ length w • T_w`.
At `a = q` this is the q-symmetrizer, and at `a = -q⁻¹` the q-antisymmetrizer. -/
noncomputable def parabolicEigenSum (a : R) : TypeAHeckeAlgebra R q n :=
  letI := Fintype.ofFinite (cs.parabolic J)
  ∑ w : cs.parabolic J, a ^ cs.length w • Tw q cs w

/-- The defining finite sum, with any enumeration of the parabolic subgroup. -/
theorem parabolicEigenSum_eq_sum [Fintype (cs.parabolic J)] (a : R) :
    parabolicEigenSum (q := q) cs J a =
      ∑ w : cs.parabolic J, a ^ cs.length w • Tw q cs w := by
  rw [parabolicEigenSum, Subsingleton.elim (Fintype.ofFinite (cs.parabolic J))
    (inferInstance : Fintype (cs.parabolic J))]

/-- A parabolic weighted sum lies in the corresponding parabolic Hecke subalgebra,
regardless of whether its weight satisfies the Hecke quadratic. -/
theorem parabolicEigenSum_mem_parabolic (a : R) :
    parabolicEigenSum (q := q) cs J a ∈ parabolic q J := by
  classical
  let := Fintype.ofFinite (cs.parabolic J)
  rw [parabolicEigenSum_eq_sum]
  exact Subalgebra.sum_mem _ fun w _ ↦
    Subalgebra.smul_mem _ (Tw_mem_parabolic cs w.2) _

open scoped Classical in
/-- The PBW coefficients of a parabolic weighted sum, extended by zero off the subgroup. -/
@[simp]
theorem basisTw_repr_parabolicEigenSum (a : R) (w : W) :
    (basisTw q cs).repr (parabolicEigenSum cs J a) w =
      if w ∈ cs.parabolic J then a ^ cs.length w else 0 := by
  classical
  let _ := Fintype.ofFinite (cs.parabolic J)
  have hrepr (v : W) : (basisTw q cs).repr (Tw q cs v) w = if v = w then 1 else 0 := by
    rw [← coe_basisTw, Module.Basis.repr_self_apply]
  rw [parabolicEigenSum_eq_sum]
  simp only [map_sum, map_smul]
  simp only [Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.smul_apply, hrepr, smul_eq_mul]
  by_cases hw : w ∈ cs.parabolic J
  · rw [ite_eq_left hw, Finset.sum_eq_single (⟨w, hw⟩ : cs.parabolic J)]
    · simp
    · intro v _ hv
      have : (v : W) ≠ w := fun h ↦ hv (Subtype.ext h)
      simp [this]
    · simp
  · simp [hw, show ∀ v : cs.parabolic J, (v : W) ≠ w from fun v h ↦ hw (h ▸ v.property)]

variable {cs J} in
/-- The identity PBW coefficient recovers the scalar multiplying a parabolic weighted sum.
Thus this parametrization of the line is injective over every coefficient ring. -/
theorem smul_parabolicEigenSum_injective (a : R) :
    Function.Injective (fun r : R => r • parabolicEigenSum (q := q) cs J a) := by
  intro r s h
  have hc := congrArg (fun x => (basisTw q cs).repr x 1) h
  simpa only [map_smul, Finsupp.smul_apply, basisTw_repr_parabolicEigenSum,
    Subgroup.one_mem, ite_true, cs.length_one, pow_zero, smul_eq_mul, mul_one] using hc

/-- The standard coset vectors of any parabolic weighted sum are linearly independent,
without requiring its weight to satisfy the Hecke quadratic. -/
theorem linearIndependent_Tw_mul_parabolicEigenSum (a : R) :
    LinearIndependent R (fun d : {d : W // cs.IsMinimalCosetRep J d} ↦
      Tw q cs d * parabolicEigenSum cs J a) := by
  classical
  let c : parabolic (R := R) q J := ⟨_, parabolicEigenSum_mem_parabolic cs J a⟩
  let f : R →ₗ[R] parabolic (R := R) q J := LinearMap.toSpanSingleton R _ c
  have hf : Function.Injective f := by
    intro r s h
    exact smul_parabolicEigenSum_injective (q := q) (cs := cs) (J := J) a
      (congrArg Subtype.val h)
  let F := (parabolicCosetEquivRight q cs J).toLinearMap ∘ₗ Finsupp.mapRange.linearMap f
  have hF : Function.Injective F :=
    (parabolicCosetEquivRight q cs J).injective.comp
      (Finsupp.mapRange_injective f (map_zero f) hf)
  convert (Finsupp.linearIndependent_single_one (R := R)
    (ι := {d : W // cs.IsMinimalCosetRep J d})).map' F
      (LinearMap.ker_eq_bot.mpr hF) using 1
  ext d
  simp [F, f, c]

/-- A parabolic weighted sum is nonzero over every nontrivial coefficient ring. -/
theorem parabolicEigenSum_ne_zero [Nontrivial R] (a : R) :
    parabolicEigenSum (q := q) cs J a ≠ 0 := by
  intro h
  have := basisTw_repr_parabolicEigenSum (q := q) cs J a 1
  simp [h] at this

/-- Every parabolic generator acts on the weighted sum on the left by `a`. -/
theorem T_mul_parabolicEigenSum {a : R} (ha : a * a = ((q : R) - ↑q⁻¹) * a + 1)
    {i : Fin (n - 1)} (hi : i ∈ J) :
    T q i * parabolicEigenSum cs J a = a • parabolicEigenSum cs J a := by
  classical
  apply (basisTw q cs).repr.injective
  ext w
  rw [basisTw_repr_T_mul]
  simp only [map_smul, Finsupp.smul_apply, smul_eq_mul, basisTw_repr_parabolicEigenSum]
  have hmem : cs.simple i * w ∈ cs.parabolic J ↔ w ∈ cs.parabolic J := by
    exact ⟨fun h ↦ by simpa using mul_mem (cs.simple_mem_parabolic hi) h,
      fun h ↦ mul_mem (cs.simple_mem_parabolic hi) h⟩
  by_cases hw : w ∈ cs.parabolic J
  · simp only [hw, hmem.mpr hw, ite_true]
    by_cases hd : cs.IsLeftDescent w i
    · rw [ite_eq_left hd]
      rw [← cs.isLeftDescent_iff.mp hd]
      exact mul_pow_succ_add_pow_of_mul_self_eq ha _
    · rw [ite_eq_right hd, zero_add, cs.not_isLeftDescent_iff.mp hd, pow_succ, mul_comm]
  · simp [hw, hmem]

/-- Every parabolic generator acts on the weighted sum on the right by `a`. -/
theorem parabolicEigenSum_mul_T {a : R} (ha : a * a = ((q : R) - ↑q⁻¹) * a + 1)
    {i : Fin (n - 1)} (hi : i ∈ J) :
    parabolicEigenSum cs J a * T q i = a • parabolicEigenSum cs J a := by
  classical
  apply (basisTw q cs).repr.injective
  ext w
  rw [basisTw_repr_mul_T]
  simp only [map_smul, Finsupp.smul_apply, smul_eq_mul, basisTw_repr_parabolicEigenSum]
  have hmem : w * cs.simple i ∈ cs.parabolic J ↔ w ∈ cs.parabolic J := by
    exact ⟨fun h ↦ by simpa using mul_mem h (cs.simple_mem_parabolic hi),
      fun h ↦ mul_mem h (cs.simple_mem_parabolic hi)⟩
  by_cases hw : w ∈ cs.parabolic J
  · simp only [hw, hmem.mpr hw, ite_true]
    by_cases hd : cs.IsRightDescent w i
    · rw [ite_eq_left hd]
      rw [← cs.isRightDescent_iff.mp hd]
      exact mul_pow_succ_add_pow_of_mul_self_eq ha _
    · rw [ite_eq_right hd, zero_add, cs.not_isRightDescent_iff.mp hd, pow_succ, mul_comm]
  · simp [hw, hmem]

/-- A parabolic PBW element acts on the weighted sum on the left by `a ^ length w`. -/
theorem Tw_mul_parabolicEigenSum {a : R} (ha : a * a = ((q : R) - ↑q⁻¹) * a + 1)
    {w : W} (hw : w ∈ cs.parabolic J) :
    Tw q cs w * parabolicEigenSum cs J a = a ^ cs.length w • parabolicEigenSum cs J a := by
  obtain ⟨ω, hω, hωJ, rfl⟩ := cs.exists_isReduced_wordProd_eq_of_mem_parabolic hw
  rw [Tw_wordProd cs hω, hω.eq]
  suffices ∀ ω : List (Fin (n - 1)), (∀ i ∈ ω, i ∈ J) →
      (ω.map (T q)).prod * parabolicEigenSum cs J a =
        a ^ ω.length • parabolicEigenSum cs J a from this ω hωJ
  intro ω hJ
  induction ω with
  | nil => simp
  | cons i ω ih =>
    simp only [List.map_cons, List.prod_cons, List.length_cons, mul_assoc]
    rw [ih (fun j hj ↦ hJ j (by simp [hj])), mul_smul_comm,
      T_mul_parabolicEigenSum cs J ha (hJ i (by simp)), smul_smul, pow_succ]

/-- A parabolic PBW element acts on the weighted sum on the right by `a ^ length w`. -/
theorem parabolicEigenSum_mul_Tw {a : R} (ha : a * a = ((q : R) - ↑q⁻¹) * a + 1)
    {w : W} (hw : w ∈ cs.parabolic J) :
    parabolicEigenSum cs J a * Tw q cs w = a ^ cs.length w • parabolicEigenSum cs J a := by
  obtain ⟨ω, hω, hωJ, rfl⟩ := cs.exists_isReduced_wordProd_eq_of_mem_parabolic hw
  rw [Tw_wordProd cs hω, hω.eq]
  suffices ∀ ω : List (Fin (n - 1)), (∀ i ∈ ω, i ∈ J) →
      parabolicEigenSum cs J a * (ω.map (T q)).prod =
        a ^ ω.length • parabolicEigenSum cs J a from this ω hωJ
  intro ω hJ
  induction ω with
  | nil => simp
  | cons i ω ih =>
    simp only [List.map_cons, List.prod_cons, List.length_cons, ← mul_assoc]
    rw [parabolicEigenSum_mul_T cs J ha (hJ i (by simp)), smul_mul_assoc,
      ih (fun j hj ↦ hJ j (by simp [hj])), smul_smul, pow_succ, mul_comm a]

/-- **Quasi-idempotence.** The scalar is the parabolic length generating function evaluated
at `a²`. This identity remains valid when that scalar vanishes. -/
theorem parabolicEigenSum_mul_self [Fintype (cs.parabolic J)] {a : R}
    (ha : a * a = ((q : R) - ↑q⁻¹) * a + 1) :
    parabolicEigenSum (q := q) cs J a * parabolicEigenSum cs J a =
      (∑ w : cs.parabolic J, a ^ (2 * cs.length w)) • parabolicEigenSum cs J a := by
  conv_lhs => lhs; rw [parabolicEigenSum_eq_sum]
  rw [Finset.sum_mul]
  simp_rw [smul_mul_assoc, Tw_mul_parabolicEigenSum cs J ha (Subtype.mem _),
    smul_smul, ← pow_add, ← two_mul]
  rw [Finset.sum_smul]

/-- Dividing by a unit quasi-idempotence scalar gives an idempotent. -/
theorem isIdempotentElem_smul_parabolicEigenSum [Fintype (cs.parabolic J)] {a : R}
    (ha : a * a = ((q : R) - ↑q⁻¹) * a + 1)
    (h : IsUnit (∑ w : cs.parabolic J, a ^ (2 * cs.length w))) :
    IsIdempotentElem ((↑h.unit⁻¹ : R) • parabolicEigenSum (q := q) cs J a) := by
  rw [IsIdempotentElem, smul_mul_assoc, mul_smul_comm, parabolicEigenSum_mul_self cs J ha,
    smul_smul, smul_smul, mul_assoc, h.val_inv_mul, mul_one]

/-- The row q-symmetrizer has quasi-idempotence scalar `∑ w ∈ W_J, q ^ (2 * length w)`. -/
theorem parabolicEigenSum_q_mul_self [Fintype (cs.parabolic J)] :
    parabolicEigenSum cs J (q : R) * parabolicEigenSum cs J (q : R) =
      (∑ w : cs.parabolic J, (q : R) ^ (2 * cs.length w)) •
        parabolicEigenSum (q := q) cs J (q : R) := by
  apply parabolicEigenSum_mul_self
  simp [sub_mul]

/-- The column q-antisymmetrizer has quasi-idempotence scalar
`∑ w ∈ W_J, q⁻¹ ^ (2 * length w)`. -/
theorem parabolicEigenSum_neg_inv_mul_self [Fintype (cs.parabolic J)] :
    parabolicEigenSum cs J (-(↑q⁻¹ : R)) * parabolicEigenSum cs J (-(↑q⁻¹ : R)) =
      (∑ w : cs.parabolic J, (↑q⁻¹ : R) ^ (2 * cs.length w)) •
        parabolicEigenSum (q := q) cs J (-(↑q⁻¹ : R)) := by
  have ha : (-(↑q⁻¹ : R)) * (-(↑q⁻¹ : R)) =
      ((q : R) - ↑q⁻¹) * (-(↑q⁻¹ : R)) + 1 := by simp [sub_mul]
  rw [parabolicEigenSum_mul_self cs J ha]
  simp [pow_mul]

/-- The full weighted sum has quasi-idempotence scalar indexed by the original Coxeter
carrier, rather than by the full parabolic subgroup subtype. -/
theorem parabolicEigenSum_univ_mul_self [Fintype W] {a : R}
    (ha : a * a = ((q : R) - ↑q⁻¹) * a + 1) :
    parabolicEigenSum (q := q) cs Set.univ a * parabolicEigenSum cs Set.univ a =
      (∑ w : W, a ^ (2 * cs.length w)) • parabolicEigenSum cs Set.univ a := by
  let := Fintype.ofFinite (cs.parabolic Set.univ)
  rw [parabolicEigenSum_mul_self cs Set.univ ha,
    cs.sum_parabolic_univ (fun w => a ^ (2 * cs.length w))]

/-- A unit full-sum normalization gives an idempotent without reindexing to the parabolic
subgroup subtype. -/
theorem isIdempotentElem_smul_parabolicEigenSum_univ [Fintype W] {a : R}
    (ha : a * a = ((q : R) - ↑q⁻¹) * a + 1)
    (h : IsUnit (∑ w : W, a ^ (2 * cs.length w))) :
    IsIdempotentElem ((↑h.unit⁻¹ : R) • parabolicEigenSum (q := q) cs Set.univ a) := by
  let := Fintype.ofFinite (cs.parabolic Set.univ)
  have hidem := isIdempotentElem_smul_parabolicEigenSum cs Set.univ ha
  rw [cs.sum_parabolic_univ (fun w => a ^ (2 * cs.length w))] at hidem
  exact hidem h

end TauCeti.TypeAHeckeAlgebra

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.RingTheory.SimpleModule.IsAlgClosed
public import TauCeti.Algebra.Algebra.PPowerCommutator.Split
public import TauCeti.GroupTheory.OrderOfElement.PPart
import TauCeti.GroupTheory.OrderOfElement.Basic
import Mathlib.Algebra.CharP.Algebra
import Mathlib.Algebra.MonoidAlgebra.Module
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.RingTheory.Artinian.Ring

/-!
# The `p`-power commutator subspace of a group algebra and the `p`-regular classes

Let `k` be a field of characteristic `p` and `G` a finite group. An element of `G` is
`p`-regular if its order is prime to `p`, and a conjugacy class is `p`-regular if its elements
are. The quotient of the group algebra `k[G]` by its `p`-power commutator subspace
`T(k[G]) = TauCeti.pPowerCommutatorSubmodule p k k[G]` has a basis given by representatives of the
`p`-regular conjugacy classes (Webb, proof of Theorem 9.3.6):

* the commutators of `k[G]` are spanned by the differences `x g x⁻¹ - g` of conjugate elements
  (Webb, Lemma 9.3.5), so conjugate elements are congruent modulo `T(k[G])`;
* every `g` is congruent to its `p`-regular part `s = pFreePart p g` modulo `T(k[G])`, since
  `g - s = (q - 1) s` with `q = pPart p g` of `p`-power order, and `(q - 1) ^ (p ^ a) = 0` once
  `q ^ (p ^ a) = 1`;
* representatives of the `p`-regular classes are linearly independent modulo `T(k[G])`: a
  suitable power `p ^ N` fixes every `p`-regular element, so the `p ^ N`-th power of a
  combination `∑ λ_c c` is congruent to `∑ λ_c ^ (p ^ N) c` modulo commutators, and the sum of the
  coefficients over a conjugacy class kills every commutator.

So `dim_k k[G] / T(k[G])` is the number of `p`-regular conjugacy classes, over every field of
characteristic `p`. With `TauCeti.finrank_quotient_pPowerCommutatorSubmodule_of_algEquiv_pi_matrix`
this counts the matrix factors of `k[G] / rad k[G]` when `k` is a splitting field, in particular
when `k` is algebraically closed.

## Main definitions

* `TauCeti.pRegularConjClasses p G`: the conjugacy classes of elements of order prime to `p`.

## Main results

* `TauCeti.finrank_quotient_pPowerCommutatorSubmodule_monoidAlgebra`: `dim_k k[G] / T(k[G])` is
  the number of `p`-regular conjugacy classes of `G`.
* `TauCeti.card_eq_card_pRegularConjClasses_of_algEquiv_pi_matrix`: if
  `k[G] / rad k[G] ≅ ∏_{i ∈ ι} M_{n_i}(k)` with every `n_i ≥ 1`, then `|ι|` is the number of
  `p`-regular conjugacy classes.
* `TauCeti.exists_algEquiv_pi_matrix_card_eq_card_pRegularConjClasses`: over an algebraically
  closed field of characteristic `p`, `k[G] / rad k[G]` is a product of as many matrix algebras over
  `k` as `G` has `p`-regular conjugacy classes.

## References

* P. Webb, *A Course in Finite Group Representation Theory*, Cambridge Studies in Advanced
  Mathematics 161, Cambridge University Press, 2016, Lemma 9.3.5, Theorem 9.3.6.
-/

public section

namespace TauCeti

open MonoidAlgebra Module Finset

section Classes

variable (p : ℕ) (G : Type*) [Group G]

/-- The **`p`-regular conjugacy classes** of a group: the classes of elements whose order is
coprime to `p`. -/
def pRegularConjClasses : Set (ConjClasses G) :=
  {c | ∃ g : G, ConjClasses.mk g = c ∧ (orderOf g).Coprime p}

variable {G}

/-- Membership in the `p`-regular conjugacy classes. -/
theorem mem_pRegularConjClasses_iff {c : ConjClasses G} :
    c ∈ pRegularConjClasses p G ↔ ∃ g : G, ConjClasses.mk g = c ∧ (orderOf g).Coprime p :=
  Iff.rfl

/-- The class of `g` is `p`-regular exactly when the order of `g` is coprime to `p`. -/
@[simp]
theorem mk_mem_pRegularConjClasses_iff {g : G} :
    ConjClasses.mk g ∈ pRegularConjClasses p G ↔ (orderOf g).Coprime p := by
  refine ⟨?_, fun h ↦ ⟨g, rfl, h⟩⟩
  rintro ⟨h, hh, hp⟩
  rwa [← (ConjClasses.mk_eq_mk_iff_isConj.1 hh).orderOf_eq]

end Classes

variable (p : ℕ) [hp : Fact p.Prime] (k : Type*) [Field k] [CharP k p]
variable {G : Type*} [Group G]

section Lemmas

variable (G) in
open Classical in
/-- The sum of the coefficients of an element of `k[G]` over a conjugacy class. -/
private noncomputable def classCoeff [Fintype G] (c : ConjClasses G) :
    MonoidAlgebra k G →ₗ[k] k where
  toFun x := ∑ g ∈ univ.filter (fun g ↦ ConjClasses.mk g = c), x.coeff g
  map_add' x y := by simp [coeff_add, sum_add_distrib]
  map_smul' r x := by simp [coeff_smul, mul_sum]

omit hp [CharP k p] in
open Classical in
private theorem classCoeff_single [Fintype G] (c : ConjClasses G) (h : G) (r : k) :
    classCoeff k G c (single h r) = if ConjClasses.mk h = c then r else 0 := by
  change ∑ g ∈ _, (single h r).coeff g = _
  simp [coeff_single, Finsupp.single_apply]

omit hp [CharP k p] in
/-- The coefficient sum over a conjugacy class kills the commutators of `k[G]`. -/
private theorem commutatorSubmodule_le_ker_classCoeff [Fintype G] (c : ConjClasses G) :
    commutatorSubmodule k (MonoidAlgebra k G) ≤ LinearMap.ker (classCoeff k G c) := by
  refine (commutatorSubmodule_le_ker_iff _).2 fun x y ↦ ?_
  induction x using MonoidAlgebra.induction_linear with
  | zero => simp
  | add x x' hx hx' => rw [add_mul, mul_add, map_add, map_add, hx, hx']
  | single g a =>
    induction y using MonoidAlgebra.induction_linear with
    | zero => simp
    | add y y' hy hy' => rw [mul_add, add_mul, map_add, map_add, hy, hy']
    | single h b =>
      have hc : ConjClasses.mk (g * h) = ConjClasses.mk (h * g) :=
        ConjClasses.mk_eq_mk_iff_isConj.2 (isConj_iff.2 ⟨g⁻¹, by group⟩)
      rw [single_mul_single, single_mul_single, classCoeff_single, classCoeff_single, hc,
        mul_comm a b]

omit [CharP k p] in
/-- Conjugate elements are congruent modulo commutators (Webb, Lemma 9.3.5). -/
theorem single_conj_sub_single_mem_commutatorSubmodule (g x : G) (r : k) :
    single (x * g * x⁻¹) r - single g r ∈ commutatorSubmodule k (MonoidAlgebra k G) := by
  simpa [single_mul_single, mul_assoc] using
    mul_sub_mul_mem_commutatorSubmodule k _ (single (x * g) r) (single x⁻¹ (1 : k))

include hp in
/-- Every element of `G` is congruent to its `p`-regular part modulo the `p`-power commutator
subspace of `k[G]`: their difference is nilpotent. -/
theorem single_sub_single_pFreePart_mem_pPowerCommutatorSubmodule (g : G) (r : k) :
    single g r - single (pFreePart p g) r ∈
      pPowerCommutatorSubmodule p k (MonoidAlgebra k G) := by
  have : CharP (MonoidAlgebra k G) p :=
    charP_of_injective_algebraMap (R := k) (A := MonoidAlgebra k G) (by
      rw [coe_algebraMap]
      exact single_right_injective.comp (algebraMap k k).injective) p
  set s := pFreePart p g
  set q := pPart p g
  have hsq : Commute q s := (commute_pFreePart_pPart p g).symm
  have hdiff : single g r - single s r = (single q 1 - 1) * single s r := by
    rw [sub_mul, single_mul_single, one_mul, one_mul, pPart_mul_pFreePart]
  have hcomm : Commute (single q (1 : k) - 1) (single s r) :=
    (single_commute_single hsq (Commute.one_left r)).sub_left (Commute.one_left _)
  have hnil : IsNilpotent (single q (1 : k) - 1) := by
    refine ⟨p ^ (orderOf g).factorization p, ?_⟩
    rw [sub_pow_char_pow_of_commute p _ (Commute.one_right _), one_pow, single_pow, one_pow,
      ← orderOf_pPart, pow_orderOf_eq_one, ← one_def, sub_self]
  rw [hdiff]
  exact mem_pPowerCommutatorSubmodule_of_isNilpotent p k (hcomm.isNilpotent_mul_right hnil)

end Lemmas

omit [CharP k p] in
/-- Conjugate elements of `G` are congruent modulo the commutators of `k[G]`. -/
theorem single_sub_single_mem_commutatorSubmodule_of_isConj {g h : G} (hgh : IsConj g h)
    (r : k) : single h r - single g r ∈ commutatorSubmodule k (MonoidAlgebra k G) := by
  obtain ⟨x, rfl⟩ := isConj_iff.1 hgh
  exact single_conj_sub_single_mem_commutatorSubmodule k g x r

include hp in
/-- Every element of `G` is congruent modulo `T(k[G])` to the chosen representative of the class of
its `p`-regular part. -/
theorem single_sub_single_out_mem_pPowerCommutatorSubmodule (g : G) (r : k) :
    single g r - single (ConjClasses.mk (pFreePart p g)).out r ∈
      pPowerCommutatorSubmodule p k (MonoidAlgebra k G) := by
  have h := single_sub_single_mem_commutatorSubmodule_of_isConj k
    (ConjClasses.mk_eq_mk_iff_isConj.1 (Quotient.out_eq (ConjClasses.mk (pFreePart p g)))) r
  rw [← sub_add_sub_cancel _ (single (pFreePart p g) r)]
  exact add_mem (single_sub_single_pFreePart_mem_pPowerCommutatorSubmodule p k g r)
    (commutatorSubmodule_le_pPowerCommutatorSubmodule p k h)

include hp in
/-- In a finite group, for every `n` there is `N ≥ n` such that `g ^ (p ^ N) = g` for every
`p`-regular `g`. -/
theorem exists_le_forall_pow_char_pow_eq_self [Finite G] (n : ℕ) :
    ∃ N, n ≤ N ∧ ∀ g : G, (orderOf g).Coprime p → g ^ p ^ N = g := by
  set m := ordCompl[p] (Nat.card G)
  have hm0 : 0 < m := Nat.ordCompl_pos p Nat.card_pos.ne'
  refine ⟨Nat.totient m * n, Nat.le_mul_of_pos_left n (Nat.totient_pos.2 hm0), fun g hg ↦ ?_⟩
  have hdvd : orderOf g ∣ m :=
    (Nat.Coprime.dvd_of_dvd_mul_left
      (hg.pow_right _)
      (by rw [Nat.ordProj_mul_ordCompl_eq_self]; exact orderOf_dvd_natCard _))
  have hpm : p ^ Nat.totient m ≡ 1 [MOD m] :=
    Nat.ModEq.pow_totient (Nat.coprime_ordCompl hp.out Nat.card_pos.ne')
  have h1 : p ^ (Nat.totient m * n) ≡ 1 [MOD orderOf g] := by
    rw [pow_mul]
    simpa using (hpm.pow n).of_dvd hdvd
  conv_rhs => rw [← pow_one g]
  exact pow_eq_pow_iff_modEq.2 h1

include hp in
/-- The representatives of the `p`-regular classes span `k[G] / T(k[G])`. -/
private theorem span_range_mkQ_single_out [Finite G] :
    ⊤ ≤ Submodule.span k (Set.range fun c : pRegularConjClasses p G ↦
      (pPowerCommutatorSubmodule p k (MonoidAlgebra k G)).mkQ (single c.val.out 1)) := by
  set T := pPowerCommutatorSubmodule p k (MonoidAlgebra k G)
  rintro x -
  obtain ⟨x, rfl⟩ := T.mkQ_surjective x
  induction x using MonoidAlgebra.induction_linear with
  | zero => simp
  | add x y hx hy => rw [map_add]; exact add_mem hx hy
  | single g r =>
    have hs : ConjClasses.mk (pFreePart p g) ∈ pRegularConjClasses p G := by
      rw [mk_mem_pRegularConjClasses_iff]
      exact coprime_orderOf_pFreePart hp.out (isOfFinOrder_of_finite g)
    have h : T.mkQ (single g r) = T.mkQ (single (ConjClasses.mk (pFreePart p g)).out r) := by
      rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq]
      exact single_sub_single_out_mem_pPowerCommutatorSubmodule p k g r
    rw [h, ← mul_one r, ← smul_eq_mul, ← smul_single, map_smul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨_, hs⟩, rfl⟩)

include hp in
/-- The representatives of the `p`-regular classes are linearly independent modulo `T(k[G])`. -/
private theorem linearIndependent_mkQ_single_out [Finite G] :
    LinearIndependent k fun c : pRegularConjClasses p G ↦
      (pPowerCommutatorSubmodule p k (MonoidAlgebra k G)).mkQ (single c.val.out 1) := by
  classical
  have := Fintype.ofFinite G
  have : Finite (ConjClasses G) := Quotient.finite _
  have := Fintype.ofFinite (pRegularConjClasses p G)
  set T := pPowerCommutatorSubmodule p k (MonoidAlgebra k G)
  have hmk : ∀ c : ConjClasses G, ConjClasses.mk c.out = c := fun c ↦ Quotient.out_eq c
  rw [Fintype.linearIndependent_iff]
  intro μ hμ c₀
  have hy : ∑ c : pRegularConjClasses p G, single c.val.out (μ c) ∈ T := by
    rw [← Submodule.Quotient.mk_eq_zero, ← Submodule.mkQ_apply, map_sum]
    simp only [show ∀ c : pRegularConjClasses p G, single c.val.out (μ c) =
      μ c • single c.val.out 1 from fun c ↦ by rw [smul_single', mul_one], map_smul]
    exact hμ
  obtain ⟨n, hn⟩ := (mem_pPowerCommutatorSubmodule p k).1 hy
  -- Raise to a power `p ^ N`, `N ≥ n`, fixing every `p`-regular element.
  obtain ⟨N, hnN, hfix⟩ := exists_le_forall_pow_char_pow_eq_self p (G := G) n
  have hz : ∑ c : pRegularConjClasses p G, single c.val.out (μ c ^ p ^ N) ∈
      commutatorSubmodule k (MonoidAlgebra k G) := by
    have h := sum_pow_char_pow_sub_mem_commutatorSubmodule p k univ
      (fun c : pRegularConjClasses p G ↦ single c.val.out (μ c)) N
    simp only [single_pow, fun c : pRegularConjClasses p G ↦ hfix c.val.out (by
      simpa [hmk] using (mk_mem_pRegularConjClasses_iff p).1 (by rw [hmk]; exact c.prop))] at h
    simpa using sub_mem (pow_char_pow_mem_commutatorSubmodule_of_le p k hnN hn) h
  -- The coefficient sum over the class of `c₀` picks out `μ c₀ ^ p ^ N`.
  have h0 := commutatorSubmodule_le_ker_classCoeff k c₀.val hz
  rw [LinearMap.mem_ker, map_sum] at h0
  simp only [classCoeff_single, hmk, Subtype.coe_inj, Finset.sum_ite_eq', Finset.mem_univ,
    ite_true] at h0
  exact pow_eq_zero_iff (pow_ne_zero N hp.out.ne_zero) |>.1 h0

include hp in
/-- **The `p`-power commutator subspace of a group algebra counts the `p`-regular classes**
(Webb, proof of Theorem 9.3.6): over a field `k` of characteristic `p`, the quotient of `k[G]` by
its `p`-power commutator subspace has dimension the number of `p`-regular conjugacy classes of the
finite group `G`. -/
theorem finrank_quotient_pPowerCommutatorSubmodule_monoidAlgebra [Finite G] :
    finrank k (MonoidAlgebra k G ⧸ pPowerCommutatorSubmodule p k (MonoidAlgebra k G)) =
      Nat.card (pRegularConjClasses p G) := by
  have : Finite (ConjClasses G) := Quotient.finite _
  have := Fintype.ofFinite (pRegularConjClasses p G)
  rw [finrank_eq_card_basis (Basis.mk (linearIndependent_mkQ_single_out p k)
    (span_range_mkQ_single_out p k)), Nat.card_eq_fintype_card]

include hp in
/-- **The number of matrix factors of a split group algebra** (Webb, Theorem 9.3.6 and
Proposition 9.3.3): if `k` is a field of characteristic `p` and
`k[G] / rad k[G] ≅ ∏_{i ∈ ι} M_{n_i}(k)` with every `n_i` nonempty, then `|ι|` is the number of
`p`-regular conjugacy classes of `G`. -/
theorem card_eq_card_pRegularConjClasses_of_algEquiv_pi_matrix [Finite G] {ι : Type*} [Fintype ι]
    {n : ι → Type*} [∀ i, Fintype (n i)] [∀ i, DecidableEq (n i)] [∀ i, Nonempty (n i)]
    (e : (MonoidAlgebra k G ⧸ Ring.jacobson (MonoidAlgebra k G)) ≃ₐ[k]
      Π i, Matrix (n i) (n i) k) :
    Fintype.card ι = Nat.card (pRegularConjClasses p G) := by
  rw [← finrank_quotient_pPowerCommutatorSubmodule_of_algEquiv_pi_matrix p k e,
    finrank_quotient_pPowerCommutatorSubmodule_monoidAlgebra]

include hp in
/-- Over an algebraically closed field `k` of characteristic `p`, `k[G] / rad k[G]` is a product
of as many matrix algebras over `k` as the finite group `G` has `p`-regular conjugacy classes. -/
theorem exists_algEquiv_pi_matrix_card_eq_card_pRegularConjClasses [IsAlgClosed k] [Finite G] :
    ∃ d : Fin (Nat.card (pRegularConjClasses p G)) → ℕ, (∀ i, NeZero (d i)) ∧
      Nonempty ((MonoidAlgebra k G ⧸ Ring.jacobson (MonoidAlgebra k G)) ≃ₐ[k]
        Π i, Matrix (Fin (d i)) (Fin (d i)) k) := by
  have := IsArtinianRing.of_finite k (MonoidAlgebra k G)
  have : FiniteDimensional k (MonoidAlgebra k G ⧸ Ring.jacobson (MonoidAlgebra k G)) :=
    Module.Finite.of_surjective (Ideal.Quotient.mkₐ k _).toLinearMap
      (Ideal.Quotient.mkₐ_surjective k _)
  obtain ⟨m, d, hd, ⟨e⟩⟩ := IsSemisimpleRing.exists_algEquiv_pi_matrix_of_isAlgClosed k
    (MonoidAlgebra k G ⧸ Ring.jacobson (MonoidAlgebra k G))
  have hm : m = Nat.card (pRegularConjClasses p G) := by
    rw [← card_eq_card_pRegularConjClasses_of_algEquiv_pi_matrix p k e, Fintype.card_fin]
  subst hm
  exact ⟨d, hd, ⟨e⟩⟩

end TauCeti

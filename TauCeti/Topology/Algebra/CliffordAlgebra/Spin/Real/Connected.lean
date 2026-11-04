/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.CliffordAlgebra.Spin.Real.Basic
public import TauCeti.Topology.Algebra.CliffordAlgebra.Spin.Basic
import TauCeti.LinearAlgebra.CliffordAlgebra.Spin.Basic
import TauCeti.LinearAlgebra.CliffordAlgebra.Spin.Kernel
import TauCeti.LinearAlgebra.CliffordAlgebra.Spin.Real.Factorization
import TauCeti.LinearAlgebra.QuadraticForm.Real
import TauCeti.Topology.Algebra.QuadraticForm.LevelSet

/-!
# Path-connectedness of real Spin groups of indefinite signature

The real Spin group `Spin(p, q)` is path-connected as soon as `2 ≤ p` or `2 ≤ q`, in particular
whenever `p + q ≥ 3`. The two remaining nonzero signatures are genuine exceptions: `Spin(1, 0)`
and `Spin(0, 1)` are `{1, -1}`, and `Spin(1, 1)` has two components.

The argument is more generally about the Spin group of a quadratic form `Q` on a real vector
space. Every Spin element is a product of an even number of vectors of norm `±1` whose norms
multiply to `1` (`CliffordAlgebra.exists_normalized_list_of_spinGroup`). Moving a single factor
inside its level set `Q = ±1` keeps the product in the Spin group
(`CliffordAlgebra.joined_of_coe_eq_prod_mul_ι_mul_prod`), and inside a level set every vector is
joined to `a` or to `-a` for any other vector `a` of the same norm
(`QuadraticMap.joinedIn_setOf_apply_eq_or_joinedIn_neg`). This removes two factors at a time,
up to the sign `±1`:

* if the first two factors `a, b` have the same norm, move `b` to `±a`, so that
  `ι a * ι b ↦ ±Q a = ±1`;
* otherwise the third factor `c` has the norm of `a` or of `b`. Moving it to `±b` turns
  `ι a * ι b * ι c` into `±Q b • ι a`, and moving it to `±a` turns it into `±ι a * ι b * ι a`,
  which is again a single vector of norm `Q b`.

The level sets themselves need not be path-connected; for `p = 1` the level set `Q = 1` is a
hyperboloid of two sheets exchanged by `v ↦ -v`. The remaining sign is absorbed by the hypothesis
that the Spin group joins `1` to `-1`: given orthogonal vectors `e` and `f` of the same norm
`±1`, moving `e` to `-e` inside its level set joins `ι e * ι e = Q e` to `-Q e`. Such a pair is
obtained by rescaling any two orthogonal vectors whose norms are nonzero of the same sign; in
signature `(p, q)` these exist exactly when `2 ≤ p` or `2 ≤ q`.

## Main results

* `CliffordAlgebra.pathConnectedSpace_spinGroup_of_isOrtho`: the Spin group of a real quadratic
  form is path-connected when the form has two orthogonal vectors whose norms are nonzero of the
  same sign.
* `CliffordAlgebra.pathConnectedSpace_realCliffordSpinGroup`: `Spin(p, q)` is path-connected when
  `2 ≤ p` or `2 ≤ q`.

## References

* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry* (1989), Chapter I, §2 and §5.
-/

public section

namespace CliffordAlgebra

open TauCeti

variable {V : Type*} [AddCommGroup V] [Module ℝ V] {Q : QuadraticForm ℝ V}

/-- The first move: inside its level set, `b` is joined to some `a' = ±a`, and then
`ι a * ι a' = ±1`. -/
private theorem exists_joinedIn_ι_mul_ι_eq_algebraMap [TopologicalSpace V] [ContinuousAdd V]
    [ContinuousSMul ℝ V] {a b : V} (ha : Q a = 1 ∨ Q a = -1) (hab : Q b = Q a) :
    ∃ a' : V, JoinedIn {v | Q v = Q b} b a' ∧
      ∃ s : ℝ, (s = 1 ∨ s = -1) ∧ ι Q a * ι Q a' = algebraMap ℝ _ s := by
  have ha0 : Q a ≠ 0 := by rcases ha with h | h <;> rw [h] <;> norm_num
  rw [hab]
  rcases QuadraticMap.joinedIn_setOf_apply_eq_or_joinedIn_neg Q hab ha0 with h | h
  · exact ⟨a, h, Q a, ha, ι_sq_scalar Q a⟩
  · refine ⟨-a, h, -Q a, ?_, by rw [map_neg, mul_neg, ι_sq_scalar, map_neg]⟩
    rcases ha with h | h <;> simp [h]

/-- The second move: inside its level set, `c` is joined to some `a' = ±a`, and then
`ι a * ι b * ι a' = ±ι w` for a vector `w` of the same norm as `b`. -/
private theorem exists_joinedIn_ι_mul_ι_mul_ι_eq_smul_ι [TopologicalSpace V] [ContinuousAdd V]
    [ContinuousSMul ℝ V] {a b c : V} (ha : Q a = 1 ∨ Q a = -1) (hca : Q c = Q a) :
    ∃ a' : V, JoinedIn {v | Q v = Q c} c a' ∧ ∃ s : ℝ, (s = 1 ∨ s = -1) ∧
      ∃ w : V, Q w = Q b ∧ ι Q a * ι Q b * ι Q a' = algebraMap ℝ _ s * ι Q w := by
  have ha0 : Q a ≠ 0 := by rcases ha with h | h <;> rw [h] <;> norm_num
  have hw : Q (QuadraticMap.polar Q a b • a - Q a • b) = Q b := by
    rw [sub_eq_add_neg, QuadraticMap.map_add Q]
    simp only [QuadraticMap.map_neg, QuadraticMap.polar_neg_right, QuadraticMap.polar_smul_left,
      QuadraticMap.polar_smul_right, QuadraticMap.map_smul, smul_eq_mul]
    linear_combination Q b * mul_self_eq_one_iff.mpr ha
  rw [hca]
  rcases QuadraticMap.joinedIn_setOf_apply_eq_or_joinedIn_neg Q hca ha0 with h | h
  · exact ⟨a, h, 1, .inl rfl, _, hw, by rw [ι_mul_ι_mul_ι, map_one, one_mul]⟩
  · exact ⟨-a, h, -1, .inr rfl, _, hw, by
      rw [map_neg, mul_neg, ι_mul_ι_mul_ι, map_neg, map_one, neg_one_mul]⟩

variable [ContinuousMul (CliffordAlgebra Q)]

/-- If `-1` lies in the identity path component of the Spin group, then that component contains
`±z` along with every element `z`. -/
private theorem exists_mem_pathComponentOne_coe_eq_algebraMap_mul (hQ : Q ≠ 0)
    (hneg : spinGroup.negOne Q hQ ∈ Subgroup.pathComponentOne (spinGroup Q)) {s : ℝ}
    (hs : s = 1 ∨ s = -1) {z : spinGroup Q} (hz : z ∈ Subgroup.pathComponentOne (spinGroup Q)) :
    ∃ y ∈ Subgroup.pathComponentOne (spinGroup Q),
      (y : CliffordAlgebra Q) = algebraMap ℝ _ s * z := by
  rcases hs with rfl | rfl
  · exact ⟨z, hz, by rw [map_one, one_mul]⟩
  · exact ⟨spinGroup.negOne Q hQ * z, mul_mem hneg hz, by
      rw [Submonoid.coe_mul, spinGroup.coe_negOne, map_neg, map_one]⟩

variable [TopologicalSpace V] [IsModuleTopology ℝ V]

/-- **The peeling induction.** If `-1` is in the identity path component of the Spin group, then
so is every product of an even number `n` of vectors of norm `±1` whose norms multiply to one. Each
step moves one factor inside its level set to reach `±` a product of `n - 2` such vectors. -/
private theorem mem_pathComponentOne_of_coe_eq_prod_map_ι (hQ : Q ≠ 0)
    (hneg : spinGroup.negOne Q hQ ∈ Subgroup.pathComponentOne (spinGroup Q)) (n : ℕ) :
    ∀ l : List V, l.length = n → (∀ v ∈ l, Q v = 1 ∨ Q v = -1) → Even n →
      (l.map Q).prod = 1 → ∀ x : spinGroup Q, (x : CliffordAlgebra Q) = (l.map (ι Q)).prod →
        x ∈ Subgroup.pathComponentOne (spinGroup Q) := by
  let _ := IsModuleTopology.toContinuousAdd ℝ V
  set H := Subgroup.pathComponentOne (spinGroup Q)
  have hjoin {x y : spinGroup Q} (h : Joined x y) (hy : y ∈ H) : x ∈ H :=
    mem_pathComponent_iff.mpr ((mem_pathComponent_iff.mp hy).trans h.symm)
  -- Strong induction on the length: a list of length `0` gives `1`, length `1` is odd, and for
  -- `a :: b :: t` one move inside a level set reaches `±` a product of a list of length `n - 2`.
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro l hn hl he hQl x hx
  -- The product of a list of length `n - 2` lies in `H`, by induction.
  have hshort (t : List V) (ht : t.length + 2 = n) (htl : ∀ v ∈ t, Q v = 1 ∨ Q v = -1)
      (htQ : (t.map Q).prod = 1) : ∃ z ∈ H, (z : CliffordAlgebra Q) = (t.map (ι Q)).prod := by
    have hte : Even t.length := by rw [← ht] at he; simpa [parity_simps] using he
    exact ⟨⟨_, prod_map_ι_mem_spinGroup hte htQ⟩,
      ih t.length (by omega) t rfl htl hte htQ _ rfl, rfl⟩
  rcases l with _ | ⟨a, _ | ⟨b, t⟩⟩
  · rw [show x = 1 from Subtype.ext (by simpa using hx)]
    exact one_mem H
  · simp only [List.length_cons, List.length_nil, zero_add] at hn
    exact absurd (hn ▸ he) (by decide)
  simp only [List.length_cons] at hn
  have ha := hl a (by simp)
  have hb := hl b (by simp)
  have ht (v : V) (hv : v ∈ t) := hl v (by simp [hv])
  have ha2 := mul_self_eq_one_iff.mpr ha
  have hb2 := mul_self_eq_one_iff.mpr hb
  simp only [List.map_cons, List.prod_cons] at hQl hx
  by_cases hab : Q b = Q a
  · -- Move `b` to `±a`; the first two factors become `±1`.
    obtain ⟨a', hpath, s, hs, has⟩ := exists_joinedIn_ι_mul_ι_eq_algebraMap ha hab
    obtain ⟨z, hz, hzc⟩ := hshort t (by omega) ht (by
      rw [hab] at hQl
      linear_combination hQl - (t.map Q).prod * ha2)
    obtain ⟨y, hy, hyc⟩ := exists_mem_pathComponentOne_coe_eq_algebraMap_mul hQ hneg hs hz
    refine hjoin (joined_of_coe_eq_prod_mul_ι_mul_prod (l₁ := [a]) (l₂ := t) ?_ ?_ hpath ?_ ?_) hy
    · convert he using 1
      simp only [List.length_cons, List.length_nil]
      omega
    · simpa [mul_assoc] using hQl
    · simp [hx, mul_assoc]
    · simp [hyc, hzc, ← has]
  -- The first two factors have opposite norms, so there is a third factor `c`.
  have hba : Q b = -Q a := by
    have h : (Q b - Q a) * (Q b + Q a) = 0 := by linear_combination hb2 - ha2
    rcases mul_eq_zero.mp h with h | h
    · exact absurd (sub_eq_zero.mp h) hab
    · linear_combination h
  rcases t with _ | ⟨c, t⟩
  · simp only [List.map_nil, List.prod_nil, mul_one, hba] at hQl
    nlinarith
  have hc := ht c (by simp)
  have ht' (v : V) (hv : v ∈ t) := ht v (by simp [hv])
  simp only [List.length_cons] at hn
  simp only [List.map_cons, List.prod_cons] at hQl hx
  have hlen : Even ([a, b].length + t.length + 1) := by
    convert he using 1
    simp only [List.length_cons, List.length_nil]
    omega
  have hQ₃ : ([a, b].map Q).prod * Q c * (t.map Q).prod = 1 := by simpa [mul_assoc] using hQl
  have hx₃ : (x : CliffordAlgebra Q) =
      ([a, b].map (ι Q)).prod * ι Q c * (t.map (ι Q)).prod := by
    simp [hx, mul_assoc]
  by_cases hca : Q c = Q a
  · -- Move `c` to `±a`; the first three factors become `±` a single vector `w` of norm `Q b`.
    obtain ⟨a', hpath, s, hs, w, hw, haw⟩ :=
      exists_joinedIn_ι_mul_ι_mul_ι_eq_smul_ι (b := b) ha hca
    obtain ⟨z, hz, hzc⟩ := hshort (w :: t) (by simp only [List.length_cons]; omega)
      (fun v hv ↦ by
        rcases List.mem_cons.mp hv with rfl | hv
        exacts [hw ▸ hb, ht' v hv])
      (by
        rw [hca] at hQl
        simp only [List.map_cons, List.prod_cons, hw]
        linear_combination hQl - Q b * (t.map Q).prod * ha2)
    obtain ⟨y, hy, hyc⟩ := exists_mem_pathComponentOne_coe_eq_algebraMap_mul hQ hneg hs hz
    refine hjoin (joined_of_coe_eq_prod_mul_ι_mul_prod hlen hQ₃ hpath hx₃ ?_) hy
    simp only [hyc, hzc, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
    rw [haw, mul_assoc]
  · -- Otherwise `Q c = Q b`: move `c` to `±b`; the factors `b, c` become `±1`.
    have hcb : Q c = Q b := by
      have h : (Q c - Q b) * (Q c - Q a) = 0 := by
        rw [hba]
        linear_combination mul_self_eq_one_iff.mpr hc - ha2
      rcases mul_eq_zero.mp h with h | h
      · exact sub_eq_zero.mp h
      · exact absurd (sub_eq_zero.mp h) hca
    obtain ⟨b', hpath, s, hs, hbs⟩ := exists_joinedIn_ι_mul_ι_eq_algebraMap hb hcb
    obtain ⟨z, hz, hzc⟩ := hshort (a :: t) (by simp only [List.length_cons]; omega)
      (fun v hv ↦ by
        rcases List.mem_cons.mp hv with rfl | hv
        exacts [ha, ht' v hv])
      (by
        rw [hcb] at hQl
        simp only [List.map_cons, List.prod_cons]
        linear_combination hQl - Q a * (t.map Q).prod * hb2)
    obtain ⟨y, hy, hyc⟩ := exists_mem_pathComponentOne_coe_eq_algebraMap_mul hQ hneg hs hz
    refine hjoin (joined_of_coe_eq_prod_mul_ι_mul_prod hlen hQ₃ hpath hx₃ ?_) hy
    simp only [hyc, hzc, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
    rw [mul_assoc (ι Q a), hbs, ← Algebra.commutes, mul_assoc]

/-- **Real Spin groups with a definite plane are path-connected.** The Spin group of a quadratic
form on a real vector space is path-connected when the form has two orthogonal vectors whose norms
are nonzero of the same sign, that is, when it is definite on some plane. -/
theorem pathConnectedSpace_spinGroup_of_isOrtho {e f : V} (hef : Q.IsOrtho e f)
    (h : 0 < Q e * Q f) : PathConnectedSpace (spinGroup Q) := by
  let _ := IsModuleTopology.toContinuousAdd ℝ V
  obtain ⟨e, f, he, hf, hef⟩ := QuadraticMap.exists_isOrtho_of_mul_pos hef h
  have he0 : Q e ≠ 0 := by rcases he with h | h <;> rw [h] <;> norm_num
  have hQ : Q ≠ 0 := fun h ↦ he0 (by simp [h])
  -- `ι e * ι e = Q e` is joined to `ι e * ι (-e) = -Q e`, so `-1` is joined to `1`.
  have hj (x y : spinGroup Q) (hx : (x : CliffordAlgebra Q) = algebraMap ℝ _ (Q e))
      (hy : (y : CliffordAlgebra Q) = -algebraMap ℝ _ (Q e)) : Joined x y :=
    joined_of_coe_eq_prod_mul_ι_mul_prod (l₁ := [e]) (l₂ := []) (by simp)
      (by simpa using mul_self_eq_one_iff.mpr he)
      (QuadraticMap.joinedIn_setOf_apply_eq_neg_of_isOrtho Q hf he0 hef)
      (by simp [hx]) (by simp [hy])
  have hneg : spinGroup.negOne Q hQ ∈ Subgroup.pathComponentOne (spinGroup Q) := by
    rcases he with h | h
    · exact hj 1 _ (by simp [h]) (by simp [h])
    · exact (hj _ 1 (by simp [h]) (by simp [h])).symm
  refine pathConnectedSpace_iff_eq.mpr ⟨1, Set.eq_univ_of_forall fun x ↦ ?_⟩
  obtain ⟨l, hl, hlen, hQl, hx⟩ := exists_normalized_list_of_spinGroup x
  exact mem_pathComponentOne_of_coe_eq_prod_map_ι hQ hneg l.length l rfl hl hlen hQl x hx

/-- **`Spin(p, q)` is path-connected** as soon as `2 ≤ p` or `2 ≤ q`, in particular whenever
`p + q ≥ 3`. -/
theorem pathConnectedSpace_realCliffordSpinGroup {p q : ℕ} (h : 2 ≤ p ∨ 2 ≤ q) :
    PathConnectedSpace (realCliffordSpinGroup p q) := by
  rcases h with h | h
  · refine pathConnectedSpace_spinGroup_of_isOrtho
      (isOrtho_realCliffordForm_single (i := ⟨0, by omega⟩) (j := ⟨1, by omega⟩) (by simp) 1 1) ?_
    simp [show 0 < p by omega, show 1 < p by omega]
  · refine pathConnectedSpace_spinGroup_of_isOrtho
      (isOrtho_realCliffordForm_single (i := ⟨p, by omega⟩) (j := ⟨p + 1, by omega⟩) (by simp) 1 1)
      ?_
    simp

end CliffordAlgebra

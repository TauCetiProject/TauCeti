/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.Fixed
public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.FieldTheory.SeparablyGenerated
import Mathlib.Algebra.BigOperators.Field

/-!
# Fixed fields and separable generation

Let `E` be a field of exponential characteristic `p` and `M` a monoid acting on `E` by ring
automorphisms, with fixed field `K`. Rosenlicht's lemma says that the `p`-th powers of
`K`-linearly independent elements of `E` are again `K`-linearly independent. The conclusion is
MacLane's criterion for `E / K` to be separable, and for a finitely generated extension it produces
a separating transcendence basis: an extension `E / k` with finitely many generators, on which the
`k`-automorphisms of `E` fix nothing outside `k`, is separably generated.

Over a base field `k`, the hypothesis that the `k`-automorphisms fix only `k` cannot be dropped:
`𝔽_p(t ^ (1 / p))` over `𝔽_p(t)` has no nontrivial automorphisms, and `t ^ (1 / p)`, which is
linearly independent from `1` over `𝔽_p(t)`, has `p`-th power `t`, which is not. Finite generation
cannot be dropped from the separable generation statement either: for an algebraic closure `K` of
`𝔽_p`, the translations `t ↦ t + a`, `a ∈ K`, of the perfect closure of `K(t)` fix only `K`, but
this perfect closure has no separating transcendence basis over `K`.

## Main results

* `FixedPoints.linearIndependent_pow_of_linearIndependent`: **Rosenlicht's lemma**, the `p`-th
  powers of linearly independent elements over the fixed field are linearly independent over it.
* `TauCeti.linearIndependent_pow_of_fixedField_eq_bot`: the same over `k`, when the fixed field of
  all `k`-automorphisms of `E` is `k`.
* `TauCeti.exists_isTranscendenceBasis_and_isSeparable_of_fixedField_eq_bot`: a finitely generated
  extension whose `k`-automorphisms have fixed field `k` has a finite separating transcendence
  basis.

## References

* M. Rosenlicht, *Automorphisms of function fields*, Trans. Amer. Math. Soc. 79 (1955), 1–11,
  §3, Lemma and Corollary, pp. 4–5.
* S. MacLane, *Modular fields. I. Separating transcendence bases*, Duke Math. J. 5 (1939),
  372–393.
-/

public section

open Finset

namespace FixedPoints

variable {E : Type*} [Field E] (M : Type*) [Monoid M] [MulSemiringAction M E] (p : ℕ)
  [ExpChar E p]

/-- If elements `c i` of the fixed field are linearly independent over its `p`-th powers, they are
linearly independent over the `p`-th powers of `E`. The `m` with `∑ m i ^ p * c i = 0` form an
`E`-subspace stable under `M`, so an element of minimal support, normalized to have a coordinate
`1`, is fixed by `M`. -/
private theorem eq_zero_of_sum_pow_mul_eq_zero {ι : Type*} (s : Finset ι)
    (c : ι → subfield M E)
    (hc : ∀ a : ι → subfield M E, ∑ i ∈ s, a i ^ p * c i = 0 → ∀ i ∈ s, a i = 0)
    (m : ι → E) (hm : ∑ i ∈ s, m i ^ p * c i = 0) : ∀ i ∈ s, m i = 0 := by
  classical
  induction h : #{i ∈ s | m i ≠ 0} using Nat.strong_induction_on generalizing m with
  | _ n ih =>
  by_contra! hne
  obtain ⟨j, hj, hmj⟩ := hne
  -- Normalize `m` so that its `j`-th coordinate is `1`.
  set m' : ι → E := fun i ↦ (m j)⁻¹ * m i with hm'_def
  have hm'j : m' j = 1 := inv_mul_cancel₀ hmj
  have hm' : ∑ i ∈ s, m' i ^ p * c i = 0 := by
    simp only [m', mul_pow, mul_assoc, ← Finset.mul_sum, hm, mul_zero]
  clear_value m'
  -- Each `σ • m' - m'` is a solution with smaller support, hence vanishes.
  have hfix : ∀ i ∈ s, ∀ σ : M, σ • m' i = m' i := by
    intro i hi σ
    set d : ι → E := fun i ↦ σ • m' i - m' i
    have hd : ∑ i ∈ s, d i ^ p * c i = 0 := by
      have hσ : ∑ i ∈ s, (σ • m' i) ^ p * (c i : E) = σ • ∑ i ∈ s, m' i ^ p * (c i : E) := by
        rw [Finset.smul_sum]
        refine Finset.sum_congr rfl fun i _ ↦ ?_
        rw [smul_mul', smul_pow', (c i).prop σ]
      simp only [d, sub_pow_expChar, sub_mul, Finset.sum_sub_distrib, hσ, hm', smul_zero,
        sub_zero]
    have hsub : {i ∈ s | d i ≠ 0} ⊆ {i ∈ s | m i ≠ 0} := by
      intro i
      simp only [Finset.mem_filter]
      refine fun ⟨his, hdi⟩ ↦ ⟨his, fun hmi ↦ hdi ?_⟩
      simp [d, hm'_def, hmi]
    have hlt : #{i ∈ s | d i ≠ 0} < n := by
      rw [← h]
      refine Finset.card_lt_card ((Finset.ssubset_iff_of_subset hsub).2 ⟨j, ?_, ?_⟩)
      · simpa using ⟨hj, hmj⟩
      · simp [d, hm'j]
    exact sub_eq_zero.mp (ih _ hlt d hd rfl i hi)
  -- So `m'` has its coordinates in the fixed field, contradicting the hypothesis on `c`.
  let a : ι → subfield M E := fun i ↦ if hi : ∀ σ : M, σ • m' i = m' i then ⟨m' i, hi⟩ else 0
  have ha : ∀ i ∈ s, (a i : E) = m' i := fun i hi ↦ by simp [a, hfix i hi]
  have hsum : ∑ i ∈ s, a i ^ p * c i = 0 := by
    apply Subtype.val_injective
    rw [AddSubmonoidClass.coe_finsetSum, ZeroMemClass.coe_zero, ← hm']
    refine Finset.sum_congr rfl fun i hi ↦ ?_
    rw [MulMemClass.coe_mul, SubmonoidClass.coe_pow, ha i hi]
  have := ha j hj
  rw [hc a hsum j hj, hm'j] at this
  exact zero_ne_one this

/-- The finite case of `FixedPoints.linearIndependent_pow_of_linearIndependent`, by induction on
the index set. -/
private theorem eq_zero_of_sum_smul_pow_eq_zero {ι : Type*} (s : Finset ι) (v : ι → E)
    (hv : LinearIndepOn (subfield M E) v s) (g : ι → subfield M E)
    (hg : ∑ i ∈ s, g i • v i ^ p = 0) : ∀ i ∈ s, g i = 0 := by
  classical
  induction s using Finset.strongInduction generalizing v g with
  | H s ih =>
  by_cases hc : ∀ a : ι → subfield M E, ∑ i ∈ s, a i ^ p * g i = 0 → ∀ i ∈ s, a i = 0
  · -- The `g i` are independent over the `p`-th powers of the fixed field, hence over those of
    -- `E`, so every `v i` vanishes, which independence of the `v i` rules out.
    have hv0 := eq_zero_of_sum_pow_mul_eq_zero M p s g hc v (by
      simpa only [Algebra.smul_def, FixedPoints.coe_algebraMap, Subfield.subtype_apply, mul_comm]
        using hg)
    exact fun i hi ↦ absurd (hv0 i hi) (hv.ne_zero hi)
  · -- A relation `∑ a i ^ p * g i = 0` with `a j = 1` eliminates the `j`-th term: replacing `v i`
    -- by `v i - a i • v j` gives a shorter relation of the same shape.
    push Not at hc
    obtain ⟨a₀, ha₀, j, hj, ha₀j⟩ := hc
    set a : ι → subfield M E := fun i ↦ a₀ i / a₀ j
    have ha : ∑ i ∈ s, a i ^ p * g i = 0 := by
      simp only [a, div_pow, div_mul_eq_mul_div, ← Finset.sum_div, ha₀, zero_div]
    have hg_j : g j + ∑ i ∈ s.erase j, a i ^ p * g i = 0 := by
      rwa [← Finset.add_sum_erase s _ hj, show a j = 1 from div_self ha₀j, one_pow, one_mul] at ha
    set w : ι → E := fun i ↦ v i - a i • v j
    have hw : LinearIndepOn (subfield M E) w ↑(s.erase j) := by
      have := (linearIndependent_add_smul_iff (v := fun i : (s : Set ι) ↦ v i) (i := ⟨j, hj⟩)
        (c := fun i ↦ if (i : ι) = j then 0 else -a i) (by simp)).2 hv
      refine (LinearIndepOn.mono (v := fun i ↦ v i + (if i = j then 0 else -a i) • v j) this
        (Finset.coe_subset.2 (Finset.erase_subset j s))).congr fun i hi ↦ ?_
      simp [w, Finset.ne_of_mem_erase hi, sub_eq_add_neg]
    have hgw : ∑ i ∈ s.erase j, g i • w i ^ p = 0 := by
      have hwp : ∀ i, w i ^ p = v i ^ p - a i ^ p • v j ^ p := fun i ↦ by
        rw [sub_pow_expChar, smul_pow]
      simp only [hwp, smul_sub, smul_smul, Finset.sum_sub_distrib, ← Finset.sum_smul]
      rw [← Finset.add_sum_erase s _ hj] at hg
      have : ∑ i ∈ s.erase j, g i * a i ^ p = -g j := by
        rw [eq_neg_iff_add_eq_zero, add_comm, ← hg_j]
        exact congrArg _ (Finset.sum_congr rfl fun i _ ↦ mul_comm _ _)
      rw [this, neg_smul, sub_neg_eq_add, add_comm, hg]
    have hrest := ih (s.erase j) (Finset.erase_ssubset hj) w hw g hgw
    intro i hi
    obtain rfl | hij := eq_or_ne i j
    · rwa [Finset.sum_eq_zero fun i hi ↦ by rw [hrest i hi, mul_zero], add_zero] at hg_j
    · exact hrest i (Finset.mem_erase.2 ⟨hij, hi⟩)

/-- **Rosenlicht's lemma**: if a monoid acts on a field `E` of exponential characteristic `p` by
ring automorphisms, the `p`-th powers of elements of `E` that are linearly independent over the
fixed field are again linearly independent over it. -/
theorem linearIndependent_pow_of_linearIndependent {ι : Type*} {v : ι → E}
    (hv : LinearIndependent (subfield M E) v) :
    LinearIndependent (subfield M E) fun i ↦ v i ^ p := by
  rw [linearIndependent_iff']
  exact fun s g hg ↦ eq_zero_of_sum_smul_pow_eq_zero M p s v (hv.linearIndepOn s) g hg

end FixedPoints

namespace TauCeti

variable {k E : Type*} [Field k] [Field E] [Algebra k E]

/-- **Rosenlicht's lemma over the base field**: if the fixed field of all `k`-automorphisms of `E`
is `k`, the `p`-th powers of `k`-linearly independent elements of `E` are `k`-linearly
independent. -/
theorem linearIndependent_pow_of_fixedField_eq_bot (p : ℕ) [ExpChar E p]
    (h : IntermediateField.fixedField (⊤ : Subgroup (E ≃ₐ[k] E)) = ⊥) {ι : Type*} {v : ι → E}
    (hv : LinearIndependent k v) : LinearIndependent k fun i ↦ v i ^ p := by
  -- Identify `k` with the fixed points of `E ≃ₐ[k] E`.
  let i : k → FixedPoints.subfield (E ≃ₐ[k] E) E := fun x ↦ ⟨algebraMap k E x, fun σ ↦ σ.commutes x⟩
  have hi : Function.Surjective i := fun y ↦ by
    have hy : (y : E) ∈ IntermediateField.fixedField (⊤ : Subgroup (E ≃ₐ[k] E)) :=
      (IntermediateField.mem_fixedField_iff _ _).2 fun σ _ ↦ y.prop σ
    rw [h, IntermediateField.mem_bot] at hy
    obtain ⟨x, hx⟩ := hy
    exact ⟨x, Subtype.ext hx⟩
  -- The scalar actions of `k` and of the fixed points on `E` agree along `i`.
  have hc : ∀ (r : k) (m : E), AddMonoidHom.id E (r • m) = i r • AddMonoidHom.id E m :=
    fun r m ↦ by
      simp only [AddMonoidHom.id_apply, Algebra.smul_def, FixedPoints.coe_algebraMap,
        Subfield.subtype_apply, i]
  have hj : ∀ m : E, AddMonoidHom.id E m = 0 → m = 0 := fun m hm ↦ by
    simpa only [AddMonoidHom.id_apply] using hm
  -- Transfer independence to the fixed points, apply Rosenlicht's lemma there, and transfer back.
  have hv₁ : LinearIndependent (FixedPoints.subfield (E ≃ₐ[k] E) E) v := by
    simpa only [AddMonoidHom.coe_id, Function.id_comp] using
      hv.map_of_surjective_injective i (AddMonoidHom.id E) hi hj hc
  have hv₂ := FixedPoints.linearIndependent_pow_of_linearIndependent _ p hv₁
  simpa only [AddMonoidHom.coe_id, Function.id_comp] using
    hv₂.map_of_injective_injective i (AddMonoidHom.id E)
      (fun r hr ↦ by simpa [i] using congrArg Subtype.val hr) hj fun r m ↦ (hc r m).symm

/-- **A finitely generated extension whose automorphisms fix only the base field is separably
generated** (Rosenlicht): if `E / k` is finitely generated and the fixed field of all
`k`-automorphisms of `E` is `k`, then `E` has a finite transcendence basis `s` over `k` with `E`
separable over `k(s)`. -/
theorem exists_isTranscendenceBasis_and_isSeparable_of_fixedField_eq_bot
    [Algebra.EssFiniteType k E]
    (h : IntermediateField.fixedField (⊤ : Subgroup (E ≃ₐ[k] E)) = ⊥) :
    ∃ s : Finset E, IsTranscendenceBasis k ((↑) : s → E) ∧
      Algebra.IsSeparable (IntermediateField.adjoin k (s : Set E)) E := by
  obtain _ | ⟨p, hp, hpk⟩ := CharP.exists' k
  · exact exists_isTranscendenceBasis_and_isSeparable_of_perfectField k E
  have : CharP E p := .of_ringHom_of_ne_zero (algebraMap k E) p hp.out.ne_zero
  have : ExpChar E p := .prime hp.out
  exact exists_isTranscendenceBasis_and_isSeparable_of_linearIndepOn_pow_of_essFiniteType p hp.out
    fun _ hs ↦ linearIndependent_pow_of_fixedField_eq_bot p h hs

end TauCeti

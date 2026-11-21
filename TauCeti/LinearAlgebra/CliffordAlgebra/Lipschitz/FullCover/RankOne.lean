/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.CliffordAlgebra.Lipschitz.FullCover.Basic
import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalGroup.LowRank

/-!
# The normalized full Clifford cover in rank one

Over a field in which `-1` is not a square, the kernel of the full-cover action of a nondegenerate
quadratic space of positive dimension is `{±1}`, a group of order two
(`CliffordAlgebra.card_ker_cliffordFullCoverToOrthogonal`). When moreover every element is a square
up to sign, as over `ℝ`, the full cover of a nondegenerate quadratic line is therefore an extension
of `O(Q) = {±1}` by `{±1}`, a group of order four. It is cyclic exactly when some vector has norm
`-1`: then that vector has order four, whereas if some vector has norm `1`, it gives together with
`1` and `-1` three solutions of `x ^ 2 = 1`, which a cyclic group of order four cannot have.

## Main results

* `CliffordAlgebra.card_cliffordFullCover_of_finrank_eq_one` and
  `CliffordAlgebra.isCyclic_cliffordFullCover_iff_of_finrank_eq_one`: when `-1` is not a square
  but every element is a square up to sign, the full cover of a nondegenerate line has order four,
  and it is cyclic exactly when some vector has norm `-1`
  (`CliffordAlgebra.isCyclic_cliffordFullCover_of_finrank_eq_one`), not when some vector has
  norm `1` (`CliffordAlgebra.not_isCyclic_cliffordFullCover_of_finrank_eq_one`).

## References

* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry* (1989), Chapter I, §2.
-/

public section

noncomputable section

namespace CliffordAlgebra

open TauCeti

universe u v

variable {K : Type u} {V : Type v} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  [Invertible (2 : K)] {Q : QuadraticForm K V}

/-! ### Rank one -/

section RankOne

variable (hQ : Q.Nondegenerate) (hV : Module.finrank K V = 1)
include hQ hV

/-- **The full cover in rank one has order four.** Over a field in which `-1` is not a square but
every element is a square up to sign, the full cover of a nondegenerate line is an extension of
`O(Q) = {±1}` by the kernel `{±1}`. -/
theorem card_cliffordFullCover_of_finrank_eq_one (h : ¬IsSquare (-1 : K))
    (hK : ∀ a : K, IsSquare a ∨ IsSquare (-a)) :
    Nat.card (cliffordFullCover Q) = 4 := by
  have : Nontrivial V := Module.nontrivial_of_finrank_eq_succ hV
  rw [← Subgroup.card_ker_mul_card_range (cliffordFullCoverToOrthogonal Q),
    card_ker_cliffordFullCoverToOrthogonal hQ h,
    MonoidHom.range_eq_top.2 (cliffordFullCoverToOrthogonal_surjective hQ hK), Subgroup.card_top,
    QuadraticMap.card_orthogonalGroup_of_finrank_eq_one hQ.ne_zero hV]

omit hQ hV [FiniteDimensional K V] in
private theorem coe_cliffordFullCoverOfNorm_pow (v : V) [Invertible (Q v)]
    (hv : Q v = 1 ∨ Q v = -1) (n : ℕ) :
    ((((cliffordFullCoverOfNorm v hv ^ n : cliffordFullCover Q) : lipschitzGroup Q) :
      (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) = ι Q v ^ n := by
  simp [coe_unitι]

omit hQ [FiniteDimensional K V] in
/-- In rank one the element of a vector of norm `±1` acts on the line by `-1`. -/
private theorem cliffordFullCoverToOrthogonal_cliffordFullCoverOfNorm (v : V) [Invertible (Q v)]
    (hv : Q v = 1 ∨ Q v = -1) :
    cliffordFullCoverToOrthogonal Q (cliffordFullCoverOfNorm v hv) = Q.negOrthogonal := by
  rw [cliffordFullCoverToOrthogonal_apply, coe_cliffordFullCoverOfNorm, lipschitzToOrthogonal_unitι,
    QuadraticMap.reflectionOrthogonal_eq_negOrthogonal_of_finrank_eq_one Q v hV]

omit hQ [FiniteDimensional K V] in
/-- In rank one the element of a vector of norm `±1` does not act trivially. -/
private theorem cliffordFullCoverOfNorm_notMem_ker (v : V) [Invertible (Q v)]
    (hv : Q v = 1 ∨ Q v = -1) :
    cliffordFullCoverOfNorm v hv ∉ (cliffordFullCoverToOrthogonal Q).ker := by
  have : Nontrivial V := Module.nontrivial_of_finrank_eq_succ hV
  rw [MonoidHom.mem_ker, cliffordFullCoverToOrthogonal_cliffordFullCoverOfNorm hV v hv]
  exact Q.negOrthogonal_ne_one

/-- **A cyclic full cover in rank one.** Over a field in which `-1` is not a square but every
element is a square up to sign, if some vector `e` of a nondegenerate line has norm `-1`, then
`e ^ 2 = -1`, so `e` has order four and generates the full cover. -/
theorem isCyclic_cliffordFullCover_of_finrank_eq_one (h : ¬IsSquare (-1 : K))
    (hK : ∀ a : K, IsSquare a ∨ IsSquare (-a)) {v : V} (hv : Q v = -1) :
    IsCyclic (cliffordFullCover Q) := by
  have hcard := card_cliffordFullCover_of_finrank_eq_one hQ hV h hK
  have : Finite (cliffordFullCover Q) := Nat.finite_of_card_ne_zero (by omega)
  let _ : Invertible (Q v) := invertibleOfNonzero (by rw [hv]; exact neg_ne_zero.2 one_ne_zero)
  refine isCyclic_of_orderOf_eq_card (cliffordFullCoverOfNorm v (Or.inr hv)) ?_
  rw [hcard]
  refine orderOf_eq_prime_pow (p := 2) (n := 1) ?_ ?_
  · rw [cliffordFullCover_ext_iff, coe_cliffordFullCoverOfNorm_pow, pow_one, sq, ι_sq_scalar, hv]
    intro h1
    have h2 : (-1 : K) = 1 := (algebraMap_injective Q).eq_iff.1 (by simpa using h1)
    exact two_ne_zero (by linear_combination -h2 : (2 : K) = 0)
  · rw [cliffordFullCover_ext_iff, coe_cliffordFullCoverOfNorm_pow,
      pow_succ 2 1, pow_one, pow_mul, sq (ι Q v), ι_sq_scalar, hv]
    simp

/-- **A non-cyclic full cover in rank one.** Over a field in which `-1` is not a square but every
element is a square up to sign, if some vector `e` of a nondegenerate line has norm `1`, then `1`,
`-1` and `e` are three solutions of `x ^ 2 = 1` in the full cover, which a cyclic group of order
four cannot have. -/
theorem not_isCyclic_cliffordFullCover_of_finrank_eq_one (h : ¬IsSquare (-1 : K))
    (hK : ∀ a : K, IsSquare a ∨ IsSquare (-a)) {v : V} (hv : Q v = 1) :
    ¬IsCyclic (cliffordFullCover Q) := by
  intro hcyc
  have : Nontrivial V := Module.nontrivial_of_finrank_eq_succ hV
  have hcard := card_cliffordFullCover_of_finrank_eq_one hQ hV h hK
  have : Finite (cliffordFullCover Q) := Nat.finite_of_card_ne_zero (by omega)
  let _ : Invertible (Q v) := invertibleOfNonzero (by rw [hv]; exact one_ne_zero)
  let _ : Fintype (cliffordFullCover Q) := Fintype.ofFinite _
  classical
  let e := cliffordFullCoverOfNorm v (Or.inl hv)
  let m := spinToCliffordFullCover Q (spinGroup.negOne Q hQ.ne_zero)
  have hm : m ∈ (cliffordFullCoverToOrthogonal Q).ker :=
    (mem_ker_cliffordFullCoverToOrthogonal_iff hQ h m).2 (Or.inr rfl)
  have hm1 : m ≠ 1 := fun h1 ↦ spinGroup.negOne_ne_one Q hQ.ne_zero
    (spinToCliffordFullCover_injective Q (by rw [map_one]; exact h1))
  have he : e ∉ (cliffordFullCoverToOrthogonal Q).ker := cliffordFullCoverOfNorm_notMem_ker hV v _
  have hsub : ({1, m, e} : Finset (cliffordFullCover Q)) ⊆
      Finset.univ.filter fun a ↦ a ^ 2 = 1 := by
    intro a ha
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    rcases ha with ha | ha | ha <;> rw [ha]
    · exact one_pow 2
    · rw [sq, ← map_mul, spinGroup.negOne_mul_self, map_one]
    · rw [cliffordFullCover_ext_iff, coe_cliffordFullCoverOfNorm_pow, sq, ι_sq_scalar, hv, map_one,
        OneMemClass.coe_one, OneMemClass.coe_one, Units.val_one]
  have h3 : ({1, m, e} : Finset (cliffordFullCover Q)).card = 3 :=
    Finset.card_eq_three.2 ⟨1, m, e, hm1.symm, fun h1 ↦ he (h1 ▸ one_mem _),
      fun h1 ↦ he (h1 ▸ hm), rfl⟩
  have := (Finset.card_le_card hsub).trans
    (IsCyclic.card_pow_eq_one_le (α := cliffordFullCover Q) two_pos)
  omega

/-- **The cyclic full cover in rank one.** Over a field in which `-1` is not a square but every
element is a square up to sign, the full cover of a nondegenerate line, a group of order four, is
cyclic exactly when some vector has norm `-1`. Otherwise some vector has norm `1`, obtained by
rescaling a vector of nonzero norm by a square root of its norm. -/
theorem isCyclic_cliffordFullCover_iff_of_finrank_eq_one (h : ¬IsSquare (-1 : K))
    (hK : ∀ a : K, IsSquare a ∨ IsSquare (-a)) :
    IsCyclic (cliffordFullCover Q) ↔ ∃ v, Q v = -1 := by
  refine ⟨fun hcyc ↦ ?_, fun ⟨v, hv⟩ ↦ isCyclic_cliffordFullCover_of_finrank_eq_one hQ hV h hK hv⟩
  have : Nontrivial V := Module.nontrivial_of_finrank_eq_succ hV
  obtain ⟨w, hw⟩ := hQ.exists_isUnit
  rcases hK (Q w) with ⟨r, hr⟩ | ⟨r, hr⟩
  · have hr0 : r ≠ 0 := by rintro rfl; simp [hr] at hw
    refine absurd hcyc (not_isCyclic_cliffordFullCover_of_finrank_eq_one hQ hV h hK
      (v := r⁻¹ • w) ?_)
    rw [QuadraticMap.map_smul, smul_eq_mul, hr]
    field_simp
  · have hr0 : r ≠ 0 := by rintro rfl; simp at hr; simp [hr] at hw
    refine ⟨r⁻¹ • w, ?_⟩
    rw [QuadraticMap.map_smul, smul_eq_mul, ← neg_neg (Q w), hr]
    field_simp

end RankOne

end CliffordAlgebra

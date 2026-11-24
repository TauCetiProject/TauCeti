/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.ZMod.Basic
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.LinearAlgebra.Matrix.Vec
public import Mathlib.LinearAlgebra.Span.Defs
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.Algebra.Order.Group.Unbundled.Int
import Mathlib.Data.Int.GCD
import Mathlib.LinearAlgebra.Matrix.AbsoluteValue
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import TauCeti.LinearAlgebra.Matrix.Determinant.Pencil
import TauCeti.LinearAlgebra.Matrix.Rank

/-!
# Small integral lifts of a one-dimensional kernel modulo `p`

Let `A` be an integer matrix whose entries are bounded by `B`, and let `p` be a prime with
`N! * B ^ N < p`, where `N` is the number of columns. Suppose that the kernel of the reduction of
`A` modulo `p` is a line, spanned by `x`. Then `x` lifts, up to a nonzero scalar, to a primitive
integer vector `v` with `A *ᵥ v = 0` and entries bounded by `N! * max B 1 ^ N`
(`Matrix.exists_primitive_mulVec_eq_zero_of_ker_map_eq_span`).

The reduction has rank `N - 1`, so after adjoining a standard basis vector `eⱼ` with `x j ≠ 0` to
`N - 1` independent rows, one obtains a square integer matrix `M` whose determinant is nonzero
modulo `p`. A row of the adjugate of `Mᵀ` is the vector of cofactors along the adjoined row: it
pairs each row of `A` with the determinant of a square matrix all of whose rows are rows of `A`.
Such a determinant is divisible by `p`, since `x` is in the kernel of its reduction, and is
smaller than `p` in absolute value by the Leibniz-expansion bound `N! * B ^ N` (`Matrix.det_le`),
so it vanishes. Its
pairing with `eⱼ` is `det M`, which is nonzero modulo `p`. Dividing the cofactor vector by the
gcd of its entries makes it primitive without changing its reduction up to a unit.

For square matrices of size `n`, a subspace of matrices over `ZMod p` in which every invertible
element is a multiple of one invertible `X` is the line through `X`, once `p > n`
(`Submodule.eq_span_singleton_of_mem_of_det_ne_zero`). Thus a unique invertible projective
solution `X` of small integral linear equations has a primitive integral representative `Q` of
small height, with `det Q` prime to `p`
(`Matrix.exists_primitive_mulVec_vec_eq_zero_of_unique_det_ne_zero`). This reconstruction is how
an element of `PGL₂(𝔽_p)` cut out by a few small congruences is identified with the reduction of
an integral matrix of determinant prime to `p`, for instance in arguments of Bakker and Tsimerman
on curves in products of modular curves. Since a nonzero minor modulo `p` is a nonzero integer,
the rational solutions also form a line, so the primitive `Q` is unique up to sign. For even `n`,
in particular `n = 2`, `det (-Q) = det Q`, so `det Q` is determined, sign included. For `n = 2`, a
primitive `Q` and `diagonal ![1, det Q]` have the same determinant and only units as common
divisors of their entries, so the elementary divisor classification
`Matrix.exists_SL_mul_mul_eq_of_det_eq_of_dvd_iff` writes `Q` as `U * diagonal ![1, det Q] * V`
with `U` and `V` in `SL₂(ℤ)`.

## Main results

* `Matrix.exists_primitive_mulVec_eq_zero_of_ker_map_eq_span`: a one-dimensional kernel modulo
  `p` of a small integer matrix lifts to a small primitive integral kernel vector.
* `Matrix.exists_primitive_mulVec_vec_eq_zero_of_unique_det_ne_zero`: a unique invertible
  projective solution modulo `p` of small integral linear equations in the entries of a square
  matrix lifts to a small primitive integral solution of determinant prime to `p`.

## References

* B. Bakker and J. Tsimerman, *p-torsion monodromy representations of elliptic curves over
  geometric function fields*, Ann. of Math. 184 (2016), 709–744, doi:10.4007/annals.2016.184.3.2,
  proofs of Lemma 15 and of Propositions 17 and 18.
-/

public section

open scoped Nat

namespace Matrix

variable {ι κ : Type*} [Finite ι] [Fintype κ] {p : ℕ} [Fact p.Prime]

omit [Finite ι] in
/-- A square integer matrix all of whose rows are rows of `A` has determinant zero, if the
reduction of `A` modulo `p` has a nonzero kernel vector and `p` exceeds the bound
`N! * B ^ N` on such determinants. -/
private theorem det_eq_zero_of_forall_exists_eq_row [DecidableEq κ] {A : Matrix ι κ ℤ} {B : ℕ}
    (hA : ∀ i j, |A i j| ≤ B) (hp : (Fintype.card κ)! * B ^ Fintype.card κ < p)
    {x : κ → ZMod p} (hx : x ≠ 0) (hAx : A.map (Int.castRingHom (ZMod p)) *ᵥ x = 0)
    {M : Matrix κ κ ℤ} (hM : ∀ k, ∃ i, M k = A i) : M.det = 0 := by
  refine Int.eq_zero_of_abs_lt_dvd ((ZMod.intCast_zmod_eq_zero_iff_dvd _ p).1 ?_) ?_
  · rw [Int.cast_det]
    refine exists_mulVec_eq_zero_iff.1 ⟨x, hx, funext fun k ↦ ?_⟩
    obtain ⟨i, hi⟩ := hM k
    simpa [mulVec, dotProduct, hi] using congrFun hAx i
  · refine (det_le (abv := AbsoluteValue.abs) (x := (B : ℤ)) fun k j ↦ ?_).trans_lt ?_
    · obtain ⟨i, hi⟩ := hM k
      simpa [hi] using hA i j
    · simpa [nsmul_eq_mul] using (Nat.cast_lt (α := ℤ)).2 hp

/-- If the kernel of the reduction of `A` modulo `p` is the line through `x`, there is a square
integer matrix `M` with a row `Pi.single j₀ 1`, where `x j₀ ≠ 0`, whose other rows are rows of
`A`, and whose determinant is nonzero modulo `p`. -/
private theorem exists_det_map_ne_zero [DecidableEq κ] {A : Matrix ι κ ℤ} {x : κ → ZMod p}
    (hx : x ≠ 0) (hAx : A.map (Int.castRingHom (ZMod p)) *ᵥ x = 0)
    (hker : LinearMap.ker (A.map (Int.castRingHom (ZMod p))).mulVecLin = ZMod p ∙ x) :
    ∃ (M : Matrix κ κ ℤ) (k₀ j₀ : κ), M k₀ = Pi.single j₀ 1 ∧ (∀ k ≠ k₀, ∃ i, M k = A i) ∧
      x j₀ ≠ 0 ∧ (M.map (Int.castRingHom (ZMod p))).det ≠ 0 := by
  classical
  set A' := A.map (Int.castRingHom (ZMod p))
  obtain ⟨j₀, hj₀⟩ : ∃ j, x j ≠ 0 := by simpa [funext_iff] using hx
  have hcard : 0 < Fintype.card κ := Fintype.card_pos_iff.2 ⟨j₀⟩
  -- The reduction has rank `N - 1`: choose `N - 1` independent rows.
  have hrank : A'.rank = Fintype.card κ - 1 := by
    have h := finrank_ker_mulVecLin A'
    rw [hker, finrank_span_singleton hx] at h
    have := A'.rank_le_card_width
    omega
  obtain ⟨r, c, hrc⟩ := le_rank_iff_exists_det_submatrix_ne_zero.1 hrank.ge
  have hli : LinearIndependent (ZMod p) (A'.submatrix r id).row :=
    linearIndependent_row_iff_exists_det_submatrix_ne_zero.2
      ⟨c, by simpa [submatrix_submatrix] using hrc⟩
  -- Every row of `A'` is orthogonal to `x`, while `Pi.single j₀ 1` is not.
  have hnot : Pi.single j₀ 1 ∉ Submodule.span (ZMod p) (Set.range (A'.submatrix r id).row) := by
    intro hmem
    have key : ∀ y ∈ Submodule.span (ZMod p) (Set.range (A'.submatrix r id).row), y ⬝ᵥ x = 0 := by
      intro y hy
      induction hy using Submodule.span_induction with
      | mem y hy =>
        obtain ⟨t, rfl⟩ := hy
        exact congrFun hAx (r t)
      | zero => exact zero_dotProduct x
      | add y z _ _ hy hz => rw [add_dotProduct, hy, hz, add_zero]
      | smul a y _ hy => rw [smul_dotProduct, hy, smul_zero]
    exact hj₀ (by simpa using key _ hmem)
  let σ : κ ≃ Option (Fin (Fintype.card κ - 1)) := Fintype.equivOfCardEq (by simp; omega)
  let M : Matrix κ κ ℤ := Matrix.of fun k ↦ Option.casesOn' (σ k) (Pi.single j₀ 1) fun t ↦ A (r t)
  refine ⟨M, σ.symm none, j₀, funext fun j ↦ by simp [M], fun k hk ↦ ?_, hj₀, ?_⟩
  · obtain ⟨t, ht⟩ := Option.ne_none_iff_exists'.1 fun h ↦ hk (σ.eq_symm_apply.2 h)
    exact ⟨r t, funext fun j ↦ by simp [M, ht]⟩
  · have hM : M.map (Int.castRingHom (ZMod p)) =
        Matrix.of fun k ↦ Option.casesOn' (σ k) (Pi.single j₀ 1) (A'.submatrix r id).row := by
      ext k j
      rcases h : σ k with _ | t
      · simp [M, h, Pi.single_apply, apply_ite]
      · simp [M, h, A']
    rw [hM]
    exact ((isUnit_iff_isUnit_det _).1 (linearIndependent_row_iff_isUnit.1
      ((linearIndependent_option'.2 ⟨hli, hnot⟩).comp σ σ.injective))).ne_zero

omit [Finite ι] in
/-- Dividing an integral kernel vector `w` of `A`, whose reduction is a multiple of `x` and is
nonzero modulo `p`, by the gcd of its entries gives a primitive integral kernel vector, no larger
than `w`, whose reduction is a nonzero multiple of `x`. -/
private theorem exists_primitive_of_mulVec_eq_zero {A : Matrix ι κ ℤ} {w : κ → ℤ}
    (hAw : A *ᵥ w = 0) {x : κ → ZMod p} (hwx : (fun j ↦ (w j : ZMod p)) ∈ ZMod p ∙ x) {j₀ : κ}
    (hwj₀ : (w j₀ : ZMod p) ≠ 0) {C : ℤ} (hC : ∀ j, |w j| ≤ C) :
    ∃ v : κ → ℤ, A *ᵥ v = 0 ∧ (∀ e : ℤ, (∀ j, e ∣ v j) → IsUnit e) ∧ (∀ j, |v j| ≤ C) ∧
      ∃ c : ZMod p, c ≠ 0 ∧ (fun j ↦ (v j : ZMod p)) = c • x := by
  classical
  obtain ⟨v, hwv, hv⟩ := Finset.extract_gcd w ⟨j₀, Finset.mem_univ _⟩
  set d := Finset.univ.gcd w
  have hwv' (j : κ) : w j = d * v j := hwv j (Finset.mem_univ j)
  have hd : (d : ZMod p) ≠ 0 := fun h ↦ hwj₀ (by rw [hwv', Int.cast_mul, h, zero_mul])
  have hd0 : d ≠ 0 := fun h ↦ hd (by rw [h, Int.cast_zero])
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.1 hwx
  refine ⟨v, ?_, fun e he ↦ isUnit_of_dvd_one (hv ▸ Finset.dvd_gcd fun j _ ↦ he j), fun j ↦ ?_,
    (d : ZMod p)⁻¹ * a, ?_, ?_⟩
  · have hw' : w = d • v := funext hwv'
    rw [hw', mulVec_smul] at hAw
    exact (smul_eq_zero.1 hAw).resolve_left hd0
  · refine le_trans ?_ (hC j)
    rw [hwv', abs_mul]
    exact le_mul_of_one_le_left (abs_nonneg _) (Int.one_le_abs hd0)
  · refine mul_ne_zero (inv_ne_zero hd) fun h ↦ hwj₀ ?_
    simpa [h] using (congrFun ha j₀).symm
  · funext j
    have hj := congrFun ha j
    simp only [Pi.smul_apply, smul_eq_mul, hwv', Int.cast_mul] at hj ⊢
    rw [mul_assoc, hj, inv_mul_cancel_left₀ hd]

/-- **Small integral lift of a one-dimensional kernel modulo `p`.** Let `A` be an integer matrix
with `N` columns and entries bounded by `B`, and `p` a prime with `N! * B ^ N < p`. If the kernel
of the reduction of `A` modulo `p` is the line through `x ≠ 0`, then there is a primitive integer
vector `v` with `A *ᵥ v = 0`, entries bounded by `N! * max B 1 ^ N`, and reduction a nonzero
multiple of `x`. -/
theorem exists_primitive_mulVec_eq_zero_of_ker_map_eq_span (A : Matrix ι κ ℤ) {B : ℕ}
    (hA : ∀ i j, |A i j| ≤ B) (hp : (Fintype.card κ)! * B ^ Fintype.card κ < p)
    {x : κ → ZMod p} (hx : x ≠ 0)
    (hker : LinearMap.ker (A.map (Int.castRingHom (ZMod p))).mulVecLin = ZMod p ∙ x) :
    ∃ v : κ → ℤ, A *ᵥ v = 0 ∧ (∀ e : ℤ, (∀ j, e ∣ v j) → IsUnit e) ∧
      (∀ j, |v j| ≤ ((Fintype.card κ)! * max B 1 ^ Fintype.card κ : ℕ)) ∧
      ∃ c : ZMod p, c ≠ 0 ∧ (fun j ↦ (v j : ZMod p)) = c • x := by
  classical
  have hAx : A.map (Int.castRingHom (ZMod p)) *ᵥ x = 0 := by
    simpa using (hker ▸ Submodule.mem_span_singleton_self x :
      x ∈ LinearMap.ker (A.map (Int.castRingHom (ZMod p))).mulVecLin)
  obtain ⟨M, k₀, j₀, hMk₀, hM, -, hdet⟩ := exists_det_map_ne_zero hx hAx hker
  -- The cofactors `w` along row `k₀`: pairing with `w` is the determinant with row `k₀` replaced.
  set w : κ → ℤ := Mᵀ.adjugate k₀
  have hw (a : κ → ℤ) : (M.updateRow k₀ a).det = w ⬝ᵥ a := by
    -- `(Mᵀ.adjugate *ᵥ a) k₀` is by definition the pairing of the row `w` with `a`.
    rw [← cramer_transpose_apply, cramer_eq_adjugate_mulVec]
    rfl
  have hAw : A *ᵥ w = 0 := funext fun i ↦ by
    rw [Pi.zero_apply, mulVec, dotProduct_comm, ← hw]
    refine det_eq_zero_of_forall_exists_eq_row hA hp hx hAx fun k ↦ ?_
    by_cases hk : k = k₀
    · exact ⟨i, by simp [hk]⟩
    · obtain ⟨i', hi'⟩ := hM k hk
      exact ⟨i', by simp [updateRow_ne hk, hi']⟩
  have hwj₀ : ((w j₀ : ℤ) : ZMod p) ≠ 0 := by
    rwa [← dotProduct_single_one w j₀, ← hw, ← hMk₀, updateRow_eq_self, Int.cast_det]
  have hwbound (j : κ) : |w j| ≤ ((Fintype.card κ)! * max B 1 ^ Fintype.card κ : ℕ) := by
    rw [← dotProduct_single_one w j, ← hw]
    refine (det_le (abv := AbsoluteValue.abs) (x := ((max B 1 : ℕ) : ℤ)) fun k j' ↦ ?_).trans
      (by simp)
    by_cases hk : k = k₀
    · subst hk
      rcases eq_or_ne j' j with rfl | hj
      · simp
      · simp [hj]
    · obtain ⟨i, hi⟩ := hM k hk
      simpa [updateRow_ne hk, hi] using (hA i j').trans
        (by exact_mod_cast le_max_left B 1 : ((B : ℕ) : ℤ) ≤ ((max B 1 : ℕ) : ℤ))
  have hwker : (fun j ↦ (w j : ZMod p)) ∈ ZMod p ∙ x := by
    rw [← hker, LinearMap.mem_ker, mulVecLin_apply]
    funext i
    simpa [hAw, Function.comp_def] using ((Int.castRingHom (ZMod p)).map_mulVec A w i).symm
  exact exists_primitive_of_mulVec_eq_zero hAw hwker hwj₀ hwbound

/-- **Small primitive lift of a unique invertible projective solution.** Let `A` be a system of
integral linear equations in the entries of an `n × n` matrix, with coefficients bounded by `B`;
each row of `A` is one equation, read against the vectorization `Matrix.vec`. Let `p` be a prime
with `N! * max B 1 ^ N < p` for `N = n²`. Suppose that `X` is an invertible solution modulo `p`
and that every invertible solution modulo `p` is a multiple of `X`. Then there is a primitive
integral solution `Q` with entries bounded by `N! * max B 1 ^ N`, whose reduction is a nonzero
multiple of `X`; in particular `p` does not divide `det Q`. -/
theorem exists_primitive_mulVec_vec_eq_zero_of_unique_det_ne_zero {n : Type*} [Fintype n]
    [DecidableEq n] [Nonempty n] (A : Matrix ι (n × n) ℤ) {B : ℕ} (hA : ∀ i j, |A i j| ≤ B)
    (hp : (Fintype.card (n × n))! * max B 1 ^ Fintype.card (n × n) < p)
    {X : Matrix n n (ZMod p)} (hX : X.det ≠ 0)
    (hAX : A.map (Int.castRingHom (ZMod p)) *ᵥ X.vec = 0)
    (huniq : ∀ Y : Matrix n n (ZMod p), Y.det ≠ 0 →
      A.map (Int.castRingHom (ZMod p)) *ᵥ Y.vec = 0 → ∃ c : ZMod p, Y = c • X) :
    ∃ Q : Matrix n n ℤ, A *ᵥ Q.vec = 0 ∧ (∀ e : ℤ, (∀ i j, e ∣ Q i j) → IsUnit e) ∧
      (∀ i j, |Q i j| ≤ ((Fintype.card (n × n))! * max B 1 ^ Fintype.card (n × n) : ℕ)) ∧
      (∃ c : ZMod p, c ≠ 0 ∧ Q.map (Int.castRingHom (ZMod p)) = c • X) ∧ ¬(p : ℤ) ∣ Q.det := by
  set A' := A.map (Int.castRingHom (ZMod p))
  set N := Fintype.card (n × n)
  have hpos : 0 < max B 1 ^ N := pow_pos (lt_max_of_lt_right one_pos) N
  -- `p` exceeds the size `n` of the matrices, and the Leibniz bound `N! * B ^ N`.
  have hcard : (Fintype.card n : Cardinal) < Cardinal.mk (ZMod p) := by
    rw [Cardinal.mk_fintype, ZMod.card, Nat.cast_lt]
    calc Fintype.card n ≤ N := by simpa [N, Fintype.card_prod] using Nat.le_mul_self _
      _ ≤ N ! := Nat.self_le_factorial N
      _ ≤ N ! * max B 1 ^ N := Nat.le_mul_of_pos_right _ hpos
      _ < p := hp
  have hp' : N ! * B ^ N < p :=
    lt_of_le_of_lt (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (le_max_left B 1) N)) hp
  -- The solutions modulo `p` form the line through `X`; transport it along the vectorization.
  let e : Matrix n n (ZMod p) ≃ₗ[ZMod p] n × n → ZMod p := LinearEquiv.ofBijective
    { toFun := vec, map_add' := vec_add, map_smul' := vec_smul } vec_bijective
  have hV := (LinearMap.ker (A'.mulVecLin ∘ₗ e)).eq_span_singleton_of_mem_of_det_ne_zero hcard
    (by simpa [e] using hAX) hX fun Y hY hYdet ↦ huniq Y hYdet (by simpa [e] using hY)
  have hker : LinearMap.ker A'.mulVecLin = ZMod p ∙ X.vec := by
    rw [← Submodule.map_comap_eq_of_surjective e.surjective (LinearMap.ker A'.mulVecLin),
      ← LinearMap.ker_comp, hV, Submodule.map_span, Set.image_singleton]
    simp [e]
  have hXvec : X.vec ≠ 0 := fun h ↦ hX (by rw [vec_eq_zero_iff.1 h, det_zero])
  obtain ⟨v, hAv, hprim, hbound, c, hc, hv⟩ :=
    exists_primitive_mulVec_eq_zero_of_ker_map_eq_span A hA hp' hXvec hker
  let Q : Matrix n n ℤ := (Equiv.ofBijective _ vec_bijective).symm v
  have hQv : Q.vec = v := Equiv.ofBijective_apply_symm_apply _ vec_bijective v
  have hQ : Q.map (Int.castRingHom (ZMod p)) = c • X := by
    rw [← vec_inj, vec_map, hQv, vec_smul, ← hv, Int.coe_castRingHom, Function.comp_def]
  refine ⟨Q, hQv ▸ hAv, fun d hd ↦ hprim d fun ij ↦ hQv ▸ hd ij.2 ij.1,
    fun i j ↦ by rw [← hQv] at hbound; exact hbound (j, i), ⟨c, hc, hQ⟩, ?_⟩
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd, Int.cast_det, ← Int.coe_castRingHom, hQ, det_smul]
  exact mul_ne_zero (pow_ne_zero _ hc) hX

end Matrix

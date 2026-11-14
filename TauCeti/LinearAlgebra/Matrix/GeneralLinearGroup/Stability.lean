/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Stable
public import TauCeti.LinearAlgebra.Matrix.OneSubVecMulVec
public import TauCeti.RingTheory.StableRange

/-!
# General linear stability theorems over rings of bounded Bass stable range

Over a possibly noncommutative ring `R` of Bass stable range at most `s`
(`TauCeti.HasStableRangeLE R s`), stabilization `u ↦ u ⊕ 1` of finite-size invertible matrices
captures algebraic `K₁(R)` already in finite rank:

* **Surjective stability (Bass).** Whenever `s ≤ Fintype.card n`, every invertible matrix in
  `GL (n ⊕ k) R` factors as `fromBlocks h 0 0 1 * e` with `h : GL n R` and
  `e ∈ elementarySubgroup (n ⊕ k) R`. Consequently `AlgebraicK1.mk R n : GL (Fin n) R →* K₁(R)` is
  surjective for `s ≤ n`.
* **Normality and unimodular orbits.** Whenever `s + 1 ≤ Fintype.card n`, the elementary subgroup
  `elementarySubgroup n R` is normal in `GL n R` and acts transitively on unimodular rows in
  `n → R`. Consequently rank-one unipotent matrices `1 - vecMulVec u v` with `v` unimodular and
  `v ⬝ᵥ u = 0` belong to `elementarySubgroup n R`.
* **Injective stability (Vaserstein).** Whenever `s + 1 ≤ Fintype.card n`, an invertible matrix
  `g : GL n R` whose block stabilization `fromBlocks g 0 0 1` lies in
  `elementarySubgroup (n ⊕ k) R` already lies in `elementarySubgroup n R`. The proof constructs
  Vaserstein's right `E_{m + 1}(R)`-invariant retraction `GL (m ⊕ Unit) R → GL m R ⧸ E m R` by
  elementary row shortening on `m ⊕ Unit`.
* **Finite-rank descriptions of `K₁(R)` and `[GLₙ(R), GLₙ(R)]`.** Outside the stable range, the
  kernel of `AlgebraicK1.mk R n` is the preimage of `E_∞(R)` (the directed union of stabilized
  elementary preimages), giving `GL (Fin n) R ⧸ (AlgebraicK1.mk R n).ker ≃* K₁(R)` already for
  `s ≤ n`. Once `s + 1 ≤ n`, this kernel equals `elementarySubgroup (Fin n) R`, yielding
  `GL (Fin n) R ⧸ elementarySubgroup (Fin n) R ≃* K₁(R)` and
  `commutator (GL n R) ≤ elementarySubgroup n R`. Once `max 3 (s + 1) ≤ n`,
  `elementarySubgroup (Fin n) R = commutator (GL (Fin n) R)` and
  `Abelianization (GL (Fin n) R) ≃* K₁(R)`.

## Main definitions

* `TauCeti.AlgebraicK1.quotientKerMkEquiv`: `GL (Fin n) R ⧸ (AlgebraicK1.mk R n).ker ≃* K₁(R)`
  for `s ≤ n`.
* `TauCeti.AlgebraicK1.quotientFinElementarySubgroupEquiv`:
  `GL (Fin n) R ⧸ elementarySubgroup (Fin n) R ≃* K₁(R)` for `s + 1 ≤ n`.
* `TauCeti.AlgebraicK1.abelianizationFinEquiv`:
  `Group.Abelianization (GL (Fin n) R) ≃* K₁(R)` for `max 3 (s + 1) ≤ n`.

## Main results

* `TauCeti.surjective_stability`: Bass's surjective stability theorem for `GL (n ⊕ k) R`.
* `TauCeti.elementarySubgroup_normal_of_hasStableRangeLE`: normality of `E n R` in `GL n R` for
  `s + 1 ≤ Fintype.card n`.
* `TauCeti.HasStableRangeLE.exists_vecMul_elementarySubgroup_eq_single`: transitive action of
  `E m R` on unimodular rows for `s + 1 ≤ Fintype.card m`.
* `TauCeti.HasStableRangeLE.oneSubVecMulVecGL_mem_elementarySubgroup`: rank-one unipotent matrices
  with unimodular covector lie in `E m R` for `s + 1 ≤ Fintype.card m`.
* `TauCeti.injective_stability`: Vaserstein's injective stability theorem for `GL n R`.
* `TauCeti.AlgebraicK1.mk_surjective`, `TauCeti.AlgebraicK1.ker_mk_eq_elementarySubgroup`:
  finite-rank surjectivity and kernel identification for `AlgebraicK1.mk` in the stable range.
* `TauCeti.elementarySubgroup_eq_commutator_of_hasStableRangeLE`: `E n R = ⁅GL n R, GL n R⁆` for
  `max 3 (s + 1) ≤ Fintype.card n`.

## References

* H. Bass, *Algebraic K-Theory*, W. A. Benjamin (1968), Chapter V, §3–§4.
* L. N. Vaserstein, *On the stabilization of the general linear group over a ring*, Mathematics of
  the USSR-Sbornik 8 (1969), 383–400.
* C. A. Weibel, *The K-book: An Introduction to Algebraic K-Theory*, Graduate Studies in
  Mathematics 145 (2013), Chapter III, Remark 1.2.5 and Exercise 1.3.
-/

public section

noncomputable section

open Matrix

open scoped Matrix commutatorElement

namespace TauCeti

/-! ## Pivot reindexing and last-row clearing -/

/-- Split off a chosen pivot `i₀ : m` as the `Unit` summand of `{i : m // i ≠ i₀} ⊕ Unit`. -/
private def complSumUnitEquiv {m : Type*} [DecidableEq m] (i₀ : m) :
    {i : m // i ≠ i₀} ⊕ Unit ≃ m where
  toFun := Sum.elim Subtype.val (fun _ ↦ i₀)
  invFun i := if hi : i = i₀ then Sum.inr () else Sum.inl ⟨i, hi⟩
  left_inv := fun
    | Sum.inl ⟨i, hi⟩ => by simp [hi]
    | Sum.inr () => by simp
  right_inv i := by by_cases hi : i = i₀ <;> simp [hi]

@[simp] private theorem complSumUnitEquiv_inl {m : Type*} [DecidableEq m] (i₀ : m)
    (i : {i : m // i ≠ i₀}) : complSumUnitEquiv i₀ (Sum.inl i) = i.1 := (rfl)

@[simp] private theorem complSumUnitEquiv_inr {m : Type*} [DecidableEq m] (i₀ : m) (u : Unit) :
    complSumUnitEquiv i₀ (Sum.inr u) = i₀ := (rfl)

@[simp] private theorem complSumUnitEquiv_symm_coe {m : Type*} [DecidableEq m] (i₀ : m)
    (i : {i : m // i ≠ i₀}) : (complSumUnitEquiv i₀).symm i.1 = Sum.inl i := by
  simp [complSumUnitEquiv, i.2]

@[simp] private theorem complSumUnitEquiv_symm_self {m : Type*} [DecidableEq m] (i₀ : m) :
    (complSumUnitEquiv i₀).symm i₀ = Sum.inr () := by simp [complSumUnitEquiv]

private theorem le_card_subtype_ne {m : Type*} [Fintype m] [DecidableEq m] {s : ℕ}
    (hm : s + 1 ≤ Fintype.card m) (i₀ : m) : s ≤ Fintype.card {i : m // i ≠ i₀} := by
  have hc := Fintype.card_congr (complSumUnitEquiv i₀)
  simp only [Fintype.card_sum, Fintype.card_unique] at hc; omega

/-- Peel one index `x₀ : k` off the right summand of `n ⊕ k`. -/
private def sumComplUnitEquiv (n : Type*) {k : Type*} [DecidableEq k] (x₀ : k) :
    (n ⊕ {x : k // x ≠ x₀}) ⊕ Unit ≃ n ⊕ k :=
  (Equiv.sumAssoc n {x : k // x ≠ x₀} Unit).trans
    (Equiv.sumCongr (Equiv.refl n) (complSumUnitEquiv x₀))

private theorem reindexGL_sumComplUnitEquiv_fromBlocksGL {R n k : Type*} [Ring R] [Fintype n]
    [DecidableEq n] [Fintype k] [DecidableEq k] (x₀ : k) (h : GL n R) :
    (sumComplUnitEquiv n x₀).reindexGL R
      (fromBlocksGL (fromBlocksGL (h, (1 : GL {x : k // x ≠ x₀} R)), (1 : GL Unit R))) =
      fromBlocksGL (h, (1 : GL k R)) := by
  let φ := sumComplUnitEquiv n x₀
  refine Units.ext ?_
  ext p q
  obtain ⟨p, rfl⟩ := φ.surjective p
  obtain ⟨q, rfl⟩ := φ.surjective q
  rcases p with (i | y) | ⟨⟩ <;> rcases q with (j | z) | ⟨⟩
  · simp [φ, sumComplUnitEquiv]
  · simp [φ, sumComplUnitEquiv]
  · simp [φ, sumComplUnitEquiv]
  · simp [φ, sumComplUnitEquiv]
  · simp [φ, sumComplUnitEquiv, Matrix.one_apply, Subtype.ext_iff]
  · simp [φ, sumComplUnitEquiv, y.2]
  · simp [φ, sumComplUnitEquiv]
  · simp [φ, sumComplUnitEquiv, z.2.symm]
  · simp [φ, sumComplUnitEquiv]

/-- Right elementary factor clearing the bottom row `(a, d)` of `A : GL (m ⊕ Unit) R` to `(0, 1)`
from a right-inverse witness `b` with `a ⬝ᵥ b = 1`. -/
private def clearLastRowFactor {R m : Type*} [Ring R] [Fintype m] [DecidableEq m]
    (A : GL (m ⊕ Unit) R) (b : m → R) : GL (m ⊕ Unit) R :=
  upperBlockGL (Matrix.of fun i (_ : Unit) ↦ b i * (1 - A (Sum.inr ()) (Sum.inr ()))) *
    lowerBlockGL (Matrix.of fun (_ : Unit) j ↦ -A (Sum.inr ()) (Sum.inl j))

private theorem clearLastRowFactor_mem_elementarySubgroup {R m : Type*} [Ring R] [Fintype m]
    [DecidableEq m] (A : GL (m ⊕ Unit) R) (b : m → R) :
    clearLastRowFactor A b ∈ elementarySubgroup (m ⊕ Unit) R :=
  mul_mem (upperBlockGL_mem_elementarySubgroup _) (lowerBlockGL_mem_elementarySubgroup _)

private theorem mul_upperBlockGL_inr_inr {R m : Type*} [Ring R] [Fintype m] [DecidableEq m]
    (A : GL (m ⊕ Unit) R) {b : m → R}
    (hb : (fun j ↦ A (Sum.inr ()) (Sum.inl j)) ⬝ᵥ b = 1) :
    (A * upperBlockGL (Matrix.of fun i (_ : Unit) ↦
        b i * (1 - A (Sum.inr ()) (Sum.inr ()))) : GL (m ⊕ Unit) R)
      (Sum.inr ()) (Sum.inr ()) = 1 := by
  simp only [Units.val_mul, coe_upperBlockGL, Matrix.mul_apply, Fintype.sum_sum_type,
    fromBlocks_apply₁₂, fromBlocks_apply₂₂, Matrix.of_apply, Fintype.univ_punit,
    Finset.sum_singleton, Matrix.one_apply_eq, mul_one]
  have hsum : (∑ x : m, A (Sum.inr ()) (Sum.inl x) *
      (b x * (1 - A (Sum.inr ()) (Sum.inr ())))) =
      ((fun j ↦ A (Sum.inr ()) (Sum.inl j)) ⬝ᵥ b) *
        (1 - A (Sum.inr ()) (Sum.inr ())) := by
    simp only [dotProduct, Finset.sum_mul, mul_assoc]
  rw [hsum, hb, one_mul, sub_add_cancel]

private theorem toBlocks_mul_clearLastRowFactor {R m : Type*} [Ring R] [Fintype m]
    [DecidableEq m] {A : GL (m ⊕ Unit) R} {b : m → R}
    (hb : (fun j ↦ A (Sum.inr ()) (Sum.inl j)) ⬝ᵥ b = 1) :
    ((A * clearLastRowFactor A b : GL (m ⊕ Unit) R) :
        Matrix (m ⊕ Unit) (m ⊕ Unit) R).toBlocks₂₁ = 0 ∧
      ((A * clearLastRowFactor A b : GL (m ⊕ Unit) R) :
        Matrix (m ⊕ Unit) (m ⊕ Unit) R).toBlocks₂₂ = 1 := by
  let A₁ : GL (m ⊕ Unit) R :=
    A * upperBlockGL (Matrix.of fun i (_ : Unit) ↦ b i * (1 - A (Sum.inr ()) (Sum.inr ())))
  have hd1 : A₁ (Sum.inr ()) (Sum.inr ()) = 1 := mul_upperBlockGL_inr_inr A hb
  have hfac : A * clearLastRowFactor A b =
      A₁ * lowerBlockGL (Matrix.of fun (_ : Unit) k ↦ -A (Sum.inr ()) (Sum.inl k)) := by
    rw [clearLastRowFactor, mul_assoc]
  constructor
  · ext ⟨⟩ j; rw [toBlocks₂₁, of_apply, hfac]
    have hleft : A₁ (Sum.inr ()) (Sum.inl j) = A (Sum.inr ()) (Sum.inl j) := by
      simp [A₁, Units.val_mul, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply]
    simp [Units.val_mul, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply, hleft, hd1]
  · ext ⟨⟩ ⟨⟩; rw [toBlocks₂₂, of_apply, hfac]
    simp [Units.val_mul, Matrix.mul_apply, Fintype.sum_sum_type, hd1]

/-- Right multiplication by `lowerBlockGL` adds `d` times the row `c` to the bottom-left row. -/
private theorem mul_lowerBlockGL_inr_inl {R m : Type*} [Ring R] [Fintype m] [DecidableEq m]
    (A : GL (m ⊕ Unit) R) (c : m → R) (j : m) :
    (A * lowerBlockGL (Matrix.of fun (_ : Unit) k ↦ c k) : GL (m ⊕ Unit) R)
      (Sum.inr ()) (Sum.inl j) =
      A (Sum.inr ()) (Sum.inl j) + A (Sum.inr ()) (Sum.inr ()) * c j := by
  simp [Units.val_mul, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply]

private theorem isUnimodular_sumElim_inr {R m : Type*} [Ring R] [Fintype m] [DecidableEq m]
    (A : GL (m ⊕ Unit) R) :
    Module.IsUnimodular R (Sum.elim (fun j ↦ A (Sum.inr ()) (Sum.inl j))
      (fun _ : Unit ↦ A (Sum.inr ()) (Sum.inr ()))) := by
  have h : (Sum.elim (fun j ↦ A (Sum.inr ()) (Sum.inl j))
      (fun _ : Unit ↦ A (Sum.inr ()) (Sum.inr ()))) = fun j ↦ A (Sum.inr ()) j := by
    ext (j | ⟨⟩) <;> rfl
  exact h ▸ A.isUnimodular_apply (Sum.inr ())

private theorem mul_fromBlocksGL_inr_inl {R m : Type*} [Ring R] [Fintype m] [DecidableEq m]
    (A : GL (m ⊕ Unit) R) (e : GL m R) :
    (fun j ↦ (A * fromBlocksGL (e, (1 : GL Unit R)) : GL (m ⊕ Unit) R) (Sum.inr ()) (Sum.inl j)) =
      (fun j ↦ A (Sum.inr ()) (Sum.inl j)) ᵥ* (e : Matrix m m R) := by
  ext j; simp [Units.val_mul, Matrix.mul_apply, Fintype.sum_sum_type, vecMul, dotProduct]

/-! ## Surjective stability and normality -/

/-- Single-step surjective stability on `n ⊕ Unit`. -/
private theorem surjective_stability_unit {R n : Type*} [Ring R] [Fintype n] [DecidableEq n]
    {s : ℕ} (hR : HasStableRangeLE R s) (hn : s ≤ Fintype.card n) (g : GL (n ⊕ Unit) R) :
    ∃ (h : GL n R) (e : GL (n ⊕ Unit) R),
      e ∈ elementarySubgroup (n ⊕ Unit) R ∧ g = fromBlocksGL (h, 1) * e := by
  obtain ⟨c, hc⟩ := hR.exists_isUnimodular_add_mul hn (isUnimodular_sumElim_inr g)
  let e₁ : GL (n ⊕ Unit) R := lowerBlockGL (Matrix.of fun (_ : Unit) j ↦ c j)
  let g₁ : GL (n ⊕ Unit) R := g * e₁
  have hg₁ : Module.IsUnimodular R (fun j ↦ g₁ (Sum.inr ()) (Sum.inl j)) := by
    simpa only [g₁, e₁, mul_lowerBlockGL_inr_inl] using hc
  obtain ⟨b, hb⟩ := TauCeti.Module.isUnimodular_pi_iff.mp hg₁
  let e₂ : GL (n ⊕ Unit) R := clearLastRowFactor g₁ b
  let g₂ : GL (n ⊕ Unit) R := g₁ * e₂
  obtain ⟨h₂₁, h₂₂⟩ := toBlocks_mul_clearLastRowFactor hb
  let h : GL n R := g₂.toBlocks₁₁GL h₂₁ h₂₂
  let u : GL (n ⊕ Unit) R := upperBlockGL
    ((↑h⁻¹ : Matrix n n R) * (g₂ : Matrix (n ⊕ Unit) (n ⊕ Unit) R).toBlocks₁₂)
  have hg₂ : g₂ = fromBlocksGL (h, 1) * u := eq_fromBlocksGL_mul_upperBlockGL g₂ h₂₁ h₂₂
  refine ⟨h, u * e₂⁻¹ * e₁⁻¹, ?_, ?_⟩
  · exact mul_mem (mul_mem (upperBlockGL_mem_elementarySubgroup _)
      (inv_mem (clearLastRowFactor_mem_elementarySubgroup g₁ b)))
      (inv_mem (lowerBlockGL_mem_elementarySubgroup _))
  · calc g = g₂ * e₂⁻¹ * e₁⁻¹ := by simp [g₂, g₁, mul_assoc]
      _ = fromBlocksGL (h, 1) * (u * e₂⁻¹ * e₁⁻¹) := by rw [hg₂]; group

/-- **Surjective stability (Bass):** if `R` has stable range at most `s` and `n` has at least `s`
indices, every invertible matrix of size `n ⊕ k` is the block sum of an invertible matrix of
size `n` with an identity block, times an elementary matrix. -/
theorem surjective_stability {R : Type*} [Ring R] (s : ℕ) (hR : HasStableRangeLE R s)
    (n k : Type*) [Fintype n] [DecidableEq n] [Fintype k] [DecidableEq k]
    (hn : s ≤ Fintype.card n) (g : Matrix.GeneralLinearGroup (n ⊕ k) R) :
    ∃ (h : Matrix.GeneralLinearGroup n R) (e : Matrix.GeneralLinearGroup (n ⊕ k) R),
      e ∈ TauCeti.elementarySubgroup (n ⊕ k) R ∧
        (g : Matrix (n ⊕ k) (n ⊕ k) R) = Matrix.fromBlocks (h : Matrix n n R) 0 0 1 *
          (e : Matrix (n ⊕ k) (n ⊕ k) R) := by
  suffices ∀ c : ℕ, ∀ (k : Type _) [Fintype k] [DecidableEq k], Fintype.card k = c →
      ∀ g : GL (n ⊕ k) R, ∃ (h : GL n R) (e : GL (n ⊕ k) R),
        e ∈ elementarySubgroup (n ⊕ k) R ∧ g = fromBlocksGL (h, 1) * e by
    obtain ⟨h, e, he, rfl⟩ := this (Fintype.card k) k rfl g
    exact ⟨h, e, he, by simp⟩
  intro c
  induction c with
  | zero =>
    intro k _ _ hk g
    have : IsEmpty k := Fintype.card_eq_zero_iff.mp hk
    let h : GL n R := g.toBlocks₁₁GL (by ext x _; exact isEmptyElim x)
      (by ext x _; exact isEmptyElim x)
    refine ⟨h, 1, one_mem _, Units.ext ?_⟩
    ext (i | x) (j | y)
    · simp [h, toBlocks₁₁]
    · exact isEmptyElim y
    · exact isEmptyElim x
    · exact isEmptyElim x
  | succ m ih =>
    intro k _ _ hk g
    obtain ⟨x₀⟩ := Fintype.card_pos_iff.mp (by omega : 0 < Fintype.card k)
    let φ := sumComplUnitEquiv n x₀
    have hcard_nk' : s ≤ Fintype.card (n ⊕ {x : k // x ≠ x₀}) := by
      rw [Fintype.card_sum]; omega
    obtain ⟨g₁, e₁, he₁, hg'⟩ := surjective_stability_unit hR hcard_nk' (φ.symm.reindexGL R g)
    have hcard_k' : Fintype.card {x : k // x ≠ x₀} = m := by
      have hc := Fintype.card_congr (complSumUnitEquiv x₀)
      simp only [Fintype.card_sum, Fintype.card_unique] at hc
      omega
    obtain ⟨h, e₂, he₂, hg₁⟩ := ih {x : k // x ≠ x₀} hcard_k' g₁
    have he₂' : fromBlocksGL (e₂, (1 : GL Unit R)) ∈
        elementarySubgroup ((n ⊕ {x : k // x ≠ x₀}) ⊕ Unit) R :=
      map_elementarySubgroup_le_elementarySubgroup ⟨e₂, he₂, rfl⟩
    let e₀ := fromBlocksGL (e₂, (1 : GL Unit R)) * e₁
    have he : φ.reindexGL R e₀ ∈ elementarySubgroup (n ⊕ k) R := by
      rw [← φ.map_reindexGL_elementarySubgroup]
      exact ⟨e₀, mul_mem he₂' he₁, rfl⟩
    refine ⟨h, φ.reindexGL R e₀, he, ?_⟩
    have hdecomp : φ.symm.reindexGL R g =
        fromBlocksGL (fromBlocksGL (h, (1 : GL {x : k // x ≠ x₀} R)), (1 : GL Unit R)) * e₀ := by
      have hmul : fromBlocksGL (fromBlocksGL (h, 1) * e₂, (1 : GL Unit R)) =
          fromBlocksGL (fromBlocksGL (h, 1), 1) * fromBlocksGL (e₂, 1) := by
        rw [← map_mul]; simp
      rw [hg', hg₁, hmul, mul_assoc]
    calc g = φ.reindexGL R (φ.symm.reindexGL R g) := by simp
      _ = fromBlocksGL (h, 1) * φ.reindexGL R e₀ := by
          rw [hdecomp, map_mul, reindexGL_sumComplUnitEquiv_fromBlocksGL]

/-- Over a ring of Bass stable range at most `s`, the elementary subgroup `elementarySubgroup n R`
is normal in `GL n R` whenever `s + 1 ≤ Fintype.card n`. -/
theorem elementarySubgroup_normal_of_hasStableRangeLE {R n : Type*} [Ring R] [Fintype n]
    [DecidableEq n] {s : ℕ} (hR : HasStableRangeLE R s) (hn : s + 1 ≤ Fintype.card n) :
    (elementarySubgroup n R).Normal := by
  refine ⟨fun x hx g ↦ ?_⟩
  suffices elementarySubgroup n R ≤
      (elementarySubgroup n R).comap (MulAut.conj g).toMonoidHom from this hx
  refine elementarySubgroup_le_iff.mpr fun i j hij a ↦ ?_
  rw [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  let φ := complSumUnitEquiv i
  obtain ⟨h, e, he, hginv⟩ := surjective_stability_unit hR (le_card_subtype_ne hn i)
    (φ.symm.reindexGL R g)⁻¹
  have hg' : φ.symm.reindexGL R g = e⁻¹ * fromBlocksGL (h⁻¹, 1) := by
    calc φ.symm.reindexGL R g = ((φ.symm.reindexGL R g)⁻¹)⁻¹ := (inv_inv _).symm
      _ = e⁻¹ * (fromBlocksGL (h, 1))⁻¹ := by rw [hginv, _root_.mul_inv_rev]
      _ = e⁻¹ * fromBlocksGL (h⁻¹, 1) := by congr 1; rw [← map_inv]; simp
  let Y : Matrix Unit {k : n // k ≠ i} R := Matrix.single () ⟨j, hij.symm⟩ a
  have htr : φ.symm.reindexGL R (transvectionUnit hij a) = lowerBlockGL Y := by
    refine Units.ext ?_
    ext (p | ⟨⟩) (q | ⟨⟩)
    · simp [φ, coe_transvectionUnit_eq_one_add_single, Matrix.one_apply,
        Subtype.ext_iff, p.2.symm]
    · simp [φ, coe_transvectionUnit_eq_one_add_single, p.2, p.2.symm]
    · simp [φ, Y, coe_transvectionUnit_eq_one_add_single, single_apply, Subtype.ext_iff, q.2.symm]
    · simp [φ, coe_transvectionUnit_eq_one_add_single, hij.symm]
  have hconj : φ.symm.reindexGL R (g * transvectionUnit hij a * g⁻¹) =
      e⁻¹ * lowerBlockGL (Y * (h : Matrix {k : n // k ≠ i} {k : n // k ≠ i} R)) * e := by
    rw [map_mul, map_mul, map_inv, hg', htr]
    have hmid : fromBlocksGL (h⁻¹, (1 : GL Unit R)) * lowerBlockGL Y *
        (fromBlocksGL (h⁻¹, (1 : GL Unit R)))⁻¹ =
        lowerBlockGL (Y * (h : Matrix {k : n // k ≠ i} {k : n // k ≠ i} R)) := by
      refine Units.ext ?_
      have hh : (↑(fromBlocksGL (h⁻¹, (1 : GL Unit R)))⁻¹ :
          Matrix ({k : n // k ≠ i} ⊕ Unit) ({k : n // k ≠ i} ⊕ Unit) R) =
          fromBlocks (h : Matrix {k : n // k ≠ i} {k : n // k ≠ i} R) 0 0 1 := by
        rw [← map_inv]; simp
      rw [Units.val_mul, Units.val_mul, hh]
      simp [fromBlocks_multiply]
    calc e⁻¹ * fromBlocksGL (h⁻¹, 1) * lowerBlockGL Y * (e⁻¹ * fromBlocksGL (h⁻¹, 1))⁻¹
        = e⁻¹ * (fromBlocksGL (h⁻¹, 1) * lowerBlockGL Y * (fromBlocksGL (h⁻¹, 1))⁻¹) * e := by
          group
      _ = e⁻¹ * lowerBlockGL (Y * (h : Matrix {k : n // k ≠ i} {k : n // k ≠ i} R)) * e := by
          rw [hmid]
  have hmem : e⁻¹ * lowerBlockGL (Y * (h : Matrix {k : n // k ≠ i} {k : n // k ≠ i} R)) * e ∈
      elementarySubgroup ({k : n // k ≠ i} ⊕ Unit) R :=
    mul_mem (mul_mem (inv_mem he) (lowerBlockGL_mem_elementarySubgroup _)) he
  rw [← φ.map_reindexGL_elementarySubgroup]
  exact ⟨_, hmem, by rw [← hconj]; simp⟩

/-! ## Unimodular orbits and rank-one unipotent matrices -/

/-- Row reduction on `ι ⊕ Unit` sending `(a', d)` to `(0, 1)` once `(a' + d • c) ⬝ᵥ b = 1`. -/
private theorem vecMul_lower_upper_lower_eq_inr {R ι : Type*} [Ring R] [Fintype ι] [DecidableEq ι]
    {a' c b : ι → R} {d : R} (hb : (fun i ↦ a' i + d * c i) ⬝ᵥ b = 1) :
    Sum.elim a' (fun _ : Unit ↦ d) ᵥ*
      ((lowerBlockGL (Matrix.of fun (_ : Unit) j ↦ c j) *
        upperBlockGL (Matrix.of fun i (_ : Unit) ↦ b i * (1 - d)) *
        lowerBlockGL (Matrix.of fun (_ : Unit) j ↦ -(a' j + d * c j)) : GL (ι ⊕ Unit) R) :
        Matrix (ι ⊕ Unit) (ι ⊕ Unit) R) = Sum.elim (0 : ι → R) (fun _ : Unit ↦ 1) := by
  let u : ι → R := fun i ↦ a' i + d * c i
  have hv₁ : Sum.elim a' (fun _ : Unit ↦ d) ᵥ*
      (lowerBlockGL (Matrix.of fun (_ : Unit) j ↦ c j) : Matrix (ι ⊕ Unit) (ι ⊕ Unit) R) =
      Sum.elim u (fun _ : Unit ↦ d) := by
    ext (j | ⟨⟩) <;> simp [u, vecMul, dotProduct, Fintype.sum_sum_type, Matrix.one_apply]
  have hv₂ : Sum.elim u (fun _ : Unit ↦ d) ᵥ*
      (upperBlockGL (Matrix.of fun i (_ : Unit) ↦ b i * (1 - d)) :
        Matrix (ι ⊕ Unit) (ι ⊕ Unit) R) = Sum.elim u (fun _ : Unit ↦ 1) := by
    ext (j | ⟨⟩)
    · simp [vecMul, dotProduct, Fintype.sum_sum_type, Matrix.one_apply]
    · simp only [coe_upperBlockGL, vecMul, dotProduct, Fintype.sum_sum_type, Sum.elim_inl,
        fromBlocks_apply₁₂, Matrix.of_apply, Sum.elim_inr, Fintype.univ_punit,
        Finset.sum_singleton, fromBlocks_apply₂₂, Matrix.one_apply_eq, mul_one]
      have hsum : (∑ i : ι, u i * (b i * (1 - d))) = (u ⬝ᵥ b) * (1 - d) := by
        simp only [dotProduct, Finset.sum_mul, mul_assoc]
      rw [hsum, hb, one_mul, sub_add_cancel]
  have hv₃ : Sum.elim u (fun _ : Unit ↦ (1 : R)) ᵥ*
      (lowerBlockGL (Matrix.of fun (_ : Unit) j ↦ -(a' j + d * c j)) :
        Matrix (ι ⊕ Unit) (ι ⊕ Unit) R) =
      Sum.elim (0 : ι → R) (fun _ : Unit ↦ 1) := by
    ext (j | ⟨⟩) <;> simp [u, vecMul, dotProduct, Fintype.sum_sum_type, Matrix.one_apply]
  simp only [Units.val_mul, ← vecMul_vecMul, hv₁, hv₂, hv₃]

/-- Over a ring of Bass stable range at most `s`, the elementary subgroup `elementarySubgroup m R`
acts transitively on unimodular rows whenever `s + 1 ≤ Fintype.card m`: every unimodular row can
be sent to any standard basis vector `Pi.single i₀ 1`. -/
theorem HasStableRangeLE.exists_vecMul_elementarySubgroup_eq_single {R m : Type*} [Ring R]
    [Fintype m] [DecidableEq m] {s : ℕ} (hR : HasStableRangeLE R s)
    (hm : s + 1 ≤ Fintype.card m) {a : m → R} (ha : Module.IsUnimodular R a) (i₀ : m) :
    ∃ e ∈ elementarySubgroup m R, a ᵥ* (e : Matrix m m R) = Pi.single i₀ 1 := by
  let φ := complSumUnitEquiv i₀
  let a' : {i : m // i ≠ i₀} → R := fun i ↦ a i.1
  let d : R := a i₀
  have ha' : Module.IsUnimodular R (Sum.elim a' (fun _ : Unit ↦ d)) := by
    have hcomp : Sum.elim a' (fun _ : Unit ↦ d) = (LinearEquiv.funCongrLeft R R φ) a := by
      ext (i | ⟨⟩) <;> rfl
    rw [hcomp, LinearEquiv.isUnimodular_apply_iff]; exact ha
  obtain ⟨c, hc⟩ := hR.exists_isUnimodular_add_mul (le_card_subtype_ne hm i₀) ha'
  obtain ⟨b, hb⟩ := TauCeti.Module.isUnimodular_pi_iff.mp hc
  let e₀ : GL ({i : m // i ≠ i₀} ⊕ Unit) R :=
    lowerBlockGL (Matrix.of fun (_ : Unit) j ↦ c j) *
      upperBlockGL (Matrix.of fun i (_ : Unit) ↦ b i * (1 - d)) *
      lowerBlockGL (Matrix.of fun (_ : Unit) j ↦ -(a' j + d * c j))
  have he₀ : e₀ ∈ elementarySubgroup ({i : m // i ≠ i₀} ⊕ Unit) R :=
    mul_mem (mul_mem (lowerBlockGL_mem_elementarySubgroup _)
      (upperBlockGL_mem_elementarySubgroup _)) (lowerBlockGL_mem_elementarySubgroup _)
  refine ⟨φ.reindexGL R e₀, by rw [← φ.map_reindexGL_elementarySubgroup]; exact ⟨e₀, he₀, rfl⟩, ?_⟩
  ext k
  obtain ⟨x, rfl⟩ := φ.surjective k
  have hmul : (a ᵥ* (φ.reindexGL R e₀ : Matrix m m R)) (φ x) =
      (Sum.elim a' (fun _ : Unit ↦ d) ᵥ* (e₀ : Matrix _ _ R)) x := by
    simp only [Equiv.coe_reindexGL, submatrix_apply, vecMul, dotProduct]
    rw [← φ.sum_comp]
    exact Fintype.sum_congr _ _ fun y ↦ by rcases y with i | ⟨⟩ <;> simp [φ, a', d]
  rw [hmul, vecMul_lower_upper_lower_eq_inr hb]
  rcases x with i | ⟨⟩
  · simp [φ, i.2]
  · simp [φ]

/-- If `a ⬝ᵥ b = 1` and `s + 1 ≤ Fintype.card m`, some `e ∈ elementarySubgroup m R` sends `b`
under `e⁻¹ *ᵥ ·` to `Pi.single i₀ 1`. -/
private theorem exists_elementarySubgroup_inv_mulVec_eq_single {R m : Type*} [Ring R]
    [Fintype m] [DecidableEq m] {s : ℕ} (hR : HasStableRangeLE R s)
    (hm : s + 1 ≤ Fintype.card m) {a b : m → R} (hab : a ⬝ᵥ b = 1) (i₀ : m) :
    ∃ e ∈ elementarySubgroup m R, (↑e⁻¹ : Matrix m m R) *ᵥ b = Pi.single i₀ 1 := by
  have ha : Module.IsUnimodular R a := TauCeti.Module.isUnimodular_pi_iff.mpr ⟨b, hab⟩
  obtain ⟨e₁, he₁, hae₁⟩ := hR.exists_vecMul_elementarySubgroup_eq_single hm ha i₀
  let b₁ : m → R := (↑e₁⁻¹ : Matrix m m R) *ᵥ b
  have hb₁0 : b₁ i₀ = 1 := by
    calc b₁ i₀ = Pi.single i₀ (1 : R) ⬝ᵥ b₁ := by simp
      _ = (a ᵥ* (e₁ : Matrix m m R)) ⬝ᵥ ((↑e₁⁻¹ : Matrix m m R) *ᵥ b) := by rw [← hae₁]
      _ = a ⬝ᵥ b := by rw [← dotProduct_mulVec, mulVec_mulVec, Units.mul_inv, one_mulVec]
      _ = 1 := hab
  let φ := complSumUnitEquiv i₀
  let e₂ : GL m R := φ.reindexGL R (upperBlockGL (Matrix.of fun i (_ : Unit) ↦ b₁ i.1))
  have he₂ : e₂ ∈ elementarySubgroup m R := by
    rw [← φ.map_reindexGL_elementarySubgroup]
    exact ⟨_, upperBlockGL_mem_elementarySubgroup _, rfl⟩
  refine ⟨e₁ * e₂, mul_mem he₁ he₂, ?_⟩
  have hinv : (↑(e₁ * e₂)⁻¹ : Matrix m m R) *ᵥ b = (↑e₂⁻¹ : Matrix m m R) *ᵥ b₁ := by
    simp [_root_.mul_inv_rev, mulVec_mulVec, b₁]
  rw [hinv]
  ext k
  obtain ⟨p, rfl⟩ := φ.surjective k
  have he₂inv : e₂⁻¹ = φ.reindexGL R (upperBlockGL (Matrix.of fun i (_ : Unit) ↦ -b₁ i.1)) := by
    rw [← map_inv, upperBlockGL_inv]; congr 2
  rw [he₂inv]
  simp only [Equiv.coe_reindexGL, submatrix_apply, mulVec, dotProduct]
  rw [← φ.sum_comp]
  simp only [φ.symm_apply_apply]
  rcases p with i | ⟨⟩
  · simp [φ, Fintype.sum_sum_type, Matrix.one_apply, hb₁0, i.2]
  · simp [φ, Fintype.sum_sum_type, hb₁0]

/-- Conjugating `1 - vecMulVec u v` by `e : GL m R` transforms `u` by `e⁻¹ *ᵥ ·` and `v` by
`· ᵥ* e`. -/
private theorem conj_one_sub_vecMulVec {R m : Type*} [Ring R] [Fintype m] [DecidableEq m]
    (e : GL m R) (u v : m → R) :
    (↑e⁻¹ : Matrix m m R) * (1 - vecMulVec u v) * (e : Matrix m m R) =
      1 - vecMulVec ((↑e⁻¹ : Matrix m m R) *ᵥ u) (v ᵥ* (e : Matrix m m R)) := by
  rw [Matrix.mul_sub, Matrix.mul_one, Matrix.sub_mul, Units.inv_mul]
  congr 1
  ext i j
  simp only [Matrix.mul_apply, vecMulVec_apply, mulVec, vecMul, dotProduct, Finset.sum_mul,
    Finset.mul_sum, mul_assoc]

/-- **Right rank-one unipotent lemma:** over a ring of stable range at most `s` with
`s + 1 ≤ Fintype.card m`, a rank-one unipotent matrix `1 - vecMulVec u v` with `v` unimodular and
`v ⬝ᵥ u = 0` belongs to `elementarySubgroup m R`. -/
theorem HasStableRangeLE.oneSubVecMulVecGL_mem_elementarySubgroup {R m : Type*} [Ring R]
    [Fintype m] [DecidableEq m] {s : ℕ} (hR : HasStableRangeLE R s)
    (hm : s + 1 ≤ Fintype.card m) {u v : m → R} (hv : Module.IsUnimodular R v)
    (hvu : v ⬝ᵥ u = 0) :
    oneSubVecMulVecGL (-1) u v (by simp [hvu]) ∈ elementarySubgroup m R := by
  obtain ⟨i₀⟩ := Fintype.card_pos_iff.mp (by omega : 0 < Fintype.card m)
  obtain ⟨e, he, hve⟩ := hR.exists_vecMul_elementarySubgroup_eq_single hm hv i₀
  set g := oneSubVecMulVecGL (-1) u v (by simp [hvu])
  let u' : m → R := (↑e⁻¹ : Matrix m m R) *ᵥ u
  have hu'0 : u' i₀ = 0 := by
    calc u' i₀ = Pi.single i₀ (1 : R) ⬝ᵥ u' := by simp
      _ = (v ᵥ* (e : Matrix m m R)) ⬝ᵥ ((↑e⁻¹ : Matrix m m R) *ᵥ u) := by rw [← hve]
      _ = v ⬝ᵥ u := by rw [← dotProduct_mulVec, mulVec_mulVec, Units.mul_inv, one_mulVec]
      _ = 0 := hvu
  let φ := complSumUnitEquiv i₀
  let U : GL ({i : m // i ≠ i₀} ⊕ Unit) R :=
    upperBlockGL (Matrix.of fun i (_ : Unit) ↦ -u' i.1)
  have hconj : e⁻¹ * g * e = φ.reindexGL R U := by
    refine Units.ext ?_
    calc ((e⁻¹ * g * e : GL m R) : Matrix m m R)
        = 1 - vecMulVec u' (Pi.single i₀ 1) := by
          rw [Units.val_mul, Units.val_mul, coe_oneSubVecMulVecGL, conj_one_sub_vecMulVec, hve]
      _ = (φ.reindexGL R U : Matrix m m R) := by
          ext p q
          obtain ⟨p, rfl⟩ := φ.surjective p
          obtain ⟨q, rfl⟩ := φ.surjective q
          simp only [Equiv.coe_reindexGL, submatrix_apply, φ.symm_apply_apply]
          rcases p with i | ⟨⟩ <;> rcases q with j | ⟨⟩
          · simp [φ, U, vecMulVec_apply, Matrix.one_apply, Subtype.ext_iff, j.2]
          · simp [φ, U, vecMulVec_apply, i.2]
          · simp [φ, U, vecMulVec_apply, j.2, j.2.symm, hu'0]
          · simp [φ, U, vecMulVec_apply, hu'0]
  have hU : φ.reindexGL R U ∈ elementarySubgroup m R := by
    rw [← φ.map_reindexGL_elementarySubgroup]
    exact ⟨U, upperBlockGL_mem_elementarySubgroup _, rfl⟩
  have hg : g = e * (e⁻¹ * g * e) * e⁻¹ := by group
  rw [hg, hconj]
  exact mul_mem (mul_mem he hU) (inv_mem he)

/-- **Left rank-one unipotent lemma:** if `a ⬝ᵥ b = 1` and `x ⬝ᵥ b = 0`, then for any `r : R` the
rank-one unipotent matrix `1 - vecMulVec (fun i ↦ b i * r) x` belongs to `elementarySubgroup m R`
whenever `s + 1 ≤ Fintype.card m`. -/
private theorem oneSubVecMulVecGL_mem_elementarySubgroup_of_dotProduct_eq_one {R m : Type*}
    [Ring R] [Fintype m] [DecidableEq m] {s : ℕ} (hR : HasStableRangeLE R s)
    (hm : s + 1 ≤ Fintype.card m) {a b x : m → R} (hab : a ⬝ᵥ b = 1) (hxb : x ⬝ᵥ b = 0)
    (r : R) (hr : (x ⬝ᵥ fun i ↦ b i * r) = (-1 : Rˣ) + 1) :
    oneSubVecMulVecGL (-1) (fun i ↦ b i * r) x hr ∈ elementarySubgroup m R := by
  obtain ⟨i₀⟩ := Fintype.card_pos_iff.mp (by omega : 0 < Fintype.card m)
  obtain ⟨e, he, heb⟩ := exists_elementarySubgroup_inv_mulVec_eq_single hR hm hab i₀
  set g := oneSubVecMulVecGL (-1) (fun i ↦ b i * r) x hr
  let x' : m → R := x ᵥ* (e : Matrix m m R)
  have hx'0 : x' i₀ = 0 := by
    calc x' i₀ = x' ⬝ᵥ Pi.single i₀ 1 := by simp
      _ = (x ᵥ* (e : Matrix m m R)) ⬝ᵥ ((↑e⁻¹ : Matrix m m R) *ᵥ b) := by rw [← heb]
      _ = x ⬝ᵥ b := by rw [← dotProduct_mulVec, mulVec_mulVec, Units.mul_inv, one_mulVec]
      _ = 0 := hxb
  let φ := complSumUnitEquiv i₀
  let L : GL ({i : m // i ≠ i₀} ⊕ Unit) R :=
    lowerBlockGL (Matrix.of fun (_ : Unit) j ↦ -r * x' j.1)
  have hconj : e⁻¹ * g * e = φ.reindexGL R L := by
    refine Units.ext ?_
    have hmulr : (↑e⁻¹ : Matrix m m R) *ᵥ (fun i ↦ b i * r) =
        fun i ↦ (Pi.single i₀ (1 : R) : m → R) i * r := by
      ext i
      calc ((↑e⁻¹ : Matrix m m R) *ᵥ fun k ↦ b k * r) i
          = (((↑e⁻¹ : Matrix m m R) *ᵥ b) i) * r := by
            simp only [mulVec, dotProduct, Finset.sum_mul, mul_assoc]
        _ = (Pi.single i₀ (1 : R) : m → R) i * r := by rw [heb]
    calc ((e⁻¹ * g * e : GL m R) : Matrix m m R)
        = 1 - vecMulVec (fun i ↦ (Pi.single i₀ (1 : R) : m → R) i * r) x' := by
          rw [Units.val_mul, Units.val_mul, coe_oneSubVecMulVecGL, conj_one_sub_vecMulVec, hmulr]
      _ = (φ.reindexGL R L : Matrix m m R) := by
          ext p q
          obtain ⟨p, rfl⟩ := φ.surjective p
          obtain ⟨q, rfl⟩ := φ.surjective q
          simp only [Equiv.coe_reindexGL, submatrix_apply, φ.symm_apply_apply]
          rcases p with i | ⟨⟩ <;> rcases q with j | ⟨⟩
          · simp [φ, L, vecMulVec_apply, Pi.single_apply, Matrix.one_apply, Subtype.ext_iff, i.2]
          · simp [φ, L, vecMulVec_apply, Pi.single_apply, i.2, hx'0]
          · simp [φ, L, vecMulVec_apply, j.2.symm]
          · simp [φ, L, vecMulVec_apply, hx'0]
  have hL : φ.reindexGL R L ∈ elementarySubgroup m R := by
    rw [← φ.map_reindexGL_elementarySubgroup]
    exact ⟨L, lowerBlockGL_mem_elementarySubgroup _, rfl⟩
  have hg : g = e * (e⁻¹ * g * e) * e⁻¹ := by group
  rw [hg, hconj]
  exact mul_mem (mul_mem he hL) (inv_mem he)

/-! ## Vaserstein's coset retraction and injective stability -/

/-- Upper-left `m × m` block extracted after clearing the bottom row of `A : GL (m ⊕ Unit) R`
using a right-inverse witness `b` for its bottom-left row. -/
private def vasersteinBlock {R m : Type*} [Ring R] [Fintype m] [DecidableEq m]
    (A : GL (m ⊕ Unit) R) (b : m → R)
    (hb : (fun j ↦ A (Sum.inr ()) (Sum.inl j)) ⬝ᵥ b = 1) : GL m R :=
  (A * clearLastRowFactor A b).toBlocks₁₁GL
    (toBlocks_mul_clearLastRowFactor hb).1 (toBlocks_mul_clearLastRowFactor hb).2

private theorem toBlocks₁₁_mul_of_toBlocks₂₁_eq_zero {R m : Type*} [Ring R] [Fintype m]
    (B C : Matrix (m ⊕ Unit) (m ⊕ Unit) R) (hC : C.toBlocks₂₁ = 0) :
    (B * C).toBlocks₁₁ = B.toBlocks₁₁ * C.toBlocks₁₁ := by
  conv_lhs => rw [← fromBlocks_toBlocks B, ← fromBlocks_toBlocks C, hC, fromBlocks_multiply]
  simp

/-- Comparing two `vasersteinBlock` extractions reduces to the `(1, 1)` block of the ratio of the
row-cleared matrices, where the outer factors `A₁` and `A₂` interact directly. -/
private theorem coe_vasersteinBlock_inv_mul {R m : Type*} [Ring R] [Fintype m] [DecidableEq m]
    {A₁ A₂ : GL (m ⊕ Unit) R} {b₁ b₂ : m → R}
    (hb₁ : (fun j ↦ A₁ (Sum.inr ()) (Sum.inl j)) ⬝ᵥ b₁ = 1)
    (hb₂ : (fun j ↦ A₂ (Sum.inr ()) (Sum.inl j)) ⬝ᵥ b₂ = 1) :
    (((vasersteinBlock A₁ b₁ hb₁)⁻¹ * vasersteinBlock A₂ b₂ hb₂ : GL m R) : Matrix m m R) =
      (((A₁ * clearLastRowFactor A₁ b₁)⁻¹ * (A₂ * clearLastRowFactor A₂ b₂) :
        GL (m ⊕ Unit) R) : Matrix (m ⊕ Unit) (m ⊕ Unit) R).toBlocks₁₁ := by
  dsimp only [vasersteinBlock]
  rw [Units.val_mul, GeneralLinearGroup.coe_toBlocks₁₁GL_inv,
    GeneralLinearGroup.coe_toBlocks₁₁GL]
  conv_rhs => rw [Units.val_mul]
  exact (toBlocks₁₁_mul_of_toBlocks₂₁_eq_zero _ _ (toBlocks_mul_clearLastRowFactor hb₂).1).symm

private theorem toBlocks₁₁_lower_upper_lower {R m : Type*} [Ring R] [Fintype m] [DecidableEq m]
    (a u : m → R) :
    ((lowerBlockGL (Matrix.of fun (_ : Unit) j ↦ a j) *
      upperBlockGL (Matrix.of fun i (_ : Unit) ↦ u i) *
      lowerBlockGL (Matrix.of fun (_ : Unit) j ↦ -a j) : GL (m ⊕ Unit) R) :
      Matrix (m ⊕ Unit) (m ⊕ Unit) R).toBlocks₁₁ = 1 - vecMulVec u a := by
  ext i j
  simp [Units.val_mul, fromBlocks_multiply, Matrix.mul_apply, vecMulVec_apply, sub_eq_add_neg]

/-- Independence of `vasersteinBlock` modulo `elementarySubgroup m R` from the witness `b`. -/
private theorem vasersteinBlock_inv_mul_mem {R m : Type*} [Ring R] [Fintype m] [DecidableEq m]
    {s : ℕ} (hR : HasStableRangeLE R s) (hm : s + 1 ≤ Fintype.card m)
    (A : GL (m ⊕ Unit) R) {b₁ b₂ : m → R}
    (hb₁ : (fun j ↦ A (Sum.inr ()) (Sum.inl j)) ⬝ᵥ b₁ = 1)
    (hb₂ : (fun j ↦ A (Sum.inr ()) (Sum.inl j)) ⬝ᵥ b₂ = 1) :
    (vasersteinBlock A b₁ hb₁)⁻¹ * vasersteinBlock A b₂ hb₂ ∈ elementarySubgroup m R := by
  let a : m → R := fun j ↦ A (Sum.inr ()) (Sum.inl j)
  let d : R := A (Sum.inr ()) (Sum.inr ())
  let u : m → R := fun i ↦ (b₂ i - b₁ i) * (1 - d)
  have ha : Module.IsUnimodular R a := TauCeti.Module.isUnimodular_pi_iff.mpr ⟨b₁, hb₁⟩
  have hau : a ⬝ᵥ u = 0 := by
    have hsum : a ⬝ᵥ u = (a ⬝ᵥ b₂ - a ⬝ᵥ b₁) * (1 - d) := by
      simp only [u, dotProduct, mul_sub, sub_mul, Finset.sum_sub_distrib, Finset.sum_mul, mul_assoc]
    rw [hsum, hb₁, hb₂, sub_self, zero_mul]
  have hmem := hR.oneSubVecMulVecGL_mem_elementarySubgroup hm ha hau
  suffices (vasersteinBlock A b₁ hb₁)⁻¹ * vasersteinBlock A b₂ hb₂ =
      oneSubVecMulVecGL (-1) u a (by simp [hau]) from this ▸ hmem
  refine Units.ext ?_
  rw [coe_vasersteinBlock_inv_mul hb₁ hb₂, coe_oneSubVecMulVecGL]
  have hmid : (A * clearLastRowFactor A b₁)⁻¹ * (A * clearLastRowFactor A b₂) =
      lowerBlockGL (Matrix.of fun (_ : Unit) j ↦ a j) *
        upperBlockGL (Matrix.of fun i (_ : Unit) ↦ u i) *
        lowerBlockGL (Matrix.of fun (_ : Unit) j ↦ -a j) := by
    have hu : upperBlockGL (-Matrix.of fun i (_ : Unit) ↦ b₁ i * (1 - d)) *
        upperBlockGL (Matrix.of fun i (_ : Unit) ↦ b₂ i * (1 - d)) =
        upperBlockGL (Matrix.of fun i (_ : Unit) ↦ u i) := by
      rw [← upperBlockGL_add]
      congr 1; ext i ⟨⟩; simp [u, sub_mul, neg_add_eq_sub]
    have hneg : (-Matrix.of fun (_ : Unit) j ↦ -A (Sum.inr ()) (Sum.inl j)) =
        Matrix.of fun (_ : Unit) j ↦ a j := by ext ⟨⟩ j; simp [a]
    calc (A * clearLastRowFactor A b₁)⁻¹ * (A * clearLastRowFactor A b₂)
        = (clearLastRowFactor A b₁)⁻¹ * clearLastRowFactor A b₂ := by group
      _ = lowerBlockGL (Matrix.of fun (_ : Unit) j ↦ a j) *
            (upperBlockGL (-Matrix.of fun i (_ : Unit) ↦ b₁ i * (1 - d)) *
              upperBlockGL (Matrix.of fun i (_ : Unit) ↦ b₂ i * (1 - d))) *
            lowerBlockGL (Matrix.of fun (_ : Unit) j ↦ -a j) := by
          simp only [clearLastRowFactor, _root_.mul_inv_rev, lowerBlockGL_inv, upperBlockGL_inv,
            hneg]
          dsimp only [a, d]; group
      _ = _ := by rw [hu]
  rw [hmid, toBlocks₁₁_lower_upper_lower]

/-- Partial Vaserstein map into left cosets `GL m R ⧸ elementarySubgroup m R` for matrices in
`GL (m ⊕ Unit) R` whose bottom-left row is unimodular. -/
private def vasersteinPsi {R m : Type*} [Ring R] [Fintype m] [DecidableEq m]
    (A : GL (m ⊕ Unit) R)
    (ha : Module.IsUnimodular R (fun j ↦ A (Sum.inr ()) (Sum.inl j))) :
    GL m R ⧸ elementarySubgroup m R :=
  have hex := TauCeti.Module.isUnimodular_pi_iff.mp ha
  QuotientGroup.mk (vasersteinBlock A hex.choose hex.choose_spec)

private theorem vasersteinPsi_congr {R m : Type*} [Ring R] [Fintype m] [DecidableEq m]
    {A₁ A₂ : GL (m ⊕ Unit) R} (h : A₁ = A₂)
    (ha₁ : Module.IsUnimodular R (fun j ↦ A₁ (Sum.inr ()) (Sum.inl j)))
    (ha₂ : Module.IsUnimodular R (fun j ↦ A₂ (Sum.inr ()) (Sum.inl j))) :
    vasersteinPsi A₁ ha₁ = vasersteinPsi A₂ ha₂ := by
  subst h; rfl

private theorem vasersteinPsi_eq_mk {R m : Type*} [Ring R] [Fintype m] [DecidableEq m]
    {s : ℕ} (hR : HasStableRangeLE R s) (hm : s + 1 ≤ Fintype.card m)
    (A : GL (m ⊕ Unit) R) (ha : Module.IsUnimodular R (fun j ↦ A (Sum.inr ()) (Sum.inl j)))
    {b : m → R} (hb : (fun j ↦ A (Sum.inr ()) (Sum.inl j)) ⬝ᵥ b = 1) :
    vasersteinPsi A ha = QuotientGroup.mk (vasersteinBlock A b hb) := by
  rw [vasersteinPsi, QuotientGroup.eq]
  exact vasersteinBlock_inv_mul_mem hR hm A _ hb

private theorem vasersteinPsi_fromBlocksGL_mul_lowerBlockGL {R m : Type*} [Ring R] [Fintype m]
    [DecidableEq m] {s : ℕ} (hR : HasStableRangeLE R s) (hm : s + 1 ≤ Fintype.card m)
    (g : GL m R) (c : m → R)
    (hc : Module.IsUnimodular R (fun j ↦
      (fromBlocksGL (g, (1 : GL Unit R)) *
        lowerBlockGL (Matrix.of fun (_ : Unit) k ↦ c k) : GL (m ⊕ Unit) R)
        (Sum.inr ()) (Sum.inl j))) :
    vasersteinPsi
      (fromBlocksGL (g, (1 : GL Unit R)) * lowerBlockGL (Matrix.of fun (_ : Unit) k ↦ c k)) hc =
      QuotientGroup.mk g := by
  obtain ⟨b, hb⟩ := TauCeti.Module.isUnimodular_pi_iff.mp hc
  rw [vasersteinPsi_eq_mk hR hm _ hc hb]
  congr 1; refine Units.ext ?_
  dsimp only [vasersteinBlock]
  rw [GeneralLinearGroup.coe_toBlocks₁₁GL]
  let A := fromBlocksGL (g, (1 : GL Unit R)) * lowerBlockGL (Matrix.of fun (_ : Unit) k ↦ c k)
  have hd : A (Sum.inr ()) (Sum.inr ()) = 1 := by
    simp [A, Units.val_mul, Matrix.mul_apply, Fintype.sum_sum_type]
  have ha : ∀ j, A (Sum.inr ()) (Sum.inl j) = c j := fun j ↦ by
    simp [A, Units.val_mul, Matrix.mul_apply, Fintype.sum_sum_type]
  have hclear : A * clearLastRowFactor A b = fromBlocksGL (g, (1 : GL Unit R)) := by
    have hu : upperBlockGL (Matrix.of fun i (_ : Unit) ↦ b i * (1 - A (Sum.inr ()) (Sum.inr ()))) =
        1 := by
      rw [hd, sub_self]; convert upperBlockGL_zero (A := R) (m := m) (k := Unit)
      ext i ⟨⟩; simp
    have hl : lowerBlockGL (Matrix.of fun (_ : Unit) k ↦ c k) *
        lowerBlockGL (Matrix.of fun (_ : Unit) j ↦ -A (Sum.inr ()) (Sum.inl j)) = 1 := by
      rw [← lowerBlockGL_add]; convert lowerBlockGL_zero (A := R) (m := m) (k := Unit)
      ext ⟨⟩ j; simp [ha j]
    rw [clearLastRowFactor, hu, one_mul]; dsimp only [A]; rw [mul_assoc, hl, mul_one]
  dsimp only [A] at hclear
  rw [hclear, coe_fromBlocksGL]; ext i j; simp

/-- Right-invariance of `vasersteinPsi` under upper block unipotent matrices. -/
private theorem vasersteinPsi_mul_upperBlockGL {R m : Type*} [Ring R] [Fintype m] [DecidableEq m]
    {s : ℕ} (hR : HasStableRangeLE R s) (hm : s + 1 ≤ Fintype.card m)
    (A : GL (m ⊕ Unit) R) (y : m → R)
    (ha : Module.IsUnimodular R (fun j ↦ A (Sum.inr ()) (Sum.inl j)))
    (ha₂ : Module.IsUnimodular R (fun j ↦
      (A * upperBlockGL (Matrix.of fun i (_ : Unit) ↦ y i) : GL (m ⊕ Unit) R)
        (Sum.inr ()) (Sum.inl j))) :
    vasersteinPsi (A * upperBlockGL (Matrix.of fun i (_ : Unit) ↦ y i)) ha₂ =
      vasersteinPsi A ha := by
  obtain ⟨b, hb⟩ := TauCeti.Module.isUnimodular_pi_iff.mp ha
  set U := upperBlockGL (Matrix.of fun i (_ : Unit) ↦ y i)
  let a : m → R := fun j ↦ A (Sum.inr ()) (Sum.inl j)
  let d : R := A (Sum.inr ()) (Sum.inr ())
  have hab : a ⬝ᵥ b = 1 := hb
  have hrow : (fun j ↦ (A * U : GL (m ⊕ Unit) R) (Sum.inr ()) (Sum.inl j)) = a := by
    ext j; simp [U, a, Units.val_mul, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply]
  have hb₂ : (fun j ↦ (A * U : GL (m ⊕ Unit) R) (Sum.inr ()) (Sum.inl j)) ⬝ᵥ b = 1 :=
    hrow.symm ▸ hab
  rw [vasersteinPsi_eq_mk hR hm _ ha₂ hb₂, vasersteinPsi_eq_mk hR hm A ha hb, eq_comm,
    QuotientGroup.eq]
  have hd₂ : (A * U : GL (m ⊕ Unit) R) (Sum.inr ()) (Sum.inr ()) = a ⬝ᵥ y + d := by
    simp [U, a, d, Units.val_mul, Matrix.mul_apply, Fintype.sum_sum_type, dotProduct]
  let w : m → R := fun i ↦ y i - b i * (a ⬝ᵥ y)
  have haw : a ⬝ᵥ w = 0 := by
    have hdot : (a ⬝ᵥ fun i ↦ b i * (a ⬝ᵥ y)) = (a ⬝ᵥ b) * (a ⬝ᵥ y) := by
      simp only [dotProduct, Finset.sum_mul, mul_assoc]
    calc a ⬝ᵥ w = a ⬝ᵥ y - (a ⬝ᵥ fun i ↦ b i * (a ⬝ᵥ y)) := by
          simp [w, dotProduct, mul_sub, Finset.sum_sub_distrib]
      _ = 0 := by rw [hdot, hab, one_mul, sub_self]
  suffices (vasersteinBlock A b hb)⁻¹ * vasersteinBlock (A * U) b hb₂ =
      oneSubVecMulVecGL (-1) w a (by simp [haw]) from
    this ▸ hR.oneSubVecMulVecGL_mem_elementarySubgroup hm ha haw
  refine Units.ext ?_
  rw [coe_vasersteinBlock_inv_mul hb hb₂, coe_oneSubVecMulVecGL]
  have hmid : (A * clearLastRowFactor A b)⁻¹ * (A * U * clearLastRowFactor (A * U) b) =
      lowerBlockGL (Matrix.of fun (_ : Unit) j ↦ a j) *
        upperBlockGL (Matrix.of fun i (_ : Unit) ↦ w i) *
        lowerBlockGL (Matrix.of fun (_ : Unit) j ↦ -a j) := by
    have hu : (upperBlockGL (Matrix.of fun i (_ : Unit) ↦ b i * (1 - d)))⁻¹ * U *
        upperBlockGL (Matrix.of fun i (_ : Unit) ↦
          b i * (1 - (A * U : GL (m ⊕ Unit) R) (Sum.inr ()) (Sum.inr ()))) =
        upperBlockGL (Matrix.of fun i (_ : Unit) ↦ w i) := by
      rw [upperBlockGL_inv, ← upperBlockGL_add, ← upperBlockGL_add]
      congr 1; ext i ⟨⟩; rw [hd₂]; simp [w, mul_sub, mul_add]; abel
    have hl : Matrix.of (fun (_ : Unit) j ↦ -(A * U : GL (m ⊕ Unit) R) (Sum.inr ()) (Sum.inl j)) =
        Matrix.of (fun (_ : Unit) j ↦ -a j) := by ext ⟨⟩ j; exact congrArg Neg.neg (congrFun hrow j)
    have hneg : (-Matrix.of fun (_ : Unit) j ↦ -A (Sum.inr ()) (Sum.inl j)) =
        Matrix.of fun (_ : Unit) j ↦ a j := by ext ⟨⟩ j; simp [a]
    calc (A * clearLastRowFactor A b)⁻¹ * (A * U * clearLastRowFactor (A * U) b)
        = (clearLastRowFactor A b)⁻¹ * U * clearLastRowFactor (A * U) b := by group
      _ = lowerBlockGL (Matrix.of fun (_ : Unit) j ↦ a j) *
            ((upperBlockGL (Matrix.of fun i (_ : Unit) ↦ b i * (1 - d)))⁻¹ * U *
              upperBlockGL (Matrix.of fun i (_ : Unit) ↦
                b i * (1 - (A * U : GL (m ⊕ Unit) R) (Sum.inr ()) (Sum.inr ())))) *
            lowerBlockGL (Matrix.of fun (_ : Unit) j ↦ -a j) := by
          simp only [clearLastRowFactor, _root_.mul_inv_rev, lowerBlockGL_inv, hl, hneg]
          dsimp only [d]; group
      _ = _ := by rw [hu]
  rw [hmid, toBlocks₁₁_lower_upper_lower]

/-- Right-invariance of `vasersteinPsi` under `fromBlocksGL (e, 1)` for `e ∈ E m R`. -/
private theorem vasersteinPsi_mul_fromBlocksGL {R m : Type*} [Ring R] [Fintype m] [DecidableEq m]
    {s : ℕ} (hR : HasStableRangeLE R s) (hm : s + 1 ≤ Fintype.card m)
    (A : GL (m ⊕ Unit) R) {e : GL m R} (he : e ∈ elementarySubgroup m R)
    (ha : Module.IsUnimodular R (fun j ↦ A (Sum.inr ()) (Sum.inl j)))
    (ha₂ : Module.IsUnimodular R (fun j ↦
      (A * fromBlocksGL (e, (1 : GL Unit R)) : GL (m ⊕ Unit) R) (Sum.inr ()) (Sum.inl j))) :
    vasersteinPsi (A * fromBlocksGL (e, (1 : GL Unit R))) ha₂ = vasersteinPsi A ha := by
  obtain ⟨b, hb⟩ := TauCeti.Module.isUnimodular_pi_iff.mp ha
  set E := fromBlocksGL (e, (1 : GL Unit R))
  have hrow := mul_fromBlocksGL_inr_inl A e
  have hd₂ : (A * E : GL (m ⊕ Unit) R) (Sum.inr ()) (Sum.inr ()) =
      A (Sum.inr ()) (Sum.inr ()) := by
    simp [E, Units.val_mul, Matrix.mul_apply, Fintype.sum_sum_type]
  let b₂ : m → R := (↑e⁻¹ : Matrix m m R) *ᵥ b
  have hb₂ : (fun j ↦ (A * E : GL (m ⊕ Unit) R) (Sum.inr ()) (Sum.inl j)) ⬝ᵥ b₂ = 1 := by
    rw [hrow, ← dotProduct_mulVec, mulVec_mulVec, Units.mul_inv, one_mulVec]
    exact hb
  rw [vasersteinPsi_eq_mk hR hm _ ha₂ hb₂, vasersteinPsi_eq_mk hR hm A ha hb, eq_comm,
    QuotientGroup.eq]
  suffices (vasersteinBlock A b hb)⁻¹ * vasersteinBlock (A * E) b₂ hb₂ = e from this ▸ he
  refine Units.ext ?_
  rw [coe_vasersteinBlock_inv_mul hb hb₂]
  have hcomm : E * clearLastRowFactor (A * E) b₂ = clearLastRowFactor A b * E := by
    refine Units.ext ?_
    have h12 : (e : Matrix m m R) *
        Matrix.of (fun i (_ : Unit) ↦ b₂ i * (1 - A (Sum.inr ()) (Sum.inr ()))) =
        Matrix.of (fun i (_ : Unit) ↦ b i * (1 - A (Sum.inr ()) (Sum.inr ()))) := by
      ext i ⟨⟩
      calc (∑ x : m, (e : Matrix m m R) i x * (b₂ x * (1 - A (Sum.inr ()) (Sum.inr ()))))
          = ((e : Matrix m m R) *ᵥ ((↑e⁻¹ : Matrix m m R) *ᵥ b)) i *
              (1 - A (Sum.inr ()) (Sum.inr ())) := by
            simp only [b₂, mulVec, dotProduct, Finset.sum_mul, mul_assoc]
        _ = b i * (1 - A (Sum.inr ()) (Sum.inr ())) := by
            rw [mulVec_mulVec, Units.mul_inv, one_mulVec]
    have h21 : Matrix.of (fun (_ : Unit) j ↦ -(A * E : GL (m ⊕ Unit) R) (Sum.inr ()) (Sum.inl j)) =
        Matrix.of (fun (_ : Unit) j ↦ -A (Sum.inr ()) (Sum.inl j)) * (e : Matrix m m R) := by
      ext ⟨⟩ j
      rw [Matrix.of_apply, congrFun hrow j]
      simp [vecMul, dotProduct, Matrix.mul_apply, Finset.sum_neg_distrib]
    rw [clearLastRowFactor, clearLastRowFactor, hd₂, h21]
    dsimp only [E]
    simp only [Units.val_mul, coe_fromBlocksGL, coe_upperBlockGL, coe_lowerBlockGL,
      fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, Matrix.mul_one,
      Matrix.one_mul, Units.val_one, Matrix.mul_add, Matrix.add_mul, ← Matrix.mul_assoc, h12]
  have hmid : (A * clearLastRowFactor A b)⁻¹ * (A * E * clearLastRowFactor (A * E) b₂) = E := by
    calc (A * clearLastRowFactor A b)⁻¹ * (A * E * clearLastRowFactor (A * E) b₂)
        = (clearLastRowFactor A b)⁻¹ * (E * clearLastRowFactor (A * E) b₂) := by group
      _ = (clearLastRowFactor A b)⁻¹ * (clearLastRowFactor A b * E) := by rw [hcomm]
      _ = E := by group
  rw [hmid, coe_fromBlocksGL]; ext i j; simp

private theorem toBlocks₁₁_conj_lowerBlockGL_of_dotProduct_eq_zero {R m : Type*} [Ring R]
    [Fintype m] [DecidableEq m] (a₁ a₂ u x : m → R) (hxu : x ⬝ᵥ u = 0) :
    ((lowerBlockGL (Matrix.of fun (_ : Unit) j ↦ a₁ j) *
      upperBlockGL (Matrix.of fun i (_ : Unit) ↦ -u i) *
      lowerBlockGL (Matrix.of fun (_ : Unit) j ↦ x j) *
      upperBlockGL (Matrix.of fun i (_ : Unit) ↦ u i) *
      lowerBlockGL (Matrix.of fun (_ : Unit) j ↦ a₂ j) : GL (m ⊕ Unit) R) :
      Matrix (m ⊕ Unit) (m ⊕ Unit) R).toBlocks₁₁ = 1 - vecMulVec u x := by
  set U₀ : Matrix m Unit R := Matrix.of fun i _ ↦ u i
  set X₀ : Matrix Unit m R := Matrix.of fun _ j ↦ x j
  have hXU : X₀ * U₀ = 0 := by
    ext ⟨⟩ ⟨⟩; simpa [X₀, U₀, Matrix.mul_apply, dotProduct] using hxu
  have hmid : ((upperBlockGL (Matrix.of fun i (_ : Unit) ↦ -u i) *
      lowerBlockGL X₀ * upperBlockGL U₀ : GL (m ⊕ Unit) R) :
      Matrix (m ⊕ Unit) (m ⊕ Unit) R) = fromBlocks (1 - U₀ * X₀) 0 X₀ 1 := by
    have hneg : Matrix.of (fun i (_ : Unit) ↦ -u i) = -U₀ := by ext i ⟨⟩; rfl
    have h11 : (1 : Matrix m m R) + -(U₀ * X₀) = 1 - U₀ * X₀ := (sub_eq_add_neg _ _).symm
    have h12 : ((1 : Matrix m m R) + -(U₀ * X₀)) * U₀ + -U₀ = 0 := by
      rw [Matrix.add_mul, Matrix.one_mul, Matrix.neg_mul, Matrix.mul_assoc, hXU, Matrix.mul_zero,
        neg_zero, add_zero, add_neg_cancel]
    rw [Units.val_mul, Units.val_mul, hneg, coe_upperBlockGL, coe_lowerBlockGL, coe_upperBlockGL]
    simp only [fromBlocks_multiply, Matrix.mul_zero, add_zero, zero_add, Matrix.mul_one,
      Matrix.one_mul, Matrix.neg_mul, hXU]
    rw [h12, h11]
  have hassoc : lowerBlockGL (Matrix.of fun (_ : Unit) j ↦ a₁ j) *
      upperBlockGL (Matrix.of fun i (_ : Unit) ↦ -u i) * lowerBlockGL X₀ * upperBlockGL U₀ *
      lowerBlockGL (Matrix.of fun (_ : Unit) j ↦ a₂ j) =
      lowerBlockGL (Matrix.of fun (_ : Unit) j ↦ a₁ j) *
        (upperBlockGL (Matrix.of fun i (_ : Unit) ↦ -u i) * lowerBlockGL X₀ * upperBlockGL U₀) *
        lowerBlockGL (Matrix.of fun (_ : Unit) j ↦ a₂ j) := by group
  rw [hassoc, Units.val_mul, Units.val_mul, hmid, coe_lowerBlockGL, coe_lowerBlockGL]
  ext i j; simp [fromBlocks_multiply, U₀, X₀, Matrix.mul_apply, vecMulVec_apply]

/-- Orthogonal case of right-invariance under `lowerBlockGL`: when `a ⬝ᵥ b = 1` and `x ⬝ᵥ b = 0`. -/
private theorem vasersteinPsi_mul_lowerBlockGL_of_dotProduct_eq_zero {R m : Type*} [Ring R]
    [Fintype m] [DecidableEq m] {s : ℕ} (hR : HasStableRangeLE R s) (hm : s + 1 ≤ Fintype.card m)
    (A : GL (m ⊕ Unit) R) {b x : m → R}
    (hb : (fun j ↦ A (Sum.inr ()) (Sum.inl j)) ⬝ᵥ b = 1) (hxb : x ⬝ᵥ b = 0)
    (ha : Module.IsUnimodular R (fun j ↦ A (Sum.inr ()) (Sum.inl j)))
    (ha₂ : Module.IsUnimodular R (fun j ↦
      (A * lowerBlockGL (Matrix.of fun (_ : Unit) k ↦ x k) : GL (m ⊕ Unit) R)
        (Sum.inr ()) (Sum.inl j))) :
    vasersteinPsi (A * lowerBlockGL (Matrix.of fun (_ : Unit) k ↦ x k)) ha₂ =
      vasersteinPsi A ha := by
  set L := lowerBlockGL (Matrix.of fun (_ : Unit) k ↦ x k)
  let a : m → R := fun j ↦ A (Sum.inr ()) (Sum.inl j)
  let d : R := A (Sum.inr ()) (Sum.inr ())
  have hb₂ : (fun j ↦ (A * L : GL (m ⊕ Unit) R) (Sum.inr ()) (Sum.inl j)) ⬝ᵥ b = 1 := by
    have hrow : (fun j ↦ (A * L : GL (m ⊕ Unit) R) (Sum.inr ()) (Sum.inl j)) =
        a + fun j ↦ d * x j := funext (mul_lowerBlockGL_inr_inl A x)
    have hdot : ((fun j ↦ d * x j) ⬝ᵥ b) = d * (x ⬝ᵥ b) := by
      simp only [dotProduct, Finset.mul_sum, mul_assoc]
    rw [hrow, add_dotProduct, hb, hdot, hxb, mul_zero, add_zero]
  have hd₂ : (A * L : GL (m ⊕ Unit) R) (Sum.inr ()) (Sum.inr ()) = d := by
    simp [L, d, Units.val_mul, Matrix.mul_apply, Fintype.sum_sum_type]
  rw [vasersteinPsi_eq_mk hR hm _ ha₂ hb₂, vasersteinPsi_eq_mk hR hm A ha hb, eq_comm,
    QuotientGroup.eq]
  let u : m → R := fun i ↦ b i * (1 - d)
  have hxu : x ⬝ᵥ u = 0 := by
    have hdot : x ⬝ᵥ u = (x ⬝ᵥ b) * (1 - d) := by
      simp only [u, dotProduct, Finset.sum_mul, mul_assoc]
    rw [hdot, hxb, zero_mul]
  have hmem := oneSubVecMulVecGL_mem_elementarySubgroup_of_dotProduct_eq_one hR hm hb hxb (1 - d)
    (by simp [u, hxu])
  suffices (vasersteinBlock A b hb)⁻¹ * vasersteinBlock (A * L) b hb₂ =
      oneSubVecMulVecGL (-1) u x (by simp [hxu]) from this ▸ hmem
  refine Units.ext ?_
  rw [coe_vasersteinBlock_inv_mul hb hb₂, coe_oneSubVecMulVecGL]
  have hmid : (A * clearLastRowFactor A b)⁻¹ * (A * L * clearLastRowFactor (A * L) b) =
      lowerBlockGL (Matrix.of fun (_ : Unit) j ↦ a j) *
        upperBlockGL (Matrix.of fun i (_ : Unit) ↦ -u i) *
        L * upperBlockGL (Matrix.of fun i (_ : Unit) ↦ u i) *
        lowerBlockGL (Matrix.of fun (_ : Unit) j ↦
          -(A * L : GL (m ⊕ Unit) R) (Sum.inr ()) (Sum.inl j)) := by
    have hneg : (-Matrix.of fun (_ : Unit) j ↦ -A (Sum.inr ()) (Sum.inl j)) =
        Matrix.of fun (_ : Unit) j ↦ a j := by ext ⟨⟩ j; simp [a]
    have hnegu : (-Matrix.of fun i (_ : Unit) ↦ b i * (1 - A (Sum.inr ()) (Sum.inr ()))) =
        Matrix.of fun i (_ : Unit) ↦ -u i := by ext i ⟨⟩; rfl
    calc (A * clearLastRowFactor A b)⁻¹ * (A * L * clearLastRowFactor (A * L) b)
        = (clearLastRowFactor A b)⁻¹ * L * clearLastRowFactor (A * L) b := by group
      _ = _ := by
          simp only [clearLastRowFactor, _root_.mul_inv_rev, lowerBlockGL_inv, upperBlockGL_inv,
            hd₂, hneg, hnegu]
          dsimp only [u, d]; group
  rw [hmid, toBlocks₁₁_conj_lowerBlockGL_of_dotProduct_eq_zero _ _ u x hxu]

private theorem mul_lowerBlockGL_mul_fromBlocksGL {R m : Type*} [Ring R] [Fintype m]
    [DecidableEq m] (A : GL (m ⊕ Unit) R) (x : m → R) (e : GL m R) :
    A * lowerBlockGL (Matrix.of fun (_ : Unit) k ↦ x k) * fromBlocksGL (e, (1 : GL Unit R)) =
      A * fromBlocksGL (e, (1 : GL Unit R)) *
        lowerBlockGL (Matrix.of fun (_ : Unit) k ↦ (x ᵥ* (e : Matrix m m R)) k) := by
  have hcomm : lowerBlockGL (Matrix.of fun (_ : Unit) k ↦ x k) * fromBlocksGL (e, (1 : GL Unit R)) =
      fromBlocksGL (e, (1 : GL Unit R)) *
        lowerBlockGL (Matrix.of fun (_ : Unit) k ↦ (x ᵥ* (e : Matrix m m R)) k) := by
    refine Units.ext ?_
    rw [Units.val_mul, Units.val_mul, coe_lowerBlockGL, coe_fromBlocksGL, coe_lowerBlockGL]
    simp only [fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add,
      Matrix.one_mul, Matrix.mul_one, Units.val_one]
    rfl
  rw [mul_assoc, hcomm, ← mul_assoc]

private theorem vecMul_reindexGL_complSumUnitEquiv_lowerBlockGL {R m : Type*} [Ring R]
    [Fintype m] [DecidableEq m] (i₀ : m) (c : {i : m // i ≠ i₀} → R) (v : m → R) :
    (∀ i : {i : m // i ≠ i₀},
      (v ᵥ* ((complSumUnitEquiv i₀).reindexGL R
        (lowerBlockGL (Matrix.of fun (_ : Unit) j ↦ c j)) : Matrix m m R)) i.1 =
        v i.1 + v i₀ * c i) ∧
      (v ᵥ* ((complSumUnitEquiv i₀).reindexGL R
        (lowerBlockGL (Matrix.of fun (_ : Unit) j ↦ c j)) : Matrix m m R)) i₀ = v i₀ := by
  let φ := complSumUnitEquiv i₀
  constructor
  · intro i
    simp only [Equiv.coe_reindexGL, submatrix_apply, vecMul, dotProduct]
    rw [← φ.sum_comp]; simp [φ, Fintype.sum_sum_type, Matrix.one_apply]
  · simp only [Equiv.coe_reindexGL, submatrix_apply, vecMul, dotProduct]
    rw [← φ.sum_comp]; simp [φ, Fintype.sum_sum_type]

private theorem dotProduct_ClearedPivot_eq_one {R m : Type*} [Ring R] [Fintype m] [DecidableEq m]
    (A : GL (m ⊕ Unit) R) (i₀ : m) (x : m → R) (c b' : {i : m // i ≠ i₀} → R)
    (hb' : (fun i : {i : m // i ≠ i₀} ↦
      (A * lowerBlockGL (Matrix.of fun (_ : Unit) k ↦ x k) : GL (m ⊕ Unit) R)
          (Sum.inr ()) (Sum.inl i.1) +
        (A * lowerBlockGL (Matrix.of fun (_ : Unit) k ↦ x k) : GL (m ⊕ Unit) R)
          (Sum.inr ()) (Sum.inl i₀) * c i) ⬝ᵥ b' = 1) :
    let e₂ := (complSumUnitEquiv i₀).reindexGL R (lowerBlockGL (Matrix.of fun (_ : Unit) i ↦ c i))
    let z : m → R := fun k ↦ if k = i₀ then 0 else (x ᵥ* (e₂ : Matrix m m R)) k
    let Az :=
      A * fromBlocksGL (e₂, (1 : GL Unit R)) * lowerBlockGL (Matrix.of fun (_ : Unit) k ↦ z k)
    (fun j ↦ Az (Sum.inr ()) (Sum.inl j)) ⬝ᵥ (fun k ↦ if hk : k = i₀ then 0 else b' ⟨k, hk⟩) =
      1 := by
  intro e₂ z Az
  let φ := complSumUnitEquiv i₀
  have hd' : (A * fromBlocksGL (e₂, (1 : GL Unit R)) : GL (m ⊕ Unit) R) (Sum.inr ()) (Sum.inr ()) =
      A (Sum.inr ()) (Sum.inr ()) := by
    simp [Units.val_mul, Matrix.mul_apply, Fintype.sum_sum_type]
  have hAz_i : ∀ i : {i : m // i ≠ i₀}, Az (Sum.inr ()) (Sum.inl i.1) =
      (A * lowerBlockGL (Matrix.of fun (_ : Unit) k ↦ x k) : GL (m ⊕ Unit) R)
          (Sum.inr ()) (Sum.inl i.1) +
        (A * lowerBlockGL (Matrix.of fun (_ : Unit) k ↦ x k) : GL (m ⊕ Unit) R)
          (Sum.inr ()) (Sum.inl i₀) * c i := by
    intro i
    have hAz := mul_lowerBlockGL_inr_inl (A * fromBlocksGL (e₂, (1 : GL Unit R))) z i.1
    have hzi : z i.1 = (x ᵥ* (e₂ : Matrix m m R)) i.1 := by simp [z, i.2]
    rw [hAz, hd', hzi, congrFun (mul_fromBlocksGL_inr_inl A e₂) i.1,
      (vecMul_reindexGL_complSumUnitEquiv_lowerBlockGL i₀ c _).1 i,
      (vecMul_reindexGL_complSumUnitEquiv_lowerBlockGL i₀ c x).1 i,
      mul_lowerBlockGL_inr_inl A x i.1, mul_lowerBlockGL_inr_inl A x i₀]
    simp only [mul_add, add_mul, mul_assoc]; abel
  calc (fun j ↦ Az (Sum.inr ()) (Sum.inl j)) ⬝ᵥ (fun k ↦ if hk : k = i₀ then 0 else b' ⟨k, hk⟩)
      = ∑ p : {i : m // i ≠ i₀} ⊕ Unit,
          Az (Sum.inr ()) (Sum.inl (φ p)) *
            (if hk : φ p = i₀ then 0 else b' ⟨φ p, hk⟩) := by
        simp only [dotProduct]; rw [← φ.sum_comp]
    _ = _ ⬝ᵥ b' := by
        simp only [φ, Fintype.sum_sum_type, complSumUnitEquiv_inl, complSumUnitEquiv_inr,
          dite_true, mul_zero, Fintype.univ_punit, Finset.sum_singleton, add_zero, dotProduct]
        exact Fintype.sum_congr _ _ fun i ↦ by simp [i.2, hAz_i i]
    _ = 1 := hb'

/-- Right-invariance under `lowerBlockGL` when the bottom-left row of `A` is `Pi.single i₀ 1`. -/
private theorem vasersteinPsi_mul_lowerBlockGL_of_single {R m : Type*} [Ring R] [Fintype m]
    [DecidableEq m] {s : ℕ} (hR : HasStableRangeLE R s) (hm : s + 1 ≤ Fintype.card m)
    (A : GL (m ⊕ Unit) R) (i₀ : m) (x : m → R)
    (ha0 : (fun j ↦ A (Sum.inr ()) (Sum.inl j)) = Pi.single i₀ 1)
    (ha : Module.IsUnimodular R (fun j ↦ A (Sum.inr ()) (Sum.inl j)))
    (ha₂ : Module.IsUnimodular R (fun j ↦
      (A * lowerBlockGL (Matrix.of fun (_ : Unit) k ↦ x k) : GL (m ⊕ Unit) R)
        (Sum.inr ()) (Sum.inl j))) :
    vasersteinPsi (A * lowerBlockGL (Matrix.of fun (_ : Unit) k ↦ x k)) ha₂ =
      vasersteinPsi A ha := by
  let φ := complSumUnitEquiv i₀
  set Lx := A * lowerBlockGL (Matrix.of fun (_ : Unit) k ↦ x k)
  let w : m → R := fun j ↦ Lx (Sum.inr ()) (Sum.inl j)
  have hw_unimod : Module.IsUnimodular R
      (Sum.elim (fun i : {i : m // i ≠ i₀} ↦ w i.1) (fun _ : Unit ↦ w i₀)) := by
    have hcomp : Sum.elim (fun i : {i : m // i ≠ i₀} ↦ w i.1) (fun _ : Unit ↦ w i₀) =
        (LinearEquiv.funCongrLeft R R φ) w := by ext (i | ⟨⟩) <;> rfl
    rw [hcomp, LinearEquiv.isUnimodular_apply_iff]; exact ha₂
  obtain ⟨c, hc⟩ := hR.exists_isUnimodular_add_mul (le_card_subtype_ne hm i₀) hw_unimod
  obtain ⟨b', hb'⟩ := TauCeti.Module.isUnimodular_pi_iff.mp hc
  let e₂ : GL m R := φ.reindexGL R (lowerBlockGL (Matrix.of fun (_ : Unit) i ↦ c i))
  have he₂ : e₂ ∈ elementarySubgroup m R := by
    rw [← φ.map_reindexGL_elementarySubgroup]; exact ⟨_, lowerBlockGL_mem_elementarySubgroup _, rfl⟩
  let A' := A * fromBlocksGL (e₂, (1 : GL Unit R))
  let x' : m → R := x ᵥ* (e₂ : Matrix m m R)
  have ha'i₀ : A' (Sum.inr ()) (Sum.inl i₀) = 1 := by
    rw [congrFun (mul_fromBlocksGL_inr_inl A e₂) i₀,
      (vecMul_reindexGL_complSumUnitEquiv_lowerBlockGL i₀ c _).2, congrFun ha0 i₀,
      Pi.single_eq_same]
  have ha'_unimod : Module.IsUnimodular R (fun j ↦ A' (Sum.inr ()) (Sum.inl j)) := by
    rw [mul_fromBlocksGL_inr_inl, e₂.isUnimodular_vecMul_iff]; exact ha
  let z : m → R := fun k ↦ if k = i₀ then 0 else x' k
  let y : m → R := Pi.single i₀ (x' i₀)
  have hzy : Matrix.of (fun (_ : Unit) k ↦ z k) + Matrix.of (fun (_ : Unit) k ↦ y k) =
      Matrix.of (fun (_ : Unit) k ↦ x' k) := by ext ⟨⟩ k; by_cases hk : k = i₀ <;> simp [z, y, hk]
  let Az := A' * lowerBlockGL (Matrix.of fun (_ : Unit) k ↦ z k)
  let b₂ : m → R := fun k ↦ if hk : k = i₀ then 0 else b' ⟨k, hk⟩
  have hb₂ : (fun j ↦ Az (Sum.inr ()) (Sum.inl j)) ⬝ᵥ b₂ = 1 :=
    dotProduct_ClearedPivot_eq_one A i₀ x c b' hb'
  have hAz_unimod : Module.IsUnimodular R (fun j ↦ Az (Sum.inr ()) (Sum.inl j)) :=
    TauCeti.Module.isUnimodular_pi_iff.mpr ⟨b₂, hb₂⟩
  have hAx'_eq : Lx * fromBlocksGL (e₂, (1 : GL Unit R)) =
      Az * lowerBlockGL (Matrix.of fun (_ : Unit) k ↦ y k) := by
    rw [mul_lowerBlockGL_mul_fromBlocksGL, ← hzy, lowerBlockGL_add, ← mul_assoc]
  have hAx'_unimod : Module.IsUnimodular R (fun j ↦
      (Az * lowerBlockGL (Matrix.of fun (_ : Unit) k ↦ y k) : GL (m ⊕ Unit) R)
        (Sum.inr ()) (Sum.inl j)) := by
    rw [← hAx'_eq, mul_fromBlocksGL_inr_inl, e₂.isUnimodular_vecMul_iff]; exact ha₂
  have heq1 : vasersteinPsi Lx ha₂ =
      vasersteinPsi (Az * lowerBlockGL (Matrix.of fun (_ : Unit) k ↦ y k)) hAx'_unimod :=
    (vasersteinPsi_mul_fromBlocksGL hR hm _ he₂ ha₂ (hAx'_eq.symm ▸ hAx'_unimod)).symm.trans
      (vasersteinPsi_congr hAx'_eq (hAx'_eq.symm ▸ hAx'_unimod) hAx'_unimod)
  rw [heq1, vasersteinPsi_mul_lowerBlockGL_of_dotProduct_eq_zero hR hm Az hb₂ (by simp [y, b₂])
      hAz_unimod hAx'_unimod,
    vasersteinPsi_mul_lowerBlockGL_of_dotProduct_eq_zero hR hm A' (b := Pi.single i₀ 1)
      (by simp [ha'i₀]) (by simp [z]) ha'_unimod hAz_unimod]
  exact vasersteinPsi_mul_fromBlocksGL hR hm A he₂ ha ha'_unimod

/-- General right-invariance of `vasersteinPsi` under `lowerBlockGL` whenever both matrices have
unimodular bottom-left row. -/
private theorem vasersteinPsi_mul_lowerBlockGL {R m : Type*} [Ring R] [Fintype m] [DecidableEq m]
    {s : ℕ} (hR : HasStableRangeLE R s) (hm : s + 1 ≤ Fintype.card m)
    (A : GL (m ⊕ Unit) R) (x : m → R)
    (ha : Module.IsUnimodular R (fun j ↦ A (Sum.inr ()) (Sum.inl j)))
    (ha₂ : Module.IsUnimodular R (fun j ↦
      (A * lowerBlockGL (Matrix.of fun (_ : Unit) k ↦ x k) : GL (m ⊕ Unit) R)
        (Sum.inr ()) (Sum.inl j))) :
    vasersteinPsi (A * lowerBlockGL (Matrix.of fun (_ : Unit) k ↦ x k)) ha₂ =
      vasersteinPsi A ha := by
  obtain ⟨i₀⟩ := Fintype.card_pos_iff.mp (by omega : 0 < Fintype.card m)
  obtain ⟨e₁, he₁, hae₁⟩ := hR.exists_vecMul_elementarySubgroup_eq_single hm ha i₀
  let A₁ := A * fromBlocksGL (e₁, (1 : GL Unit R))
  let x₁ : m → R := x ᵥ* (e₁ : Matrix m m R)
  have ha₁_eq : (fun j ↦ A₁ (Sum.inr ()) (Sum.inl j)) = Pi.single i₀ 1 := by
    rw [mul_fromBlocksGL_inr_inl, hae₁]
  have ha₁ : Module.IsUnimodular R (fun j ↦ A₁ (Sum.inr ()) (Sum.inl j)) := by
    rw [mul_fromBlocksGL_inr_inl, e₁.isUnimodular_vecMul_iff]; exact ha
  have hcomm := mul_lowerBlockGL_mul_fromBlocksGL A x e₁
  have ha₂₁ : Module.IsUnimodular R (fun j ↦
      (A₁ * lowerBlockGL (Matrix.of fun (_ : Unit) k ↦ x₁ k) : GL (m ⊕ Unit) R)
        (Sum.inr ()) (Sum.inl j)) := by
    rw [← hcomm, mul_fromBlocksGL_inr_inl, e₁.isUnimodular_vecMul_iff]; exact ha₂
  calc vasersteinPsi (A * lowerBlockGL (Matrix.of fun (_ : Unit) k ↦ x k)) ha₂
      = vasersteinPsi (A₁ * lowerBlockGL (Matrix.of fun (_ : Unit) k ↦ x₁ k)) ha₂₁ :=
        (vasersteinPsi_mul_fromBlocksGL hR hm _ he₁ ha₂ (hcomm.symm ▸ ha₂₁)).symm.trans
          (vasersteinPsi_congr hcomm (hcomm.symm ▸ ha₂₁) ha₂₁)
    _ = vasersteinPsi A₁ ha₁ :=
        vasersteinPsi_mul_lowerBlockGL_of_single hR hm A₁ i₀ x₁ ha₁_eq ha₁ ha₂₁
    _ = vasersteinPsi A ha := vasersteinPsi_mul_fromBlocksGL hR hm A he₁ ha ha₁

private theorem exists_unimodular_mul_lowerBlockGL {R m : Type*} [Ring R] [Fintype m]
    [DecidableEq m] {s : ℕ} (hR : HasStableRangeLE R s) (hm : s ≤ Fintype.card m)
    (A : GL (m ⊕ Unit) R) :
    ∃ c : m → R, Module.IsUnimodular R (fun j ↦
      (A * lowerBlockGL (Matrix.of fun (_ : Unit) k ↦ c k) : GL (m ⊕ Unit) R)
        (Sum.inr ()) (Sum.inl j)) := by
  obtain ⟨c, hc⟩ := hR.exists_isUnimodular_add_mul hm (isUnimodular_sumElim_inr A)
  exact ⟨c, by simpa only [mul_lowerBlockGL_inr_inl] using hc⟩

/-- Vaserstein's coset retraction `GL (m ⊕ Unit) R → GL m R ⧸ elementarySubgroup m R`. -/
private def vasersteinPhi {R m : Type*} [Ring R] [Fintype m] [DecidableEq m]
    {s : ℕ} (hR : HasStableRangeLE R s) (hm : s + 1 ≤ Fintype.card m)
    (A : GL (m ⊕ Unit) R) : GL m R ⧸ elementarySubgroup m R :=
  have hex := exists_unimodular_mul_lowerBlockGL hR (Nat.le_of_succ_le hm) A
  vasersteinPsi (A * lowerBlockGL (Matrix.of fun (_ : Unit) k ↦ hex.choose k)) hex.choose_spec

private theorem vasersteinPhi_eq_vasersteinPsi_mul_lowerBlockGL {R m : Type*} [Ring R]
    [Fintype m] [DecidableEq m] {s : ℕ} (hR : HasStableRangeLE R s) (hm : s + 1 ≤ Fintype.card m)
    (A : GL (m ⊕ Unit) R) (c : m → R)
    (hc : Module.IsUnimodular R (fun j ↦
      (A * lowerBlockGL (Matrix.of fun (_ : Unit) k ↦ c k) : GL (m ⊕ Unit) R)
        (Sum.inr ()) (Sum.inl j))) :
    vasersteinPhi hR hm A =
      vasersteinPsi (A * lowerBlockGL (Matrix.of fun (_ : Unit) k ↦ c k)) hc := by
  rw [vasersteinPhi]
  set hex := exists_unimodular_mul_lowerBlockGL hR (Nat.le_of_succ_le hm) A
  let c₀ := hex.choose
  have hadd : A * lowerBlockGL (Matrix.of fun (_ : Unit) k ↦ c k) =
      A * lowerBlockGL (Matrix.of fun (_ : Unit) k ↦ c₀ k) *
        lowerBlockGL (Matrix.of fun (_ : Unit) k ↦ c k - c₀ k) := by
    rw [mul_assoc, ← lowerBlockGL_add]; congr 2; ext ⟨⟩ k; simp
  have hc' : Module.IsUnimodular R (fun j ↦
      (A * lowerBlockGL (Matrix.of fun (_ : Unit) k ↦ c₀ k) *
        lowerBlockGL (Matrix.of fun (_ : Unit) k ↦ c k - c₀ k) : GL (m ⊕ Unit) R)
        (Sum.inr ()) (Sum.inl j)) := hadd ▸ hc
  exact (vasersteinPsi_mul_lowerBlockGL hR hm
    (A * lowerBlockGL (Matrix.of fun (_ : Unit) k ↦ c₀ k))
    (fun k ↦ c k - c₀ k) hex.choose_spec hc').symm.trans (vasersteinPsi_congr hadd.symm hc' hc)

private theorem vasersteinPhi_fromBlocksGL {R m : Type*} [Ring R] [Fintype m] [DecidableEq m]
    {s : ℕ} (hR : HasStableRangeLE R s) (hm : s + 1 ≤ Fintype.card m) (g : GL m R) :
    vasersteinPhi hR hm (fromBlocksGL (g, (1 : GL Unit R))) = QuotientGroup.mk g := by
  obtain ⟨i₀⟩ := Fintype.card_pos_iff.mp (by omega : 0 < Fintype.card m)
  let c : m → R := Pi.single i₀ 1
  have hc : Module.IsUnimodular R (fun j ↦
      (fromBlocksGL (g, (1 : GL Unit R)) * lowerBlockGL (Matrix.of fun (_ : Unit) k ↦ c k) :
        GL (m ⊕ Unit) R) (Sum.inr ()) (Sum.inl j)) := by
    have hrow : (fun j ↦ (fromBlocksGL (g, (1 : GL Unit R)) *
        lowerBlockGL (Matrix.of fun (_ : Unit) k ↦ c k) : GL (m ⊕ Unit) R)
        (Sum.inr ()) (Sum.inl j)) = c := by
      ext j; simp [Units.val_mul, Matrix.mul_apply, Fintype.sum_sum_type]
    rw [hrow]
    exact TauCeti.Module.isUnimodular_pi_iff.mpr ⟨Pi.single i₀ 1, by simp [c, Pi.single_apply]⟩
  rw [vasersteinPhi_eq_vasersteinPsi_mul_lowerBlockGL hR hm _ c hc]
  exact vasersteinPsi_fromBlocksGL_mul_lowerBlockGL hR hm g c hc

/-- Block commutation identity moving `upperBlockGL (single p₀ () r)` past `lowerBlockGL c` when
`c p₀ = 0`. -/
private theorem upperBlockGL_single_mul_lowerBlockGL_of_eq_zero {R m : Type*} [Ring R]
    [Fintype m] [DecidableEq m] (p₀ : m) (r : R) {c : m → R} (hc0 : c p₀ = 0) :
    ∃ e₀ ∈ elementarySubgroup m R,
      upperBlockGL (Matrix.single p₀ () r) * lowerBlockGL (Matrix.of fun (_ : Unit) j ↦ c j) =
        lowerBlockGL (Matrix.of fun (_ : Unit) j ↦ c j) *
          fromBlocksGL (e₀, (1 : GL Unit R)) * upperBlockGL (Matrix.single p₀ () r) := by
  let φ := complSumUnitEquiv p₀
  let e₀ : GL m R :=
    φ.reindexGL R (lowerBlockGL (Matrix.of fun (_ : Unit) (j : {j : m // j ≠ p₀}) ↦ r * c j.1))
  have he₀ : e₀ ∈ elementarySubgroup m R := by
    rw [← φ.map_reindexGL_elementarySubgroup]
    exact ⟨_, lowerBlockGL_mem_elementarySubgroup _, rfl⟩
  refine ⟨e₀, he₀, Units.ext ?_⟩
  set Y : Matrix m Unit R := Matrix.single p₀ () r
  set C : Matrix Unit m R := Matrix.of fun _ j ↦ c j
  have hCY : C * Y = 0 := by ext ⟨⟩ ⟨⟩; simp [C, Y, Matrix.mul_apply, single_apply, hc0]
  have he₀_mat : (e₀ : Matrix m m R) = 1 + Y * C := by
    ext p q
    obtain ⟨p, rfl⟩ := φ.surjective p
    obtain ⟨q, rfl⟩ := φ.surjective q
    simp only [e₀, Equiv.coe_reindexGL, submatrix_apply, φ.symm_apply_apply]
    rcases p with i | ⟨⟩ <;> rcases q with j | ⟨⟩
    · simp [φ, Y, C, Matrix.mul_apply, Matrix.one_apply, Subtype.ext_iff, i.2.symm]
    · simp [φ, Y, C, Matrix.mul_apply, i.2, i.2.symm]
    · simp [φ, Y, C, Matrix.mul_apply, j.2.symm]
    · simp [φ, Y, C, Matrix.mul_apply, hc0]
  have hCe₀ : C * (e₀ : Matrix m m R) = C := by
    rw [he₀_mat, Matrix.mul_add, Matrix.mul_one, ← Matrix.mul_assoc, hCY, Matrix.zero_mul, add_zero]
  have he₀Y : (e₀ : Matrix m m R) * Y = Y := by
    rw [he₀_mat, Matrix.add_mul, Matrix.one_mul, Matrix.mul_assoc, hCY, Matrix.mul_zero, add_zero]
  rw [Units.val_mul, Units.val_mul, Units.val_mul, coe_upperBlockGL, coe_lowerBlockGL,
    coe_fromBlocksGL]
  simp only [fromBlocks_multiply, Matrix.mul_zero, add_zero, zero_add, Matrix.mul_one,
    Matrix.one_mul, Units.val_one]
  rw [hCe₀, he₀Y, hCY, zero_add, he₀_mat]

private theorem vasersteinPhi_mul_upperBlockGL_single {R m : Type*} [Ring R] [Fintype m]
    [DecidableEq m] {s : ℕ} (hR : HasStableRangeLE R s) (hm : s + 1 ≤ Fintype.card m)
    (A : GL (m ⊕ Unit) R) (p₀ : m) (r : R) :
    vasersteinPhi hR hm (A * upperBlockGL (Matrix.single p₀ () r)) = vasersteinPhi hR hm A := by
  set U := upperBlockGL (Matrix.single p₀ () r)
  have hScard : s ≤ (({p₀} : Finset m)ᶜ).card := by
    rw [Finset.card_compl, Finset.card_singleton]; omega
  obtain ⟨c, hcsupp, hc_unimod⟩ := hR.exists_isUnimodular_add_mul_of_subset hScard
    (isUnimodular_sumElim_inr (A * U))
  have hc₁ : Module.IsUnimodular R (fun j ↦
      (A * U * lowerBlockGL (Matrix.of fun (_ : Unit) k ↦ c k) : GL (m ⊕ Unit) R)
        (Sum.inr ()) (Sum.inl j)) := by
    simpa only [mul_lowerBlockGL_inr_inl] using hc_unimod
  obtain ⟨e₀, he₀, hUcomm⟩ :=
    upperBlockGL_single_mul_lowerBlockGL_of_eq_zero p₀ r (hcsupp p₀ (by simp))
  set L := lowerBlockGL (Matrix.of fun (_ : Unit) k ↦ c k)
  have hchain : A * U * L = A * L * fromBlocksGL (e₀, (1 : GL Unit R)) * U := by
    calc A * U * L = A * (U * L) := by group
      _ = A * (L * fromBlocksGL (e₀, 1) * U) := by rw [hUcomm]
      _ = A * L * fromBlocksGL (e₀, 1) * U := by group
  have hc₂ : Module.IsUnimodular R (fun j ↦
      (A * L * fromBlocksGL (e₀, (1 : GL Unit R)) : GL (m ⊕ Unit) R)
        (Sum.inr ()) (Sum.inl j)) := by
    have hsame : (fun j ↦ (A * L * fromBlocksGL (e₀, (1 : GL Unit R)) * U : GL (m ⊕ Unit) R)
        (Sum.inr ()) (Sum.inl j)) =
        fun j ↦ (A * L * fromBlocksGL (e₀, (1 : GL Unit R)) : GL (m ⊕ Unit) R)
          (Sum.inr ()) (Sum.inl j) := by
      ext j; simp [U, Units.val_mul, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply]
    rw [← hsame, ← hchain]; exact hc₁
  have hc₀ : Module.IsUnimodular R (fun j ↦ (A * L : GL (m ⊕ Unit) R) (Sum.inr ()) (Sum.inl j)) :=
    by rw [← e₀.isUnimodular_vecMul_iff, ← mul_fromBlocksGL_inr_inl]; exact hc₂
  have hUmat : U = upperBlockGL (Matrix.of fun i (_ : Unit) ↦ Matrix.single p₀ () r i ()) := by
    congr 1
  rw [vasersteinPhi_eq_vasersteinPsi_mul_lowerBlockGL hR hm (A * U) c hc₁,
    vasersteinPhi_eq_vasersteinPsi_mul_lowerBlockGL hR hm A c hc₀]
  have hstepU : vasersteinPsi (A * U * L) hc₁ =
      vasersteinPsi (A * L * fromBlocksGL (e₀, (1 : GL Unit R))) hc₂ := by
    refine (vasersteinPsi_congr hchain hc₁ (hchain ▸ hc₁)).trans ?_
    simpa only [← hUmat] using vasersteinPsi_mul_upperBlockGL hR hm
      (A * L * fromBlocksGL (e₀, 1)) (fun i ↦ Matrix.single p₀ () r i ()) hc₂
      (hUmat ▸ hchain ▸ hc₁)
  rw [hstepU]
  exact vasersteinPsi_mul_fromBlocksGL hR hm (A * L) he₀ hc₀ hc₂

/-- Right-invariance of `vasersteinPhi` under every elementary transvection on `m ⊕ Unit`. -/
private theorem vasersteinPhi_mul_transvectionUnit {R m : Type*} [Ring R] [Fintype m]
    [DecidableEq m] {s : ℕ} (hR : HasStableRangeLE R s) (hm : s + 1 ≤ Fintype.card m)
    (A : GL (m ⊕ Unit) R) {p q : m ⊕ Unit} (hpq : p ≠ q) (r : R) :
    vasersteinPhi hR hm (A * transvectionUnit hpq r) = vasersteinPhi hR hm A := by
  rcases p with p₀ | ⟨⟩ <;> rcases q with q₀ | ⟨⟩
  · have hpq₀ : p₀ ≠ q₀ := fun h ↦ hpq (congrArg Sum.inl h)
    let e := transvectionUnit hpq₀ r
    have he : e ∈ elementarySubgroup m R := transvectionUnit_mem_elementarySubgroup hpq₀ r
    have htr : transvectionUnit hpq r = fromBlocksGL (e, (1 : GL Unit R)) := by
      refine Units.ext ?_
      ext (i | ⟨⟩) (j | ⟨⟩) <;>
        simp [e, coe_transvectionUnit_eq_one_add_single, single_apply, Matrix.one_apply]
    rw [htr]
    obtain ⟨c, hc⟩ := exists_unimodular_mul_lowerBlockGL hR (Nat.le_of_succ_le hm)
      (A * fromBlocksGL (e, (1 : GL Unit R)))
    let c₀ : m → R := c ᵥ* (↑e⁻¹ : Matrix m m R)
    have hcomm : A * fromBlocksGL (e, (1 : GL Unit R)) *
        lowerBlockGL (Matrix.of fun (_ : Unit) k ↦ c k) =
        A * lowerBlockGL (Matrix.of fun (_ : Unit) k ↦ c₀ k) *
          fromBlocksGL (e, (1 : GL Unit R)) := by
      have hc₀e : c₀ ᵥ* (e : Matrix m m R) = c := by simp [c₀, vecMul_vecMul]
      simpa only [hc₀e] using (mul_lowerBlockGL_mul_fromBlocksGL A c₀ e).symm
    have hc₀ : Module.IsUnimodular R (fun j ↦
        (A * lowerBlockGL (Matrix.of fun (_ : Unit) k ↦ c₀ k) : GL (m ⊕ Unit) R)
          (Sum.inr ()) (Sum.inl j)) := by
      rw [← e.isUnimodular_vecMul_iff, ← mul_fromBlocksGL_inr_inl, ← hcomm]; exact hc
    rw [vasersteinPhi_eq_vasersteinPsi_mul_lowerBlockGL hR hm _ c hc,
      vasersteinPhi_eq_vasersteinPsi_mul_lowerBlockGL hR hm A c₀ hc₀]
    exact (vasersteinPsi_congr hcomm hc (hcomm ▸ hc)).trans
      (vasersteinPsi_mul_fromBlocksGL hR hm _ he hc₀ (hcomm ▸ hc))
  · have htr : transvectionUnit hpq r = upperBlockGL (Matrix.single p₀ () r) := by
      refine Units.ext ?_
      ext (i | ⟨⟩) (j | ⟨⟩) <;>
        simp [coe_transvectionUnit_eq_one_add_single, single_apply, Matrix.one_apply]
    rw [htr]
    exact vasersteinPhi_mul_upperBlockGL_single hR hm A p₀ r
  · have htr : transvectionUnit hpq r = lowerBlockGL (Matrix.single () q₀ r) := by
      refine Units.ext ?_
      ext (i | ⟨⟩) (j | ⟨⟩) <;>
        simp [coe_transvectionUnit_eq_one_add_single, single_apply, Matrix.one_apply]
    rw [htr]
    obtain ⟨c, hc⟩ := exists_unimodular_mul_lowerBlockGL hR (Nat.le_of_succ_le hm)
      (A * lowerBlockGL (Matrix.single () q₀ r))
    let c' : m → R := fun k ↦ Matrix.single () q₀ r () k + c k
    have hcomb : A * lowerBlockGL (Matrix.single () q₀ r) *
        lowerBlockGL (Matrix.of fun (_ : Unit) k ↦ c k) =
        A * lowerBlockGL (Matrix.of fun (_ : Unit) k ↦ c' k) := by
      rw [mul_assoc, ← lowerBlockGL_add]; rfl
    rw [vasersteinPhi_eq_vasersteinPsi_mul_lowerBlockGL hR hm _ c hc,
      vasersteinPhi_eq_vasersteinPsi_mul_lowerBlockGL hR hm A c' (hcomb ▸ hc)]
    exact vasersteinPsi_congr hcomb hc (hcomb ▸ hc)
  · exact (hpq rfl).elim

private theorem vasersteinPhi_mul_elementarySubgroup {R m : Type*} [Ring R] [Fintype m]
    [DecidableEq m] {s : ℕ} (hR : HasStableRangeLE R s) (hm : s + 1 ≤ Fintype.card m)
    (A : GL (m ⊕ Unit) R) {E : GL (m ⊕ Unit) R} (hE : E ∈ elementarySubgroup (m ⊕ Unit) R) :
    vasersteinPhi hR hm (A * E) = vasersteinPhi hR hm A := by
  let H : Subgroup (GL (m ⊕ Unit) R) :=
    { carrier := {E | ∀ B, vasersteinPhi hR hm (B * E) = vasersteinPhi hR hm B}
      one_mem' := fun B ↦ by simp
      mul_mem' := fun {E₁ E₂} h₁ h₂ B ↦ by rw [← mul_assoc, h₂, h₁]
      inv_mem' := fun {E₁} h₁ B ↦ (h₁ (B * E₁⁻¹)).symm.trans (by simp) }
  have hle : elementarySubgroup (m ⊕ Unit) R ≤ H :=
    elementarySubgroup_le_iff.mpr fun p q hpq r B ↦
      vasersteinPhi_mul_transvectionUnit hR hm B hpq r
  exact hle hE A

private theorem injective_stability_unit {R m : Type*} [Ring R] [Fintype m] [DecidableEq m]
    {s : ℕ} (hR : HasStableRangeLE R s) (hm : s + 1 ≤ Fintype.card m) (g : GL m R)
    (hg : fromBlocksGL (g, (1 : GL Unit R)) ∈ elementarySubgroup (m ⊕ Unit) R) :
    g ∈ elementarySubgroup m R := by
  have h1 : (1 : GL (m ⊕ Unit) R) = fromBlocksGL (1, (1 : GL Unit R)) :=
    (map_one fromBlocksGL).symm
  have hmk : (QuotientGroup.mk g : GL m R ⧸ elementarySubgroup m R) = QuotientGroup.mk 1 := by
    calc (QuotientGroup.mk g : GL m R ⧸ elementarySubgroup m R)
        = vasersteinPhi hR hm (1 * fromBlocksGL (g, (1 : GL Unit R))) := by
          rw [one_mul, vasersteinPhi_fromBlocksGL]
      _ = vasersteinPhi hR hm 1 := vasersteinPhi_mul_elementarySubgroup hR hm 1 hg
      _ = vasersteinPhi hR hm (fromBlocksGL (1, (1 : GL Unit R))) := by rw [← h1]
      _ = QuotientGroup.mk 1 := vasersteinPhi_fromBlocksGL hR hm 1
  rw [QuotientGroup.eq, mul_one, Subgroup.inv_mem_iff] at hmk
  exact hmk

private def sumIsEmptyEquiv (n k : Type*) [IsEmpty k] : n ⊕ k ≃ n where
  toFun := Sum.elim id isEmptyElim
  invFun := Sum.inl
  left_inv := fun
    | Sum.inl _ => rfl
    | Sum.inr x => isEmptyElim x
  right_inv _ := rfl

/-- **Injective stability (Vaserstein):** if `R` has stable range at most `s` and `n` has at least
`s + 1` indices, an invertible matrix of size `n` whose block sum with an identity block is
elementary is already elementary. -/
theorem injective_stability {R : Type*} [Ring R] (s : ℕ) (hR : HasStableRangeLE R s)
    (n k : Type*) [Fintype n] [DecidableEq n] [Fintype k] [DecidableEq k]
    (hn : s + 1 ≤ Fintype.card n) (g : Matrix.GeneralLinearGroup n R)
    (U : Matrix.GeneralLinearGroup (n ⊕ k) R)
    (hU : (U : Matrix (n ⊕ k) (n ⊕ k) R) = Matrix.fromBlocks (g : Matrix n n R) 0 0 1)
    (hUe : U ∈ TauCeti.elementarySubgroup (n ⊕ k) R) :
    g ∈ TauCeti.elementarySubgroup n R := by
  have hUeq : U = fromBlocksGL (g, (1 : GL k R)) := Units.ext (by simpa using hU)
  rw [hUeq] at hUe
  clear U hU hUeq
  suffices ∀ c : ℕ, ∀ (k : Type _) [Fintype k] [DecidableEq k], Fintype.card k = c →
      fromBlocksGL (g, (1 : GL k R)) ∈ elementarySubgroup (n ⊕ k) R →
      g ∈ elementarySubgroup n R from this (Fintype.card k) k rfl hUe
  intro c
  induction c with
  | zero =>
    intro k _ _ hk hg'
    have : IsEmpty k := Fintype.card_eq_zero_iff.mp hk
    let ψ := sumIsEmptyEquiv n k
    have hg_eq : ψ.reindexGL R (fromBlocksGL (g, (1 : GL k R))) = g := by
      refine Units.ext ?_
      ext i j
      simp only [Equiv.coe_reindexGL, coe_fromBlocksGL, submatrix_apply]
      rfl
    rw [← hg_eq, ← ψ.map_reindexGL_elementarySubgroup]
    exact ⟨_, hg', rfl⟩
  | succ m ih =>
    intro k _ _ hk hg'
    obtain ⟨x₀⟩ := Fintype.card_pos_iff.mp (by omega : 0 < Fintype.card k)
    let φ := sumComplUnitEquiv n x₀
    have hcard_nk' : s + 1 ≤ Fintype.card (n ⊕ {x : k // x ≠ x₀}) := by
      rw [Fintype.card_sum]; omega
    have hcard_k' : Fintype.card {x : k // x ≠ x₀} = m := by
      have hc := Fintype.card_congr (complSumUnitEquiv x₀)
      simp only [Fintype.card_sum, Fintype.card_unique] at hc; omega
    have hmem : fromBlocksGL
        (fromBlocksGL (g, (1 : GL {x : k // x ≠ x₀} R)), (1 : GL Unit R)) ∈
        elementarySubgroup ((n ⊕ {x : k // x ≠ x₀}) ⊕ Unit) R := by
      have hre : φ.symm.reindexGL R (fromBlocksGL (g, (1 : GL k R))) =
          fromBlocksGL (fromBlocksGL (g, (1 : GL {x : k // x ≠ x₀} R)), (1 : GL Unit R)) := by
        rw [← reindexGL_sumComplUnitEquiv_fromBlocksGL x₀ g]; dsimp only [φ]; simp
      rw [← hre, ← φ.symm.map_reindexGL_elementarySubgroup]
      exact ⟨_, hg', rfl⟩
    exact ih {x : k // x ≠ x₀} hcard_k' (injective_stability_unit hR hcard_nk' _ hmem)

/-! ## Finite-rank descriptions of `K₁` and commutator subgroups -/

namespace AlgebraicK1

/-- **Surjective `K₁`-stability:** if `R` has Bass stable range at most `s` and `s ≤ n`, the
canonical homomorphism `AlgebraicK1.mk R n : GL (Fin n) R →* AlgebraicK1 R` is surjective. -/
theorem mk_surjective {R : Type*} [Ring R] {s n : ℕ} (hR : HasStableRangeLE R s) (hn : s ≤ n) :
    Function.Surjective (mk R n) := by
  intro x
  obtain ⟨m, u, rfl⟩ := exists_mk x
  rcases le_total m n with hmn | hnm
  · exact ⟨stabilizeGL R hmn u, mk_stabilizeGL hmn u⟩
  · let φ := finSumFinEquiv.trans (finCongr (Nat.add_sub_cancel' hnm))
    have hcard : s ≤ Fintype.card (Fin n) := by simpa using hn
    obtain ⟨h, e, he, hge⟩ := surjective_stability s hR (Fin n) (Fin (m - n)) hcard
      (φ.symm.reindexGL R u)
    have hge' : φ.symm.reindexGL R u = fromBlocksGL (h, (1 : GL (Fin (m - n)) R)) * e :=
      Units.ext (by simpa using hge)
    have hu : u = stabilizeGL R hnm h * φ.reindexGL R e := by
      calc u = φ.reindexGL R (φ.symm.reindexGL R u) := by simp
        _ = φ.reindexGL R (fromBlocksGL (h, 1)) * φ.reindexGL R e := by rw [hge', map_mul]
        _ = stabilizeGL R hnm h * φ.reindexGL R e := by rw [← stabilizeGL_apply]
    have he_ker : mk R m (φ.reindexGL R e) = 1 := by
      apply elementarySubgroup_le_ker_mk m
      rw [← φ.map_reindexGL_elementarySubgroup]
      exact ⟨e, he, rfl⟩
    refine ⟨h, ?_⟩
    rw [hu, map_mul, mk_stabilizeGL hnm h, he_ker, mul_one]

/-- When `R` has Bass stable range at most `s` and `s ≤ n` (including at the boundary `n = s` where
injective stability need not yet hold), `K₁(R)` is the quotient of `GL (Fin n) R` by the actual
kernel `(AlgebraicK1.mk R n).ker`. -/
def quotientKerMkEquiv {R : Type*} [Ring R] {s n : ℕ} (hR : HasStableRangeLE R s) (hn : s ≤ n) :
    GL (Fin n) R ⧸ (mk R n).ker ≃* AlgebraicK1 R :=
  QuotientGroup.quotientKerEquivOfSurjective (mk R n) (mk_surjective hR hn)

/-- `AlgebraicK1.quotientKerMkEquiv` sends the coset of `u` to `AlgebraicK1.mk R n u`. -/
@[simp]
theorem quotientKerMkEquiv_mk {R : Type*} [Ring R] {s n : ℕ} (hR : HasStableRangeLE R s)
    (hn : s ≤ n) (u : GL (Fin n) R) :
    quotientKerMkEquiv hR hn (QuotientGroup.mk u) = mk R n u :=
  (rfl)

/-- **Injective `K₁`-stability:** if `R` has Bass stable range at most `s` and `s + 1 ≤ n`, the
kernel of `AlgebraicK1.mk R n` equals `elementarySubgroup (Fin n) R`. -/
theorem ker_mk_eq_elementarySubgroup {R : Type*} [Ring R] {s n : ℕ} (hR : HasStableRangeLE R s)
    (hn : s + 1 ≤ n) :
    (mk R n).ker = TauCeti.elementarySubgroup (Fin n) R := by
  refine le_antisymm (fun u hu ↦ ?_) (elementarySubgroup_le_ker_mk n)
  rw [MonoidHom.mem_ker, mk_eq_one_iff] at hu
  obtain ⟨k, hnk, hu⟩ := hu
  let φ := finSumFinEquiv.trans (finCongr (Nat.add_sub_cancel' hnk))
  have hst : stabilizeGL R hnk u = φ.reindexGL R (fromBlocksGL (u, (1 : GL (Fin (k - n)) R))) :=
    stabilizeGL_apply hnk u
  have hU : φ.symm.reindexGL R (stabilizeGL R hnk u) =
      fromBlocksGL (u, (1 : GL (Fin (k - n)) R)) := by
    rw [hst]; simp
  have hUe : φ.symm.reindexGL R (stabilizeGL R hnk u) ∈
      TauCeti.elementarySubgroup (Fin n ⊕ Fin (k - n)) R := by
    rw [← φ.symm.map_reindexGL_elementarySubgroup]
    exact ⟨_, hu, rfl⟩
  exact injective_stability s hR (Fin n) (Fin (k - n)) (by simpa using hn) u
    (φ.symm.reindexGL R (stabilizeGL R hnk u)) (by simp [hU]) hUe

/-- When `R` has Bass stable range at most `s` and `s + 1 ≤ n`, algebraic `K₁(R)` is canonically
isomorphic to `GL (Fin n) R ⧸ elementarySubgroup (Fin n) R` (with normality provided by
`TauCeti.elementarySubgroup_normal_of_hasStableRangeLE`). -/
def quotientFinElementarySubgroupEquiv {R : Type*} [Ring R] {s n : ℕ}
    [(TauCeti.elementarySubgroup (Fin n) R).Normal]
    (hR : HasStableRangeLE R s) (hn : s + 1 ≤ n) :
    GL (Fin n) R ⧸ TauCeti.elementarySubgroup (Fin n) R ≃* AlgebraicK1 R :=
  (QuotientGroup.quotientMulEquivOfEq (ker_mk_eq_elementarySubgroup hR hn).symm).trans
    (quotientKerMkEquiv hR (Nat.le_of_succ_le hn))

/-- `AlgebraicK1.quotientFinElementarySubgroupEquiv` sends the coset of `u` to
`AlgebraicK1.mk R n u`. -/
@[simp]
theorem quotientFinElementarySubgroupEquiv_mk {R : Type*} [Ring R] {s n : ℕ}
    [(TauCeti.elementarySubgroup (Fin n) R).Normal]
    (hR : HasStableRangeLE R s) (hn : s + 1 ≤ n) (u : GL (Fin n) R) :
    quotientFinElementarySubgroupEquiv hR hn (QuotientGroup.mk u) = mk R n u :=
  (rfl)

end AlgebraicK1

/-- When `R` has Bass stable range at most `s` and `s + 1 ≤ Fintype.card n`, the commutator
subgroup of `GL n R` is contained in `elementarySubgroup n R`. -/
theorem commutator_le_elementarySubgroup_of_hasStableRangeLE {R n : Type*} [Ring R] [Fintype n]
    [DecidableEq n] {s : ℕ} (hR : HasStableRangeLE R s) (hn : s + 1 ≤ Fintype.card n) :
    commutator (GL n R) ≤ elementarySubgroup n R :=
  Subgroup.commutator_le.mpr fun u _ v _ ↦
    injective_stability s hR n n hn ⁅u, v⁆ (fromBlocksGL (⁅u, v⁆, 1)) (by simp)
      (fromBlocksGL_commutatorElement_mem_elementarySubgroup u v)

/-- When `R` has Bass stable range at most `s` and `max 3 (s + 1) ≤ Fintype.card n`, the
elementary subgroup `elementarySubgroup n R` equals the commutator subgroup of `GL n R`. -/
theorem elementarySubgroup_eq_commutator_of_hasStableRangeLE {R n : Type*} [Ring R] [Fintype n]
    [DecidableEq n] {s : ℕ} (hR : HasStableRangeLE R s)
    (hn : max 3 (s + 1) ≤ Fintype.card n) :
    elementarySubgroup n R = commutator (GL n R) :=
  le_antisymm (elementarySubgroup_le_commutator (le_of_max_le_left hn))
    (commutator_le_elementarySubgroup_of_hasStableRangeLE hR (le_of_max_le_right hn))

namespace AlgebraicK1

/-- When `R` has Bass stable range at most `s` and `max 3 (s + 1) ≤ n`, algebraic `K₁(R)` is
canonically isomorphic to the abelianization of `GL (Fin n) R`. -/
def abelianizationFinEquiv {R : Type*} [Ring R] {s n : ℕ} (hR : HasStableRangeLE R s)
    (hn : max 3 (s + 1) ≤ n) :
    Group.Abelianization (GL (Fin n) R) ≃* AlgebraicK1 R :=
  have hker : commutator (GL (Fin n) R) = (mk R n).ker := by
    rw [ker_mk_eq_elementarySubgroup hR (le_of_max_le_right hn),
      elementarySubgroup_eq_commutator_of_hasStableRangeLE hR (by simpa using hn)]
  (QuotientGroup.quotientMulEquivOfEq hker).trans
    (quotientKerMkEquiv hR (Nat.le_of_succ_le (le_of_max_le_right hn)))

/-- `AlgebraicK1.abelianizationFinEquiv` sends the abelianization class of `u` to
`AlgebraicK1.mk R n u`. -/
@[simp]
theorem abelianizationFinEquiv_of {R : Type*} [Ring R] {s n : ℕ} (hR : HasStableRangeLE R s)
    (hn : max 3 (s + 1) ≤ n) (u : GL (Fin n) R) :
    abelianizationFinEquiv hR hn (Group.Abelianization.of u) = mk R n u :=
  (rfl)

end AlgebraicK1

end TauCeti

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Elementary
public import TauCeti.LinearAlgebra.Matrix.OneSubVecMulVec
public import TauCeti.RingTheory.StableRange

/-!
# Surjective stability, normality of `Eₙ(R)`, and unimodular orbits

Over a possibly noncommutative ring `R` of Bass stable range at most `s`
(`TauCeti.HasStableRangeLE R s`), elementary row and column operations reduce invertible matrices
and unimodular rows into finite rank:

* **Surjective stability (Bass).** Whenever `s ≤ Fintype.card n`, every invertible matrix in
  `GL (n ⊕ k) R` factors as `fromBlocks h 0 0 1 * e` with `h : GL n R` and
  `e ∈ elementarySubgroup (n ⊕ k) R`.
* **Normality of `Eₙ(R)`.** Whenever `s + 1 ≤ Fintype.card n`, the elementary subgroup
  `elementarySubgroup n R` is normal in `GL n R`.
* **Unimodular orbits and rank-one unipotent matrices.** Whenever `s + 1 ≤ Fintype.card m`,
  `elementarySubgroup m R` acts transitively on unimodular rows in `m → R`, and consequently every
  rank-one unipotent matrix `1 - vecMulVec u v` with `v` unimodular and `v ⬝ᵥ u = 0` belongs to
  `elementarySubgroup m R`.

## Main results

* `TauCeti.surjective_stability`: Bass's surjective stability theorem for `GL (n ⊕ k) R`.
* `TauCeti.elementarySubgroup_normal_of_hasStableRangeLE`: normality of `E n R` in `GL n R` for
  `s + 1 ≤ Fintype.card n`.
* `TauCeti.HasStableRangeLE.exists_vecMul_elementarySubgroup_eq_single`: transitive action of
  `E m R` on unimodular rows for `s + 1 ≤ Fintype.card m`.
* `TauCeti.HasStableRangeLE.oneSubVecMulVecGL_mem_elementarySubgroup`: rank-one unipotent matrices
  with unimodular covector lie in `E m R` for `s + 1 ≤ Fintype.card m`.

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

open scoped Matrix

namespace TauCeti

/-! ## Pivot reindexing and row reduction -/

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

private theorem card_subtype_ne {m : Type*} [Fintype m] [DecidableEq m] (i₀ : m) :
    Fintype.card {i : m // i ≠ i₀} + 1 = Fintype.card m := by
  simpa using Fintype.card_congr (complSumUnitEquiv i₀)

private theorem reindexGL_mem_elementarySubgroup {R m n : Type*} [Ring R] [Fintype m]
    [DecidableEq m] [Fintype n] [DecidableEq n] (φ : m ≃ n) {u : GL m R}
    (hu : u ∈ elementarySubgroup m R) : φ.reindexGL R u ∈ elementarySubgroup n R := by
  rw [← φ.map_reindexGL_elementarySubgroup]; exact ⟨u, hu, rfl⟩

private theorem isUnimodular_sumElim_complSumUnitEquiv {R m : Type*} [Ring R]
    {a : m → R} (ha : Module.IsUnimodular R a) (i₀ : m) :
    Module.IsUnimodular R
      (Sum.elim (fun i : {i : m // i ≠ i₀} ↦ a i.1) (fun _ : Unit ↦ a i₀)) := by
  classical
  have hcomp : Sum.elim (fun i : {i : m // i ≠ i₀} ↦ a i.1) (fun _ : Unit ↦ a i₀) =
      (LinearEquiv.funCongrLeft R R (complSumUnitEquiv i₀)) a := by
    ext (i | ⟨⟩) <;> rfl
  rw [hcomp, LinearEquiv.isUnimodular_apply_iff]; exact ha

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
  have hne : ∀ y : {x : k // x ≠ x₀}, (y : k) ≠ x₀ := fun y ↦ y.2
  have hne' : ∀ y : {x : k // x ≠ x₀}, x₀ ≠ (y : k) := fun y ↦ y.2.symm
  refine Units.ext ?_; ext p q
  obtain ⟨p, rfl⟩ := φ.surjective p; obtain ⟨q, rfl⟩ := φ.surjective q
  rcases p with (i | y) | ⟨⟩ <;> rcases q with (j | z) | ⟨⟩ <;>
    simp [φ, sumComplUnitEquiv, Matrix.one_apply, Subtype.ext_iff, hne, hne']

private abbrev lowerVec {R m : Type*} [Ring R] [Fintype m] [DecidableEq m] (c : m → R) :
    GL (m ⊕ Unit) R :=
  lowerBlockGL (Matrix.of fun _ j ↦ c j)

private abbrev upperVec {R m : Type*} [Ring R] [Fintype m] [DecidableEq m] (y : m → R) :
    GL (m ⊕ Unit) R :=
  upperBlockGL (Matrix.of fun i _ ↦ y i)

private abbrev blockOne {R m : Type*} [Ring R] [Fintype m] [DecidableEq m] (e : GL m R) :
    GL (m ⊕ Unit) R :=
  fromBlocksGL (e, (1 : GL Unit R))

/-- Row reduction on `ι ⊕ Unit` sending `(a', d)` to `(0, 1)` once `(a' + d • c) ⬝ᵥ b = 1`. -/
private theorem vecMul_lower_upper_lower_eq_inr {R ι : Type*} [Ring R] [Fintype ι] [DecidableEq ι]
    {a' c b : ι → R} {d : R} (hb : (fun i ↦ a' i + d * c i) ⬝ᵥ b = 1) :
    Sum.elim a' (fun _ : Unit ↦ d) ᵥ*
      ((lowerVec c * upperVec (fun i ↦ b i * (1 - d)) *
        lowerVec (fun j ↦ -(a' j + d * c j)) : GL (ι ⊕ Unit) R) :
        Matrix (ι ⊕ Unit) (ι ⊕ Unit) R) = Sum.elim (0 : ι → R) (fun _ : Unit ↦ 1) := by
  let u : ι → R := fun i ↦ a' i + d * c i
  have hv₁ : Sum.elim a' (fun _ : Unit ↦ d) ᵥ* (lowerVec c : Matrix _ _ R) =
      Sum.elim u (fun _ : Unit ↦ d) := by
    ext (j | ⟨⟩) <;> simp [u, vecMul, dotProduct, Fintype.sum_sum_type, Matrix.one_apply]
  have hv₂ : Sum.elim u (fun _ : Unit ↦ d) ᵥ*
      (upperVec (fun i ↦ b i * (1 - d)) : Matrix _ _ R) = Sum.elim u (fun _ : Unit ↦ 1) := by
    ext (j | ⟨⟩)
    · simp [vecMul, dotProduct, Fintype.sum_sum_type, Matrix.one_apply]
    · simp only [coe_upperBlockGL, vecMul, dotProduct, Fintype.sum_sum_type, Sum.elim_inl,
        fromBlocks_apply₁₂, Matrix.of_apply, Sum.elim_inr, Fintype.univ_punit,
        Finset.sum_singleton, fromBlocks_apply₂₂, Matrix.one_apply_eq, mul_one]
      have hsum : (∑ i : ι, u i * (b i * (1 - d))) = (u ⬝ᵥ b) * (1 - d) := by
        simp only [dotProduct, Finset.sum_mul, mul_assoc]
      rw [hsum, hb, one_mul, sub_add_cancel]
  have hv₃ : Sum.elim u (fun _ : Unit ↦ (1 : R)) ᵥ*
      (lowerVec (fun j ↦ -(a' j + d * c j)) : Matrix _ _ R) =
      Sum.elim (0 : ι → R) (fun _ : Unit ↦ 1) := by
    ext (j | ⟨⟩) <;> simp [u, vecMul, dotProduct, Fintype.sum_sum_type, Matrix.one_apply]
  simp only [Units.val_mul, ← vecMul_vecMul, hv₁, hv₂, hv₃]

/-! ## Surjective stability and normality -/

/-- Single-step surjective stability on `m ⊕ Unit`. -/
private theorem surjective_stability_unit {R m : Type*} [Ring R] [Fintype m] [DecidableEq m]
    {s : ℕ} (hR : HasStableRangeLE R s) (hm : s ≤ Fintype.card m) (g : GL (m ⊕ Unit) R) :
    ∃ (h : GL m R) (e : GL (m ⊕ Unit) R),
      e ∈ elementarySubgroup (m ⊕ Unit) R ∧ g = blockOne h * e := by
  let a' : m → R := fun j ↦ g (Sum.inr ()) (Sum.inl j)
  let d : R := g (Sum.inr ()) (Sum.inr ())
  have hrow : Sum.elim a' (fun _ : Unit ↦ d) =
      (g : Matrix (m ⊕ Unit) (m ⊕ Unit) R) (Sum.inr ()) := by
    ext (j | ⟨⟩) <;> rfl
  obtain ⟨c, hc⟩ := hR.exists_isUnimodular_add_mul hm (hrow ▸ g.isUnimodular_apply (Sum.inr ()))
  obtain ⟨b, hb⟩ := TauCeti.Module.isUnimodular_pi_iff.mp hc
  let e₀ : GL (m ⊕ Unit) R :=
    lowerVec c * upperVec (fun i ↦ b i * (1 - d)) * lowerVec (fun j ↦ -(a' j + d * c j))
  have he₀ : e₀ ∈ elementarySubgroup (m ⊕ Unit) R :=
    mul_mem (mul_mem (lowerBlockGL_mem_elementarySubgroup _)
      (upperBlockGL_mem_elementarySubgroup _)) (lowerBlockGL_mem_elementarySubgroup _)
  have hbot : ∀ q : m ⊕ Unit,
      ((g * e₀ : GL (m ⊕ Unit) R) : Matrix (m ⊕ Unit) (m ⊕ Unit) R) (Sum.inr ()) q =
        Sum.elim (0 : m → R) (fun _ : Unit ↦ 1) q := by
    intro q
    change ((g : Matrix (m ⊕ Unit) (m ⊕ Unit) R) (Sum.inr ()) ᵥ*
      (e₀ : Matrix (m ⊕ Unit) (m ⊕ Unit) R)) q = _
    rw [← hrow, vecMul_lower_upper_lower_eq_inr hb]
  have h₂₁ : ((g * e₀ : GL (m ⊕ Unit) R) : Matrix (m ⊕ Unit) (m ⊕ Unit) R).toBlocks₂₁ = 0 := by
    ext ⟨⟩ j; simpa [toBlocks₂₁] using hbot (Sum.inl j)
  have h₂₂ : ((g * e₀ : GL (m ⊕ Unit) R) : Matrix (m ⊕ Unit) (m ⊕ Unit) R).toBlocks₂₂ = 1 := by
    ext ⟨⟩ ⟨⟩; simpa [toBlocks₂₂] using hbot (Sum.inr ())
  let h : GL m R := (g * e₀).toBlocks₁₁GL h₂₁ h₂₂
  let u : GL (m ⊕ Unit) R := upperBlockGL
    ((↑h⁻¹ : Matrix m m R) *
      ((g * e₀ : GL (m ⊕ Unit) R) : Matrix (m ⊕ Unit) (m ⊕ Unit) R).toBlocks₁₂)
  have hge₀ : g * e₀ = blockOne h * u := eq_fromBlocksGL_mul_upperBlockGL (g * e₀) h₂₁ h₂₂
  refine ⟨h, u * e₀⁻¹, mul_mem (upperBlockGL_mem_elementarySubgroup _) (inv_mem he₀), ?_⟩
  calc g = g * e₀ * e₀⁻¹ := by group
    _ = blockOne h * (u * e₀⁻¹) := by rw [hge₀]; group

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
    ext (i | x) (j | y) <;> first | exact isEmptyElim x | exact isEmptyElim y | simp [h, toBlocks₁₁]
  | succ m ih =>
    intro k _ _ hk g
    obtain ⟨x₀⟩ := Fintype.card_pos_iff.mp (by omega : 0 < Fintype.card k)
    let φ := sumComplUnitEquiv n x₀
    have hcard_k' : Fintype.card {x : k // x ≠ x₀} = m := by have := card_subtype_ne x₀; omega
    obtain ⟨g₁, e₁, he₁, hg'⟩ := surjective_stability_unit hR
      (by rw [Fintype.card_sum]; omega) (φ.symm.reindexGL R g)
    obtain ⟨h, e₂, he₂, hg₁⟩ := ih {x : k // x ≠ x₀} hcard_k' g₁
    let e₀ := blockOne e₂ * e₁
    have he₀ : e₀ ∈ elementarySubgroup ((n ⊕ {x : k // x ≠ x₀}) ⊕ Unit) R :=
      mul_mem (map_elementarySubgroup_le_elementarySubgroup ⟨e₂, he₂, rfl⟩) he₁
    refine ⟨h, φ.reindexGL R e₀, reindexGL_mem_elementarySubgroup φ he₀, ?_⟩
    have hdecomp : φ.symm.reindexGL R g =
        blockOne (fromBlocksGL (h, (1 : GL {x : k // x ≠ x₀} R))) * e₀ := by
      have hmul : blockOne (fromBlocksGL (h, (1 : GL {x : k // x ≠ x₀} R)) * e₂) =
          blockOne (fromBlocksGL (h, 1)) * blockOne e₂ := by rw [← map_mul]; simp
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
  have hcard : s ≤ Fintype.card {k : n // k ≠ i} := by have := card_subtype_ne i; omega
  obtain ⟨h, e, he, hginv⟩ := surjective_stability_unit hR hcard (φ.symm.reindexGL R g)⁻¹
  have hg' : φ.symm.reindexGL R g = e⁻¹ * blockOne h⁻¹ := by
    calc φ.symm.reindexGL R g = ((φ.symm.reindexGL R g)⁻¹)⁻¹ := (inv_inv _).symm
      _ = e⁻¹ * (blockOne h)⁻¹ := by rw [hginv, _root_.mul_inv_rev]
      _ = e⁻¹ * blockOne h⁻¹ := by congr 1; rw [← map_inv]; simp
  let Y : Matrix Unit {k : n // k ≠ i} R := Matrix.single () ⟨j, hij.symm⟩ a
  have htr : φ.symm.reindexGL R (transvectionUnit hij a) = lowerBlockGL Y := by
    refine Units.ext ?_; ext (p | ⟨⟩) (q | ⟨⟩)
    · simp [φ, coe_transvectionUnit_eq_one_add_single, Matrix.one_apply, Subtype.ext_iff, p.2.symm]
    · simp [φ, coe_transvectionUnit_eq_one_add_single, p.2, p.2.symm]
    · simp [φ, Y, coe_transvectionUnit_eq_one_add_single, single_apply, Subtype.ext_iff, q.2.symm]
    · simp [φ, coe_transvectionUnit_eq_one_add_single, hij.symm]
  have hmid : blockOne h⁻¹ * lowerBlockGL Y * (blockOne h⁻¹)⁻¹ =
      lowerBlockGL (Y * (h : Matrix {k : n // k ≠ i} {k : n // k ≠ i} R)) := by
    refine Units.ext ?_
    have hh : (↑(blockOne h⁻¹)⁻¹ :
        Matrix ({k : n // k ≠ i} ⊕ Unit) ({k : n // k ≠ i} ⊕ Unit) R) =
        fromBlocks (h : Matrix {k : n // k ≠ i} {k : n // k ≠ i} R) 0 0 1 := by
      rw [← map_inv]; simp
    rw [Units.val_mul, Units.val_mul, hh]; simp [fromBlocks_multiply]
  have hconj : φ.symm.reindexGL R (g * transvectionUnit hij a * g⁻¹) =
      e⁻¹ * lowerBlockGL (Y * (h : Matrix {k : n // k ≠ i} {k : n // k ≠ i} R)) * e := by
    rw [map_mul, map_mul, map_inv, hg', htr]
    calc _ = e⁻¹ * (blockOne h⁻¹ * lowerBlockGL Y * (blockOne h⁻¹)⁻¹) * e := by group
      _ = _ := by rw [hmid]
  have hmem := mul_mem (mul_mem (inv_mem he) (lowerBlockGL_mem_elementarySubgroup
    (Y * (h : Matrix {k : n // k ≠ i} {k : n // k ≠ i} R)))) he
  simpa [← hconj] using reindexGL_mem_elementarySubgroup φ hmem

/-! ## Unimodular orbits and rank-one unipotent matrices -/

/-- Over a ring of Bass stable range at most `s`, the elementary subgroup `elementarySubgroup m R`
acts transitively on unimodular rows whenever `s + 1 ≤ Fintype.card m`: every unimodular row can
be sent to any standard basis vector `Pi.single i₀ 1`. -/
theorem HasStableRangeLE.exists_vecMul_elementarySubgroup_eq_single {R m : Type*} [Ring R]
    [Fintype m] [DecidableEq m] {s : ℕ} (hR : HasStableRangeLE R s)
    (hm : s + 1 ≤ Fintype.card m) {a : m → R} (ha : Module.IsUnimodular R a) (i₀ : m) :
    ∃ e ∈ elementarySubgroup m R, a ᵥ* (e : Matrix m m R) = Pi.single i₀ 1 := by
  let φ := complSumUnitEquiv i₀
  have hcard : s ≤ Fintype.card {i : m // i ≠ i₀} := by have := card_subtype_ne i₀; omega
  obtain ⟨c, hc⟩ := hR.exists_isUnimodular_add_mul hcard
    (isUnimodular_sumElim_complSumUnitEquiv ha i₀)
  obtain ⟨b, hb⟩ := TauCeti.Module.isUnimodular_pi_iff.mp hc
  let e₀ : GL ({i : m // i ≠ i₀} ⊕ Unit) R :=
    lowerVec c * upperVec (fun i ↦ b i * (1 - a i₀)) * lowerVec (fun j ↦ -(a j.1 + a i₀ * c j))
  have he₀ : e₀ ∈ elementarySubgroup ({i : m // i ≠ i₀} ⊕ Unit) R :=
    mul_mem (mul_mem (lowerBlockGL_mem_elementarySubgroup _)
      (upperBlockGL_mem_elementarySubgroup _)) (lowerBlockGL_mem_elementarySubgroup _)
  refine ⟨φ.reindexGL R e₀, reindexGL_mem_elementarySubgroup φ he₀, ?_⟩
  ext k; obtain ⟨x, rfl⟩ := φ.surjective k
  have hmul : (a ᵥ* (φ.reindexGL R e₀ : Matrix m m R)) (φ x) =
      (Sum.elim (fun i : {i : m // i ≠ i₀} ↦ a i.1) (fun _ : Unit ↦ a i₀) ᵥ*
        (e₀ : Matrix _ _ R)) x := by
    simp only [Equiv.coe_reindexGL, submatrix_apply, vecMul, dotProduct]
    rw [← φ.sum_comp]
    exact Fintype.sum_congr _ _ fun y ↦ by rcases y with i | ⟨⟩ <;> simp [φ]
  rw [hmul, vecMul_lower_upper_lower_eq_inr hb]
  rcases x with i | ⟨⟩ <;> simp [φ, show ∀ i : {i : m // i ≠ i₀}, i.1 ≠ i₀ from fun i ↦ i.2]

/-- Conjugating `1 - vecMulVec u v` by `e : GL m R` transforms `u` by `e⁻¹ *ᵥ ·` and `v` by
`· ᵥ* e`. -/
private theorem conj_one_sub_vecMulVec {R m : Type*} [Ring R] [Fintype m] [DecidableEq m]
    (e : GL m R) (u v : m → R) :
    (↑e⁻¹ : Matrix m m R) * (1 - vecMulVec u v) * (e : Matrix m m R) =
      1 - vecMulVec ((↑e⁻¹ : Matrix m m R) *ᵥ u) (v ᵥ* (e : Matrix m m R)) := by
  rw [Matrix.mul_sub, Matrix.mul_one, Matrix.sub_mul, Units.inv_mul]
  congr 1; ext i j
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
      _ = 0 := by rw [← dotProduct_mulVec, mulVec_mulVec, Units.mul_inv, one_mulVec, hvu]
  let φ := complSumUnitEquiv i₀
  let U := upperVec (R := R) (m := {i : m // i ≠ i₀}) (fun i ↦ -u' i.1)
  have hconj : e⁻¹ * g * e = φ.reindexGL R U := by
    refine Units.ext ?_
    rw [Units.val_mul, Units.val_mul, coe_oneSubVecMulVecGL, conj_one_sub_vecMulVec, hve]
    change 1 - vecMulVec u' (Pi.single i₀ 1) = _
    ext p q; obtain ⟨p, rfl⟩ := φ.surjective p; obtain ⟨q, rfl⟩ := φ.surjective q
    simp only [Equiv.coe_reindexGL, submatrix_apply, φ.symm_apply_apply]
    rcases p with i | ⟨⟩ <;> rcases q with j | ⟨⟩
    · simp [φ, U, vecMulVec_apply, Matrix.one_apply, Subtype.ext_iff, j.2]
    · simp [φ, U, vecMulVec_apply, i.2]
    · simp [φ, U, vecMulVec_apply, j.2, j.2.symm]
    · simp [φ, U, vecMulVec_apply, hu'0]
  rw [show g = e * (e⁻¹ * g * e) * e⁻¹ by group, hconj]
  exact mul_mem (mul_mem he (reindexGL_mem_elementarySubgroup φ
    (upperBlockGL_mem_elementarySubgroup _))) (inv_mem he)

end TauCeti

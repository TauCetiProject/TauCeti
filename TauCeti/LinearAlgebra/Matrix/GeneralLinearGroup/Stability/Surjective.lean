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

/-! ## Row reduction and surjective stability -/

/-- Row reduction on `ι ⊕ Unit`: once `(a' + d • c) ⬝ᵥ b = 1`, an elementary matrix sends
`(a', d)` to `(0, 1)`. -/
private theorem exists_elementarySubgroup_vecMul_eq_inr {R ι : Type*} [Ring R] [Fintype ι]
    [DecidableEq ι] {a' c b : ι → R} {d : R} (hb : (fun i ↦ a' i + d * c i) ⬝ᵥ b = 1) :
    ∃ e ∈ elementarySubgroup (ι ⊕ Unit) R,
      Sum.elim a' (fun _ : Unit ↦ d) ᵥ* (e : Matrix (ι ⊕ Unit) (ι ⊕ Unit) R) =
        Sum.elim (0 : ι → R) (fun _ : Unit ↦ 1) := by
  let u : ι → R := fun i ↦ a' i + d * c i
  let e₁ : GL (ι ⊕ Unit) R := lowerBlockGL (Matrix.of fun _ j ↦ c j)
  let e₂ : GL (ι ⊕ Unit) R := upperBlockGL (Matrix.of fun i _ ↦ b i * (1 - d))
  let e₃ : GL (ι ⊕ Unit) R := lowerBlockGL (Matrix.of fun _ j ↦ -u j)
  have hv₁ : Sum.elim a' (fun _ : Unit ↦ d) ᵥ* (e₁ : Matrix _ _ R) =
      Sum.elim u (fun _ : Unit ↦ d) := by
    ext (j | ⟨⟩) <;> simp [e₁, u, vecMul, dotProduct, Fintype.sum_sum_type, Matrix.one_apply]
  have hv₂ : Sum.elim u (fun _ : Unit ↦ d) ᵥ* (e₂ : Matrix _ _ R) =
      Sum.elim u (fun _ : Unit ↦ 1) := by
    ext (j | ⟨⟩)
    · simp [e₂, vecMul, dotProduct, Fintype.sum_sum_type, Matrix.one_apply]
    · simp only [e₂, coe_upperBlockGL, vecMul, dotProduct, Fintype.sum_sum_type, Sum.elim_inl,
        fromBlocks_apply₁₂, Matrix.of_apply, Sum.elim_inr, Fintype.univ_punit,
        Finset.sum_singleton, fromBlocks_apply₂₂, Matrix.one_apply_eq, mul_one]
      have hsum : (∑ i : ι, u i * (b i * (1 - d))) = (u ⬝ᵥ b) * (1 - d) := by
        simp only [dotProduct, Finset.sum_mul, mul_assoc]
      rw [hsum, hb, one_mul, sub_add_cancel]
  have hv₃ : Sum.elim u (fun _ : Unit ↦ (1 : R)) ᵥ* (e₃ : Matrix _ _ R) =
      Sum.elim (0 : ι → R) (fun _ : Unit ↦ 1) := by
    ext (j | ⟨⟩) <;> simp [e₃, vecMul, dotProduct, Fintype.sum_sum_type, Matrix.one_apply]
  refine ⟨e₁ * e₂ * e₃, mul_mem (mul_mem (lowerBlockGL_mem_elementarySubgroup _)
    (upperBlockGL_mem_elementarySubgroup _)) (lowerBlockGL_mem_elementarySubgroup _), ?_⟩
  simp only [Units.val_mul, ← vecMul_vecMul, hv₁, hv₂, hv₃]

/-- Single-step surjective stability on `m ⊕ Unit`. -/
private theorem surjective_stability_unit {R m : Type*} [Ring R] [Fintype m] [DecidableEq m]
    {s : ℕ} (hR : HasStableRangeLE R s) (hm : s ≤ Fintype.card m) (g : GL (m ⊕ Unit) R) :
    ∃ (h : GL m R) (e : GL (m ⊕ Unit) R),
      e ∈ elementarySubgroup (m ⊕ Unit) R ∧ g = fromBlocksGL (h, (1 : GL Unit R)) * e := by
  let a' : m → R := fun j ↦ g (Sum.inr ()) (Sum.inl j)
  let d : R := g (Sum.inr ()) (Sum.inr ())
  have hrow : Sum.elim a' (fun _ : Unit ↦ d) =
      (g : Matrix (m ⊕ Unit) (m ⊕ Unit) R) (Sum.inr ()) := by
    ext (j | ⟨⟩) <;> rfl
  obtain ⟨c, hc⟩ := hR.exists_isUnimodular_add_mul hm (hrow ▸ g.isUnimodular_apply (Sum.inr ()))
  obtain ⟨b, hb⟩ := TauCeti.Module.isUnimodular_pi_iff.mp hc
  obtain ⟨e₀, he₀, he₀_mul⟩ := exists_elementarySubgroup_vecMul_eq_inr hb
  have hbot : ((g * e₀ : GL (m ⊕ Unit) R) : Matrix (m ⊕ Unit) (m ⊕ Unit) R) (Sum.inr ()) =
      Sum.elim (0 : m → R) (fun _ : Unit ↦ 1) := by
    rw [Units.val_mul, Matrix.mul_apply_eq_vecMul, ← hrow, he₀_mul]
  have h₂₁ : ((g * e₀ : GL (m ⊕ Unit) R) : Matrix (m ⊕ Unit) (m ⊕ Unit) R).toBlocks₂₁ = 0 := by
    ext ⟨⟩ j; simpa [toBlocks₂₁] using congrFun hbot (Sum.inl j)
  have h₂₂ : ((g * e₀ : GL (m ⊕ Unit) R) : Matrix (m ⊕ Unit) (m ⊕ Unit) R).toBlocks₂₂ = 1 := by
    ext ⟨⟩ ⟨⟩; simpa [toBlocks₂₂] using congrFun hbot (Sum.inr ())
  let h : GL m R := (g * e₀).toBlocks₁₁GL h₂₁ h₂₂
  let u : GL (m ⊕ Unit) R := upperBlockGL
    ((↑h⁻¹ : Matrix m m R) *
      ((g * e₀ : GL (m ⊕ Unit) R) : Matrix (m ⊕ Unit) (m ⊕ Unit) R).toBlocks₁₂)
  have hge₀ : g * e₀ = fromBlocksGL (h, (1 : GL Unit R)) * u :=
    (g * e₀).eq_fromBlocksGL_mul_upperBlockGL h₂₁ h₂₂
  refine ⟨h, u * e₀⁻¹, mul_mem (upperBlockGL_mem_elementarySubgroup _) (inv_mem he₀), ?_⟩
  calc g = g * e₀ * e₀⁻¹ := by group
    _ = fromBlocksGL (h, (1 : GL Unit R)) * (u * e₀⁻¹) := by rw [hge₀]; group

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
    let φ := (Equiv.sumAssoc n {x : k // x ≠ x₀} Unit).trans
      (Equiv.sumCongr (Equiv.refl n) (Equiv.subtypeNeSumPUnit.{0} x₀))
    have hcard_k' : Fintype.card {x : k // x ≠ x₀} = m := by
      rw [Fintype.card_subtype_compl, Fintype.card_subtype_eq]; omega
    obtain ⟨g₁, e₁, he₁, hg'⟩ := surjective_stability_unit hR
      (by rw [Fintype.card_sum]; omega) (φ.symm.reindexGL R g)
    obtain ⟨h, e₂, he₂, hg₁⟩ := ih {x : k // x ≠ x₀} hcard_k' g₁
    let e₀ := fromBlocksGL (e₂, (1 : GL Unit R)) * e₁
    have he₀ : e₀ ∈ elementarySubgroup ((n ⊕ {x : k // x ≠ x₀}) ⊕ Unit) R :=
      mul_mem (map_elementarySubgroup_le_elementarySubgroup ⟨e₂, he₂, rfl⟩) he₁
    refine ⟨h, φ.reindexGL R e₀, (φ.reindexGL_mem_elementarySubgroup_iff).mpr he₀, ?_⟩
    have hdecomp : φ.symm.reindexGL R g =
        fromBlocksGL (fromBlocksGL (h, (1 : GL {x : k // x ≠ x₀} R)), (1 : GL Unit R)) * e₀ := by
      rw [hg', hg₁]; simp only [e₀, ← mul_assoc, ← map_mul, Prod.mk_mul_mk, mul_one]
    have hre : φ.reindexGL R (fromBlocksGL (fromBlocksGL (h, (1 : GL {x : k // x ≠ x₀} R)),
        (1 : GL Unit R))) = fromBlocksGL (h, (1 : GL k R)) := by
      dsimp only [φ]
      rw [← Equiv.reindexGL_trans_reindexGL, MulEquiv.trans_apply,
        Equiv.reindexGL_sumAssoc_fromBlocksGL, Equiv.reindexGL_sumCongr_fromBlocksGL]
      simp [Prod.mk_one_one]
    calc g = φ.reindexGL R (φ.symm.reindexGL R g) := by simp
      _ = fromBlocksGL (h, 1) * φ.reindexGL R e₀ := by rw [hdecomp, map_mul, hre]

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
  let φ := Equiv.subtypeNeSumPUnit.{0} i
  have hcard : s ≤ Fintype.card {k : n // k ≠ i} := by
    rw [Fintype.card_subtype_compl, Fintype.card_subtype_eq]; omega
  obtain ⟨h, e, he, hginv⟩ := surjective_stability_unit hR hcard (φ.symm.reindexGL R g)⁻¹
  have hg' : φ.symm.reindexGL R g = e⁻¹ * fromBlocksGL (h⁻¹, (1 : GL Unit R)) := by
    calc φ.symm.reindexGL R g = ((φ.symm.reindexGL R g)⁻¹)⁻¹ := (inv_inv _).symm
      _ = e⁻¹ * (fromBlocksGL (h, (1 : GL Unit R)))⁻¹ := by rw [hginv, _root_.mul_inv_rev]
      _ = e⁻¹ * fromBlocksGL (h⁻¹, (1 : GL Unit R)) := by congr 1; rw [← map_inv]; simp
  let Y : Matrix Unit {k : n // k ≠ i} R := Matrix.single () ⟨j, hij.symm⟩ a
  have htr : φ.symm.reindexGL R (transvectionUnit hij a) = lowerBlockGL Y := by
    refine Units.ext ?_; ext (p | ⟨⟩) (q | ⟨⟩)
    · simp [φ, coe_transvectionUnit_eq_one_add_single, Matrix.one_apply, Subtype.ext_iff,
        p.property.symm]
    · simp [φ, coe_transvectionUnit_eq_one_add_single, p.property, p.property.symm]
    · simp [φ, Y, coe_transvectionUnit_eq_one_add_single, single_apply, Subtype.ext_iff,
        q.property.symm]
    · simp [φ, coe_transvectionUnit_eq_one_add_single, hij.symm]
  have hmid : fromBlocksGL (h⁻¹, (1 : GL Unit R)) * lowerBlockGL Y *
      (fromBlocksGL (h⁻¹, (1 : GL Unit R)))⁻¹ =
      lowerBlockGL (Y * (h : Matrix {k : n // k ≠ i} {k : n // k ≠ i} R)) := by
    refine Units.ext ?_
    have hh : (↑(fromBlocksGL (h⁻¹, (1 : GL Unit R)))⁻¹ :
        Matrix ({k : n // k ≠ i} ⊕ Unit) ({k : n // k ≠ i} ⊕ Unit) R) =
        fromBlocks (h : Matrix {k : n // k ≠ i} {k : n // k ≠ i} R) 0 0 1 := by
      rw [← map_inv]; simp
    rw [Units.val_mul, Units.val_mul, hh]; simp [fromBlocks_multiply]
  have hconj : φ.symm.reindexGL R (g * transvectionUnit hij a * g⁻¹) =
      e⁻¹ * lowerBlockGL (Y * (h : Matrix {k : n // k ≠ i} {k : n // k ≠ i} R)) * e := by
    rw [map_mul, map_mul, map_inv, hg', htr]
    calc _ = e⁻¹ * (fromBlocksGL (h⁻¹, (1 : GL Unit R)) * lowerBlockGL Y *
          (fromBlocksGL (h⁻¹, (1 : GL Unit R)))⁻¹) * e := by group
      _ = _ := by rw [hmid]
  have hmem := mul_mem (mul_mem (inv_mem he) (lowerBlockGL_mem_elementarySubgroup
    (Y * (h : Matrix {k : n // k ≠ i} {k : n // k ≠ i} R)))) he
  simpa [← hconj] using (φ.reindexGL_mem_elementarySubgroup_iff).mpr hmem

/-! ## Unimodular orbits and rank-one unipotent matrices -/

/-- Over a ring of Bass stable range at most `s`, the elementary subgroup `elementarySubgroup m R`
acts transitively on unimodular rows whenever `s + 1 ≤ Fintype.card m`: every unimodular row can
be sent to any standard basis vector `Pi.single i₀ 1`. -/
theorem HasStableRangeLE.exists_vecMul_elementarySubgroup_eq_single {R m : Type*} [Ring R]
    [Fintype m] [DecidableEq m] {s : ℕ} (hR : HasStableRangeLE R s)
    (hm : s + 1 ≤ Fintype.card m) {a : m → R} (ha : Module.IsUnimodular R a) (i₀ : m) :
    ∃ e ∈ elementarySubgroup m R, a ᵥ* (e : Matrix m m R) = Pi.single i₀ 1 := by
  let φ := Equiv.subtypeNeSumPUnit.{0} i₀
  obtain ⟨c, hc⟩ := hR.exists_isUnimodular_add_mul_subtype_ne hm ha i₀
  obtain ⟨b, hb⟩ := TauCeti.Module.isUnimodular_pi_iff.mp hc
  obtain ⟨e₀, he₀, he₀_mul⟩ := exists_elementarySubgroup_vecMul_eq_inr hb
  refine ⟨φ.reindexGL R e₀, (φ.reindexGL_mem_elementarySubgroup_iff).mpr he₀, ?_⟩
  ext k; obtain ⟨x, rfl⟩ := φ.surjective k
  have hmul : (a ᵥ* (φ.reindexGL R e₀ : Matrix m m R)) (φ x) =
      (Sum.elim (fun i : {i : m // i ≠ i₀} ↦ a i.val) (fun _ : Unit ↦ a i₀) ᵥ*
        (e₀ : Matrix _ _ R)) x := by
    simp only [Equiv.coe_reindexGL, submatrix_apply, vecMul, dotProduct]
    rw [← φ.sum_comp]
    simp only [φ.symm_apply_apply]
    exact Fintype.sum_congr _ _ fun y ↦ by rcases y with i | ⟨⟩ <;> simp [φ]
  rw [hmul, he₀_mul]
  rcases x with i | ⟨⟩
  · simp [φ, i.property]
  · simp [φ]

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
  set u' : m → R := (↑e⁻¹ : Matrix m m R) *ᵥ u with hu'_def
  have hu'0 : u' i₀ = 0 := by
    calc u' i₀ = Pi.single i₀ (1 : R) ⬝ᵥ u' := by simp
      _ = (v ᵥ* (e : Matrix m m R)) ⬝ᵥ ((↑e⁻¹ : Matrix m m R) *ᵥ u) := by rw [← hve, hu'_def]
      _ = 0 := by rw [← dotProduct_mulVec, mulVec_mulVec, Units.mul_inv, one_mulVec, hvu]
  let φ := Equiv.subtypeNeSumPUnit.{0} i₀
  let U : GL ({i : m // i ≠ i₀} ⊕ Unit) R :=
    upperBlockGL (Matrix.of fun (i : {i : m // i ≠ i₀}) (_ : Unit) ↦ -u' i.val)
  have hconj : e⁻¹ * g * e = φ.reindexGL R U := by
    refine Units.ext ?_
    rw [Units.val_mul, Units.val_mul, coe_oneSubVecMulVecGL, Matrix.mul_sub, Matrix.mul_one,
      Matrix.sub_mul, Units.inv_mul, Matrix.mul_vecMulVec, Matrix.vecMulVec_mul, ← hu'_def, hve]
    ext p q; obtain ⟨p, rfl⟩ := φ.surjective p; obtain ⟨q, rfl⟩ := φ.surjective q
    simp only [Equiv.coe_reindexGL, submatrix_apply, φ.symm_apply_apply]
    rcases p with i | ⟨⟩ <;> rcases q with j | ⟨⟩
    · simp [φ, U, vecMulVec_apply, Matrix.one_apply, Subtype.ext_iff, j.property]
    · simp [φ, U, vecMulVec_apply, i.property]
    · simp [φ, U, vecMulVec_apply, j.property, j.property.symm]
    · simp [φ, U, vecMulVec_apply, hu'0]
  have hg : g = e * (e⁻¹ * g * e) * e⁻¹ := by group
  rw [hg, hconj]
  exact mul_mem (mul_mem he ((φ.reindexGL_mem_elementarySubgroup_iff).mpr
    (upperBlockGL_mem_elementarySubgroup _))) (inv_mem he)

end TauCeti

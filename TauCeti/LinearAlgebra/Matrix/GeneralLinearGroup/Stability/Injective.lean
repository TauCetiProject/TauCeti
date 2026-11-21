/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Elementary
public import TauCeti.RingTheory.StableRange
import TauCeti.Data.Matrix.Block
import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Stability.Surjective

/-!
# Vaserstein's injective stability theorem for general linear groups

Over a possibly noncommutative ring `R` of Bass stable range at most `s`
(`TauCeti.HasStableRangeLE R s`), whenever `s + 1 ≤ Fintype.card n`, an invertible matrix
`g : GL n R` whose block stabilization `fromBlocks g 0 0 1` lies in
`elementarySubgroup (n ⊕ k) R` already lies in `elementarySubgroup n R`.

The proof constructs Vaserstein's right `E_{m + 1}(R)`-invariant retraction
`GL (m ⊕ Unit) R → GL m R ⧸ E m R` by shortening the bottom row of `A : GL (m ⊕ Unit) R` via
lower block-unipotent matrices, clearing the bottom row to `(0, 1)`, extracting the upper-left
`m × m` block modulo `E m R`, and proving right-invariance under all elementary transvections on
`m ⊕ Unit`.

## Main results

* `TauCeti.injective_stability`: Vaserstein's injective stability theorem for `GL n R`.

## References

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

/-! ## Block-vector helpers -/

section BlockVec

variable {R m : Type*} [Ring R] [Fintype m] [DecidableEq m]

private abbrev botRow (A : GL (m ⊕ Unit) R) : m → R := fun j ↦ A (Sum.inr ()) (Sum.inl j)
private abbrev botEntry (A : GL (m ⊕ Unit) R) : R := A (Sum.inr ()) (Sum.inr ())
private abbrev lowerVec (c : m → R) : GL (m ⊕ Unit) R := lowerBlockGL (Matrix.of fun _ j ↦ c j)
private abbrev upperVec (y : m → R) : GL (m ⊕ Unit) R := upperBlockGL (Matrix.of fun i _ ↦ y i)
private abbrev blockOne (e : GL m R) : GL (m ⊕ Unit) R := fromBlocksGL (e, (1 : GL Unit R))

private theorem lowerVec_mul (x y : m → R) : lowerVec x * lowerVec y = lowerVec (x + y) := by
  rw [← lowerBlockGL_add]; rfl

private theorem lowerVec_inv (x : m → R) : (lowerVec x)⁻¹ = lowerVec (-x) := by
  rw [lowerBlockGL_inv]; rfl

private theorem lowerVec_zero : lowerVec (0 : m → R) = 1 := lowerBlockGL_zero

private theorem upperVec_mul (x y : m → R) : upperVec x * upperVec y = upperVec (x + y) := by
  rw [← upperBlockGL_add]; rfl

private theorem upperVec_inv (x : m → R) : (upperVec x)⁻¹ = upperVec (-x) := by
  rw [upperBlockGL_inv]; rfl

private theorem upperVec_zero : upperVec (0 : m → R) = 1 := upperBlockGL_zero

private theorem botRow_mul_lowerVec (A : GL (m ⊕ Unit) R) (c : m → R) :
    botRow (A * lowerVec c) = fun j ↦ botRow A j + botEntry A * c j := by
  ext j
  simp [botRow, botEntry, Units.val_mul, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply]

private theorem botEntry_mul_lowerVec (A : GL (m ⊕ Unit) R) (c : m → R) :
    botEntry (A * lowerVec c) = botEntry A := by
  simp [botEntry, Units.val_mul, Matrix.mul_apply, Fintype.sum_sum_type]

private theorem botRow_mul_upperVec (A : GL (m ⊕ Unit) R) (y : m → R) :
    botRow (A * upperVec y) = botRow A := by
  ext j
  simp [botRow, Units.val_mul, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply]

private theorem botEntry_mul_upperVec (A : GL (m ⊕ Unit) R) (y : m → R) :
    botEntry (A * upperVec y) = botRow A ⬝ᵥ y + botEntry A := by
  simp [botRow, botEntry, Units.val_mul, Matrix.mul_apply, Fintype.sum_sum_type, dotProduct]

private theorem botRow_mul_blockOne (A : GL (m ⊕ Unit) R) (e : GL m R) :
    botRow (A * blockOne e) = botRow A ᵥ* (e : Matrix m m R) := by
  ext j; simp [botRow, Units.val_mul, Matrix.mul_apply, Fintype.sum_sum_type, vecMul, dotProduct]

private theorem botEntry_mul_blockOne (A : GL (m ⊕ Unit) R) (e : GL m R) :
    botEntry (A * blockOne e) = botEntry A := by
  simp [botEntry, Units.val_mul, Matrix.mul_apply, Fintype.sum_sum_type]

private theorem lowerVec_mul_blockOne (x : m → R) (e : GL m R) :
    lowerVec x * blockOne e = blockOne e * lowerVec (x ᵥ* (e : Matrix m m R)) := by
  refine Units.ext ?_
  rw [Units.val_mul, Units.val_mul, coe_lowerBlockGL, coe_fromBlocksGL, coe_lowerBlockGL]
  simp only [fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add,
    Matrix.one_mul, Matrix.mul_one, Units.val_one]
  refine congrArg (fun M ↦ fromBlocks (e : Matrix m m R) 0 M 1) ?_
  ext ⟨⟩ j
  simp [Matrix.mul_apply, vecMul, dotProduct]

private theorem blockOne_mul_upperVec (e : GL m R) (y : m → R) :
    blockOne e * upperVec y = upperVec ((e : Matrix m m R) *ᵥ y) * blockOne e := by
  refine Units.ext ?_
  rw [Units.val_mul, Units.val_mul, coe_fromBlocksGL, coe_upperBlockGL, coe_upperBlockGL]
  simp only [fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add,
    Matrix.one_mul, Matrix.mul_one, Units.val_one]
  refine congrArg (fun M ↦ fromBlocks (e : Matrix m m R) M 0 1) ?_
  ext i ⟨⟩
  simp [Matrix.mul_apply, mulVec, dotProduct]

private theorem toBlocks₂₁_apply (A : GL (m ⊕ Unit) R) (j : m) :
    (A : Matrix (m ⊕ Unit) (m ⊕ Unit) R).toBlocks₂₁ () j = botRow A j :=
  (rfl)

private theorem toBlocks₂₂_apply (A : GL (m ⊕ Unit) R) :
    (A : Matrix (m ⊕ Unit) (m ⊕ Unit) R).toBlocks₂₂ () () = botEntry A :=
  (rfl)

private theorem isUnimodular_sumElim_bot (A : GL (m ⊕ Unit) R) :
    Module.IsUnimodular R (Sum.elim (botRow A) (fun _ : Unit ↦ botEntry A)) := by
  have h : Sum.elim (botRow A) (fun _ : Unit ↦ botEntry A) = fun j ↦ A (Sum.inr ()) j := by
    ext (j | ⟨⟩) <;> rfl
  exact h ▸ A.isUnimodular_apply (Sum.inr ())

/-- Right elementary factor clearing the bottom row `(a, d)` of `A : GL (m ⊕ Unit) R` to `(0, 1)`
from a right-inverse witness `b` with `a ⬝ᵥ b = 1`. -/
private def clearLastRowFactor (A : GL (m ⊕ Unit) R) (b : m → R) : GL (m ⊕ Unit) R :=
  upperVec (fun i ↦ b i * (1 - botEntry A)) * lowerVec (-botRow A)

private theorem toBlocks_mul_clearLastRowFactor {A : GL (m ⊕ Unit) R} {b : m → R}
    (hb : botRow A ⬝ᵥ b = 1) :
    ((A * clearLastRowFactor A b : GL (m ⊕ Unit) R) :
        Matrix (m ⊕ Unit) (m ⊕ Unit) R).toBlocks₂₁ = 0 ∧
      ((A * clearLastRowFactor A b : GL (m ⊕ Unit) R) :
        Matrix (m ⊕ Unit) (m ⊕ Unit) R).toBlocks₂₂ = 1 := by
  let A₁ := A * upperVec (fun i ↦ b i * (1 - botEntry A))
  have hrow₁ : botRow A₁ = botRow A := botRow_mul_upperVec A _
  have hd₁ : botEntry A₁ = 1 := by
    have hsum : (botRow A ⬝ᵥ fun i ↦ b i * (1 - botEntry A)) =
        (botRow A ⬝ᵥ b) * (1 - botEntry A) := by
      simp only [dotProduct, Finset.sum_mul, mul_assoc]
    rw [botEntry_mul_upperVec, hsum, hb, one_mul, sub_add_cancel]
  have hfac : A * clearLastRowFactor A b = A₁ * lowerVec (-botRow A) := by
    rw [clearLastRowFactor, mul_assoc]
  refine ⟨?_, ?_⟩
  · ext ⟨⟩ j
    rw [toBlocks₂₁_apply, hfac, botRow_mul_lowerVec, hrow₁, hd₁]
    simp
  · ext ⟨⟩ ⟨⟩
    rw [toBlocks₂₂_apply, hfac, botEntry_mul_lowerVec, hd₁, Matrix.one_apply_eq]

end BlockVec

/-! ## Left rank-one unipotent lemma -/

/-- If `a ⬝ᵥ b = 1` and `s + 1 ≤ Fintype.card m`, some `e ∈ elementarySubgroup m R` sends `b`
under `e⁻¹ *ᵥ ·` to `Pi.single i₀ 1`. -/
private theorem exists_elementarySubgroup_inv_mulVec_eq_single {R m : Type*} [Ring R]
    [Fintype m] [DecidableEq m] {s : ℕ} (hR : HasStableRangeLE R s)
    (hm : s + 1 ≤ Fintype.card m) {a b : m → R} (hab : a ⬝ᵥ b = 1) (i₀ : m) :
    ∃ e ∈ elementarySubgroup m R, (↑e⁻¹ : Matrix m m R) *ᵥ b = Pi.single i₀ 1 := by
  obtain ⟨e₁, he₁, hae₁⟩ := hR.exists_vecMul_elementarySubgroup_eq_single hm
    (TauCeti.Module.isUnimodular_pi_iff.mpr ⟨b, hab⟩) i₀
  set b₁ : m → R := (↑e₁⁻¹ : Matrix m m R) *ᵥ b with hb₁_def
  have hb₁0 : b₁ i₀ = 1 := by
    calc b₁ i₀ = Pi.single i₀ (1 : R) ⬝ᵥ b₁ := by simp
      _ = (a ᵥ* (e₁ : Matrix m m R)) ⬝ᵥ ((↑e₁⁻¹ : Matrix m m R) *ᵥ b) := by rw [← hae₁, hb₁_def]
      _ = 1 := by rw [← dotProduct_mulVec, mulVec_mulVec, Units.mul_inv, one_mulVec, hab]
  let φ := Equiv.subtypeNeSumPUnit.{0} i₀
  let e₂ : GL m R := φ.reindexGL R (upperVec fun i ↦ b₁ i.val)
  refine ⟨e₁ * e₂, mul_mem he₁ ((φ.reindexGL_mem_elementarySubgroup_iff).mpr
    (upperBlockGL_mem_elementarySubgroup _)), ?_⟩
  rw [_root_.mul_inv_rev, Units.val_mul, ← mulVec_mulVec, ← hb₁_def]
  ext k; obtain ⟨p, rfl⟩ := φ.surjective k
  have he₂_inv : e₂⁻¹ = φ.reindexGL R (upperVec (-(fun i : {i : m // i ≠ i₀} ↦ b₁ i.val))) := by
    rw [← map_inv, upperVec_inv]
  rw [he₂_inv]
  simp only [Equiv.coe_reindexGL, submatrix_apply, mulVec, dotProduct]
  rw [← φ.sum_comp]; simp only [φ.symm_apply_apply]
  rcases p with i | ⟨⟩
  · simp [φ, Fintype.sum_sum_type, Matrix.one_apply, hb₁0, i.property]
  · simp [φ, Fintype.sum_sum_type, hb₁0]

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
  set x' : m → R := x ᵥ* (e : Matrix m m R) with hx'_def
  have hx'0 : x' i₀ = 0 := by
    calc x' i₀ = x' ⬝ᵥ Pi.single i₀ 1 := by simp
      _ = (x ᵥ* (e : Matrix m m R)) ⬝ᵥ ((↑e⁻¹ : Matrix m m R) *ᵥ b) := by rw [← heb, hx'_def]
      _ = 0 := by rw [← dotProduct_mulVec, mulVec_mulVec, Units.mul_inv, one_mulVec, hxb]
  let φ := Equiv.subtypeNeSumPUnit.{0} i₀
  let L := lowerVec (R := R) (m := {i : m // i ≠ i₀}) (fun j ↦ -r * x' j.val)
  have hconj : e⁻¹ * g * e = φ.reindexGL R L := by
    refine Units.ext ?_
    have hmulr : (↑e⁻¹ : Matrix m m R) *ᵥ (fun i ↦ b i * r) =
        fun i ↦ (Pi.single i₀ (1 : R) : m → R) i * r := by
      ext i
      calc ((↑e⁻¹ : Matrix m m R) *ᵥ fun k ↦ b k * r) i
          = ((↑e⁻¹ : Matrix m m R) *ᵥ b) i * r := by
            simp only [mulVec, dotProduct, Finset.sum_mul, mul_assoc]
        _ = (Pi.single i₀ (1 : R) : m → R) i * r := by rw [heb]
    rw [Units.val_mul, Units.val_mul, coe_oneSubVecMulVecGL, Matrix.mul_sub, Matrix.mul_one,
      Matrix.sub_mul, Units.inv_mul, Matrix.mul_vecMulVec, Matrix.vecMulVec_mul, hmulr, ← hx'_def]
    ext p q; obtain ⟨p, rfl⟩ := φ.surjective p; obtain ⟨q, rfl⟩ := φ.surjective q
    simp only [Equiv.coe_reindexGL, submatrix_apply, φ.symm_apply_apply]
    rcases p with i | ⟨⟩ <;> rcases q with j | ⟨⟩
    · simp [φ, L, vecMulVec_apply, Pi.single_apply, Matrix.one_apply, Subtype.ext_iff, i.property]
    · simp [φ, L, vecMulVec_apply, Pi.single_apply, i.property]
    · simp [φ, L, vecMulVec_apply, j.property.symm]
    · simp [φ, L, vecMulVec_apply, hx'0]
  have hg : g = e * (e⁻¹ * g * e) * e⁻¹ := by group
  rw [hg, hconj]
  exact mul_mem (mul_mem he ((φ.reindexGL_mem_elementarySubgroup_iff).mpr
    (lowerBlockGL_mem_elementarySubgroup _))) (inv_mem he)

/-! ## Vaserstein's coset retraction and injective stability -/

section Vaserstein

variable {R m : Type*} [Ring R] [Fintype m] [DecidableEq m]

/-- Upper-left `m × m` block extracted after clearing the bottom row of `A : GL (m ⊕ Unit) R`
using a right-inverse witness `b` for its bottom-left row. -/
private def vasersteinBlock (A : GL (m ⊕ Unit) R) (b : m → R) (hb : botRow A ⬝ᵥ b = 1) :
    GL m R :=
  (A * clearLastRowFactor A b).toBlocks₁₁GL
    (toBlocks_mul_clearLastRowFactor hb).1 (toBlocks_mul_clearLastRowFactor hb).2

/-- Comparing two `vasersteinBlock` extractions reduces to the `(1, 1)` block of the ratio of the
row-cleared matrices, where the outer factors `A₁` and `A₂` interact directly. -/
private theorem coe_vasersteinBlock_inv_mul {A₁ A₂ : GL (m ⊕ Unit) R} {b₁ b₂ : m → R}
    (hb₁ : botRow A₁ ⬝ᵥ b₁ = 1) (hb₂ : botRow A₂ ⬝ᵥ b₂ = 1) :
    (((vasersteinBlock A₁ b₁ hb₁)⁻¹ * vasersteinBlock A₂ b₂ hb₂ : GL m R) : Matrix m m R) =
      (((A₁ * clearLastRowFactor A₁ b₁)⁻¹ * (A₂ * clearLastRowFactor A₂ b₂) :
        GL (m ⊕ Unit) R) : Matrix (m ⊕ Unit) (m ⊕ Unit) R).toBlocks₁₁ := by
  dsimp only [vasersteinBlock]
  rw [Units.val_mul, GeneralLinearGroup.coe_toBlocks₁₁GL_inv, GeneralLinearGroup.coe_toBlocks₁₁GL]
  conv_rhs =>
    rw [Units.val_mul, Matrix.toBlocks₁₁_mul, (toBlocks_mul_clearLastRowFactor hb₂).1,
      Matrix.mul_zero, add_zero]

private theorem toBlocks₁₁_lower_upper_lower (a u : m → R) :
    ((lowerVec a * upperVec u * lowerVec (-a) : GL (m ⊕ Unit) R) :
      Matrix (m ⊕ Unit) (m ⊕ Unit) R).toBlocks₁₁ = 1 - vecMulVec u a := by
  ext i j
  simp [Units.val_mul, fromBlocks_multiply, Matrix.mul_apply, vecMulVec_apply, sub_eq_add_neg]

/-- Independence of `vasersteinBlock` modulo `elementarySubgroup m R` from the witness `b`. -/
private theorem vasersteinBlock_inv_mul_mem {s : ℕ} (hR : HasStableRangeLE R s)
    (hm : s + 1 ≤ Fintype.card m) (A : GL (m ⊕ Unit) R) {b₁ b₂ : m → R}
    (hb₁ : botRow A ⬝ᵥ b₁ = 1) (hb₂ : botRow A ⬝ᵥ b₂ = 1) :
    (vasersteinBlock A b₁ hb₁)⁻¹ * vasersteinBlock A b₂ hb₂ ∈ elementarySubgroup m R := by
  let u : m → R := fun i ↦ (b₂ i - b₁ i) * (1 - botEntry A)
  have ha : Module.IsUnimodular R (botRow A) := TauCeti.Module.isUnimodular_pi_iff.mpr ⟨b₁, hb₁⟩
  have hau : botRow A ⬝ᵥ u = 0 := by
    have hsum : botRow A ⬝ᵥ u = (botRow A ⬝ᵥ b₂ - botRow A ⬝ᵥ b₁) * (1 - botEntry A) := by
      simp only [u, dotProduct, mul_sub, sub_mul, Finset.sum_sub_distrib, Finset.sum_mul, mul_assoc]
    rw [hsum, hb₁, hb₂, sub_self, zero_mul]
  suffices (vasersteinBlock A b₁ hb₁)⁻¹ * vasersteinBlock A b₂ hb₂ =
      oneSubVecMulVecGL (-1) u (botRow A) (by simp [hau]) from
    this ▸ hR.oneSubVecMulVecGL_mem_elementarySubgroup hm ha hau
  refine Units.ext ?_; rw [coe_vasersteinBlock_inv_mul hb₁ hb₂, coe_oneSubVecMulVecGL]
  have hmid : (A * clearLastRowFactor A b₁)⁻¹ * (A * clearLastRowFactor A b₂) =
      lowerVec (botRow A) * upperVec u * lowerVec (-botRow A) := by
    have hu : upperVec (-fun i ↦ b₁ i * (1 - botEntry A)) *
        upperVec (fun i ↦ b₂ i * (1 - botEntry A)) = upperVec u := by
      rw [upperVec_mul]; congr 1; ext i; simp [u, sub_mul, neg_add_eq_sub]
    simp only [clearLastRowFactor, _root_.mul_inv_rev, lowerVec_inv, upperVec_inv, neg_neg,
      mul_assoc, inv_mul_cancel_left]
    rw [← mul_assoc (upperVec _), hu]
  rw [hmid, toBlocks₁₁_lower_upper_lower]

/-- Partial Vaserstein map into left cosets `GL m R ⧸ elementarySubgroup m R` for matrices in
`GL (m ⊕ Unit) R` whose bottom-left row is unimodular. -/
private def vasersteinPsi (A : GL (m ⊕ Unit) R) (ha : Module.IsUnimodular R (botRow A)) :
    GL m R ⧸ elementarySubgroup m R :=
  have hex := TauCeti.Module.isUnimodular_pi_iff.mp ha
  QuotientGroup.mk (vasersteinBlock A hex.choose hex.choose_spec)

private theorem vasersteinPsi_congr {A₁ A₂ : GL (m ⊕ Unit) R} (h : A₁ = A₂)
    (ha₁ : Module.IsUnimodular R (botRow A₁)) (ha₂ : Module.IsUnimodular R (botRow A₂)) :
    vasersteinPsi A₁ ha₁ = vasersteinPsi A₂ ha₂ := by
  subst h; rfl

private theorem vasersteinPsi_eq_mk {s : ℕ} (hR : HasStableRangeLE R s)
    (hm : s + 1 ≤ Fintype.card m) (A : GL (m ⊕ Unit) R)
    (ha : Module.IsUnimodular R (botRow A)) {b : m → R} (hb : botRow A ⬝ᵥ b = 1) :
    vasersteinPsi A ha = QuotientGroup.mk (vasersteinBlock A b hb) := by
  rw [vasersteinPsi, QuotientGroup.eq]
  exact vasersteinBlock_inv_mul_mem hR hm A _ hb

private theorem vasersteinPsi_blockOne_mul_lowerVec {s : ℕ} (hR : HasStableRangeLE R s)
    (hm : s + 1 ≤ Fintype.card m) (g : GL m R) (c : m → R)
    (hc : Module.IsUnimodular R (botRow (blockOne g * lowerVec c))) :
    vasersteinPsi (blockOne g * lowerVec c) hc = QuotientGroup.mk g := by
  obtain ⟨b, hb⟩ := TauCeti.Module.isUnimodular_pi_iff.mp hc
  rw [vasersteinPsi_eq_mk hR hm _ hc hb]
  congr 1; refine Units.ext ?_
  dsimp only [vasersteinBlock]
  rw [GeneralLinearGroup.coe_toBlocks₁₁GL]
  have hd : botEntry (blockOne g * lowerVec c) = 1 := by
    rw [botEntry_mul_lowerVec]; simp [botEntry, blockOne]
  have ha : botRow (blockOne g * lowerVec c) = c := by
    rw [botRow_mul_lowerVec]; ext j; simp [botRow, botEntry, blockOne]
  have hclear : blockOne g * lowerVec c * clearLastRowFactor (blockOne g * lowerVec c) b =
      blockOne g := by
    have hzero : (fun i ↦ b i * (0 : R)) = 0 := funext fun i ↦ mul_zero (b i)
    rw [clearLastRowFactor, hd, sub_self, hzero, upperVec_zero, one_mul, ha, mul_assoc,
      lowerVec_mul, add_neg_cancel, lowerVec_zero, mul_one]
  rw [hclear, coe_fromBlocksGL]; ext i j; simp

/-- Right-invariance of `vasersteinPsi` under upper block unipotent matrices. -/
private theorem vasersteinPsi_mul_upperVec {s : ℕ} (hR : HasStableRangeLE R s)
    (hm : s + 1 ≤ Fintype.card m) (A : GL (m ⊕ Unit) R) (y : m → R)
    (ha : Module.IsUnimodular R (botRow A))
    (ha₂ : Module.IsUnimodular R (botRow (A * upperVec y))) :
    vasersteinPsi (A * upperVec y) ha₂ = vasersteinPsi A ha := by
  obtain ⟨b, hb⟩ := TauCeti.Module.isUnimodular_pi_iff.mp ha
  have hab : botRow A ⬝ᵥ b = 1 := hb
  have hb₂ : botRow (A * upperVec y) ⬝ᵥ b = 1 := by rw [botRow_mul_upperVec]; exact hab
  rw [vasersteinPsi_eq_mk hR hm _ ha₂ hb₂, vasersteinPsi_eq_mk hR hm A ha hab, eq_comm,
    QuotientGroup.eq]
  let w : m → R := fun i ↦ y i - b i * (botRow A ⬝ᵥ y)
  have haw : botRow A ⬝ᵥ w = 0 := by
    have hdot : (botRow A ⬝ᵥ fun i ↦ b i * (botRow A ⬝ᵥ y)) =
        (botRow A ⬝ᵥ b) * (botRow A ⬝ᵥ y) := by
      simp only [dotProduct, Finset.sum_mul, mul_assoc]
    calc botRow A ⬝ᵥ w = botRow A ⬝ᵥ y - (botRow A ⬝ᵥ fun i ↦ b i * (botRow A ⬝ᵥ y)) := by
          simp [w, dotProduct, mul_sub, Finset.sum_sub_distrib]
      _ = 0 := by rw [hdot, hab, one_mul, sub_self]
  suffices (vasersteinBlock A b hab)⁻¹ * vasersteinBlock (A * upperVec y) b hb₂ =
      oneSubVecMulVecGL (-1) w (botRow A) (by simp [haw]) from
    this ▸ hR.oneSubVecMulVecGL_mem_elementarySubgroup hm ha haw
  refine Units.ext ?_; rw [coe_vasersteinBlock_inv_mul hab hb₂, coe_oneSubVecMulVecGL]
  have hmid : (A * clearLastRowFactor A b)⁻¹ *
      (A * upperVec y * clearLastRowFactor (A * upperVec y) b) =
      lowerVec (botRow A) * upperVec w * lowerVec (-botRow A) := by
    have hw : upperVec (-fun i ↦ b i * (1 - botEntry A)) * upperVec y *
        upperVec (fun i ↦ b i * (1 - (botRow A ⬝ᵥ y + botEntry A))) = upperVec w := by
      rw [upperVec_mul, upperVec_mul]; congr 1; ext i; simp [w, mul_sub, mul_add]; abel
    simp only [clearLastRowFactor, _root_.mul_inv_rev, lowerVec_inv, upperVec_inv, neg_neg,
      botRow_mul_upperVec, botEntry_mul_upperVec, mul_assoc, inv_mul_cancel_left]
    rw [← mul_assoc (upperVec _), ← mul_assoc (upperVec _ * upperVec y), hw]
  rw [hmid, toBlocks₁₁_lower_upper_lower]

/-- Right-invariance of `vasersteinPsi` under `blockOne e` for `e ∈ E m R`. -/
private theorem vasersteinPsi_mul_blockOne {s : ℕ} (hR : HasStableRangeLE R s)
    (hm : s + 1 ≤ Fintype.card m) (A : GL (m ⊕ Unit) R) {e : GL m R}
    (he : e ∈ elementarySubgroup m R) (ha : Module.IsUnimodular R (botRow A))
    (ha₂ : Module.IsUnimodular R (botRow (A * blockOne e))) :
    vasersteinPsi (A * blockOne e) ha₂ = vasersteinPsi A ha := by
  obtain ⟨b, hb⟩ := TauCeti.Module.isUnimodular_pi_iff.mp ha
  let b₂ : m → R := (↑e⁻¹ : Matrix m m R) *ᵥ b
  have hb₂ : botRow (A * blockOne e) ⬝ᵥ b₂ = 1 := by
    rw [botRow_mul_blockOne, ← dotProduct_mulVec, mulVec_mulVec, Units.mul_inv, one_mulVec]
    exact hb
  rw [vasersteinPsi_eq_mk hR hm _ ha₂ hb₂, vasersteinPsi_eq_mk hR hm A ha hb, eq_comm,
    QuotientGroup.eq]
  suffices (vasersteinBlock A b hb)⁻¹ * vasersteinBlock (A * blockOne e) b₂ hb₂ = e by
    rwa [this]
  refine Units.ext ?_; rw [coe_vasersteinBlock_inv_mul hb hb₂]
  have h12 : ((e : Matrix m m R) *ᵥ fun i ↦ b₂ i * (1 - botEntry A)) =
      fun i ↦ b i * (1 - botEntry A) := by
    ext i
    calc ((e : Matrix m m R) *ᵥ fun x ↦ b₂ x * (1 - botEntry A)) i
        = ((e : Matrix m m R) *ᵥ ((↑e⁻¹ : Matrix m m R) *ᵥ b)) i * (1 - botEntry A) := by
          simp only [b₂, mulVec, dotProduct, Finset.sum_mul, mul_assoc]
      _ = b i * (1 - botEntry A) := by rw [mulVec_mulVec, Units.mul_inv, one_mulVec]
  have hcomm : blockOne e * clearLastRowFactor (A * blockOne e) b₂ =
      clearLastRowFactor A b * blockOne e := by
    rw [clearLastRowFactor, clearLastRowFactor, botEntry_mul_blockOne, botRow_mul_blockOne,
      ← mul_assoc, blockOne_mul_upperVec, h12, mul_assoc, ← neg_vecMul, ← lowerVec_mul_blockOne,
      ← mul_assoc]
  have hmid : (A * clearLastRowFactor A b)⁻¹ *
      (A * blockOne e * clearLastRowFactor (A * blockOne e) b₂) = blockOne e := by
    calc _ = (clearLastRowFactor A b)⁻¹ *
          (blockOne e * clearLastRowFactor (A * blockOne e) b₂) := by group
      _ = (clearLastRowFactor A b)⁻¹ * (clearLastRowFactor A b * blockOne e) := by rw [hcomm]
      _ = blockOne e := by group
  rw [hmid, coe_fromBlocksGL]; ext i j; simp

private theorem toBlocks₁₁_conj_lowerVec_of_dotProduct_eq_zero (a₁ a₂ u x : m → R)
    (hxu : x ⬝ᵥ u = 0) :
    ((lowerVec a₁ * upperVec (-u) * lowerVec x * upperVec u * lowerVec a₂ : GL (m ⊕ Unit) R) :
      Matrix (m ⊕ Unit) (m ⊕ Unit) R).toBlocks₁₁ = 1 - vecMulVec u x := by
  set U₀ : Matrix m Unit R := Matrix.of fun i _ ↦ u i
  set X₀ : Matrix Unit m R := Matrix.of fun _ j ↦ x j
  have hXU : X₀ * U₀ = 0 := by
    ext ⟨⟩ ⟨⟩; simpa [X₀, U₀, Matrix.mul_apply, dotProduct] using hxu
  have hmid : ((upperVec (-u) * lowerVec x * upperVec u : GL (m ⊕ Unit) R) :
      Matrix (m ⊕ Unit) (m ⊕ Unit) R) = fromBlocks (1 - U₀ * X₀) 0 X₀ 1 := by
    have h12 : ((1 : Matrix m m R) + -(U₀ * X₀)) * U₀ + -U₀ = 0 := by
      rw [Matrix.add_mul, Matrix.one_mul, Matrix.neg_mul, Matrix.mul_assoc, hXU, Matrix.mul_zero,
        neg_zero, add_zero, add_neg_cancel]
    have hl : lowerVec x = lowerBlockGL X₀ := rfl
    have hu : upperVec u = upperBlockGL U₀ := rfl
    have hu_neg : upperVec (-u) = upperBlockGL (-U₀) := by
      rw [← upperVec_inv, hu, upperBlockGL_inv]
    rw [Units.val_mul, Units.val_mul, hu_neg, hl, hu, coe_upperBlockGL, coe_lowerBlockGL,
      coe_upperBlockGL]
    simp only [fromBlocks_multiply, Matrix.mul_zero, add_zero, zero_add, Matrix.mul_one,
      Matrix.one_mul, Matrix.neg_mul, hXU]
    rw [h12, ← sub_eq_add_neg]
  have hassoc : lowerVec a₁ * upperVec (-u) * lowerVec x * upperVec u * lowerVec a₂ =
      lowerVec a₁ * (upperVec (-u) * lowerVec x * upperVec u) * lowerVec a₂ := by group
  rw [hassoc, Units.val_mul, Units.val_mul, hmid, coe_lowerBlockGL, coe_lowerBlockGL]
  ext i j; simp [fromBlocks_multiply, U₀, X₀, Matrix.mul_apply, vecMulVec_apply]

/-- Orthogonal case of right-invariance under `lowerVec`: when `a ⬝ᵥ b = 1` and `x ⬝ᵥ b = 0`. -/
private theorem vasersteinPsi_mul_lowerVec_of_dotProduct_eq_zero {s : ℕ}
    (hR : HasStableRangeLE R s) (hm : s + 1 ≤ Fintype.card m) (A : GL (m ⊕ Unit) R) {b x : m → R}
    (hb : botRow A ⬝ᵥ b = 1) (hxb : x ⬝ᵥ b = 0) (ha : Module.IsUnimodular R (botRow A))
    (ha₂ : Module.IsUnimodular R (botRow (A * lowerVec x))) :
    vasersteinPsi (A * lowerVec x) ha₂ = vasersteinPsi A ha := by
  have hb₂ : botRow (A * lowerVec x) ⬝ᵥ b = 1 := by
    have hrow : botRow (A * lowerVec x) = botRow A + fun j ↦ botEntry A * x j :=
      botRow_mul_lowerVec A x
    have hdot : ((fun j ↦ botEntry A * x j) ⬝ᵥ b) = botEntry A * (x ⬝ᵥ b) := by
      simp only [dotProduct, Finset.mul_sum, mul_assoc]
    rw [hrow, add_dotProduct, hb, hdot, hxb, mul_zero, add_zero]
  rw [vasersteinPsi_eq_mk hR hm _ ha₂ hb₂, vasersteinPsi_eq_mk hR hm A ha hb, eq_comm,
    QuotientGroup.eq]
  let u : m → R := fun i ↦ b i * (1 - botEntry A)
  have hxu : x ⬝ᵥ u = 0 := by
    have hdot : x ⬝ᵥ u = (x ⬝ᵥ b) * (1 - botEntry A) := by
      simp only [u, dotProduct, Finset.sum_mul, mul_assoc]
    rw [hdot, hxb, zero_mul]
  suffices (vasersteinBlock A b hb)⁻¹ * vasersteinBlock (A * lowerVec x) b hb₂ =
      oneSubVecMulVecGL (-1) u x (by simp [hxu]) from
    this ▸ oneSubVecMulVecGL_mem_elementarySubgroup_of_dotProduct_eq_one hR hm hb hxb
      (1 - botEntry A) (by simp [u, hxu])
  refine Units.ext ?_; rw [coe_vasersteinBlock_inv_mul hb hb₂, coe_oneSubVecMulVecGL]
  have hmid : (A * clearLastRowFactor A b)⁻¹ *
      (A * lowerVec x * clearLastRowFactor (A * lowerVec x) b) =
      lowerVec (botRow A) * upperVec (-u) * lowerVec x * upperVec u *
        lowerVec (-botRow (A * lowerVec x)) := by
    simp only [clearLastRowFactor, _root_.mul_inv_rev, lowerVec_inv, upperVec_inv, neg_neg,
      botEntry_mul_lowerVec]
    dsimp only [u]; group
  rw [hmid, toBlocks₁₁_conj_lowerVec_of_dotProduct_eq_zero _ _ u x hxu]

private theorem vecMul_reindexGL_subtypeNeSumPUnit_lowerVec (i₀ : m)
    (c : {i : m // i ≠ i₀} → R) (v : m → R) :
    (∀ i : {i : m // i ≠ i₀},
      (v ᵥ* ((Equiv.subtypeNeSumPUnit.{0} i₀).reindexGL R (lowerVec c) : Matrix m m R)) i.val =
        v i.val + v i₀ * c i) ∧
      (v ᵥ* ((Equiv.subtypeNeSumPUnit.{0} i₀).reindexGL R (lowerVec c) : Matrix m m R)) i₀ =
        v i₀ := by
  set φ := Equiv.subtypeNeSumPUnit.{0} i₀
  constructor
  · intro i; simp only [Equiv.coe_reindexGL, submatrix_apply, vecMul, dotProduct]
    rw [← φ.sum_comp]; simp only [φ.symm_apply_apply]
    simp [φ, Fintype.sum_sum_type, Matrix.one_apply, i.property]
  · simp only [Equiv.coe_reindexGL, submatrix_apply, vecMul, dotProduct]
    rw [← φ.sum_comp]; simp only [φ.symm_apply_apply]
    simp [φ, Fintype.sum_sum_type]

private theorem dotProduct_clearedPivot_eq_one (A : GL (m ⊕ Unit) R) (i₀ : m) (x : m → R)
    (c b' : {i : m // i ≠ i₀} → R)
    (hb' : (fun i : {i : m // i ≠ i₀} ↦
      botRow (A * lowerVec x) i.val + botRow (A * lowerVec x) i₀ * c i) ⬝ᵥ b' = 1) :
    let e₂ := (Equiv.subtypeNeSumPUnit.{0} i₀).reindexGL R (lowerVec c)
    let z : m → R := fun k ↦ if k = i₀ then 0 else (x ᵥ* (e₂ : Matrix m m R)) k
    botRow (A * blockOne e₂ * lowerVec z) ⬝ᵥ (fun k ↦ if hk : k = i₀ then 0 else b' ⟨k, hk⟩) =
      1 := by
  intro e₂ z
  let φ := Equiv.subtypeNeSumPUnit.{0} i₀
  have hAz_i : ∀ i : {i : m // i ≠ i₀}, botRow (A * blockOne e₂ * lowerVec z) i.val =
      botRow (A * lowerVec x) i.val + botRow (A * lowerVec x) i₀ * c i := by
    intro i
    have hzi : z i.val = (x ᵥ* (e₂ : Matrix m m R)) i.val := by simp [z, i.property]
    rw [botRow_mul_lowerVec, botRow_mul_lowerVec, botEntry_mul_blockOne]
    dsimp only
    rw [hzi, congrFun (botRow_mul_blockOne A e₂) i.val,
      (vecMul_reindexGL_subtypeNeSumPUnit_lowerVec i₀ c _).1 i,
      (vecMul_reindexGL_subtypeNeSumPUnit_lowerVec i₀ c x).1 i]
    simp only [mul_add, add_mul, mul_assoc]; abel
  calc botRow (A * blockOne e₂ * lowerVec z) ⬝ᵥ (fun k ↦ if hk : k = i₀ then 0 else b' ⟨k, hk⟩)
      = ∑ p : {i : m // i ≠ i₀} ⊕ Unit, botRow (A * blockOne e₂ * lowerVec z) (φ p) *
          (if hk : φ p = i₀ then 0 else b' ⟨φ p, hk⟩) := by
        simp only [dotProduct]; rw [← φ.sum_comp]
    _ = _ ⬝ᵥ b' := by
        simp only [φ, Fintype.sum_sum_type, Equiv.trans_apply, Equiv.optionEquivSumPUnit_symm_inl,
          Equiv.optionEquivSumPUnit_symm_inr, Equiv.optionSubtypeNe_some,
          Equiv.optionSubtypeNe_none, ↓reduceDIte, mul_zero, Fintype.univ_punit,
          Finset.sum_singleton, add_zero, dotProduct]
        exact Fintype.sum_congr _ _ fun i ↦ by simp [i.property, hAz_i i]
    _ = 1 := hb'

/-- Right-invariance under `lowerVec` when the bottom-left row of `A` is `Pi.single i₀ 1`. -/
private theorem vasersteinPsi_mul_lowerVec_of_single {s : ℕ} (hR : HasStableRangeLE R s)
    (hm : s + 1 ≤ Fintype.card m) (A : GL (m ⊕ Unit) R) (i₀ : m) (x : m → R)
    (ha0 : botRow A = Pi.single i₀ 1) (ha : Module.IsUnimodular R (botRow A))
    (ha₂ : Module.IsUnimodular R (botRow (A * lowerVec x))) :
    vasersteinPsi (A * lowerVec x) ha₂ = vasersteinPsi A ha := by
  let φ := Equiv.subtypeNeSumPUnit.{0} i₀
  obtain ⟨c, hc⟩ := hR.exists_isUnimodular_add_mul_subtype_ne hm ha₂ i₀
  obtain ⟨b', hb'⟩ := TauCeti.Module.isUnimodular_pi_iff.mp hc
  let e₂ : GL m R := φ.reindexGL R (lowerVec c)
  have he₂ : e₂ ∈ elementarySubgroup m R :=
    (φ.reindexGL_mem_elementarySubgroup_iff).mpr (lowerBlockGL_mem_elementarySubgroup _)
  let A' := A * blockOne e₂
  let x' : m → R := x ᵥ* (e₂ : Matrix m m R)
  have ha'i₀ : botRow A' i₀ = 1 := by
    rw [congrFun (botRow_mul_blockOne A e₂) i₀,
      (vecMul_reindexGL_subtypeNeSumPUnit_lowerVec i₀ c _).2, congrFun ha0 i₀, Pi.single_eq_same]
  have ha'_unimod : Module.IsUnimodular R (botRow A') := by
    rw [botRow_mul_blockOne, e₂.isUnimodular_vecMul_iff]; exact ha
  let z : m → R := fun k ↦ if k = i₀ then 0 else x' k
  let y : m → R := Pi.single i₀ (x' i₀)
  have hzy : z + y = x' := by ext k; by_cases hk : k = i₀ <;> simp [z, y, hk]
  let Az := A' * lowerVec z
  let b₂ : m → R := fun k ↦ if hk : k = i₀ then 0 else b' ⟨k, hk⟩
  have hb₂ : botRow Az ⬝ᵥ b₂ = 1 := dotProduct_clearedPivot_eq_one A i₀ x c b' hb'
  have hAz_unimod : Module.IsUnimodular R (botRow Az) :=
    TauCeti.Module.isUnimodular_pi_iff.mpr ⟨b₂, hb₂⟩
  have hAx'_eq : A * lowerVec x * blockOne e₂ = Az * lowerVec y := by
    calc A * lowerVec x * blockOne e₂
        = A * (lowerVec x * blockOne e₂) := mul_assoc ..
      _ = A * (blockOne e₂ * lowerVec x') := by rw [lowerVec_mul_blockOne]
      _ = A' * lowerVec x' := (mul_assoc ..).symm
      _ = A' * (lowerVec z * lowerVec y) := by rw [← hzy, ← lowerVec_mul]
      _ = Az * lowerVec y := (mul_assoc ..).symm
  have hAx'_unimod : Module.IsUnimodular R (botRow (Az * lowerVec y)) := by
    rw [← hAx'_eq, botRow_mul_blockOne, e₂.isUnimodular_vecMul_iff]; exact ha₂
  have heq1 : vasersteinPsi (A * lowerVec x) ha₂ = vasersteinPsi (Az * lowerVec y) hAx'_unimod :=
    (vasersteinPsi_mul_blockOne hR hm _ he₂ ha₂ (hAx'_eq.symm ▸ hAx'_unimod)).symm.trans
      (vasersteinPsi_congr hAx'_eq (hAx'_eq.symm ▸ hAx'_unimod) hAx'_unimod)
  rw [heq1, vasersteinPsi_mul_lowerVec_of_dotProduct_eq_zero hR hm Az hb₂ (by simp [y, b₂])
      hAz_unimod hAx'_unimod,
    vasersteinPsi_mul_lowerVec_of_dotProduct_eq_zero hR hm A' (b := Pi.single i₀ 1)
      (by simp [ha'i₀]) (by simp [z]) ha'_unimod hAz_unimod]
  exact vasersteinPsi_mul_blockOne hR hm A he₂ ha ha'_unimod

/-- General right-invariance of `vasersteinPsi` under `lowerVec` whenever both matrices have
unimodular bottom-left row. -/
private theorem vasersteinPsi_mul_lowerVec {s : ℕ} (hR : HasStableRangeLE R s)
    (hm : s + 1 ≤ Fintype.card m) (A : GL (m ⊕ Unit) R) (x : m → R)
    (ha : Module.IsUnimodular R (botRow A))
    (ha₂ : Module.IsUnimodular R (botRow (A * lowerVec x))) :
    vasersteinPsi (A * lowerVec x) ha₂ = vasersteinPsi A ha := by
  obtain ⟨i₀⟩ := Fintype.card_pos_iff.mp (by omega : 0 < Fintype.card m)
  obtain ⟨e₁, he₁, hae₁⟩ := hR.exists_vecMul_elementarySubgroup_eq_single hm ha i₀
  let A₁ := A * blockOne e₁
  let x₁ : m → R := x ᵥ* (e₁ : Matrix m m R)
  have ha₁_eq : botRow A₁ = Pi.single i₀ 1 := by rw [botRow_mul_blockOne, hae₁]
  have ha₁ : Module.IsUnimodular R (botRow A₁) := by
    rw [botRow_mul_blockOne, e₁.isUnimodular_vecMul_iff]; exact ha
  have hcomm : A * lowerVec x * blockOne e₁ = A₁ * lowerVec x₁ := by
    rw [mul_assoc, lowerVec_mul_blockOne, ← mul_assoc]
  have ha₂₁ : Module.IsUnimodular R (botRow (A₁ * lowerVec x₁)) := by
    rw [← hcomm, botRow_mul_blockOne, e₁.isUnimodular_vecMul_iff]; exact ha₂
  calc vasersteinPsi (A * lowerVec x) ha₂
      = vasersteinPsi (A₁ * lowerVec x₁) ha₂₁ :=
        (vasersteinPsi_mul_blockOne hR hm _ he₁ ha₂ (hcomm.symm ▸ ha₂₁)).symm.trans
          (vasersteinPsi_congr hcomm (hcomm.symm ▸ ha₂₁) ha₂₁)
    _ = vasersteinPsi A₁ ha₁ := vasersteinPsi_mul_lowerVec_of_single hR hm A₁ i₀ x₁ ha₁_eq ha₁ ha₂₁
    _ = vasersteinPsi A ha := vasersteinPsi_mul_blockOne hR hm A he₁ ha ha₁

private theorem exists_unimodular_mul_lowerVec {s : ℕ} (hR : HasStableRangeLE R s)
    (hm : s ≤ Fintype.card m) (A : GL (m ⊕ Unit) R) :
    ∃ c : m → R, Module.IsUnimodular R (botRow (A * lowerVec c)) := by
  obtain ⟨c, hc⟩ := hR.exists_isUnimodular_add_mul hm (isUnimodular_sumElim_bot A)
  exact ⟨c, by simpa only [botRow_mul_lowerVec] using hc⟩

/-- Vaserstein's coset retraction `GL (m ⊕ Unit) R → GL m R ⧸ elementarySubgroup m R`. -/
private def vasersteinPhi {s : ℕ} (hR : HasStableRangeLE R s) (hm : s + 1 ≤ Fintype.card m)
    (A : GL (m ⊕ Unit) R) : GL m R ⧸ elementarySubgroup m R :=
  have hex := exists_unimodular_mul_lowerVec hR (Nat.le_of_succ_le hm) A
  vasersteinPsi (A * lowerVec hex.choose) hex.choose_spec

private theorem vasersteinPhi_eq_vasersteinPsi_mul_lowerVec {s : ℕ} (hR : HasStableRangeLE R s)
    (hm : s + 1 ≤ Fintype.card m) (A : GL (m ⊕ Unit) R) (c : m → R)
    (hc : Module.IsUnimodular R (botRow (A * lowerVec c))) :
    vasersteinPhi hR hm A = vasersteinPsi (A * lowerVec c) hc := by
  rw [vasersteinPhi]
  set hex := exists_unimodular_mul_lowerVec hR (Nat.le_of_succ_le hm) A
  have hadd : A * lowerVec c = A * lowerVec hex.choose * lowerVec (c - hex.choose) := by
    rw [mul_assoc, lowerVec_mul, add_sub_cancel]
  exact (vasersteinPsi_mul_lowerVec hR hm (A * lowerVec hex.choose) (c - hex.choose)
    hex.choose_spec (hadd ▸ hc)).symm.trans (vasersteinPsi_congr hadd.symm (hadd ▸ hc) hc)

private theorem vasersteinPhi_blockOne {s : ℕ} (hR : HasStableRangeLE R s)
    (hm : s + 1 ≤ Fintype.card m) (g : GL m R) :
    vasersteinPhi hR hm (blockOne g) = QuotientGroup.mk g := by
  obtain ⟨i₀⟩ := Fintype.card_pos_iff.mp (by omega : 0 < Fintype.card m)
  let c : m → R := Pi.single i₀ 1
  have hc : Module.IsUnimodular R (botRow (blockOne g * lowerVec c)) := by
    have hrow : botRow (blockOne g * lowerVec c) = c := by
      rw [botRow_mul_lowerVec]; ext j; simp [botRow, botEntry, blockOne]
    rw [hrow]
    exact TauCeti.Module.isUnimodular_pi_iff.mpr ⟨Pi.single i₀ 1, by simp [c, Pi.single_apply]⟩
  rw [vasersteinPhi_eq_vasersteinPsi_mul_lowerVec hR hm _ c hc]
  exact vasersteinPsi_blockOne_mul_lowerVec hR hm g c hc

/-- Block commutation identity moving `upperVec (Pi.single p₀ r)` past `lowerVec c` when
`c p₀ = 0`. -/
private theorem upperVec_single_mul_lowerVec_of_eq_zero (p₀ : m) (r : R) {c : m → R}
    (hc0 : c p₀ = 0) :
    ∃ e₀ ∈ elementarySubgroup m R,
      upperVec (Pi.single p₀ r) * lowerVec c =
        lowerVec c * blockOne e₀ * upperVec (Pi.single p₀ r) := by
  let φ := Equiv.subtypeNeSumPUnit.{0} p₀
  let e₀ : GL m R := φ.reindexGL R (lowerVec (fun j : {j : m // j ≠ p₀} ↦ r * c j.val))
  refine ⟨e₀, (φ.reindexGL_mem_elementarySubgroup_iff).mpr (lowerBlockGL_mem_elementarySubgroup _),
    Units.ext ?_⟩
  set Y : Matrix m Unit R := Matrix.of fun i _ ↦ (Pi.single p₀ r : m → R) i
  set C : Matrix Unit m R := Matrix.of fun _ j ↦ c j
  have hCY : C * Y = 0 := by ext ⟨⟩ ⟨⟩; simp [C, Y, Matrix.mul_apply, Pi.single_apply, hc0]
  have he₀_mat : (e₀ : Matrix m m R) = 1 + Y * C := by
    ext p q; obtain ⟨p, rfl⟩ := φ.surjective p; obtain ⟨q, rfl⟩ := φ.surjective q
    simp only [e₀, Equiv.coe_reindexGL, submatrix_apply, φ.symm_apply_apply]
    rcases p with i | ⟨⟩ <;> rcases q with j | ⟨⟩
    · simp [φ, Y, C, Matrix.mul_apply, Matrix.one_apply, Subtype.ext_iff, i.property]
    · simp [φ, Y, C, Matrix.mul_apply, i.property]
    · simp [φ, Y, C, Matrix.mul_apply, j.property.symm]
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

private theorem vasersteinPhi_mul_upperVec_single {s : ℕ} (hR : HasStableRangeLE R s)
    (hm : s + 1 ≤ Fintype.card m) (A : GL (m ⊕ Unit) R) (p₀ : m) (r : R) :
    vasersteinPhi hR hm (A * upperVec (Pi.single p₀ r)) = vasersteinPhi hR hm A := by
  set U := upperVec (Pi.single p₀ r)
  have hScard : s ≤ (({p₀} : Finset m)ᶜ).card := by
    rw [Finset.card_compl, Finset.card_singleton]; omega
  obtain ⟨c, hcsupp, hc_unimod⟩ := hR.exists_isUnimodular_add_mul_of_subset hScard
    (isUnimodular_sumElim_bot (A * U))
  have hc₁ : Module.IsUnimodular R (botRow (A * U * lowerVec c)) := by
    simpa only [botRow_mul_lowerVec] using hc_unimod
  obtain ⟨e₀, he₀, hUcomm⟩ := upperVec_single_mul_lowerVec_of_eq_zero p₀ r (hcsupp p₀ (by simp))
  have hchain : A * U * lowerVec c = A * lowerVec c * blockOne e₀ * U := by
    calc A * U * lowerVec c = A * (U * lowerVec c) := by group
      _ = A * (lowerVec c * blockOne e₀ * U) := by rw [hUcomm]
      _ = A * lowerVec c * blockOne e₀ * U := by group
  have hc₂ : Module.IsUnimodular R (botRow (A * lowerVec c * blockOne e₀)) := by
    rw [← botRow_mul_upperVec _ (Pi.single p₀ r), ← hchain]; exact hc₁
  have hc₀ : Module.IsUnimodular R (botRow (A * lowerVec c)) := by
    rw [← e₀.isUnimodular_vecMul_iff, ← botRow_mul_blockOne]; exact hc₂
  rw [vasersteinPhi_eq_vasersteinPsi_mul_lowerVec hR hm (A * U) c hc₁,
    vasersteinPhi_eq_vasersteinPsi_mul_lowerVec hR hm A c hc₀]
  exact ((vasersteinPsi_congr hchain hc₁ (hchain ▸ hc₁)).trans
    (vasersteinPsi_mul_upperVec hR hm _ _ hc₂ (hchain ▸ hc₁))).trans
    (vasersteinPsi_mul_blockOne hR hm (A * lowerVec c) he₀ hc₀ hc₂)

/-- Right-invariance of `vasersteinPhi` under every elementary transvection on `m ⊕ Unit`. -/
private theorem vasersteinPhi_mul_transvectionUnit {s : ℕ} (hR : HasStableRangeLE R s)
    (hm : s + 1 ≤ Fintype.card m) (A : GL (m ⊕ Unit) R) {p q : m ⊕ Unit} (hpq : p ≠ q) (r : R) :
    vasersteinPhi hR hm (A * transvectionUnit hpq r) = vasersteinPhi hR hm A := by
  rcases p with p₀ | ⟨⟩ <;> rcases q with q₀ | ⟨⟩
  · have hpq₀ : p₀ ≠ q₀ := fun h ↦ hpq (congrArg Sum.inl h)
    let e := transvectionUnit hpq₀ r
    have htr : transvectionUnit hpq r = blockOne e := by
      refine Units.ext ?_; ext (i | ⟨⟩) (j | ⟨⟩) <;>
        simp [e, coe_transvectionUnit_eq_one_add_single, single_apply, Matrix.one_apply]
    rw [htr]
    obtain ⟨c, hc⟩ := exists_unimodular_mul_lowerVec hR (Nat.le_of_succ_le hm) (A * blockOne e)
    let c₀ : m → R := c ᵥ* (↑e⁻¹ : Matrix m m R)
    have hcomm : A * blockOne e * lowerVec c = A * lowerVec c₀ * blockOne e := by
      have hc₀e : c₀ ᵥ* (e : Matrix m m R) = c := by simp [c₀, vecMul_vecMul]
      rw [mul_assoc A (lowerVec c₀), lowerVec_mul_blockOne, hc₀e, ← mul_assoc]
    have hc₀ : Module.IsUnimodular R (botRow (A * lowerVec c₀)) := by
      rw [← e.isUnimodular_vecMul_iff, ← botRow_mul_blockOne, ← hcomm]; exact hc
    rw [vasersteinPhi_eq_vasersteinPsi_mul_lowerVec hR hm _ c hc,
      vasersteinPhi_eq_vasersteinPsi_mul_lowerVec hR hm A c₀ hc₀]
    exact (vasersteinPsi_congr hcomm hc (hcomm ▸ hc)).trans
      (vasersteinPsi_mul_blockOne hR hm _ (transvectionUnit_mem_elementarySubgroup hpq₀ r)
        hc₀ (hcomm ▸ hc))
  · have htr : transvectionUnit hpq r = upperVec (Pi.single p₀ r) := by
      refine Units.ext ?_; ext (i | ⟨⟩) (j | ⟨⟩) <;>
        simp [coe_transvectionUnit_eq_one_add_single, single_apply, Pi.single_apply,
          Matrix.one_apply, eq_comm]
    rw [htr]; exact vasersteinPhi_mul_upperVec_single hR hm A p₀ r
  · have htr : transvectionUnit hpq r = lowerVec (Pi.single q₀ r) := by
      refine Units.ext ?_; ext (i | ⟨⟩) (j | ⟨⟩) <;>
        simp [coe_transvectionUnit_eq_one_add_single, single_apply, Pi.single_apply,
          Matrix.one_apply, eq_comm]
    rw [htr]
    obtain ⟨c, hc⟩ := exists_unimodular_mul_lowerVec hR (Nat.le_of_succ_le hm)
      (A * lowerVec (Pi.single q₀ r))
    have hcomb : A * lowerVec (Pi.single q₀ r) * lowerVec c =
        A * lowerVec (Pi.single q₀ r + c) := by
      rw [mul_assoc, lowerVec_mul]
    rw [vasersteinPhi_eq_vasersteinPsi_mul_lowerVec hR hm _ c hc,
      vasersteinPhi_eq_vasersteinPsi_mul_lowerVec hR hm A _ (hcomb ▸ hc)]
    exact vasersteinPsi_congr hcomb hc (hcomb ▸ hc)
  · exact (hpq rfl).elim

private theorem vasersteinPhi_mul_elementarySubgroup {s : ℕ} (hR : HasStableRangeLE R s)
    (hm : s + 1 ≤ Fintype.card m) (A : GL (m ⊕ Unit) R) {E : GL (m ⊕ Unit) R}
    (hE : E ∈ elementarySubgroup (m ⊕ Unit) R) :
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

private theorem injective_stability_unit {s : ℕ} (hR : HasStableRangeLE R s)
    (hm : s + 1 ≤ Fintype.card m) (g : GL m R)
    (hg : blockOne g ∈ elementarySubgroup (m ⊕ Unit) R) :
    g ∈ elementarySubgroup m R := by
  have h1 : (1 : GL (m ⊕ Unit) R) = blockOne 1 := (map_one fromBlocksGL).symm
  have hmk : (QuotientGroup.mk g : GL m R ⧸ elementarySubgroup m R) = QuotientGroup.mk 1 := by
    calc (QuotientGroup.mk g : GL m R ⧸ elementarySubgroup m R)
        = vasersteinPhi hR hm (1 * blockOne g) := by rw [one_mul, vasersteinPhi_blockOne]
      _ = vasersteinPhi hR hm 1 := vasersteinPhi_mul_elementarySubgroup hR hm 1 hg
      _ = vasersteinPhi hR hm (blockOne 1) := by rw [← h1]
      _ = QuotientGroup.mk 1 := vasersteinPhi_blockOne hR hm 1
  rw [QuotientGroup.eq, mul_one, Subgroup.inv_mem_iff] at hmk
  exact hmk

end Vaserstein

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
    let ψ := Equiv.sumEmpty n k
    have hg_eq : ψ.reindexGL R (fromBlocksGL (g, (1 : GL k R))) = g := by
      refine Units.ext ?_; ext i j
      simp [ψ]
    rw [← hg_eq]
    exact (ψ.reindexGL_mem_elementarySubgroup_iff).mpr hg'
  | succ m ih =>
    intro k _ _ hk hg'
    obtain ⟨x₀⟩ := Fintype.card_pos_iff.mp (by omega : 0 < Fintype.card k)
    let φ := (Equiv.sumAssoc n {x : k // x ≠ x₀} Unit).trans
      (Equiv.sumCongr (Equiv.refl n) (Equiv.subtypeNeSumPUnit.{0} x₀))
    have hcard_k' : Fintype.card {x : k // x ≠ x₀} = m := by
      rw [Fintype.card_subtype_compl, Fintype.card_subtype_eq]; omega
    have hre_fwd : φ.reindexGL R
        (blockOne (fromBlocksGL (g, (1 : GL {x : k // x ≠ x₀} R)))) =
        fromBlocksGL (g, (1 : GL k R)) := by
      dsimp only [φ, blockOne]
      rw [← Equiv.reindexGL_trans_reindexGL, MulEquiv.trans_apply,
        Equiv.reindexGL_sumAssoc_fromBlocksGL, Equiv.reindexGL_sumCongr_fromBlocksGL]
      simp [Prod.mk_one_one]
    have hre : φ.symm.reindexGL R (fromBlocksGL (g, (1 : GL k R))) =
        blockOne (fromBlocksGL (g, (1 : GL {x : k // x ≠ x₀} R))) := by
      rw [← hre_fwd, Equiv.reindexGL_symm_apply_reindexGL]
    have hmem := hre ▸ (φ.symm.reindexGL_mem_elementarySubgroup_iff).mpr hg'
    exact ih {x : k // x ≠ x₀} hcard_k'
      (injective_stability_unit hR (by rw [Fintype.card_sum]; omega) _ hmem)

end TauCeti

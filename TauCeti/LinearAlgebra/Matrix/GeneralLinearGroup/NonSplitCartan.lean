/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

-- `Subgroup.index`, `Subgroup.relIndex` and `Subgroup.normalizer` occur in the statements below,
-- and this module re-exports the `GL` notation.
public import Mathlib.GroupTheory.Index
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
-- `TauCeti.index_eq_of_natCard_eq_mul`: an index from the orders of a subgroup and its group.
import TauCeti.GroupTheory.Index.Basic
-- `TauCeti.natCard_GL_fin_two_eq_sq_sub_one_mul`: the order of `GL₂` over a finite field.
import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Card
-- `TauCeti.FiniteField.ne_zero_or_two_ne_zero_of_forall_sq_ne`: over a finite field an
-- irreducible quadratic is separable.
import TauCeti.FieldTheory.Finite.Card
-- `TauCeti.sq_add_mul_mul_sub_mul_sq_eq_zero_iff`: the norm form of `F[α]` has no nontrivial zero.
import TauCeti.Algebra.Field.Basic

/-!
# The nonsplit Cartan subgroup of `GL₂` and its normalizer

Let `R` be a commutative ring and `t n : R`. Multiplication by `a + b α` on `R[α] / (α² - t α - n)`,
in the basis `(1, α)`, is the matrix `!![a, n b; b, a + t b]`. The invertible matrices of this
shape form the subgroup `TauCeti.GL2NonSplitCartan t n` of `GL₂(R)`. When `R = F` is a field and
`X² - t X - n` has no root in `F`, the algebra is the field `F[α]` of degree `2` over `F` and this
subgroup is the image of its unit group, a **nonsplit Cartan subgroup** `C_ns` of `GL₂(F)`. Its
normalizer is `TauCeti.GL2NonSplitCartanNormalizer t n`, written `C_ns⁺`.

For an odd prime `ℓ` and a nonsquare `ε ∈ 𝔽_ℓ` the choice `t = 0`, `n = ε` gives the standard
`C_ns(ℓ) = {!![a, ε b; b, a]}`; over `𝔽₂` the choice `t = n = 1` gives the cyclic subgroup of
order `3` of `GL₂(𝔽₂)`. These are the levels of the modular curves `X_ns(ℓ)` and `X_ns⁺(ℓ)`.

Over a field `F` in which `X² - t X - n` has no root, the subgroup is
`{a + b α : (a, b) ≠ (0, 0)}`, so over a finite field with `q` elements it has `q² - 1` elements
and index `q (q - 1)`. When this irreducible quadratic is moreover separable, that is `t ≠ 0` or
`2 ≠ 0`, the Cartan subgroup has index `2` in its normalizer: an
element `g` of the normalizer sends `α` to a root of `X² - t X - n` in `F[α]`, which is `α` or its
conjugate `t - α`. In the first case `g` commutes with `α` and lies in the Cartan subgroup; in the
second, so does `σ g`, where `σ = !![1, t; 0, -1]` is the matrix of the conjugation `α ↦ t - α`.
Over a finite field an irreducible quadratic is automatically separable.

`TauCeti.GL2NonSplitTorus F E` is the same construction for an abstract quadratic extension `E/F`
with a chosen basis, hence conjugate to this subgroup when `E ≅ F[α]`; the explicit entries here
are those of the standard level `C_ns(ℓ)`, and they also make sense over `ℤ / N`.

## Main definitions

* `TauCeti.GL2NonSplitCartan t n`: the invertible matrices `!![a, n b; b, a + t b]`.
* `TauCeti.GL2NonSplitCartanNormalizer t n`: its normalizer.

## Main results

* `TauCeti.GL2NonSplitCartan.mem_iff_exists_mk`: when `X² - t X - n` has no root in `F`, the
  elements of `C_ns` are exactly the matrices `!![a, n b; b, a + t b]` with `(a, b) ≠ (0, 0)`.
* `TauCeti.GL2NonSplitCartan.natCard`, `TauCeti.GL2NonSplitCartan.index_eq`: `|C_ns| = q² - 1` and
  `[GL₂(𝔽_q) : C_ns] = q (q - 1)` when `X² - t X - n` has no root in `𝔽_q`.
* `TauCeti.GL2NonSplitCartan.relIndex_normalizer`: `[C_ns⁺ : C_ns] = 2` when `X² - t X - n` is
  irreducible and separable.
* `TauCeti.GL2NonSplitCartanNormalizer.natCard`,
  `TauCeti.GL2NonSplitCartanNormalizer.two_mul_index`: `|C_ns⁺| = 2 (q² - 1)` and
  `2 [GL₂(𝔽_q) : C_ns⁺] = q (q - 1)` when `X² - t X - n` has no root in `𝔽_q`.

## References

* D. Zywina, *On the possible images of the mod `ℓ` representations associated to elliptic curves
  over `ℚ`*, arXiv:1508.07660, §1 (Notation) and §3.2.
-/

public section

namespace TauCeti

open Matrix

universe u

section CommRing

variable {R : Type u} [CommRing R]

/-- **The nonsplit Cartan subgroup** attached to `X² - t X - n`: the invertible matrices
`!![a, n b; b, a + t b]`, which are the matrices of multiplication by the units `a + b α` of
`R[α] / (α² - t α - n)` in the basis `(1, α)`. It is a nonsplit Cartan subgroup of `GL₂(F)` when
`R = F` is a field in which `X² - t X - n` has no root; for `t = 0` and a nonsquare `n = ε` it is
`{!![a, ε b; b, a]}`. -/
def GL2NonSplitCartan (t n : R) : Subgroup (GL (Fin 2) R) where
  carrier := {g | (g : Matrix (Fin 2) (Fin 2) R) 1 1 =
      (g : Matrix (Fin 2) (Fin 2) R) 0 0 + t * (g : Matrix (Fin 2) (Fin 2) R) 1 0 ∧
    (g : Matrix (Fin 2) (Fin 2) R) 0 1 = n * (g : Matrix (Fin 2) (Fin 2) R) 1 0}
  mul_mem' := by
    rintro g h ⟨hg₁, hg₂⟩ ⟨hh₁, hh₂⟩
    simp only [Set.mem_ofPred_eq, Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two]
    rw [hg₁, hg₂, hh₁, hh₂]
    constructor <;> ring
  one_mem' := by simp
  inv_mem' := by
    rintro g ⟨hg₁, hg₂⟩
    simp only [Set.mem_ofPred_eq, Matrix.coe_units_inv, Matrix.inv_def,
      Matrix.adjugate_fin_two, Matrix.smul_apply,
      Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one, smul_eq_mul]
    constructor
    · linear_combination -(Ring.inverse (g : Matrix (Fin 2) (Fin 2) R).det) * hg₁
    · linear_combination -(Ring.inverse (g : Matrix (Fin 2) (Fin 2) R).det) * hg₂

/-- **The normalizer of the nonsplit Cartan subgroup**, written `C_ns⁺`. -/
def GL2NonSplitCartanNormalizer (t n : R) : Subgroup (GL (Fin 2) R) :=
  Subgroup.normalizer (GL2NonSplitCartan t n : Set (GL (Fin 2) R))

theorem GL2NonSplitCartanNormalizer_def (t n : R) :
    GL2NonSplitCartanNormalizer t n =
      Subgroup.normalizer (GL2NonSplitCartan t n : Set (GL (Fin 2) R)) :=
  (rfl)

namespace GL2NonSplitCartan

variable {t n : R}

@[simp]
theorem mem_iff {g : GL (Fin 2) R} :
    g ∈ GL2NonSplitCartan t n ↔
      (g : Matrix (Fin 2) (Fin 2) R) 1 1 =
          (g : Matrix (Fin 2) (Fin 2) R) 0 0 + t * (g : Matrix (Fin 2) (Fin 2) R) 1 0 ∧
        (g : Matrix (Fin 2) (Fin 2) R) 0 1 = n * (g : Matrix (Fin 2) (Fin 2) R) 1 0 :=
  Iff.rfl

/-- The scalar matrices lie in the nonsplit Cartan subgroup. -/
theorem scalar_mem (u : Rˣ) : GeneralLinearGroup.scalar (Fin 2) u ∈ GL2NonSplitCartan t n := by
  simp

/-- `-1` lies in the nonsplit Cartan subgroup. -/
theorem neg_one_mem : (-1 : GL (Fin 2) R) ∈ GL2NonSplitCartan t n := by
  simp

theorem le_normalizer : GL2NonSplitCartan t n ≤ GL2NonSplitCartanNormalizer t n :=
  Subgroup.le_normalizer

/-- **A matrix commuting with the companion matrix `!![0, n; 1, t]` has the shape
`!![a, n b; b, a + t b]`.** -/
theorem mem_of_commute {g : GL (Fin 2) R}
    (h : (g : Matrix (Fin 2) (Fin 2) R) * !![0, n; 1, t] =
      !![0, n; 1, t] * (g : Matrix (Fin 2) (Fin 2) R)) :
    g ∈ GL2NonSplitCartan t n := by
  refine ⟨?_, ?_⟩
  · simpa [Matrix.mul_apply, Fin.sum_univ_two] using congrFun (congrFun h 1) 0
  · simpa [Matrix.mul_apply, Fin.sum_univ_two] using congrFun (congrFun h 0) 0

end GL2NonSplitCartan

end CommRing

section Field

variable {F : Type u} [Field F] {t n : F}

namespace GL2NonSplitCartan

/-- The determinant `a (a + t b) - n b²` of `!![a, n b; b, a + t b]` is nonzero for
`(a, b) ≠ (0, 0)` when `X² - t X - n` has no root in `F`. -/
theorem det_ne_zero (hirr : ∀ x : F, x ^ 2 ≠ t * x + n) {a b : F} (hab : a ≠ 0 ∨ b ≠ 0) :
    (!![a, n * b; b, a + t * b] : Matrix (Fin 2) (Fin 2) F).det ≠ 0 := by
  rw [det_fin_two_of]
  intro h
  have := (sq_add_mul_mul_sub_mul_sq_eq_zero_iff hirr (a := a) (b := b)).mp
    (by linear_combination h)
  tauto

/-- The element `!![a, n b; b, a + t b]` of the nonsplit Cartan subgroup, for `(a, b) ≠ (0, 0)`. -/
noncomputable def mk (hirr : ∀ x : F, x ^ 2 ≠ t * x + n) (a b : F) (hab : a ≠ 0 ∨ b ≠ 0) :
    GL2NonSplitCartan t n :=
  ⟨GeneralLinearGroup.mkOfDetNeZero _ (det_ne_zero hirr hab), by simp⟩

/-- The matrix of `TauCeti.GL2NonSplitCartan.mk hirr a b hab` is `!![a, n b; b, a + t b]`. -/
@[simp]
theorem coe_mk (hirr : ∀ x : F, x ^ 2 ≠ t * x + n) (a b : F) (hab : a ≠ 0 ∨ b ≠ 0) :
    (((mk hirr a b hab : GL2NonSplitCartan t n) : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
      !![a, n * b; b, a + t * b] :=
  GeneralLinearGroup.val_mkOfDetNeZero _ _

/-- **Every element of the nonsplit Cartan subgroup is some `!![a, n b; b, a + t b]`**, built by
`TauCeti.GL2NonSplitCartan.mk`, when `X² - t X - n` has no root in `F`. -/
theorem mem_iff_exists_mk (hirr : ∀ x : F, x ^ 2 ≠ t * x + n) {g : GL (Fin 2) F} :
    g ∈ GL2NonSplitCartan t n ↔
      ∃ a b hab, ((mk hirr a b hab : GL2NonSplitCartan t n) : GL (Fin 2) F) = g := by
  refine ⟨fun hg ↦ ⟨(g : Matrix (Fin 2) (Fin 2) F) 0 0, (g : Matrix (Fin 2) (Fin 2) F) 1 0, ?_,
    Units.ext ?_⟩, fun ⟨a, b, hab, h⟩ ↦ h ▸ (mk hirr a b hab).property⟩
  · by_contra! h
    have := g.isUnit.map Matrix.detMonoidHom
    simp_all [det_fin_two]
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [hg.1, hg.2]

/-- Over an infinite field the nonsplit Cartan subgroup is infinite. -/
private theorem infinite [Infinite F] (hirr : ∀ x : F, x ^ 2 ≠ t * x + n) :
    Infinite (GL2NonSplitCartan t n) :=
  Infinite.of_injective (fun x ↦ mk hirr x 1 (Or.inr one_ne_zero)) fun x y h ↦ by
    simpa using congrArg
      (fun g : GL2NonSplitCartan t n ↦ ((g : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) 0 0) h

/-- **`|C_ns| = q² - 1`** over a field with `q` elements: an element is determined by its first
column `(a, b) ≠ (0, 0)`. -/
theorem natCard (hirr : ∀ x : F, x ^ 2 ≠ t * x + n) :
    Nat.card (GL2NonSplitCartan t n) = Nat.card F ^ 2 - 1 := by
  classical
  rcases finite_or_infinite F with _ | _
  swap
  · have := infinite hirr
    rw [Nat.card_eq_zero_of_infinite, Nat.card_eq_zero_of_infinite]
    rfl
  let := Fintype.ofFinite F
  let f (p : {p : F × F // p ≠ 0}) : GL2NonSplitCartan t n :=
    mk hirr p.val.1 p.val.2 (by
      by_contra h
      exact p.property (Prod.ext (by tauto) (by tauto)))
  have hf : Function.Bijective f := by
    refine ⟨fun p q h ↦ ?_, fun g ↦ ?_⟩
    · have h' := congrArg
        (fun g : GL2NonSplitCartan t n ↦ ((g : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)) h
      simp only [f, coe_mk] at h'
      exact Subtype.ext (Prod.ext (by simpa using congrFun (congrFun h' 0) 0)
        (by simpa using congrFun (congrFun h' 1) 0))
    · obtain ⟨a, b, hab, h⟩ := (mem_iff_exists_mk hirr).mp g.property
      refine ⟨⟨(a, b), fun h ↦ ?_⟩, Subtype.ext h⟩
      simp only [Prod.ext_iff, Prod.fst_zero, Prod.snd_zero] at h
      tauto
  rw [← Nat.card_congr (Equiv.ofBijective f hf), Nat.card_eq_fintype_card,
    Fintype.card_subtype_compl, Fintype.card_subtype_eq, Fintype.card_prod,
    ← Nat.card_eq_fintype_card, sq]

/-- **`[GL₂(𝔽_q) : C_ns] = q (q - 1)`**, the degree of `X_ns(ℓ)` over the `j`-line for `q = ℓ`. -/
theorem index_eq [Finite F] (hirr : ∀ x : F, x ^ 2 ≠ t * x + n) :
    (GL2NonSplitCartan t n).index = Nat.card F * (Nat.card F - 1) := by
  have hpos : 0 < Nat.card F ^ 2 - 1 := by
    have := Finite.one_lt_card (α := F)
    have : 1 < Nat.card F ^ 2 := by nlinarith
    omega
  exact index_eq_of_natCard_eq_mul hpos (natCard hirr) (natCard_GL_fin_two_eq_sq_sub_one_mul F)

/-- The companion matrix `!![0, n; 1, t]`, the matrix of multiplication by `α`. -/
private noncomputable def alpha (t : F) (hn : n ≠ 0) : GL (Fin 2) F :=
  GeneralLinearGroup.mkOfDetNeZero !![0, n; 1, t] (by simpa [det_fin_two_of] using hn)

@[simp]
private theorem coe_alpha (hn : n ≠ 0) :
    ((alpha t hn : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = !![0, n; 1, t] :=
  GeneralLinearGroup.val_mkOfDetNeZero _ _

/-- The matrix `!![1, t; 0, -1]` of the conjugation `α ↦ t - α` of `F[α]`. -/
private noncomputable def conjMatrix (t : F) : GL (Fin 2) F :=
  GeneralLinearGroup.mkOfDetNeZero !![1, t; 0, -1] (by simp [det_fin_two_of])

@[simp]
private theorem coe_conjMatrix :
    ((conjMatrix t : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = !![1, t; 0, -1] :=
  GeneralLinearGroup.val_mkOfDetNeZero _ _

private theorem conjMatrix_mul_self : conjMatrix t * conjMatrix t = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

private theorem conjMatrix_inv : (conjMatrix t)⁻¹ = conjMatrix t :=
  inv_eq_of_mul_eq_one_right conjMatrix_mul_self

private theorem conjMatrix_mul_mul_mem {h : GL (Fin 2) F} (hh : h ∈ GL2NonSplitCartan t n) :
    conjMatrix t * h * conjMatrix t ∈ GL2NonSplitCartan t n := by
  obtain ⟨h₁, h₂⟩ := hh
  simp only [mem_iff, Units.val_mul, coe_conjMatrix, Matrix.mul_apply, Fin.sum_univ_two,
    Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one, Matrix.empty_val', Fin.isValue, one_mul, zero_mul, zero_add,
    neg_mul]
  constructor
  · linear_combination h₁
  · linear_combination -t * h₁ - h₂

private theorem conjMatrix_mem_normalizer :
    conjMatrix t ∈ GL2NonSplitCartanNormalizer (t := t) (n := n) := by
  have hinv : (conjMatrix t)⁻¹ = conjMatrix t := conjMatrix_inv
  refine Subgroup.mem_normalizer_iff.mpr fun h ↦ ⟨fun hh ↦ ?_, fun hh ↦ ?_⟩
  · rw [hinv]
    exact conjMatrix_mul_mul_mem hh
  rw [hinv] at hh
  have := conjMatrix_mul_mul_mem hh
  rwa [← mul_assoc, ← mul_assoc, conjMatrix_mul_self, one_mul, mul_assoc, conjMatrix_mul_self,
    mul_one] at this

private theorem conjMatrix_notMem (hsep : t ≠ 0 ∨ (2 : F) ≠ 0) :
    conjMatrix t ∉ GL2NonSplitCartan t n := by
  rintro ⟨h₁, h₂⟩
  rcases hsep with h | h
  · exact h (by simpa using h₂)
  · have h₁' : (-1 : F) = 1 := by simpa using h₁
    exact h (by linear_combination -h₁')

/-- An element of the normalizer conjugates `α` to `α` or to its conjugate `t - α`. -/
private theorem conj_alpha_eq (hirr : ∀ x : F, x ^ 2 ≠ t * x + n) (hn : n ≠ 0) {g : GL (Fin 2) F}
    (hg : g ∈ GL2NonSplitCartanNormalizer t n) :
    g * alpha t hn * g⁻¹ = alpha t hn ∨
      g * alpha t hn * g⁻¹ = conjMatrix t * alpha t hn * conjMatrix t := by
  have hα : alpha t hn ∈ GL2NonSplitCartan t n := by
    simp
  set y := g * alpha t hn * g⁻¹ with hy
  obtain ⟨h₁, h₂⟩ : y ∈ GL2NonSplitCartan t n := (Subgroup.mem_normalizer_iff.mp hg _).mp hα
  have htr : (y : Matrix (Fin 2) (Fin 2) F).trace = t := by
    rw [hy, Units.val_mul, Units.val_mul, Matrix.trace_units_conj]
    simp [trace_fin_two]
  have hdet : (y : Matrix (Fin 2) (Fin 2) F).det = -n := by
    rw [hy, Units.val_mul, Units.val_mul, Matrix.det_units_conj]
    simp [det_fin_two]
  rw [trace_fin_two, h₁] at htr
  rw [det_fin_two, h₁, h₂] at hdet
  set a := (y : Matrix (Fin 2) (Fin 2) F) 0 0
  set b := (y : Matrix (Fin 2) (Fin 2) F) 1 0
  -- `(y - α) (y - (t - α)) = 0` in `F[α]`, so one of the two factors has norm zero.
  have key : (a ^ 2 + t * a * (b - 1) - n * (b - 1) ^ 2) *
      ((a - t) ^ 2 + t * (a - t) * (b + 1) - n * (b + 1) ^ 2) = 0 := by
    linear_combination
      ((a ^ 2 - t * a + n * b ^ 2 - n + t * (2 * a * b - b * t + t * b ^ 2)) * a -
        n * (2 * a * b - b * t + t * b ^ 2) * b) * htr -
      (a ^ 2 - t * a + n * b ^ 2 - n + t * (2 * a * b - b * t + t * b ^ 2)) * hdet
  rcases mul_eq_zero.mp key with h | h
  · obtain ⟨ha, hb⟩ := (sq_add_mul_mul_sub_mul_sq_eq_zero_iff hirr).mp h
    have hb' : b = 1 := sub_eq_zero.mp hb
    refine Or.inl (Units.ext ?_)
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [h₁, h₂, a, b, ha, hb']
  · obtain ⟨ha, hb⟩ := (sq_add_mul_mul_sub_mul_sq_eq_zero_iff hirr).mp h
    have ha' : a = t := sub_eq_zero.mp ha
    have hb' : b = -1 := eq_neg_of_add_eq_zero_left hb
    refine Or.inr (Units.ext ?_)
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, h₁, h₂, a, b, ha', hb']

/-- **`[C_ns⁺ : C_ns] = 2`** when `X² - t X - n` has no root in `F` and is separable, that is
`t ≠ 0` or `2 ≠ 0`. Over a finite field separability is automatic
(`TauCeti.GL2NonSplitCartanNormalizer.two_mul_index`); for an inseparable `X² - n` the
conjugation `!![1, 0; 0, -1]` is the identity. -/
theorem relIndex_normalizer (hirr : ∀ x : F, x ^ 2 ≠ t * x + n) (hsep : t ≠ 0 ∨ (2 : F) ≠ 0) :
    (GL2NonSplitCartan t n).relIndex (GL2NonSplitCartanNormalizer t n) = 2 := by
  have hn : n ≠ 0 := fun h ↦ hirr 0 (by simp [h])
  refine Subgroup.relIndex_eq_two_iff'.mpr ⟨conjMatrix t, conjMatrix_mem_normalizer,
    fun g hg ↦ ?_⟩
  by_cases hgC : g ∈ GL2NonSplitCartan t n
  · refine Or.inr ⟨hgC, fun h ↦ conjMatrix_notMem (n := n) hsep ?_⟩
    simpa using mul_mem h (inv_mem hgC)
  · refine Or.inl ⟨?_, hgC⟩
    rcases conj_alpha_eq hirr hn hg with h | h
    · exact absurd (mem_of_commute (congrArg Units.val (mul_inv_eq_iff_eq_mul.mp h))) hgC
    · apply mem_of_commute
      have : conjMatrix t * g * alpha t hn * (conjMatrix t * g)⁻¹ = alpha t hn := by
        rw [_root_.mul_inv_rev, conjMatrix_inv]
        calc conjMatrix t * g * alpha t hn * (g⁻¹ * conjMatrix t)
            = conjMatrix t * (g * alpha t hn * g⁻¹) * conjMatrix t := by simp only [mul_assoc]
          _ = alpha t hn := by
            rw [h]
            simp only [← mul_assoc, conjMatrix_mul_self, one_mul]
            simp only [mul_assoc, conjMatrix_mul_self, mul_one]
      exact congrArg Units.val (mul_inv_eq_iff_eq_mul.mp this)

end GL2NonSplitCartan

namespace GL2NonSplitCartanNormalizer

/-- **`|C_ns⁺| = 2 (q² - 1)`** over a field with `q` elements. -/
theorem natCard (hirr : ∀ x : F, x ^ 2 ≠ t * x + n) :
    Nat.card (GL2NonSplitCartanNormalizer t n) = 2 * (Nat.card F ^ 2 - 1) := by
  rcases finite_or_infinite F with _ | _
  swap
  · have := GL2NonSplitCartan.infinite hirr
    have : Infinite (GL2NonSplitCartanNormalizer t n) :=
      Infinite.of_injective _ (Subgroup.inclusion_injective GL2NonSplitCartan.le_normalizer)
    rw [Nat.card_eq_zero_of_infinite, Nat.card_eq_zero_of_infinite]
    rfl
  have h := (GL2NonSplitCartan t n).relIndex_mul_card (GL2NonSplitCartanNormalizer t n)
  rwa [inf_of_le_left GL2NonSplitCartan.le_normalizer,
    GL2NonSplitCartan.relIndex_normalizer hirr
      (FiniteField.ne_zero_or_two_ne_zero_of_forall_sq_ne hirr),
    GL2NonSplitCartan.natCard hirr, eq_comm] at h

/-- **`2 [GL₂(𝔽_q) : C_ns⁺] = q (q - 1)`**: the degree of `X_ns⁺(ℓ)` over the `j`-line is
`ℓ (ℓ - 1) / 2`. -/
theorem two_mul_index [Finite F] (hirr : ∀ x : F, x ^ 2 ≠ t * x + n) :
    2 * (GL2NonSplitCartanNormalizer t n).index = Nat.card F * (Nat.card F - 1) := by
  rw [← GL2NonSplitCartan.index_eq hirr,
    ← Subgroup.relIndex_mul_index GL2NonSplitCartan.le_normalizer,
    GL2NonSplitCartan.relIndex_normalizer hirr
      (FiniteField.ne_zero_or_two_ne_zero_of_forall_sq_ne hirr)]

end GL2NonSplitCartanNormalizer

end Field

end TauCeti

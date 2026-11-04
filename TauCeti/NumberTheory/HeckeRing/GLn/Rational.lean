/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Diagonal.Basic
public import TauCeti.NumberTheory.HeckeRing.GLn.ScalarMul
public import TauCeti.NumberTheory.HeckeRing.Map.SubgroupExtension
public import TauCeti.NumberTheory.HeckeRing.Normalizer

import Mathlib.LinearAlgebra.Matrix.Integer
import Mathlib.Tactic.Group
import TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.Basic

/-!
# Rational and full `GL_n` Hecke rings, global comparison, and central scalar units

Following Proposition 3.16 of [Shimura][shimura1971] and §2 of [Rhodes–Shemanske][rhodes1999], this
file constructs the rational Hecke triples `(SL_n(ℤ), GL_n^+(ℚ))` and `(GL_n(ℤ), GL_n(ℚ))` inside
`GL_n(ℚ)`, proves their commutativity, establishes the global comparison chain

`IntegralHeckeRing n ↪ RationalHeckeRing n ≃+* FullHeckeRing n`

(over `ℤ`, and more generally over any coefficient semiring `R`), and packages the central scalar
units `T(c, …, c)` that clear denominators across `RationalHeckeRing n`.

Every element of `GL_n(ℚ)` clears denominators under multiplication by a positive scalar matrix
`diag(c, …, c)` (`exists_pos_natDiagGL_mul_mem_intEntries`). Together with Shimura's Lemma 3.10
(`mem_commensurator_of_hasIntEntries`), this forces `commensurator (SL_n(ℤ)) = ⊤` and, by finite
index of `SL_n(ℤ)` in `GL_n(ℤ)`, `commensurator (GL_n(ℤ)) = ⊤`. Enlarging the submonoid from
`posDetInt n` to `GL_n^+(ℚ)` gives the injective ring homomorphism `integralToRationalRingHom`,
while applying `HeckeCosetModule.mapSubgroupRingEquiv` to `SL_n(ℤ) = GL_n(ℤ) ⊓ GL_n^+(ℚ)` gives the
ring isomorphism `rationalToFullRingEquiv`. To verify the stabilizer coset condition on `GL_n^+(ℚ)`,
one clears denominators and puts the resulting integral matrix in Smith normal form `γ₁ · D · γ₂`
(`γ₁, γ₂ ∈ SL_n(ℤ)`), so conjugating `diag(-1, 1, …, 1)` by `γ₁` produces a determinant-`-1` element
of `GL_n(ℤ) ∩ g · GL_n(ℤ) · g⁻¹`.

Finally, each scalar operator `T(c, …, c)` normalizes `SL_n(ℤ)` and becomes a central unit
`scalarUnit n c` in `RationalHeckeRing n`; the positive scalar operators form `scalarSubmonoid n`
inside `IntegralHeckeRing n` and clear denominators for every element of `RationalHeckeRing n`
(`exists_mul_mem_scalarSubmonoid_eq`).

## Main definitions

* `HeckeRing.GLn.RationalHeckeRing`, `HeckeRing.GLn.FullHeckeRing`: the Hecke rings of
  `(SL_n(ℤ), GL_n^+(ℚ))` and `(GL_n(ℤ), GL_n(ℚ))` over `ℤ`.
* `HeckeRing.GLn.integralToRationalRingHom`, `HeckeRing.GLn.integralToRational`: the injective
  embedding `𝕋 (posDetInt n) (SLnZ n) R →+* 𝕋 (GLPos (Fin n) ℚ).toSubmonoid (SLnZ n) R`.
* `HeckeRing.GLn.rationalToFullRingEquiv`, `HeckeRing.GLn.rationalToFullEquiv`,
  `HeckeRing.GLn.integralToFullRingHom`: the ring isomorphism
  `𝕋 (GLPos (Fin n) ℚ).toSubmonoid (SLnZ n) R ≃+* 𝕋 ⊤ (GLnZ n) R` and composite embedding from the
  integral Hecke ring.
* `HeckeRing.GLn.commSemiringRationalHeckeRing`, `HeckeRing.GLn.commRingRationalHeckeRing`,
  `HeckeRing.GLn.commSemiringFullHeckeRing`, `HeckeRing.GLn.commRingFullHeckeRing`: commutativity of
  both rational Hecke rings.
* `HeckeRing.GLn.scalarUnit`, `HeckeRing.GLn.scalarSubmonoid`: the central scalar units of
  `RationalHeckeRing n` and the multiplicative submonoid of positive scalar operators in
  `IntegralHeckeRing n`.

## Main results

* `HeckeRing.GLn.neg_one_mem_SLnZ_iff`, `HeckeRing.GLn.neg_mem_doubleCoset_SLnZ_iff`,
  `HeckeRing.GLn.doubleCoset_neg_GLnZ`: parity behavior of `-I_n` on double cosets.
* `HeckeRing.GLn.exists_pos_natDiagGL_mul_mem_intEntries`,
  `HeckeRing.GLn.exists_pos_natDiagGL_mul_mem_posDetInt`: clearing denominators by a positive scalar
  matrix.
* `HeckeRing.GLn.commensurator_SLnZ_eq_top`, `HeckeRing.GLn.commensurator_GLnZ_eq_top`: both
  arithmetic subgroups have commensurator all of `GL_n(ℚ)`.
* `HeckeRing.GLn.isUnit_integralToRational_of_mem_scalarSubmonoid`,
  `HeckeRing.GLn.exists_mul_mem_scalarSubmonoid_eq`: `integralToRational n` sends
  `scalarSubmonoid n` to units and clears denominators across `RationalHeckeRing n`.

## References

* [G. Shimura, *Introduction to the arithmetic theory of automorphic functions*][shimura1971],
  Proposition 3.16.
* [J. A. Rhodes and T. R. Shemanske,
  *Rationality theorems for Hecke operators on GL_n*][rhodes1999], §2.
-/

public section

open Matrix Subgroup.Commensurable DoubleCoset Matrix.SpecialLinearGroup
open scoped Pointwise HeckeCosetModule

namespace HeckeRing.GLn

variable (n : ℕ)

section ParityAndSign

/-- `-I_n` belongs to `GL_n(ℤ)` in every rank `n`. -/
theorem neg_one_mem_GLnZ : (-1 : GL (Fin n) ℚ) ∈ GLnZ n := by
  refine (mem_GLnZ_iff n).mpr ⟨-1, Units.ext ?_⟩
  ext i j; by_cases hij : i = j <;> simp [Matrix.GeneralLinearGroup.map_apply, hij]

/-- Whenever `-I_n` belongs to the left subgroup `H₁`, negating a matrix leaves its
`(H₁, H₂)`-double coset unchanged. -/
theorem doubleCoset_neg_of_neg_one_mem_left {H₁ H₂ : Subgroup (GL (Fin n) ℚ)}
    (hneg : (-1 : GL (Fin n) ℚ) ∈ H₁) (g : GL (Fin n) ℚ) :
    doubleCoset (-g) H₁ H₂ = doubleCoset g H₁ H₂ :=
  (doubleCoset_eq_of_mem (mem_doubleCoset.mpr ⟨-1, hneg, 1, H₂.one_mem, by simp⟩)).symm

/-- Negating a matrix leaves its `GL_n(ℤ)`-double coset unchanged (`Rhodes–Shemanske`, §2). -/
@[simp]
theorem doubleCoset_neg_GLnZ (g : GL (Fin n) ℚ) :
    doubleCoset (-g) (GLnZ n) (GLnZ n) = doubleCoset g (GLnZ n) (GLnZ n) :=
  doubleCoset_neg_of_neg_one_mem_left n (neg_one_mem_GLnZ n) g

/-- `-I_n` belongs to `SL_n(ℤ)` if and only if `n` is even. -/
theorem neg_one_mem_SLnZ_iff : (-1 : GL (Fin n) ℚ) ∈ SLnZ n ↔ Even n := by
  refine ⟨fun h ↦ ?_, fun hn ↦ ?_⟩
  · have hdet := det_eq_one_of_mem_SLnZ n h
    rw [show ((-1 : GL (Fin n) ℚ) : Matrix (Fin n) (Fin n) ℚ) = (-1 : ℚ) • 1 by ext; simp,
      Matrix.det_smul, Fintype.card_fin, Matrix.det_one, mul_one] at hdet
    exact (neg_one_pow_eq_one_iff_even (by norm_num : (-1 : ℚ) ≠ 1)).mp hdet
  · have : Fact (Even (Fintype.card (Fin n))) := ⟨by simpa using hn⟩
    exact (mem_SLnZ_iff n).mpr ⟨-1, mapGL_neg_one⟩

/-- `-g` lies in the `SL_n(ℤ)`-double coset of `g ∈ GL_n(ℚ)` if and only if `n` is even
(`Rhodes–Shemanske`, §2). -/
theorem neg_mem_doubleCoset_SLnZ_iff (g : GL (Fin n) ℚ) :
    -g ∈ doubleCoset g (SLnZ n) (SLnZ n) ↔ Even n := by
  refine ⟨fun hmem ↦ ?_, fun hn ↦ ?_⟩
  · have hdet := det_eq_of_mem_doubleCoset_SLnZ n hmem
    rw [show ((-g : GL (Fin n) ℚ) : Matrix (Fin n) (Fin n) ℚ) = (-1 : ℚ) • ↑g by ext; simp,
      Matrix.det_smul, Fintype.card_fin] at hdet
    exact (neg_one_pow_eq_one_iff_even (by norm_num : (-1 : ℚ) ≠ 1)).mp
      (mul_right_cancel₀ g.det_ne_zero (hdet.trans (one_mul _).symm))
  · rw [← doubleCoset_neg_of_neg_one_mem_left n ((neg_one_mem_SLnZ_iff n).mpr hn) g]
    exact mem_doubleCoset_self _ _ _

/-- In even rank `n`, negating a matrix leaves its `SL_n(ℤ)`-double coset unchanged. -/
theorem doubleCoset_neg_SLnZ_of_even (hn : Even n) (g : GL (Fin n) ℚ) :
    doubleCoset (-g) (SLnZ n) (SLnZ n) = doubleCoset g (SLnZ n) (SLnZ n) :=
  doubleCoset_neg_of_neg_one_mem_left n ((neg_one_mem_SLnZ_iff n).mpr hn) g

/-- The diagonal sign-flip matrix `diag(-1, 1, …, 1) ∈ GL_n(ℤ)` in positive rank `n`. -/
noncomputable def signFlipGL [NeZero n] : GL (Fin n) ℚ :=
  TauCeti.diagGL fun i : Fin n ↦ if i = 0 then (-1 : ℚˣ) else 1

/-- `signFlipGL` belongs to `GL_n(ℤ)`. -/
theorem signFlipGL_mem_GLnZ [NeZero n] : signFlipGL n ∈ GLnZ n := by
  refine (mem_GLnZ_iff n).mpr ⟨TauCeti.diagGL fun i : Fin n ↦ if i = 0 then (-1 : ℤˣ) else 1, ?_⟩
  rw [TauCeti.map_diagGL, signFlipGL]; congr 1; funext i; split_ifs <;> rfl

/-- `signFlipGL` is an involution. -/
@[simp]
theorem signFlipGL_mul_self [NeZero n] : signFlipGL n * signFlipGL n = 1 := by
  rw [signFlipGL, ← map_mul]; convert map_one TauCeti.diagGL
  funext i; simp only [Pi.mul_apply, Pi.one_apply]; split_ifs <;> simp

/-- `signFlipGL` equals its own inverse. -/
@[simp]
theorem signFlipGL_inv [NeZero n] : (signFlipGL n)⁻¹ = signFlipGL n :=
  inv_eq_of_mul_eq_one_right (signFlipGL_mul_self n)

/-- `signFlipGL` has determinant `-1`. -/
@[simp]
theorem det_signFlipGL [NeZero n] : (↑(signFlipGL n) : Matrix (Fin n) (Fin n) ℚ).det = -1 := by
  rw [← Matrix.GeneralLinearGroup.val_det_apply, signFlipGL, TauCeti.det_diagGL,
    Finset.prod_eq_single (0 : Fin n)]
  · simp
  · exact fun i _ hi ↦ by rw [ite_eq_right hi]
  · exact fun h ↦ absurd (Finset.mem_univ (0 : Fin n)) h

/-- `signFlipGL` commutes with every diagonal matrix in `GL_n(ℚ)`. -/
theorem signFlipGL_comm_diagGL [NeZero n] (t : Fin n → ℚˣ) :
    signFlipGL n * TauCeti.diagGL t = TauCeti.diagGL t * signFlipGL n :=
  ((Commute.all _ t).map TauCeti.diagGL).eq

/-- `signFlipGL` commutes with every natural diagonal matrix `natDiagGL n a`. -/
theorem signFlipGL_comm_natDiagGL [NeZero n] (a : Fin n → ℕ) :
    signFlipGL n * natDiagGL n a = natDiagGL n a * signFlipGL n := by
  by_cases ha : ∀ i, 0 < a i
  · apply Units.ext
    simp only [Units.val_mul, natDiagGL_coe n a ha, signFlipGL, TauCeti.diagGL_coe,
      Matrix.diagonal_mul_diagonal]
    exact congrArg Matrix.diagonal (funext fun _ ↦ mul_comm _ _)
  · rw [natDiagGL_of_not_pos n ha, mul_one, one_mul]

end ParityAndSign

section Commensurator

/-- **Clearing denominators in `GL_n(ℚ)`**: for every `g ∈ GL_n(ℚ)` there is a positive natural `c`
such that `diag(c, …, c) * g` has integer entries. -/
theorem exists_pos_natDiagGL_mul_mem_intEntries (g : GL (Fin n) ℚ) :
    ∃ c : ℕ, 0 < c ∧ natDiagGL n (fun _ ↦ c) * g ∈ intEntries n := by
  set A : Matrix (Fin n) (Fin n) ℚ := ↑g with hA
  have hc : 0 < A.den := Nat.pos_of_ne_zero A.den_ne_zero
  refine ⟨A.den, hc, (mem_intEntries n).mpr ((hasIntEntries_iff n).mpr ⟨A.num, ?_⟩)⟩
  ext i j
  simp only [Units.val_mul, ← hA, natDiagGL_coe n _ fun _ ↦ hc, Matrix.diagonal_mul,
    Matrix.map_apply]
  rw [← A.num_div_den i j, mul_div_cancel₀ _ (Nat.cast_ne_zero.mpr A.den_ne_zero)]

/-- **Clearing denominators in `GL_n^+(ℚ)`**: for every `g ∈ GL_n^+(ℚ)` there is a positive natural
`c` such that `diag(c, …, c) * g` lies in Shimura's integral submonoid `posDetInt n`. -/
theorem exists_pos_natDiagGL_mul_mem_posDetInt {g : GL (Fin n) ℚ}
    (hg : g ∈ Matrix.GLPos (Fin n) ℚ) :
    ∃ c : ℕ, 0 < c ∧ natDiagGL n (fun _ ↦ c) * g ∈ posDetInt n := by
  obtain ⟨c, hc, hint⟩ := exists_pos_natDiagGL_mul_mem_intEntries n g
  have hprod := (Matrix.GLPos (Fin n) ℚ).mul_mem
    (posDetInt_le_glpos n (natDiagGL_mem_posDetInt n (fun _ ↦ c))) hg
  rw [Matrix.mem_glpos, Matrix.GeneralLinearGroup.val_det_apply] at hprod
  exact ⟨c, hc, (mem_posDetInt_iff n).mpr ⟨(mem_intEntries n).mp hint, hprod⟩⟩

/-- **The commensurator of `SL_n(ℤ)` in `GL_n(ℚ)` is the whole group.** -/
theorem commensurator_SLnZ_eq_top : commensurator (SLnZ n) = ⊤ := by
  rw [Subgroup.eq_top_iff']
  intro g
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact Subsingleton.elim g 1 ▸ (commensurator (SLnZ 0)).one_mem
  · have : NeZero n := ⟨hn.ne'⟩
    obtain ⟨c, -, hcg⟩ := exists_pos_natDiagGL_mul_mem_intEntries n g
    have h1 := mem_commensurator_of_hasIntEntries n (hasIntEntries_natDiagGL n (fun _ ↦ c))
    have h2 := mem_commensurator_of_hasIntEntries n ((mem_intEntries n).mp hcg)
    have hprod := (commensurator (SLnZ n)).mul_mem ((commensurator (SLnZ n)).inv_mem h1) h2
    rwa [inv_mul_cancel_left] at hprod

/-- `SL_n(ℤ)` has finite index (at most `2`) inside `GL_n(ℤ)`. -/
instance finiteIndex_SLnZ_subgroupOf_GLnZ : ((SLnZ n).subgroupOf (GLnZ n)).FiniteIndex := by
  have hinj : Function.Injective (fun q : GLnZ n ⧸ (SLnZ n).subgroupOf (GLnZ n) ↦
      decide (((q.out : GL (Fin n) ℚ) : Matrix (Fin n) (Fin n) ℚ).det = 1)) := by
    intro q₁ q₂ hdec
    have hiff := decide_eq_decide.mp hdec
    have hdet_eq : ((q₁.out : GL (Fin n) ℚ) : Matrix (Fin n) (Fin n) ℚ).det =
        ((q₂.out : GL (Fin n) ℚ) : Matrix (Fin n) (Fin n) ℚ).det := by
      rcases det_eq_one_or_neg_one_of_mem_GLnZ n q₁.out.2 with h₁ | h₁
      · exact h₁.trans (hiff.mp h₁).symm
      · have h₂ := (det_eq_one_or_neg_one_of_mem_GLnZ n q₂.out.2).resolve_left
          fun h₂ ↦ absurd (hiff.mpr h₂) (by rw [h₁]; norm_num)
        exact h₁.trans h₂.symm
    have hSL := inv_mul_mem_SLnZ_of_mem_GLnZ_of_det_eq n q₁.out.2 q₂.out.2 hdet_eq
    simpa only [QuotientGroup.out_eq'] using QuotientGroup.eq.mpr (Subgroup.mem_subgroupOf.mpr hSL)
  have : Finite (GLnZ n ⧸ (SLnZ n).subgroupOf (GLnZ n)) := Finite.of_injective _ hinj
  exact Subgroup.finiteIndex_of_finite_quotient

/-- `GL_n(ℤ)` and `SL_n(ℤ)` are commensurable in `GL_n(ℚ)`. -/
theorem commensurable_GLnZ_SLnZ : Subgroup.Commensurable (GLnZ n) (SLnZ n) :=
  ⟨Subgroup.isFiniteRelIndex_iff_relIndex_ne_zero.mpr
      (by rw [Subgroup.relIndex_eq_one.mpr (SLnZ_le_GLnZ n)]; exact one_ne_zero),
    Subgroup.isFiniteRelIndex_iff_relIndex_ne_zero.mpr Subgroup.FiniteIndex.index_ne_zero⟩

/-- **The commensurator of `GL_n(ℤ)` in `GL_n(ℚ)` is the whole group.** -/
theorem commensurator_GLnZ_eq_top : commensurator (GLnZ n) = ⊤ :=
  (commensurable_GLnZ_SLnZ n).eq.trans (commensurator_SLnZ_eq_top n)

/-- The positive-determinant rational Hecke triple `(SL_n(ℤ), GL_n^+(ℚ))`. -/
instance instIsHeckeTripleGLPosSLnZ :
    IsHeckeTriple (Matrix.GLPos (Fin n) ℚ).toSubmonoid (SLnZ n) (SLnZ n) :=
  IsHeckeTriple.of_diagonal (SLnZ_le_glpos n) (by rw [commensurator_SLnZ_eq_top]; exact le_top)

/-- The full rational Hecke triple `(GL_n(ℤ), GL_n(ℚ))`. -/
instance instIsHeckeTripleTopGLnZ :
    IsHeckeTriple (⊤ : Submonoid (GL (Fin n) ℚ)) (GLnZ n) (GLnZ n) :=
  IsHeckeTriple.of_diagonal le_top (by rw [commensurator_GLnZ_eq_top]; exact le_top)

/-- The positive-determinant rational Hecke ring `H(SL_n(ℤ), GL_n^+(ℚ))` over `ℤ`. -/
abbrev RationalHeckeRing := 𝕋 (Matrix.GLPos (Fin n) ℚ).toSubmonoid (SLnZ n) ℤ

/-- The full rational Hecke ring `H(GL_n(ℤ), GL_n(ℚ))` over `ℤ`. -/
abbrev FullHeckeRing := 𝕋 (⊤ : Submonoid (GL (Fin n) ℚ)) (GLnZ n) ℤ

end Commensurator

section Comparison

/-- **Integral-to-rational Hecke ring embedding** (`Shimura` Proposition 3.16 /
`Rhodes–Shemanske` §2): enlarging `posDetInt n` to `GL_n^+(ℚ)` embeds `𝕋 (posDetInt n) (SLnZ n) R`
injectively into `𝕋 (GLPos (Fin n) ℚ).toSubmonoid (SLnZ n) R` over any coefficient semiring `R`. -/
noncomputable def integralToRationalRingHom [NeZero n] (R : Type*) [Semiring R] :
    𝕋 (posDetInt n) (SLnZ n) R →+* 𝕋 (Matrix.GLPos (Fin n) ℚ).toSubmonoid (SLnZ n) R :=
  HeckeCosetModule.mapSubmonoidRingHom R (posDetInt_le_glpos n)

/-- The integral-to-rational embedding over `ℤ`. -/
noncomputable abbrev integralToRational [NeZero n] :
    IntegralHeckeRing n →+* RationalHeckeRing n :=
  integralToRationalRingHom n ℤ

/-- `integralToRationalRingHom` maps a basis element to the corresponding rational basis element. -/
@[simp]
theorem integralToRationalRingHom_single [NeZero n] (R : Type*) [Semiring R]
    (D : HeckeCoset (posDetInt n) (SLnZ n) (SLnZ n)) (b : R) :
    integralToRationalRingHom n R (HeckeCosetModule.single R D b) =
      HeckeCosetModule.single R (D.map (posDetInt_le_glpos n) le_rfl le_rfl) b :=
  HeckeCosetModule.mapSubmonoidRingHom_single R (posDetInt_le_glpos n) D b

/-- `integralToRationalRingHom` is injective over any coefficient semiring `R`. -/
theorem integralToRationalRingHom_injective [NeZero n] (R : Type*) [Semiring R] :
    Function.Injective (integralToRationalRingHom n R) :=
  HeckeCosetModule.mapSubmonoidRingHom_injective R (posDetInt_le_glpos n)

/-- `integralToRational` is injective. -/
theorem integralToRational_injective [NeZero n] :
    Function.Injective (integralToRational n) :=
  integralToRationalRingHom_injective n ℤ

/-- Image of a diagonal Hecke operator `diagElem a` under `integralToRational`. -/
theorem integralToRational_diagElem [NeZero n] (a : Fin n → ℕ) :
    integralToRational n (diagElem a) =
      HeckeCosetModule.single ℤ
        (HeckeCoset.mk (SLnZ n) (SLnZ n)
          ⟨natDiagGL n a, posDetInt_le_glpos n (natDiagGL_mem_posDetInt n a)⟩) 1 := by
  rw [diagElem_def, integralToRationalRingHom_single, diagCoset_def, HeckeCoset.map_mk]; rfl

/-- Every `g ∈ GL_n(ℚ)` can be translated on the left into `GL_n^+(ℚ)` by an element of
`GL_n(ℤ)`. -/
theorem exists_mem_GLnZ_mul_mem_glpos (g : GL (Fin n) ℚ) :
    ∃ u ∈ GLnZ n, u * g ∈ Matrix.GLPos (Fin n) ℚ := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact ⟨1, (GLnZ 0).one_mem, Subsingleton.elim (1 * g) 1 ▸ (Matrix.GLPos (Fin 0) ℚ).one_mem⟩
  · have : NeZero n := ⟨hn.ne'⟩
    rcases lt_or_gt_of_ne g.det_ne_zero with hneg | hpos
    · refine ⟨signFlipGL n, signFlipGL_mem_GLnZ n, ?_⟩
      rw [Matrix.mem_glpos, Matrix.GeneralLinearGroup.val_det_apply, Units.val_mul,
        Matrix.det_mul, det_signFlipGL]; linarith
    · refine ⟨1, (GLnZ n).one_mem, ?_⟩
      rwa [one_mul, Matrix.mem_glpos, Matrix.GeneralLinearGroup.val_det_apply]

/-- For every `g ∈ GL_n^+(ℚ)` in positive rank `n`, clearing denominators and putting
`diag(c, …, c) * g = γ₁ * diag(a) * γ₂` in Smith normal form produces `s₁, s₂ ∈ GL_n(ℤ)` with
`det s₁ = -1` and `s₁ * g = g * s₂` (`Rhodes–Shemanske`, §2). -/
private lemma exists_mem_GLnZ_det_neg_one_mul_eq_mul [NeZero n] {g : GL (Fin n) ℚ}
    (hg : g ∈ Matrix.GLPos (Fin n) ℚ) :
    ∃ s₁ ∈ GLnZ n, ∃ s₂ ∈ GLnZ n,
      (↑s₁ : Matrix (Fin n) (Fin n) ℚ).det = -1 ∧ s₁ * g = g * s₂ := by
  obtain ⟨c, -, hcg⟩ := exists_pos_natDiagGL_mul_mem_posDetInt n hg
  obtain ⟨a, -, -, hD⟩ :=
    exists_diagonal_representative (HeckeCoset.mk (SLnZ n) (SLnZ n) ⟨_, hcg⟩)
  have hmem : natDiagGL n (fun _ ↦ c) * g ∈ doubleCoset (natDiagGL n a) (SLnZ n) (SLnZ n) := by
    have hset := congrArg HeckeCoset.toSet hD
    rw [HeckeCoset.toSet_mk, diagCoset_toSet] at hset
    exact hset ▸ mem_doubleCoset_self _ _ _
  obtain ⟨γ₁, hγ₁, γ₂, hγ₂, hsnf⟩ := mem_doubleCoset.mp hmem
  refine ⟨γ₁ * signFlipGL n * γ₁⁻¹,
    (GLnZ n).mul_mem ((GLnZ n).mul_mem (SLnZ_le_GLnZ n hγ₁) (signFlipGL_mem_GLnZ n))
      ((GLnZ n).inv_mem (SLnZ_le_GLnZ n hγ₁)),
    γ₂⁻¹ * signFlipGL n * γ₂,
    (GLnZ n).mul_mem ((GLnZ n).mul_mem ((GLnZ n).inv_mem (SLnZ_le_GLnZ n hγ₂))
      (signFlipGL_mem_GLnZ n)) (SLnZ_le_GLnZ n hγ₂), ?_, ?_⟩
  · simp only [Units.val_mul, Matrix.det_mul, det_signFlipGL,
      det_eq_one_of_mem_SLnZ n hγ₁, det_eq_one_of_mem_SLnZ n ((SLnZ n).inv_mem hγ₁)]; ring
  · apply mul_left_cancel (a := natDiagGL n (fun _ ↦ c))
    calc natDiagGL n (fun _ ↦ c) * ((γ₁ * signFlipGL n * γ₁⁻¹) * g)
        = (γ₁ * signFlipGL n * γ₁⁻¹) * (natDiagGL n (fun _ ↦ c) * g) := by
            rw [← mul_assoc, natDiagGL_const_comm n c, mul_assoc]
      _ = γ₁ * (natDiagGL n a * signFlipGL n) * γ₂ := by
            rw [hsnf, ← signFlipGL_comm_natDiagGL]; group
      _ = natDiagGL n (fun _ ↦ c) * (g * (γ₂⁻¹ * signFlipGL n * γ₂)) := by
            rw [← mul_assoc (natDiagGL n _), hsnf]; group

/-- **Stabilizer coset condition for `(SL_n(ℤ), GL_n(ℤ))` along `GL_n^+(ℚ)`.** For every
`g ∈ GL_n^+(ℚ)`, `SL_n(ℤ)` meets every left coset of `GL_n(ℤ) ∩ g · GL_n(ℤ) · g⁻¹` in `GL_n(ℤ)`. -/
theorem exists_mem_SLnZ_inv_mul_mem_conj_GLnZ {g : GL (Fin n) ℚ}
    (hg : g ∈ Matrix.GLPos (Fin n) ℚ) {u : GL (Fin n) ℚ} (hu : u ∈ GLnZ n) :
    ∃ x ∈ SLnZ n, x⁻¹ * u ∈ ConjAct.toConjAct g • GLnZ n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact ⟨1, (SLnZ 0).one_mem,
      Subsingleton.elim ((1 : GL (Fin 0) ℚ)⁻¹ * u) 1 ▸ (ConjAct.toConjAct g • GLnZ 0).one_mem⟩
  have : NeZero n := ⟨hn.ne'⟩
  rcases det_eq_one_or_neg_one_of_mem_GLnZ n hu with hu1 | hu1
  · exact ⟨u, mem_SLnZ_of_mem_GLnZ_of_det_eq_one n hu hu1,
      by rw [inv_mul_cancel]; exact Subgroup.one_mem _⟩
  · obtain ⟨s₁, hs₁, s₂, hs₂, hs₁_det, hintertwine⟩ :=
      exists_mem_GLnZ_det_neg_one_mul_eq_mul n hg
    refine ⟨u * s₁⁻¹, mem_SLnZ_of_mem_GLnZ_of_det_eq_one n
      ((GLnZ n).mul_mem hu ((GLnZ n).inv_mem hs₁)) ?_, ?_⟩
    · rw [Units.val_mul, Matrix.det_mul, det_inv_of_mem_GLnZ n hs₁, hu1, hs₁_det]; norm_num
    · rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ConjAct.smul_def, ConjAct.ofConjAct_inv,
        ConjAct.ofConjAct_toConjAct, inv_inv, show (u * s₁⁻¹)⁻¹ * u = s₁ by group,
        mul_assoc, hintertwine, inv_mul_cancel_left]
      exact hs₂

/-- **Rational-to-full Hecke ring isomorphism** (`Shimura` Proposition 3.16 /
`Rhodes–Shemanske` §2): `H_R(SL_n(ℤ), GL_n^+(ℚ)) ≃+* H_R(GL_n(ℤ), GL_n(ℚ))` over any coefficient
semiring `R`. -/
noncomputable def rationalToFullRingEquiv (R : Type*) [Semiring R] :
    𝕋 (Matrix.GLPos (Fin n) ℚ).toSubmonoid (SLnZ n) R ≃+*
      𝕋 (⊤ : Submonoid (GL (Fin n) ℚ)) (GLnZ n) R :=
  HeckeCosetModule.mapSubgroupRingEquiv R (SLnZ_eq_GLnZ_inf_glpos n) le_top le_rfl
    (fun δ' ↦ exists_mem_GLnZ_mul_mem_glpos n (δ' : GL (Fin n) ℚ))
    (fun g _ hu ↦ exists_mem_SLnZ_inv_mul_mem_conj_GLnZ n g.2 hu)

/-- The rational-to-full Hecke ring isomorphism over `ℤ`. -/
noncomputable abbrev rationalToFullEquiv : RationalHeckeRing n ≃+* FullHeckeRing n :=
  rationalToFullRingEquiv n ℤ

/-- `rationalToFullRingEquiv` sends each basis element to the corresponding `GL_n(ℤ)`-coset basis
element. -/
@[simp]
theorem rationalToFullRingEquiv_single (R : Type*) [Semiring R]
    (D : HeckeCoset (Matrix.GLPos (Fin n) ℚ).toSubmonoid (SLnZ n) (SLnZ n)) (b : R) :
    rationalToFullRingEquiv n R (HeckeCosetModule.single R D b) =
      HeckeCosetModule.single R (D.map le_top (SLnZ_le_GLnZ n) (SLnZ_le_GLnZ n)) b :=
  HeckeCosetModule.mapSubgroupRingEquiv_single R (SLnZ_eq_GLnZ_inf_glpos n) le_top le_rfl _ _ D b

/-- Composite embedding `H_R(SL_n(ℤ), M_n^+(ℤ)) ↪ H_R(GL_n(ℤ), GL_n(ℚ))` of the integral Hecke ring
into the full rational Hecke ring. -/
noncomputable def integralToFullRingHom [NeZero n] (R : Type*) [Semiring R] :
    𝕋 (posDetInt n) (SLnZ n) R →+* 𝕋 (⊤ : Submonoid (GL (Fin n) ℚ)) (GLnZ n) R :=
  (rationalToFullRingEquiv n R).toRingHom.comp (integralToRationalRingHom n R)

/-- `integralToFullRingHom` maps a basis element to the corresponding `GL_n(ℤ)`-coset basis
element. -/
@[simp]
theorem integralToFullRingHom_single [NeZero n] (R : Type*) [Semiring R]
    (D : HeckeCoset (posDetInt n) (SLnZ n) (SLnZ n)) (b : R) :
    integralToFullRingHom n R (HeckeCosetModule.single R D b) =
      HeckeCosetModule.single R (D.map le_top (SLnZ_le_GLnZ n) (SLnZ_le_GLnZ n)) b := by
  simp [integralToFullRingHom]

/-- `integralToFullRingHom` is injective over any coefficient semiring `R`. -/
theorem integralToFullRingHom_injective [NeZero n] (R : Type*) [Semiring R] :
    Function.Injective (integralToFullRingHom n R) :=
  (rationalToFullRingEquiv n R).injective.comp (integralToRationalRingHom_injective n R)

end Comparison

section Commutativity

/-- Transposition as an anti-involution of the rational Hecke datum `(GL_n^+(ℚ), SL_n(ℤ))`. -/
noncomputable def transposeRationalAntiInvolution :
    HeckeAntiInvolution (Matrix.GLPos (Fin n) ℚ).toSubmonoid (SLnZ n) :=
  HeckeAntiInvolution.ofAmbient
    (Matrix.GeneralLinearGroup.transposeMulEquiv (R := ℚ) (Fin n)).toMonoidHom
    Matrix.GeneralLinearGroup.transposeMulEquiv_transposeMulEquiv
    (fun _ hg ↦ transposeMulEquiv_mem_SLnZ n hg)
    (fun _ hg ↦ Matrix.GeneralLinearGroup.transposeMulEquiv_mem_glpos hg)

/-- `transposeRationalAntiInvolution` acts on `GL_n^+(ℚ)` by matrix transposition. -/
@[simp]
theorem transposeRationalAntiInvolution_bar {x : GL (Fin n) ℚ}
    (hx : x ∈ (Matrix.GLPos (Fin n) ℚ).toSubmonoid) :
    (transposeRationalAntiInvolution n).bar x hx =
      (Matrix.GeneralLinearGroup.transposeMulEquiv (Fin n) x).unop :=
  HeckeAntiInvolution.ofAmbient_bar _ _ _ _ x hx

/-- Transposition fixes every double coset in `SL_n(ℤ) \ GL_n^+(ℚ) / SL_n(ℤ)`. -/
@[simp]
theorem transposeRationalAntiInvolution_onHeckeCoset_eq_self
    (D : HeckeCoset (Matrix.GLPos (Fin n) ℚ).toSubmonoid (SLnZ n) (SLnZ n)) :
    (transposeRationalAntiInvolution n).onHeckeCoset D = D := by
  induction D using HeckeCoset.induction with | h g =>
  rw [(transposeRationalAntiInvolution n).onHeckeCoset_mk]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact congrArg (HeckeCoset.mk _ _) (Subtype.ext (Subsingleton.elim _ _))
  have : NeZero n := ⟨hn.ne'⟩
  obtain ⟨c, -, hcg⟩ := exists_pos_natDiagGL_mul_mem_posDetInt n g.2
  have hbar_int := (transposeAntiInvolution n).bar_mem_doubleCoset_self
    (transposeAntiInvolution_onHeckeCoset_eq_self n) ⟨natDiagGL n (fun _ ↦ c) * g, hcg⟩
  rw [transposeAntiInvolution_bar] at hbar_int
  obtain ⟨γ₁, hγ₁, γ₂, hγ₂, hEq⟩ := mem_doubleCoset.mp hbar_int
  refine HeckeCoset.mk_eq_mk_of_mem (mem_doubleCoset.mpr ⟨γ₁, hγ₁, γ₂, hγ₂, ?_⟩)
  dsimp only; rw [transposeRationalAntiInvolution_bar]
  apply mul_left_cancel (a := natDiagGL n (fun _ ↦ c))
  calc natDiagGL n (fun _ ↦ c) *
        (Matrix.GeneralLinearGroup.transposeMulEquiv (Fin n) (g : GL (Fin n) ℚ)).unop
      = (Matrix.GeneralLinearGroup.transposeMulEquiv (Fin n)
          (natDiagGL n (fun _ ↦ c) * (g : GL (Fin n) ℚ))).unop := by
        rw [map_mul, MulOpposite.unop_mul, transposeMulEquiv_natDiagGL, ← natDiagGL_const_comm]
    _ = natDiagGL n (fun _ ↦ c) * (γ₁ * (g : GL (Fin n) ℚ) * γ₂) := by
        rw [hEq, ← mul_assoc γ₁, ← natDiagGL_const_comm n c γ₁]; group

/-- The positive-determinant rational Hecke ring is commutative over any commutative semiring
`R`. -/
@[instance_reducible]
noncomputable def commSemiringRationalHeckeRing (R : Type*) [CommSemiring R] :
    CommSemiring (𝕋 (Matrix.GLPos (Fin n) ℚ).toSubmonoid (SLnZ n) R) :=
  HeckeCosetModule.commSemiringOfAntiInvolution R (transposeRationalAntiInvolution n)
    (transposeRationalAntiInvolution_onHeckeCoset_eq_self n)

/-- The positive-determinant rational Hecke ring is a commutative ring over any commutative ring
`R`, extending the ambient `Ring` instance. -/
-- `@[expose]` keeps `toRing` definitionally equal to the ambient `Ring` instance when activated
-- as a local instance in downstream modules (e.g. `PolynomialRing/Localization.lean`).
@[expose, instance_reducible]
noncomputable def commRingRationalHeckeRing (R : Type*) [CommRing R] :
    CommRing (𝕋 (Matrix.GLPos (Fin n) ℚ).toSubmonoid (SLnZ n) R) :=
  { (inferInstance : Ring (𝕋 (Matrix.GLPos (Fin n) ℚ).toSubmonoid (SLnZ n) R)) with
    mul_comm := HeckeCosetModule.mul_comm_of_antiInvolution R (transposeRationalAntiInvolution n)
      (transposeRationalAntiInvolution_onHeckeCoset_eq_self n) }

/-- Multiplication in the full rational Hecke ring `H_R(GL_n(ℤ), GL_n(ℚ))` is commutative over any
commutative semiring `R`. -/
theorem mul_comm_fullHeckeRing (R : Type*) [CommSemiring R]
    (f g : 𝕋 (⊤ : Submonoid (GL (Fin n) ℚ)) (GLnZ n) R) : f * g = g * f :=
  (rationalToFullRingEquiv n R).symm.injective (by
    rw [map_mul, map_mul]
    exact HeckeCosetModule.mul_comm_of_antiInvolution R (transposeRationalAntiInvolution n)
      (transposeRationalAntiInvolution_onHeckeCoset_eq_self n) _ _)

/-- The full rational Hecke ring `H_R(GL_n(ℤ), GL_n(ℚ))` is a commutative semiring over any
commutative semiring `R`. -/
@[instance_reducible]
noncomputable def commSemiringFullHeckeRing (R : Type*) [CommSemiring R] :
    CommSemiring (𝕋 (⊤ : Submonoid (GL (Fin n) ℚ)) (GLnZ n) R) :=
  { HeckeCosetModule.instSemiringHeckeRing R with
    mul_comm := mul_comm_fullHeckeRing n R }

/-- The full rational Hecke ring `H_R(GL_n(ℤ), GL_n(ℚ))` is a commutative ring over any commutative
ring `R`, extending the ambient `Ring` instance. -/
@[instance_reducible]
noncomputable def commRingFullHeckeRing (R : Type*) [CommRing R] :
    CommRing (𝕋 (⊤ : Submonoid (GL (Fin n) ℚ)) (GLnZ n) R) :=
  { (inferInstance : Ring (𝕋 (⊤ : Submonoid (GL (Fin n) ℚ)) (GLnZ n) R)) with
    mul_comm := mul_comm_fullHeckeRing n R }

end Commutativity

attribute [local instance] commRingRationalHeckeRing

section ScalarUnits

/-- Multiplying a rational double-coset basis element on the right by the scalar coset of
`natDiagGL n (fun _ ↦ c)` gives the single double coset of the product representative. -/
theorem single_mul_natDiagGL_const (g : (Matrix.GLPos (Fin n) ℚ).toSubmonoid) (c : ℕ) :
    HeckeCosetModule.single ℤ (HeckeCoset.mk (SLnZ n) (SLnZ n) g) 1 *
        HeckeCosetModule.single ℤ
          (HeckeCoset.mk (SLnZ n) (SLnZ n)
            ⟨natDiagGL n (fun _ ↦ c),
              posDetInt_le_glpos n (natDiagGL_mem_posDetInt n (fun _ ↦ c))⟩) 1 =
      HeckeCosetModule.single ℤ
        (HeckeCoset.mk (SLnZ n) (SLnZ n)
          ⟨(g : GL (Fin n) ℚ) * natDiagGL n (fun _ ↦ c),
            (Matrix.GLPos (Fin n) ℚ).mul_mem g.2
              (posDetInt_le_glpos n (natDiagGL_mem_posDetInt n (fun _ ↦ c)))⟩) 1 :=
  HeckeCosetModule.single_mul_single_of_mem_normalizer_right (x := g)
    (y := ⟨natDiagGL n (fun _ ↦ c),
      posDetInt_le_glpos n (natDiagGL_mem_posDetInt n (fun _ ↦ c))⟩) ℤ
    (natDiagGL_const_mem_normalizer n c (SLnZ n))

/-- The scalar operator `T(c, …, c)` as a central unit of `RationalHeckeRing n`, with inverse
`[SL_n(ℤ) · (natDiagGL n (fun _ ↦ c))⁻¹ · SL_n(ℤ)]` (taking the fallback value `1` at `c = 0` to
match `natDiagGL`). -/
noncomputable def scalarUnit (c : ℕ) : (RationalHeckeRing n)ˣ :=
  HeckeCosetModule.unitOfMemNormalizer ℤ
    (posDetInt_le_glpos n (natDiagGL_mem_posDetInt n (fun _ ↦ c)))
    ((Matrix.GLPos (Fin n) ℚ).inv_mem
      (posDetInt_le_glpos n (natDiagGL_mem_posDetInt n (fun _ ↦ c))))
    (natDiagGL_const_mem_normalizer n c (SLnZ n))

/-- The inverse of `scalarUnit` is the single double-coset operator of
`(natDiagGL n (fun _ ↦ c))⁻¹`. -/
@[simp]
theorem val_inv_scalarUnit (c : ℕ) :
    (↑(scalarUnit n c)⁻¹ : RationalHeckeRing n) =
      HeckeCosetModule.single ℤ
        (HeckeCoset.mk (SLnZ n) (SLnZ n)
          ⟨(natDiagGL n (fun _ ↦ c))⁻¹,
             (Matrix.GLPos (Fin n) ℚ).inv_mem
               (posDetInt_le_glpos n (natDiagGL_mem_posDetInt n (fun _ ↦ c)))⟩) 1 := by
  rw [scalarUnit, HeckeCosetModule.val_inv_unitOfMemNormalizer]

private lemma natDiagGL_const_zero : natDiagGL n (fun _ ↦ 0) = 1 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact Subsingleton.elim _ _
  · exact natDiagGL_of_not_pos n fun h ↦ Nat.lt_irrefl 0 (h ⟨0, hn⟩)

/-- At `c = 0`, `scalarUnit` takes the fallback value `1`. -/
@[simp]
theorem scalarUnit_zero : scalarUnit n 0 = 1 := by
  apply Units.ext
  rw [scalarUnit, HeckeCosetModule.val_unitOfMemNormalizer, Units.val_one,
    HeckeCosetModule.one_def, HeckeCoset.one_def]
  exact congrArg (HeckeCosetModule.single ℤ · 1)
    (congrArg (HeckeCoset.mk (SLnZ n) (SLnZ n)) (Subtype.ext (natDiagGL_const_zero n)))

/-- At `c = 1`, `scalarUnit` is the multiplicative identity. -/
@[simp]
theorem scalarUnit_one : scalarUnit n 1 = 1 := by
  apply Units.ext
  rw [scalarUnit, HeckeCosetModule.val_unitOfMemNormalizer, Units.val_one,
    HeckeCosetModule.one_def, HeckeCoset.one_def]
  exact congrArg (HeckeCosetModule.single ℤ · 1)
    (congrArg (HeckeCoset.mk (SLnZ n) (SLnZ n)) (Subtype.ext (natDiagGL_one n)))

variable [NeZero n]

/-- The underlying element of `scalarUnit` is the image of `diagElem (fun _ ↦ c)` in
`RationalHeckeRing n`. -/
@[simp]
theorem val_scalarUnit (c : ℕ) :
    (scalarUnit n c : RationalHeckeRing n) = integralToRational n (diagElem (fun _ ↦ c)) := by
  rw [scalarUnit, HeckeCosetModule.val_unitOfMemNormalizer, integralToRational_diagElem]

/-- `scalarUnit` is multiplicative in positive scalars `c` and `d`. -/
theorem scalarUnit_mul {c d : ℕ} (hc : 0 < c) (hd : 0 < d) :
    scalarUnit n (c * d) = scalarUnit n c * scalarUnit n d := by
  apply Units.ext
  rw [Units.val_mul, val_scalarUnit, val_scalarUnit, val_scalarUnit, ← map_mul,
    diagElem_const_mul n c hc (fun _ ↦ d) (fun _ ↦ hd)]
  rfl

/-- The `k`-th power of `scalarUnit` at `c` is `scalarUnit` at `c ^ k`. -/
theorem scalarUnit_pow (c k : ℕ) :
    scalarUnit n c ^ k = scalarUnit n (c ^ k) := by
  rcases Nat.eq_zero_or_pos c with rfl | hc
  · rcases k with _ | k
    · simp
    · rw [Nat.zero_pow (Nat.succ_pos k), scalarUnit_zero, one_pow]
  · apply Units.ext
    rw [Units.val_pow_eq_pow_val, val_scalarUnit, val_scalarUnit, ← map_pow,
      diagElem_const_pow n c hc k]

/-- Every scalar operator `diagElem (fun _ ↦ c)` becomes a unit in `RationalHeckeRing n`. -/
theorem isUnit_integralToRational_diagElem_const (c : ℕ) :
    IsUnit (integralToRational n (diagElem (fun _ ↦ c))) :=
  val_scalarUnit n c ▸ (scalarUnit n c).isUnit

/-- The multiplicative submonoid of `IntegralHeckeRing n` consisting of the positive scalar Hecke
operators `T(c, …, c)` (`0 < c`). -/
noncomputable def scalarSubmonoid : Submonoid (IntegralHeckeRing n) where
  carrier := {f | ∃ c : ℕ, 0 < c ∧ f = diagElem (fun _ ↦ c)}
  one_mem' := ⟨1, Nat.one_pos, diagElem_one.symm⟩
  mul_mem' := by
    rintro _ _ ⟨c, hc, rfl⟩ ⟨d, hd, rfl⟩
    refine ⟨c * d, mul_pos hc hd, ?_⟩
    rw [diagElem_const_mul n c hc (fun _ ↦ d) (fun _ ↦ hd)]
    rfl

/-- Membership in `scalarSubmonoid n` by a positive scalar witness `c`. -/
@[simp]
theorem mem_scalarSubmonoid_iff {f : IntegralHeckeRing n} :
    f ∈ scalarSubmonoid n ↔ ∃ c : ℕ, 0 < c ∧ f = diagElem (fun _ ↦ c) :=
  Iff.rfl

/-- Every positive scalar operator `diagElem (fun _ ↦ c)` belongs to `scalarSubmonoid n`. -/
theorem diagElem_const_mem_scalarSubmonoid {c : ℕ} (hc : 0 < c) :
    diagElem (fun _ ↦ c) ∈ scalarSubmonoid n :=
  ⟨c, hc, rfl⟩

/-- Every element of `scalarSubmonoid n` maps to a unit under `integralToRational n`. -/
theorem isUnit_integralToRational_of_mem_scalarSubmonoid {s : IntegralHeckeRing n}
    (hs : s ∈ scalarSubmonoid n) : IsUnit (integralToRational n s) := by
  obtain ⟨c, -, rfl⟩ := hs
  exact isUnit_integralToRational_diagElem_const n c

/-- **Global denominator clearing in `RationalHeckeRing n`** (`Shimura`, Proposition 3.16): every
rational Hecke operator `z` becomes integral after multiplying by a positive scalar operator
`s ∈ scalarSubmonoid n`. -/
theorem exists_mul_mem_scalarSubmonoid_eq (z : RationalHeckeRing n) :
    ∃ x : IntegralHeckeRing n, ∃ s ∈ scalarSubmonoid n,
      z * integralToRational n s = integralToRational n x := by
  induction z using HeckeCosetModule.induction_linear with
  | h0 => exact ⟨0, 1, (scalarSubmonoid n).one_mem, by simp⟩
  | hsingle D m =>
    induction D using HeckeCoset.induction with | h g =>
    obtain ⟨c, hc, hcg⟩ := exists_pos_natDiagGL_mul_mem_posDetInt n g.2
    have hgc : (g : GL (Fin n) ℚ) * natDiagGL n (fun _ ↦ c) ∈ posDetInt n :=
      natDiagGL_const_comm n c g ▸ hcg
    refine ⟨HeckeCosetModule.single ℤ (HeckeCoset.mk (SLnZ n) (SLnZ n) ⟨_, hgc⟩) m,
      diagElem (fun _ ↦ c), diagElem_const_mem_scalarSubmonoid n hc, ?_⟩
    have h1 := single_mul_natDiagGL_const n g c
    rw [HeckeCosetModule.single_mul_single] at h1
    rw [integralToRational_diagElem, HeckeCosetModule.single_mul_single,
      integralToRational, integralToRationalRingHom_single, HeckeCoset.map_mk]
    exact (congrArg (m • ·) ((one_smul ℤ _).symm.trans h1)).trans
      (HeckeCosetModule.smul_single_one ℤ _ m)
  | hadd z₁ z₂ ih₁ ih₂ =>
    obtain ⟨x₁, s₁, hs₁, hx₁⟩ := ih₁
    obtain ⟨x₂, s₂, hs₂, hx₂⟩ := ih₂
    refine ⟨x₁ * s₂ + x₂ * s₁, s₁ * s₂, (scalarSubmonoid n).mul_mem hs₁ hs₂, ?_⟩
    calc (z₁ + z₂) * integralToRational n (s₁ * s₂)
        = (z₁ * integralToRational n s₁) * integralToRational n s₂ +
            (z₂ * integralToRational n s₂) * integralToRational n s₁ := by rw [map_mul]; ring
      _ = integralToRational n (x₁ * s₂ + x₂ * s₁) := by rw [hx₁, hx₂, map_add, map_mul, map_mul]

end ScalarUnits

end HeckeRing.GLn

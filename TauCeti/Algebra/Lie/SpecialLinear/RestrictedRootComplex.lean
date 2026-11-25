/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.CartanInvolution.RestrictScalars
public import TauCeti.Algebra.Lie.CartanInvolution.RestrictedRoot.Basic
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.LinearAlgebra.Matrix.IsDiag

/-!
# Restricted roots of `𝔰𝔩_n(ℂ)` viewed as a real Lie algebra

On `𝔰𝔩_n(ℂ)` viewed as a real Lie algebra, with the Cartan involution `θ X = -Xᴴ`
(`TauCeti.isCartanInvolution_restrictNegConjTranspose_slComplex`), the real trace-zero diagonal
matrices `𝔞` (`TauCeti.slComplexRealDiagonal`) form a maximal abelian subspace of the
`-1`-eigenspace `𝔭` (the Hermitian matrices). For `H ∈ 𝔞` the bracket `[H, X]` has `(k, l)` entry
`(H k k - H l l) X k l`, so:

* the centralizer `𝔤_0` of `𝔞` is the complex trace-zero diagonal matrices, and
  `𝔪 = 𝔤_0 ∩ 𝔨` is `i𝔞`, the imaginary trace-zero diagonal matrices;
* the restricted roots are the functionals `e_i - e_j : H ↦ H i i - H j j` for `i ≠ j`;
* the restricted root space of `e_i - e_j` is the complex line `ℂ E_ij`, of real dimension `2`.

So the restricted root system of `𝔰𝔩_n(ℂ)` as a real Lie algebra has the same roots as that of
`𝔰𝔩_n(ℝ)` (`TauCeti.mem_restrictedRoots_specialLinearDiagonal_iff`), with all multiplicities `2`
and `𝔪 = i𝔞`: this is the `𝔰𝔩₃(ℂ)` Check of RealSemisimpleLieGroups §1.2, for every `n`.

## Main definitions

* `TauCeti.slComplexReal`: `𝔰𝔩_n(ℂ)` viewed as a real Lie subalgebra of `𝔤𝔩_n(ℂ)`, with the Cartan
  involution `TauCeti.slComplexNegConjTranspose`.
* `TauCeti.slComplexRealDiagonal`: the real trace-zero diagonal matrices in `𝔰𝔩_n(ℂ)`.
* `TauCeti.slComplexRestrictedRoot`: the functional `e_i - e_j` on them.

## Main results

* `TauCeti.isMaximalAbelianInP_slComplexRealDiagonal`: `𝔞` is maximal abelian in `𝔭`.
* `TauCeti.mem_restrictedRootSpace_zero_slComplexRealDiagonal_iff`: `𝔤_0` is the diagonal
  matrices.
* `TauCeti.mem_restrictedRootSpace_zero_inf_fixedSubalgebra_slComplexRealDiagonal_iff`:
  `𝔪 = i𝔞`.
* `TauCeti.mem_restrictedRoots_slComplexRealDiagonal_iff`: the restricted roots are the
  `e_i - e_j` with `i ≠ j`.
* `TauCeti.mem_restrictedRootSpace_slComplexRestrictedRoot_iff`: the root space of `e_i - e_j`
  consists of the matrices supported at `(i, j)`.
* `TauCeti.finrank_restrictedRootSpace_slComplexRestrictedRoot`: its real dimension is `2`.

## References

* A. W. Knapp, *Lie Groups Beyond an Introduction*, 2nd ed., Chapter VI, §4.
-/

public section

open LieAlgebra Matrix Module Submodule

attribute [local instance 100] LieRing.ofAssociativeRing

namespace TauCeti

/-- For a diagonal `H`, the commutator `H X - X H` has `(k, l)` entry `(H k k - H l l) X k l`. -/
theorem mul_sub_mul_apply_of_isDiag {n R : Type*} [Fintype n] [CommRing R] {H : Matrix n n R}
    (hH : H.IsDiag) (X : Matrix n n R) (k l : n) :
    (H * X - X * H) k l = (H k k - H l l) * X k l := by
  rw [Matrix.sub_apply, Matrix.mul_apply, Matrix.mul_apply,
    Finset.sum_eq_single k (fun m _ hm ↦ by rw [hH (Ne.symm hm), zero_mul]) (by simp),
    Finset.sum_eq_single l (fun m _ hm ↦ by rw [hH hm, mul_zero]) (by simp)]
  ring

variable {n : Type*} [Fintype n] [DecidableEq n]

variable (n) in
/-- `𝔰𝔩_n(ℂ)` viewed as a real Lie algebra, as a real Lie subalgebra of `𝔤𝔩_n(ℂ)`. -/
noncomputable abbrev slComplexReal : LieSubalgebra ℝ (Matrix n n ℂ) :=
  ((SpecialLinear.sl n ℂ).restrictScalarsIncl ℝ).range

variable (n) in
/-- The Cartan involution `X ↦ -Xᴴ` of `𝔰𝔩_n(ℂ)` viewed as a real Lie algebra
(`TauCeti.isCartanInvolution_restrictNegConjTranspose_slComplex`). -/
noncomputable abbrev slComplexNegConjTranspose : slComplexReal n ≃ₗ⁅ℝ⁆ slComplexReal n :=
  (slComplexReal n).restrictNegConjTranspose
    ((SpecialLinear.sl n ℂ).conjTranspose_mem_range_restrictScalarsIncl
      fun _ ↦ SpecialLinear.conjTranspose_mem_sl)

variable (n) in
/-- `X ↦ -Xᴴ` is a Cartan involution of `𝔰𝔩_n(ℂ)` viewed as a real Lie algebra. -/
theorem isCartanInvolution_slComplexNegConjTranspose :
    (slComplexNegConjTranspose n).IsCartanInvolution :=
  isCartanInvolution_restrictNegConjTranspose_slComplex

variable (n) in
/-- The real trace-zero diagonal matrices, as a real subspace of `𝔰𝔩_n(ℂ)` viewed as a real Lie
algebra: a maximal abelian subspace of the Hermitian matrices
(`TauCeti.isMaximalAbelianInP_slComplexRealDiagonal`). -/
def slComplexRealDiagonal :
    Submodule ℝ (slComplexReal n) where
  carrier := {X | (X : Matrix n n ℂ).IsDiag ∧ ∀ k, ((X : Matrix n n ℂ) k k).im = 0}
  add_mem' {X Y} hX hY := ⟨by simpa using hX.1.add hY.1, fun k ↦ by simp [hX.2 k, hY.2 k]⟩
  zero_mem' := ⟨by simp, fun _ ↦ by simp⟩
  smul_mem' c X hX := ⟨by simpa using hX.1.smul c, fun k ↦ by simp [hX.2 k]⟩

theorem mem_slComplexRealDiagonal {X : slComplexReal n} :
    X ∈ slComplexRealDiagonal n ↔
      (X : Matrix n n ℂ).IsDiag ∧ ∀ k, ((X : Matrix n n ℂ) k k).im = 0 :=
  Iff.rfl

/-- The diagonal entries of an element of `𝔞` are real. -/
theorem ofReal_re_apply_self_of_mem_slComplexRealDiagonal
    {X : slComplexReal n} (hX : X ∈ slComplexRealDiagonal n)
    (k : n) : (((X : Matrix n n ℂ) k k).re : ℂ) = (X : Matrix n n ℂ) k k :=
  Complex.ext rfl (by simp [hX.2 k])

/-- For `H ∈ 𝔞`, the bracket `[H, X]` has `(k, l)` entry `(H k k - H l l) X k l`. -/
theorem coe_lie_apply_of_mem_slComplexRealDiagonal
    {H : slComplexReal n} (hH : H ∈ slComplexRealDiagonal n)
    (X : slComplexReal n) (k l : n) :
    ((⁅H, X⁆ : slComplexReal n) : Matrix n n ℂ) k l =
      ((((H : Matrix n n ℂ) k k).re - ((H : Matrix n n ℂ) l l).re : ℝ) : ℂ) *
        (X : Matrix n n ℂ) k l := by
  rw [LieSubalgebra.coe_bracket, Ring.lie_def, mul_sub_mul_apply_of_isDiag hH.1, Complex.ofReal_sub,
    ofReal_re_apply_self_of_mem_slComplexRealDiagonal hH,
    ofReal_re_apply_self_of_mem_slComplexRealDiagonal hH]

variable (n) in
/-- The functional `e_i - e_j : H ↦ H i i - H j j` on the real trace-zero diagonal matrices. Over
`𝔰𝔩_n(ℂ)` viewed as real it is a restricted root exactly when `i ≠ j`
(`TauCeti.mem_restrictedRoots_slComplexRealDiagonal_iff`). -/
@[expose] noncomputable def slComplexRestrictedRoot (i j : n) : Dual ℝ (slComplexRealDiagonal n) :=
  Complex.reLm ∘ₗ (entryLinearMap ℝ ℂ i i - entryLinearMap ℝ ℂ j j) ∘ₗ
    (slComplexReal n).incl.toLinearMap ∘ₗ (slComplexRealDiagonal n).subtype

@[simp]
theorem slComplexRestrictedRoot_apply (i j : n) (H : slComplexRealDiagonal n) :
    slComplexRestrictedRoot n i j H =
      (((H : slComplexReal n) : Matrix n n ℂ) i i).re -
        (((H : slComplexReal n) : Matrix n n ℂ) j j).re :=
  rfl

/-- `e_k - e_k = 0`. -/
@[simp]
theorem slComplexRestrictedRoot_self (k : n) : slComplexRestrictedRoot n k k = 0 :=
  LinearMap.ext fun H ↦ by simp

variable (n) in
/-- The element `E_kk - E_ll` of `𝔞`, used to separate the functionals `e_i - e_j`. -/
noncomputable def slComplexRealDiagonalSingle (k l : n) : slComplexRealDiagonal n :=
  ⟨⟨single k k 1 - single l l 1, (LieSubalgebra.mem_range_restrictScalarsIncl _ _ _).mpr <|
      LinearMap.mem_ker.mpr (by simp)⟩,
    ⟨fun i j hij ↦ by
        simp only [Matrix.sub_apply, Matrix.single_apply]; split_ifs <;> simp_all <;> grind,
      fun i ↦ by simp only [Matrix.sub_apply, Matrix.single_apply]; split_ifs <;> simp⟩⟩

theorem slComplexRestrictedRoot_slComplexRealDiagonalSingle (i j k l : n) :
    slComplexRestrictedRoot n i j (slComplexRealDiagonalSingle n k l) =
      ((if k = i then 1 else 0) - (if l = i then 1 else 0)) -
        ((if k = j then 1 else 0) - (if l = j then 1 else 0)) := by
  simp only [slComplexRestrictedRoot_apply, slComplexRealDiagonalSingle, Matrix.sub_apply,
    Matrix.single_apply]
  split_ifs <;> simp_all

/-- `e_i - e_j ≠ 0` for `i ≠ j`: it takes the value `2` at `E_ii - E_jj`. -/
theorem slComplexRestrictedRoot_ne_zero {i j : n} (hij : i ≠ j) :
    slComplexRestrictedRoot n i j ≠ 0 := by
  intro h
  have := LinearMap.congr_fun h (slComplexRealDiagonalSingle n i j)
  rw [slComplexRestrictedRoot_slComplexRealDiagonalSingle, LinearMap.zero_apply] at this
  simp [hij, hij.symm] at this

/-- `X ∈ 𝔤_μ` exactly when `(H k k - H l l - μ H) X k l = 0` for every `H ∈ 𝔞` and every entry. -/
theorem mem_restrictedRootSpace_slComplexRealDiagonal_iff {μ : Dual ℝ (slComplexRealDiagonal n)}
    {X : slComplexReal n} :
    X ∈ (slComplexRealDiagonal n).restrictedRootSpace μ ↔
      ∀ (H : slComplexRealDiagonal n) (k l : n),
        ((slComplexRestrictedRoot n k l H - μ H : ℝ) : ℂ) * (X : Matrix n n ℂ) k l = 0 := by
  rw [mem_restrictedRootSpace]
  refine forall_congr' fun H ↦ ⟨fun h k l ↦ ?_, fun h ↦ ?_⟩
  · have := congrFun (congrFun (congrArg Subtype.val h) k) l
    rw [coe_lie_apply_of_mem_slComplexRealDiagonal H.property] at this
    rw [SetLike.val_smul, Matrix.smul_apply, Complex.real_smul] at this
    rw [Complex.ofReal_sub, sub_mul, slComplexRestrictedRoot_apply, this, sub_self]
  · ext k l
    rw [coe_lie_apply_of_mem_slComplexRealDiagonal H.property, SetLike.val_smul, Matrix.smul_apply,
      Complex.real_smul, ← sub_eq_zero, ← sub_mul, ← Complex.ofReal_sub]
    exact h k l

/-- **The centralizer `𝔤_0` of `𝔞` is the diagonal matrices.** -/
theorem mem_restrictedRootSpace_zero_slComplexRealDiagonal_iff
    {X : slComplexReal n} :
    X ∈ (slComplexRealDiagonal n).restrictedRootSpace 0 ↔ (X : Matrix n n ℂ).IsDiag := by
  rw [mem_restrictedRootSpace_slComplexRealDiagonal_iff]
  refine ⟨fun h k l hkl ↦ ?_, fun h H k l ↦ ?_⟩
  · have := h (slComplexRealDiagonalSingle n k l) k l
    rw [LinearMap.zero_apply, sub_zero, slComplexRestrictedRoot_slComplexRealDiagonalSingle] at this
    simpa [hkl, Ne.symm hkl] using this
  · by_cases hkl : k = l
    · simp [hkl]
    · rw [h hkl, mul_zero]

/-- `𝔞` lies in the `-1`-eigenspace `𝔭` of `X ↦ -Xᴴ`: real diagonal matrices are Hermitian. -/
theorem slComplexRealDiagonal_le_cartanP :
    slComplexRealDiagonal n ≤
      (slComplexNegConjTranspose n).cartanP := fun X hX ↦ by
  rw [LieSubalgebra.mem_cartanP_restrictNegConjTranspose_iff]
  ext k l
  rw [conjTranspose_apply]
  by_cases hkl : k = l
  · subst hkl
    rw [← ofReal_re_apply_self_of_mem_slComplexRealDiagonal hX, RCLike.star_def,
      Complex.conj_ofReal]
  · rw [hX.1 hkl, hX.1 (Ne.symm hkl), star_zero]

/-- The bracket vanishes on `𝔞`. -/
theorem lie_eq_zero_of_mem_slComplexRealDiagonal
    {H H' : slComplexReal n}
    (hH : H ∈ slComplexRealDiagonal n) (hH' : H' ∈ slComplexRealDiagonal n) : ⁅H, H'⁆ = 0 :=
  (mem_restrictedRootSpace_zero.mp
    (mem_restrictedRootSpace_zero_slComplexRealDiagonal_iff.mpr hH'.1)) ⟨H, hH⟩

/-- **The real trace-zero diagonal matrices are a maximal abelian subspace of `𝔭`.** -/
theorem isMaximalAbelianInP_slComplexRealDiagonal :
    (slComplexNegConjTranspose n).IsMaximalAbelianInP
      (slComplexRealDiagonal n) := by
  refine LieEquiv.isMaximalAbelianInP_iff.mpr ⟨⟨slComplexRealDiagonal_le_cartanP,
    fun _ hX _ hY ↦ lie_eq_zero_of_mem_slComplexRealDiagonal hX hY⟩, fun 𝔟 h𝔟 hle Y hY ↦ ?_⟩
  have hdiag : (Y : Matrix n n ℂ).IsDiag :=
    mem_restrictedRootSpace_zero_slComplexRealDiagonal_iff.mp
      (mem_restrictedRootSpace_zero.mpr fun H ↦ h𝔟.2 _ (hle H.property) Y hY)
  refine ⟨hdiag, fun k ↦ ?_⟩
  have hherm := congrFun (congrFun
    ((LieSubalgebra.mem_cartanP_restrictNegConjTranspose_iff _ _).mp (h𝔟.1 hY)) k) k
  rw [conjTranspose_apply, RCLike.star_def] at hherm
  exact Complex.conj_eq_iff_im.mp hherm

/-- **`𝔪 = i𝔞`**: an element of the fixed subalgebra `𝔨` (the skew-Hermitian matrices) centralizes
`𝔞` exactly when it is `i` times an element of `𝔞`. -/
theorem mem_restrictedRootSpace_zero_inf_fixedSubalgebra_slComplexRealDiagonal_iff
    {X : slComplexReal n} :
    X ∈ (slComplexRealDiagonal n).restrictedRootSpace 0 ⊓
        (slComplexNegConjTranspose n).toLieHom.fixedSubalgebra.toSubmodule ↔
      ∃ H ∈ slComplexRealDiagonal n, (X : Matrix n n ℂ) = Complex.I • (H : Matrix n n ℂ) := by
  rw [Submodule.mem_inf, mem_restrictedRootSpace_zero_slComplexRealDiagonal_iff,
    LieSubalgebra.mem_toSubmodule, LieSubalgebra.mem_fixedSubalgebra_restrictNegConjTranspose_iff]
  constructor
  · rintro ⟨hdiag, hskew⟩
    have hmem : -Complex.I • (X : Matrix n n ℂ) ∈
        slComplexReal n := by
      exact (LieSubalgebra.mem_range_restrictScalarsIncl _ _ _).mpr ((SpecialLinear.sl n ℂ).smul_mem
        _ ((LieSubalgebra.mem_range_restrictScalarsIncl _ _ _).mp X.property))
    refine ⟨⟨_, hmem⟩, ⟨hdiag.smul _, fun k ↦ ?_⟩, ?_⟩
    · have := congrFun (congrFun hskew k) k
      rw [conjTranspose_apply, RCLike.star_def, Matrix.neg_apply] at this
      have hre : ((X : Matrix n n ℂ) k k).re = 0 := by
        have := congrArg Complex.re this
        rw [Complex.conj_re, Complex.neg_re] at this
        linarith
      simp [hre]
    · rw [smul_smul]
      simp
  · rintro ⟨H, hH, hX⟩
    refine ⟨hX ▸ hH.1.smul _, ?_⟩
    rw [hX, conjTranspose_smul,
      (LieSubalgebra.mem_cartanP_restrictNegConjTranspose_iff _ _).mp
        (slComplexRealDiagonal_le_cartanP hH)]
    simp

/-- The matrix unit `E_ij` (`i ≠ j`) lies in `𝔰𝔩_n(ℂ)` viewed as real. -/
theorem single_mem_slComplexReal {i j : n} (hij : i ≠ j) (c : ℂ) :
    single i j c ∈ slComplexReal n :=
  (LieSubalgebra.mem_range_restrictScalarsIncl _ _ _).mpr <|
    LinearMap.mem_ker.mpr (by simp [hij])

/-- `e_k - e_l = e_i - e_j` with `i ≠ j` forces `(k, l) = (i, j)`. -/
theorem eq_and_eq_of_slComplexRestrictedRoot_eq {i j k l : n} (hij : i ≠ j)
    (h : ∀ H, slComplexRestrictedRoot n k l H = slComplexRestrictedRoot n i j H) :
    k = i ∧ l = j := by
  have := h (slComplexRealDiagonalSingle n i j)
  rw [slComplexRestrictedRoot_slComplexRealDiagonalSingle,
    slComplexRestrictedRoot_slComplexRealDiagonalSingle] at this
  simp only [hij, Ne.symm hij, ↓reduceIte] at this
  split_ifs at this <;> simp_all <;> norm_num at this

/-- **The restricted root space of `e_i - e_j` consists of the matrices supported at `(i, j)`.** -/
theorem mem_restrictedRootSpace_slComplexRestrictedRoot_iff {i j : n} (hij : i ≠ j)
    {X : slComplexReal n} :
    X ∈ (slComplexRealDiagonal n).restrictedRootSpace (slComplexRestrictedRoot n i j) ↔
      (X : Matrix n n ℂ) = single i j ((X : Matrix n n ℂ) i j) := by
  rw [mem_restrictedRootSpace_slComplexRealDiagonal_iff]
  constructor
  · intro h
    ext k l
    rw [single_apply]
    split_ifs with hkl
    · rw [hkl.1, hkl.2]
    · by_contra hne
      refine hkl ((eq_and_eq_of_slComplexRestrictedRoot_eq hij fun H ↦ ?_).imp Eq.symm Eq.symm)
      have := (mul_eq_zero.mp (h H k l)).resolve_right hne
      rw [Complex.ofReal_eq_zero, sub_eq_zero] at this
      exact this
  · intro h H k l
    rw [h, single_apply]
    split_ifs with hkl
    · rw [hkl.1, hkl.2, sub_self, Complex.ofReal_zero, zero_mul]
    · rw [mul_zero]

/-- **The restricted roots of `𝔰𝔩_n(ℂ)` viewed as real are the `e_i - e_j` with `i ≠ j`.** -/
theorem mem_restrictedRoots_slComplexRealDiagonal_iff {μ : Dual ℝ (slComplexRealDiagonal n)} :
    μ ∈ (slComplexRealDiagonal n).restrictedRoots ↔
      ∃ i j, i ≠ j ∧ μ = slComplexRestrictedRoot n i j := by
  rw [mem_restrictedRoots]
  constructor
  · rintro ⟨hμ, hne⟩
    obtain ⟨X, hX, hX0⟩ := (Submodule.ne_bot_iff _).mp hne
    obtain ⟨k, l, hkl⟩ : ∃ k l, (X : Matrix n n ℂ) k l ≠ 0 := by
      by_contra! h
      exact hX0 (Subtype.ext (Matrix.ext h))
    have hroot : μ = slComplexRestrictedRoot n k l := LinearMap.ext fun H ↦ by
      have := (mul_eq_zero.mp
        (mem_restrictedRootSpace_slComplexRealDiagonal_iff.mp hX H k l)).resolve_right hkl
      rw [Complex.ofReal_eq_zero, sub_eq_zero] at this
      exact this.symm
    refine ⟨k, l, fun h ↦ hμ ?_, hroot⟩
    rw [hroot, h, slComplexRestrictedRoot_self]
  · rintro ⟨i, j, hij, rfl⟩
    refine ⟨slComplexRestrictedRoot_ne_zero hij, (Submodule.ne_bot_iff _).mpr
      ⟨⟨single i j 1, single_mem_slComplexReal hij 1⟩, ?_, fun h ↦ ?_⟩⟩
    · rw [mem_restrictedRootSpace_slComplexRestrictedRoot_iff hij]
      simp
    · have := congrFun (congrFun (congrArg Subtype.val h) i) j
      simp at this

/-- The restricted root space of `e_i - e_j` is linearly equivalent to `ℂ`, through the `(i, j)`
entry. -/
noncomputable def restrictedRootSpaceSlComplexEquiv {i j : n} (hij : i ≠ j) :
    (slComplexRealDiagonal n).restrictedRootSpace (slComplexRestrictedRoot n i j) ≃ₗ[ℝ] ℂ where
  toFun X := ((X : slComplexReal n) : Matrix n n ℂ) i j
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun c := ⟨⟨single i j c, single_mem_slComplexReal hij c⟩,
    (mem_restrictedRootSpace_slComplexRestrictedRoot_iff hij).mpr (by simp)⟩
  left_inv X := Subtype.ext <| Subtype.ext
    ((mem_restrictedRootSpace_slComplexRestrictedRoot_iff hij).mp X.property).symm
  right_inv c := by simp

/-- **Multiplicity two**: the restricted root space of `e_i - e_j` has real dimension `2`. -/
theorem finrank_restrictedRootSpace_slComplexRestrictedRoot {i j : n} (hij : i ≠ j) :
    finrank ℝ ((slComplexRealDiagonal n).restrictedRootSpace (slComplexRestrictedRoot n i j)) = 2 :=
  (restrictedRootSpaceSlComplexEquiv hij).finrank_eq.trans Complex.finrank_real_complex

end TauCeti

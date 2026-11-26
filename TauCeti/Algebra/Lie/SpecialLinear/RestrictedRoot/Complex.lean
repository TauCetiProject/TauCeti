/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.CartanInvolution.RestrictScalars
public import TauCeti.Algebra.Lie.CartanInvolution.RestrictedRoot.Basic
public import TauCeti.Algebra.Lie.GeneralLinear.DiagonalCartan
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.LinearAlgebra.Matrix.IsDiag

/-!
# Restricted roots of `𝔰𝔩_n(ℂ)` viewed as a real Lie algebra

On `𝔰𝔩_n(ℂ)` viewed as a real Lie algebra (`TauCeti.slComplexReal`), with the Cartan involution
`θ X = -Xᴴ` (`TauCeti.isCartanInvolution_slComplexNegConjTranspose`), the real trace-zero
diagonal matrices `𝔞` (`TauCeti.slComplexRealDiagonal`) form a maximal abelian subspace of the
`-1`-eigenspace `𝔭` (the Hermitian matrices). For `H ∈ 𝔞` the bracket `[H, X]` has `(k, l)` entry
`(H k k - H l l) X k l`, so:

* the centralizer `𝔤_0` of `𝔞` is the complex trace-zero diagonal matrices, and
  `𝔪 = 𝔤_0 ∩ 𝔨` is `i𝔞`, the imaginary trace-zero diagonal matrices;
* the restricted roots are the functionals `e_i - e_j : H ↦ H i i - H j j` for `i ≠ j`;
* the restricted root space of `e_i - e_j` is the complex line `ℂ E_ij`, of real dimension `2`.

So the restricted root system of `𝔰𝔩_n(ℂ)` as a real Lie algebra has the same roots as that of
`𝔰𝔩_n(ℝ)` (`TauCeti.mem_restrictedRoots_specialLinearDiagonal_iff`), with all multiplicities `2`
and `𝔪 = i𝔞`.

## Main definitions

* `TauCeti.slComplexRealDiagonal`: the real trace-zero diagonal matrices in `𝔰𝔩_n(ℂ)`.
* `TauCeti.slComplexRealDiagonalSubalgebra`: the same, as a Lie subalgebra.
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

variable {n : Type*} [Fintype n] [DecidableEq n]

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

@[simp]
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
  rw [LieSubalgebra.coe_bracket,
    lie_apply_of_mem_diagonalCartan (mem_diagonalCartan_iff_isDiag.mpr hH.1), Complex.ofReal_sub,
    ofReal_re_apply_self_of_mem_slComplexRealDiagonal hH,
    ofReal_re_apply_self_of_mem_slComplexRealDiagonal hH]

variable (n) in
/-- The functional `e_i - e_j : H ↦ H i i - H j j` on the real trace-zero diagonal matrices. Over
`𝔰𝔩_n(ℂ)` viewed as real it is a restricted root exactly when `i ≠ j`
(`TauCeti.mem_restrictedRoots_slComplexRealDiagonal_iff`). -/
noncomputable def slComplexRestrictedRoot (i j : n) : Dual ℝ (slComplexRealDiagonal n) :=
  Complex.reLm ∘ₗ (entryLinearMap ℝ ℂ i i - entryLinearMap ℝ ℂ j j) ∘ₗ
    (slComplexReal n).incl.toLinearMap ∘ₗ (slComplexRealDiagonal n).subtype

@[simp]
theorem slComplexRestrictedRoot_apply (i j : n) (H : slComplexRealDiagonal n) :
    slComplexRestrictedRoot n i j H =
      (((H : slComplexReal n) : Matrix n n ℂ) i i).re -
        (((H : slComplexReal n) : Matrix n n ℂ) j j).re :=
  (rfl)

/-- `e_k - e_k = 0`. -/
@[simp]
theorem slComplexRestrictedRoot_self (k : n) : slComplexRestrictedRoot n k k = 0 :=
  LinearMap.ext fun H ↦ by simp

variable (n) in
/-- The element `E_kk - E_ll` of `𝔞`, used to separate the functionals `e_i - e_j`. -/
noncomputable def slComplexRealDiagonalSingleSubSingle (k l : n) : slComplexRealDiagonal n :=
  ⟨⟨single k k 1 - single l l 1, mem_slComplexReal_iff.mpr (by simp)⟩,
    ⟨fun i j hij ↦ by
        simp only [Matrix.sub_apply, Matrix.single_apply]; split_ifs <;> grind,
      fun i ↦ by simp only [Matrix.sub_apply, Matrix.single_apply]; split_ifs <;> simp⟩⟩

@[simp]
theorem coe_slComplexRealDiagonalSingleSubSingle (k l : n) :
    (((slComplexRealDiagonalSingleSubSingle n k l : slComplexRealDiagonal n) : slComplexReal n) :
      Matrix n n ℂ) = single k k 1 - single l l 1 :=
  (rfl)

theorem slComplexRestrictedRoot_slComplexRealDiagonalSingleSubSingle (i j k l : n) :
    slComplexRestrictedRoot n i j (slComplexRealDiagonalSingleSubSingle n k l) =
      ((if k = i then 1 else 0) - (if l = i then 1 else 0)) -
        ((if k = j then 1 else 0) - (if l = j then 1 else 0)) := by
  simp only [slComplexRestrictedRoot_apply, coe_slComplexRealDiagonalSingleSubSingle,
    Matrix.sub_apply, Matrix.single_apply]
  split_ifs <;> simp_all

/-- `e_i - e_j ≠ 0` for `i ≠ j`: it takes the value `2` at `E_ii - E_jj`. -/
theorem slComplexRestrictedRoot_ne_zero {i j : n} (hij : i ≠ j) :
    slComplexRestrictedRoot n i j ≠ 0 := by
  intro h
  have := LinearMap.congr_fun h (slComplexRealDiagonalSingleSubSingle n i j)
  rw [slComplexRestrictedRoot_slComplexRealDiagonalSingleSubSingle, LinearMap.zero_apply] at this
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
    simp only [slComplexRestrictedRoot_apply, Complex.ofReal_sub, SetLike.val_smul,
      Matrix.smul_apply, Complex.real_smul] at this ⊢
    linear_combination this
  · ext k l
    have := h k l
    rw [coe_lie_apply_of_mem_slComplexRealDiagonal H.property]
    simp only [slComplexRestrictedRoot_apply, Complex.ofReal_sub, SetLike.val_smul,
      Matrix.smul_apply, Complex.real_smul] at this ⊢
    linear_combination this

/-- **The centralizer `𝔤_0` of `𝔞` is the diagonal matrices.** -/
theorem mem_restrictedRootSpace_zero_slComplexRealDiagonal_iff
    {X : slComplexReal n} :
    X ∈ (slComplexRealDiagonal n).restrictedRootSpace 0 ↔ (X : Matrix n n ℂ).IsDiag := by
  rw [mem_restrictedRootSpace_slComplexRealDiagonal_iff]
  refine ⟨fun h k l hkl ↦ ?_, fun h H k l ↦ ?_⟩
  · have := h (slComplexRealDiagonalSingleSubSingle n k l) k l
    rw [LinearMap.zero_apply, sub_zero,
      slComplexRestrictedRoot_slComplexRealDiagonalSingleSubSingle] at this
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
  by_cases hkl : k = l
  · subst hkl
    simp [Complex.conj_eq_iff_im, hX.2 k]
  · simp [hX.1 hkl, hX.1 (Ne.symm hkl)]

/-- **The real trace-zero diagonal matrices are a maximal abelian subspace of `𝔭`.** -/
theorem isMaximalAbelianInP_slComplexRealDiagonal :
    (slComplexNegConjTranspose n).IsMaximalAbelianInP
      (slComplexRealDiagonal n) := by
  refine LieEquiv.isMaximalAbelianInP_iff.mpr ⟨⟨slComplexRealDiagonal_le_cartanP,
    fun _ hX _ hY ↦ Subtype.ext (lie_eq_zero_of_isDiag hX.1 hY.1)⟩, fun 𝔟 h𝔟 hle Y hY ↦ ?_⟩
  have hdiag : (Y : Matrix n n ℂ).IsDiag :=
    mem_restrictedRootSpace_zero_slComplexRealDiagonal_iff.mp
      (mem_restrictedRootSpace_zero.mpr fun H ↦ h𝔟.2 _ (hle H.property) Y hY)
  refine ⟨hdiag, fun k ↦ ?_⟩
  simpa [Complex.conj_eq_iff_im] using congrFun (congrFun
    ((LieSubalgebra.mem_cartanP_restrictNegConjTranspose_iff _ _).mp (h𝔟.1 hY)) k) k

variable (n) in
/-- The real trace-zero diagonal matrices in `𝔰𝔩_n(ℂ)` viewed as real, as a Lie subalgebra (it
is abelian). Its underlying subspace is `TauCeti.slComplexRealDiagonal`
(`TauCeti.slComplexRealDiagonalSubalgebra_toSubmodule`). -/
def slComplexRealDiagonalSubalgebra : LieSubalgebra ℝ (slComplexReal n) :=
  { slComplexRealDiagonal n with
    lie_mem' := fun hX hY ↦ by
      rw [isMaximalAbelianInP_slComplexRealDiagonal.lie_eq_zero hX hY]
      exact (slComplexRealDiagonal n).zero_mem }

variable (n) in
/-- The Lie subalgebra `TauCeti.slComplexRealDiagonalSubalgebra` has underlying subspace
`TauCeti.slComplexRealDiagonal`. -/
@[simp]
theorem slComplexRealDiagonalSubalgebra_toSubmodule :
    (slComplexRealDiagonalSubalgebra n).toSubmodule = slComplexRealDiagonal n :=
  (rfl)

/-- Membership in `TauCeti.slComplexRealDiagonalSubalgebra` is membership in its underlying
subspace `TauCeti.slComplexRealDiagonal`. -/
@[simp]
theorem mem_slComplexRealDiagonalSubalgebra {X : slComplexReal n} :
    X ∈ slComplexRealDiagonalSubalgebra n ↔ X ∈ slComplexRealDiagonal n :=
  Iff.rfl

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
    have hmem : -Complex.I • (X : Matrix n n ℂ) ∈ slComplexReal n :=
      mem_slComplexReal_iff.mpr <| by
        rw [trace_smul, mem_slComplexReal_iff.mp X.property, smul_zero]
    refine ⟨⟨_, hmem⟩, ⟨hdiag.smul _, fun k ↦ ?_⟩, ?_⟩
    · have hre : ((X : Matrix n n ℂ) k k).re = 0 := by
        simpa [CharZero.eq_neg_self_iff] using congrArg Complex.re (congrFun (congrFun hskew k) k)
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
  mem_slComplexReal_iff.mpr (by simp [hij])

/-- The functionals `e_k - e_l` and `e_i - e_j` with `i ≠ j` coincide exactly when
`(k, l) = (i, j)`. -/
@[simp]
theorem slComplexRestrictedRoot_inj {i j k l : n} (hij : i ≠ j) :
    slComplexRestrictedRoot n k l = slComplexRestrictedRoot n i j ↔ k = i ∧ l = j := by
  refine ⟨fun h ↦ ?_, fun ⟨hki, hlj⟩ ↦ hki ▸ hlj ▸ rfl⟩
  have := LinearMap.congr_fun h (slComplexRealDiagonalSingleSubSingle n i j)
  rw [slComplexRestrictedRoot_slComplexRealDiagonalSingleSubSingle,
    slComplexRestrictedRoot_slComplexRealDiagonalSingleSubSingle] at this
  simp only [hij, Ne.symm hij, ↓reduceIte] at this
  grind

/-- A nonzero `(k, l)` entry of `X ∈ 𝔤_μ` forces `μ = e_k - e_l`. -/
theorem eq_slComplexRestrictedRoot_of_mem_restrictedRootSpace
    {μ : Dual ℝ (slComplexRealDiagonal n)} {X : slComplexReal n}
    (hX : X ∈ (slComplexRealDiagonal n).restrictedRootSpace μ) {k l : n}
    (hkl : (X : Matrix n n ℂ) k l ≠ 0) : μ = slComplexRestrictedRoot n k l :=
  LinearMap.ext fun H ↦ by
    have := (mul_eq_zero.mp
      (mem_restrictedRootSpace_slComplexRealDiagonal_iff.mp hX H k l)).resolve_right hkl
    rw [Complex.ofReal_eq_zero, sub_eq_zero] at this
    exact this.symm

/-- **The restricted root space of `e_i - e_j` consists of the matrices supported at `(i, j)`.** -/
theorem mem_restrictedRootSpace_slComplexRestrictedRoot_iff {i j : n} (hij : i ≠ j)
    {X : slComplexReal n} :
    X ∈ (slComplexRealDiagonal n).restrictedRootSpace (slComplexRestrictedRoot n i j) ↔
      (X : Matrix n n ℂ) = single i j ((X : Matrix n n ℂ) i j) := by
  constructor
  · intro h
    ext k l
    rw [single_apply]
    split_ifs with hkl
    · rw [hkl.1, hkl.2]
    · by_contra hne
      exact hkl (((slComplexRestrictedRoot_inj hij).mp
        (eq_slComplexRestrictedRoot_of_mem_restrictedRootSpace h hne).symm).imp Eq.symm Eq.symm)
  · intro h
    rw [mem_restrictedRootSpace_slComplexRealDiagonal_iff]
    intro H k l
    rw [h, single_apply]
    split_ifs with hkl
    · simp [hkl.1, hkl.2]
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
    have hroot := eq_slComplexRestrictedRoot_of_mem_restrictedRootSpace hX hkl
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

@[simp]
theorem restrictedRootSpaceSlComplexEquiv_apply {i j : n} (hij : i ≠ j)
    (X : (slComplexRealDiagonal n).restrictedRootSpace (slComplexRestrictedRoot n i j)) :
    restrictedRootSpaceSlComplexEquiv hij X = ((X : slComplexReal n) : Matrix n n ℂ) i j :=
  (rfl)

@[simp]
theorem coe_restrictedRootSpaceSlComplexEquiv_symm_apply {i j : n} (hij : i ≠ j) (c : ℂ) :
    (((restrictedRootSpaceSlComplexEquiv hij).symm c : slComplexReal n) : Matrix n n ℂ) =
      single i j c :=
  (rfl)

/-- **Multiplicity two**: the restricted root space of `e_i - e_j` has real dimension `2`. -/
theorem finrank_restrictedRootSpace_slComplexRestrictedRoot {i j : n} (hij : i ≠ j) :
    finrank ℝ ((slComplexRealDiagonal n).restrictedRootSpace (slComplexRestrictedRoot n i j)) = 2 :=
  (restrictedRootSpaceSlComplexEquiv hij).finrank_eq.trans Complex.finrank_real_complex

end TauCeti

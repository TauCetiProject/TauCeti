/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.CartanInvolution.RestrictedRoot.Split
public import TauCeti.Algebra.Lie.Symplectic.Killing
public import TauCeti.Algebra.Lie.GeneralLinear.DiagonalCartan

/-!
# The real symplectic Lie algebra is split

On the symplectic Lie algebra `𝔰𝔭(2n, K)` = `LieAlgebra.Symplectic.sp l K` over an ordered field,
with the Cartan involution `θ X = -Xᵀ` (`LieAlgebra.Symplectic.cartanInvolution`), the diagonal
matrices `𝔞 = {diag(D, -D)}` (`LieAlgebra.Symplectic.diagonalSubalgebra`) form a maximal abelian
subspace of the `-1`-eigenspace `𝔭` (the symmetric matrices). For `H ∈ 𝔞` the bracket `[H, X]` has
`(a, b)` entry `(H a a - H b b) X a b`, and the elements
`H_i = E_(i, i) - E_(n + i, n + i)` of `𝔞` separate the indices of `l ⊕ l`, so:

* the centralizer `𝔤_0` of `𝔞` is `𝔞` itself, and `𝔪 = 𝔤_0 ∩ 𝔨 = 0`;
* `𝔞` is a Cartan subalgebra of `𝔰𝔭(2n, K)`: **`𝔰𝔭(2n, ℝ)` is split**, in the sense of
  `LieEquiv.IsMaximalAbelianInP.isCartanSubalgebra_iff`.

The centralizer computation, the maximality of `𝔞` and `𝔪 = 0` hold over every field of
characteristic other than two; only the Cartan subalgebra criterion uses the order.

## Main results

* `LieAlgebra.Symplectic.diagonalSubalgebra`: the diagonal matrices in `sp l R`.
* `LieAlgebra.Symplectic.restrictedRootSpace_zero_diagonalSubalgebra`: `𝔤_0 = 𝔞`.
* `LieAlgebra.Symplectic.isMaximalAbelianInP_diagonalSubalgebra`: `𝔞` is maximal abelian in `𝔭`.
* `LieAlgebra.Symplectic.restrictedRootSpace_zero_inf_fixedSubalgebra_diagonalSubalgebra`:
  `𝔪 = 0`.
* `LieAlgebra.Symplectic.isCartanSubalgebra_diagonalSubalgebra`: `𝔞` is a Cartan subalgebra.

## References

* A. W. Knapp, *Lie Groups Beyond an Introduction*, 2nd ed., Chapter VI, §§5–6.
-/

public section

open LieAlgebra Matrix Module Submodule

attribute [local instance 100] LieRing.ofAssociativeRing

namespace LieAlgebra.Symplectic

variable {l : Type*} [Fintype l] [DecidableEq l]

section CommRing

variable (l) (R : Type*) [CommRing R]

/-- The diagonal matrices in the symplectic Lie algebra `sp l R`, that is, the matrices
`diag(D, -D)`: the diagonal matrices of `gl` (`TauCeti.diagonalCartan`) pulled back along the
inclusion. They form an abelian Lie subalgebra. -/
def diagonalSubalgebra : LieSubalgebra R (sp l R) :=
  (TauCeti.diagonalCartan R (l ⊕ l)).comap (sp l R).incl

variable {l R}

/-- Membership in `LieAlgebra.Symplectic.diagonalSubalgebra`. -/
@[simp]
theorem mem_diagonalSubalgebra {X : sp l R} :
    X ∈ diagonalSubalgebra l R ↔ (X : Matrix (l ⊕ l) (l ⊕ l) R).IsDiag :=
  TauCeti.mem_diagonalCartan_iff_isDiag

/-- Diagonal symplectic Lie matrices commute. -/
theorem lie_eq_zero_of_mem_diagonalSubalgebra {X Y : sp l R} (hX : X ∈ diagonalSubalgebra l R)
    (hY : Y ∈ diagonalSubalgebra l R) : ⁅X, Y⁆ = 0 :=
  Subtype.ext <| by
    rw [LieSubalgebra.coe_bracket, ZeroMemClass.coe_zero]
    exact TauCeti.lie_eq_zero_of_isDiag (mem_diagonalSubalgebra.mp hX)
      (mem_diagonalSubalgebra.mp hY)

instance : IsLieAbelian (diagonalSubalgebra l R) where
  trivial X Y := Subtype.ext (lie_eq_zero_of_mem_diagonalSubalgebra X.property Y.property)

/-- The entries of `[H, X]` for a diagonal `H`: `[H, X] a b = (H a a - H b b) X a b`. -/
theorem lie_apply_of_mem_diagonalSubalgebra {H : sp l R} (hH : H ∈ diagonalSubalgebra l R)
    (X : sp l R) (a b : l ⊕ l) :
    (⁅H, X⁆ : sp l R).val a b =
      ((H : Matrix (l ⊕ l) (l ⊕ l) R) a a - (H : Matrix (l ⊕ l) (l ⊕ l) R) b b) *
        (X : Matrix (l ⊕ l) (l ⊕ l) R) a b := by
  rw [LieSubalgebra.coe_bracket]
  exact TauCeti.lie_apply_of_mem_diagonalCartan
    (TauCeti.mem_diagonalCartan_iff_isDiag.mpr (mem_diagonalSubalgebra.mp hH)) _ a b

/-- The element `H_i = E_(i, i) - E_(n + i, n + i)` of `𝔞`. -/
def diagonalSubalgebraElement (i : l) : diagonalSubalgebra l R :=
  ⟨⟨single (.inl i) (.inl i) 1 - single (.inr i) (.inr i) 1,
    single_inl_inl_sub_single_inr_inr_mem_sp i i⟩, by
      simp only [mem_diagonalSubalgebra]
      intro a b hab
      simp only [Matrix.sub_apply, single_apply]
      grind⟩

/-- The matrix of `H_i = E_(i, i) - E_(n + i, n + i)`. -/
@[simp]
theorem coe_diagonalSubalgebraElement (i : l) :
    ((diagonalSubalgebraElement (R := R) i : sp l R) : Matrix (l ⊕ l) (l ⊕ l) R) =
      single (.inl i) (.inl i) 1 - single (.inr i) (.inr i) 1 :=
  (rfl)

/-- The diagonal entries of `H_i = E_(i, i) - E_(n + i, n + i)`. -/
theorem diagonalSubalgebraElement_apply (i : l) (a : l ⊕ l) :
    (((diagonalSubalgebraElement (R := R) i : sp l R) : Matrix (l ⊕ l) (l ⊕ l) R) a a) =
      (if a = .inl i then 1 else 0) - if a = .inr i then 1 else 0 := by
  simp [diagonalSubalgebraElement, Matrix.sub_apply, single_apply, eq_comm]

/-- `𝔞` lies in the `-1`-eigenspace `𝔭` of `θ X = -Xᵀ`: diagonal matrices are symmetric. -/
theorem diagonalSubalgebra_le_cartanP :
    (diagonalSubalgebra l R).toSubmodule ≤ (cartanInvolution l R).cartanP := fun X hX ↦
  LieEquiv.mem_cartanP.mpr ((cartanInvolution_eq_neg_iff X).mpr
    (mem_diagonalSubalgebra.mp hX).isSymm.eq)

end CommRing

section Field

variable {K : Type*} [Field K] [NeZero (2 : K)]

/-- The elements `H_i = E_(i, i) - E_(n + i, n + i)` of `𝔞` separate the indices of `l ⊕ l`:
for `a ≠ b` some `H_i` has different diagonal entries at `a` and `b`. -/
theorem exists_diagonalSubalgebraElement_apply_ne {a b : l ⊕ l} (hab : a ≠ b) :
    ∃ i : l, ((diagonalSubalgebraElement (R := K) i : sp l K) : Matrix (l ⊕ l) (l ⊕ l) K) a a ≠
      ((diagonalSubalgebraElement (R := K) i : sp l K) : Matrix (l ⊕ l) (l ⊕ l) K) b b := by
  have h2 : (1 : K) ≠ -1 := fun h ↦ two_ne_zero (α := K) (by linear_combination h)
  rcases a with i | i
  · refine ⟨i, ?_⟩
    rcases b with j | j
    · simp_all [diagonalSubalgebraElement_apply, eq_comm]
    · by_cases hij : j = i
      · subst hij; simpa [diagonalSubalgebraElement_apply] using h2
      · simp [diagonalSubalgebraElement_apply, hij]
  · refine ⟨i, ?_⟩
    rcases b with j | j
    · by_cases hij : j = i
      · subst hij; simpa [diagonalSubalgebraElement_apply] using h2.symm
      · simp [diagonalSubalgebraElement_apply, hij]
    · simp_all [diagonalSubalgebraElement_apply, eq_comm]

/-- **The centralizer `𝔤_0` of `𝔞` in `𝔰𝔭(2n, K)` is `𝔞` itself**: an element commuting with
every `H_i` is diagonal. -/
theorem restrictedRootSpace_zero_diagonalSubalgebra :
    (diagonalSubalgebra l K).toSubmodule.restrictedRootSpace 0 =
      (diagonalSubalgebra l K).toSubmodule := by
  refine le_antisymm (fun X hX ↦ ?_) (Submodule.le_restrictedRootSpace_zero
    fun _ hX _ hY ↦ lie_eq_zero_of_mem_diagonalSubalgebra hX hY)
  rw [mem_restrictedRootSpace_zero] at hX
  rw [LieSubalgebra.mem_toSubmodule, mem_diagonalSubalgebra]
  intro a b hab
  obtain ⟨i, hi⟩ := exists_diagonalSubalgebraElement_apply_ne (K := K) hab
  have h := congrArg (fun Y : sp l K ↦ (Y : Matrix (l ⊕ l) (l ⊕ l) K) a b)
    (hX ⟨_, (diagonalSubalgebraElement i).property⟩)
  simp only [ZeroMemClass.coe_zero, Matrix.zero_apply] at h
  rw [lie_apply_of_mem_diagonalSubalgebra (diagonalSubalgebraElement i).property] at h
  exact (mul_eq_zero.mp h).resolve_left (sub_ne_zero.mpr hi)

/-- **The diagonal matrices are a maximal abelian subspace of `𝔭`** in `𝔰𝔭(2n, K)`, over any field
of characteristic other than two. -/
theorem isMaximalAbelianInP_diagonalSubalgebra :
    (cartanInvolution l K).IsMaximalAbelianInP (diagonalSubalgebra l K).toSubmodule := by
  refine LieEquiv.isMaximalAbelianInP_iff.mpr ⟨⟨diagonalSubalgebra_le_cartanP,
    fun _ hX _ hY ↦ lie_eq_zero_of_mem_diagonalSubalgebra hX hY⟩, fun 𝔟 h𝔟 hle Y hY ↦ ?_⟩
  rw [← restrictedRootSpace_zero_diagonalSubalgebra, mem_restrictedRootSpace_zero]
  exact fun H ↦ h𝔟.2 _ (hle H.property) Y hY

/-- **`𝔪 = 0`** for `𝔰𝔭(2n, K)`: no nonzero element of the fixed subalgebra `𝔨` (the
skew-symmetric matrices) centralizes `𝔞`. -/
theorem restrictedRootSpace_zero_inf_fixedSubalgebra_diagonalSubalgebra :
    (diagonalSubalgebra l K).toSubmodule.restrictedRootSpace 0 ⊓
      (cartanInvolution l K).toLieHom.fixedSubalgebra.toSubmodule = ⊥ := by
  rw [restrictedRootSpace_zero_diagonalSubalgebra, ← disjoint_iff]
  exact ((cartanInvolution l K).isCompl_fixedSubalgebra_cartanP two_ne_zero.isUnit
    cartanInvolution_cartanInvolution).disjoint.symm.mono_left
      diagonalSubalgebra_le_cartanP

end Field

section OrderedField

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- **`𝔰𝔭(2n, K)` is split**: the diagonal matrices, maximal abelian in `𝔭` for `θ X = -Xᵀ`, form
a Cartan subalgebra, since `𝔪 = 0`. -/
theorem isCartanSubalgebra_diagonalSubalgebra : (diagonalSubalgebra l K).IsCartanSubalgebra :=
  (isMaximalAbelianInP_diagonalSubalgebra.isCartanSubalgebra_iff
    isCartanInvolution_cartanInvolution).mpr
    restrictedRootSpace_zero_inf_fixedSubalgebra_diagonalSubalgebra

end OrderedField

end LieAlgebra.Symplectic

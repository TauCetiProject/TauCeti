/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.SymplecticGroup

/-!
# The block embedding of a symplectic group in the next one

The standard symplectic space `R^{2(n+1)}`, with coordinates indexed by `Fin (n + 1) ⊕ Fin (n + 1)`
and form `Matrix.J`, is the orthogonal direct sum of the standard symplectic space `R^{2n}` on
the coordinates `(inl i, inr i)` with `i < n` and the hyperbolic plane spanned by the last pair of
coordinates `(inl (last n), inr (last n))`.  A symplectic matrix of size `2n` therefore becomes one
of size `2(n+1)` by acting on the first summand and fixing the plane pointwise.  This file builds
that **block inclusion** `TauCeti.symplecticBlockSucc : Sp(2n, R) →* Sp(2(n+1), R)`, the step of the
chain `Sp(2, R) ⊂ Sp(4, R) ⊂ ⋯` along which representations of the symplectic groups are
restricted; it is the symplectic counterpart of `TauCeti.orthogonalBlockSucc`.

The splitting of the coordinates is the equivalence `TauCeti.finSuccSumFinSuccEquiv` of
`Fin (n + 1) ⊕ Fin (n + 1)` with `(Fin n ⊕ Fin n) ⊕ (Fin 1 ⊕ Fin 1)`.  Read through it,
`Matrix.J` is the block-diagonal matrix with blocks the `Matrix.J` of the two summands
(`TauCeti.fromBlocks_J_submatrix_finSuccSumFinSuccEquiv`), and the extension `Matrix.sumBlockSucc M`
of a matrix `M` is the block-diagonal matrix with blocks `M` and `1`.

The image of the inclusion is exactly the pointwise stabilizer of the last hyperbolic plane
(`TauCeti.exists_symplecticBlockSucc_eq_iff_mulVec_single`).  As for the orthogonal group, the form
does real work here: fixing the two last basis vectors says only that the two last *columns* of the
matrix are those basis vectors, and it takes `Aᵀ * J * A = J` to read off that the two last *rows*
are too.

## Main definitions

* `TauCeti.finSuccSumFinSuccEquiv`: the splitting of the coordinates of `R^{2(n+1)}` into those of
  `R^{2n}` and those of the last hyperbolic plane.
* `Matrix.sumBlockSucc`: the extension of a matrix indexed by `Fin n ⊕ Fin n` by the identity on
  the last hyperbolic plane.
* `TauCeti.symplecticBlockSucc`: the induced group homomorphism
  `Matrix.symplecticGroup (Fin n) R →* Matrix.symplecticGroup (Fin (n + 1)) R`.

## Main results

* `TauCeti.fromBlocks_J_submatrix_finSuccSumFinSuccEquiv`: the standard symplectic form of
  `R^{2(n+1)}` is the orthogonal sum of those of `R^{2n}` and of the last hyperbolic plane.
* `Matrix.sumBlockSucc_mem_symplecticGroup_iff`: the extension of a matrix is symplectic exactly
  when the matrix is.
* `TauCeti.symplecticBlockSucc_injective`: the block inclusion is injective.
* `TauCeti.exists_symplecticBlockSucc_eq_iff_mulVec_single`: a symplectic matrix of size
  `2(n+1)` is an extension exactly when it fixes the two last basis vectors.
* `Matrix.trace_sumBlockSucc`: extending a matrix adds `2` to its trace.
-/

public section

universe u

open Matrix

namespace TauCeti

variable (n : ℕ)

/-! ### Splitting the coordinates -/

/-- **The splitting of the coordinates of `R^{2(n+1)}`**: an index `inl i` or `inr i` with
`i < n` is an index of `R^{2n}`, and the two indices `inl (last n)` and `inr (last n)` are those of
the last hyperbolic plane, indexed by `Fin 1 ⊕ Fin 1`. -/
def finSuccSumFinSuccEquiv : Fin (n + 1) ⊕ Fin (n + 1) ≃ (Fin n ⊕ Fin n) ⊕ (Fin 1 ⊕ Fin 1) :=
  (Equiv.sumCongr finSumFinEquiv.symm finSumFinEquiv.symm).trans
    (Equiv.sumSumSumComm (Fin n) (Fin 1) (Fin n) (Fin 1))

@[simp]
theorem finSuccSumFinSuccEquiv_inl_castSucc (i : Fin n) :
    finSuccSumFinSuccEquiv n (Sum.inl i.castSucc) = Sum.inl (Sum.inl i) := by
  simp [finSuccSumFinSuccEquiv]

@[simp]
theorem finSuccSumFinSuccEquiv_inr_castSucc (i : Fin n) :
    finSuccSumFinSuccEquiv n (Sum.inr i.castSucc) = Sum.inl (Sum.inr i) := by
  simp [finSuccSumFinSuccEquiv]

@[simp]
theorem finSuccSumFinSuccEquiv_inl_last :
    finSuccSumFinSuccEquiv n (Sum.inl (Fin.last n)) = Sum.inr (Sum.inl 0) := by
  simp [finSuccSumFinSuccEquiv]

@[simp]
theorem finSuccSumFinSuccEquiv_inr_last :
    finSuccSumFinSuccEquiv n (Sum.inr (Fin.last n)) = Sum.inr (Sum.inr 0) := by
  simp [finSuccSumFinSuccEquiv]

@[simp]
theorem finSuccSumFinSuccEquiv_symm_inl_inl (i : Fin n) :
    (finSuccSumFinSuccEquiv n).symm (Sum.inl (Sum.inl i)) = Sum.inl i.castSucc := by
  rw [Equiv.symm_apply_eq, finSuccSumFinSuccEquiv_inl_castSucc]

@[simp]
theorem finSuccSumFinSuccEquiv_symm_inl_inr (i : Fin n) :
    (finSuccSumFinSuccEquiv n).symm (Sum.inl (Sum.inr i)) = Sum.inr i.castSucc := by
  rw [Equiv.symm_apply_eq, finSuccSumFinSuccEquiv_inr_castSucc]

@[simp]
theorem finSuccSumFinSuccEquiv_symm_inr_inl (i : Fin 1) :
    (finSuccSumFinSuccEquiv n).symm (Sum.inr (Sum.inl i)) = Sum.inl (Fin.last n) := by
  rw [Equiv.symm_apply_eq, finSuccSumFinSuccEquiv_inl_last, Subsingleton.elim i 0]

@[simp]
theorem finSuccSumFinSuccEquiv_symm_inr_inr (i : Fin 1) :
    (finSuccSumFinSuccEquiv n).symm (Sum.inr (Sum.inr i)) = Sum.inr (Fin.last n) := by
  rw [Equiv.symm_apply_eq, finSuccSumFinSuccEquiv_inr_last, Subsingleton.elim i 0]

variable (R : Type u) [CommRing R]

/-- **The standard symplectic form splits along the last hyperbolic plane**: read through
`TauCeti.finSuccSumFinSuccEquiv`, the matrix `Matrix.J` of `R^{2(n+1)}` is block diagonal, with the
`Matrix.J` of `R^{2n}` and the `Matrix.J` of the plane as its blocks. -/
theorem fromBlocks_J_submatrix_finSuccSumFinSuccEquiv :
    (fromBlocks (J (Fin n) R) 0 0 (J (Fin 1) R)).submatrix (finSuccSumFinSuccEquiv n)
        (finSuccSumFinSuccEquiv n) = J (Fin (n + 1)) R := by
  ext (x | x) (y | y) <;>
    induction x using Fin.lastCases <;> induction y using Fin.lastCases <;>
    simp [J, one_apply, Fin.castSucc_ne_last, eq_comm (a := Fin.last n)]

end TauCeti

/-! ### Extending a matrix by the identity on the last hyperbolic plane -/

namespace Matrix

open TauCeti

variable {n : ℕ} {R : Type u} [Semiring R]

/-- **The extension of a matrix on `R^{2n}` to `R^{2(n+1)}`** that acts by `M` on the coordinates
`inl i` and `inr i` with `i < n` and by the identity on the two last coordinates: read through
`TauCeti.finSuccSumFinSuccEquiv`, it is the block-diagonal matrix with blocks `M` and `1`. -/
def sumBlockSucc (M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) R) :
    Matrix (Fin (n + 1) ⊕ Fin (n + 1)) (Fin (n + 1) ⊕ Fin (n + 1)) R :=
  (fromBlocks M 0 0 1).submatrix (finSuccSumFinSuccEquiv n) (finSuccSumFinSuccEquiv n)

theorem sumBlockSucc_def (M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) R) :
    sumBlockSucc M =
      (fromBlocks M 0 0 1).submatrix (finSuccSumFinSuccEquiv n) (finSuccSumFinSuccEquiv n) :=
  (rfl)

/-- Read through `TauCeti.finSuccSumFinSuccEquiv`, the extension is the block-diagonal matrix with
blocks `M` and `1`. -/
@[simp]
theorem sumBlockSucc_submatrix_symm (M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) R) :
    (sumBlockSucc M).submatrix (finSuccSumFinSuccEquiv n).symm (finSuccSumFinSuccEquiv n).symm =
      fromBlocks M 0 0 1 := by
  simp [sumBlockSucc_def]

@[simp]
theorem sumBlockSucc_one :
    sumBlockSucc (1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) R) = 1 := by
  rw [sumBlockSucc_def, fromBlocks_one, submatrix_one_equiv]

theorem sumBlockSucc_mul (M N : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) R) :
    sumBlockSucc (M * N) = sumBlockSucc M * sumBlockSucc N := by
  simp [sumBlockSucc_def, fromBlocks_multiply]

theorem transpose_sumBlockSucc (M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) R) :
    (sumBlockSucc M)ᵀ = sumBlockSucc Mᵀ := by
  simp [sumBlockSucc_def, transpose_submatrix, fromBlocks_transpose]

theorem sumBlockSucc_injective :
    Function.Injective (sumBlockSucc : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) R → _) := by
  intro M N h
  have := congrArg
    (fun X => X.submatrix (finSuccSumFinSuccEquiv n).symm (finSuccSumFinSuccEquiv n).symm) h
  simpa [fromBlocks_inj] using this

/-- On the coordinates of `R^{2n}` the extension acts by `M`. -/
@[simp]
theorem sumBlockSucc_mulVec_symm_inl (M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) R)
    (v : Fin (n + 1) ⊕ Fin (n + 1) → R) (x : Fin n ⊕ Fin n) :
    (sumBlockSucc M *ᵥ v) ((finSuccSumFinSuccEquiv n).symm (Sum.inl x)) =
      (M *ᵥ fun y => v ((finSuccSumFinSuccEquiv n).symm (Sum.inl y))) x := by
  simp [sumBlockSucc_def, submatrix_mulVec_equiv, fromBlocks_mulVec, Function.comp_def]

/-- On the coordinates of the last hyperbolic plane the extension acts by the identity. -/
@[simp]
theorem sumBlockSucc_mulVec_symm_inr (M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) R)
    (v : Fin (n + 1) ⊕ Fin (n + 1) → R) (x : Fin 1 ⊕ Fin 1) :
    (sumBlockSucc M *ᵥ v) ((finSuccSumFinSuccEquiv n).symm (Sum.inr x)) =
      v ((finSuccSumFinSuccEquiv n).symm (Sum.inr x)) := by
  simp [sumBlockSucc_def, submatrix_mulVec_equiv, fromBlocks_mulVec, Function.comp_def]

/-- Extending a matrix adds the trace `2` of the identity on the last hyperbolic plane. -/
theorem trace_sumBlockSucc (M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) R) :
    (sumBlockSucc M).trace = M.trace + 2 := by
  simp only [sumBlockSucc_def, trace, diag_apply, submatrix_apply]
  rw [(finSuccSumFinSuccEquiv n).sum_comp fun x => fromBlocks M 0 0 1 x x, Fintype.sum_sum_type]
  simp [one_add_one_eq_two]

end Matrix

namespace TauCeti

variable (n : ℕ) (R : Type u) [CommRing R]

/-- **A matrix read through the splitting is symplectic** exactly when, in the split coordinates,
it preserves the block-diagonal form `fromBlocks J 0 0 J`. -/
theorem submatrix_finSuccSumFinSuccEquiv_mem_symplecticGroup_iff
    (X : Matrix ((Fin n ⊕ Fin n) ⊕ (Fin 1 ⊕ Fin 1)) ((Fin n ⊕ Fin n) ⊕ (Fin 1 ⊕ Fin 1)) R) :
    X.submatrix (finSuccSumFinSuccEquiv n) (finSuccSumFinSuccEquiv n) ∈
        symplecticGroup (Fin (n + 1)) R ↔
      Xᵀ * fromBlocks (J (Fin n) R) 0 0 (J (Fin 1) R) * X =
        fromBlocks (J (Fin n) R) 0 0 (J (Fin 1) R) := by
  rw [SymplecticGroup.mem_iff', ← fromBlocks_J_submatrix_finSuccSumFinSuccEquiv,
    transpose_submatrix, submatrix_mul_equiv, submatrix_mul_equiv]
  refine ⟨fun h => ?_, fun h => by rw [h]⟩
  simpa using congrArg
    (fun Y => Y.submatrix (finSuccSumFinSuccEquiv n).symm (finSuccSumFinSuccEquiv n).symm) h

end TauCeti

namespace Matrix

open TauCeti

variable {n : ℕ} {R : Type u} [CommRing R]

/-- **The extension of a matrix is symplectic exactly when the matrix is.** -/
@[simp]
theorem sumBlockSucc_mem_symplecticGroup_iff {M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) R} :
    sumBlockSucc M ∈ symplecticGroup (Fin (n + 1)) R ↔ M ∈ symplecticGroup (Fin n) R := by
  -- Read through the splitting, the extension is `fromBlocks M 0 0 1` and the form is
  -- `fromBlocks J 0 0 J`, so the condition on the identity block holds trivially.
  rw [sumBlockSucc_def, submatrix_finSuccSumFinSuccEquiv_mem_symplecticGroup_iff,
    SymplecticGroup.mem_iff']
  simp [fromBlocks_transpose, fromBlocks_multiply, fromBlocks_inj]

end Matrix

namespace TauCeti

variable (n : ℕ) (R : Type u) [CommRing R]

/-- **The symplectic block inclusion** `Sp(2n, R) →* Sp(2(n+1), R)`: a symplectic matrix acts on
the coordinates of `R^{2n}` and the last hyperbolic plane is fixed pointwise.  This is the step of
the chain `Sp(2, R) ⊂ Sp(4, R) ⊂ ⋯` along which representations of the symplectic groups are
restricted, the symplectic counterpart of `TauCeti.orthogonalBlockSucc`. -/
def symplecticBlockSucc :
    symplecticGroup (Fin n) R →* symplecticGroup (Fin (n + 1)) R where
  toFun g := ⟨sumBlockSucc (g : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) R),
    sumBlockSucc_mem_symplecticGroup_iff.mpr g.property⟩
  map_one' := Subtype.ext sumBlockSucc_one
  map_mul' _ _ := Subtype.ext (sumBlockSucc_mul _ _)

/-- The symplectic block inclusion has the extended matrix as its underlying matrix. -/
@[simp]
theorem coe_symplecticBlockSucc (g : symplecticGroup (Fin n) R) :
    (symplecticBlockSucc n R g : Matrix (Fin (n + 1) ⊕ Fin (n + 1)) (Fin (n + 1) ⊕ Fin (n + 1)) R) =
      sumBlockSucc (g : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) R) :=
  (rfl)

/-- The symplectic block inclusion is injective, so the chain `Sp(2, R) ⊂ Sp(4, R) ⊂ ⋯` is a chain
of subgroups. -/
theorem symplecticBlockSucc_injective : Function.Injective (symplecticBlockSucc n R) :=
  fun _ _ hgh => Subtype.ext (sumBlockSucc_injective (congrArg Subtype.val hgh))

/-- **The image of the symplectic block inclusion is the pointwise stabilizer of the last
hyperbolic plane**: a symplectic matrix of size `2(n+1)` lies in the image exactly when it fixes
the two last standard basis vectors. -/
theorem exists_symplecticBlockSucc_eq_iff_mulVec_single (g : symplecticGroup (Fin (n + 1)) R) :
    (∃ h : symplecticGroup (Fin n) R, symplecticBlockSucc n R h = g) ↔
      (g : Matrix (Fin (n + 1) ⊕ Fin (n + 1)) (Fin (n + 1) ⊕ Fin (n + 1)) R) *ᵥ
          Pi.single (Sum.inl (Fin.last n)) 1 = Pi.single (Sum.inl (Fin.last n)) 1 ∧
        (g : Matrix (Fin (n + 1) ⊕ Fin (n + 1)) (Fin (n + 1) ⊕ Fin (n + 1)) R) *ᵥ
          Pi.single (Sum.inr (Fin.last n)) 1 = Pi.single (Sum.inr (Fin.last n)) 1 := by
  set e := finSuccSumFinSuccEquiv n
  constructor
  · rintro ⟨h, rfl⟩
    -- The two last basis vectors have no component on the coordinates of `R^{2n}`.
    have hzero : ∀ (z : Fin 1 ⊕ Fin 1),
        (fun y => (Pi.single (e.symm (Sum.inr z)) 1 : _ → R) (e.symm (Sum.inl y))) = 0 := by
      intro z
      ext y
      simp [e.symm.injective.eq_iff]
    constructor <;> ext x <;>
      · rw [← e.symm_apply_apply x]
        rcases e x with y | y
        · rw [coe_symplecticBlockSucc, sumBlockSucc_mulVec_symm_inl]
          first
          | rw [← finSuccSumFinSuccEquiv_symm_inr_inl n 0, hzero]
          | rw [← finSuccSumFinSuccEquiv_symm_inr_inr n 0, hzero]
          rw [mulVec_zero, Pi.zero_apply, Pi.single_eq_of_ne (e.symm.injective.ne Sum.inl_ne_inr)]
        · rw [coe_symplecticBlockSucc, sumBlockSucc_mulVec_symm_inr]
  · -- Fixing the two last basis vectors says that, read through the splitting, the matrix is
    -- `fromBlocks A 0 C 1`.  The symplectic condition then has upper-right block `Cᵀ * J = 0`,
    -- which forces `C = 0` because `J` is invertible, and upper-left block `Aᵀ * J * A = J`,
    -- which says that `A` is symplectic.
    rintro ⟨hinl, hinr⟩
    set G := (g : Matrix (Fin (n + 1) ⊕ Fin (n + 1)) (Fin (n + 1) ⊕ Fin (n + 1)) R)
    -- Read through the splitting, `g` fixes the last hyperbolic plane pointwise.
    have hcol : ∀ x (y : Fin 1 ⊕ Fin 1),
        G x (e.symm (Sum.inr y)) = (Pi.single (e.symm (Sum.inr y)) 1 : _ → R) x := by
      intro x y
      rcases y with y | y
      · simpa [e, mulVec_single_one] using congrFun hinl x
      · simpa [e, mulVec_single_one] using congrFun hinr x
    set X := G.submatrix e.symm e.symm
    have hX : X = fromBlocks X.toBlocks₁₁ 0 X.toBlocks₂₁ 1 := by
      conv_lhs => rw [← fromBlocks_toBlocks X]
      congr 1
      · ext i j
        simp [X, toBlocks₁₂, hcol]
      · ext i j
        simp [X, toBlocks₂₂, hcol, Pi.single_apply, one_apply, e.symm.injective.eq_iff]
    have hGX : X.submatrix e e = G := by simp [X]
    have hmem : G ∈ symplecticGroup (Fin (n + 1)) R := g.property
    rw [← hGX, submatrix_finSuccSumFinSuccEquiv_mem_symplecticGroup_iff, hX] at hmem
    simp only [fromBlocks_transpose, fromBlocks_multiply, fromBlocks_inj, transpose_zero,
      transpose_one, Matrix.zero_mul, Matrix.mul_zero, add_zero, zero_add, Matrix.one_mul,
      Matrix.mul_one] at hmem
    obtain ⟨hA, hC, -, -⟩ := hmem
    -- The upper-right block `Cᵀ * J = 0` forces `C = 0`, since `J * J = -1`.
    have hC0 : X.toBlocks₂₁ = 0 := by
      have hCJJ := congrArg (· * J (Fin 1) R) hC
      simp only [Matrix.mul_assoc, J_squared, Matrix.mul_neg, Matrix.mul_one, Matrix.zero_mul,
        neg_eq_zero] at hCJJ
      simpa using congrArg transpose hCJJ
    rw [hC0, transpose_zero, Matrix.zero_mul, Matrix.mul_zero, add_zero] at hA
    rw [hC0] at hX
    refine ⟨⟨X.toBlocks₁₁, SymplecticGroup.mem_iff'.mpr hA⟩, Subtype.ext ?_⟩
    rw [coe_symplecticBlockSucc, sumBlockSucc_def, ← hX, hGX]

end TauCeti

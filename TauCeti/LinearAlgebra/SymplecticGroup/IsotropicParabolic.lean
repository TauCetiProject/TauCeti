/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import TauCeti.LinearAlgebra.Matrix.BilinearForm
public import TauCeti.LinearAlgebra.Matrix.ColumnRowPartitioned

/-!
# The stabilizer of an isotropic subspace in a symplectic group

Let `R` be a commutative ring and split the coordinates of a free module as `ι ⊕ κ ⊕ ι`. On the
middle block fix a Gram matrix `J₀` with `J₀ᵀ = -J₀`, and on the whole module the Gram matrix

```text
         [  0   0   1 ]
    Ω =  [  0   J₀  0 ]      (`TauCeti.IsotropicParabolic.form ι J₀`).
         [ -1   0   0 ]
```

The first block `U = R^ι` (`TauCeti.IsotropicParabolic.isotropicSubmodule`) is isotropic for `Ω`;
when `Ω` is nondegenerate its orthogonal is `U ⊕ R^κ`. For instance, for `m = r + s`, `ι = Fin r`,
`κ = Fin (2 * s)` and `J₀ = [[0, 1], [-1, 0]]`, the form `Ω` is the standard alternating form of
rank `2m` written in a symplectic basis `u₁, …, u_r, u_{r+1}, …, u_m, f_{r+1}, …, f_m, f₁, …, f_r`
with `ω(uᵢ, fᵢ) = 1`, and `U` is spanned by `u₁, …, u_r`.

The matrices `g` with `gᵀ Ω g = Ω` mapping `U` into itself form the submonoid
`TauCeti.IsotropicParabolic.stabilizer ι J₀`, the stabilizer `P` of `U`. Its elements are
exactly the block upper triangular symplectic matrices: a symplectic matrix preserving `U` also
preserves `U ⊕ R^κ` (`TauCeti.IsotropicParabolic.toBlocks₂₁_toBlocks₂₂_eq_zero`). This file
proves that `P` is the product of a Levi part and a unipotent part:

```text
                [ A  0      0   ]                [ 1  Yᵀ J₀  Z ]
    l(A, D)  =  [ 0  D      0   ],   u(Y, Z)  =  [ 0  1      Y ],
                [ 0  0   A⁻ᵀ    ]                [ 0  0      1 ]
```

(`TauCeti.IsotropicParabolic.levi` and `TauCeti.IsotropicParabolic.unipotent`). Here `l(A, D)`
lies in `P` exactly when `Dᵀ J₀ D = J₀`, and `u(Y, Z)` exactly when `Z - Zᵀ = Yᵀ J₀ Y`. Every
element of `P` is uniquely a product `u(Y, Z) l(A, D)`, whose coordinates are read off its blocks.
The unipotent matrices multiply by `(Y, Z)(Y', Z') = (Y + Y', Z + Z' + Yᵀ J₀ Y')`, with inverse
`(-Y, -Zᵀ)`, and the Levi part normalizes them:
`l(A, D) u(Y, Z) = u(D Y Aᵀ, A Z Aᵀ) l(A, D)`.

When `J₀` is alternating, so is `Yᵀ J₀ Y`, and it is `Z₀ - Z₀ᵀ` for its strictly upper triangular
part `Z₀` (`TauCeti.IsotropicParabolic.unipotentBase`). Thus `u(Y, Z)` lies in `P` exactly when
`Z - Z₀` is symmetric, and `(Y, Z) ↦ (Y, Z - Z₀)` identifies the unipotent part of `P` with the
pairs of a matrix `Y` and a symmetric matrix (`TauCeti.IsotropicParabolic.unipotentEquiv`). These
are affine coordinates in every characteristic: no division by `2` is used.

## Main definitions

* `TauCeti.IsotropicParabolic.form`: the Gram matrix `Ω`.
* `TauCeti.IsotropicParabolic.isotropicSubmodule`: the isotropic subspace `U`.
* `TauCeti.IsotropicParabolic.stabilizer`: the matrices preserving `Ω` and mapping `U` into `U`.
* `TauCeti.IsotropicParabolic.levi` and `TauCeti.IsotropicParabolic.unipotent`: the Levi and
  unipotent matrices `l(A, D)` and `u(Y, Z)`.
* `TauCeti.IsotropicParabolic.unipotentEquiv`: the affine coordinates of the unipotent part.

## Main results

* `TauCeti.IsotropicParabolic.mem_stabilizer_iff_exists_unipotent_mul_levi`: the elements of
  `P` are the products `u(Y, Z) l(A, D)` with `Z - Zᵀ = Yᵀ J₀ Y` and `Dᵀ J₀ D = J₀`.
* `TauCeti.IsotropicParabolic.unipotent_mul_levi_eq`: the factors of an element of `P`, read off
  its blocks.
* `TauCeti.IsotropicParabolic.unipotent_mul_levi_inj`: the factorization is unique.
* `TauCeti.IsotropicParabolic.unipotent_mul_unipotent`,
  `TauCeti.IsotropicParabolic.unipotent_mul_unipotent_neg_transpose` and
  `TauCeti.IsotropicParabolic.levi_mul_unipotent`: the multiplication, inverse and conjugation
  laws of the unipotent part.

## References

* J. S. Milne, *Algebraic Groups* (2017), §24.6 (symplectic groups and isotropic flags).
-/

public section

open Matrix

namespace TauCeti.IsotropicParabolic

variable {R ι κ : Type*} [CommRing R]

section Definitions

variable (ι) in
/-- The Gram matrix `[[0, 0, 1], [0, J₀, 0], [-1, 0, 0]]` on the coordinates `ι ⊕ κ ⊕ ι`. The
first block of coordinates is isotropic for it
(`TauCeti.IsotropicParabolic.dotProduct_form_mulVec_eq_zero`). -/
def form [DecidableEq ι] (J₀ : Matrix κ κ R) : Matrix (ι ⊕ κ ⊕ ι) (ι ⊕ κ ⊕ ι) R :=
  fromBlocks 0 (fromCols 0 1) (fromRows 0 (-1)) (fromBlocks J₀ 0 0 0)

/-- The unipotent matrix `u(Y, Z) = [[1, Yᵀ J₀, Z], [0, 1, Y], [0, 0, 1]]`. For `J₀ᵀ = -J₀` it
preserves `TauCeti.IsotropicParabolic.form` exactly when `Z - Zᵀ = Yᵀ J₀ Y`
(`TauCeti.IsotropicParabolic.unipotent_mem_stabilizer_iff`). -/
def unipotent [DecidableEq ι] [Fintype κ] [DecidableEq κ] (J₀ : Matrix κ κ R) (Y : Matrix κ ι R)
    (Z : Matrix ι ι R) : Matrix (ι ⊕ κ ⊕ ι) (ι ⊕ κ ⊕ ι) R :=
  fromBlocks 1 (fromCols (Yᵀ * J₀) Z) 0 (fromBlocks 1 Y 0 1)

/-- The block diagonal matrix `l(A, D) = diag(A, D, A⁻ᵀ)`. It preserves
`TauCeti.IsotropicParabolic.form` exactly when `Dᵀ J₀ D = J₀`
(`TauCeti.IsotropicParabolic.levi_mem_stabilizer_iff`). -/
noncomputable def levi [Fintype ι] [DecidableEq ι] (A : GL ι R) (D : Matrix κ κ R) :
    Matrix (ι ⊕ κ ⊕ ι) (ι ⊕ κ ⊕ ι) R :=
  fromBlocks A 0 0 (fromBlocks D 0 0 (A : Matrix ι ι R)⁻¹ᵀ)

variable (R ι κ) in
/-- The submodule of vectors supported on the first block of `ι ⊕ κ ⊕ ι`, isotropic for
`TauCeti.IsotropicParabolic.form` (`TauCeti.IsotropicParabolic.dotProduct_form_mulVec_eq_zero`). -/
def isotropicSubmodule : Submodule R (ι ⊕ κ ⊕ ι → R) :=
  ⨅ j : κ ⊕ ι, LinearMap.ker (LinearMap.proj (R := R) (φ := fun _ => R) (Sum.inr j))

variable (ι) in
/-- The stabilizer `P` of the isotropic subspace `TauCeti.IsotropicParabolic.isotropicSubmodule`
in the symplectic monoid of `TauCeti.IsotropicParabolic.form ι J₀`: the matrices `g` with
`gᵀ Ω g = Ω` mapping the first block into itself. -/
def stabilizer [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] (J₀ : Matrix κ κ R) :
    Submonoid (Matrix (ι ⊕ κ ⊕ ι) (ι ⊕ κ ⊕ ι) R) where
  carrier := {g | gᵀ * form ι J₀ * g = form ι J₀ ∧
    (isotropicSubmodule R ι κ).map g.mulVecLin ≤ isotropicSubmodule R ι κ}
  mul_mem' {g h} hg hh := by
    refine ⟨?_, ?_⟩
    · rw [transpose_mul, show hᵀ * gᵀ * form ι J₀ * (g * h) = hᵀ * (gᵀ * form ι J₀ * g) * h by
        simp only [Matrix.mul_assoc], hg.1, hh.1]
    · rw [mulVecLin_mul, Submodule.map_comp]
      exact (Submodule.map_mono hh.2).trans hg.2
  one_mem' := by simp

end Definitions

/-- A vector lies in `TauCeti.IsotropicParabolic.isotropicSubmodule` exactly when its coordinates
outside the first block vanish. -/
theorem mem_isotropicSubmodule {v : ι ⊕ κ ⊕ ι → R} :
    v ∈ isotropicSubmodule R ι κ ↔ ∀ j, v (Sum.inr j) = 0 := by
  simp [isotropicSubmodule]

variable [Fintype ι] [DecidableEq ι] [Fintype κ]

/-- The subspace `TauCeti.IsotropicParabolic.isotropicSubmodule` is isotropic for
`TauCeti.IsotropicParabolic.form`. -/
theorem dotProduct_form_mulVec_eq_zero (J₀ : Matrix κ κ R) {v w : ι ⊕ κ ⊕ ι → R}
    (hv : v ∈ isotropicSubmodule R ι κ) (hw : w ∈ isotropicSubmodule R ι κ) :
    v ⬝ᵥ (form ι J₀ *ᵥ w) = 0 := by
  rw [mem_isotropicSubmodule] at hv hw
  simp [dotProduct, mulVec, Fintype.sum_sum_type, form, hv, hw]

omit [DecidableEq ι] in
/-- A matrix maps the first block into itself exactly when its lower left block vanishes. -/
theorem map_mulVecLin_le_isotropicSubmodule_iff (g : Matrix (ι ⊕ κ ⊕ ι) (ι ⊕ κ ⊕ ι) R) :
    (isotropicSubmodule R ι κ).map g.mulVecLin ≤ isotropicSubmodule R ι κ ↔
      g.toBlocks₂₁ = 0 := by
  classical
  rw [Submodule.map_le_iff_le_comap]
  constructor
  · intro h
    ext j i
    have := h (show Pi.single (Sum.inl i) 1 ∈ isotropicSubmodule R ι κ by
      simp [mem_isotropicSubmodule])
    rw [Submodule.mem_comap, mem_isotropicSubmodule] at this
    simpa [toBlocks₂₁, mulVec_single] using this j
  · intro h v hv
    rw [mem_isotropicSubmodule] at hv
    rw [Submodule.mem_comap, mem_isotropicSubmodule]
    intro j
    have := fun i => congrFun (congrFun h j) i
    simp only [toBlocks₂₁, of_apply] at this
    simp [mulVec, dotProduct, Fintype.sum_sum_type, hv, this]

variable [DecidableEq κ]

/-- A matrix lies in the stabilizer exactly when it preserves the form and its lower left block
vanishes. -/
theorem mem_stabilizer_iff {J₀ : Matrix κ κ R} {g : Matrix (ι ⊕ κ ⊕ ι) (ι ⊕ κ ⊕ ι) R} :
    g ∈ stabilizer ι J₀ ↔ gᵀ * form ι J₀ * g = form ι J₀ ∧ g.toBlocks₂₁ = 0 := by
  rw [← map_mulVecLin_le_isotropicSubmodule_iff]
  rfl

/-! ### The form on block upper triangular matrices -/

omit [DecidableEq κ] in
/-- The Gram matrix `gᵀ Ω g` of a matrix `g` whose lower left block vanishes. -/
private theorem transpose_mul_form_mul_fromBlocks (J₀ : Matrix κ κ R) (a : Matrix ι ι R)
    (b : Matrix ι κ R) (c : Matrix ι ι R) (e : Matrix κ κ R) (f : Matrix κ ι R)
    (h : Matrix ι κ R) (k : Matrix ι ι R) :
    (fromBlocks a (fromCols b c) 0 (fromBlocks e f h k))ᵀ * form ι J₀ *
        fromBlocks a (fromCols b c) 0 (fromBlocks e f h k) =
      fromBlocks 0 (fromCols (aᵀ * h) (aᵀ * k)) (fromRows (-(hᵀ * a)) (-(kᵀ * a)))
        (fromBlocks (bᵀ * h + eᵀ * J₀ * e - hᵀ * b) (bᵀ * k + eᵀ * J₀ * f - hᵀ * c)
          (cᵀ * h + fᵀ * J₀ * e - kᵀ * b) (cᵀ * k + fᵀ * J₀ * f - kᵀ * c)) := by
  simp only [form, fromBlocks_transpose, transpose_fromCols, transpose_zero, fromBlocks_multiply,
    fromBlocks_mul_fromRows, mul_fromCols, fromRows_mul, fromCols_fromRows_eq_fromBlocks,
    fromBlocks_add, fromRows_add]
  simp [fromCols_mul_fromBlocks, Matrix.mul_assoc, sub_eq_add_neg, add_comm]

/-- The equations that `gᵀ Ω g = Ω` imposes on the blocks of a matrix `g` whose lower left block
vanishes: the block `h` vanishes too, so that `g` also preserves the orthogonal of the first
block, and the remaining blocks are related as stated. -/
private theorem block_eqs {J₀ : Matrix κ κ R} {a : Matrix ι ι R}
    {b : Matrix ι κ R} {c : Matrix ι ι R} {e : Matrix κ κ R} {f : Matrix κ ι R}
    {h : Matrix ι κ R} {k : Matrix ι ι R}
    (hg : fromBlocks a (fromCols b c) 0 (fromBlocks e f h k) ∈ stabilizer ι J₀) :
    h = 0 ∧ aᵀ * k = 1 ∧ k * aᵀ = 1 ∧ eᵀ * J₀ * e = J₀ ∧ kᵀ * b = fᵀ * J₀ * e ∧
      cᵀ * k + fᵀ * J₀ * f - kᵀ * c = 0 := by
  have hg := (mem_stabilizer_iff.1 hg).1
  rw [transpose_mul_form_mul_fromBlocks, form] at hg
  simp only [fromBlocks_inj, fromCols_ext_iff, fromRows_ext_iff] at hg
  obtain ⟨-, ⟨h₁, h₂⟩, -, h₃, -, h₄, h₅⟩ := hg
  have hk : k * aᵀ = 1 := mul_eq_one_comm.1 h₂
  have hh : h = 0 := by rw [← Matrix.one_mul h, ← hk, Matrix.mul_assoc, h₁, Matrix.mul_zero]
  subst hh
  simp only [Matrix.mul_zero, transpose_zero, Matrix.zero_mul, zero_add, sub_zero] at h₃ h₄ h₅
  exact ⟨rfl, h₂, hk, h₃, (sub_eq_zero.1 h₄).symm, h₅⟩

omit [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] in
private theorem eq_fromBlocks_of_toBlocks₂₁_eq_zero {g : Matrix (ι ⊕ κ ⊕ ι) (ι ⊕ κ ⊕ ι) R}
    (hg : g.toBlocks₂₁ = 0) :
    g = fromBlocks g.toBlocks₁₁ (fromCols g.toBlocks₁₂.toCols₁ g.toBlocks₁₂.toCols₂) 0
      (fromBlocks g.toBlocks₂₂.toBlocks₁₁ g.toBlocks₂₂.toBlocks₁₂ g.toBlocks₂₂.toBlocks₂₁
        g.toBlocks₂₂.toBlocks₂₂) := by
  rw [fromCols_toCols, fromBlocks_toBlocks, ← hg, fromBlocks_toBlocks]

/-- A symplectic matrix preserving the isotropic subspace `U` also preserves its orthogonal
`U ⊕ R^κ`: its block in position `(3, 2)` vanishes. -/
theorem toBlocks₂₁_toBlocks₂₂_eq_zero {J₀ : Matrix κ κ R}
    {g : Matrix (ι ⊕ κ ⊕ ι) (ι ⊕ κ ⊕ ι) R} (hg : g ∈ stabilizer ι J₀) :
    g.toBlocks₂₂.toBlocks₂₁ = 0 := by
  rw [eq_fromBlocks_of_toBlocks₂₁_eq_zero (mem_stabilizer_iff.1 hg).2] at hg
  exact (block_eqs hg).1

/-- The block of an element of the stabilizer acting on the isotropic subspace is invertible. -/
theorem isUnit_toBlocks₁₁ {J₀ : Matrix κ κ R} {g : Matrix (ι ⊕ κ ⊕ ι) (ι ⊕ κ ⊕ ι) R}
    (hg : g ∈ stabilizer ι J₀) : IsUnit g.toBlocks₁₁ := by
  rw [eq_fromBlocks_of_toBlocks₂₁_eq_zero (mem_stabilizer_iff.1 hg).2] at hg
  obtain ⟨-, h₁, h₂, -⟩ := block_eqs hg
  refine ⟨⟨g.toBlocks₁₁, g.toBlocks₂₂.toBlocks₂₂ᵀ, ?_, ?_⟩, rfl⟩
  · simpa [transpose_mul] using congrArg transpose h₂
  · simpa [transpose_mul] using congrArg transpose h₁

/-! ### Levi and unipotent matrices -/

omit [DecidableEq κ] in
/-- The blocks of the product `u(Y, Z) l(A, D)`. -/
theorem unipotent_mul_levi (J₀ : Matrix κ κ R) (Y : Matrix κ ι R) (Z : Matrix ι ι R)
    (A : GL ι R) (D : Matrix κ κ R) [DecidableEq κ] :
    unipotent J₀ Y Z * levi A D =
      fromBlocks A (fromCols (Yᵀ * J₀ * D) (Z * (A : Matrix ι ι R)⁻¹ᵀ)) 0
        (fromBlocks D (Y * (A : Matrix ι ι R)⁻¹ᵀ) 0 (A : Matrix ι ι R)⁻¹ᵀ) := by
  simp [unipotent, levi, fromBlocks_multiply, fromCols_mul_fromBlocks]

/-- The Levi part normalizes the unipotent part: `l(A, D) u(Y, Z) = u(D Y Aᵀ, A Z Aᵀ) l(A, D)`
when `Dᵀ J₀ D = J₀`. -/
theorem levi_mul_unipotent {J₀ : Matrix κ κ R} {D : Matrix κ κ R} (hD : Dᵀ * J₀ * D = J₀)
    (A : GL ι R) (Y : Matrix κ ι R) (Z : Matrix ι ι R) :
    levi A D * unipotent J₀ Y Z =
      unipotent J₀ (D * Y * (A : Matrix ι ι R)ᵀ) (A * Z * (A : Matrix ι ι R)ᵀ) * levi A D := by
  have hA : (A : Matrix ι ι R)ᵀ * (A : Matrix ι ι R)⁻¹ᵀ = 1 := by
    rw [← transpose_mul, ← Matrix.coe_units_inv, Units.inv_mul, transpose_one]
  rw [unipotent_mul_levi]
  rw [Matrix.mul_assoc] at hD
  simp [unipotent, levi, fromBlocks_multiply, Matrix.mul_assoc, hA, hD]

private theorem transpose_mul_form_mul_unipotent_eq_iff {J₀ : Matrix κ κ R} (hJ₀ : J₀ᵀ = -J₀)
    (Y : Matrix κ ι R) (Z : Matrix ι ι R) :
    (unipotent J₀ Y Z)ᵀ * form ι J₀ * unipotent J₀ Y Z = form ι J₀ ↔
      Z - Zᵀ = Yᵀ * J₀ * Y := by
  rw [unipotent, transpose_mul_form_mul_fromBlocks, form]
  simp only [transpose_one, Matrix.mul_zero, mul_one, transpose_zero, Matrix.mul_one, neg_zero,
    transpose_mul, hJ₀, transpose_transpose, Matrix.neg_mul, one_mul, zero_add, Matrix.zero_mul,
    sub_zero, neg_add_cancel, sub_self, Matrix.one_mul, Matrix.mul_assoc, fromBlocks_inj, true_and]
  rw [sub_eq_zero, sub_eq_iff_eq_add', eq_comm]

/-- The unipotent matrix `u(Y, Z)` lies in the stabilizer exactly when `Z - Zᵀ = Yᵀ J₀ Y`. -/
theorem unipotent_mem_stabilizer_iff {J₀ : Matrix κ κ R} (hJ₀ : J₀ᵀ = -J₀) {Y : Matrix κ ι R}
    {Z : Matrix ι ι R} : unipotent J₀ Y Z ∈ stabilizer ι J₀ ↔ Z - Zᵀ = Yᵀ * J₀ * Y := by
  rw [mem_stabilizer_iff, transpose_mul_form_mul_unipotent_eq_iff hJ₀]
  simp [unipotent]

/-- The Levi matrix `l(A, D)` lies in the stabilizer exactly when `Dᵀ J₀ D = J₀`. -/
theorem levi_mem_stabilizer_iff {J₀ : Matrix κ κ R} {A : GL ι R} {D : Matrix κ κ R} :
    levi A D ∈ stabilizer ι J₀ ↔ Dᵀ * J₀ * D = J₀ := by
  rw [mem_stabilizer_iff, levi, ← fromCols_zero, transpose_mul_form_mul_fromBlocks, form]
  simp [fromBlocks_inj, ← transpose_mul, Matrix.mul_assoc]

/-! ### The Levi decomposition of the stabilizer -/

/-- The factorization of an element of the stabilizer, given by its blocks. -/
private theorem factor_blocks {J₀ : Matrix κ κ R} {a : Matrix ι ι R}
    {b : Matrix ι κ R} {c : Matrix ι ι R} {e : Matrix κ κ R} {f : Matrix κ ι R}
    {h : Matrix ι κ R} {k : Matrix ι ι R}
    (hg : fromBlocks a (fromCols b c) 0 (fromBlocks e f h k) ∈ stabilizer ι J₀)
    (A : GL ι R) (hA : (A : Matrix ι ι R) = a) :
    c * aᵀ - (c * aᵀ)ᵀ = (f * aᵀ)ᵀ * J₀ * (f * aᵀ) ∧ eᵀ * J₀ * e = J₀ ∧
      unipotent J₀ (f * aᵀ) (c * aᵀ) * levi A e =
        fromBlocks a (fromCols b c) 0 (fromBlocks e f h k) := by
  obtain ⟨rfl, h₁, h₂, h₃, h₄, h₅⟩ := block_eqs hg
  have hak : a * kᵀ = 1 := by rw [← transpose_transpose a, ← transpose_mul, h₂, transpose_one]
  have hinv : (A : Matrix ι ι R)⁻¹ᵀ = k := by
    rw [← Matrix.coe_units_inv, Units.inv_eq_of_mul_eq_one_right (hA ▸ hak), transpose_transpose]
  refine ⟨?_, h₃, ?_⟩
  · -- conjugate the `(3, 3)` block equation by `a`
    have := congrArg (fun M => a * M * aᵀ) h₅
    simp only [Matrix.mul_sub, Matrix.mul_add, Matrix.sub_mul, Matrix.add_mul, Matrix.mul_zero,
      Matrix.zero_mul] at this
    simp only [Matrix.mul_assoc, h₂, Matrix.mul_one] at this
    rw [← Matrix.mul_assoc a kᵀ, hak, Matrix.one_mul] at this
    simp only [transpose_mul, transpose_transpose, Matrix.mul_assoc]
    rw [← sub_eq_zero, ← neg_eq_zero, ← this]
    abel
  · have hb : (f * aᵀ)ᵀ * J₀ * e = b := by
      simp only [transpose_mul, transpose_transpose, Matrix.mul_assoc]
      rw [← Matrix.mul_assoc fᵀ, ← h₄, ← Matrix.mul_assoc, hak, Matrix.one_mul]
    rw [unipotent_mul_levi, hinv, hA, hb, Matrix.mul_assoc c, h₁, Matrix.mul_one,
      Matrix.mul_assoc f, h₁, Matrix.mul_one]

/-- **The coordinates of an element of the stabilizer.** An element `g` of the stabilizer is
`u(Y, Z) l(A, D)`, where `A` and `D` are its diagonal blocks in positions `(1, 1)` and `(2, 2)`,
and `Y` and `Z` are its blocks in positions `(2, 3)` and `(1, 3)` multiplied on the right by
`Aᵀ`. -/
theorem unipotent_mul_levi_eq {J₀ : Matrix κ κ R} {g : Matrix (ι ⊕ κ ⊕ ι) (ι ⊕ κ ⊕ ι) R}
    (hg : g ∈ stabilizer ι J₀) (A : GL ι R) (hA : (A : Matrix ι ι R) = g.toBlocks₁₁) :
    unipotent J₀ (g.toBlocks₂₂.toBlocks₁₂ * g.toBlocks₁₁ᵀ) (g.toBlocks₁₂.toCols₂ * g.toBlocks₁₁ᵀ) *
      levi A g.toBlocks₂₂.toBlocks₁₁ = g := by
  have h := eq_fromBlocks_of_toBlocks₂₁_eq_zero (mem_stabilizer_iff.1 hg).2
  rw [h] at hg
  exact (factor_blocks hg A hA).2.2.trans h.symm

/-- **Levi decomposition of the stabilizer of an isotropic subspace.** A matrix lies in the
stabilizer exactly when it is a product `u(Y, Z) l(A, D)` of a unipotent matrix with
`Z - Zᵀ = Yᵀ J₀ Y` and a Levi matrix with `Dᵀ J₀ D = J₀`. -/
theorem mem_stabilizer_iff_exists_unipotent_mul_levi {J₀ : Matrix κ κ R} (hJ₀ : J₀ᵀ = -J₀)
    {g : Matrix (ι ⊕ κ ⊕ ι) (ι ⊕ κ ⊕ ι) R} :
    g ∈ stabilizer ι J₀ ↔ ∃ (Y : Matrix κ ι R) (Z : Matrix ι ι R) (A : GL ι R) (D : Matrix κ κ R),
      Z - Zᵀ = Yᵀ * J₀ * Y ∧ Dᵀ * J₀ * D = J₀ ∧ unipotent J₀ Y Z * levi A D = g := by
  constructor
  · intro hg
    obtain ⟨A, hA⟩ := isUnit_toBlocks₁₁ hg
    have h := eq_fromBlocks_of_toBlocks₂₁_eq_zero (mem_stabilizer_iff.1 hg).2
    rw [h] at hg
    obtain ⟨hYZ, hD, hg⟩ := factor_blocks hg A hA
    exact ⟨_, _, A, _, hYZ, hD, hg.trans h.symm⟩
  · rintro ⟨Y, Z, A, D, hYZ, hD, rfl⟩
    exact mul_mem ((unipotent_mem_stabilizer_iff hJ₀).2 hYZ) (levi_mem_stabilizer_iff.2 hD)

/-- **Uniqueness of the Levi decomposition.** The factors of `u(Y, Z) l(A, D)` are determined by
the product. -/
theorem unipotent_mul_levi_inj {J₀ : Matrix κ κ R} {Y Y' : Matrix κ ι R} {Z Z' : Matrix ι ι R}
    {A A' : GL ι R} {D D' : Matrix κ κ R} :
    unipotent J₀ Y Z * levi A D = unipotent J₀ Y' Z' * levi A' D' ↔
      Y = Y' ∧ Z = Z' ∧ A = A' ∧ D = D' := by
  refine ⟨fun h => ?_, by rintro ⟨rfl, rfl, rfl, rfl⟩; rfl⟩
  rw [unipotent_mul_levi, unipotent_mul_levi] at h
  simp only [fromBlocks_inj, fromCols_ext_iff] at h
  obtain ⟨hA, ⟨-, hZ⟩, -, hD, hY, -, -⟩ := h
  obtain rfl : A = A' := Units.ext hA
  have hA : (A : Matrix ι ι R)⁻¹ᵀ * (A : Matrix ι ι R)ᵀ = 1 := by
    rw [← transpose_mul, ← Matrix.coe_units_inv, Units.mul_inv, transpose_one]
  refine ⟨?_, ?_, rfl, hD⟩
  · simpa [Matrix.mul_assoc, hA] using congrArg (· * (A : Matrix ι ι R)ᵀ) hY
  · simpa [Matrix.mul_assoc, hA] using congrArg (· * (A : Matrix ι ι R)ᵀ) hZ

/-! ### The group laws -/

omit [Fintype ι] in
/-- The unipotent matrix with coordinates `(0, 0)` is the identity. -/
@[simp]
theorem unipotent_zero_zero (J₀ : Matrix κ κ R) : unipotent J₀ (0 : Matrix κ ι R) 0 = 1 := by
  simp [unipotent, ← fromBlocks_one]

/-- The multiplication law `(Y, Z)(Y', Z') = (Y + Y', Z + Z' + Yᵀ J₀ Y')` of the unipotent
matrices. -/
@[simp]
theorem unipotent_mul_unipotent (J₀ : Matrix κ κ R) (Y Y' : Matrix κ ι R) (Z Z' : Matrix ι ι R) :
    unipotent J₀ Y Z * unipotent J₀ Y' Z' = unipotent J₀ (Y + Y') (Z + Z' + Yᵀ * J₀ * Y') := by
  simp only [unipotent, fromBlocks_multiply, fromCols_mul_fromBlocks]
  simp only [Matrix.one_mul, Matrix.mul_one, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add,
    transpose_add, Matrix.add_mul, Matrix.mul_assoc, fromCols_add]
  congr 2 <;> abel

/-- The inverse `(Y, Z)⁻¹ = (-Y, -Zᵀ)` of a unipotent matrix in the stabilizer. -/
theorem unipotent_mul_unipotent_neg_transpose {J₀ : Matrix κ κ R} {Y : Matrix κ ι R}
    {Z : Matrix ι ι R} (hYZ : Z - Zᵀ = Yᵀ * J₀ * Y) :
    unipotent J₀ Y Z * unipotent J₀ (-Y) (-Zᵀ) = 1 := by
  rw [unipotent_mul_unipotent, ← unipotent_zero_zero J₀]
  congr 1
  · abel
  · rw [Matrix.mul_neg, ← hYZ]
    abel

/-- The inverse `(Y, Z)⁻¹ = (-Y, -Zᵀ)` of a unipotent matrix in the stabilizer, on the left. -/
theorem unipotent_neg_transpose_mul_unipotent {J₀ : Matrix κ κ R} {Y : Matrix κ ι R}
    {Z : Matrix ι ι R} (hYZ : Z - Zᵀ = Yᵀ * J₀ * Y) :
    unipotent J₀ (-Y) (-Zᵀ) * unipotent J₀ Y Z = 1 := by
  rw [unipotent_mul_unipotent, ← unipotent_zero_zero J₀]
  congr 1
  · abel
  · rw [transpose_neg, Matrix.neg_mul, Matrix.neg_mul, ← hYZ]
    abel

omit [Fintype κ] in
/-- The Levi matrix with coordinates `(1, 1)` is the identity. -/
@[simp]
theorem levi_one_one : levi (1 : GL ι R) (1 : Matrix κ κ R) = 1 := by
  simp [levi, ← fromBlocks_one]

omit [DecidableEq κ] in
/-- The Levi matrices multiply coordinatewise: `l(A, D) l(A', D') = l(A A', D D')`. -/
@[simp]
theorem levi_mul_levi (A A' : GL ι R) (D D' : Matrix κ κ R) :
    levi A D * levi A' D' = levi (A * A') (D * D') := by
  simp [levi, fromBlocks_multiply, Matrix.mul_inv_rev, transpose_mul]

/-! ### Affine coordinates on the unipotent part -/

section Coordinates

variable [LinearOrder ι]

omit [DecidableEq ι] [DecidableEq κ] in
variable (J₀ : Matrix κ κ R) (Y : Matrix κ ι R) in
/-- The strictly upper triangular part `Z₀` of `Yᵀ J₀ Y`. For alternating `J₀` it satisfies
`Z₀ - Z₀ᵀ = Yᵀ J₀ Y` (`TauCeti.IsotropicParabolic.unipotentBase_sub_transpose`), so it is a
base point of the matrices `Z` with `u(Y, Z)` in the stabilizer. -/
def unipotentBase : Matrix ι ι R :=
  of fun i j => if i < j then (Yᵀ * J₀ * Y) i j else 0

omit [Fintype ι] [DecidableEq ι] in
theorem unipotentBase_sub_transpose {J₀ : Matrix κ κ R} (hJ₀ : J₀.toBilin'.IsAlt)
    (Y : Matrix κ ι R) : unipotentBase J₀ Y - (unipotentBase J₀ Y)ᵀ = Yᵀ * J₀ * Y := by
  -- `Yᵀ J₀ Y` is alternating: skew because `J₀` is, and its diagonal entries are values of the
  -- form of `J₀` on the columns of `Y`
  have hskew : (Yᵀ * J₀ * Y)ᵀ = -(Yᵀ * J₀ * Y) := by
    simp [transpose_mul, transpose_eq_neg_of_isAlt_toBilin' hJ₀, Matrix.mul_assoc]
  have hdiag (i : ι) : (Yᵀ * J₀ * Y) i i = 0 := by
    have := hJ₀ (fun a => Y a i)
    rw [toBilin'_apply] at this
    simp only [Matrix.mul_apply, transpose_apply, Finset.sum_mul]
    rwa [Finset.sum_comm]
  ext i j
  rw [Matrix.sub_apply, transpose_apply]
  rcases lt_trichotomy i j with h | rfl | h
  · simp [unipotentBase, h, lt_asymm h]
  · simp [unipotentBase, hdiag]
  · simp only [unipotentBase, of_apply, h, lt_asymm h, ↓reduceIte, zero_sub]
    have := congrFun (congrFun hskew i) j
    simp only [transpose_apply, Matrix.neg_apply] at this
    rw [this, neg_neg]

/-- For alternating `J₀`, the unipotent matrix `u(Y, Z)` lies in the stabilizer exactly when
`Z - Z₀` is symmetric, where `Z₀` is the strictly upper triangular part of `Yᵀ J₀ Y`. -/
theorem unipotent_mem_stabilizer_iff_isSymm {J₀ : Matrix κ κ R} (hJ₀ : J₀.toBilin'.IsAlt)
    {Y : Matrix κ ι R} {Z : Matrix ι ι R} :
    unipotent J₀ Y Z ∈ stabilizer ι J₀ ↔ (Z - unipotentBase J₀ Y).IsSymm := by
  rw [unipotent_mem_stabilizer_iff (transpose_eq_neg_of_isAlt_toBilin' hJ₀),
    ← unipotentBase_sub_transpose hJ₀ Y, IsSymm, transpose_sub,
    sub_eq_sub_iff_sub_eq_sub (a := Zᵀ), ← neg_inj, neg_sub, neg_sub]

/-- **Affine coordinates on the unipotent part.** For alternating `J₀`, the pairs `(Y, Z)` with
`u(Y, Z)` in the stabilizer correspond to the pairs of a matrix `Y` and a symmetric matrix
`S = Z - Z₀`. -/
def unipotentEquiv {J₀ : Matrix κ κ R} (hJ₀ : J₀.toBilin'.IsAlt) :
    {p : Matrix κ ι R × Matrix ι ι R // unipotent J₀ p.fst p.snd ∈ stabilizer ι J₀} ≃
      Matrix κ ι R × {S : Matrix ι ι R // S.IsSymm} where
  toFun p := (p.val.fst, ⟨p.val.snd - unipotentBase J₀ p.val.fst,
    (unipotent_mem_stabilizer_iff_isSymm hJ₀).1 p.property⟩)
  invFun q := ⟨(q.fst, q.snd.val + unipotentBase J₀ q.fst),
    (unipotent_mem_stabilizer_iff_isSymm hJ₀).2 (by simpa using q.snd.property)⟩
  left_inv p := by ext <;> simp
  right_inv q := by ext <;> simp

/-- The coordinates `(Y, Z - Z₀)` of a unipotent element. -/
@[simp]
theorem unipotentEquiv_apply {J₀ : Matrix κ κ R} (hJ₀ : J₀.toBilin'.IsAlt)
    (p : {p : Matrix κ ι R × Matrix ι ι R // unipotent J₀ p.fst p.snd ∈ stabilizer ι J₀}) :
    unipotentEquiv hJ₀ p = (p.val.fst, ⟨p.val.snd - unipotentBase J₀ p.val.fst,
      (unipotent_mem_stabilizer_iff_isSymm hJ₀).1 p.property⟩) :=
  (rfl)

/-- The unipotent element `(Y, S + Z₀)` with given affine coordinates `(Y, S)`. -/
@[simp]
theorem coe_unipotentEquiv_symm_apply {J₀ : Matrix κ κ R} (hJ₀ : J₀.toBilin'.IsAlt)
    (q : Matrix κ ι R × {S : Matrix ι ι R // S.IsSymm}) :
    ((unipotentEquiv hJ₀).symm q : Matrix κ ι R × Matrix ι ι R) =
      (q.fst, q.snd.val + unipotentBase J₀ q.fst) :=
  (rfl)

end Coordinates

end TauCeti.IsotropicParabolic

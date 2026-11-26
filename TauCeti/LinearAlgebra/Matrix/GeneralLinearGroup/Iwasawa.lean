/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Topology.Algebra.Constructions
public import Mathlib.Topology.Instances.Matrix
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Diagonal.Positive
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Unitary
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.UpperTriangular.Positive
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.UpperUnitriangular.Basic

import Mathlib.Topology.Algebra.Group.Matrix
import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Topology.Maps.Proper.Basic
import TauCeti.Analysis.Matrix.LDL
import TauCeti.Analysis.Matrix.Triangular
import TauCeti.LinearAlgebra.Matrix.Triangular
import TauCeti.Topology.Algebra.UnitaryGroup
import TauCeti.Topology.Algebra.Matrix.GeneralLinearGroup.UpperTriangular.Positive

/-!
# The Iwasawa decomposition of `GL n ℝ` and `GL n ℂ`

Let `𝕜` be `ℝ` or `ℂ`, or more generally any `RCLike` field. Every invertible matrix `g` over `𝕜`
factors uniquely as `g = k a u`, with `k` unitary, `a` diagonal with positive real diagonal
entries, and `u` upper unitriangular, and the three factors depend continuously on `g`. This is
the Iwasawa decomposition `G = K A N` of the real reductive group `G = GL n 𝕜`, with maximal
compact subgroup `K = U(n)` (the orthogonal group `O(n)` when `𝕜 = ℝ`), `A` the positive real
diagonal matrices, and `N` the unipotent radical of the upper triangular Borel subgroup. In matrix
language it is the Gram-Schmidt process, or the `QR` factorization of an invertible matrix with
the triangular factor `R = a u` normalized to have a positive diagonal.

The three factors are the subgroups `unitarySubgroup (GL (Fin n) 𝕜)`,
`TauCeti.posDiagonalSubgroup (Fin n) ℝ` and `TauCeti.upperUnitriangularGroup (Fin n) 𝕜`. The factor
`A` consists of real matrices, which act on `𝕜ⁿ` through
`Matrix.GeneralLinearGroup.map (algebraMap ℝ 𝕜)`; for `𝕜 = ℝ` this map is the identity. The
homeomorphism `TauCeti.iwasawaHomeomorph 𝕜 n : K × A × N ≃ₜ GL n 𝕜` is given by multiplication. The
statement here is topological; the real smooth diffeomorphism is supplied in
`TauCeti/Geometry/Lie/Iwasawa.lean`.

## The construction

* **Existence.** The Gram matrix `gᴴ g` is positive definite, so its Cholesky factorization
  (`Matrix.PosDef.exists_isUpperTriangular_conjTranspose_mul_self_eq`, built from the LDL
  decomposition) gives `b` upper triangular with positive diagonal and `bᴴ b = gᴴ g`. Then
  `k = g b⁻¹` is unitary and `g = k b`.
* **Uniqueness.** If `k b = k' b'` with `k, k'` unitary and `b, b'` upper triangular with positive
  diagonal, then `k'⁻¹ k = b' b⁻¹` is unitary and upper triangular with positive diagonal, hence
  the identity (`Matrix.IsUpperTriangular.eq_one_of_mem_unitaryGroup`). An upper triangular `b`
  with positive diagonal is `a u` for exactly one pair: `a` is its diagonal.
* **Continuity.** The unitary factor is a map into the compact group `K` whose graph is closed: `k`
  is the unitary factor of `g` exactly when `k⁻¹ g` is upper triangular with nonnegative diagonal,
  a closed condition. A map into a compact space with closed graph is continuous
  (`continuous_of_isClosed_graph`). The other two factors are read off `k⁻¹ g` continuously.

## Main definitions

* `TauCeti.iwasawaHomeomorph 𝕜 n`: the Iwasawa decomposition, the homeomorphism
  `U(n) × A × N ≃ₜ GL n 𝕜` sending `(k, a, u)` to `k a u`.

## Main results

* `TauCeti.iwasawaHomeomorph_apply`: the decomposition multiplies the three factors.
* `TauCeti.iwasawaHomeomorph_symm_unitary_eq_iff`: the unitary factor is characterized by the
  positive upper-triangular remainder.
* `Matrix.GeneralLinearGroup.iwasawaUnitaryFactor`: the unitary factor as an element of the
  unitary group, continuous and equivariant for left multiplication by unitary matrices.
* `Matrix.GeneralLinearGroup.iwasawaUnitaryFactor_eq_iff`: the unitary factor is the unitary `U`
  for which `star U * g` is upper triangular with positive diagonal
  (`Matrix.GeneralLinearGroup.star_iwasawaUnitaryFactor_mul_isUpperTriangular`,
  `Matrix.GeneralLinearGroup.star_iwasawaUnitaryFactor_mul_diag_pos`).
* `Matrix.GeneralLinearGroup.iwasawaUnitaryFactor_eq_iwasawaUnitaryFactor_iff`: `g` and `h` have
  the same unitary factor exactly when `h⁻¹ * g` is upper triangular with positive diagonal.
* `Matrix.GeneralLinearGroup.col_zero_eq_smul_col_zero_iwasawaUnitaryFactor`,
  `Matrix.GeneralLinearGroup.col_zero_iwasawaUnitaryFactor`: the first column of `g` is a positive
  multiple of the first column of the unitary factor, and equal to it when it has Hermitian length
  one, `star c ⬝ᵥ c = 1` (not length for the sup norm of the column type).
* `TauCeti.coe_iwasawaHomeomorph_symm_diagonal`,
  `TauCeti.coe_iwasawaHomeomorph_symm_unitriangular`: formulas for the other two factors.
* `Matrix.GeneralLinearGroup.existsUnique_iwasawa`: every invertible matrix over `𝕜` is uniquely
  `k a u`.

## References

* A. W. Knapp, *Lie Groups Beyond an Introduction*, second edition, Birkhäuser, 2002,
  Section VI.4 (the Iwasawa decomposition).
* R. A. Horn and C. R. Johnson, *Matrix Analysis*, second edition, Cambridge University Press,
  2013, Section 2.1 (the `QR` factorization).
-/

public section

noncomputable section

open Matrix
open scoped ComplexOrder

namespace TauCeti

variable {𝕜 : Type*} [RCLike 𝕜] {n : ℕ}

/-- The matrix of a positive real diagonal matrix, read over `𝕜`. -/
private theorem coe_map_of_mem_posDiagonalSubgroup {a : GL (Fin n) ℝ}
    {d : Fin n → ℝ} (ha : (a : Matrix (Fin n) (Fin n) ℝ) = diagonal d) :
    (GeneralLinearGroup.map (algebraMap ℝ 𝕜) a : Matrix (Fin n) (Fin n) 𝕜) =
      diagonal fun i => (d i : 𝕜) := by
  rw [GeneralLinearGroup.val_map_apply, ha, diagonal_map (map_zero _)]

/-- A positive real diagonal matrix times an upper unitriangular matrix belongs to the
positive upper-triangular group. -/
private theorem map_mul_mem_posUpperTriangularGroup {a : GL (Fin n) ℝ} {u : GL (Fin n) 𝕜}
    (ha : a ∈ posDiagonalSubgroup (Fin n) ℝ) (hu : u ∈ upperUnitriangularGroup (Fin n) 𝕜) :
    GeneralLinearGroup.map (algebraMap ℝ 𝕜) a * u ∈ posUpperTriangularGroup (Fin n) 𝕜 :=
  (posUpperTriangularGroup (Fin n) 𝕜).mul_mem
    (posDiagonalSubgroup_map_le_posUpperTriangularGroup (Subgroup.mem_map.mpr ⟨a, ha, rfl⟩))
    (upperUnitriangularGroup_le_posUpperTriangularGroup hu)

/-- **`K ∩ A N = 1`, in the form of uniqueness of the unitary factor**: if `k b = k' b'` with `k`,
`k'` unitary and `b`, `b'` upper triangular with positive diagonal, then `k = k'`. -/
private theorem eq_of_mul_eq_mul {k k' b b' : GL (Fin n) 𝕜}
    (hk : k ∈ unitarySubgroup (GL (Fin n) 𝕜)) (hk' : k' ∈ unitarySubgroup (GL (Fin n) 𝕜))
    (hb : b ∈ posUpperTriangularGroup (Fin n) 𝕜)
    (hb' : b' ∈ posUpperTriangularGroup (Fin n) 𝕜) (h : k * b = k' * b') : k = k' := by
  have hw : k'⁻¹ * k = b' * b⁻¹ := by
    rw [eq_mul_inv_iff_mul_eq, mul_assoc, h, inv_mul_cancel_left]
  have hwU : ((k'⁻¹ * k : GL (Fin n) 𝕜) : Matrix (Fin n) (Fin n) 𝕜) ∈ unitaryGroup (Fin n) 𝕜 :=
    mem_unitarySubgroup_GL_iff_mem_unitaryGroup.1 (mul_mem (inv_mem hk') hk)
  have hwT : k'⁻¹ * k ∈ posUpperTriangularGroup (Fin n) 𝕜 := by
    rw [hw]
    exact mul_mem hb' (inv_mem hb)
  have hwT' := PosUpperTriangularGroup.mem_iff.mp hwT
  exact (inv_mul_eq_one.1 (Units.ext ((hwT'.1.eq_one_of_mem_unitaryGroup hwU hwT'.2).trans
    Units.val_one.symm))).symm

/-- **Existence of the Iwasawa decomposition**: every invertible matrix `g` is a unitary matrix
times an upper triangular matrix `b` with positive diagonal. Here `b` is chosen with
`bᴴ b = gᴴ g`, and then `g b⁻¹` is unitary. -/
private theorem exists_mem_unitarySubgroup_mul_mem_posUpperTriangularGroup (g : GL (Fin n) 𝕜) :
    ∃ k ∈ unitarySubgroup (GL (Fin n) 𝕜),
      k⁻¹ * g ∈ posUpperTriangularGroup (Fin n) 𝕜 := by
  obtain ⟨B, hBT, hBpos, hBB⟩ :=
    (PosDef.conjTranspose_mul_self _ (mulVec_injective_of_isUnit g.isUnit)
      ).exists_isUpperTriangular_conjTranspose_mul_self_eq
  -- `B` is invertible, being triangular with nonzero diagonal
  have hBu : IsUnit B := by
    rw [isUnit_iff_isUnit_det, isUnit_iff_ne_zero, hBT.det_ne_zero_iff]
    exact fun i => (hBpos i).ne'
  obtain ⟨b, rfl⟩ := hBu
  refine ⟨g * b⁻¹, ?_, ?_⟩
  · -- `(g b⁻¹)ᴴ (g b⁻¹) = b⁻ᴴ (bᴴ b) b⁻¹ = (b b⁻¹)ᴴ (b b⁻¹) = 1`
    rw [mem_unitarySubgroup_GL_iff_mem_unitaryGroup, mem_unitaryGroup_iff', star_eq_conjTranspose]
    calc ((g * b⁻¹ : GL (Fin n) 𝕜) : Matrix (Fin n) (Fin n) 𝕜)ᴴ * (g * b⁻¹ : GL (Fin n) 𝕜)
        = ((b⁻¹ : GL (Fin n) 𝕜) : Matrix (Fin n) (Fin n) 𝕜)ᴴ *
            ((g : Matrix (Fin n) (Fin n) 𝕜)ᴴ * g) * (b⁻¹ : GL (Fin n) 𝕜) := by
          simp only [Units.val_mul, conjTranspose_mul, Matrix.mul_assoc]
      _ = ((b * b⁻¹ : GL (Fin n) 𝕜) : Matrix (Fin n) (Fin n) 𝕜)ᴴ *
            (b * b⁻¹ : GL (Fin n) 𝕜) := by
          rw [← hBB]
          simp only [Units.val_mul, conjTranspose_mul, Matrix.mul_assoc]
      _ = 1 := by rw [mul_inv_cancel, Units.val_one, conjTranspose_one, Matrix.one_mul]
  · rw [_root_.mul_inv_rev, inv_inv, inv_mul_cancel_right]
    exact PosUpperTriangularGroup.mem_iff.mpr ⟨hBT, hBpos⟩

/-- The unitary factor `k` of the Iwasawa decomposition `g = k a u`. -/
private def iwasawaUnitary (g : GL (Fin n) 𝕜) : GL (Fin n) 𝕜 :=
  (exists_mem_unitarySubgroup_mul_mem_posUpperTriangularGroup g).choose

private theorem iwasawaUnitary_mem (g : GL (Fin n) 𝕜) :
    iwasawaUnitary g ∈ unitarySubgroup (GL (Fin n) 𝕜) :=
  (exists_mem_unitarySubgroup_mul_mem_posUpperTriangularGroup g).choose_spec.1

/-- The triangular factor `a u = k⁻¹ g` of the Iwasawa decomposition `g = k a u`. -/
private def iwasawaTriangular (g : GL (Fin n) 𝕜) : GL (Fin n) 𝕜 :=
  (iwasawaUnitary g)⁻¹ * g

private theorem iwasawaTriangular_mem (g : GL (Fin n) 𝕜) :
    iwasawaTriangular g ∈ posUpperTriangularGroup (Fin n) 𝕜 :=
  (exists_mem_unitarySubgroup_mul_mem_posUpperTriangularGroup g).choose_spec.2

/-- The diagonal of the triangular Iwasawa remainder is positive. -/
private theorem iwasawaTriangular_diag_pos (g : GL (Fin n) 𝕜) (i : Fin n) :
    0 < (iwasawaTriangular g : Matrix (Fin n) (Fin n) 𝕜) i i :=
  (PosUpperTriangularGroup.mem_iff.mp (iwasawaTriangular_mem g)).2 i

/-- The unitary factor of `k b` is `k`, for `k` unitary and `b` upper triangular with positive
diagonal. -/
private theorem iwasawaUnitary_mul {k b : GL (Fin n) 𝕜} (hk : k ∈ unitarySubgroup (GL (Fin n) 𝕜))
    (hb : b ∈ posUpperTriangularGroup (Fin n) 𝕜) : iwasawaUnitary (k * b) = k :=
  eq_of_mul_eq_mul (iwasawaUnitary_mem _) hk (iwasawaTriangular_mem _) hb <| by
    rw [iwasawaTriangular, mul_inv_cancel_left]

/-- The positive diagonal factor `a` of the Iwasawa decomposition `g = k a u`: the real parts of
the diagonal entries of `k⁻¹ g`, which are positive reals. -/
private def iwasawaDiagonal (g : GL (Fin n) 𝕜) : GL (Fin n) ℝ :=
  diagGL fun i => Units.mk0 (RCLike.re ((iwasawaTriangular g : Matrix (Fin n) (Fin n) 𝕜) i i))
    (RCLike.pos_iff.1 (iwasawaTriangular_diag_pos g i)).1.ne'

private theorem coe_iwasawaDiagonal (g : GL (Fin n) 𝕜) :
    (iwasawaDiagonal g : Matrix (Fin n) (Fin n) ℝ) =
      diagonal fun i => RCLike.re ((iwasawaTriangular g : Matrix (Fin n) (Fin n) 𝕜) i i) := by
  simp [iwasawaDiagonal]

private theorem coe_inv_iwasawaDiagonal (g : GL (Fin n) 𝕜) :
    (((iwasawaDiagonal g)⁻¹ : GL (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ) =
      diagonal fun i => (RCLike.re ((iwasawaTriangular g : Matrix (Fin n) (Fin n) 𝕜) i i))⁻¹ :=
  coe_inv_of_coe_eq_diagonal (coe_iwasawaDiagonal g)

private theorem iwasawaDiagonal_mem (g : GL (Fin n) 𝕜) :
    iwasawaDiagonal g ∈ posDiagonalSubgroup (Fin n) ℝ :=
  mem_posDiagonalSubgroup_iff.2 ⟨_,
    fun i ↦ (RCLike.pos_iff.1
      (iwasawaTriangular_diag_pos g i)).1,
    coe_iwasawaDiagonal g⟩

/-- Read over `𝕜`, the positive diagonal factor of `g` is the diagonal of `k⁻¹ g`. -/
private theorem coe_map_iwasawaDiagonal (g : GL (Fin n) 𝕜) :
    (GeneralLinearGroup.map (algebraMap ℝ 𝕜) (iwasawaDiagonal g) : Matrix (Fin n) (Fin n) 𝕜) =
      diagonal fun i => (iwasawaTriangular g : Matrix (Fin n) (Fin n) 𝕜) i i := by
  rw [coe_map_of_mem_posDiagonalSubgroup (coe_iwasawaDiagonal g)]
  congr 1
  funext i
  obtain ⟨x, -, hx⟩ := RCLike.pos_iff_exists_ofReal.1
    (iwasawaTriangular_diag_pos g i)
  rw [← hx, RCLike.ofReal_re]

/-- The upper unitriangular factor `a⁻¹ k⁻¹ g` of the Iwasawa decomposition `g = k a u`. -/
private def iwasawaUnitriangular (g : GL (Fin n) 𝕜) : GL (Fin n) 𝕜 :=
  (GeneralLinearGroup.map (algebraMap ℝ 𝕜) (iwasawaDiagonal g))⁻¹ * iwasawaTriangular g

private theorem iwasawaUnitriangular_mem (g : GL (Fin n) 𝕜) :
    iwasawaUnitriangular g ∈ upperUnitriangularGroup (Fin n) 𝕜 := by
  have htri := (PosUpperTriangularGroup.mem_iff.mp (iwasawaTriangular_mem g)).1
  rw [UpperUnitriangularGroup.mem_iff, iwasawaUnitriangular, Units.val_mul,
    coe_inv_of_coe_eq_diagonal (coe_map_iwasawaDiagonal g), isUpperUnitriangular_def]
  refine ⟨fun i j hji => ?_, fun i => ?_⟩
  · rw [diagonal_mul, htri hji, mul_zero]
  · rw [diagonal_mul, Pi.inv_apply, inv_mul_cancel₀ (iwasawaTriangular_diag_pos g i).ne']

/-- The Iwasawa factors of `k a u` are `k`, `a` and `u`. -/
private theorem iwasawa_mul_mul {k : GL (Fin n) 𝕜} {a : GL (Fin n) ℝ} {u : GL (Fin n) 𝕜}
    (hk : k ∈ unitarySubgroup (GL (Fin n) 𝕜)) (ha : a ∈ posDiagonalSubgroup (Fin n) ℝ)
    (hu : u ∈ upperUnitriangularGroup (Fin n) 𝕜) :
    iwasawaUnitary (k * GeneralLinearGroup.map (algebraMap ℝ 𝕜) a * u) = k ∧
      iwasawaDiagonal (k * GeneralLinearGroup.map (algebraMap ℝ 𝕜) a * u) = a ∧
      iwasawaUnitriangular (k * GeneralLinearGroup.map (algebraMap ℝ 𝕜) a * u) = u := by
  have hK : iwasawaUnitary (k * GeneralLinearGroup.map (algebraMap ℝ 𝕜) a * u) = k := by
    rw [mul_assoc]
    exact iwasawaUnitary_mul hk (map_mul_mem_posUpperTriangularGroup ha hu)
  have hT : iwasawaTriangular (k * GeneralLinearGroup.map (algebraMap ℝ 𝕜) a * u) =
      GeneralLinearGroup.map (algebraMap ℝ 𝕜) a * u := by
    rw [iwasawaTriangular, hK, mul_assoc, inv_mul_cancel_left]
  obtain ⟨d, -, had⟩ := mem_posDiagonalSubgroup_iff.1 ha
  have hA : iwasawaDiagonal (k * GeneralLinearGroup.map (algebraMap ℝ 𝕜) a * u) = a := by
    refine Units.ext ?_
    rw [coe_iwasawaDiagonal, hT, had, Units.val_mul, coe_map_of_mem_posDiagonalSubgroup had]
    congr 1
    funext i
    rw [diagonal_mul, (UpperUnitriangularGroup.mem_iff.1 hu).apply_diag, mul_one,
      RCLike.ofReal_re]
  refine ⟨hK, hA, ?_⟩
  rw [iwasawaUnitriangular, hA, hT, inv_mul_cancel_left]

/-- **The unitary factor depends continuously on `g`.** Its graph is closed, since `k` is the
unitary factor of `g` exactly when `k⁻¹ g` is upper triangular with nonnegative diagonal, and it
takes values in the compact group `K`. -/
private theorem continuous_iwasawaUnitary : Continuous (iwasawaUnitary (𝕜 := 𝕜) (n := n)) := by
  have : CompactSpace (unitarySubgroup (GL (Fin n) 𝕜)) :=
    isCompact_iff_compactSpace.1 GeneralLinearGroup.isCompact_unitarySubgroup
  let f : GL (Fin n) 𝕜 → unitarySubgroup (GL (Fin n) 𝕜) :=
    fun g => ⟨iwasawaUnitary g, iwasawaUnitary_mem g⟩
  have hgraph : f.graph = (fun p : GL (Fin n) 𝕜 × unitarySubgroup (GL (Fin n) 𝕜) ↦
      (p.2 : GL (Fin n) 𝕜)⁻¹ * p.1) ⁻¹'
        (posUpperTriangularGroup (Fin n) 𝕜 : Set (GL (Fin n) 𝕜)) := by
    ext ⟨g, x⟩
    simp only [Function.mem_graph, Set.mem_preimage, SetLike.mem_coe]
    constructor
    · rintro rfl
      exact iwasawaTriangular_mem g
    · intro hx
      apply Subtype.ext
      have h := iwasawaUnitary_mul x.property hx
      rwa [mul_inv_cancel_left] at h
  have hclosed : IsClosed f.graph := by
    rw [hgraph]
    exact (isClosed_posUpperTriangularGroup (Fin n) 𝕜).preimage
      ((continuous_subtypeVal.comp continuous_snd).inv.mul continuous_fst)
  exact continuous_subtypeVal.comp (continuous_of_isClosed_graph hclosed)

variable (𝕜 n) in
/-- **The Iwasawa decomposition of `GL n 𝕜`**, for `𝕜 = ℝ` or `ℂ`. Multiplication
`(k, a, u) ↦ k a u` is a homeomorphism from the product of the unitary group (the orthogonal
group when `𝕜 = ℝ`), the positive real diagonal subgroup and the upper unitriangular group onto
`GL n 𝕜`. The real diagonal factor acts through `Matrix.GeneralLinearGroup.map (algebraMap ℝ 𝕜)`.
-/
def iwasawaHomeomorph :
    unitarySubgroup (GL (Fin n) 𝕜) × posDiagonalSubgroup (Fin n) ℝ ×
        upperUnitriangularGroup (Fin n) 𝕜 ≃ₜ GL (Fin n) 𝕜 where
  toFun x := (x.1 : GL (Fin n) 𝕜) *
    GeneralLinearGroup.map (algebraMap ℝ 𝕜) (x.2.1 : GL (Fin n) ℝ) * (x.2.2 : GL (Fin n) 𝕜)
  invFun g := (⟨iwasawaUnitary g, iwasawaUnitary_mem g⟩,
    ⟨iwasawaDiagonal g, iwasawaDiagonal_mem g⟩,
    ⟨iwasawaUnitriangular g, iwasawaUnitriangular_mem g⟩)
  left_inv := by
    rintro ⟨⟨k, hk⟩, ⟨a, ha⟩, ⟨u, hu⟩⟩
    obtain ⟨hK, hA, hU⟩ := iwasawa_mul_mul hk ha hu
    -- `invFun` produces the three factors of its argument, here `k * a * u`
    exact Prod.ext (Subtype.ext hK) (Prod.ext (Subtype.ext hA) (Subtype.ext hU))
  right_inv g := by
    -- `toFun` multiplies the three factors that `invFun` produces, as elements of `GL n 𝕜`
    change iwasawaUnitary g * GeneralLinearGroup.map (algebraMap ℝ 𝕜) (iwasawaDiagonal g) *
      iwasawaUnitriangular g = g
    rw [iwasawaUnitriangular, mul_assoc, mul_inv_cancel_left, iwasawaTriangular,
      mul_inv_cancel_left]
  continuous_toFun := by
    have := (RCLike.continuous_ofReal (K := 𝕜)).generalLinearGroup_map (n := Fin n)
    fun_prop
  continuous_invFun := by
    have hK := continuous_iwasawaUnitary (𝕜 := 𝕜) (n := n)
    have hT : Continuous (iwasawaTriangular (𝕜 := 𝕜) (n := n)) := hK.inv.mul continuous_id
    have hdiag (i : Fin n) : Continuous fun g : GL (Fin n) 𝕜 =>
        RCLike.re ((iwasawaTriangular g : Matrix (Fin n) (Fin n) 𝕜) i i) :=
      RCLike.continuous_re.comp ((Units.continuous_val.comp hT).matrix_elem i i)
    have hA : Continuous (iwasawaDiagonal (𝕜 := 𝕜) (n := n)) :=
      Units.continuous_iff.2
        ⟨((continuous_pi hdiag).matrix_diagonal).congr fun g => (coe_iwasawaDiagonal g).symm,
          ((continuous_pi fun i => (hdiag i).inv₀ fun g =>
            (RCLike.pos_iff.1
              (iwasawaTriangular_diag_pos g i)).1.ne').matrix_diagonal).congr
            fun g => (coe_inv_iwasawaDiagonal g).symm⟩
    have hU : Continuous (iwasawaUnitriangular (𝕜 := 𝕜) (n := n)) :=
      (((RCLike.continuous_ofReal (K := 𝕜)).generalLinearGroup_map (n := Fin n)).comp hA).inv.mul
        hT
    exact (hK.subtype_mk _).prodMk ((hA.subtype_mk _).prodMk (hU.subtype_mk _))

/-- The Iwasawa decomposition multiplies its three factors. -/
@[simp]
theorem iwasawaHomeomorph_apply
    (x : unitarySubgroup (GL (Fin n) 𝕜) × posDiagonalSubgroup (Fin n) ℝ ×
      upperUnitriangularGroup (Fin n) 𝕜) :
    iwasawaHomeomorph 𝕜 n x = (x.1 : GL (Fin n) 𝕜) *
      GeneralLinearGroup.map (algebraMap ℝ 𝕜) (x.2.1 : GL (Fin n) ℝ) * (x.2.2 : GL (Fin n) 𝕜) :=
  (rfl)

private lemma iwasawaHomeomorph_symm_apply (g : GL (Fin n) 𝕜) :
    (iwasawaHomeomorph 𝕜 n).symm g =
      (⟨iwasawaUnitary g, iwasawaUnitary_mem g⟩,
        ⟨iwasawaDiagonal g, iwasawaDiagonal_mem g⟩,
        ⟨iwasawaUnitriangular g, iwasawaUnitriangular_mem g⟩) := by
  -- This is the accessor for the inverse function defined by `iwasawaHomeomorph`; the
  -- `Homeomorph.symm` application reduces directly to that defining tuple of subgroup elements.
  rfl

/-- The unitary factor is characterized by the positive upper-triangular remainder. -/
theorem iwasawaHomeomorph_symm_unitary_eq_iff (g k : GL (Fin n) 𝕜)
    (hk : k ∈ unitarySubgroup (GL (Fin n) 𝕜)) :
    (((iwasawaHomeomorph 𝕜 n).symm g).1 : GL (Fin n) 𝕜) = k ↔
      ((k⁻¹ * g : GL (Fin n) 𝕜) : Matrix (Fin n) (Fin n) 𝕜).IsUpperTriangular ∧
        ∀ i, 0 < ((k⁻¹ * g : GL (Fin n) 𝕜) : Matrix (Fin n) (Fin n) 𝕜) i i := by
  rw [iwasawaHomeomorph_symm_apply]
  constructor
  · rintro rfl
    exact ⟨(PosUpperTriangularGroup.mem_iff.mp (iwasawaTriangular_mem g)).1,
      iwasawaTriangular_diag_pos g⟩
  · intro hb
    simpa only [mul_inv_cancel_left] using
      (iwasawaUnitary_mul (k := k) (b := k⁻¹ * g) hk
        (PosUpperTriangularGroup.mem_iff.mpr hb))

/-- The unitary Iwasawa factor is equivariant for left multiplication by unitary matrices: the
unitary factor of `k * g` is `k` times the unitary factor of `g`. -/
private theorem iwasawaHomeomorph_symm_mul_fst {k : GL (Fin n) 𝕜}
    (hk : k ∈ unitarySubgroup (GL (Fin n) 𝕜)) (g : GL (Fin n) 𝕜) :
    (((iwasawaHomeomorph 𝕜 n).symm (k * g)).1 : GL (Fin n) 𝕜) =
      k * ((iwasawaHomeomorph 𝕜 n).symm g).1 := by
  have hK := ((iwasawaHomeomorph 𝕜 n).symm g).1.property
  rw [iwasawaHomeomorph_symm_unitary_eq_iff _ _ (mul_mem hk hK), _root_.mul_inv_rev, mul_assoc,
    inv_mul_cancel_left]
  exact (iwasawaHomeomorph_symm_unitary_eq_iff g _ hK).mp rfl

/-- The real diagonal factor consists of the real parts of the triangular remainder's diagonal. -/
theorem coe_iwasawaHomeomorph_symm_diagonal (g : GL (Fin n) 𝕜) :
    ((((iwasawaHomeomorph 𝕜 n).symm g).2.1 : GL (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ) =
      diagonal (fun i ↦ RCLike.re
        (Units.val ((((iwasawaHomeomorph 𝕜 n).symm g).1 : GL (Fin n) 𝕜)⁻¹ * g) i i)) := by
  rw [iwasawaHomeomorph_symm_apply]
  exact coe_iwasawaDiagonal g

/-- The unitriangular factor is the triangular remainder divided on the left by its diagonal. -/
theorem coe_iwasawaHomeomorph_symm_unitriangular (g : GL (Fin n) 𝕜) :
    (((iwasawaHomeomorph 𝕜 n).symm g).2.2 : GL (Fin n) 𝕜) =
      (GeneralLinearGroup.map (algebraMap ℝ 𝕜)
        (((iwasawaHomeomorph 𝕜 n).symm g).2.1 : GL (Fin n) ℝ))⁻¹ *
          ((((iwasawaHomeomorph 𝕜 n).symm g).1 : GL (Fin n) 𝕜)⁻¹ * g) := by
  rw [iwasawaHomeomorph_symm_apply]
  simp only [iwasawaUnitriangular, iwasawaTriangular]

end TauCeti

namespace Matrix.GeneralLinearGroup

open TauCeti

/-- **Every invertible matrix over `𝕜 = ℝ` or `ℂ` is uniquely `k a u`**, with `k` unitary, `a`
real diagonal with positive diagonal entries and `u` upper unitriangular. -/
theorem existsUnique_iwasawa {𝕜 : Type*} [RCLike 𝕜] {n : ℕ} (g : GL (Fin n) 𝕜) :
    ∃! x : unitarySubgroup (GL (Fin n) 𝕜) × posDiagonalSubgroup (Fin n) ℝ ×
        upperUnitriangularGroup (Fin n) 𝕜,
      (x.1 : GL (Fin n) 𝕜) * map (algebraMap ℝ 𝕜) (x.2.1 : GL (Fin n) ℝ) *
        (x.2.2 : GL (Fin n) 𝕜) = g :=
  (iwasawaHomeomorph 𝕜 n).bijective.existsUnique g

variable {𝕜 : Type*} [RCLike 𝕜] {n : ℕ}

/-- The **unitary Iwasawa factor** of an invertible matrix `g`, the first factor of
`TauCeti.iwasawaHomeomorph`, as an element of the unitary group (the orthogonal group when
`𝕜 = ℝ`). Its columns are the Gram–Schmidt orthonormalisation of the columns of `g`. -/
def iwasawaUnitaryFactor (g : GL (Fin n) 𝕜) : unitaryGroup (Fin n) 𝕜 :=
  unitarySubgroupUnitsEquiv ((iwasawaHomeomorph 𝕜 n).symm g).1

theorem coe_iwasawaUnitaryFactor (g : GL (Fin n) 𝕜) :
    (g.iwasawaUnitaryFactor : Matrix (Fin n) (Fin n) 𝕜) =
      ((((iwasawaHomeomorph 𝕜 n).symm g).1 : GL (Fin n) 𝕜) : Matrix (Fin n) (Fin n) 𝕜) :=
  (rfl)

/-- The unitary Iwasawa factor depends continuously on the matrix. -/
theorem continuous_iwasawaUnitaryFactor :
    Continuous (iwasawaUnitaryFactor (𝕜 := 𝕜) (n := n)) :=
  ((unitarySubgroupUnitsHomeomorph (Matrix (Fin n) (Fin n) 𝕜)).continuous.comp
    (continuous_fst.comp (iwasawaHomeomorph 𝕜 n).symm.continuous)).congr fun _ ↦
      unitarySubgroupUnitsHomeomorph_apply _

/-- The unitary Iwasawa factor is equivariant for left multiplication by unitary matrices. -/
theorem iwasawaUnitaryFactor_toUnits_mul (g : GL (Fin n) 𝕜) (A : unitaryGroup (Fin n) 𝕜) :
    iwasawaUnitaryFactor (Unitary.toUnits A * g) = A * g.iwasawaUnitaryFactor := by
  have hA : Unitary.toUnits A ∈ unitarySubgroup (GL (Fin n) 𝕜) :=
    mem_unitarySubgroup_GL_iff_mem_unitaryGroup.mpr (by simp)
  refine Subtype.ext ?_
  rw [coe_iwasawaUnitaryFactor, iwasawaHomeomorph_symm_mul_fst hA, Units.val_mul,
    Unitary.val_toUnits_apply, Submonoid.coe_mul, coe_iwasawaUnitaryFactor]

/-- **Characterization of the unitary Iwasawa factor.** The unitary Iwasawa factor of `g` is the
unitary matrix `U` for which the remainder `star U * g` is upper triangular with positive
diagonal. -/
theorem iwasawaUnitaryFactor_eq_iff (g : GL (Fin n) 𝕜) (U : unitaryGroup (Fin n) 𝕜) :
    g.iwasawaUnitaryFactor = U ↔
      (star (U : Matrix (Fin n) (Fin n) 𝕜) * g).IsUpperTriangular ∧
        ∀ i, 0 < (star (U : Matrix (Fin n) (Fin n) 𝕜) * g) i i := by
  have hU : Unitary.toUnits U ∈ unitarySubgroup (GL (Fin n) 𝕜) :=
    mem_unitarySubgroup_GL_iff_mem_unitaryGroup.mpr (by simp)
  have hmul : (((Unitary.toUnits U)⁻¹ * g : GL (Fin n) 𝕜) : Matrix (Fin n) (Fin n) 𝕜) =
      star (U : Matrix (Fin n) (Fin n) 𝕜) * g := by
    rw [Units.val_mul, coe_inv_eq_star_of_mem_unitarySubgroup hU, Unitary.val_toUnits_apply]
  rw [← hmul, ← iwasawaHomeomorph_symm_unitary_eq_iff _ _ hU, ← Units.val_inj,
    Unitary.val_toUnits_apply, ← coe_iwasawaUnitaryFactor, Subtype.coe_inj]

/-- The remainder `star U * g` of `g` after its unitary Iwasawa factor `U` is upper triangular. -/
theorem star_iwasawaUnitaryFactor_mul_isUpperTriangular (g : GL (Fin n) 𝕜) :
    (star (g.iwasawaUnitaryFactor : Matrix (Fin n) (Fin n) 𝕜) * g).IsUpperTriangular :=
  ((iwasawaUnitaryFactor_eq_iff g _).mp rfl).1

/-- The remainder `star U * g` of `g` after its unitary Iwasawa factor `U` has positive
diagonal. -/
theorem star_iwasawaUnitaryFactor_mul_diag_pos (g : GL (Fin n) 𝕜) (i : Fin n) :
    0 < (star (g.iwasawaUnitaryFactor : Matrix (Fin n) (Fin n) 𝕜) * g) i i :=
  ((iwasawaUnitaryFactor_eq_iff g _).mp rfl).2 i

/-- Two invertible matrices `g` and `h` have the same unitary Iwasawa factor exactly when `h⁻¹ * g`
is upper triangular with positive diagonal. -/
theorem iwasawaUnitaryFactor_eq_iwasawaUnitaryFactor_iff (g h : GL (Fin n) 𝕜) :
    g.iwasawaUnitaryFactor = h.iwasawaUnitaryFactor ↔
      h⁻¹ * g ∈ posUpperTriangularGroup (Fin n) 𝕜 := by
  set k : GL (Fin n) 𝕜 := Unitary.toUnits h.iwasawaUnitaryFactor
  have hk : k ∈ unitarySubgroup (GL (Fin n) 𝕜) :=
    mem_unitarySubgroup_GL_iff_mem_unitaryGroup.mpr (by simp [k])
  have hcoe (x : GL (Fin n) 𝕜) : ((k⁻¹ * x : GL (Fin n) 𝕜) : Matrix (Fin n) (Fin n) 𝕜) =
      star (h.iwasawaUnitaryFactor : Matrix (Fin n) (Fin n) 𝕜) * x := by
    rw [Units.val_mul, coe_inv_eq_star_of_mem_unitarySubgroup hk, Unitary.val_toUnits_apply]
  -- The remainder `k⁻¹ * h` of `h` after its unitary factor `k` is positive upper triangular.
  have hb : k⁻¹ * h ∈ posUpperTriangularGroup (Fin n) 𝕜 := by
    rw [PosUpperTriangularGroup.mem_iff, hcoe]
    exact (iwasawaUnitaryFactor_eq_iff h _).mp rfl
  -- So `k⁻¹ * g` is positive upper triangular iff `(k⁻¹ * h)⁻¹ * (k⁻¹ * g) = h⁻¹ * g` is.
  rw [iwasawaUnitaryFactor_eq_iff, ← hcoe, ← PosUpperTriangularGroup.mem_iff,
    ← (posUpperTriangularGroup (Fin n) 𝕜).mul_mem_cancel_left (inv_mem hb), ← mul_assoc,
    _root_.mul_inv_rev, inv_inv, mul_inv_cancel_right]

/-- The first column of an invertible matrix `g` is the first column of its unitary Iwasawa factor
`U`, scaled by the top-left entry of the upper triangular remainder `star U * g`, which is positive
(`star_iwasawaUnitaryFactor_mul_diag_pos`). -/
theorem col_zero_eq_smul_col_zero_iwasawaUnitaryFactor {n : ℕ} (g : GL (Fin (n + 1)) 𝕜) :
    (g : Matrix (Fin (n + 1)) (Fin (n + 1)) 𝕜).col 0 =
      (star (g.iwasawaUnitaryFactor : Matrix (Fin (n + 1)) (Fin (n + 1)) 𝕜) * g) 0 0 •
        (g.iwasawaUnitaryFactor : Matrix (Fin (n + 1)) (Fin (n + 1)) 𝕜).col 0 := by
  set U := (g.iwasawaUnitaryFactor : Matrix (Fin (n + 1)) (Fin (n + 1)) 𝕜) with hUdef
  -- The remainder `b = star U * g` is upper triangular, so its first column is `b 0 0 • e₀`.
  have hT := star_iwasawaUnitaryFactor_mul_isUpperTriangular g
  rw [← hUdef] at hT
  have hcol : (star U * g).col 0 = (star U * g) 0 0 • Pi.single 0 1 := by
    ext i
    rcases eq_or_ne i 0 with rfl | hi
    · simp
    · rw [col_apply, Pi.smul_apply, Pi.single_eq_of_ne hi, smul_zero,
        hT (Fin.pos_iff_ne_zero.mpr hi)]
  -- Since `U` is unitary, `g = U * (star U * g)`.
  have hg : (g : Matrix (Fin (n + 1)) (Fin (n + 1)) 𝕜) = U * (star U * g) := by
    rw [← Matrix.mul_assoc, Unitary.mul_star_self_of_mem g.iwasawaUnitaryFactor.property,
      Matrix.one_mul]
  conv_lhs => rw [hg]
  rw [col_mul_eq_mulVec_col, hcol, mulVec_smul, mulVec_single_one]

/-- If the first column `c` of `g` has Hermitian length one, `star c ⬝ᵥ c = 1`, it is also the
first column of the unitary Iwasawa factor of `g`. In general the first column of `g` is a
positive multiple of that column, the first vector of the Gram–Schmidt process
(`col_zero_eq_smul_col_zero_iwasawaUnitaryFactor`, `star_iwasawaUnitaryFactor_mul_diag_pos`). -/
theorem col_zero_iwasawaUnitaryFactor {n : ℕ} (g : GL (Fin (n + 1)) 𝕜)
    (hg : star ((g : Matrix (Fin (n + 1)) (Fin (n + 1)) 𝕜).col 0) ⬝ᵥ
      (g : Matrix (Fin (n + 1)) (Fin (n + 1)) 𝕜).col 0 = 1) :
    (g.iwasawaUnitaryFactor : Matrix (Fin (n + 1)) (Fin (n + 1)) 𝕜).col 0 =
      (g : Matrix (Fin (n + 1)) (Fin (n + 1)) 𝕜).col 0 := by
  set U := (g.iwasawaUnitaryFactor : Matrix (Fin (n + 1)) (Fin (n + 1)) 𝕜) with hUdef
  -- The scaling factor is a positive real number `x`.
  have hpos := star_iwasawaUnitaryFactor_mul_diag_pos g 0
  rw [← hUdef] at hpos
  obtain ⟨x, hx, hxb⟩ := RCLike.pos_iff_exists_ofReal.mp hpos
  have hcol : (g : Matrix (Fin (n + 1)) (Fin (n + 1)) 𝕜).col 0 = (x : 𝕜) • U.col 0 := by
    rw [hxb]
    exact col_zero_eq_smul_col_zero_iwasawaUnitaryFactor g
  -- The first column of the unitary `U` is a unit vector.
  have hU : star (U.col 0) ⬝ᵥ U.col 0 = 1 := by
    have h : (star U * U) 0 0 = 1 := by
      rw [Unitary.star_mul_self_of_mem g.iwasawaUnitaryFactor.property, one_apply_eq]
    simpa [Matrix.mul_apply, dotProduct, Matrix.star_apply] using h
  -- So the squared length of `x • U.col 0` is `x * x`, which must be `1`.
  have hsq : star ((x : 𝕜) • U.col 0) ⬝ᵥ ((x : 𝕜) • U.col 0) = ((x * x : ℝ) : 𝕜) := by
    simp only [star_smul, smul_dotProduct, dotProduct_smul, hU, RCLike.star_def,
      RCLike.conj_ofReal, smul_eq_mul, mul_one, RCLike.ofReal_mul]
  have hxx : x * x = 1 := by
    rw [← hcol, hg] at hsq
    exact_mod_cast hsq.symm
  have hx1 : x = 1 := by nlinarith
  rw [hcol, hx1, RCLike.ofReal_one, one_smul]

end Matrix.GeneralLinearGroup

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
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.UpperUnitriangular.Basic

import Mathlib.Topology.Algebra.Group.Matrix
import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Topology.Maps.Proper.Basic
import TauCeti.Analysis.Matrix.LDL
import TauCeti.Analysis.Matrix.Triangular
import TauCeti.LinearAlgebra.Matrix.Triangular
import TauCeti.Topology.Algebra.UnitaryGroup
import TauCeti.Topology.Instances.Matrix

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
statement is topological: that the factors also depend smoothly on `g`, making the decomposition a
diffeomorphism, is not proved here.

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

/-- A matrix is upper triangular with positive diagonal: the shape of the factor `a u` of the
Iwasawa decomposition `k a u`. -/
private abbrev IsPosUpper (b : Matrix (Fin n) (Fin n) 𝕜) : Prop :=
  b.IsUpperTriangular ∧ ∀ i, 0 < b i i

private theorem IsPosUpper.mul {b c : Matrix (Fin n) (Fin n) 𝕜} (hb : IsPosUpper b)
    (hc : IsPosUpper c) : IsPosUpper (b * c) :=
  ⟨hb.1.mul hc.1, fun i => by
    rw [mul_apply_diag_of_isUpperTriangular hb.1 hc.1]
    exact mul_pos (hb.2 i) (hc.2 i)⟩

private theorem IsPosUpper.inv {b : GL (Fin n) 𝕜} (hb : IsPosUpper (b : Matrix (Fin n) (Fin n) 𝕜)) :
    IsPosUpper ((b⁻¹ : GL (Fin n) 𝕜) : Matrix (Fin n) (Fin n) 𝕜) := by
  let _ := b.invertible
  rw [coe_units_inv]
  refine ⟨blockTriangular_inv_of_blockTriangular hb.1, fun i => ?_⟩
  rw [eq_inv_of_mul_eq_one_left (inv_apply_diag_mul_of_isUpperTriangular hb.1 i)]
  exact RCLike.inv_pos.2 (hb.2 i)

/-- The matrix of a positive real diagonal matrix, read over `𝕜`. -/
private theorem coe_map_of_mem_posDiagonalSubgroup {a : GL (Fin n) ℝ}
    {d : Fin n → ℝ} (ha : (a : Matrix (Fin n) (Fin n) ℝ) = diagonal d) :
    (GeneralLinearGroup.map (algebraMap ℝ 𝕜) a : Matrix (Fin n) (Fin n) 𝕜) =
      diagonal fun i => (d i : 𝕜) := by
  rw [GeneralLinearGroup.val_map_apply, ha, diagonal_map (map_zero _)]

/-- A positive real diagonal matrix times an upper unitriangular matrix is upper triangular with
positive diagonal. -/
private theorem isPosUpper_map_mul {a : GL (Fin n) ℝ} {u : GL (Fin n) 𝕜}
    (ha : a ∈ posDiagonalSubgroup (Fin n) ℝ) (hu : u ∈ upperUnitriangularGroup (Fin n) 𝕜) :
    IsPosUpper ((GeneralLinearGroup.map (algebraMap ℝ 𝕜) a * u : GL (Fin n) 𝕜) :
      Matrix (Fin n) (Fin n) 𝕜) := by
  obtain ⟨d, hd, had⟩ := mem_posDiagonalSubgroup_iff.1 ha
  have hu' := UpperUnitriangularGroup.mem_iff.1 hu
  rw [Units.val_mul, coe_map_of_mem_posDiagonalSubgroup had]
  exact IsPosUpper.mul ⟨blockTriangular_diagonal _, fun i => by simpa using hd i⟩
    ⟨hu'.isUpperTriangular, fun i => by rw [hu'.apply_diag]; exact one_pos⟩

/-- **`K ∩ A N = 1`, in the form of uniqueness of the unitary factor**: if `k b = k' b'` with `k`,
`k'` unitary and `b`, `b'` upper triangular with positive diagonal, then `k = k'`. -/
private theorem eq_of_mul_eq_mul {k k' b b' : GL (Fin n) 𝕜}
    (hk : k ∈ unitarySubgroup (GL (Fin n) 𝕜)) (hk' : k' ∈ unitarySubgroup (GL (Fin n) 𝕜))
    (hb : IsPosUpper (b : Matrix (Fin n) (Fin n) 𝕜))
    (hb' : IsPosUpper (b' : Matrix (Fin n) (Fin n) 𝕜)) (h : k * b = k' * b') : k = k' := by
  have hw : k'⁻¹ * k = b' * b⁻¹ := by
    rw [eq_mul_inv_iff_mul_eq, mul_assoc, h, inv_mul_cancel_left]
  have hwU : ((k'⁻¹ * k : GL (Fin n) 𝕜) : Matrix (Fin n) (Fin n) 𝕜) ∈ unitaryGroup (Fin n) 𝕜 :=
    mem_unitarySubgroup_GL_iff_mem_unitaryGroup.1 (mul_mem (inv_mem hk') hk)
  have hwT : IsPosUpper ((k'⁻¹ * k : GL (Fin n) 𝕜) : Matrix (Fin n) (Fin n) 𝕜) := by
    rw [hw, Units.val_mul]
    exact hb'.mul hb.inv
  exact (inv_mul_eq_one.1 (Units.ext ((hwT.1.eq_one_of_mem_unitaryGroup hwU hwT.2).trans
    Units.val_one.symm))).symm

/-- **Existence of the Iwasawa decomposition**: every invertible matrix `g` is a unitary matrix
times an upper triangular matrix `b` with positive diagonal. Here `b` is chosen with
`bᴴ b = gᴴ g`, and then `g b⁻¹` is unitary. -/
private theorem exists_mem_unitarySubgroup_isPosUpper (g : GL (Fin n) 𝕜) :
    ∃ k ∈ unitarySubgroup (GL (Fin n) 𝕜),
      IsPosUpper ((k⁻¹ * g : GL (Fin n) 𝕜) : Matrix (Fin n) (Fin n) 𝕜) := by
  obtain ⟨B, hBT, hBpos, hBB⟩ :=
    (PosDef.conjTranspose_mul_self _ (mulVec_injective_of_isUnit g.isUnit)
      ).exists_isUpperTriangular_conjTranspose_mul_self_eq
  have hB : IsPosUpper B := ⟨hBT, hBpos⟩
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
    exact hB

/-- The unitary factor `k` of the Iwasawa decomposition `g = k a u`. -/
private def iwasawaUnitary (g : GL (Fin n) 𝕜) : GL (Fin n) 𝕜 :=
  (exists_mem_unitarySubgroup_isPosUpper g).choose

private theorem iwasawaUnitary_mem (g : GL (Fin n) 𝕜) :
    iwasawaUnitary g ∈ unitarySubgroup (GL (Fin n) 𝕜) :=
  (exists_mem_unitarySubgroup_isPosUpper g).choose_spec.1

/-- The triangular factor `a u = k⁻¹ g` of the Iwasawa decomposition `g = k a u`. -/
private def iwasawaTriangular (g : GL (Fin n) 𝕜) : GL (Fin n) 𝕜 :=
  (iwasawaUnitary g)⁻¹ * g

private theorem isPosUpper_iwasawaTriangular (g : GL (Fin n) 𝕜) :
    IsPosUpper (iwasawaTriangular g : Matrix (Fin n) (Fin n) 𝕜) :=
  (exists_mem_unitarySubgroup_isPosUpper g).choose_spec.2

/-- The unitary factor of `k b` is `k`, for `k` unitary and `b` upper triangular with positive
diagonal. -/
private theorem iwasawaUnitary_mul {k b : GL (Fin n) 𝕜} (hk : k ∈ unitarySubgroup (GL (Fin n) 𝕜))
    (hb : IsPosUpper (b : Matrix (Fin n) (Fin n) 𝕜)) : iwasawaUnitary (k * b) = k :=
  eq_of_mul_eq_mul (iwasawaUnitary_mem _) hk (isPosUpper_iwasawaTriangular _) hb <| by
    rw [iwasawaTriangular, mul_inv_cancel_left]

/-- The positive diagonal factor `a` of the Iwasawa decomposition `g = k a u`: the real parts of
the diagonal entries of `k⁻¹ g`, which are positive reals. -/
private def iwasawaDiagonal (g : GL (Fin n) 𝕜) : GL (Fin n) ℝ :=
  diagGL fun i => Units.mk0 (RCLike.re ((iwasawaTriangular g : Matrix (Fin n) (Fin n) 𝕜) i i))
    (RCLike.pos_iff.1 ((isPosUpper_iwasawaTriangular g).2 i)).1.ne'

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
    fun i => (RCLike.pos_iff.1 ((isPosUpper_iwasawaTriangular g).2 i)).1, coe_iwasawaDiagonal g⟩

/-- Read over `𝕜`, the positive diagonal factor of `g` is the diagonal of `k⁻¹ g`. -/
private theorem coe_map_iwasawaDiagonal (g : GL (Fin n) 𝕜) :
    (GeneralLinearGroup.map (algebraMap ℝ 𝕜) (iwasawaDiagonal g) : Matrix (Fin n) (Fin n) 𝕜) =
      diagonal fun i => (iwasawaTriangular g : Matrix (Fin n) (Fin n) 𝕜) i i := by
  rw [coe_map_of_mem_posDiagonalSubgroup (coe_iwasawaDiagonal g)]
  congr 1
  funext i
  obtain ⟨x, -, hx⟩ := RCLike.pos_iff_exists_ofReal.1 ((isPosUpper_iwasawaTriangular g).2 i)
  rw [← hx, RCLike.ofReal_re]

/-- The upper unitriangular factor `a⁻¹ k⁻¹ g` of the Iwasawa decomposition `g = k a u`. -/
private def iwasawaUnitriangular (g : GL (Fin n) 𝕜) : GL (Fin n) 𝕜 :=
  (GeneralLinearGroup.map (algebraMap ℝ 𝕜) (iwasawaDiagonal g))⁻¹ * iwasawaTriangular g

private theorem iwasawaUnitriangular_mem (g : GL (Fin n) 𝕜) :
    iwasawaUnitriangular g ∈ upperUnitriangularGroup (Fin n) 𝕜 := by
  have hb := isPosUpper_iwasawaTriangular g
  rw [UpperUnitriangularGroup.mem_iff, iwasawaUnitriangular, Units.val_mul,
    coe_inv_of_coe_eq_diagonal (coe_map_iwasawaDiagonal g), isUpperUnitriangular_def]
  refine ⟨fun i j hji => ?_, fun i => ?_⟩
  · rw [diagonal_mul, hb.1 hji, mul_zero]
  · rw [diagonal_mul, Pi.inv_apply, inv_mul_cancel₀ (hb.2 i).ne']

/-- The Iwasawa factors of `k a u` are `k`, `a` and `u`. -/
private theorem iwasawa_mul_mul {k : GL (Fin n) 𝕜} {a : GL (Fin n) ℝ} {u : GL (Fin n) 𝕜}
    (hk : k ∈ unitarySubgroup (GL (Fin n) 𝕜)) (ha : a ∈ posDiagonalSubgroup (Fin n) ℝ)
    (hu : u ∈ upperUnitriangularGroup (Fin n) 𝕜) :
    iwasawaUnitary (k * GeneralLinearGroup.map (algebraMap ℝ 𝕜) a * u) = k ∧
      iwasawaDiagonal (k * GeneralLinearGroup.map (algebraMap ℝ 𝕜) a * u) = a ∧
      iwasawaUnitriangular (k * GeneralLinearGroup.map (algebraMap ℝ 𝕜) a * u) = u := by
  have hK : iwasawaUnitary (k * GeneralLinearGroup.map (algebraMap ℝ 𝕜) a * u) = k := by
    rw [mul_assoc]
    exact iwasawaUnitary_mul hk (isPosUpper_map_mul ha hu)
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
  have hgraph : f.graph = (fun p : GL (Fin n) 𝕜 × unitarySubgroup (GL (Fin n) 𝕜) =>
      (((p.2 : GL (Fin n) 𝕜)⁻¹ * p.1 : GL (Fin n) 𝕜) : Matrix (Fin n) (Fin n) 𝕜)) ⁻¹'
        {M | M.IsUpperTriangular ∧ ∀ i, 0 ≤ M i i} := by
    ext ⟨g, x⟩
    simp only [Function.mem_graph, Set.mem_preimage, Set.mem_ofPred_eq]
    constructor
    · rintro rfl
      exact ⟨(isPosUpper_iwasawaTriangular g).1, fun i =>
        ((isPosUpper_iwasawaTriangular g).2 i).le⟩
    · rintro ⟨htri, hnonneg⟩
      refine Subtype.ext ?_
      -- `x⁻¹ g` is invertible, so its diagonal entries are nonzero, hence positive
      have hdiag := (htri.det_ne_zero_iff).1
        ((isUnit_iff_isUnit_det _).1 ((x : GL (Fin n) 𝕜)⁻¹ * g).isUnit).ne_zero
      have h := iwasawaUnitary_mul x.2 ⟨htri, fun i => (hnonneg i).lt_of_ne (hdiag i).symm⟩
      rwa [mul_inv_cancel_left] at h
  have hclosed : IsClosed f.graph := by
    rw [hgraph]
    have hset : IsClosed {M : Matrix (Fin n) (Fin n) 𝕜 | M.IsUpperTriangular ∧ ∀ i, 0 ≤ M i i} :=
      (isClosed_setOfPred_blockTriangular (b := id)).inter (s₂ := {M | ∀ i, 0 ≤ M i i}) <| by
        simp only [Set.ofPred_forall]
        exact isClosed_iInter fun i => isClosed_le continuous_const (continuous_id.matrix_elem i i)
    exact hset.preimage
      (Units.continuous_val.comp ((continuous_subtype_val.comp continuous_snd).inv.mul
        continuous_fst))
  exact continuous_subtype_val.comp (continuous_of_isClosed_graph hclosed)

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
            (RCLike.pos_iff.1 ((isPosUpper_iwasawaTriangular g).2 i)).1.ne').matrix_diagonal).congr
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

end Matrix.GeneralLinearGroup

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Group.Matrix
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.MaximalCompact

/-!
# The maximal compact subgroups of the real and complex special linear groups

For `𝕜 = ℝ` or `ℂ` and a finite index type `ι`, the unitary matrices of determinant one form a
compact subgroup of `SL ι 𝕜`: the preimage `(unitarySubgroup (GL ι 𝕜)).comap toGL` of the unitary
subgroup of `GL ι 𝕜` under the inclusion `toGL : SL ι 𝕜 →* GL ι 𝕜`. Over `ℝ` it is the special
orthogonal group `SO(n)`, and over `ℂ` the special unitary group `SU(n)`. It is the largest compact
subgroup of `SL ι 𝕜` up to conjugacy:

* **maximality**: a compact subgroup of `SL ι 𝕜` containing it is equal to it;
* **conjugacy**: every compact subgroup of `SL ι 𝕜` is conjugate into it by an element of
  `SL ι 𝕜`.

Together these say that the maximal compact subgroups of `SL ι 𝕜` are exactly the
`SL ι 𝕜`-conjugates of the determinant-one unitary matrices. In particular `SU(n)` is a maximal
compact subgroup of its complexification `SL(n, ℂ)`, and `SO(n)` is the maximal compact subgroup of
`SL(n, ℝ)` occurring in its Cartan, Iwasawa and `KAK` decompositions.

Both statements are deduced from their counterparts for `GL ι 𝕜` in
`TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.MaximalCompact`.

For maximality, the unitary factor `V` of the polar decomposition `g = P V` of a matrix of
determinant one again has determinant one
(`Matrix.GeneralLinearGroup.det_polarUnitary_of_det_eq_one`). So a compact subgroup of `SL ι 𝕜`
containing the determinant-one unitary matrices contains `V` along with `g`, and the polar-factor
argument `Matrix.GeneralLinearGroup.mem_unitarySubgroup_of_isCompact_of_polarUnitary_mem` shows
that `g` is unitary.

For conjugacy, Weyl's unitarian trick provides `h : GL ι 𝕜` conjugating a compact subgroup of
`SL ι 𝕜` into the unitary matrices
(`Matrix.GeneralLinearGroup.exists_conj_smul_le_unitarySubgroup`), but `h` need not have
determinant one. Write `h = c V g` with `c` a scalar, `V` unitary and `g` of determinant one
(`Matrix.GeneralLinearGroup.exists_scalar_mul_mul_toGL_eq`: for `V` the unitary factor of the polar
decomposition of `h`, the determinant of `V⁻¹ h` is the positive real number `‖det h‖`). Conjugation
by the central scalar `c` is trivial and conjugation by `V` preserves unitarity, so `g` already
conjugates the subgroup into the unitary matrices.

## Main results

* `Matrix.SpecialLinearGroup.isCompact_comap_unitarySubgroup`: the determinant-one unitary matrices
  form a compact subgroup of `SL ι 𝕜`.
* `Matrix.SpecialLinearGroup.eq_comap_unitarySubgroup_of_isCompact_of_le`: a compact subgroup of
  `SL ι 𝕜` containing every determinant-one unitary matrix consists of determinant-one unitary
  matrices.
* `Matrix.SpecialLinearGroup.maximal_isCompact_comap_unitarySubgroup`: the determinant-one unitary
  matrices form a maximal compact subgroup of `SL ι 𝕜`.
* `Matrix.SpecialLinearGroup.exists_conj_smul_le_comap_unitarySubgroup`: every compact subgroup of
  `SL ι 𝕜` is conjugate, by an element of `SL ι 𝕜`, into the determinant-one unitary matrices.
* `Matrix.SpecialLinearGroup.maximal_isCompact_iff`: the maximal compact subgroups of `SL ι 𝕜`
  are exactly the conjugates of the determinant-one unitary matrices.

## References

* A. W. Knapp, *Lie Groups Beyond an Introduction*, second edition, Chapter VI.
* B. C. Hall, *Lie Groups, Lie Algebras, and Representations*, second edition, Section 2.5.
-/

public section

open Matrix Pointwise
open scoped MatrixOrder

variable {𝕜 : Type*} [RCLike 𝕜] {ι : Type*} [Fintype ι] [DecidableEq ι]

namespace Matrix.SpecialLinearGroup

/-- **The determinant-one unitary matrices form a compact subgroup of `SL ι 𝕜`**, over `ℝ` or
`ℂ`: the inclusion of `SL ι 𝕜` in `GL ι 𝕜` is a closed embedding and the unitary subgroup of
`GL ι 𝕜` is compact. -/
theorem isCompact_comap_unitarySubgroup :
    IsCompact (((unitarySubgroup (GL ι 𝕜)).comap toGL : Subgroup (SpecialLinearGroup ι 𝕜)) :
      Set (SpecialLinearGroup ι 𝕜)) :=
  isClosedEmbedding_toGL.isCompact_preimage GeneralLinearGroup.isCompact_unitarySubgroup

/-- **The determinant-one unitary matrices form a maximal compact subgroup of `SL ι 𝕜`**, in the
elementwise form: an element of a compact subgroup containing every determinant-one unitary matrix
is unitary. -/
theorem mem_comap_unitarySubgroup_of_isCompact_of_le {K : Subgroup (SpecialLinearGroup ι 𝕜)}
    (hK : IsCompact (K : Set (SpecialLinearGroup ι 𝕜)))
    (hUK : (unitarySubgroup (GL ι 𝕜)).comap toGL ≤ K) {g : SpecialLinearGroup ι 𝕜}
    (hg : g ∈ K) : g ∈ (unitarySubgroup (GL ι 𝕜)).comap toGL := by
  -- The unitary polar factor of `g` has determinant one, so it is an element of `K`.
  let V : SpecialLinearGroup ι 𝕜 := ⟨(Units.polarUnitary (toGL g) : Matrix ι ι 𝕜),
    GeneralLinearGroup.det_polarUnitary_of_det_eq_one _ (by simp)⟩
  have hV : toGL V = Unitary.toUnits (Units.polarUnitary (toGL g)) :=
    Units.ext (coe_GL_coe_matrix _)
  have hVK : V ∈ K := hUK (by simp [hV])
  exact GeneralLinearGroup.mem_unitarySubgroup_of_isCompact_of_polarUnitary_mem
    (Subgroup.isCompact_map hK _ continuous_toGL) ⟨g, hg, rfl⟩ ⟨V, hVK, hV⟩

/-- **The determinant-one unitary matrices form a maximal compact subgroup of `SL ι 𝕜`.** A compact
subgroup containing every determinant-one unitary matrix is the subgroup of determinant-one
unitary matrices. Over `ℝ` this is the special orthogonal group `SO(n)`, and over `ℂ` the special
unitary group `SU(n)`. -/
theorem eq_comap_unitarySubgroup_of_isCompact_of_le {K : Subgroup (SpecialLinearGroup ι 𝕜)}
    (hK : IsCompact (K : Set (SpecialLinearGroup ι 𝕜)))
    (hUK : (unitarySubgroup (GL ι 𝕜)).comap toGL ≤ K) :
    K = (unitarySubgroup (GL ι 𝕜)).comap toGL :=
  le_antisymm (fun _ hg ↦ mem_comap_unitarySubgroup_of_isCompact_of_le hK hUK hg) hUK

/-- **The determinant-one unitary matrices form a maximal compact subgroup of `SL ι 𝕜`**, stated in
the lattice of subgroups of `SL ι 𝕜`. -/
theorem maximal_isCompact_comap_unitarySubgroup :
    Maximal (fun H : Subgroup (SpecialLinearGroup ι 𝕜) ↦
        IsCompact (H : Set (SpecialLinearGroup ι 𝕜)))
      ((unitarySubgroup (GL ι 𝕜)).comap toGL) :=
  ⟨isCompact_comap_unitarySubgroup, fun _ hK hUK ↦
    (eq_comap_unitarySubgroup_of_isCompact_of_le hK hUK).le⟩

/-- **Every compact subgroup of `SL ι 𝕜` is conjugate into the determinant-one unitary matrices**
by an element of `SL ι 𝕜`. Over `ℝ` the target is `SO(n)`, and over `ℂ` it is `SU(n)`. -/
theorem exists_conj_smul_le_comap_unitarySubgroup {K : Subgroup (SpecialLinearGroup ι 𝕜)}
    (hK : IsCompact (K : Set (SpecialLinearGroup ι 𝕜))) :
    ∃ g : SpecialLinearGroup ι 𝕜,
      MulAut.conj g • K ≤ (unitarySubgroup (GL ι 𝕜)).comap toGL := by
  -- Conjugate `K` into the unitary matrices by `h : GL ι 𝕜`, and write `h = c V g`. Conjugation
  -- by the scalar `c` is trivial and conjugation by the unitary `V` preserves unitarity.
  obtain ⟨h, hh⟩ := GeneralLinearGroup.exists_conj_smul_le_unitarySubgroup
    (Subgroup.isCompact_map hK _ continuous_toGL)
  obtain ⟨c, V, hV, g, hcVg⟩ := GeneralLinearGroup.exists_scalar_mul_mul_toGL_eq h
  refine ⟨g, fun x hx ↦ ?_⟩
  obtain ⟨k, hk, rfl⟩ := (Subgroup.mem_smul_pointwise_iff_exists _ _ _).mp hx
  have hhk : h * toGL k * h⁻¹ ∈ unitarySubgroup (GL ι 𝕜) :=
    hh ((Subgroup.mem_smul_pointwise_iff_exists _ _ _).mpr ⟨toGL k, ⟨k, hk, rfl⟩, rfl⟩)
  -- Conjugation by the central scalar `c` is trivial.
  have hc : Commute (GeneralLinearGroup.scalar ι c) (V * toGL (g * k * g⁻¹) * V⁻¹) :=
    GeneralLinearGroup.scalar_commute _ _
  have hconj : V * toGL (g * k * g⁻¹) * V⁻¹ = h * toGL k * h⁻¹ := by
    rw [← hc.mul_inv_cancel, ← hcVg, map_mul, map_mul, map_inv]
    group
  rw [MulAut.smul_def, MulAut.conj_apply, Subgroup.mem_comap,
    ← Subgroup.mul_mem_cancel_left _ hV, ← Subgroup.mul_mem_cancel_right _ (inv_mem hV), hconj]
  exact hhk

/-- **The maximal compact subgroups of `SL ι 𝕜` are the conjugates of the determinant-one unitary
matrices.** Over `ℝ` these are the conjugates of the special orthogonal group `SO(n)`, and over `ℂ`
of the special unitary group `SU(n)`. -/
theorem maximal_isCompact_iff {K : Subgroup (SpecialLinearGroup ι 𝕜)} :
    Maximal (fun H : Subgroup (SpecialLinearGroup ι 𝕜) ↦
        IsCompact (H : Set (SpecialLinearGroup ι 𝕜))) K ↔
      ∃ g : SpecialLinearGroup ι 𝕜, K = MulAut.conj g • (unitarySubgroup (GL ι 𝕜)).comap toGL :=
  Subgroup.maximal_isCompact_iff_exists_eq_conj_smul maximal_isCompact_comap_unitarySubgroup
    fun _ ↦ exists_conj_smul_le_comap_unitarySubgroup

end Matrix.SpecialLinearGroup

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Diagonal.Positive
public import TauCeti.LinearAlgebra.Matrix.UnitaryGroup.PermutationGL
-- The units of an ordered field are infinite, hence nontrivial, which the coordinate permutation of
-- a monomial matrix needs.
public import Mathlib.Algebra.CharZero.Infinite
public import TauCeti.Algebra.GroupWithZero.Units.Basic
import Mathlib.Data.Finite.Perm

/-!
# The restricted Weyl group of the general linear group

Let `𝕜` be a linearly ordered field with a star operation, such as `ℝ`. In `G = GL n 𝕜` take
the compact subgroup `K = unitarySubgroup (GL (Fin n) 𝕜)` (for `𝕜 = ℝ`, the orthogonal group
`O(n)`) and the positive diagonal subgroup `A = TauCeti.posDiagonalSubgroup (Fin n) 𝕜`, the
`A` of the Iwasawa decomposition `G = K A N` and of the `KAK` decomposition. The **restricted
Weyl group** of `G` is the quotient `W = N_K(A) / Z_K(A)` of the normalizer of `A` in `K` by the
centralizer of `A` in `K`. (Knapp writes these groups `M' = N_K(𝔞)` and `M = Z_K(𝔞)`, through the
Lie algebra `𝔞` of `A`; here they are defined through the group `A` itself.) This file proves
that `W` is the symmetric group on the `n` coordinates
(`TauCeti.unitaryNormalizerPosDiagonalQuotientMulEquivPerm`), acting on `A` by permuting the
diagonal entries (`TauCeti.unitaryNormalizerPosDiagonal_mul_diagGL_mul_inv`).

The computation reduces to the one for the diagonal torus `D` of `GL n 𝕜` in
`TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Diagonal.Normalizer`. The positive diagonal
matrices already separate any two coordinates, so the centralizer of `A` in `G` is `D`
(`TauCeti.centralizer_posDiagonalSubgroup`) and the normalizer of `A` in `G` is the normalizer of
`D`, the monomial matrices (`TauCeti.normalizer_posDiagonalSubgroup`). Thus `Z_K(A) = K ∩ D` is the
group of diagonal matrices in `K` (over `ℝ`, the diagonal matrices with entries `±1`), and
`N_K(A)` is the group of monomial matrices in `K`. The coordinate permutation of a monomial matrix
is trivial exactly on `D`, and every permutation is realized by a permutation matrix, which lies
in `K`.

## Main definitions

* `TauCeti.unitaryNormalizerPosDiagonal 𝕜 n`: the normalizer `N_K(A)` of `A` in `K`.
* `TauCeti.unitaryCentralizerPosDiagonal 𝕜 n`: the centralizer `Z_K(A)` of `A` in `K`.
* `TauCeti.unitaryNormalizerPosDiagonalPerm`: the coordinate permutation of an element of
  `N_K(A)`.
* `TauCeti.unitaryNormalizerPosDiagonalQuotientMulEquivPerm`: the restricted Weyl group
  `N_K(A) / Z_K(A)` is the symmetric group `Equiv.Perm (Fin n)`.

## Main results

* `TauCeti.normalizer_posDiagonalSubgroup`: in `GL n 𝕜`, normalizing `A` is normalizing the
  diagonal torus.
* `TauCeti.unitaryNormalizerPosDiagonal_eq`: `N_K(A)` is the normalizer of the diagonal torus in
  `K`.
* `TauCeti.mem_unitaryNormalizerPosDiagonal_iff`: the elements of `N_K(A)` are the elements of `K`
  that are a diagonal matrix times a permutation matrix.
* `TauCeti.unitaryCentralizerPosDiagonal_eq`: `Z_K(A)` is the group of diagonal matrices in `K`.
* `TauCeti.unitaryNormalizerPosDiagonal_mul_diagGL_mul_inv`: conjugation by an element of
  `N_K(A)` permutes the diagonal entries of a diagonal matrix by its coordinate permutation.
* `TauCeti.ker_unitaryNormalizerPosDiagonalPerm`: the coordinate permutation has kernel `Z_K(A)`.
* `TauCeti.natCard_unitaryNormalizerPosDiagonal_quotient`: the restricted Weyl group has `n!`
  elements.

## References

* A. W. Knapp, *Lie Groups Beyond an Introduction*, second edition, Progress in Mathematics 140,
  Birkhäuser, 2002, Chapter VI, Sections 4 and 5 (the groups `M = Z_K(𝔞)`, `M' = N_K(𝔞)` and
  the Weyl group `W(G, A) = M' / M`, with `GL n ℝ` and `SL n ℝ` as examples).
-/

public section

open Matrix

namespace TauCeti

variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] {n : ℕ}

/-- Conjugation by an invertible matrix normalizing the diagonal torus keeps the positive diagonal
subgroup inside itself. -/
private theorem mul_mul_inv_mem_posDiagonalSubgroup {g : GL (Fin n) 𝕜}
    (hg : g ∈ Subgroup.normalizer (diagonalTorus 𝕜 n : Set (GL (Fin n) 𝕜)))
    {a : GL (Fin n) 𝕜} (ha : a ∈ posDiagonalSubgroup (Fin n) 𝕜) :
    g * a * g⁻¹ ∈ posDiagonalSubgroup (Fin n) 𝕜 := by
  obtain ⟨t, rfl⟩ :=
    mem_diagonalTorus_iff_exists_diagGL.mp (posDiagonalSubgroup_le_diagonalTorus 𝕜 n ha)
  have hconj := diagonalNormalizer_mul_diagGL_mul_inv ⟨g, hg⟩ t
  rw [Subgroup.coe_mk] at hconj
  rw [hconj, diagGL_mem_posDiagonalSubgroup_iff]
  exact fun i => diagGL_mem_posDiagonalSubgroup_iff.mp ha _

variable (𝕜 n) in
/-- **The normalizer of the positive diagonal subgroup is the normalizer of the diagonal torus**:
an invertible matrix normalizes the positive diagonal matrices exactly when it is monomial. -/
theorem normalizer_posDiagonalSubgroup :
    Subgroup.normalizer (posDiagonalSubgroup (Fin n) 𝕜 : Set (GL (Fin n) 𝕜)) =
      Subgroup.normalizer (diagonalTorus 𝕜 n : Set (GL (Fin n) 𝕜)) := by
  refine le_antisymm (fun g hg => ?_) fun g hg =>
    Subgroup.mem_normalizer_iff.mpr fun a => ⟨mul_mul_inv_mem_posDiagonalSubgroup hg, fun ha => ?_⟩
  · -- The positive diagonal matrix with `2` at `i` and `1` elsewhere separates `i` from `j`.
    have hsep (i j : Fin n) (hij : i ≠ j) : ∃ t : Fin n → 𝕜ˣ,
        g * diagGL t * g⁻¹ ∈ diagonalTorus 𝕜 n ∧ t i ≠ t j := by
      let t : Fin n → 𝕜ˣ := Pi.mulSingle i (Units.mk0 2 two_ne_zero)
      have ht : diagGL t ∈ posDiagonalSubgroup (Fin n) 𝕜 :=
        diagGL_mem_posDiagonalSubgroup_iff.mpr fun m => by
          rcases eq_or_ne m i with rfl | hm <;> simp [t, *]
      refine ⟨t, posDiagonalSubgroup_le_diagonalTorus 𝕜 n
        ((Subgroup.mem_normalizer_iff.mp hg _).mp ht), ?_⟩
      simp [t, Pi.mulSingle_eq_of_ne hij.symm, Units.ext_iff]
    obtain ⟨d, σ, rfl⟩ := exists_eq_diagGL_mul_permutationGL_of_forall_ne hsep
    exact mem_normalizer_diagonalTorus_iff_exists.mpr ⟨d, σ, rfl⟩
  · simpa [mul_assoc] using mul_mul_inv_mem_posDiagonalSubgroup (inv_mem hg) ha

variable [StarRing 𝕜]

variable (𝕜 n) in
/-- The normalizer `N_K(A)` of the positive diagonal subgroup `A` in the unitary subgroup `K` of
`GL n 𝕜`; for `𝕜 = ℝ`, `K` is the orthogonal group. -/
def unitaryNormalizerPosDiagonal : Subgroup (GL (Fin n) 𝕜) :=
  unitarySubgroup (GL (Fin n) 𝕜) ⊓
    Subgroup.normalizer (posDiagonalSubgroup (Fin n) 𝕜 : Set (GL (Fin n) 𝕜))

variable (𝕜 n) in
/-- The centralizer `Z_K(A)` of the positive diagonal subgroup `A` in the unitary subgroup `K` of
`GL n 𝕜`; for `𝕜 = ℝ`, `K` is the orthogonal group. -/
def unitaryCentralizerPosDiagonal : Subgroup (GL (Fin n) 𝕜) :=
  unitarySubgroup (GL (Fin n) 𝕜) ⊓
    Subgroup.centralizer (posDiagonalSubgroup (Fin n) 𝕜 : Set (GL (Fin n) 𝕜))

variable (𝕜 n) in
/-- **`N_K(A)` is the normalizer of the diagonal torus in `K`.** -/
theorem unitaryNormalizerPosDiagonal_eq :
    unitaryNormalizerPosDiagonal 𝕜 n = unitarySubgroup (GL (Fin n) 𝕜) ⊓
      Subgroup.normalizer (diagonalTorus 𝕜 n : Set (GL (Fin n) 𝕜)) := by
  rw [unitaryNormalizerPosDiagonal, normalizer_posDiagonalSubgroup]

/-- An invertible matrix lies in `N_K(A)` exactly when it lies in `K` and normalizes the diagonal
torus. -/
theorem mem_unitaryNormalizerPosDiagonal_iff_mem_normalizer {g : GL (Fin n) 𝕜} :
    g ∈ unitaryNormalizerPosDiagonal 𝕜 n ↔ g ∈ unitarySubgroup (GL (Fin n) 𝕜) ∧
      g ∈ Subgroup.normalizer (diagonalTorus 𝕜 n : Set (GL (Fin n) 𝕜)) := by
  rw [unitaryNormalizerPosDiagonal_eq, Subgroup.mem_inf]

/-- **The elements of `N_K(A)` are the monomial matrices in `K`**: the elements of `K` that are a
diagonal matrix times a permutation matrix. -/
theorem mem_unitaryNormalizerPosDiagonal_iff {g : GL (Fin n) 𝕜} :
    g ∈ unitaryNormalizerPosDiagonal 𝕜 n ↔ g ∈ unitarySubgroup (GL (Fin n) 𝕜) ∧
      ∃ d : Fin n → 𝕜ˣ, ∃ σ : Equiv.Perm (Fin n), g = diagGL d * permutationGL σ := by
  rw [mem_unitaryNormalizerPosDiagonal_iff_mem_normalizer, mem_normalizer_diagonalTorus_iff_exists]

variable (𝕜 n) in
/-- **`Z_K(A)` is the group of diagonal matrices in `K`.** Over `ℝ` these are the diagonal
matrices with entries `±1`. -/
theorem unitaryCentralizerPosDiagonal_eq :
    unitaryCentralizerPosDiagonal 𝕜 n = unitarySubgroup (GL (Fin n) 𝕜) ⊓ diagonalTorus 𝕜 n := by
  rw [unitaryCentralizerPosDiagonal, centralizer_posDiagonalSubgroup]

/-- An invertible matrix lies in `Z_K(A)` exactly when it lies in `K` and is diagonal. -/
@[simp]
theorem mem_unitaryCentralizerPosDiagonal_iff {g : GL (Fin n) 𝕜} :
    g ∈ unitaryCentralizerPosDiagonal 𝕜 n ↔
      g ∈ unitarySubgroup (GL (Fin n) 𝕜) ∧ (g : Matrix (Fin n) (Fin n) 𝕜).IsDiag := by
  rw [unitaryCentralizerPosDiagonal_eq, Subgroup.mem_inf, mem_diagonalTorus_iff]

variable (𝕜 n) in
/-- `Z_K(A) ≤ N_K(A)`. -/
theorem unitaryCentralizerPosDiagonal_le_unitaryNormalizerPosDiagonal :
    unitaryCentralizerPosDiagonal 𝕜 n ≤ unitaryNormalizerPosDiagonal 𝕜 n :=
  inf_le_inf_left _ (Subgroup.centralizer_le_normalizer _)

/-- A permutation matrix lies in `N_K(A)`. -/
theorem permutationGL_mem_unitaryNormalizerPosDiagonal (σ : Equiv.Perm (Fin n)) :
    permutationGL σ ∈ unitaryNormalizerPosDiagonal 𝕜 n :=
  mem_unitaryNormalizerPosDiagonal_iff_mem_normalizer.mpr
    ⟨permutationGL_mem_unitarySubgroup σ, permutationGL_mem_normalizer σ⟩

/-- The coordinate permutation of an element of `N_K(A)`: the coordinate permutation of the same
matrix as an element of the normalizer of the diagonal torus. -/
noncomputable def unitaryNormalizerPosDiagonalPerm :
    unitaryNormalizerPosDiagonal 𝕜 n →* Equiv.Perm (Fin n) :=
  diagonalNormalizerPerm.comp <| Subgroup.inclusion fun _ hg =>
    (mem_unitaryNormalizerPosDiagonal_iff_mem_normalizer.mp hg).2

/-- The coordinate permutation of an element of `N_K(A)` is its coordinate permutation as an
element of the normalizer of the diagonal torus. -/
theorem unitaryNormalizerPosDiagonalPerm_apply (g : unitaryNormalizerPosDiagonal 𝕜 n) :
    unitaryNormalizerPosDiagonalPerm g =
      diagonalNormalizerPerm ⟨(g : GL (Fin n) 𝕜),
        (mem_unitaryNormalizerPosDiagonal_iff_mem_normalizer.mp g.property).2⟩ :=
  (rfl)

/-- **Conjugation by an element of `N_K(A)` permutes the diagonal entries of a diagonal matrix**:
the entry at `i` becomes the original entry at the inverse image of `i` under the coordinate
permutation. In particular `N_K(A)` acts on `A` through its coordinate permutation. -/
@[simp]
theorem unitaryNormalizerPosDiagonal_mul_diagGL_mul_inv (g : unitaryNormalizerPosDiagonal 𝕜 n)
    (t : Fin n → 𝕜ˣ) :
    (g : GL (Fin n) 𝕜) * diagGL t * (g : GL (Fin n) 𝕜)⁻¹ =
      diagGL fun i => t ((unitaryNormalizerPosDiagonalPerm g).symm i) := by
  rw [unitaryNormalizerPosDiagonalPerm_apply, ← diagonalNormalizer_mul_diagGL_mul_inv,
    Subgroup.coe_mk]

/-- The coordinate permutation of an element of `N_K(A)` is trivial exactly on `Z_K(A)`. -/
theorem unitaryNormalizerPosDiagonalPerm_eq_one_iff (g : unitaryNormalizerPosDiagonal 𝕜 n) :
    unitaryNormalizerPosDiagonalPerm g = 1 ↔
      (g : GL (Fin n) 𝕜) ∈ unitaryCentralizerPosDiagonal 𝕜 n := by
  rw [unitaryNormalizerPosDiagonalPerm_apply, diagonalNormalizerPerm_eq_one_iff, Subgroup.coe_mk,
    unitaryCentralizerPosDiagonal_eq, Subgroup.mem_inf]
  exact ⟨fun h => ⟨(mem_unitaryNormalizerPosDiagonal_iff_mem_normalizer.mp g.property).1, h⟩,
    And.right⟩

/-- The coordinate permutation of a permutation matrix is the original permutation. -/
@[simp]
theorem unitaryNormalizerPosDiagonalPerm_permutationGL (σ : Equiv.Perm (Fin n)) :
    unitaryNormalizerPosDiagonalPerm
      ⟨permutationGL σ, permutationGL_mem_unitaryNormalizerPosDiagonal (𝕜 := 𝕜) σ⟩ = σ := by
  rw [unitaryNormalizerPosDiagonalPerm_apply]
  exact diagonalNormalizerPerm_permutationGL σ

/-- Every permutation of the coordinates is the coordinate permutation of an element of `N_K(A)`,
namely of a permutation matrix. -/
theorem unitaryNormalizerPosDiagonalPerm_surjective :
    Function.Surjective (unitaryNormalizerPosDiagonalPerm (𝕜 := 𝕜) (n := n)) := fun σ =>
  ⟨_, unitaryNormalizerPosDiagonalPerm_permutationGL σ⟩

/-- **The kernel of the coordinate permutation of `N_K(A)` is `Z_K(A)`.** -/
theorem ker_unitaryNormalizerPosDiagonalPerm :
    (unitaryNormalizerPosDiagonalPerm (𝕜 := 𝕜) (n := n)).ker =
      (unitaryCentralizerPosDiagonal 𝕜 n).subgroupOf (unitaryNormalizerPosDiagonal 𝕜 n) :=
  Subgroup.ext fun g => by
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, unitaryNormalizerPosDiagonalPerm_eq_one_iff]

/-- `Z_K(A)` is normal in `N_K(A)`. -/
instance : ((unitaryCentralizerPosDiagonal 𝕜 n).subgroupOf
    (unitaryNormalizerPosDiagonal 𝕜 n)).Normal :=
  ker_unitaryNormalizerPosDiagonalPerm (𝕜 := 𝕜) (n := n) ▸ MonoidHom.normal_ker _

/-- **The restricted Weyl group of `GL n 𝕜` is the symmetric group**: the normalizer `N_K(A)` of
the positive diagonal subgroup in the unitary subgroup, modulo its centralizer `Z_K(A)`, is
canonically the group of permutations of the `n` coordinates. -/
noncomputable def unitaryNormalizerPosDiagonalQuotientMulEquivPerm :
    unitaryNormalizerPosDiagonal 𝕜 n ⧸
        (unitaryCentralizerPosDiagonal 𝕜 n).subgroupOf (unitaryNormalizerPosDiagonal 𝕜 n) ≃*
      Equiv.Perm (Fin n) :=
  (QuotientGroup.quotientMulEquivOfEq ker_unitaryNormalizerPosDiagonalPerm.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective _ unitaryNormalizerPosDiagonalPerm_surjective)

/-- The restricted Weyl group equivalence sends the class of an element of `N_K(A)` to its
coordinate permutation. -/
@[simp]
theorem unitaryNormalizerPosDiagonalQuotientMulEquivPerm_mk
    (g : unitaryNormalizerPosDiagonal 𝕜 n) :
    unitaryNormalizerPosDiagonalQuotientMulEquivPerm (g : unitaryNormalizerPosDiagonal 𝕜 n ⧸
        (unitaryCentralizerPosDiagonal 𝕜 n).subgroupOf (unitaryNormalizerPosDiagonal 𝕜 n)) =
      unitaryNormalizerPosDiagonalPerm g :=
  (rfl)

/-- The inverse of the restricted Weyl group equivalence sends a coordinate permutation to the
class of its permutation matrix. -/
@[simp]
theorem unitaryNormalizerPosDiagonalQuotientMulEquivPerm_symm_apply (σ : Equiv.Perm (Fin n)) :
    (unitaryNormalizerPosDiagonalQuotientMulEquivPerm (𝕜 := 𝕜)).symm σ =
      ((⟨permutationGL σ, permutationGL_mem_unitaryNormalizerPosDiagonal σ⟩ :
          unitaryNormalizerPosDiagonal 𝕜 n) : unitaryNormalizerPosDiagonal 𝕜 n ⧸
        (unitaryCentralizerPosDiagonal 𝕜 n).subgroupOf (unitaryNormalizerPosDiagonal 𝕜 n)) := by
  rw [MulEquiv.symm_apply_eq, unitaryNormalizerPosDiagonalQuotientMulEquivPerm_mk,
    unitaryNormalizerPosDiagonalPerm_permutationGL]

variable (𝕜 n) in
/-- The restricted Weyl group of `GL n 𝕜` has `n!` elements. -/
theorem natCard_unitaryNormalizerPosDiagonal_quotient :
    Nat.card (unitaryNormalizerPosDiagonal 𝕜 n ⧸
        (unitaryCentralizerPosDiagonal 𝕜 n).subgroupOf (unitaryNormalizerPosDiagonal 𝕜 n)) =
      n.factorial := by
  rw [Nat.card_congr unitaryNormalizerPosDiagonalQuotientMulEquivPerm.toEquiv, Nat.card_perm,
    Nat.card_fin]

end TauCeti

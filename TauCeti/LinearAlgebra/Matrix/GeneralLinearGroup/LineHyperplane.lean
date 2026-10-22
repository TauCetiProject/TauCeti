/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.Submodule.Pointwise
public import Mathlib.LinearAlgebra.Span.Defs
public import TauCeti.GroupTheory.AlmostConjugate
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.InverseTranspose
import TauCeti.GroupTheory.GroupAction.Stabilizer
import TauCeti.LinearAlgebra.Matrix.Eigenvectors
import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.NonzeroVectors
import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Transvection
import TauCeti.LinearAlgebra.Matrix.MulVec
import TauCeti.LinearAlgebra.Span.Basic

/-!
# The stabilizers of a coordinate line and of a coordinate hyperplane

Let `K` be a field and `n` a finite index type. In `GL n K`, acting on `n → K` by
`Matrix.mulVec`, consider the stabilizer `P` of the coordinate line `K ∙ eᵢ` and the stabilizer
`Q` of the coordinate hyperplane `{v | v i = 0}`. In matrix entries, `P` consists of the invertible
matrices whose column `i` vanishes off the diagonal, and `Q` of those whose row `i` does. When `n`
has at least two elements, these are the maximal parabolic subgroups of `GLₙ` of block shapes
`(1, n - 1)` and `(n - 1, 1)`, and both contain the block-diagonal subgroup `GL₁ × GLₙ₋₁` as a
common Levi factor. When `n` has one element, both are the whole group.

Inverse transpose `g ↦ (g⁻¹)ᵀ` is an automorphism of `GL n K` carrying `P` onto `Q`. Over a finite
field the two subgroups are **almost conjugate**: they meet every conjugacy class in the same
number of elements. Indeed, `x⁻¹ g x ∈ P` exactly when `x eᵢ` is an eigenvector of `g`, so the
number of such `x` is the number of eigenvectors of `g` times the order of the stabilizer of `eᵢ`.
Transport along inverse transpose replaces `g` by `(g⁻¹)ᵀ`, which has as many eigenvectors as
`g`: for each scalar `c` the eigenspaces of `g` and `gᵀ` have the same dimension, because a matrix
and its transpose have the same rank.

When `n` has at least three elements the two subgroups are nevertheless **not conjugate**. Every
conjugate of `P` stabilizes a line, while `Q` stabilizes no line at all: a line outside the
hyperplane is moved by a transvection fixing the hyperplane pointwise, and a line inside it is
moved by a transvection of the hyperplane itself. For `n = 3` this is the classical pair of a
point stabilizer and a line stabilizer in `GL₃(𝔽_q)`, an almost-conjugate but non-conjugate pair
of parabolic subgroups with a common Levi factor, for every prime power `q`, including `q = 2`.
For `n = 2` both subgroups are line stabilizers and they are conjugate.

## Main definitions

* `TauCeti.lineStabilizer K i`: the stabilizer of the coordinate line `K ∙ eᵢ`.
* `TauCeti.hyperplaneStabilizer K i`: the stabilizer of the coordinate hyperplane `{v | v i = 0}`.

## Main results

* `TauCeti.lineStabilizer_def` and `TauCeti.hyperplaneStabilizer_def`: the defining
  stabilizer equations.
* `TauCeti.mem_lineStabilizer_iff` and `TauCeti.mem_hyperplaneStabilizer_iff`: membership in
  terms of matrix entries.
* `TauCeti.map_inverseTranspose_lineStabilizer`: inverse transpose carries the line stabilizer
  onto the hyperplane stabilizer.
* `TauCeti.exists_mem_hyperplaneStabilizer_smul_ne`: if `n` has at least three elements, the
  hyperplane stabilizer stabilizes no line.
* `TauCeti.conj_smul_lineStabilizer_ne_hyperplaneStabilizer`: if `n` has at least three elements,
  no conjugate of a line stabilizer is a hyperplane stabilizer.
* `TauCeti.almostConjugate_lineStabilizer_hyperplaneStabilizer`: over a finite field, the line and
  hyperplane stabilizers are almost conjugate.

## References

* R. Perlis, *On the equation `ζ_K(s) = ζ_K'(s)`*, J. Number Theory 9 (1977), 342–360, where
  the points and hyperplanes of a projective space give Gassmann triples.
-/

public section

open Matrix MulAction Pointwise

namespace TauCeti

variable (K : Type*) [Field K] {n : Type*} [Fintype n] [DecidableEq n]

/-- The stabilizer in `GL n K` of the coordinate line `K ∙ eᵢ`, for the action of invertible
matrices on `n → K` by `Matrix.mulVec`. -/
def lineStabilizer (i : n) : Subgroup (GL n K) :=
  stabilizer (GL n K) (K ∙ (Pi.single i 1 : n → K))

/-- The stabilizer in `GL n K` of the coordinate hyperplane `{v | v i = 0}`, for the action of
invertible matrices on `n → K` by `Matrix.mulVec`. -/
def hyperplaneStabilizer (i : n) : Subgroup (GL n K) :=
  stabilizer (GL n K) (LinearMap.ker (LinearMap.proj i : (n → K) →ₗ[K] K))

/-- The line stabilizer is the stabilizer of the coordinate line `K ∙ eᵢ` for the action of
`GL n K` on submodules of `n → K`. -/
theorem lineStabilizer_def (i : n) :
    lineStabilizer K i = stabilizer (GL n K) (K ∙ (Pi.single i 1 : n → K)) :=
  (rfl)

/-- The hyperplane stabilizer is the stabilizer of the coordinate hyperplane `{v | v i = 0}` for
the action of `GL n K` on submodules of `n → K`. -/
theorem hyperplaneStabilizer_def (i : n) :
    hyperplaneStabilizer K i =
      stabilizer (GL n K) (LinearMap.ker (LinearMap.proj i : (n → K) →ₗ[K] K)) :=
  (rfl)

variable {K}

/-- **Membership in the line stabilizer**: an invertible matrix stabilizes the line `K ∙ eᵢ`
exactly when its column `i` vanishes off the diagonal. -/
@[simp]
theorem mem_lineStabilizer_iff {g : GL n K} {i : n} :
    g ∈ lineStabilizer K i ↔ ∀ j ≠ i, g j i = 0 := by
  rw [lineStabilizer_def, mem_stabilizer_iff]
  -- `GL n K` acts on submodules through its matrices (`Units.instSMul`), which agrees with the
  -- pointwise action of the group only after unfolding instances, so the general span lemmas are
  -- applied as terms rather than rewritten. The same holds below.
  refine Submodule.smul_span_singleton_eq_iff.trans ?_
  rw [Units.smul_def, Matrix.smul_eq_mulVec, Matrix.mulVec_single_one]
  constructor
  · rintro ⟨c, hc⟩ j hj
    simpa [hj] using congrFun hc j
  · intro h
    refine ⟨g i i, funext fun j ↦ ?_⟩
    by_cases hj : j = i
    · subst hj
      simp
    · simp [h j hj, hj]

/-- **Membership in the hyperplane stabilizer**: an invertible matrix stabilizes the coordinate
hyperplane `{v | v i = 0}` exactly when its row `i` vanishes off the diagonal. -/
@[simp]
theorem mem_hyperplaneStabilizer_iff {g : GL n K} {i : n} :
    g ∈ hyperplaneStabilizer K i ↔ ∀ j ≠ i, g i j = 0 := by
  rw [hyperplaneStabilizer_def, mem_stabilizer_iff]
  constructor
  · intro h j hj
    have hmem : g • (Pi.single j (1 : K) : n → K) ∈
        g • LinearMap.ker (LinearMap.proj i : (n → K) →ₗ[K] K) :=
      Submodule.smul_mem_pointwise_smul _ _ _ (by simp [Ne.symm hj])
    rw [h, LinearMap.mem_ker, Units.smul_def, Matrix.smul_eq_mulVec,
      Matrix.mulVec_single_one] at hmem
    exact hmem
  · intro h
    -- Row `i` vanishing off the diagonal is block triangularity for the two-block partition
    -- `{i}`, `{j ≠ i}`, which is inherited by the inverse matrix.
    have hb : (g : Matrix n n K).BlockTriangular (fun j ↦ if j = i then 1 else 0 : n → ℕ) := by
      intro r c hrc
      by_cases hr : r = i <;> by_cases hc : c = i <;> simp_all
    have hinv : ∀ j ≠ i, (g⁻¹ : GL n K) i j = 0 := fun j hj ↦ by
      have := Matrix.blockTriangular_inv_of_blockTriangular hb (i := i) (j := j) (by simp [hj])
      rwa [← Matrix.coe_units_inv] at this
    -- A matrix whose row `i` vanishes off the diagonal maps the hyperplane into itself.
    have hmaps {h : GL n K} (hh : ∀ j ≠ i, h i j = 0) {w : n → K} (hw : w i = 0) :
        (h • w) i = 0 := by
      rw [Units.smul_def, Matrix.smul_eq_mulVec, mulVec_apply_eq_mul_of_forall_ne_eq_zero hh, hw,
        mul_zero]
    refine le_antisymm (fun x hx ↦ ?_) (fun w hw ↦ ?_)
    · obtain ⟨w, hw, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).mp hx
      exact hmaps h hw
    · exact (Submodule.mem_smul_pointwise_iff_exists _ _ _).mpr
        ⟨g⁻¹ • w, hmaps hinv hw, smul_inv_smul g w⟩

/-- **Inverse transpose exchanges the two stabilizers**: the automorphism `g ↦ (g⁻¹)ᵀ` of
`GL n K` carries the stabilizer of the line `K ∙ eᵢ` onto the stabilizer of the hyperplane
`{v | v i = 0}`. -/
theorem map_inverseTranspose_lineStabilizer (i : n) :
    (lineStabilizer K i).map GeneralLinearGroup.inverseTranspose.toMonoidHom =
      hyperplaneStabilizer K i := by
  ext g
  rw [Subgroup.mem_map_equiv, GeneralLinearGroup.inverseTranspose_symm, mem_lineStabilizer_iff,
    ← Subgroup.inv_mem_iff, mem_hyperplaneStabilizer_iff]
  simp [GeneralLinearGroup.coe_inverseTranspose]

/-! ### The hyperplane stabilizer fixes no line -/

/-- **The hyperplane stabilizer stabilizes no line** when `n` has at least three elements: for
every nonzero `v`, some invertible matrix stabilizing the hyperplane `{w | w i = 0}` moves the
line `K ∙ v`. -/
theorem exists_mem_hyperplaneStabilizer_smul_ne (hn : 3 ≤ Fintype.card n) (i : n)
    {v : n → K} (hv : v ≠ 0) :
    ∃ g ∈ hyperplaneStabilizer K i, g • (K ∙ v) ≠ K ∙ v := by
  -- Choose `k` with `v k ≠ 0` and `m ∉ {i, k}`. The transvection `1 + E_{mk}` keeps row `i` of
  -- the identity, and it adds `v k • e_m` to `v`, which is not a multiple of `v`.
  obtain ⟨k, hk⟩ := Function.ne_iff.mp hv
  obtain ⟨m, -, hm⟩ := Finset.exists_mem_notMem_of_card_lt_card (s := {i, k})
    (t := Finset.univ) (by
      rw [Finset.card_univ]
      exact (Finset.card_le_two).trans_lt (by omega))
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hm
  refine ⟨transvectionUnit hm.2 1, mem_hyperplaneStabilizer_iff.mpr fun j hj ↦ ?_, fun h ↦ ?_⟩
  · simp [transvection, Matrix.one_apply_ne (Ne.symm hj), hm.1]
  obtain ⟨c, hc⟩ := Submodule.smul_span_singleton_eq_iff.mp h
  have hcoord (j : n) : v j + (if j = m then v k else 0) = c * v j := by
    have := congrFun hc j
    rw [Units.smul_def, Matrix.smul_eq_mulVec, coe_transvectionUnit] at this
    simpa [transvection, add_mulVec, single_mulVec, Function.update_apply] using this
  have hc1 : c = 1 := (mul_eq_right₀ hk).mp (by simpa [Ne.symm hm.2] using (hcoord k).symm)
  exact hk (by simpa [hc1] using hcoord m)

/-- **Line and hyperplane stabilizers are not conjugate** when `n` has at least three elements:
no conjugate of the stabilizer of a coordinate line is the stabilizer of a coordinate hyperplane.
Every conjugate of a line stabilizer stabilizes a line, while a hyperplane stabilizer stabilizes
none. -/
theorem conj_smul_lineStabilizer_ne_hyperplaneStabilizer (hn : 3 ≤ Fintype.card n)
    (i j : n) (g : GL n K) :
    MulAut.conj g • lineStabilizer K i ≠ hyperplaneStabilizer K j := by
  intro h
  have hv : g • (Pi.single i 1 : n → K) ≠ 0 :=
    (smul_ne_zero_iff_ne g).mpr (Pi.single_ne_zero_iff.mpr one_ne_zero)
  obtain ⟨q, hq, hne⟩ := exists_mem_hyperplaneStabilizer_smul_ne hn j hv
  rw [← h, Subgroup.mem_pointwise_smul_iff_inv_smul_mem, lineStabilizer_def,
    mem_stabilizer_iff] at hq
  simp only [MulAut.smul_def, MulAut.conj_inv_apply, mul_smul, inv_smul_eq_iff] at hq
  have hspan : g • (K ∙ (Pi.single i 1 : n → K)) = K ∙ (g • Pi.single i 1) :=
    Submodule.smul_span_singleton g _
  rw [hspan] at hq
  exact hne hq

/-! ### Almost conjugacy over a finite field -/

/-- The elements `x` with `x⁻¹ h x` in the stabilizer of the line `K ∙ eᵢ` are those sending `eᵢ`
to an eigenvector of `h`; they number the eigenvectors of `h` times the order of the stabilizer of
`eᵢ`. -/
private theorem natCard_conj_mem_lineStabilizer (i : n) (h : GL n K) :
    Nat.card {x : GL n K // x⁻¹ * h * x ∈ lineStabilizer K i} =
      Nat.card (eigenvectors (h : Matrix n n K)) *
        Nat.card (stabilizer (GL n K) (Pi.single i 1 : n → K)) := by
  rw [← natCard_smul_mem_eq_natCard_mul_natCard_stabilizer _ fun v hv ↦
    mem_orbit_iff.mpr (exists_smul_eq_of_ne_zero (Pi.single_ne_zero_iff.mpr one_ne_zero)
      (GeneralLinearGroup.mem_eigenvectors_iff.mp hv).1)]
  refine Nat.card_congr (Equiv.subtypeEquivRight fun x ↦ ?_)
  have hx : x • (Pi.single i 1 : n → K) ≠ 0 :=
    (smul_ne_zero_iff_ne x).mpr (Pi.single_ne_zero_iff.mpr one_ne_zero)
  have hspan : x • (K ∙ (Pi.single i 1 : n → K)) = K ∙ (x • Pi.single i 1) :=
    Submodule.smul_span_singleton x _
  rw [lineStabilizer_def, mem_stabilizer_iff, mul_smul, mul_smul, inv_smul_eq_iff, hspan,
    GeneralLinearGroup.mem_eigenvectors_iff]
  exact Submodule.smul_span_singleton_eq_iff.trans (and_iff_right hx).symm

/-- **Line and hyperplane stabilizers are almost conjugate over a finite field**: they meet every
conjugacy class of `GL n K` in the same number of elements. Equivalently, every element fixes as
many lines as hyperplanes, so the permutation representations on lines and on hyperplanes have the
same character. -/
theorem almostConjugate_lineStabilizer_hyperplaneStabilizer [Finite K] (i : n) :
    (lineStabilizer K i).AlmostConjugate (hyperplaneStabilizer K i) := by
  set θ := (GeneralLinearGroup.inverseTranspose : GL n K ≃* GL n K)
  have hQ := map_inverseTranspose_lineStabilizer (K := K) i
  have hmemQ (y : GL n K) : y ∈ hyperplaneStabilizer K i ↔ θ y ∈ lineStabilizer K i := by
    rw [← hQ, Subgroup.mem_map_equiv, GeneralLinearGroup.inverseTranspose_symm]
  have hcard : Nat.card (lineStabilizer K i) = Nat.card (hyperplaneStabilizer K i) := by
    rw [← hQ]
    exact (Subgroup.card_map_of_injective θ.injective).symm
  rw [Subgroup.almostConjugate_iff_forall_natCard_fixedBy_eq]
  intro g
  refine Nat.eq_of_mul_eq_mul_left (Nat.card_pos (α := lineStabilizer K i)) ?_
  rw [Subgroup.natCard_mul_natCard_fixedBy, hcard, Subgroup.natCard_mul_natCard_fixedBy]
  -- Transport along `θ` replaces `g` by `(g⁻¹)ᵀ`, which has as many eigenvectors as `g`.
  have heig : Nat.card (eigenvectors ((θ g : GL n K) : Matrix n n K)) =
      Nat.card (eigenvectors (g : Matrix n n K)) := by
    rw [GeneralLinearGroup.coe_inverseTranspose, natCard_eigenvectors_transpose, coe_units_inv,
      GeneralLinearGroup.eigenvectors_inv]
  calc Nat.card {x : GL n K // x⁻¹ * g * x ∈ lineStabilizer K i}
      = Nat.card {x : GL n K // x⁻¹ * θ g * x ∈ lineStabilizer K i} := by
        rw [natCard_conj_mem_lineStabilizer, natCard_conj_mem_lineStabilizer, heig]
    _ = Nat.card {x : GL n K // x⁻¹ * g * x ∈ hyperplaneStabilizer K i} :=
        Nat.card_congr (θ.toEquiv.subtypeEquiv fun x ↦ by
          simp only [hmemQ, map_mul, map_inv, MulEquiv.toEquiv_eq_coe, EquivLike.coe_coe]).symm

end TauCeti

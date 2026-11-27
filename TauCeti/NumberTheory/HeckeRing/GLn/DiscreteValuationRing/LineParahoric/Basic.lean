/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Diagonal.Basic
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.LineHyperplane
public import TauCeti.NumberTheory.HeckeRing.CosetSystem.Basic
public import TauCeti.NumberTheory.HeckeRing.GLn.FractionRing

import TauCeti.LinearAlgebra.Matrix.Determinant.Basic
import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Lift
import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Map
import TauCeti.RingTheory.DiscreteValuationRing.Basic

/-!
# The stabiliser of a line modulo the maximal ideal

Let `R` be a discrete valuation ring with uniformizer `ϖ` and residue field `k` with `q` elements,
and `K` a field containing `R` in which `ϖ` maps to `π`. Let `ι` be a finite index type with `n`
elements and `i ∈ ι`. The **stabiliser of a line modulo `ϖ`**, the parahoric subgroup
`J ⊆ GL_ι(R) ⊆ GL_ι(K)` (`HeckeRing.GLn.lineParahoric`), consists of the `g ∈ GL_ι(R)` whose
reduction modulo `ϖ` lies in the stabiliser `TauCeti.lineStabilizer k i` of the line `k eᵢ`, that
is, whose `i`th column is congruent to a multiple of `eᵢ`. Let
`t = diag(1, …, π, …, 1)` with `π` in position `i`. This file describes the double cosets `J t J`
and `J t⁻¹ J` and counts the cosets of `J t J` and of its inverse through a given coset, which is
the product `1_{J t J} ⋆ 1_{J t⁻¹ J}` in the Hecke algebra of `J`.

The conjugate `t J t⁻¹` is the preimage of the stabiliser `TauCeti.hyperplaneStabilizer k i` of the
hyperplane `xᵢ = 0`, and inverse transpose exchanges it with `J`, as it exchanges the two
stabilisers over `k` (`TauCeti.map_inverseTranspose_lineStabilizer`); hence `J t J` and `J t⁻¹ J`
both consist of `q^{n-1}` left cosets of `J`. The left cosets in `J t J` are the `u t J` for the
matrices `u` that are the identity off the `i`th row, which is `eᵢ + c` for `c` a vector of
residues vanishing at `i`. A coset `t⁻¹ z` lies in `J t⁻¹ J` exactly when `z ∈ GL_ι(R)` and its
`(i, i)` entry is a unit. So the coefficient of `x` in `1_{J t J} ⋆ 1_{J t⁻¹ J}` counts the `c`
with `(u x)ᵢᵢ = xᵢᵢ + ∑_{b ≠ i} c_b x_{b i}` a unit: all `q^{n-1}` of them if `x ∈ J`, and
`q^{n-1} - q^{n-2}` if `x ∈ GL_ι(R) ∖ J`, since then the residues of the `x_{b i}` do not all
vanish and `c ↦ ∑_{b ≠ i} c_b x_{b i}` is a nonzero linear form.

## Main definitions

* `HeckeRing.GLn.lineParahoric R K i`: the stabiliser `J` of the line `k eᵢ` modulo the maximal
  ideal, as a subgroup of `GL_ι(K)`.

## Main results

* `HeckeRing.GLn.mem_lineParahoric_iff`: `J` is the set of `g ∈ GL_ι(R)` with `g_{a i}` in the
  maximal ideal for `a ≠ i`.
* `HeckeRing.GLn.mem_conjAct_lineParahoric_iff`: `t J t⁻¹` is the set of `g ∈ GL_ι(R)` with
  `g_{i b}` in the maximal ideal for `b ≠ i`.
* `HeckeRing.GLn.map_inverseTranspose_lineParahoric`: inverse transpose carries `J` to `t J t⁻¹`.
* `HeckeRing.GLn.relIndex_conjAct_lineParahoric`,
  `HeckeRing.GLn.relIndex_conjAct_inv_lineParahoric`: `J t J` and `J t⁻¹ J` are unions of
  `q^{n-1}` left cosets of `J`.
* `HeckeRing.GLn.relIndex_lineParahoric_mul`: `[GL_ι(R) : J] (q - 1) = qⁿ - 1`.
* `HeckeRing.GLn.inv_mul_mem_doubleCoset_inv_lineParahoric_iff`: `t⁻¹ z ∈ J t⁻¹ J` exactly when
  `z ∈ GL_ι(R)` has a unit `(i, i)` entry.
* `HeckeRing.GLn.sum_indicator_doubleCoset_inv_lineParahoric`: for `n ≥ 2` and representatives
  `g` of the cosets in `J t J`,
  `∑_g 1_{J t⁻¹ J}(g⁻¹ x) = q^{n-2} (1_J(x) + (q - 1) 1_{GL_ι(R)}(x))`.

## References

* G. Shimura, *Introduction to the arithmetic theory of automorphic functions*, Princeton
  University Press (1971), ch. 3, for double cosets and their decomposition into cosets.

The method, counting the cosets of `J t J` and of its inverse through a given coset with the
counts of linear forms over the residue field, follows grh-lean
(<https://github.com/lsernau/grh-lean>, Apache 2.0, Copyright 2026 Anthropic PBC),
`Lib/Adelic/TraceFormula/LineStabiliser.lean` and `Lib/Adelic/TraceFormula/LineCount.lean`
(`New.lineStabilizer`, `New.lineRaise_lineLower`, `New.card_forms_missing_line`).
-/

public section

open Matrix IsLocalRing TauCeti Function
open scoped Pointwise

namespace HeckeRing.GLn

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ### Matrices over the residue field -/

section Field

variable {k : Type*} [Field k] {i : ι}

/-- An element of the stabiliser of the line `k eᵢ` has a nonzero `(i, i)` entry. -/
private theorem apply_self_ne_zero_of_mem_lineStabilizer {g : GL ι k}
    (hg : g ∈ lineStabilizer k i) : (g : Matrix ι ι k) i i ≠ 0 := by
  intro h
  have h0 : (g : Matrix ι ι k) *ᵥ Pi.single i 1 = 0 := by
    ext a
    rw [mulVec_single_one, col_apply, Pi.zero_apply]
    by_cases ha : a = i
    · rwa [ha]
    · exact mem_lineStabilizer_iff.mp hg a ha
  have h1 : (Pi.single i 1 : ι → k) = 0 := by
    rw [← one_mulVec (Pi.single i 1), ← Units.inv_mul g, ← mulVec_mulVec, h0, mulVec_zero]
  simpa using congrFun h1 i

/-- An element of the stabiliser of the hyperplane `xᵢ = 0` has a nonzero `(i, i)` entry. -/
private theorem apply_self_ne_zero_of_mem_hyperplaneStabilizer {g : GL ι k}
    (hg : g ∈ hyperplaneStabilizer k i) : (g : Matrix ι ι k) i i ≠ 0 := by
  intro h
  have h0 : Pi.single i 1 ᵥ* (g : Matrix ι ι k) = 0 := by
    ext b
    rw [single_one_vecMul, row_apply, Pi.zero_apply]
    by_cases hb : b = i
    · rwa [hb]
    · exact mem_hyperplaneStabilizer_iff.mp hg b hb
  have h1 : (Pi.single i 1 : ι → k) = 0 := by
    rw [← vecMul_one (Pi.single i 1), ← Units.mul_inv g, ← vecMul_vecMul, h0, zero_vecMul]
  simpa using congrFun h1 i

/-- The vector `eᵢ + c` of the `i`th row of `rowUnipotent c`, for `c` supported off `i`. -/
private def rowVec (c : {b // b ≠ i} → k) (b : ι) : k := if h : b = i then 1 else c ⟨b, h⟩

omit [Fintype ι] in
private theorem rowVec_self (c : {b // b ≠ i} → k) : rowVec c i = 1 := by
  simp [rowVec]

omit [Fintype ι] in
private theorem rowVec_coe (c : {b // b ≠ i} → k) (b : {b // b ≠ i}) : rowVec c b = c b := by
  simp [rowVec, b.property]

/-- The matrix that agrees with the identity off the `i`th row, whose `i`th row is `eᵢ + c`. Its
determinant is `1`. -/
private noncomputable def rowUnipotent (c : {b // b ≠ i} → k) : GL ι k :=
  GeneralLinearGroup.mkOfDetNeZero ((1 : Matrix ι ι k).updateRow i (rowVec c)) (by simp [rowVec])

private theorem rowUnipotent_apply (c : {b // b ≠ i} → k) (a b : ι) :
    (rowUnipotent c : Matrix ι ι k) a b = if a = i then rowVec c b else (1 : Matrix ι ι k) a b := by
  rw [rowUnipotent, GeneralLinearGroup.val_mkOfDetNeZero]
  split_ifs with ha
  · rw [ha, updateRow_self]
  · rw [updateRow_ne ha]

/-- The `i`th row of `rowUnipotent c` is `eᵢ + c`. -/
private theorem single_vecMul_rowUnipotent (c : {b // b ≠ i} → k) :
    Pi.single i 1 ᵥ* (rowUnipotent c : Matrix ι ι k) = rowVec c := by
  ext b
  rw [single_one_vecMul, row_apply, rowUnipotent_apply, ite_eq_left rfl]

/-- `rowUnipotent c` fixes `eᵢ`. -/
private theorem rowUnipotent_mem_lineStabilizer (c : {b // b ≠ i} → k) :
    rowUnipotent c ∈ lineStabilizer k i :=
  mem_lineStabilizer_iff.mpr fun a ha ↦ by
    rw [rowUnipotent_apply, ite_eq_right ha, one_apply_ne ha]

/-- The `i`th row of a matrix stabilising the hyperplane `xᵢ = 0` is a multiple of `eᵢ`. -/
private theorem single_vecMul_eq_of_mem_hyperplaneStabilizer {g : GL ι k}
    (hg : g ∈ hyperplaneStabilizer k i) :
    Pi.single i 1 ᵥ* (g : Matrix ι ι k) = (g : Matrix ι ι k) i i • Pi.single i 1 := by
  ext b
  rw [single_one_vecMul, row_apply, Pi.smul_apply, smul_eq_mul]
  by_cases hb : b = i
  · subst hb
    simp
  · rw [mem_hyperplaneStabilizer_iff.mp hg b hb, Pi.single_eq_of_ne hb, mul_zero]

/-- **Distinct `c` give distinct cosets.** If `rowUnipotent c * (rowUnipotent c')⁻¹` stabilises the
hyperplane `xᵢ = 0`, then `c = c'`. -/
private theorem eq_of_rowUnipotent_mul_inv_mem {c c' : {b // b ≠ i} → k}
    (h : rowUnipotent c * (rowUnipotent c')⁻¹ ∈ hyperplaneStabilizer k i) : c = c' := by
  set M := rowUnipotent c * (rowUnipotent c')⁻¹
  have hM : (rowUnipotent c : Matrix ι ι k) = (M : Matrix ι ι k) * rowUnipotent c' := by
    rw [← Units.val_mul, inv_mul_cancel_right]
  -- the `i`th rows satisfy `eᵢ + c = Mᵢᵢ (eᵢ + c')`, and comparing `i`th entries gives `Mᵢᵢ = 1`
  have hrow : rowVec c = (M : Matrix ι ι k) i i • rowVec c' := by
    rw [← single_vecMul_rowUnipotent, hM, ← vecMul_vecMul,
      single_vecMul_eq_of_mem_hyperplaneStabilizer h, smul_vecMul, single_vecMul_rowUnipotent]
  have hii : (M : Matrix ι ι k) i i = 1 := by
    simpa [rowVec] using (congrFun hrow i).symm
  rw [hii, one_smul] at hrow
  funext b
  simpa [rowVec, b.property] using congrFun hrow b

/-- **Every coset is reached.** For `p` stabilising the line `k eᵢ`, some `rowUnipotent c * p`
stabilises the hyperplane `xᵢ = 0`. -/
private theorem exists_rowUnipotent_mul_mem {p : GL ι k} (hp : p ∈ lineStabilizer k i) :
    ∃ c : {b // b ≠ i} → k, rowUnipotent c * p ∈ hyperplaneStabilizer k i := by
  -- `c` is read off the `i`th row `φ` of `p⁻¹`, normalised to have `i`th entry `1`
  set d := ((p⁻¹ : GL ι k) : Matrix ι ι k) i i
  have hd : d ≠ 0 := apply_self_ne_zero_of_mem_lineStabilizer (inv_mem hp)
  set φ := Pi.single i 1 ᵥ* ((p⁻¹ : GL ι k) : Matrix ι ι k)
  have hφ : φ ᵥ* (p : Matrix ι ι k) = Pi.single i 1 := by
    rw [vecMul_vecMul, ← Units.val_mul, inv_mul_cancel, Units.val_one, vecMul_one]
  refine ⟨fun b ↦ d⁻¹ * φ b, mem_hyperplaneStabilizer_iff.mpr fun b hb ↦ ?_⟩
  have hrow : rowVec (fun b : {b // b ≠ i} ↦ d⁻¹ * φ b) = d⁻¹ • φ := by
    funext a
    by_cases ha : a = i
    · subst ha
      simp only [rowVec, dite_true, Pi.smul_apply, smul_eq_mul, φ, single_one_vecMul, row_apply]
      exact (inv_mul_cancel₀ hd).symm
    · simp [rowVec, ha]
  have h := congrFun (congrArg (· ᵥ* (p : Matrix ι ι k)) hrow) b
  simp only [← single_vecMul_rowUnipotent, vecMul_vecMul, smul_vecMul, hφ] at h
  rw [single_one_vecMul, row_apply, ← Units.val_mul] at h
  rw [h, Pi.smul_apply, Pi.single_eq_of_ne hb, smul_zero]

/-- The `(i, i)` entry of `rowUnipotent c * M` is `(eᵢ + c) ⬝ Mᵢ`, with `Mᵢ` the `i`th column. -/
private theorem rowUnipotent_mul_apply_self (c : {b // b ≠ i} → k) (M : Matrix ι ι k) :
    ((rowUnipotent c : Matrix ι ι k) * M) i i = rowVec c ⬝ᵥ fun a ↦ M a i := by
  simp [Matrix.mul_apply, dotProduct, rowUnipotent_apply]

/-- A product `p' p` of a matrix stabilising the hyperplane `xᵢ = 0` and one stabilising the line
`k eᵢ` has nonzero `(i, i)` entry `p'ᵢᵢ pᵢᵢ`. -/
private theorem mul_apply_self_ne_zero {p p' : GL ι k} (hp' : p' ∈ hyperplaneStabilizer k i)
    (hp : p ∈ lineStabilizer k i) : ((p' * p : GL ι k) : Matrix ι ι k) i i ≠ 0 := by
  rw [coe_mul_apply_of_mem_lineStabilizer p' hp i]
  exact mul_ne_zero (apply_self_ne_zero_of_mem_hyperplaneStabilizer hp')
    (apply_self_ne_zero_of_mem_lineStabilizer hp)

/-- For `ξ` with `ξᵢᵢ ≠ 0` there is `p'` stabilising the hyperplane `xᵢ = 0` with `p'⁻¹ ξ`
stabilising the line `k eᵢ`: `p'` is the identity off the `i`th column, which is the `i`th column of
`ξ` scaled to have `i`th entry `1`. -/
private theorem exists_mem_hyperplaneStabilizer_inv_mul_mem {ξ : GL ι k}
    (hξ : (ξ : Matrix ι ι k) i i ≠ 0) :
    ∃ p' ∈ hyperplaneStabilizer k i, p'⁻¹ * ξ ∈ lineStabilizer k i := by
  set d := (ξ : Matrix ι ι k) i i
  set w : ι → k := d⁻¹ • (ξ : Matrix ι ι k) *ᵥ Pi.single i 1
  have hw : w i = 1 := by simp [w, d, hξ]
  have hdet : ((1 : Matrix ι ι k).updateCol i w).det ≠ 0 := by
    rw [← det_transpose, ← updateRow_transpose, transpose_one, det_updateRow_one, hw]
    exact one_ne_zero
  set p' := GeneralLinearGroup.mkOfDetNeZero _ hdet
  have hp' : (p' : Matrix ι ι k) = (1 : Matrix ι ι k).updateCol i w :=
    GeneralLinearGroup.val_mkOfDetNeZero _ _
  have hp'e : (p' : Matrix ι ι k) *ᵥ Pi.single i 1 = w := by
    ext a
    rw [hp', mulVec_single_one, col_apply, updateCol_self]
  refine ⟨p', mem_hyperplaneStabilizer_iff.mpr fun b hb ↦ ?_,
    mem_lineStabilizer_iff.mpr fun a ha ↦ ?_⟩
  · rw [hp', updateCol_ne hb, one_apply_ne (Ne.symm hb)]
  · -- `p'⁻¹ ξ eᵢ = d p'⁻¹ w = d eᵢ`
    have hcol : ((p'⁻¹ * ξ : GL ι k) : Matrix ι ι k) *ᵥ Pi.single i 1 = d • Pi.single i 1 := by
      have hξe : (ξ : Matrix ι ι k) *ᵥ Pi.single i 1 = d • w := by
        simp [w, smul_smul, mul_inv_cancel₀ hξ]
      rw [Units.val_mul, ← mulVec_mulVec, hξe, mulVec_smul, ← hp'e, mulVec_mulVec,
        ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mulVec]
    simpa [mulVec_single_one, Pi.single_eq_of_ne ha] using congrFun hcol a

variable [Finite k]

/-- **The count of linear forms missing a vector.** For `v : ι → k` with `v` not a multiple of
`eᵢ`, exactly `q^{n-1} - q^{n-2}` of the vectors `eᵢ + c` with `c` supported off `i` are not
orthogonal to `v`, where `q = |k|` and `n = |ι|`: the map `c ↦ ∑ c_b v_b` is a nonzero linear form,
whose fibres all have `q^{n-2}` elements. -/
private theorem card_filter_rowVec_dotProduct_ne_zero {v : ι → k} (hv : ∃ a, a ≠ i ∧ v a ≠ 0) :
    Nat.card {c : {b // b ≠ i} → k // rowVec c ⬝ᵥ v ≠ 0} =
      Nat.card k ^ (Fintype.card ι - 1) - Nat.card k ^ (Fintype.card ι - 2) := by
  classical
  have := Fintype.ofFinite k
  obtain ⟨a, ha, hva⟩ := hv
  set f : ({b // b ≠ i} → k) →+ k :=
    { toFun := fun c ↦ ∑ b, c b * v b
      map_zero' := by simp
      map_add' := fun c c' ↦ by simp [add_mul, Finset.sum_add_distrib] }
  have hfc (c : {b // b ≠ i} → k) : f c = ∑ b, c b * v b := rfl
  have hf (c : {b // b ≠ i} → k) : rowVec c ⬝ᵥ v = v i + f c := by
    rw [dotProduct, Fintype.sum_eq_add_sum_subtype_ne _ i, hfc, rowVec_self, one_mul]
    simp only [rowVec_coe]
  have hsurj : Surjective f := fun x ↦ ⟨Pi.single ⟨a, ha⟩ (x / v a), by
    rw [hfc, Finset.sum_eq_single (⟨a, ha⟩ : {b // b ≠ i})
      (fun b _ hb ↦ by rw [Pi.single_eq_of_ne hb, zero_mul]) (by simp), Pi.single_eq_same,
      div_mul_cancel₀ _ hva]⟩
  have hκ : Fintype.card {b // b ≠ i} = Fintype.card ι - 1 := by
    simp [Fintype.card_subtype_compl]
  -- all fibres of `f` have the same size `N`, and there are `q` of them
  set N := (Finset.univ.filter fun c ↦ f c = 0).card
  have hfib (x : k) : (Finset.univ.filter fun c ↦ f c = x).card = N :=
    AddMonoidHom.card_fiber_eq_of_mem_range f (hsurj x) (hsurj 0)
  have htot : Fintype.card k ^ (Fintype.card ι - 1) = Fintype.card k * N := by
    rw [← hκ, ← Fintype.card_fun, ← Finset.card_univ,
      Finset.card_eq_sum_card_fiberwise (f := f) (t := Finset.univ) (fun _ _ ↦ Finset.mem_coe.2
        (Finset.mem_univ _))]
    simp [hfib]
  have hN : N = Fintype.card k ^ (Fintype.card ι - 2) := by
    have hn : Fintype.card ι - 1 = Fintype.card ι - 2 + 1 := by
      have : 1 < Fintype.card ι := Fintype.one_lt_card_iff.mpr ⟨a, i, ha⟩
      omega
    rw [hn, pow_succ, mul_comm] at htot
    exact (Nat.eq_of_mul_eq_mul_left Fintype.card_pos htot).symm
  have hset : (Finset.univ.filter fun c ↦ rowVec c ⬝ᵥ v ≠ 0) =
      Finset.univ.filter fun c ↦ ¬ f c = -v i := by
    ext c
    simp [hf, eq_neg_iff_add_eq_zero, add_comm]
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype, hset, Finset.filter_not,
    Finset.card_sdiff_of_subset (Finset.filter_subset _ _), hfib, hN, Finset.card_univ,
    Fintype.card_fun, hκ, Nat.card_eq_fintype_card]

/-- When `v` is a multiple of `eᵢ` with `vᵢ ≠ 0`, every vector `eᵢ + c` with `c` supported off `i`
is not orthogonal to `v`. -/
private theorem card_filter_rowVec_dotProduct_ne_zero_of_forall {v : ι → k} (hvi : v i ≠ 0)
    (hv : ∀ a, a ≠ i → v a = 0) :
    Nat.card {c : {b // b ≠ i} → k // rowVec c ⬝ᵥ v ≠ 0} =
      Nat.card k ^ (Fintype.card ι - 1) := by
  classical
  have := Fintype.ofFinite k
  have hκ : Fintype.card {b // b ≠ i} = Fintype.card ι - 1 := by
    simp [Fintype.card_subtype_compl]
  have h (c : {b // b ≠ i} → k) : rowVec c ⬝ᵥ v = v i := by
    rw [dotProduct, Finset.sum_eq_single i (fun b _ hb ↦ by rw [hv b hb, mul_zero]) (by simp)]
    simp [rowVec]
  rw [Nat.card_congr (Equiv.subtypeUnivEquiv fun c ↦ by rw [h c]; exact hvi),
    Nat.card_eq_fintype_card, Fintype.card_fun, hκ, Nat.card_eq_fintype_card]

end Field

/-! ### The stabiliser of a line modulo the maximal ideal -/

section Defs

variable (R K : Type*) [CommRing R] [IsLocalRing R] [CommRing K] [Algebra R K] (i : ι)

/-- **The stabiliser `J` of the line `k eᵢ` modulo the maximal ideal**, as a subgroup of
`GL_ι(K)`: the image of the `g ∈ GL_ι(R)` whose reduction to the residue field `k` lies in the
stabiliser `TauCeti.lineStabilizer k i` of the line through the basis vector `eᵢ`. These are the
`g` whose `i`th column is congruent to a multiple of `eᵢ` (`HeckeRing.GLn.mem_lineParahoric_iff`).
It is the parahoric subgroup of the lattice chain `Rⁿ ⊃ R eᵢ + 𝔪 Rⁿ`. -/
noncomputable def lineParahoric : Subgroup (GL ι K) :=
  ((lineStabilizer (ResidueField R) i).comap (GeneralLinearGroup.map (residue R))).map
    (GeneralLinearGroup.map (algebraMap R K))

/-- The defining equation of `lineParahoric`, for modules that import it: the definition is not
exposed. -/
theorem lineParahoric_def :
    lineParahoric R K i = ((lineStabilizer (ResidueField R) i).comap
      (GeneralLinearGroup.map (residue R))).map (GeneralLinearGroup.map (algebraMap R K)) :=
  (rfl)

variable {R K i}

/-- **Membership in `J`**: `g ∈ J` exactly when `g` is the image of some
`γ ∈ GL_ι(R)` whose entries `γ_{a i}` with `a ≠ i` lie in the maximal ideal. -/
theorem mem_lineParahoric_iff {g : GL ι K} :
    g ∈ lineParahoric R K i ↔ ∃ γ : GL ι R, GeneralLinearGroup.map (algebraMap R K) γ = g ∧
      ∀ a, a ≠ i → (γ : Matrix ι ι R) a i ∈ maximalIdeal R := by
  simp only [lineParahoric, Subgroup.mem_map, Subgroup.mem_comap, mem_lineStabilizer_iff,
    GeneralLinearGroup.map_apply, residue_eq_zero_iff]
  exact ⟨fun ⟨γ, hγ, h⟩ ↦ ⟨γ, h, hγ⟩, fun ⟨γ, h, hγ⟩ ↦ ⟨γ, hγ, h⟩⟩

/-- The stabiliser `J` of a line modulo the maximal ideal lies in `GL_ι(R)`. -/
theorem lineParahoric_le_integralGL : lineParahoric R K i ≤ integralGL R K ι := by
  rintro g hg
  obtain ⟨γ, hγ, -⟩ := mem_lineParahoric_iff.mp hg
  exact ⟨γ, hγ⟩

end Defs

section DVR

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] {K : Type*} [Field K]
  [Algebra R K] {ϖ : R} {π : Kˣ} {i : ι}

/-- Reduction stabilises the line `k eᵢ` exactly when the entries `γ_{a i}`, `a ≠ i`, lie in the
maximal ideal. -/
private theorem map_residue_mem_lineStabilizer_iff (γ : GL ι R) :
    GeneralLinearGroup.map (residue R) γ ∈ lineStabilizer (ResidueField R) i ↔
      ∀ a, a ≠ i → (γ : Matrix ι ι R) a i ∈ maximalIdeal R := by
  simp only [mem_lineStabilizer_iff, GeneralLinearGroup.map_apply, residue_eq_zero_iff]

/-- Reduction stabilises the hyperplane `xᵢ = 0` exactly when the entries `γ_{i b}`, `b ≠ i`, lie
in the maximal ideal. -/
private theorem map_residue_mem_hyperplaneStabilizer_iff (γ : GL ι R) :
    GeneralLinearGroup.map (residue R) γ ∈ hyperplaneStabilizer (ResidueField R) i ↔
      ∀ b, b ≠ i → (γ : Matrix ι ι R) i b ∈ maximalIdeal R := by
  simp only [mem_hyperplaneStabilizer_iff, GeneralLinearGroup.map_apply, residue_eq_zero_iff]

private theorem map_mem_lineParahoric {γ : GL ι R}
    (hγ : GeneralLinearGroup.map (residue R) γ ∈ lineStabilizer (ResidueField R) i) :
    GeneralLinearGroup.map (algebraMap R K) γ ∈ lineParahoric R K i :=
  Subgroup.mem_map_of_mem _ hγ

omit [IsDomain R] [IsDiscreteValuationRing R] in
/-- If the entries of a conjugate `(diag s) γ (diag s)⁻¹` of `γ ∈ GL_ι(R)` are those of a matrix
`A` over `R`, the conjugate is an element of `GL_ι(R)` with matrix `A`. -/
private theorem exists_map_eq_diagGL_conj (hinj : Injective (algebraMap R K)) (s : ι → Kˣ)
    (γ : GL ι R) {A : Matrix ι ι R}
    (hA : ∀ a b, algebraMap R K (A a b) =
      (s a : K) * algebraMap R K ((γ : Matrix ι ι R) a b) * ((s b)⁻¹ : Kˣ)) :
    ∃ γ' : GL ι R, GeneralLinearGroup.map (algebraMap R K) γ' =
      diagGL s * GeneralLinearGroup.map (algebraMap R K) γ * (diagGL s)⁻¹ ∧
        (γ' : Matrix ι ι R) = A := by
  have hconj : A.map (algebraMap R K) =
      ↑((diagGL s)⁻¹⁻¹ * GeneralLinearGroup.map (algebraMap R K) γ * (diagGL s)⁻¹) := by
    ext a b
    rw [map_apply, hA, inv_inv, diagGL_mul_mul_inv_apply, GeneralLinearGroup.map_apply]
  obtain ⟨γ', hγ'⟩ := inv_mul_map_mul_mem_integralGL_of_map_eq hinj hconj
  rw [inv_inv] at hγ' hconj
  refine ⟨γ', hγ', ?_⟩
  ext a b
  apply hinj
  rw [← GeneralLinearGroup.map_apply, hγ', ← hconj, map_apply]

/-- Conjugating `γ ∈ GL_ι(R)` by `t⁻¹` divides the entries `γ_{i b}` by `π` and multiplies the
entries `γ_{a i}` by `π`; if the `γ_{i b}`, `b ≠ i`, lie in the maximal ideal, the result lies in
`J`. -/
private theorem inv_mul_map_mul_mem_lineParahoric (hϖ : Irreducible ϖ)
    (hπ : algebraMap R K ϖ = π) {γ : GL ι R}
    (hrow : ∀ b, b ≠ i → (γ : Matrix ι ι R) i b ∈ maximalIdeal R) :
    (diagGL (Pi.mulSingle i π))⁻¹ * GeneralLinearGroup.map (algebraMap R K) γ *
      diagGL (Pi.mulSingle i π) ∈ lineParahoric R K i := by
  have hinj : Injective (algebraMap R K) :=
    TauCeti.IsDiscreteValuationRing.injective_of_map_ne_zero _ hϖ (hπ ▸ π.ne_zero)
  have hϖm : ϖ ∈ maximalIdeal R := hϖ.maximalIdeal_eq ▸ Ideal.mem_span_singleton_self ϖ
  have hent (a b : ι) : ∃ r : R, algebraMap R K r = ((Pi.mulSingle i π⁻¹ : ι → Kˣ) a : K) *
      algebraMap R K ((γ : Matrix ι ι R) a b) * (((Pi.mulSingle i π⁻¹ : ι → Kˣ) b)⁻¹ : Kˣ) := by
    by_cases ha : a = i <;> by_cases hb : b = i
    · refine ⟨(γ : Matrix ι ι R) a b, ?_⟩
      rw [ha, hb, Pi.mulSingle_eq_same, inv_inv, Units.val_inv_eq_inv_val]
      field_simp
    · obtain ⟨d, hd⟩ := Ideal.mem_span_singleton'.mp (hϖ.maximalIdeal_eq ▸ hrow b hb)
      refine ⟨d, ?_⟩
      rw [ha, ← hd, Pi.mulSingle_eq_same, Pi.mulSingle_eq_of_ne hb, inv_one, Units.val_one,
        mul_one, map_mul, hπ, Units.val_inv_eq_inv_val]
      field_simp
    · refine ⟨(γ : Matrix ι ι R) a b * ϖ, ?_⟩
      rw [hb]
      simp [Pi.mulSingle_eq_of_ne ha, hπ]
    · exact ⟨(γ : Matrix ι ι R) a b, by simp [Pi.mulSingle_eq_of_ne ha, Pi.mulSingle_eq_of_ne hb]⟩
  choose A hA using hent
  obtain ⟨γ', hγ'g, hγ'A⟩ := exists_map_eq_diagGL_conj hinj _ γ (A := Matrix.of A) hA
  rw [Pi.mulSingle_inv, map_inv, inv_inv] at hγ'g
  refine hγ'g ▸ mem_lineParahoric_iff.mpr ⟨γ', rfl, fun a ha ↦ ?_⟩
  have h := hA a i
  simp only [Pi.mulSingle_eq_same, Pi.mulSingle_eq_of_ne ha, Units.val_one, inv_inv, one_mul,
    ← hπ, ← map_mul] at h
  rw [hγ'A, of_apply, hinj h]
  exact Ideal.mul_mem_left _ _ hϖm

/-- Conjugating `γ ∈ GL_ι(R)` by `t` multiplies the entries `γ_{i b}` by `π` and divides the
entries `γ_{a i}` by `π`; if the `γ_{a i}`, `a ≠ i`, lie in the maximal ideal, the result lies in
`GL_ι(R)` with its entries `(i, b)`, `b ≠ i`, in the maximal ideal. -/
private theorem exists_map_eq_mul_map_mul_inv (hϖ : Irreducible ϖ) (hπ : algebraMap R K ϖ = π)
    {γ : GL ι R} (hcol : ∀ a, a ≠ i → (γ : Matrix ι ι R) a i ∈ maximalIdeal R) :
    ∃ γ' : GL ι R, GeneralLinearGroup.map (algebraMap R K) γ' =
      diagGL (Pi.mulSingle i π) * GeneralLinearGroup.map (algebraMap R K) γ *
        (diagGL (Pi.mulSingle i π))⁻¹ ∧
      ∀ b, b ≠ i → (γ' : Matrix ι ι R) i b ∈ maximalIdeal R := by
  have hinj : Injective (algebraMap R K) :=
    TauCeti.IsDiscreteValuationRing.injective_of_map_ne_zero _ hϖ (hπ ▸ π.ne_zero)
  have hϖm : ϖ ∈ maximalIdeal R := hϖ.maximalIdeal_eq ▸ Ideal.mem_span_singleton_self ϖ
  have hent (a b : ι) : ∃ r : R, algebraMap R K r = ((Pi.mulSingle i π : ι → Kˣ) a : K) *
      algebraMap R K ((γ : Matrix ι ι R) a b) * (((Pi.mulSingle i π : ι → Kˣ) b)⁻¹ : Kˣ) := by
    by_cases ha : a = i <;> by_cases hb : b = i
    · refine ⟨(γ : Matrix ι ι R) a b, ?_⟩
      rw [ha, hb, Pi.mulSingle_eq_same, Units.val_inv_eq_inv_val]
      field_simp
    · refine ⟨ϖ * (γ : Matrix ι ι R) a b, ?_⟩
      rw [ha]
      simp [Pi.mulSingle_eq_of_ne hb, hπ]
    · obtain ⟨d, hd⟩ := Ideal.mem_span_singleton'.mp (hϖ.maximalIdeal_eq ▸ hcol a ha)
      refine ⟨d, ?_⟩
      rw [hb, ← hd]
      simp [Pi.mulSingle_eq_of_ne ha, hπ, π.ne_zero]
    · exact ⟨(γ : Matrix ι ι R) a b, by simp [Pi.mulSingle_eq_of_ne ha, Pi.mulSingle_eq_of_ne hb]⟩
  choose A hA using hent
  obtain ⟨γ', hγ'g, hγ'A⟩ := exists_map_eq_diagGL_conj hinj _ γ (A := Matrix.of A) hA
  refine ⟨γ', hγ'g, fun b hb ↦ ?_⟩
  have h := hA i b
  simp only [Pi.mulSingle_eq_same, Pi.mulSingle_eq_of_ne hb, inv_one, Units.val_one, mul_one,
    ← hπ, ← map_mul] at h
  rw [hγ'A, of_apply, hinj h]
  exact Ideal.mul_mem_right _ _ hϖm

/-- **The conjugate `t J t⁻¹`**, for `t = diag(1, …, π, …, 1)` with `π` in position `i`: it is the
set of `g ∈ GL_ι(R)` whose entries `g_{i b}`, `b ≠ i`, lie in the maximal ideal, the stabiliser of
the hyperplane `xᵢ = 0` modulo the maximal ideal. -/
theorem mem_conjAct_lineParahoric_iff (hϖ : Irreducible ϖ) (hπ : algebraMap R K ϖ = π)
    {g : GL ι K} :
    g ∈ ConjAct.toConjAct (diagGL (Pi.mulSingle i π)) • lineParahoric R K i ↔
      ∃ γ : GL ι R, GeneralLinearGroup.map (algebraMap R K) γ = g ∧
        ∀ b, b ≠ i → (γ : Matrix ι ι R) i b ∈ maximalIdeal R := by
  rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ← ConjAct.toConjAct_inv, ConjAct.smul_def,
    ConjAct.ofConjAct_toConjAct, inv_inv]
  constructor
  · intro h
    obtain ⟨γ, hγ, hcol⟩ := mem_lineParahoric_iff.mp h
    obtain ⟨γ', hγ'g, hrow⟩ := exists_map_eq_mul_map_mul_inv hϖ hπ hcol
    exact ⟨γ', by rw [hγ'g, hγ]; group, hrow⟩
  · rintro ⟨γ, rfl, hrow⟩
    exact inv_mul_map_mul_mem_lineParahoric hϖ hπ hrow

/-- Inverse transpose carries the stabiliser of the line `k eᵢ` modulo the maximal ideal onto its
conjugate `t J t⁻¹`, the stabiliser of the hyperplane `xᵢ = 0`. -/
theorem map_inverseTranspose_lineParahoric (hϖ : Irreducible ϖ) (hπ : algebraMap R K ϖ = π) :
    (lineParahoric R K i).map
        (GeneralLinearGroup.inverseTranspose : GL ι K ≃* GL ι K).toMonoidHom =
      ConjAct.toConjAct (diagGL (Pi.mulSingle i π)) • lineParahoric R K i := by
  ext g
  rw [Subgroup.mem_map_equiv, GeneralLinearGroup.inverseTranspose_symm, mem_lineParahoric_iff,
    mem_conjAct_lineParahoric_iff hϖ hπ]
  have hmap (γ : GL ι R) :
      GeneralLinearGroup.map (algebraMap R K) (GeneralLinearGroup.inverseTranspose γ) =
        GeneralLinearGroup.inverseTranspose (GeneralLinearGroup.map (algebraMap R K) γ) :=
    GeneralLinearGroup.map_inverseTranspose (algebraMap R K) γ
  have hred (γ : GL ι R) :
      GeneralLinearGroup.map (residue R) (GeneralLinearGroup.inverseTranspose γ) =
        GeneralLinearGroup.inverseTranspose (GeneralLinearGroup.map (residue R) γ) :=
    GeneralLinearGroup.map_inverseTranspose (residue R) γ
  -- over the residue field, inverse transpose exchanges the line and the hyperplane stabilisers
  have hPQ := map_inverseTranspose_lineStabilizer (K := ResidueField R) i
  constructor
  · rintro ⟨γ, hγ, hcol⟩
    refine ⟨GeneralLinearGroup.inverseTranspose γ, by
      rw [hmap, hγ, GeneralLinearGroup.inverseTranspose_inverseTranspose],
      (map_residue_mem_hyperplaneStabilizer_iff _).mp ?_⟩
    rw [hred, ← hPQ]
    exact Subgroup.mem_map_of_mem _ ((map_residue_mem_lineStabilizer_iff γ).mpr hcol)
  · rintro ⟨γ, rfl, hrow⟩
    refine ⟨GeneralLinearGroup.inverseTranspose γ, hmap γ,
      (map_residue_mem_lineStabilizer_iff _).mp ?_⟩
    have hQ := (map_residue_mem_hyperplaneStabilizer_iff γ).mpr hrow
    rw [← hPQ, Subgroup.mem_map_equiv, GeneralLinearGroup.inverseTranspose_symm] at hQ
    rwa [hred]

/-- **`J t J` and `J t⁻¹ J` have the same degree**: `[J : J ∩ t⁻¹ J t] = [J : J ∩ t J t⁻¹]`.
Conjugating by `t` turns the first index into `[t J t⁻¹ : J ∩ t J t⁻¹]`, and inverse transpose
exchanges `J` and `t J t⁻¹`. -/
theorem relIndex_conjAct_inv_lineParahoric_eq (hϖ : Irreducible ϖ)
    (hπ : algebraMap R K ϖ = π) :
    (ConjAct.toConjAct (diagGL (Pi.mulSingle i π))⁻¹ • lineParahoric R K i).relIndex
        (lineParahoric R K i) =
      (ConjAct.toConjAct (diagGL (Pi.mulSingle i π)) • lineParahoric R K i).relIndex
        (lineParahoric R K i) := by
  set J := lineParahoric R K i
  set t := diagGL (Pi.mulSingle i π)
  set σ := (GeneralLinearGroup.inverseTranspose : GL ι K ≃* GL ι K).toMonoidHom
  have hσJ : J.map σ = ConjAct.toConjAct t • J := map_inverseTranspose_lineParahoric hϖ hπ
  have hσσ : (J.map σ).map σ = J := by
    ext g
    simp [σ]
  rw [← Subgroup.relIndex_pointwise_smul (ConjAct.toConjAct t), smul_smul, ← map_mul,
    mul_inv_cancel, map_one, one_smul, ← hσJ,
    ← Subgroup.relIndex_map_map_of_injective (f := σ) J (J.map σ)
      (GeneralLinearGroup.inverseTranspose (n := ι) (A := K)).injective, hσσ]

variable (R) in
/-- A lift to `GL_ι(R)` of an element of `GL_ι(k)`. -/
private noncomputable def liftGL : GL ι (ResidueField R) → GL ι R :=
  surjInv (GeneralLinearGroup.map_surjective (residue R) residue_surjective)

private theorem map_residue_liftGL (p : GL ι (ResidueField R)) :
    GeneralLinearGroup.map (residue R) (liftGL R p) = p :=
  surjInv_eq _ p

variable (R) in
/-- The representatives `u t` of the left cosets of `J` in `J t J`, for `u` lifting the inverse
of `rowUnipotent c`. -/
private noncomputable def cosetRep (π : Kˣ) (i : ι) (c : {b // b ≠ i} → ResidueField R) :
    GL ι K :=
  GeneralLinearGroup.map (algebraMap R K) (liftGL R (rowUnipotent c)⁻¹) *
    diagGL (Pi.mulSingle i π)

private theorem map_liftGL_inv_rowUnipotent_mem (c : {b // b ≠ i} → ResidueField R) :
    GeneralLinearGroup.map (algebraMap R K) (liftGL R (rowUnipotent c)⁻¹) ∈
      lineParahoric R K i :=
  map_mem_lineParahoric (by
    rw [map_residue_liftGL]
    exact inv_mem (rowUnipotent_mem_lineStabilizer c))

/-- **The coset decomposition of `J t J`**: the `cosetRep c` are representatives of the distinct
left cosets of `J` in `J t J`. -/
private theorem isCosetSystem_cosetRep (hϖ : Irreducible ϖ) (hπ : algebraMap R K ϖ = π) :
    Subgroup.IsCosetSystem (lineParahoric R K i) (lineParahoric R K i)
      (diagGL (Pi.mulSingle i π)) (cosetRep R π i) := by
  have hinj : Injective (GeneralLinearGroup.map (n := ι) (algebraMap R K)) :=
    GeneralLinearGroup.map_injective
      (TauCeti.IsDiscreteValuationRing.injective_of_map_ne_zero _ hϖ (hπ ▸ π.ne_zero))
  set J := lineParahoric R K i
  set t := diagGL (Pi.mulSingle i π) with ht
  refine ⟨fun c ↦ DoubleCoset.mem_doubleCoset.mpr ⟨_, map_liftGL_inv_rowUnipotent_mem c, 1,
    J.one_mem, by rw [cosetRep, mul_one]⟩, fun x hx ↦ ?_, fun c c' h ↦ ?_⟩
  · -- `x = a t b`; choose `c` with `rowUnipotent c` straightening the reduction of `a`
    obtain ⟨a, ha, b, hb, rfl⟩ := DoubleCoset.mem_doubleCoset.mp hx
    obtain ⟨γ, rfl, hcol⟩ := mem_lineParahoric_iff.mp ha
    obtain ⟨c, hc⟩ := exists_rowUnipotent_mul_mem ((map_residue_mem_lineStabilizer_iff γ).mpr hcol)
    have hconj : (GeneralLinearGroup.map (algebraMap R K) (liftGL R (rowUnipotent c)⁻¹))⁻¹ *
        GeneralLinearGroup.map (algebraMap R K) γ ∈ ConjAct.toConjAct t • J := by
      refine (mem_conjAct_lineParahoric_iff hϖ hπ).mpr
        ⟨(liftGL R (rowUnipotent c)⁻¹)⁻¹ * γ, by rw [map_mul, map_inv], ?_⟩
      refine (map_residue_mem_hyperplaneStabilizer_iff _).mp ?_
      rwa [map_mul, map_inv, map_residue_liftGL, inv_inv]
    rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ← ConjAct.toConjAct_inv, ConjAct.smul_def,
      ConjAct.ofConjAct_toConjAct, inv_inv] at hconj
    refine Set.mem_iUnion.mpr ⟨c, mem_leftCoset_iff _ |>.mpr ?_⟩
    have heq : (cosetRep R π i c)⁻¹ * (GeneralLinearGroup.map (algebraMap R K) γ * t * b) =
        t⁻¹ * ((GeneralLinearGroup.map (algebraMap R K) (liftGL R (rowUnipotent c)⁻¹))⁻¹ *
          GeneralLinearGroup.map (algebraMap R K) γ) * t * b := by
      rw [cosetRep, ← ht]
      group
    rw [SetLike.mem_coe, heq]
    exact J.mul_mem hconj hb
  · -- equal cosets force `rowUnipotent c (rowUnipotent c')⁻¹` to fix the hyperplane `xᵢ = 0`
    have h' := QuotientGroup.eq.mp h
    have hconj : (GeneralLinearGroup.map (algebraMap R K) (liftGL R (rowUnipotent c)⁻¹))⁻¹ *
        GeneralLinearGroup.map (algebraMap R K) (liftGL R (rowUnipotent c')⁻¹) ∈
          ConjAct.toConjAct t • J := by
      have heq : (cosetRep R π i c)⁻¹ * cosetRep R π i c' = t⁻¹ *
          ((GeneralLinearGroup.map (algebraMap R K) (liftGL R (rowUnipotent c)⁻¹))⁻¹ *
            GeneralLinearGroup.map (algebraMap R K) (liftGL R (rowUnipotent c')⁻¹)) * t := by
        rw [cosetRep, cosetRep, ← ht]
        group
      rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ← ConjAct.toConjAct_inv, ConjAct.smul_def,
        ConjAct.ofConjAct_toConjAct, inv_inv, ← heq]
      exact h'
    obtain ⟨γ, hγ, hrow⟩ := (mem_conjAct_lineParahoric_iff hϖ hπ).mp hconj
    rw [← map_inv, ← map_mul] at hγ
    rw [hinj hγ] at hrow
    refine eq_of_rowUnipotent_mul_inv_mem ?_
    have := (map_residue_mem_hyperplaneStabilizer_iff _).mpr hrow
    rwa [map_mul, map_inv, map_residue_liftGL, map_residue_liftGL, inv_inv] at this

/-- **`J t J` is the union of `q^{n-1}` left cosets of `J`**, where `q` is the size of the residue
field and `n = |ι|`: `[J : J ∩ t J t⁻¹] = q^{n-1}`. -/
theorem relIndex_conjAct_lineParahoric (hϖ : Irreducible ϖ) (hπ : algebraMap R K ϖ = π) :
    (ConjAct.toConjAct (diagGL (Pi.mulSingle i π)) • lineParahoric R K i).relIndex
        (lineParahoric R K i) = Nat.card (ResidueField R) ^ (Fintype.card ι - 1) := by
  rw [← (isCosetSystem_cosetRep hϖ hπ).natCard_eq_relIndex, Nat.card_fun, Nat.card_eq_fintype_card
    (α := {b // b ≠ i})]
  simp [Fintype.card_subtype_compl]

/-- **`J t⁻¹ J` is the union of `q^{n-1}` left cosets of `J`**: `[J : J ∩ t⁻¹ J t] = q^{n-1}`. -/
theorem relIndex_conjAct_inv_lineParahoric (hϖ : Irreducible ϖ) (hπ : algebraMap R K ϖ = π) :
    (ConjAct.toConjAct (diagGL (Pi.mulSingle i π))⁻¹ • lineParahoric R K i).relIndex
        (lineParahoric R K i) = Nat.card (ResidueField R) ^ (Fintype.card ι - 1) := by
  rw [relIndex_conjAct_inv_lineParahoric_eq hϖ hπ, relIndex_conjAct_lineParahoric hϖ hπ]

/-- The index of `J` in `GL_ι(R)` is the index of the stabiliser of the line `k eᵢ` in `GL_ι(k)`.
-/
theorem relIndex_lineParahoric (hϖ : Irreducible ϖ) (hπ : algebraMap R K ϖ = π) :
    (lineParahoric R K i).relIndex (integralGL R K ι) =
      (lineStabilizer (ResidueField R) i).index := by
  have hinj : Injective (GeneralLinearGroup.map (n := ι) (algebraMap R K)) :=
    GeneralLinearGroup.map_injective
      (TauCeti.IsDiscreteValuationRing.injective_of_map_ne_zero _ hϖ (hπ ▸ π.ne_zero))
  rw [lineParahoric, integralGL, MonoidHom.range_eq_map,
    Subgroup.relIndex_map_map_of_injective _ _ hinj, Subgroup.relIndex_top_right,
    Subgroup.index_comap_of_surjective _
      (GeneralLinearGroup.map_surjective (residue R) residue_surjective)]

/-- **The index of `J`** in `GL_ι(R)` is the number `(qⁿ - 1)/(q - 1)` of lines in `kⁿ`, stated
without division: `[GL_ι(R) : J] (q - 1) = qⁿ - 1`. -/
theorem relIndex_lineParahoric_mul (hϖ : Irreducible ϖ) (hπ : algebraMap R K ϖ = π) :
    (lineParahoric R K i).relIndex (integralGL R K ι) * (Nat.card (ResidueField R) - 1) =
      Nat.card (ResidueField R) ^ Fintype.card ι - 1 := by
  rw [relIndex_lineParahoric hϖ hπ, index_lineStabilizer_mul i]

/-- `J` has finite index in `GL_ι(R)`. -/
theorem isFiniteRelIndex_lineParahoric [Finite (ResidueField R)] (hϖ : Irreducible ϖ)
    (hπ : algebraMap R K ϖ = π) :
    (lineParahoric R K i).IsFiniteRelIndex (integralGL R K ι) :=
  ⟨by rw [relIndex_lineParahoric hϖ hπ]; exact Subgroup.index_ne_zero_of_finite⟩

/-- **The double coset `J t⁻¹ J`**: `t⁻¹ z ∈ J t⁻¹ J` exactly when `z ∈ GL_ι(R)` and its `(i, i)`
entry is a unit. -/
theorem inv_mul_mem_doubleCoset_inv_lineParahoric_iff (hϖ : Irreducible ϖ)
    (hπ : algebraMap R K ϖ = π) {z : GL ι K} :
    (diagGL (Pi.mulSingle i π))⁻¹ * z ∈ DoubleCoset.doubleCoset (diagGL (Pi.mulSingle i π))⁻¹
        (lineParahoric R K i) (lineParahoric R K i) ↔
      ∃ ξ : GL ι R, GeneralLinearGroup.map (algebraMap R K) ξ = z ∧
        IsUnit ((ξ : Matrix ι ι R) i i) := by
  set J := lineParahoric R K i
  set t := diagGL (Pi.mulSingle i π)
  constructor
  · -- `z = (t a t⁻¹) b`, a product of a matrix with `i`th row and one with `i`th column
    -- vanishing off the diagonal modulo the maximal ideal
    rintro hz
    obtain ⟨a, ha, b, hb, h⟩ := DoubleCoset.mem_doubleCoset.mp hz
    have hta : t * a * t⁻¹ ∈ ConjAct.toConjAct t • J := by
      rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ← ConjAct.toConjAct_inv, ConjAct.smul_def,
        ConjAct.ofConjAct_toConjAct, inv_inv]
      simpa [mul_assoc] using ha
    obtain ⟨γ₁, hγ₁, hrow⟩ := (mem_conjAct_lineParahoric_iff hϖ hπ).mp hta
    obtain ⟨γ₂, hγ₂, hcol⟩ := mem_lineParahoric_iff.mp hb
    refine ⟨γ₁ * γ₂, ?_, ?_⟩
    · rw [map_mul, hγ₁, hγ₂, ← inv_mul_eq_iff_eq_mul.mpr h.symm]
      group
    · rw [← residue_ne_zero_iff_isUnit, ← GeneralLinearGroup.map_apply, map_mul]
      exact mul_apply_self_ne_zero ((map_residue_mem_hyperplaneStabilizer_iff γ₁).mpr hrow)
        ((map_residue_mem_lineStabilizer_iff γ₂).mpr hcol)
  · -- conversely `z = u (u⁻¹ z)`, with `u` lifting a matrix stabilising the hyperplane `xᵢ = 0`
    rintro ⟨ξ, rfl, hξ⟩
    rw [← residue_ne_zero_iff_isUnit, ← GeneralLinearGroup.map_apply] at hξ
    obtain ⟨p', hp', hp'ξ⟩ := exists_mem_hyperplaneStabilizer_inv_mul_mem hξ
    have hu : GeneralLinearGroup.map (algebraMap R K) (liftGL R p') ∈ ConjAct.toConjAct t • J :=
      (mem_conjAct_lineParahoric_iff hϖ hπ).mpr ⟨_, rfl,
        (map_residue_mem_hyperplaneStabilizer_iff _).mp (by rw [map_residue_liftGL]; exact hp')⟩
    rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ← ConjAct.toConjAct_inv, ConjAct.smul_def,
      ConjAct.ofConjAct_toConjAct, inv_inv] at hu
    have hv : GeneralLinearGroup.map (algebraMap R K) ((liftGL R p')⁻¹ * ξ) ∈ J :=
      map_mem_lineParahoric (by rw [map_mul, map_inv, map_residue_liftGL]; exact hp'ξ)
    refine DoubleCoset.mem_doubleCoset.mpr ⟨_, hu, _, hv, ?_⟩
    rw [map_mul, map_inv]
    group

/-- **The coset criterion.** For `x ∈ GL_ι(R)` with `(i, i)` column `v` of residues,
`(u t)⁻¹ x ∈ J t⁻¹ J` for the representative `u t = cosetRep c` exactly when `(eᵢ + c) ⬝ v ≠ 0`. -/
private theorem cosetRep_inv_mul_mem_iff (hϖ : Irreducible ϖ) (hπ : algebraMap R K ϖ = π)
    (ξ₀ : GL ι R) (c : {b // b ≠ i} → ResidueField R) :
    (cosetRep R π i c)⁻¹ * GeneralLinearGroup.map (algebraMap R K) ξ₀ ∈
        DoubleCoset.doubleCoset (diagGL (Pi.mulSingle i π))⁻¹ (lineParahoric R K i)
          (lineParahoric R K i) ↔
      (rowVec c ⬝ᵥ fun a ↦ residue R ((ξ₀ : Matrix ι ι R) a i)) ≠ 0 := by
  have hinj : Injective (GeneralLinearGroup.map (n := ι) (algebraMap R K)) :=
    GeneralLinearGroup.map_injective
      (TauCeti.IsDiscreteValuationRing.injective_of_map_ne_zero _ hϖ (hπ ▸ π.ne_zero))
  -- `(u t)⁻¹ x = t⁻¹ (u⁻¹ x)` with `u⁻¹ x ∈ GL_ι(R)`, whose reduction is `rowUnipotent c * x`
  have hred : GeneralLinearGroup.map (residue R) ((liftGL R (rowUnipotent c)⁻¹)⁻¹ * ξ₀) =
      rowUnipotent c * GeneralLinearGroup.map (residue R) ξ₀ := by
    rw [map_mul, map_inv, map_residue_liftGL, inv_inv]
  rw [cosetRep, _root_.mul_inv_rev, mul_assoc, inv_mul_mem_doubleCoset_inv_lineParahoric_iff hϖ hπ]
  constructor
  · rintro ⟨ξ, hξ, hunit⟩
    rw [← map_inv, ← map_mul] at hξ
    rw [hinj hξ, ← residue_ne_zero_iff_isUnit, ← GeneralLinearGroup.map_apply, hred, Units.val_mul,
      rowUnipotent_mul_apply_self] at hunit
    simpa [GeneralLinearGroup.map_apply] using hunit
  · intro h
    refine ⟨(liftGL R (rowUnipotent c)⁻¹)⁻¹ * ξ₀, by rw [map_mul, map_inv], ?_⟩
    rw [← residue_ne_zero_iff_isUnit, ← GeneralLinearGroup.map_apply, hred, Units.val_mul,
      rowUnipotent_mul_apply_self]
    simpa [GeneralLinearGroup.map_apply] using h

open Classical in
/-- **The count of cosets.** The number of representatives `u t` of the cosets in `J t J` with
`(u t)⁻¹ x ∈ J t⁻¹ J` is `q^{n-1}` for `x ∈ J`, `q^{n-1} - q^{n-2}` for `x ∈ GL_ι(R) ∖ J` and `0`
for `x ∉ GL_ι(R)`. -/
private theorem natCard_cosetRep_inv_mul_mem [Finite (ResidueField R)] (hϖ : Irreducible ϖ)
    (hπ : algebraMap R K ϖ = π) (x : GL ι K) :
    Nat.card {c // (cosetRep R π i c)⁻¹ * x ∈ DoubleCoset.doubleCoset
        (diagGL (Pi.mulSingle i π))⁻¹ (lineParahoric R K i) (lineParahoric R K i)} =
      if x ∈ lineParahoric R K i then Nat.card (ResidueField R) ^ (Fintype.card ι - 1)
      else if x ∈ integralGL R K ι then
        Nat.card (ResidueField R) ^ (Fintype.card ι - 1) -
          Nat.card (ResidueField R) ^ (Fintype.card ι - 2)
      else 0 := by
  have hinj : Injective (GeneralLinearGroup.map (n := ι) (algebraMap R K)) :=
    GeneralLinearGroup.map_injective
      (TauCeti.IsDiscreteValuationRing.injective_of_map_ne_zero _ hϖ (hπ ▸ π.ne_zero))
  by_cases hx : x ∈ integralGL R K ι
  · obtain ⟨ξ₀, rfl⟩ := hx
    set v : ι → ResidueField R := fun a ↦ residue R ((ξ₀ : Matrix ι ι R) a i)
    rw [Nat.card_congr (Equiv.subtypeEquivRight (cosetRep_inv_mul_mem_iff hϖ hπ ξ₀)),
      ite_eq_left (c := GeneralLinearGroup.map (algebraMap R K) ξ₀ ∈ integralGL R K ι) ⟨ξ₀, rfl⟩]
    have hJ : GeneralLinearGroup.map (algebraMap R K) ξ₀ ∈ lineParahoric R K i ↔
        ∀ a, a ≠ i → v a = 0 := by
      rw [mem_lineParahoric_iff]
      simp only [v, residue_eq_zero_iff]
      exact ⟨fun ⟨γ, hγ, h⟩ ↦ hinj hγ ▸ h, fun h ↦ ⟨ξ₀, rfl, h⟩⟩
    split_ifs with hxJ
    · have hv := hJ.mp hxJ
      refine card_filter_rowVec_dotProduct_ne_zero_of_forall ?_ hv
      have := apply_self_ne_zero_of_mem_lineStabilizer
        (g := GeneralLinearGroup.map (residue R) ξ₀) (i := i)
        (mem_lineStabilizer_iff.mpr fun a ha ↦ by rw [GeneralLinearGroup.map_apply]; exact hv a ha)
      simpa [v, GeneralLinearGroup.map_apply] using this
    · rw [hJ] at hxJ
      push Not at hxJ
      exact card_filter_rowVec_dotProduct_ne_zero hxJ
  · -- off `GL_ι(R)` no coset qualifies: `(u t)⁻¹ x ∈ J t⁻¹ J` forces `x ∈ u t J t⁻¹ J ⊆ GL_ι(R)`
    rw [ite_eq_right (fun h ↦ hx (lineParahoric_le_integralGL h)), ite_eq_right hx,
      Nat.card_eq_zero]
    refine Or.inl ⟨fun ⟨c, hc⟩ ↦ hx ?_⟩
    rw [cosetRep, _root_.mul_inv_rev, mul_assoc,
      inv_mul_mem_doubleCoset_inv_lineParahoric_iff hϖ hπ] at hc
    obtain ⟨ξ, hξ, -⟩ := hc
    exact ⟨liftGL R (rowUnipotent c)⁻¹ * ξ, by rw [map_mul, hξ, mul_inv_cancel_left]⟩

/-- **The coset count in the Hecke algebra of `J`**:
`1_{J t J} ⋆ 1_{J t⁻¹ J} = q^{n-2} (1_J + (q - 1) 1_{GL_ι(R)})`. For representatives `r c` of the
left cosets of `J` in `J t J`, the number of `c` with `(r c)⁻¹ x ∈ J t⁻¹ J` is `q^{n-1}` for
`x ∈ J`, `q^{n-1} - q^{n-2}` for `x ∈ GL_ι(R) ∖ J` and `0` otherwise, where `q` is the size of the
residue field and `n = |ι| ≥ 2`. -/
theorem sum_indicator_doubleCoset_inv_lineParahoric {A : Type*} [CommSemiring A]
    (hϖ : Irreducible ϖ) (hπ : algebraMap R K ϖ = π)
    (hn : 2 ≤ Fintype.card ι) {κ : Type*} [Fintype κ] {r : κ → GL ι K}
    (hr : Subgroup.IsCosetSystem (lineParahoric R K i) (lineParahoric R K i)
      (diagGL (Pi.mulSingle i π)) r) (x : GL ι K) :
    ∑ c, (DoubleCoset.doubleCoset (diagGL (Pi.mulSingle i π))⁻¹ (lineParahoric R K i)
        (lineParahoric R K i)).indicator (1 : GL ι K → A) ((r c)⁻¹ * x) =
      ((Nat.card (ResidueField R) ^ (Fintype.card ι - 2) : ℕ) : A) *
          (lineParahoric R K i : Set (GL ι K)).indicator 1 x +
        ((Nat.card (ResidueField R) ^ (Fintype.card ι - 2) * (Nat.card (ResidueField R) - 1) :
          ℕ) : A) * (integralGL R K ι : Set (GL ι K)).indicator 1 x := by
  classical
  -- pass to the coset system `cosetRep`, whose members lie in the same cosets
  obtain ⟨e, he⟩ := hr.exists_equiv (isCosetSystem_cosetRep (i := i) hϖ hπ)
  -- the residue field is finite, since `J t J` has `|κ| = q^{n-1}` left cosets
  have : Nonempty κ := ⟨e.symm 0⟩
  have : Finite (ResidueField R) := by
    refine Nat.finite_of_card_ne_zero fun h ↦ ?_
    have hκ := hr.natCard_eq_relIndex
    rw [relIndex_conjAct_lineParahoric hϖ hπ, h, zero_pow (by omega)] at hκ
    exact Nat.card_pos.ne' hκ
  have := Fintype.ofFinite (ResidueField R)
  have hq : 1 ≤ Nat.card (ResidueField R) := Nat.card_pos
  have hn' : Fintype.card ι - 1 = Fintype.card ι - 2 + 1 := by omega
  have hle : Nat.card (ResidueField R) ^ (Fintype.card ι - 2) ≤
      Nat.card (ResidueField R) ^ (Fintype.card ι - 2) * Nat.card (ResidueField R) :=
    Nat.le_mul_of_pos_right _ hq
  have hmem (c : κ) : (r c)⁻¹ * x ∈ DoubleCoset.doubleCoset (diagGL (Pi.mulSingle i π))⁻¹
      (lineParahoric R K i : Set (GL ι K)) (lineParahoric R K i) ↔
        (cosetRep R π i (e c))⁻¹ * x ∈ DoubleCoset.doubleCoset (diagGL (Pi.mulSingle i π))⁻¹
          (lineParahoric R K i : Set (GL ι K)) (lineParahoric R K i) :=
    DoubleCoset.inv_mul_mem_doubleCoset_iff_of_mem (QuotientGroup.eq.mp (he c).symm)
  simp only [Set.indicator_apply, Pi.one_apply, SetLike.mem_coe, hmem]
  rw [e.sum_comp (fun c ↦ if (cosetRep R π i c)⁻¹ * x ∈ DoubleCoset.doubleCoset
      (diagGL (Pi.mulSingle i π))⁻¹ (lineParahoric R K i : Set (GL ι K)) (lineParahoric R K i)
      then (1 : A) else 0), Finset.sum_boole, ← Fintype.card_subtype, ← Nat.card_eq_fintype_card,
    natCard_cosetRep_inv_mul_mem hϖ hπ x]
  by_cases hJ : x ∈ lineParahoric R K i
  · simp only [hJ, lineParahoric_le_integralGL hJ, ↓reduceIte, mul_one, ← Nat.cast_add]
    rw [hn', pow_succ, Nat.mul_sub_one, Nat.add_sub_cancel' hle]
  · by_cases hK : x ∈ integralGL R K ι
    · simp only [hJ, hK, ↓reduceIte, mul_zero, mul_one, zero_add]
      rw [hn', pow_succ, Nat.mul_sub_one]
    · simp [hJ, hK]

/-- `J ∩ t J t⁻¹` has finite index in `J`. -/
theorem isFiniteRelIndex_conjAct_lineParahoric [Finite (ResidueField R)] (hϖ : Irreducible ϖ)
    (hπ : algebraMap R K ϖ = π) :
    (ConjAct.toConjAct (diagGL (Pi.mulSingle i π)) • lineParahoric R K i).IsFiniteRelIndex
      (lineParahoric R K i) :=
  ⟨by rw [relIndex_conjAct_lineParahoric hϖ hπ]; exact pow_ne_zero _ Nat.card_pos.ne'⟩

/-- `J ∩ t⁻¹ J t` has finite index in `J`. -/
theorem isFiniteRelIndex_conjAct_inv_lineParahoric [Finite (ResidueField R)]
    (hϖ : Irreducible ϖ) (hπ : algebraMap R K ϖ = π) :
    (ConjAct.toConjAct (diagGL (Pi.mulSingle i π))⁻¹ • lineParahoric R K i).IsFiniteRelIndex
      (lineParahoric R K i) :=
  ⟨by rw [relIndex_conjAct_inv_lineParahoric hϖ hπ]; exact pow_ne_zero _ Nat.card_pos.ne'⟩

end DVR

end HeckeRing.GLn

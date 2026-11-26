/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.GroupAlgebra.DefectGroup.DefectZero.Simple

/-!
# Matrix blocks have defect zero

Let `e` be a central idempotent of `k[G]`, `G` a finite group, whose corner `e k[G]` is a matrix
algebra `M_n(k)`. Then `e = Tr_1^G(a) = ∑_g g a g⁻¹` for some `a ∈ k[G]`. So a block whose block
algebra is a matrix algebra over `k` has defect group `1`, and over an algebraically closed field
of characteristic `p` a block has defect group `1` exactly when its block algebra is a matrix
algebra over `k` (Webb, Corollary 12.4.8, p. 242, with Theorem 9.6.1, p. 161).

The route is the converse half of the defect-zero bullet of the roadmap. Write `E_{ij}` for the
matrix units of `e k[G]`, transported from `M_n(k)`, and `f = E_{i₀ i₀}`. On the left ideal
`k[G] f`, the simple module of the block, the identity is `∑_g g α g⁻¹` for the `k`-linear map
`α w = w(1) f`, `w(1)` the coefficient of `w` at `1`: indeed `∑_g g (g⁻¹ w)(1) f = ∑_g w(g) g f =
w f = w`. Every `k`-linear endomorphism of `k[G] f` is left multiplication by an element of the
block algebra, and here `α` is left multiplication by `c = ∑_i λ_i E_{i₀ i}`, with
`λ_i = E_{i i₀}(1)`. Hence `z = ∑_g g c g⁻¹`, an element of the block algebra, acts as the
identity on each `E_{i i₀}`, so it is the identity `e` of `M_n(k)`.

## Main results

* `TauCeti.exists_sum_conjRepresentation_eq_of_algEquiv_matrix`: a central
  idempotent `e` of `k[G]` with `e k[G] ≅ M_n(k)` is a relative trace `Tr_1^G(a)`.
* `TauCeti.IsBlockIdempotent.isDefectGroup_bot_of_algEquiv_matrix`: a block whose block algebra
  is `M_n(k)` has defect group `1`.
* `TauCeti.IsBlockIdempotent.isDefectGroup_bot_iff_exists_algEquiv_matrix`: over an
  algebraically closed field, a block has defect group `1` exactly when its block algebra is a
  matrix algebra over `k`.

## References

* P. Webb, *A Course in Finite Group Representation Theory*, Theorem 9.6.1, p. 161, and
  Corollary 12.4.8, p. 242.
-/

public section

universe u v w

namespace TauCeti

open MonoidAlgebra

section Trace

variable {k : Type u} {G : Type v} [CommRing k] [Group G] [Fintype G]

omit [Fintype G] in
/-- The coefficient of `g⁻¹ w` at `1` is the coefficient of `w` at `g`. -/
private theorem coeff_of_inv_mul_one (g : G) (w : MonoidAlgebra k G) :
    (of k G g⁻¹ * w).coeff 1 = w.coeff g := by
  rw [of_apply, coeff_single_mul_apply, one_mul, inv_inv, mul_one]

/-- `∑_g w(g) g = w` in `k[G]`. -/
private theorem sum_coeff_smul_of (w : MonoidAlgebra k G) :
    ∑ g : G, w.coeff g • of k G g = w := by
  classical
  ext h
  simp [coeff_sum, of_apply, coeff_single]

/-- If left multiplication by `c` sends every `w` of the left ideal `k[G] f` to `w(1) f`, then
`∑_g g c g⁻¹` fixes every element of `k[G] f`. -/
private theorem sum_conj_mul_of_forall {c f w : MonoidAlgebra k G}
    (hc : ∀ x : MonoidAlgebra k G, x * f = x → c * x = x.coeff 1 • f) (hw : w * f = w) :
    (∑ g : G, conjRepresentation k G g c) * w = w := by
  have hgw (g : G) : of k G g⁻¹ * w * f = of k G g⁻¹ * w := by rw [mul_assoc, hw]
  calc (∑ g : G, conjRepresentation k G g c) * w
      = ∑ g : G, of k G g * (c * (of k G g⁻¹ * w)) := by
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun g _ ↦ ?_
        rw [conjRepresentation_apply_eq_mul, mul_assoc, mul_assoc]
    _ = (∑ g : G, w.coeff g • of k G g) * f := by
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun g _ ↦ ?_
        rw [hc _ (hgw g), coeff_of_inv_mul_one, mul_smul_comm, smul_mul_assoc]
    _ = w := by rw [sum_coeff_smul_of, hw]

/-- A matrix `X` with `X E_{i j₀} = E_{i j₀}` for every `i` is the identity. -/
private theorem matrix_eq_one_of_mul_single {n : Type w} [Fintype n] [DecidableEq n]
    {X : Matrix n n k} (j₀ : n) (hX : ∀ i, X * Matrix.single i j₀ 1 = Matrix.single i j₀ 1) :
    X = 1 := by
  ext a i
  have := congrFun (congrFun (hX i) a) j₀
  rw [Matrix.mul_single_apply_same, mul_one, Matrix.single_apply] at this
  rw [this, Matrix.one_apply]
  simp only [and_true, eq_comm]

/-- Left multiplication by the row `∑_i l_i E_{j₀ i}` sends a matrix supported on column `j₀`
to a multiple of `E_{j₀ j₀}`. -/
private theorem sum_smul_single_mul_of_col {n : Type w} [Fintype n] [DecidableEq n] (j₀ : n)
    (l : n → k) {X : Matrix n n k} (hX : ∀ i j, j ≠ j₀ → X i j = 0) :
    (∑ i, l i • Matrix.single j₀ i 1) * X = (∑ i, X i j₀ * l i) • Matrix.single j₀ j₀ 1 := by
  rw [Finset.sum_mul, Finset.sum_smul]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  ext a b
  rw [Matrix.smul_mul, Matrix.smul_apply, Matrix.smul_apply, smul_eq_mul, smul_eq_mul]
  by_cases ha : a = j₀
  · rw [ha, Matrix.single_mul_apply_same, one_mul]
    by_cases hb : b = j₀
    · rw [hb, Matrix.single_apply_same, mul_one, mul_comm]
    · rw [hX i b hb, Matrix.single_apply_of_col_ne _ _ (Ne.symm hb), mul_zero, mul_zero]
  · rw [Matrix.single_mul_apply_of_ne 1 j₀ i a b ha,
      Matrix.single_apply_of_row_ne (Ne.symm ha), mul_zero, mul_zero]

variable {e : MonoidAlgebra k G} (he : IsIdempotentElem e)

omit [Fintype G] in
/-- On the left ideal `k[G] f`, `f = E_{i₀ i₀}` a matrix unit of a matrix corner `e k[G]`, the
`k`-linear map `w ↦ w(1) f` is left multiplication by an element of the corner. -/
private theorem exists_mul_eq_coeff_one_smul (hcen : e ∈ Set.center _) {n : Type w} [Fintype n]
    [DecidableEq n] (ψ : he.Corner ≃ₐ[k] Matrix n n k) (i₀ : n) :
    ∃ c : he.Corner, ∀ x : MonoidAlgebra k G, x * (ψ.symm (Matrix.single i₀ i₀ 1)).val = x →
      c.val * x = x.coeff 1 • (ψ.symm (Matrix.single i₀ i₀ 1)).val := by
  have hcomm (x : MonoidAlgebra k G) : e * x = x * e := (Set.mem_center_iff.mp hcen).comm x
  -- The linear functional `X ↦ ψ⁻¹(X)(1)` on matrices.
  let L : Matrix n n k →ₗ[k] k :=
    { toFun X := (ψ.symm X).val.coeff 1
      map_add' X Y := by
        simp only [map_add, _root_.IsIdempotentElem.Corner.val_add, coeff_add, Finsupp.add_apply]
      map_smul' r X := by
        simp only [map_smul, _root_.IsIdempotentElem.Corner.val_smul, coeff_smul_apply,
          RingHom.id_apply] }
  have hL (X : Matrix n n k) : L X = ∑ i, ∑ j, X i j * L (Matrix.single i j 1) := by
    conv_lhs => rw [Matrix.matrix_eq_sum_single X]
    simp only [map_sum]
    refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
    rw [show Matrix.single i j (X i j) = X i j • Matrix.single i j (1 : k) by
      rw [Matrix.smul_single, smul_eq_mul, mul_one], map_smul, smul_eq_mul]
  refine ⟨ψ.symm (∑ i, L (Matrix.single i i₀ 1) • Matrix.single i₀ i 1), fun x hx ↦ ?_⟩
  have hxe : x * e = x := by rw [← hx, mul_assoc, IsIdempotentElem.corner_val_mul]
  let x' : he.Corner := ⟨x, (Subsemigroup.mem_corner_iff he).2 ⟨by rw [hcomm, hxe], hxe⟩⟩
  have hXcol (i j : n) (hj : j ≠ i₀) : ψ x' i j = 0 := by
    have : ψ x' * Matrix.single i₀ i₀ 1 = ψ x' := by
      rw [← AlgEquiv.apply_symm_apply ψ (Matrix.single i₀ i₀ 1), ← map_mul]
      exact congrArg ψ (Subtype.ext hx)
    rw [← this, Matrix.mul_single_apply_of_ne 1 i₀ i₀ i j hj]
  have hxL : x.coeff 1 = ∑ i, ψ x' i i₀ * L (Matrix.single i i₀ 1) := by
    have : x.coeff 1 = L (ψ x') := by
      simp only [L, LinearMap.coe_mk, AddHom.coe_mk, AlgEquiv.symm_apply_apply]; rfl
    rw [this, hL]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [Finset.sum_eq_single i₀ (fun j _ hj ↦ by rw [hXcol i j hj, zero_mul])
      (fun h ↦ (h (Finset.mem_univ _)).elim)]
  have : ψ.symm (∑ i, L (Matrix.single i i₀ 1) • Matrix.single i₀ i 1) * x' =
      x.coeff 1 • ψ.symm (Matrix.single i₀ i₀ 1) := by
    apply ψ.injective
    rw [map_mul, AlgEquiv.apply_symm_apply, sum_smul_single_mul_of_col i₀ _ hXcol, ← hxL,
      map_smul, AlgEquiv.apply_symm_apply]
  simpa only [_root_.IsIdempotentElem.Corner.val_mul,
    _root_.IsIdempotentElem.Corner.val_smul] using congrArg Subtype.val this

/-- **A matrix corner is a relative trace from `1`.** If `e` is a central idempotent of `k[G]`,
`G` a finite group, whose corner `e k[G]` is isomorphic to a matrix algebra `M_n(k)`, then
`e = Tr_1^G(a) = ∑_g g a g⁻¹` for some `a ∈ k[G]`. -/
theorem exists_sum_conjRepresentation_eq_of_algEquiv_matrix (hcen : e ∈ Set.center _)
    {n : Type w} [Fintype n] [DecidableEq n] (ψ : he.Corner ≃ₐ[k] Matrix n n k) :
    ∃ a : MonoidAlgebra k G, ∑ g : G, conjRepresentation k G g a = e := by
  have hcomm (x : MonoidAlgebra k G) : e * x = x * e := (Set.mem_center_iff.mp hcen).comm x
  rcases isEmpty_or_nonempty n with hn | ⟨⟨i₀⟩⟩
  · -- `M_0(k) = 0`, so `e = 0`.
    refine ⟨0, ?_⟩
    have h1 : (1 : he.Corner) = 0 := ψ.injective (Subsingleton.elim _ _)
    simp only [map_zero, Finset.sum_const_zero]
    simpa only [_root_.IsIdempotentElem.Corner.val_one,
      _root_.IsIdempotentElem.Corner.val_zero] using (congrArg Subtype.val h1).symm
  -- The matrix units `E i j` of the corner, and `c` acting as `w ↦ w(1) E i₀ i₀`.
  set E : n → n → he.Corner := fun i j ↦ ψ.symm (Matrix.single i j 1)
  obtain ⟨c, hc⟩ := exists_mul_eq_coeff_one_smul he hcen ψ i₀
  refine ⟨c.val, ?_⟩
  -- `z = ∑_g g c g⁻¹` lies in the corner and fixes every `E i i₀`, so it is `e`.
  set z := ∑ g : G, conjRepresentation k G g c.val with hz
  have hze : e * z = z := by
    rw [hz, Finset.mul_sum]
    refine Finset.sum_congr rfl fun g _ ↦ ?_
    rw [conjRepresentation_apply_eq_mul, ← mul_assoc, ← mul_assoc, hcomm (of k G g),
      mul_assoc (of k G g) e, IsIdempotentElem.mul_corner_val]
  let z' : he.Corner := ⟨z, (Subsemigroup.mem_corner_iff he).2 ⟨hze, by rw [← hcomm, hze]⟩⟩
  have hz' : ψ z' = 1 := by
    refine matrix_eq_one_of_mul_single i₀ fun i ↦ ?_
    have hEi : (E i i₀).val * (E i₀ i₀).val = (E i i₀).val := by
      rw [← _root_.IsIdempotentElem.Corner.val_mul]
      simp only [E, ← map_mul, Matrix.single_mul_single_same, mul_one]
    have : z' * E i i₀ = E i i₀ := Subtype.ext (sum_conj_mul_of_forall hc hEi)
    simpa [E] using congrArg ψ this
  have : z' = 1 := ψ.injective (by rw [hz', map_one])
  simpa only [_root_.IsIdempotentElem.Corner.val_one] using congrArg Subtype.val this

end Trace

namespace IsBlockIdempotent

variable {k : Type u} {G : Type v} [Field k] [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
  [CharP k p] {b : Subalgebra.center k (MonoidAlgebra k G)}

/-- **A matrix block has defect zero.** If the block algebra `e k[G]` of a block idempotent `e`
of `k[G]`, `k` a field of characteristic `p`, is isomorphic to a matrix algebra `M_n(k)`, then `1`
is a defect group of `e` (Webb, Corollary 12.4.8, p. 242). -/
theorem isDefectGroup_bot_of_algEquiv_matrix (hb : IsBlockIdempotent b) {n : Type w}
    [Fintype n] [DecidableEq n] (ψ : hb.BlockAlgebra ≃ₐ[k] Matrix n n k) :
    IsDefectGroup k p (b : MonoidAlgebra k G) ⊥ := by
  have := Fintype.ofFinite G
  exact hb.isDefectGroup_bot_iff.2 <|
    exists_sum_conjRepresentation_eq_of_algEquiv_matrix hb.isIdempotentElem_val b.property ψ

/-- **Defect zero over an algebraically closed field.** A block idempotent `e` of `k[G]`, `k` an
algebraically closed field of characteristic `p`, has defect group `1` exactly when its block
algebra `e k[G]` is a matrix algebra `M_n(k)` (Webb, Corollary 12.4.8, p. 242, with
Theorem 9.6.1, p. 161). -/
theorem isDefectGroup_bot_iff_exists_algEquiv_matrix [IsAlgClosed k] (hb : IsBlockIdempotent b) :
    IsDefectGroup k p (b : MonoidAlgebra k G) ⊥ ↔
      ∃ n : ℕ, Nonempty (hb.BlockAlgebra ≃ₐ[k] Matrix (Fin n) (Fin n) k) := by
  refine ⟨fun hD ↦ ?_, fun ⟨n, ⟨ψ⟩⟩ ↦ hb.isDefectGroup_bot_of_algEquiv_matrix ψ⟩
  obtain ⟨n, -, hψ⟩ := hb.exists_algEquiv_matrix_of_isDefectGroup_bot hD
  exact ⟨n, hψ⟩

end IsBlockIdempotent

end TauCeti

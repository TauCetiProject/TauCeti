/-
Copyright (c) 2026 Tau Ceti. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Determinant
public import TauCeti.LinearAlgebra.BilinearForm.Basic
public import Mathlib.RingTheory.Ideal.Span
public import TauCeti.LinearAlgebra.Multilinear.Span
import TauCeti.LinearAlgebra.BilinearMap.Multilinear
import Mathlib.LinearAlgebra.SpecialLinearGroup
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.LinearAlgebra.Matrix.Nonsingular
import Mathlib.LinearAlgebra.Matrix.Nondegenerate
import Mathlib.LinearAlgebra.Matrix.SchurComplement

/-!
# Determinant transformation laws, evaluation, and determinants of updated rows

Precomposing an alternating form of top degree with an endomorphism `φ` multiplies it by
`LinearMap.det φ`, and — the direction that is actually used — a *nonzero* form merely known to be
*scaled* by some `d` thereby identifies `d` as the determinant, without computing it, as soon as
scalars cancel against nonzero vectors of the codomain (`IsCancelMulZero R` and
`Module.IsTorsionFree R N`; see the implementation notes, where `ω ≠ 0` alone is shown to be
insufficient). This file records that law in three vocabularies: for
an `AlternatingMap` indexed by a basis' index type, for an alternating bilinear form on a rank-two
module, and for the standard-basis determinant form under matrix multiplication. It also
identifies evaluation of the row determinant form on a family of linear functionals with the
determinant of their evaluation matrix. Ideal membership of these determinants extends from
a set of rows to its linear span.

Mathlib's `Module.Basis.det_comp` is the case `ω = b.det` of the first statement. The step taken
here is that every top-degree alternating form is a multiple of `b.det`
(`AlternatingMap.eq_basis_det_smulRight`), so the same law holds for all of them; that is what
makes the converse available for a form supplied by something other than a basis, such as a
pairing.

The file also records one identity for the determinant of a matrix with one row replaced,
alongside Mathlib's `Matrix.det_updateRow_add` and `Matrix.det_updateRow_smul`: Jacobi's formula
in row form, that rescaling one row entry by entry along a fixed vector of factors and summing the
results over the rows multiplies the determinant by the total of the factors.

It also records facts used to compute ideals of maximal minors: the determinant in a product
basis of a block-diagonal family, and of a family that becomes block diagonal after a permutation,
and Cramer's rule for an endomorphism of a free module of finite rank. On a free module of rank
one, every endomorphism is multiplication by its determinant.

Finally, it records the Weinstein–Aronszajn identity `det (1 + X ∘ₗ Y) = det (1 + Y ∘ₗ X)` for
linear maps `X` and `Y` between two free modules of finite rank, possibly of different ranks.

## Main results

* `AlternatingMap.eq_basis_det_smulRight`: `ω = b.det.smulRight (ω b)` for `ω` of top degree.
* `AlternatingMap.compLinearMap_eq_det_smul`: `ω ∘ φ = det φ • ω` for `ω` of top degree.
* `LinearMap.det_eq_of_compLinearMap_eq_smul`: if `ω ≠ 0` and `ω ∘ φ = d • ω` then `det φ = d`,
  for `R` cancellative and `N` torsion-free.
* `LinearMap.IsAlt.compl₁₂_self_eq_det_smul` and `LinearMap.det_eq_of_compl₁₂_self_eq_smul`: the
  same two statements for an alternating bilinear form on a module of rank two.
* `LinearMap.det_eq_of_compl₁₂_self_eq_smul_of_separatingLeft`: the recovery statement over any
  commutative ring, for a left-separating form.
* `LinearMap.det_mul_det_eq_of_compl₁₂_eq_smul`: if a pairing `B` identifies `M'` with the dual of
  a finite free module `M` and `B (F x) (F' y) = c • B x y`, then `det F * det F' = c ^ finrank M`.
* `Matrix.detRowAlternating_mulVec`: multiplication by a square matrix scales the
  standard-basis determinant form by the matrix determinant.
* `Matrix.detRowAlternating_apply`: the row determinant form evaluated on a family of rows is
  the determinant of the matrix with those rows.
* `Matrix.detRowAlternating_pi_apply`: evaluating the row determinant form on a family of
  linear functionals gives the determinant of their evaluation matrix.
* `Matrix.detRowAlternating_compLinearMap_pi_apply`: the same evaluation in multilinear-map
  vocabulary after precomposition with the family of functionals.
* `TauCeti.det_mem_of_mem_span`: ideal membership of evaluation determinants extends from
  a set of rows to its linear span.
* `Matrix.sum_det_updateRow_mul_row`: Jacobi's formula for a determinant, in row form.
* `Matrix.det_mul_column_intCast`: scaling every row `i` of an integer matrix by `d i`
  multiplies the determinant by `∏ i, d i`, over any commutative ring.
* `LinearMap.det_one_add_comp_comm`, `LinearMap.det_one_sub_comp_comm`: the Weinstein–Aronszajn
  identity `det (1 ± X ∘ₗ Y) = det (1 ± Y ∘ₗ X)` for linear maps between free modules of finite
  rank.
* `LinearEquiv.det_eq_pow_of_forall_eq_smul`: an automorphism acting as multiplication by a unit
  `c` has determinant `c ^ finrank R V`.
* `LinearEquiv.det_ker_eq_bot_of_finrank_le_one`: the determinant kernel is trivial in
  dimension at most one.
* `Module.Basis.det_comp_eq_mul`: `b'.det (f ∘ v) = b'.det (f ∘ b) * b.det v` for a linear map
  `f` between two modules with bases `b` and `b'`.
* `Module.Basis.prod_det_sumElim`: the determinant in a product basis of a family split between
  the two factors is the product of the two determinants.
* `Module.Basis.exists_prod_det_eq_sign_smul_mul`: the same up to sign for a family with exactly
  as many members in the first factor as the rank of the first factor.
* `Module.Basis.det_unique`: over an index type with a single element, the determinant of a
  family in a basis `b` is the coordinate in `b` of its single vector.
* `Module.Basis.det_unique_smul`: over an index type with a single element, the single vector of
  a family is its determinant in a basis `b` times the single vector of `b`.
* `Module.Basis.det_smul_smul_vecCons`: rescaling the first two of three vectors by `r` and `r'`
  multiplies their determinant by `r * r'`.
* `Module.Basis.det_equivFun_symm_trans_equivFun`: the coordinate change from a basis `b` to a
  basis `b'` has determinant `b'.det b`.
* `Module.Basis.det_map_eq_det_toMatrix`: evaluating `b'.det` on the image `b.map e` of a basis `b`
  under a linear equivalence `e` gives the determinant of `LinearMap.toMatrix b b' e`.
* `Module.Basis.det_mem_nonZeroDivisors`: the determinant `b.det v` of a linearly independent
  family `v` is a non-zero-divisor.
* `Module.Basis.det_eq_det_of_det_eq_one`: a basis `b'` with `b.det b' = 1` has the same
  determinant form as `b`.
* `Module.Basis.eq_zero_of_forall_det_eq_zero`: the determinant form of a rank-two basis is
  nondegenerate.
* `LinearMap.det_smul_mem_range`: Cramer's rule, `det φ • x ∈ range φ`.
* `LinearMap.injective_of_det_mem_nonZeroDivisors`: an endomorphism of a free module of finite
  rank whose determinant is a non-zero-divisor is injective.
* `LinearMap.apply_eq_det_smul_of_finrank_eq_one`: on a free module of rank one, an endomorphism
  is multiplication by its determinant.
* `LinearMap.det_eq_of_comp_eq`: endomorphisms intertwined by a linear equivalence have the same
  determinant.

## Implementation notes

The forms are valued in an arbitrary module `N`, not in `R`. Mathlib's
`AlternatingMap.eq_smul_basis_det` is the `N = R` case of the first result here; the codomain plays
no part in the argument, only the coordinates do, so the `N`-valued statement is what is proved.

The recovery statements need cancellation hypotheses, not just `ω ≠ 0`, and neither of the two
assumed can be dropped:

* without `IsCancelMulZero R`: over `R = ZMod 4`, with `N = R` (which is torsion-free over
  itself), the form `ω = 2 • b.det` is nonzero and satisfies `ω ∘ id = 3 • ω`, while
  `det id = 1`;
* without `Module.IsTorsionFree R N`: over `R = ℤ`, with `M = ℤ²` and `N = ZMod 2`, the
  determinant form reduced mod `2`, `(x, y) ↦ x₀ y₁ - x₁ y₀`, is nonzero and alternating, and
  `φ = 3 • id` scales it by `9`, that is by `1`, while `det φ = 9`.

`IsCancelMulZero R` and `Module.IsTorsionFree R N` are assumed for these recovery statements, and
for nothing else; together they let a nonzero form, an element of a torsion-free module of
alternating or bilinear maps, cancel from `det φ • ω = d • ω`. A left-separating form needs neither:
a scalar killing it kills a basis vector, so vanishes, and
`LinearMap.det_eq_of_compl₁₂_self_eq_smul_of_separatingLeft` holds over every commutative ring. The
examples above are not left-separating: `2 • b.det` pairs `2 • b 0` to zero, and the reduced
determinant form pairs `2 • e₀` to zero.

None of the transformation laws stated for a basis is a `simp` lemma: the basis is a hypothesis
and does not occur in the conclusion, so `simp` could not infer it.

The bilinear statements use `LinearMap.IsAlt.toAlternatingMap` to read an alternating bilinear form
as an `AlternatingMap` on `Fin 2`.

## Provenance

The four transformation and recovery laws are ported from the AINTLIB `HasseWeil` project
(Apache-2.0), revision `513e83879e2f`, file `HasseWeil/WeilPairing/PairingDet.lean`, declarations
`alternating_comp_eq_det_smul` and `det_eq_of_alternating_scaling`. The source states them over a
field, for a scalar-valued form, evaluated at a basis, and proves the first by expanding `φ (b j)`
in coordinates; none of that is reproduced here. `Matrix.detRowAlternating_mulVec` predates
that port and is not from the source, nor is the left-separating recovery statement.
-/

public section

open Module

namespace AlternatingMap

variable {ι R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N]
  [Module R N]

/-- **A top-degree alternating form is its basis determinant times its value on the basis.** This
is Mathlib's `AlternatingMap.eq_smul_basis_det` with the codomain an arbitrary module rather than
`R`. -/
theorem eq_basis_det_smulRight [Fintype ι] [DecidableEq ι] (b : Basis ι R M)
    (ω : M [⋀^ι]→ₗ[R] N) : ω = b.det.smulRight (ω ⇑b) := by
  -- Mathlib's proof generalises unchanged: it reads off the coordinates and never touches the
  -- values, and `Module.Basis.ext_alternating` is already stated for an arbitrary codomain.
  refine Module.Basis.ext_alternating b fun i h => ?_
  let σ : Equiv.Perm ι := Equiv.ofBijective i (Finite.injective_iff_bijective.1 h)
  -- `ext_alternating` hands back the arguments as `fun i => b (i j)`, whereas `map_perm` and
  -- `Basis.det_self` are stated for the composite `⇑b ∘ σ`. The two are the same function, so
  -- the `change` is definitional; Mathlib's own `eq_smul_basis_det` opens with the same step.
  change ω (⇑b ∘ σ) = (b.det.smulRight (ω ⇑b)) (⇑b ∘ σ)
  simp [map_perm, Basis.det_self]

/-- **An endomorphism scales a top-degree alternating form by its determinant.** Here `ω` is of
top degree in the sense that its index type indexes a basis of `M`; that basis is a hypothesis and
does not occur in the conclusion, which is an equality of alternating maps. -/
theorem compLinearMap_eq_det_smul [Finite ι] (b : Basis ι R M) (ω : M [⋀^ι]→ₗ[R] N)
    (φ : M →ₗ[R] M) : ω.compLinearMap φ = LinearMap.det φ • ω := by
  cases nonempty_fintype ι
  classical
  rw [eq_basis_det_smulRight b ω]
  ext v
  simp [← Function.comp_def, mul_smul]

end AlternatingMap

namespace Module.Basis

variable {ι ι' R M M' : Type*} [Fintype ι] [DecidableEq ι] [Fintype ι'] [DecidableEq ι']
  [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup M'] [Module R M']

/-- The determinant in a product basis of a family whose first arguments lie in the first factor
and whose last arguments lie in the second factor is the product of the two determinants. -/
theorem prod_det_sumElim (b : Basis ι R M) (b' : Basis ι' R M') (v : ι → M) (v' : ι' → M') :
    (b.prod b').det (Sum.elim (LinearMap.inl R M M' ∘ v) (LinearMap.inr R M M' ∘ v')) =
      b.det v * b'.det v' := by
  have h : (b.prod b').toMatrix (Sum.elim (LinearMap.inl R M M' ∘ v)
      (LinearMap.inr R M M' ∘ v')) = Matrix.fromBlocks (b.toMatrix v) 0 0 (b'.toMatrix v') := by
    ext (i | i) (j | j) <;> simp [Basis.toMatrix_apply]
  rw [det_apply, h, Matrix.det_fromBlocks_zero₂₁, det_apply, det_apply]

/-- If the members of a family satisfying `P` lie in the first factor, the others lie in the
second factor, and exactly `card ι` members satisfy `P`, then, after a permutation `σ` moving the
former to the front, the determinant of the family in a product basis is, up to the sign of `σ`,
the product of the determinants of the two blocks of components. -/
theorem exists_prod_det_eq_sign_smul_mul (b : Basis ι R M) (b' : Basis ι' R M')
    (w : ι ⊕ ι' → M × M') (P : ι ⊕ ι' → Prop) [DecidablePred P]
    (hcard : Fintype.card {i // P i} = Fintype.card ι) (h₁ : ∀ i, P i → (w i).2 = 0)
    (h₂ : ∀ i, ¬P i → (w i).1 = 0) :
    ∃ σ : Equiv.Perm (ι ⊕ ι'), (b.prod b').det w = Equiv.Perm.sign σ •
      (b.det (fun k ↦ (w (σ (.inl k))).1) * b'.det (fun l ↦ (w (σ (.inr l))).2)) := by
  let e₁ : ι ≃ {i // P i} := (Fintype.equivOfCardEq hcard).symm
  let e₂ : ι' ≃ {i // ¬P i} := (Fintype.equivOfCardEq (by
    rw [Fintype.card_subtype_compl, hcard, Fintype.card_sum, Nat.add_sub_cancel_left])).symm
  let σ : Equiv.Perm (ι ⊕ ι') := (e₁.sumCongr e₂).trans (Equiv.sumCompl P)
  have hσ : w ∘ σ = Sum.elim (LinearMap.inl R M M' ∘ fun k ↦ (w (σ (.inl k))).1)
      (LinearMap.inr R M M' ∘ fun l ↦ (w (σ (.inr l))).2) := by
    ext1 (k | l)
    · exact Prod.ext (by simp) (by simpa using h₁ _ (by simpa [σ] using (e₁ k).property))
    · exact Prod.ext (by simpa using h₂ _ (by simpa [σ] using (e₂ l).property)) (by simp)
  refine ⟨σ, ?_⟩
  have h := (b.prod b').det.map_perm w σ
  rw [hσ, prod_det_sumElim] at h
  rw [h, smul_smul, Int.units_mul_self, one_smul]

/-- Over an index type with a single element, the determinant of a family `v` in a basis `b` is
the coordinate in `b` of its single vector. This is `Matrix.det_unique` for `Module.Basis.det`. -/
theorem det_unique [Unique ι] (b : Basis ι R M) (v : ι → M) :
    b.det v = b.repr (v default) default := by
  rw [det_apply, Matrix.det_unique, toMatrix_apply]

/-- Over an index type with a single element, the single vector of a family `v` is its
determinant in a basis `b` times the single vector of `b`. -/
theorem det_unique_smul [Unique ι] (b : Basis ι R M) (v : ι → M) :
    b.det v • b default = v default := by
  rw [det_unique]
  simpa using b.sum_repr (v default)

/-- Rescaling the first two of three vectors by `r` and `r'` multiplies their determinant in a
basis by `r * r'`. -/
theorem det_smul_smul_vecCons (b : Basis (Fin 3) R M) (r r' : R) (u w d : M) :
    b.det ![r • u, r' • w, d] = r * r' * b.det ![u, w, d] := by
  have hv : ![r • u, r' • w, d] = fun k ↦ ![r, r', 1] k • ![u, w, d] k := by
    ext k
    fin_cases k <;> simp
  rw [hv, AlternatingMap.map_smul_univ, Fin.prod_univ_three]
  simp

/-- The coordinate change from the basis `b` to the basis `b'`, which sends the coordinates `x` of
`∑ i, x i • b i` in `b` to its coordinates in `b'`, has determinant `b'.det b`. -/
theorem det_equivFun_symm_trans_equivFun (b b' : Basis ι R M) :
    (LinearEquiv.det (b.equivFun.symm.trans b'.equivFun) : R) = b'.det b := by
  -- The coordinate change is the change of basis `b' i ↦ b i`, written in the coordinates of `b'`.
  have h : b.equivFun.symm.trans b'.equivFun =
      (b'.equivFun.symm.trans (b'.equiv b (Equiv.refl ι))).trans b'.equivFun := by
    ext x : 1
    simp [map_sum, map_smul]
  rw [h, LinearEquiv.det_conj, LinearEquiv.coe_det, det_basis]

/-- Evaluating the determinant form of a basis `b'` on the image `b.map e` of a basis `b` under a
linear equivalence `e` gives the determinant of the matrix of `e` with respect to `b` and `b'`. -/
theorem det_map_eq_det_toMatrix (b : Basis ι R M) (b' : Basis ι R M') (e : M ≃ₗ[R] M') :
    b'.det (b.map e) = (LinearMap.toMatrix b b' (e : M →ₗ[R] M')).det := by
  rw [det_apply, coe_map, ← LinearEquiv.coe_toLinearMap, ← LinearMap.toMatrix_eq_basisToMatrix]

/-- Evaluating the determinant form of a basis `b'` of `M'` on the image `f ∘ v` of a family `v`
under a linear map `f : M → M'` gives its value on `f ∘ b` times the determinant of `v` in a basis
`b` of `M`. This is `Module.Basis.det_comp` for linear maps between two different modules. -/
theorem det_comp_eq_mul (b : Basis ι R M) (b' : Basis ι R M') (f : M →ₗ[R] M') (v : ι → M) :
    b'.det (f ∘ v) = b'.det (f ∘ b) * b.det v :=
  DFunLike.congr_fun (AlternatingMap.eq_smul_basis_det b (b'.det.compLinearMap f)) v

/-- The determinant of a linearly independent family `v` in a basis `b` of the same size is a
non-zero-divisor, although `v` need not span: over `ℤ`, the family `(2)` in the basis `(1)` of `ℤ`
has determinant `2`. -/
theorem det_mem_nonZeroDivisors (b : Basis ι R M) {v : ι → M} (hv : LinearIndependent R v) :
    b.det v ∈ nonZeroDivisors R := by
  rw [det_apply, ← Matrix.nonsingular_iff_det_mem_nonZeroDivisors,
    ← Matrix.linearIndependent_col_iff]
  convert hv.map' b.equivFun.toLinearMap b.equivFun.ker using 1
  ext j i
  simp [toMatrix_apply, Matrix.col]

/-- If a basis `b'` has determinant `1` in the basis `b`, then `b` and `b'` have the same
determinant form. -/
theorem det_eq_det_of_det_eq_one {b b' : Basis ι R M} (h : b.det b' = 1) : b'.det = b.det := by
  rw [AlternatingMap.eq_smul_basis_det b b'.det, ← mul_one (b'.det b), ← h, det_mul_det, det_self,
    one_smul]

/-- **The determinant form of a rank-two basis is nondegenerate.** A vector `u` with
`e.det ![u, v] = 0` for every `v` is zero. -/
theorem eq_zero_of_forall_det_eq_zero (e : Basis (Fin 2) R M) {u : M}
    (h : ∀ v, e.det ![u, v] = 0) : u = 0 := by
  refine e.forall_coord_eq_zero_iff.1 fun i ↦ ?_
  rw [coord_apply]
  fin_cases i
  · simpa [det_apply, Matrix.det_fin_two, toMatrix_apply] using h (e 1)
  · simpa [det_apply, Matrix.det_fin_two, toMatrix_apply] using h (e 0)

end Module.Basis

namespace LinearMap

variable {ι R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N]
  [Module R N]

/-- **The multiplier of a nonzero top-degree alternating form is the determinant.** An
endomorphism which scales `ω` by `d` has `det φ = d`; the scaling identifies the determinant
without computing it, and only the one endomorphism is involved.

The cancellation hypotheses on `R` and `N` are required, not incidental: dropping either one
leaves the multiplier of a nonzero `ω` ambiguous, as the two examples in the module docstring show.
-/
theorem det_eq_of_compLinearMap_eq_smul [Finite ι] [IsCancelMulZero R] [Module.IsTorsionFree R N]
    (b : Basis ι R M) {ω : M [⋀^ι]→ₗ[R] N} (hω : ω ≠ 0) {φ : M →ₗ[R] M} {d : R}
    (h : ω.compLinearMap φ = d • ω) : LinearMap.det φ = d :=
  smul_left_injective R hω <| (AlternatingMap.compLinearMap_eq_det_smul b ω φ).symm.trans h

/-- **An endomorphism of a rank-two module scales an alternating bilinear form by its
determinant.** The basis is a hypothesis witnessing that the rank is two; it does not occur in the
conclusion, which is an equality of bilinear maps. -/
theorem IsAlt.compl₁₂_self_eq_det_smul (b : Basis (Fin 2) R M) {ω : M →ₗ[R] M →ₗ[R] N}
    (halt : ω.IsAlt) (φ : M →ₗ[R] M) : ω.compl₁₂ φ φ = LinearMap.det φ • ω := by
  ext x y
  simpa only [compl₁₂_apply, LinearMap.smul_apply, AlternatingMap.compLinearMap_apply,
    IsAlt.toAlternatingMap_apply, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one, _root_.smul_apply] using
    congr($(AlternatingMap.compLinearMap_eq_det_smul b halt.toAlternatingMap φ) ![x, y])

/-- **The multiplier of a nonzero alternating bilinear form on a rank-two module is the
determinant.** This is the form the additivised Weil pairing supplies: its scaling by an isogeny's
degree identifies that degree as a determinant.

As above, neither cancellation hypothesis can be dropped; the module docstring's `ZMod 2` example
is itself an alternating bilinear form on a rank-two module. -/
theorem det_eq_of_compl₁₂_self_eq_smul [IsCancelMulZero R] [Module.IsTorsionFree R N]
    (b : Basis (Fin 2) R M) {ω : M →ₗ[R] M →ₗ[R] N} (halt : ω.IsAlt) (hω : ω ≠ 0)
    {φ : M →ₗ[R] M} {d : R} (h : ω.compl₁₂ φ φ = d • ω) : LinearMap.det φ = d :=
  smul_left_injective R hω <| (halt.compl₁₂_self_eq_det_smul b φ).symm.trans h

/-- **The multiplier of a left-separating alternating bilinear form on a rank-two module is the
determinant**, over any commutative ring. Left separation of `ω` takes the place of the
cancellation hypotheses of `LinearMap.det_eq_of_compl₁₂_self_eq_smul`; this is the form that
applies to the Weil pairing on `N`-torsion, a module over `ZMod N`, which is not a domain for
composite `N`. -/
theorem det_eq_of_compl₁₂_self_eq_smul_of_separatingLeft (b : Basis (Fin 2) R M)
    {ω : M →ₗ[R] M →ₗ[R] N} (halt : ω.IsAlt) (hω : ω.SeparatingLeft) {φ : M →ₗ[R] M} {d : R}
    (h : ω.compl₁₂ φ φ = d • ω) : LinearMap.det φ = d := by
  have hd : LinearMap.det φ • ω = d • ω := (halt.compl₁₂_self_eq_det_smul b φ).symm.trans h
  -- the difference kills `ω (b 0) (b 1)`, so it vanishes
  refine sub_eq_zero.1 <| halt.eq_zero_of_smul_apply_basis_eq_zero b hω ?_
  rw [sub_smul, sub_eq_zero]
  simpa using congr($hd (b 0) (b 1))

/-- **The two-space determinant identity.** If `B` identifies `M'` with the dual of the finite
free module `M` and `B (F x) (F' y) = c • B x y`, then `det F * det F' = c ^ finrank M`: under the
identification, the transpose of `F` composed with `F'` is `c • id`, so `F'` is `c` times the
inverse of the transpose of `F` when `c` is a unit. -/
theorem det_mul_det_eq_of_compl₁₂_eq_smul {M' : Type*} [AddCommGroup M'] [Module R M']
    [Module.Free R M] [Module.Finite R M] (B : M →ₗ[R] M' →ₗ[R] R)
    (hB : Function.Bijective B.flip) {F : End R M} {F' : End R M'} {c : R}
    (h : B.compl₁₂ F F' = c • B) :
    LinearMap.det F * LinearMap.det F' = c ^ finrank R M := by
  let e : M' ≃ₗ[R] Dual R M := LinearEquiv.ofBijective B.flip hB
  have key : F.dualMap ∘ₗ ((e : M' →ₗ[R] Dual R M) ∘ₗ F' ∘ₗ (e.symm : Dual R M →ₗ[R] M')) =
      c • LinearMap.id := by
    ext φ x
    obtain ⟨y, rfl⟩ := e.surjective φ
    simpa [e] using congr($h x y)
  have hdet := congr(LinearMap.det $key)
  rw [det_comp, det_dualMap, det_conj, det_smul, det_id, mul_one] at hdet
  rw [hdet, (Free.chooseBasis R M).toDualEquiv.finrank_eq]

/-- The **Weinstein–Aronszajn identity** for linear maps: for linear maps `X : F' →ₗ[R] F` and
`Y : F →ₗ[R] F'` between free modules of finite rank, `det (1 + X ∘ₗ Y) = det (1 + Y ∘ₗ X)`. This
is Mathlib's `Matrix.det_one_add_mul_comm`, read through the matrices of `X` and `Y` in bases. -/
theorem det_one_add_comp_comm {F F' : Type*} [AddCommGroup F] [Module R F] [Module.Free R F]
    [Module.Finite R F] [AddCommGroup F'] [Module R F'] [Module.Free R F'] [Module.Finite R F']
    (X : F' →ₗ[R] F) (Y : F →ₗ[R] F') :
    LinearMap.det (1 + X ∘ₗ Y) = LinearMap.det (1 + Y ∘ₗ X) := by
  classical
  let b := Free.chooseBasis R F
  let b' := Free.chooseBasis R F'
  rw [← det_toMatrix b, ← det_toMatrix b', map_add, map_add, toMatrix_one, toMatrix_one,
    toMatrix_comp b b' b, toMatrix_comp b' b b']
  exact Matrix.det_one_add_mul_comm _ _

/-- The Weinstein–Aronszajn identity with a minus sign: for linear maps `X : F' →ₗ[R] F` and
`Y : F →ₗ[R] F'` between free modules of finite rank, `det (1 - X ∘ₗ Y) = det (1 - Y ∘ₗ X)`. This is
`LinearMap.det_one_add_comp_comm` applied to `-X` and `Y`. -/
theorem det_one_sub_comp_comm {F F' : Type*} [AddCommGroup F] [Module R F] [Module.Free R F]
    [Module.Finite R F] [AddCommGroup F'] [Module R F'] [Module.Free R F'] [Module.Finite R F']
    (X : F' →ₗ[R] F) (Y : F →ₗ[R] F') :
    LinearMap.det (1 - X ∘ₗ Y) = LinearMap.det (1 - Y ∘ₗ X) := by
  rw [sub_eq_add_neg, sub_eq_add_neg, ← neg_comp, ← comp_neg]
  exact det_one_add_comp_comm (-X) Y

/-- **Cramer's rule for an endomorphism.** The determinant of an endomorphism `φ` of a free
module of finite rank multiplies every vector into the range of `φ`: `det φ • x = φ (adj φ x)`,
for the adjugate `adj φ` of `φ`. -/
theorem det_smul_mem_range {F : Type*} [AddCommGroup F] [Module R F] [Module.Free R F]
    [Module.Finite R F] (φ : F →ₗ[R] F) (x : F) : LinearMap.det φ • x ∈ range φ := by
  classical
  let b := Free.chooseBasis R F
  refine ⟨Matrix.toLin b b (toMatrix b b φ).adjugate x, ?_⟩
  have h := congr(Matrix.toLin b b $((toMatrix b b φ).mul_adjugate) x)
  rw [Matrix.toLin_mul b b b, Matrix.toLin_toMatrix, map_smul, Matrix.toLin_one,
    det_toMatrix] at h
  simpa using h

/-- An endomorphism of a free module of finite rank whose determinant is a non-zero-divisor is
injective. This is Mathlib's `Matrix.mulVec_injective_of_det_mem_nonZeroDivisors`, read through
the matrix of the endomorphism in a basis. -/
theorem injective_of_det_mem_nonZeroDivisors [Module.Free R M] [Module.Finite R M]
    {f : M →ₗ[R] M} (hf : LinearMap.det f ∈ nonZeroDivisors R) : Function.Injective f := by
  classical
  let b := Free.chooseBasis R M
  intro x y hxy
  refine b.repr.injective (DFunLike.coe_injective <|
    Matrix.mulVec_injective_of_det_mem_nonZeroDivisors (M := toMatrix b b f) ?_ ?_)
  · rwa [det_toMatrix]
  · simp only [toMatrix_mulVec_repr, hxy]

/-- An endomorphism of a free module of rank one is multiplication by its determinant. -/
theorem apply_eq_det_smul_of_finrank_eq_one [Module.Free R M] (hM : Module.finrank R M = 1)
    (f : M →ₗ[R] M) (x : M) : f x = LinearMap.det f • x := by
  cases subsingleton_or_nontrivial R
  · have := Module.subsingleton R M
    exact Subsingleton.elim _ _
  obtain ⟨c, rfl, -⟩ := f.existsUnique_eq_smul_id_of_finrank_eq_one hM
  rw [det_smul, det_id, mul_one, hM, pow_one, LinearMap.smul_apply, id_apply]

/-- **Intertwined endomorphisms have the same determinant.** If a linear equivalence `e`
intertwines endomorphisms `f` and `g`, that is `e ∘ₗ f = g ∘ₗ e`, then `det f = det g`. This is
Mathlib's `LinearMap.det_conj` with the conjugation written as a commuting square. -/
theorem det_eq_of_comp_eq {f : M →ₗ[R] M} {g : N →ₗ[R] N} (e : M ≃ₗ[R] N)
    (h : (e : M →ₗ[R] N) ∘ₗ f = g ∘ₗ (e : M →ₗ[R] N)) : LinearMap.det f = LinearMap.det g := by
  rw [← det_conj f e, ← comp_assoc, h, comp_assoc, LinearEquiv.comp_coe, e.symm_trans_self,
    LinearEquiv.refl_toLinearMap, comp_id]

end LinearMap

namespace LinearEquiv

/-- An automorphism of a free module acting as multiplication by a unit `c` has determinant
`c ^ finrank R V`. -/
theorem det_eq_pow_of_forall_eq_smul {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]
    [Module.Free R V] (e : V ≃ₗ[R] V) (c : Rˣ) (h : ∀ x, e x = c • x) :
    LinearEquiv.det e = c ^ Module.finrank R V := by
  have he : (e : V →ₗ[R] V) = (c : R) • LinearMap.id :=
    LinearMap.ext fun x ↦ by simp [h, Units.smul_def]
  ext
  rw [LinearEquiv.coe_det, he, LinearMap.det_smul, LinearMap.det_id, mul_one,
    Units.val_pow_eq_pow_val]

/-- The determinant kernel on a finite free module of rank at most one is trivial. -/
@[simp]
theorem det_ker_eq_bot_of_finrank_le_one {R V : Type*} [CommRing R] [AddCommGroup V]
    [Module R V] [Module.Free R V] [Module.Finite R V] (hV : Module.finrank R V ≤ 1) :
    (LinearEquiv.det (R := R) (M := V)).ker = ⊥ := by
  nontriviality R
  refine (Subgroup.eq_bot_iff_forall _).mpr fun g hg => ?_
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hV with hV | hV
  · have := (Module.finrank_eq_zero_iff_of_free R V).mp hV
    exact Subsingleton.elim _ _
  · have := SpecialLinearGroup.subsingleton_of_finrank_eq_one (R := R) (V := V) hV
    exact congrArg Subtype.val (Subsingleton.elim (⟨g, hg⟩ : SpecialLinearGroup R V) 1)

end LinearEquiv

namespace Matrix

/-- The row determinant form evaluated on a family of rows is the determinant of the matrix with
those rows. -/
theorem detRowAlternating_apply {n R : Type*} [Fintype n] [DecidableEq n] [CommRing R]
    (v : n → n → R) : detRowAlternating v = (Matrix.of v).det :=
  -- Mathlib defines `det` as evaluation of `detRowAlternating` on the rows.
  rfl

/-- Evaluating the row determinant form after a family of linear functionals gives the
matrix of those functionals evaluated on the input vectors. -/
@[simp]
theorem detRowAlternating_pi_apply {ι R F : Type*} [Fintype ι]
    [DecidableEq ι] [CommRing R] [AddCommGroup F] [Module R F]
    (f : ι → Module.Dual R F) (v : ι → F) :
    detRowAlternating (fun i => LinearMap.pi f (v i)) =
      (Matrix.of fun i j => f j (v i)).det := by
  have hmatrix : (fun i => LinearMap.pi f (v i)) = Matrix.of (fun i j => f j (v i)) := by
    ext i j
    simp only [LinearMap.pi_apply, Matrix.of_apply]
  -- Mathlib defines `det` as evaluation of `detRowAlternating` on the rows.
  simpa only [Matrix.det] using congrArg Matrix.det hmatrix

/-- The multilinear form obtained by precomposing the row determinant with a family of linear
functionals evaluates to the determinant of their evaluation matrix. -/
theorem detRowAlternating_compLinearMap_pi_apply {ι R F : Type*} [Fintype ι]
    [DecidableEq ι] [CommRing R] [AddCommGroup F] [Module R F]
    (f : ι → Module.Dual R F) (v : ι → F) :
    (detRowAlternating.compLinearMap (LinearMap.pi f)).toMultilinearMap v =
      (Matrix.of fun i j => f j (v i)).det := by
  rw [AlternatingMap.coe_multilinearMap, AlternatingMap.compLinearMap_apply,
    detRowAlternating_pi_apply]

end Matrix

namespace TauCeti

/-- If an ideal contains all evaluation determinants whose rows lie in a set, it also contains
those whose rows lie in the linear span of that set. The row and functional families may be
indexed by any finite type. -/
theorem det_mem_of_mem_span {ι R F : Type*} [Fintype ι] [DecidableEq ι] [CommRing R]
    [AddCommGroup F] [Module R F] {s : Set F} {I : Ideal R} (f : ι → Dual R F) {v : ι → F}
    (hv : ∀ i, v i ∈ Submodule.span R s)
    (h : ∀ w : ι → F, (∀ i, w i ∈ s) → (Matrix.of fun i j ↦ f j (w i)).det ∈ I) :
    (Matrix.of fun i j ↦ f j (v i)).det ∈ I := by
  rw [← Matrix.detRowAlternating_compLinearMap_pi_apply]
  refine Submodule.span_le.2 ?_ <|
    MultilinearMap.map_mem_span_image_pi
      (Matrix.detRowAlternating.compLinearMap (LinearMap.pi f)).toMultilinearMap (fun _ ↦ s) hv
  rintro _ ⟨w, hw, rfl⟩
  rw [Matrix.detRowAlternating_compLinearMap_pi_apply]
  exact h w fun i ↦ hw i trivial

end TauCeti

namespace Matrix

/-- Multiplication by a square matrix scales the standard-basis determinant form by its
determinant. This is `AlternatingMap.compLinearMap_eq_det_smul` at `ω = (Pi.basisFun R ι).det`,
in matrix vocabulary. -/
@[simp]
theorem detRowAlternating_mulVec {ι R : Type*} [Fintype ι] [DecidableEq ι] [CommRing R]
    (M : Matrix ι ι R) (v : ι → ι → R) :
    detRowAlternating (fun i => M *ᵥ v i) = M.det * detRowAlternating v := by
  simpa only [Pi.basisFun_det, Function.comp_def, toLin'_apply, LinearMap.det_toLin'] using
    (Pi.basisFun R ι).det_comp (toLin' M) v

/-- **Jacobi's formula for a determinant, in row form.**  Rescale one row of a matrix entry by
entry along a fixed vector of factors, and sum the resulting determinants over the rows: the
answer is the determinant multiplied by the total of the factors. -/
theorem sum_det_updateRow_mul_row {ι : Type*} [DecidableEq ι] [Fintype ι] {R : Type*} [CommRing R]
    (A : Matrix ι ι R) (d : ι → R) :
    (∑ k, (A.updateRow k fun j => d j * A k j).det) = (∑ j, d j) * A.det := by
  have key (k : ι) : (A.updateRow k fun j => d j * A k j).det
      = ∑ σ : Equiv.Perm ι, ((Equiv.Perm.sign σ : ℤ) : R) * (d (σ⁻¹ k) * ∏ i, A (σ i) i) := by
    rw [det_apply']
    refine Finset.sum_congr rfl fun σ _ => ?_
    have hterm (i : ι) : (A.updateRow k fun j => d j * A k j) (σ i) i
        = (if i = σ⁻¹ k then d i else 1) * A (σ i) i := by
      rcases eq_or_ne i (σ⁻¹ k) with rfl | h
      · simp [updateRow_apply]
      · have hk : σ i ≠ k := fun hc => h (by rw [← hc]; simp)
        rw [updateRow_apply, ite_eq_right hk, ite_eq_right h, one_mul]
    rw [Finset.prod_congr rfl fun i _ => hterm i, Finset.prod_mul_distrib,
      Finset.prod_ite_eq' Finset.univ (σ⁻¹ k) d]
    simp
  rw [Finset.sum_congr rfl fun k _ => key k, Finset.sum_comm, det_apply', Finset.mul_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [← Finset.mul_sum, ← Finset.sum_mul, Equiv.sum_comp (σ⁻¹ : Equiv.Perm ι) d]
  ring

/-- **The determinant of a scaled integer matrix.** Scaling every row `i` of an integer
matrix `M` by `d i`, with the entries cast into a commutative ring `R`, multiplies the
determinant by `∏ i, d i`. -/
theorem det_mul_column_intCast {n : Type*} [Fintype n] [DecidableEq n]
    {R : Type*} [CommRing R] (d : n → R) (M : Matrix n n ℤ) :
    (of fun i j ↦ d i * (M i j : R)).det = (∏ i, d i) * (M.det : R) := by
  simpa [Int.cast_det] using det_mul_column d (M.map ((↑) : ℤ → R))

end Matrix

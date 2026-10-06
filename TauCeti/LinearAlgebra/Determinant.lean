/-
Copyright (c) 2026 Tau Ceti. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.LinearAlgebra.BilinearForm.Properties
import TauCeti.LinearAlgebra.BilinearForm.Multilinear
import Mathlib.LinearAlgebra.SpecialLinearGroup

/-!
# Determinant transformation laws, and determinants of updated rows

Precomposing an alternating form of top degree with an endomorphism `φ` multiplies it by
`LinearMap.det φ`, and — the direction that is actually used — a *nonzero* form merely known to be
*scaled* by some `d` thereby identifies `d` as the determinant, without computing it, as soon as
scalars cancel against nonzero vectors of the codomain (`IsCancelMulZero R` and
`Module.IsTorsionFree R N`; see the implementation notes, where `ω ≠ 0` alone is shown to be
insufficient). This file records that law in three vocabularies: for
an `AlternatingMap` indexed by a basis' index type, for an alternating bilinear form on a rank-two
module, and for the standard-basis determinant form under matrix multiplication.

Mathlib's `Module.Basis.det_comp` is the case `ω = b.det` of the first statement. The step taken
here is that every top-degree alternating form is a multiple of `b.det`
(`AlternatingMap.eq_basis_det_smulRight`), so the same law holds for all of them; that is what
makes the converse available for a form supplied by something other than a basis, such as a
pairing.

The file also records one identity for the determinant of a matrix with one row replaced,
alongside Mathlib's `Matrix.det_updateRow_add` and `Matrix.det_updateRow_smul`: Jacobi's formula
in row form, that rescaling one row entry by entry along a fixed vector of factors and summing the
results over the rows multiplies the determinant by the total of the factors.

## Main results

* `AlternatingMap.eq_basis_det_smulRight`: `ω = b.det.smulRight (ω b)` for `ω` of top degree.
* `AlternatingMap.compLinearMap_eq_det_smul`: `ω ∘ φ = det φ • ω` for `ω` of top degree.
* `LinearMap.det_eq_of_compLinearMap_eq_smul`: if `ω ≠ 0` and `ω ∘ φ = d • ω` then `det φ = d`,
  for `R` cancellative and `N` torsion-free.
* `LinearMap.IsAlt.compl₁₂_self_eq_det_smul` and `LinearMap.det_eq_of_compl₁₂_self_eq_smul`: the
  same two statements for an alternating bilinear form on a module of rank two.
* `LinearMap.det_eq_of_compl₁₂_self_eq_smul_of_separatingLeft`: the recovery statement over any
  commutative ring, for a left-separating form.
* `Matrix.detRowAlternating_mulVec`: multiplication by a square matrix scales the
  standard-basis determinant form by the matrix determinant.
* `Matrix.sum_det_updateRow_mul_row`: Jacobi's formula for a determinant, in row form.
* `Matrix.det_mul_column_intCast`: scaling every row `i` of an integer matrix by `d i`
  multiplies the determinant by `∏ i, d i`, over any commutative ring.
* `LinearEquiv.det_ker_eq_bot_of_finrank_le_one`: the determinant kernel is trivial in
  dimension at most one.

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
  simpa only [compl₁₂_apply, smul_apply, AlternatingMap.compLinearMap_apply,
    IsAlt.toAlternatingMap_apply, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one, AlternatingMap.smul_apply] using
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
  -- the difference kills `ω (b 0)`, so it kills `b 0` by left separation, so it vanishes
  have hb : (LinearMap.det φ - d) • b 0 = 0 := hω _ fun y ↦ by
    rw [map_smul, smul_apply, sub_smul, sub_eq_zero]
    simpa using congr($hd (b 0) y)
  rw [← sub_eq_zero]
  simpa using congr(b.repr $hb 0)

end LinearMap

namespace LinearEquiv

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

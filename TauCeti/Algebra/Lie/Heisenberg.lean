/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.GeneralLinear.Borel
public import TauCeti.Algebra.Lie.UniversalEnveloping.Augmentation
-- Private: `fin_cases` is used only inside proofs.
import Mathlib.Tactic.FinCases
-- Private: the Lie module structure of `gl n R` on the column space is used only by the
-- faithfulness example at the end of the file.
import Mathlib.Algebra.Lie.Matrix

/-!
# The three-dimensional Heisenberg Lie algebra

The Heisenberg Lie algebra is the strictly upper triangular `3 × 3` matrices, that is,
`TauCeti.strictUpperTriangular R (Fin 3)`, and `TauCeti.heisenberg` is that Lie subalgebra of
`gl 3 R` under its traditional name. It is free of rank three on the matrix units

`x = E₀₁`, `y = E₁₂`, `z = E₀₂`,

whose only nonzero bracket is `⁅x, y⁆ = z`. Everything below comes out of one computation,
`TauCeti.lie_eq_smul_heisenbergZ`: the bracket of two strictly upper triangular `3 × 3` matrices
is a multiple of the corner `z`, with the `2 × 2` determinant of their two superdiagonal entries as
its coefficient. Products of three of them vanish, so `z` is central and the algebra is nilpotent
of class two, with `⁅L, L⁆` and the centre both equal to the line `R ∙ z`.

This is the standard two-step nilpotent Lie algebra, and it is the test case the Ado--Iwasawa
roadmap asks for at two places. Its centre shows that the adjoint representation is *not* faithful
(`TauCeti.not_isFaithful_heisenberg`), so the finite-dimensional faithful representation that Ado's
theorem provides cannot be the adjoint one; here the defining action on `R³` supplies one, but for
a general nilpotent Lie algebra it is the weighted quotient of the universal enveloping algebra by
a power of the augmentation ideal that does. And the augmentation ideal `U⁺(L)` of
`TauCeti/Algebra/Lie/UniversalEnveloping/Augmentation.lean` pins its indexing convention here: the
central generator `z` is a single bracket, so it lands in the **square** `(U⁺)²` and not merely in
`U⁺` itself (`TauCeti.ι_heisenbergZ_mem_augmentation_toIdeal_sq`).

## Main definitions

* `TauCeti.heisenberg`: the three-dimensional Heisenberg Lie algebra over `R`, as the Lie
  subalgebra `TauCeti.strictUpperTriangular R (Fin 3)` of `gl 3 R`.
* `TauCeti.heisenbergX`, `TauCeti.heisenbergY`, `TauCeti.heisenbergZ`: its standard generators
  `E₀₁`, `E₁₂` and `E₀₂`.
* `TauCeti.heisenbergEquivFun` and `TauCeti.heisenbergBasis`: the coordinate isomorphism
  `heisenberg R ≃ₗ[R] (Fin 3 → R)` reading off the three superdiagonal and corner entries, and the
  basis `(x, y, z)` it produces, whose three vectors are `TauCeti.heisenbergBasis_zero`,
  `TauCeti.heisenbergBasis_one` and `TauCeti.heisenbergBasis_two`.

## Main results

* `TauCeti.lie_eq_smul_heisenbergZ`: **the bracket is a multiple of the corner generator**, with an
  explicit coefficient. The defining relation `TauCeti.lie_heisenbergX_heisenbergY` and the
  centrality `TauCeti.heisenbergZ_lie`, `TauCeti.lie_heisenbergZ` of `z` — which together are the
  whole bracket table — are its special cases.
* `TauCeti.lie_lie_heisenberg_eq_zero` and `TauCeti.lie_mem_center_heisenberg`: **an iterated
  bracket vanishes**, so every bracket is central.
* `TauCeti.finrank_heisenberg`: the Heisenberg Lie algebra is free of rank three.
* `TauCeti.center_heisenberg_toSubmodule` and
  `TauCeti.lowerCentralSeries_heisenberg_one_toSubmodule`: **the centre and the derived subalgebra
  are both the line `R ∙ z`**, and `TauCeti.lowerCentralSeries_heisenberg_two` is the vanishing of
  the next term, which makes the Heisenberg Lie algebra nilpotent of class two.
* `TauCeti.not_isFaithful_heisenberg`: **the adjoint representation is not faithful**, in contrast
  with the defining action on `R³`.
* `TauCeti.ι_heisenbergZ_mem_augmentation_toIdeal_sq`: **the central generator lies in the square of
  the augmentation ideal** of `U(L)`.

## Implementation notes

`TauCeti.heisenberg` is an abbreviation rather than a new type: the Heisenberg Lie algebra *is* the
strict upper triangle of `gl 3 R`, and every fact about `TauCeti.strictUpperTriangular` — that it is
a Lie subalgebra, spanned by the raising matrix units, closed under the associative product — is
meant to apply to it unchanged. What this file adds is the three-dimensional arithmetic, which the
general `n` does not have: for `n = 3`, and only there, a bracket is a multiple of a single fixed
matrix unit.

Everything is stated over an arbitrary commutative ring. `[Nontrivial R]` appears only where a
generator is claimed to be nonzero, and `[StrongRankCondition R]` only for the rank computation, as
in `TauCeti/Algebra/Lie/Sl2/Basic.lean`. Mathlib does not register `LieRing.ofAssociativeRing` as a
global instance, so, as in `Mathlib/Algebra/Lie/Classical.lean` and in
`TauCeti/Algebra/Lie/GeneralLinear/Borel.lean`, it is a local instance here.

## References

This supplies the Heisenberg test case of Layer 2 of
`TauCetiRoadmap/RepresentationTheory/AdoIwasawa/README.md`, whose "powers and brackets" milestone
asks to "state the exact indexing convention and test it on the Heisenberg algebra, where the
central bracket belongs to the square of the augmentation ideal", and whose acceptance criterion
asks for the three-dimensional Heisenberg Lie algebra together with the observation that the
adjoint representation does not detect its centre.

* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory* (1972), §1.2 and §17.
-/

public section

namespace TauCeti

open Matrix LieAlgebra LieModule Module

attribute [local instance 100] LieRing.ofAssociativeRing

variable (R : Type*) [CommRing R]

/-- **The three-dimensional Heisenberg Lie algebra** over `R`: the strictly upper triangular
`3 × 3` matrices, as a Lie subalgebra of `gl 3 R = Matrix (Fin 3) (Fin 3) R`.

It is free of rank three on the matrix units `x = E₀₁`, `y = E₁₂` and `z = E₀₂`
(`TauCeti.heisenbergBasis`), whose only nonzero bracket is `⁅x, y⁆ = z`. -/
abbrev heisenberg : LieSubalgebra R (Matrix (Fin 3) (Fin 3) R) :=
  strictUpperTriangular R (Fin 3)

/-- The generator `x = E₀₁` of the Heisenberg Lie algebra. -/
def heisenbergX : heisenberg R :=
  ⟨single 0 1 1, single_mem_strictUpperTriangular (by decide) 1⟩

/-- The generator `y = E₁₂` of the Heisenberg Lie algebra. -/
def heisenbergY : heisenberg R :=
  ⟨single 1 2 1, single_mem_strictUpperTriangular (by decide) 1⟩

/-- The central generator `z = E₀₂` of the Heisenberg Lie algebra, the bracket `⁅x, y⁆`. -/
def heisenbergZ : heisenberg R :=
  ⟨single 0 2 1, single_mem_strictUpperTriangular (by decide) 1⟩

@[simp]
theorem coe_heisenbergX : (heisenbergX R : Matrix (Fin 3) (Fin 3) R) = single 0 1 1 := (rfl)

@[simp]
theorem coe_heisenbergY : (heisenbergY R : Matrix (Fin 3) (Fin 3) R) = single 1 2 1 := (rfl)

@[simp]
theorem coe_heisenbergZ : (heisenbergZ R : Matrix (Fin 3) (Fin 3) R) = single 0 2 1 := (rfl)

variable {R}

/-! ### Coordinates -/

/-- **The entries of a strictly upper triangular `3 × 3` matrix expand it in the three matrix
units** `E₀₁`, `E₁₂` and `E₀₂`. -/
theorem eq_smul_heisenbergX_add_smul_heisenbergY_add_smul_heisenbergZ (A : heisenberg R) :
    A = (A : Matrix (Fin 3) (Fin 3) R) 0 1 • heisenbergX R
      + (A : Matrix (Fin 3) (Fin 3) R) 1 2 • heisenbergY R
      + (A : Matrix (Fin 3) (Fin 3) R) 0 2 • heisenbergZ R := by
  have hA := mem_strictUpperTriangular_iff.mp A.2
  refine Subtype.ext (Matrix.ext fun i j => ?_)
  fin_cases i <;> fin_cases j <;> simp [hA]

/-- A multiple of the central generator vanishes only for a vanishing coefficient: reading off the
corner entry recovers the coefficient. -/
@[simp]
theorem smul_heisenbergZ_eq_zero_iff {c : R} : c • heisenbergZ R = 0 ↔ c = 0 := by
  refine ⟨fun h => ?_, fun h => by rw [h, zero_smul]⟩
  have h' := congrArg (fun A : heisenberg R => (A : Matrix (Fin 3) (Fin 3) R) 0 2) h
  simpa using h'

/-- The central generator is nonzero over a nontrivial ring. -/
theorem heisenbergZ_ne_zero [Nontrivial R] : heisenbergZ R ≠ 0 := by
  intro h
  rw [← one_smul R (heisenbergZ R), smul_heisenbergZ_eq_zero_iff] at h
  exact one_ne_zero h

/-! ### The bracket -/

/-- **The bracket of the Heisenberg Lie algebra is a multiple of its central generator.** The
coefficient is the `2 × 2` determinant of the two superdiagonal entries, so the whole bracket
structure of the strict upper triangle in size three is one `2 × 2` determinant. -/
theorem lie_eq_smul_heisenbergZ (A B : heisenberg R) :
    ⁅A, B⁆ = ((A : Matrix (Fin 3) (Fin 3) R) 0 1 * (B : Matrix (Fin 3) (Fin 3) R) 1 2
      - (B : Matrix (Fin 3) (Fin 3) R) 0 1 * (A : Matrix (Fin 3) (Fin 3) R) 1 2)
      • heisenbergZ R := by
  have hA := mem_strictUpperTriangular_iff.mp A.2
  have hB := mem_strictUpperTriangular_iff.mp B.2
  refine Subtype.ext (Matrix.ext fun i j => ?_)
  fin_cases i <;> fin_cases j <;>
    simp [LieRing.of_associative_ring_bracket, Matrix.mul_apply, Fin.sum_univ_three, hA, hB]

/-- **The defining relation of the Heisenberg Lie algebra**: `⁅x, y⁆ = z`. -/
@[simp]
theorem lie_heisenbergX_heisenbergY : ⁅heisenbergX R, heisenbergY R⁆ = heisenbergZ R := by
  rw [lie_eq_smul_heisenbergZ]
  simp

/-- **The central generator commutes with everything.** -/
@[simp]
theorem heisenbergZ_lie (A : heisenberg R) : ⁅heisenbergZ R, A⁆ = 0 := by
  rw [lie_eq_smul_heisenbergZ]
  simp

/-- **The central generator commutes with everything**, on the other side. -/
@[simp]
theorem lie_heisenbergZ (A : heisenberg R) : ⁅A, heisenbergZ R⁆ = 0 := by
  rw [← lie_skew, heisenbergZ_lie, neg_zero]

/-- **A product of three brackets vanishes**: the Heisenberg Lie algebra is nilpotent of class
two. -/
theorem lie_lie_heisenberg_eq_zero (A B C : heisenberg R) : ⁅⁅A, B⁆, C⁆ = 0 := by
  rw [lie_eq_smul_heisenbergZ A B, smul_lie, heisenbergZ_lie, smul_zero]

/-- A bracket lies in the centre of the Heisenberg Lie algebra. -/
theorem lie_mem_center_heisenberg (A B : heisenberg R) :
    ⁅A, B⁆ ∈ center R (heisenberg R) := by
  rw [LieModule.mem_maxTrivSubmodule]
  intro C
  rw [← lie_skew, lie_lie_heisenberg_eq_zero, neg_zero]

/-! ### Coordinates, as a basis -/

variable (R)

/-- **The coordinate isomorphism of the Heisenberg Lie algebra**: a strictly upper triangular
`3 × 3` matrix is its two superdiagonal entries together with its corner entry. -/
def heisenbergEquivFun : heisenberg R ≃ₗ[R] (Fin 3 → R) where
  toFun A := ![(A : Matrix (Fin 3) (Fin 3) R) 0 1, (A : Matrix (Fin 3) (Fin 3) R) 1 2,
    (A : Matrix (Fin 3) (Fin 3) R) 0 2]
  map_add' A B := by ext k; fin_cases k <;> simp
  map_smul' c A := by ext k; fin_cases k <;> simp
  invFun v := v 0 • heisenbergX R + v 1 • heisenbergY R + v 2 • heisenbergZ R
  left_inv A := by
    simpa using (eq_smul_heisenbergX_add_smul_heisenbergY_add_smul_heisenbergZ A).symm
  right_inv v := by ext k; fin_cases k <;> simp

variable {R}

@[simp]
theorem heisenbergEquivFun_apply (A : heisenberg R) :
    heisenbergEquivFun R A = ![(A : Matrix (Fin 3) (Fin 3) R) 0 1,
      (A : Matrix (Fin 3) (Fin 3) R) 1 2, (A : Matrix (Fin 3) (Fin 3) R) 0 2] := (rfl)

@[simp]
theorem heisenbergEquivFun_symm_apply (v : Fin 3 → R) :
    (heisenbergEquivFun R).symm v
      = v 0 • heisenbergX R + v 1 • heisenbergY R + v 2 • heisenbergZ R := (rfl)

variable (R)

/-- **The standard basis of the Heisenberg Lie algebra**, the matrix units `x = E₀₁`, `y = E₁₂`
and `z = E₀₂`; see `TauCeti.heisenbergBasis_apply`. -/
noncomputable def heisenbergBasis : Basis (Fin 3) R (heisenberg R) :=
  Basis.ofEquivFun (heisenbergEquivFun R)

variable {R}

theorem heisenbergBasis_apply (k : Fin 3) :
    heisenbergBasis R k = ![heisenbergX R, heisenbergY R, heisenbergZ R] k := by
  rw [heisenbergBasis, Basis.coe_ofEquivFun]
  fin_cases k <;> · refine Subtype.ext (Matrix.ext fun a b => ?_); fin_cases a <;> fin_cases b <;>
      simp

variable (R)

/-- The first standard basis vector of the Heisenberg Lie algebra is `x = E₀₁`. -/
@[simp]
theorem heisenbergBasis_zero : heisenbergBasis R 0 = heisenbergX R := heisenbergBasis_apply 0

/-- The second standard basis vector of the Heisenberg Lie algebra is `y = E₁₂`. -/
@[simp]
theorem heisenbergBasis_one : heisenbergBasis R 1 = heisenbergY R := heisenbergBasis_apply 1

/-- The third standard basis vector of the Heisenberg Lie algebra is the central `z = E₀₂`. -/
@[simp]
theorem heisenbergBasis_two : heisenbergBasis R 2 = heisenbergZ R := heisenbergBasis_apply 2

/-- **The Heisenberg Lie algebra is free of rank three.** -/
@[simp]
theorem finrank_heisenberg [StrongRankCondition R] : finrank R (heisenberg R) = 3 := by
  rw [finrank_eq_card_basis (heisenbergBasis R), Fintype.card_fin]

/-! ### The centre and the lower central series -/

/-- **The centre of the Heisenberg Lie algebra is the line spanned by its central generator.** -/
theorem center_heisenberg_toSubmodule :
    (center R (heisenberg R)).toSubmodule = R ∙ heisenbergZ R := by
  refine le_antisymm (fun A hA => ?_) ?_
  · rw [LieSubmodule.mem_toSubmodule, LieModule.mem_maxTrivSubmodule] at hA
    -- bracketing with `x` reads off the entry `A 1 2`, bracketing with `y` the entry `A 0 1`
    have hx := hA (heisenbergX R)
    have hy := hA (heisenbergY R)
    rw [lie_eq_smul_heisenbergZ] at hx hy
    simp only [coe_heisenbergX, coe_heisenbergY, single_apply,
      smul_heisenbergZ_eq_zero_iff] at hx hy
    norm_num at hx hy
    rw [Submodule.mem_span_singleton]
    refine ⟨(A : Matrix (Fin 3) (Fin 3) R) 0 2, ?_⟩
    rw [eq_smul_heisenbergX_add_smul_heisenbergY_add_smul_heisenbergZ A, hx, hy]
    simp
  · -- conversely `z = ⁅x, y⁆` is a bracket, and every bracket is central
    rw [Submodule.span_le, Set.singleton_subset_iff, SetLike.mem_coe,
      LieSubmodule.mem_toSubmodule, ← lie_heisenbergX_heisenbergY]
    exact lie_mem_center_heisenberg _ _

/-- **The derived subalgebra of the Heisenberg Lie algebra is the line spanned by its central
generator**, and so coincides with its centre. -/
theorem lowerCentralSeries_heisenberg_one_toSubmodule :
    (lowerCentralSeries R (heisenberg R) (heisenberg R) 1).toSubmodule = R ∙ heisenbergZ R := by
  refine le_antisymm ?_ ?_
  · rw [LieModule.lowerCentralSeries_succ, LieSubmodule.lieIdeal_oper_eq_linear_span',
      Submodule.span_le]
    rintro _ ⟨A, -, B, -, rfl⟩
    rw [SetLike.mem_coe, lie_eq_smul_heisenbergZ, Submodule.mem_span_singleton]
    exact ⟨_, rfl⟩
  · rw [Submodule.span_le, Set.singleton_subset_iff, SetLike.mem_coe,
      LieSubmodule.mem_toSubmodule, ← lie_heisenbergX_heisenbergY,
      LieModule.lowerCentralSeries_succ]
    exact LieSubmodule.lie_mem_lie trivial trivial

/-- **The Heisenberg Lie algebra is nilpotent of class two**: the second term of its lower central
series vanishes. -/
theorem lowerCentralSeries_heisenberg_two :
    lowerCentralSeries R (heisenberg R) (heisenberg R) 2 = ⊥ := by
  rw [LieModule.lowerCentralSeries_succ, LieSubmodule.lie_eq_bot_iff]
  intro A _ B hB
  have hmem : B ∈ center R (heisenberg R) := by
    rw [← LieSubmodule.mem_toSubmodule, center_heisenberg_toSubmodule,
      ← lowerCentralSeries_heisenberg_one_toSubmodule, LieSubmodule.mem_toSubmodule]
    exact hB
  rw [LieModule.mem_maxTrivSubmodule] at hmem
  exact hmem A

instance instIsNilpotentHeisenberg : LieModule.IsNilpotent (heisenberg R) (heisenberg R) :=
  (LieModule.isNilpotent_iff R _ _).mpr ⟨2, lowerCentralSeries_heisenberg_two R⟩

/-! ### Faithfulness -/

/-- The Heisenberg Lie algebra is not abelian. -/
theorem not_isLieAbelian_heisenberg [Nontrivial R] : ¬ IsLieAbelian (heisenberg R) := by
  intro h
  exact heisenbergZ_ne_zero (R := R) (lie_heisenbergX_heisenbergY.symm.trans (h.trivial _ _))

/-- **The adjoint representation of the Heisenberg Lie algebra is not faithful**: it kills the
central generator. The defining action on `R³` is faithful, so this is a property of the adjoint
representation and not of the algebra. -/
theorem not_isFaithful_heisenberg [Nontrivial R] :
    ¬ LieModule.IsFaithful R (heisenberg R) (heisenberg R) := by
  rw [isFaithful_self_iff]
  intro h
  refine heisenbergZ_ne_zero (R := R) ?_
  have : heisenbergZ R ∈ center R (heisenberg R) := by
    rw [← LieSubmodule.mem_toSubmodule, center_heisenberg_toSubmodule]
    exact Submodule.mem_span_singleton_self _
  rw [h] at this
  simpa using this

/-- The defining action of the Heisenberg Lie algebra on `R³` *is* faithful: a Lie subalgebra of
`gl 3 R` acts faithfully on the column space, by `LieModule.instIsFaithful`. -/
example : LieModule.IsFaithful R (heisenberg R) (Fin 3 → R) := inferInstance

/-! ### The augmentation ideal -/

/-- **The central generator of the Heisenberg Lie algebra lies in the square of the augmentation
ideal** of its universal enveloping algebra, being the single bracket `⁅x, y⁆`. This is the
indexing convention of
`TauCeti.UniversalEnvelopingAlgebra.ι_mem_augmentation_toIdeal_pow_of_mem_lowerCentralSeries`,
whose `n`-th term of the lower central series lands in the `(n + 1)`-st power: `z` belongs to the
first term, not the zeroth. -/
theorem ι_heisenbergZ_mem_augmentation_toIdeal_sq :
    _root_.UniversalEnvelopingAlgebra.ι R (heisenbergZ R) ∈
      (HopfIdeal.augmentation R
        (_root_.UniversalEnvelopingAlgebra R (heisenberg R))).toIdeal ^ 2 := by
  rw [← lie_heisenbergX_heisenbergY]
  exact UniversalEnvelopingAlgebra.ι_lie_mem_augmentation_toIdeal_sq R (heisenberg R) _ _

end TauCeti

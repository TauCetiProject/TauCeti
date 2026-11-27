/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.Killing
public import TauCeti.Algebra.Lie.Cohomology.CartanThreeForm
public import TauCeti.Algebra.Lie.Unitary
import Mathlib.Algebra.Lie.Classical
import TauCeti.Algebra.Lie.Killing.Subalgebra
import TauCeti.Data.Matrix.Block
import TauCeti.Algebra.Lie.Unitary.Killing
import TauCeti.Analysis.Matrix.Frobenius

/-!
# The special unitary Lie algebra, its Killing form and its block inclusions

The Lie algebra of the special unitary group `SU(n)` is the real Lie algebra `𝔰𝔲(n)` of
trace-free skew-Hermitian `n × n` matrices (`TauCeti.specialUnitaryLieAlgebra ι`, with
`n = card ι`), a real Lie subalgebra of `𝔲(n) = TauCeti.unitaryLieAlgebra ι`. In the algebra
coordinates of the general linear group these are the matrices of the Lie algebra of the special
unitary subgroup
(`TauCeti.Lie.unitsLieAlgebraLieEquiv_symm_mem_GLSpecialUnitary_lieSubalgebra_iff`), and inside
`𝔲(n)` they form its derived algebra (`TauCeti.coe_mem_specialUnitaryLieAlgebra_iff`), the
complement of the centre `iℝ · 1`. Its real dimension is `n² - 1`
(`TauCeti.finrank_specialUnitaryLieAlgebra`): the imaginary part of the trace is a surjection
`𝔲(n) → ℝ` with kernel `𝔰𝔲(n)` (for `n ≥ 1`), and `𝔲(n)` has dimension `n²`.
Reindexed along `ι ≃ ι ⊕ ∅`, the same algebra is the indefinite special unitary algebra `𝔰𝔲(n, 0)`
(`TauCeti.specialIndefiniteUnitaryLieAlgebra`); as for `𝔲(n)`, the compact algebra is given its own
carrier on `Matrix ι ι ℂ`, so that its block inclusions and conjugations are stated on matrices
indexed by `ι`.

The Killing form of `𝔰𝔲(n)` is `κ(X, Y) = 2 n Re tr(X Y)`
(`TauCeti.killingForm_specialUnitaryLieAlgebra_apply`), the restriction of the Killing form of
`𝔲(n)`, whose trace correction `-2 tr X tr Y` vanishes on trace-free matrices. It is negative
definite (`TauCeti.killingForm_specialUnitaryLieAlgebra_self_neg`): `κ(X, X) = -2 n Re tr(X Xᴴ)` is
`-2 n` times the sum of the squared absolute values of the entries of `X`.

Placing a matrix in the top-left block, `X ↦ diag(X, 0)`, is an injective homomorphism
`𝔰𝔲(m) → 𝔰𝔲(m + k)` (`TauCeti.specialUnitaryBlockInclusion`). Since the trace of a product of
block matrices is the trace of the product of the blocks, the Killing form of `𝔰𝔲(m + k)` pulls
back along it to `(m + k) / m` times the Killing form of `𝔰𝔲(m)`
(`TauCeti.card_smul_killingForm_compl₁₂_specialUnitaryBlockInclusion`), and the same holds for the
Cartan three-forms `ω(X, Y, Z) = κ(X, ⁅Y, Z⁆)`
(`TauCeti.card_smul_cartanThreeForm_compLinearMap_specialUnitaryBlockInclusion`). So the values of
the Cartan three-form of a compact group on a subalgebra `𝔰𝔲(2) ⊆ 𝔰𝔲(n)` depend on `n`, but their
signs do not. These Cartan three-forms are how a homomorphism `SU(2) → G` attached to a root of a
compact group is shown to be essential on `π₃`.

The unitary group acts on `𝔰𝔲(n)` by conjugation, `X ↦ U X Uᴴ`, through Lie algebra endomorphisms
(`TauCeti.specialUnitaryAdjoint`) that compose as the group multiplies
(`TauCeti.specialUnitaryAdjoint_one`, `TauCeti.specialUnitaryAdjoint_mul`), hence are automorphisms;
for `SU(2)` and `U` a Weyl element this exchanges the two coroots `±diag(i, -i)` of the diagonal
torus. Packaged as a representation (`TauCeti.specialUnitaryAdjointRepresentation`) this is the
adjoint representation of `SU(n)` extended to `U(n)`; its invariant metric, orientation and kernel
are computed in `TauCeti.Algebra.Lie.Unitary.Adjoint`.

## Main definitions

* `TauCeti.specialUnitaryLieAlgebra`: the real Lie algebra `𝔰𝔲(n)`.
* `TauCeti.specialUnitaryBlockInclusion`: the block inclusion `𝔰𝔲(m) → 𝔰𝔲(m + k)`.
* `TauCeti.specialUnitaryAdjoint`: conjugation by a unitary matrix on `𝔰𝔲(n)`.
* `TauCeti.specialUnitaryAdjointRepresentation ι`: the action of `U(n)` on `𝔰𝔲(n)` by
  conjugation, as a representation.

## Main results

* `TauCeti.coe_mem_specialUnitaryLieAlgebra_iff`: `𝔰𝔲(n)` is the derived algebra of `𝔲(n)`.
* `TauCeti.mem_range_scalar_of_forall_mem_specialUnitaryLieAlgebra_commute`: a matrix commuting
  with every element of `𝔰𝔲(n)` is scalar.
* `TauCeti.finrank_specialUnitaryLieAlgebra`: `𝔰𝔲(n)` has real dimension `n² - 1`.
* `TauCeti.killingForm_specialUnitaryLieAlgebra_apply`: `κ(X, Y) = 2 n Re tr(X Y)`.
* `TauCeti.killingForm_specialUnitaryLieAlgebra_self_neg`: the Killing form is negative definite.
* `TauCeti.card_smul_killingForm_compl₁₂_specialUnitaryBlockInclusion`,
  `TauCeti.card_smul_cartanThreeForm_compLinearMap_specialUnitaryBlockInclusion`: the Killing form
  and the Cartan three-form of `𝔰𝔲(m + k)` restrict to `(m + k) / m` times those of `𝔰𝔲(m)`.

## References

* A. W. Knapp, *Lie Groups Beyond an Introduction*, second edition, Progress in Mathematics 140,
  Birkhäuser, 2002, Chapter I, §§1 and 8 (`𝔰𝔲(n)` and its Killing form).
* E. Meinrenken, *Lie groups and Lie algebras*, lecture notes, §§8 and 12.
* R. Bott, *An application of the Morse theory to the topology of Lie-groups*, Bull. Soc. Math.
  France 84 (1956), 251–281, §1.
* Brian C. Hall, *Lie Groups, Lie Algebras, and Representations*, second edition,
  Springer GTM 222, 2015, Chapter 3 (the Lie algebras of the classical groups).
-/

public section

noncomputable section

open LieAlgebra Matrix Module Complex
open scoped ComplexOrder

attribute [local instance 100] LieRing.ofAssociativeRing

namespace TauCeti

variable (ι κ : Type*) [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/-! ### The special unitary Lie algebra -/

/-- The **special unitary Lie algebra** `𝔰𝔲(n)`: the real Lie subalgebra of `Matrix ι ι ℂ`
consisting of the trace-free skew-Hermitian matrices, `Xᴴ = -X` and `tr X = 0`. It is the Lie
algebra of the special unitary group. -/
def specialUnitaryLieAlgebra : LieSubalgebra ℝ (Matrix ι ι ℂ) where
  carrier := {X | Xᴴ = -X ∧ X.trace = 0}
  add_mem' hX hY := ⟨by rw [conjTranspose_add, hX.1, hY.1, neg_add], by
    rw [trace_add, hX.2, hY.2, add_zero]⟩
  zero_mem' := ⟨by rw [conjTranspose_zero, neg_zero], trace_zero _ _⟩
  smul_mem' r X hX := ⟨by rw [conjTranspose_smul, star_trivial, hX.1, smul_neg], by
    rw [trace_smul, hX.2, smul_zero]⟩
  lie_mem' hX hY := ⟨mem_unitaryLieAlgebra_iff.mp <| LieSubalgebra.lie_mem _
    (mem_unitaryLieAlgebra_iff.mpr hX.1) (mem_unitaryLieAlgebra_iff.mpr hY.1),
    matrix_trace_commutator_zero _ _ _ _⟩

variable {ι κ}

@[simp]
theorem mem_specialUnitaryLieAlgebra_iff {X : Matrix ι ι ℂ} :
    X ∈ specialUnitaryLieAlgebra ι ↔ Xᴴ = -X ∧ X.trace = 0 :=
  Iff.rfl

@[simp]
theorem conjTranspose_coe_specialUnitaryLieAlgebra (X : specialUnitaryLieAlgebra ι) :
    (X : Matrix ι ι ℂ)ᴴ = -X :=
  X.property.1

@[simp]
theorem trace_coe_specialUnitaryLieAlgebra (X : specialUnitaryLieAlgebra ι) :
    (X : Matrix ι ι ℂ).trace = 0 :=
  X.property.2

variable (ι) in
/-- `𝔰𝔲(n)` is contained in `𝔲(n)`. -/
theorem specialUnitaryLieAlgebra_le_unitaryLieAlgebra :
    specialUnitaryLieAlgebra ι ≤ unitaryLieAlgebra ι :=
  fun _ hX ↦ mem_unitaryLieAlgebra_iff.mpr hX.1

/-- **`𝔰𝔲(n)` is an ideal of `𝔲(n)`**, and indeed contains every bracket of `𝔲(n)`: the
bracket of two skew-Hermitian matrices is trace-free. -/
theorem lie_mem_specialUnitaryLieAlgebra_of_mem_unitaryLieAlgebra {X Y : Matrix ι ι ℂ}
    (hX : X ∈ unitaryLieAlgebra ι) (hY : Y ∈ unitaryLieAlgebra ι) :
    ⁅X, Y⁆ ∈ specialUnitaryLieAlgebra ι :=
  ⟨mem_unitaryLieAlgebra_iff.mp <| LieSubalgebra.lie_mem _ hX hY,
    matrix_trace_commutator_zero _ _ X Y⟩

instance : FiniteDimensional ℝ (specialUnitaryLieAlgebra ι) :=
  Module.Finite.of_injective (LieSubalgebra.inclusion
    (specialUnitaryLieAlgebra_le_unitaryLieAlgebra ι)).toLinearMap
    (LieSubalgebra.inclusion_injective _)

/-- **`𝔰𝔲(n)` is the derived algebra of `𝔲(n)`**: an element of `𝔲(n)` lies in `𝔰𝔲(n)` exactly
when it lies in `[𝔲(n), 𝔲(n)]`. -/
theorem coe_mem_specialUnitaryLieAlgebra_iff {X : unitaryLieAlgebra ι} :
    (X : Matrix ι ι ℂ) ∈ specialUnitaryLieAlgebra ι ↔
      X ∈ derivedSeries ℝ (unitaryLieAlgebra ι) 1 := by
  rw [mem_derivedSeries_one_unitaryLieAlgebra_iff, mem_specialUnitaryLieAlgebra_iff]
  exact and_iff_right (conjTranspose_coe_unitaryLieAlgebra X)

/-- **A matrix commuting with every element of `𝔰𝔲(n)` is scalar.** -/
theorem mem_range_scalar_of_forall_mem_specialUnitaryLieAlgebra_commute {M : Matrix ι ι ℂ}
    (h : ∀ X ∈ specialUnitaryLieAlgebra ι, Commute X M) : M ∈ Set.range (scalar ι) := by
  -- For `i ≠ j`, `E_ij = (A - I • B) / 2` with `A = E_ij - E_ji` and `B = I • (E_ij + E_ji)`.
  refine mem_range_scalar_of_commute_single fun i j hij ↦ ?_
  have hA : single i j (1 : ℂ) - single j i 1 ∈ specialUnitaryLieAlgebra ι := by
    simp [conjTranspose_sub, trace_single_eq_of_ne _ _ _ hij, trace_single_eq_of_ne _ _ _ hij.symm]
  have hB : I • (single i j (1 : ℂ) + single j i 1) ∈ specialUnitaryLieAlgebra ι := by
    simp [conjTranspose_add, single_neg, trace_single_eq_of_ne _ _ _ hij,
      trace_single_eq_of_ne _ _ _ hij.symm, add_comm]
  have hE : single i j (1 : ℂ) =
      (2⁻¹ : ℂ) • ((single i j 1 - single j i 1) - I • I • (single i j 1 + single j i 1)) := by
    rw [smul_smul, I_mul_I]
    module
  dsimp only
  rw [hE]
  exact ((h _ hA).sub_left ((h _ hB).smul_left I)).smul_left _

/-- The imaginary part of the trace on `𝔲(n)`; its kernel is `𝔰𝔲(n)`. -/
private def imTrace : unitaryLieAlgebra ι →ₗ[ℝ] ℝ where
  toFun X := (X : Matrix ι ι ℂ).trace.im
  map_add' X Y := by simp
  map_smul' c X := by simp

private theorem imTrace_apply (X : unitaryLieAlgebra ι) :
    imTrace X = (X : Matrix ι ι ℂ).trace.im :=
  (rfl)

/-- `𝔰𝔲(n)` is the kernel of the imaginary part of the trace on `𝔲(n)`. -/
private def specialUnitaryLieAlgebraEquivKer :
    specialUnitaryLieAlgebra ι ≃ₗ[ℝ] LinearMap.ker (imTrace (ι := ι)) where
  toFun X := ⟨⟨X, specialUnitaryLieAlgebra_le_unitaryLieAlgebra ι X.property⟩,
    by simp [imTrace_apply]⟩
  invFun X := ⟨X.val, conjTranspose_coe_unitaryLieAlgebra X.val,
    Complex.ext (re_trace_coe_unitaryLieAlgebra X.val)
      (by rw [← imTrace_apply]; exact LinearMap.mem_ker.mp X.property)⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

variable (ι) in
/-- **`𝔰𝔲(n)` has real dimension `n² - 1`.** For `n = 0` both sides vanish. -/
theorem finrank_specialUnitaryLieAlgebra :
    finrank ℝ (specialUnitaryLieAlgebra ι) = Fintype.card ι * Fintype.card ι - 1 := by
  rcases isEmpty_or_nonempty ι with hι | ⟨⟨i⟩⟩
  · rw [Fintype.card_eq_zero, finrank_zero_iff.mpr inferInstance]
  have hsurj : Function.Surjective (imTrace (ι := ι)) := fun t ↦ by
    refine ⟨⟨single i i ((t : ℂ) * I), ?_⟩, ?_⟩
    · have h : star ((t : ℂ) * I) = -((t : ℂ) * I) := by simp
      rw [mem_unitaryLieAlgebra_iff, conjTranspose_single, h, single_neg]
    · simp [imTrace_apply]
  have h := LinearMap.finrank_range_add_finrank_ker (imTrace (ι := ι))
  rw [LinearMap.range_eq_top.mpr hsurj, finrank_top, finrank_self, finrank_unitaryLieAlgebra,
    ← specialUnitaryLieAlgebraEquivKer.finrank_eq] at h
  omega

/-! ### The Killing form -/

/-- **The Killing form of `𝔰𝔲(n)`** is `κ(X, Y) = 2 n Re tr(X Y)` for `n = card ι`. -/
theorem killingForm_specialUnitaryLieAlgebra_apply (X Y : specialUnitaryLieAlgebra ι) :
    killingForm ℝ (specialUnitaryLieAlgebra ι) X Y =
      2 * Fintype.card ι * ((X : Matrix ι ι ℂ) * Y).trace.re := by
  rw [LieSubalgebra.killingForm_inclusion_eq (specialUnitaryLieAlgebra_le_unitaryLieAlgebra ι)
      (fun _ hX _ hY ↦ lie_mem_specialUnitaryLieAlgebra_of_mem_unitaryLieAlgebra
        (specialUnitaryLieAlgebra_le_unitaryLieAlgebra ι hX) hY),
    killingForm_unitaryLieAlgebra_apply]
  simp only [LieSubalgebra.coe_inclusion, trace_coe_specialUnitaryLieAlgebra, mul_zero,
    sub_zero]
  norm_cast
  simp [Complex.mul_re]

/-- **The Killing form of `𝔰𝔲(n)` is negative definite**: `κ(X, X) = -2 n Re tr(X Xᴴ) < 0` for
`X ≠ 0`. -/
theorem killingForm_specialUnitaryLieAlgebra_self_neg {X : specialUnitaryLieAlgebra ι}
    (hX : X ≠ 0) : killingForm ℝ (specialUnitaryLieAlgebra ι) X X < 0 := by
  have hne : (X : Matrix ι ι ℂ) ≠ 0 := fun h ↦ hX (Subtype.ext h)
  have hι : Nonempty ι := by
    by_contra h
    exact hne (Matrix.ext fun i ↦ (not_nonempty_iff.mp h).elim i)
  have hpos : 0 < ((X : Matrix ι ι ℂ) * (X : Matrix ι ι ℂ)ᴴ).trace.re := by
    simpa using posDef_reTraceForm ℂ ι ι _ hne
  have hsq : (X : Matrix ι ι ℂ) * X = -((X : Matrix ι ι ℂ) * (X : Matrix ι ι ℂ)ᴴ) := by
    rw [conjTranspose_coe_specialUnitaryLieAlgebra, mul_neg, neg_neg]
  rw [killingForm_specialUnitaryLieAlgebra_apply, hsq, trace_neg, neg_re, mul_neg,
    neg_neg_iff_pos]
  exact mul_pos (by positivity) hpos

/-! ### Block inclusions -/

variable (ι κ) in
/-- The **block inclusion** `𝔰𝔲(m) → 𝔰𝔲(m + k)`, `X ↦ diag(X, 0)`: the matrix `X` placed in the
top-left block of a matrix indexed by `ι ⊕ κ`. As mathematical background, this is the
differential of the group block inclusion `SU(m) → SU(m + k)`, `g ↦ diag(g, 1)`; that group map and
the identification of its differential are not formalized here. -/
def specialUnitaryBlockInclusion :
    specialUnitaryLieAlgebra ι →ₗ⁅ℝ⁆ specialUnitaryLieAlgebra (ι ⊕ κ) where
  toFun X := ⟨fromBlocks₁₁NonUnitalStarAlgHom ℝ ℂ ι κ X, by
    simp [fromBlocks_conjTranspose, fromBlocks_neg, trace_fromBlocks]⟩
  map_add' X Y := Subtype.ext (map_add _ _ _)
  map_smul' r X := Subtype.ext (map_smul _ r _)
  map_lie' {X Y} := Subtype.ext <| by
    simp only [LieSubalgebra.coe_bracket, Ring.lie_def, map_sub, map_mul]

@[simp]
theorem coe_specialUnitaryBlockInclusion_apply (X : specialUnitaryLieAlgebra ι) :
    (specialUnitaryBlockInclusion ι κ X : Matrix (ι ⊕ κ) (ι ⊕ κ) ℂ) = fromBlocks X 0 0 0 :=
  fromBlocks₁₁NonUnitalStarAlgHom_apply (R := ℝ) _

theorem specialUnitaryBlockInclusion_injective :
    Function.Injective (specialUnitaryBlockInclusion ι κ) := fun X Y h ↦ by
  have h' := congrArg
    (fun Z : specialUnitaryLieAlgebra (ι ⊕ κ) ↦ (Z : Matrix (ι ⊕ κ) (ι ⊕ κ) ℂ).toBlocks₁₁) h
  exact Subtype.ext (by simpa using h')

/-- **The Killing form of `𝔰𝔲(m + k)` on the block `𝔰𝔲(m)`** is `2 (m + k) Re tr(X Y)`. -/
theorem killingForm_specialUnitaryBlockInclusion_apply (X Y : specialUnitaryLieAlgebra ι) :
    killingForm ℝ (specialUnitaryLieAlgebra (ι ⊕ κ)) (specialUnitaryBlockInclusion ι κ X)
        (specialUnitaryBlockInclusion ι κ Y) =
      2 * (Fintype.card ι + Fintype.card κ) * ((X : Matrix ι ι ℂ) * Y).trace.re := by
  rw [killingForm_specialUnitaryLieAlgebra_apply]
  simp [fromBlocks_multiply, trace_fromBlocks, Fintype.card_sum]

/-- **The Killing form of `𝔰𝔲(m + k)` restricts to `(m + k) / m` times that of `𝔰𝔲(m)`**: in
the form `m κ_{m+k}(diag(X, 0), diag(Y, 0)) = (m + k) κ_m(X, Y)`. -/
theorem card_smul_killingForm_compl₁₂_specialUnitaryBlockInclusion :
    (Fintype.card ι : ℝ) • (killingForm ℝ (specialUnitaryLieAlgebra (ι ⊕ κ))).compl₁₂
        (specialUnitaryBlockInclusion ι κ).toLinearMap
        (specialUnitaryBlockInclusion ι κ).toLinearMap =
      ((Fintype.card ι + Fintype.card κ : ℕ) : ℝ) • killingForm ℝ (specialUnitaryLieAlgebra ι) := by
  ext X Y
  simp only [LinearMap.smul_apply, LinearMap.compl₁₂_apply, LieHom.coe_toLinearMap, smul_eq_mul]
  rw [killingForm_specialUnitaryBlockInclusion_apply, killingForm_specialUnitaryLieAlgebra_apply]
  push_cast
  ring

/-- **The Cartan three-form of `𝔰𝔲(m + k)` restricts to `(m + k) / m` times that of `𝔰𝔲(m)`**:
for `ω(X, Y, Z) = κ(X, ⁅Y, Z⁆)` built from the Killing forms,
`m ω_{m+k}(diag(X, 0), diag(Y, 0), diag(Z, 0)) = (m + k) ω_m(X, Y, Z)`. In particular the two
forms have the same sign on every triple. -/
theorem card_smul_cartanThreeForm_compLinearMap_specialUnitaryBlockInclusion :
    (Fintype.card ι : ℝ) •
        ((killingForm ℝ (specialUnitaryLieAlgebra (ι ⊕ κ))).cartanThreeForm fun x y z ↦
          LieModule.traceForm_lieInvariant ℝ _ _ x y z).compLinearMap
          (specialUnitaryBlockInclusion ι κ).toLinearMap =
      ((Fintype.card ι + Fintype.card κ : ℕ) : ℝ) •
        (killingForm ℝ (specialUnitaryLieAlgebra ι)).cartanThreeForm fun x y z ↦
          LieModule.traceForm_lieInvariant ℝ _ _ x y z := by
  ext v
  have h := LinearMap.congr_fun₂
    (card_smul_killingForm_compl₁₂_specialUnitaryBlockInclusion (ι := ι) (κ := κ)) (v 0) ⁅v 1, v 2⁆
  simpa using h

/-! ### Conjugation by unitary matrices -/

/-- **Conjugation by a unitary matrix**, `X ↦ U X Uᴴ`, as a Lie algebra endomorphism of `𝔰𝔲(n)`.
It is the adjoint action of `U` on `𝔲(n)` (`TauCeti.unitaryAdjointRepresentation`) restricted to
the trace-free matrices. -/
def specialUnitaryAdjoint (U : unitaryGroup ι ℂ) :
    specialUnitaryLieAlgebra ι →ₗ⁅ℝ⁆ specialUnitaryLieAlgebra ι where
  toFun X := ⟨U * X * star (U : Matrix ι ι ℂ), mem_unitaryLieAlgebra_iff.mp <| by
    simpa using (unitaryAdjointRepresentation ι U
      ⟨X, specialUnitaryLieAlgebra_le_unitaryLieAlgebra ι X.property⟩).property, by
    rw [Matrix.mul_assoc, trace_mul_comm, Matrix.mul_assoc, Unitary.star_mul_self_of_mem U.property,
      Matrix.mul_one, trace_coe_specialUnitaryLieAlgebra]⟩
  map_add' X Y := Subtype.ext (by simp [Matrix.mul_add, Matrix.add_mul])
  map_smul' r X := Subtype.ext (by simp)
  map_lie' {X Y} := Subtype.ext <| by
    simpa using congrArg Subtype.val <| unitaryAdjointRepresentation_lie U
      ⟨X, specialUnitaryLieAlgebra_le_unitaryLieAlgebra ι X.property⟩
      ⟨Y, specialUnitaryLieAlgebra_le_unitaryLieAlgebra ι Y.property⟩

@[simp]
theorem coe_specialUnitaryAdjoint_apply (U : unitaryGroup ι ℂ) (X : specialUnitaryLieAlgebra ι) :
    (specialUnitaryAdjoint U X : Matrix ι ι ℂ) = U * X * star (U : Matrix ι ι ℂ) :=
  (rfl)

/-- Conjugation by the identity is the identity. -/
@[simp]
theorem specialUnitaryAdjoint_one :
    specialUnitaryAdjoint (1 : unitaryGroup ι ℂ) = LieHom.id := by
  ext X : 2
  simp

/-- Conjugation by `U V` is conjugation by `V` followed by conjugation by `U`. -/
theorem specialUnitaryAdjoint_mul (U V : unitaryGroup ι ℂ) :
    specialUnitaryAdjoint (U * V) = (specialUnitaryAdjoint U).comp (specialUnitaryAdjoint V) := by
  ext X : 2
  simp [Matrix.mul_assoc]

variable (ι) in
/-- The **adjoint representation** of `U(n)` on `𝔰𝔲(n)`, by conjugation `Ad_U X = U X Uᴴ`
(`TauCeti.specialUnitaryAdjoint`). Restricted to `SU(n)` it is the adjoint representation of
`SU(n)`. -/
def specialUnitaryAdjointRepresentation :
    Representation ℝ (unitaryGroup ι ℂ) (specialUnitaryLieAlgebra ι) where
  toFun U := (specialUnitaryAdjoint U).toLinearMap
  map_one' := by rw [specialUnitaryAdjoint_one]; rfl
  map_mul' U V := by rw [specialUnitaryAdjoint_mul]; rfl

@[simp]
theorem coe_specialUnitaryAdjointRepresentation_apply (U : unitaryGroup ι ℂ)
    (X : specialUnitaryLieAlgebra ι) :
    (specialUnitaryAdjointRepresentation ι U X : Matrix ι ι ℂ) = U * X * star (U : Matrix ι ι ℂ) :=
  (rfl)

/-- **The adjoint action on `𝔰𝔲(n)` is by Lie algebra automorphisms.** -/
theorem specialUnitaryAdjointRepresentation_lie (U : unitaryGroup ι ℂ)
    (X Y : specialUnitaryLieAlgebra ι) :
    specialUnitaryAdjointRepresentation ι U ⁅X, Y⁆ =
      ⁅specialUnitaryAdjointRepresentation ι U X, specialUnitaryAdjointRepresentation ι U Y⁆ :=
  (specialUnitaryAdjoint U).map_lie X Y

end TauCeti

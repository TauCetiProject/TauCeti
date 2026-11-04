/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.CharP.Invertible
public import Mathlib.Algebra.Lie.Basis.Base
public import TauCeti.Algebra.Lie.NormTwoShell.TrialityD4.Folding

/-!
# Bracket table and generation of the D₄ triality fixed Lie algebra

Folding `CartanMatrix.D 4` along `TauCeti.trialityPermD4` equips the triality-fixed Lie subalgebra
with the Serre comparison homomorphism `TauCeti.D4Triality.g2SerreLift A` from
`Matrix.ToLieAlgebra A CartanMatrix.G₂` over any commutative ring `A`. Unlike the ambient simply
laced shell Lie algebra, the integral fixed Lie subring is not generated over `ℤ` by its folded
Chevalley frame alone: bracketing along the short root string introduces factors of `2` and `3`.

Specifically, uniformly in `negative : Bool` (`false` for positive roots, `true` for negative
roots), the six signed root orbit basis vectors satisfy:

* `⁅x₀, x₁⁆ = x₂` (height `2`, short root `α₁ + α₂`),
* `⁅x₀, x₂⁆ = -2 • x₃` (height `3`, short root `2α₁ + α₂`),
* `⁅x₀, x₃⁆ = -3 • x₄` (height `4`, long root `3α₁ + α₂`),
* `⁅x₁, x₄⁆ = -x₅` and `⁅x₂, x₃⁆ = -3 • x₅` (height `5`, highest long root `3α₁ + 2α₂`),

while `⁅E'₀, F'₀⁆ = H'₀` and `⁅E'₁, F'₁⁆ = H'₁` recover the two invariant Cartan basis vectors.

Combining these iterated Lie-word formulas with `2`- and `3`-divisibility invariants on the high
root coordinates yields a sharp characterization over an arbitrary commutative ring `A`:

* `TauCeti.D4Triality.lieSpan_foldedGenerators_eq_top_iff`: the folded raising and lowering
  generators span the entire `14`-rank triality-fixed Lie subalgebra as an `A`-Lie algebra if and
  only if `IsUnit (2 : A) ∧ IsUnit (3 : A)`.
* `TauCeti.D4Triality.g2SerreLift_surjective_iff`: `g2SerreLift A` is surjective if and only if
  `IsUnit (2 : A) ∧ IsUnit (3 : A)`.
* `TauCeti.D4Triality.lieSpan_foldedGenerators_eq_top` and
  `TauCeti.D4Triality.g2SerreLift_surjective`: typeclass specializations under
  `[Invertible (2 : A)] [Invertible (3 : A)]`, which apply automatically over `ℚ` and every
  characteristic-zero division ring.
* `TauCeti.D4Triality.foldedLieBasis`: packages the folded generators into a `LieAlgebra.Basis`
  with Cartan matrix `TauCeti.DynkinType.G2.cartanMatrix` over any nontrivial commutative ring in
  which `2` and `3` are invertible.

## References

* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Plate IX.
* R. Steinberg, *Lectures on Chevalley Groups*, Yale University, 1967, §10.
* V. G. Kac, *Infinite dimensional Lie algebras*, third edition, §7.9.
-/

public section

open scoped TensorProduct

namespace TauCeti.D4Triality

open _root_.Matrix

/-! ### Structure-constant transfer and ambient bracket coordinates -/

/-- Over any commutative ring `A`, the structure constants of `fixedSubalgebraBaseChangeBasis A`
are the integer casts of the integral structure constants of `fixedBasis`. -/
@[simp]
theorem fixedSubalgebraBaseChangeBasis_repr_lie (A : Type*) [CommRing A]
    (i j l : Fin 2 ⊕ (Bool × Fin 6)) :
    (fixedSubalgebraBaseChangeBasis A).repr
        ⁅fixedSubalgebraBaseChangeBasis A i, fixedSubalgebraBaseChangeBasis A j⁆ l =
      (fixedBasis.repr ⁅fixedBasis i, fixedBasis j⁆ l : A) := by
  rw [fixedSubalgebraBaseChangeBasis_apply, fixedSubalgebraBaseChangeBasis_apply,
    ← (fixedSubalgebraBaseChangeLieEquiv A).map_lie, LieAlgebra.ExtendScalars.bracket_tmul,
    one_mul, fixedSubalgebraBaseChangeBasis_repr_tmul, zsmul_one]

private theorem basis_repr_lie_invariantRoot_inl (neg₁ neg₂ : Bool) (o₁ o₂ : Fin 6)
    (k : Fin 4) :
    (ShellLieAlgebra.basis (CartanMatrix.D 4)).repr
        ⁅invariantRoot neg₁ o₁, invariantRoot neg₂ o₂⁆ (.inl k) =
      ∑ i : Fin 12 with orbit i = o₁, ∑ j : Fin 12 with orbit j = o₂,
        orbitCoeff i * (orbitCoeff j *
          if (root neg₁ i : Fin 4 → ℤ) + root neg₂ j = 0 then
            ((-1 : ℤ) ^
              (∑ r : Fin 4, ∑ s : Fin 4,
                if s < r then
                  (root neg₁ i : Fin 4 → ℤ) r * CartanMatrix.D 4 r s *
                    (root neg₂ j : Fin 4 → ℤ) s
                else 0).natAbs) *
              (root neg₁ i : Fin 4 → ℤ) k
          else 0) := by
  rw [invariantRoot_eq_sum neg₁ o₁, ← ShellLieAlgebra.bracketBilin_apply_apply,
    map_sum, LinearMap.sum_apply, map_sum, Finsupp.finsetSum_apply]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [invariantRoot_eq_sum neg₂ o₂]
  simp only [map_zsmul, LinearMap.smul_apply, map_sum, ShellLieAlgebra.bracketBilin_apply_apply,
    ShellLieAlgebra.root_lie_root, Finsupp.finsetSum_apply, Finsupp.smul_apply, smul_eq_mul,
    ShellLieAlgebra.basis_repr_rootBracket_inl, orderedSignForm_apply]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [mul_left_comm]
  congr 4
  exact Int.coe_negOnePow ℤ _

private theorem basis_repr_lie_invariantRoot_inr (neg₁ neg₂ : Bool) (o₁ o₂ : Fin 6)
    (c : (CartanMatrix.D 4).normTwoShell) :
    (ShellLieAlgebra.basis (CartanMatrix.D 4)).repr
        ⁅invariantRoot neg₁ o₁, invariantRoot neg₂ o₂⁆ (.inr c) =
      ∑ i : Fin 12 with orbit i = o₁, ∑ j : Fin 12 with orbit j = o₂,
        orbitCoeff i * (orbitCoeff j *
          if (root neg₁ i : Fin 4 → ℤ) + root neg₂ j = c then
            (-1 : ℤ) ^
              (∑ r : Fin 4, ∑ s : Fin 4,
                if s < r then
                  (root neg₁ i : Fin 4 → ℤ) r * CartanMatrix.D 4 r s *
                    (root neg₂ j : Fin 4 → ℤ) s
                else 0).natAbs
          else 0) := by
  rw [invariantRoot_eq_sum neg₁ o₁, ← ShellLieAlgebra.bracketBilin_apply_apply,
    map_sum, LinearMap.sum_apply, map_sum, Finsupp.finsetSum_apply]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [invariantRoot_eq_sum neg₂ o₂]
  simp only [map_zsmul, LinearMap.smul_apply, map_sum, ShellLieAlgebra.bracketBilin_apply_apply,
    ShellLieAlgebra.root_lie_root, Finsupp.finsetSum_apply, Finsupp.smul_apply, smul_eq_mul,
    ShellLieAlgebra.basis_repr_rootBracket_inr, orderedSignForm_apply]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [mul_left_comm]
  congr 3
  exact Int.coe_negOnePow ℤ _

/-! ### Integral Chevalley-like bracket relations along the six root orbits -/

/-- Bracketing the short simple orbit `0` with the long simple orbit `1` produces the height-`2`
short orbit `2` with coefficient `1`. -/
@[simp]
theorem lie_fixedBasis_zero_one (negative : Bool) :
    ⁅fixedBasis (.inr (negative, 0)), fixedBasis (.inr (negative, 1))⁆ =
      fixedBasis (.inr (negative, 2)) := by
  refine fixedBasis.repr.injective (Finsupp.ext fun idx ↦ ?_)
  rcases idx with k | ⟨neg', o⟩
  · rw [fixedBasis_repr_inl, LieSubalgebra.coe_bracket, coe_fixedBasis_inr, coe_fixedBasis_inr,
      basis_repr_lie_invariantRoot_inl, Module.Basis.repr_self, Finsupp.single_apply]
    simp only [coe_root, reduceCtorEq, ↓reduceIte]
    cases negative <;> fin_cases k <;> decide
  · rw [fixedBasis_repr_inr, LieSubalgebra.coe_bracket, coe_fixedBasis_inr, coe_fixedBasis_inr,
      basis_repr_lie_invariantRoot_inr, Module.Basis.repr_self, Finsupp.single_apply]
    simp only [coe_root, Sum.inr.injEq, Prod.mk.injEq]
    cases negative <;> cases neg' <;> fin_cases o <;> decide

@[simp]
theorem lie_invariantRoot_zero_one (negative : Bool) :
    ⁅invariantRoot negative 0, invariantRoot negative 1⁆ = invariantRoot negative 2 := by
  simpa only [LieSubalgebra.coe_bracket, coe_fixedBasis_inr] using
    congrArg Subtype.val (lie_fixedBasis_zero_one negative)

/-- Bracketing the short simple orbit `0` with the height-`2` short orbit `2` produces `-2` times
the height-`3` short orbit `3`. -/
@[simp]
theorem lie_fixedBasis_zero_two (negative : Bool) :
    ⁅fixedBasis (.inr (negative, 0)), fixedBasis (.inr (negative, 2))⁆ =
      -(2 : ℤ) • fixedBasis (.inr (negative, 3)) := by
  refine fixedBasis.repr.injective (Finsupp.ext fun idx ↦ ?_)
  rcases idx with k | ⟨neg', o⟩
  · rw [fixedBasis_repr_inl, LieSubalgebra.coe_bracket, coe_fixedBasis_inr, coe_fixedBasis_inr,
      basis_repr_lie_invariantRoot_inl, map_zsmul, Module.Basis.repr_self]
    simp only [coe_root, Finsupp.coe_smul, Pi.smul_apply, Finsupp.single_apply, reduceCtorEq,
      ↓reduceIte, smul_zero]
    cases negative <;> fin_cases k <;> decide
  · rw [fixedBasis_repr_inr, LieSubalgebra.coe_bracket, coe_fixedBasis_inr, coe_fixedBasis_inr,
      basis_repr_lie_invariantRoot_inr, map_zsmul, Module.Basis.repr_self]
    simp only [coe_root, Finsupp.coe_smul, Pi.smul_apply, Finsupp.single_apply, Sum.inr.injEq,
      Prod.mk.injEq, smul_eq_mul]
    cases negative <;> cases neg' <;> fin_cases o <;> decide

@[simp]
theorem lie_invariantRoot_zero_two (negative : Bool) :
    ⁅invariantRoot negative 0, invariantRoot negative 2⁆ =
      -(2 : ℤ) • invariantRoot negative 3 := by
  simpa only [LieSubalgebra.coe_bracket, SetLike.val_smul, coe_fixedBasis_inr] using
    congrArg Subtype.val (lie_fixedBasis_zero_two negative)

/-- Bracketing the short simple orbit `0` with the height-`3` short orbit `3` produces `-3` times
the height-`4` long orbit `4`. -/
@[simp]
theorem lie_fixedBasis_zero_three (negative : Bool) :
    ⁅fixedBasis (.inr (negative, 0)), fixedBasis (.inr (negative, 3))⁆ =
      -(3 : ℤ) • fixedBasis (.inr (negative, 4)) := by
  refine fixedBasis.repr.injective (Finsupp.ext fun idx ↦ ?_)
  rcases idx with k | ⟨neg', o⟩
  · rw [fixedBasis_repr_inl, LieSubalgebra.coe_bracket, coe_fixedBasis_inr, coe_fixedBasis_inr,
      basis_repr_lie_invariantRoot_inl, map_zsmul, Module.Basis.repr_self]
    simp only [coe_root, Finsupp.coe_smul, Pi.smul_apply, Finsupp.single_apply, reduceCtorEq,
      ↓reduceIte, smul_zero]
    cases negative <;> fin_cases k <;> decide
  · rw [fixedBasis_repr_inr, LieSubalgebra.coe_bracket, coe_fixedBasis_inr, coe_fixedBasis_inr,
      basis_repr_lie_invariantRoot_inr, map_zsmul, Module.Basis.repr_self]
    simp only [coe_root, Finsupp.coe_smul, Pi.smul_apply, Finsupp.single_apply, Sum.inr.injEq,
      Prod.mk.injEq, smul_eq_mul]
    cases negative <;> cases neg' <;> fin_cases o <;> decide

@[simp]
theorem lie_invariantRoot_zero_three (negative : Bool) :
    ⁅invariantRoot negative 0, invariantRoot negative 3⁆ =
      -(3 : ℤ) • invariantRoot negative 4 := by
  simpa only [LieSubalgebra.coe_bracket, SetLike.val_smul, coe_fixedBasis_inr] using
    congrArg Subtype.val (lie_fixedBasis_zero_three negative)

/-- Bracketing the long simple orbit `1` with the height-`4` long orbit `4` produces `-1` times
the highest long orbit `5`. -/
@[simp]
theorem lie_fixedBasis_one_four (negative : Bool) :
    ⁅fixedBasis (.inr (negative, 1)), fixedBasis (.inr (negative, 4))⁆ =
      -fixedBasis (.inr (negative, 5)) := by
  refine fixedBasis.repr.injective (Finsupp.ext fun idx ↦ ?_)
  rcases idx with k | ⟨neg', o⟩
  · rw [fixedBasis_repr_inl, LieSubalgebra.coe_bracket, coe_fixedBasis_inr, coe_fixedBasis_inr,
      basis_repr_lie_invariantRoot_inl, map_neg, Module.Basis.repr_self]
    simp only [coe_root, Finsupp.coe_neg, Pi.neg_apply, Finsupp.single_apply, reduceCtorEq,
      ↓reduceIte, neg_zero]
    cases negative <;> fin_cases k <;> decide
  · rw [fixedBasis_repr_inr, LieSubalgebra.coe_bracket, coe_fixedBasis_inr, coe_fixedBasis_inr,
      basis_repr_lie_invariantRoot_inr, map_neg, Module.Basis.repr_self]
    simp only [coe_root, Finsupp.coe_neg, Pi.neg_apply, Finsupp.single_apply, Sum.inr.injEq,
      Prod.mk.injEq]
    cases negative <;> cases neg' <;> fin_cases o <;> decide

@[simp]
theorem lie_invariantRoot_one_four (negative : Bool) :
    ⁅invariantRoot negative 1, invariantRoot negative 4⁆ = -invariantRoot negative 5 := by
  simpa only [LieSubalgebra.coe_bracket, NegMemClass.coe_neg, coe_fixedBasis_inr] using
    congrArg Subtype.val (lie_fixedBasis_one_four negative)

/-- Bracketing the two intermediate short orbits `2` and `3` produces `-3` times the highest long
orbit `5` (the extraspecial `(2, 3)` pair of `G₂`). -/
@[simp]
theorem lie_fixedBasis_two_three (negative : Bool) :
    ⁅fixedBasis (.inr (negative, 2)), fixedBasis (.inr (negative, 3))⁆ =
      -(3 : ℤ) • fixedBasis (.inr (negative, 5)) := by
  refine fixedBasis.repr.injective (Finsupp.ext fun idx ↦ ?_)
  rcases idx with k | ⟨neg', o⟩
  · rw [fixedBasis_repr_inl, LieSubalgebra.coe_bracket, coe_fixedBasis_inr, coe_fixedBasis_inr,
      basis_repr_lie_invariantRoot_inl, map_zsmul, Module.Basis.repr_self]
    simp only [coe_root, Finsupp.coe_smul, Pi.smul_apply, Finsupp.single_apply, reduceCtorEq,
      ↓reduceIte, smul_zero]
    cases negative <;> fin_cases k <;> decide
  · rw [fixedBasis_repr_inr, LieSubalgebra.coe_bracket, coe_fixedBasis_inr, coe_fixedBasis_inr,
      basis_repr_lie_invariantRoot_inr, map_zsmul, Module.Basis.repr_self]
    simp only [coe_root, Finsupp.coe_smul, Pi.smul_apply, Finsupp.single_apply, Sum.inr.injEq,
      Prod.mk.injEq, smul_eq_mul]
    cases negative <;> cases neg' <;> fin_cases o <;> decide

@[simp]
theorem lie_invariantRoot_two_three (negative : Bool) :
    ⁅invariantRoot negative 2, invariantRoot negative 3⁆ =
      -(3 : ℤ) • invariantRoot negative 5 := by
  simpa only [LieSubalgebra.coe_bracket, SetLike.val_smul, coe_fixedBasis_inr] using
    congrArg Subtype.val (lie_fixedBasis_two_three negative)

/-- Opposite short simple orbits bracket to `invariantCartan 0`. -/
@[simp]
theorem lie_fixedBasis_false_true_zero :
    ⁅fixedBasis (.inr (false, 0)), fixedBasis (.inr (true, 0))⁆ = fixedBasis (.inl 0) :=
  isSerreSystem_g2Fixed.lie_E_F_self 0

@[simp]
theorem lie_invariantRoot_false_true_zero :
    ⁅invariantRoot false 0, invariantRoot true 0⁆ = invariantCartan 0 :=
  isSerreSystem_g2.lie_E_F_self 0

/-- Opposite long simple orbits bracket to `invariantCartan 1`. -/
@[simp]
theorem lie_fixedBasis_false_true_one :
    ⁅fixedBasis (.inr (false, 1)), fixedBasis (.inr (true, 1))⁆ = fixedBasis (.inl 1) :=
  isSerreSystem_g2Fixed.lie_E_F_self 1

@[simp]
theorem lie_invariantRoot_false_true_one :
    ⁅invariantRoot false 1, invariantRoot true 1⁆ = invariantCartan 1 :=
  isSerreSystem_g2.lie_E_F_self 1

/-- Explicit iterated Lie-word expression for twice the height-`3` short orbit vector. -/
theorem two_smul_invariantRoot_three (negative : Bool) :
    (2 : ℤ) • invariantRoot negative 3 =
      -⁅invariantRoot negative 0, ⁅invariantRoot negative 0, invariantRoot negative 1⁆⁆ := by
  rw [lie_invariantRoot_zero_one, lie_invariantRoot_zero_two, neg_smul, neg_neg]

/-- Explicit iterated Lie-word expression for six times the height-`4` long orbit vector. -/
theorem six_smul_invariantRoot_four (negative : Bool) :
    (6 : ℤ) • invariantRoot negative 4 =
      ⁅invariantRoot negative 0,
        ⁅invariantRoot negative 0, ⁅invariantRoot negative 0, invariantRoot negative 1⁆⁆⁆ := by
  rw [lie_invariantRoot_zero_one, lie_invariantRoot_zero_two, neg_smul, lie_neg, lie_zsmul,
    lie_invariantRoot_zero_three, neg_smul, smul_neg, neg_neg, smul_smul]
  norm_num

/-- Explicit iterated Lie-word expression for six times the highest long orbit vector. -/
theorem six_smul_invariantRoot_five (negative : Bool) :
    (6 : ℤ) • invariantRoot negative 5 =
      -⁅invariantRoot negative 1,
        ⁅invariantRoot negative 0,
          ⁅invariantRoot negative 0, ⁅invariantRoot negative 0, invariantRoot negative 1⁆⁆⁆⁆ := by
  rw [← six_smul_invariantRoot_four, lie_zsmul, lie_invariantRoot_one_four, smul_neg, neg_neg]

/-! ### Divisibility obstructions and sharp generation over arbitrary commutative rings -/

private theorem lieSpan_le_submodule_of_lie_mem {R L : Type*} [CommRing R] [LieRing L]
    [LieAlgebra R L] {s : Set L} (M : Submodule R L) (hs : s ⊆ M)
    (hlie : ∀ g ∈ s, ∀ y ∈ M, ⁅g, y⁆ ∈ M) :
    (LieSubalgebra.lieSpan R L s).toSubmodule ≤ M := by
  let N : LieSubalgebra R L :=
    { carrier := {z | z ∈ M ∧ ∀ y ∈ M, ⁅z, y⁆ ∈ M}
      zero_mem' := ⟨M.zero_mem, fun _ _ ↦ by simp⟩
      add_mem' := fun {x y} hx hy ↦ ⟨M.add_mem hx.1 hy.1, fun z hz ↦ by
        rw [add_lie]
        exact M.add_mem (hx.2 z hz) (hy.2 z hz)⟩
      smul_mem' := fun c {x} hx ↦ ⟨M.smul_mem c hx.1, fun z hz ↦ by
        rw [smul_lie]
        exact M.smul_mem c (hx.2 z hz)⟩
      lie_mem' := fun {x y} hx hy ↦ ⟨hx.2 y hy.1, fun z hz ↦ by
        rw [lie_lie]
        exact M.sub_mem (hx.2 _ (hy.2 z hz)) (hy.2 _ (hx.2 z hz))⟩ }
  have hle : LieSubalgebra.lieSpan R L s ≤ N :=
    LieSubalgebra.lieSpan_le.mpr fun g hg ↦ ⟨hs hg, hlie g hg⟩
  exact fun x hx ↦ (hle hx).1

private theorem fixedBasis_repr_lie_gen_inl_inr_eq_zero (neg_g : Bool) (k k' : Fin 2)
    (o : Fin 6) (ho : 2 ≤ o.val) :
    fixedBasis.repr
        ⁅fixedBasis (.inr (neg_g, k.castLE (by decide))), fixedBasis (.inl k')⁆
        (.inr (false, o)) = 0 := by
  have hne : k.castLE (by decide) ≠ o := by fin_cases k <;> simp <;> omega
  rw [← lie_skew]
  cases neg_g
  · rw [isSerreSystem_g2Fixed.lie_H_E k' k, map_neg, map_zsmul, Module.Basis.repr_self]
    simp [hne]
  · rw [isSerreSystem_g2Fixed.lie_H_F k' k, neg_neg, map_zsmul, Module.Basis.repr_self]
    simp

private theorem dvd_two_fixedBasis_repr_lie_gen (neg_g : Bool) (k : Fin 2)
    (idx : Fin 2 ⊕ (Bool × Fin 6)) (o : Fin 6) (ho : 3 ≤ o.val)
    (hidx : ∀ o' : Fin 6, 3 ≤ o'.val → idx ≠ .inr (false, o')) :
    (2 : ℤ) ∣ fixedBasis.repr
        ⁅fixedBasis (.inr (neg_g, k.castLE (by decide))), fixedBasis idx⁆
        (.inr (false, o)) := by
  rcases idx with k' | ⟨neg', o'⟩
  · rw [fixedBasis_repr_lie_gen_inl_inr_eq_zero neg_g k k' o (by omega)]
    exact dvd_zero 2
  · have h' : neg' = true ∨ o'.val < 3 := by
      cases neg'
      · exact Or.inr (Nat.lt_of_not_ge fun hge ↦ hidx o' hge rfl)
      · exact Or.inl rfl
    clear hidx
    rw [fixedBasis_repr_inr, LieSubalgebra.coe_bracket, coe_fixedBasis_inr, coe_fixedBasis_inr,
      basis_repr_lie_invariantRoot_inr]
    simp only [coe_root]
    cases neg_g <;> cases neg' <;> fin_cases k <;> fin_cases o' <;> fin_cases o <;>
      revert ho h' <;> decide

private theorem dvd_three_fixedBasis_repr_lie_gen (neg_g : Bool) (k : Fin 2)
    (idx : Fin 2 ⊕ (Bool × Fin 6)) (o : Fin 6) (ho : 4 ≤ o.val)
    (hidx : ∀ o' : Fin 6, 4 ≤ o'.val → idx ≠ .inr (false, o')) :
    (3 : ℤ) ∣ fixedBasis.repr
        ⁅fixedBasis (.inr (neg_g, k.castLE (by decide))), fixedBasis idx⁆
        (.inr (false, o)) := by
  rcases idx with k' | ⟨neg', o'⟩
  · rw [fixedBasis_repr_lie_gen_inl_inr_eq_zero neg_g k k' o (by omega)]
    exact dvd_zero 3
  · have h' : neg' = true ∨ o'.val < 4 := by
      cases neg'
      · exact Or.inr (Nat.lt_of_not_ge fun hge ↦ hidx o' hge rfl)
      · exact Or.inl rfl
    clear hidx
    rw [fixedBasis_repr_inr, LieSubalgebra.coe_bracket, coe_fixedBasis_inr, coe_fixedBasis_inr,
      basis_repr_lie_invariantRoot_inr]
    simp only [coe_root]
    cases neg_g <;> cases neg' <;> fin_cases k <;> fin_cases o' <;> fin_cases o <;>
      revert ho h' <;> decide

private def coordDvdSubmodule (A : Type*) [CommRing A] (n cut : ℕ) :
    Submodule A (LieEquiv.baseChange A trialityLieEquiv).toLieHom.fixedSubalgebra where
  carrier := {y | ∀ o : Fin 6, cut ≤ o.val →
    (n : A) ∣ (fixedSubalgebraBaseChangeBasis A).repr y (.inr (false, o))}
  zero_mem' _ _ := by simp
  add_mem' {x y} hx hy o ho := by
    rw [map_add, Finsupp.add_apply]
    exact dvd_add (hx o ho) (hy o ho)
  smul_mem' c {x} hx o ho := by
    rw [map_smul, Finsupp.smul_apply, smul_eq_mul]
    exact dvd_mul_of_dvd_right (hx o ho) c

private theorem lieSpan_le_coordDvdSubmodule (A : Type*) [CommRing A] {n cut : ℕ}
    (hcut : 2 ≤ cut)
    (hdvd : ∀ (neg_g : Bool) (k : Fin 2) (idx : Fin 2 ⊕ (Bool × Fin 6)) (o : Fin 6),
      cut ≤ o.val → (∀ o' : Fin 6, cut ≤ o'.val → idx ≠ .inr (false, o')) →
        (n : ℤ) ∣ fixedBasis.repr
          ⁅fixedBasis (.inr (neg_g, k.castLE (by decide))), fixedBasis idx⁆
          (.inr (false, o))) :
    (LieSubalgebra.lieSpan A (LieEquiv.baseChange A trialityLieEquiv).toLieHom.fixedSubalgebra
      (Set.range (fun k : Fin 2 ↦
          fixedSubalgebraBaseChangeBasis A (.inr (false, k.castLE (by decide)))) ∪
        Set.range (fun k : Fin 2 ↦
          fixedSubalgebraBaseChangeBasis A (.inr (true, k.castLE (by decide)))))).toSubmodule ≤
      coordDvdSubmodule A n cut := by
  let b := fixedSubalgebraBaseChangeBasis A
  refine lieSpan_le_submodule_of_lie_mem (coordDvdSubmodule A n cut) ?_ ?_
  · rintro _ (⟨k, rfl⟩ | ⟨k, rfl⟩) o ho
    · have hne : (k.castLE (by decide) : Fin 6) ≠ o := by fin_cases k <;> simp <;> omega
      rw [Module.Basis.repr_self]
      simp [hne]
    · rw [Module.Basis.repr_self]
      simp
  · have hgen : ∀ (neg_g : Bool) (k : Fin 2) (y : _), y ∈ coordDvdSubmodule A n cut →
        ⁅b (.inr (neg_g, k.castLE (by decide))), y⁆ ∈ coordDvdSubmodule A n cut := by
      intro neg_g k y hy o ho
      change (n : A) ∣ b.repr ⁅b (.inr (neg_g, k.castLE (by decide))), y⁆ (.inr (false, o))
      rw [← b.sum_repr y, lie_sum, map_sum, Finsupp.finsetSum_apply]
      refine Finset.dvd_sum fun idx _ ↦ ?_
      rw [lie_smul, map_smul, Finsupp.smul_apply, smul_eq_mul,
        fixedSubalgebraBaseChangeBasis_repr_lie]
      by_cases hidx : ∃ o' : Fin 6, cut ≤ o'.val ∧ idx = .inr (false, o')
      · rcases hidx with ⟨o', ho', rfl⟩
        exact dvd_mul_of_dvd_left (hy o' ho') _
      · have hidx' : ∀ o' : Fin 6, cut ≤ o'.val → idx ≠ .inr (false, o') :=
          fun o' ho' heq ↦ hidx ⟨o', ho', heq⟩
        obtain ⟨q, hq⟩ := hdvd neg_g k idx o ho hidx'
        rw [hq, Int.cast_mul, Int.cast_natCast]
        exact dvd_mul_of_dvd_right (dvd_mul_right (n : A) (q : A)) _
    rintro _ (⟨k, rfl⟩ | ⟨k, rfl⟩) y hy
    · exact hgen false k y hy
    · exact hgen true k y hy

private theorem lie_fixedSubalgebraBaseChangeBasis_of_lie_fixedBasis (A : Type*) [CommRing A]
    {i j m : Fin 2 ⊕ (Bool × Fin 6)} {c : ℤ}
    (h : ⁅fixedBasis i, fixedBasis j⁆ = c • fixedBasis m) :
    ⁅fixedSubalgebraBaseChangeBasis A i, fixedSubalgebraBaseChangeBasis A j⁆ =
      (c : A) • fixedSubalgebraBaseChangeBasis A m := by
  refine (fixedSubalgebraBaseChangeBasis A).repr.injective (Finsupp.ext fun l ↦ ?_)
  simp [h, Finsupp.single_apply]

private theorem mem_lieSpan_foldedGenerators_inr (A : Type*) [CommRing A]
    [Invertible (2 : A)] [Invertible (3 : A)] (neg : Bool) (o : Fin 6) :
    fixedSubalgebraBaseChangeBasis A (.inr (neg, o)) ∈
      LieSubalgebra.lieSpan A (LieEquiv.baseChange A trialityLieEquiv).toLieHom.fixedSubalgebra
        (Set.range (fun k : Fin 2 ↦
            fixedSubalgebraBaseChangeBasis A (.inr (false, k.castLE (by decide)))) ∪
          Set.range (fun k : Fin 2 ↦
            fixedSubalgebraBaseChangeBasis A (.inr (true, k.castLE (by decide))))) := by
  let b := fixedSubalgebraBaseChangeBasis A
  set K := LieSubalgebra.lieSpan A
    (LieEquiv.baseChange A trialityLieEquiv).toLieHom.fixedSubalgebra
    (Set.range (fun k : Fin 2 ↦ b (.inr (false, k.castLE (by decide)))) ∪
      Set.range (fun k : Fin 2 ↦ b (.inr (true, k.castLE (by decide)))))
  have h0 : b (.inr (neg, 0)) ∈ K :=
    LieSubalgebra.subset_lieSpan (by cases neg; exacts [Or.inl ⟨0, rfl⟩, Or.inr ⟨0, rfl⟩])
  have h1 : b (.inr (neg, 1)) ∈ K :=
    LieSubalgebra.subset_lieSpan (by cases neg; exacts [Or.inl ⟨1, rfl⟩, Or.inr ⟨1, rfl⟩])
  have h2 : b (.inr (neg, 2)) ∈ K := by
    have hlie := lie_fixedSubalgebraBaseChangeBasis_of_lie_fixedBasis A
      ((lie_fixedBasis_zero_one neg).trans (one_smul ℤ _).symm)
    rw [Int.cast_one, one_smul] at hlie
    exact hlie ▸ K.lie_mem h0 h1
  have h3 : b (.inr (neg, 3)) ∈ K := by
    have hlie := lie_fixedSubalgebraBaseChangeBasis_of_lie_fixedBasis A
      (lie_fixedBasis_zero_two neg)
    rw [Int.cast_neg, Int.cast_ofNat] at hlie
    have hm := K.smul_mem (-⅟(2 : A)) (hlie ▸ K.lie_mem h0 h2)
    rwa [smul_smul, neg_mul_neg, invOf_mul_self, one_smul] at hm
  have h4 : b (.inr (neg, 4)) ∈ K := by
    have hlie := lie_fixedSubalgebraBaseChangeBasis_of_lie_fixedBasis A
      (lie_fixedBasis_zero_three neg)
    rw [Int.cast_neg, Int.cast_ofNat] at hlie
    have hm := K.smul_mem (-⅟(3 : A)) (hlie ▸ K.lie_mem h0 h3)
    rwa [smul_smul, neg_mul_neg, invOf_mul_self, one_smul] at hm
  have h5 : b (.inr (neg, 5)) ∈ K := by
    have hlie := lie_fixedSubalgebraBaseChangeBasis_of_lie_fixedBasis A
      ((lie_fixedBasis_one_four neg).trans (neg_one_smul ℤ _).symm)
    rw [Int.cast_neg, Int.cast_one, neg_one_smul] at hlie
    have hm : -b (.inr (neg, 5)) ∈ K := hlie ▸ K.lie_mem h1 h4
    simpa using K.neg_mem hm
  fin_cases o
  exacts [h0, h1, h2, h3, h4, h5]

private theorem lieSpan_foldedGenerators_eq_top_of_invertible (A : Type*) [CommRing A]
    [Invertible (2 : A)] [Invertible (3 : A)] :
    LieSubalgebra.lieSpan A (LieEquiv.baseChange A trialityLieEquiv).toLieHom.fixedSubalgebra
      (Set.range (fun k : Fin 2 ↦
          fixedSubalgebraBaseChangeBasis A (.inr (false, k.castLE (by decide)))) ∪
        Set.range (fun k : Fin 2 ↦
          fixedSubalgebraBaseChangeBasis A (.inr (true, k.castLE (by decide))))) = ⊤ := by
  let b := fixedSubalgebraBaseChangeBasis A
  rw [← LieSubalgebra.toSubmodule_eq_top, eq_top_iff, ← b.span_eq, Submodule.span_le]
  rintro _ ⟨k | ⟨neg, o⟩, rfl⟩
  · rw [SetLike.mem_coe, ← (isSerreSystem_g2FixedBaseChange A).lie_E_F_self k]
    exact LieSubalgebra.lie_mem _
      (mem_lieSpan_foldedGenerators_inr A false _)
      (mem_lieSpan_foldedGenerators_inr A true _)
  · exact mem_lieSpan_foldedGenerators_inr A neg o

/-- **Sharp Lie-generation theorem for the `D₄` triality fixed Lie subalgebra.**
Over any commutative ring `A`, the four folded `G₂` simple root vectors generate the entire
`14`-rank triality-fixed Lie subalgebra if and only if both `2` and `3` are units in `A`. -/
theorem lieSpan_foldedGenerators_eq_top_iff (A : Type*) [CommRing A] :
    LieSubalgebra.lieSpan A (LieEquiv.baseChange A trialityLieEquiv).toLieHom.fixedSubalgebra
        (Set.range (fun k : Fin 2 ↦
            fixedSubalgebraBaseChangeBasis A (.inr (false, k.castLE (by decide)))) ∪
          Set.range (fun k : Fin 2 ↦
            fixedSubalgebraBaseChangeBasis A (.inr (true, k.castLE (by decide))))) = ⊤ ↔
      IsUnit (2 : A) ∧ IsUnit (3 : A) := by
  constructor
  · intro htop
    constructor
    · have hle := lieSpan_le_coordDvdSubmodule A (n := 2) (cut := 3) (by decide)
        dvd_two_fixedBasis_repr_lie_gen
      rw [htop] at hle
      have hmem : fixedSubalgebraBaseChangeBasis A (.inr (false, 3)) ∈
          coordDvdSubmodule A 2 3 := hle trivial
      have hdvd := hmem 3 (by decide)
      rw [Module.Basis.repr_self, Finsupp.single_eq_same] at hdvd
      exact isUnit_iff_dvd_one.mpr (by simpa using hdvd)
    · have hle := lieSpan_le_coordDvdSubmodule A (n := 3) (cut := 4) (by decide)
        dvd_three_fixedBasis_repr_lie_gen
      rw [htop] at hle
      have hmem : fixedSubalgebraBaseChangeBasis A (.inr (false, 4)) ∈
          coordDvdSubmodule A 3 4 := hle trivial
      have hdvd := hmem 4 (by decide)
      rw [Module.Basis.repr_self, Finsupp.single_eq_same] at hdvd
      exact isUnit_iff_dvd_one.mpr (by simpa using hdvd)
  · rintro ⟨h2, h3⟩
    have := h2.nonempty_invertible.some
    have := h3.nonempty_invertible.some
    exact lieSpan_foldedGenerators_eq_top_of_invertible A

/-- When `2` and `3` are invertible in `A` (in particular over `ℚ` or any characteristic-zero
division ring), the folded `G₂` simple root vectors generate the entire triality-fixed Lie
subalgebra. -/
theorem lieSpan_foldedGenerators_eq_top (A : Type*) [CommRing A]
    [Invertible (2 : A)] [Invertible (3 : A)] :
    LieSubalgebra.lieSpan A (LieEquiv.baseChange A trialityLieEquiv).toLieHom.fixedSubalgebra
      (Set.range (fun k : Fin 2 ↦
          fixedSubalgebraBaseChangeBasis A (.inr (false, k.castLE (by decide)))) ∪
        Set.range (fun k : Fin 2 ↦
          fixedSubalgebraBaseChangeBasis A (.inr (true, k.castLE (by decide))))) = ⊤ :=
  lieSpan_foldedGenerators_eq_top_of_invertible A

/-- The image of `g2SerreLift A` is always the `A`-Lie subalgebra generated by the four folded
simple root vectors. -/
theorem range_g2SerreLift (A : Type*) [CommRing A] :
    (g2SerreLift A).range =
      LieSubalgebra.lieSpan A (LieEquiv.baseChange A trialityLieEquiv).toLieHom.fixedSubalgebra
        (Set.range (fun k : Fin 2 ↦
            fixedSubalgebraBaseChangeBasis A (.inr (false, k.castLE (by decide)))) ∪
          Set.range (fun k : Fin 2 ↦
            fixedSubalgebraBaseChangeBasis A (.inr (true, k.castLE (by decide))))) := by
  rw [LieHom.range_eq_map, ← lieSpan_serreE_union_serreF_eq_top A CartanMatrix.G₂,
    LieSubalgebra.map_lieSpan]
  simp [Set.image_union, ← Set.range_comp, Function.comp_def]

/-- **Sharp surjectivity characterization for `g2SerreLift A`.**
Over any commutative ring `A`, the folded `G₂` Serre comparison homomorphism `g2SerreLift A` onto
the `D₄` triality fixed Lie subalgebra is surjective if and only if both `2` and `3` are units in
`A`. -/
theorem g2SerreLift_surjective_iff (A : Type*) [CommRing A] :
    Function.Surjective (g2SerreLift A) ↔ IsUnit (2 : A) ∧ IsUnit (3 : A) := by
  rw [← LieHom.range_eq_top, range_g2SerreLift, lieSpan_foldedGenerators_eq_top_iff]

/-- When `2` and `3` are invertible in `A` (in particular over `ℚ` or any characteristic-zero
division ring), `g2SerreLift A` maps `Matrix.ToLieAlgebra A CartanMatrix.G₂` surjectively onto the
triality-fixed Lie subalgebra. -/
theorem g2SerreLift_surjective (A : Type*) [CommRing A]
    [Invertible (2 : A)] [Invertible (3 : A)] :
    Function.Surjective (g2SerreLift A) :=
  (g2SerreLift_surjective_iff A).mpr ⟨isUnit_of_invertible _, isUnit_of_invertible _⟩

/-! ### Packaging as a `LieAlgebra.Basis` of type `G₂` -/

/-- The `A`-Lie subalgebra of the `D₄` triality fixed Lie subalgebra generated by the two folded
Cartan basis elements. -/
noncomputable def foldedCartanSubalgebra (A : Type*) [CommRing A] :
    LieSubalgebra A (LieEquiv.baseChange A trialityLieEquiv).toLieHom.fixedSubalgebra :=
  LieSubalgebra.lieSpan A _
    (Set.range fun k : Fin 2 ↦ fixedSubalgebraBaseChangeBasis A (.inl k))

/-- The folded Cartan subalgebra is abelian over every commutative ring. -/
instance instIsLieAbelianFoldedCartanSubalgebra (A : Type*) [CommRing A] :
    IsLieAbelian (foldedCartanSubalgebra A) := by
  rw [foldedCartanSubalgebra, LieSubalgebra.isLieAbelian_lieSpan_iff]
  rintro - ⟨i, rfl⟩ - ⟨j, rfl⟩
  exact (isSerreSystem_g2FixedBaseChange A).lie_H_H i j

/-- The two folded Cartan generators are linearly independent over every commutative ring `A`. -/
theorem linearIndependent_foldedCartan (A : Type*) [CommRing A] :
    LinearIndependent A (fun k : Fin 2 ↦ fixedSubalgebraBaseChangeBasis A (.inl k)) :=
  (fixedSubalgebraBaseChangeBasis A).linearIndependent.comp Sum.inl Sum.inl_injective

/-- **The folded Chevalley generators of the `D₄` triality fixed Lie subalgebra form a
`LieAlgebra.Basis` of type `G₂`** with Cartan matrix `CartanMatrix.G₂ᵀ`
(`= DynkinType.G2.cartanMatrix`, short root at `0`, long root at `1`) over any nontrivial
commutative ring `A` in which `2` and `3` are invertible. -/
noncomputable def foldedLieBasis (A : Type*) [CommRing A] [Nontrivial A]
    [Invertible (2 : A)] [Invertible (3 : A)] :
    LieAlgebra.Basis (Fin 2) (foldedCartanSubalgebra A) where
  A := DynkinType.G2.cartanMatrix
  h k := fixedSubalgebraBaseChangeBasis A (.inl k)
  e k := fixedSubalgebraBaseChangeBasis A (.inr (false, k.castLE (by decide)))
  f k := fixedSubalgebraBaseChangeBasis A (.inr (true, k.castLE (by decide)))
  cartan_eq_lieSpan := rfl
  span_ef := lieSpan_foldedGenerators_eq_top A
  linInd := linearIndependent_foldedCartan A
  nondegen := Matrix.Nondegenerate.of_det_ne_zero (by
    rw [DynkinType.cartanMatrix_G2, det_transpose, CartanMatrix.G₂_det]
    norm_num)
  sl2 i :=
    { h_ne_zero := (linearIndependent_foldedCartan A).ne_zero i
      lie_e_f := (isSerreSystem_g2FixedBaseChange A).lie_E_F_self i
      lie_h_e_nsmul := by
        rw [(isSerreSystem_g2FixedBaseChange A).lie_H_E, CartanMatrix.G₂_diag, ofNat_zsmul]
      lie_h_f_nsmul := by
        rw [(isSerreSystem_g2FixedBaseChange A).lie_H_F, CartanMatrix.G₂_diag, ofNat_zsmul] }
  lie_h_h i j := (isSerreSystem_g2FixedBaseChange A).lie_H_H i j
  lie_h_e i j := by
    rw [DynkinType.cartanMatrix_G2, transpose_apply]
    exact (isSerreSystem_g2FixedBaseChange A).lie_H_E j i
  lie_h_f i j := by
    rw [(isSerreSystem_g2FixedBaseChange A).lie_H_F, DynkinType.cartanMatrix_G2, transpose_apply,
      neg_smul]
  lie_e_f_ne i j hij := (isSerreSystem_g2FixedBaseChange A).lie_E_F_of_ne i j hij

@[simp]
theorem foldedLieBasis_A (A : Type*) [CommRing A] [Nontrivial A]
    [Invertible (2 : A)] [Invertible (3 : A)] :
    (foldedLieBasis A).A = DynkinType.G2.cartanMatrix := by
  rfl

@[simp]
theorem foldedLieBasis_h (A : Type*) [CommRing A] [Nontrivial A]
    [Invertible (2 : A)] [Invertible (3 : A)] (k : Fin 2) :
    (foldedLieBasis A).h k = fixedSubalgebraBaseChangeBasis A (.inl k) := by
  rfl

@[simp]
theorem foldedLieBasis_e (A : Type*) [CommRing A] [Nontrivial A]
    [Invertible (2 : A)] [Invertible (3 : A)] (k : Fin 2) :
    (foldedLieBasis A).e k =
      fixedSubalgebraBaseChangeBasis A (.inr (false, k.castLE (by decide))) := by
  rfl

@[simp]
theorem foldedLieBasis_f (A : Type*) [CommRing A] [Nontrivial A]
    [Invertible (2 : A)] [Invertible (3 : A)] (k : Fin 2) :
    (foldedLieBasis A).f k =
      fixedSubalgebraBaseChangeBasis A (.inr (true, k.castLE (by decide))) := by
  rfl

end TauCeti.D4Triality

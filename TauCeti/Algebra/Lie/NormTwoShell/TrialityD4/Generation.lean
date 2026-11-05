/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.CharP.Invertible
public import Mathlib.Algebra.Lie.Basis.Base
public import TauCeti.Algebra.Lie.NormTwoShell.TrialityD4.Folding
public import TauCeti.Algebra.Lie.Subalgebra.LieSpan

/-!
# Bracket table and generation of the D₄ triality fixed Lie algebra

Folding `CartanMatrix.D 4` along `TauCeti.trialityPermD4` equips the triality-fixed Lie subalgebra
with the Serre comparison homomorphism `TauCeti.D4Triality.g2SerreLift A` from
`Matrix.ToLieAlgebra A CartanMatrix.G₂` over any commutative ring `A`. Unlike the ambient simply
laced shell Lie algebra, the integral fixed Lie subring is not generated over `ℤ` by its folded
Chevalley frame alone: bracketing along the short root string introduces factors of `2` and `3`.

Specifically, uniformly in `negative : Bool` (`false` for positive roots, `true` for negative
roots), writing `xₒ := invariantRoot negative o` and denoting by `α₀` and `α₁` the short (index
`0`) and long (index `1`) simple roots of `G₂`, the six signed root orbit sums satisfy:

* `⁅x₀, x₁⁆ = x₂` (height `2`, short root `α₀ + α₁`),
* `⁅x₀, x₂⁆ = -2 • x₃` (height `3`, short root `2α₀ + α₁`),
* `⁅x₀, x₃⁆ = -3 • x₄` (height `4`, long root `3α₀ + α₁`),
* `⁅x₁, x₄⁆ = -x₅` and `⁅x₂, x₃⁆ = -3 • x₅` (height `5`, highest long root `3α₀ + 2α₁`),

while for `k : Fin 2`, writing `E'ₖ := invariantRoot false (simpleOrbit k)`,
`F'ₖ := invariantRoot true (simpleOrbit k)`, and `H'ₖ := invariantCartan k`, the relations
`⁅E'₀, F'₀⁆ = H'₀` and `⁅E'₁, F'₁⁆ = H'₁` recover the two invariant Cartan basis vectors
(`isSerreSystem_g2.lie_E_F_self`).

Combining these iterated Lie-word formulas with `2`- and `3`-divisibility invariants on the high
root coordinates yields a sharp characterization over an arbitrary commutative ring `A`:

* `TauCeti.D4Triality.foldedGenerators` and
  `TauCeti.D4Triality.lieSpan_foldedGenerators_eq_top_iff`: the four folded raising and lowering
  generators span the entire `14`-rank triality-fixed Lie subalgebra as an `A`-Lie algebra if and
  only if `IsUnit (2 : A) ∧ IsUnit (3 : A)`.
* `TauCeti.D4Triality.g2SerreLift_surjective_iff`: `g2SerreLift A` is surjective if and only if
  `IsUnit (2 : A) ∧ IsUnit (3 : A)`.
* `TauCeti.D4Triality.lieSpan_foldedGenerators_eq_top` and
  `TauCeti.D4Triality.g2SerreLift_surjective`: typeclass specializations under
  `[Invertible (2 : A)] [Invertible (3 : A)]`, which apply automatically over `ℚ` and every
  characteristic-zero field.
* `TauCeti.D4Triality.foldedCartanSubalgebra` and `TauCeti.D4Triality.foldedLieBasis`: the abelian
  folded Cartan subalgebra and the resulting `LieAlgebra.Basis` with Cartan matrix
  `TauCeti.DynkinType.G2.cartanMatrix` over any nontrivial commutative ring in which `2` and `3`
  are invertible.

## References

* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Plate IX.
* R. Steinberg, *Lectures on Chevalley Groups*, Yale University, 1967, §10.
* V. G. Kac, *Infinite dimensional Lie algebras*, third edition, §7.9.
-/

public section

open scoped TensorProduct

namespace TauCeti.D4Triality

open _root_.Matrix

/-! ### Ambient and fixed-basis bracket coordinates -/

private theorem lie_invariantRoot_eq_sum (neg₁ neg₂ : Bool) (o₁ o₂ : Fin 6) :
    ⁅invariantRoot neg₁ o₁, invariantRoot neg₂ o₂⁆ =
      ∑ i : Fin 12 with orbit i = o₁, ∑ j : Fin 12 with orbit j = o₂,
        (orbitCoeff i * orbitCoeff j) •
          ShellLieAlgebra.rootBracket (CartanMatrix.D 4) (root neg₁ i) (root neg₂ j) := by
  rw [invariantRoot_eq_sum neg₁ o₁, ← ShellLieAlgebra.bracketBilin_apply_apply,
    map_sum, LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [invariantRoot_eq_sum neg₂ o₂]
  simp only [map_zsmul, LinearMap.smul_apply, map_sum, ShellLieAlgebra.bracketBilin_apply_apply,
    ShellLieAlgebra.root_lie_root, smul_smul]
  exact Finset.sum_congr rfl fun j _ ↦ by rw [mul_comm]

private theorem basis_repr_lie_invariantRoot_inl (neg₁ neg₂ : Bool) (o₁ o₂ : Fin 6)
    (k : Fin 4) :
    (ShellLieAlgebra.basis (CartanMatrix.D 4)).repr
        ⁅invariantRoot neg₁ o₁, invariantRoot neg₂ o₂⁆ (.inl k) =
      ∑ i : Fin 12 with orbit i = o₁, ∑ j : Fin 12 with orbit j = o₂,
        orbitCoeff i * orbitCoeff j *
          if (root neg₁ i : Fin 4 → ℤ) + root neg₂ j = 0 then
            ((-1 : ℤ) ^
              (∑ r : Fin 4, ∑ s : Fin 4,
                if s < r then
                  (root neg₁ i : Fin 4 → ℤ) r * CartanMatrix.D 4 r s *
                    (root neg₂ j : Fin 4 → ℤ) s
                else 0).natAbs) *
              (root neg₁ i : Fin 4 → ℤ) k
          else 0 := by
  simp only [lie_invariantRoot_eq_sum, map_sum, map_zsmul, Finsupp.finsetSum_apply,
    Finsupp.smul_apply, smul_eq_mul, ShellLieAlgebra.basis_repr_rootBracket_inl,
    orderedSignForm_apply]
  refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
  congr 4
  exact Int.coe_negOnePow ℤ _

private theorem basis_repr_lie_invariantRoot_inr (neg₁ neg₂ : Bool) (o₁ o₂ : Fin 6)
    (c : (CartanMatrix.D 4).normTwoShell) :
    (ShellLieAlgebra.basis (CartanMatrix.D 4)).repr
        ⁅invariantRoot neg₁ o₁, invariantRoot neg₂ o₂⁆ (.inr c) =
      ∑ i : Fin 12 with orbit i = o₁, ∑ j : Fin 12 with orbit j = o₂,
        orbitCoeff i * orbitCoeff j *
          if (root neg₁ i : Fin 4 → ℤ) + root neg₂ j = c then
            (-1 : ℤ) ^
              (∑ r : Fin 4, ∑ s : Fin 4,
                if s < r then
                  (root neg₁ i : Fin 4 → ℤ) r * CartanMatrix.D 4 r s *
                    (root neg₂ j : Fin 4 → ℤ) s
                else 0).natAbs
          else 0 := by
  simp only [lie_invariantRoot_eq_sum, map_sum, map_zsmul, Finsupp.finsetSum_apply,
    Finsupp.smul_apply, smul_eq_mul, ShellLieAlgebra.basis_repr_rootBracket_inr,
    orderedSignForm_apply]
  refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
  congr 3
  exact Int.coe_negOnePow ℤ _

private def rootVec (negative : Bool) (i : Fin 12) : Fin 4 → ℤ :=
  if negative then -positiveRoot i else positiveRoot i

private def fixedBasisBracketInrCoord (neg₁ neg₂ : Bool) (o₁ o₂ : Fin 6) :
    Fin 2 ⊕ (Bool × Fin 6) → ℤ
  | .inl k =>
      ∑ i : Fin 12 with orbit i = o₁, ∑ j : Fin 12 with orbit j = o₂,
        orbitCoeff i * orbitCoeff j *
          if rootVec neg₁ i + rootVec neg₂ j = 0 then
            ((-1 : ℤ) ^
              (∑ r : Fin 4, ∑ s : Fin 4,
                if s < r then
                  rootVec neg₁ i r * CartanMatrix.D 4 r s * rootVec neg₂ j s
                else 0).natAbs) *
              rootVec neg₁ i (vertexRepresentative k)
          else 0
  | .inr (neg', o) =>
      ∑ i : Fin 12 with orbit i = o₁, ∑ j : Fin 12 with orbit j = o₂,
        orbitCoeff i * orbitCoeff j *
          if rootVec neg₁ i + rootVec neg₂ j = rootVec neg' (representative o) then
            (-1 : ℤ) ^
              (∑ r : Fin 4, ∑ s : Fin 4,
                if s < r then
                  rootVec neg₁ i r * CartanMatrix.D 4 r s * rootVec neg₂ j s
                else 0).natAbs
          else 0

private theorem fixedBasis_repr_lie_inr (neg₁ neg₂ : Bool) (o₁ o₂ : Fin 6)
    (idx : Fin 2 ⊕ (Bool × Fin 6)) :
    fixedBasis.repr ⁅fixedBasis (.inr (neg₁, o₁)), fixedBasis (.inr (neg₂, o₂))⁆ idx =
      fixedBasisBracketInrCoord neg₁ neg₂ o₁ o₂ idx := by
  -- `congr` equates the `Classical` and computable `Decidable` instances on the root-sum condition.
  rcases idx with k | ⟨neg', o⟩
  · simp only [fixedBasis_repr_inl, LieSubalgebra.coe_bracket, coe_fixedBasis_inr,
      basis_repr_lie_invariantRoot_inl, coe_root, fixedBasisBracketInrCoord, rootVec]
    exact Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ by congr
  · simp only [fixedBasis_repr_inr, LieSubalgebra.coe_bracket, coe_fixedBasis_inr,
      basis_repr_lie_invariantRoot_inr, coe_root, fixedBasisBracketInrCoord, rootVec]
    exact Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ by congr

private theorem lie_fixedBasis_inr_eq_zsmul {negative : Bool} {o₁ o₂ o₃ : Fin 6} {c : ℤ}
    (h : ∀ idx : Fin 2 ⊕ (Bool × Fin 6),
      fixedBasisBracketInrCoord negative negative o₁ o₂ idx =
        if idx = .inr (negative, o₃) then c else 0) :
    ⁅fixedBasis (.inr (negative, o₁)), fixedBasis (.inr (negative, o₂))⁆ =
      c • fixedBasis (.inr (negative, o₃)) := by
  refine fixedBasis.repr.injective (Finsupp.ext fun idx ↦ ?_)
  rw [fixedBasis_repr_lie_inr, h idx, map_zsmul, Module.Basis.repr_self, Finsupp.smul_apply,
    Finsupp.single_apply, smul_eq_mul]
  split_ifs with hidx hidx' hidx''
  · ring
  · exact absurd hidx.symm hidx'
  · exact absurd hidx''.symm hidx
  · ring

private theorem lie_invariantRoot_eq_zsmul_of_lie_fixedBasis {negative : Bool}
    {o₁ o₂ o₃ : Fin 6} {c : ℤ}
    (h : ⁅fixedBasis (.inr (negative, o₁)), fixedBasis (.inr (negative, o₂))⁆ =
      c • fixedBasis (.inr (negative, o₃))) :
    ⁅invariantRoot negative o₁, invariantRoot negative o₂⁆ =
      c • invariantRoot negative o₃ := by
  simpa only [LieSubalgebra.coe_bracket, SetLike.val_smul, coe_fixedBasis_inr] using
    congrArg Subtype.val h

/-! ### Integral Chevalley-like bracket relations along the six root orbits -/

/-- Bracketing the short simple orbit `0` with the long simple orbit `1` produces the height-`2`
short orbit `2` with coefficient `1`. -/
@[simp]
theorem lie_fixedBasis_zero_one (negative : Bool) :
    ⁅fixedBasis (.inr (negative, 0)), fixedBasis (.inr (negative, 1))⁆ =
      fixedBasis (.inr (negative, 2)) :=
  (lie_fixedBasis_inr_eq_zsmul (c := 1) (by revert negative; decide)).trans (one_smul ℤ _)

@[simp]
theorem lie_invariantRoot_zero_one (negative : Bool) :
    ⁅invariantRoot negative 0, invariantRoot negative 1⁆ = invariantRoot negative 2 :=
  (lie_invariantRoot_eq_zsmul_of_lie_fixedBasis
    ((lie_fixedBasis_zero_one negative).trans (one_smul ℤ _).symm)).trans (one_smul ℤ _)

/-- Bracketing the short simple orbit `0` with the height-`2` short orbit `2` produces `-2` times
the height-`3` short orbit `3`. -/
@[simp]
theorem lie_fixedBasis_zero_two (negative : Bool) :
    ⁅fixedBasis (.inr (negative, 0)), fixedBasis (.inr (negative, 2))⁆ =
      -(2 : ℤ) • fixedBasis (.inr (negative, 3)) :=
  lie_fixedBasis_inr_eq_zsmul (by revert negative; decide)

@[simp]
theorem lie_invariantRoot_zero_two (negative : Bool) :
    ⁅invariantRoot negative 0, invariantRoot negative 2⁆ =
      -(2 : ℤ) • invariantRoot negative 3 :=
  lie_invariantRoot_eq_zsmul_of_lie_fixedBasis (lie_fixedBasis_zero_two negative)

/-- Bracketing the short simple orbit `0` with the height-`3` short orbit `3` produces `-3` times
the height-`4` long orbit `4`. -/
@[simp]
theorem lie_fixedBasis_zero_three (negative : Bool) :
    ⁅fixedBasis (.inr (negative, 0)), fixedBasis (.inr (negative, 3))⁆ =
      -(3 : ℤ) • fixedBasis (.inr (negative, 4)) :=
  lie_fixedBasis_inr_eq_zsmul (by revert negative; decide)

@[simp]
theorem lie_invariantRoot_zero_three (negative : Bool) :
    ⁅invariantRoot negative 0, invariantRoot negative 3⁆ =
      -(3 : ℤ) • invariantRoot negative 4 :=
  lie_invariantRoot_eq_zsmul_of_lie_fixedBasis (lie_fixedBasis_zero_three negative)

/-- Bracketing the long simple orbit `1` with the height-`4` long orbit `4` (the extraspecial pair
for the highest root `3α₀ + 2α₁`) produces `-1` times the highest long orbit `5`. -/
@[simp]
theorem lie_fixedBasis_one_four (negative : Bool) :
    ⁅fixedBasis (.inr (negative, 1)), fixedBasis (.inr (negative, 4))⁆ =
      -fixedBasis (.inr (negative, 5)) :=
  (lie_fixedBasis_inr_eq_zsmul (c := -1) (by revert negative; decide)).trans (neg_one_smul ℤ _)

@[simp]
theorem lie_invariantRoot_one_four (negative : Bool) :
    ⁅invariantRoot negative 1, invariantRoot negative 4⁆ = -invariantRoot negative 5 :=
  (lie_invariantRoot_eq_zsmul_of_lie_fixedBasis
    ((lie_fixedBasis_one_four negative).trans (neg_one_smul ℤ _).symm)).trans (neg_one_smul ℤ _)

/-- Bracketing the two intermediate short orbits `2` and `3` (a special, non-extraspecial pair for
the highest root `3α₀ + 2α₁`) produces `-3` times the highest long orbit `5`. -/
@[simp]
theorem lie_fixedBasis_two_three (negative : Bool) :
    ⁅fixedBasis (.inr (negative, 2)), fixedBasis (.inr (negative, 3))⁆ =
      -(3 : ℤ) • fixedBasis (.inr (negative, 5)) :=
  lie_fixedBasis_inr_eq_zsmul (by revert negative; decide)

@[simp]
theorem lie_invariantRoot_two_three (negative : Bool) :
    ⁅invariantRoot negative 2, invariantRoot negative 3⁆ =
      -(3 : ℤ) • invariantRoot negative 5 :=
  lie_invariantRoot_eq_zsmul_of_lie_fixedBasis (lie_fixedBasis_two_three negative)

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

/-- The four folded `G₂` simple root vectors (`E'₀, E'₁, F'₀, F'₁`) in the scalar-extended `D₄`
triality fixed Lie subalgebra. -/
noncomputable def foldedGenerators (A : Type*) [CommRing A] :
    Set (LieEquiv.baseChange A trialityLieEquiv).toLieHom.fixedSubalgebra :=
  Set.range (fun k : Fin 2 ↦ fixedSubalgebraBaseChangeBasis A (.inr (false, simpleOrbit k))) ∪
    Set.range (fun k : Fin 2 ↦ fixedSubalgebraBaseChangeBasis A (.inr (true, simpleOrbit k)))

theorem foldedGenerators_def (A : Type*) [CommRing A] :
    foldedGenerators A =
      Set.range (fun k : Fin 2 ↦ fixedSubalgebraBaseChangeBasis A (.inr (false, simpleOrbit k))) ∪
        Set.range
          (fun k : Fin 2 ↦ fixedSubalgebraBaseChangeBasis A (.inr (true, simpleOrbit k))) :=
  (rfl)

/-- Each folded raising (`negative = false`) and lowering (`negative = true`) simple root vector
belongs to `foldedGenerators A`. -/
@[simp]
theorem fixedSubalgebraBaseChangeBasis_simpleOrbit_mem_foldedGenerators
    (A : Type*) [CommRing A] (negative : Bool) (k : Fin 2) :
    fixedSubalgebraBaseChangeBasis A (.inr (negative, simpleOrbit k)) ∈ foldedGenerators A := by
  cases negative
  · exact Or.inl ⟨k, rfl⟩
  · exact Or.inr ⟨k, rfl⟩

/-- An element of the triality-fixed Lie subalgebra belongs to `foldedGenerators A` if and only if
it is one of the four folded raising or lowering simple root vectors. -/
theorem mem_foldedGenerators_iff (A : Type*) [CommRing A]
    (x : (LieEquiv.baseChange A trialityLieEquiv).toLieHom.fixedSubalgebra) :
    x ∈ foldedGenerators A ↔
      ∃ (negative : Bool) (k : Fin 2),
        fixedSubalgebraBaseChangeBasis A (.inr (negative, simpleOrbit k)) = x := by
  simp only [foldedGenerators_def, Set.mem_union, Set.mem_range, Bool.exists_bool]

private theorem simpleOrbit_ne_of_two_le (k : Fin 2) {o : Fin 6} (ho : 2 ≤ o.val) :
    simpleOrbit k ≠ o := by
  intro h
  have hval := congrArg Fin.val h
  simp only [coe_simpleOrbit] at hval
  omega

private theorem fixedBasis_repr_lie_gen_inl_inr_eq_zero (neg_g : Bool) (k k' : Fin 2)
    (o : Fin 6) (ho : 2 ≤ o.val) :
    fixedBasis.repr
        ⁅fixedBasis (.inr (neg_g, simpleOrbit k)), fixedBasis (.inl k')⁆
        (.inr (false, o)) = 0 := by
  rw [← lie_skew]
  cases neg_g
  · rw [isSerreSystem_g2Fixed.lie_H_E k' k, map_neg, map_zsmul, Module.Basis.repr_self]
    simp [simpleOrbit_ne_of_two_le k ho]
  · rw [isSerreSystem_g2Fixed.lie_H_F k' k, neg_neg, map_zsmul, Module.Basis.repr_self]
    simp

private theorem dvd_fixedBasis_repr_lie_gen {n cut : ℕ} (hcut : 2 ≤ cut)
    (hcoord : ∀ (neg_g neg' : Bool) (k : Fin 2) (o' o : Fin 6),
      cut ≤ o.val → (neg' = true ∨ o'.val < cut) →
        (n : ℤ) ∣ fixedBasisBracketInrCoord neg_g neg' (simpleOrbit k) o'
          (.inr (false, o)))
    (neg_g : Bool) (k : Fin 2) (idx : Fin 2 ⊕ (Bool × Fin 6)) (o : Fin 6) (ho : cut ≤ o.val)
    (hidx : ∀ o' : Fin 6, cut ≤ o'.val → idx ≠ .inr (false, o')) :
    (n : ℤ) ∣ fixedBasis.repr
        ⁅fixedBasis (.inr (neg_g, simpleOrbit k)), fixedBasis idx⁆
        (.inr (false, o)) := by
  rcases idx with k' | ⟨neg', o'⟩
  · rw [fixedBasis_repr_lie_gen_inl_inr_eq_zero neg_g k k' o (le_trans hcut ho)]
    exact dvd_zero (n : ℤ)
  · rw [fixedBasis_repr_lie_inr]
    refine hcoord neg_g neg' k o' o ho ?_
    cases neg'
    · exact Or.inr (Nat.lt_of_not_ge fun hge ↦ hidx o' hge rfl)
    · exact Or.inl rfl

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

private theorem mem_coordDvdSubmodule_iff (A : Type*) [CommRing A] (n cut : ℕ)
    (y : (LieEquiv.baseChange A trialityLieEquiv).toLieHom.fixedSubalgebra) :
    y ∈ coordDvdSubmodule A n cut ↔
      ∀ o : Fin 6, cut ≤ o.val →
        (n : A) ∣ (fixedSubalgebraBaseChangeBasis A).repr y (.inr (false, o)) :=
  Iff.rfl

private theorem lieSpan_le_coordDvdSubmodule (A : Type*) [CommRing A] {n cut : ℕ}
    (hcut : 2 ≤ cut)
    (hdvd : ∀ (neg_g : Bool) (k : Fin 2) (idx : Fin 2 ⊕ (Bool × Fin 6)) (o : Fin 6),
      cut ≤ o.val → (∀ o' : Fin 6, cut ≤ o'.val → idx ≠ .inr (false, o')) →
        (n : ℤ) ∣ fixedBasis.repr
          ⁅fixedBasis (.inr (neg_g, simpleOrbit k)), fixedBasis idx⁆
          (.inr (false, o))) :
    (LieSubalgebra.lieSpan A (LieEquiv.baseChange A trialityLieEquiv).toLieHom.fixedSubalgebra
      (foldedGenerators A)).toSubmodule ≤
      coordDvdSubmodule A n cut := by
  let b := fixedSubalgebraBaseChangeBasis A
  refine LieSubalgebra.lieSpan_toSubmodule_le_of_lie_mem ?_ ?_
  · intro x hx
    obtain ⟨neg_g, k, rfl⟩ := (mem_foldedGenerators_iff A x).mp hx
    rw [SetLike.mem_coe, mem_coordDvdSubmodule_iff]
    intro o ho
    rw [Module.Basis.repr_self]
    cases neg_g
    · simp [simpleOrbit_ne_of_two_le k (le_trans hcut ho)]
    · simp
  · intro x hx y hy
    obtain ⟨neg_g, k, rfl⟩ := (mem_foldedGenerators_iff A x).mp hx
    rw [mem_coordDvdSubmodule_iff] at hy ⊢
    intro o ho
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

private theorem isUnit_of_lieSpan_foldedGenerators_eq_top (A : Type*) [CommRing A]
    (n cut : ℕ) (hcut : 2 ≤ cut) (o : Fin 6) (ho : cut ≤ o.val)
    (hcoord : ∀ (neg_g neg' : Bool) (k : Fin 2) (o' o : Fin 6),
      cut ≤ o.val → (neg' = true ∨ o'.val < cut) →
        (n : ℤ) ∣ fixedBasisBracketInrCoord neg_g neg' (simpleOrbit k) o'
          (.inr (false, o)))
    (htop :
      LieSubalgebra.lieSpan A (LieEquiv.baseChange A trialityLieEquiv).toLieHom.fixedSubalgebra
        (foldedGenerators A) = ⊤) :
    IsUnit (n : A) := by
  have hle := lieSpan_le_coordDvdSubmodule A hcut (dvd_fixedBasis_repr_lie_gen hcut hcoord)
  rw [htop] at hle
  have hmem : fixedSubalgebraBaseChangeBasis A (.inr (false, o)) ∈
      coordDvdSubmodule A n cut := hle trivial
  have hdvd := (mem_coordDvdSubmodule_iff A n cut _).mp hmem o ho
  rw [Module.Basis.repr_self, Finsupp.single_eq_same] at hdvd
  exact isUnit_iff_dvd_one.mpr hdvd

private theorem mem_lieSpan_foldedGenerators_inr (A : Type*) [CommRing A]
    [Invertible (2 : A)] [Invertible (3 : A)] (neg : Bool) (o : Fin 6) :
    fixedSubalgebraBaseChangeBasis A (.inr (neg, o)) ∈
      LieSubalgebra.lieSpan A (LieEquiv.baseChange A trialityLieEquiv).toLieHom.fixedSubalgebra
        (foldedGenerators A) := by
  let b := fixedSubalgebraBaseChangeBasis A
  let K := LieSubalgebra.lieSpan A
    (LieEquiv.baseChange A trialityLieEquiv).toLieHom.fixedSubalgebra (foldedGenerators A)
  have h0 : b (.inr (neg, 0)) ∈ K :=
    LieSubalgebra.subset_lieSpan
      (by simpa using fixedSubalgebraBaseChangeBasis_simpleOrbit_mem_foldedGenerators A neg 0)
  have h1 : b (.inr (neg, 1)) ∈ K :=
    LieSubalgebra.subset_lieSpan
      (by simpa using fixedSubalgebraBaseChangeBasis_simpleOrbit_mem_foldedGenerators A neg 1)
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
      (foldedGenerators A) = ⊤ := by
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
        (foldedGenerators A) = ⊤ ↔
      IsUnit (2 : A) ∧ IsUnit (3 : A) := by
  constructor
  · intro htop
    exact ⟨isUnit_of_lieSpan_foldedGenerators_eq_top A 2 3 (by decide) 3 (by decide)
        (by decide) htop,
      isUnit_of_lieSpan_foldedGenerators_eq_top A 3 4 (by decide) 4 (by decide)
        (by decide) htop⟩
  · rintro ⟨h2, h3⟩
    have := h2.nonempty_invertible.some
    have := h3.nonempty_invertible.some
    exact lieSpan_foldedGenerators_eq_top_of_invertible A

/-- When `2` and `3` are invertible in `A` (in particular over `ℚ` or any characteristic-zero
field), the folded `G₂` simple root vectors generate the entire triality-fixed Lie subalgebra. -/
theorem lieSpan_foldedGenerators_eq_top (A : Type*) [CommRing A]
    [Invertible (2 : A)] [Invertible (3 : A)] :
    LieSubalgebra.lieSpan A (LieEquiv.baseChange A trialityLieEquiv).toLieHom.fixedSubalgebra
      (foldedGenerators A) = ⊤ :=
  lieSpan_foldedGenerators_eq_top_of_invertible A

/-- The image of `g2SerreLift A` is always the `A`-Lie subalgebra generated by
`foldedGenerators A`. -/
theorem range_g2SerreLift (A : Type*) [CommRing A] :
    (g2SerreLift A).range =
      LieSubalgebra.lieSpan A (LieEquiv.baseChange A trialityLieEquiv).toLieHom.fixedSubalgebra
        (foldedGenerators A) := by
  rw [LieHom.range_eq_map, ← lieSpan_serreE_union_serreF_eq_top A CartanMatrix.G₂,
    LieSubalgebra.map_lieSpan]
  simp [foldedGenerators_def, Set.image_union, ← Set.range_comp, Function.comp_def]

/-- **Sharp surjectivity characterization for `g2SerreLift A`.**
Over any commutative ring `A`, the folded `G₂` Serre comparison homomorphism `g2SerreLift A` onto
the `D₄` triality fixed Lie subalgebra is surjective if and only if both `2` and `3` are units in
`A`. -/
theorem g2SerreLift_surjective_iff (A : Type*) [CommRing A] :
    Function.Surjective (g2SerreLift A) ↔ IsUnit (2 : A) ∧ IsUnit (3 : A) := by
  rw [← LieHom.range_eq_top, range_g2SerreLift, lieSpan_foldedGenerators_eq_top_iff]

/-- When `2` and `3` are invertible in `A` (in particular over `ℚ` or any characteristic-zero
field), `g2SerreLift A` maps `Matrix.ToLieAlgebra A CartanMatrix.G₂` surjectively onto the
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

theorem foldedCartanSubalgebra_def (A : Type*) [CommRing A] :
    foldedCartanSubalgebra A =
      LieSubalgebra.lieSpan A _
        (Set.range fun k : Fin 2 ↦ fixedSubalgebraBaseChangeBasis A (.inl k)) :=
  (rfl)

/-- Both folded Cartan basis vectors belong to `foldedCartanSubalgebra A`. -/
@[simp]
theorem fixedSubalgebraBaseChangeBasis_inl_mem_foldedCartanSubalgebra
    (A : Type*) [CommRing A] (k : Fin 2) :
    fixedSubalgebraBaseChangeBasis A (.inl k) ∈ foldedCartanSubalgebra A :=
  LieSubalgebra.subset_lieSpan ⟨k, rfl⟩

/-- The folded Cartan subalgebra is abelian over every commutative ring. -/
instance instIsLieAbelianFoldedCartanSubalgebra (A : Type*) [CommRing A] :
    IsLieAbelian (foldedCartanSubalgebra A) := by
  rw [foldedCartanSubalgebra_def, LieSubalgebra.isLieAbelian_lieSpan_iff]
  rintro - ⟨i, rfl⟩ - ⟨j, rfl⟩
  exact (isSerreSystem_g2FixedBaseChange A).lie_H_H i j

/-- The underlying `A`-submodule of `foldedCartanSubalgebra A` is the `A`-linear span of the two
folded Cartan basis vectors. -/
theorem toSubmodule_foldedCartanSubalgebra (A : Type*) [CommRing A] :
    (foldedCartanSubalgebra A).toSubmodule =
      Submodule.span A
        (Set.range fun k : Fin 2 ↦ fixedSubalgebraBaseChangeBasis A (.inl k)) := by
  rw [foldedCartanSubalgebra_def]
  refine LieSubalgebra.coe_lieSpan_eq_span_of_forall_lie_eq_zero ?_
  rintro - ⟨i, rfl⟩ - ⟨j, rfl⟩
  exact (isSerreSystem_g2FixedBaseChange A).lie_H_H i j

/-- An element of the triality-fixed Lie subalgebra belongs to `foldedCartanSubalgebra A` if and
only if all twelve of its root-orbit coordinates vanish. -/
theorem mem_foldedCartanSubalgebra_iff (A : Type*) [CommRing A]
    (x : (LieEquiv.baseChange A trialityLieEquiv).toLieHom.fixedSubalgebra) :
    x ∈ foldedCartanSubalgebra A ↔
      ∀ (negative : Bool) (o : Fin 6),
        (fixedSubalgebraBaseChangeBasis A).repr x (.inr (negative, o)) = 0 := by
  classical
  have hs :
      Set.range (fun k : Fin 2 ↦ fixedSubalgebraBaseChangeBasis A (.inl k)) =
        fixedSubalgebraBaseChangeBasis A '' Set.range Sum.inl := by
    ext y
    simp
  rw [← LieSubalgebra.mem_toSubmodule, toSubmodule_foldedCartanSubalgebra, hs,
    Module.Basis.mem_span_image]
  constructor
  · intro hx negative o
    by_contra ho
    have hmem := hx (Finsupp.mem_support_iff.mpr ho)
    simp at hmem
  · intro hx idx hidx
    rcases idx with k | ⟨negative, o⟩
    · exact ⟨k, rfl⟩
    · exact False.elim ((Finsupp.mem_support_iff.mp hidx) (hx negative o))

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
  e k := fixedSubalgebraBaseChangeBasis A (.inr (false, simpleOrbit k))
  f k := fixedSubalgebraBaseChangeBasis A (.inr (true, simpleOrbit k))
  cartan_eq_lieSpan := rfl
  span_ef := by rw [← foldedGenerators_def]; exact lieSpan_foldedGenerators_eq_top A
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
      fixedSubalgebraBaseChangeBasis A (.inr (false, simpleOrbit k)) := by
  rfl

@[simp]
theorem foldedLieBasis_f (A : Type*) [CommRing A] [Nontrivial A]
    [Invertible (2 : A)] [Invertible (3 : A)] (k : Fin 2) :
    (foldedLieBasis A).f k =
      fixedSubalgebraBaseChangeBasis A (.inr (true, simpleOrbit k)) := by
  rfl

end TauCeti.D4Triality

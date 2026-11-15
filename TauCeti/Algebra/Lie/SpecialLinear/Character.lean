/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.SpecialLinear.Root.Basis
public import TauCeti.Algebra.Lie.Weights.Basis

/-!
# Weights and formal characters of `sl (Fin (r + 1))`

Let `H = TauCeti.specialLinearDiagonalCartan r A` be the trace-zero diagonal matrices in
`sl (Fin (r + 1)) A`. Its linear forms are read through two families:

* the **coordinate weights** `εₖ = TauCeti.specialLinearEpsilon r A k`, the `k`-th diagonal entry,
  which sum to zero on `H`;
* the **fundamental weights** `ωᵢ = TauCeti.specialLinearFundamentalWeight r A i`, the basis dual
  to the simple coroots `hᵢ = Eᵢᵢ - Eᵢ₊₁,ᵢ₊₁` (`TauCeti.specialLinearDiagonalCartanBasis`), so that
  `ωᵢ (hⱼ) = δᵢⱼ`. In coordinates `ωᵢ = ε₀ + ⋯ + εᵢ`
  (`TauCeti.specialLinearFundamentalWeight_eq_sum`).

The three basic modules have bases of `H`-weight vectors, so their formal characters
(`TauCeti.formalCharacter`, the generating function of the weight multiplicities) can be read off:

* the standard module `Fin (r + 1) → K` has the basis vectors `eₖ`, of weight `εₖ`;
* its dual has the coordinate functionals, of weight `-εₖ`;
* the adjoint module `sl (Fin (r + 1)) K` has the simple coroots, of weight `0`, and the signed
  matrix units `Eᵢⱼ` with `i ≠ j`, of weight `εᵢ - εⱼ`, the roots.

These characters sum over the basis vectors, so they hold over every field. Distinct basis
vectors can however have equal weights in positive characteristic, and then the multiplicities add:
for `sl₂` (`r = 1`) with `2 = 0` one has `ε₀ = ε₁`.

For `sl₃` (`r = 2`) this gives the classical weight diagrams in terms of the fundamental weights,
indexed from zero as `ω₀, ω₁`. The standard module has the triangle of weights
`ω₀, ω₁ - ω₀, -ω₁`, and its dual has their negatives. The adjoint module has the six roots
`±(2ω₀ - ω₁)`, `±(2ω₁ - ω₀)`, `±(ω₀ + ω₁)` together with the weight `0`, of multiplicity `2` over
every field. The six roots are distinct, forming a hexagon, exactly when `2 ≠ 0` and `3 ≠ 0`: if
`2 = 0` each root equals its negative, and if `3 = 0` they collapse to `±(ω₀ + ω₁)`. In
characteristic zero these three modules are the irreducible modules classically denoted `V(ω₀)`,
`V(ω₁)` and `V(ω₀ + ω₁)`; if `3 = 0` the adjoint module is reducible, as it contains the scalar
matrices.

## Main definitions

* `TauCeti.specialLinearEpsilon`: the coordinate weight `εₖ` on the diagonal Cartan.
* `TauCeti.specialLinearFundamentalWeight`: the fundamental weights, dual to the simple coroots.
* `TauCeti.specialLinearRootBasisWeight`: the weights of the vectors of
  `TauCeti.specialLinearRootBasis`.

## Main results

* `TauCeti.specialLinearFundamentalWeight_eq_sum`: `ωᵢ = ε₀ + ⋯ + εᵢ`.
* `TauCeti.formalCharacter_specialLinear_pi`, `TauCeti.formalCharacter_specialLinear_dual` and
  `TauCeti.formalCharacter_specialLinear_adjoint`: the characters of the standard module, its dual
  and the adjoint module of `sl (Fin (r + 1)) K`, with their supports
  `TauCeti.coe_support_formalCharacter_specialLinear_pi`,
  `TauCeti.coe_support_formalCharacter_specialLinear_dual` and
  `TauCeti.coe_support_formalCharacter_specialLinear_adjoint`.
* `TauCeti.coeff_formalCharacter_specialLinear_adjoint_zero`: the weight `0` of the adjoint module
  has multiplicity the rank `r`, unless `r = 1` and `2 = 0`.
* `TauCeti.formalCharacter_slThree_pi`, `TauCeti.formalCharacter_slThree_dual` and
  `TauCeti.formalCharacter_slThree_adjoint`, with the supports
  `TauCeti.coe_support_formalCharacter_slThree_pi`,
  `TauCeti.coe_support_formalCharacter_slThree_dual` and
  `TauCeti.coe_support_formalCharacter_slThree_adjoint` and the multiplicity
  `TauCeti.coeff_formalCharacter_slThree_adjoint_zero`: the weight diagrams of `sl₃`.

## References

* W. Fulton and J. Harris, *Representation Theory: A First Course*, GTM 129, Lecture 12.
* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, GTM 9, §13.
-/

public section

open LieModule Module LieAlgebra.SpecialLinear

namespace TauCeti

attribute [local instance 100] LieRing.ofAssociativeRing

/-! ### Coordinate and fundamental weights -/

section Weights

variable (r : ℕ) (A : Type*) [CommRing A]

/-- The **coordinate weight** `εₖ` on the diagonal Cartan subalgebra of `sl (Fin (r + 1)) A`: the
`k`-th diagonal entry. -/
def specialLinearEpsilon (k : Fin (r + 1)) : Dual A (specialLinearDiagonalCartan r A) where
  toFun h := (h : Matrix (Fin (r + 1)) (Fin (r + 1)) A) k k
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

variable {r A}

/-- The coordinate weight `εₖ` reads off the `k`-th diagonal entry. -/
@[simp]
theorem specialLinearEpsilon_apply (k : Fin (r + 1)) (h : specialLinearDiagonalCartan r A) :
    specialLinearEpsilon r A k h = (h : Matrix (Fin (r + 1)) (Fin (r + 1)) A) k k :=
  (rfl)

/-- The coordinate weights sum to zero on the diagonal Cartan subalgebra, the matrices there
having trace zero. -/
theorem sum_specialLinearEpsilon : ∑ k, specialLinearEpsilon r A k = 0 := by
  ext h
  have hz : ∑ k, (h : Matrix (Fin (r + 1)) (Fin (r + 1)) A) k k = 0 :=
    (h : sl (Fin (r + 1)) A).property
  simpa [LinearMap.sum_apply] using hz

variable (r A)

/-- The **fundamental weights** `ωᵢ` of `sl (Fin (r + 1)) A`: the basis of linear forms on the
diagonal Cartan subalgebra dual to the simple coroots, `ωᵢ (hⱼ) = δᵢⱼ`. -/
noncomputable def specialLinearFundamentalWeight (i : Fin r) :
    Dual A (specialLinearDiagonalCartan r A) :=
  (specialLinearDiagonalCartanBasis r A).dualBasis i

variable {r A}

/-- The fundamental weights are dual to the simple coroots: `ωᵢ (hⱼ) = δᵢⱼ`. -/
@[simp]
theorem specialLinearFundamentalWeight_apply_specialLinearDiagonalCartanBasis (i j : Fin r) :
    specialLinearFundamentalWeight r A i (specialLinearDiagonalCartanBasis r A j) =
      if j = i then 1 else 0 :=
  (specialLinearDiagonalCartanBasis r A).dualBasis_apply_self i j

/-- The coordinate weight `εₖ` takes the value `δₖᵢ - δₖ,ᵢ₊₁` on the simple coroot `hᵢ`. -/
theorem specialLinearEpsilon_apply_specialLinearDiagonalCartanBasis (k : Fin (r + 1))
    (i : Fin r) :
    specialLinearEpsilon r A k (specialLinearDiagonalCartanBasis r A i) =
      (if k = i.castSucc then 1 else 0) - if k = i.succ then 1 else 0 := by
  rw [specialLinearEpsilon_apply, specialLinearDiagonalCartanBasis_apply, val_singleSubSingle]
  simp [Matrix.single_apply, eq_comm]

/-- **The fundamental weights in coordinates**: `ωᵢ = ε₀ + ⋯ + εᵢ`. -/
theorem specialLinearFundamentalWeight_eq_sum (i : Fin r) :
    specialLinearFundamentalWeight r A i =
      ∑ k ∈ Finset.Iic i.castSucc, specialLinearEpsilon r A k := by
  refine (specialLinearDiagonalCartanBasis _ _).ext fun j => ?_
  rw [specialLinearFundamentalWeight_apply_specialLinearDiagonalCartanBasis, LinearMap.sum_apply]
  simp only [specialLinearEpsilon_apply_specialLinearDiagonalCartanBasis, Finset.sum_sub_distrib,
    Finset.sum_ite_eq', Finset.mem_Iic, Fin.castSucc_le_castSucc_iff]
  by_cases hji : j = i
  · subst hji
    simp [Fin.le_castSucc_iff]
  · rcases lt_or_gt_of_ne hji with h | h
    · have h' : j.succ ≤ i.castSucc := by
        rw [Fin.le_castSucc_iff]
        exact Fin.succ_lt_succ_iff.mpr h
      simp [hji, h.le, h']
    · have h' : ¬ j.succ ≤ i.castSucc := by
        rw [Fin.le_castSucc_iff, not_lt]
        exact (Fin.succ_le_succ_iff.mpr h.le)
      simp [hji, not_le.mpr h, h']

end Weights

/-! ### Weight vectors -/

section WeightVectors

variable {r : ℕ} {A : Type*} [CommRing A]

/-- The diagonal Cartan subalgebra acts on a standard basis vector by its coordinate weight. -/
theorem lie_specialLinearDiagonalCartan_pi_single (h : specialLinearDiagonalCartan r A)
    (k : Fin (r + 1)) :
    ⁅h, (Pi.single k 1 : Fin (r + 1) → A)⁆ =
      specialLinearEpsilon r A k h • (Pi.single k 1 : Fin (r + 1) → A) := by
  have hd := (mem_specialLinearDiagonalCartan_iff r A _).mp h.property
  rw [LieSubalgebra.coe_bracket_of_module, LieSubalgebra.coe_bracket_of_module, Matrix.lie_apply,
    Matrix.mulVec_single_one, specialLinearEpsilon_apply]
  ext i
  by_cases hik : i = k
  · subst hik
    simp
  · simp [hik, hd hik]

/-- The diagonal Cartan subalgebra acts on a coordinate functional of the dual standard module by
minus its coordinate weight. -/
theorem lie_specialLinearDiagonalCartan_proj (h : specialLinearDiagonalCartan r A)
    (k : Fin (r + 1)) :
    ⁅h, (LinearMap.proj k : Dual A (Fin (r + 1) → A))⁆ =
      (-specialLinearEpsilon r A k h) • (LinearMap.proj k : Dual A (Fin (r + 1) → A)) := by
  have hd := (mem_specialLinearDiagonalCartan_iff r A _).mp h.property
  refine LinearMap.ext fun v => ?_
  rw [Module.Dual.lie_apply, LieSubalgebra.coe_bracket_of_module,
    LieSubalgebra.coe_bracket_of_module, Matrix.lie_apply]
  simp only [LinearMap.proj_apply, LinearMap.smul_apply, specialLinearEpsilon_apply, smul_eq_mul,
    Matrix.mulVec, dotProduct]
  rw [Finset.sum_eq_single k (fun j _ hjk => by simp [hd (Ne.symm hjk)]) (by simp)]
  ring

/-- The weight of a vector of `specialLinearRootBasis` under the diagonal Cartan subalgebra: `0`
on the simple coroots and the root `εᵢ - εⱼ` on the signed matrix unit `Eᵢⱼ`. -/
def specialLinearRootBasisWeight :
    Fin r ⊕ {p : Fin (r + 1) × Fin (r + 1) // p.1 ≠ p.2} →
      Dual A (specialLinearDiagonalCartan r A) :=
  Sum.elim 0 fun p => specialLinearEpsilon r A p.val.1 - specialLinearEpsilon r A p.val.2

/-- The simple coroots have weight `0`. -/
@[simp]
theorem specialLinearRootBasisWeight_inl (i : Fin r) :
    specialLinearRootBasisWeight (A := A) (.inl i) = 0 :=
  (rfl)

/-- The signed matrix unit `Eᵢⱼ` has the root `εᵢ - εⱼ` as weight. -/
@[simp]
theorem specialLinearRootBasisWeight_inr (p : {p : Fin (r + 1) × Fin (r + 1) // p.1 ≠ p.2}) :
    specialLinearRootBasisWeight (.inr p) =
      specialLinearEpsilon r A p.val.1 - specialLinearEpsilon r A p.val.2 :=
  (rfl)

/-- The diagonal Cartan subalgebra acts on each vector of `specialLinearRootBasis` by its weight. -/
theorem lie_specialLinearDiagonalCartan_specialLinearRootBasis
    (h : specialLinearDiagonalCartan r A)
    (p : Fin r ⊕ {p : Fin (r + 1) × Fin (r + 1) // p.1 ≠ p.2}) :
    ⁅h, specialLinearRootBasis r A p⁆ =
      specialLinearRootBasisWeight p h • specialLinearRootBasis r A p := by
  rw [LieSubalgebra.coe_bracket_of_module]
  rcases p with i | p
  · rw [specialLinearRootBasis_inl]
    have h0 : ⁅h, specialLinearDiagonalCartanBasis r A i⁆ = 0 := trivial_lie_zero _ _ _ _
    simpa using congrArg Subtype.val h0
  · have hd : (h : Matrix (Fin (r + 1)) (Fin (r + 1)) A) ∈ diagonalCartan A (Fin (r + 1)) :=
      mem_diagonalCartan_iff_isDiag.mpr ((mem_specialLinearDiagonalCartan_iff r A _).mp h.property)
    rw [specialLinearRootBasis_inr]
    apply Subtype.ext
    rw [LieSubalgebra.coe_bracket, specialLinearSignedRoot_val, SetLike.val_smul,
      specialLinearSignedRoot_val, lie_single_of_mem_diagonalCartan hd]
    simp [specialLinearRootBasisWeight]

end WeightVectors

/-! ### Formal characters -/

section Characters

variable (r : ℕ) (K : Type*) [Field K]

/-- **The formal character of the standard module** of `sl (Fin (r + 1)) K`: its weights are the
coordinate weights `εₖ`, one for each basis vector `eₖ`. In positive characteristic distinct `εₖ`
can coincide (for `r = 1` and `2 = 0`), and then their multiplicities add. -/
theorem formalCharacter_specialLinear_pi :
    formalCharacter K (specialLinearDiagonalCartan r K) (Fin (r + 1) → K) =
      ∑ k, AddMonoidAlgebra.single (specialLinearEpsilon r K k) (1 : ℤ) := by
  apply (Pi.basisFun K (Fin (r + 1))).formalCharacter_eq_sum_single_of_weight_basis
  intro k h
  simpa using lie_specialLinearDiagonalCartan_pi_single h k

/-- The dual basis of the standard basis consists of weight vectors of weights `-εₖ`. -/
private theorem lie_specialLinearDiagonalCartan_dualBasis (h : specialLinearDiagonalCartan r K)
    (k : Fin (r + 1)) :
    ⁅h, (Pi.basisFun K (Fin (r + 1))).dualBasis k⁆ =
      (-specialLinearEpsilon r K k) h • (Pi.basisFun K (Fin (r + 1))).dualBasis k := by
  have hk : (Pi.basisFun K (Fin (r + 1))).dualBasis k = LinearMap.proj k := by
    ext v
    simp
  rw [hk, LinearMap.neg_apply]
  exact lie_specialLinearDiagonalCartan_proj h k

/-- **The formal character of the dual standard module** of `sl (Fin (r + 1)) K`: its weights are
the negated coordinate weights `-εₖ`, one for each coordinate functional. In positive
characteristic distinct `-εₖ` can coincide (for `r = 1` and `2 = 0`), and then their multiplicities
add. -/
theorem formalCharacter_specialLinear_dual :
    formalCharacter K (specialLinearDiagonalCartan r K) (Dual K (Fin (r + 1) → K)) =
      ∑ k, AddMonoidAlgebra.single (-specialLinearEpsilon r K k) (1 : ℤ) := by
  apply (Pi.basisFun K (Fin (r + 1))).dualBasis.formalCharacter_eq_sum_single_of_weight_basis
  exact fun k h => lie_specialLinearDiagonalCartan_dualBasis r K h k

/-- **The formal character of the adjoint module** of `sl (Fin (r + 1)) K`: the weight `0`
contributes once for each simple coroot, and each root `εᵢ - εⱼ` with `i ≠ j` once. -/
theorem formalCharacter_specialLinear_adjoint :
    formalCharacter K (specialLinearDiagonalCartan r K) (sl (Fin (r + 1)) K) =
      r • AddMonoidAlgebra.single 0 (1 : ℤ) +
        ∑ p : {p : Fin (r + 1) × Fin (r + 1) // p.1 ≠ p.2},
          AddMonoidAlgebra.single
            (specialLinearEpsilon r K p.val.1 - specialLinearEpsilon r K p.val.2) (1 : ℤ) := by
  rw [(specialLinearRootBasis r K).formalCharacter_eq_sum_single_of_weight_basis
    (μ := specialLinearRootBasisWeight) fun p h =>
      lie_specialLinearDiagonalCartan_specialLinearRootBasis h p,
    Fintype.sum_sum_type]
  simp [specialLinearRootBasisWeight]

/-- The weight diagram of the standard module: the coordinate weights. -/
theorem coe_support_formalCharacter_specialLinear_pi :
    ((formalCharacter K (specialLinearDiagonalCartan r K) (Fin (r + 1) → K)).coeff.support :
      Set (Dual K (specialLinearDiagonalCartan r K))) = Set.range (specialLinearEpsilon r K) :=
  (Pi.basisFun K (Fin (r + 1))).coe_support_formalCharacter_of_weight_basis fun k h => by
    simpa using lie_specialLinearDiagonalCartan_pi_single h k

/-- The weight diagram of the dual standard module: the negated coordinate weights. -/
theorem coe_support_formalCharacter_specialLinear_dual :
    ((formalCharacter K (specialLinearDiagonalCartan r K)
      (Dual K (Fin (r + 1) → K))).coeff.support :
      Set (Dual K (specialLinearDiagonalCartan r K))) = Set.range (-specialLinearEpsilon r K) :=
  (Pi.basisFun K (Fin (r + 1))).dualBasis.coe_support_formalCharacter_of_weight_basis
    fun k h => lie_specialLinearDiagonalCartan_dualBasis r K h k

/-- The weight diagram of the adjoint module in positive rank: the weight `0` together with the
roots `εᵢ - εⱼ`. -/
theorem coe_support_formalCharacter_specialLinear_adjoint (hr : r ≠ 0) :
    ((formalCharacter K (specialLinearDiagonalCartan r K) (sl (Fin (r + 1)) K)).coeff.support :
      Set (Dual K (specialLinearDiagonalCartan r K))) =
      insert 0 (Set.range fun p : {p : Fin (r + 1) × Fin (r + 1) // p.1 ≠ p.2} =>
        specialLinearEpsilon r K p.val.1 - specialLinearEpsilon r K p.val.2) := by
  rw [(specialLinearRootBasis r K).coe_support_formalCharacter_of_weight_basis
    (μ := specialLinearRootBasisWeight) fun p h =>
      lie_specialLinearDiagonalCartan_specialLinearRootBasis h p]
  have : Nonempty (Fin r) := ⟨⟨0, Nat.pos_of_ne_zero hr⟩⟩
  ext χ
  simp [Sum.exists, eq_comm]

/-- **The weight `0` of the adjoint module has multiplicity the rank**, unless `r = 1` and
`2 = 0`. Then no root `εᵢ - εⱼ` vanishes, so only the `r` simple coroots have weight `0`: in rank
at least two the root takes the value `1` on `Eᵢᵢ - Eₖₖ` for a third index `k`, and once `2 ≠ 0` it
takes the value `2` on `Eᵢᵢ - Eⱼⱼ`. For `sl₂` with `2 = 0` the root `ε₀ - ε₁` vanishes and the
weight `0` has multiplicity `3`. -/
theorem coeff_formalCharacter_specialLinear_adjoint_zero (hr : r ≠ 1 ∨ (2 : K) ≠ 0) :
    (formalCharacter K (specialLinearDiagonalCartan r K) (sl (Fin (r + 1)) K)).coeff 0 = r := by
  classical
  have hroot (p : {p : Fin (r + 1) × Fin (r + 1) // p.1 ≠ p.2}) :
      specialLinearEpsilon r K p.val.1 - specialLinearEpsilon r K p.val.2 ≠ 0 := by
    obtain ⟨⟨i, j⟩, hij⟩ := p
    intro h
    rcases hr with hr | h2
    · obtain ⟨k, hki, hkj⟩ : ∃ k : Fin (r + 1), k ≠ i ∧ k ≠ j := by
        refine Fin.exists_ne_and_ne_of_two_lt i j ?_
        have : r ≠ 0 := by
          rintro rfl
          exact hij (Fin.ext (by have := i.isLt; have := j.isLt; omega))
        omega
      have hmem : singleSubSingle i k (1 : K) ∈ specialLinearDiagonalCartan r K :=
        (mem_specialLinearDiagonalCartan_iff r K _).mpr
          ((mem_specialLinearDiagonal_iff r K _).mp
            (singleSubSingle_mem_specialLinearDiagonal r K _ _ _))
      have h1 := LinearMap.congr_fun h ⟨_, hmem⟩
      simp [val_singleSubSingle, hij, hki, hkj] at h1
    · have hmem : singleSubSingle i j (1 : K) ∈ specialLinearDiagonalCartan r K :=
        (mem_specialLinearDiagonalCartan_iff r K _).mpr
          ((mem_specialLinearDiagonal_iff r K _).mp
            (singleSubSingle_mem_specialLinearDiagonal r K _ _ _))
      have h2' := LinearMap.congr_fun h ⟨_, hmem⟩
      norm_num [val_singleSubSingle, hij, Ne.symm hij] at h2'
      exact h2 h2'
  rw [formalCharacter_specialLinear_adjoint]
  simp [AddMonoidAlgebra.coeff_sum, AddMonoidAlgebra.coeff_single, hroot]

end Characters

/-! ### The weight diagrams of `sl₃`

For `r = 2` the two fundamental weights are written `ω₀` and `ω₁` (zero-based). In
characteristic zero the standard module, its dual and the adjoint module are the irreducible
modules classically denoted `V(ω₀)`, `V(ω₁)` and `V(ω₀ + ω₁)`; the statements below compute their
characters and supports directly, over any field. In characteristic `2` or `3` some of the six
roots coincide, as explained in the module docstring.
-/

section SlThreeWeights

variable (A : Type*) [CommRing A]

/-- The coordinate weights of `sl₃` in terms of the fundamental weights: `ε₀ = ω₀`. -/
theorem specialLinearEpsilon_two_zero :
    specialLinearEpsilon 2 A 0 = specialLinearFundamentalWeight 2 A 0 := by
  refine (specialLinearDiagonalCartanBasis _ _).ext fun j => ?_
  rw [specialLinearEpsilon_apply_specialLinearDiagonalCartanBasis,
    specialLinearFundamentalWeight_apply_specialLinearDiagonalCartanBasis]
  fin_cases j <;> simp

/-- The coordinate weights of `sl₃` in terms of the fundamental weights: `ε₁ = ω₁ - ω₀`. -/
theorem specialLinearEpsilon_two_one :
    specialLinearEpsilon 2 A 1 =
      specialLinearFundamentalWeight 2 A 1 - specialLinearFundamentalWeight 2 A 0 := by
  refine (specialLinearDiagonalCartanBasis _ _).ext fun j => ?_
  rw [specialLinearEpsilon_apply_specialLinearDiagonalCartanBasis, LinearMap.sub_apply,
    specialLinearFundamentalWeight_apply_specialLinearDiagonalCartanBasis,
    specialLinearFundamentalWeight_apply_specialLinearDiagonalCartanBasis]
  fin_cases j <;> simp

/-- The coordinate weights of `sl₃` in terms of the fundamental weights: `ε₂ = -ω₁`. -/
theorem specialLinearEpsilon_two_two :
    specialLinearEpsilon 2 A 2 = -specialLinearFundamentalWeight 2 A 1 := by
  refine (specialLinearDiagonalCartanBasis _ _).ext fun j => ?_
  rw [specialLinearEpsilon_apply_specialLinearDiagonalCartanBasis, LinearMap.neg_apply,
    specialLinearFundamentalWeight_apply_specialLinearDiagonalCartanBasis]
  fin_cases j <;> simp

/-- A root of `sl₃` in fundamental-weight coordinates: `ε₀ - ε₁ = 2ω₀ - ω₁`. -/
private theorem specialLinearEpsilon_two_zero_sub_one :
    specialLinearEpsilon 2 A 0 - specialLinearEpsilon 2 A 1 =
      2 • specialLinearFundamentalWeight 2 A 0 - specialLinearFundamentalWeight 2 A 1 := by
  rw [specialLinearEpsilon_two_zero, specialLinearEpsilon_two_one, two_nsmul]
  abel

/-- A root of `sl₃` in fundamental-weight coordinates: `ε₁ - ε₂ = 2ω₁ - ω₀`. -/
private theorem specialLinearEpsilon_two_one_sub_two :
    specialLinearEpsilon 2 A 1 - specialLinearEpsilon 2 A 2 =
      2 • specialLinearFundamentalWeight 2 A 1 - specialLinearFundamentalWeight 2 A 0 := by
  rw [specialLinearEpsilon_two_one, specialLinearEpsilon_two_two, two_nsmul]
  abel

/-- A root of `sl₃` in fundamental-weight coordinates: `ε₀ - ε₂ = ω₀ + ω₁`. -/
private theorem specialLinearEpsilon_two_zero_sub_two :
    specialLinearEpsilon 2 A 0 - specialLinearEpsilon 2 A 2 =
      specialLinearFundamentalWeight 2 A 0 + specialLinearFundamentalWeight 2 A 1 := by
  rw [specialLinearEpsilon_two_zero, specialLinearEpsilon_two_two, sub_neg_eq_add]

/-- The negative root `ε₁ - ε₀ = -(2ω₀ - ω₁)` of `sl₃`. -/
private theorem specialLinearEpsilon_two_one_sub_zero :
    specialLinearEpsilon 2 A 1 - specialLinearEpsilon 2 A 0 =
      -(2 • specialLinearFundamentalWeight 2 A 0 - specialLinearFundamentalWeight 2 A 1) := by
  rw [← specialLinearEpsilon_two_zero_sub_one, neg_sub]

/-- The negative root `ε₂ - ε₁ = -(2ω₁ - ω₀)` of `sl₃`. -/
private theorem specialLinearEpsilon_two_two_sub_one :
    specialLinearEpsilon 2 A 2 - specialLinearEpsilon 2 A 1 =
      -(2 • specialLinearFundamentalWeight 2 A 1 - specialLinearFundamentalWeight 2 A 0) := by
  rw [← specialLinearEpsilon_two_one_sub_two, neg_sub]

/-- The negative root `ε₂ - ε₀ = -(ω₀ + ω₁)` of `sl₃`. -/
private theorem specialLinearEpsilon_two_two_sub_zero :
    specialLinearEpsilon 2 A 2 - specialLinearEpsilon 2 A 0 =
      -(specialLinearFundamentalWeight 2 A 0 + specialLinearFundamentalWeight 2 A 1) := by
  rw [← specialLinearEpsilon_two_zero_sub_two, neg_sub]

end SlThreeWeights

section SlThree

variable (K : Type*) [Field K]

/-- **The character of the standard module of `sl₃`**, classically `V(ω₀)`: the three weights
`ω₀, ω₁ - ω₀, -ω₁`, each with multiplicity one. -/
theorem formalCharacter_slThree_pi :
    formalCharacter K (specialLinearDiagonalCartan 2 K) (Fin 3 → K) =
      AddMonoidAlgebra.single (specialLinearFundamentalWeight 2 K 0) (1 : ℤ) +
        AddMonoidAlgebra.single
          (specialLinearFundamentalWeight 2 K 1 - specialLinearFundamentalWeight 2 K 0) 1 +
        AddMonoidAlgebra.single (-specialLinearFundamentalWeight 2 K 1) 1 := by
  rw [formalCharacter_specialLinear_pi, Fin.sum_univ_three, specialLinearEpsilon_two_zero,
    specialLinearEpsilon_two_one, specialLinearEpsilon_two_two]

/-- **The character of the dual standard module of `sl₃`**, classically `V(ω₁)`: the three weights
`-ω₀, ω₀ - ω₁, ω₁`, each with multiplicity one. -/
theorem formalCharacter_slThree_dual :
    formalCharacter K (specialLinearDiagonalCartan 2 K) (Dual K (Fin 3 → K)) =
      AddMonoidAlgebra.single (-specialLinearFundamentalWeight 2 K 0) (1 : ℤ) +
        AddMonoidAlgebra.single
          (specialLinearFundamentalWeight 2 K 0 - specialLinearFundamentalWeight 2 K 1) 1 +
        AddMonoidAlgebra.single (specialLinearFundamentalWeight 2 K 1) 1 := by
  rw [formalCharacter_specialLinear_dual, Fin.sum_univ_three, specialLinearEpsilon_two_zero,
    specialLinearEpsilon_two_one, specialLinearEpsilon_two_two, neg_sub, neg_neg]

/-- **The character of the adjoint module of `sl₃`**, in characteristic zero `V(ω₀ + ω₁)`: the
weight `0` twice, from the two simple coroots, and the six roots `±α₀, ±α₁` and `±(α₀ + α₁)` once
each, where `α₀ = 2ω₀ - ω₁` and `α₁ = 2ω₁ - ω₀` are the simple roots and `α₀ + α₁ = ω₀ + ω₁` is the
highest root. When `2 ≠ 0` and `3 ≠ 0` the six roots are distinct and form a hexagon; otherwise
some coincide and their multiplicities add. -/
theorem formalCharacter_slThree_adjoint :
    formalCharacter K (specialLinearDiagonalCartan 2 K) (sl (Fin 3) K) =
      2 • AddMonoidAlgebra.single 0 (1 : ℤ) +
        AddMonoidAlgebra.single
          (2 • specialLinearFundamentalWeight 2 K 0 - specialLinearFundamentalWeight 2 K 1) 1 +
        AddMonoidAlgebra.single
          (specialLinearFundamentalWeight 2 K 0 + specialLinearFundamentalWeight 2 K 1) 1 +
        AddMonoidAlgebra.single
          (-(2 • specialLinearFundamentalWeight 2 K 0 - specialLinearFundamentalWeight 2 K 1)) 1 +
        AddMonoidAlgebra.single
          (2 • specialLinearFundamentalWeight 2 K 1 - specialLinearFundamentalWeight 2 K 0) 1 +
        AddMonoidAlgebra.single
          (-(specialLinearFundamentalWeight 2 K 0 + specialLinearFundamentalWeight 2 K 1)) 1 +
        AddMonoidAlgebra.single
          (-(2 • specialLinearFundamentalWeight 2 K 1 - specialLinearFundamentalWeight 2 K 0))
          1 := by
  rw [formalCharacter_specialLinear_adjoint,
    ← Finset.sum_subtype (Finset.univ.filter fun p : Fin (2 + 1) × Fin (2 + 1) => p.1 ≠ p.2)
      (p := fun p => p.1 ≠ p.2) (by simp) fun p =>
        AddMonoidAlgebra.single (specialLinearEpsilon 2 K p.1 - specialLinearEpsilon 2 K p.2) 1,
    Finset.sum_filter, Fintype.sum_prod_type]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, Fin.succ_one_eq_two]
  -- Evaluate the nine tests `i ≠ j` on the literals of `Fin (2 + 1)`.
  simp +decide only [ite_true, ite_false, add_zero, zero_add]
  simp only [specialLinearEpsilon_two_zero_sub_one, specialLinearEpsilon_two_one_sub_two,
    specialLinearEpsilon_two_zero_sub_two, specialLinearEpsilon_two_one_sub_zero,
    specialLinearEpsilon_two_two_sub_one, specialLinearEpsilon_two_two_sub_zero, add_assoc]

/-- **The weight diagram of the standard module of `sl₃`**: the triangle
`ω₀, ω₁ - ω₀, -ω₁`. -/
theorem coe_support_formalCharacter_slThree_pi :
    ((formalCharacter K (specialLinearDiagonalCartan 2 K) (Fin 3 → K)).coeff.support :
      Set (Dual K (specialLinearDiagonalCartan 2 K))) =
      {specialLinearFundamentalWeight 2 K 0,
        specialLinearFundamentalWeight 2 K 1 - specialLinearFundamentalWeight 2 K 0,
        -specialLinearFundamentalWeight 2 K 1} := by
  rw [coe_support_formalCharacter_specialLinear_pi]
  ext χ
  simp only [Set.mem_range, Fin.exists_fin_succ, Fin.succ_zero_eq_one, Fin.succ_one_eq_two,
    IsEmpty.exists_iff, or_false, specialLinearEpsilon_two_zero, specialLinearEpsilon_two_one,
    specialLinearEpsilon_two_two, Set.mem_insert_iff, Set.mem_singleton_iff]
  simp only [eq_comm]

/-- **The weight diagram of the dual standard module of `sl₃`**: the triangle
`-ω₀, ω₀ - ω₁, ω₁`. -/
theorem coe_support_formalCharacter_slThree_dual :
    ((formalCharacter K (specialLinearDiagonalCartan 2 K) (Dual K (Fin 3 → K))).coeff.support :
      Set (Dual K (specialLinearDiagonalCartan 2 K))) =
      {-specialLinearFundamentalWeight 2 K 0,
        specialLinearFundamentalWeight 2 K 0 - specialLinearFundamentalWeight 2 K 1,
        specialLinearFundamentalWeight 2 K 1} := by
  rw [coe_support_formalCharacter_specialLinear_dual]
  ext χ
  simp only [Set.mem_range, Fin.exists_fin_succ, Fin.succ_zero_eq_one, Fin.succ_one_eq_two,
    IsEmpty.exists_iff, or_false, Pi.neg_apply, specialLinearEpsilon_two_zero,
    specialLinearEpsilon_two_one, specialLinearEpsilon_two_two, neg_sub, neg_neg,
    Set.mem_insert_iff, Set.mem_singleton_iff]
  simp only [eq_comm]

/-- **The weight diagram of the adjoint module of `sl₃`**: the six roots
`±(2ω₀ - ω₁), ±(2ω₁ - ω₀), ±(ω₀ + ω₁)` together with `0`. When `2 ≠ 0` and `3 ≠ 0` these are
seven distinct points, the hexagon of roots and its centre; in characteristic `2` or `3` some roots
coincide. -/
theorem coe_support_formalCharacter_slThree_adjoint :
    ((formalCharacter K (specialLinearDiagonalCartan 2 K) (sl (Fin 3) K)).coeff.support :
      Set (Dual K (specialLinearDiagonalCartan 2 K))) =
      {0,
        2 • specialLinearFundamentalWeight 2 K 0 - specialLinearFundamentalWeight 2 K 1,
        specialLinearFundamentalWeight 2 K 0 + specialLinearFundamentalWeight 2 K 1,
        -(2 • specialLinearFundamentalWeight 2 K 0 - specialLinearFundamentalWeight 2 K 1),
        2 • specialLinearFundamentalWeight 2 K 1 - specialLinearFundamentalWeight 2 K 0,
        -(specialLinearFundamentalWeight 2 K 0 + specialLinearFundamentalWeight 2 K 1),
        -(2 • specialLinearFundamentalWeight 2 K 1 - specialLinearFundamentalWeight 2 K 0)} := by
  rw [coe_support_formalCharacter_specialLinear_adjoint 2 K two_ne_zero]
  ext χ
  simp only [Set.mem_insert_iff, Set.mem_range, Subtype.exists, Prod.exists, Fin.exists_fin_succ,
    Fin.succ_zero_eq_one, Fin.succ_one_eq_two, IsEmpty.exists_iff, or_false,
    Set.mem_singleton_iff]
  -- Evaluate the nine tests `i ≠ j` on the literals of `Fin (2 + 1)`.
  simp +decide only [exists_const, IsEmpty.exists_iff, false_or,
    or_false]
  simp only [specialLinearEpsilon_two_zero_sub_one, specialLinearEpsilon_two_one_sub_two,
    specialLinearEpsilon_two_zero_sub_two, specialLinearEpsilon_two_one_sub_zero,
    specialLinearEpsilon_two_two_sub_one, specialLinearEpsilon_two_two_sub_zero, or_assoc,
    eq_comm]

/-- **The weight `0` of the adjoint module of `sl₃` has multiplicity two**, over every field: no
root of `sl₃` vanishes, even in characteristic `2`. -/
theorem coeff_formalCharacter_slThree_adjoint_zero :
    (formalCharacter K (specialLinearDiagonalCartan 2 K) (sl (Fin 3) K)).coeff 0 = 2 :=
  coeff_formalCharacter_specialLinear_adjoint_zero 2 K (.inl (by decide))

end SlThree

end TauCeti

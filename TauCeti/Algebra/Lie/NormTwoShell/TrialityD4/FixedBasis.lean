/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.TensorProduct.Basis
public import TauCeti.Algebra.Lie.BaseChange.Hom
public import TauCeti.Algebra.Lie.NormTwoShell.BaseChange
public import TauCeti.Algebra.Lie.NormTwoShell.TrialityD4.Basic
public import TauCeti.Algebra.Lie.Subalgebra.Fixed
public import TauCeti.LinearAlgebra.Matrix.Cartan.Folding.TrialityD4

/-!
# Integral fixed basis and scalar extension for D₄ triality

For the pinned triality action `Matrix.ShellLieAlgebra.reindex trialityPermD4 reindex_cartanMatrix`
on `Matrix.ShellLieAlgebra (CartanMatrix.D 4)`, this file proves that all twelve root cycles have
positive monodromy, constructs the concrete fourteen-element integral basis of the fixed Lie
subring, and proves that scalar extension commutes unconditionally with taking triality fixed points
over every commutative ring.

Specifically:
* `TauCeti.D4Triality.monodromy_eq_one` shows that `Matrix.ShellLieAlgebra.monodromy` equals `1`
  on every root cycle of `D₄` triality, both on the three-element outer orbits and on the fixed
  roots.
* `TauCeti.D4Triality.invariantCartan` embeds the primitive invariant Cartan coordinate vectors
  `TauCeti.D4Triality.invariantCartanVec` (from
  `TauCeti.LinearAlgebra.Matrix.Cartan.Folding.TrialityD4`) into the shell Lie algebra, and
  `TauCeti.D4Triality.fixedBasis` assembles `invariantCartan` and `TauCeti.D4Triality.invariantRoot`
  into a `ℤ`-basis of `trialityLieEquiv.toLieHom.fixedSubalgebra` indexed by
  `Fin 2 ⊕ (Bool × Fin 6)`.
* `TauCeti.D4Triality.fixedSubalgebraBaseChangeLieEquiv` specializes
  `Matrix.ShellLieAlgebra.fixedSubalgebraBaseChangeLieEquiv` to an isomorphism of `A`-Lie algebras
  `A ⊗[ℤ] trialityLieEquiv.toLieHom.fixedSubalgebra ≃ₗ⁅A⁆
  (LieEquiv.baseChange A trialityLieEquiv).toLieHom.fixedSubalgebra` over any commutative ring `A`,
  with no flatness or `2`-torsion hypothesis because no negative-monodromy root cycles occur.

## References

* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Plate IV.
* V. G. Kac, *Infinite dimensional Lie algebras*, third edition, §§7.8--7.9.
-/

public section

open scoped TensorProduct

namespace TauCeti.D4Triality

open _root_.Matrix

/-! ### Positivity and scoped shell instances -/

/-- Positivity of `CartanMatrix.D 4` as a scoped typeclass fact for `Matrix.ShellLieAlgebra`. -/
scoped instance instFactPosDefCartanMatrix : Fact (CartanMatrix.D 4).PosDef :=
  ⟨posDef_cartanMatrix_D 4⟩

/-- Evenness of the diagonal of `CartanMatrix.D 4` as a scoped typeclass fact for
`Matrix.ShellLieAlgebra`. -/
scoped instance instFactEvenDiagCartanMatrix : Fact (∀ i, Even (CartanMatrix.D 4 i i)) :=
  ⟨fun i ↦ by rw [CartanMatrix.D_diag]; exact even_two⟩

/-- Finiteness of the `D₄` norm-two shell as a scoped instance. -/
scoped instance instFiniteNormTwoShell : Finite (CartanMatrix.D 4).normTwoShell :=
  (posDef_cartanMatrix_D 4).finite_normTwoShell

/-! ### Root cycles and positive monodromy -/

/-- Iterates of the triality permutation on the twenty-four roots follow `next` on indices. -/
@[simp]
theorem normTwoShellCongr_pow_root (negative : Bool) (i : Fin 12) (r : ℕ) :
    (normTwoShellCongr reindex_cartanMatrix ^ r) (root negative i) =
      root negative ((next ^ r) i) := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [pow_succ', Equiv.Perm.mul_apply, ih, normTwoShellCongr_root, pow_succ',
      Equiv.Perm.mul_apply]

/-- Two roots lie in the same triality cycle exactly when they have the same sign and orbit. -/
theorem sameCycle_normTwoShellCongr_root_iff (neg₁ neg₂ : Bool) (i j : Fin 12) :
    Equiv.Perm.SameCycle (normTwoShellCongr reindex_cartanMatrix) (root neg₁ i) (root neg₂ j) ↔
      neg₁ = neg₂ ∧ orbit i = orbit j := by
  constructor
  · intro h
    obtain ⟨r, hr⟩ := h.exists_nat_pow_eq
    rw [normTwoShellCongr_pow_root] at hr
    have hinj : (neg₁, (next ^ r) i) = (neg₂, j) :=
      rootEquiv.injective (by simpa only [rootEquiv_apply] using hr)
    rcases Prod.mk.inj hinj with ⟨rfl, hij⟩
    exact ⟨rfl, (sameCycle_next_iff i j).mp ⟨r, hij⟩⟩
  · rintro ⟨rfl, horb⟩
    obtain ⟨r, rfl⟩ := ((sameCycle_next_iff i j).mpr horb).exists_nat_pow_eq
    exact ⟨r, normTwoShellCongr_pow_root neg₁ i r⟩

private theorem existsUnique_sameCycle_rootRepresentative (a : (CartanMatrix.D 4).normTwoShell) :
    ∃! p : Bool × Fin 6,
      Equiv.Perm.SameCycle (normTwoShellCongr reindex_cartanMatrix)
        (root p.1 (representative p.2)) a := by
  obtain ⟨⟨negative, i⟩, rfl⟩ := rootEquiv.surjective a
  rw [rootEquiv_apply]
  refine ⟨(negative, orbit i), ?_, fun ⟨neg', o'⟩ hp ↦ ?_⟩
  · dsimp only
    rw [sameCycle_normTwoShellCongr_root_iff, orbit_representative]
    exact ⟨rfl, rfl⟩
  · dsimp only at hp
    rw [sameCycle_normTwoShellCongr_root_iff, orbit_representative] at hp
    exact Prod.ext hp.1 hp.2

private theorem minimalPeriod_normTwoShellCongr_root (negative : Bool) (i : Fin 12) :
    Function.minimalPeriod (normTwoShellCongr reindex_cartanMatrix) (root negative i) =
      Function.minimalPeriod next i := by
  have hinj : Function.Injective (root negative) := fun j k h ↦
    (Prod.mk.inj (rootEquiv.injective (by simpa only [rootEquiv_apply] using h))).2
  exact Function.minimalPeriod_eq_minimalPeriod_iff.mpr fun n ↦ by
    simp only [Function.IsPeriodicPt, Function.IsFixedPt, ← Equiv.Perm.coe_pow,
      normTwoShellCongr_pow_root, hinj.eq_iff]

private theorem monodromy_root_eq_one (negative : Bool) (i : Fin 12) :
    Equiv.Perm.monodromy (normTwoShellCongr reindex_cartanMatrix)
      (fun a ↦ inversionSign (CartanMatrix.D 4) trialityPermD4 a) (root negative i) = 1 := by
  rw [Equiv.Perm.monodromy_def, Equiv.Perm.cycleCoeff_def, minimalPeriod_normTwoShellCongr_root]
  have hpow : (next ^ 3) i = i := by decide +revert
  have hdvd : Function.minimalPeriod next i ∣ 3 :=
    Function.IsPeriodicPt.minimalPeriod_dvd
      (by simpa only [Function.IsPeriodicPt, Function.IsFixedPt, ← Equiv.Perm.coe_pow] using hpow)
  rcases Nat.Prime.eq_one_or_self_of_dvd Nat.prime_three _ hdvd with h1 | h3
  · rw [h1, Finset.prod_range_one, pow_zero, Equiv.Perm.one_apply, inversionSign_root]
    have hfix : next i = i := Function.minimalPeriod_eq_one_iff_isFixedPt.mp h1
    revert hfix
    fin_cases i <;> decide
  · rw [h3, Finset.prod_range_succ, Finset.prod_range_succ, Finset.prod_range_one]
    simp only [pow_zero, pow_one, pow_two, Equiv.Perm.one_apply,
      Equiv.Perm.mul_apply, normTwoShellCongr_root, inversionSign_root]
    exact rootSign_cycle i

/-- Every root cycle of the pinned `D₄` triality action has monodromy `1`. -/
@[simp]
theorem monodromy_eq_one
    (C : Quotient (Equiv.Perm.SameCycle.setoid (normTwoShellCongr reindex_cartanMatrix))) :
    ShellLieAlgebra.monodromy trialityPermD4 reindex_cartanMatrix C = 1 := by
  obtain ⟨⟨negative, i⟩, h⟩ := rootEquiv.surjective C.out
  rw [ShellLieAlgebra.monodromy_def, ShellLieAlgebra.cycleCoeff_def, ← h, rootEquiv_apply]
  simpa only [Equiv.Perm.monodromy_def, Equiv.Perm.cycleCoeff_def] using
    monodromy_root_eq_one negative i

/-- No root cycle of `D₄` triality has negative monodromy. -/
scoped instance instIsEmptyNegativeRootCycle :
    IsEmpty {C : Quotient (Equiv.Perm.SameCycle.setoid (normTwoShellCongr reindex_cartanMatrix)) //
      ShellLieAlgebra.monodromy trialityPermD4 reindex_cartanMatrix C = -1} :=
  ⟨fun ⟨C, hC⟩ ↦ by simp at hC⟩

/-! ### Triality Lie automorphism and invariant Cartan vectors -/

/-- The pinned `D₄` triality action as an automorphism of the integral shell Lie algebra. -/
noncomputable def trialityLieEquiv :
    ShellLieAlgebra (CartanMatrix.D 4) ≃ₗ⁅ℤ⁆ ShellLieAlgebra (CartanMatrix.D 4) :=
  ShellLieAlgebra.reindexLieEquiv trialityPermD4 reindex_cartanMatrix Fact.out Fact.out

@[simp]
theorem trialityLieEquiv_apply (x : ShellLieAlgebra (CartanMatrix.D 4)) :
    trialityLieEquiv x = ShellLieAlgebra.reindex trialityPermD4 reindex_cartanMatrix x :=
  ShellLieAlgebra.reindexLieEquiv_apply _ _ _ _ x

@[simp]
theorem toLinearEquiv_trialityLieEquiv :
    trialityLieEquiv.toLinearEquiv =
      ShellLieAlgebra.reindex trialityPermD4 reindex_cartanMatrix :=
  LinearEquiv.ext trialityLieEquiv_apply

private theorem toSubmodule_fixedSubalgebra :
    trialityLieEquiv.toLieHom.fixedSubalgebra.toSubmodule =
      (ShellLieAlgebra.reindex trialityPermD4 reindex_cartanMatrix).toLinearMap.fixedSubmodule :=
  ShellLieAlgebra.toSubmodule_fixedSubalgebra_reindexLieEquiv trialityPermD4 reindex_cartanMatrix

/-- The two `trialityPermD4`-invariant Cartan basis vectors in
`Matrix.ShellLieAlgebra (CartanMatrix.D 4)`. -/
noncomputable def invariantCartan (k : Fin 2) : ShellLieAlgebra (CartanMatrix.D 4) :=
  ShellLieAlgebra.cartan (CartanMatrix.D 4) (invariantCartanVec k)

theorem invariantCartan_def (k : Fin 2) :
    invariantCartan k = ShellLieAlgebra.cartan (CartanMatrix.D 4) (invariantCartanVec k) :=
  (rfl)

/-- Each `invariantCartan k` is the sum of the simple Cartan vectors over vertex orbit `k`. -/
theorem invariantCartan_eq_sum (k : Fin 2) :
    invariantCartan k =
      ∑ i : Fin 4 with vertexOrbit i = k,
        ShellLieAlgebra.cartan (CartanMatrix.D 4) (Pi.single i 1) := by
  rw [invariantCartan_def, ← map_sum]
  congr 1
  ext j
  fin_cases k <;> fin_cases j <;> decide

@[simp]
theorem reindex_invariantCartan (k : Fin 2) :
    ShellLieAlgebra.reindex trialityPermD4 reindex_cartanMatrix (invariantCartan k) =
      invariantCartan k := by
  rw [invariantCartan_def, ShellLieAlgebra.reindex_cartan,
    invariantCartanVec_comp_trialityPermD4_symm]

@[simp]
theorem basis_repr_invariantCartan_inl (k : Fin 2) (i : Fin 4) :
    (ShellLieAlgebra.basis (CartanMatrix.D 4)).repr (invariantCartan k) (.inl i) =
      invariantCartanVec k i := by
  rw [invariantCartan_def, ShellLieAlgebra.basis_repr_cartan_inl]

@[simp]
theorem basis_repr_invariantCartan_inr (k : Fin 2) (a : (CartanMatrix.D 4).normTwoShell) :
    (ShellLieAlgebra.basis (CartanMatrix.D 4)).repr (invariantCartan k) (.inr a) = 0 := by
  rw [invariantCartan_def, ShellLieAlgebra.basis_repr_cartan_inr]

/-! ### The concrete 14-element integral fixed basis -/

private theorem existsUnique_sameCycle_vertexRepresentative (i : Fin 4) :
    ∃! k : Fin 2, trialityPermD4.SameCycle (vertexRepresentative k) i := by
  refine ⟨vertexOrbit i, ?_, fun k hk ↦ ?_⟩
  · dsimp only
    rw [sameCycle_trialityPermD4_iff, vertexOrbit_vertexRepresentative]
  · dsimp only at hk
    rwa [sameCycle_trialityPermD4_iff, vertexOrbit_vertexRepresentative] at hk

private noncomputable abbrev fixedBasisRep :
    Fin 2 ⊕ (Bool × Fin 6) → Fin 4 ⊕ (CartanMatrix.D 4).normTwoShell :=
  Sum.map vertexRepresentative fun p ↦ root p.1 (representative p.2)

private theorem existsUnique_sameCycle_fixedBasisRep
    (x : Fin 4 ⊕ (CartanMatrix.D 4).normTwoShell) :
    ∃! j : Fin 2 ⊕ (Bool × Fin 6),
      (Equiv.Perm.sumCongr trialityPermD4 (normTwoShellCongr reindex_cartanMatrix)).SameCycle
        (fixedBasisRep j) x :=
  Equiv.Perm.existsUnique_sameCycle_sumCongr existsUnique_sameCycle_vertexRepresentative
    existsUnique_sameCycle_rootRepresentative x

private theorem monodromy_fixedBasisRep (j : Fin 2 ⊕ (Bool × Fin 6)) :
    (Equiv.Perm.sumCongr trialityPermD4 (normTwoShellCongr reindex_cartanMatrix)).monodromy
      (Sum.elim (1 : Fin 4 → ℤˣ) (fun a ↦ inversionSign (CartanMatrix.D 4) trialityPermD4 a))
      (fixedBasisRep j) = 1 := by
  rcases j with k | ⟨negative, o⟩
  · simp [fixedBasisRep]
  · dsimp only [fixedBasisRep, Sum.map_inr]
    rw [Equiv.Perm.monodromy_sumCongr_inr]
    exact monodromy_root_eq_one negative (representative o)

/-- **The concrete fourteen-element integral basis of the `D₄` triality fixed Lie subring**,
sending `.inl k` to the Cartan orbit sum `invariantCartan k` (`k : Fin 2`) and
`.inr (negative, o)` to the signed root orbit sum `invariantRoot negative o`
(`negative : Bool`, `o : Fin 6`). -/
noncomputable def fixedBasis :
    Module.Basis (Fin 2 ⊕ (Bool × Fin 6)) ℤ trialityLieEquiv.toLieHom.fixedSubalgebra :=
  (((ShellLieAlgebra.basis (CartanMatrix.D 4)).fixedBasisSignedPerm
    (Equiv.Perm.sumCongr trialityPermD4 (normTwoShellCongr reindex_cartanMatrix))
    (Sum.elim (1 : Fin 4 → ℤˣ) (fun a ↦ inversionSign (CartanMatrix.D 4) trialityPermD4 a))
    (ShellLieAlgebra.reindex trialityPermD4 reindex_cartanMatrix).toLinearMap
    (ShellLieAlgebra.reindex_basis trialityPermD4 reindex_cartanMatrix)
    fixedBasisRep existsUnique_sameCycle_fixedBasisRep).reindex
    (Equiv.subtypeUnivEquiv monodromy_fixedBasisRep)).map
    (LinearEquiv.ofEq _ _ toSubmodule_fixedSubalgebra.symm)

private theorem coe_ofEq_toSubmodule_fixedSubalgebra_symm
    (v : trialityLieEquiv.toLieHom.fixedSubalgebra) :
    (((LinearEquiv.ofEq _ _ toSubmodule_fixedSubalgebra.symm).symm v :
        (ShellLieAlgebra.reindex trialityPermD4 reindex_cartanMatrix).toLinearMap.fixedSubmodule) :
        ShellLieAlgebra (CartanMatrix.D 4)) = v := by
  rw [LinearEquiv.ofEq_symm, LinearEquiv.coe_ofEq_apply]

/-- Coordinate of a fixed vector at Cartan orbit `k` is its ambient Cartan coordinate at
`vertexRepresentative k`. -/
@[simp]
theorem fixedBasis_repr_inl (v : trialityLieEquiv.toLieHom.fixedSubalgebra) (k : Fin 2) :
    fixedBasis.repr v (.inl k) =
      (ShellLieAlgebra.basis (CartanMatrix.D 4)).repr v (.inl (vertexRepresentative k)) := by
  simp [fixedBasis, fixedBasisRep, coe_ofEq_toSubmodule_fixedSubalgebra_symm v]

/-- Coordinate of a fixed vector at signed root orbit `(negative, o)` is its ambient root
coordinate at `root negative (representative o)`. -/
@[simp]
theorem fixedBasis_repr_inr (v : trialityLieEquiv.toLieHom.fixedSubalgebra)
    (negative : Bool) (o : Fin 6) :
    fixedBasis.repr v (.inr (negative, o)) =
      (ShellLieAlgebra.basis (CartanMatrix.D 4)).repr v
        (.inr (root negative (representative o))) := by
  simp [fixedBasis, fixedBasisRep, coe_ofEq_toSubmodule_fixedSubalgebra_symm v]

@[simp]
theorem coe_fixedBasis_inl (k : Fin 2) :
    (fixedBasis (.inl k) : ShellLieAlgebra (CartanMatrix.D 4)) = invariantCartan k := by
  suffices fixedBasis (.inl k) =
      ⟨invariantCartan k, by simp⟩ from
    congrArg Subtype.val this
  refine fixedBasis.repr.injective (Finsupp.ext fun j ↦ ?_)
  rw [Module.Basis.repr_self, Finsupp.single_apply]
  rcases j with k' | ⟨neg', o'⟩
  · rw [fixedBasis_repr_inl]
    simp only [Sum.inl.injEq, basis_repr_invariantCartan_inl]
    fin_cases k <;> fin_cases k' <;> decide
  · simp

@[simp]
theorem coe_fixedBasis_inr (negative : Bool) (o : Fin 6) :
    (fixedBasis (.inr (negative, o)) : ShellLieAlgebra (CartanMatrix.D 4)) =
      invariantRoot negative o := by
  suffices fixedBasis (.inr (negative, o)) =
      ⟨invariantRoot negative o, by simp⟩ from
    congrArg Subtype.val this
  refine fixedBasis.repr.injective (Finsupp.ext fun j ↦ ?_)
  rw [Module.Basis.repr_self, Finsupp.single_apply]
  rcases j with k' | ⟨neg', o'⟩
  · simp
  · rw [fixedBasis_repr_inr]
    simp only [Sum.inr.injEq, Prod.mk.injEq, basis_repr_invariantRoot, orbit_representative,
      orbitCoeff_representative, eq_comm (a := o')]

/-- The integral fixed Lie subring of `D₄` triality has rank `14`. -/
theorem finrank_fixedSubalgebra :
    Module.finrank ℤ trialityLieEquiv.toLieHom.fixedSubalgebra = 14 := by
  rw [Module.finrank_eq_card_basis fixedBasis]
  decide

/-! ### Unconditional scalar extension of the fixed Lie subalgebra -/

/-- Canonical scalar-extension `ℤ`-Lie homomorphism from the integral `D₄` triality-fixed Lie
subring to the fixed Lie subalgebra after scalar extension to `A`, sending `v` to `1 ⊗ₜ[ℤ] v`. -/
noncomputable def toFixedSubalgebraBaseChange (A : Type*) [CommRing A] :
    trialityLieEquiv.toLieHom.fixedSubalgebra →ₗ⁅ℤ⁆
      (LieEquiv.baseChange A trialityLieEquiv).toLieHom.fixedSubalgebra :=
  ShellLieAlgebra.toFixedSubalgebraBaseChange trialityPermD4 reindex_cartanMatrix A

@[simp]
theorem coe_toFixedSubalgebraBaseChange (A : Type*) [CommRing A]
    (v : trialityLieEquiv.toLieHom.fixedSubalgebra) :
    ((toFixedSubalgebraBaseChange A v :
        (LieEquiv.baseChange A trialityLieEquiv).toLieHom.fixedSubalgebra) :
        A ⊗[ℤ] ShellLieAlgebra (CartanMatrix.D 4)) =
      1 ⊗ₜ[ℤ] (v : ShellLieAlgebra (CartanMatrix.D 4)) :=
  ShellLieAlgebra.coe_toFixedSubalgebraBaseChange trialityPermD4 reindex_cartanMatrix A v

/-- Over every commutative ring `A`, `toFixedSubalgebraBaseChange A` exhibits the triality-fixed
Lie subalgebra after scalar extension as the base change of the integral fixed Lie subring. -/
theorem isBaseChange_toFixedSubalgebraBaseChange (A : Type*) [CommRing A] :
    IsBaseChange A (toFixedSubalgebraBaseChange A).toLinearMap :=
  ShellLieAlgebra.isBaseChange_toFixedSubalgebraBaseChange
    trialityPermD4 reindex_cartanMatrix A (Or.inl inferInstance)

/-- Over every commutative ring `A`, the scalar extension of the integral triality-fixed Lie
subring maps isomorphically as an `A`-Lie algebra onto the fixed Lie subalgebra of the
scalar-extended triality automorphism, with no flatness or `2`-torsion hypothesis. -/
noncomputable def fixedSubalgebraBaseChangeLieEquiv (A : Type*) [CommRing A] :
    A ⊗[ℤ] trialityLieEquiv.toLieHom.fixedSubalgebra ≃ₗ⁅A⁆
      (LieEquiv.baseChange A trialityLieEquiv).toLieHom.fixedSubalgebra :=
  ShellLieAlgebra.fixedSubalgebraBaseChangeLieEquiv
    trialityPermD4 reindex_cartanMatrix A (Or.inl inferInstance)

theorem fixedSubalgebraBaseChangeLieEquiv_tmul (A : Type*) [CommRing A] (a : A)
    (v : trialityLieEquiv.toLieHom.fixedSubalgebra) :
    fixedSubalgebraBaseChangeLieEquiv A (a ⊗ₜ[ℤ] v) =
      a • toFixedSubalgebraBaseChange A v :=
  ShellLieAlgebra.fixedSubalgebraBaseChangeLieEquiv_tmul
    trialityPermD4 reindex_cartanMatrix A (Or.inl inferInstance) a v

@[simp]
theorem coe_fixedSubalgebraBaseChangeLieEquiv_tmul (A : Type*) [CommRing A] (a : A)
    (v : trialityLieEquiv.toLieHom.fixedSubalgebra) :
    ((fixedSubalgebraBaseChangeLieEquiv A (a ⊗ₜ[ℤ] v) :
        (LieEquiv.baseChange A trialityLieEquiv).toLieHom.fixedSubalgebra) :
        A ⊗[ℤ] ShellLieAlgebra (CartanMatrix.D 4)) =
      a ⊗ₜ[ℤ] (v : ShellLieAlgebra (CartanMatrix.D 4)) :=
  ShellLieAlgebra.coe_fixedSubalgebraBaseChangeLieEquiv_tmul
    trialityPermD4 reindex_cartanMatrix A (Or.inl inferInstance) a v

/-- Explicit fourteen-element `A`-basis of the triality-fixed Lie subalgebra after extension of
scalars to any commutative ring `A`. -/
noncomputable def fixedSubalgebraBaseChangeBasis (A : Type*) [CommRing A] :
    Module.Basis (Fin 2 ⊕ (Bool × Fin 6)) A
      (LieEquiv.baseChange A trialityLieEquiv).toLieHom.fixedSubalgebra :=
  (fixedBasis.baseChange A).map (fixedSubalgebraBaseChangeLieEquiv A).toLinearEquiv

theorem fixedSubalgebraBaseChangeBasis_apply (A : Type*) [CommRing A]
    (idx : Fin 2 ⊕ (Bool × Fin 6)) :
    fixedSubalgebraBaseChangeBasis A idx =
      fixedSubalgebraBaseChangeLieEquiv A (1 ⊗ₜ[ℤ] fixedBasis idx) := by
  simp [fixedSubalgebraBaseChangeBasis]

theorem toFixedSubalgebraBaseChange_fixedBasis (A : Type*) [CommRing A]
    (idx : Fin 2 ⊕ (Bool × Fin 6)) :
    toFixedSubalgebraBaseChange A (fixedBasis idx) =
      fixedSubalgebraBaseChangeBasis A idx := by
  rw [fixedSubalgebraBaseChangeBasis_apply, fixedSubalgebraBaseChangeLieEquiv_tmul, one_smul]

@[simp]
theorem fixedSubalgebraBaseChangeBasis_repr_tmul (A : Type*) [CommRing A] (a : A)
    (v : trialityLieEquiv.toLieHom.fixedSubalgebra) (idx : Fin 2 ⊕ (Bool × Fin 6)) :
    (fixedSubalgebraBaseChangeBasis A).repr (fixedSubalgebraBaseChangeLieEquiv A (a ⊗ₜ[ℤ] v))
        idx =
      fixedBasis.repr v idx • a := by
  have heq :
      (fixedSubalgebraBaseChangeLieEquiv A).toLinearEquiv.symm
          (fixedSubalgebraBaseChangeLieEquiv A (a ⊗ₜ[ℤ] v)) =
        a ⊗ₜ[ℤ] v :=
    (fixedSubalgebraBaseChangeLieEquiv A).toLinearEquiv.symm_apply_apply (a ⊗ₜ[ℤ] v)
  rw [fixedSubalgebraBaseChangeBasis, Module.Basis.map_repr, LinearEquiv.trans_apply, heq,
    Module.Basis.baseChange_repr_tmul]

@[simp]
theorem coe_fixedSubalgebraBaseChangeBasis_inl (A : Type*) [CommRing A] (k : Fin 2) :
    ((fixedSubalgebraBaseChangeBasis A (.inl k) :
        (LieEquiv.baseChange A trialityLieEquiv).toLieHom.fixedSubalgebra) :
        A ⊗[ℤ] ShellLieAlgebra (CartanMatrix.D 4)) =
      1 ⊗ₜ[ℤ] invariantCartan k := by
  simp [fixedSubalgebraBaseChangeBasis]

@[simp]
theorem coe_fixedSubalgebraBaseChangeBasis_inr (A : Type*) [CommRing A]
    (negative : Bool) (o : Fin 6) :
    ((fixedSubalgebraBaseChangeBasis A (.inr (negative, o)) :
        (LieEquiv.baseChange A trialityLieEquiv).toLieHom.fixedSubalgebra) :
        A ⊗[ℤ] ShellLieAlgebra (CartanMatrix.D 4)) =
      1 ⊗ₜ[ℤ] invariantRoot negative o := by
  simp [fixedSubalgebraBaseChangeBasis]

/-- Over any commutative ring `A`, the structure constants of `fixedSubalgebraBaseChangeBasis A`
are the integer casts of the integral structure constants of `fixedBasis`. -/
@[simp]
theorem fixedSubalgebraBaseChangeBasis_repr_lie (A : Type*) [CommRing A]
    (i j l : Fin 2 ⊕ (Bool × Fin 6)) :
    (fixedSubalgebraBaseChangeBasis A).repr
        ⁅fixedSubalgebraBaseChangeBasis A i, fixedSubalgebraBaseChangeBasis A j⁆ l =
      (fixedBasis.repr ⁅fixedBasis i, fixedBasis j⁆ l : A) := by
  simp [fixedSubalgebraBaseChangeBasis_apply, ← LieEquiv.map_lie]

/-- A scalar-multiple bracket relation between two integral fixed-basis elements transfers to
`fixedSubalgebraBaseChangeBasis A` over any commutative ring `A`. -/
theorem lie_fixedSubalgebraBaseChangeBasis_of_lie_fixedBasis (A : Type*) [CommRing A]
    {i j m : Fin 2 ⊕ (Bool × Fin 6)} {c : ℤ}
    (h : ⁅fixedBasis i, fixedBasis j⁆ = c • fixedBasis m) :
    ⁅fixedSubalgebraBaseChangeBasis A i, fixedSubalgebraBaseChangeBasis A j⁆ =
      (c : A) • fixedSubalgebraBaseChangeBasis A m := by
  refine (fixedSubalgebraBaseChangeBasis A).repr.injective (Finsupp.ext fun l ↦ ?_)
  simp [h, Finsupp.single_apply]

/-- Over any commutative ring satisfying `StrongRankCondition`, the triality-fixed Lie subalgebra
has rank `14`. -/
theorem finrank_fixedSubalgebraBaseChange (A : Type*) [CommRing A] [StrongRankCondition A] :
    Module.finrank A (LieEquiv.baseChange A trialityLieEquiv).toLieHom.fixedSubalgebra = 14 := by
  rw [Module.finrank_eq_card_basis (fixedSubalgebraBaseChangeBasis A)]
  decide

end TauCeti.D4Triality

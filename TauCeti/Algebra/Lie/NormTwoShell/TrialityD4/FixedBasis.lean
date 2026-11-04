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

/-!
# Integral fixed basis and scalar extension for D₄ triality

For the pinned triality action `Matrix.ShellLieAlgebra.reindex trialityPermD4 reindex_cartanMatrix`
on `Matrix.ShellLieAlgebra (CartanMatrix.D 4)`, this file identifies the vertex orbits, proves that
all twelve root cycles have positive monodromy, constructs the concrete fourteen-element integral
basis of the fixed Lie subring, and proves that scalar extension commutes unconditionally with
taking triality fixed points over every commutative ring.

Specifically:
* `TauCeti.D4Triality.vertexOrbitEquiv` enumerates the two `trialityPermD4`-orbits on `Fin 4`:
  index `0` is the outer three-cycle `{0, 2, 3}` and index `1` is the fixed central node `{1}`.
* `TauCeti.D4Triality.monodromy_eq_one` shows that `Matrix.ShellLieAlgebra.monodromy` equals `1`
  on every root cycle of `D₄` triality, both on the three-element outer orbits and on the fixed
  roots.
* `TauCeti.D4Triality.fixedBasis` is the concrete `ℤ`-basis of
  `trialityLieEquiv.toLieHom.fixedSubalgebra` indexed by `Fin 2 ⊕ (Bool × Fin 6)` whose vectors are
  the two Cartan orbit sums `TauCeti.D4Triality.invariantCartan` and the twelve signed root orbit
  sums `TauCeti.D4Triality.invariantRoot`.
* `TauCeti.D4Triality.fixedSubalgebraBaseChangeLieEquiv` upgrades
  `Matrix.ShellLieAlgebra.fixedSubmoduleBaseChangeEquiv` to an isomorphism of `A`-Lie algebras
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

private theorem posDef_cartanMatrix : (CartanMatrix.D 4).PosDef := by
  rw [← transpose_typeDSimpleRootMatrix_mul_self (by decide),
    ← conjTranspose_eq_transpose_of_trivial]
  exact PosDef.conjTranspose_mul_self _ (typeDSimpleRootMatrix_mulVec_injective (by decide))

private theorem even_diag_cartanMatrix (i : Fin 4) : Even (CartanMatrix.D 4 i i) := by
  rw [CartanMatrix.D_diag]
  exact even_two

/-- Positivity of `CartanMatrix.D 4` as a scoped typeclass fact for `Matrix.ShellLieAlgebra`. -/
scoped instance instFactPosDefCartanMatrix : Fact (CartanMatrix.D 4).PosDef :=
  ⟨posDef_cartanMatrix⟩

/-- Evenness of the diagonal of `CartanMatrix.D 4` as a scoped typeclass fact for
`Matrix.ShellLieAlgebra`. -/
scoped instance instFactEvenDiagCartanMatrix : Fact (∀ i, Even (CartanMatrix.D 4 i i)) :=
  ⟨even_diag_cartanMatrix⟩

/-- Finiteness of the `D₄` norm-two shell as a scoped instance. -/
scoped instance instFiniteNormTwoShell : Finite (CartanMatrix.D 4).normTwoShell :=
  posDef_cartanMatrix.finite_normTwoShell

/-! ### Vertex orbits of `trialityPermD4` -/

/-- Orbit labels for `trialityPermD4`: `0` is the outer three-cycle `{0, 2, 3}` and `1` is the
central fixed vertex `{1}`. -/
@[expose] def vertexOrbit : Fin 4 → Fin 2 := ![0, 1, 0, 0]

/-- Chosen representatives `0` and `1` of the two `trialityPermD4`-orbits on `Fin 4`. -/
@[expose] def vertexRepresentative : Fin 2 → Fin 4 := ![0, 1]

@[simp]
theorem vertexOrbit_vertexRepresentative (k : Fin 2) :
    vertexOrbit (vertexRepresentative k) = k := by
  decide +revert

@[simp]
theorem vertexOrbit_trialityPermD4 (i : Fin 4) :
    vertexOrbit (trialityPermD4 i) = vertexOrbit i := by
  fin_cases i <;> simp [vertexOrbit]

/-- `vertexOrbit` distinguishes exactly the cycles of `trialityPermD4`. -/
theorem sameCycle_trialityPermD4_iff (i j : Fin 4) :
    trialityPermD4.SameCycle i j ↔ vertexOrbit i = vertexOrbit j := by
  constructor
  · exact fun h ↦ h.apply_eq_of_apply_eq vertexOrbit_trialityPermD4
  · intro h
    have h02 : trialityPermD4.SameCycle 0 2 := ⟨1, by simp⟩
    have h23 : trialityPermD4.SameCycle 2 3 := ⟨1, by simp⟩
    have h03 : trialityPermD4.SameCycle 0 3 := h02.trans h23
    fin_cases i <;> fin_cases j <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk] at h ⊢
    all_goals first
      | exact Equiv.Perm.SameCycle.refl _ _
      | exact h02 | exact h02.symm | exact h23 | exact h23.symm | exact h03 | exact h03.symm
      | exact absurd h (by decide)

/-- Explicit enumeration of the two vertex orbits of `trialityPermD4`: `0` corresponds to the
outer three-cycle `{0, 2, 3}` and `1` to the central fixed vertex `{1}`. -/
def vertexOrbitEquiv : Fin 2 ≃ Quotient (Equiv.Perm.SameCycle.setoid trialityPermD4) where
  toFun k := Quotient.mk _ (vertexRepresentative k)
  invFun O := Quotient.liftOn O vertexOrbit fun _ _ h ↦ (sameCycle_trialityPermD4_iff _ _).mp h
  left_inv := vertexOrbit_vertexRepresentative
  right_inv O := Quotient.inductionOn O fun _ ↦
    Quotient.sound ((sameCycle_trialityPermD4_iff _ _).mpr (vertexOrbit_vertexRepresentative _))

theorem vertexOrbitEquiv_apply (k : Fin 2) :
    vertexOrbitEquiv k = Quotient.mk _ (vertexRepresentative k) :=
  (rfl)

@[simp]
theorem vertexOrbitEquiv_symm_mk (i : Fin 4) :
    vertexOrbitEquiv.symm (Quotient.mk _ i) = vertexOrbit i :=
  (rfl)

@[simp]
theorem vertexOrbit_out_vertexOrbitEquiv (k : Fin 2) :
    vertexOrbit (vertexOrbitEquiv k).out = k := by
  have h := congrArg vertexOrbitEquiv.symm (Quotient.out_eq (vertexOrbitEquiv k))
  rwa [vertexOrbitEquiv_symm_mk, Equiv.symm_apply_apply] at h

@[simp]
theorem sameCycle_vertexOrbitEquiv_out_iff (i : Fin 4) (k : Fin 2) :
    trialityPermD4.SameCycle i (vertexOrbitEquiv k).out ↔ vertexOrbit i = k := by
  rw [sameCycle_trialityPermD4_iff, vertexOrbit_out_vertexOrbitEquiv]

private theorem existsUnique_sameCycle_vertexRepresentative (i : Fin 4) :
    ∃! k : Fin 2, trialityPermD4.SameCycle (vertexRepresentative k) i := by
  refine ⟨vertexOrbit i, ?_, fun k hk ↦ ?_⟩
  · dsimp only
    rw [sameCycle_trialityPermD4_iff, vertexOrbit_vertexRepresentative]
  · dsimp only at hk
    rwa [sameCycle_trialityPermD4_iff, vertexOrbit_vertexRepresentative] at hk

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
  ShellLieAlgebra.reindexLieEquiv trialityPermD4 reindex_cartanMatrix
    posDef_cartanMatrix even_diag_cartanMatrix

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
      (ShellLieAlgebra.reindex trialityPermD4 reindex_cartanMatrix).toLinearMap.fixedSubmodule := by
  rw [LieHom.fixedSubalgebra_toSubmodule]
  exact congrArg LinearMap.fixedSubmodule (LinearMap.ext trialityLieEquiv_apply)

/-- Coordinates of the two primitive `trialityPermD4`-invariant Cartan vectors:
`![1, 0, 1, 1]` for the outer three-cycle and `![0, 1, 0, 0]` for the central vertex. -/
@[expose] def invariantCartanVec : Fin 2 → Fin 4 → ℤ :=
  ![![1, 0, 1, 1], ![0, 1, 0, 0]]

@[simp]
theorem invariantCartanVec_comp_trialityPermD4_symm (k : Fin 2) :
    invariantCartanVec k ∘ trialityPermD4.symm = invariantCartanVec k := by
  ext i
  obtain ⟨i, rfl⟩ := trialityPermD4.surjective i
  simp only [Function.comp_apply, Equiv.symm_apply_apply]
  fin_cases k <;> fin_cases i <;> simp [invariantCartanVec]

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

/-- Coordinate of a fixed vector at Cartan orbit `k` is its ambient Cartan coordinate at
`vertexRepresentative k`. -/
@[simp]
theorem fixedBasis_repr_inl (v : trialityLieEquiv.toLieHom.fixedSubalgebra) (k : Fin 2) :
    fixedBasis.repr v (.inl k) =
      (ShellLieAlgebra.basis (CartanMatrix.D 4)).repr v (.inl (vertexRepresentative k)) := by
  have hv : (((LinearEquiv.ofEq _ _ toSubmodule_fixedSubalgebra.symm).symm v :
      (ShellLieAlgebra.reindex trialityPermD4 reindex_cartanMatrix).toLinearMap.fixedSubmodule) :
      ShellLieAlgebra (CartanMatrix.D 4)) = v := by
    rw [LinearEquiv.ofEq_symm, LinearEquiv.coe_ofEq_apply]
  simp [fixedBasis, fixedBasisRep, hv]

/-- Coordinate of a fixed vector at signed root orbit `(negative, o)` is its ambient root
coordinate at `root negative (representative o)`. -/
@[simp]
theorem fixedBasis_repr_inr (v : trialityLieEquiv.toLieHom.fixedSubalgebra)
    (negative : Bool) (o : Fin 6) :
    fixedBasis.repr v (.inr (negative, o)) =
      (ShellLieAlgebra.basis (CartanMatrix.D 4)).repr v
        (.inr (root negative (representative o))) := by
  have hv : (((LinearEquiv.ofEq _ _ toSubmodule_fixedSubalgebra.symm).symm v :
      (ShellLieAlgebra.reindex trialityPermD4 reindex_cartanMatrix).toLinearMap.fixedSubmodule) :
      ShellLieAlgebra (CartanMatrix.D 4)) = v := by
    rw [LinearEquiv.ofEq_symm, LinearEquiv.coe_ofEq_apply]
  simp [fixedBasis, fixedBasisRep, hv]

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

private theorem toSubmodule_fixedSubalgebra_baseChange (A : Type*) [CommRing A] :
    (LieEquiv.baseChange A trialityLieEquiv).toLieHom.fixedSubalgebra.toSubmodule =
      ((ShellLieAlgebra.reindex trialityPermD4 reindex_cartanMatrix).toLinearMap.baseChange
        A).fixedSubmodule := by
  rw [LieHom.fixedSubalgebra_toSubmodule, LieEquiv.toLieHom_baseChange, LieHom.coe_baseChange]
  refine congrArg (fun f : ShellLieAlgebra (CartanMatrix.D 4) →ₗ[ℤ]
      ShellLieAlgebra (CartanMatrix.D 4) ↦ (f.baseChange A).fixedSubmodule) ?_
  exact LinearMap.ext trialityLieEquiv_apply

private noncomputable def fixedSubalgebraBaseChangeLinearEquiv (A : Type*) [CommRing A] :
    A ⊗[ℤ] trialityLieEquiv.toLieHom.fixedSubalgebra ≃ₗ[A]
      (LieEquiv.baseChange A trialityLieEquiv).toLieHom.fixedSubalgebra :=
  ((LinearEquiv.ofEq _ _ toSubmodule_fixedSubalgebra).baseChange ℤ A _ _).trans
    ((ShellLieAlgebra.fixedSubmoduleBaseChangeEquiv
      trialityPermD4 reindex_cartanMatrix A (Or.inl inferInstance)).trans
      (LinearEquiv.ofEq _ _ (toSubmodule_fixedSubalgebra_baseChange A).symm))

private theorem coe_fixedSubalgebraBaseChangeLinearEquiv (A : Type*) [CommRing A]
    (x : A ⊗[ℤ] trialityLieEquiv.toLieHom.fixedSubalgebra) :
    (fixedSubalgebraBaseChangeLinearEquiv A x : A ⊗[ℤ] ShellLieAlgebra (CartanMatrix.D 4)) =
      LieHom.baseChange A trialityLieEquiv.toLieHom.fixedSubalgebra.incl x := by
  induction x with
  | tmul a v =>
    have hcoe (u : (LieEquiv.baseChange A trialityLieEquiv).toLieHom.fixedSubalgebra.toSubmodule) :
        ((u : (LieEquiv.baseChange A trialityLieEquiv).toLieHom.fixedSubalgebra) :
          A ⊗[ℤ] ShellLieAlgebra (CartanMatrix.D 4)) = u := rfl
    rw [fixedSubalgebraBaseChangeLinearEquiv, LinearEquiv.trans_apply, LinearEquiv.trans_apply,
      LinearEquiv.baseChange_tmul, ShellLieAlgebra.fixedSubmoduleBaseChangeEquiv_apply, hcoe,
      LinearEquiv.coe_ofEq_apply, LinearMap.fixedSubmoduleBaseChange_tmul,
      LinearEquiv.coe_ofEq_apply, LieHom.baseChange_tmul]
    rfl
  | add x y hx hy =>
    rw [map_add, map_add, AddMemClass.coe_add, hx, hy]

/-- Over every commutative ring `A`, the scalar extension of the integral triality-fixed Lie
subring maps isomorphically as an `A`-Lie algebra onto the fixed Lie subalgebra of the
scalar-extended triality automorphism, with no flatness or `2`-torsion hypothesis. -/
noncomputable def fixedSubalgebraBaseChangeLieEquiv (A : Type*) [CommRing A] :
    A ⊗[ℤ] trialityLieEquiv.toLieHom.fixedSubalgebra ≃ₗ⁅A⁆
      (LieEquiv.baseChange A trialityLieEquiv).toLieHom.fixedSubalgebra :=
  { fixedSubalgebraBaseChangeLinearEquiv A with
    map_lie' := fun {x y} ↦ Subtype.ext <| by
      change (fixedSubalgebraBaseChangeLinearEquiv A ⁅x, y⁆ :
          A ⊗[ℤ] ShellLieAlgebra (CartanMatrix.D 4)) =
        ⁅(fixedSubalgebraBaseChangeLinearEquiv A x :
            A ⊗[ℤ] ShellLieAlgebra (CartanMatrix.D 4)),
          (fixedSubalgebraBaseChangeLinearEquiv A y :
            A ⊗[ℤ] ShellLieAlgebra (CartanMatrix.D 4))⁆
      rw [coe_fixedSubalgebraBaseChangeLinearEquiv, coe_fixedSubalgebraBaseChangeLinearEquiv,
        coe_fixedSubalgebraBaseChangeLinearEquiv]
      exact (LieHom.baseChange A trialityLieEquiv.toLieHom.fixedSubalgebra.incl).map_lie x y }

@[simp]
theorem coe_fixedSubalgebraBaseChangeLieEquiv_tmul (A : Type*) [CommRing A] (a : A)
    (v : trialityLieEquiv.toLieHom.fixedSubalgebra) :
    ((fixedSubalgebraBaseChangeLieEquiv A (a ⊗ₜ[ℤ] v) :
        (LieEquiv.baseChange A trialityLieEquiv).toLieHom.fixedSubalgebra) :
        A ⊗[ℤ] ShellLieAlgebra (CartanMatrix.D 4)) =
      a ⊗ₜ[ℤ] (v : ShellLieAlgebra (CartanMatrix.D 4)) := by
  exact (coe_fixedSubalgebraBaseChangeLinearEquiv A (a ⊗ₜ[ℤ] v)).trans (by simp)

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

/-- Over any commutative ring satisfying `StrongRankCondition`, the triality-fixed Lie subalgebra
has rank `14`. -/
theorem finrank_fixedSubalgebraBaseChange (A : Type*) [CommRing A] [StrongRankCondition A] :
    Module.finrank A (LieEquiv.baseChange A trialityLieEquiv).toLieHom.fixedSubalgebra = 14 := by
  rw [Module.finrank_eq_card_basis (fixedSubalgebraBaseChangeBasis A)]
  decide

end TauCeti.D4Triality

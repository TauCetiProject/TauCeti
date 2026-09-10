/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.GeneralLinear.Fock
public import TauCeti.Algebra.Lie.GeneralLinear.Restriction
import TauCeti.Algebra.Lie.GeneralLinear.Radical
import TauCeti.Algebra.Lie.HighestWeight.CompleteReducibility
import Mathlib.Algebra.Lie.CartanCriterion
import TauCeti.LinearAlgebra.CliffordAlgebra.Dimension

/-!
# Complete reducibility for the general linear Lie algebra and its CAR module

The Killing form of `gl n` is degenerate on the scalar matrices, so Weyl's complete-reducibility
theorem does not apply to it directly. It does apply to `sl n`. This file proves that `sl n` has
trivial radical in characteristic zero, restricts a `gl n`-module to `sl n`, and then promotes an
`sl n`-stable complement back to `gl n` whenever the identity matrix acts by a scalar.

The final section applies this transfer to the left-regular CAR module. The normal-ordered lift
sends the identity matrix to the scalar `(card n) ^ 2 / 2`; hence the centre preserves every
`sl n`-submodule, and the CAR module is completely reducible.

## Main results

* `TauCeti.hasTrivialRadical_specialLinear`: `sl n` has zero solvable radical over a
  characteristic-zero field.
* `TauCeti.exists_isCompl_gl_of_forall_one_lie_eq_smul`: a finite-dimensional `gl n`-module on
  which the identity acts by a scalar has a complement to every Lie submodule.
* `TauCeti.complementedLattice_lieSubmodule_gl_of_forall_one_lie_eq_smul`: the corresponding
  complemented-lattice statement.
* `TauCeti.complementedLattice_lieSubmodule_car`: complete reducibility of the CAR module.

## References

* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, GTM 9, §6.3, for
  Weyl's complete-reducibility theorem.
* B. Kostant, *Clifford algebra analogue of the Hopf--Koszul--Samelson theorem*, Adv. Math. 125
  (1997), 275--350, for the left-regular Clifford module.
-/

public section

namespace TauCeti

open _root_.LieAlgebra

attribute [local instance 100] LieRing.ofAssociativeRing

universe u v w

/-! ### Semisimplicity of the special linear Lie algebra -/

section SpecialLinear

variable (K : Type u) [Field K] [CharZero K]
variable (n : Type v) [Fintype n] [DecidableEq n]

/-- The inclusion of an ideal of `sl n` into `gl n` has ideal range. Scalar matrices commute with
the image, while the `sl n` summand preserves the ideal. -/
private theorem slIncl_isIdealMorphism (J : LieIdeal K (SpecialLinear.sl n K)) :
    ((SpecialLinear.sl n K).incl.comp J.incl).IsIdealMorphism := by
  rw [LieHom.isIdealMorphism_iff]
  intro A y
  cases isEmpty_or_nonempty n with
  | inl hn =>
      let _ := hn
      exact ⟨0, Subsingleton.elim _ _⟩
  | inr hn =>
      let _ := hn
      let _ : Invertible (Fintype.card n : K) :=
        invertibleOfNonzero (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)
      obtain ⟨X, Z, hX, hZ, hXZ⟩ := Submodule.codisjoint_iff_exists_add_eq.mp
        (isCompl_center_derivedSeries_one_matrix K n).codisjoint A
      have hZsl : Z ∈ SpecialLinear.sl n K := by
        rw [← derivedSeries_one_toLieSubalgebra_eq_sl K n]
        exact hZ
      have hXzero : ⁅X, ((SpecialLinear.sl n K).incl.comp J.incl) y⁆ = 0 := by
        rw [← lie_skew, (LieModule.mem_maxTrivSubmodule K _ _ X).1 hX, neg_zero]
      let z : J := ⟨⁅⟨Z, hZsl⟩, (y : SpecialLinear.sl n K)⁆, J.lie_mem y.property⟩
      refine ⟨z, ?_⟩
      rw [← hXZ, add_lie, hXzero, zero_add]
      rfl

/-- **The special linear Lie algebra has trivial radical in characteristic zero.** A solvable
ideal of `sl n` maps to a solvable ideal of `gl n`, hence lies in the scalar matrices because the
radical of `gl n` is its centre. Its image also lies in the derived ideal `sl n`; the centre and
derived ideal are complementary, so the original ideal vanishes. -/
theorem hasTrivialRadical_specialLinear :
    LieAlgebra.HasTrivialRadical K (SpecialLinear.sl n K) := by
  rw [LieAlgebra.hasTrivialRadical_iff_no_solvable_ideals]
  intro J hJ
  rw [eq_bot_iff]
  intro x hx
  let f : J →ₗ⁅K⁆ Matrix n n K := (SpecialLinear.sl n K).incl.comp J.incl
  have hf : f.IsIdealMorphism := slIncl_isIdealMorphism K n J
  have hsolvRange : LieAlgebra.IsSolvable f.range := by
    let _ : LieAlgebra.IsSolvable J := hJ
    infer_instance
  have hsolv : LieAlgebra.IsSolvable f.idealRange := by
    let e : (f.idealRange : LieSubalgebra K (Matrix n n K)) ≃ₗ⁅K⁆ f.range :=
      LieEquiv.ofEq _ _ (congrArg (fun S : LieSubalgebra K (Matrix n n K) ↦
        (S : Set (Matrix n n K))) hf.eq)
    exact (LieAlgebra.solvable_iff_equiv_solvable e).mpr hsolvRange
  have hcenter : f ⟨x, hx⟩ ∈ LieAlgebra.center K (Matrix n n K) := by
    rw [← radical_eq_center]
    exact (LieIdeal.solvable_iff_le_radical K _ f.idealRange).mp hsolv
      (f.mem_idealRange ⟨x, hx⟩)
  cases isEmpty_or_nonempty n with
  | inl hn =>
      let _ := hn
      exact Subsingleton.elim _ _
  | inr hn =>
      let _ := hn
      let _ : Invertible (Fintype.card n : K) :=
        invertibleOfNonzero (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)
      have hderived : f ⟨x, hx⟩ ∈ (derivedSeries K (Matrix n n K) 1).toSubmodule := by
        rw [derivedSeries_one_eq_slIdeal K n, LieSubmodule.mem_toSubmodule, mem_slIdeal_iff]
        exact x.property
      have hzero : f ⟨x, hx⟩ = 0 :=
        (isCompl_center_derivedSeries_one_matrix K n).disjoint.le_bot ⟨hcenter, hderived⟩
      exact Subtype.ext (by simpa [f] using hzero)

end SpecialLinear

/-! ### Complete reducibility for scalar-centre `gl n` modules -/

section GeneralLinear

variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]
variable {n : Type v} [Fintype n] [DecidableEq n]
variable {M : Type w} [AddCommGroup M] [Module K M]
variable [LieRingModule (Matrix n n K) M] [LieModule K (Matrix n n K) M]

/-- Extend an `sl n`-submodule to `gl n` when the identity acts by a scalar. -/
private def extendSl (c : K) (hc : ∀ m : M, ⁅(1 : Matrix n n K), m⁆ = c • m)
    (N : LieSubmodule K (SpecialLinear.sl n K) M) : LieSubmodule K (Matrix n n K) M where
  __ := N.toSubmodule
  lie_mem {A m} hm := by
    obtain ⟨X, r, rfl⟩ := exists_sl_add_smul_one_eq
      (fun h ↦ by let _ := h; exact Nat.cast_ne_zero.mpr Fintype.card_ne_zero) A
    rw [add_lie, smul_lie, hc, smul_smul]
    exact N.add_mem (N.lie_mem hm) (N.smul_mem _ hm)

/-- **Complete reducibility for a general-linear module with scalar centre.** Every Lie submodule
has a complement when the identity matrix acts by a scalar. Restriction to `sl n` supplies a
complement by Weyl's theorem, and the scalar action makes that complement stable under all of
`gl n`. -/
theorem exists_isCompl_gl_of_forall_one_lie_eq_smul [FiniteDimensional K M] {c : K}
    (hc : ∀ m : M, ⁅(1 : Matrix n n K), m⁆ = c • m)
    (N : LieSubmodule K (Matrix n n K) M) :
    ∃ N' : LieSubmodule K (Matrix n n K) M, IsCompl N N' := by
  let _ : LieAlgebra.HasTrivialRadical K (SpecialLinear.sl n K) :=
    hasTrivialRadical_specialLinear K n
  obtain ⟨P, hP⟩ := exists_isCompl_of_isKilling (K := K)
    (L := SpecialLinear.sl n K) (N.restr (SpecialLinear.sl n K))
  refine ⟨extendSl c hc P, IsCompl.of_eq ?_ ?_⟩
  · apply LieSubmodule.toSubmodule_injective
    simpa [extendSl] using congrArg LieSubmodule.toSubmodule hP.inf_eq_bot
  · apply LieSubmodule.toSubmodule_injective
    simpa [extendSl] using congrArg LieSubmodule.toSubmodule hP.sup_eq_top

variable (K n M) in
/-- The Lie-submodule lattice of a finite-dimensional `gl n`-module is complemented when the
identity matrix acts by a scalar. -/
theorem complementedLattice_lieSubmodule_gl_of_forall_one_lie_eq_smul
    [FiniteDimensional K M] {c : K}
    (hc : ∀ m : M, ⁅(1 : Matrix n n K), m⁆ = c • m) :
    ComplementedLattice (LieSubmodule K (Matrix n n K) M) :=
  ⟨exists_isCompl_gl_of_forall_one_lie_eq_smul hc⟩

end GeneralLinear

/-! ### The CAR module -/

section CAR

attribute [local instance] Classical.decEq
open scoped TauCeti

variable {K n : Type*} [Field K] [Fintype n] [Invertible (2 : K)]

variable [CharZero K] [IsAlgClosed K]

variable (K n) in
/-- **The CAR module is completely reducible.** Its Lie-submodule lattice is complemented because
the normal-ordered action of the identity matrix is scalar. -/
theorem complementedLattice_lieSubmodule_car :
    ComplementedLattice
      (LieSubmodule K (Matrix n n K) (CliffordAlgebra (traceQuadraticForm K n))) :=
  complementedLattice_lieSubmodule_gl_of_forall_one_lie_eq_smul K n _ car_one_lie_eq_smul

end CAR

end TauCeti

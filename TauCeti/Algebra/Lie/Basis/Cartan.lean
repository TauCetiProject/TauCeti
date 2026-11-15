/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.Basis.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# The Cartan generators of a Lie algebra basis as a module basis

A `LieAlgebra.Basis ι H` carries a family `h : ι → H` of Cartan generators which is linearly
independent and spans `H`. This file packages that data as a `Module.Basis` of `H` and reads off
the dimension of `H`. It also records a height vector for the Cartan matrix.

## Main definitions

* `LieAlgebra.Basis.cartanBasis`: the Cartan generators as a module basis of the Cartan
  subalgebra.

## Main statements

* `LieAlgebra.Basis.finrank_cartan`: the Cartan subalgebra has dimension the cardinality of the
  index type.
* `LieAlgebra.Basis.exists_sum_A_mul_eq_one`: over a field of characteristic zero, some vector
  pairs to `1` with every row of the Cartan matrix.
-/

public section

namespace LieAlgebra.Basis

variable {ι R L : Type*} [Finite ι] [CommRing R] [LieRing L] [LieAlgebra R L]
  {H : LieSubalgebra R L}

/-- The Cartan generators of a Lie algebra basis form a module basis of its Cartan subalgebra. -/
noncomputable def cartanBasis (b : Basis ι H) : Module.Basis ι R H :=
  (Module.Basis.span b.linInd).map (LinearEquiv.ofEq _ _ b.coe_cartan_eq_span).symm

/-- The vectors of `LieAlgebra.Basis.cartanBasis` are the Cartan generators. -/
@[simp] theorem coe_cartanBasis (b : Basis ι H) (i : ι) :
    (b.cartanBasis i : L) = b.h i := by
  rw [cartanBasis, Module.Basis.map_apply, LinearEquiv.ofEq_symm, LinearEquiv.coe_ofEq_apply,
    Module.Basis.coe_span_apply]

/-- The vectors of `LieAlgebra.Basis.cartanBasis` are the Cartan generators `h'`, read as elements
of the Cartan subalgebra. -/
theorem cartanBasis_apply (b : Basis ι H) (i : ι) : b.cartanBasis i = b.h' i :=
  Subtype.ext (b.coe_cartanBasis i)

/-- The Cartan subalgebra has dimension the cardinality of the basis's index type. -/
theorem finrank_cartan [StrongRankCondition R] (b : Basis ι H) :
    Module.finrank R H = Nat.card ι :=
  Module.finrank_eq_nat_card_basis b.cartanBasis

/-- A **height vector** for the Cartan matrix: since the Cartan matrix of a basis is
nondegenerate, over a field `K` of characteristic zero some vector pairs to `1` with every row. -/
theorem exists_sum_A_mul_eq_one [Fintype ι] (b : Basis ι H) (K : Type*) [Field K] [CharZero K] :
    ∃ a : ι → K, ∀ i, ∑ j, (b.A i j : K) * a j = 1 := by
  classical
  have hA : IsUnit ((Int.castRingHom K).mapMatrix b.A) := by
    rw [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero, ← RingHom.map_det]
    simpa using b.nondegen.det_ne_zero
  obtain ⟨a, ha⟩ := Matrix.mulVec_surjective_iff_isUnit.2 hA 1
  exact ⟨a, fun i => by simpa [Matrix.mulVec, dotProduct] using congr_fun ha i⟩

end LieAlgebra.Basis

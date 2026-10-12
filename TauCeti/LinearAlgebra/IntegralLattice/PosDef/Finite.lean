/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Rat.Floor
public import TauCeti.LinearAlgebra.IntegralLattice.Signature
public import TauCeti.LinearAlgebra.QuadraticForm.PosDef

/-!
# Finiteness in a definite lattice: bounded-norm sets, shells and isometries

A positive definite integral lattice has only finitely many vectors of norm at most any given
bound, and hence only finitely many vectors of any given norm. This is what makes the minimum,
the shells and the representation numbers of a positive definite lattice finite quantities.
A negative definite lattice likewise has only finitely many vectors of norm at least any given
bound, and finite shells.

Finite shells make the isometry group finite: an isometry `L → M` is determined by the images of
a `ℤ`-basis of `L`, and each of these lies in the shell of `M` of the corresponding norm. Hence
there are only finitely many isometries into a definite lattice, and in particular the isometry
group `O(L) = Isometry L L` of a definite lattice `L` is finite.

Definiteness is load-bearing: the hyperbolic plane is nondegenerate, yet its isotropic
vectors form an infinite shell of norm zero
(`TauCeti.IntegralLattice.infinite_vectorsOfNorm_zero_hyperbolicPlane`).

## Main results

* `TauCeti.IntegralLattice.IsPosSemidef.integralNorm_nonneg`,
  `TauCeti.IntegralLattice.IsPosSemidef.isPosSemidef_integralForm` and
  `TauCeti.IntegralLattice.IsPosDef.posDef_integralNorm`: the integral norm form of a positive
  semidefinite lattice is nonnegative (and its integral bilinear form is positive semidefinite),
  and that of a positive definite lattice is positive definite.
* `TauCeti.IntegralLattice.IsPosDef.finite_setOf_norm_le`: only finitely many lattice vectors have
  norm at most a given rational bound.
* `TauCeti.IntegralLattice.IsPosDef.finite_vectorsOfNorm` and
  `TauCeti.IntegralLattice.IsNegDef.finite_vectorsOfNorm`: every shell of a definite lattice is
  finite.
* `TauCeti.IntegralLattice.finite_isometry_of_forall_finite_vectorsOfNorm`: there are only
  finitely many isometries into a lattice all of whose shells are finite.
* `TauCeti.IntegralLattice.IsPosDef.finite_isometry` and
  `TauCeti.IntegralLattice.IsNegDef.finite_isometry`: there are only finitely many isometries
  into a definite lattice; in particular the isometry group of a definite lattice is finite.

## References

* O. T. O'Meara, *Introduction to Quadratic Forms*, §102.
* J. H. Conway and N. J. A. Sloane, *Sphere Packings, Lattices and Groups*, Chapter 1, §2.
-/

public section

namespace TauCeti

universe u

variable {V : Type u} [AddCommGroup V] [Module ℚ V]

namespace IntegralLattice

variable {L : IntegralLattice V}

/-- The integral norm of a positive semidefinite lattice is nonnegative. -/
theorem IsPosSemidef.integralNorm_nonneg (hL : L.IsPosSemidef) (x : L) :
    0 ≤ L.integralNorm x := by
  have h : (0 : ℚ) ≤ L.norm x := by
    rw [L.norm_apply]
    exact L.isPosSemidef_iff.mp hL x
  rw [← L.integralNorm_cast x] at h
  exact_mod_cast h

/-- The integral bilinear form of a positive semidefinite lattice is positive semidefinite. -/
theorem IsPosSemidef.isPosSemidef_integralForm (hL : L.IsPosSemidef) :
    L.integralForm.IsPosSemidef :=
  (LinearMap.BilinForm.isPosSemidef_iff_forall_nonneg _ L.isSymm_integralForm).2 fun x ↦ by
    simpa only [integralNorm_apply] using hL.integralNorm_nonneg x

/-- The integral norm form of a positive definite lattice is positive definite. -/
theorem IsPosDef.posDef_integralNorm (hL : L.IsPosDef) : L.integralNorm.PosDef := by
  intro x hx
  have h : (0 : ℚ) < L.norm x := by
    rw [L.norm_def]
    exact hL (x : V) (Submodule.coe_eq_zero.not.mpr hx)
  rw [← L.integralNorm_cast x] at h
  exact_mod_cast h

/-- **Bounded-norm sets of a positive definite lattice are finite.** Only finitely many vectors of
a positive definite integral lattice have norm at most a given rational bound. -/
theorem IsPosDef.finite_setOf_norm_le (hL : L.IsPosDef) (C : ℚ) :
    {x : L | L.norm x ≤ C}.Finite := by
  refine (hL.posDef_integralNorm.finite_setOf_apply_le ⌊C⌋).subset fun x hx ↦ ?_
  simp only [Set.mem_ofPred_eq] at hx ⊢
  rw [Int.le_floor, L.integralNorm_cast]
  exact hx

/-- **Every shell of a positive definite lattice is finite.** -/
theorem IsPosDef.finite_vectorsOfNorm (hL : L.IsPosDef) (n : ℚ) :
    (L.vectorsOfNorm n).Finite :=
  (hL.finite_setOf_norm_le n).subset fun _ hx ↦ (mem_vectorsOfNorm.mp hx).le

/-- The negated integral norm form of a negative definite lattice is positive definite. -/
theorem IsNegDef.posDef_neg_integralNorm (hL : L.IsNegDef) : (-L.integralNorm).PosDef := by
  intro x hx
  have h : L.norm x < 0 := by
    rw [L.norm_def]
    exact L.isNegDef_iff.mp hL (x : V) (Submodule.coe_eq_zero.not.mpr hx)
  rw [← L.integralNorm_cast x] at h
  rw [neg_apply, neg_pos]
  exact_mod_cast h

/-- **Sets of bounded norm in a negative definite lattice are finite.** Only finitely many vectors
of a negative definite integral lattice have norm at least a given rational bound. -/
theorem IsNegDef.finite_setOf_le_norm (hL : L.IsNegDef) (C : ℚ) :
    {x : L | C ≤ L.norm x}.Finite := by
  refine (hL.posDef_neg_integralNorm.finite_setOf_apply_le ⌊-C⌋).subset fun x hx ↦ ?_
  simp only [Set.mem_ofPred_eq] at hx ⊢
  rw [neg_apply, Int.le_floor, Int.cast_neg, L.integralNorm_cast, neg_le_neg_iff]
  exact hx

/-- **Every shell of a negative definite lattice is finite.** -/
theorem IsNegDef.finite_vectorsOfNorm (hL : L.IsNegDef) (n : ℚ) :
    (L.vectorsOfNorm n).Finite :=
  (hL.finite_setOf_le_norm n).subset fun _ hx ↦ (mem_vectorsOfNorm.mp hx).ge

variable {W : Type*} [AddCommGroup W] [Module ℚ W] {M : IntegralLattice W}

/-- **Finite shells give finitely many isometries.** An isometry `L → M` is determined by the
images of a `ℤ`-basis of `L`, each of which lies in the shell of `M` of the corresponding norm; so
if every shell of `M` is finite, there are only finitely many isometries from `L` to `M`. -/
theorem finite_isometry_of_forall_finite_vectorsOfNorm
    (h : ∀ n : ℚ, (M.vectorsOfNorm n).Finite) : Finite (Isometry L M) := by
  let b := Module.Free.chooseBasis ℤ L
  have : ∀ i, Finite (M.vectorsOfNorm (L.norm (b i))) := fun i ↦ (h _).to_subtype
  refine Finite.of_injective
    (fun e : Isometry L M ↦ fun i ↦ (⟨e.carrierEquiv (b i),
      (e.carrierEquiv_mem_vectorsOfNorm_iff (b i) _).mpr (mem_vectorsOfNorm.mpr rfl)⟩ :
        M.vectorsOfNorm (L.norm (b i))))
    fun e f hef ↦ ?_
  refine Isometry.carrierEquiv_injective (LinearEquiv.toLinearMap_injective (b.ext fun i ↦ ?_))
  exact congrArg Subtype.val (congrFun hef i)

/-- **The isometry group of a positive definite lattice is finite.** More generally, there are only
finitely many isometries into a positive definite lattice. -/
theorem IsPosDef.finite_isometry (hM : M.IsPosDef) : Finite (Isometry L M) :=
  finite_isometry_of_forall_finite_vectorsOfNorm hM.finite_vectorsOfNorm

/-- **The isometry group of a negative definite lattice is finite.** More generally, there are only
finitely many isometries into a negative definite lattice. -/
theorem IsNegDef.finite_isometry (hM : M.IsNegDef) : Finite (Isometry L M) :=
  finite_isometry_of_forall_finite_vectorsOfNorm hM.finite_vectorsOfNorm

end IntegralLattice

end TauCeti

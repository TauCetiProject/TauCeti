/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.Coalgebra.Comodule.MonoidAlgebra.Basic

/-!
# Regular one-cocycles of diagonalizable groups

For a comodule `V` over `R[G]`, a regular one-cochain is a tensor `b : V ⊗ R[G]`.
The cocycle identity is `b(gh) = b(g) + g • b(h)`, expressed using comultiplication
and the coaction. Every such cocycle is a coboundary `b(g) = v - g • v`.
The coefficient of the identity character in `b` gives a canonical choice of `v`;
its invariant weight component vanishes. This proves the vector-group complement
calculation used when conjugating tori in solvable affine groups.

The result works over any commutative semiring with an additive group of coefficients,
with no finiteness, smoothness, or characteristic restriction.
In the group-scheme interpretation `G` is an abelian group
of characters; the calculation itself only needs an index type with a distinguished `1`.
In particular it includes diagonalizable groups that are nonreduced in positive
characteristic. These are regular cocycles, not arbitrary cocycles of rational-point groups.

The proof uses `Comodule.monoidCoeff`, `Comodule.coact_comp_tensorComponent`, and the
weight projections from `Comodule.MonoidAlgebra.Basic`.

## References

* W. C. Waterhouse, *Introduction to Affine Group Schemes*, §3.2.
* J. C. Jantzen, *Representations of Algebraic Groups*, I.4 (rational cohomology).
-/

public section

open scoped TensorProduct

namespace TauCeti.Comodule

universe u v w

variable {R : Type u} [CommSemiring R] {G : Type v} [One G]
  {V : Type w} [AddCommMonoid V] [Module R V] [Comodule R (MonoidAlgebra R G) V]

/-- The regular one-cocycle identity `b(gh) = b(g) + g • b(h)`, expressed in
`V ⊗ (R[G] ⊗ R[G])` using the comultiplication and the coaction. -/
def IsRegularCocycle₁ (b : V ⊗[R] MonoidAlgebra R G) : Prop :=
  Coalgebra.comul.lTensor V b =
    TensorProduct.assoc R V (MonoidAlgebra R G) (MonoidAlgebra R G)
      ((coact (R := R) (C := MonoidAlgebra R G) (M := V)).rTensor _ b +
        b ⊗ₜ[R] MonoidAlgebra.single 1 1)

/-- The tensor equation characterizing a regular one-cocycle. -/
theorem isRegularCocycle₁_iff (b : V ⊗[R] MonoidAlgebra R G) :
    IsRegularCocycle₁ b ↔
      Coalgebra.comul.lTensor V b =
        TensorProduct.assoc R V (MonoidAlgebra R G) (MonoidAlgebra R G)
          ((coact (R := R) (C := MonoidAlgebra R G) (M := V)).rTensor _ b +
            b ⊗ₜ[R] MonoidAlgebra.single 1 1) := (Iff.rfl)

variable {V : Type w} [AddCommGroup V] [Module R V] [Comodule R (MonoidAlgebra R G) V]

/-- The regular coboundary map, sending `v` to the cochain `g ↦ v - g • v`. -/
noncomputable def regularCoboundary : V →ₗ[R] V ⊗[R] MonoidAlgebra R G :=
  (TensorProduct.mk R V (MonoidAlgebra R G)).flip (MonoidAlgebra.single 1 1) -
    coact (R := R) (C := MonoidAlgebra R G)

/-- A regular coboundary is the constant cochain minus the coaction.

This is not a `simp` lemma: keeping `regularCoboundary` folded lets the coefficient
and cocycle simp lemmas apply. -/
theorem regularCoboundary_apply (v : V) :
    regularCoboundary (R := R) (G := G) v =
      v ⊗ₜ[R] MonoidAlgebra.single 1 1 - coact (R := R) (C := MonoidAlgebra R G) v := (rfl)

/-- The identity-character coefficient of a coboundary is its representative minus
its invariant weight component. -/
@[simp]
theorem tensorComponent_monoidCoeff_one_regularCoboundary (v : V) :
    LinearMap.tensorComponent (monoidCoeff R G 1) (regularCoboundary (R := R) (G := G) v) =
      v - weightProj R G V 1 v := by
  classical
  simp [regularCoboundary_apply, weightProj_apply]

/-- A regular cocycle is the coboundary of its identity-character coefficient. -/
theorem eq_regularCoboundary_tensorComponent_monoidCoeff_one {b : V ⊗[R] MonoidAlgebra R G}
    (hb : IsRegularCocycle₁ b) :
    b = regularCoboundary (LinearMap.tensorComponent (monoidCoeff R G 1) b) := by
  classical
  rw [isRegularCocycle₁_iff] at hb
  have h := congrArg (fun t ↦ LinearMap.tensorComponent (monoidCoeff R G 1)
    ((TensorProduct.assoc R V (MonoidAlgebra R G) (MonoidAlgebra R G)).symm t)) hb
  rw [LinearMap.tensorComponent_assoc_symm, tensorComponent_monoidCoeff_comul_lTensor] at h
  simp only [LinearEquiv.symm_apply_apply, map_add, LinearMap.tensorComponent_tmul,
    tensorComponent_rTensor_coact, monoidCoeff_apply, MonoidAlgebra.coeff_single,
    Finsupp.single_eq_same, one_smul] at h
  rw [regularCoboundary_apply]
  exact (eq_sub_iff_add_eq).mpr (by simpa only [add_comm] using h.symm)

/-- A coboundary satisfies the regular cocycle identity. -/
@[simp]
theorem isRegularCocycle₁_regularCoboundary (v : V) :
    IsRegularCocycle₁ (regularCoboundary (R := R) (G := G) v) := by
  rw [isRegularCocycle₁_iff, regularCoboundary_apply]
  simp only [map_sub, map_add, LinearMap.lTensor_tmul, LinearMap.rTensor_tmul,
    TensorProduct.sub_tmul, TensorProduct.assoc_tmul, MonoidAlgebra.comul_single,
    CommSemiring.comul_apply, TensorProduct.map_tmul, MonoidAlgebra.lsingle_apply,
    coassoc_apply]
  abel

/-- Every regular one-cocycle has a unique coboundary representative whose invariant
weight component vanishes. Thus the coboundary representative is determined without
choosing a complement to the invariant submodule. -/
theorem existsUnique_weightProj_one_eq_zero_and_eq_regularCoboundary
    {b : V ⊗[R] MonoidAlgebra R G}
    (hb : IsRegularCocycle₁ b) :
    ∃! v : V, weightProj R G V 1 v = 0 ∧ b = regularCoboundary v := by
  let v := LinearMap.tensorComponent (monoidCoeff R G 1) b
  have hv := eq_regularCoboundary_tensorComponent_monoidCoeff_one hb
  have hc := congrArg (LinearMap.tensorComponent (monoidCoeff R G 1)) hv
  have hzero : weightProj R G V 1 v = 0 := by
    simpa only [tensorComponent_monoidCoeff_one_regularCoboundary, sub_eq_self, v] using hc.symm
  refine ⟨v, ⟨hzero, hv⟩, ?_⟩
  rintro w ⟨hw, hbw⟩
  have h := congrArg (LinearMap.tensorComponent (monoidCoeff R G 1)) hbw
  simpa only [tensorComponent_monoidCoeff_one_regularCoboundary, hw, sub_zero, v] using h.symm

/-- The regular cocycle equation is equivalent to being a coboundary. This is vanishing
of rational first cohomology with module coefficients for a diagonalizable group. -/
theorem isRegularCocycle₁_iff_exists_eq_regularCoboundary (b : V ⊗[R] MonoidAlgebra R G) :
    IsRegularCocycle₁ b ↔ ∃ v : V, b = regularCoboundary v := by
  constructor
  · intro hb
    exact ⟨_, eq_regularCoboundary_tensorComponent_monoidCoeff_one hb⟩
  · rintro ⟨v, rfl⟩
    exact isRegularCocycle₁_regularCoboundary v

end TauCeti.Comodule

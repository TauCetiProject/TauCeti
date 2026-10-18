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

The result works over any commutative ring, with no finiteness, smoothness, or
characteristic restriction. In the group-scheme interpretation `G` is an abelian group
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

variable {R : Type u} [CommRing R] {G : Type v} [One G]
  {V : Type w} [AddCommGroup V] [Module R V] [Comodule R (MonoidAlgebra R G) V]

/-- A regular cocycle is the coboundary of its identity-character coefficient.
The multiplication identity is written in `V ⊗ (R[G] ⊗ R[G])`. -/
theorem eq_coboundary_monoidCoeff_one {b : V ⊗[R] MonoidAlgebra R G}
    (hb : Coalgebra.comul.lTensor V b =
      TensorProduct.assoc R V (MonoidAlgebra R G) (MonoidAlgebra R G)
        ((coact (R := R) (C := MonoidAlgebra R G) (M := V)).rTensor _ b +
          b ⊗ₜ[R] MonoidAlgebra.single 1 1)) :
    b = LinearMap.tensorComponent (monoidCoeff R G 1) b ⊗ₜ[R]
        MonoidAlgebra.single 1 1 -
      coact (R := R) (C := MonoidAlgebra R G)
        (LinearMap.tensorComponent (monoidCoeff R G 1) b) := by
  have hleft :
      LinearMap.tensorComponent (monoidCoeff R G 1)
          ((TensorProduct.assoc R V (MonoidAlgebra R G) (MonoidAlgebra R G)).symm
            (Coalgebra.comul.lTensor V b)) =
        LinearMap.tensorComponent (monoidCoeff R G 1) b ⊗ₜ[R]
          MonoidAlgebra.single 1 1 := by
    clear hb
    induction b using TensorProduct.inductionOn with
    | add b c hb hc => simp [hb, hc, TensorProduct.add_tmul]
    | tmul v a =>
      rw [LinearMap.tensorComponent_assoc_symm, LinearMap.lTensor_tmul,
        LinearMap.lTensor_tmul, tensorComponent_monoidCoeff_comul]
      simp only [LinearMap.tensorComponent_tmul, monoidCoeff_apply,
        TensorProduct.smul_tmul, MonoidAlgebra.smul_single, smul_eq_mul, mul_one]
  classical
  have h := congrArg (fun t ↦ LinearMap.tensorComponent (monoidCoeff R G 1)
    ((TensorProduct.assoc R V (MonoidAlgebra R G) (MonoidAlgebra R G)).symm t)) hb
  rw [hleft] at h
  simp only [LinearEquiv.symm_apply_apply, map_add, LinearMap.tensorComponent_tmul,
    monoidCoeff_apply, MonoidAlgebra.coeff_single] at h
  rw [← LinearMap.comp_apply, ← coact_comp_tensorComponent, LinearMap.comp_apply] at h
  exact (eq_sub_iff_add_eq).mpr (by simpa [add_comm] using h.symm)

/-- A coboundary satisfies the regular cocycle identity. -/
theorem comul_lTensor_coboundary (v : V) :
    Coalgebra.comul.lTensor V
        (v ⊗ₜ[R] MonoidAlgebra.single (1 : G) 1 -
          coact (R := R) (C := MonoidAlgebra R G) v) =
      TensorProduct.assoc R V (MonoidAlgebra R G) (MonoidAlgebra R G)
        ((coact (R := R) (C := MonoidAlgebra R G) (M := V)).rTensor _
            (v ⊗ₜ[R] MonoidAlgebra.single 1 1 -
              coact (R := R) (C := MonoidAlgebra R G) v) +
          (v ⊗ₜ[R] MonoidAlgebra.single 1 1 -
            coact (R := R) (C := MonoidAlgebra R G) v) ⊗ₜ[R]
              MonoidAlgebra.single 1 1) := by
  simp only [map_sub, map_add, LinearMap.lTensor_tmul, LinearMap.rTensor_tmul,
    TensorProduct.sub_tmul, TensorProduct.assoc_tmul, MonoidAlgebra.comul_single,
    CommSemiring.comul_apply, TensorProduct.map_tmul, MonoidAlgebra.lsingle_apply,
    coassoc_apply]
  abel

/-- Every regular one-cocycle has a unique coboundary representative whose invariant
weight component vanishes. Thus the coboundary representative is determined without
choosing a complement to the invariant submodule. -/
theorem existsUnique_coboundary_weightProj_one_eq_zero {b : V ⊗[R] MonoidAlgebra R G}
    (hb : Coalgebra.comul.lTensor V b =
      TensorProduct.assoc R V (MonoidAlgebra R G) (MonoidAlgebra R G)
        ((coact (R := R) (C := MonoidAlgebra R G) (M := V)).rTensor _ b +
          b ⊗ₜ[R] MonoidAlgebra.single 1 1)) :
    ∃! v : V, weightProj R G V 1 v = 0 ∧
      b = v ⊗ₜ[R] MonoidAlgebra.single 1 1 -
        coact (R := R) (C := MonoidAlgebra R G) v := by
  classical
  let v := LinearMap.tensorComponent (monoidCoeff R G 1) b
  have hv := eq_coboundary_monoidCoeff_one hb
  have hc := congrArg (LinearMap.tensorComponent (monoidCoeff R G 1)) hv
  have hzero : weightProj R G V 1 v = 0 := by
    simpa only [map_sub, LinearMap.tensorComponent_tmul, monoidCoeff_apply,
      MonoidAlgebra.coeff_single, Finsupp.single_eq_same, one_smul, ← weightProj_apply,
      sub_eq_self, v] using hc.symm
  refine ⟨v, ⟨hzero, hv⟩, ?_⟩
  rintro w ⟨hw, hbw⟩
  have h := congrArg (LinearMap.tensorComponent (monoidCoeff R G 1)) hbw
  simpa only [map_sub, LinearMap.tensorComponent_tmul, monoidCoeff_apply,
    MonoidAlgebra.coeff_single, Finsupp.single_eq_same, one_smul, ← weightProj_apply,
    hw, sub_zero, v] using h.symm

/-- The regular cocycle equation is equivalent to being a coboundary. This is vanishing
of rational first cohomology with module coefficients for a diagonalizable group. -/
theorem one_cocycle_iff_exists_coboundary (b : V ⊗[R] MonoidAlgebra R G) :
    (Coalgebra.comul.lTensor V b =
      TensorProduct.assoc R V (MonoidAlgebra R G) (MonoidAlgebra R G)
        ((coact (R := R) (C := MonoidAlgebra R G) (M := V)).rTensor _ b +
          b ⊗ₜ[R] MonoidAlgebra.single 1 1)) ↔
      ∃ v : V, b = v ⊗ₜ[R] MonoidAlgebra.single 1 1 -
        coact (R := R) (C := MonoidAlgebra R G) v := by
  constructor
  · intro hb
    exact ⟨_, eq_coboundary_monoidCoeff_one hb⟩
  · rintro ⟨v, rfl⟩
    exact comul_lTensor_coboundary v

end TauCeti.Comodule

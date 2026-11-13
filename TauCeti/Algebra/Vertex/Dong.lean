/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Vertex.Axioms
public import TauCeti.Algebra.Vertex.ResidueProduct
import Mathlib.Tactic.Module
import Mathlib.Tactic.NoncommRing
import TauCeti.Algebra.Ring.Commute
import TauCeti.Algebra.Vertex.FormalDistribution.ThreeVariable
import TauCeti.Data.Nat.Choose.Sum

/-!
# Dong's lemma for nonnegative residue products

If three fields `A(z)`, `B(z)` and `C(z)` are pairwise mutually local, then every nonnegative
residue product `A₍ₙ₎B = Res_z (z - w)ⁿ [A(z), B(w)]` is again local with `C(z)`
(`VertexOperator.IsLocalOfOrder.nonnegResidueProduct`). Explicitly, if the three pairs are local
of orders `N_AB`, `N_AC` and `N_BC`, then `A₍ₙ₎B` and `C` are local of order
`N_AB + N_AC + N_BC`, for every `n`.

The proof works with the three-variable distribution `[[A(x), B(w)], C(z)]`, read
coefficientwise, on which multiplication by `x - w`, `x - z` and `w - z` are commuting
operators (`TauCeti.FormalDistribution.mulX` and its analogues). By the Jacobi identity it is
the sum of `[A(x), [B(w), C(z)]]`, killed by `(w - z)^N_BC`, and `[[A(x), C(z)], B(w)]`,
killed by `(x - z)^N_AC`, while the whole distribution is killed by `(x - w)^N_AB`. Writing
`w - z = (x - z) - (x - w)` and expanding, every term of `(w - z)^(N_AB + N_AC + N_BC)` falls
under one of these three annihilators (`Commute.sub_pow_smul_add_eq_zero`).
Taking the residue against `(x - w)ⁿ` commutes with multiplication by `w - z`.

In a formal vertex algebra all fields are pairwise local, so every nonnegative residue product
of two fields `Y(a,z)` and `Y(b,z)` is local with every field `Y(c,z)`
(`TauCeti.FormalVertexAxioms.exists_isLocalOfOrder_nonnegResidueProduct`). This is the locality
hypothesis of Goddard's uniqueness theorem for these products, as used for the commutator
formula and the reconstruction of vertex algebras from generating fields.

## Main results

* `VertexOperator.IsLocalOfOrder.nonnegResidueProduct`: Dong's lemma for nonnegative residue
  products.
* `TauCeti.FormalVertexAxioms.exists_isLocalOfOrder_nonnegResidueProduct`: in a formal vertex
  algebra, `Y(a,z)₍ₙ₎Y(b,z)` is local with every `Y(c,z)`.

## References

* V. Kac, *Vertex Algebras for Beginners*, 2nd ed., Chapter 3, Dong's lemma, whose proof by
  expanding `w - z = (x - z) - (x - w)` is followed here.
* H. Li, *Local systems of vertex operators, vertex superalgebras and modules*, J. Pure Appl.
  Algebra 109 (1996), where the lemma is attributed to C. Dong.
-/

public section

noncomputable section

open Finset TauCeti.FormalDistribution
open scoped VertexOperator

namespace VertexOperator

/-! ### Dong's lemma -/

variable {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]

/-- **Dong's lemma** for nonnegative residue products: if `A`, `B` and `C` are pairwise mutually
local, of orders `N_AB`, `N_AC` and `N_BC`, then every residue product
`A₍ₙ₎B = Res_z (z - w)ⁿ [A(z), B(w)]` is local with `C`, of order `N_AB + N_AC + N_BC`. -/
theorem IsLocalOfOrder.nonnegResidueProduct {A B C : VertexOperator R V} {Nab Nac Nbc : ℕ}
    (hAB : A.IsLocalOfOrder B Nab) (hAC : A.IsLocalOfOrder C Nac)
    (hBC : B.IsLocalOfOrder C Nbc) (n : ℕ) :
    (nonnegResidueProduct n A B).IsLocalOfOrder C (Nab + Nac + Nbc) := by
  -- The coefficients of `[[A(x), B(w)], C(z)]` and of its two Jacobi summands.
  set d : ℤ → ℤ → ℤ → Module.End R V := fun a b c ↦
    (A[[a]] * B[[b]] - B[[b]] * A[[a]]) * C[[c]] - C[[c]] * (A[[a]] * B[[b]] - B[[b]] * A[[a]])
  set d₁ : ℤ → ℤ → ℤ → Module.End R V := fun a b c ↦
    A[[a]] * (B[[b]] * C[[c]] - C[[c]] * B[[b]]) - (B[[b]] * C[[c]] - C[[c]] * B[[b]]) * A[[a]]
  set d₂ : ℤ → ℤ → ℤ → Module.End R V := fun a b c ↦
    (A[[a]] * C[[c]] - C[[c]] * A[[a]]) * B[[b]] - B[[b]] * (A[[a]] * C[[c]] - C[[c]] * A[[a]])
  have hjac : d = d₁ + d₂ := by
    funext a b c
    simp only [d, d₁, d₂, Pi.add_apply]
    noncomm_ring
  have hab : ((mulX - mulW : Module.End ℤ (ℤ → ℤ → ℤ → Module.End R V)) ^ Nab) d = 0 := by
    funext a b c
    simp only [(commute_mulX_mulW (M := Module.End R V)).sub_pow',
      LinearMap.sum_apply, Finset.sum_apply, LinearMap.smul_apply, Pi.smul_apply, mul_apply_eq_comp,
      mulX_pow_apply, mulW_pow_apply, d, Pi.zero_apply]
    -- Take the commutator with `C[[c]]` of a locality relation between the other two fields.
    have h := congr_arg (AddMonoidHom.mulRight (C[[c]]) - AddMonoidHom.mulLeft (C[[c]]))
      (isLocalOfOrder_iff.mp hAB a b)
    simpa only [map_sum, map_nsmul, map_zsmul, map_zero, AddMonoidHom.sub_apply,
      AddMonoidHom.mulRight_apply, AddMonoidHom.coe_mulLeft] using h
  have hac : ((mulX - mulZ : Module.End ℤ (ℤ → ℤ → ℤ → Module.End R V)) ^ Nac) d₂ = 0 := by
    funext a b c
    simp only [(commute_mulX_mulZ (M := Module.End R V)).sub_pow',
      LinearMap.sum_apply, Finset.sum_apply, LinearMap.smul_apply, Pi.smul_apply, mul_apply_eq_comp,
      mulX_pow_apply, mulZ_pow_apply, d₂, Pi.zero_apply]
    -- Take the commutator with `B[[b]]` of a locality relation between the other two fields.
    have h := congr_arg (AddMonoidHom.mulRight (B[[b]]) - AddMonoidHom.mulLeft (B[[b]]))
      (isLocalOfOrder_iff.mp hAC a c)
    simpa only [map_sum, map_nsmul, map_zsmul, map_zero, AddMonoidHom.sub_apply,
      AddMonoidHom.mulRight_apply, AddMonoidHom.coe_mulLeft] using h
  have hbc : ((mulW - mulZ : Module.End ℤ (ℤ → ℤ → ℤ → Module.End R V)) ^ Nbc) d₁ = 0 := by
    funext a b c
    simp only [(commute_mulW_mulZ (M := Module.End R V)).sub_pow',
    LinearMap.sum_apply, Finset.sum_apply, LinearMap.smul_apply, Pi.smul_apply, mul_apply_eq_comp,
      mulW_pow_apply, mulZ_pow_apply, d₁, Pi.zero_apply]
    -- Take the commutator of `A[[a]]` with a locality relation between `B` and `C`.
    have h := congr_arg (AddMonoidHom.mulLeft (A[[a]]) - AddMonoidHom.mulRight (A[[a]]))
      (isLocalOfOrder_iff.mp hBC b c)
    simpa only [map_sum, map_nsmul, map_zsmul, map_zero, AddMonoidHom.sub_apply,
      AddMonoidHom.mulRight_apply, AddMonoidHom.coe_mulLeft] using h
  have key : ((mulW - mulZ : Module.End ℤ (ℤ → ℤ → ℤ → Module.End R V)) ^ (Nab + Nac + Nbc)) d =
      0 := by
    rw [← Module.End.smul_def, hjac] at hab ⊢
    rw [← Module.End.smul_def] at hac hbc
    exact commute_mulX_mulW.sub_pow_smul_add_eq_zero commute_mulX_mulZ commute_mulW_mulZ hab hac hbc
  -- Expand the residue product and exchange the two binomial sums; each inner sum is a
  -- coefficient of `(w - z)^(N_AB + N_AC + N_BC) [[A(x), B(w)], C(z)] = 0`.
  rw [isLocalOfOrder_iff]
  intro p q
  simp only [ncoeff_nonnegResidueProduct, sum_mul, mul_sum, ← sum_sub_distrib, smul_mul_assoc,
    mul_smul_comm, ← smul_sub, smul_sum]
  rw [sum_comm]
  refine sum_eq_zero fun kl _ ↦ ?_
  have hk := congr_fun (congr_fun (congr_fun key kl.1) (p + kl.2)) q
  simp only [(commute_mulW_mulZ (M := Module.End R V)).sub_pow',
    LinearMap.sum_apply, Finset.sum_apply, LinearMap.smul_apply, Pi.smul_apply, mul_apply_eq_comp,
    mulW_pow_apply, mulZ_pow_apply, d, Pi.zero_apply] at hk
  rw [← smul_zero (n.choose kl.1), ← smul_zero ((-1 : ℤ) ^ kl.2), ← hk, smul_sum, smul_sum]
  refine sum_congr rfl fun ij _ ↦ ?_
  rw [show p + ij.1 + kl.2 = p + kl.2 + ij.1 by ring]
  module

end VertexOperator

namespace TauCeti.FormalVertexAxioms

open VertexOperator

variable {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]

/-- In a formal vertex algebra, every nonnegative residue product `Y(a,z)₍ₙ₎Y(b,z)` of two fields
is local with every field `Y(c,z)`. -/
theorem exists_isLocalOfOrder_nonnegResidueProduct (A : FormalVertexAxioms R V) (n : ℕ)
    (a b c : V) :
    ∃ N, (nonnegResidueProduct n (A.field a) (A.field b)).IsLocalOfOrder (A.field c) N := by
  obtain ⟨_, hab⟩ := A.exists_isLocalOfOrder a b
  obtain ⟨_, hac⟩ := A.exists_isLocalOfOrder a c
  obtain ⟨_, hbc⟩ := A.exists_isLocalOfOrder b c
  exact ⟨_, hab.nonnegResidueProduct hac hbc n⟩

end TauCeti.FormalVertexAxioms

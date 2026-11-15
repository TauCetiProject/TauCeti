/-
Copyright (c) 2024 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import TauCeti.NumberTheory.HeckeRing.LeftCosetModule.Action
public import Mathlib.Data.Finsupp.Weight

/-!
# Hecke rings: the degree homomorphism

The degree of a double coset `HgH = ⊔ᵢ σᵢgH` is the number of left cosets in its
decomposition, `deg(HgH) = [H : H ∩ gHg⁻¹]`. Extended linearly it gives the degree
homomorphism `deg : 𝕋 Δ H R →+* R` of the Hecke ring (Proposition 3.3 of
[Shimura][shimura1971]). Multiplicativity is proved through the module of left cosets:
`deg f` is the coefficient sum of `f • [H]`, and the action satisfies the compatibility law
`op (f * g) • m = op g • (op f • m)` — `mul_smul` of the opposite ring
(Proposition 3.4) — so the coefficient sum multiplies.

Ported from the AINTLIB `LeanModularForms` project
(`HeckeRIngs/AbstractHeckeRing/Degree.lean` and the compatibility law of
`HeckeRIngs/AbstractHeckeRing/Associativity.lean`,
<https://github.com/CBirkbeck/AINTLIB/tree/main/projects/LeanModularForms>). The
compatibility law is exposed through the `Module (𝕋 Δ H R)ᵐᵒᵖ` instance, rather than through
AINTLIB's reversed scalar action.

## Main definitions

* `LeftCosetModule.deg`: the degree homomorphism `𝕋 Δ H R →+* R` over any semiring of
  coefficients, built on Mathlib's
  coefficient sum `Finsupp.degree` of the left-coset module.

## Main results

* `LeftCosetModule.degree_single_smul_single`: the coefficient sum of a basis element acting
  on a basis element is the degree of the double coset times the product of coefficients.
* `LeftCosetModule.degree_smul`: acting by `t` multiplies the coefficient sum by `deg t`.
* `LeftCosetModule.deg_single`, `RingHom` laws of `deg`: Proposition 3.3.
-/

public section

open DoubleCoset Subgroup

variable {G : Type*} [Group G] {Δ : Submonoid G} {H : Subgroup G}

namespace LeftCosetModule

open HeckeCoset

open scoped HeckeCosetModule Pointwise

variable [IsHeckeTriple Δ H H] {R : Type*}

section NonUnital

variable [NonUnitalNonAssocSemiring R]

/-- The coefficient sum of the action of a ring basis element on a module basis element:
the degree of the double coset appears as the orbit size. Only the additive structure and
the single product `b * a` are involved, so no unit or associativity is needed. -/
-- not `@[simp]`: the left-hand side is itself reduced by `single_smul_single`, `map_sum`,
-- `Finsupp.degree_single` and `Finset.sum_const`, so the env linter rejects it as a
-- non-normal form
lemma degree_single_smul_single (D : HeckeCoset Δ H H) (q : HeckeCoset Δ ⊥ H)
    (a b : R) :
    Finsupp.degree (MulOpposite.op (HeckeCosetModule.single R D a) •
      Finsupp.single q b) = (D.degree : ℕ) • (b * a) := by
  classical
  rw [single_smul_single, map_sum]
  simp [HeckeCoset.degree_eq_card_decompQuotient, smulOrbit_card]

end NonUnital

variable [Semiring R]

/-- The coefficient sum is multiplicative against the action: the orbit-sum coefficient is
independent of the acted-on coset, so the action factors through its value on the identity
coset. Stated before `deg` exists; `degree_smul` is the public form. -/
private lemma degree_smul_eq_degree_mul (t : 𝕋 Δ H R) (m : LeftCosetModule Δ H R) :
    Finsupp.degree (MulOpposite.op t • m) =
      Finsupp.degree m *
        Finsupp.degree (MulOpposite.op t • (Finsupp.single 1 1 : LeftCosetModule Δ H R)) := by
  induction t using HeckeCosetModule.induction_linear with
  | h0 => simp
  | hadd t₁ t₂ h₁ h₂ =>
    rw [MulOpposite.op_add, add_smul, add_smul, map_add, map_add, h₁, h₂, mul_add]
  | hsingle D a =>
    induction m using Finsupp.induction_linear with
    | zero => rw [smul_zero, map_zero, zero_mul]
    | add m₁ m₂ h₁ h₂ => rw [smul_add, map_add, map_add, h₁, h₂, add_mul]
    | single q c =>
      rw [degree_single_smul_single, degree_single_smul_single, Finsupp.degree_single,
        one_mul, mul_smul_comm]

variable (Δ H R) in
/-- **The degree homomorphism** (Shimura, Proposition 3.3): the coefficient sum of the
action on the identity coset, as a ring homomorphism `𝕋 Δ H R →+* R`. On a basis element
it is the degree of the double coset — the number of left cosets in its decomposition —
scaled by the coefficient; multiplicativity is the compatibility law `mul_smul` of the
`Module (𝕋 Δ H R)ᵐᵒᵖ` instance. -/
noncomputable def deg : 𝕋 Δ H R →+* R where
  toFun t := Finsupp.degree (MulOpposite.op t •
    (Finsupp.single 1 1 : LeftCosetModule Δ H R))
  map_one' := by
    rw [HeckeCosetModule.one_def, degree_single_smul_single, HeckeCoset.degree_one]
    simp
  map_mul' f g := by
    rw [MulOpposite.op_mul, mul_smul, degree_smul_eq_degree_mul]
  map_zero' := by
    rw [MulOpposite.op_zero, zero_smul, map_zero]
  map_add' f g := by rw [MulOpposite.op_add, add_smul, map_add]

/-- The defining equation of `deg`. -/
lemma deg_apply (t : 𝕋 Δ H R) :
    deg Δ H R t =
      Finsupp.degree (MulOpposite.op t •
        (Finsupp.single 1 1 : LeftCosetModule Δ H R)) := (rfl)

/-- The coefficient sum is multiplicative against the action: acting by `t` multiplies the
coefficient sum by `deg t`. -/
lemma degree_smul (t : 𝕋 Δ H R) (m : LeftCosetModule Δ H R) :
    Finsupp.degree (MulOpposite.op t • m) = Finsupp.degree m * deg Δ H R t :=
  degree_smul_eq_degree_mul t m

/-- The degree of a basis element: the degree of its double coset, scaled by the
coefficient. -/
@[simp] lemma deg_single (D : HeckeCoset Δ H H) (a : R) :
    deg Δ H R (HeckeCosetModule.single R D a) = D.degree • a := by
  rw [deg_apply, degree_single_smul_single, one_mul]

end LeftCosetModule

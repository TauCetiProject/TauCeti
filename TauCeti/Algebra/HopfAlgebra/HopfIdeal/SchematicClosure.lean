/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.HopfAlgebra.TensorProduct
public import TauCeti.Algebra.Coalgebra.BaseChange
public import TauCeti.Algebra.HopfAlgebra.HopfIdeal.Basic
public import TauCeti.RingTheory.Ideal.SchematicClosure

/-!
# Schematic closure of a closed subgroup of the generic fibre

Let `O` be a ring with fraction field `K` and `B` a commutative Hopf `O`-algebra, the coordinate
ring of an affine group scheme `𝒳` over `O`. A Hopf ideal `I` of `K ⊗[O] B` cuts out a closed
subgroup of the generic fibre. Its schematic closure in `𝒳` is cut out by the closure ideal
`I^♮ = B ∩ I` (`TauCeti.SchematicClosure.closureIdeal`), and this file shows that `I^♮` is a
Hopf ideal, so the closure is a closed subgroup scheme of `𝒳`.

The counit and antipode conditions follow directly from those of `I`, using that `O → K` is
injective. For the comultiplication, the image of `Δ b` in `(B ⧸ I^♮) ⊗[O] (B ⧸ I^♮)` becomes
zero after base change to `K`, because base change identifies that tensor square with the tensor
square over `K` of `(K ⊗[O] B) ⧸ I`. It is therefore zero when the tensor square is torsion-free
over `O`. That holds over a Dedekind domain, for instance a discrete valuation ring: there
`B ⧸ I^♮` is torsion-free, hence flat, and so is its tensor square.

The hypothesis that `K` is the fraction field cannot be dropped: for `O = ℤ`, `K = ℚ(√2)` and
the line `y = √2 x` in the additive group `G_a²`, the closure ideal is `(y² - 2x²)`, the ideal of
the union of that line and its conjugate, which is not a subgroup.

## Main definitions

* `TauCeti.HopfIdeal.schematicClosure`: the closure ideal of a Hopf ideal of the generic fibre,
  as a Hopf ideal.

## Main results

* `TauCeti.SchematicClosure.closureIdeal_isHopfIdeal`: the closure ideal of a Hopf ideal of the
  generic fibre is a Hopf ideal in Mathlib's sense.

## References

* F. Bruhat and J. Tits, *Groupes réductifs sur un corps local II*, Publ. Math. IHÉS 60
  (1984), 1.2.6–1.2.7.
-/

public section

open scoped TensorProduct

namespace TauCeti

universe u v w

open Algebra.TensorProduct SchematicClosure

variable {O : Type u} {K : Type v} {B : Type w}
variable [CommRing O] [CommRing K] [Algebra O K] [CommRing B] [HopfAlgebra O B]

namespace HopfIdeal

variable (I : HopfIdeal K (K ⊗[O] B))

/-- The closure ideal of a Hopf ideal of the generic fibre is stable under the antipode. -/
private theorem antipode_mem_closureIdeal {b : B} (hb : b ∈ closureIdeal K I.toIdeal) :
    HopfAlgebra.antipode O b ∈ closureIdeal K I.toIdeal := by
  have h := I.antipode_mem (mem_closureIdeal.mp hb)
  rw [TensorProduct.antipode_def, TensorProduct.AlgebraTensorModule.map_tmul] at h
  simpa using h

variable [IsFractionRing O K]

/-- The closure ideal of a Hopf ideal of the generic fibre kills the counit. -/
private theorem counit_eq_zero_of_mem_closureIdeal {b : B} (hb : b ∈ closureIdeal K I.toIdeal) :
    Coalgebra.counit (R := O) b = 0 := by
  have h := I.counit_eq_zero (mem_closureIdeal.mp hb)
  rw [TensorProduct.counit_tmul, Algebra.smul_def, Bialgebra.counit_one, mul_one] at h
  exact IsFractionRing.injective O K (by rw [h, map_zero])

variable [Module.IsTorsionFree O (closure K I.toIdeal ⊗[O] closure K I.toIdeal)]

/-- The comultiplication of an element of the closure ideal of a Hopf ideal of the generic fibre
vanishes in the tensor square of the closure, when that tensor square is torsion-free. -/
private theorem map_comul_eq_zero_of_mem_closureIdeal {b : B}
    (hb : b ∈ closureIdeal K I.toIdeal) :
    Algebra.TensorProduct.map (Ideal.Quotient.mkₐ O (closureIdeal K I.toIdeal))
      (Ideal.Quotient.mkₐ O (closureIdeal K I.toIdeal)) (Coalgebra.comul (R := O) b) = 0 := by
  have hQ : Algebra.TensorProduct.map (Ideal.Quotient.mkₐ K I.toIdeal)
      (Ideal.Quotient.mkₐ K I.toIdeal) (Coalgebra.comul (R := K) ((1 : K) ⊗ₜ[O] b)) = 0 := by
    rw [← RingHom.mem_ker, Ideal.ker_tensorProduct_map_quotient_quotient]
    exact I.comul_mem (mem_closureIdeal.mp hb)
  rw [Coalgebra.baseChange_comul_tmul K 1 b,
    ← closureGenericFiber_congr_distribBaseChange (nonZeroDivisors O), LinearEquiv.map_eq_zero_iff,
    LinearEquiv.map_eq_zero_iff] at hQ
  exact Module.IsTorsionFree.eq_zero_of_one_tmul_eq_zero (R := O) (K := K) hQ

/-- **The schematic closure of a closed subgroup.** For a Hopf ideal `I` of the generic fibre
`K ⊗[O] B`, the closure ideal `I^♮ = B ∩ I` is a Hopf ideal of `B`, provided the tensor square of
`B ⧸ I^♮` is torsion-free over `O`. Over a Dedekind domain this holds automatically. -/
noncomputable def schematicClosure : HopfIdeal O B :=
  ofIdeal (closureIdeal K I.toIdeal)
    (fun {b} hb ↦ by
      rw [← Ideal.ker_tensorProduct_map_quotient_quotient, RingHom.mem_ker]
      exact map_comul_eq_zero_of_mem_closureIdeal I hb)
    (fun {_} hb ↦ counit_eq_zero_of_mem_closureIdeal I hb)
    (fun {_} hb ↦ antipode_mem_closureIdeal I hb)

/-- The underlying ideal of the schematic closure is the closure ideal. -/
@[simp]
theorem schematicClosure_toIdeal : (schematicClosure I).toIdeal = closureIdeal K I.toIdeal :=
  (toIdeal_carrier _).trans (ofIdeal_carrier _ _ _ _)

/-- Membership in the schematic closure: `b ∈ I^♮` iff `1 ⊗ b ∈ I`. -/
@[simp]
theorem mem_schematicClosure {b : B} : b ∈ schematicClosure I ↔ (1 : K) ⊗ₜ[O] b ∈ I := by
  rw [← mem_toIdeal, schematicClosure_toIdeal, mem_closureIdeal, mem_toIdeal]

end HopfIdeal

namespace SchematicClosure

variable [IsFractionRing O K]

/-- **The closure of a closed subgroup is a closed subgroup.** For a Hopf ideal `I` of the
generic fibre `K ⊗[O] B`, the closure ideal `I^♮` is a Hopf ideal of `B` in Mathlib's sense,
provided the tensor square of `B ⧸ I^♮` is torsion-free over `O`, as it is over a Dedekind
domain. -/
theorem closureIdeal_isHopfIdeal (I : TauCeti.HopfIdeal K (K ⊗[O] B))
    [Module.IsTorsionFree O (closure K I.toIdeal ⊗[O] closure K I.toIdeal)] :
    (closureIdeal K I.toIdeal).IsHopfIdeal O :=
  HopfIdeal.instIsHopfIdeal (HopfIdeal.schematicClosure I)

end SchematicClosure

end TauCeti

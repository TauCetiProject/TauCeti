/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.CliffordAlgebra.Spin.SpecialOrthogonal
public import TauCeti.RepresentationTheory.Spin.Representation

/-!
# Clifford multiplication on the spinor module is Pin- and Spin-equivariant

Let `S = ⋀·W` be the Fock model of the spinor module of a polarized quadratic space `(V, Q)`, with
`c = TauCeti.spinAction Q P` the action of the Clifford algebra on it, so that a vector `v` acts by
the operator `c (ι Q v)`. The Pin group acts on `S` through `ρ = TauCeti.pinRep Q P`, and on `V`
through twisted conjugation, `CliffordAlgebra.pinToOrthogonal`. This file proves that the two are
compatible: for a Pin element `g` of parity `p`,

`ρ(g) c(v) ρ(g⁻¹) = (-1) ^ p • c(g • v)`,

and for a Spin element `g`, which has parity `0`, `ρ(g) c(v) ρ(g⁻¹) = c(g • v)`, with `g • v` the
action of `g` through `CliffordAlgebra.spinToSpecialOrthogonal`. In other words, Clifford
multiplication `V ⊗ S → S` is a map of Spin representations, and of Pin representations up to the
parity character.

The sign is where twisted conjugation enters: a Pin element acts on vectors by
`v ↦ involute g * v * g⁻¹`, and `involute g = (-1) ^ p • g` for `g` of parity `p`
(`CliffordAlgebra.involute_eq_of_mem_even`, `CliffordAlgebra.involute_eq_of_mem_odd`), while
`ρ(g) c(v) ρ(g⁻¹)` is the image under the algebra map `c` of the untwisted conjugate
`g * v * g⁻¹`. The inverse of a Pin element is its Clifford conjugate `star g`
(`pinGroup.star_eq_inv`). Every Pin element has a parity, by `pinGroup.exists_mem_evenOdd`, so the
parity hypothesis of the Pin statements can always be met.

## Main results

* `TauCeti.pinRep_mul_spinAction_ι`: `ρ(g) c(v) = (-1) ^ p • c(g • v) ρ(g)` for a Pin element of
  parity `p`, and `TauCeti.pinRep_mul_spinAction_ι_mul_pinRep_inv`, its conjugation form.
* `TauCeti.spinRep_mul_spinAction_ι` and `TauCeti.spinRep_mul_spinAction_ι_mul_spinRep_inv`: the
  sign-free Spin forms, with the action through the special orthogonal group.

## References

* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry* (1989), Chapter I §2 and §5.
-/

public section

namespace TauCeti

open CliffordAlgebra

universe u v

variable {K : Type u} [CommRing K] [Invertible (2 : K)]
variable {V : Type v} [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}
variable (P : SpinPolarizationData Q)

/-- **Clifford multiplication is Pin-equivariant up to parity**, in intertwining form: for a Pin
element `g` of parity `p`, acting on the spinor module by `ρ = TauCeti.pinRep Q P` and on vectors by
twisted conjugation, `ρ(g) c(v) = (-1) ^ p • c(g • v) ρ(g)`. -/
theorem pinRep_mul_spinAction_ι {p : ZMod 2} (g : pinGroup Q)
    (hg : (g : CliffordAlgebra Q) ∈ evenOdd Q p) (v : V) :
    pinRep Q P g * spinAction Q P (ι Q v) =
      ((-1 : ℤˣ) ^ p) • (spinAction Q P
        (ι Q (((pinToOrthogonal Q g : QuadraticMap.orthogonalGroup Q) : V ≃ₗ[K] V) v)) *
          pinRep Q P g) := by
  have hstar : star (g : CliffordAlgebra Q) * g = 1 := pinGroup.coe_star_mul_self g
  -- Both sides are images under the algebra map `spinAction Q P`; the inverse `star g` cancels on
  -- the right, leaving `g * v = (-1) ^ p • (involute g * v)`.
  rw [pinRep_apply, ι_pinToOrthogonal_apply, ← map_mul, ← map_mul, ← map_zsmul_unit, mul_assoc,
    mul_assoc, hstar, mul_one]
  congr 1
  obtain rfl | rfl : p = 0 ∨ p = 1 := by clear hg; revert p; decide
  · rw [involute_eq_of_mem_even hg, uzpow_zero, one_smul]
  · rw [involute_eq_of_mem_odd hg, uzpow_one, Units.neg_smul, one_smul, neg_mul, neg_neg]

/-- **Clifford multiplication is Pin-equivariant up to parity**: for a Pin element `g` of parity
`p`, acting on the spinor module by `ρ = TauCeti.pinRep Q P` and on vectors by twisted
conjugation, `ρ(g) c(v) ρ(g⁻¹) = (-1) ^ p • c(g • v)`. -/
theorem pinRep_mul_spinAction_ι_mul_pinRep_inv {p : ZMod 2} (g : pinGroup Q)
    (hg : (g : CliffordAlgebra Q) ∈ evenOdd Q p) (v : V) :
    pinRep Q P g * spinAction Q P (ι Q v) * pinRep Q P g⁻¹ =
      ((-1 : ℤˣ) ^ p) • spinAction Q P
        (ι Q (((pinToOrthogonal Q g : QuadraticMap.orthogonalGroup Q) : V ≃ₗ[K] V) v)) := by
  rw [pinRep_mul_spinAction_ι P g hg, smul_mul_assoc, mul_assoc, ← map_mul, mul_inv_cancel,
    map_one, mul_one]

/-- **Clifford multiplication is Spin-equivariant**, in intertwining form: a Spin element `g`
acting on the spinor module by `ρ = TauCeti.spinRep Q P` satisfies `ρ(g) c(v) = c(g • v) ρ(g)`,
where `g` acts on vectors through the special orthogonal group. -/
theorem spinRep_mul_spinAction_ι (g : spinGroup Q) (v : V) :
    spinRep Q P g * spinAction Q P (ι Q v) =
      spinAction Q P (ι Q
        (((spinToSpecialOrthogonal Q g : QuadraticMap.specialOrthogonalGroup Q) : V ≃ₗ[K] V) v)) *
        spinRep Q P g := by
  have h := pinRep_mul_spinAction_ι P (spinToPin Q g) (p := 0)
    (by rw [coe_spinToPin_apply]; exact spinGroup.mem_even g.2) v
  simpa using h

/-- **Clifford multiplication is Spin-equivariant**: a Spin element `g` acting on the spinor module
by `ρ = TauCeti.spinRep Q P` satisfies `ρ(g) c(v) ρ(g⁻¹) = c(g • v)`, where `g` acts on vectors
through the special orthogonal group. -/
theorem spinRep_mul_spinAction_ι_mul_spinRep_inv (g : spinGroup Q) (v : V) :
    spinRep Q P g * spinAction Q P (ι Q v) * spinRep Q P g⁻¹ =
      spinAction Q P (ι Q
        (((spinToSpecialOrthogonal Q g : QuadraticMap.specialOrthogonalGroup Q) : V ≃ₗ[K] V)
          v)) := by
  rw [spinRep_mul_spinAction_ι, mul_assoc, ← map_mul, mul_inv_cancel, map_one, mul_one]

end TauCeti

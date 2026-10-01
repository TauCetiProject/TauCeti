/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.Group.Profinite.Free.Peripheral.Automorphism

/-!
# The dyadic peripheral system

Let `F` be a free pro-`2` group on two generators, presented by a marked isomorphism
`e : F ≃ₜ* freeProP 2 (Fin 2)`. This file names its three peripheral elements

`P := basis e 0`, `T := basis e 1`, and `C := (P * T)⁻¹`.

Thus `C` is the cusp of the ordered basis and `P * T * C = 1`. The general peripheral product
identity and peripheral-power theorem specialize to consumer-facing statements with three named
conjugators: every dyadic unit exponent is realized by a continuous automorphism carrying each
peripheral element to a conjugate of its power by that exponent, and the corresponding three
conjugated powers multiply to one.

## Main definitions

* `TauCeti.Peripheral.periphP`: the first distinguished generator `basis e 0`.
* `TauCeti.Peripheral.periphT`: the second distinguished generator `basis e 1`.
* `TauCeti.Peripheral.periphC`: the third peripheral element `(periphP e * periphT e)⁻¹`, equal
  to `cusp (basis e)`.

## Main results

* `TauCeti.Peripheral.exists_peripheralPowerAutomorphism_two`: the dyadic peripheral-power
  theorem, with one conjugator for each of `P`, `T`, and `C`, and the `P`-conjugator equal to one.
* `TauCeti.Peripheral.exists_peripheral_identity_two`: the dyadic peripheral product identity in
  three-element form.

## References

* Y. Ihara, "Braids, Galois groups, and some arithmetic functions", Proc. ICM Kyoto 1990,
  99–120, for peripheral automorphisms of free pro-`p` groups of rank two and the role of the
  third conjugacy class.
-/

public section

namespace TauCeti

namespace Peripheral

variable {F : Type*} [Group F] [TopologicalSpace F] [IsTopologicalGroup F] [CompactSpace F]
  [TotallyDisconnectedSpace F]

/-- The first distinguished generator of a marked free pro-`2` group of rank two. -/
noncomputable def periphP (e : F ≃ₜ* freeProP 2 (Fin 2)) : F :=
  basis e 0

/-- The second distinguished generator of a marked free pro-`2` group of rank two. -/
noncomputable def periphT (e : F ≃ₜ* freeProP 2 (Fin 2)) : F :=
  basis e 1

/-- The third peripheral element `C := (P * T)⁻¹` of a marked free pro-`2` group of rank two. -/
noncomputable def periphC (e : F ≃ₜ* freeProP 2 (Fin 2)) : F :=
  (periphP e * periphT e)⁻¹

omit [IsTopologicalGroup F] [CompactSpace F] [TotallyDisconnectedSpace F] in
/-- The first dyadic peripheral element is the first element of the ordered basis. -/
@[simp]
theorem periphP_eq_basis (e : F ≃ₜ* freeProP 2 (Fin 2)) : periphP e = basis e 0 := by
  simp [periphP]

omit [IsTopologicalGroup F] [CompactSpace F] [TotallyDisconnectedSpace F] in
/-- The second dyadic peripheral element is the second element of the ordered basis. -/
@[simp]
theorem periphT_eq_basis (e : F ≃ₜ* freeProP 2 (Fin 2)) : periphT e = basis e 1 := by
  simp [periphT]

omit [IsTopologicalGroup F] [CompactSpace F] [TotallyDisconnectedSpace F] in
/-- The third dyadic peripheral element is the inverse of the product of the first two. -/
theorem periphC_def (e : F ≃ₜ* freeProP 2 (Fin 2)) :
    periphC e = (periphP e * periphT e)⁻¹ := by
  simp [periphC]

omit [IsTopologicalGroup F] [CompactSpace F] [TotallyDisconnectedSpace F] in
/-- The third dyadic peripheral element is the cusp of the ordered basis. -/
@[simp]
theorem periphC_eq_cusp (e : F ≃ₜ* freeProP 2 (Fin 2)) : periphC e = cusp (basis e) := by
  simp [periphC_def, cusp_def, List.ofFn_succ]

omit [IsTopologicalGroup F] [CompactSpace F] [TotallyDisconnectedSpace F] in
/-- The three dyadic peripheral elements satisfy the ordered peripheral relation
`P * T * C = 1`. -/
theorem periphP_mul_periphT_mul_periphC (e : F ≃ₜ* freeProP 2 (Fin 2)) :
    periphP e * periphT e * periphC e = 1 := by
  rw [periphC_def]
  simp

/-- For every dyadic unit `u`, a marked free pro-`2` group of rank two has a continuous
automorphism carrying `P`, `T`, and `C` to conjugates of their `u`-th powers. The conjugator of
`P` is normalized to be one. -/
theorem exists_peripheralPowerAutomorphism_two (hF : IsProP 2 F)
    (e : F ≃ₜ* freeProP 2 (Fin 2)) (u : ℤ_[2]ˣ) :
    ∃ (φ : ContinuousAut F) (cP cT cC : F), cP = 1 ∧
      φ (periphP e) = cP⁻¹ * hF.padicPow (periphP e) u * cP ∧
      φ (periphT e) = cT⁻¹ * hF.padicPow (periphT e) u * cT ∧
      φ (periphC e) = cC⁻¹ * hF.padicPow (periphC e) u * cC := by
  obtain ⟨φ, c, d, hc0, hc, hd⟩ := exists_peripheralAut hF e u
  refine ⟨φ, c 0, c 1, d, ?_, ?_, ?_, ?_⟩
  · simpa using hc0 (by omega)
  · simpa using hc 0
  · simpa using hc 1
  · simpa using hd

/-- For every dyadic unit `u`, there are conjugators, with the `P`-conjugator equal to one, such
that the conjugates of the `u`-th powers of `P`, `T`, and `C` multiply to one in peripheral
order. -/
theorem exists_peripheral_identity_two (hF : IsProP 2 F)
    (e : F ≃ₜ* freeProP 2 (Fin 2)) (u : ℤ_[2]ˣ) :
    ∃ cP cT cC : F, cP = 1 ∧
      (cP⁻¹ * hF.padicPow (periphP e) u * cP) *
          (cT⁻¹ * hF.padicPow (periphT e) u * cT) *
        (cC⁻¹ * hF.padicPow (periphC e) u * cC) = 1 := by
  obtain ⟨c, d, hc0, h⟩ := exists_defect_eq_one hF e u
  refine ⟨c 0, c 1, d, ?_, ?_⟩
  · simpa using hc0 (by omega)
  · simpa [defect_def, List.ofFn_succ] using h

end Peripheral

end TauCeti

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.ConjugationTransfer
public import TauCeti.Topology.Algebra.Group.Profinite.Free.Automorphism
public import TauCeti.Topology.Algebra.Group.Profinite.Free.Peripheral.Identity

/-!
# Peripheral automorphisms of every exponent

Let `F` be a free pro-`p` group of rank `r` with basis `x : Fin r → F` and cusp
`z = (x_0 ⋯ x_{r-1})⁻¹`. For every unit `u ∈ ℤ_pˣ` there is a continuous automorphism `φ` of `F`
and conjugators `c : Fin r → F`, `d : F`, with `c 0 = 1` in positive rank, such that

`φ (x i) = (c i)⁻¹ * x i ^ u * c i` and `φ z = d⁻¹ * z ^ u * d`,

where `^ u` is the `p`-adic power. In particular `φ` is peripheral of exponent `u`, and it carries
the first basis element to its `u`-th power on the nose.

The automorphism is the one prescribed on the basis by the conjugators of the peripheral product
identity (`TauCeti.Peripheral.exists_defect_eq_one`); it is an automorphism by the criterion for
conjugated unit powers (`TauCeti.IsProP.exists_continuousAut_apply_eq_conj_padicPow_const`, which
rests on Burnside's basis theorem and the Hopf property). The identity says exactly that the image
of `x_0 ⋯ x_{r-1}` is the inverse of the conjugate `d⁻¹ * z ^ u * d`, which is the value on the
cusp.

The same automorphism carries every conjugate `q * z * q⁻¹` of the cusp to a conjugate of its
`u`-th power, with the conjugator `q * d * (φ q)⁻¹` computed by the conjugation-transfer lemma
`TauCeti.map_conj_eq_conj_of_map_eq_conj`. This covers any other convention for the last
peripheral element, such as `(x_1 x_0)⁻¹ = x_0⁻¹ * z * x_0` in rank two.

The assignment `u ↦ φ` is not canonical: it depends on the choice of conjugators.

## Main results

* `TauCeti.Peripheral.exists_peripheralAut`: **the peripheral-power theorem**, the existence of
  a continuous automorphism with prescribed normalized conjugators, for every unit exponent.
* `TauCeti.Peripheral.exists_peripheralAut_conj_cusp`: the same, with the value on every
  conjugate of the cusp.
* `TauCeti.Peripheral.exists_isPeripheralAut`: for every unit `u`, the basis of a free pro-`p`
  group admits a peripheral automorphism of exponent `u`.

## References

* Y. Ihara, "Braids, Galois groups, and some arithmetic functions", Proc. ICM Kyoto 1990,
  99–120, for the peripheral automorphisms `x ↦ x ^ λ`, `y ↦ f⁻¹ y ^ λ f` of free pro-`p` groups
  of rank two, which Ihara obtains from the Galois action on the fundamental group of the
  thrice-punctured line.
-/

public section

namespace TauCeti

namespace Peripheral

variable {p r : ℕ} [Fact p.Prime] {F : Type*} [Group F] [TopologicalSpace F]
  [IsTopologicalGroup F] [CompactSpace F] [TotallyDisconnectedSpace F]

/-- **The peripheral-power theorem.** For every unit `u ∈ ℤ_pˣ` there are a continuous
automorphism `φ` of `F`, conjugators `c` on the basis `x = basis e`, with `c 0 = 1` in positive
rank, and a conjugator `d` on the cusp, such that `φ (x i) = (c i)⁻¹ * x i ^ u * c i` for every
`i` and `φ (cusp x) = d⁻¹ * cusp x ^ u * d`, where `^ u` is the `p`-adic power. -/
theorem exists_peripheralAut (hF : IsProP p F) (e : F ≃ₜ* freeProP p (Fin r)) (u : ℤ_[p]ˣ) :
    ∃ (φ : ContinuousAut F) (c : Fin r → F) (d : F), (∀ h0 : 0 < r, c ⟨0, h0⟩ = 1) ∧
      (∀ i, φ (basis e i) = (c i)⁻¹ * hF.padicPow (basis e i) u * c i) ∧
      φ (cusp (basis e)) = d⁻¹ * hF.padicPow (cusp (basis e)) u * d := by
  obtain ⟨c, d, hc0, hcd⟩ := exists_defect_eq_one hF e u
  obtain ⟨φ, hφ⟩ := hF.exists_continuousAut_apply_eq_conj_padicPow_const e u c
  have hφx : ⇑φ ∘ basis e = fun i ↦ (c i)⁻¹ * hF.padicPow (basis e i) u * c i :=
    funext fun i ↦ by rw [Function.comp_apply, basis_apply, hφ]
  refine ⟨φ, c, d, hc0, fun i ↦ congr_fun hφx i, ?_⟩
  -- By the peripheral product identity, `φ` carries `x_0 ⋯ x_{r-1}` to the inverse of
  -- `d⁻¹ * cusp x ^ u * d`.
  rw [map_cusp, hφx, cusp_def]
  exact inv_eq_of_mul_eq_one_right ((defect_def ..).symm.trans hcd)

/-- **The peripheral-power theorem for the conjugates of the cusp.** For every unit `u ∈ ℤ_pˣ`
there are a continuous automorphism `φ` of `F`, conjugators `c` on the basis `x = basis e`, with
`c 0 = 1` in positive rank, and `d : F`, such that `φ (x i) = (c i)⁻¹ * x i ^ u * c i` for every
`i` and, for every `q : F`, `φ` carries the conjugate `y = q * cusp x * q⁻¹` of the cusp to
`d'⁻¹ * y ^ u * d'` with `d' = q * d * (φ q)⁻¹`. At `q = 1` the conjugator is `d`. -/
theorem exists_peripheralAut_conj_cusp (hF : IsProP p F) (e : F ≃ₜ* freeProP p (Fin r))
    (u : ℤ_[p]ˣ) :
    ∃ (φ : ContinuousAut F) (c : Fin r → F) (d : F), (∀ h0 : 0 < r, c ⟨0, h0⟩ = 1) ∧
      (∀ i, φ (basis e i) = (c i)⁻¹ * hF.padicPow (basis e i) u * c i) ∧
      ∀ q : F, φ (q * cusp (basis e) * q⁻¹) =
        (q * d * (φ q)⁻¹)⁻¹ * hF.padicPow (q * cusp (basis e) * q⁻¹) u * (q * d * (φ q)⁻¹) := by
  obtain ⟨φ, c, d, hc0, hc, hd⟩ := exists_peripheralAut hF e u
  exact ⟨φ, c, d, hc0, hc,
    map_conj_eq_conj_of_map_eq_conj φ (hF.padicPow · u) (hF.conj_padicPow · · u) hd⟩

/-- For every unit `u ∈ ℤ_pˣ`, the basis of a free pro-`p` group admits a continuous
automorphism that is peripheral of exponent `u`. -/
theorem exists_isPeripheralAut (hF : IsProP p F) (e : F ≃ₜ* freeProP p (Fin r)) (u : ℤ_[p]ˣ) :
    ∃ φ : ContinuousAut F, IsPeripheralAut hF (basis e) u φ := by
  obtain ⟨φ, c, d, -, hc, hd⟩ := exists_peripheralAut hF e u
  exact ⟨φ, isPeripheralAut_of_apply_eq_conj hF hc hd⟩

end Peripheral

end TauCeti

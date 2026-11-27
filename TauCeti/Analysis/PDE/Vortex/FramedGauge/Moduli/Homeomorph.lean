/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Vortex.FramedGauge.SymmetricPower
public import TauCeti.Analysis.PDE.Vortex.Moduli.Topology

/-!
# Comparisons for the Sobolev vortex moduli homeomorphism

For `k ≥ 4`, `TauCeti.Vortex.SobolevFieldSpace.vortexModuliHomeomorph` identifies the Sobolev
vortex moduli space `vortexModuli f m hs ⊆ A_m^k / G_(k+1)` with `Sym ℂ m` via the zero divisor.
This file identifies `vortexModuli f m hs` with the set-level Sobolev vortex moduli
`sobolevVortexSubMulAction hk / sobolevGaugeGroup hs`
(`TauCeti.Vortex.SobolevFieldSpace.vortexModuliEquivSobolevVortexModuli`), and composes
`vortexModuliHomeomorph` with `TauCeti.Vortex.framedVortexModuliHomeomorph` to give a
homeomorphism `TauCeti.Vortex.SobolevFieldSpace.vortexModuliHomeomorphFramedVortexModuli` between
`vortexModuli f m hs` and the orbit space of the smooth framed vortices `framedVortices 1 m`, where
locally uniform convergence topologizes the representatives `framedVortices 1 m` and their orbit
space carries the quotient topology.

## Main definitions

* `TauCeti.Vortex.SobolevFieldSpace.vortexModuliEquivSobolevVortexModuli`: for `k ≥ 4`, bijection
  between `vortexModuli f m hs` and `sobolevVortexSubMulAction hk / sobolevGaugeGroup hs`.
* `TauCeti.Vortex.SobolevFieldSpace.vortexModuliHomeomorphFramedVortexModuli`: for `k ≥ 4`, the
  homeomorphism between `vortexModuli f m hs` and the smooth framed vortex moduli space.

## References

* A. Jaffe and C. H. Taubes, *Vortices and Monopoles*, Progress in Physics 2, Birkhäuser, 1980,
  Chapter III.
* C. H. Taubes, *Arbitrary N-vortex solutions to the first order Ginzburg–Landau equations*,
  Comm. Math. Phys. 72 (1980), 277–292.
-/

public section

namespace TauCeti.Vortex

section

variable {f : ContDiffBump (0 : ℝ)} {m k : ℕ} [Fact (1 < k)] {hs : 1 < (k : ℝ) + 1} {hk : 3 < k}

/-- A vortex of `sobolevVortexSubMulAction` is continuous. -/
theorem continuous_sobolevVortexSubMulAction
    (y : sobolevVortexSubMulAction (f := f) (m := m) (hs := hs) hk) :
    Continuous (y : ℂ → EuclideanSpace ℝ (Fin 4)) :=
  (mem_sobolevVortices.1 (mem_sobolevVortexSubMulAction.1 y.property)).1.continuous

/-- A vortex of `sobolevVortexSubMulAction` solves the vortex equation everywhere. -/
theorem equation_sobolevVortexSubMulAction_eq_zero
    (y : sobolevVortexSubMulAction (f := f) (m := m) (hs := hs) hk) (z : ℂ) :
    equation (y : ℂ → EuclideanSpace ℝ (Fin 4)) z = 0 :=
  (mem_sobolevVortices.1 (mem_sobolevVortexSubMulAction.1 y.property)).2 z

end

namespace SobolevFieldSpace

open Filter Topology
open scoped ContDiff

variable {f : ContDiffBump (0 : ℝ)} {m k : ℕ} [Fact (1 < k)] {hs : 1 < (k : ℝ) + 1}

private def sobolevVortexContinuousSubMulAction {f : ContDiffBump (0 : ℝ)} {m k : ℕ}
    [Fact (1 < k)] {hs : 1 < (k : ℝ) + 1} (hk : 3 < k) :
    SubMulAction (SobolevTopologicalGaugeGroup hs) (SobolevFieldSpace f m k) where
  carrier := {x | ∀ z, equation x z = 0}
  smul_mem' u _ hx z := (equation_smul_eq_zero_iff hk.le u _ z).2 (hx z)

private noncomputable def continuousVortexEquivSobolevVortex (hk : 3 < k) :
    sobolevVortexContinuousSubMulAction (f := f) (m := m) (hs := hs) hk ≃
      sobolevVortexSubMulAction (f := f) (m := m) (hs := hs) hk where
  toFun x := ⟨x.val.toFramedFieldSpace, mem_sobolevVortexSubMulAction.2
    (toFramedFieldSpace_mem_sobolevVortices hk x.property)⟩
  invFun y := ⟨⟨y.val, y.val.property, continuous_sobolevVortexSubMulAction y⟩,
    equation_sobolevVortexSubMulAction_eq_zero y⟩
  left_inv _ := Subtype.ext (ext rfl)
  right_inv _ := Subtype.ext (Subtype.ext rfl)

private theorem continuousVortexEquivSobolevVortex_apply (hk : 3 < k)
    (x : sobolevVortexContinuousSubMulAction (f := f) (m := m) (hs := hs) hk) :
    continuousVortexEquivSobolevVortex hk x =
      ⟨x.val.toFramedFieldSpace, mem_sobolevVortexSubMulAction.2
        (toFramedFieldSpace_mem_sobolevVortices hk x.property)⟩ :=
  rfl

private theorem continuousVortexEquivSobolevVortex_symm_apply (hk : 3 < k)
    (y : sobolevVortexSubMulAction (f := f) (m := m) (hs := hs) hk) :
    (continuousVortexEquivSobolevVortex hk).symm y =
      ⟨⟨y.val, y.val.property, continuous_sobolevVortexSubMulAction y⟩,
        equation_sobolevVortexSubMulAction_eq_zero y⟩ :=
  rfl

private theorem mem_sobolevVortexContinuousSubMulAction (hk : 3 < k)
    {x : SobolevFieldSpace f m k} :
    x ∈ sobolevVortexContinuousSubMulAction (f := f) (m := m) (hs := hs) hk ↔
      ∀ z, equation x z = 0 :=
  Iff.rfl

/-- For `k ≥ 4`, the vortex moduli subset `vortexModuli f m hs ⊆ A_m^k / G_(k+1)` is in
canonical bijection with `sobolevVortexSubMulAction hk / sobolevGaugeGroup hs`. -/
noncomputable def vortexModuliEquivSobolevVortexModuli (hk : 3 < k) :
    vortexModuli f m hs ≃ MulAction.orbitRel.Quotient (sobolevGaugeGroup hs)
      (sobolevVortexSubMulAction (f := f) (m := m) (hs := hs) hk) :=
  (Equiv.subtypeQuotientEquivQuotientSubtype
    (p₁ := (· ∈ sobolevVortexContinuousSubMulAction (f := f) (m := m) (hs := hs) hk))
    (s₂ := MulAction.orbitRel (SobolevTopologicalGaugeGroup hs)
      (sobolevVortexContinuousSubMulAction (f := f) (m := m) (hs := hs) hk))
    (· ∈ vortexModuli f m hs)
    (fun _ ↦ (mem_sobolevVortexContinuousSubMulAction hk).trans
      (mk_mem_vortexModuli_iff hk.le).symm)
    (fun _ _ ↦ by
      simp only [MulAction.orbitRel_apply, MulAction.mem_orbit_iff, Subtype.ext_iff,
        SubMulAction.val_smul])).trans
    (MulAction.orbitRelQuotientCongr (SobolevTopologicalGaugeGroup.toSubgroup hs)
      (continuousVortexEquivSobolevVortex hk)
      (fun u x ↦ Subtype.ext (toFramedFieldSpace_smul u x.val)))

/-- The inverse of `vortexModuliEquivSobolevVortexModuli` sends the orbit of a `C²` vortex of
`A_m^k` to its orbit in `vortexModuli`. -/
@[simp]
theorem vortexModuliEquivSobolevVortexModuli_symm_mk (hk : 3 < k)
    (x : sobolevVortexSubMulAction (f := f) (m := m) (hs := hs) hk) :
    (vortexModuliEquivSobolevVortexModuli hk).symm (Quotient.mk'' x) =
      ⟨Quotient.mk _ ⟨x.val, x.val.property, continuous_sobolevVortexSubMulAction x⟩,
        mk_mem_vortexModuli (equation_sobolevVortexSubMulAction_eq_zero x)⟩ := by
  simp [vortexModuliEquivSobolevVortexModuli, continuousVortexEquivSobolevVortex_symm_apply]

/-- `vortexModuliEquivSobolevVortexModuli` sends the orbit of a continuous vortex `x` of `A_m^k` to
its `sobolevGaugeGroup`-orbit in `sobolevVortexSubMulAction`. -/
@[simp]
theorem vortexModuliEquivSobolevVortexModuli_mk (hk : 3 < k) {x : SobolevFieldSpace f m k}
    (hx : ∀ z, equation x z = 0) :
    vortexModuliEquivSobolevVortexModuli (hs := hs) hk
        ⟨Quotient.mk _ x, mk_mem_vortexModuli hx⟩ =
      Quotient.mk'' ⟨x.toFramedFieldSpace,
        mem_sobolevVortexSubMulAction.2 (toFramedFieldSpace_mem_sobolevVortices hk hx)⟩ := by
  simp [vortexModuliEquivSobolevVortexModuli, continuousVortexEquivSobolevVortex_apply]

/-- **Homeomorphism between `vortexModuli` and the smooth framed vortex moduli.** For `k ≥ 4`, the
Sobolev vortex moduli space `vortexModuli f m hs` is homeomorphic to the orbit space of the smooth
framed vortices `framedVortices 1 m` (where locally uniform convergence topologizes the
representatives `framedVortices 1 m`, and their orbit space carries the quotient topology),
identifying orbits with the same zero divisor. -/
noncomputable def vortexModuliHomeomorphFramedVortexModuli (hk : 3 < k) :
    vortexModuli f m hs ≃ₜ
      MulAction.orbitRel.Quotient framedGaugeGroup (framedVortices 1 m) :=
  (vortexModuliHomeomorph f m hs hk).trans (framedVortexModuliHomeomorph one_pos m).symm

/-- Passing from `vortexModuli` to `framedVortices 1 m / framedGaugeGroup` and then taking the
divisor recovers `vortexModuliDivisor`. -/
@[simp]
theorem framedVortexModuliHomeomorph_vortexModuliHomeomorphFramedVortexModuli (hk : 3 < k)
    (q : vortexModuli f m hs) :
    framedVortexModuliHomeomorph one_pos m
        (vortexModuliHomeomorphFramedVortexModuli hk q) =
      vortexModuliDivisor hs hk q := by
  simp [vortexModuliHomeomorphFramedVortexModuli]

/-- On the orbit of a smooth vortex in `A_m^k`, `vortexModuliHomeomorphFramedVortexModuli` agrees
with taking its `framedGaugeGroup`-orbit. -/
theorem vortexModuliHomeomorphFramedVortexModuli_mk_of_eq (hk : 3 < k)
    {x : SobolevFieldSpace f m k} (hx : ∀ z, equation x z = 0) (x' : framedVortices 1 m)
    (hxx' : (x : ℂ → EuclideanSpace ℝ (Fin 4)) =
      ⇑(x' : C(ℂ, EuclideanSpace ℝ (Fin 4)))) :
    vortexModuliHomeomorphFramedVortexModuli (hs := hs) hk
        ⟨Quotient.mk _ x, mk_mem_vortexModuli hx⟩ = Quotient.mk'' x' := by
  refine (framedVortexModuliHomeomorph one_pos m).injective ?_
  rw [framedVortexModuliHomeomorph_vortexModuliHomeomorphFramedVortexModuli,
    framedVortexModuliHomeomorph_mk, vortexModuliDivisor_mk hk hx]
  exact sobolevVortexDivisor_eq_framedVortexDivisor
    ⟨x.toFramedFieldSpace, toFramedFieldSpace_mem_sobolevVortices hk hx⟩
    ((framedVortexEquiv 1 m).symm x') (hxx'.trans (coe_framedVortexEquiv_symm x').symm)

end SobolevFieldSpace

end TauCeti.Vortex

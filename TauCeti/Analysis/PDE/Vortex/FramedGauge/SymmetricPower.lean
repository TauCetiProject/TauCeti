/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Vortex.FramedGauge.Moduli
public import TauCeti.Analysis.PDE.Vortex.FramedGauge.OrbitChart
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Topology.LocalAtTarget
import TauCeti.AlgebraicTopology.Singular.InvarianceOfDomain
import TauCeti.Analysis.Polynomial.SymmetricPower

/-!
# The Sobolev moduli space of framed plane vortices is homeomorphic to `Sym ℂ m`

For an integer `k ≥ 4`, the Sobolev framed gauge group `G_(k+1)`
(`TauCeti.Vortex.SobolevTopologicalGaugeGroup`) acts on the continuous fields of the affine
space `A_m^k = x_m + H^k(ℂ; iT*ℂ ⊕ ℂ)` (`TauCeti.Vortex.SobolevFieldSpace`), and the vortex orbits
form the Sobolev moduli space `TauCeti.Vortex.SobolevFieldSpace.vortexModuli`, a subspace of the
orbit space `A_m^k / G_(k+1)` with its quotient topology. This file shows that the zero divisor
identifies this moduli space with `Sym ℂ m` as a topological space
(`TauCeti.Vortex.SobolevFieldSpace.vortexModuliHomeomorph`), collisions of zeros included. Through
the elementary symmetric chart `Sym.coeffHomeomorph`, it is homeomorphic to `ℂᵐ`.

The fields of `A_m^k`, `k ≥ 4`, are `C²`, so each vortex orbit has a zero divisor
(`TauCeti.Vortex.SobolevFieldSpace.vortexModuliDivisor`), the divisor of any of its fields, which
gauges of `G_(k+1)` do not change.

* **Bijectivity.** This is Taubes's classification on the Sobolev scale: two `C²` vortices of
  `A_m^k` with the same divisor lie in one `G_(k+1)`-orbit
  (`TauCeti.Vortex.sobolevVortexDivisor_eq_sobolevVortexDivisor_iff`), and every effective
  divisor of degree `m` is the divisor of a smooth vortex lying in every `A_m^j`
  (`TauCeti.Vortex.exists_contDiff_sobolevVortexDivisor_eq`). So each vortex orbit has such a
  smooth representative (`TauCeti.Vortex.SobolevFieldSpace.exists_contDiff_mk_eq`).
* **Continuity.** Convergence in `A_m^k` implies uniform convergence of the fields
  (`TauCeti.Vortex.SobolevFieldSpace.tendstoUniformly_of_tendsto`), so by Hurwitz's theorem the
  divisors of convergent vortices converge in `Sym ℂ m`
  (`TauCeti.Vortex.tendsto_of_tendstoLocallyUniformly`). The quotient map onto the orbit space is
  open, so its restriction to the vortices is a quotient map onto the moduli space, through which
  the divisor descends continuously.
* **Openness.** Near the orbit of a vortex lying in every `A_m^j`, the moduli space is homeomorphic
  to an open subset of `ℝ^(2m)` by the Coulomb slice charts
  (`TauCeti.Vortex.SobolevFieldSpace.exists_openPartialHomeomorph_vortexModuli`). With the smooth
  representatives above, these charts cover the moduli space, so it is a topological manifold
  without boundary of dimension `2m`, like `ℂᵐ`. A continuous injection between such manifolds of
  the same dimension is an open embedding by invariance of domain
  (`Continuous.isOpenEmbedding_of_injective`), so the divisor is an open map.

The divisor is therefore a continuous open bijection, hence a homeomorphism. Its counterpart for
the smooth framed vortices with the topology of locally uniform convergence is
`TauCeti.Vortex.framedVortexModuliHomeomorph`, and its set-level counterpart on the `C²` vortices of
`A_m^k` is `TauCeti.Vortex.sobolevVortexModuliEquiv`.

## Main definitions

* `TauCeti.Vortex.SobolevFieldSpace.vortexModuliDivisor`: the zero divisor of a vortex orbit.
* `TauCeti.Vortex.SobolevFieldSpace.vortexModuliHomeomorph`: the homeomorphism from the Sobolev
  vortex moduli space onto `Sym ℂ m`.

## Main results

* `TauCeti.Vortex.SobolevFieldSpace.vortexModuliDivisor_mk`: the divisor of the orbit of a vortex
  is the divisor of the vortex.
* `TauCeti.Vortex.SobolevFieldSpace.exists_contDiff_mk_eq`: every vortex orbit has a smooth
  representative lying in every `A_m^j`.
* `TauCeti.Vortex.SobolevFieldSpace.continuous_vortexModuliDivisor`,
  `TauCeti.Vortex.SobolevFieldSpace.isOpenMap_vortexModuliDivisor`: the divisor is continuous and
  open.

## References

* C. H. Taubes, *Arbitrary N-vortex solutions to the first order Ginzburg–Landau equations*,
  Comm. Math. Phys. 72 (1980), 277–292.
* A. Jaffe and C. H. Taubes, *Vortices and Monopoles*, Progress in Physics 2, Birkhäuser, 1980,
  Chapter III.
* A. Hatcher, *Algebraic Topology*, Theorem 2B.3 (invariance of domain).
-/

public section

noncomputable section

namespace TauCeti.Vortex

namespace SobolevFieldSpace

open Filter Topology
open scoped ContDiff

variable {f : ContDiffBump (0 : ℝ)} {m k : ℕ}

/-- A continuous vortex of `A_m^k`, `k ≥ 4`, is a `C²` vortex of `A_m^k`: its field is `C²` by the
Sobolev embedding. -/
theorem toFramedFieldSpace_mem_sobolevVortices (hk : 3 < k) {x : SobolevFieldSpace f m k}
    (hx : ∀ z, equation x z = 0) : x.toFramedFieldSpace ∈ sobolevVortices f m k :=
  mem_sobolevVortices.2 ⟨contDiff_of_mem_framedFieldSpace (n := 2)
    (by norm_num; exact_mod_cast hk) x.continuous x.mem_framedFieldSpace, hx⟩

variable [Fact (1 < k)] {hs : 1 < (k : ℝ) + 1}

variable (hs) in
/-- **The zero divisor of a vortex orbit** in the Sobolev moduli space of `A_m^k / G_(k+1)`,
`k ≥ 4`: the divisor of any of its vortices (`vortexModuliDivisor_mk`). -/
def vortexModuliDivisor (hk : 3 < k) (q : vortexModuli f m hs) : Sym ℂ m :=
  sobolevVortexDivisor
    ⟨_, toFramedFieldSpace_mem_sobolevVortices hk (mem_vortexModuli_iff.1 q.property).choose_spec.1⟩

/-- The divisor of the orbit of a continuous vortex of `A_m^k`, `k ≥ 4`, is the divisor of the
vortex. -/
@[simp]
theorem vortexModuliDivisor_mk (hk : 3 < k) {x : SobolevFieldSpace f m k}
    (hx : ∀ z, equation x z = 0) :
    vortexModuliDivisor hs hk ⟨Quotient.mk _ x, mk_mem_vortexModuli hx⟩ =
      sobolevVortexDivisor ⟨_, toFramedFieldSpace_mem_sobolevVortices hk hx⟩ := by
  -- The chosen representative lies in the orbit of `x`, and gauges keep the divisor.
  have hy := (mem_vortexModuli_iff.1 (mk_mem_vortexModuli (hs := hs) hx)).choose_spec.2
  obtain ⟨u, hu, hux⟩ := orbitRel_iff.1 (Quotient.exact hy.symm)
  exact sobolevVortexDivisor_eq_sobolevVortexDivisor_iff.2 ⟨⟨u, hu⟩, Subtype.ext hux⟩

/-- **Taubes's uniqueness theorem on the Sobolev moduli space**: for `k ≥ 4`, two vortex orbits of
`A_m^k / G_(k+1)` with the same divisor coincide. -/
theorem vortexModuliDivisor_injective (hk : 3 < k) :
    Function.Injective (vortexModuliDivisor (f := f) (m := m) hs hk) := by
  rintro ⟨_, hxq⟩ ⟨_, hyq⟩ h
  obtain ⟨x, hx, rfl⟩ := mem_vortexModuli_iff.1 hxq
  obtain ⟨y, hy, rfl⟩ := mem_vortexModuli_iff.1 hyq
  rw [vortexModuliDivisor_mk hk hx, vortexModuliDivisor_mk hk hy] at h
  obtain ⟨u, hu⟩ := sobolevVortexDivisor_eq_sobolevVortexDivisor_iff (hs := hs).1 h
  exact Subtype.ext (Quotient.sound (orbitRel_iff.2 ⟨u, u.property, congrArg Subtype.val hu⟩)).symm

/-- Every effective divisor of degree `m` is the divisor of the orbit of a smooth vortex of `A_m^k`,
`k ≥ 4`, lying in `A_m^j` for every `j`. -/
private theorem exists_vortexModuliDivisor_mk_eq (hk : 3 < k) (D : Sym ℂ m) :
    ∃ (x : SobolevFieldSpace f m k) (hx : ∀ z, equation x z = 0),
      vortexModuliDivisor hs hk ⟨Quotient.mk _ x, mk_mem_vortexModuli hx⟩ = D ∧
        ContDiff ℝ ∞ x ∧ ∀ j : ℕ, ⇑x ∈ framedFieldSpace f m j := by
  obtain ⟨x, hxD, hxc, hmem, -⟩ := exists_contDiff_sobolevVortexDivisor_eq (f := f) (k := k) D
  let y : SobolevFieldSpace f m k := ⟨x, x.val.property, hxc.continuous⟩
  have hy : ∀ z, equation y z = 0 := (mem_sobolevVortices.1 x.property).2
  exact ⟨y, hy, (vortexModuliDivisor_mk hk hy).trans hxD, hxc, fun j ↦ hmem j⟩

/-- **Existence on the Sobolev moduli space**: for `k ≥ 4`, every effective divisor of degree `m`,
repeated points included, is the divisor of a vortex orbit of `A_m^k / G_(k+1)`. -/
theorem vortexModuliDivisor_surjective (hk : 3 < k) :
    Function.Surjective (vortexModuliDivisor (f := f) (m := m) hs hk) := fun D ↦
  let ⟨_, _, hxD, _⟩ := exists_vortexModuliDivisor_mk_eq hk D
  ⟨_, hxD⟩

/-- **Smooth representatives of vortex orbits.** For `k ≥ 4`, every vortex orbit of
`A_m^k / G_(k+1)` is the orbit of a smooth vortex lying in `A_m^j` for every `j`. -/
theorem exists_contDiff_mk_eq (hk : 3 < k) (q : vortexModuli f m hs) :
    ∃ x : SobolevFieldSpace f m k, (∀ z, equation x z = 0) ∧ Quotient.mk _ x = q.val ∧
      ContDiff ℝ ∞ x ∧ ∀ j : ℕ, ⇑x ∈ framedFieldSpace f m j := by
  obtain ⟨x, hx, hxq, hxc, hmem⟩ :=
    exists_vortexModuliDivisor_mk_eq hk (vortexModuliDivisor hs hk q)
  exact ⟨x, hx, congrArg Subtype.val (vortexModuliDivisor_injective hk hxq), hxc, hmem⟩

/-- **The divisor is continuous on the Sobolev moduli space**: for `k ≥ 4`, the zero divisor of a
vortex orbit depends continuously on the orbit, for the quotient topology of `A_m^k / G_(k+1)`. -/
theorem continuous_vortexModuliDivisor (hk : 3 < k) :
    Continuous (vortexModuliDivisor (f := f) (m := m) hs hk) := by
  -- The quotient map restricted to the vortices is a quotient map onto the moduli space.
  have hq := (MulAction.isOpenQuotientMap_quotientMk (Γ := SobolevTopologicalGaugeGroup hs)
    (T := SobolevFieldSpace f m k)).restrictPreimage (vortexModuli f m hs)
  have hvort (x : Quotient.mk _ ⁻¹' vortexModuli f m hs) : ∀ z, equation x.val z = 0 :=
    (mk_mem_vortexModuli_iff hk.le).1 x.property
  refine hq.isQuotientMap.continuous_iff.2 <| (continuous_iff_continuousAt.2 fun x₀ ↦ ?_).congr
    fun x ↦ (vortexModuliDivisor_mk hk (hvort x)).symm
  -- Convergent vortices converge uniformly, so their divisors converge by Hurwitz's theorem.
  have hunif := tendstoUniformly_of_tendsto (by exact_mod_cast (Fact.out : 1 < k))
    (continuous_subtypeVal.continuousAt (x := x₀))
  exact tendsto_of_tendstoLocallyUniformly (x := ⇑x₀.val)
    (isZeroMultiplicity_sectionValue_sobolevVortexDivisor
      ⟨_, toFramedFieldSpace_mem_sobolevVortices hk (hvort x₀)⟩)
    (.of_forall fun x ↦ isZeroMultiplicity_sectionValue_sobolevVortexDivisor
      ⟨_, toFramedFieldSpace_mem_sobolevVortices hk (hvort x)⟩)
    hunif.tendstoLocallyUniformly

/-- **The divisor is an open map on the Sobolev moduli space**, for `k ≥ 4`. By the Coulomb slice
charts the moduli space is a topological manifold of dimension `2m`, like `Sym ℂ m ≃ₜ ℂᵐ`, so the
continuous injective divisor is open by invariance of domain. -/
theorem isOpenMap_vortexModuliDivisor (hk : 3 < k) :
    IsOpenMap (vortexModuliDivisor (f := f) (m := m) hs hk) := by
  obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  -- The Coulomb slice charts at smooth representatives cover the moduli space.
  have hchart (q : vortexModuli f m hs) :
      ∃ e : OpenPartialHomeomorph (vortexModuli f m hs) (Fin (2 * m) → ℝ), q ∈ e.source := by
    obtain ⟨x, hx, hxq, -, hmem⟩ := exists_contDiff_mk_eq hk q
    obtain ⟨e, he, -⟩ := exists_openPartialHomeomorph_vortexModuli (hs := hs) (by omega) x hmem hx
    exact ⟨e, by rwa [show q = ⟨_, mk_mem_vortexModuli hx⟩ from Subtype.ext hxq.symm]⟩
  choose e he using hchart
  let : ChartedSpace (Fin (2 * m) → ℝ) (vortexModuli f m hs) :=
    ⟨Set.range e, e, he, Set.mem_range_self⟩
  -- Read in the elementary symmetric chart `Sym ℂ m ≃ₜ ℂᵐ`, the divisor is an open embedding.
  have hemb := ((Sym.coeffHomeomorph ℂ m).continuous.comp
    (continuous_vortexModuliDivisor hk)).isOpenEmbedding_of_injective
    (E := Fin (2 * m) → ℝ) (F := Fin m → ℂ) (M := vortexModuli f m hs)
    ((Sym.coeffHomeomorph ℂ m).injective.comp (vortexModuliDivisor_injective hk))
    (by simp [Module.finrank_pi_fintype, mul_comm])
  simpa [Function.comp_def] using (Sym.coeffHomeomorph ℂ m).symm.isOpenMap.comp hemb.isOpenMap

variable (f m hs) in
/-- **The Sobolev moduli space of framed vortices is homeomorphic to `Sym ℂ m`** (Taubes). For
`k ≥ 4`, the zero divisor identifies the vortex orbits of `A_m^k / G_(k+1)`, with the quotient
topology of the Sobolev topology, with the effective divisors of degree `m`, collisions of zeros
included. -/
def vortexModuliHomeomorph (hk : 3 < k) : vortexModuli f m hs ≃ₜ Sym ℂ m :=
  (Equiv.ofBijective _ ⟨vortexModuliDivisor_injective hk, vortexModuliDivisor_surjective hk⟩)
    |>.toHomeomorphOfContinuousOpen (continuous_vortexModuliDivisor hk)
      (isOpenMap_vortexModuliDivisor hk)

/-- The homeomorphism sends a vortex orbit to its divisor. -/
@[simp]
theorem vortexModuliHomeomorph_apply (hk : 3 < k) (q : vortexModuli f m hs) :
    vortexModuliHomeomorph f m hs hk q = vortexModuliDivisor hs hk q :=
  (rfl)

end SobolevFieldSpace

end TauCeti.Vortex

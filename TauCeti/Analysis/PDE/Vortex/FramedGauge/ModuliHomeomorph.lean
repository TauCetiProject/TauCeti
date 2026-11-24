/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Vortex.FramedGauge.OrbitChart
public import TauCeti.Analysis.PDE.Vortex.FramedGauge.SobolevOrder
public import TauCeti.Analysis.PDE.Vortex.Moduli.Topology
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Geometry.Manifold.ChartedSpace
import TauCeti.AlgebraicTopology.Singular.InvarianceOfDomain

/-!
# Homeomorphism between the Sobolev vortex moduli space and `Sym ℂ m`

For `k ≥ 4`, every continuous vortex of `A_m^k` is `C²`
(`TauCeti.Vortex.SobolevFieldSpace.toFramedFieldSpace_mem_sobolevVortices_of_equation_eq_zero`) and
has a smooth representative in `⋂_j A_m^j` in its `G_(k+1)`-orbit
(`TauCeti.Vortex.exists_sobolevGaugeGroup_smul_mem_framedFieldSpace`), so every orbit in
`vortexModuli f m hs ⊆ A_m^k / G_(k+1)` admits a Coulomb-slice `ℝ^(2m)`-chart
(`TauCeti.Vortex.SobolevFieldSpace.exists_openPartialHomeomorph_vortexModuli_of_lt`).

The zero divisor therefore yields a bijection
`TauCeti.Vortex.SobolevFieldSpace.vortexModuliEquiv : vortexModuli f m hs ≃ Sym ℂ m`, which is
continuous (`TauCeti.Vortex.SobolevFieldSpace.continuous_vortexModuliEquiv`) since the quotient map
from the vortices onto `vortexModuli` is a quotient map
(`TauCeti.Vortex.SobolevFieldSpace.isQuotientMap_vortexModuli_quotientMk`) and the divisor is
continuous on `A_m^k`. Composing with the elementary symmetric chart
`Sym.coeffHomeomorph ℂ m : Sym ℂ m ≃ₜ ℂᵐ` and applying Brouwer's invariance of domain
(`Continuous.isOpenEmbedding_of_injective`) to the `ℝ^(2m)`-charts shows that the divisor
bijection is an open embedding, hence a homeomorphism
`TauCeti.Vortex.SobolevFieldSpace.vortexModuliHomeomorph : vortexModuli f m hs ≃ₜ Sym ℂ m`,
and comparing with `TauCeti.Vortex.framedVortexModuliHomeomorph` gives a homeomorphism
`TauCeti.Vortex.SobolevFieldSpace.vortexModuliHomeomorphFramedVortexModuli` with the smooth framed
vortex moduli space.

## Main definitions

* `TauCeti.Vortex.SobolevFieldSpace.vortexModuliEquivSobolevVortexModuli`: for `k ≥ 4`, bijection
  between `vortexModuli f m hs` and `sobolevVortexSubMulAction hk / sobolevGaugeGroup hs`.
* `TauCeti.Vortex.SobolevFieldSpace.vortexModuliEquiv`: for `k ≥ 4`, the divisor bijection
  `vortexModuli f m hs ≃ Sym ℂ m`.
* `TauCeti.Vortex.SobolevFieldSpace.vortexModuliHomeomorph`: for `k ≥ 4`, the divisor
  homeomorphism `vortexModuli f m hs ≃ₜ Sym ℂ m`.
* `TauCeti.Vortex.SobolevFieldSpace.vortexModuliHomeomorphFramedVortexModuli`: for `k ≥ 4`, the
  homeomorphism between `vortexModuli f m hs` and the smooth framed vortex moduli space.

## Main results

* `TauCeti.Vortex.SobolevFieldSpace.exists_openPartialHomeomorph_vortexModuli_of_lt`: for `k ≥ 4`,
  every orbit of `vortexModuli` has a `ℝ^(2m)`-chart sending it to `0`.
* `TauCeti.Vortex.SobolevFieldSpace.continuous_vortexModuliEquiv`: for `k ≥ 4`,
  `vortexModuliEquiv` is continuous.

## References

* A. Jaffe and C. H. Taubes, *Vortices and Monopoles*, Progress in Physics 2, Birkhäuser, 1980,
  Chapter III.
* C. H. Taubes, *Arbitrary N-vortex solutions to the first order Ginzburg–Landau equations*,
  Comm. Math. Phys. 72 (1980), 277–292.
-/

public section

namespace TauCeti.Vortex

namespace SobolevFieldSpace

open Filter Topology
open scoped ContDiff

variable {f : ContDiffBump (0 : ℝ)} {m k : ℕ}

/-- For `k ≥ 4`, a continuous vortex of `A_m^k` lies in `sobolevVortices f m k`. -/
theorem toFramedFieldSpace_mem_sobolevVortices_of_equation_eq_zero (hk : 3 < k)
    {x : SobolevFieldSpace f m k} (hx : ∀ z, equation x z = 0) :
    x.toFramedFieldSpace ∈ sobolevVortices f m k :=
  mem_sobolevVortices.2 ⟨x.contDiff (n := 2) (by exact_mod_cast (by omega : 2 + 1 < k)), hx⟩

variable [Fact (1 < k)] {hs : 1 < (k : ℝ) + 1}

/-- **Every vortex orbit has a `ℝ^(2m)`-chart.** For `k ≥ 4`, every point `q` of `vortexModuli`
in `A_m^k / G_(k+1)` admits a chart modelled on `Fin (2 * m) → ℝ` sending `q` to `0`, without
assuming a smooth representative in advance. -/
theorem exists_openPartialHomeomorph_vortexModuli_of_lt (hk : 3 < k) (q : vortexModuli f m hs) :
    ∃ e : OpenPartialHomeomorph (vortexModuli f m hs) (Fin (2 * m) → ℝ),
      q ∈ e.source ∧ e q = 0 := by
  revert hs q
  rcases Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0) with ⟨k', rfl⟩
  intro hs q
  rcases q with ⟨q, hq⟩
  obtain ⟨x, hsol, rfl⟩ := mem_vortexModuli_iff.1 hq
  obtain ⟨y, hyc, hys, -, u, hu, -⟩ :=
    exists_sobolevGaugeGroup_smul_mem_framedFieldSpace (hs := hs)
      ⟨x.toFramedFieldSpace, toFramedFieldSpace_mem_sobolevVortices_of_equation_eq_zero hk hsol⟩
  let y' : SobolevFieldSpace f m (k' + 1 : ℕ) := ⟨y.val, y.val.property, hyc.continuous⟩
  have hxy : Quotient.mk (MulAction.orbitRel (SobolevTopologicalGaugeGroup hs)
      (SobolevFieldSpace f m (k' + 1 : ℕ))) y' = Quotient.mk _ x := by
    refine Quotient.sound (orbitRel_iff.2 ⟨u⁻¹, u⁻¹.property, ?_⟩)
    have h := congrArg (fun z : framedFieldSpace f m (k'.succ : ℕ) ↦
      ((u⁻¹ • z : framedFieldSpace f m (k'.succ : ℕ)) :
        ℂ → EuclideanSpace ℝ (Fin 4))) hu.symm
    rw [inv_smul_smul, coe_sobolevGaugeGroup_smul] at h
    exact h
  have hqeq :
      (⟨Quotient.mk _ y', mk_mem_vortexModuli (mem_sobolevVortices.1 y.property).2⟩ :
        vortexModuli f m hs) =
      ⟨Quotient.mk _ x, mk_mem_vortexModuli hsol⟩ := Subtype.ext hxy
  obtain ⟨e, hesrc, he0⟩ := exists_openPartialHomeomorph_vortexModuli (hs := hs)
    (by omega : 2 ≤ k') y' (fun j ↦ hys j) (mem_sobolevVortices.1 y.property).2
  exact ⟨e, hqeq ▸ hesrc, hqeq ▸ he0⟩

/-- Inclusion of `G_(k+1)`-orbits of `C²` vortices of `A_m^k` into `vortexModuli`. -/
private noncomputable def sobolevVortexToVortexModuli (hk : 3 < k) :
    MulAction.orbitRel.Quotient (sobolevGaugeGroup hs)
        (sobolevVortexSubMulAction (f := f) (m := m) (hs := hs) hk) →
      vortexModuli f m hs :=
  Quotient.lift
    (fun x : sobolevVortexSubMulAction (f := f) (m := m) (hs := hs) hk ↦
      (⟨Quotient.mk _ ⟨x.val, x.val.property,
          (mem_sobolevVortices.1 (mem_sobolevVortexSubMulAction.1 x.property)).1.continuous⟩,
        mk_mem_vortexModuli
          (mem_sobolevVortices.1 (mem_sobolevVortexSubMulAction.1 x.property)).2⟩ :
        vortexModuli f m hs))
    fun x y h ↦ Subtype.ext <| Quotient.sound <| orbitRel_iff.2 <| by
      obtain ⟨u, rfl⟩ := MulAction.mem_orbit_iff.1 (MulAction.orbitRel_apply.1 h)
      have hinv := congrArg
        (fun z : framedFieldSpace f m k ↦ (z : ℂ → EuclideanSpace ℝ (Fin 4)))
        (inv_smul_smul u y.val)
      rw [coe_sobolevGaugeGroup_smul] at hinv
      exact ⟨u⁻¹, u⁻¹.property, hinv⟩

private theorem sobolevVortexToVortexModuli_mk (hk : 3 < k)
    (x : sobolevVortexSubMulAction (f := f) (m := m) (hs := hs) hk) :
    sobolevVortexToVortexModuli hk (Quotient.mk'' x) =
      ⟨Quotient.mk _ ⟨x.val, x.val.property,
          (mem_sobolevVortices.1 (mem_sobolevVortexSubMulAction.1 x.property)).1.continuous⟩,
        mk_mem_vortexModuli
          (mem_sobolevVortices.1 (mem_sobolevVortexSubMulAction.1 x.property)).2⟩ :=
  rfl

private theorem sobolevVortexToVortexModuli_injective (hk : 3 < k) :
    Function.Injective (sobolevVortexToVortexModuli (f := f) (m := m) (hs := hs) hk) :=
  Quotient.ind₂ fun _ _ h ↦ Quotient.sound <| MulAction.orbitRel_apply.2 <|
    MulAction.mem_orbit_iff.2 <| by
      obtain ⟨u, hu, hxy⟩ := orbitRel_iff.1 (Quotient.exact (congrArg Subtype.val h).symm)
      exact ⟨⟨u, hu⟩, Subtype.ext (Subtype.ext hxy)⟩

private theorem sobolevVortexToVortexModuli_surjective (hk : 3 < k) :
    Function.Surjective (sobolevVortexToVortexModuli (f := f) (m := m) (hs := hs) hk) := by
  rintro ⟨q, hq⟩
  obtain ⟨x, hx, rfl⟩ := mem_vortexModuli_iff.1 hq
  exact ⟨Quotient.mk'' ⟨x.toFramedFieldSpace,
      mem_sobolevVortexSubMulAction.2
        (toFramedFieldSpace_mem_sobolevVortices_of_equation_eq_zero hk hx)⟩,
    sobolevVortexToVortexModuli_mk hk _⟩

private theorem sobolevVortexToVortexModuli_bijective (hk : 3 < k) :
    Function.Bijective (sobolevVortexToVortexModuli (f := f) (m := m) (hs := hs) hk) :=
  ⟨sobolevVortexToVortexModuli_injective hk, sobolevVortexToVortexModuli_surjective hk⟩

/-- For `k ≥ 4`, the vortex moduli subset `vortexModuli f m hs ⊆ A_m^k / G_(k+1)` is in
canonical bijection with `sobolevVortexSubMulAction hk / sobolevGaugeGroup hs`. -/
noncomputable def vortexModuliEquivSobolevVortexModuli (hk : 3 < k) :
    vortexModuli f m hs ≃ MulAction.orbitRel.Quotient (sobolevGaugeGroup hs)
      (sobolevVortexSubMulAction (f := f) (m := m) (hs := hs) hk) :=
  (Equiv.ofBijective (sobolevVortexToVortexModuli hk)
    (sobolevVortexToVortexModuli_bijective hk)).symm

/-- The inverse of `vortexModuliEquivSobolevVortexModuli` sends the orbit of a `C²` vortex of
`A_m^k` to its orbit in `vortexModuli`. -/
@[simp]
theorem vortexModuliEquivSobolevVortexModuli_symm_mk (hk : 3 < k)
    (x : sobolevVortexSubMulAction (f := f) (m := m) (hs := hs) hk) :
    (vortexModuliEquivSobolevVortexModuli hk).symm (Quotient.mk'' x) =
      ⟨Quotient.mk _ ⟨x.val, x.val.property,
          (mem_sobolevVortices.1 (mem_sobolevVortexSubMulAction.1 x.property)).1.continuous⟩,
        mk_mem_vortexModuli
          (mem_sobolevVortices.1 (mem_sobolevVortexSubMulAction.1 x.property)).2⟩ := by
  rw [vortexModuliEquivSobolevVortexModuli, Equiv.symm_symm, Equiv.ofBijective_apply,
    sobolevVortexToVortexModuli_mk]

/-- `vortexModuliEquivSobolevVortexModuli` sends the orbit of a continuous vortex `x` of `A_m^k` to
its `sobolevGaugeGroup`-orbit in `sobolevVortexSubMulAction`. -/
@[simp]
theorem vortexModuliEquivSobolevVortexModuli_mk (hk : 3 < k) {x : SobolevFieldSpace f m k}
    (hx : ∀ z, equation x z = 0) :
    vortexModuliEquivSobolevVortexModuli (hs := hs) hk
        ⟨Quotient.mk _ x, mk_mem_vortexModuli hx⟩ =
      Quotient.mk'' ⟨x.toFramedFieldSpace,
        mem_sobolevVortexSubMulAction.2
          (toFramedFieldSpace_mem_sobolevVortices_of_equation_eq_zero hk hx)⟩ := by
  refine ((vortexModuliEquivSobolevVortexModuli hk).eq_symm_apply).1 ?_
  rw [vortexModuliEquivSobolevVortexModuli_symm_mk]
  exact Subtype.ext (congrArg (Quotient.mk _) (ext rfl))

/-- **The divisor bijection on `vortexModuli`.** For `k ≥ 4`, the zero divisor identifies the
Sobolev vortex moduli space `vortexModuli f m hs ⊆ A_m^k / G_(k+1)` bijectively with
`Sym ℂ m`. -/
noncomputable def vortexModuliEquiv (hk : 3 < k) : vortexModuli f m hs ≃ Sym ℂ m :=
  (vortexModuliEquivSobolevVortexModuli hk).trans (sobolevVortexModuliEquiv hk)

/-- `vortexModuliEquiv` sends the orbit of a vortex to its zero divisor. -/
@[simp]
theorem vortexModuliEquiv_mk (hk : 3 < k) {x : SobolevFieldSpace f m k}
    (hx : ∀ z, equation x z = 0) :
    vortexModuliEquiv (hs := hs) hk ⟨Quotient.mk _ x, mk_mem_vortexModuli hx⟩ =
      sobolevVortexDivisor
        ⟨x.toFramedFieldSpace,
          toFramedFieldSpace_mem_sobolevVortices_of_equation_eq_zero hk hx⟩ := by
  rw [vortexModuliEquiv, Equiv.trans_apply, vortexModuliEquivSobolevVortexModuli_mk hk hx,
    sobolevVortexModuliEquiv_apply, sobolevVortexModuliDivisor_mk]

/-- The section of a continuous vortex of `A_m^k`, `k ≥ 4`, has zero multiplicities given by
`vortexModuliEquiv` of its orbit. -/
private theorem isZeroMultiplicity_sectionValue_vortexModuliEquiv_mk (hk : 3 < k)
    {x : SobolevFieldSpace f m k} (hx : ∀ z, equation x z = 0) :
    IsZeroMultiplicity (sectionValue (x : ℂ → EuclideanSpace ℝ (Fin 4)))
      fun z ↦ ((vortexModuliEquiv (hs := hs) hk
        ⟨Quotient.mk _ x, mk_mem_vortexModuli hx⟩ : Sym ℂ m) : Multiset ℂ).count z := by
  rw [vortexModuliEquiv_mk hk hx]
  exact isZeroMultiplicity_sectionValue_sobolevVortexDivisor
    ⟨x.toFramedFieldSpace, toFramedFieldSpace_mem_sobolevVortices_of_equation_eq_zero hk hx⟩

/-- **The divisor on `vortexModuli` is continuous.** For `k ≥ 4`, `vortexModuliEquiv` is
continuous with respect to the quotient topology on `vortexModuli` and the topology of
`Sym ℂ m`. -/
theorem continuous_vortexModuliEquiv (hk : 3 < k) :
    Continuous (vortexModuliEquiv (f := f) (m := m) (hs := hs) hk) := by
  rw [(isQuotientMap_vortexModuli_quotientMk (f := f) (m := m) (hs := hs)
    (by omega : 3 ≤ k)).continuous_iff, continuous_iff_continuousAt]
  intro x₀
  have hs1 : (1 : ℝ) < k := by exact_mod_cast (Fact.out : 1 < k)
  refine tendsto_of_tendsto hs1 continuous_subtypeVal.continuousAt
    (isZeroMultiplicity_sectionValue_vortexModuliEquiv_mk hk x₀.property)
    (.of_forall fun x ↦ isZeroMultiplicity_sectionValue_vortexModuliEquiv_mk hk x.property)

/-- **The Sobolev moduli space of framed vortices is homeomorphic to `Sym ℂ m`** (Taubes). For
`k ≥ 4`, the divisor bijection `vortexModuliEquiv` is a homeomorphism
`vortexModuli f m hs ≃ₜ Sym ℂ m`. -/
noncomputable def vortexModuliHomeomorph (hk : 3 < k) : vortexModuli f m hs ≃ₜ Sym ℂ m :=
  let _ : ChartedSpace (Fin (2 * m) → ℝ) (vortexModuli f m hs) :=
    { atlas := Set.range fun q ↦ (exists_openPartialHomeomorph_vortexModuli_of_lt hk q).choose
      chartAt q := (exists_openPartialHomeomorph_vortexModuli_of_lt hk q).choose
      mem_chart_source q := (exists_openPartialHomeomorph_vortexModuli_of_lt hk q).choose_spec.1
      chart_mem_atlas q := Set.mem_range_self q }
  let ψ := Sym.coeffHomeomorph ℂ m
  have hEF : Module.finrank ℝ (Fin (2 * m) → ℝ) = Module.finrank ℝ (Fin m → ℂ) := by
    rw [Module.finrank_fin_fun, Module.finrank_pi_fintype, Complex.finrank_real_complex]
    simp [mul_comm]
  have hψ : IsOpenEmbedding (ψ ∘ vortexModuliEquiv (f := f) (m := m) (hs := hs) hk) :=
    (ψ.continuous.comp (continuous_vortexModuliEquiv hk)).isOpenEmbedding_of_injective
      (ψ.injective.comp (vortexModuliEquiv hk).injective) hEF
  have he : IsOpenEmbedding (vortexModuliEquiv (f := f) (m := m) (hs := hs) hk) :=
    ψ.comp_isOpenEmbedding_iff.1 hψ
  (vortexModuliEquiv hk).toHomeomorphOfContinuousOpen (continuous_vortexModuliEquiv hk) he.isOpenMap

/-- Underlying equivalence of `vortexModuliHomeomorph`. -/
@[simp]
theorem coe_vortexModuliHomeomorph (hk : 3 < k) :
    ⇑(vortexModuliHomeomorph (f := f) (m := m) (hs := hs) hk) = vortexModuliEquiv hk :=
  (rfl)

/-- **Homeomorphism between `vortexModuli` and the smooth framed vortex moduli.** For `k ≥ 4`, the
Sobolev vortex moduli space `vortexModuli f m hs` is homeomorphic to the orbit space of the smooth
framed vortices `framedVortices 1 m` with the topology of locally uniform convergence, identifying
orbits with the same zero divisor. -/
noncomputable def vortexModuliHomeomorphFramedVortexModuli (hk : 3 < k) :
    vortexModuli f m hs ≃ₜ
      MulAction.orbitRel.Quotient framedGaugeGroup (framedVortices 1 m) :=
  (vortexModuliHomeomorph hk).trans (framedVortexModuliHomeomorph one_pos m).symm

/-- Passing from `vortexModuli` to `framedVortices 1 m / framedGaugeGroup` and then taking the
divisor recovers `vortexModuliEquiv`. -/
@[simp]
theorem framedVortexModuliHomeomorph_vortexModuliHomeomorphFramedVortexModuli (hk : 3 < k)
    (q : vortexModuli f m hs) :
    framedVortexModuliHomeomorph one_pos m
        (vortexModuliHomeomorphFramedVortexModuli hk q) =
      vortexModuliEquiv hk q := by
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
    framedVortexModuliHomeomorph_mk, vortexModuliEquiv_mk hk hx]
  exact sobolevVortexDivisor_eq_framedVortexDivisor
    ⟨x.toFramedFieldSpace, toFramedFieldSpace_mem_sobolevVortices_of_equation_eq_zero hk hx⟩
    ((framedVortexEquiv 1 m).symm x') (hxx'.trans (coe_framedVortexEquiv_symm x').symm)

end SobolevFieldSpace

end TauCeti.Vortex

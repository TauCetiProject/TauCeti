/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Vortex.FramedGauge.FieldInclusion
public import TauCeti.Analysis.PDE.Vortex.FramedGauge.SmoothDivisor
import TauCeti.Analysis.PDE.Vortex.FramedGauge.SobolevOrder

/-!
# The vortex moduli spaces of different Sobolev orders are diffeomorphic

For an integer `k ≥ 4`, the orbits of the continuous vortices of the affine Sobolev space
`A_m^k = x_m + H^k(ℂ; iT*ℂ ⊕ ℂ)` (`TauCeti.Vortex.SobolevFieldSpace`) under the Sobolev gauge group
`G_(k+1)` form the vortex moduli space `TauCeti.Vortex.SobolevFieldSpace.vortexModuli`, a smooth
manifold of dimension `2m` diffeomorphic to `ℂᵐ` by the coefficients of its zero divisor
(`TauCeti.Vortex.SobolevFieldSpace.vortexModuliDiffeomorph`). This file shows that this manifold
does not depend on the order: for `4 ≤ k ≤ k'`, the inclusion `A_m^(k') ⊆ A_m^k` induces a
diffeomorphism between the vortex moduli spaces of orders `k'` and `k`.

**The inclusion of fields.** For `0 ≤ s ≤ s'`, a continuous field of `A_m^(s')` is a continuous
field of `A_m^s`, and this inclusion is continuous (`TauCeti.Vortex.SobolevFieldSpace.inclusion`,
`TauCeti.Vortex.SobolevFieldSpace.continuous_inclusion`, in
`TauCeti.Analysis.PDE.Vortex.FramedGauge.FieldInclusion`).

**The induced map of orbit spaces.** The gauge groups decrease with the order,
`G_(k'+1) ≤ G_(k+1)` (`TauCeti.Vortex.sobolevGaugeGroup_mono`), so the inclusion carries
`G_(k'+1)`-orbits into `G_(k+1)`-orbits and descends to a continuous map
`A_m^(k') / G_(k'+1) → A_m^k / G_(k+1)` (`TauCeti.Vortex.SobolevFieldSpace.quotientInclusion`).
It carries vortex orbits to vortex orbits
(`TauCeti.Vortex.SobolevFieldSpace.vortexModuliInclusion`) and keeps their zero divisors
(`TauCeti.Vortex.SobolevFieldSpace.vortexModuliDivisor_vortexModuliInclusion`), since the divisor
of a vortex is read off its section.

**The diffeomorphism.** For `k ≥ 4`, the divisor identifies both moduli spaces with `Sym ℂ m`
(`TauCeti.Vortex.SobolevFieldSpace.vortexModuliHomeomorph`), and in its elementary symmetric
coordinates with `ℂᵐ` as smooth manifolds. Since the induced map keeps the divisor, it is the
composite of the identification of order `k'` with the inverse of that of order `k`. So it is a
homeomorphism (`TauCeti.Vortex.SobolevFieldSpace.vortexModuliHomeomorphOfLE`) and a diffeomorphism
for the atlases `TauCeti.Vortex.SobolevFieldSpace.vortexModuliChartedSpace`
(`TauCeti.Vortex.SobolevFieldSpace.vortexModuliDiffeomorphOfLE`). Its set-level counterpart on the
`C²` vortices is `TauCeti.Vortex.sobolevVortexModuliEquivOfLE`.

## Main definitions

* `TauCeti.Vortex.SobolevFieldSpace.quotientInclusion`: the induced map of orbit spaces.
* `TauCeti.Vortex.SobolevFieldSpace.vortexModuliInclusion`: its restriction to the vortex moduli.
* `TauCeti.Vortex.SobolevFieldSpace.vortexModuliHomeomorphOfLE`,
  `TauCeti.Vortex.SobolevFieldSpace.vortexModuliDiffeomorphOfLE`: for `4 ≤ k ≤ k'`, the
  restriction as a homeomorphism and as a diffeomorphism.

## Main results

* `TauCeti.Vortex.SobolevFieldSpace.continuous_quotientInclusion`: the induced map of orbit
  spaces is continuous.
* `TauCeti.Vortex.SobolevFieldSpace.vortexModuliDivisor_vortexModuliInclusion`: the induced map
  keeps the zero divisor.
* `TauCeti.Vortex.SobolevFieldSpace.coe_vortexModuliHomeomorphOfLE`,
  `TauCeti.Vortex.SobolevFieldSpace.coe_vortexModuliDiffeomorphOfLE`: the homeomorphism and the
  diffeomorphism are the map induced by the inclusion.
* `TauCeti.Vortex.SobolevFieldSpace.toHomeomorph_vortexModuliDiffeomorphOfLE`: the diffeomorphism
  has the homeomorphism as underlying homeomorphism.

## References

* C. H. Taubes, *Arbitrary N-vortex solutions to the first order Ginzburg–Landau equations*,
  Comm. Math. Phys. 72 (1980), 277–292.
* A. Jaffe and C. H. Taubes, *Vortices and Monopoles*, Progress in Physics 2, Birkhäuser, 1980,
  Chapter III.
-/

public section

noncomputable section

namespace TauCeti.Vortex

namespace SobolevFieldSpace

open scoped ContDiff Manifold

variable {f : ContDiffBump (0 : ℝ)} {m : ℕ}

/-! ### The induced map of orbit spaces -/

section Quotient

variable {k k' k'' : ℕ} [Fact (1 < k)] [Fact (1 < k')] [Fact (1 < k'')]
  {hs : 1 < (k : ℝ) + 1} {hs' : 1 < (k' : ℝ) + 1} {hs'' : 1 < (k'' : ℝ) + 1}

/-- **The map of orbit spaces induced by the inclusion** `A_m^(k') ⊆ A_m^k`, for `k ≤ k'`: since
`G_(k'+1) ≤ G_(k+1)`, it sends the `G_(k'+1)`-orbit of a field to its `G_(k+1)`-orbit. -/
def quotientInclusion (h : k ≤ k') :
    MulAction.orbitRel.Quotient (SobolevTopologicalGaugeGroup hs') (SobolevFieldSpace f m k') →
      MulAction.orbitRel.Quotient (SobolevTopologicalGaugeGroup hs) (SobolevFieldSpace f m k) :=
  Quotient.map' (inclusion (Nat.cast_le.2 h)) fun _ _ hxy ↦ by
    obtain ⟨u, hu, hxy⟩ := orbitRel_iff.1 hxy
    exact orbitRel_iff.2 ⟨u, sobolevGaugeGroup_mono hs
      (by exact_mod_cast Nat.add_le_add_right h 1) hu, by simpa only [coe_inclusion] using hxy⟩

/-- The induced map sends the `G_(k'+1)`-orbit of a field to its `G_(k+1)`-orbit. -/
@[simp]
theorem quotientInclusion_mk (h : k ≤ k') (x : SobolevFieldSpace f m k') :
    quotientInclusion (hs := hs) (hs' := hs') h (Quotient.mk _ x) =
      Quotient.mk _ (inclusion (Nat.cast_le.2 h) x) :=
  (rfl)

/-- The induced map of orbit spaces is continuous. -/
theorem continuous_quotientInclusion (h : k ≤ k') :
    Continuous (quotientInclusion (f := f) (m := m) (hs := hs) (hs' := hs') h) :=
  (continuous_inclusion k.cast_nonneg _).quotient_map' _

/-- The map of orbit spaces induced by the inclusion of `A_m^k` into itself is the identity. -/
@[simp]
theorem quotientInclusion_self
    (q : MulAction.orbitRel.Quotient (SobolevTopologicalGaugeGroup hs) (SobolevFieldSpace f m k)) :
    quotientInclusion (hs := hs) (hs' := hs) le_rfl q = q :=
  Quotient.inductionOn' q fun x ↦ congrArg (Quotient.mk _) (inclusion_self x)

/-- The maps of orbit spaces induced by inclusions compose. -/
@[simp]
theorem quotientInclusion_quotientInclusion (h : k ≤ k') (h' : k' ≤ k'')
    (q : MulAction.orbitRel.Quotient (SobolevTopologicalGaugeGroup hs'')
      (SobolevFieldSpace f m k'')) :
    quotientInclusion (hs := hs) (hs' := hs') h (quotientInclusion (hs' := hs'') h' q) =
      quotientInclusion (h.trans h') q :=
  Quotient.inductionOn' q fun x ↦ congrArg (Quotient.mk _) (inclusion_inclusion _ _ x)

/-- The induced map of orbit spaces carries vortex orbits to vortex orbits. -/
theorem quotientInclusion_mem_vortexModuli (h : k ≤ k')
    {q : MulAction.orbitRel.Quotient (SobolevTopologicalGaugeGroup hs')
      (SobolevFieldSpace f m k')} (hq : q ∈ vortexModuli f m hs') :
    quotientInclusion (hs := hs) h q ∈ vortexModuli f m hs := by
  obtain ⟨x, hx, rfl⟩ := mem_vortexModuli_iff.1 hq
  exact mk_mem_vortexModuli (by simpa only [coe_inclusion] using hx)

/-- **The map of vortex moduli induced by the inclusion** `A_m^(k') ⊆ A_m^k`, for `k ≤ k'`: the
`G_(k'+1)`-orbit of a vortex goes to its `G_(k+1)`-orbit. -/
def vortexModuliInclusion (h : k ≤ k') : vortexModuli f m hs' → vortexModuli f m hs :=
  Subtype.map (quotientInclusion h) fun _ ↦ quotientInclusion_mem_vortexModuli h

/-- The induced map of vortex moduli is the restriction of the induced map of orbit spaces. -/
@[simp]
theorem coe_vortexModuliInclusion (h : k ≤ k') (q : vortexModuli f m hs') :
    (vortexModuliInclusion (hs := hs) h q : MulAction.orbitRel.Quotient
      (SobolevTopologicalGaugeGroup hs) (SobolevFieldSpace f m k)) = quotientInclusion h q :=
  (rfl)

/-- The induced map of vortex moduli sends the `G_(k'+1)`-orbit of a vortex to its
`G_(k+1)`-orbit. -/
@[simp]
theorem vortexModuliInclusion_mk (h : k ≤ k') {x : SobolevFieldSpace f m k'}
    (hx : ∀ z, equation x z = 0) :
    vortexModuliInclusion (hs := hs) (hs' := hs') h ⟨Quotient.mk _ x, mk_mem_vortexModuli hx⟩ =
      ⟨Quotient.mk _ (inclusion (Nat.cast_le.2 h) x),
        mk_mem_vortexModuli (by simpa only [coe_inclusion] using hx)⟩ :=
  (rfl)

/-- The map of vortex moduli induced by the inclusion of `A_m^k` into itself is the identity. -/
@[simp]
theorem vortexModuliInclusion_self (q : vortexModuli f m hs) :
    vortexModuliInclusion (hs := hs) (hs' := hs) le_rfl q = q :=
  Subtype.ext (quotientInclusion_self q.val)

/-- The maps of vortex moduli induced by inclusions compose. -/
@[simp]
theorem vortexModuliInclusion_vortexModuliInclusion (h : k ≤ k') (h' : k' ≤ k'')
    (q : vortexModuli f m hs'') :
    vortexModuliInclusion (hs := hs) (hs' := hs') h (vortexModuliInclusion (hs' := hs'') h' q) =
      vortexModuliInclusion (h.trans h') q :=
  Subtype.ext (quotientInclusion_quotientInclusion h h' q.val)

/-- The induced map of vortex moduli is continuous. -/
theorem continuous_vortexModuliInclusion (h : k ≤ k') :
    Continuous (vortexModuliInclusion (f := f) (m := m) (hs := hs) (hs' := hs') h) :=
  (continuous_quotientInclusion h).subtype_map _

/-- **The induced map of vortex moduli keeps the zero divisor**, for `4 ≤ k ≤ k'`: the divisor of
a vortex is read off its section, which the inclusion does not change. -/
@[simp]
theorem vortexModuliDivisor_vortexModuliInclusion (hk : 3 < k) (h : k ≤ k')
    (q : vortexModuli f m hs') :
    vortexModuliDivisor hs hk (vortexModuliInclusion h q) =
      vortexModuliDivisor hs' (hk.trans_le h) q := by
  obtain ⟨q, hq⟩ := q
  obtain ⟨x, hx, rfl⟩ := mem_vortexModuli_iff.1 hq
  rw [vortexModuliInclusion_mk h hx,
    vortexModuliDivisor_mk _ (by simpa only [coe_inclusion] using hx), vortexModuliDivisor_mk _ hx]
  simp only [toFramedFieldSpace_inclusion]
  exact sobolevVortexDivisor_inclusion h
    ⟨_, toFramedFieldSpace_mem_sobolevVortices (hk.trans_le h) hx⟩

end Quotient

/-! ### The homeomorphism and the diffeomorphism -/

section Diffeomorph

variable {k k' : ℕ} [Fact (1 < k)] [Fact (1 < k')] {hs : 1 < (k : ℝ) + 1}
  {hs' : 1 < (k' : ℝ) + 1}

variable (hs hs') in
/-- **The vortex moduli spaces of orders `k'` and `k` are homeomorphic**, for `4 ≤ k ≤ k'`, by the
map induced by the inclusion `A_m^(k') ⊆ A_m^k` (`coe_vortexModuliHomeomorphOfLE`). It is the
divisor homeomorphism of order `k'` onto `Sym ℂ m` followed by the inverse of that of order `k`. -/
def vortexModuliHomeomorphOfLE (hk : 3 < k) (h : k ≤ k') :
    vortexModuli f m hs' ≃ₜ vortexModuli f m hs :=
  (vortexModuliHomeomorph f m hs' (hk.trans_le h)).trans (vortexModuliHomeomorph f m hs hk).symm

/-- The homeomorphism is the map induced by the inclusion. -/
@[simp]
theorem coe_vortexModuliHomeomorphOfLE (hk : 3 < k) (h : k ≤ k') :
    ⇑(vortexModuliHomeomorphOfLE (f := f) (m := m) hs hs' hk h) = vortexModuliInclusion h := by
  ext1 q
  rw [vortexModuliHomeomorphOfLE, Homeomorph.trans_apply, Homeomorph.symm_apply_eq,
    vortexModuliHomeomorph_apply, vortexModuliHomeomorph_apply,
    vortexModuliDivisor_vortexModuliInclusion]

/-- The inverse of the homeomorphism keeps the zero divisor: it sends the vortex orbit of order `k`
with divisor `D` to the vortex orbit of order `k'` with divisor `D`. -/
@[simp]
theorem vortexModuliDivisor_vortexModuliHomeomorphOfLE_symm (hk : 3 < k) (h : k ≤ k')
    (q : vortexModuli f m hs) :
    vortexModuliDivisor hs' (hk.trans_le h) ((vortexModuliHomeomorphOfLE hs hs' hk h).symm q) =
      vortexModuliDivisor hs hk q := by
  obtain ⟨q, rfl⟩ := (vortexModuliHomeomorphOfLE (f := f) (m := m) hs hs' hk h).surjective q
  rw [Homeomorph.symm_apply_apply, coe_vortexModuliHomeomorphOfLE,
    vortexModuliDivisor_vortexModuliInclusion]

variable (hs hs') in
/-- **The vortex moduli spaces of orders `k'` and `k` are diffeomorphic** (Taubes), for
`4 ≤ k ≤ k'`, with their atlases `vortexModuliChartedSpace`, by the map induced by the inclusion
`A_m^(k') ⊆ A_m^k` (`coe_vortexModuliDiffeomorphOfLE`). So the smooth manifold of framed vortices
modulo gauge does not depend on the Sobolev order. -/
def vortexModuliDiffeomorphOfLE (hk : 3 < k) (h : k ≤ k') :
    letI := vortexModuliChartedSpace (f := f) (m := m) (hs := hs') (hk.trans_le h)
    letI := vortexModuliChartedSpace (f := f) (m := m) (hs := hs) hk
    Diffeomorph 𝓘(ℝ, Fin (2 * m) → ℝ) 𝓘(ℝ, Fin (2 * m) → ℝ) (vortexModuli f m hs')
      (vortexModuli f m hs) ∞ :=
  letI := vortexModuliChartedSpace (f := f) (m := m) (hs := hs') (hk.trans_le h)
  letI := vortexModuliChartedSpace (f := f) (m := m) (hs := hs) hk
  (vortexModuliDiffeomorph (hk.trans_le h)).trans (vortexModuliDiffeomorph hk).symm

/-- The diffeomorphism is the map induced by the inclusion. -/
@[simp]
theorem coe_vortexModuliDiffeomorphOfLE (hk : 3 < k) (h : k ≤ k') :
    ⇑(vortexModuliDiffeomorphOfLE (f := f) (m := m) hs hs' hk h) = vortexModuliInclusion h := by
  let _ := vortexModuliChartedSpace (f := f) (m := m) (hs := hs') (hk.trans_le h)
  let _ := vortexModuliChartedSpace (f := f) (m := m) (hs := hs) hk
  ext1 q
  -- Both sides are sent to the divisor coefficients of `q` by the diffeomorphism of order `k`.
  rw [vortexModuliDiffeomorphOfLE, Diffeomorph.coe_trans, Function.comp_apply,
    ← Diffeomorph.symm_apply_apply (vortexModuliDiffeomorph hk) (vortexModuliInclusion h q),
    vortexModuliDiffeomorph_apply, vortexModuliDiffeomorph_apply,
    vortexModuliDivisor_vortexModuliInclusion]

/-- The underlying homeomorphism of the diffeomorphism is `vortexModuliHomeomorphOfLE`. -/
@[simp]
theorem toHomeomorph_vortexModuliDiffeomorphOfLE (hk : 3 < k) (h : k ≤ k') :
    letI := vortexModuliChartedSpace (f := f) (m := m) (hs := hs') (hk.trans_le h)
    letI := vortexModuliChartedSpace (f := f) (m := m) (hs := hs) hk
    (vortexModuliDiffeomorphOfLE (f := f) (m := m) hs hs' hk h).toHomeomorph =
      vortexModuliHomeomorphOfLE hs hs' hk h := by
  let _ := vortexModuliChartedSpace (f := f) (m := m) (hs := hs') (hk.trans_le h)
  let _ := vortexModuliChartedSpace (f := f) (m := m) (hs := hs) hk
  ext q
  rw [Diffeomorph.coe_toHomeomorph, coe_vortexModuliDiffeomorphOfLE,
    coe_vortexModuliHomeomorphOfLE]

end Diffeomorph

end SobolevFieldSpace

end TauCeti.Vortex

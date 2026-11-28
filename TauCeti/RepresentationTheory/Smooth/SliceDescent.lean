/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.MeasureTheory.Group.Integral
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import TauCeti.RepresentationTheory.Smooth.CompactSupport
public import TauCeti.Topology.Algebra.Group.LocallyConstant
public import TauCeti.Topology.LocallyConstant.CompactSupport.OpenClosed

/-!
# Descent of invariant distributions to a slice

Let a topological group `Γ` act on a topological group `G` by conjugation through a continuous
homomorphism `j : Γ →* G`, and let `H ⊆ Γ` be a closed subgroup. A pair `X ⊆ C ⊆ G` is a *slice*
(`TauCeti.IsSlice j H X C`) if `C` is closed, `C` is the set of conjugates `j γ * y * (j γ)⁻¹` of
points `y ∈ X`, such a conjugate lies in `X` exactly when `γ ∈ H`, and near `X` every point of `C`
is conjugated into `X` by an element of `Γ` close to `1`. The map `(γ, y) ↦ j γ * y * (j γ)⁻¹`
from `Γ × X` onto `C` then has the `H`-orbits `(γ h, j h⁻¹ * y * j h)` as fibres.

For a test function `Ψ` on `Γ × G` (a locally constant function with compact support,
`LocallyConstant.compactlySupported`) and a left invariant measure `μ` on `H`, the
*fibre integral* (`TauCeti.fiberIntegral j μ Ψ γ y`) integrates `Ψ` over the `H`-orbit of
`(γ, y)`. Its value at `(γ, y)` with `y ∈ X` depends only on the point `j γ * y * (j γ)⁻¹` of `C`
(`TauCeti.IsSlice.fiberIntegral_eq`), and the resulting function on `C` is the restriction of a
test function on `G` when `G` is Hausdorff, locally compact and totally disconnected
(`TauCeti.IsSlice.exists_eq_fiberIntegral`).

The main theorem is the descent of invariant distributions
(`TauCeti.IsSlice.map_eq_zero_of_eq_fiberIntegral`): let `I` be a linear form on the test functions
on `G` that is invariant under conjugation by `j Γ` and only depends on the restriction of a test
function to `C`. If `Ψ` integrates to zero along `Γ` at every point of `X`, that is
`∫ γ, Ψ (γ, y) = 0` for a Haar measure on `Γ` and every `y ∈ X`, then `I` vanishes on every test
function whose restriction to `C` is the fibre integral of `Ψ`.

The proof follows Harish-Chandra's descent along a slice. Choose an open subgroup `U ⊆ Γ` under
which `Ψ` is invariant on the right in the first variable; finitely many cosets `r U` cover the
`Γ`-support of `Ψ`, and `Ψ (γ, y) = ∑_r 1_{r U} (γ) Ψ (r, y)`. The fibre integral of the piece
supported on `r U` is the translate, under conjugation by `j r`, of the fibre integral of the
piece `1_U (γ) Ψ (r, y)`, so invariance of `I` replaces every piece by one supported on `U`. The sum
of those pieces is `1_U (γ) ∑_r Ψ (r, y)`, and `vol(U) ∑_r Ψ (r, y) = ∫ γ, Ψ (γ, y) = 0` for
`y ∈ X`, so its fibre integral vanishes on `C`.

## Main definitions

* `TauCeti.IsSlice j H X C`: `X ⊆ C` is a slice for the conjugation action of `Γ` through `j`, with
  stabiliser `H`.
* `TauCeti.fiberIntegral j μ Ψ γ y`: the integral `∫ h, Ψ (γ * h, (j h)⁻¹ * y * j h) ∂μ` over the
  `H`-orbit of `(γ, y)`.

## Main results

* `TauCeti.IsSlice.fiberIntegral_eq`: the fibre integral is constant on the fibres of
  `(γ, y) ↦ j γ * y * (j γ)⁻¹` over `C`.
* `TauCeti.IsSlice.exists_eq_fiberIntegral`: the fibre integral of a test function on `Γ × G` is
  the restriction to `C` of a test function on `G`.
* `TauCeti.IsSlice.map_eq_zero_of_eq_fiberIntegral`: the descent of invariant distributions.

## References

* Harish-Chandra, *Harmonic analysis on reductive p-adic groups*, notes by G. van Dijk, Lecture
  Notes in Mathematics 162, Springer, 1970 (descent of invariant distributions to a slice).
* The statements adapt the declarations `New.IsSlice`, `New.fibreIntegral`,
  `New.IsSlice.exists_isImage` and `New.IsInvariantDistribution.eq_zero_of_isImage` of the formal
  proof `[ShortProof]`, grh-lean (https://github.com/lsernau/grh-lean, Apache 2.0, Copyright 2026
  Anthropic PBC), file `src/Lib/Adelic/TraceFormula/FibreIntegral.lean`. Here the test functions
  are those of `LocallyConstant.compactlySupported`, the invariance of the linear form is stated
  through `TauCeti.compactlySupportedRep`, and the proofs are written independently.
-/

public section

noncomputable section

open Filter Function MeasureTheory Set Topology LocallyConstant

namespace TauCeti

variable {Γ G : Type*} [Group Γ] [Group G] {j : Γ →* G} {H : Subgroup Γ} {X C : Set G}

section Slice

variable [TopologicalSpace Γ] [TopologicalSpace G]

variable (j H X C) in
/-- `X ⊆ C ⊆ G` is a **slice** for the conjugation action of `Γ` on `G` through `j`, with stabiliser
`H`: `C` is closed and is the set of conjugates `j γ * y * (j γ)⁻¹` of points `y ∈ X`; such a
conjugate lies in `X` exactly when `γ ∈ H`; and near each point of `X`, every point of `C` is
conjugated into `X` by an element of `Γ` close to `1`. -/
structure IsSlice : Prop where
  /-- The set `C` of conjugates of `X` is closed. -/
  isClosed : IsClosed C
  /-- `C` is the set of conjugates of the points of `X`. -/
  mem_iff : ∀ c, c ∈ C ↔ ∃ γ, ∃ y ∈ X, j γ * y * (j γ)⁻¹ = c
  /-- A conjugate of a point of `X` lies in `X` exactly when the conjugating element lies in
  `H`. -/
  conj_mem_iff : ∀ γ, ∀ y ∈ X, j γ * y * (j γ)⁻¹ ∈ X ↔ γ ∈ H
  /-- Near each point `y` of `X`, the points of `C` are conjugates of points of `X` by elements of
  any given neighbourhood of `1` in `Γ`. -/
  eventually_exists_conj : ∀ y ∈ X, ∀ U ∈ 𝓝 (1 : Γ), ∀ᶠ c in 𝓝[C] y,
    ∃ u ∈ U, ∃ x ∈ X, j u * x * (j u)⁻¹ = c

namespace IsSlice

/-- A conjugate of a point of `X` lies in `C`. -/
theorem conj_mem (hs : IsSlice j H X C) (γ : Γ) {y : G} (hy : y ∈ X) :
    j γ * y * (j γ)⁻¹ ∈ C :=
  (hs.mem_iff _).2 ⟨γ, y, hy, rfl⟩

/-- The slice `X` is contained in `C`. -/
theorem subset (hs : IsSlice j H X C) : X ⊆ C := fun y hy => by
  simpa using hs.conj_mem 1 hy

/-- `C` is stable under conjugation by `j Γ`. -/
theorem conj_mem_of_mem (hs : IsSlice j H X C) (δ : Γ) {c : G} (hc : c ∈ C) :
    j δ * c * (j δ)⁻¹ ∈ C := by
  obtain ⟨γ, y, hy, rfl⟩ := (hs.mem_iff c).1 hc
  convert hs.conj_mem (δ * γ) hy using 1
  simp only [map_mul, mul_inv_rev, mul_assoc]

/-- Conjugation by `(j h)⁻¹` for `h ∈ H` preserves `X`. -/
theorem inv_conj_mem (hs : IsSlice j H X C) {h : Γ} (hh : h ∈ H) {y : G} (hy : y ∈ X) :
    (j h)⁻¹ * y * j h ∈ X := by
  simpa using (hs.conj_mem_iff h⁻¹ y hy).2 (inv_mem hh)

/-- A closed set `X` stable under conjugation by `j Γ` is a slice for the whole group `Γ`, with
`C = X`. -/
theorem of_conj_mem (hX : IsClosed X) (h : ∀ γ, ∀ y ∈ X, j γ * y * (j γ)⁻¹ ∈ X) :
    IsSlice j ⊤ X X where
  isClosed := hX
  mem_iff c := ⟨fun hc => ⟨1, c, hc, by simp⟩, fun ⟨γ, y, hy, hc⟩ => hc ▸ h γ y hy⟩
  conj_mem_iff γ y hy := by simpa using h γ y hy
  eventually_exists_conj y _ U hU := eventually_mem_nhdsWithin.mono fun c hc =>
    ⟨1, mem_of_mem_nhds hU, c, hc, by simp⟩

end IsSlice

end Slice

section FiberIntegral

variable [MeasurableSpace H]

variable (j) in
/-- The **fibre integral** of `Ψ : Γ × G → ℂ` at `(γ, y)`: the integral
`∫ h, Ψ (γ * h, (j h)⁻¹ * y * j h) ∂μ` of `Ψ` over the orbit of `(γ, y)` under the action of `H`
by `h • (γ, y) = (γ * h⁻¹, j h * y * (j h)⁻¹)`. For `y` in a slice it only depends on
`j γ * y * (j γ)⁻¹` (`TauCeti.IsSlice.fiberIntegral_eq`). -/
def fiberIntegral (μ : Measure H) (Ψ : Γ × G → ℂ) (γ : Γ) (y : G) : ℂ :=
  ∫ h, Ψ (γ * h, (j h)⁻¹ * y * j h) ∂μ

/-- The fibre integral as an integral over `H`. -/
theorem fiberIntegral_def (μ : Measure H) (Ψ : Γ × G → ℂ) (γ : Γ) (y : G) :
    fiberIntegral j μ Ψ γ y = ∫ h, Ψ (γ * h, (j h)⁻¹ * y * j h) ∂μ :=
  (rfl)

/-- The fibre integral of `0` vanishes. -/
@[simp]
theorem fiberIntegral_zero (μ : Measure H) (γ : Γ) (y : G) :
    fiberIntegral j μ (0 : Γ × G → ℂ) γ y = 0 := by
  simp [fiberIntegral_def]

/-- Translating `Ψ` on the left in the first variable translates its fibre integral. -/
theorem fiberIntegral_comp_mul_left (μ : Measure H) (Ψ : Γ × G → ℂ) (δ γ : Γ) (y : G) :
    fiberIntegral j μ (fun p => Ψ (δ * p.1, p.2)) γ y = fiberIntegral j μ Ψ (δ * γ) y := by
  simp only [fiberIntegral_def, mul_assoc]

/-- **The fibre integral is constant on the fibres over `C`.** If two points `(γ, y)` and
`(γ', y')` of `Γ × X` have the same conjugate `j γ * y * (j γ)⁻¹ = j γ' * y' * (j γ')⁻¹`, their
fibre integrals agree. -/
theorem IsSlice.fiberIntegral_eq [TopologicalSpace Γ] [TopologicalSpace G] [MeasurableMul H]
    (hs : IsSlice j H X C) (μ : Measure H) [μ.IsMulLeftInvariant] (Ψ : Γ × G → ℂ) {γ γ' : Γ}
    {y y' : G} (hy : y ∈ X) (hy' : y' ∈ X)
    (h : j γ * y * (j γ)⁻¹ = j γ' * y' * (j γ')⁻¹) :
    fiberIntegral j μ Ψ γ y = fiberIntegral j μ Ψ γ' y' := by
  -- The element `k = γ'⁻¹ γ` conjugates `y` to `y'`, hence lies in `H`.
  have hk : j (γ'⁻¹ * γ) * y * (j (γ'⁻¹ * γ))⁻¹ = y' := by
    calc j (γ'⁻¹ * γ) * y * (j (γ'⁻¹ * γ))⁻¹ = (j γ')⁻¹ * (j γ * y * (j γ)⁻¹) * j γ' := by
          simp only [map_mul, map_inv]; group
      _ = y' := by rw [h]; group
  have hkH : γ'⁻¹ * γ ∈ H := (hs.conj_mem_iff _ y hy).1 (hk ▸ hy')
  -- Substituting `h ↦ k h` in the integral over `H` moves the orbit of `(γ', y')` to that of
  -- `(γ, y)`.
  rw [fiberIntegral_def, fiberIntegral_def, eq_comm,
    ← integral_mul_left_eq_self _ (⟨_, hkH⟩ : H)]
  congr 1
  funext h
  rw [← hk]
  simp only [Subgroup.coe_mul, map_mul, map_inv]
  congr 2 <;> group

/-- The integrand of the fibre integral of a test function is integrable over a closed subgroup
`H`, being continuous with compact support. -/
theorem integrable_fiberIntegral_integrand [TopologicalSpace Γ] [TopologicalSpace G]
    [IsTopologicalGroup Γ] [IsTopologicalGroup G] [OpensMeasurableSpace H] (hj : Continuous j)
    (hH : IsClosed (H : Set Γ)) (μ : Measure H) [IsFiniteMeasureOnCompacts μ]
    (Ψ : compactlySupported ℂ (Γ × G) ℂ) (γ : Γ) (y : G) :
    Integrable (fun h : H => (Ψ : LocallyConstant (Γ × G) ℂ) (γ * h, (j h)⁻¹ * y * j h)) μ := by
  have hQ : IsCompact (Prod.fst '' support (Ψ : LocallyConstant (Γ × G) ℂ)) :=
    (hasCompactSupport_iff_isCompact_support.1 (mem_compactlySupported.1 Ψ.property)).image
      continuous_fst
  let φ : LocallyConstant H ℂ := (Ψ : LocallyConstant (Γ × G) ℂ).comap
    ⟨fun h => (γ * h, (j h)⁻¹ * y * j h), by fun_prop⟩
  -- The support of `φ` lies in the preimage of the compact `Γ`-support of `Ψ` under the closed
  -- embedding `h ↦ γ * h`.
  have hemb : IsClosedEmbedding fun h : H => γ * (h : Γ) :=
    (Homeomorph.mulLeft γ).isClosedEmbedding.comp hH.isClosedEmbedding_subtypeVal
  have hφ : HasCompactSupport φ := by
    rw [hasCompactSupport_iff_isCompact_support]
    exact (hemb.isCompact_preimage hQ).of_isClosed_subset φ.isClopen_support.isClosed
      fun h hh => ⟨_, hh, rfl⟩
  exact φ.continuous.integrable_of_hasCompactSupport hφ

end FiberIntegral

section Existence

variable [TopologicalSpace Γ] [TopologicalSpace G] [IsTopologicalGroup Γ] [IsTopologicalGroup G]
  [MeasurableSpace H]

/-- A test function `Ψ` on `Γ × G` is invariant under left translation of the first variable by
the conjugates `γ * u * γ⁻¹` of all `u` near `1`. -/
private theorem eventually_forall_conj_mul_eq (Ψ : compactlySupported ℂ (Γ × G) ℂ) (γ : Γ) :
    ∀ᶠ u in 𝓝 (1 : Γ), ∀ a z, (Ψ : LocallyConstant (Γ × G) ℂ) (γ * u * γ⁻¹ * a, z) =
      (Ψ : LocallyConstant (Γ × G) ℂ) (a, z) := by
  set ψ := (Ψ : LocallyConstant (Γ × G) ℂ)
  have hψc : HasCompactSupport ψ := mem_compactlySupported.1 Ψ.property
  -- Left translation invariance of `ψ` is right translation invariance of `p ↦ ψ p⁻¹`.
  have hS := isOpen_rightTranslationStabilizer_of_hasCompactSupport
    (ψ.isLocallyConstant.comp_continuous continuous_inv) (hψc.comp_homeomorph (.inv _))
  have ht : Tendsto (fun u : Γ => (((γ * u * γ⁻¹)⁻¹, 1) : Γ × G)) (𝓝 1) (𝓝 1) :=
    (by fun_prop : Continuous fun u : Γ => (((γ * u * γ⁻¹)⁻¹, 1) : Γ × G)).tendsto' 1 1
      (by ext <;> simp)
  filter_upwards [ht (hS.mem_nhds (one_mem _))] with u hu a z
  simpa using mem_rightTranslationStabilizer.1 hu (a, z)⁻¹

/-- A test function `Ψ` on `Γ × G` is invariant under right translation of the second variable by
the conjugates `(j l)⁻¹ * w * j l` of all `w` near `1`, uniformly for `l` in a compact set. -/
private theorem eventually_forall_mul_conj_eq (hj : Continuous j)
    (Ψ : compactlySupported ℂ (Γ × G) ℂ) {K : Set Γ} (hK : IsCompact K) :
    ∀ᶠ w in 𝓝 (1 : G), ∀ l ∈ K, ∀ a z,
      (Ψ : LocallyConstant (Γ × G) ℂ) (a, z * ((j l)⁻¹ * w * j l)) =
        (Ψ : LocallyConstant (Γ × G) ℂ) (a, z) := by
  set ψ := (Ψ : LocallyConstant (Γ × G) ℂ)
  have hS := isOpen_rightTranslationStabilizer_of_hasCompactSupport ψ.isLocallyConstant
    (mem_compactlySupported.1 Ψ.property)
  refine hK.eventually_forall_of_forall_eventually fun l _ => ?_
  have ht : Tendsto (fun p : G × Γ => ((1, (j p.2)⁻¹ * p.1 * j p.2) : Γ × G)) (𝓝 (1, l))
      (𝓝 1) :=
    (by fun_prop : Continuous fun p : G × Γ => ((1, (j p.2)⁻¹ * p.1 * j p.2) : Γ × G)).tendsto'
      _ _ (by ext <;> simp)
  filter_upwards [ht (hS.mem_nhds (one_mem _))] with p hp a z
  simpa using mem_rightTranslationStabilizer.1 hp (a, z)

omit [IsTopologicalGroup Γ] [IsTopologicalGroup G] in
/-- The fibre integrals of `Ψ` at `(γ * u, x)` and at `(γ, y)` agree when `Ψ` is invariant under
left translation of the first variable by `γ * u * γ⁻¹`, and under right translation of the second
variable by the conjugates of `y⁻¹ * x` by `j l` for `l ∈ γ⁻¹ Q`, where `Q` is the projection of the
support of `Ψ` to `Γ`. -/
private theorem fiberIntegral_mul_eq (μ : Measure H) (Ψ : compactlySupported ℂ (Γ × G) ℂ)
    {γ u : Γ} {x y : G}
    (hu : ∀ a z, (Ψ : LocallyConstant (Γ × G) ℂ) (γ * u * γ⁻¹ * a, z) =
      (Ψ : LocallyConstant (Γ × G) ℂ) (a, z))
    (hx : ∀ l ∈ (γ⁻¹ * ·) '' (Prod.fst '' support (Ψ : LocallyConstant (Γ × G) ℂ)), ∀ a z,
      (Ψ : LocallyConstant (Γ × G) ℂ) (a, z * ((j l)⁻¹ * (y⁻¹ * x) * j l)) =
        (Ψ : LocallyConstant (Γ × G) ℂ) (a, z)) :
    fiberIntegral j μ Ψ (γ * u) x = fiberIntegral j μ Ψ γ y := by
  set ψ := (Ψ : LocallyConstant (Γ × G) ℂ)
  simp only [fiberIntegral_def]
  congr 1
  funext h
  rw [show γ * u * h = γ * u * γ⁻¹ * (γ * h) by group, hu]
  by_cases hh : γ * h ∈ Prod.fst '' support ψ
  · rw [← hx h ⟨γ * h, hh, by group⟩ (γ * h) ((j h)⁻¹ * y * j h)]
    congr 2
    group
  · -- Off the projection of the support, both values vanish.
    have h0 (z : G) : ψ (γ * h, z) = 0 := by
      by_contra hz
      exact hh ⟨(γ * h, z), hz, rfl⟩
    rw [h0, h0]

/-- Near a point `j γ * y * (j γ)⁻¹` of `C` with `y ∈ X`, every point of `C` is a conjugate of a
point of `X` whose fibre integral equals that of `(γ, y)`. -/
private theorem IsSlice.eventually_exists_fiberIntegral_eq (hs : IsSlice j H X C)
    (hj : Continuous j) (μ : Measure H) (Ψ : compactlySupported ℂ (Γ × G) ℂ) (γ : Γ) {y : G}
    (hy : y ∈ X) :
    ∀ᶠ c in 𝓝[C] (j γ * y * (j γ)⁻¹), ∃ γ', ∃ y' ∈ X, j γ' * y' * (j γ')⁻¹ = c ∧
      fiberIntegral j μ Ψ γ' y' = fiberIntegral j μ Ψ γ y := by
  have hQ : IsCompact ((γ⁻¹ * ·) '' (Prod.fst '' support (Ψ : LocallyConstant (Γ × G) ℂ))) :=
    ((hasCompactSupport_iff_isCompact_support.1 (mem_compactlySupported.1 Ψ.property)).image
      continuous_fst).image (continuous_const_mul _)
  -- Points of `C` near `y` are `j u * x * (j u)⁻¹` with `u` near `1` and `y⁻¹ * x` near `1`.
  have hx : Tendsto (fun p : Γ × G => y⁻¹ * ((j p.1)⁻¹ * p.2 * j p.1)) (𝓝 (1, y)) (𝓝 1) :=
    (by fun_prop : Continuous fun p : Γ × G => y⁻¹ * ((j p.1)⁻¹ * p.2 * j p.1)).tendsto' _ _
      (by simp)
  have hx' := hx.eventually (eventually_forall_mul_conj_eq hj Ψ hQ)
  rw [nhds_prod_eq] at hx'
  obtain ⟨pa, hpa, pb, hpb, hpab⟩ := eventually_prod_iff.1 hx'
  have hy' : ∀ᶠ c in 𝓝[C] y, ∃ γ', ∃ y' ∈ X, j γ' * y' * (j γ')⁻¹ = j γ * c * (j γ)⁻¹ ∧
      fiberIntegral j μ Ψ γ' y' = fiberIntegral j μ Ψ γ y := by
    filter_upwards [hs.eventually_exists_conj y hy _ (hpa.and (eventually_forall_conj_mul_eq Ψ γ)),
      nhdsWithin_le_nhds hpb] with c ⟨u, ⟨hua, huV⟩, x, hx, hc⟩ hcb
    refine ⟨γ * u, x, hx, by rw [← hc, map_mul]; group, fiberIntegral_mul_eq μ Ψ huV ?_⟩
    have hxy := hpab hua hcb
    rwa [← hc, show (j u)⁻¹ * (j u * x * (j u)⁻¹) * j u = x by group] at hxy
  -- Transport from `y` to `j γ * y * (j γ)⁻¹` by conjugation with `(j γ)⁻¹`.
  have ht : Tendsto (fun c => (j γ)⁻¹ * c * j γ) (𝓝[C] (j γ * y * (j γ)⁻¹)) (𝓝[C] y) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, eventually_mem_nhdsWithin.mono fun c hc => ?_⟩
    · refine Tendsto.mono_left ?_ nhdsWithin_le_nhds
      exact (by fun_prop : Continuous fun c => (j γ)⁻¹ * c * j γ).tendsto' _ _ (by group)
    · simpa using hs.conj_mem_of_mem γ⁻¹ hc
  filter_upwards [ht.eventually hy'] with c hc
  simpa [mul_assoc] using hc

/-- **The fibre integral of a test function is the restriction of a test function.** For a slice
`X ⊆ C` in a Hausdorff, locally compact, totally disconnected group `G` and a test function `Ψ` on
`Γ × G`, there is a test function `f` on `G` with `f (j γ * y * (j γ)⁻¹)` equal to the fibre
integral of `Ψ` at `(γ, y)` for all `γ` and all `y ∈ X`. -/
theorem IsSlice.exists_eq_fiberIntegral [T2Space G] [WeaklyLocallyCompactSpace G]
    [TotallyDisconnectedSpace G] [MeasurableMul H] (hs : IsSlice j H X C) (hj : Continuous j)
    (μ : Measure H) [μ.IsMulLeftInvariant] (Ψ : compactlySupported ℂ (Γ × G) ℂ) :
    ∃ f : compactlySupported ℂ G ℂ, ∀ γ, ∀ y ∈ X,
      (f : LocallyConstant G ℂ) (j γ * y * (j γ)⁻¹) = fiberIntegral j μ Ψ γ y := by
  -- Choose a point of `Γ × X` above every point of `C`; the value there does not depend on it.
  have hrep : ∀ c : C, ∃ γ, ∃ y ∈ X, j γ * y * (j γ)⁻¹ = c := fun c => (hs.mem_iff c).1 c.property
  choose g x hx hgx using hrep
  set F : C → ℂ := fun c => fiberIntegral j μ Ψ (g c) (x c)
  have hF : ∀ c : C, ∀ γ, ∀ y ∈ X, j γ * y * (j γ)⁻¹ = c → F c = fiberIntegral j μ Ψ γ y :=
    fun c γ y hy hc => hs.fiberIntegral_eq μ Ψ (hx c) hy ((hgx c).trans hc.symm)
  have hlc : IsLocallyConstant F := by
    refine (IsLocallyConstant.iff_eventually_eq F).2 fun c => ?_
    have ht : Tendsto ((↑) : C → G) (𝓝 c) (𝓝[C] (c : G)) :=
      tendsto_nhdsWithin_iff.2 ⟨continuous_subtypeVal.tendsto c, .of_forall fun c' => c'.property⟩
    have hev := hs.eventually_exists_fiberIntegral_eq hj μ Ψ (g c) (hx c)
    rw [hgx c] at hev
    filter_upwards [ht.eventually hev] with c' ⟨γ', y', hy', hc', hval⟩
    rw [hF c' γ' y' hy' hc', hval]
  -- `F` vanishes off the preimage of the compact image of `support Ψ` under conjugation.
  set ψ := (Ψ : LocallyConstant (Γ × G) ℂ)
  have hK : IsCompact (((↑) : C → G) ⁻¹'
      ((fun p : Γ × G => j p.1 * p.2 * (j p.1)⁻¹) '' support ψ)) :=
    hs.isClosed.isClosedEmbedding_subtypeVal.isCompact_preimage
      ((hasCompactSupport_iff_isCompact_support.1 (mem_compactlySupported.1 Ψ.property)).image
        (by fun_prop))
  have hcs : HasCompactSupport F := by
    refine HasCompactSupport.intro hK fun c hc => ?_
    by_contra hne
    obtain ⟨h, hh⟩ := exists_ne_zero_of_integral_ne_zero hne
    refine hc ⟨(g c * h, (j h)⁻¹ * x c * j h), hh, ?_⟩
    rw [← hgx c]
    simp only [map_mul]
    group
  obtain ⟨f, hf⟩ := compactlySupported.restrict_surjective (R := ℂ) (M := ℂ) hs.isClosed
    ⟨⟨F, hlc⟩, mem_compactlySupported.2 hcs⟩
  refine ⟨f, fun γ y hy => ?_⟩
  have hfc := congrArg (fun F : compactlySupported ℂ C ℂ =>
    (F : LocallyConstant C ℂ) ⟨_, hs.conj_mem γ hy⟩) hf
  simp only [compactlySupported.restrict_apply] at hfc
  rw [hfc]
  exact hF _ γ y hy rfl

end Existence

section Descent

variable [TopologicalSpace Γ] [TopologicalSpace G] [IsTopologicalGroup Γ] [IsTopologicalGroup G]

/-- A test function `Ψ` on `Γ × G` is invariant under right translation in the first variable by
an open subgroup `U`, and finitely many cosets of `U` contain the first coordinates of the points
where `Ψ` does not vanish. -/
private theorem exists_openSubgroup_finset (Ψ : compactlySupported ℂ (Γ × G) ℂ) :
    ∃ (U : Subgroup Γ) (T : Finset (Γ ⧸ U)), IsOpen (U : Set Γ) ∧
      (∀ u ∈ U, ∀ a z, (Ψ : LocallyConstant (Γ × G) ℂ) (a * u, z) =
        (Ψ : LocallyConstant (Γ × G) ℂ) (a, z)) ∧
      ∀ a z, (Ψ : LocallyConstant (Γ × G) ℂ) (a, z) ≠ 0 → (a : Γ ⧸ U) ∈ T := by
  classical
  set ψ := (Ψ : LocallyConstant (Γ × G) ℂ)
  have hψc : HasCompactSupport ψ := mem_compactlySupported.1 Ψ.property
  set U : Subgroup Γ := (rightTranslationStabilizer ψ).comap (MonoidHom.inl Γ G)
  have hinl' : ⇑(MonoidHom.inl Γ G) = fun u => (u, 1) := funext fun u => by simp
  have hinl : Continuous (MonoidHom.inl Γ G) := by
    rw [hinl']
    fun_prop
  have hUopen : IsOpen (U : Set Γ) :=
    (isOpen_rightTranslationStabilizer_of_hasCompactSupport ψ.isLocallyConstant hψc).preimage
      hinl
  have hUψ : ∀ u ∈ U, ∀ a z, ψ (a * u, z) = ψ (a, z) := fun u hu a z => by
    simpa using mem_rightTranslationStabilizer.1 (Subgroup.mem_comap.1 hu) (a, z)
  -- Cover the compact first projection of the support by the open cosets `a U`.
  have hQ : IsCompact (Prod.fst '' support ψ) :=
    (hasCompactSupport_iff_isCompact_support.1 hψc).image continuous_fst
  obtain ⟨T, hT⟩ := hQ.elim_finite_subcover (fun a : Γ => (a⁻¹ * ·) ⁻¹' (U : Set Γ))
    (fun a => hUopen.preimage (continuous_const_mul _))
    (fun a _ => mem_iUnion.2 ⟨a, by simp⟩)
  refine ⟨U, T.image (↑), hUopen, hUψ, fun a z ha => ?_⟩
  obtain ⟨t, ht, hta⟩ := mem_iUnion₂.1 (hT ⟨(a, z), ha, rfl⟩)
  exact Finset.mem_image.2 ⟨t, ht, QuotientGroup.eq.2 (by simpa using hta)⟩

variable {U : Subgroup Γ} {T : Finset (Γ ⧸ U)}

omit [Group G] [IsTopologicalGroup Γ] [IsTopologicalGroup G] in
open scoped Classical in
/-- Summing the restrictions of `Ψ (·, z)` to the cosets in `T` recovers `Ψ (·, z)`. -/
private theorem sum_ite_eq (Ψ : compactlySupported ℂ (Γ × G) ℂ)
    (hT : ∀ a z, (Ψ : LocallyConstant (Γ × G) ℂ) (a, z) ≠ 0 → (a : Γ ⧸ U) ∈ T) (a : Γ) (z : G) :
    ∑ q ∈ T, (if q.out⁻¹ * a ∈ U then (Ψ : LocallyConstant (Γ × G) ℂ) (a, z) else 0) =
      (Ψ : LocallyConstant (Γ × G) ℂ) (a, z) := by
  have hq (q : Γ ⧸ U) : q.out⁻¹ * a ∈ U ↔ (a : Γ ⧸ U) = q := by
    rw [← QuotientGroup.eq, QuotientGroup.out_eq', eq_comm]
  simp_rw [hq, Finset.sum_ite_eq]
  split_ifs with h
  · rfl
  · by_contra hne
    exact h (hT a z (Ne.symm hne))

omit [Group G] [IsTopologicalGroup G] in
/-- The integral of `Ψ (·, y)` over `Γ` is `vol(U)` times the sum of the values of `Ψ (·, y)` at
the representatives of the cosets in `T`. -/
private theorem integral_eq_measureReal_mul_sum [MeasurableSpace Γ] [BorelSpace Γ]
    (ν : Measure Γ) [ν.IsMulLeftInvariant] [IsFiniteMeasureOnCompacts ν]
    (Ψ : compactlySupported ℂ (Γ × G) ℂ) (hUopen : IsOpen (U : Set Γ))
    (hUψ : ∀ u ∈ U, ∀ a z, (Ψ : LocallyConstant (Γ × G) ℂ) (a * u, z) =
        (Ψ : LocallyConstant (Γ × G) ℂ) (a, z))
    (hT : ∀ a z, (Ψ : LocallyConstant (Γ × G) ℂ) (a, z) ≠ 0 → (a : Γ ⧸ U) ∈ T) (y : G) :
    ∫ γ, (Ψ : LocallyConstant (Γ × G) ℂ) (γ, y) ∂ν =
      ν.real U * ∑ q ∈ T, (Ψ : LocallyConstant (Γ × G) ℂ) (q.out, y) := by
  classical
  set ψ := (Ψ : LocallyConstant (Γ × G) ℂ)
  have hint : Integrable (fun γ => ψ (γ, y)) ν := by
    let φ : LocallyConstant Γ ℂ := ψ.comap ⟨fun γ => (γ, y), by fun_prop⟩
    have hφ : HasCompactSupport φ := by
      rw [hasCompactSupport_iff_isCompact_support]
      exact ((hasCompactSupport_iff_isCompact_support.1 (mem_compactlySupported.1
        Ψ.property)).image continuous_fst).of_isClosed_subset φ.isClopen_support.isClosed
          fun γ hγ => ⟨_, hγ, rfl⟩
    exact φ.continuous.integrable_of_hasCompactSupport hφ
  set s : Γ ⧸ U → Set Γ := fun q => (q.out⁻¹ * ·) ⁻¹' (U : Set Γ)
  have hs (q : Γ ⧸ U) : MeasurableSet (s q) :=
    (hUopen.preimage (continuous_const_mul _)).measurableSet
  calc ∫ γ, ψ (γ, y) ∂ν = ∫ γ, ∑ q ∈ T, (s q).indicator (fun γ => ψ (γ, y)) γ ∂ν := by
        congr 1
        funext γ
        rw [← sum_ite_eq Ψ hT γ y]
        exact Finset.sum_congr rfl fun q _ => by simp [s, Set.indicator_apply, ψ]
    _ = ∑ q ∈ T, ∫ γ, (s q).indicator (fun γ => ψ (γ, y)) γ ∂ν :=
        integral_finsetSum _ fun q _ => hint.indicator (hs q)
    _ = ∑ q ∈ T, ν.real U * ψ (q.out, y) := by
        refine Finset.sum_congr rfl fun q _ => ?_
        -- On the coset `s q`, the function `ψ (·, y)` is the constant `ψ (q.out, y)`.
        have hc : (s q).indicator (fun γ => ψ (γ, y)) = (s q).indicator fun _ => ψ (q.out, y) :=
          indicator_congr fun γ hγ => by
            rw [← hUψ _ hγ q.out y, mul_inv_cancel_left]
        rw [hc, integral_indicator_const _ (hs q), Complex.real_smul, measureReal_def,
          measure_preimage_mul, measureReal_def]
    _ = ν.real U * ∑ q ∈ T, ψ (q.out, y) := (Finset.mul_sum _ _ _).symm

omit [Group G] [IsTopologicalGroup G] in
/-- If `Ψ (·, y)` integrates to zero over `Γ`, the values of `Ψ (·, y)` at the representatives of
the cosets in `T` sum to zero. -/
private theorem sum_eq_zero_of_integral_eq_zero [MeasurableSpace Γ] [BorelSpace Γ]
    (ν : Measure Γ) [ν.IsHaarMeasure] (Ψ : compactlySupported ℂ (Γ × G) ℂ)
    (hUopen : IsOpen (U : Set Γ))
    (hUψ : ∀ u ∈ U, ∀ a z, (Ψ : LocallyConstant (Γ × G) ℂ) (a * u, z) =
      (Ψ : LocallyConstant (Γ × G) ℂ) (a, z))
    (hT : ∀ a z, (Ψ : LocallyConstant (Γ × G) ℂ) (a, z) ≠ 0 → (a : Γ ⧸ U) ∈ T) (y : G)
    (h0 : ∫ γ, (Ψ : LocallyConstant (Γ × G) ℂ) (γ, y) ∂ν = 0) :
    ∑ q ∈ T, (Ψ : LocallyConstant (Γ × G) ℂ) (q.out, y) = 0 := by
  set ψ := (Ψ : LocallyConstant (Γ × G) ℂ)
  by_contra hne
  obtain ⟨q, -, hq⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
  -- The coset `q.out U` lies in the compact first projection of the support, so `vol(U) < ∞`.
  have hUQ : (U : Set Γ) ⊆ (q.out * ·) ⁻¹' (Prod.fst '' support ψ) := fun u hu =>
    ⟨(q.out * u, y), by rwa [mem_support, hUψ u hu], rfl⟩
  have hfin : ν U ≠ ⊤ := ((measure_mono hUQ).trans_lt
    (((Homeomorph.mulLeft q.out).isCompact_preimage.2
      ((hasCompactSupport_iff_isCompact_support.1 (mem_compactlySupported.1
        Ψ.property)).image continuous_fst)).measure_lt_top)).ne
  rw [integral_eq_measureReal_mul_sum ν Ψ hUopen hUψ hT y, mul_eq_zero, measureReal_def,
    Complex.ofReal_eq_zero, ENNReal.toReal_eq_zero_iff] at h0
  exact h0.elim (·.elim (hUopen.measure_pos ν ⟨1, U.one_mem⟩).ne' hfin) hne

open scoped Classical in
/-- The piece `(γ, y) ↦ 1_U (γ) Ψ (r * γ, y)` of a test function `Ψ` on `Γ × G`, for an open
subgroup `U` and a coset representative `r`, is a test function. -/
private theorem exists_eq_ite_mem (Ψ : compactlySupported ℂ (Γ × G) ℂ)
    (hUopen : IsOpen (U : Set Γ)) :
    ∃ Φ : Γ ⧸ U → compactlySupported ℂ (Γ × G) ℂ, ∀ q a z,
      (Φ q : LocallyConstant (Γ × G) ℂ) (a, z) =
        if a ∈ U then (Ψ : LocallyConstant (Γ × G) ℂ) (q.out * a, z) else 0 := by
  classical
  have hUcl : IsClopen ((U : Set Γ) ×ˢ (univ : Set G)) :=
    ⟨(U.isClosed_of_isOpen hUopen).prod isClosed_univ, hUopen.prod isOpen_univ⟩
  -- The translate `(γ, y) ↦ Ψ (r * γ, y)` is a test function, and so is its restriction to the
  -- clopen set `U × G`.
  set τ : Γ ⧸ U → compactlySupported ℂ (Γ × G) ℂ := fun q =>
    compactlySupportedRep ℂ (Γ × G) (Γ × G) ℂ (q.out⁻¹, 1) Ψ
  refine ⟨fun q => ⟨(τ q : LocallyConstant (Γ × G) ℂ).indicator hUcl,
    mem_compactlySupported.2 ((mem_compactlySupported.1 (τ q).property).mono fun p hp => ?_)⟩,
    fun q a z => by simp [τ, LocallyConstant.indicator_apply, Set.indicator_apply]⟩
  rw [mem_support, LocallyConstant.indicator_apply] at hp
  exact (indicator_apply_ne_zero.1 hp).2

open scoped Classical in
/-- The fibre integral of `Ψ` is the sum of the fibre integrals of the pieces `1_U (γ) Ψ (r γ, y)`
at `(r⁻¹ γ, y)`, over the representatives `r` of the cosets in `T`. -/
private theorem fiberIntegral_eq_sum [MeasurableSpace H] [OpensMeasurableSpace H]
    (hj : Continuous j) (hH : IsClosed (H : Set Γ)) (μ : Measure H) [IsFiniteMeasureOnCompacts μ]
    (Ψ : compactlySupported ℂ (Γ × G) ℂ)
    (hT : ∀ a z, (Ψ : LocallyConstant (Γ × G) ℂ) (a, z) ≠ 0 → (a : Γ ⧸ U) ∈ T)
    (Φ : Γ ⧸ U → compactlySupported ℂ (Γ × G) ℂ)
    (hΦ : ∀ q a z, (Φ q : LocallyConstant (Γ × G) ℂ) (a, z) =
      if a ∈ U then (Ψ : LocallyConstant (Γ × G) ℂ) (q.out * a, z) else 0) (γ : Γ) (y : G) :
    fiberIntegral j μ Ψ γ y = ∑ q ∈ T, fiberIntegral j μ (Φ q) (q.out⁻¹ * γ) y := by
  simp only [fiberIntegral_def]
  rw [← integral_finsetSum _ fun q _ => integrable_fiberIntegral_integrand hj hH μ (Φ q) _ y]
  congr 1
  funext h
  rw [← sum_ite_eq Ψ hT]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [hΦ]
  simp only [mul_assoc, mul_inv_cancel_left]

/-- **Descent of invariant distributions to a slice.** Let `X ⊆ C` be a slice for the conjugation
action of `Γ` on a Hausdorff, locally compact, totally disconnected group `G` through a continuous
`j`, with closed stabiliser `H` carrying a left invariant measure `μ` finite on compact sets, and
let `ν` be a Haar measure on `Γ`.
Let `I` be a linear form on the test functions on `G` that is invariant under conjugation by
`j Γ` and vanishes on the test functions vanishing on `C`. If a test function `Ψ` on `Γ × G`
satisfies `∫ γ, Ψ (γ, y) ∂ν = 0` for every `y ∈ X`, then `I f = 0` for every test function `f`
whose value at `j γ * y * (j γ)⁻¹` is the fibre integral of `Ψ` at `(γ, y)` for all `γ` and
`y ∈ X`. Such an `f` exists by `TauCeti.IsSlice.exists_eq_fiberIntegral`. -/
theorem IsSlice.map_eq_zero_of_eq_fiberIntegral [T2Space G] [WeaklyLocallyCompactSpace G]
    [TotallyDisconnectedSpace G] [MeasurableSpace Γ] [BorelSpace Γ] [MeasurableSpace H]
    [BorelSpace H] (hs : IsSlice j H X C) (hj : Continuous j)
    (hH : IsClosed (H : Set Γ)) (ν : Measure Γ) [ν.IsHaarMeasure] (μ : Measure H)
    [μ.IsMulLeftInvariant] [IsFiniteMeasureOnCompacts μ] (I : compactlySupported ℂ G ℂ →ₗ[ℂ] ℂ)
    (hI : ∀ γ f, I (compactlySupportedRep ℂ (ConjAct G) G ℂ (ConjAct.toConjAct (j γ)) f) = I f)
    (hIC : ∀ f : compactlySupported ℂ G ℂ, (∀ c ∈ C, (f : LocallyConstant G ℂ) c = 0) → I f = 0)
    (Ψ : compactlySupported ℂ (Γ × G) ℂ)
    (hΨ : ∀ y ∈ X, ∫ γ, (Ψ : LocallyConstant (Γ × G) ℂ) (γ, y) ∂ν = 0)
    (f : compactlySupported ℂ G ℂ)
    (hf : ∀ γ, ∀ y ∈ X, (f : LocallyConstant G ℂ) (j γ * y * (j γ)⁻¹) = fiberIntegral j μ Ψ γ y) :
    I f = 0 := by
  classical
  obtain ⟨U, T, hUopen, hUψ, hT⟩ := exists_openSubgroup_finset Ψ
  have hsum (y : G) (hy : y ∈ X) : ∑ q ∈ T, (Ψ : LocallyConstant (Γ × G) ℂ) (q.out, y) = 0 :=
    sum_eq_zero_of_integral_eq_zero ν Ψ hUopen hUψ hT y (hΨ y hy)
  obtain ⟨Φ, hΦ⟩ := exists_eq_ite_mem Ψ hUopen
  choose g hg using fun q => hs.exists_eq_fiberIntegral hj μ (Φ q)
  set R : Γ ⧸ U → compactlySupported ℂ G ℂ := fun q =>
    compactlySupportedRep ℂ (ConjAct G) G ℂ (ConjAct.toConjAct (j q.out)) (g q)
  have hsum_apply (F : Γ ⧸ U → compactlySupported ℂ G ℂ) (x : G) :
      ((∑ q ∈ T, F q : compactlySupported ℂ G ℂ) : LocallyConstant G ℂ) x =
        ∑ q ∈ T, (F q : LocallyConstant G ℂ) x := by
    rw [Submodule.coe_sum]
    exact map_sum (LocallyConstant.evalAddMonoidHom x) _ _
  -- On `C`, `f` is the sum of the conjugates `R q` of the `g q`.
  have h₁ : I f = ∑ q ∈ T, I (R q) := by
    rw [← map_sum, ← sub_eq_zero, ← map_sub]
    refine hIC _ fun c hc => ?_
    obtain ⟨γ, y, hy, rfl⟩ := (hs.mem_iff c).1 hc
    have hR : ∀ q, (R q : LocallyConstant G ℂ) (j γ * y * (j γ)⁻¹) =
        fiberIntegral j μ (Φ q) (q.out⁻¹ * γ) y := fun q => by
      rw [← hg q _ y hy]
      simp only [R, compactlySupportedRep_apply_coe, ConjAct.smul_def, map_mul, map_inv,
        ConjAct.ofConjAct_toConjAct, inv_inv]
      congr 1
      group
    simp only [Submodule.coe_sub, LocallyConstant.coe_sub, Pi.sub_apply, hsum_apply, hR,
      hf γ y hy, fiberIntegral_eq_sum hj hH μ Ψ hT Φ hΦ γ y, sub_self]
  -- The sum of the `g q` vanishes on `C`, since the sum of the pieces vanishes on `Γ × X`.
  have h₂ : I (∑ q ∈ T, g q) = 0 := by
    refine hIC _ fun c hc => ?_
    obtain ⟨γ, y, hy, rfl⟩ := (hs.mem_iff c).1 hc
    simp only [hsum_apply, hg _ γ y hy, fiberIntegral_def]
    rw [← integral_finsetSum _ fun q _ => integrable_fiberIntegral_integrand hj hH μ (Φ q) _ y]
    refine integral_eq_zero_of_ae (ae_of_all _ fun h => ?_)
    simp only [hΦ, Pi.zero_apply]
    split_ifs with hγh
    · have hX := hs.inv_conj_mem h.property hy
      rw [← hsum _ hX]
      exact Finset.sum_congr rfl fun q _ => hUψ _ hγh _ _
    · simp
  rw [h₁]
  simpa [R, hI, ← map_sum] using h₂

end Descent

end TauCeti

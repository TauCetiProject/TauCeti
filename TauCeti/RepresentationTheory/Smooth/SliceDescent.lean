/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.MeasureTheory.Group.Integral
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import TauCeti.MeasureTheory.Group.OpenSubgroup
public import TauCeti.RepresentationTheory.Smooth.CompactSupport
public import TauCeti.Topology.Algebra.Group.LocallyConstant
public import TauCeti.Topology.Algebra.Support
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
`LocallyConstant.compactlySupported`, with values in a real normed space `E`) and a measure `μ` on
`H`, the *fibre integral* (`TauCeti.fiberIntegral j μ Ψ γ y`) integrates `Ψ` over the `H`-orbit of
`(γ, y)`. When `μ` is left invariant, its value at `(γ, y)` with `y ∈ X` depends only on the point
`j γ * y * (j γ)⁻¹` of `C` (`TauCeti.IsSlice.fiberIntegral_eq`), because the fibres of
`(γ, y) ↦ j γ * y * (j γ)⁻¹` over `C` are the `H`-orbits (`TauCeti.IsSlice.conj_eq_conj_iff`); the
resulting function on `C` is the restriction of a test function on `G` when `G` is Hausdorff,
locally compact and totally disconnected (`TauCeti.IsSlice.exists_eq_fiberIntegral`).

The main theorem is the descent of invariant distributions
(`TauCeti.IsSlice.map_eq_zero_of_integral_eq_zero_of_eq_fiberIntegral`): let `μ` be left invariant
and finite on compact sets, and let `I` be a linear form on the complex test functions on `G` that
is invariant under conjugation by `j Γ` and only depends on the restriction of a test function to
`C`. If `Ψ` integrates to zero along `Γ` at every point of `X`, that is `∫ γ, Ψ (γ, y) = 0` for a
Haar measure on `Γ` and every `y ∈ X`, then `I` vanishes on every test function whose restriction
to `C` is the fibre integral of `Ψ`.

The proof follows Harish-Chandra's descent along a slice. Choose an open subgroup `U ⊆ Γ` under
which `Ψ` is invariant on the right in the first variable; finitely many cosets `r U` cover the
`Γ`-support of `Ψ`, and `Ψ (γ, y) = ∑_r 1_{r U} (γ) Ψ (r, y)`. The fibre integral of the piece
supported on `r U` is the translate, under conjugation by `j r`, of the fibre integral of the
piece `1_U (γ) Ψ (r, y)`, so invariance of `I` replaces every piece by one supported on `U`. The sum
of those pieces is `1_U (γ) ∑_r Ψ (r, y)`, and `vol(U) ∑_r Ψ (r, y) = ∫ γ, Ψ (γ, y) = 0` for
`y ∈ X` (`OpenSubgroup.sum_eq_zero_of_integral_eq_zero`), so its fibre integral vanishes on `C`.

## Main definitions

* `TauCeti.IsSlice j H X C`: `X ⊆ C` is a slice for the conjugation action of `Γ` through `j`, with
  stabiliser `H`.
* `TauCeti.fiberIntegral j μ Ψ γ y`: the integral `∫ h, Ψ (γ * h, (j h)⁻¹ * y * j h) ∂μ` over the
  `H`-orbit of `(γ, y)`.

## Main results

* `TauCeti.IsSlice.conj_eq_conj_iff`: the fibres of `(γ, y) ↦ j γ * y * (j γ)⁻¹` on `Γ × X` are
  the `H`-orbits.
* `TauCeti.fiberIntegral_add`, `TauCeti.fiberIntegral_smul`, `TauCeti.fiberIntegral_finsetSum`:
  linearity of the fibre integral.
* `TauCeti.IsSlice.fiberIntegral_eq`: for left invariant `μ`, the fibre integral is constant on the
  fibres of `(γ, y) ↦ j γ * y * (j γ)⁻¹` over `C`.
* `TauCeti.IsSlice.exists_eq_fiberIntegral`: the fibre integral of a test function on `Γ × G` is
  the restriction to `C` of a test function on `G`.
* `TauCeti.IsSlice.map_eq_zero_of_integral_eq_zero_of_eq_fiberIntegral`: the descent of invariant
  distributions.

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

variable {Γ G E : Type*} [Group Γ] [Group G] [NormedAddCommGroup E] [NormedSpace ℝ E]
  {R : Type*} [Semiring R] [Module R E] {j : Γ →* G} {H : Subgroup Γ} {X C : Set G}

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

/-- **The fibres over `C` are the `H`-orbits.** Two points `(γ, y)` and `(γ', y')` of `Γ × X` have
the same conjugate `j γ * y * (j γ)⁻¹ = j γ' * y' * (j γ')⁻¹` exactly when
`(γ', y') = (γ * h, (j h)⁻¹ * y * j h)` for some `h ∈ H`. -/
theorem conj_eq_conj_iff (hs : IsSlice j H X C) {γ γ' : Γ} {y y' : G} (hy : y ∈ X)
    (hy' : y' ∈ X) :
    j γ * y * (j γ)⁻¹ = j γ' * y' * (j γ')⁻¹ ↔ ∃ h ∈ H, γ' = γ * h ∧ y' = (j h)⁻¹ * y * j h := by
  refine ⟨fun hc => ?_, ?_⟩
  · -- The element `h = γ⁻¹ * γ'` conjugates `y'` to `y`, hence lies in `H`.
    have hk : y' = (j (γ⁻¹ * γ'))⁻¹ * y * j (γ⁻¹ * γ') :=
      calc y' = (j γ')⁻¹ * (j γ' * y' * (j γ')⁻¹) * j γ' := by group
        _ = (j (γ⁻¹ * γ'))⁻¹ * y * j (γ⁻¹ * γ') := by
          rw [← hc]
          simp only [map_mul, map_inv]
          group
    have hkH : γ⁻¹ * γ' ∈ H := by
      have hk' : j (γ⁻¹ * γ')⁻¹ * y * (j (γ⁻¹ * γ')⁻¹)⁻¹ = y' := by rw [hk, map_inv, inv_inv]
      rw [← inv_mem_iff, ← hs.conj_mem_iff _ y hy, hk']
      exact hy'
    exact ⟨_, hkH, (mul_inv_cancel_left γ γ').symm, hk⟩
  · rintro ⟨h, -, rfl, rfl⟩
    simp only [map_mul]
    group

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
/-- The **fibre integral** of `Ψ : Γ × G → E` at `(γ, y)`: the integral
`∫ h, Ψ (γ * h, (j h)⁻¹ * y * j h) ∂μ` of `Ψ` over the orbit of `(γ, y)` under the action of `H`
by `h • (γ, y) = (γ * h⁻¹, j h * y * (j h)⁻¹)`. For `y` in a slice and left invariant `μ` it only
depends on `j γ * y * (j γ)⁻¹` (`TauCeti.IsSlice.fiberIntegral_eq`). -/
def fiberIntegral (μ : Measure H) (Ψ : Γ × G → E) (γ : Γ) (y : G) : E :=
  ∫ h, Ψ (γ * h, (j h)⁻¹ * y * j h) ∂μ

/-- The value of the fibre integral at `(γ, y)` as an integral over `H`. -/
theorem fiberIntegral_apply (μ : Measure H) (Ψ : Γ × G → E) (γ : Γ) (y : G) :
    fiberIntegral j μ Ψ γ y = ∫ h, Ψ (γ * h, (j h)⁻¹ * y * j h) ∂μ :=
  (rfl)

/-- The fibre integral of `0` vanishes. -/
@[simp]
theorem fiberIntegral_zero (μ : Measure H) (γ : Γ) (y : G) :
    fiberIntegral j μ (0 : Γ × G → E) γ y = 0 := by
  simp [fiberIntegral_apply]

/-- The fibre integral is additive on functions whose integrands over the orbit are integrable. -/
theorem fiberIntegral_add (μ : Measure H) {Ψ Φ : Γ × G → E} {γ : Γ} {y : G}
    (hΨ : Integrable (fun h : H => Ψ (γ * h, (j h)⁻¹ * y * j h)) μ)
    (hΦ : Integrable (fun h : H => Φ (γ * h, (j h)⁻¹ * y * j h)) μ) :
    fiberIntegral j μ (Ψ + Φ) γ y = fiberIntegral j μ Ψ γ y + fiberIntegral j μ Φ γ y := by
  simp only [fiberIntegral_apply, Pi.add_apply]
  exact integral_add hΨ hΦ

/-- The fibre integral commutes with scalar multiplication. -/
theorem fiberIntegral_smul {𝕜 : Type*} [NontriviallyNormedField 𝕜] [NormedSpace 𝕜 E]
    [SMulCommClass ℝ 𝕜 E] (μ : Measure H) (c : 𝕜) (Ψ : Γ × G → E) (γ : Γ) (y : G) :
    fiberIntegral j μ (c • Ψ) γ y = c • fiberIntegral j μ Ψ γ y := by
  simp only [fiberIntegral_apply, Pi.smul_apply]
  exact integral_smul c _

/-- The fibre integral of a finite sum of functions whose integrands over the orbit are integrable
is the sum of their fibre integrals. -/
theorem fiberIntegral_finsetSum {ι : Type*} (μ : Measure H) (s : Finset ι) {Ψ : ι → Γ × G → E}
    {γ : Γ} {y : G} (hΨ : ∀ i ∈ s, Integrable (fun h : H => Ψ i (γ * h, (j h)⁻¹ * y * j h)) μ) :
    fiberIntegral j μ (∑ i ∈ s, Ψ i) γ y = ∑ i ∈ s, fiberIntegral j μ (Ψ i) γ y := by
  simp only [fiberIntegral_apply, Finset.sum_apply]
  exact integral_finsetSum s hΨ

/-- Translating `Ψ` on the left in the first variable translates its fibre integral. -/
theorem fiberIntegral_comp_mul_left (μ : Measure H) (Ψ : Γ × G → E) (δ γ : Γ) (y : G) :
    fiberIntegral j μ (fun p => Ψ (δ * p.1, p.2)) γ y = fiberIntegral j μ Ψ (δ * γ) y := by
  simp only [fiberIntegral_apply, mul_assoc]

/-- **The fibre integral is constant on the fibres over `C`.** For a left invariant measure `μ` on
`H`, if two points `(γ, y)` and `(γ', y')` of `Γ × X` have the same conjugate
`j γ * y * (j γ)⁻¹ = j γ' * y' * (j γ')⁻¹`, their fibre integrals agree. -/
theorem IsSlice.fiberIntegral_eq [TopologicalSpace Γ] [TopologicalSpace G] [MeasurableMul H]
    (hs : IsSlice j H X C) (μ : Measure H) [μ.IsMulLeftInvariant] (Ψ : Γ × G → E) {γ γ' : Γ}
    {y y' : G} (hy : y ∈ X) (hy' : y' ∈ X)
    (h : j γ * y * (j γ)⁻¹ = j γ' * y' * (j γ')⁻¹) :
    fiberIntegral j μ Ψ γ y = fiberIntegral j μ Ψ γ' y' := by
  obtain ⟨k, hk, rfl, rfl⟩ := (hs.conj_eq_conj_iff hy hy').1 h
  -- Substituting `h ↦ k h` in the integral over `H` moves the orbit of `(γ, y)` to that of
  -- `(γ * k, (j k)⁻¹ * y * j k)`.
  rw [fiberIntegral_apply, fiberIntegral_apply, ← integral_mul_left_eq_self _ (⟨k, hk⟩ : H)]
  congr 1
  funext h
  simp only [Subgroup.coe_mul, map_mul]
  congr 2 <;> group

omit [NormedSpace ℝ E] [Group Γ] [Group G] [MeasurableSpace H] in
/-- The projection to `Γ` of the support of a test function on `Γ × G` is compact. -/
private theorem isCompact_image_fst_support [TopologicalSpace Γ] [TopologicalSpace G]
    (Ψ : compactlySupported R (Γ × G) E) :
    IsCompact (Prod.fst '' support (Ψ : LocallyConstant (Γ × G) E)) :=
  (hasCompactSupport_iff_isCompact_support.1 (mem_compactlySupported.1 Ψ.property)).image
    continuous_fst

omit [NormedSpace ℝ E] in
/-- The integrand of the fibre integral of a test function is integrable over a closed subgroup
`H`, for continuous `j` and a measure `μ` finite on compact sets: it is continuous with compact
support. -/
theorem integrable_fiberIntegral_integrand [TopologicalSpace Γ] [TopologicalSpace G]
    [IsTopologicalGroup Γ] [IsTopologicalGroup G] [OpensMeasurableSpace H] (hj : Continuous j)
    (hH : IsClosed (H : Set Γ)) (μ : Measure H) [IsFiniteMeasureOnCompacts μ]
    (Ψ : compactlySupported R (Γ × G) E) (γ : Γ) (y : G) :
    Integrable (fun h : H => (Ψ : LocallyConstant (Γ × G) E) (γ * h, (j h)⁻¹ * y * j h)) μ := by
  let φ : LocallyConstant H E := (Ψ : LocallyConstant (Γ × G) E).comap
    ⟨fun h => (γ * h, (j h)⁻¹ * y * j h), by fun_prop⟩
  -- The support of `φ` lies in the preimage of the compact `Γ`-support of `Ψ` under the closed
  -- embedding `h ↦ γ * h`.
  have hemb : IsClosedEmbedding fun h : H => γ * (h : Γ) :=
    (Homeomorph.mulLeft γ).isClosedEmbedding.comp hH.isClosedEmbedding_subtypeVal
  have hφ : HasCompactSupport φ := by
    rw [hasCompactSupport_iff_isCompact_support]
    exact (hemb.isCompact_preimage (isCompact_image_fst_support Ψ)).of_isClosed_subset
      φ.isClopen_support.isClosed fun h hh => ⟨_, hh, rfl⟩
  exact (φ.continuous.integrable_of_hasCompactSupport hφ).congr
    (.of_forall fun h => coe_comap_apply _ _ h)

end FiberIntegral

section Existence

variable [TopologicalSpace Γ] [TopologicalSpace G] [IsTopologicalGroup Γ] [IsTopologicalGroup G]
  [MeasurableSpace H]

omit [NormedSpace ℝ E] [MeasurableSpace H] in
/-- A test function `Ψ` on `Γ × G` is invariant under left translation of the first variable by
the conjugates `γ * u * γ⁻¹` of all `u` near `1`. -/
private theorem eventually_forall_conj_mul_eq (Ψ : compactlySupported R (Γ × G) E) (γ : Γ) :
    ∀ᶠ u in 𝓝 (1 : Γ), ∀ a z, (Ψ : LocallyConstant (Γ × G) E) (γ * u * γ⁻¹ * a, z) =
      (Ψ : LocallyConstant (Γ × G) E) (a, z) := by
  set ψ := (Ψ : LocallyConstant (Γ × G) E)
  have hψc : HasCompactSupport ψ := mem_compactlySupported.1 Ψ.property
  -- Left translation invariance of `ψ` is right translation invariance of `p ↦ ψ p⁻¹`.
  have hS := isOpen_rightTranslationStabilizer_of_hasCompactSupport
    (ψ.isLocallyConstant.comp_continuous continuous_inv) (hψc.comp_homeomorph (.inv _))
  have ht : Tendsto (fun u : Γ => (((γ * u * γ⁻¹)⁻¹, 1) : Γ × G)) (𝓝 1) (𝓝 1) :=
    (by fun_prop : Continuous fun u : Γ => (((γ * u * γ⁻¹)⁻¹, 1) : Γ × G)).tendsto' 1 1
      (by ext <;> simp)
  filter_upwards [ht (hS.mem_nhds (one_mem _))] with u hu a z
  simpa using mem_rightTranslationStabilizer.1 hu (a, z)⁻¹

omit [NormedSpace ℝ E] [MeasurableSpace H] in
/-- A test function `Ψ` on `Γ × G` is invariant under right translation of the second variable by
the conjugates `(j l)⁻¹ * w * j l` of all `w` near `1`, uniformly for `l` in a compact set. -/
private theorem eventually_forall_mul_conj_eq (hj : Continuous j)
    (Ψ : compactlySupported R (Γ × G) E) {K : Set Γ} (hK : IsCompact K) :
    ∀ᶠ w in 𝓝 (1 : G), ∀ l ∈ K, ∀ a z,
      (Ψ : LocallyConstant (Γ × G) E) (a, z * ((j l)⁻¹ * w * j l)) =
        (Ψ : LocallyConstant (Γ × G) E) (a, z) := by
  set ψ := (Ψ : LocallyConstant (Γ × G) E)
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
private theorem fiberIntegral_mul_eq (μ : Measure H) (Ψ : compactlySupported R (Γ × G) E)
    {γ u : Γ} {x y : G}
    (hu : ∀ a z, (Ψ : LocallyConstant (Γ × G) E) (γ * u * γ⁻¹ * a, z) =
      (Ψ : LocallyConstant (Γ × G) E) (a, z))
    (hx : ∀ l ∈ (γ⁻¹ * ·) '' (Prod.fst '' support (Ψ : LocallyConstant (Γ × G) E)), ∀ a z,
      (Ψ : LocallyConstant (Γ × G) E) (a, z * ((j l)⁻¹ * (y⁻¹ * x) * j l)) =
        (Ψ : LocallyConstant (Γ × G) E) (a, z)) :
    fiberIntegral j μ (Ψ : LocallyConstant (Γ × G) E) (γ * u) x =
      fiberIntegral j μ (Ψ : LocallyConstant (Γ × G) E) γ y := by
  set ψ := (Ψ : LocallyConstant (Γ × G) E)
  simp only [fiberIntegral_apply]
  congr 1
  funext h
  -- `γ * u * h` is the left translate of `γ * h` by `γ * u * γ⁻¹`.
  have hγuh : γ * u * h = γ * u * γ⁻¹ * (γ * h) := by group
  rw [hγuh, hu]
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
    (hj : Continuous j) (μ : Measure H) (Ψ : compactlySupported R (Γ × G) E) (γ : Γ) {y : G}
    (hy : y ∈ X) :
    ∀ᶠ c in 𝓝[C] (j γ * y * (j γ)⁻¹), ∃ γ', ∃ y' ∈ X, j γ' * y' * (j γ')⁻¹ = c ∧
      fiberIntegral j μ (Ψ : LocallyConstant (Γ × G) E) γ' y' =
        fiberIntegral j μ (Ψ : LocallyConstant (Γ × G) E) γ y := by
  have hQ : IsCompact ((γ⁻¹ * ·) '' (Prod.fst '' support (Ψ : LocallyConstant (Γ × G) E))) :=
    (isCompact_image_fst_support Ψ).image (continuous_const_mul _)
  -- Points of `C` near `y` are `j u * x * (j u)⁻¹` with `u` near `1` and `y⁻¹ * x` near `1`.
  have hx : Tendsto (fun p : Γ × G => y⁻¹ * ((j p.1)⁻¹ * p.2 * j p.1)) (𝓝 (1, y)) (𝓝 1) :=
    (by fun_prop : Continuous fun p : Γ × G => y⁻¹ * ((j p.1)⁻¹ * p.2 * j p.1)).tendsto' _ _
      (by simp)
  have hx' := hx.eventually (eventually_forall_mul_conj_eq hj Ψ hQ)
  rw [nhds_prod_eq] at hx'
  obtain ⟨pa, hpa, pb, hpb, hpab⟩ := eventually_prod_iff.1 hx'
  have hy' : ∀ᶠ c in 𝓝[C] y, ∃ γ', ∃ y' ∈ X, j γ' * y' * (j γ')⁻¹ = j γ * c * (j γ)⁻¹ ∧
      fiberIntegral j μ (Ψ : LocallyConstant (Γ × G) E) γ' y' =
        fiberIntegral j μ (Ψ : LocallyConstant (Γ × G) E) γ y := by
    filter_upwards [hs.eventually_exists_conj y hy _ (hpa.and (eventually_forall_conj_mul_eq Ψ γ)),
      nhdsWithin_le_nhds hpb] with c ⟨u, ⟨hua, huV⟩, x, hx, hc⟩ hcb
    refine ⟨γ * u, x, hx, by rw [← hc, map_mul]; group, fiberIntegral_mul_eq μ Ψ huV ?_⟩
    have hxy := hpab hua hcb
    -- Conjugating `c = j u * x * (j u)⁻¹` back by `j u` recovers `x`.
    have hcx : (j u)⁻¹ * c * j u = x := by
      rw [← hc]
      group
    rwa [hcx] at hxy
  -- Transport from `y` to `j γ * y * (j γ)⁻¹` by conjugation with `(j γ)⁻¹`.
  have ht : Tendsto (fun c => (j γ)⁻¹ * c * j γ) (𝓝[C] (j γ * y * (j γ)⁻¹)) (𝓝[C] y) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, eventually_mem_nhdsWithin.mono fun c hc => ?_⟩
    · refine Tendsto.mono_left ?_ nhdsWithin_le_nhds
      exact (by fun_prop : Continuous fun c => (j γ)⁻¹ * c * j γ).tendsto' _ _ (by group)
    · simpa using hs.conj_mem_of_mem γ⁻¹ hc
  filter_upwards [ht.eventually hy'] with c hc
  simpa [mul_assoc] using hc

/-- **The fibre integral of a test function is the restriction of a test function.** For a slice
`X ⊆ C` in a Hausdorff, locally compact, totally disconnected group `G`, a left invariant measure
`μ` on `H` and a test function `Ψ` on `Γ × G`, there is a test function `f` on `G` with
`f (j γ * y * (j γ)⁻¹)` equal to the fibre integral of `Ψ` at `(γ, y)` for all `γ` and all
`y ∈ X`. -/
theorem IsSlice.exists_eq_fiberIntegral [T2Space G] [WeaklyLocallyCompactSpace G]
    [TotallyDisconnectedSpace G] [MeasurableMul H] (hs : IsSlice j H X C) (hj : Continuous j)
    (μ : Measure H) [μ.IsMulLeftInvariant] (Ψ : compactlySupported R (Γ × G) E) :
    ∃ f : compactlySupported R G E, ∀ γ, ∀ y ∈ X,
      (f : LocallyConstant G E) (j γ * y * (j γ)⁻¹) =
        fiberIntegral j μ (Ψ : LocallyConstant (Γ × G) E) γ y := by
  set ψ := (Ψ : LocallyConstant (Γ × G) E)
  -- Choose a point of `Γ × X` above every point of `C`; the value there does not depend on it.
  have hrep : ∀ c : C, ∃ γ, ∃ y ∈ X, j γ * y * (j γ)⁻¹ = c := fun c => (hs.mem_iff c).1 c.property
  choose g x hx hgx using hrep
  set F : C → E := fun c => fiberIntegral j μ ψ (g c) (x c) with hFdef
  have hF : ∀ c : C, ∀ γ, ∀ y ∈ X, j γ * y * (j γ)⁻¹ = c →
      F c = fiberIntegral j μ ψ γ y :=
    fun c γ y hy hc => hs.fiberIntegral_eq μ ψ (hx c) hy ((hgx c).trans hc.symm)
  have hlc : IsLocallyConstant F := by
    refine (IsLocallyConstant.iff_eventually_eq F).2 fun c => ?_
    have ht : Tendsto ((↑) : C → G) (𝓝 c) (𝓝[C] (c : G)) :=
      tendsto_nhdsWithin_iff.2 ⟨continuous_subtypeVal.tendsto c, .of_forall fun c' => c'.property⟩
    have hev := hs.eventually_exists_fiberIntegral_eq hj μ Ψ (g c) (hx c)
    rw [hgx c] at hev
    filter_upwards [ht.eventually hev] with c' ⟨γ', y', hy', hc', hval⟩
    rw [hF c' γ' y' hy' hc', hval]
  -- `F` vanishes off the preimage of the compact image of `support Ψ` under conjugation.
  have hK : IsCompact (((↑) : C → G) ⁻¹'
      ((fun p : Γ × G => j p.1 * p.2 * (j p.1)⁻¹) '' support ψ)) :=
    hs.isClosed.isClosedEmbedding_subtypeVal.isCompact_preimage
      ((hasCompactSupport_iff_isCompact_support.1 (mem_compactlySupported.1 Ψ.property)).image
        (by fun_prop))
  have hcs : HasCompactSupport F := by
    refine HasCompactSupport.intro hK fun c hc => ?_
    by_contra hne
    simp only [hFdef, fiberIntegral_apply] at hne
    obtain ⟨h, hh⟩ := exists_ne_zero_of_integral_ne_zero hne
    refine hc ⟨(g c * h, (j h)⁻¹ * x c * j h), hh, ?_⟩
    rw [← hgx c]
    simp only [map_mul]
    group
  obtain ⟨f, hf⟩ := compactlySupported.restrict_surjective (R := R) (M := E) hs.isClosed
    ⟨⟨F, hlc⟩, mem_compactlySupported.2 hcs⟩
  refine ⟨f, fun γ y hy => ?_⟩
  have hfc := congrArg (fun F : compactlySupported R C E =>
    (F : LocallyConstant C E) ⟨_, hs.conj_mem γ hy⟩) hf
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
    ∃ (U : OpenSubgroup Γ) (T : Finset (Γ ⧸ U.toSubgroup)),
      (∀ u ∈ U, ∀ a z, (Ψ : LocallyConstant (Γ × G) ℂ) (a * u, z) =
        (Ψ : LocallyConstant (Γ × G) ℂ) (a, z)) ∧
      ∀ a z, (Ψ : LocallyConstant (Γ × G) ℂ) (a, z) ≠ 0 → (a : Γ ⧸ U.toSubgroup) ∈ T := by
  set ψ := (Ψ : LocallyConstant (Γ × G) ℂ)
  have hinl' : ⇑(MonoidHom.inl Γ G) = fun u => (u, 1) := funext fun u => by simp
  have hinl : Continuous (MonoidHom.inl Γ G) := by
    rw [hinl']
    fun_prop
  let U : OpenSubgroup Γ :=
    { toSubgroup := (rightTranslationStabilizer ψ).comap (MonoidHom.inl Γ G)
      isOpen' := (isOpen_rightTranslationStabilizer_of_hasCompactSupport ψ.isLocallyConstant
        (mem_compactlySupported.1 Ψ.property)).preimage hinl }
  -- The quotient by the open subgroup `U` is discrete, so the image of the compact first
  -- projection of the support in it is finite.
  have := QuotientGroup.discreteTopology U.isOpen
  have hfin := ((isCompact_image_fst_support Ψ).image
    (QuotientGroup.continuous_mk (N := U.toSubgroup))).finite_of_discrete
  refine ⟨U, hfin.toFinset, fun u hu a z => ?_, fun a z ha =>
    hfin.mem_toFinset.2 ⟨a, ⟨(a, z), ha, rfl⟩, rfl⟩⟩
  simpa using mem_rightTranslationStabilizer.1 (Subgroup.mem_comap.1 hu) (a, z)

variable {U : OpenSubgroup Γ} {T : Finset (Γ ⧸ U.toSubgroup)}

open scoped Classical in
/-- The piece `(γ, y) ↦ 1_U (γ) Ψ (r * γ, y)` of a test function `Ψ` on `Γ × G`, for an open
subgroup `U` and a coset representative `r`, is a test function. -/
private theorem exists_eq_ite_mem (Ψ : compactlySupported ℂ (Γ × G) ℂ) :
    ∃ Φ : Γ ⧸ U.toSubgroup → compactlySupported ℂ (Γ × G) ℂ, ∀ q a z,
      (Φ q : LocallyConstant (Γ × G) ℂ) (a, z) =
        if a ∈ U then (Ψ : LocallyConstant (Γ × G) ℂ) (q.out * a, z) else 0 := by
  classical
  have hUcl : IsClopen ((U : Set Γ) ×ˢ (univ : Set G)) :=
    ⟨U.isClosed.prod isClosed_univ, U.isOpen.prod isOpen_univ⟩
  -- The translate `(γ, y) ↦ Ψ (r * γ, y)` is a test function, and so is its restriction to the
  -- clopen set `U × G`.
  set τ : Γ ⧸ U.toSubgroup → compactlySupported ℂ (Γ × G) ℂ := fun q =>
    compactlySupportedRep ℂ (Γ × G) (Γ × G) ℂ (q.out⁻¹, 1) Ψ
  exact ⟨fun q => ⟨(τ q : LocallyConstant (Γ × G) ℂ).indicator hUcl,
    indicator_mem_compactlySupported_of_mem (τ q).property hUcl⟩,
    fun q a z => by simp [τ, LocallyConstant.indicator_apply, Set.indicator_apply]⟩

open scoped Classical in
/-- The fibre integral of `Ψ` is the sum of the fibre integrals of the pieces `1_U (γ) Ψ (r γ, y)`
at `(r⁻¹ γ, y)`, over the representatives `r` of the cosets in `T`. -/
private theorem fiberIntegral_eq_sum [MeasurableSpace H] [OpensMeasurableSpace H]
    (hj : Continuous j) (hH : IsClosed (H : Set Γ)) (μ : Measure H) [IsFiniteMeasureOnCompacts μ]
    (Ψ : compactlySupported ℂ (Γ × G) ℂ)
    (hT : ∀ a z, (Ψ : LocallyConstant (Γ × G) ℂ) (a, z) ≠ 0 → (a : Γ ⧸ U.toSubgroup) ∈ T)
    (Φ : Γ ⧸ U.toSubgroup → compactlySupported ℂ (Γ × G) ℂ)
    (hΦ : ∀ q a z, (Φ q : LocallyConstant (Γ × G) ℂ) (a, z) =
      if a ∈ U then (Ψ : LocallyConstant (Γ × G) ℂ) (q.out * a, z) else 0) (γ : Γ) (y : G) :
    fiberIntegral j μ Ψ γ y =
      ∑ q ∈ T, fiberIntegral j μ (Φ q : LocallyConstant (Γ × G) ℂ) (q.out⁻¹ * γ) y := by
  simp only [fiberIntegral_apply]
  rw [← integral_finsetSum _ fun q _ => integrable_fiberIntegral_integrand hj hH μ (Φ q) _ y]
  congr 1
  funext h
  rw [← QuotientGroup.sum_ite_out_inv_mul_mem (fun a => hT a ((j h)⁻¹ * y * j h))]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [hΦ]
  simp only [OpenSubgroup.mem_toSubgroup, mul_assoc, mul_inv_cancel_left]

/-- **Descent of invariant distributions to a slice.** Let `X ⊆ C` be a slice for the conjugation
action of `Γ` on a Hausdorff, locally compact, totally disconnected group `G` through a continuous
`j`, with closed stabiliser `H` carrying a left invariant measure `μ` finite on compact sets, and
let `ν` be a Haar measure on `Γ`.
Let `I` be a linear form on the test functions on `G` that is invariant under conjugation by
`j Γ` and vanishes on the test functions vanishing on `C`. If a test function `Ψ` on `Γ × G`
satisfies `∫ γ, Ψ (γ, y) ∂ν = 0` for every `y ∈ X`, then `I f = 0` for every test function `f`
whose value at `j γ * y * (j γ)⁻¹` is the fibre integral of `Ψ` at `(γ, y)` for all `γ` and
`y ∈ X`. Such an `f` exists by `TauCeti.IsSlice.exists_eq_fiberIntegral`. -/
theorem IsSlice.map_eq_zero_of_integral_eq_zero_of_eq_fiberIntegral [T2Space G]
    [WeaklyLocallyCompactSpace G] [TotallyDisconnectedSpace G] [MeasurableSpace Γ]
    [OpensMeasurableSpace Γ] [MeasurableMul Γ] [MeasurableSpace H] [OpensMeasurableSpace H]
    [MeasurableMul H] (hs : IsSlice j H X C) (hj : Continuous j)
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
  obtain ⟨U, T, hUψ, hT⟩ := exists_openSubgroup_finset Ψ
  have hsum (y : G) (hy : y ∈ X) : ∑ q ∈ T, (Ψ : LocallyConstant (Γ × G) ℂ) (q.out, y) = 0 :=
    OpenSubgroup.sum_eq_zero_of_integral_eq_zero ν U
      ((mem_compactlySupported.1 Ψ.property).comp_prodMk_left y) (fun a u hu => hUψ u hu a y)
      (fun a => hT a y) (hΨ y hy)
  obtain ⟨Φ, hΦ⟩ := exists_eq_ite_mem (U := U) Ψ
  choose g hg using fun q => hs.exists_eq_fiberIntegral hj μ (Φ q)
  set R : Γ ⧸ U.toSubgroup → compactlySupported ℂ G ℂ := fun q =>
    compactlySupportedRep ℂ (ConjAct G) G ℂ (ConjAct.toConjAct (j q.out)) (g q)
  have hsum_apply (F : Γ ⧸ U.toSubgroup → compactlySupported ℂ G ℂ) (x : G) :
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
    simp only [hsum_apply, hg _ γ y hy]
    rw [← fiberIntegral_finsetSum μ T fun q _ =>
      integrable_fiberIntegral_integrand hj hH μ (Φ q) _ y, fiberIntegral_apply]
    refine integral_eq_zero_of_ae (ae_of_all _ fun h => ?_)
    simp only [Finset.sum_apply, hΦ, Pi.zero_apply]
    split_ifs with hγh
    · have hX := hs.inv_conj_mem h.property hy
      rw [← hsum _ hX]
      exact Finset.sum_congr rfl fun q _ => hUψ _ hγh _ _
    · simp
  rw [h₁]
  simpa [R, hI, ← map_sum] using h₂

end Descent

end TauCeti

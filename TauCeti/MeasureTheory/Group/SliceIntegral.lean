/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.MeasureTheory.Group.Integral
public import TauCeti.Topology.Algebra.Group.Slice
public import TauCeti.Topology.LocallyConstant.CompactSupport.OpenClosed
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Tactic.Group
import TauCeti.Topology.Algebra.Group.Basic
import TauCeti.Topology.Algebra.Group.LocallyConstant

/-!
# Integration along the fibres of a slice

Let `Γ` act on `G` by conjugation through `j : Γ →* G`, and let `X ⊆ C` be a slice for this action
with stabiliser `H ⊆ Γ` (`TauCeti.IsSlice j H X C`), so that the fibres of
`(γ, y) ↦ j γ * y * (j γ)⁻¹` from `Γ × X` onto `C` are the `H`-orbits
`(γ * h, (j h)⁻¹ * y * j h)`. For a function `Ψ` on `Γ × G` with values in a real normed space `E`
and a measure `μ` on `H`, the *fibre integral* (`TauCeti.fiberIntegral j μ Ψ γ y`) integrates `Ψ`
over the `H`-orbit of `(γ, y)`.

When `μ` is left invariant, the fibre integral is constant on `H`-orbits
(`TauCeti.fiberIntegral_mul_conj`), so on `Γ × X` its value at `(γ, y)` only depends on the point
`j γ * y * (j γ)⁻¹` of `C` (`TauCeti.IsSlice.fiberIntegral_eq`). For a test function `Ψ` (a locally
constant function with compact support, `LocallyConstant.compactlySupported`) and continuous `j`,
the resulting function on `C` is a test function on `C`
(`TauCeti.IsSlice.existsUnique_eq_fiberIntegral`), hence the restriction of a test function on `G`
when `G` is Hausdorff, locally compact and totally disconnected
(`TauCeti.IsSlice.exists_eq_fiberIntegral`). This is the descended test function of
Harish-Chandra's descent of invariant distributions to a slice,
`TauCeti.IsSlice.map_eq_zero_of_integral_eq_zero_of_eq_fiberIntegral` in
`TauCeti.RepresentationTheory.Smooth.SliceDescent`.

## Main definitions

* `TauCeti.fiberIntegral j μ Ψ γ y`: the integral `∫ h, Ψ (γ * h, (j h)⁻¹ * y * j h) ∂μ` over the
  `H`-orbit of `(γ, y)`.

## Main results

* `TauCeti.fiberIntegral_add`, `TauCeti.fiberIntegral_smul`, `TauCeti.fiberIntegral_finsetSum`:
  linearity of the fibre integral.
* `TauCeti.fiberIntegral_mul_conj`: for left invariant `μ`, the fibre integral is constant on
  `H`-orbits.
* `TauCeti.IsSlice.fiberIntegral_eq`: for left invariant `μ`, the fibre integral is constant on the
  fibres of `(γ, y) ↦ j γ * y * (j γ)⁻¹` over `C`.
* `TauCeti.integrable_fiberIntegral_integrand`: the integrand of the fibre integral of a test
  function is integrable.
* `TauCeti.IsSlice.existsUnique_eq_fiberIntegral`: the fibre integral of a test function on
  `Γ × G` is a uniquely determined test function on `C`.
* `TauCeti.IsSlice.exists_eq_fiberIntegral`: the fibre integral of a test function on `Γ × G` is
  the restriction to `C` of a test function on `G`.

## References

* Harish-Chandra, *Harmonic analysis on reductive p-adic groups*, notes by G. van Dijk, Lecture
  Notes in Mathematics 162, Springer, 1970 (descent of invariant distributions to a slice).
* The statements adapt the declarations `New.fibreIntegral` and `New.IsSlice.exists_isImage` of the
  formal proof `[ShortProof]`, grh-lean (https://github.com/lsernau/grh-lean, Apache 2.0, Copyright
  2026 Anthropic PBC), file `src/Lib/Adelic/TraceFormula/FibreIntegral.lean`. Here the test
  functions are those of `LocallyConstant.compactlySupported`, and the proofs are written
  independently.
-/

public section

noncomputable section

open Filter Function MeasureTheory Set Topology LocallyConstant

namespace TauCeti

variable {Γ G E : Type*} [Group Γ] [Group G] [NormedAddCommGroup E] [NormedSpace ℝ E]
  {R : Type*} [Semiring R] [Module R E] {j : Γ →* G} {H : Subgroup Γ} {X C : Set G}

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
theorem fiberIntegral_smul {𝕜 : Type*} [NormedDivisionRing 𝕜] [Module 𝕜 E] [NormSMulClass 𝕜 E]
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

/-- **Orbit invariance of the fibre integral.** For a left invariant measure `μ` on `H`, the fibre
integral takes the same value at `(γ * k, (j k)⁻¹ * y * j k)` as at `(γ, y)`, for every `k : H`. -/
theorem fiberIntegral_mul_conj [MeasurableMul H] (μ : Measure H) [μ.IsMulLeftInvariant]
    (Ψ : Γ × G → E) (γ : Γ) (y : G) (k : H) :
    fiberIntegral j μ Ψ (γ * k) ((j k)⁻¹ * y * j k) = fiberIntegral j μ Ψ γ y := by
  symm
  -- Substituting `h ↦ k h` in the integral over `H` moves the orbit of `(γ, y)` to that of
  -- `(γ * k, (j k)⁻¹ * y * j k)`.
  rw [fiberIntegral_apply, fiberIntegral_apply, ← integral_mul_left_eq_self _ k]
  congr 1
  funext h
  simp only [Subgroup.coe_mul, map_mul]
  congr 2 <;> group

/-- **The fibre integral is constant on the fibres over `C`.** For a left invariant measure `μ` on
`H`, if two points `(γ, y)` and `(γ', y')` of `Γ × X` have the same conjugate
`j γ * y * (j γ)⁻¹ = j γ' * y' * (j γ')⁻¹`, their fibre integrals agree. -/
theorem IsSlice.fiberIntegral_eq [TopologicalSpace Γ] [TopologicalSpace G] [MeasurableMul H]
    (hs : IsSlice j H X C) (μ : Measure H) [μ.IsMulLeftInvariant] (Ψ : Γ × G → E) {γ γ' : Γ}
    {y y' : G} (hy : y ∈ X) (hy' : y' ∈ X)
    (h : j γ * y * (j γ)⁻¹ = j γ' * y' * (j γ')⁻¹) :
    fiberIntegral j μ Ψ γ y = fiberIntegral j μ Ψ γ' y' := by
  -- The two points lie in one `H`-orbit.
  obtain ⟨k, hk, rfl, rfl⟩ := (hs.conj_eq_conj_iff hy hy').1 h
  exact (fiberIntegral_mul_conj μ Ψ γ y ⟨k, hk⟩).symm

omit [NormedSpace ℝ E] in
/-- The integrand of the fibre integral of a test function is integrable over a closed subgroup
`H`, for continuous `j` and a measure `μ` finite on compact sets: it is continuous with compact
support. -/
theorem integrable_fiberIntegral_integrand [TopologicalSpace Γ] [TopologicalSpace G]
    [IsTopologicalGroup Γ] [IsTopologicalGroup G] [OpensMeasurableSpace H] (hj : Continuous j)
    (hH : IsClosed (H : Set Γ)) (μ : Measure H) [IsFiniteMeasureOnCompacts μ]
    (Ψ : compactlySupported R (Γ × G) E) (γ : Γ) (y : G) :
    Integrable (fun h : H => (Ψ : LocallyConstant (Γ × G) E) (γ * h, (j h)⁻¹ * y * j h)) μ := by
  set ψ := (Ψ : LocallyConstant (Γ × G) E)
  let φ : LocallyConstant H E := ψ.comap ⟨fun h => (γ * h, (j h)⁻¹ * y * j h), by fun_prop⟩
  have hφ_apply (h : H) : φ h = ψ (γ * h, (j h)⁻¹ * y * j h) := coe_comap_apply _ _ h
  -- The support of `φ` lies in the preimage of the compact `Γ`-support of `Ψ` under the closed
  -- embedding `h ↦ γ * h`.
  have hemb : IsClosedEmbedding fun h : H => γ * (h : Γ) :=
    (Homeomorph.mulLeft γ).isClosedEmbedding.comp hH.isClosedEmbedding_subtypeVal
  have hφ : HasCompactSupport φ := by
    rw [hasCompactSupport_iff_isCompact_support]
    exact (hemb.isCompact_preimage
      (isCompact_image_fst_support (mem_compactlySupported.1 Ψ.property))).of_isClosed_subset
      φ.isClopen_support.isClosed fun h hh =>
        ⟨(γ * h, (j h)⁻¹ * y * j h), by rwa [Function.mem_support, ← hφ_apply], rfl⟩
  exact (φ.continuous.integrable_of_hasCompactSupport hφ).congr (.of_forall hφ_apply)

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
  -- Left translations of `Ψ` by elements near `1` fix it, and `(γ * u * γ⁻¹, 1) → 1` as `u → 1`.
  have hL := eventually_forall_mul_left_eq_of_hasCompactSupport
    (Ψ : LocallyConstant (Γ × G) E).isLocallyConstant (mem_compactlySupported.1 Ψ.property)
  have ht : Tendsto (fun u : Γ => ((γ * u * γ⁻¹, 1) : Γ × G)) (𝓝 1) (𝓝 1) :=
    (by fun_prop : Continuous fun u : Γ => ((γ * u * γ⁻¹, 1) : Γ × G)).tendsto' 1 1
      (by ext <;> simp)
  filter_upwards [ht hL] with u hu a z
  simpa using hu (a, z)

omit [NormedSpace ℝ E] [MeasurableSpace H] [IsTopologicalGroup Γ] in
/-- A test function `Ψ` on `Γ × G` is invariant under right translation of the second variable by
the conjugates `(j l)⁻¹ * w * j l` of all `w` near `1`, uniformly for `l` in a compact set. -/
private theorem eventually_forall_mul_conj_eq (hj : Continuous j)
    (Ψ : compactlySupported R (Γ × G) E) {K : Set Γ} (hK : IsCompact K) :
    ∀ᶠ w in 𝓝 (1 : G), ∀ l ∈ K, ∀ a z,
      (Ψ : LocallyConstant (Γ × G) E) (a, z * ((j l)⁻¹ * w * j l)) =
        (Ψ : LocallyConstant (Γ × G) E) (a, z) := by
  -- Right translations of the second variable by elements of some `V ∈ 𝓝 1` fix `Ψ`.
  have hV : {v : G | ∀ p : Γ × G, (Ψ : LocallyConstant (Γ × G) E) (p.1, p.2 * v) =
      (Ψ : LocallyConstant (Γ × G) E) p} ∈ 𝓝 (1 : G) :=
    eventually_forall_apply_act_eq_of_hasCompactSupport (act := fun p v => (p.1, p.2 * v))
      (Ψ : LocallyConstant (Γ × G) E).isLocallyConstant (mem_compactlySupported.1 Ψ.property)
      (by fun_prop) (fun _ => by simp) (fun _ _ => by simp)
  -- Conjugation by the compact family `(j l)⁻¹`, `l ∈ K`, sends small elements into `V`.
  obtain ⟨W, hW, hWV⟩ := ((hK.image hj).image continuous_inv).exists_nhds_one_conj_subset hV
  filter_upwards [hW] with w hw l hl a z
  simpa using hWV _ ⟨j l, ⟨l, hl, rfl⟩, rfl⟩ w hw (a, z)

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
    (isCompact_image_fst_support (mem_compactlySupported.1 Ψ.property)).image
      (continuous_const_mul _)
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

/-- **The fibre integral of a test function is a test function on `C`.** For a slice `X ⊆ C` for
the conjugation action through a continuous homomorphism `j`, a left invariant measure `μ` on `H`
and a test function `Ψ` on `Γ × G`, there is exactly one test function `F` on `C` whose value at
`j γ * y * (j γ)⁻¹` is the fibre integral of `Ψ` at `(γ, y)`, for all `γ` and all `y ∈ X`. -/
theorem IsSlice.existsUnique_eq_fiberIntegral [MeasurableMul H]
    (hs : IsSlice j H X C) (hj : Continuous j) (μ : Measure H) [μ.IsMulLeftInvariant]
    (Ψ : compactlySupported R (Γ × G) E) :
    ∃! F : compactlySupported R C E, ∀ γ y (hy : y ∈ X),
      (F : LocallyConstant C E) ⟨j γ * y * (j γ)⁻¹, hs.conj_mem γ hy⟩ =
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
  refine ⟨⟨⟨F, hlc⟩, mem_compactlySupported.2 hcs⟩, fun γ y hy => hF _ γ y hy rfl,
    fun F' hF' => Subtype.ext <| LocallyConstant.ext fun c => ?_⟩
  -- Both test functions take the value of the fibre integral above each point of `C`.
  obtain ⟨c, hc⟩ := c
  obtain ⟨γ, y, hy, rfl⟩ := (hs.mem_iff c).1 hc
  exact (hF' γ y hy).trans (hF _ γ y hy rfl).symm

/-- **The fibre integral of a test function is the restriction of a test function.** For a slice
`X ⊆ C` in a Hausdorff, locally compact, totally disconnected group `G`, for the conjugation action
through a continuous homomorphism `j`, a left invariant measure `μ` on `H` and a test function `Ψ`
on `Γ × G`, there is a test function `f` on `G` with `f (j γ * y * (j γ)⁻¹)` equal to the fibre
integral of `Ψ` at `(γ, y)` for all `γ` and all `y ∈ X`. Its restriction to `C` is the test
function of `TauCeti.IsSlice.existsUnique_eq_fiberIntegral`. -/
theorem IsSlice.exists_eq_fiberIntegral [T2Space G] [WeaklyLocallyCompactSpace G]
    [TotallyDisconnectedSpace G] [MeasurableMul H] (hs : IsSlice j H X C) (hj : Continuous j)
    (μ : Measure H) [μ.IsMulLeftInvariant] (Ψ : compactlySupported R (Γ × G) E) :
    ∃ f : compactlySupported R G E, ∀ γ, ∀ y ∈ X,
      (f : LocallyConstant G E) (j γ * y * (j γ)⁻¹) =
        fiberIntegral j μ (Ψ : LocallyConstant (Γ × G) E) γ y := by
  obtain ⟨F, hF, -⟩ := hs.existsUnique_eq_fiberIntegral hj μ Ψ
  obtain ⟨f, rfl⟩ := compactlySupported.restrict_surjective (R := R) (M := E) hs.isClosed F
  exact ⟨f, fun γ y hy => by rw [← hF γ y hy, compactlySupported.restrict_apply]⟩

end Existence

end TauCeti

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Runge.SimpleFraction
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import TauCeti.Analysis.Complex.Pompeiu.Cutoff
import TauCeti.MeasureTheory.Integral.Bochner.Basic

/-!
# Runge's approximation theorem on plane domains

Let `K` be a compact subset of an open set `Ω ⊆ ℂ`. **Runge's theorem** says that every function
holomorphic on a neighbourhood of `K` is a uniform limit on `K` of functions holomorphic on all of
`Ω` exactly when `K` is filled in `Ω` (`TauCeti.IsFilledIn K Ω`): no connected component of
`Ω \ K` is relatively compact in `Ω`. Neither `K` nor `Ω` needs to be connected, and the
approximation holds for functions with values in any complex Banach space.

Runge's theorem is what turns local solutions into global ones on `Ω`. Along an exhaustion of `Ω`
by compact sets filled in `Ω`, solutions of a holomorphic problem (a `\bar∂` equation, or
prescribed principal parts as in the Mittag-Leffler theorem) on a neighbourhood of each compact set
are corrected by global holomorphic approximants with summable errors, and the corrected solutions
converge on all of `Ω`. Such exhaustions come from `IsOpen.exists_isFilledIn_compact_exhaustion`;
filledness of a single closed set in the whole plane is the equality `filledHull K = K` of
`TauCeti.isFilledIn_univ_iff`.

## The argument

Approximation follows from the simple-fraction case
`TauCeti.IsFilledIn.exists_differentiableOn_norm_inv_sub_lt`. By the Cauchy–Green formula with a
cutoff (`DifferentiableOn.exists_eqOn_cauchyTransform`), on `K` the function `f` is

`f ξ = π⁻¹ ∫ (ξ - z)⁻¹ • h z dz`

for a continuous compactly supported `h` whose closed support misses `K`: an integral of simple
fractions `ξ ↦ (ξ - z)⁻¹` with poles `z ∉ K`. Rather than discretising it by Riemann sums, we read
it as a Bochner integral of a continuous compactly supported function with values in the Banach
space `C(K, F)`. Every value lies in the closure of the restrictions to `K` of functions
holomorphic on `Ω`, by the simple-fraction case, and this closure is a closed subspace, so it
contains the integral (`Submodule.integral_mem`). The converse is
`TauCeti.isFilledIn_of_forall_exists_differentiableOn_norm_inv_sub_lt`.

## Main results

* `TauCeti.IsFilledIn.exists_differentiableOn_norm_sub_lt`: **Runge's theorem.** If `K` is
  compact and filled in the open set `Ω`, every function holomorphic on a neighbourhood of `K`,
  with values in a complex Banach space, is uniformly approximable on `K` by functions holomorphic
  on `Ω`.
* `TauCeti.isFilledIn_iff_forall_exists_differentiableOn_norm_sub_lt`: the resulting
  characterisation of compact sets filled in `Ω` by approximation.

## References

* A. Rainer, *Advanced Complex Analysis*, Theorems 10.3 and 11.1.
* W. Rudin, *Real and Complex Analysis*, 3rd ed., Theorem 13.9.
-/

public section

open Set MeasureTheory

namespace TauCeti

variable {K Ω : Set ℂ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]

variable (K Ω F) in
/-- The closure, inside `C(K, F)`, of the restrictions to `K` of the `F`-valued functions
holomorphic on `Ω`. For compact `K` the compact-open topology on `C(K, F)` is the topology of
uniform convergence, so this is the uniform closure. -/
private noncomputable def rungeClosure : Submodule ℂ C(K, F) :=
  Submodule.topologicalClosure
    { carrier := {φ | ∃ g : ℂ → F, DifferentiableOn ℂ g Ω ∧ ∀ z : K, g z = φ z}
      add_mem' := fun ⟨g₁, hg₁, h₁⟩ ⟨g₂, hg₂, h₂⟩ ↦
        ⟨g₁ + g₂, hg₁.add hg₂, fun z ↦ by simp [h₁, h₂]⟩
      zero_mem' := ⟨0, differentiableOn_const 0, fun _ ↦ by simp⟩
      smul_mem' := fun c _ ⟨g, hg, h⟩ ↦ ⟨c • g, hg.const_smul c, fun z ↦ by simp [h]⟩ }

/-- A continuous function on a compact `K ⊆ Ω` lies in `rungeClosure` exactly when it is a
uniform limit on `K` of functions holomorphic on `Ω`. -/
private theorem mem_rungeClosure_iff [CompactSpace K] (hKΩ : K ⊆ Ω) (φ : C(K, F)) :
    φ ∈ rungeClosure K Ω F ↔
      ∀ ε > 0, ∃ g : ℂ → F, DifferentiableOn ℂ g Ω ∧ ∀ z : K, ‖φ z - g z‖ < ε := by
  rw [rungeClosure, ← SetLike.mem_coe, Submodule.topologicalClosure_coe, Metric.mem_closure_iff]
  constructor
  · intro hφ ε hε
    obtain ⟨ψ, ⟨g, hg, hgψ⟩, hdist⟩ := hφ ε hε
    refine ⟨g, hg, fun z ↦ ?_⟩
    rw [hgψ z, ← ContinuousMap.sub_apply]
    exact ((φ - ψ).norm_coe_le_norm z).trans_lt (by rwa [dist_eq_norm] at hdist)
  · intro hφ ε hε
    obtain ⟨g, hg, hgK⟩ := hφ (ε / 2) (half_pos hε)
    refine ⟨⟨fun z : K ↦ g z, (hg.continuousOn.mono hKΩ).comp_continuous continuous_subtype_val
      fun z ↦ z.property⟩, ⟨g, hg, fun _ ↦ rfl⟩, lt_of_le_of_lt ?_ (half_lt_self hε)⟩
    rw [ContinuousMap.dist_le (half_pos hε).le]
    intro z
    rw [dist_eq_norm]
    simpa using (hgK z).le

/-- **Runge's theorem.** Let `K` be a compact subset of an open set `Ω ⊆ ℂ` that is filled in
`Ω`: no connected component of `Ω \ K` is relatively compact in `Ω`. Then every function with
values in a complex Banach space, holomorphic on an open neighbourhood `U` of `K`, is a uniform
limit on `K` of functions holomorphic on `Ω`. -/
theorem IsFilledIn.exists_differentiableOn_norm_sub_lt [CompleteSpace F] (hfill : IsFilledIn K Ω)
    (hΩ : IsOpen Ω) (hK : IsCompact K) (hKΩ : K ⊆ Ω) {U : Set ℂ} (hU : IsOpen U)
    (hKU : K ⊆ U) {f : ℂ → F} (hf : DifferentiableOn ℂ f U) {ε : ℝ} (hε : 0 < ε) :
    ∃ g : ℂ → F, DifferentiableOn ℂ g Ω ∧ ∀ z ∈ K, ‖f z - g z‖ < ε := by
  obtain ⟨h, hh, hhc, hhU, hfh⟩ := hf.exists_eqOn_cauchyTransform hU hK hKU
  have hhK : Disjoint (tsupport h) K := disjoint_left.2 fun z hz ↦ (hhU hz).2
  -- Read `f` on `K` as `π⁻¹ ∫ G`, a `C(K, F)`-valued integral of simple fractions.
  have : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let G : C(ℂ, C(K, F)) := ContinuousMap.curry ⟨_, hh.inv_sub_smul_of_disjoint_tsupport hhK⟩
  have hG_apply (z : ℂ) (ξ : K) : G z ξ = ((ξ : ℂ) - z)⁻¹ • h z := rfl
  have hGc : HasCompactSupport G := hhc.mono fun z hz hhz ↦
    hz (ContinuousMap.ext fun ξ ↦ by simp [hG_apply, hhz])
  have hfK : (⟨fun ξ : K ↦ f ξ, hf.continuousOn.comp_continuous continuous_subtype_val
      fun ξ ↦ hKU ξ.property⟩ : C(K, F)) = (Real.pi : ℂ)⁻¹ • ∫ z, G z := by
    ext ξ
    rw [ContinuousMap.smul_apply, ContinuousMap.integral_apply
      ((map_continuous G).integrable_of_hasCompactSupport hGc), ContinuousMap.coe_mk,
      ← hfh ξ.property, cauchyTransform_apply]
    simp [hG_apply]
  -- Each value of `G` is a simple fraction with pole off `K` times a constant, so it lies in the
  -- Runge closure, which is a closed subspace and hence contains the integral.
  have hGA (z : ℂ) : G z ∈ rungeClosure K Ω F := by
    by_cases hz : z ∈ tsupport h
    swap
    · have hG0 : G z = 0 :=
        ContinuousMap.ext fun ξ ↦ by simp [hG_apply, image_eq_zero_of_notMem_tsupport hz]
      rw [hG0]
      exact zero_mem _
    -- Scale uniform approximations of the simple fraction with pole `z ∉ K` by `h z`.
    have hpos : 0 < ‖h z‖ + 1 := by positivity
    refine (mem_rungeClosure_iff hKΩ _).2 fun δ hδ ↦ ?_
    obtain ⟨g, hg, hgK⟩ := hfill.exists_differentiableOn_norm_inv_sub_lt hΩ hK hKΩ (hhU hz).2
      (div_pos hδ hpos)
    refine ⟨fun ξ ↦ g ξ • h z, hg.smul_const (h z), fun ξ ↦ ?_⟩
    simp only [hG_apply, ← sub_smul, norm_smul]
    calc ‖((ξ : ℂ) - z)⁻¹ - g ξ‖ * ‖h z‖ ≤ ‖((ξ : ℂ) - z)⁻¹ - g ξ‖ * (‖h z‖ + 1) := by
          gcongr
          exact le_add_of_nonneg_right zero_le_one
      _ < δ / (‖h z‖ + 1) * (‖h z‖ + 1) := by
          gcongr
          exact hgK ξ ξ.property
      _ = δ := div_mul_cancel₀ δ hpos.ne'
  have hmem := Submodule.smul_mem _ (Real.pi : ℂ)⁻¹
    (Submodule.integral_mem (μ := volume) (A := rungeClosure K Ω F)
      (Submodule.isClosed_topologicalClosure _) (.of_forall hGA))
  rw [← hfK] at hmem
  obtain ⟨g, hg, hgK⟩ := (mem_rungeClosure_iff hKΩ _).1 hmem ε hε
  exact ⟨g, hg, fun z hz ↦ hgK ⟨z, hz⟩⟩

/-- **Runge's theorem, characterisation.** A compact subset `K` of an open set `Ω ⊆ ℂ` is filled in
`Ω` if and only if every function holomorphic on an open neighbourhood of `K` is a uniform limit on
`K` of functions holomorphic on `Ω`. -/
theorem isFilledIn_iff_forall_exists_differentiableOn_norm_sub_lt (hΩ : IsOpen Ω)
    (hK : IsCompact K) (hKΩ : K ⊆ Ω) :
    IsFilledIn K Ω ↔ ∀ U : Set ℂ, IsOpen U → K ⊆ U → ∀ f : ℂ → ℂ, DifferentiableOn ℂ f U →
      ∀ ε > 0, ∃ g : ℂ → ℂ, DifferentiableOn ℂ g Ω ∧ ∀ z ∈ K, ‖f z - g z‖ < ε := by
  refine ⟨fun hfill U hU hKU f hf ε hε ↦
    hfill.exists_differentiableOn_norm_sub_lt hΩ hK hKΩ hU hKU hf hε, fun h ↦ ?_⟩
  refine isFilledIn_of_forall_exists_differentiableOn_norm_inv_sub_lt hΩ hK.isClosed fun a ha ↦
    h {a}ᶜ isOpen_compl_singleton (fun z hz hza ↦ ha.2 (hza ▸ hz)) _ ?_
  exact ((differentiableOn_id.sub_const a).inv fun z hz ↦ sub_ne_zero.2 hz)

end TauCeti

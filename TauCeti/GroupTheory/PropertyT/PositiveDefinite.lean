/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.PropertyT.KazhdanPair
public import TauCeti.RepresentationTheory.Continuous.Unitary.PositiveDefinite
import TauCeti.Analysis.InnerProductSpace.UnitVector
import TauCeti.Analysis.RCLike.Basic
import TauCeti.RepresentationTheory.Continuous.Unitary.OrbitConvexHull

/-!
# Relative property (T) through positive-definite functions

A subgroup `Λ` of a discrete group `Γ` has relative property (T) when every net of positive-definite
functions `φᵢ : Γ → ℂ` with `φᵢ 1 = 1` converging pointwise to `1` converges uniformly on `Λ`. In
uniform form: for every `ε > 0` there are a finite set `F ⊆ Γ` and a `δ > 0` such that every such
`φ` with `‖φ g - 1‖ < δ` for `g ∈ F` satisfies `‖φ h - 1‖ < ε` for every `h ∈ Λ`.

Either condition implies relative property (T), for every subgroup and in every universe of
representations. A unit vector `ξ` moved little by a finite set gives the coefficient
`g ↦ ⟪ξ, ρ g ξ⟫`, a normalized positive-definite function close to `1` on that set. If it is
within `ε < 1` of `1` on `Λ`, its real part is at least `1 - ε` there, and the element of minimal
norm in the closed convex hull of the `Λ`-orbit of `ξ` is a nonzero `Λ`-invariant vector.

Conversely, when `Λ` is normal, relative property (T) gives the uniform form. The GNS vector of
a normalized positive-definite function close to `1` on a finite set is a unit vector moved little
by that set, so by the quantitative Kazhdan-pair theorem it lies close to a `Λ`-invariant vector,
and the coefficient of a vector close to a `Λ`-invariant one is close to `1` on `Λ`. The converse
for subgroups that are not normal is a theorem of Jolissaint and is not proved here.

Relative property (T) is used here with Hilbert spaces in the universe of the group, which
contains the GNS spaces of positive-definite functions on it.

## Main statements

* `Subgroup.RelativePropertyT.exists_forall_norm_sub_one_lt`: for a normal subgroup, relative
  property (T) gives the uniform form.
* `Subgroup.RelativePropertyT.tendstoUniformlyOn`: for a normal subgroup with relative property
  (T), normalized positive-definite functions converging pointwise to `1` converge uniformly on
  the subgroup.
* `Subgroup.relativePropertyT_of_exists_forall_norm_sub_one_lt` and
  `Subgroup.relativePropertyT_of_forall_tendstoUniformlyOn`: each form implies relative
  property (T).
* `Subgroup.relativePropertyT_iff_forall_exists_forall_norm_sub_one_lt` and
  `Subgroup.relativePropertyT_iff_forall_tendstoUniformlyOn`: the equivalences for normal
  subgroups.

## References

* C. Anantharaman and S. Popa, *An Introduction to II₁ Factors*, Proposition 14.1.2.
* P. Jolissaint, *On property (T) for pairs of topological groups*, Enseign. Math. (2) 51 (2005),
  31–45.
-/

public section

open Filter Topology InnerProductSpace
open scoped ComplexOrder

namespace Subgroup

universe u v

open ContRepresentation

variable {Γ : Type v} [Group Γ] {Λ : Subgroup Γ}

/-- **Relative property (T) by positive-definite functions, uniform form.** If a normal subgroup
`Λ` has relative property (T), then for every `ε > 0` there are a finite set `F` and a `δ > 0` such
that every positive-definite function `φ` with `φ 1 = 1` and `‖φ g - 1‖ < δ` for `g ∈ F` satisfies
`‖φ h - 1‖ < ε` for every `h ∈ Λ`. -/
theorem RelativePropertyT.exists_forall_norm_sub_one_lt [Λ.Normal]
    (hΛ : Λ.RelativePropertyT.{v}) {ε : ℝ} (hε : 0 < ε) :
    ∃ (F : Finset Γ) (δ : ℝ), 0 < δ ∧ ∀ φ : Γ → ℂ,
      (Matrix.of fun g h ↦ φ (g⁻¹ * h)).PosSemidef → φ 1 = 1 →
        (∀ g ∈ F, ‖φ g - 1‖ < δ) → ∀ h ∈ Λ, ‖φ h - 1‖ < ε := by
  obtain ⟨F, δ, hδ, hK⟩ := hΛ.exists_mem_invariants_norm_sub_lt.{v, v} (half_pos hε)
  refine ⟨F, δ ^ 2 / 2, by positivity, fun φ hφ hφ1 hφF h hh ↦ ?_⟩
  set π := hφ.gnsRepresentation
  set ξ := hφ.gnsVector 1
  have hπ : π.IsUnitary := hφ.isUnitary_gnsRepresentation
  -- The GNS vector at the identity is moved by less than `δ` by each element of `F`, so it lies
  -- within `ε / 2` of a `Λ`-invariant vector `η`.
  obtain ⟨η, hη, hξη⟩ := hK hφ.gnsSpace π hπ ξ fun g hg ↦ (sq_lt_sq₀ (norm_nonneg _) hδ.le).mp <|
    (hφ.norm_gnsRepresentation_gnsVector_one_sub_sq_le hφ1 g).trans_lt (by linarith [hφF g hg])
  -- Hence `h ∈ Λ` moves `ξ` by at most `2 * ‖ξ - η‖ < ε`.
  have hπη : π h η = η := (mem_invariants_restrict.mp hη) h hh
  have hmove : ‖π h ξ - ξ‖ ≤ 2 * ‖ξ - η‖ := by
    calc ‖π h ξ - ξ‖ = ‖π h (ξ - η) - (ξ - η)‖ := by rw [map_sub, hπη]; abel_nf
      _ ≤ ‖π h (ξ - η)‖ + ‖ξ - η‖ := norm_sub_le _ _
      _ = 2 * ‖ξ - η‖ := by rw [hπ.norm_map]; ring
  calc ‖φ h - 1‖ = ‖⟪ξ, π h ξ⟫_ℂ - 1‖ := by rw [hφ.inner_gnsVector_one_gnsRepresentation]
    _ ≤ ‖π h ξ - ξ‖ := TauCeti.norm_inner_sub_one_le (hφ.norm_gnsVector_one hφ1) _
    _ < ε := by linarith

/-- **Relative property (T) by positive-definite functions.** If a normal subgroup `Λ` has relative
property (T), then every net of positive-definite functions `φᵢ` with `φᵢ 1 = 1` converging
pointwise to `1` converges to `1` uniformly on `Λ`. -/
theorem RelativePropertyT.tendstoUniformlyOn [Λ.Normal] (hΛ : Λ.RelativePropertyT.{v})
    {ι : Type*} {l : Filter ι} {φ : ι → Γ → ℂ}
    (hφ : ∀ i, (Matrix.of fun g h ↦ φ i (g⁻¹ * h)).PosSemidef) (hφ1 : ∀ i, φ i 1 = 1)
    (hlim : ∀ g, Tendsto (fun i ↦ φ i g) l (𝓝 1)) :
    TendstoUniformlyOn φ (fun _ ↦ 1) l Λ := by
  refine Metric.tendstoUniformlyOn_iff.mpr fun ε hε ↦ ?_
  obtain ⟨F, δ, hδ, hF⟩ := hΛ.exists_forall_norm_sub_one_lt hε
  have hev : ∀ᶠ i in l, ∀ g ∈ F, ‖φ i g - 1‖ < δ :=
    (F.eventually_all).mpr fun g _ ↦ by
      simpa [dist_eq_norm] using Metric.tendsto_nhds.mp (hlim g) δ hδ
  filter_upwards [hev] with i hi h hh
  rw [dist_comm, dist_eq_norm]
  exact hF (φ i) (hφ i) (hφ1 i) hi h hh

/-- **Relative property (T) from positive-definite functions, uniform form.** Let `ε < 1`. If there
are a finite set `F` and a `δ > 0` such that every positive-definite function `φ` with `φ 1 = 1`
and `‖φ g - 1‖ < δ` for `g ∈ F` satisfies `‖φ h - 1‖ < ε` for every `h ∈ Λ`, then `Λ` has relative
property (T), in every universe of representations. -/
theorem relativePropertyT_of_exists_forall_norm_sub_one_lt {ε : ℝ} (hε : ε < 1)
    (hΛ : ∃ (F : Finset Γ) (δ : ℝ), 0 < δ ∧ ∀ φ : Γ → ℂ,
      (Matrix.of fun g h ↦ φ (g⁻¹ * h)).PosSemidef → φ 1 = 1 →
        (∀ g ∈ F, ‖φ g - 1‖ < δ) → ∀ h ∈ Λ, ‖φ h - 1‖ < ε) :
    Λ.RelativePropertyT.{u} := by
  obtain ⟨F, δ, hδ, hF⟩ := hΛ
  refine (relativePropertyT_def Λ).mpr fun H _ _ _ ρ hρ hal ↦ ?_
  obtain ⟨ξ, hξ, hξF⟩ := (hasAlmostInvariantVectors_def ρ).mp hal F δ hδ
  -- The coefficient of `ξ` is a normalized positive-definite function close to `1` on `F`.
  have hclose := hF (fun g ↦ ⟪ξ, ρ g ξ⟫_ℂ) (hρ.posSemidef_inner_map_inv_mul ξ)
    (by simpa using inner_self_eq_one_of_norm_eq_one (𝕜 := ℂ) hξ)
    fun g hg ↦ (TauCeti.norm_inner_sub_one_le hξ _).trans_lt (hξF g hg)
  -- So its real part is at least `1 - ε > 0` on `Λ`.
  refine (hρ.restrict Λ.subtype).exists_ne_zero_mem_invariants_of_le_re_inner (ξ := ξ)
    (sub_pos.mpr hε) fun h ↦ ?_
  simp only [restrict_apply_apply, coe_subtype]
  linarith [hclose h h.property, RCLike.one_sub_re_le_norm_sub_one ⟪ξ, ρ h ξ⟫_ℂ]

/-- **Relative property (T) from positive-definite functions.** If every net of positive-definite
functions `φᵢ` with `φᵢ 1 = 1` converging pointwise to `1`, indexed by a type in the universe of
`Γ`, converges to `1` uniformly on `Λ`, then `Λ` has relative property (T), in every universe of
representations. -/
theorem relativePropertyT_of_forall_tendstoUniformlyOn
    (hΛ : ∀ (ι : Type v) (l : Filter ι) (φ : ι → Γ → ℂ),
      (∀ i, (Matrix.of fun g h ↦ φ i (g⁻¹ * h)).PosSemidef) → (∀ i, φ i 1 = 1) →
        (∀ g, Tendsto (fun i ↦ φ i g) l (𝓝 1)) → TendstoUniformlyOn φ (fun _ ↦ 1) l Λ) :
    Λ.RelativePropertyT.{u} := by
  classical
  refine relativePropertyT_of_exists_forall_norm_sub_one_lt (ε := 1 / 2) (by norm_num) ?_
  by_contra! hne
  -- Otherwise, for each finite set `F` and each `n`, choose a normalized positive-definite
  -- function within `1 / (n + 1)` of `1` on `F` and at least `1 / 2` away from `1` somewhere
  -- on `Λ`.
  have key (i : Finset Γ × ℕ) := hne i.1 (1 / (i.2 + 1)) Nat.one_div_pos_of_nat
  choose φ hφ hφ1 hφF h hh hφh using key
  -- These converge pointwise to `1`, but not uniformly on `Λ`.
  have hlim (g : Γ) : Tendsto (fun i ↦ φ i g) atTop (𝓝 1) := by
    refine Metric.tendsto_nhds.mpr fun ε hε ↦ ?_
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt hε
    filter_upwards [eventually_ge_atTop (({g}, n) : Finset Γ × ℕ)] with i hi
    rw [dist_eq_norm]
    refine (hφF i g (hi.1 (Finset.mem_singleton_self g))).trans_le ((one_div_le_one_div_of_le
      (by positivity) (by exact_mod_cast Nat.add_le_add_right hi.2 1)).trans hn.le)
  obtain ⟨i, hi⟩ := ((Metric.tendstoUniformlyOn_iff.mp (hΛ _ atTop φ hφ hφ1 hlim)) (1 / 2)
    (by norm_num)).exists
  have := hi (h i) (hh i)
  rw [dist_comm, dist_eq_norm] at this
  exact (hφh i).not_gt this

/-- **Relative property (T) by positive-definite functions, uniform form.** A normal subgroup `Λ`
has relative property (T) exactly when for every `ε > 0` there are a finite set `F` and a `δ > 0`
such that every positive-definite function `φ` with `φ 1 = 1` and `‖φ g - 1‖ < δ` for `g ∈ F`
satisfies `‖φ h - 1‖ < ε` for every `h ∈ Λ`. -/
theorem relativePropertyT_iff_forall_exists_forall_norm_sub_one_lt [Λ.Normal] :
    Λ.RelativePropertyT.{v} ↔ ∀ ε > 0, ∃ (F : Finset Γ) (δ : ℝ), 0 < δ ∧ ∀ φ : Γ → ℂ,
      (Matrix.of fun g h ↦ φ (g⁻¹ * h)).PosSemidef → φ 1 = 1 →
        (∀ g ∈ F, ‖φ g - 1‖ < δ) → ∀ h ∈ Λ, ‖φ h - 1‖ < ε :=
  ⟨fun hΛ _ hε ↦ hΛ.exists_forall_norm_sub_one_lt hε, fun h ↦
    relativePropertyT_of_exists_forall_norm_sub_one_lt (by norm_num) (h (1 / 2) (by norm_num))⟩

/-- **Relative property (T) by positive-definite functions.** A normal subgroup `Λ` has relative
property (T) exactly when every net of positive-definite functions `φᵢ` with `φᵢ 1 = 1` converging
pointwise to `1` converges to `1` uniformly on `Λ` (Anantharaman–Popa, Proposition 14.1.2). -/
theorem relativePropertyT_iff_forall_tendstoUniformlyOn [Λ.Normal] :
    Λ.RelativePropertyT.{v} ↔ ∀ (ι : Type v) (l : Filter ι) (φ : ι → Γ → ℂ),
      (∀ i, (Matrix.of fun g h ↦ φ i (g⁻¹ * h)).PosSemidef) → (∀ i, φ i 1 = 1) →
        (∀ g, Tendsto (fun i ↦ φ i g) l (𝓝 1)) → TendstoUniformlyOn φ (fun _ ↦ 1) l Λ :=
  ⟨fun hΛ _ _ _ hφ hφ1 hlim ↦ hΛ.tendstoUniformlyOn hφ hφ1 hlim,
    relativePropertyT_of_forall_tendstoUniformlyOn⟩

end Subgroup

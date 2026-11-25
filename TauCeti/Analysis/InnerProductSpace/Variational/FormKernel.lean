/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.Variational.CompactFormPair
public import TauCeti.Analysis.InnerProductSpace.Variational.EnergySpace
public import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import TauCeti.Analysis.Normed.Operator.Compact.Estimate
import TauCeti.Analysis.Variational.QuadraticEnergy

/-!
# The kernel-orthogonal Poincaré connector of a compact form pair

Let `P` be a compact form pair (`TauCeti.CompactFormPair 𝕜 V H`): a compact injective map
`j : V → H` of dense range and a bounded Hermitian form `a` on `V` with energy `q(u) = re a(u, u)`
and a shifted coercivity bound `c ‖u‖² ≤ q(u) + ω ‖j u‖²`. Its **form kernel**
`N = {u | ∀ v, a(u, v) = 0}` (`TauCeti.CompactFormPair.formKernel`) is finite dimensional, since
the shifted bound gives `c ‖u‖² ≤ ω ‖j u‖²` on `N` and `j` is compact. So `j N` is closed in `H`,
and `N` is a complement of `{u | j u ⊥ j N}` in `V`.

When the energy is nonnegative, `N = {u | q(u) = 0}`. When moreover `V` is complete, the energy
is coercive on the kernel-orthogonal part: there is `δ > 0` with `δ ‖j u‖² ≤ q(u)` whenever
`j u ⊥ j N` (`TauCeti.CompactFormPair.exists_pos_mul_norm_inclusion_sq_le_energy`), and then
`c' ‖u‖² ≤ q(u)` there for some `c' > 0`. The best constant `δ` is the minimum of the energy on
the constrained sphere of `(j N)ᗮ`. This gives the solvability of the weak equation
`a(u, v) = ℓ(v)` for all `v`: it has a solution if and only if `ℓ` vanishes on `N`, and solutions
are unique modulo `N` (`TauCeti.CompactFormPair.exists_forall_form_apply_eq_iff`).

## Main results

* `TauCeti.CompactFormPair.formKernel`: the form kernel `N`, with
  `mem_formKernel_iff_energy_eq_zero` for nonnegative energies.
* `TauCeti.CompactFormPair.finiteDimensional_formKernel`, `isClosed_map_formKernel`: `N` is finite
  dimensional and `j N` is closed.
* `TauCeti.CompactFormPair.isCompl_formKernel`: `N` and `{u | j u ⊥ j N}` are complements.
* `TauCeti.CompactFormPair.isGreatest_setOf_mul_norm_sq_le_energy`: the best constant of the
  inequality `δ ‖j u‖² ≤ q(u)` on `{j u ∈ W}` is the minimum of the energy on the constrained
  sphere of `W`.
* `TauCeti.CompactFormPair.exists_pos_mul_norm_inclusion_sq_le_energy`,
  `exists_pos_mul_norm_sq_le_energy`: coercivity of a nonnegative energy in the
  `H` norm and in the `V` norm on the kernel-orthogonal part.
* `TauCeti.CompactFormPair.finiteDimensional_of_orthogonal_eq_bot`: if `(j N)ᗮ = 0` then `H` is
  finite dimensional.
* `TauCeti.CompactFormPair.exists_forall_form_apply_eq_iff` and
  `sub_mem_formKernel_of_forall_form_apply_eq`: the annihilator criterion for the weak equation and
  uniqueness modulo `N`.

## References

* V. Ivrii, *Partial Differential Equations*, Chapter 13, §13.1, Theorems 1–4.
* J. K. Hunter, *Notes on Partial Differential Equations*, Chapter 4, §4.8, §4.10 and
  Theorem 4.20 (the Lax–Milgram theorem).
-/

public section

open RCLike Set
open scoped InnerProductSpace

namespace TauCeti

namespace CompactFormPair

variable {𝕜 V H : Type*} [RCLike 𝕜] [NormedAddCommGroup V] [InnerProductSpace 𝕜 V]
  [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] (P : CompactFormPair 𝕜 V H)

/-! ### The form kernel -/

/-- The **form kernel** `N = {u | ∀ v, a(u, v) = 0}` of a compact form pair. -/
def formKernel : Submodule 𝕜 V where
  carrier := {u | ∀ v, P.form u v = 0}
  add_mem' hu hv w := by simp [hu w, hv w]
  zero_mem' := by simp
  smul_mem' c u hu w := by simp [hu w]

variable {P} {u v n : V}

@[simp]
theorem mem_formKernel : u ∈ P.formKernel ↔ ∀ v, P.form u v = 0 :=
  Iff.rfl

/-- A vector of the form kernel is also annihilated from the right, by the Hermitian symmetry. -/
theorem form_apply_eq_zero_of_mem_formKernel (hn : n ∈ P.formKernel) (u : V) :
    P.form u n = 0 := by
  rw [P.hermitian, mem_formKernel.1 hn, star_zero]

theorem energy_eq_zero_of_mem_formKernel (hn : n ∈ P.formKernel) : P.energy n = 0 := by
  simp [energy_def, mem_formKernel.1 hn]

/-- For a nonnegative energy the form kernel is the zero set of the energy. -/
theorem mem_formKernel_iff_energy_eq_zero (hq : ∀ w, 0 ≤ P.energy w) :
    u ∈ P.formKernel ↔ P.energy u = 0 := by
  rw [energy_def, ContinuousLinearMap.re_apply_self_eq_zero_iff P.hermitian
    (fun w ↦ by simpa only [energy_def] using hq w), mem_formKernel]
  simp only [ContinuousLinearMap.ext_iff, zero_apply]

variable (P)

/-- On the form kernel the shifted coercivity bound reads `c ‖u‖² ≤ ω ‖j u‖²`: the norms of `V`
and `H` are equivalent there. -/
theorem exists_mul_norm_sq_le_mul_norm_inclusion_sq :
    ∃ c > 0, ∃ ω : ℝ, ∀ u ∈ P.formKernel, c * ‖u‖ ^ 2 ≤ ω * ‖P.inclusion u‖ ^ 2 := by
  obtain ⟨c, hc, ω, h⟩ := P.exists_mul_norm_sq_le_energy_add
  exact ⟨c, hc, ω, fun u hu ↦ by simpa [energy_eq_zero_of_mem_formKernel hu] using h u⟩

/-- The form kernel is finite dimensional: the inclusion is compact and bounded below on it. -/
instance finiteDimensional_formKernel : FiniteDimensional 𝕜 P.formKernel := by
  obtain ⟨c, hc, ω, h⟩ := P.exists_mul_norm_sq_le_mul_norm_inclusion_sq
  refine IsCompactOperator.finiteDimensional_of_norm_le_mul_norm
    (K := P.inclusion ∘L P.formKernel.subtypeL) (C := √(max ω 0 / c))
    (P.isCompactOperator.comp_clm _) fun x ↦ ?_
  have hle : ‖(x : V)‖ ^ 2 ≤ (√(max ω 0 / c) * ‖P.inclusion x‖) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (div_nonneg (le_max_right _ _) hc.le), div_mul_eq_mul_div,
      le_div_iff₀ hc, mul_comm]
    exact (h x x.property).trans (by gcongr; exact le_max_left _ _)
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 hle

instance finiteDimensional_map_formKernel :
    FiniteDimensional 𝕜 (P.formKernel.map (P.inclusion : V →ₗ[𝕜] H)) :=
  Module.Finite.map _ _

/-- The image `j N` of the form kernel is closed in `H`. -/
theorem isClosed_map_formKernel :
    IsClosed (P.formKernel.map (P.inclusion : V →ₗ[𝕜] H) : Set H) :=
  Submodule.isClosed_of_finiteDimensional _

/-- The form kernel `N` and the kernel-orthogonal part `{u | j u ⊥ j N}` are complements. -/
theorem isCompl_formKernel :
    IsCompl P.formKernel
      ((P.formKernel.map (P.inclusion : V →ₗ[𝕜] H))ᗮ.comap (P.inclusion : V →ₗ[𝕜] H)) := by
  set K := P.formKernel.map (P.inclusion : V →ₗ[𝕜] H)
  refine ⟨Submodule.disjoint_def.2 fun n hn hn' ↦ P.injective ?_, ?_⟩
  · have h : P.inclusion n ∈ K ⊓ Kᗮ := ⟨Submodule.mem_map_of_mem hn, hn'⟩
    rw [Submodule.inf_orthogonal_eq_bot, Submodule.mem_bot] at h
    rw [h, map_zero]
  · refine codisjoint_iff_le_sup.2 fun v _ ↦ ?_
    obtain ⟨n, hn, hjn⟩ := Submodule.mem_map.1 (K.starProjection_apply_mem (P.inclusion v))
    refine Submodule.mem_sup.2 ⟨n, hn, v - n, ?_, add_sub_cancel _ _⟩
    simp [Submodule.mem_comap, map_sub, hjn]

/-! ### Coercivity on the kernel-orthogonal part -/

variable {P}

/-- **The best Poincaré constant.** For a minimizer `u₀` of the energy on the constrained sphere
`S_W`, the value `q(u₀)` is the greatest `δ` with `δ ‖j u‖² ≤ q(u)` for every `u` with
`j u ∈ W`. -/
theorem isGreatest_setOf_mul_norm_sq_le_energy {W : Submodule 𝕜 H} {u₀ : V}
    (hu₀ : u₀ ∈ P.unitConstraint W) (hmin : IsMinOn P.energy (P.unitConstraint W) u₀) :
    IsGreatest {δ | ∀ u, P.inclusion u ∈ W → δ * ‖P.inclusion u‖ ^ 2 ≤ P.energy u}
      (P.energy u₀) :=
  ⟨fun _ hu ↦ mul_norm_sq_le_energy_of_isMinOn hmin hu,
    fun δ hδ ↦ by simpa [(mem_unitConstraint.1 hu₀).2] using hδ u₀ (mem_unitConstraint.1 hu₀).1⟩

/-- For a nonnegative energy, every vector of the constrained sphere of `(j N)ᗮ` has positive
energy. -/
theorem energy_pos_of_mem_unitConstraint_orthogonal (hq : ∀ w, 0 ≤ P.energy w)
    (hu : u ∈ P.unitConstraint (P.formKernel.map (P.inclusion : V →ₗ[𝕜] H))ᗮ) :
    0 < P.energy u := by
  refine (hq u).lt_of_ne fun h0 ↦ ?_
  have hN : u ∈ P.formKernel := (mem_formKernel_iff_energy_eq_zero hq).2 h0.symm
  have h : P.inclusion u ∈ P.formKernel.map (P.inclusion : V →ₗ[𝕜] H) ⊓
      (P.formKernel.map (P.inclusion : V →ₗ[𝕜] H))ᗮ :=
    ⟨Submodule.mem_map_of_mem hN, (mem_unitConstraint.1 hu).1⟩
  rw [Submodule.inf_orthogonal_eq_bot, Submodule.mem_bot] at h
  simpa [h] using (mem_unitConstraint.1 hu).2

variable (P)

/-- **The kernel-orthogonal Poincaré inequality.** For a nonnegative energy on a complete form
domain there is `δ > 0` with `δ ‖j u‖² ≤ q(u)` whenever `j u ⊥ j N`. -/
theorem exists_pos_mul_norm_inclusion_sq_le_energy [CompleteSpace V]
    (hq : ∀ w, 0 ≤ P.energy w) :
    ∃ δ > 0, ∀ u, P.inclusion u ∈ (P.formKernel.map (P.inclusion : V →ₗ[𝕜] H))ᗮ →
      δ * ‖P.inclusion u‖ ^ 2 ≤ P.energy u := by
  set W := (P.formKernel.map (P.inclusion : V →ₗ[𝕜] H))ᗮ
  by_cases hne : (P.unitConstraint W).Nonempty
  · obtain ⟨u₀, hu₀, hmin⟩ :=
      P.exists_isMinOn_energy_unitConstraint W (Submodule.isClosed_orthogonal _) hne
    exact ⟨P.energy u₀, energy_pos_of_mem_unitConstraint_orthogonal hq hu₀,
      fun _ hu ↦ mul_norm_sq_le_energy_of_isMinOn hmin hu⟩
  · refine ⟨1, one_pos, fun u hu ↦ ?_⟩
    by_cases hu0 : P.inclusion u = 0
    · simpa [hu0] using hq u
    · exact absurd (unitConstraint_nonempty_iff.2 ⟨u, hu, hu0⟩) hne

/-- **Coercivity on the kernel-orthogonal part.** For a nonnegative energy on a complete form
domain there is `c' > 0` with `c' ‖u‖² ≤ q(u)` whenever `j u ⊥ j N`. -/
theorem exists_pos_mul_norm_sq_le_energy [CompleteSpace V] (hq : ∀ w, 0 ≤ P.energy w) :
    ∃ c > 0, ∀ u, P.inclusion u ∈ (P.formKernel.map (P.inclusion : V →ₗ[𝕜] H))ᗮ →
      c * ‖u‖ ^ 2 ≤ P.energy u := by
  obtain ⟨δ, hδ, hP⟩ := P.exists_pos_mul_norm_inclusion_sq_le_energy hq
  obtain ⟨c, hc, ω, h⟩ := P.exists_mul_norm_sq_le_energy_add
  set ω' := max ω 0
  refine ⟨c / (1 + ω' / δ), by positivity, fun u hu ↦ ?_⟩
  have h1 : ω * ‖P.inclusion u‖ ^ 2 ≤ ω' / δ * P.energy u := by
    calc ω * ‖P.inclusion u‖ ^ 2 ≤ ω' * ‖P.inclusion u‖ ^ 2 := by
          gcongr; exact le_max_left _ _
      _ = ω' / δ * (δ * ‖P.inclusion u‖ ^ 2) := by field_simp
      _ ≤ ω' / δ * P.energy u := by gcongr; exact hP u hu
  rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
  nlinarith [h u]

/-- If the kernel-orthogonal part `(j N)ᗮ` is zero, then `j N = H`, so `H` is finite
dimensional. -/
theorem finiteDimensional_of_orthogonal_eq_bot
    (h : (P.formKernel.map (P.inclusion : V →ₗ[𝕜] H))ᗮ = ⊥) : FiniteDimensional 𝕜 H := by
  refine Module.Finite.of_surjective ((P.inclusion : V →ₗ[𝕜] H) ∘ₗ P.formKernel.subtype) ?_
  rw [← LinearMap.range_eq_top, LinearMap.range_comp, Submodule.range_subtype,
    ← Submodule.orthogonal_eq_bot_iff, h]

/-! ### The weak equation modulo the kernel -/

variable {P}

/-- A forcing `ℓ` for which the weak equation `a(u, v) = ℓ(v)` has a solution vanishes on the form
kernel. -/
theorem apply_eq_zero_of_forall_form_apply_eq {ℓ : StrongDual 𝕜 V}
    (h : ∀ v, P.form u v = ℓ v) (hn : n ∈ P.formKernel) : ℓ n = 0 := by
  rw [← h, form_apply_eq_zero_of_mem_formKernel hn]

/-- Two solutions of the same weak equation differ by an element of the form kernel. -/
theorem sub_mem_formKernel_of_forall_form_apply_eq {u₁ u₂ : V} {ℓ : StrongDual 𝕜 V}
    (h₁ : ∀ v, P.form u₁ v = ℓ v) (h₂ : ∀ v, P.form u₂ v = ℓ v) :
    u₁ - u₂ ∈ P.formKernel :=
  mem_formKernel.2 fun v ↦ by simp [h₁, h₂]

variable (P)

/-- The restriction of the form `a` to the kernel-orthogonal part `{u | j u ⊥ j N}`, which is a
coercive Hermitian form there when the energy is nonnegative and `V` is complete. -/
noncomputable def kernelOrthogonalForm [CompleteSpace V] (hq : ∀ w, 0 ≤ P.energy w) :
    CoerciveHermitianForm 𝕜
      ((P.formKernel.map (P.inclusion : V →ₗ[𝕜] H))ᗮ.comap (P.inclusion : V →ₗ[𝕜] H)) where
  form := P.form.bilinearComp (Submodule.subtypeL _) (Submodule.subtypeL _)
  form_apply_eq_star u v := P.hermitian u v
  exists_coercive := by
    obtain ⟨c, hc, h⟩ := P.exists_pos_mul_norm_sq_le_energy hq
    exact ⟨c, hc, fun u ↦ by simpa [energy_def] using h u u.property⟩

/-- The form of `kernelOrthogonalForm` is `a` on the kernel-orthogonal part. -/
@[simp]
theorem kernelOrthogonalForm_form_apply [CompleteSpace V] (hq : ∀ w, 0 ≤ P.energy w)
    (u v : (P.formKernel.map (P.inclusion : V →ₗ[𝕜] H))ᗮ.comap (P.inclusion : V →ₗ[𝕜] H)) :
    (P.kernelOrthogonalForm hq).form u v = P.form u v := by
  simp [kernelOrthogonalForm]

/-- **The annihilator criterion.** For a nonnegative energy on a complete form domain, the weak
equation `a(u, v) = ℓ(v)` for all `v` has a solution exactly when `ℓ` vanishes on the form kernel;
solutions are then unique modulo the kernel
(`TauCeti.CompactFormPair.sub_mem_formKernel_of_forall_form_apply_eq`). -/
theorem exists_forall_form_apply_eq_iff [CompleteSpace V] (hq : ∀ w, 0 ≤ P.energy w)
    (ℓ : StrongDual 𝕜 V) :
    (∃ u, ∀ v, P.form u v = ℓ v) ↔ ∀ n ∈ P.formKernel, ℓ n = 0 := by
  refine ⟨fun ⟨u, hu⟩ _ hn ↦ apply_eq_zero_of_forall_form_apply_eq hu hn, fun hℓ ↦ ?_⟩
  set V' := (P.formKernel.map (P.inclusion : V →ₗ[𝕜] H))ᗮ.comap (P.inclusion : V →ₗ[𝕜] H)
  have hV' : IsClosed (V' : Set V) :=
    (Submodule.isClosed_orthogonal _).preimage P.inclusion.continuous
  have : CompleteSpace V' := hV'.completeSpace_coe
  set a := P.kernelOrthogonalForm hq
  obtain ⟨u', hu', -⟩ := InnerProductSpace.existsUnique_forall_apply_eq a.form
    a.isUnit_continuousLinearMapOfBilin (ℓ ∘L V'.subtypeL)
  simp only [a, kernelOrthogonalForm_form_apply, ContinuousLinearMap.comp_apply,
    Submodule.subtypeL_apply] at hu'
  refine ⟨u', fun v ↦ ?_⟩
  obtain ⟨n, hn, w, hw, rfl⟩ := Submodule.mem_sup.1
    ((P.isCompl_formKernel.codisjoint.eq_top ▸ Submodule.mem_top) : v ∈ P.formKernel ⊔ V')
  rw [map_add, map_add, form_apply_eq_zero_of_mem_formKernel hn, hℓ n hn, zero_add, zero_add]
  exact hu' ⟨w, hw⟩

end CompactFormPair

end TauCeti

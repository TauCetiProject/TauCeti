/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.Variational.CompactFormPair
public import TauCeti.Analysis.InnerProductSpace.Variational.FormEigenspace
public import TauCeti.Analysis.InnerProductSpace.Variational.EnergySpace
public import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import TauCeti.Analysis.RCLike.SesquilinearForm

/-!
# The kernel-orthogonal Poincaré connector of a compact form pair

Let `P` be a compact form pair (`TauCeti.CompactFormPair 𝕜 V H`): a compact injective map
`j : V → H` of dense range and a bounded Hermitian form `a` on `V` with energy `q(u) = re a(u, u)`
and a shifted coercivity bound `c ‖u‖² ≤ q(u) + ω ‖j u‖²`. Its **form kernel**
`N = {u | ∀ v, a(u, v) = 0}` (`TauCeti.CompactFormPair.formKernel`) is the variational eigenspace
at `λ = 0` (`TauCeti.CompactFormPair.formEigenspace_zero`), so it is finite dimensional.
Hence `j N` is closed in `H`, and `N` is a complement of `{u | j u ⊥ j N}` in `V`.

When the energy is nonnegative, `N = {u | q(u) = 0}`. When moreover `V` is complete, the energy
is coercive on the kernel-orthogonal part: there is `δ > 0` with `δ ‖j u‖² ≤ q(u)` whenever
`j u ⊥ j N` (`TauCeti.CompactFormPair.exists_pos_mul_norm_inclusion_sq_le_energy`), and then
`c' ‖u‖² ≤ q(u)` there for some `c' > 0`. The best constant `δ` is the minimum of the energy on
the constrained sphere of `(j N)ᗮ`. This gives the solvability of the weak equation
`a(u, v) = ℓ(v)` for all `v`: it has a solution if and only if `ℓ` vanishes on `N`, and solutions
are unique modulo `N` (`TauCeti.CompactFormPair.exists_forall_form_apply_eq_iff`).

## Main results

* `TauCeti.CompactFormPair.formKernel`: the form kernel `N`, with `formEigenspace_zero` and
  `mem_formKernel_iff_energy_eq_zero` for nonnegative energies.
* `TauCeti.CompactFormPair.finiteDimensional_formKernel`, `isClosed_formKernelImage`: `N` is
  finite dimensional and its image `j N` (`TauCeti.CompactFormPair.formKernelImage`) is closed.
* `TauCeti.CompactFormPair.kernelOrthogonal`: the kernel-orthogonal part `{u | j u ⊥ j N}`,
  closed in `V` (`isClosed_kernelOrthogonal`).
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

/-- The **form kernel** `N = {u | ∀ v, a(u, v) = 0}` of a compact form pair, the kernel of the
form `a : V →L⋆[𝕜] V →L[𝕜] 𝕜`. -/
def formKernel : Submodule 𝕜 V :=
  LinearMap.ker (P.form : V →ₗ⋆[𝕜] V →L[𝕜] 𝕜)

variable {P} {u v n : V}

@[simp]
theorem mem_formKernel : u ∈ P.formKernel ↔ ∀ v, P.form u v = 0 := by
  simp [formKernel, ContinuousLinearMap.ext_iff]

/-- A vector of the form kernel is also annihilated from the right, by the Hermitian symmetry. -/
theorem form_apply_eq_zero_of_mem_formKernel (hn : n ∈ P.formKernel) (u : V) :
    P.form u n = 0 := by
  rw [P.hermitian, mem_formKernel.1 hn, star_zero]

theorem energy_eq_zero_of_mem_formKernel (hn : n ∈ P.formKernel) : P.energy n = 0 := by
  simp [energy_def, mem_formKernel.1 hn]

/-- For a nonnegative energy the form kernel is the zero set of the energy. -/
theorem mem_formKernel_iff_energy_eq_zero (hq : ∀ w, 0 ≤ P.energy w) :
    u ∈ P.formKernel ↔ P.energy u = 0 := by
  rw [mem_formKernel, energy_def]
  simpa using P.form.toLinearMap₁₂.forall_apply_eq_zero_iff_re_apply_self_eq_zero
    (fun x y ↦ by simpa using P.hermitian x y)
    (fun w ↦ by simpa [energy_def] using hq w)

/-- The form kernel is the variational eigenspace at `λ = 0`. -/
@[simp]
theorem formEigenspace_zero : P.formEigenspace 0 = P.formKernel := by
  ext u
  simp

variable (P)

/-- The form kernel is finite dimensional, as the variational eigenspace at `λ = 0`
(`TauCeti.CompactFormPair.finiteDimensional_formEigenspace`). -/
instance finiteDimensional_formKernel : FiniteDimensional 𝕜 P.formKernel :=
  formEigenspace_zero (P := P) ▸ P.finiteDimensional_formEigenspace 0

/-! ### The image of the form kernel and the kernel-orthogonal part -/

/-- The image `j N` of the form kernel in `H`. -/
def formKernelImage : Submodule 𝕜 H :=
  P.formKernel.map (P.inclusion : V →ₗ[𝕜] H)

/-- The **kernel-orthogonal part** `{u | j u ⊥ j N}` of a compact form pair. -/
def kernelOrthogonal : Submodule 𝕜 V :=
  P.formKernelImageᗮ.comap (P.inclusion : V →ₗ[𝕜] H)

variable {P}

@[simp]
theorem mem_formKernelImage {x : H} :
    x ∈ P.formKernelImage ↔ ∃ n ∈ P.formKernel, P.inclusion n = x :=
  Submodule.mem_map

theorem inclusion_mem_formKernelImage (hn : n ∈ P.formKernel) :
    P.inclusion n ∈ P.formKernelImage :=
  Submodule.mem_map_of_mem hn

@[simp]
theorem mem_kernelOrthogonal : u ∈ P.kernelOrthogonal ↔ P.inclusion u ∈ P.formKernelImageᗮ :=
  Iff.rfl

variable (P)

instance finiteDimensional_formKernelImage : FiniteDimensional 𝕜 P.formKernelImage :=
  Module.Finite.map _ _

/-- The image `j N` of the form kernel is closed in `H`. -/
theorem isClosed_formKernelImage : IsClosed (P.formKernelImage : Set H) :=
  Submodule.isClosed_of_finiteDimensional _

/-- The kernel-orthogonal part is closed in `V`. -/
theorem isClosed_kernelOrthogonal : IsClosed (P.kernelOrthogonal : Set V) :=
  (Submodule.isClosed_orthogonal _).preimage P.inclusion.continuous

instance completeSpace_kernelOrthogonal [CompleteSpace V] : CompleteSpace P.kernelOrthogonal :=
  P.isClosed_kernelOrthogonal.completeSpace_coe

/-- The form kernel `N` and the kernel-orthogonal part `{u | j u ⊥ j N}` are complements. -/
theorem isCompl_formKernel : IsCompl P.formKernel P.kernelOrthogonal := by
  refine ⟨Submodule.disjoint_def.2 fun n hn hn' ↦ P.injective ?_, ?_⟩
  · have h : P.inclusion n ∈ P.formKernelImage ⊓ P.formKernelImageᗮ :=
      ⟨inclusion_mem_formKernelImage hn, mem_kernelOrthogonal.1 hn'⟩
    rw [Submodule.inf_orthogonal_eq_bot, Submodule.mem_bot] at h
    rw [h, map_zero]
  · refine codisjoint_iff_le_sup.2 fun v _ ↦ ?_
    obtain ⟨n, hn, hjn⟩ :=
      mem_formKernelImage.1 (P.formKernelImage.starProjection_apply_mem (P.inclusion v))
    refine Submodule.mem_sup.2 ⟨n, hn, v - n, mem_kernelOrthogonal.2 ?_, add_sub_cancel _ _⟩
    rw [map_sub, hjn]
    exact P.formKernelImage.sub_starProjection_mem_orthogonal (P.inclusion v)

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
    (hu : u ∈ P.unitConstraint P.formKernelImageᗮ) : 0 < P.energy u := by
  refine (hq u).lt_of_ne fun h0 ↦ ?_
  have hN : u ∈ P.formKernel := (mem_formKernel_iff_energy_eq_zero hq).2 h0.symm
  have h0 : u = 0 := Submodule.disjoint_def.1 P.isCompl_formKernel.disjoint u hN
    (mem_kernelOrthogonal.2 (mem_unitConstraint.1 hu).1)
  simpa [h0] using (mem_unitConstraint.1 hu).2

variable (P)

/-- **The kernel-orthogonal Poincaré inequality.** For a nonnegative energy on a complete form
domain there is `δ > 0` with `δ ‖j u‖² ≤ q(u)` whenever `j u ⊥ j N`. -/
theorem exists_pos_mul_norm_inclusion_sq_le_energy [CompleteSpace V]
    (hq : ∀ w, 0 ≤ P.energy w) :
    ∃ δ > 0, ∀ u ∈ P.kernelOrthogonal, δ * ‖P.inclusion u‖ ^ 2 ≤ P.energy u := by
  by_cases hne : (P.unitConstraint P.formKernelImageᗮ).Nonempty
  · obtain ⟨u₀, hu₀, hmin⟩ := P.exists_isMinOn_energy_unitConstraint P.formKernelImageᗮ
      (Submodule.isClosed_orthogonal _) hne
    exact ⟨P.energy u₀, energy_pos_of_mem_unitConstraint_orthogonal hq hu₀,
      fun _ hu ↦ mul_norm_sq_le_energy_of_isMinOn hmin (mem_kernelOrthogonal.1 hu)⟩
  · refine ⟨1, one_pos, fun u hu ↦ ?_⟩
    by_cases hu0 : P.inclusion u = 0
    · simpa [hu0] using hq u
    · exact absurd (unitConstraint_nonempty_iff.2 ⟨u, mem_kernelOrthogonal.1 hu, hu0⟩) hne

/-- **Coercivity on the kernel-orthogonal part.** For a nonnegative energy on a complete form
domain there is `c' > 0` with `c' ‖u‖² ≤ q(u)` whenever `j u ⊥ j N`. -/
theorem exists_pos_mul_norm_sq_le_energy [CompleteSpace V] (hq : ∀ w, 0 ≤ P.energy w) :
    ∃ c > 0, ∀ u ∈ P.kernelOrthogonal, c * ‖u‖ ^ 2 ≤ P.energy u := by
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

/-- If the orthogonal complement `(j N)ᗮ` is zero, then `j N = H`, so `H` is finite
dimensional. -/
theorem finiteDimensional_of_orthogonal_eq_bot (h : P.formKernelImageᗮ = ⊥) :
    FiniteDimensional 𝕜 H := by
  refine Module.Finite.of_surjective ((P.inclusion : V →ₗ[𝕜] H) ∘ₗ P.formKernel.subtype) ?_
  rw [← LinearMap.range_eq_top, LinearMap.range_comp, Submodule.range_subtype]
  exact Submodule.orthogonal_eq_bot_iff.1 h

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
    CoerciveHermitianForm 𝕜 P.kernelOrthogonal where
  form := P.form.bilinearComp (Submodule.subtypeL _) (Submodule.subtypeL _)
  form_apply_eq_star u v := by simpa using P.hermitian u v
  exists_coercive := by
    obtain ⟨c, hc, h⟩ := P.exists_pos_mul_norm_sq_le_energy hq
    exact ⟨c, hc, fun u ↦ by simpa [energy_def] using h u u.property⟩

/-- The form of `kernelOrthogonalForm` is `a` on the kernel-orthogonal part. -/
@[simp]
theorem kernelOrthogonalForm_form_apply [CompleteSpace V] (hq : ∀ w, 0 ≤ P.energy w)
    (u v : P.kernelOrthogonal) : (P.kernelOrthogonalForm hq).form u v = P.form u v := by
  simp [kernelOrthogonalForm]

/-- **The annihilator criterion.** For a nonnegative energy on a complete form domain, the weak
equation `a(u, v) = ℓ(v)` for all `v` has a solution exactly when `ℓ` vanishes on the form kernel;
solutions are then unique modulo the kernel
(`TauCeti.CompactFormPair.sub_mem_formKernel_of_forall_form_apply_eq`). -/
theorem exists_forall_form_apply_eq_iff [CompleteSpace V] (hq : ∀ w, 0 ≤ P.energy w)
    (ℓ : StrongDual 𝕜 V) :
    (∃ u, ∀ v, P.form u v = ℓ v) ↔ ∀ n ∈ P.formKernel, ℓ n = 0 := by
  refine ⟨fun ⟨u, hu⟩ _ hn ↦ apply_eq_zero_of_forall_form_apply_eq hu hn, fun hℓ ↦ ?_⟩
  set a := P.kernelOrthogonalForm hq
  obtain ⟨u', hu', -⟩ := InnerProductSpace.existsUnique_forall_apply_eq a.form
    a.isUnit_continuousLinearMapOfBilin (ℓ ∘L P.kernelOrthogonal.subtypeL)
  simp only [a, kernelOrthogonalForm_form_apply, ContinuousLinearMap.comp_apply,
    Submodule.subtypeL_apply] at hu'
  refine ⟨u', fun v ↦ ?_⟩
  obtain ⟨n, hn, w, hw, rfl⟩ :=
    Submodule.mem_sup.1 (P.isCompl_formKernel.sup_eq_top.ge (Submodule.mem_top (x := v)))
  rw [map_add, map_add, form_apply_eq_zero_of_mem_formKernel hn, hℓ n hn, zero_add, zero_add]
  exact hu' ⟨w, hw⟩

end CompactFormPair

end TauCeti

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Diffeomorphism.Diffeotopy.Prod
public import TauCeti.Geometry.Manifold.DifferentialForm.Pullback.Smooth

/-!
# Diffeomorphisms isotopic to the identity through form-preserving diffeomorphisms

Let `σ` be a smooth differential form on a manifold `M`. Its stabilizer
`TauCeti.SmoothForm.diffeomorphStabilizer σ` is the group of smooth diffeomorphisms `φ` with
`φ^* σ = σ`; for a symplectic form `ω` it is `Symp(M, ω)`. This file defines the subgroup

`TauCeti.SmoothForm.isotopyStabilizer σ ≤ diffeomorphStabilizer σ`

of the final diffeomorphisms `φ₁` of the smooth diffeotopies `φ_t`, `t ∈ [0, 1]`, starting at the
identity, all of whose time slices preserve `σ`. For a symplectic form these are the
symplectomorphisms joined to the identity by a smooth symplectic isotopy. The diffeotopies are
those of `TauCeti.Diffeotopy`; they are not required to be constant near the ends of the time
interval.

It is a subgroup because the constant diffeotopy, pointwise composites `ψ_t ∘ φ_t` and pointwise
inverses `φ_t⁻¹` of `σ`-preserving diffeotopies preserve `σ`. Conjugating a `σ`-preserving
diffeotopy by an element `f` of the stabilizer gives the `σ`-preserving diffeotopy
`f ∘ φ_t ∘ f⁻¹` (`TauCeti.Diffeotopy.transDiffeomorph`), so the subgroup is normal in the
stabilizer (`TauCeti.SmoothForm.normal_isotopyStabilizer_subgroupOf`).

Stabilizers are natural under intertwining maps: if a smooth map `g : M' → M` satisfies
`g ∘ f' = f ∘ g` and `f` preserves `σ`, then `f'` preserves `g^* σ`
(`TauCeti.SmoothForm.mem_diffeomorphStabilizer_mpullback_of_semiconj`). Applied to the two
projections of a product, this shows that products `f × f'` of diffeomorphisms preserving `σ` on
`M` and `τ` on `N` preserve the form `pr₁^* σ + pr₂^* τ` on `M × N`, and products of
diffeomorphisms in the isotopy stabilizers lie in the isotopy stabilizer of `pr₁^* σ + pr₂^* τ`,
through the product diffeotopy `TauCeti.Diffeotopy.prodCongr`.

## Main definitions

* `TauCeti.SmoothForm.isotopyStabilizer σ`: the final diffeomorphisms of the diffeotopies
  preserving `σ` at every time.

## Main results

* `TauCeti.SmoothForm.timeSlice_trans_mem_diffeomorphStabilizer`,
  `TauCeti.SmoothForm.timeSlice_symm_mem_diffeomorphStabilizer`,
  `TauCeti.SmoothForm.timeSlice_transDiffeomorph_mem_diffeomorphStabilizer`: pointwise
  composites, inverses and conjugates of `σ`-preserving diffeotopies preserve `σ`.
* `TauCeti.SmoothForm.isotopyStabilizer_le_diffeomorphStabilizer`: these preserve `σ`.
* `TauCeti.SmoothForm.mul_mul_inv_mem_isotopyStabilizer`: conjugation by an element of the
  stabilizer preserves the subgroup.
* `TauCeti.SmoothForm.normal_isotopyStabilizer_subgroupOf`: the subgroup is normal in the
  stabilizer of `σ` (an instance).
* `TauCeti.SmoothForm.eval₂_mfderiv_of_mem_diffeomorphStabilizer`: a diffeomorphism preserving a
  two-form preserves its values on pushed-forward tangent vectors.
* `TauCeti.SmoothForm.mem_diffeomorphStabilizer_mpullback_of_semiconj`: naturality of
  stabilizers under intertwining maps.
* `TauCeti.SmoothForm.prodCongr_mem_diffeomorphStabilizer`,
  `TauCeti.SmoothForm.timeSlice_prodCongr_mem_diffeomorphStabilizer`,
  `TauCeti.SmoothForm.prodCongr_mem_isotopyStabilizer`: products of form-preserving
  diffeomorphisms and diffeotopies preserve the sum of the pulled-back forms.

## References

* Dusa McDuff and Dietmar Salamon, *Introduction to Symplectic Topology*, 3rd ed., Oxford
  University Press, 2017, Section 10.2.
-/

public section

noncomputable section

open scoped ContDiff Manifold

namespace TauCeti

namespace SmoothForm

variable {E H M F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {J : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [IsManifold J 1 M]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {k : ℕ} {σ : SmoothForm J M F k}

/-- The time slices of the constant diffeotopy preserve `σ`. -/
theorem timeSlice_refl_mem_diffeomorphStabilizer (t : unitInterval) :
    (Diffeotopy.refl J ∞ M).timeSlice t ∈ diffeomorphStabilizer σ := by
  rw [Diffeotopy.timeSlice_refl]
  exact (diffeomorphStabilizer σ).one_mem

/-- If two diffeotopies preserve `σ` at every time, so does their pointwise composite. -/
theorem timeSlice_trans_mem_diffeomorphStabilizer {Φ Ψ : Diffeotopy J ∞ M}
    (hΦ : ∀ t, Φ.timeSlice t ∈ diffeomorphStabilizer σ)
    (hΨ : ∀ t, Ψ.timeSlice t ∈ diffeomorphStabilizer σ) (t : unitInterval) :
    (Φ.trans Ψ).timeSlice t ∈ diffeomorphStabilizer σ := by
  rw [Diffeotopy.timeSlice_trans, ← Diffeomorph.mul_def]
  exact (diffeomorphStabilizer σ).mul_mem (hΨ t) (hΦ t)

/-- If a diffeotopy preserves `σ` at every time, so does its pointwise inverse. -/
theorem timeSlice_symm_mem_diffeomorphStabilizer {Φ : Diffeotopy J ∞ M}
    (hΦ : ∀ t, Φ.timeSlice t ∈ diffeomorphStabilizer σ) (t : unitInterval) :
    Φ.symm.timeSlice t ∈ diffeomorphStabilizer σ := by
  rw [Diffeotopy.timeSlice_symm, ← Diffeomorph.inv_def]
  exact (diffeomorphStabilizer σ).inv_mem (hΦ t)

/-- If a diffeotopy `φ_t` preserves `σ` at every time and `f` preserves `σ`, then the conjugated
diffeotopy `f ∘ φ_t ∘ f⁻¹` preserves `σ` at every time. -/
theorem timeSlice_transDiffeomorph_mem_diffeomorphStabilizer {f : M ≃ₘ⟮J, J⟯ M}
    {Φ : Diffeotopy J ∞ M} (hf : f ∈ diffeomorphStabilizer σ)
    (hΦ : ∀ t, Φ.timeSlice t ∈ diffeomorphStabilizer σ) (t : unitInterval) :
    (Φ.transDiffeomorph f).timeSlice t ∈ diffeomorphStabilizer σ := by
  rw [Diffeotopy.timeSlice_transDiffeomorph_eq_mul_mul_inv]
  exact (diffeomorphStabilizer σ).mul_mem ((diffeomorphStabilizer σ).mul_mem hf (hΦ t))
    ((diffeomorphStabilizer σ).inv_mem hf)

/-- The **isotopy stabilizer** of a smooth form `σ`: the final diffeomorphisms `φ₁` of the smooth
diffeotopies `φ_t` all of whose time slices preserve `σ`. For a symplectic form these are the
symplectomorphisms joined to the identity by a smooth symplectic isotopy. -/
def isotopyStabilizer (σ : SmoothForm J M F k) : Subgroup (M ≃ₘ⟮J, J⟯ M) where
  carrier := {φ | ∃ Φ : Diffeotopy J ∞ M,
    (∀ t, Φ.timeSlice t ∈ diffeomorphStabilizer σ) ∧ Φ.final = φ}
  one_mem' := ⟨Diffeotopy.refl J ∞ M, timeSlice_refl_mem_diffeomorphStabilizer,
    Diffeotopy.final_refl⟩
  mul_mem' := by
    rintro _ _ ⟨Φ, hΦ, rfl⟩ ⟨Ψ, hΨ, rfl⟩
    exact ⟨Ψ.trans Φ, timeSlice_trans_mem_diffeomorphStabilizer hΨ hΦ, by
      rw [Diffeotopy.final_trans, Diffeomorph.mul_def]⟩
  inv_mem' := by
    rintro _ ⟨Φ, hΦ, rfl⟩
    exact ⟨Φ.symm, timeSlice_symm_mem_diffeomorphStabilizer hΦ, by
      rw [Diffeotopy.final_symm, Diffeomorph.inv_def]⟩

/-- A diffeomorphism lies in the isotopy stabilizer of `σ` exactly when it is the final
diffeomorphism of a diffeotopy all of whose time slices preserve `σ`. -/
theorem mem_isotopyStabilizer {φ : M ≃ₘ⟮J, J⟯ M} :
    φ ∈ isotopyStabilizer σ ↔
      ∃ Φ : Diffeotopy J ∞ M, (∀ t, Φ.timeSlice t ∈ diffeomorphStabilizer σ) ∧ Φ.final = φ :=
  Iff.rfl

/-- The final diffeomorphism of a diffeotopy preserving `σ` at every time lies in the isotopy
stabilizer of `σ`. -/
theorem final_mem_isotopyStabilizer {Φ : Diffeotopy J ∞ M}
    (hΦ : ∀ t, Φ.timeSlice t ∈ diffeomorphStabilizer σ) : Φ.final ∈ isotopyStabilizer σ :=
  ⟨Φ, hΦ, rfl⟩

/-- The final diffeomorphism of a diffeotopy preserving `σ` at every time preserves `σ`. -/
theorem final_mem_diffeomorphStabilizer {Φ : Diffeotopy J ∞ M}
    (hΦ : ∀ t, Φ.timeSlice t ∈ diffeomorphStabilizer σ) : Φ.final ∈ diffeomorphStabilizer σ := by
  rw [Diffeotopy.final_def]
  exact hΦ 1

/-- Diffeomorphisms isotopic to the identity through `σ`-preserving diffeomorphisms preserve
`σ`. -/
theorem isotopyStabilizer_le_diffeomorphStabilizer :
    isotopyStabilizer σ ≤ diffeomorphStabilizer σ := by
  rintro _ ⟨Φ, hΦ, rfl⟩
  exact final_mem_diffeomorphStabilizer hΦ

/-- Conjugating an element of the isotopy stabilizer of `σ` by an element `f` of the stabilizer
of `σ` gives an element of the isotopy stabilizer: if `φ_t` preserves `σ` at every time, so does
`f ∘ φ_t ∘ f⁻¹`. -/
theorem mul_mul_inv_mem_isotopyStabilizer {f φ : M ≃ₘ⟮J, J⟯ M}
    (hf : f ∈ diffeomorphStabilizer σ) (hφ : φ ∈ isotopyStabilizer σ) :
    f * φ * f⁻¹ ∈ isotopyStabilizer σ := by
  obtain ⟨Φ, hΦ, rfl⟩ := hφ
  refine ⟨Φ.transDiffeomorph f, timeSlice_transDiffeomorph_mem_diffeomorphStabilizer hf hΦ, ?_⟩
  rw [Diffeotopy.final_transDiffeomorph_eq_mul_mul_inv]

/-- The isotopy stabilizer of `σ` is a normal subgroup of the stabilizer of `σ`. For a
symplectic form, the symplectomorphisms joined to the identity by a smooth symplectic isotopy form
a normal subgroup of `Symp(M, ω)`. -/
instance normal_isotopyStabilizer_subgroupOf :
    ((isotopyStabilizer σ).subgroupOf (diffeomorphStabilizer σ)).Normal :=
  (Subgroup.normal_subgroupOf_iff isotopyStabilizer_le_diffeomorphStabilizer).2
    fun _ _ hφ hf ↦ mul_mul_inv_mem_isotopyStabilizer hf hφ

/-- A diffeomorphism preserving a two-form `τ` preserves its values on pushed-forward tangent
vectors: `τ(dφ a, dφ b) = τ(a, b)`. -/
theorem eval₂_mfderiv_of_mem_diffeomorphStabilizer {τ : SmoothForm J M F 2}
    {φ : M ≃ₘ⟮J, J⟯ M} (hφ : φ ∈ diffeomorphStabilizer τ) (x : M) (a b : TangentSpace J x) :
    SmoothBundleForm.eval₂ τ (φ x) (mfderiv J J φ x a) (mfderiv J J φ x b) =
      SmoothBundleForm.eval₂ τ x a b := by
  rw [← eval₂_mpullback φ φ.contMDiff, mem_diffeomorphStabilizer.1 hφ]

/-! ### Naturality and products -/

section Naturality

variable {E' H' M' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
  {J' : ModelWithCorners ℝ E' H'} [TopologicalSpace M'] [ChartedSpace H' M'] [IsManifold J' 1 M']

/-- **Naturality of stabilizers.** If a smooth map `g` intertwines two diffeomorphisms,
`g ∘ f' = f ∘ g`, and `f` preserves `σ`, then `f'` preserves the pullback `g^* σ`. -/
theorem mem_diffeomorphStabilizer_mpullback_of_semiconj {g : M' → M} (hg : ContMDiff J' J ∞ g)
    {f' : M' ≃ₘ⟮J', J'⟯ M'} {f : M ≃ₘ⟮J, J⟯ M} (h : Function.Semiconj g f' f)
    (hf : f ∈ diffeomorphStabilizer σ) : f' ∈ diffeomorphStabilizer (mpullback g hg σ) := by
  rw [mem_diffeomorphStabilizer] at hf ⊢
  rw [mpullback_mpullback_of_comp_eq f'.contMDiff hg hg f.contMDiff h.comp_eq, hf]

/-- The product `f × f'` of a diffeomorphism `f` of `M` preserving `σ` and a diffeomorphism `f'`
of `M'` preserving `τ` preserves the form `pr₁^* σ + pr₂^* τ` on `M × M'`. -/
theorem prodCongr_mem_diffeomorphStabilizer {τ : SmoothForm J' M' F k} {f : M ≃ₘ⟮J, J⟯ M}
    {f' : M' ≃ₘ⟮J', J'⟯ M'} (hf : f ∈ diffeomorphStabilizer σ)
    (hf' : f' ∈ diffeomorphStabilizer τ) :
    f.prodCongr f' ∈ diffeomorphStabilizer
      (mpullback Prod.fst contMDiff_fst σ + mpullback Prod.snd contMDiff_snd τ) := by
  have hfst := mem_diffeomorphStabilizer_mpullback_of_semiconj contMDiff_fst
    (f' := f.prodCongr f') (fun _ ↦ by rw [Diffeomorph.coe_prodCongr, Prod.map_fst]) hf
  have hsnd := mem_diffeomorphStabilizer_mpullback_of_semiconj contMDiff_snd
    (f' := f.prodCongr f') (fun _ ↦ by rw [Diffeomorph.coe_prodCongr, Prod.map_snd]) hf'
  rw [mem_diffeomorphStabilizer] at hfst hsnd ⊢
  rw [map_add, hfst, hsnd]

/-- If diffeotopies `φ_t` of `M` and `ψ_t` of `M'` preserve `σ` and `τ` at every time, their
product `φ_t × ψ_t` preserves `pr₁^* σ + pr₂^* τ` at every time. -/
theorem timeSlice_prodCongr_mem_diffeomorphStabilizer {τ : SmoothForm J' M' F k}
    {Φ : Diffeotopy J ∞ M} {Ψ : Diffeotopy J' ∞ M'}
    (hΦ : ∀ t, Φ.timeSlice t ∈ diffeomorphStabilizer σ)
    (hΨ : ∀ t, Ψ.timeSlice t ∈ diffeomorphStabilizer τ) (t : unitInterval) :
    (Φ.prodCongr Ψ).timeSlice t ∈ diffeomorphStabilizer
      (mpullback Prod.fst contMDiff_fst σ + mpullback Prod.snd contMDiff_snd τ) := by
  rw [Diffeotopy.timeSlice_prodCongr]
  exact prodCongr_mem_diffeomorphStabilizer (hΦ t) (hΨ t)

/-- The product `f × f'` of a diffeomorphism `f` in the isotopy stabilizer of `σ` and a
diffeomorphism `f'` in the isotopy stabilizer of `τ` lies in the isotopy stabilizer of
`pr₁^* σ + pr₂^* τ`: the product of the two isotopies preserves this form at every time. -/
theorem prodCongr_mem_isotopyStabilizer {τ : SmoothForm J' M' F k} {f : M ≃ₘ⟮J, J⟯ M}
    {f' : M' ≃ₘ⟮J', J'⟯ M'} (hf : f ∈ isotopyStabilizer σ) (hf' : f' ∈ isotopyStabilizer τ) :
    f.prodCongr f' ∈ isotopyStabilizer
      (mpullback Prod.fst contMDiff_fst σ + mpullback Prod.snd contMDiff_snd τ) := by
  obtain ⟨Φ, hΦ, rfl⟩ := hf
  obtain ⟨Ψ, hΨ, rfl⟩ := hf'
  exact ⟨Φ.prodCongr Ψ, timeSlice_prodCongr_mem_diffeomorphStabilizer hΦ hΨ,
    Diffeotopy.final_prodCongr Φ Ψ⟩

end Naturality

end SmoothForm

end TauCeti

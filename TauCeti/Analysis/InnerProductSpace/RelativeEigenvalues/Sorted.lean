/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.RelativeEigenvalues.Vector
import TauCeti.LinearAlgebra.Dimension.CardEqFinrank

/-!
# The sorted eigenvalue vector of a form relative to another

For forms `h a : E → E → 𝕜`, `TauCeti.relEigenvalueVector h a` is the decreasingly sorted eigenvalue
vector of `a` relative to `h`: the antitone `μ` with `TauCeti.IsRelEigenvalueVector h a μ`. For a
positive definite Hermitian `h` and a Hermitian `a` on a finite-dimensional space it exists
(`TauCeti.exists_isRelEigenvalueVector`) and is unique
(`TauCeti.IsRelEigenvalueVector.eq_of_antitone`); otherwise the definition returns `0`. Unlike
`LinearMap.IsSymm.relEigenvalues`, which is relative to a fixed inner product, the reference form
`h` is an argument, so that it may vary, as a Hermitian metric does from point to point.

## Main definitions

* `TauCeti.relEigenvalueVector h a`: the sorted eigenvalue vector `λ_h[a]`.

## Main results

* `TauCeti.IsRelEigenvalueVector.relEigenvalueVector_eq`: an antitone eigenvalue vector is
  `λ_h[a]`.
* `TauCeti.isRelEigenvalueVector_relEigenvalueVector`: `λ_h[a]` is an eigenvalue vector.
* `TauCeti.relEigenvalueVector_self`, `TauCeti.relEigenvalueVector_zero`,
  `TauCeti.relEigenvalueVector_add_smul_self`, `TauCeti.relEigenvalueVector_smul_left`:
  `λ_h[h] = e`, `λ_h[0] = 0`, `λ_h[a + t·h] = λ_h[a] + t·e` and `λ_{s·h}[a] = s⁻¹·λ_h[a]` for
  `s > 0`; the last two need no hypothesis on `h` beyond sesquilinearity, and `λ_h[0] = 0` none.
* `TauCeti.sum_relEigenvalueVector_eq_sum_re_apply`: `Σ λ_i = Σ_j Re a(b_j, b_j)` for any
  `h`-orthonormal family `b`, the trace of `a` relative to `h`.
-/

public section

open Module

noncomputable section

namespace TauCeti

variable {𝕜 E : Type*} [RCLike 𝕜] [AddCommGroup E] [Module 𝕜 E]

open Classical in
/-- The **sorted eigenvalue vector** `λ_h[a]` of a form `a` relative to a form `h`: the antitone
`μ` with `IsRelEigenvalueVector h a μ`, which exists and is unique when `h` is positive definite
Hermitian, `a` is Hermitian and `E` is finite-dimensional. It is `0` when there is none. -/
def relEigenvalueVector (h a : E → E → 𝕜) : Fin (finrank 𝕜 E) → ℝ :=
  if hμ : ∃ μ, Antitone μ ∧ IsRelEigenvalueVector h a μ then hμ.choose else 0

open Classical in
/-- Unfolding lemma for `relEigenvalueVector`. -/
theorem relEigenvalueVector_def (h a : E → E → 𝕜) :
    relEigenvalueVector h a =
      if hμ : ∃ μ, Antitone μ ∧ IsRelEigenvalueVector h a μ then hμ.choose else 0 :=
  (rfl)

/-- The sorted eigenvalue vector is sorted decreasingly. -/
theorem antitone_relEigenvalueVector (h a : E → E → 𝕜) : Antitone (relEigenvalueVector h a) := by
  rw [relEigenvalueVector_def]
  split_ifs with hμ
  · exact hμ.choose_spec.1
  · exact fun _ _ _ ↦ le_rfl

/-- If some antitone eigenvalue vector exists, `λ_h[a]` is one. -/
theorem isRelEigenvalueVector_relEigenvalueVector_of_exists {h a : E → E → 𝕜}
    (hμ : ∃ μ, Antitone μ ∧ IsRelEigenvalueVector h a μ) :
    IsRelEigenvalueVector h a (relEigenvalueVector h a) := by
  simp only [relEigenvalueVector_def, hμ, ↓reduceDIte]
  exact hμ.choose_spec.2

/-- **`λ_h[0] = 0`** for any form `h`. -/
theorem relEigenvalueVector_zero (h : E → E → 𝕜) : relEigenvalueVector h (fun _ _ ↦ 0) = 0 := by
  rw [relEigenvalueVector_def]
  split_ifs with hμ
  · obtain ⟨b, hb⟩ := (isRelEigenvalueVector_def _ _ _).1 hμ.choose_spec.2
    funext i
    simpa using ((hb i i).2).symm
  · rfl

variable {h a : E →ₗ⋆[𝕜] E →ₗ[𝕜] 𝕜}

/-- **The sorted eigenvalue vector is the antitone eigenvalue vector.** -/
theorem IsRelEigenvalueVector.relEigenvalueVector_eq {μ : Fin (finrank 𝕜 E) → ℝ}
    (hμ : IsRelEigenvalueVector (h · ·) (a · ·) μ) (hμa : Antitone μ) :
    relEigenvalueVector (h · ·) (a · ·) = μ :=
  (isRelEigenvalueVector_relEigenvalueVector_of_exists ⟨μ, hμa, hμ⟩).eq_of_antitone
    (antitone_relEigenvalueVector _ _) hμ hμa

/-- For a positive definite Hermitian `h` and a Hermitian `a`, `λ_h[a]` is an eigenvalue vector of
`a` relative to `h`. -/
theorem isRelEigenvalueVector_relEigenvalueVector (hh : h.IsSymm)
    (hpos : ∀ v, v ≠ 0 → 0 < RCLike.re (h v v)) (ha : a.IsSymm) :
    IsRelEigenvalueVector (h · ·) (a · ·) (relEigenvalueVector (h · ·) (a · ·)) :=
  isRelEigenvalueVector_relEigenvalueVector_of_exists (exists_isRelEigenvalueVector hh hpos ha)

/-- **`λ_h[h] = e`** for a positive definite Hermitian form `h`. -/
theorem relEigenvalueVector_self (hh : h.IsSymm) (hpos : ∀ v, v ≠ 0 → 0 < RCLike.re (h v v)) :
    relEigenvalueVector (h · ·) (h · ·) = 1 := by
  obtain ⟨μ, hμa, hμ⟩ := exists_isRelEigenvalueVector hh hpos hh
  rw [hμ.relEigenvalueVector_eq hμa, ← isRelEigenvalueVector_self_iff hh hpos]
  exact hμ

/-- **`λ_h[a + t·h] = λ_h[a] + t·e`** for a positive definite Hermitian `h` and a Hermitian `a`. -/
theorem relEigenvalueVector_add_smul_self (hh : h.IsSymm)
    (hpos : ∀ v, v ≠ 0 → 0 < RCLike.re (h v v)) (ha : a.IsSymm) (t : ℝ) :
    relEigenvalueVector (h · ·) ((a + (t : 𝕜) • h) · ·) =
      relEigenvalueVector (h · ·) (a · ·) + fun _ ↦ t := by
  obtain ⟨μ, hμa, hμ⟩ := exists_isRelEigenvalueVector hh hpos ha
  rw [hμ.relEigenvalueVector_eq hμa]
  exact IsRelEigenvalueVector.relEigenvalueVector_eq
    (by simpa [RCLike.real_smul_eq_coe_mul] using hμ.add_smul_self t)
    (hμa.add_const t)

/-- **`λ_{s·h}[a] = s⁻¹·λ_h[a]`** for `s > 0`. -/
theorem relEigenvalueVector_smul_left {s : ℝ} (hs : 0 < s) :
    relEigenvalueVector (((s : 𝕜) • h) · ·) (a · ·) =
      s⁻¹ • relEigenvalueVector (h · ·) (a · ·) := by
  by_cases hμ : ∃ μ, Antitone μ ∧ IsRelEigenvalueVector (h · ·) (a · ·) μ
  · exact IsRelEigenvalueVector.relEigenvalueVector_eq
      (by simpa [RCLike.real_smul_eq_coe_mul] using
        (isRelEigenvalueVector_relEigenvalueVector_of_exists hμ).smul_left hs)
      fun i j hij ↦ smul_le_smul_of_nonneg_left (antitone_relEigenvalueVector _ _ hij)
        (inv_nonneg.2 hs.le)
  · -- rescaling by `s⁻¹`, an eigenvalue vector relative to `s·h` would give one relative to `h`
    have hν : ¬∃ ν, Antitone ν ∧ IsRelEigenvalueVector (((s : 𝕜) • h) · ·) (a · ·) ν := by
      rintro ⟨ν, hνa, hν⟩
      have hh : (fun u v ↦ ((s⁻¹ : ℝ) : 𝕜) * ((s : 𝕜) • h) u v) = (h · ·) := by
        ext u v
        simp only [LinearMap.smul_apply, smul_eq_mul, ← mul_assoc, ← RCLike.ofReal_mul,
          inv_mul_cancel₀ hs.ne', RCLike.ofReal_one, one_mul]
      refine hμ ⟨s • ν, fun i j hij ↦ smul_le_smul_of_nonneg_left (hνa hij) hs.le, ?_⟩
      simpa only [hh, inv_inv] using hν.smul_left (inv_pos.2 hs)
    simp only [relEigenvalueVector_def, hν, hμ, ↓reduceDIte, smul_zero]

/-- **The sum of the relative eigenvalues is the relative trace.** For a positive definite
Hermitian `h`, a Hermitian `a` and any family `b` that is orthonormal for `h`, `Σ_i λ_i[a]` is
`Σ_j Re a(b_j, b_j)`. -/
theorem sum_relEigenvalueVector_eq_sum_re_apply (hh : h.IsSymm)
    (hpos : ∀ v, v ≠ 0 → 0 < RCLike.re (h v v)) (ha : a.IsSymm) (b : Fin (finrank 𝕜 E) → E)
    (hb : ∀ i j, h (b i) (b j) = if i = j then 1 else 0) :
    ∑ i, relEigenvalueVector (h · ·) (a · ·) i = ∑ j, RCLike.re (a (b j) (b j)) := by
  by_cases hE : FiniteDimensional 𝕜 E
  swap
  · have : IsEmpty (Fin (finrank 𝕜 E)) :=
      Module.isEmpty_of_card_eq_finrank_of_not_finite (Fintype.card_fin _) hE
    simp
  let : NormedAddCommGroup E := (hh.innerProductCore hpos).toNormedAddCommGroup
  let : InnerProductSpace 𝕜 E := InnerProductSpace.ofCore (hh.innerProductCore hpos).toCore
  have hin : (fun u v ↦ inner 𝕜 u v) = (h · ·) := funext₂ (hh.inner_ofCore_innerProductCore hpos)
  have hon : Orthonormal 𝕜 b := orthonormal_iff_ite.2 fun i j ↦
    (hh.inner_ofCore_innerProductCore hpos _ _).trans (hb i j)
  obtain ⟨w, hw⟩ := Orthonormal.exists_orthonormalBasis_extension_of_card_eq (s := Set.univ)
    (Fintype.card_fin _).symm (hon.comp _ Subtype.val_injective)
  obtain rfl : ⇑w = b := funext fun i ↦ hw i (Set.mem_univ i)
  have hlam : IsRelEigenvalueVector (h · ·) (a · ·) (ha.relEigenvalues rfl) :=
    hin ▸ ha.isRelEigenvalueVector_relEigenvalues
  rw [hlam.relEigenvalueVector_eq (ha.relEigenvalues_antitone rfl),
    ha.sum_relEigenvalues_eq_sum_re_apply rfl w]

end TauCeti

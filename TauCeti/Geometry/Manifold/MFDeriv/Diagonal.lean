/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.MFDeriv.LocalInjectivity
public import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions

/-!
# Zeros of a displacement near the diagonal

Let `S : M × M → F` be a map into a vector space that vanishes on the diagonal, such as the
secant `(x, y) ↦ φ y - φ x` of a map `φ : M → F`. If `S` is `C^n`, `n ≠ 0`, at a diagonal point
`(x, x)` and the derivative at `x` of `y ↦ S (x, y)` is injective, then near `(x, x)` the map `S`
vanishes only on the diagonal. Indeed `(y, z) ↦ (y, S (y, z))` then has injective derivative at
`(x, x)`, hence is injective near `(x, x)` (`ContMDiffAt.exists_mem_nhds_injOn`), and it takes the
same value at `(y, z)` and at `(y, y)` exactly when `S (y, z) = 0`. For the secant of an immersion
this says that two distinct nearby points have distinct images. The manifold may have boundary or
corners.

## Main results

* `TauCeti.Manifold.eventually_eq_zero_iff_eq_of_injective_mfderiv`: near `(x, x)`,
  `S (y, z) = 0` exactly when `y = z`.
* `TauCeti.Manifold.exists_isOpen_image_diagonal_subset_and_eq_zero_iff`: the same on one open
  neighbourhood of the diagonal points over a set `D`.
* `ContMDiff.exists_isOpen_diagonal_subset_and_eq_zero_iff`: the same on an open neighbourhood of
  the whole diagonal, for a globally `C^n` map `S`.
-/

public section

open Function Set Filter
open scoped Manifold Topology

namespace TauCeti.Manifold

variable {𝕜 E H M F : Type*} [NontriviallyNormedField 𝕜] [IsRCLikeNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E] [TopologicalSpace H]
  {I : ModelWithCorners 𝕜 E H} [TopologicalSpace M] [ChartedSpace H M]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] {S : M × M → F} {n : WithTop ℕ∞}

omit [IsRCLikeNormedField 𝕜] [FiniteDimensional 𝕜 E] in
/-- If the derivative at `x` of `y ↦ S (x, y)` is injective, then so is the derivative of
`(y, z) ↦ (y, S (y, z))` at `(x, x)`. -/
private theorem injective_mfderiv_prodMk_fst {x : M}
    (hS : MDifferentiableAt (I.prod I) 𝓘(𝕜, F) S (x, x))
    (hder : Injective (mfderiv I 𝓘(𝕜, F) (fun y ↦ S (x, y)) x)) :
    Injective (mfderiv (I.prod I) (I.prod 𝓘(𝕜, F)) (fun z : M × M ↦ (z.1, S z)) (x, x)) := by
  rw [injective_iff_map_eq_zero]
  intro v hv
  rw [mfderiv_prodMk mdifferentiableAt_fst hS, mfderiv_fst] at hv
  have h₁ : v.1 = 0 := congrArg Prod.fst hv
  have h₂ : mfderiv (I.prod I) 𝓘(𝕜, F) S (x, x) v = 0 := congrArg Prod.snd hv
  rw [mfderiv_prod_eq_add_apply hS] at h₂
  simp only [h₁] at h₂
  erw [map_zero, zero_add] at h₂
  exact Prod.ext h₁ (hder (h₂.trans (map_zero _).symm))

/-- If `S` vanishes on the diagonal near `x`, is `C^n`, `n ≠ 0`, at `(x, x)`, and the derivative at
`x` of `y ↦ S (x, y)` is injective, then near `(x, x)` the map `S` vanishes exactly on the
diagonal. -/
theorem eventually_eq_zero_iff_eq_of_injective_mfderiv {x : M}
    (hS : ContMDiffAt (I.prod I) 𝓘(𝕜, F) n S (x, x)) (hn : n ≠ 0)
    (hdiag : ∀ᶠ y in 𝓝 x, S (y, y) = 0)
    (hder : Injective (mfderiv I 𝓘(𝕜, F) (fun y ↦ S (x, y)) x)) :
    ∀ᶠ z in 𝓝 (x, x), S z = 0 ↔ z.1 = z.2 := by
  obtain ⟨W, hW, hinj⟩ := (contMDiffAt_fst.prodMk hS).exists_mem_nhds_injOn hn
    (injective_mfderiv_prodMk_fst (hS.mdifferentiableAt hn) hder)
  have hfst : Tendsto (fun z : M × M ↦ (z.1, z.1)) (𝓝 (x, x)) (𝓝 (x, x)) :=
    (continuous_fst.prodMk continuous_fst).continuousAt
  filter_upwards [hW, hfst hW, continuous_fst.continuousAt.preimage_mem_nhds hdiag]
    with ⟨y, z⟩ hz hzz (hdz : S (y, y) = 0)
  refine ⟨fun h ↦ (congrArg Prod.snd (hinj hz hzz ?_)).symm, fun (h : y = z) ↦ h ▸ hdz⟩
  change (y, S (y, z)) = (y, S (y, y))
  rw [h, hdz]

/-- If `S` vanishes on the diagonal near every point of `D`, is `C^n`, `n ≠ 0`, at `(x, x)` for
`x ∈ D`, and the derivative at `x` of `y ↦ S (x, y)` is injective for `x ∈ D`, then there is an open
neighbourhood of the diagonal points over `D` on which `S` vanishes exactly on the diagonal. -/
theorem exists_isOpen_image_diagonal_subset_and_eq_zero_iff {D : Set M}
    (hS : ∀ x ∈ D, ContMDiffAt (I.prod I) 𝓘(𝕜, F) n S (x, x)) (hn : n ≠ 0)
    (hdiag : ∀ x ∈ D, ∀ᶠ y in 𝓝 x, S (y, y) = 0)
    (hder : ∀ x ∈ D, Injective (mfderiv I 𝓘(𝕜, F) (fun y ↦ S (x, y)) x)) :
    ∃ U : Set (M × M), IsOpen U ∧ (fun x ↦ (x, x)) '' D ⊆ U ∧
      ∀ x y, (x, y) ∈ U → (S (x, y) = 0 ↔ x = y) := by
  refine ⟨interior {z | S z = 0 ↔ z.1 = z.2}, isOpen_interior, ?_,
    fun x y hxy ↦ interior_subset hxy⟩
  rintro _ ⟨x, hx, rfl⟩
  exact mem_interior_iff_mem_nhds.2
    (eventually_eq_zero_iff_eq_of_injective_mfderiv (hS x hx) hn (hdiag x hx) (hder x hx))

end TauCeti.Manifold

/-- If a `C^n` map `S : M × M → F`, `n ≠ 0`, vanishes on the diagonal and the derivative at `x` of
`y ↦ S (x, y)` is injective for every `x`, then there is an open neighbourhood of the diagonal on
which `S` vanishes exactly on the diagonal. -/
theorem ContMDiff.exists_isOpen_diagonal_subset_and_eq_zero_iff {𝕜 E H M F : Type*}
    [NontriviallyNormedField 𝕜] [IsRCLikeNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [FiniteDimensional 𝕜 E] [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H} [TopologicalSpace M]
    [ChartedSpace H M] [NormedAddCommGroup F] [NormedSpace 𝕜 F] {S : M × M → F}
    {n : WithTop ℕ∞} (hS : ContMDiff (I.prod I) 𝓘(𝕜, F) n S) (hn : n ≠ 0)
    (hdiag : ∀ x, S (x, x) = 0)
    (hder : ∀ x, Injective (mfderiv I 𝓘(𝕜, F) (fun y ↦ S (x, y)) x)) :
    ∃ U : Set (M × M), IsOpen U ∧ diagonal M ⊆ U ∧
      ∀ x y, (x, y) ∈ U → (S (x, y) = 0 ↔ x = y) := by
  obtain ⟨U, hU, hDU, hzero⟩ := TauCeti.Manifold.exists_isOpen_image_diagonal_subset_and_eq_zero_iff
    (D := univ) (fun x _ ↦ hS.contMDiffAt) hn (fun _ _ ↦ Eventually.of_forall hdiag)
    (fun x _ ↦ hder x)
  refine ⟨U, hU, fun z hz ↦ ?_, hzero⟩
  obtain ⟨x, y⟩ := z
  obtain rfl : x = y := hz
  exact hDU ⟨x, mem_univ x, rfl⟩

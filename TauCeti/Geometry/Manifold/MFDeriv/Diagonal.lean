/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.MFDeriv.LocalInjectivity
import TauCeti.Geometry.Manifold.MFDeriv.Prod

/-!
# Equality with a displacement's diagonal value

Let `M` be a manifold modelled on a finite-dimensional space over `ℝ` or `ℂ` (more generally,
a field `𝕜` with `IsRCLikeNormedField 𝕜`), and let `N` be a manifold over the same field.
Suppose `S : M × M → N` is `C^n`, `n ≠ 0`, at `(x, x)` and the derivative at `x` of
`y ↦ S (x, y)` is injective. Near `(x, x)`, equality `S (y, z) = S (y, y)` then holds exactly
when `y = z`. If `S` is constant with value `c` on the diagonal near `x`, this says that
`S (y, z) = c` holds exactly on the diagonal nearby. Both manifolds may have boundary or corners.

The proof applies `ContMDiffAt.exists_mem_nhds_injOn` to `(y, z) ↦ (y, S (y, z))`, whose
injective derivative is supplied by `MDifferentiableAt.injective_mfderiv_fst_prod_iff`.
For a displacement into a normed space, with diagonal value zero, this gives a neighbourhood
where displacements between distinct points do not vanish. Such displacements include secants
`φ z - φ y` and their projections onto a frame depending on `y`.

## Main results

* `ContMDiffAt.eventually_eq_diag_iff_eq_of_mfderiv_injective`: near `(x, x)`,
  `S (y, z) = S (y, y)` exactly when `y = z`.
* `ContMDiffAt.eventually_eq_iff_eq_of_mfderiv_injective`: the constant-diagonal version.
* `TauCeti.Manifold.exists_isOpen_diag_image_subset_and_eq_diag_iff`: the same on one open
  neighbourhood of the diagonal points over a set `D`.
* `TauCeti.Manifold.exists_isOpen_diag_image_subset_and_eq_iff`: the constant-diagonal version.
* `ContMDiff.exists_isOpen_diagonal_subset_and_eq_iff`: the constant-diagonal version on an
  open neighbourhood of the whole diagonal, for a globally `C^n` map `S`.
-/

public section

open Function Set Filter
open scoped Manifold Topology

variable {𝕜 E H M F G N : Type*} [NontriviallyNormedField 𝕜] [IsRCLikeNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E] [TopologicalSpace H]
  {I : ModelWithCorners 𝕜 E H} [TopologicalSpace M] [ChartedSpace H M]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [TopologicalSpace G] {J : ModelWithCorners 𝕜 F G}
  [TopologicalSpace N] [ChartedSpace G N] {S : M × M → N} {n : WithTop ℕ∞}

/-- For manifolds over a field with `IsRCLikeNormedField`, with `M` modelled on a
finite-dimensional space, suppose `S` is `C^n`, `n ≠ 0`, at `(x, x)` and the derivative at `x`
of `y ↦ S (x, y)` is injective. Near `(x, x)`, `S (y, z) = S (y, y)` exactly when `y = z`.
The manifolds may have boundary or corners. -/
theorem ContMDiffAt.eventually_eq_diag_iff_eq_of_mfderiv_injective {x : M}
    (hS : ContMDiffAt (I.prod I) J n S (x, x)) (hn : n ≠ 0)
    (hder : Injective (mfderiv I J (fun y ↦ S (x, y)) x)) :
    ∀ᶠ z in 𝓝 (x, x), S z = S (z.1, z.1) ↔ z.1 = z.2 := by
  obtain ⟨W, hW, hinj⟩ := (contMDiffAt_fst.prodMk hS).exists_mem_nhds_injOn hn
    ((hS.mdifferentiableAt hn).injective_mfderiv_fst_prod_iff.2 hder)
  have hfst : Tendsto (fun z : M × M ↦ (z.1, z.1)) (𝓝 (x, x)) (𝓝 (x, x)) :=
    (continuous_fst.prodMk continuous_fst).continuousAt
  filter_upwards [hW, hfst hW] with ⟨y, z⟩ hz hzz
  -- `hinj` compares the graph values `(y, S (y, z))` and `(y, S (y, y))`.
  refine ⟨fun h ↦ (congrArg Prod.snd (hinj hz hzz (Prod.ext rfl h))).symm, ?_⟩
  intro h
  exact congrArg (fun w ↦ S (y, w)) h.symm

/-- For manifolds over a field with `IsRCLikeNormedField`, with `M` modelled on a
finite-dimensional space, suppose `S` is `C^n`, `n ≠ 0`, at `(x, x)`, has constant diagonal value
`c` near `x`, and the derivative at `x` of `y ↦ S (x, y)` is injective. Near `(x, x)`,
`S (y, z) = c` exactly when `y = z`. -/
theorem ContMDiffAt.eventually_eq_iff_eq_of_mfderiv_injective {x : M} {c : N}
    (hS : ContMDiffAt (I.prod I) J n S (x, x)) (hn : n ≠ 0)
    (hdiag : ∀ᶠ y in 𝓝 x, S (y, y) = c)
    (hder : Injective (mfderiv I J (fun y ↦ S (x, y)) x)) :
    ∀ᶠ z in 𝓝 (x, x), S z = c ↔ z.1 = z.2 := by
  -- Preimage membership under the first projection is the diagonal-value equality at `z.1`.
  filter_upwards [hS.eventually_eq_diag_iff_eq_of_mfderiv_injective hn hder,
    continuous_fst.continuousAt.preimage_mem_nhds hdiag] with z hz (hdz : S (z.1, z.1) = c)
  simpa only [hdz] using hz

namespace TauCeti.Manifold

/-- For manifolds over a field with `IsRCLikeNormedField`, with `M` modelled on a
finite-dimensional space, suppose `S` is `C^n`, `n ≠ 0`, at `(x, x)` for `x ∈ D`, and the
derivative at `x` of `y ↦ S (x, y)` is injective there. There is an open neighbourhood of the
diagonal points over `D` on which `S (x, y) = S (x, x)` exactly when `x = y`. -/
theorem exists_isOpen_diag_image_subset_and_eq_diag_iff {D : Set M}
    (hS : ∀ x ∈ D, ContMDiffAt (I.prod I) J n S (x, x)) (hn : n ≠ 0)
    (hder : ∀ x ∈ D, Injective (mfderiv I J (fun y ↦ S (x, y)) x)) :
    ∃ U : Set (M × M), IsOpen U ∧ Function.diag '' D ⊆ U ∧
      ∀ x y, (x, y) ∈ U → (S (x, y) = S (x, x) ↔ x = y) := by
  refine ⟨interior {z | S z = S (z.1, z.1) ↔ z.1 = z.2}, isOpen_interior, ?_,
    fun x y hxy ↦ interior_subset hxy⟩
  rintro _ ⟨x, hx, rfl⟩
  exact mem_interior_iff_mem_nhds.2
    ((hS x hx).eventually_eq_diag_iff_eq_of_mfderiv_injective hn (hder x hx))

/-- For manifolds over a field with `IsRCLikeNormedField`, with `M` modelled on a
finite-dimensional space, suppose `S` is `C^n`, `n ≠ 0`, at the diagonal points over `D`, has
constant diagonal value `c` near every point of `D`, and its derivatives in the second variable
there are injective. There is an open neighbourhood of these diagonal points on which `S (x, y) = c`
exactly when `x = y`. -/
theorem exists_isOpen_diag_image_subset_and_eq_iff {D : Set M} {c : N}
    (hS : ∀ x ∈ D, ContMDiffAt (I.prod I) J n S (x, x)) (hn : n ≠ 0)
    (hdiag : ∀ x ∈ D, ∀ᶠ y in 𝓝 x, S (y, y) = c)
    (hder : ∀ x ∈ D, Injective (mfderiv I J (fun y ↦ S (x, y)) x)) :
    ∃ U : Set (M × M), IsOpen U ∧ Function.diag '' D ⊆ U ∧
      ∀ x y, (x, y) ∈ U → (S (x, y) = c ↔ x = y) := by
  obtain ⟨U, hU, hDU, hzero⟩ := exists_isOpen_diag_image_subset_and_eq_diag_iff hS hn hder
  refine ⟨U ∩ interior {z : M × M | S (z.1, z.1) = c}, hU.inter isOpen_interior, ?_, ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    refine ⟨hDU ⟨x, hx, rfl⟩, mem_interior_iff_mem_nhds.2 ?_⟩
    -- Pulling back the diagonal-value neighbourhood along `Prod.fst` gives this set.
    have hfst : Tendsto (Prod.fst : M × M → M) (𝓝 (x, x)) (𝓝 x) :=
      continuous_fst.continuousAt
    exact hfst.eventually (hdiag x hx)
  · intro x y hxy
    have hconst : S (x, x) = c := interior_subset hxy.2
    simpa only [hconst] using hzero x y hxy.1

end TauCeti.Manifold

/-- For manifolds over a field with `IsRCLikeNormedField`, with `M` modelled on a
finite-dimensional space, suppose a `C^n` map `S`, `n ≠ 0`, has constant diagonal value `c` and
the derivative at `x` of `y ↦ S (x, y)` is injective for every `x`. There is an open neighbourhood
of the diagonal on which `S (x, y) = c` exactly when `x = y`. -/
theorem ContMDiff.exists_isOpen_diagonal_subset_and_eq_iff {c : N}
    (hS : ContMDiff (I.prod I) J n S) (hn : n ≠ 0) (hdiag : ∀ x, S (x, x) = c)
    (hder : ∀ x, Injective (mfderiv I J (fun y ↦ S (x, y)) x)) :
    ∃ U : Set (M × M), IsOpen U ∧ diagonal M ⊆ U ∧
      ∀ x y, (x, y) ∈ U → (S (x, y) = c ↔ x = y) := by
  obtain ⟨U, hU, hDU, hzero⟩ := TauCeti.Manifold.exists_isOpen_diag_image_subset_and_eq_iff
    (D := univ) (fun x _ ↦ hS.contMDiffAt) hn (fun _ _ ↦ Eventually.of_forall hdiag)
    (fun x _ ↦ hder x)
  refine ⟨U, hU, fun z hz ↦ ?_, hzero⟩
  obtain ⟨x, y⟩ := z
  obtain rfl : x = y := Set.mem_diagonal_iff.1 hz
  exact hDU ⟨x, mem_univ x, rfl⟩

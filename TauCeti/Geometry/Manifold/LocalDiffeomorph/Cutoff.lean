/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.LocalDiffeomorph
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import TauCeti.Analysis.Calculus.BumpFunction.Cutoff

/-!
# Globalizing a function read in a partial diffeomorphism

Let `φ : M ⊇ U → V` be a smooth partial diffeomorphism onto an open subset of a finite-dimensional
real normed space `V`, such as a chart, and let `f : G → M → F` be a `C^k` family of functions on
`M` depending on a parameter in a normed space `G`. Read in `φ`, the family `(t, y) ↦ f t (φ⁻¹ y)`
is only defined on the target of `φ`. Multiplying it by a cutoff equal to one near a compact subset
`K` of the target gives a `C^k` family on all of `V` which agrees with it near every point of `K`,
for all parameters, and keeps every period of `f` in the parameter
(`PartialDiffeomorph.exists_contDiff_eventuallyEq_comp_symm`). For instance a time-periodic
Hamiltonian on a manifold, read in a chart, becomes a time-periodic Hamiltonian on the model
vector space with the same Hamiltonian dynamics near `K`. The converse transplant, from a compactly
supported function on the model space to one on the manifold, is
`TauCeti.Manifold.exists_contMDiff_comp_extChartAt_symm_eq`.
-/

public section

open Function Set Filter Topology
open scoped Manifold

namespace PartialDiffeomorph

variable {E H M V G F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] [NormedAddCommGroup G]
  [NormedSpace ℝ G] [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- **Globalizing a family of functions read in a partial diffeomorphism.** Let `φ` be a `C^m`
partial diffeomorphism from `M` onto an open subset of `V`, let `f : G → M → F` be `C^k` on
`G × M` for some `k ≤ m`, and let `K` be a compact subset of the target of `φ`. Then there is a
family `g : G → V → F`, `C^k` on `G × V`, which agrees with the family read in `φ`,
`y ↦ f t (φ⁻¹ y)`, near every point of `K`, for all parameters `t`, and which keeps every period
of `f`. -/
theorem exists_contDiff_eventuallyEq_comp_symm {m : WithTop ℕ∞} {k : ℕ∞}
    (φ : PartialDiffeomorph I 𝓘(ℝ, V) M V m) (hkm : (k : WithTop ℕ∞) ≤ m) {f : G → M → F}
    (hf : ContMDiff (𝓘(ℝ, G).prod I) 𝓘(ℝ, F) k (uncurry f)) {K : Set V} (hK : IsCompact K)
    (hKφ : K ⊆ φ.target) :
    ∃ g : G → V → F, ContDiff ℝ k (uncurry g) ∧ (∀ T, Periodic f T → Periodic g T) ∧
      ∀ y ∈ K, ∀ᶠ y' in 𝓝 y, ∀ t, g t y' = f t (φ.symm y') := by
  -- The family read in `φ`, `(y, t) ↦ f t (φ⁻¹ y)`, is `C^k` on `φ.target × G`.
  have hfφ : ContDiffOn ℝ k (fun p : V × G ↦ f p.2 (φ.symm p.1)) (φ.target ×ˢ univ) := by
    rintro ⟨y, t⟩ ⟨hy, -⟩
    have hsymm : ContMDiffAt 𝓘(ℝ, V) I k φ.symm y :=
      (φ.symm.contMDiffOn.of_le hkm).contMDiffAt (φ.open_target.mem_nhds hy)
    have hpair : ContMDiffAt 𝓘(ℝ, V × G) (𝓘(ℝ, G).prod I) k
        (fun p : V × G ↦ (p.2, φ.symm p.1)) (y, t) :=
      contDiff_snd.contMDiff.contMDiffAt.prodMk
        (hsymm.comp (y, t) contDiff_fst.contMDiff.contMDiffAt)
    exact (contMDiffAt_iff_contDiffAt.1 ((hf (t, φ.symm y)).comp (y, t) hpair)).contDiffWithinAt
  obtain ⟨g, hg, hgeq, hgper⟩ := hfφ.exists_contDiff_eventually_eq_prod_univ hK φ.open_target hKφ
  exact ⟨fun t y ↦ g (y, t), hg.comp (contDiff_snd.prodMk contDiff_fst),
    fun T hT t ↦ funext fun y ↦ hgper T (fun y t ↦ congrFun (hT t) (φ.symm y)) y t, hgeq⟩

end PartialDiffeomorph

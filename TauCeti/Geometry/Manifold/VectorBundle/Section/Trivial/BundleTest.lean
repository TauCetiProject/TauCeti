/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.Section.Distribution
public import TauCeti.Geometry.Manifold.VectorBundle.Section.Trivial

/-!
# Smooth maps on a compact manifold as bundle tests

The bundle tests `TauCeti.BundleTest I F (Bundle.Trivial M F)` of the trivial bundle with fibre `F`
are the compactly supported smooth maps `M → F`. On a compact manifold every smooth map has compact
support, so they are all the smooth maps `M → F`
(`TauCeti.BundleTest.contMDiffMapEquiv`). Through this identification, operators on the smooth
maps `M → F`, such as pseudodifferential operators on a compact manifold, act on bundle tests, and
by transposition on the functionals on bundle tests, which include the distributions on `M`.

## Main declarations

* `TauCeti.BundleTest.contMDiffMapEquiv`: on a compact manifold, the real-linear identification of
  the bundle tests of the trivial bundle with fibre `F` with the smooth maps `M → F`, which keeps
  the values (`TauCeti.BundleTest.contMDiffMapEquiv_apply`,
  `TauCeti.BundleTest.contMDiffMapEquiv_symm_apply`).
-/

public noncomputable section

open Bundle ContMDiffSection
open scoped ContDiff Manifold

namespace TauCeti.BundleTest

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [CompactSpace M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

variable (I M F) in
/-- **Smooth maps on a compact manifold are bundle tests.** On a compact manifold `M`, the bundle
tests of the trivial bundle with fibre `F`, its compactly supported smooth sections, are exactly
the smooth maps `M → F`, keeping the values. -/
def contMDiffMapEquiv : BundleTest I F (Bundle.Trivial M F) ≃ₗ[ℝ] C^∞⟮I, M; 𝓘(ℝ, F), F⟯ where
  toFun s := ⟨fun x ↦ s x, (Bundle.Trivial.contMDiff_mk_iff.1 s.contMDiff).2⟩
  invFun f := ofCompactlySupported I F (Bundle.Trivial M F)
    ⟨⟨fun x ↦ f x, Bundle.Trivial.contMDiff_mk_iff.2 ⟨contMDiff_id, f.contMDiff⟩⟩,
      by simp [compactlySupported_eq_top]⟩
  map_add' _ _ := (rfl)
  map_smul' _ _ := (rfl)
  left_inv _ := (rfl)
  right_inv _ := (rfl)

@[simp]
theorem contMDiffMapEquiv_apply (s : BundleTest I F (Bundle.Trivial M F)) (x : M) :
    contMDiffMapEquiv I M F s x = s x :=
  (rfl)

@[simp]
theorem contMDiffMapEquiv_symm_apply (f : C^∞⟮I, M; 𝓘(ℝ, F), F⟯) (x : M) :
    (contMDiffMapEquiv I M F).symm f x = f x :=
  (rfl)

end TauCeti.BundleTest

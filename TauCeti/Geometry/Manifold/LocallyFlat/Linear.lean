/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import TauCeti.Geometry.Manifold.LocallyFlat.Basic

/-!
# Injective linear maps are locally flat

An injective linear map `f : F → E` of finite-dimensional real normed spaces is a locally flat
embedding, with complementary model any space `G` of the complementary dimension
(`LinearMap.isLocallyFlat_of_injective`). A complement `W` of the range of `f` and a linear
isomorphism `G ≃ W` give a linear isomorphism `(x, y) ↦ f x + y` of `F × G` onto `E`, which carries
the coordinate slice `F × {0}` onto the range of `f`.

This is the flat model against which the local flatness of other embeddings is tested; for example,
a plane through the origin in three-space is flat.

## Main results

* `LinearMap.isLocallyFlat_of_injective`: an injective linear map of finite-dimensional real normed
  spaces is locally flat with complementary model of the complementary dimension.
-/

public section

open Module Set TauCeti

variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]

/-- **An injective linear map is locally flat.** An injective linear map `f : F → E` of
finite-dimensional real normed spaces is a locally flat embedding with complementary model `G`, for
any finite-dimensional `G` with `finrank F + finrank G = finrank E`. -/
theorem LinearMap.isLocallyFlat_of_injective (f : F →ₗ[ℝ] E) (hf : Function.Injective f)
    (hdim : finrank ℝ F + finrank ℝ G = finrank ℝ E) : IsLocallyFlat F G f := by
  obtain ⟨W, hW⟩ := (LinearMap.range f).exists_isCompl
  have hWG : finrank ℝ G = finrank ℝ W := by
    have := Submodule.finrank_add_eq_of_isCompl hW
    rw [LinearMap.finrank_range_of_inj hf] at this
    omega
  /- The linear isomorphism `(x, y) ↦ f x + e y` of `F × G` onto `E`, for `e : G ≃ W`. -/
  let S : F × G ≃ₜ E :=
    (((LinearEquiv.ofInjective f hf).prodCongr (LinearEquiv.ofFinrankEq G W hWG)).trans
      (Submodule.prodEquivOfIsCompl _ _ hW)).toContinuousLinearEquiv.toHomeomorph
  convert (isLocallyFlat_prodMkLeft (N := F) (F := F) (F' := G)).homeomorph_comp S using 1
  funext x
  simp [S, Submodule.coe_prodEquivOfIsCompl']

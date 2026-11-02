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
  let e : G ≃ₗ[ℝ] W := LinearEquiv.ofFinrankEq G W hWG
  /- The linear isomorphism `(x, y) ↦ f x + e y` of `F × G` onto `E`. -/
  let S₀ : F × G →ₗ[ℝ] E := f.coprod (W.subtype ∘ₗ e.toLinearMap)
  have hS₀ (p : F × G) : S₀ p = f p.1 + (e p.2 : E) := by
    simp [S₀]
  have hS₀i : Function.Injective S₀ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro p hp
    rw [hS₀] at hp
    have hfe : f p.1 = -(e p.2 : E) := eq_neg_of_add_eq_zero_left hp
    have h0 : (e p.2 : E) = 0 := by
      refine Submodule.disjoint_def.1 hW.disjoint _ ⟨-p.1, ?_⟩ (e p.2).2
      rw [map_neg, hfe, neg_neg]
    have hy : p.2 = 0 := e.injective (Subtype.ext (by simpa using h0))
    have hx : p.1 = 0 := hf (by rw [hfe, h0, neg_zero, map_zero])
    exact Prod.ext hx hy
  have hdim' : finrank ℝ (F × G) = finrank ℝ E := by
    rw [Module.finrank_prod, hdim]
  let S : F × G ≃ₜ E :=
    (LinearMap.linearEquivOfInjective S₀ hS₀i hdim').toContinuousLinearEquiv.toHomeomorph
  convert (isLocallyFlat_prodMkLeft (N := F) (F := F) (F' := G)).homeomorph_comp S using 1
  funext x
  simp [S, hS₀]

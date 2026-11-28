/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.CoordinateRealification
public import TauCeti.LinearAlgebra.Complex.Orientation
public import TauCeti.Topology.Grassmannian.Basic
import TauCeti.Topology.Grassmannian.Orthonormal
import TauCeti.Topology.Grassmannian.Plucker

/-!
# Realification of finite Grassmannians

Forgetting complex scalars sends a complex `r`-plane in `ℂ^N` to a real `2r`-plane in
`ℝ^(2N)`. We use `TauCeti.complexPiEquivRealPi` to place the real and imaginary parts of
each coordinate next to one another. On frames the map likewise replaces each vector `v`
by the consecutive pair `v, I • v`, using `TauCeti.complexToRealFamily`.

The frame map descends along the frame-span quotients as in
`TauCeti.finiteGrassmannian.continuous_map`. The induced map is a closed embedding,
with image the real planes preserved by multiplication by `I` in complex coordinates.
-/

public section

open Set

namespace TauCeti

variable {r N : ℕ}

namespace finiteFullRankFrame

/-- The real frame underlying a complex frame, in interleaved real and imaginary coordinates. -/
noncomputable def realify (v : finiteFullRankFrame ℂ r N) :
    finiteFullRankFrame ℝ (2 * r) (2 * N) :=
  ⟨complexPiEquivRealPi N ∘ complexToRealFamily v.val, by
    have h := linearIndependent_smul Complex.basisOneI.linearIndependent v.property
    apply LinearIndependent.map' _ (complexPiEquivRealPi N).toLinearEquiv.toLinearMap
      (LinearMap.ker_eq_bot.2 (complexPiEquivRealPi N).injective)
    refine (linearIndependent_equiv' ((Equiv.prodComm _ _).trans (complexRealIndexEquiv r)) ?_).mp h
    funext ⟨k, i⟩
    exact complexToRealFamily_complexRealIndexEquiv _ i k⟩

/-- The doubled frame in ambient real coordinates. -/
@[simp] theorem coe_realify (v : finiteFullRankFrame ℂ r N) :
    v.realify.val = complexPiEquivRealPi N ∘ complexToRealFamily v.val := (rfl)

/-- Doubling a frame is continuous in all of its vectors. -/
@[fun_prop] theorem continuous_realify :
    Continuous (realify : finiteFullRankFrame ℂ r N → _) := by
  refine Continuous.subtype_mk (continuous_pi fun j ↦ ?_) _
  obtain ⟨⟨i, k⟩, rfl⟩ := (complexRealIndexEquiv r).surjective j
  simp only [Function.comp_apply, complexToRealFamily_complexRealIndexEquiv]
  apply (complexPiEquivRealPi N).continuous.comp
  exact ((continuous_apply i).comp continuous_subtypeVal).const_smul (Complex.basisOneI k)

end finiteFullRankFrame

namespace finiteGrassmannian

private theorem finrank_realify_submodule (V : Submodule ℂ (Fin N → ℂ)) :
    Module.finrank ℝ
      ((V.restrictScalars ℝ).map (complexPiEquivRealPi N).toLinearEquiv.toLinearMap) =
      2 * Module.finrank ℂ V := by
  rw [LinearEquiv.finrank_map_eq, finrank_real_eq_two_mul_finrank_complex,
    (V.restrictScalarsEquiv ℝ).finrank_eq]

/-- The underlying real plane of a complex plane, with each coordinate split into its real
and imaginary parts in that order. -/
noncomputable def realify (V : finiteGrassmannian ℂ r N) :
    finiteGrassmannian ℝ (2 * r) (2 * N) :=
  ⟨(V.val.restrictScalars ℝ).map (complexPiEquivRealPi N).toLinearEquiv.toLinearMap, by
    rw [finrank_realify_submodule, V.property]⟩

/-- The realified plane is the coordinate image of the restriction of scalars.
Use `mem_realify` to simplify membership. -/
theorem coe_realify (V : finiteGrassmannian ℂ r N) :
    V.realify.val =
      (V.val.restrictScalars ℝ).map (complexPiEquivRealPi N).toLinearEquiv.toLinearMap :=
  (rfl)

/-- A vector belongs to the realified plane exactly when its complex coordinates belong
to the original plane. -/
@[simp] theorem mem_realify {V : finiteGrassmannian ℂ r N} {x : Fin (2 * N) → ℝ} :
    x ∈ V.realify.val ↔ (complexPiEquivRealPi N).symm x ∈ V.val := by
  simp only [coe_realify, Submodule.mem_map_equiv, ContinuousLinearEquiv.coe_symm_toLinearEquiv,
    Submodule.restrictScalars_mem]

/-- Realifying a spanning frame spans the underlying real plane. -/
@[simp] theorem frameSpan_realify (v : finiteFullRankFrame ℂ r N) :
    frameSpan v.realify = (frameSpan v).realify := by
  apply Subtype.ext
  rw [coe_frameSpan, finiteFullRankFrame.coe_realify, range_comp,
    ← ContinuousLinearEquiv.coe_toLinearEquiv, Submodule.span_image_linearEquiv,
    span_range_complexToRealFamily, coe_realify, coe_frameSpan]

/-- Scalar forgetting is continuous for the frame-span quotient topologies. -/
@[fun_prop] theorem continuous_realify :
    Continuous (realify : finiteGrassmannian ℂ r N → _) := by
  apply isQuotientMap_frameSpan.continuous_iff.2
  exact (continuous_frameSpan.comp finiteFullRankFrame.continuous_realify).congr frameSpan_realify

/-- A complex plane is determined by its underlying real plane. -/
theorem realify_injective : Function.Injective (realify : finiteGrassmannian ℂ r N → _) := by
  intro V W h
  apply Subtype.ext
  apply Submodule.restrictScalars_injective ℝ ℂ (Fin N → ℂ)
  apply Submodule.map_injective_of_injective (complexPiEquivRealPi N).injective
  simpa only [coe_realify] using congrArg Subtype.val h

/-- Forgetting scalars embeds the complex Grassmannian as a closed subspace of the real one. -/
theorem isClosedEmbedding_realify :
    Topology.IsClosedEmbedding (realify : finiteGrassmannian ℂ r N → _) :=
  continuous_realify.isClosedEmbedding realify_injective

/-- A real plane comes from a complex plane exactly when it is closed under multiplication
by `I` in complex coordinates. -/
theorem mem_range_realify (W : finiteGrassmannian ℝ (2 * r) (2 * N)) :
    W ∈ range (realify : finiteGrassmannian ℂ r N → _) ↔
      ∀ z, complexPiEquivRealPi N z ∈ W.val → complexPiEquivRealPi N (Complex.I • z) ∈ W.val := by
  constructor
  · rintro ⟨V, rfl⟩
    intro z
    simpa using (V.val.smul_mem Complex.I (x := z))
  · intro h
    let P := W.val.comap (complexPiEquivRealPi N).toLinearEquiv.toLinearMap
    have hP : ∀ z ∈ P, Complex.I • z ∈ P := by
      simpa only [P, Submodule.mem_comap, LinearEquiv.coe_coe,
        ContinuousLinearEquiv.coe_toLinearEquiv] using h
    obtain ⟨V, hV⟩ := P.exists_restrictScalars_eq_iff_I_smul_mem.mpr hP
    have hmap :
        (V.restrictScalars ℝ).map (complexPiEquivRealPi N).toLinearEquiv.toLinearMap = W.val := by
      rw [hV]
      exact Submodule.map_comap_eq_of_surjective (complexPiEquivRealPi N).surjective _
    have hdim := congrArg (fun Q : Submodule ℝ (Fin (2 * N) → ℝ) ↦ Module.finrank ℝ Q) hmap
    rw [finrank_realify_submodule, W.property] at hdim
    exact ⟨⟨V, by omega⟩, Subtype.ext ((coe_realify _).trans hmap)⟩

end finiteGrassmannian

end TauCeti

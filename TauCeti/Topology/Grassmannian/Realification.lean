/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.CoordinateRealification
public import TauCeti.LinearAlgebra.Complex.Orientation
public import TauCeti.Topology.Grassmannian.Tautological
public import TauCeti.Topology.VectorBundle.Pullback
import TauCeti.Topology.FiberBundle.Pullback
import TauCeti.Topology.Grassmannian.Plucker
import TauCeti.Topology.VectorBundle.Hom

/-!
# Realification of finite Grassmannians

Forgetting complex scalars sends a complex `r`-plane in `ℂ^N` to a real `2r`-plane in
`ℝ^(2N)`. We use `TauCeti.complexPiEquivRealPi` to place the real and imaginary parts of
each coordinate next to one another. On frames the map likewise replaces each vector `v`
by the consecutive pair `v, I • v`, using `TauCeti.complexToRealFamily`.

The induced map of Grassmannians is a closed embedding for the frame-quotient topologies.
Its image consists precisely of the real planes preserved by multiplication by `I` in
the complex coordinates. Pullback along this map identifies the real tautological bundle
with the underlying real bundle of the complex tautological bundle.
-/

public section

open Bundle Set

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

/-- The underlying real plane of a complex plane, with each coordinate split into its real
and imaginary parts in that order. -/
noncomputable def realify (V : finiteGrassmannian ℂ r N) :
    finiteGrassmannian ℝ (2 * r) (2 * N) :=
  ⟨(V.val.restrictScalars ℝ).map (complexPiEquivRealPi N).toLinearEquiv.toLinearMap, by
    rw [LinearEquiv.finrank_map_eq, finrank_real_eq_two_mul_finrank_complex,
      (V.val.restrictScalarsEquiv ℝ).finrank_eq, V.property]⟩

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
  refine Submodule.eq_of_le_of_finrank_eq ?_ ((frameSpan v.realify).property.trans
    (frameSpan v).realify.property.symm)
  rw [coe_frameSpan, Submodule.span_le, range_subset_iff]
  intro j
  obtain ⟨⟨i, k⟩, rfl⟩ := (complexRealIndexEquiv r).surjective j
  simp only [SetLike.mem_coe, mem_realify, finiteFullRankFrame.coe_realify, Function.comp_apply,
    ContinuousLinearEquiv.symm_apply_apply, complexToRealFamily_complexRealIndexEquiv,
    coe_frameSpan]
  exact Submodule.smul_mem _ _ (Submodule.subset_span (mem_range_self i))

/-- Scalar forgetting is continuous for the frame-span quotient topologies. -/
@[fun_prop] theorem continuous_realify :
    Continuous (realify : finiteGrassmannian ℂ r N → _) := by
  apply isQuotientMap_frameSpan.continuous_iff.2
  exact (continuous_frameSpan.comp finiteFullRankFrame.continuous_realify).congr frameSpan_realify

/-- A complex plane is determined by its underlying real plane. -/
theorem realify_injective : Function.Injective (realify : finiteGrassmannian ℂ r N → _) := by
  intro V W h
  refine Subtype.ext <| Submodule.ext fun z ↦ ?_
  simpa only [mem_realify, ContinuousLinearEquiv.symm_apply_apply] using
    (SetLike.ext_iff.mp (congrArg Subtype.val h) (complexPiEquivRealPi N z))

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
    let V : Submodule ℂ (Fin N → ℂ) :=
      { P.toAddSubmonoid with
        smul_mem' := fun c z hz ↦ by
          rw [← Complex.re_smul_add_im_smul c z]
          exact P.add_mem (P.smul_mem c.re hz) (P.smul_mem c.im (h z hz)) }
    have hV : V.restrictScalars ℝ = P := (rfl)
    have hmap : P.map (complexPiEquivRealPi N).toLinearEquiv.toLinearMap = W.val :=
      Submodule.map_comap_eq_of_surjective (complexPiEquivRealPi N).surjective _
    have hdim := congrArg (fun Q : Submodule ℝ (Fin (2 * N) → ℝ) ↦ Module.finrank ℝ Q) hmap
    rw [LinearEquiv.finrank_map_eq, ← hV, finrank_real_eq_two_mul_finrank_complex,
      (V.restrictScalarsEquiv ℝ).finrank_eq, W.property] at hdim
    exact ⟨⟨V, by omega⟩, Subtype.ext ((coe_realify _).trans hmap)⟩

/-! ### Pullback of the real tautological bundle -/

/-- Interleaving coordinates identifies the underlying real vector space of the complex
tautological fibre with the real tautological fibre over the realified plane. -/
noncomputable def realifyTautologicalEquiv (V : finiteGrassmannian ℂ r N) :
    Tautological ℂ r N V ≃L[ℝ] Tautological ℝ (2 * r) (2 * N) V.realify :=
  (((tautologicalEquiv ℂ r N V).restrictScalars ℝ ≪≫ₗ
    (complexPiEquivRealPi N).toLinearEquiv.ofSubmodules (V.val.restrictScalars ℝ)
      V.realify.val (coe_realify V).symm) ≪≫ₗ
    (tautologicalEquiv ℝ (2 * r) (2 * N) V.realify).symm).toContinuousLinearEquiv

/-- On ambient vectors the fibre equivalence splits each complex coordinate. -/
@[simp] theorem realifyTautologicalEquiv_apply (V : finiteGrassmannian ℂ r N)
    (v : Tautological ℂ r N V) :
    (V.realifyTautologicalEquiv v).val =
      WithLp.toLp 2 (complexPiEquivRealPi N (WithLp.ofLp v.val)) := by
  let u : V.val.restrictScalars ℝ := (tautologicalEquiv ℂ r N V).restrictScalars ℝ v
  simp only [realifyTautologicalEquiv, LinearEquiv.coe_toContinuousLinearEquiv',
    LinearEquiv.trans_apply, tautologicalEquiv_symm_apply]
  calc
    _ = WithLp.toLp 2 (complexPiEquivRealPi N u.val) :=
      congrArg (WithLp.toLp 2) (LinearEquiv.ofSubmodules_apply
        (e := (complexPiEquivRealPi N).toLinearEquiv) (coe_realify V).symm u)
    _ = _ := by
      -- Restricting scalars keeps the underlying subtype value.
      have hu : u.val = WithLp.ofLp v.val := tautologicalEquiv_apply ℂ r N V v
      rw [hu]

/-- The inverse fibre equivalence recombines each pair of adjacent real coordinates. -/
@[simp] theorem realifyTautologicalEquiv_symm_apply (V : finiteGrassmannian ℂ r N)
    (w : Tautological ℝ (2 * r) (2 * N) V.realify) :
    (V.realifyTautologicalEquiv.symm w).val =
      WithLp.toLp 2 ((complexPiEquivRealPi N).symm (WithLp.ofLp w.val)) := by
  obtain ⟨v, rfl⟩ := V.realifyTautologicalEquiv.surjective w
  simp

noncomputable section

/-- Restrict the complex tautological atlas to real scalars. -/
local instance : VectorBundle ℝ (Fin r → ℂ) (Tautological ℂ r N) :=
  VectorBundle.restrictScalars ℝ ℂ (Fin r → ℂ) (Tautological ℂ r N)

/-- Pull back the real tautological atlas along scalar forgetting. -/
local instance : FiberBundle (Fin (2 * r) → ℝ)
    ((realify : finiteGrassmannian ℂ r N → _) *ᵖ (Tautological ℝ (2 * r) (2 * N))) :=
  FiberBundle.pullback (⟨realify, continuous_realify⟩ :
    C(finiteGrassmannian ℂ r N, finiteGrassmannian ℝ (2 * r) (2 * N)))

/-- The pulled-back tautological charts are real-linear on the fibres. -/
local instance : VectorBundle ℝ (Fin (2 * r) → ℝ)
    ((realify : finiteGrassmannian ℂ r N → _) *ᵖ (Tautological ℝ (2 * r) (2 * N))) :=
  VectorBundle.pullback ℝ (⟨realify, continuous_realify⟩ :
    C(finiteGrassmannian ℂ r N, finiteGrassmannian ℝ (2 * r) (2 * N)))

/-- The real tautological bundle pulls back to the underlying real bundle of the complex
tautological bundle. The homeomorphism fixes the base and is real-linear on each fibre. -/
def realifyTautologicalHomeomorph :
    TotalSpace (Fin r → ℂ) (Tautological ℂ r N) ≃ₜ TotalSpace (Fin (2 * r) → ℝ)
      ((realify : finiteGrassmannian ℂ r N → _) *ᵖ (Tautological ℝ (2 * r) (2 * N))) := by
  refine bundleHomeomorph (E₂ := realify *ᵖ (Tautological ℝ (2 * r) (2 * N)))
    realifyTautologicalEquiv ?_
  have h := (isEmbedding_totalSpace_range (Fin r → ℂ)
    (fun V : finiteGrassmannian ℂ r N ↦ V.toEuclidean.starProjection)).continuous
  refine Pullback.continuous_iff.2 ⟨continuous_fst.comp h, ?_⟩
  apply (isEmbedding_totalSpace_range _ _).continuous_iff.mpr
  refine (continuous_realify.comp (continuous_fst.comp h)).prodMk ?_
  exact ((PiLp.continuous_toLp 2 _).comp ((complexPiEquivRealPi N).continuous.comp
    ((PiLp.continuous_ofLp 2 _).comp (continuous_snd.comp h)))).congr
      fun p ↦ (realifyTautologicalEquiv_apply p.proj p.snd).symm

/-- The forward bundle comparison acts by coordinate realification in each fibre. -/
@[simp] theorem realifyTautologicalHomeomorph_apply
    (p : TotalSpace (Fin r → ℂ) (Tautological ℂ r N)) :
    realifyTautologicalHomeomorph p =
      TotalSpace.mk' (Fin (2 * r) → ℝ) p.proj (p.proj.realifyTautologicalEquiv p.snd) := by
  unfold realifyTautologicalHomeomorph
  apply bundleHomeomorph_apply

/-- The inverse bundle comparison recovers the complex vector over the same plane. -/
@[simp] theorem realifyTautologicalHomeomorph_symm_apply
    (p : TotalSpace (Fin (2 * r) → ℝ) ((realify : finiteGrassmannian ℂ r N → _) *ᵖ
      (Tautological ℝ (2 * r) (2 * N)))) :
    realifyTautologicalHomeomorph.symm p =
      TotalSpace.mk' (Fin r → ℂ) p.proj (p.proj.realifyTautologicalEquiv.symm p.snd) := by
  unfold realifyTautologicalHomeomorph
  apply bundleHomeomorph_symm_apply

end

end finiteGrassmannian

end TauCeti

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Grassmannian.Realification.Basic
public import TauCeti.Topology.Grassmannian.Tautological
public import TauCeti.Topology.VectorBundle.Pullback
import TauCeti.Topology.FiberBundle.Pullback
import TauCeti.Topology.VectorBundle.Hom

/-!
# Realification of the finite tautological bundle

Pulling back the real tautological bundle along scalar forgetting gives the underlying
real bundle of the complex tautological bundle. The fibrewise identification interleaves
the real and imaginary parts of the complex coordinates.
-/

public section

open Bundle

namespace TauCeti
namespace finiteGrassmannian

variable {r N : ℕ}

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
tautological bundle. The homeomorphism fixes the base and is real-linear on each fibre.
`Bundle.bundleHomeomorph` assembles the fibre equivalences once the forward map is continuous.
`isEmbedding_totalSpace_range` computes that continuity in the ambient product spaces. -/
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

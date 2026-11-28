/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.SmoothEmbedding.NormalSpace.Level
public import TauCeti.Geometry.Manifold.SmoothEmbedding.NormalSpace.VectorBundle.Quotient
import TauCeti.Geometry.Manifold.ContMDiff.MFDeriv
import TauCeti.Geometry.Manifold.SmoothEmbedding.NormalSpace.VectorBundle.Equiv
import TauCeti.Geometry.Manifold.VectorBundle.Pullback
import TauCeti.Geometry.Manifold.VectorBundle.Trivial

/-!
# Normal bundle trivialization along a single regular defining map

`TauCeti.SmoothEmbedding.normalBundleDiffeomorphOfLevel` trivializes the intrinsic normal
bundle when an embedded submanifold is locally a regular level of one defining map. The
trivialization is induced by the differential of the defining map via
`TauCeti.SmoothEmbedding.normalBundleDiffeomorphOfKer` and `Bundle.Trivial.diffeomorphProd`.
Its forward and inverse application lemmas identify it with the fibrewise
`TauCeti.SmoothEmbedding.normalSpaceEquivOfLevel`. At analytic order over `ℂ` it gives
a holomorphic trivialization in arbitrary codimension.
-/

public noncomputable section

open Bundle Filter Topology
open scoped ContDiff Manifold

namespace TauCeti.SmoothEmbedding

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E]
  {V : Type*} [NormedAddCommGroup V] [NormedSpace 𝕜 V] [FiniteDimensional 𝕜 V]
  {P : Type*} [NormedAddCommGroup P] [NormedSpace 𝕜 P] [FiniteDimensional 𝕜 P]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {G : Type*} [TopologicalSpace G] {J : ModelWithCorners 𝕜 V G}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {N : Type*} [TopologicalSpace N] [ChartedSpace G N]
  {n m : ℕ∞ω} [IsManifold I (m + 1) M] [IsManifold J (m + 1) N]
  (f : SmoothEmbedding I J n M N) (hm : m + 1 ≤ n) {g : N → P}
  (hg : ∀ x, ContMDiffAt J 𝓘(𝕜, P) (m + 1) g (f x))
  (hlevel : ∀ x, ∀ᶠ y in 𝓝 x, g (f y) = g (f x))
  (hreg : ∀ x, IsRegularPoint J 𝓘(𝕜, P) g (f x))
  (hdim : Module.finrank 𝕜 E + Module.finrank 𝕜 P = Module.finrank 𝕜 V)

/-- A `C^(m + 1)` defining map that is locally constant along a `C^n` embedding, regular at every
image point, and has target dimension equal to the codimension trivializes the intrinsic normal
bundle by its differential. The trivialization is a fibrewise linear `C^m` diffeomorphism over
the base when `m + 1 ≤ n`. -/
def normalBundleDiffeomorphOfLevel :
    haveI : IsManifold I 1 M := .of_le (n := m + 1) le_add_self
    haveI : IsManifold J 1 N := .of_le (n := m + 1) le_add_self
    have hn : n ≠ 0 := fun h0 ↦ by simp [h0] at hm
    letI := f.normalSpaceFiberBundle hn (P := P) (Nat.eq_sub_of_add_eq' hdim)
    TotalSpace P (fun x ↦ f.isImmersion.NormalSpace x hn) ≃ₘ^m⟮I.prod 𝓘(𝕜, P),
      I.prod 𝓘(𝕜, P)⟯ (M × P) :=
  have hn : n ≠ 0 := fun h0 ↦ by simp [h0] at hm
  haveI : IsManifold I 1 M := .of_le (n := m + 1) le_add_self
  haveI : IsManifold J 1 N := .of_le (n := m + 1) le_add_self
  letI := f.normalSpaceFiberBundle hn (P := P) (Nat.eq_sub_of_add_eq' hdim)
  have hforward : ContMDiff (I.prod 𝓘(𝕜, V)) (I.prod 𝓘(𝕜, P)) m
      (fun p : TotalSpace V ((f : M → N) *ᵖ (TangentSpace J)) ↦
        TotalSpace.mk' P (E := Trivial M P) p.proj (mfderiv J 𝓘(𝕜, P) g (f p.proj) p.snd)) := by
    apply Trivial.contMDiff_mk_iff.mpr
    refine ⟨Bundle.contMDiff_proj _, fun p ↦ ?_⟩
    have hf : ContMDiff I J m f := f.contMDiff.of_le (le_self_add.trans hm)
    have hlift := (Pullback.contMDiff_lift (E := TangentSpace J) f hf) p
    have ht := (hg p.proj).mfderiv_apply_sectionAlong
      (b := fun q : TotalSpace V ((f : M → N) *ᵖ (TangentSpace J)) ↦ f q.proj) hlift le_rfl
    simpa only [trivializationAt_model_space_apply] using (contMDiffAt_totalSpace_iff.mp ht).2
  have hker (x : M) (v : TangentSpace J (f x)) :
      mfderiv J 𝓘(𝕜, P) g (f x) v = 0 ↔ v ∈ f.isImmersion.tangentRange x hn := by
    rw [f.tangentRange_eq_ker_mfderiv x hn (hlevel x) (hreg x) hdim]
    exact LinearMap.mem_ker.symm
  have hcodim (x : M) :
      Module.finrank 𝕜 (f.isImmersion.NormalSpace x hn) = Module.finrank 𝕜 P := by
    exact (f.normalSpaceEquivOfLevel x hn (hlevel x) (hreg x) hdim).toLinearEquiv.finrank_eq
  (f.normalBundleDiffeomorphOfKer (E₂ := Trivial M P) hn hm (Nat.eq_sub_of_add_eq' hdim)
    (fun x ↦ mfderiv J 𝓘(𝕜, P) g (f x)) hker hcodim hforward).trans
    (Trivial.diffeomorphProd I M P m)

variable (p : TotalSpace P (fun x ↦ f.isImmersion.NormalSpace x (fun h0 ↦ by simp [h0] at hm))) in
/-- The trivialization of a regular level sends a normal vector to the value of the defining
differential on that normal class. -/
@[simp]
theorem normalBundleDiffeomorphOfLevel_apply :
    haveI : IsManifold I 1 M := .of_le (n := m + 1) le_add_self
    haveI : IsManifold J 1 N := .of_le (n := m + 1) le_add_self
    have hn : n ≠ 0 := fun h0 ↦ by simp [h0] at hm
    letI := f.normalSpaceFiberBundle hn (P := P) (Nat.eq_sub_of_add_eq' hdim)
    f.normalBundleDiffeomorphOfLevel hm hg hlevel hreg hdim p =
      (p.proj, f.normalSpaceEquivOfLevel p.proj hn (hlevel p.proj) (hreg p.proj) hdim p.snd) := by
  have hn : n ≠ 0 := fun h0 ↦ by simp [h0] at hm
  have : IsManifold I 1 M := .of_le (n := m + 1) le_add_self
  have : IsManifold J 1 N := .of_le (n := m + 1) le_add_self
  let := f.normalSpaceFiberBundle hn (P := P) (Nat.eq_sub_of_add_eq' hdim)
  rw [normalBundleDiffeomorphOfLevel.eq_def, Diffeomorph.coe_trans, Function.comp_apply]
  refine (congrArg (Trivial.diffeomorphProd I M P m)
    (f.normalBundleDiffeomorphOfKer_apply (E₂ := Trivial M P) hn hm
      (Nat.eq_sub_of_add_eq' hdim) (fun x ↦ mfderiv J 𝓘(𝕜, P) g (f x)) _ _ _ p)).trans ?_
  rw [Trivial.diffeomorphProd_apply]
  refine Prod.ext rfl ?_
  obtain ⟨v, hv⟩ := f.isImmersion.normalClass_surjective p.proj hn p.snd
  rw [← hv]
  exact (f.isImmersion.normalSpaceEquivOfKer_normalClass p.proj hn
    (mfderiv J 𝓘(𝕜, P) g (f p.proj)) _ _ v).trans
    (f.normalSpaceEquivOfLevel_normalClass p.proj hn (hlevel p.proj) (hreg p.proj) hdim v).symm

/-- The inverse trivialization takes the unique normal class with the prescribed defining
differential at the given base point. -/
@[simp]
theorem normalBundleDiffeomorphOfLevel_symm_apply (q : M × P) :
    haveI : IsManifold I 1 M := .of_le (n := m + 1) le_add_self
    haveI : IsManifold J 1 N := .of_le (n := m + 1) le_add_self
    have hn : n ≠ 0 := fun h0 ↦ by simp [h0] at hm
    letI := f.normalSpaceFiberBundle hn (P := P) (Nat.eq_sub_of_add_eq' hdim)
    (f.normalBundleDiffeomorphOfLevel hm hg hlevel hreg hdim).symm q =
      ⟨q.1, (f.normalSpaceEquivOfLevel q.1 hn (hlevel q.1) (hreg q.1) hdim).symm q.2⟩ := by
  have hn : n ≠ 0 := fun h0 ↦ by simp [h0] at hm
  have : IsManifold I 1 M := .of_le (n := m + 1) le_add_self
  have : IsManifold J 1 N := .of_le (n := m + 1) le_add_self
  let := f.normalSpaceFiberBundle hn (P := P) (Nat.eq_sub_of_add_eq' hdim)
  apply (f.normalBundleDiffeomorphOfLevel hm hg hlevel hreg hdim).injective
  rw [Diffeomorph.coe_toEquiv, Diffeomorph.apply_symm_apply, normalBundleDiffeomorphOfLevel_apply]
  exact Prod.ext rfl (ContinuousLinearEquiv.apply_symm_apply _ _).symm

end TauCeti.SmoothEmbedding

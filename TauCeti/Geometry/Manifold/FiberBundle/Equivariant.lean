/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.FiberBundle.Principal
public import Mathlib.Geometry.Manifold.Diffeomorph

/-!
# Equivariant equivalences of principal bundles

A fibrewise equivariant equivalence of principal bundles over the same base has a smooth inverse
as soon as its forward map is smooth. Thus one can construct principal-bundle isomorphisms without
separately checking inverse smoothness. We package the result as a native `Diffeomorph` on the
total spaces charted through the group, so that identity, composition and inverse use the existing
diffeomorphism API.

The inverse is locally expressed using a section `σ` of the source bundle and division in the
target bundle: `q ↦ σ(π(q)) · division(f(σ(π(q))), q)`.

## References

* I. Kolář, P. W. Michor, J. Slovák, *Natural Operations in Differential Geometry*, Springer,
  1993, §10.2 (principal bundle morphisms).
* S. Kobayashi, K. Nomizu, *Foundations of Differential Geometry I*, Interscience, 1963,
  Chapter I, §5.
-/

public section

open Bundle Filter MulOpposite Set
open scoped Manifold ContDiff Topology

namespace TauCeti.PrincipalBundle

variable {n : ℕ∞ω} {𝕜 B G : Type*} [NontriviallyNormedField 𝕜]
  {EB : Type*} [NormedAddCommGroup EB] [NormedSpace 𝕜 EB]
  {HB : Type*} [TopologicalSpace HB] {IB : ModelWithCorners 𝕜 EB HB}
  [TopologicalSpace B] [ChartedSpace HB B]
  {EG : Type*} [NormedAddCommGroup EG] [NormedSpace 𝕜 EG]
  {HG : Type*} [TopologicalSpace HG] {IG : ModelWithCorners 𝕜 EG HG}
  [Group G] [TopologicalSpace G] [ChartedSpace HG G]
  {P Q : B → Type*}
  [TopologicalSpace (TotalSpace G P)] [∀ b, TopologicalSpace (P b)] [FiberBundle G P]
  [∀ b, MulAction Gᵐᵒᵖ (P b)] [PrincipalBundle G P]
  [TopologicalSpace (TotalSpace G Q)] [∀ b, TopologicalSpace (Q b)] [FiberBundle G Q]
  [∀ b, MulAction Gᵐᵒᵖ (Q b)] [PrincipalBundle G Q]

/-- A fibrewise equivariant equivalence of principal bundles with a `C^n` forward map has a
`C^n` inverse. Both total spaces carry their charts through the structure group. -/
theorem contMDiff_symm_of_equivariant [LieGroup IG n G]
    (e : ∀ b, P b ≃ Q b)
    (he : ∀ b (g : G) (p : P b), e b (op g • p) = op g • e b p)
    (hf : ContMDiff (IB.prod IG) (IB.prod IG) n fun p : ManifoldTotalSpace G P ↦
      ManifoldTotalSpace.homeomorph G Q
        ⟨((ManifoldTotalSpace.homeomorph G P).symm p).proj,
          e _ ((ManifoldTotalSpace.homeomorph G P).symm p).2⟩) :
    ContMDiff (IB.prod IG) (IB.prod IG) n fun q : ManifoldTotalSpace G Q ↦
      ManifoldTotalSpace.homeomorph G P
        ⟨((ManifoldTotalSpace.homeomorph G Q).symm q).proj,
          (e _).symm ((ManifoldTotalSpace.homeomorph G Q).symm q).2⟩ := by
  classical
  have (b : B) : Nonempty (P b) := by
    obtain ⟨p, hp⟩ := FiberBundle.surjective_proj G P b
    subst b
    exact ⟨p.2⟩
  intro q
  let b₀ := ((ManifoldTotalSpace.homeomorph G Q).symm q).proj
  let t := trivializationAt G P b₀
  let σ : ∀ b, P b := fun b ↦ t.symm b 1
  have hb₀ : b₀ ∈ t.baseSet := mem_baseSet_trivializationAt G P b₀
  have hσ : ContMDiffAt IB (IB.prod IG) n
      (fun b ↦ ManifoldTotalSpace.homeomorph G P ⟨b, σ b⟩) b₀ := by
    rw [ManifoldTotalSpace.contMDiffAt_iff]
    refine ⟨contMDiffAt_id, ?_⟩
    refine (contMDiffAt_const (c := (1 : G))).congr_of_eventuallyEq ?_
    filter_upwards [t.open_baseSet.mem_nhds hb₀] with b hb
    exact congrArg Prod.snd (t.apply_mk_symm hb 1)
  have hπ := ManifoldTotalSpace.contMDiff_proj n G Q IB IG q
  have hs := hσ.comp q hπ
  have hfs : ContMDiffAt (IB.prod IG) (IB.prod IG) n
      (fun y : ManifoldTotalSpace G Q ↦ ManifoldTotalSpace.homeomorph G Q
        ⟨((ManifoldTotalSpace.homeomorph G Q).symm y).proj,
          e _ (σ ((ManifoldTotalSpace.homeomorph G Q).symm y).proj)⟩) q := by
    refine (hf.contMDiffAt.comp q hs).congr_of_eventuallyEq (.of_forall fun y ↦ ?_)
    simpa only [Function.comp_apply] using
      (congrArg (fun p : TotalSpace G P ↦
        ManifoldTotalSpace.homeomorph G Q ⟨p.proj, e _ p.2⟩)
        ((ManifoldTotalSpace.homeomorph G P).symm_apply_apply
          ⟨((ManifoldTotalSpace.homeomorph G Q).symm y).proj,
            σ ((ManifoldTotalSpace.homeomorph G Q).symm y).proj⟩)).symm
  have hq : ContMDiffAt (IB.prod IG) (IB.prod IG) n
      (fun y : ManifoldTotalSpace G Q ↦ ManifoldTotalSpace.homeomorph G Q
        ⟨((ManifoldTotalSpace.homeomorph G Q).symm y).proj,
          ((ManifoldTotalSpace.homeomorph G Q).symm y).2⟩) q := by
    convert (contMDiffAt_id (I := IB.prod IG) (n := n) (x := q)) using 1
    funext y
    exact (ManifoldTotalSpace.homeomorph G Q).apply_symm_apply y
  have hd := hfs.division hq
  refine (hs.totalSpaceMk_smul hd).congr_of_eventuallyEq (Filter.Eventually.of_forall ?_)
  intro y
  apply congrArg (ManifoldTotalSpace.homeomorph G P)
  apply congrArg (TotalSpace.mk _)
  apply (e _).injective
  simp only [Equiv.apply_symm_apply, he, smul_division]

variable (G) in
/-- The diffeomorphism of total spaces determined by a smooth fibrewise equivariant equivalence.
No separate smoothness hypothesis on the inverse is required. -/
def diffeomorphOfEquivariant [LieGroup IG n G]
    (e : ∀ b, P b ≃ Q b)
    (he : ∀ b (g : G) (p : P b), e b (op g • p) = op g • e b p)
    (hf : ContMDiff (IB.prod IG) (IB.prod IG) n fun p : ManifoldTotalSpace G P ↦
      ManifoldTotalSpace.homeomorph G Q
        ⟨((ManifoldTotalSpace.homeomorph G P).symm p).proj,
          e _ ((ManifoldTotalSpace.homeomorph G P).symm p).2⟩) :
    Diffeomorph (IB.prod IG) (IB.prod IG) (ManifoldTotalSpace G P) (ManifoldTotalSpace G Q) n where
  toFun p := ManifoldTotalSpace.homeomorph G Q
    ⟨((ManifoldTotalSpace.homeomorph G P).symm p).proj,
      e _ ((ManifoldTotalSpace.homeomorph G P).symm p).2⟩
  invFun q := ManifoldTotalSpace.homeomorph G P
    ⟨((ManifoldTotalSpace.homeomorph G Q).symm q).proj,
      (e _).symm ((ManifoldTotalSpace.homeomorph G Q).symm q).2⟩
  left_inv p := by
    have h := congrArg (fun q : TotalSpace G Q ↦
      ManifoldTotalSpace.homeomorph G P ⟨q.proj, (e _).symm q.2⟩)
      ((ManifoldTotalSpace.homeomorph G Q).symm_apply_apply
        ⟨((ManifoldTotalSpace.homeomorph G P).symm p).proj,
          e _ ((ManifoldTotalSpace.homeomorph G P).symm p).2⟩)
    exact h.trans (by simp only [Equiv.symm_apply_apply, TotalSpace.eta,
      Homeomorph.apply_symm_apply])
  right_inv q := by
    have h := congrArg (fun p : TotalSpace G P ↦
      ManifoldTotalSpace.homeomorph G Q ⟨p.proj, e _ p.2⟩)
      ((ManifoldTotalSpace.homeomorph G P).symm_apply_apply
        ⟨((ManifoldTotalSpace.homeomorph G Q).symm q).proj,
          (e _).symm ((ManifoldTotalSpace.homeomorph G Q).symm q).2⟩)
    exact h.trans (by simp only [Equiv.apply_symm_apply, TotalSpace.eta,
      Homeomorph.apply_symm_apply])
  contMDiff_toFun := hf
  contMDiff_invFun := contMDiff_symm_of_equivariant e he hf

section

variable [LieGroup IG n G] (e : ∀ b, P b ≃ Q b)
  (he : ∀ b (g : G) (p : P b), e b (op g • p) = op g • e b p)
  (hf : ContMDiff (IB.prod IG) (IB.prod IG) n fun p : ManifoldTotalSpace G P ↦
    ManifoldTotalSpace.homeomorph G Q
      ⟨((ManifoldTotalSpace.homeomorph G P).symm p).proj,
        e _ ((ManifoldTotalSpace.homeomorph G P).symm p).2⟩)

/-- On each fibre the induced diffeomorphism is the given equivalence. -/
@[simp]
theorem diffeomorphOfEquivariant_apply (p : TotalSpace G P) :
    diffeomorphOfEquivariant G e he hf (ManifoldTotalSpace.homeomorph G P p) =
      ManifoldTotalSpace.homeomorph G Q ⟨p.proj, e _ p.2⟩ := by
  exact congrArg (fun p : TotalSpace G P ↦
    ManifoldTotalSpace.homeomorph G Q ⟨p.proj, e _ p.2⟩)
    ((ManifoldTotalSpace.homeomorph G P).symm_apply_apply p)

/-- On each fibre the inverse diffeomorphism is the inverse equivalence. -/
@[simp]
theorem diffeomorphOfEquivariant_symm_apply (q : TotalSpace G Q) :
    (diffeomorphOfEquivariant G e he hf).symm (ManifoldTotalSpace.homeomorph G Q q) =
      ManifoldTotalSpace.homeomorph G P ⟨q.proj, (e _).symm q.2⟩ := by
  exact congrArg (fun q : TotalSpace G Q ↦
    ManifoldTotalSpace.homeomorph G P ⟨q.proj, (e _).symm q.2⟩)
    ((ManifoldTotalSpace.homeomorph G Q).symm_apply_apply q)

end

end TauCeti.PrincipalBundle

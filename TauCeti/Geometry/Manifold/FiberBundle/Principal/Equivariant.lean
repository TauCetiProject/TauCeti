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
open TauCeti.ManifoldTotalSpace
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
    (hf : ContMDiff (IB.prod IG) (IB.prod IG) n (fiberwiseMap (F := G) fun b ↦ e b)) :
    ContMDiff (IB.prod IG) (IB.prod IG) n (fiberwiseMap (F := G) fun b ↦ (e b).symm) := by
  classical
  have (b : B) : Nonempty (P b) := ⟨(FiberBundle.homeomorphAt G P b).symm 1⟩
  intro q
  let b₀ := ((ManifoldTotalSpace.homeomorph G Q).symm q).proj
  let t := trivializationAt G P b₀
  let σ : ∀ b, P b := fun b ↦ t.symm b 1
  have hσ : ContMDiffAt IB (IB.prod IG) n
      (fun b ↦ ManifoldTotalSpace.homeomorph G P ⟨b, σ b⟩) b₀ :=
    contMDiffAt_totalSpaceMk_trivializationAt_symm b₀ 1
  have hπ := ManifoldTotalSpace.contMDiff_proj n G Q IB IG q
  have hs := hσ.comp q hπ
  have hfs : ContMDiffAt (IB.prod IG) (IB.prod IG) n
      (fun y : ManifoldTotalSpace G Q ↦ ManifoldTotalSpace.homeomorph G Q
        ⟨((ManifoldTotalSpace.homeomorph G Q).symm y).proj,
          e _ (σ ((ManifoldTotalSpace.homeomorph G Q).symm y).proj)⟩) q := by
    simpa only [Function.comp_def, fiberwiseMap_homeomorph] using hf.contMDiffAt.comp q hs
  have hq : ContMDiffAt (IB.prod IG) (IB.prod IG) n
      (fun y : ManifoldTotalSpace G Q ↦ ManifoldTotalSpace.homeomorph G Q
        ⟨((ManifoldTotalSpace.homeomorph G Q).symm y).proj,
          ((ManifoldTotalSpace.homeomorph G Q).symm y).2⟩) q := by
    exact contMDiffAt_id.congr_of_eventuallyEq (.of_forall fun y ↦ by
      simp only [TotalSpace.eta, Homeomorph.apply_symm_apply, id_eq])
  have hd := hfs.division hq
  refine (hs.totalSpaceMk_smul hd).congr_of_eventuallyEq (Filter.Eventually.of_forall ?_)
  intro y
  apply (ManifoldTotalSpace.homeomorph G P).symm.injective
  simp only [Homeomorph.symm_apply_apply, homeomorph_symm_fiberwiseMap]
  apply congrArg (TotalSpace.mk _)
  apply (e _).injective
  simp only [Equiv.apply_symm_apply, he, smul_division]

omit [TopologicalSpace G] in
/-- The inverse of an equivalence from `G` that intertwines right multiplication with a right
action of `G` intertwines them too. -/
theorem symm_op_smul_of_equivariant {X : Type*} [MulAction Gᵐᵒᵖ X] (e : G ≃ X)
    (he : ∀ v g : G, e (v * g) = op g • e v) (g : G) (x : X) :
    e.symm (op g • x) = e.symm x * g := by
  rw [Equiv.symm_apply_eq, he, Equiv.apply_symm_apply]

variable (G) in
/-- The diffeomorphism of total spaces determined by a smooth fibrewise equivariant equivalence.
No separate smoothness hypothesis on the inverse is required. -/
def diffeomorphOfEquivariant [LieGroup IG n G]
    (e : ∀ b, P b ≃ Q b)
    (he : ∀ b (g : G) (p : P b), e b (op g • p) = op g • e b p)
    (hf : ContMDiff (IB.prod IG) (IB.prod IG) n (fiberwiseMap (F := G) fun b ↦ e b)) :
    Diffeomorph (IB.prod IG) (IB.prod IG) (ManifoldTotalSpace G P) (ManifoldTotalSpace G Q) n where
  toFun := fiberwiseMap fun b ↦ e b
  invFun := fiberwiseMap fun b ↦ (e b).symm
  left_inv p := by
    obtain ⟨p, rfl⟩ := (ManifoldTotalSpace.homeomorph G P).surjective p
    simp
  right_inv q := by
    obtain ⟨q, rfl⟩ := (ManifoldTotalSpace.homeomorph G Q).surjective q
    simp
  contMDiff_toFun := hf
  contMDiff_invFun := contMDiff_symm_of_equivariant e he hf

section

variable [LieGroup IG n G] (e : ∀ b, P b ≃ Q b)
  (he : ∀ b (g : G) (p : P b), e b (op g • p) = op g • e b p)
  (hf : ContMDiff (IB.prod IG) (IB.prod IG) n (fiberwiseMap (F := G) fun b ↦ e b))

/-- On each fibre the induced diffeomorphism is the given equivalence. -/
@[simp]
theorem diffeomorphOfEquivariant_apply (p : TotalSpace G P) :
    diffeomorphOfEquivariant G e he hf (ManifoldTotalSpace.homeomorph G P p) =
      ManifoldTotalSpace.homeomorph G Q ⟨p.proj, e _ p.2⟩ := by
  exact fiberwiseMap_homeomorph (fun b ↦ e b) p

/-- On each fibre the inverse diffeomorphism is the inverse equivalence. -/
@[simp]
theorem diffeomorphOfEquivariant_symm_apply (q : TotalSpace G Q) :
    (diffeomorphOfEquivariant G e he hf).symm (ManifoldTotalSpace.homeomorph G Q q) =
      ManifoldTotalSpace.homeomorph G P ⟨q.proj, (e _).symm q.2⟩ := by
  exact fiberwiseMap_homeomorph (fun b ↦ (e b).symm) q

/-- Reading the induced diffeomorphism in the original total space gives the fibre equivalence
at any point of the charted total space. -/
@[simp]
theorem homeomorph_symm_diffeomorphOfEquivariant_apply (x : ManifoldTotalSpace G P) :
    (ManifoldTotalSpace.homeomorph G Q).symm (diffeomorphOfEquivariant G e he hf x) =
      ⟨((ManifoldTotalSpace.homeomorph G P).symm x).proj,
        e _ ((ManifoldTotalSpace.homeomorph G P).symm x).2⟩ :=
  homeomorph_symm_fiberwiseMap (fun b ↦ e b) x

/-- Reading the inverse diffeomorphism in the original total space gives the inverse fibre
equivalence at any point of the charted total space. -/
@[simp]
theorem homeomorph_symm_diffeomorphOfEquivariant_symm_apply (y : ManifoldTotalSpace G Q) :
    (ManifoldTotalSpace.homeomorph G P).symm ((diffeomorphOfEquivariant G e he hf).symm y) =
      ⟨((ManifoldTotalSpace.homeomorph G Q).symm y).proj,
        (e _).symm ((ManifoldTotalSpace.homeomorph G Q).symm y).2⟩ :=
  homeomorph_symm_fiberwiseMap (fun b ↦ (e b).symm) y

/-- The induced diffeomorphism lies over the identity on the base. -/
theorem diffeomorphOfEquivariant_proj (x : ManifoldTotalSpace G P) :
    ((ManifoldTotalSpace.homeomorph G Q).symm (diffeomorphOfEquivariant G e he hf x)).proj =
      ((ManifoldTotalSpace.homeomorph G P).symm x).proj := by
  rw [homeomorph_symm_diffeomorphOfEquivariant_apply]

/-- The inverse diffeomorphism lies over the identity on the base. -/
theorem diffeomorphOfEquivariant_symm_proj (y : ManifoldTotalSpace G Q) :
    ((ManifoldTotalSpace.homeomorph G P).symm ((diffeomorphOfEquivariant G e he hf).symm y)).proj =
      ((ManifoldTotalSpace.homeomorph G Q).symm y).proj := by
  rw [homeomorph_symm_diffeomorphOfEquivariant_symm_apply]

/-- `diffeomorphOfEquivariant` is equivariant for the right `G`-actions on the charted total
spaces. -/
theorem diffeomorphOfEquivariant_op_smul (g : G) (x : ManifoldTotalSpace G P) :
    diffeomorphOfEquivariant G e he hf (op g • x) =
      op g • diffeomorphOfEquivariant G e he hf x := by
  obtain ⟨⟨b, p⟩, rfl⟩ := (ManifoldTotalSpace.homeomorph G P).surjective x
  simp [he]

end

end TauCeti.PrincipalBundle

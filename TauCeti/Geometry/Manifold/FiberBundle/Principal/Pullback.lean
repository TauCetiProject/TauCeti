/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.FiberBundle.Principal.Equivariant
public import TauCeti.Topology.FiberBundle.Principal.Pullback
import TauCeti.Geometry.Manifold.FiberBundle.Pullback.Map

/-!
# Pullbacks of smooth principal-bundle isomorphisms

A principal-bundle equivalence with smooth forward map induces a diffeomorphism of the pullback
total spaces along a smooth map. This restricts smooth principal-bundle isomorphisms to open
subsets: take the base map to be the smooth inclusion `Subtype.val`. The fibre formula and lift
compatibility characterize the operation, and restriction commutes with identity, composition,
and inverse through the native `Diffeomorph` operations.
-/

public section

open Bundle MulOpposite TauCeti.ManifoldTotalSpace
open scoped Manifold ContDiff

namespace TauCeti.PrincipalBundle.Equiv

variable {n : ℕ∞ω} {𝕜 B B' G : Type*} [NontriviallyNormedField 𝕜]
  {EB : Type*} [NormedAddCommGroup EB] [NormedSpace 𝕜 EB]
  {HB : Type*} [TopologicalSpace HB] {IB : ModelWithCorners 𝕜 EB HB}
  [TopologicalSpace B] [ChartedSpace HB B]
  {EB' : Type*} [NormedAddCommGroup EB'] [NormedSpace 𝕜 EB']
  {HB' : Type*} [TopologicalSpace HB'] {IB' : ModelWithCorners 𝕜 EB' HB'}
  [TopologicalSpace B'] [ChartedSpace HB' B']
  {EG : Type*} [NormedAddCommGroup EG] [NormedSpace 𝕜 EG]
  {HG : Type*} [TopologicalSpace HG] {IG : ModelWithCorners 𝕜 EG HG}
  [Group G] [TopologicalSpace G] [ChartedSpace HG G]
  {P Q : B → Type*}
  [TopologicalSpace (TotalSpace G P)] [∀ b, TopologicalSpace (P b)] [FiberBundle G P]
  [∀ b, MulAction Gᵐᵒᵖ (P b)] [PrincipalBundle G P]
  [TopologicalSpace (TotalSpace G Q)] [∀ b, TopologicalSpace (Q b)] [FiberBundle G Q]
  [∀ b, MulAction Gᵐᵒᵖ (Q b)] [PrincipalBundle G Q]

/-- Supply the canonical pullback bundle instance for the charted total-space signatures.
The group model supplies the nonempty fibres required by the canonical construction. -/
noncomputable local instance {E : B → Type*}
    [TopologicalSpace (TotalSpace G E)] [∀ b, TopologicalSpace (E b)] [FiberBundle G E]
    {K : Type*} [FunLike K B' B] [ContinuousMapClass K B' B] (f : K) :
    FiberBundle G ((f : B' → B) *ᵖ E) := by
  have (b : B) : Nonempty (E b) := ⟨(FiberBundle.homeomorphAt G E b).symm 1⟩
  exact FiberBundle.pullback f

variable (ψ : PrincipalBundle.Equiv G P Q) (f : C^n⟮IB', B'; IB, B⟯)
  (hψ : ContMDiff (IB.prod IG) (IB.prod IG) n (fiberwiseMap (F := G) fun b ↦ ψ.toEquiv b))

/-- Pull back a smooth principal-bundle isomorphism to a diffeomorphism of charted total spaces.
Smoothness of the inverse follows from equivariance. -/
noncomputable def diffeomorphPullback [LieGroup IG n G] :
    Diffeomorph (IB'.prod IG) (IB'.prod IG)
      (ManifoldTotalSpace G ((f : B' → B) *ᵖ P))
      (ManifoldTotalSpace G ((f : B' → B) *ᵖ Q)) n := by
  have (b : B) : Nonempty (P b) := ⟨(FiberBundle.homeomorphAt G P b).symm 1⟩
  have (b : B) : Nonempty (Q b) := ⟨(FiberBundle.homeomorphAt G Q b).symm 1⟩
  have hEquiv : (ψ.pullback f).toEquiv = (fun b ↦ ψ.toEquiv (f b)) :=
    funext (pullback_toEquiv ψ f)
  exact diffeomorphOfEquivariant (P := (f : B' → B) *ᵖ P) (Q := (f : B' → B) *ᵖ Q) G
    (ψ.pullback f).toEquiv (fun b g p ↦ (ψ.pullback f).map_smul b p g)
    (by
      rw [hEquiv]
      exact contMDiff_fiberwiseMap_pullback f f.contMDiff hψ)

variable [LieGroup IG n G]

/-- The pulled-back diffeomorphism uses the original equivalence at the image base point. -/
@[simp]
theorem diffeomorphPullback_apply (p : TotalSpace G ((f : B' → B) *ᵖ P)) :
    ψ.diffeomorphPullback f hψ (homeomorph G ((f : B' → B) *ᵖ P) p) =
      homeomorph G ((f : B' → B) *ᵖ Q) ⟨p.proj, ψ.toEquiv (f p.proj) p.snd⟩ := by
  dsimp only [diffeomorphPullback]
  rw [diffeomorphOfEquivariant_apply, pullback_toEquiv]
  rfl

/-- The inverse of the pulled-back diffeomorphism uses the original inverse in each fibre. -/
@[simp]
theorem diffeomorphPullback_symm_apply (q : TotalSpace G ((f : B' → B) *ᵖ Q)) :
    (ψ.diffeomorphPullback f hψ).symm (homeomorph G ((f : B' → B) *ᵖ Q) q) =
      homeomorph G ((f : B' → B) *ᵖ P) ⟨q.proj, (ψ.toEquiv (f q.proj)).symm q.snd⟩ := by
  dsimp only [diffeomorphPullback]
  rw [diffeomorphOfEquivariant_symm_apply, pullback_toEquiv]
  rfl

/-- The pulled-back diffeomorphism preserves the point of the new base. -/
theorem diffeomorphPullback_proj (x : ManifoldTotalSpace G ((f : B' → B) *ᵖ P)) :
    ((homeomorph G ((f : B' → B) *ᵖ Q)).symm (ψ.diffeomorphPullback f hψ x)).proj =
      ((homeomorph G ((f : B' → B) *ᵖ P)).symm x).proj := by
  exact diffeomorphOfEquivariant_proj (IB := IB') (IG := IG) _ _ _ x

/-- The pulled-back diffeomorphism preserves the right action on arbitrary charted points. -/
theorem diffeomorphPullback_op_smul (g : G)
    (x : ManifoldTotalSpace G ((f : B' → B) *ᵖ P)) :
    ψ.diffeomorphPullback f hψ (op g • x) = op g • ψ.diffeomorphPullback f hψ x := by
  exact diffeomorphOfEquivariant_op_smul (IB := IB') (IG := IG) _ _ _ g x

/-- Lifting after the pulled-back isomorphism agrees with the original isomorphism after lifting.
Both lifts are read in their original total spaces. -/
theorem diffeomorphPullback_lift (x : ManifoldTotalSpace G ((f : B' → B) *ᵖ P)) :
    homeomorph G Q (Pullback.lift f ((homeomorph G ((f : B' → B) *ᵖ Q)).symm
      (ψ.diffeomorphPullback f hψ x))) =
      diffeomorphOfEquivariant G ψ.toEquiv (fun b g p ↦ ψ.map_smul b p g) hψ
        (homeomorph G P (Pullback.lift f
          ((homeomorph G ((f : B' → B) *ᵖ P)).symm x))) := by
  obtain ⟨p, rfl⟩ := (homeomorph G ((f : B' → B) *ᵖ P)).surjective x
  rw [ψ.diffeomorphPullback_apply f hψ p]
  rw [(homeomorph G ((f : B' → B) *ᵖ Q)).symm_apply_apply]
  rw [(homeomorph G ((f : B' → B) *ᵖ P)).symm_apply_apply]
  exact (diffeomorphOfEquivariant_apply ψ.toEquiv
    (fun b g p ↦ ψ.map_smul b p g) hψ (Pullback.lift f p)).symm

/-- Pullback of the identity is the identity diffeomorphism. -/
@[simp]
theorem diffeomorphPullback_refl :
    (refl G P).diffeomorphPullback f (by
      refine contMDiff_id.congr fun x ↦ ?_
      obtain ⟨p, rfl⟩ := (homeomorph G P).surjective x
      simp) =
      Diffeomorph.refl (IB'.prod IG) (ManifoldTotalSpace G ((f : B' → B) *ᵖ P)) n := by
  dsimp only [diffeomorphPullback]
  apply Eq.trans ?_ (diffeomorphOfEquivariant_refl (n := n) (IB := IB') (IG := IG)
    (P := (f : B' → B) *ᵖ P))
  congr 1
  funext b
  rw [pullback_refl, refl_toEquiv]

/-- Pullback commutes with inverse, using the smooth inverse provided by equivariance. -/
theorem diffeomorphPullback_symm :
    ψ.symm.diffeomorphPullback f (by
      simpa only [symm_toEquiv] using contMDiff_symm_of_equivariant ψ.toEquiv
        (fun b g p ↦ ψ.map_smul b p g) hψ) = (ψ.diffeomorphPullback f hψ).symm := by
  dsimp only [diffeomorphPullback]
  apply Eq.trans ?_ (diffeomorphOfEquivariant_symm (IB := IB') (IG := IG)
    (ψ.pullback f).toEquiv (fun b g p ↦ (ψ.pullback f).map_smul b p g) _)
  congr 1
  funext b
  rw [pullback_symm, symm_toEquiv]

variable {R : B → Type*}
  [TopologicalSpace (TotalSpace G R)] [∀ b, TopologicalSpace (R b)] [FiberBundle G R]
  [∀ b, MulAction Gᵐᵒᵖ (R b)] [PrincipalBundle G R]

/-- Pullback commutes with composition of smooth principal-bundle isomorphisms. -/
theorem diffeomorphPullback_trans (φ : PrincipalBundle.Equiv G Q R)
    (hφ : ContMDiff (IB.prod IG) (IB.prod IG) n (fiberwiseMap (F := G) fun b ↦ φ.toEquiv b)) :
    (ψ.trans φ).diffeomorphPullback f (by
      refine (hφ.fiberwiseMap_comp hψ).congr ?_
      intro x
      obtain ⟨p, rfl⟩ := (homeomorph G P).surjective x
      simp [Function.comp_def]) =
      (ψ.diffeomorphPullback f hψ).trans (φ.diffeomorphPullback f hφ) := by
  dsimp only [diffeomorphPullback]
  apply Eq.trans ?_ (diffeomorphOfEquivariant_trans (IB := IB') (IG := IG)
    (ψ.pullback f).toEquiv (fun b g p ↦ (ψ.pullback f).map_smul b p g) _
    (φ.pullback f).toEquiv (fun b g q ↦ (φ.pullback f).map_smul b q g) _)
  congr 1
  funext b
  rw [pullback_trans, trans_toEquiv]

end TauCeti.PrincipalBundle.Equiv

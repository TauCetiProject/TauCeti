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

variable [∀ b, Nonempty (P b)] [∀ b, Nonempty (Q b)]

variable (ψ : PrincipalBundle.Equiv G P Q) (f : C^n⟮IB', B'; IB, B⟯)
  (hψ : ContMDiff (IB.prod IG) (IB.prod IG) n (fiberwiseMap (F := G) fun b ↦ ψ.toEquiv b))

/-- Pull back a smooth principal-bundle isomorphism to a diffeomorphism of charted total spaces.
Smoothness of the inverse follows from equivariance. -/
noncomputable def diffeomorphPullback [LieGroup IG n G] :
    Diffeomorph (IB'.prod IG) (IB'.prod IG)
      (ManifoldTotalSpace G ((f : B' → B) *ᵖ P))
      (ManifoldTotalSpace G ((f : B' → B) *ᵖ Q)) n :=
  diffeomorphOfEquivariant (P := (f : B' → B) *ᵖ P) (Q := (f : B' → B) *ᵖ Q) G
    (fun b ↦ ψ.toEquiv (f b)) (fun b g p ↦ ψ.map_smul (f b) p g)
    (contMDiff_fiberwiseMap_pullback f f.contMDiff hψ)

variable [LieGroup IG n G]

/-- The pulled-back diffeomorphism uses the original equivalence at the image base point. -/
@[simp]
theorem diffeomorphPullback_apply (p : TotalSpace G ((f : B' → B) *ᵖ P)) :
    ψ.diffeomorphPullback f hψ (homeomorph G ((f : B' → B) *ᵖ P) p) =
      homeomorph G ((f : B' → B) *ᵖ Q) ⟨p.proj, ψ.toEquiv (f p.proj) p.snd⟩ := by
  exact diffeomorphOfEquivariant_apply (IB := IB') (IG := IG) _ _ _ p

/-- The inverse of the pulled-back diffeomorphism uses the original inverse in each fibre. -/
@[simp]
theorem diffeomorphPullback_symm_apply (q : TotalSpace G ((f : B' → B) *ᵖ Q)) :
    (ψ.diffeomorphPullback f hψ).symm (homeomorph G ((f : B' → B) *ᵖ Q) q) =
      homeomorph G ((f : B' → B) *ᵖ P) ⟨q.proj, (ψ.toEquiv (f q.proj)).symm q.snd⟩ := by
  exact diffeomorphOfEquivariant_symm_apply (IB := IB') (IG := IG) _ _ _ q

/-- The pulled-back diffeomorphism preserves the point of the new base. -/
theorem diffeomorphPullback_proj (x : ManifoldTotalSpace G ((f : B' → B) *ᵖ P)) :
    ((homeomorph G ((f : B' → B) *ᵖ Q)).symm (ψ.diffeomorphPullback f hψ x)).proj =
      ((homeomorph G ((f : B' → B) *ᵖ P)).symm x).proj := by
  exact diffeomorphOfEquivariant_proj (IB := IB') (IG := IG) _ _ _ x

/-- The pulled-back diffeomorphism preserves the right action on arbitrary charted points. -/
theorem diffeomorphPullback_op_smul (g : G)
    (x : ManifoldTotalSpace G ((f : B' → B) *ᵖ P)) :
    ψ.diffeomorphPullback f hψ (op g • x) = op g • ψ.diffeomorphPullback f hψ x := by
  obtain ⟨p, rfl⟩ := (homeomorph G ((f : B' → B) *ᵖ P)).surjective x
  simp only [smul_homeomorph, diffeomorphPullback_apply, EmbeddingLike.apply_eq_iff_eq]
  exact congrArg (TotalSpace.mk p.proj) (ψ.map_smul (f p.proj) p.snd g)

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
  apply Diffeomorph.ext
  intro x
  obtain ⟨p, rfl⟩ := (homeomorph G ((f : B' → B) *ᵖ P)).surjective x
  simp
  rfl

/-- Pullback commutes with inverse, using the smooth inverse provided by equivariance. -/
theorem diffeomorphPullback_symm :
    ψ.symm.diffeomorphPullback f (by
      simpa only [symm_toEquiv] using contMDiff_symm_of_equivariant ψ.toEquiv
        (fun b g p ↦ ψ.map_smul b p g) hψ) = (ψ.diffeomorphPullback f hψ).symm := by
  apply Diffeomorph.ext
  intro x
  obtain ⟨q, rfl⟩ := (homeomorph G ((f : B' → B) *ᵖ Q)).surjective x
  rw [ψ.symm.diffeomorphPullback_apply f _ q, ψ.diffeomorphPullback_symm_apply f hψ q]
  simp

variable {R : B → Type*}
  [TopologicalSpace (TotalSpace G R)] [∀ b, TopologicalSpace (R b)] [FiberBundle G R]
  [∀ b, MulAction Gᵐᵒᵖ (R b)] [PrincipalBundle G R] [∀ b, Nonempty (R b)]

/-- Pullback commutes with composition of smooth principal-bundle isomorphisms. -/
theorem diffeomorphPullback_trans (φ : PrincipalBundle.Equiv G Q R)
    (hφ : ContMDiff (IB.prod IG) (IB.prod IG) n (fiberwiseMap (F := G) fun b ↦ φ.toEquiv b)) :
    (ψ.trans φ).diffeomorphPullback f (by
      refine (hφ.fiberwiseMap_comp hψ).congr ?_
      intro x
      obtain ⟨p, rfl⟩ := (homeomorph G P).surjective x
      simp [Function.comp_def]) =
      (ψ.diffeomorphPullback f hψ).trans (φ.diffeomorphPullback f hφ) := by
  apply Diffeomorph.ext
  intro x
  obtain ⟨p, rfl⟩ := (homeomorph G ((f : B' → B) *ᵖ P)).surjective x
  simp
  rfl

end TauCeti.PrincipalBundle.Equiv

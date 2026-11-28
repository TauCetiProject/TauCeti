/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.FiberBundle.Principal.Equivariant
public import TauCeti.Geometry.Manifold.FiberBundle.Pullback.Coherence
public import TauCeti.Geometry.Manifold.FiberBundle.Pullback.Map
public import TauCeti.Topology.FiberBundle.Principal.Pullback
public import TauCeti.Topology.FiberBundle.Trivialization

/-!
# Pullbacks of smooth principal-bundle isomorphisms

A fibrewise equivariant equivalence with smooth forward map induces a diffeomorphism of the
pullback total spaces along a smooth map. In particular, a principal-bundle isomorphism restricts
to an open subset by pulling back along the smooth inclusion `Subtype.val`.

The projection and lift equations characterize the pulled-back diffeomorphism. The construction
preserves identity, composition and inverse of isomorphisms and commutes with the canonical
comparisons for identity and composite base maps.

Mathlib's pullback charts use a nonemptiness instance for each fibre of the original bundle.
For a principal `G`-bundle `P`, install this family with
`letI (b : B) := nonempty_fiber_of_nonempty G P b`.
-/

public section

open Bundle MulOpposite TauCeti.ManifoldTotalSpace
open scoped Manifold ContDiff

namespace TauCeti.PrincipalBundle

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

variable [LieGroup IG n G] (e : ∀ b, P b ≃ Q b)
  (he : ∀ b (g : G) (p : P b), e b (op g • p) = op g • e b p)
  (f : C^n⟮IB', B'; IB, B⟯)
  (hf : ContMDiff (IB.prod IG) (IB.prod IG) n
    (fiberwiseMap (F := G) (F' := G) fun b ↦ e b))

/-- Bundle the fibre equivalences for the topological pullback using continuity in both
directions of the induced diffeomorphism. -/
private def equivOfSmooth : PrincipalBundle.Equiv G P Q where
  toEquiv := e
  continuous_toFun := by
    simpa only [Function.comp_def, fiberwiseMap_homeomorph, Homeomorph.symm_apply_apply] using
      (homeomorph G Q).symm.continuous.comp (hf.continuous.comp (homeomorph G P).continuous)
  continuous_invFun := by
    simpa only [Function.comp_def, fiberwiseMap_homeomorph, Homeomorph.symm_apply_apply] using
      (homeomorph G P).symm.continuous.comp
        ((contMDiff_symm_of_equivariant e he hf).continuous.comp (homeomorph G Q).continuous)
  map_smul b p g := he b g p

variable [∀ b, Nonempty (P b)] [∀ b, Nonempty (Q b)]

/-- Pull back a smooth fibrewise equivariant equivalence to a diffeomorphism of charted total
spaces. Smoothness of the inverse follows from equivariance. -/
noncomputable def diffeomorphPullback :
    Diffeomorph (IB'.prod IG) (IB'.prod IG)
      (ManifoldTotalSpace G ((f : B' → B) *ᵖ P))
      (ManifoldTotalSpace G ((f : B' → B) *ᵖ Q)) n := by
  let ψ := equivOfSmooth e he hf
  have hEquiv : (ψ.pullback f).toEquiv = (fun b ↦ e (f b)) :=
    funext (Equiv.pullback_toEquiv ψ f)
  exact diffeomorphOfEquivariant G (ψ.pullback f).toEquiv
    (fun b g p ↦ (ψ.pullback f).map_smul b p g) (by
      rw [hEquiv]
      exact contMDiff_fiberwiseMap_pullback f f.contMDiff hf)

private theorem diffeomorphPullback_eq :
    diffeomorphPullback e he f hf =
      diffeomorphOfEquivariant G (P := (f : B' → B) *ᵖ P) (Q := (f : B' → B) *ᵖ Q)
        (fun b ↦ e (f b)) (fun b g p ↦ he (f b) g p)
        (contMDiff_fiberwiseMap_pullback f f.contMDiff hf) := by
  dsimp only [diffeomorphPullback]
  congr 1
  exact funext (Equiv.pullback_toEquiv (equivOfSmooth e he hf) f)

/-- The pulled-back diffeomorphism uses the original equivalence at the image base point. -/
@[simp]
theorem diffeomorphPullback_apply (p : TotalSpace G ((f : B' → B) *ᵖ P)) :
    diffeomorphPullback e he f hf (homeomorph G ((f : B' → B) *ᵖ P) p) =
      homeomorph G ((f : B' → B) *ᵖ Q) ⟨p.proj, e (f p.proj) p.snd⟩ := by
  rw [diffeomorphPullback_eq]
  exact diffeomorphOfEquivariant_apply (P := (f : B' → B) *ᵖ P)
    (Q := (f : B' → B) *ᵖ Q) _ _ _ p

/-- The inverse of the pulled-back diffeomorphism uses the original inverse in each fibre. -/
@[simp]
theorem diffeomorphPullback_symm_apply (q : TotalSpace G ((f : B' → B) *ᵖ Q)) :
    (diffeomorphPullback e he f hf).symm (homeomorph G ((f : B' → B) *ᵖ Q) q) =
      homeomorph G ((f : B' → B) *ᵖ P) ⟨q.proj, (e (f q.proj)).symm q.snd⟩ := by
  rw [diffeomorphPullback_eq]
  exact diffeomorphOfEquivariant_symm_apply (P := (f : B' → B) *ᵖ P)
    (Q := (f : B' → B) *ᵖ Q) _ _ _ q

/-- The pulled-back diffeomorphism preserves the point of the new base. -/
theorem diffeomorphPullback_proj (x : ManifoldTotalSpace G ((f : B' → B) *ᵖ P)) :
    ((homeomorph G ((f : B' → B) *ᵖ Q)).symm (diffeomorphPullback e he f hf x)).proj =
      ((homeomorph G ((f : B' → B) *ᵖ P)).symm x).proj := by
  rw [diffeomorphPullback_eq]
  exact diffeomorphOfEquivariant_proj (IB := IB') (IG := IG) _ _ _ x

/-- The pulled-back diffeomorphism preserves the right action on arbitrary charted points. -/
theorem diffeomorphPullback_op_smul (g : G)
    (x : ManifoldTotalSpace G ((f : B' → B) *ᵖ P)) :
    diffeomorphPullback e he f hf (op g • x) = op g • diffeomorphPullback e he f hf x := by
  rw [diffeomorphPullback_eq]
  exact diffeomorphOfEquivariant_op_smul (IB := IB') (IG := IG) _ _ _ g x

/-- Lifting after the pulled-back isomorphism agrees with the original isomorphism after lifting.
Both lifts are read in their original total spaces. -/
theorem diffeomorphPullback_lift (x : ManifoldTotalSpace G ((f : B' → B) *ᵖ P)) :
    homeomorph G Q (Pullback.lift f ((homeomorph G ((f : B' → B) *ᵖ Q)).symm
      (diffeomorphPullback e he f hf x))) =
      diffeomorphOfEquivariant G e he hf
        (homeomorph G P (Pullback.lift f
          ((homeomorph G ((f : B' → B) *ᵖ P)).symm x))) := by
  obtain ⟨p, rfl⟩ := (homeomorph G ((f : B' → B) *ᵖ P)).surjective x
  rw [diffeomorphPullback_apply]
  rw [(homeomorph G ((f : B' → B) *ᵖ Q)).symm_apply_apply]
  rw [(homeomorph G ((f : B' → B) *ᵖ P)).symm_apply_apply]
  exact (diffeomorphOfEquivariant_apply e he hf (Pullback.lift f p)).symm

/-- Pullback of the identity is the identity diffeomorphism. -/
@[simp]
theorem diffeomorphPullback_refl :
    diffeomorphPullback (P := P) (Q := P) (IG := IG) (fun b ↦ _root_.Equiv.refl (P b))
      (fun _ _ _ ↦ by simp only [_root_.Equiv.refl_apply]) f (by
        refine contMDiff_id.congr fun x ↦ ?_
        obtain ⟨p, rfl⟩ := (homeomorph G P).surjective x
        simp) =
      Diffeomorph.refl (IB'.prod IG) (ManifoldTotalSpace G ((f : B' → B) *ᵖ P)) n := by
  rw [diffeomorphPullback_eq]
  exact diffeomorphOfEquivariant_refl (P := (f : B' → B) *ᵖ P)

/-- Pullback commutes with inverse, using the smooth inverse provided by equivariance. -/
theorem diffeomorphPullback_symm :
    diffeomorphPullback (fun b ↦ (e b).symm) (fun b g q ↦ by
      apply (e b).injective
      simp only [_root_.Equiv.apply_symm_apply, he]) f (contMDiff_symm_of_equivariant e he hf) =
      (diffeomorphPullback e he f hf).symm := by
  rw [diffeomorphPullback_eq, diffeomorphPullback_eq]
  exact diffeomorphOfEquivariant_symm (P := (f : B' → B) *ᵖ P)
    (Q := (f : B' → B) *ᵖ Q) _ _ _

variable {R : B → Type*}
  [TopologicalSpace (TotalSpace G R)] [∀ b, TopologicalSpace (R b)] [FiberBundle G R]
  [∀ b, MulAction Gᵐᵒᵖ (R b)] [PrincipalBundle G R] [∀ b, Nonempty (R b)]

/-- Pullback commutes with composition of smooth principal-bundle isomorphisms. -/
theorem diffeomorphPullback_trans (e' : ∀ b, Q b ≃ R b)
    (he' : ∀ b (g : G) (q : Q b), e' b (op g • q) = op g • e' b q)
    (hf' : ContMDiff (IB.prod IG) (IB.prod IG) n
      (fiberwiseMap (F := G) (F' := G) fun b ↦ e' b)) :
    diffeomorphPullback (fun b ↦ (e b).trans (e' b))
      (fun b g p ↦ by simp only [_root_.Equiv.trans_apply, he, he']) f
      (by simpa only [_root_.Equiv.coe_trans] using hf'.fiberwiseMap_comp hf) =
      (diffeomorphPullback e he f hf).trans (diffeomorphPullback e' he' f hf') := by
  rw [diffeomorphPullback_eq, diffeomorphPullback_eq, diffeomorphPullback_eq]
  exact diffeomorphOfEquivariant_trans (P := (f : B' → B) *ᵖ P)
    (Q := (f : B' → B) *ᵖ Q) (R := (f : B' → B) *ᵖ R) _ _ _ _ _ _

/-- Projection and lift compatibility uniquely characterize the pulled-back diffeomorphism. -/
theorem diffeomorphPullback_unique
    (d : Diffeomorph (IB'.prod IG) (IB'.prod IG)
      (ManifoldTotalSpace G ((f : B' → B) *ᵖ P))
      (ManifoldTotalSpace G ((f : B' → B) *ᵖ Q)) n)
    (hproj : ∀ x, ((homeomorph G ((f : B' → B) *ᵖ Q)).symm (d x)).proj =
      ((homeomorph G ((f : B' → B) *ᵖ P)).symm x).proj)
    (hlift : ∀ x, homeomorph G Q (Pullback.lift f
      ((homeomorph G ((f : B' → B) *ᵖ Q)).symm (d x))) =
      diffeomorphOfEquivariant G e he hf
        (homeomorph G P (Pullback.lift f
          ((homeomorph G ((f : B' → B) *ᵖ P)).symm x)))) :
    d = diffeomorphPullback e he f hf := by
  apply Diffeomorph.ext
  intro x
  apply (homeomorph G ((f : B' → B) *ᵖ Q)).symm.injective
  apply Pullback.totalSpace_ext
  · exact (hproj x).trans (diffeomorphPullback_proj e he f hf x).symm
  · apply (homeomorph G Q).injective
    exact (hlift x).trans (diffeomorphPullback_lift e he f hf x).symm

/-- Pullback along the identity commutes with the canonical identity comparisons. -/
theorem diffeomorphPullback_id :
    (diffeomorphPullback e he (ContMDiffMap.id : C^n⟮IB, B; IB, B⟯) hf).trans
        (idDiffeomorph (n := n) (F := G) (E := Q) IB IG) =
      (idDiffeomorph (n := n) (F := G) (E := P) IB IG).trans
        (diffeomorphOfEquivariant G e he hf) := by
  apply Diffeomorph.ext
  intro x
  obtain ⟨p, rfl⟩ := (homeomorph G ((ContinuousMap.id B : B → B) *ᵖ P)).surjective x
  -- View the identity pullback through each bundled base map's own fibre formula.
  -- Rewriting the composed diffeomorphisms directly does not match those two presentations.
  change idDiffeomorph (n := n) (F := G) (E := Q) IB IG
      (diffeomorphPullback e he ContMDiffMap.id hf (homeomorph G _ p)) =
    diffeomorphOfEquivariant G e he hf
      (idDiffeomorph (n := n) (F := G) (E := P) IB IG (homeomorph G _ p))
  erw [diffeomorphPullback_apply, idDiffeomorph_homeomorph, idDiffeomorph_homeomorph,
    diffeomorphOfEquivariant_apply]
  rfl

variable {B'' EB'' HB'' : Type*} [NormedAddCommGroup EB''] [NormedSpace 𝕜 EB'']
  [TopologicalSpace HB''] {IB'' : ModelWithCorners 𝕜 EB'' HB''}
  [TopologicalSpace B''] [ChartedSpace HB'' B'']

/-- Pullback along a composite commutes with the canonical composition comparisons. -/
theorem diffeomorphPullback_comp (g : C^n⟮IB'', B''; IB', B'⟯) :
    (diffeomorphPullback e he (f.comp g) hf).trans
        (compDiffeomorph (n := n) (F := G) (E := Q) IB'' IG
          ⟨f, f.contMDiff.continuous⟩ ⟨g, g.contMDiff.continuous⟩) =
      (compDiffeomorph (n := n) (F := G) (E := P) IB'' IG
          ⟨f, f.contMDiff.continuous⟩ ⟨g, g.contMDiff.continuous⟩).trans
        (diffeomorphPullback (P := (f : B' → B) *ᵖ P) (Q := (f : B' → B) *ᵖ Q)
          (fun b ↦ e (f b)) (fun b a p ↦ he (f b) a p) g
          (contMDiff_fiberwiseMap_pullback f f.contMDiff hf)) := by
  apply Diffeomorph.ext
  intro x
  obtain ⟨p, rfl⟩ := (homeomorph G (((f.comp g) : B'' → B) *ᵖ P)).surjective x
  -- The comparison uses continuous maps and the restriction uses smooth maps.
  -- Expose the composite applications so the fibre equations match their respective maps.
  change compDiffeomorph (n := n) (F := G) (E := Q) IB'' IG
      ⟨f, f.contMDiff.continuous⟩ ⟨g, g.contMDiff.continuous⟩
      (diffeomorphPullback e he (f.comp g) hf (homeomorph G _ p)) =
    diffeomorphPullback (P := (f : B' → B) *ᵖ P) (Q := (f : B' → B) *ᵖ Q)
      (fun b ↦ e (f b)) (fun b a p ↦ he (f b) a p) g _
      (compDiffeomorph (n := n) (F := G) (E := P) IB'' IG
        ⟨f, f.contMDiff.continuous⟩ ⟨g, g.contMDiff.continuous⟩ (homeomorph G _ p))
  erw [diffeomorphPullback_apply, compDiffeomorph_homeomorph, compDiffeomorph_homeomorph,
    diffeomorphPullback_apply]
  rfl

end TauCeti.PrincipalBundle

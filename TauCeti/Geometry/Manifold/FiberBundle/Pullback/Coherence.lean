/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.FiberBundle.Pullback.Basic

/-!
# Identity and composition comparisons for pullback bundles

For bundles with manifold fibres, the pullback along the identity is diffeomorphic to the
original bundle, and pullback along a composite is diffeomorphic to successive pullback.
These comparisons preserve base points and fibre elements. They intertwine the canonical
lifts and every fibrewise scalar operation, so in particular they are equivariant comparisons
for principal bundles. All total spaces retain their native pullback topologies and the
charts through their model fibre.

The composition comparison is smooth for continuous base maps, even when those maps are
not smooth: the two preferred trivializations use the same original fibre coordinates.
No smooth-bundle, finite-dimensionality, or separation assumption is needed.

## References

* D. Husemoller, *Fibre Bundles*, third edition, Springer, 1994, Chapter 2 (induced bundles).
* The constructions extend `Bundle.Pullback.idDiffeomorph` and
  `Bundle.Pullback.compDiffeomorph` from normed-space model fibres to manifold model fibres.
-/

public section

open Bundle
open scoped Manifold ContDiff

namespace TauCeti.ManifoldTotalSpace

variable {n : ℕ∞ω} {𝕜 B B' B'' F : Type*} [NontriviallyNormedField 𝕜]
  {EB : Type*} [NormedAddCommGroup EB] [NormedSpace 𝕜 EB]
  {HB : Type*} [TopologicalSpace HB] {IB : ModelWithCorners 𝕜 EB HB}
  [TopologicalSpace B] [ChartedSpace HB B]
  {EB' : Type*} [NormedAddCommGroup EB'] [NormedSpace 𝕜 EB']
  {HB' : Type*} [TopologicalSpace HB'] {IB' : ModelWithCorners 𝕜 EB' HB'}
  [TopologicalSpace B'] [ChartedSpace HB' B']
  {EB'' : Type*} [NormedAddCommGroup EB''] [NormedSpace 𝕜 EB'']
  {HB'' : Type*} [TopologicalSpace HB''] {IB'' : ModelWithCorners 𝕜 EB'' HB''}
  [TopologicalSpace B''] [ChartedSpace HB'' B'']
  {EF : Type*} [NormedAddCommGroup EF] [NormedSpace 𝕜 EF]
  {HF : Type*} [TopologicalSpace HF] {IF : ModelWithCorners 𝕜 EF HF}
  [TopologicalSpace F] [ChartedSpace HF F]
  {E : B → Type*} [TopologicalSpace (TotalSpace F E)]
  [∀ b, TopologicalSpace (E b)] [FiberBundle F E] [∀ b, Nonempty (E b)]

variable (n F E IB IF) in
/-- Pullback along the identity is canonically diffeomorphic to the original total space.
The comparison is the identity on each fibre. -/
noncomputable def idDiffeomorph :
    Diffeomorph (IB.prod IF) (IB.prod IF)
      (ManifoldTotalSpace F ((ContinuousMap.id B : B → B) *ᵖ E))
      (ManifoldTotalSpace F E) n where
  toFun x := homeomorph F E ⟨((homeomorph F _).symm x).proj, ((homeomorph F _).symm x).2⟩
  invFun x := homeomorph F _ ⟨((homeomorph F E).symm x).proj, ((homeomorph F E).symm x).2⟩
  left_inv x := by
    -- Unfold the fibre identity through the pullback type synonym before cancellation.
    dsimp only
    erw [Homeomorph.symm_apply_apply]
    exact Homeomorph.apply_symm_apply _ x
  right_inv x := by
    -- Unfold the fibre identity through the pullback type synonym before cancellation.
    dsimp only
    erw [Homeomorph.symm_apply_apply]
    exact Homeomorph.apply_symm_apply _ x
  contMDiff_toFun := contMDiff_pullbackLift n IF (ContinuousMap.id B) contMDiff_id
  contMDiff_invFun := (contMDiff_pullback_iff (ContinuousMap.id B) contMDiff_id).2
    ⟨contMDiff_proj n F E IB IF, contMDiff_id.congr fun x ↦ Homeomorph.apply_symm_apply _ x⟩

-- Use the computation and equivariance lemmas explicitly: default simp normalizes the
-- continuous-map coercions in their dependent bundle types before it can match these rules.
/-- The identity comparison preserves the displayed base point and fibre element. -/
theorem idDiffeomorph_homeomorph (p : TotalSpace F ((ContinuousMap.id B : B → B) *ᵖ E)) :
    idDiffeomorph (n := n) (F := F) (E := E) IB IF
        (homeomorph F ((ContinuousMap.id B : B → B) *ᵖ E) p) =
      homeomorph F E ⟨p.proj, p.2⟩ := by
  exact congrArg (fun q : TotalSpace F ((ContinuousMap.id B : B → B) *ᵖ E) ↦
    homeomorph F E ⟨q.proj, q.2⟩)
      ((homeomorph F ((ContinuousMap.id B : B → B) *ᵖ E)).symm_apply_apply p)

/-- The inverse identity comparison preserves the displayed base point and fibre element. -/
theorem idDiffeomorph_symm_homeomorph (p : TotalSpace F E) :
    (idDiffeomorph (n := n) (F := F) (E := E) IB IF).symm (homeomorph F E p) =
      homeomorph F ((ContinuousMap.id B : B → B) *ᵖ E) ⟨p.proj, p.2⟩ := by
  exact congrArg (fun q : TotalSpace F E ↦
    homeomorph F ((ContinuousMap.id B : B → B) *ᵖ E) ⟨q.proj, q.2⟩)
      ((homeomorph F E).symm_apply_apply p)

variable (n F E IB'' IF) in
/-- Pullback along a composite and successive pullback have canonically diffeomorphic
total spaces. Both atlases read the same original fibre coordinates, so the comparison is
`C^n` even when the continuous base maps are not smooth. -/
noncomputable def compDiffeomorph (g : C(B', B)) (f : C(B'', B')) :
    Diffeomorph (IB''.prod IF) (IB''.prod IF)
      (ManifoldTotalSpace F ((g.comp f : B'' → B) *ᵖ E))
      (ManifoldTotalSpace F ((f : B'' → B') *ᵖ ((g : B' → B) *ᵖ E))) n where
  toFun x := homeomorph F _ ⟨((homeomorph F _).symm x).proj, ((homeomorph F _).symm x).2⟩
  invFun x := homeomorph F _ ⟨((homeomorph F _).symm x).proj, ((homeomorph F _).symm x).2⟩
  left_inv x := by
    -- Unfold the fibre identity through the pullback type synonym before cancellation.
    dsimp only
    erw [Homeomorph.symm_apply_apply]
    exact Homeomorph.apply_symm_apply _ x
  right_inv x := by
    -- Unfold the fibre identity through the pullback type synonym before cancellation.
    dsimp only
    erw [Homeomorph.symm_apply_apply]
    exact Homeomorph.apply_symm_apply _ x
  contMDiff_toFun x := by
    have hx : ContMDiffAt (IB''.prod IF) (IB''.prod IF) n
        (fun y ↦ homeomorph F ((g.comp f : B'' → B) *ᵖ E)
          ((homeomorph F _).symm y)) x :=
      contMDiffAt_id.congr_of_eventuallyEq (.of_forall fun y ↦ by
        simp only [Homeomorph.apply_symm_apply, id_eq])
    have h := ManifoldTotalSpace.contMDiffAt_iff.1 hx
    exact ManifoldTotalSpace.contMDiffAt_iff.2 h
  contMDiff_invFun x := by
    have hx : ContMDiffAt (IB''.prod IF) (IB''.prod IF) n
        (fun y ↦ homeomorph F ((f : B'' → B') *ᵖ ((g : B' → B) *ᵖ E))
          ((homeomorph F _).symm y)) x :=
      contMDiffAt_id.congr_of_eventuallyEq (.of_forall fun y ↦ by
        simp only [Homeomorph.apply_symm_apply, id_eq])
    have h := ManifoldTotalSpace.contMDiffAt_iff.1 hx
    exact ManifoldTotalSpace.contMDiffAt_iff.2 h

/-- The composition comparison preserves the displayed base point and fibre element. -/
theorem compDiffeomorph_homeomorph (g : C(B', B)) (f : C(B'', B'))
    (p : TotalSpace F ((g.comp f : B'' → B) *ᵖ E)) :
    compDiffeomorph (n := n) (F := F) (E := E) IB'' IF g f
        (homeomorph F ((g.comp f : B'' → B) *ᵖ E) p) =
      homeomorph F ((f : B'' → B') *ᵖ ((g : B' → B) *ᵖ E)) ⟨p.proj, p.2⟩ := by
  exact congrArg (fun q : TotalSpace F ((g.comp f : B'' → B) *ᵖ E) ↦
    homeomorph F ((f : B'' → B') *ᵖ ((g : B' → B) *ᵖ E)) ⟨q.proj, q.2⟩)
      ((homeomorph F ((g.comp f : B'' → B) *ᵖ E)).symm_apply_apply p)

/-- The inverse composition comparison preserves the displayed base point and fibre element. -/
theorem compDiffeomorph_symm_homeomorph (g : C(B', B)) (f : C(B'', B'))
    (p : TotalSpace F ((f : B'' → B') *ᵖ ((g : B' → B) *ᵖ E))) :
    (compDiffeomorph (n := n) (F := F) (E := E) IB'' IF g f).symm
        (homeomorph F ((f : B'' → B') *ᵖ ((g : B' → B) *ᵖ E)) p) =
      homeomorph F ((g.comp f : B'' → B) *ᵖ E) ⟨p.proj, p.2⟩ := by
  exact congrArg (fun q : TotalSpace F ((f : B'' → B') *ᵖ ((g : B' → B) *ᵖ E)) ↦
    homeomorph F ((g.comp f : B'' → B) *ᵖ E) ⟨q.proj, q.2⟩)
      ((homeomorph F ((f : B'' → B') *ᵖ ((g : B' → B) *ᵖ E))).symm_apply_apply p)

/-- The comparison intertwines the lift from a composite pullback with the two successive
lifts to the original bundle. This identity does not require smoothness of the base maps. -/
theorem lift_comp_compDiffeomorph (g : C(B', B)) (f : C(B'', B'))
    (x : ManifoldTotalSpace F ((g.comp f : B'' → B) *ᵖ E)) :
    Pullback.lift g (Pullback.lift f
      ((homeomorph F ((f : B'' → B') *ᵖ ((g : B' → B) *ᵖ E))).symm
        (compDiffeomorph (n := n) (F := F) (E := E) IB'' IF g f x))) =
        Pullback.lift (g.comp f) ((homeomorph F ((g.comp f : B'' → B) *ᵖ E)).symm x) := by
  obtain ⟨p, rfl⟩ := (homeomorph F ((g.comp f : B'' → B) *ᵖ E)).surjective x
  rw [compDiffeomorph_homeomorph]
  simp only [Homeomorph.symm_apply_apply]
  rfl

/-- Pullback along the identity after a base map cancels the identity comparison.
This is the unit law for the composition comparison. -/
@[simp]
theorem compDiffeomorph_id (g : C(B', B)) :
    compDiffeomorph (n := n) (F := F) (E := E) IB' IF g (ContinuousMap.id B') =
      (idDiffeomorph (n := n) (F := F) (E := (g : B' → B) *ᵖ E) IB' IF).symm := by
  -- Both comparisons keep the point in the same fibre; composition with the identity
  -- reduces to the same continuous base map and hence the same pullback topology.
  ext x
  rfl

section Actions

variable {A : Type*} [∀ b, SMul A (E b)]

/-- The identity comparison intertwines fibrewise scalar multiplication. In particular it is an
equivariant isomorphism for the right action of a principal bundle. -/
theorem idDiffeomorph_smul (a : A)
    (x : ManifoldTotalSpace F ((ContinuousMap.id B : B → B) *ᵖ E)) :
    idDiffeomorph (n := n) (F := F) (E := E) IB IF (a • x) =
      a • idDiffeomorph (n := n) (F := F) (E := E) IB IF x := by
  obtain ⟨p, rfl⟩ := (homeomorph F ((ContinuousMap.id B : B → B) *ᵖ E)).surjective x
  rw [smul_homeomorph, idDiffeomorph_homeomorph, idDiffeomorph_homeomorph,
    smul_homeomorph]
  rfl

/-- The composition comparison intertwines fibrewise scalar multiplication. In particular it is an
equivariant isomorphism between the composite and iterated pullbacks of a principal bundle. -/
theorem compDiffeomorph_smul (g : C(B', B)) (f : C(B'', B')) (a : A)
    (x : ManifoldTotalSpace F ((g.comp f : B'' → B) *ᵖ E)) :
    compDiffeomorph (n := n) (F := F) (E := E) IB'' IF g f (a • x) =
      a • compDiffeomorph (n := n) (F := F) (E := E) IB'' IF g f x := by
  obtain ⟨p, rfl⟩ := (homeomorph F ((g.comp f : B'' → B) *ᵖ E)).surjective x
  rw [smul_homeomorph, compDiffeomorph_homeomorph, compDiffeomorph_homeomorph,
    smul_homeomorph]
  rfl

end Actions

end TauCeti.ManifoldTotalSpace

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
noncomputable def pullbackIdDiffeomorph :
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
theorem pullbackIdDiffeomorph_homeomorph (p : TotalSpace F ((ContinuousMap.id B : B → B) *ᵖ E)) :
    pullbackIdDiffeomorph (n := n) (F := F) (E := E) IB IF
        (homeomorph F ((ContinuousMap.id B : B → B) *ᵖ E) p) =
      homeomorph F E ⟨p.proj, p.2⟩ := by
  exact congrArg (fun q : TotalSpace F ((ContinuousMap.id B : B → B) *ᵖ E) ↦
    homeomorph F E ⟨q.proj, q.2⟩)
      ((homeomorph F ((ContinuousMap.id B : B → B) *ᵖ E)).symm_apply_apply p)

/-- The inverse identity comparison preserves the displayed base point and fibre element. -/
theorem pullbackIdDiffeomorph_symm_homeomorph (p : TotalSpace F E) :
    (pullbackIdDiffeomorph (n := n) (F := F) (E := E) IB IF).symm (homeomorph F E p) =
      homeomorph F ((ContinuousMap.id B : B → B) *ᵖ E) ⟨p.proj, p.2⟩ := by
  exact congrArg (fun q : TotalSpace F E ↦
    homeomorph F ((ContinuousMap.id B : B → B) *ᵖ E) ⟨q.proj, q.2⟩)
      ((homeomorph F E).symm_apply_apply p)

/-- Reading the identity comparison in the original total space preserves both components. -/
theorem homeomorph_symm_pullbackIdDiffeomorph
    (x : ManifoldTotalSpace F ((ContinuousMap.id B : B → B) *ᵖ E)) :
    (homeomorph F E).symm (pullbackIdDiffeomorph (n := n) (F := F) (E := E) IB IF x) =
      ⟨((homeomorph F _).symm x).proj, ((homeomorph F _).symm x).2⟩ := by
  exact (homeomorph F E).symm_apply_apply _

/-- Reading the inverse identity comparison in the pullback preserves both components. -/
theorem homeomorph_symm_pullbackIdDiffeomorph_symm (x : ManifoldTotalSpace F E) :
    (homeomorph F ((ContinuousMap.id B : B → B) *ᵖ E)).symm
        ((pullbackIdDiffeomorph (n := n) (F := F) (E := E) IB IF).symm x) =
      ⟨((homeomorph F E).symm x).proj, ((homeomorph F E).symm x).2⟩ := by
  exact (homeomorph F ((ContinuousMap.id B : B → B) *ᵖ E)).symm_apply_apply _

/-- The identity comparison is the fibrewise identity map. -/
theorem coe_pullbackIdDiffeomorph :
    ⇑(pullbackIdDiffeomorph (n := n) (F := F) (E := E) IB IF) =
      fiberwiseMap (E := ((ContinuousMap.id B : B → B) *ᵖ E))
        (E' := E) (fun _ ↦ id) := by
  funext x
  obtain ⟨p, rfl⟩ := (homeomorph F ((ContinuousMap.id B : B → B) *ᵖ E)).surjective x
  exact (pullbackIdDiffeomorph_homeomorph p).trans
    (fiberwiseMap_homeomorph (E := ((ContinuousMap.id B : B → B) *ᵖ E))
      (E' := E) (fun _ ↦ id) p).symm

/-- The inverse identity comparison is the fibrewise identity map. -/
theorem coe_pullbackIdDiffeomorph_symm :
    ⇑(pullbackIdDiffeomorph (n := n) (F := F) (E := E) IB IF).symm =
      fiberwiseMap (E := E)
        (E' := ((ContinuousMap.id B : B → B) *ᵖ E)) (fun _ ↦ id) := by
  funext x
  obtain ⟨p, rfl⟩ := (homeomorph F E).surjective x
  exact (pullbackIdDiffeomorph_symm_homeomorph p).trans
    (fiberwiseMap_homeomorph (E := E)
      (E' := ((ContinuousMap.id B : B → B) *ᵖ E)) (fun _ ↦ id) p).symm

/-- The identity comparison agrees with the canonical lift from the identity pullback. -/
theorem pullbackIdDiffeomorph_eq_pullbackLift
    (x : ManifoldTotalSpace F ((ContinuousMap.id B : B → B) *ᵖ E)) :
    pullbackIdDiffeomorph (n := n) (F := F) (E := E) IB IF x =
      homeomorph F E (Pullback.lift (ContinuousMap.id B) ((homeomorph F _).symm x)) := by
  obtain ⟨p, rfl⟩ := (homeomorph F ((ContinuousMap.id B : B → B) *ᵖ E)).surjective x
  rw [pullbackIdDiffeomorph_homeomorph, Homeomorph.symm_apply_apply]
  rfl

-- Composite and iterated pullbacks read the same fibre coordinate in their preferred charts.
private theorem pullbackComp_trivializationAt_snd (g : C(B', B)) (f : C(B'', B'))
    (b₀ : B'') (p : TotalSpace F ((g.comp f : B'' → B) *ᵖ E)) :
    (trivializationAt F ((f : B'' → B') *ᵖ ((g : B' → B) *ᵖ E)) b₀
      ⟨p.proj, p.2⟩).2 =
      (trivializationAt F ((g.comp f : B'' → B) *ᵖ E) b₀ p).2 := by
  simp only [trivializationAt, FiberBundle.pullback_trivializationAt',
    Trivialization.pullback_apply, Pullback.lift, ContinuousMap.comp_apply]

variable (n F E IB'' IF) in
/-- Pullback along a composite and successive pullback have canonically diffeomorphic
total spaces. Both atlases read the same original fibre coordinates, so the comparison is
`C^n` even when the continuous base maps are not smooth. -/
noncomputable def pullbackCompDiffeomorph (g : C(B', B)) (f : C(B'', B')) :
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
    refine ManifoldTotalSpace.contMDiffAt_iff.2
      ⟨contMDiff_proj n F _ IB'' IF x, ?_⟩
    exact (contMDiffAt_trivializationAt_snd n IB'' IF x).congr_of_eventuallyEq
      (.of_forall fun y ↦ pullbackComp_trivializationAt_snd g f _ _)
  contMDiff_invFun x := by
    refine ManifoldTotalSpace.contMDiffAt_iff.2
      ⟨contMDiff_proj n F _ IB'' IF x, ?_⟩
    exact (contMDiffAt_trivializationAt_snd n IB'' IF x).congr_of_eventuallyEq
      (.of_forall fun y ↦ (pullbackComp_trivializationAt_snd g f _ _).symm)

/-- The composition comparison preserves the displayed base point and fibre element. -/
theorem pullbackCompDiffeomorph_homeomorph (g : C(B', B)) (f : C(B'', B'))
    (p : TotalSpace F ((g.comp f : B'' → B) *ᵖ E)) :
    pullbackCompDiffeomorph (n := n) (F := F) (E := E) IB'' IF g f
        (homeomorph F ((g.comp f : B'' → B) *ᵖ E) p) =
      homeomorph F ((f : B'' → B') *ᵖ ((g : B' → B) *ᵖ E)) ⟨p.proj, p.2⟩ := by
  exact congrArg (fun q : TotalSpace F ((g.comp f : B'' → B) *ᵖ E) ↦
    homeomorph F ((f : B'' → B') *ᵖ ((g : B' → B) *ᵖ E)) ⟨q.proj, q.2⟩)
      ((homeomorph F ((g.comp f : B'' → B) *ᵖ E)).symm_apply_apply p)

/-- The inverse composition comparison preserves the displayed base point and fibre element. -/
theorem pullbackCompDiffeomorph_symm_homeomorph (g : C(B', B)) (f : C(B'', B'))
    (p : TotalSpace F ((f : B'' → B') *ᵖ ((g : B' → B) *ᵖ E))) :
    (pullbackCompDiffeomorph (n := n) (F := F) (E := E) IB'' IF g f).symm
        (homeomorph F ((f : B'' → B') *ᵖ ((g : B' → B) *ᵖ E)) p) =
      homeomorph F ((g.comp f : B'' → B) *ᵖ E) ⟨p.proj, p.2⟩ := by
  exact congrArg (fun q : TotalSpace F ((f : B'' → B') *ᵖ ((g : B' → B) *ᵖ E)) ↦
    homeomorph F ((g.comp f : B'' → B) *ᵖ E) ⟨q.proj, q.2⟩)
      ((homeomorph F ((f : B'' → B') *ᵖ ((g : B' → B) *ᵖ E))).symm_apply_apply p)

/-- Reading the composition comparison in the iterated pullback preserves both components. -/
theorem homeomorph_symm_pullbackCompDiffeomorph (g : C(B', B)) (f : C(B'', B'))
    (x : ManifoldTotalSpace F ((g.comp f : B'' → B) *ᵖ E)) :
    (homeomorph F ((f : B'' → B') *ᵖ ((g : B' → B) *ᵖ E))).symm
        (pullbackCompDiffeomorph (n := n) (F := F) (E := E) IB'' IF g f x) =
      ⟨((homeomorph F _).symm x).proj, ((homeomorph F _).symm x).2⟩ := by
  exact (homeomorph F ((f : B'' → B') *ᵖ ((g : B' → B) *ᵖ E))).symm_apply_apply _

/-- Reading the inverse composition comparison in the composite pullback preserves both
components. -/
theorem homeomorph_symm_pullbackCompDiffeomorph_symm (g : C(B', B)) (f : C(B'', B'))
    (x : ManifoldTotalSpace F ((f : B'' → B') *ᵖ ((g : B' → B) *ᵖ E))) :
    (homeomorph F ((g.comp f : B'' → B) *ᵖ E)).symm
        ((pullbackCompDiffeomorph (n := n) (F := F) (E := E) IB'' IF g f).symm x) =
      ⟨((homeomorph F _).symm x).proj, ((homeomorph F _).symm x).2⟩ := by
  exact (homeomorph F ((g.comp f : B'' → B) *ᵖ E)).symm_apply_apply _

/-- The composition comparison is the fibrewise identity map. -/
theorem coe_pullbackCompDiffeomorph (g : C(B', B)) (f : C(B'', B')) :
    ⇑(pullbackCompDiffeomorph (n := n) (F := F) (E := E) IB'' IF g f) =
      fiberwiseMap (E := ((g.comp f : B'' → B) *ᵖ E))
        (E' := ((f : B'' → B') *ᵖ ((g : B' → B) *ᵖ E))) (fun _ ↦ id) := by
  funext x
  obtain ⟨p, rfl⟩ := (homeomorph F ((g.comp f : B'' → B) *ᵖ E)).surjective x
  exact (pullbackCompDiffeomorph_homeomorph g f p).trans
    (fiberwiseMap_homeomorph (E := ((g.comp f : B'' → B) *ᵖ E))
      (E' := ((f : B'' → B') *ᵖ ((g : B' → B) *ᵖ E))) (fun _ ↦ id) p).symm

/-- The inverse composition comparison is the fibrewise identity map. -/
theorem coe_pullbackCompDiffeomorph_symm (g : C(B', B)) (f : C(B'', B')) :
    ⇑(pullbackCompDiffeomorph (n := n) (F := F) (E := E) IB'' IF g f).symm =
      fiberwiseMap (E := ((f : B'' → B') *ᵖ ((g : B' → B) *ᵖ E)))
        (E' := ((g.comp f : B'' → B) *ᵖ E)) (fun _ ↦ id) := by
  funext x
  obtain ⟨p, rfl⟩ := (homeomorph F ((f : B'' → B') *ᵖ ((g : B' → B) *ᵖ E))).surjective x
  exact (pullbackCompDiffeomorph_symm_homeomorph g f p).trans
    (fiberwiseMap_homeomorph (E := ((f : B'' → B') *ᵖ ((g : B' → B) *ᵖ E)))
      (E' := ((g.comp f : B'' → B) *ᵖ E)) (fun _ ↦ id) p).symm

/-- The comparison intertwines the lift from a composite pullback with the two successive
lifts to the original bundle. This identity does not require smoothness of the base maps. -/
theorem pullbackLift_pullbackLift_homeomorph_symm_pullbackCompDiffeomorph
    (g : C(B', B)) (f : C(B'', B'))
    (x : ManifoldTotalSpace F ((g.comp f : B'' → B) *ᵖ E)) :
    Pullback.lift g (Pullback.lift f
      ((homeomorph F ((f : B'' → B') *ᵖ ((g : B' → B) *ᵖ E))).symm
        (pullbackCompDiffeomorph (n := n) (F := F) (E := E) IB'' IF g f x))) =
        Pullback.lift (g.comp f) ((homeomorph F ((g.comp f : B'' → B) *ᵖ E)).symm x) := by
  obtain ⟨p, rfl⟩ := (homeomorph F ((g.comp f : B'' → B) *ᵖ E)).surjective x
  rw [pullbackCompDiffeomorph_homeomorph]
  simp only [Homeomorph.symm_apply_apply]
  rfl

/-- The inverse comparison intertwines the composite lift with the two successive lifts. -/
theorem pullbackLift_homeomorph_symm_pullbackCompDiffeomorph_symm
    (g : C(B', B)) (f : C(B'', B'))
    (x : ManifoldTotalSpace F ((f : B'' → B') *ᵖ ((g : B' → B) *ᵖ E))) :
    Pullback.lift (g.comp f) ((homeomorph F ((g.comp f : B'' → B) *ᵖ E)).symm
        ((pullbackCompDiffeomorph (n := n) (F := F) (E := E) IB'' IF g f).symm x)) =
      Pullback.lift g (Pullback.lift f ((homeomorph F _).symm x)) := by
  rw [homeomorph_symm_pullbackCompDiffeomorph_symm]
  rfl

/-- Pullback along the identity after a base map cancels the identity comparison.
This is the unit law for the composition comparison. -/
@[simp]
theorem pullbackCompDiffeomorph_id_right (g : C(B', B)) :
    pullbackCompDiffeomorph (n := n) (F := F) (E := E) IB' IF g (ContinuousMap.id B') =
      (pullbackIdDiffeomorph (n := n) (F := F) (E := (g : B' → B) *ᵖ E) IB' IF).symm := by
  -- Both comparisons keep the point in the same fibre; composition with the identity
  -- reduces to the same continuous base map and hence the same pullback topology.
  ext x
  rfl

section Actions

variable {A : Type*} [∀ b, SMul A (E b)]

/-- The identity comparison intertwines fibrewise scalar multiplication. In particular it is an
equivariant isomorphism for the right action of a principal bundle. -/
theorem pullbackIdDiffeomorph_smul (a : A)
    (x : ManifoldTotalSpace F ((ContinuousMap.id B : B → B) *ᵖ E)) :
    pullbackIdDiffeomorph (n := n) (F := F) (E := E) IB IF (a • x) =
      a • pullbackIdDiffeomorph (n := n) (F := F) (E := E) IB IF x := by
  obtain ⟨p, rfl⟩ := (homeomorph F ((ContinuousMap.id B : B → B) *ᵖ E)).surjective x
  rw [smul_homeomorph, pullbackIdDiffeomorph_homeomorph, pullbackIdDiffeomorph_homeomorph,
    smul_homeomorph]
  rfl

/-- The inverse identity comparison intertwines fibrewise scalar multiplication. -/
theorem pullbackIdDiffeomorph_symm_smul (a : A) (x : ManifoldTotalSpace F E) :
    (pullbackIdDiffeomorph (n := n) (F := F) (E := E) IB IF).symm (a • x) =
      a • (pullbackIdDiffeomorph (n := n) (F := F) (E := E) IB IF).symm x := by
  obtain ⟨p, rfl⟩ := (homeomorph F E).surjective x
  rw [smul_homeomorph, pullbackIdDiffeomorph_symm_homeomorph,
    pullbackIdDiffeomorph_symm_homeomorph, smul_homeomorph]
  rfl

/-- The composition comparison intertwines fibrewise scalar multiplication. In particular it is an
equivariant isomorphism between the composite and iterated pullbacks of a principal bundle. -/
theorem pullbackCompDiffeomorph_smul (g : C(B', B)) (f : C(B'', B')) (a : A)
    (x : ManifoldTotalSpace F ((g.comp f : B'' → B) *ᵖ E)) :
    pullbackCompDiffeomorph (n := n) (F := F) (E := E) IB'' IF g f (a • x) =
      a • pullbackCompDiffeomorph (n := n) (F := F) (E := E) IB'' IF g f x := by
  obtain ⟨p, rfl⟩ := (homeomorph F ((g.comp f : B'' → B) *ᵖ E)).surjective x
  rw [smul_homeomorph, pullbackCompDiffeomorph_homeomorph, pullbackCompDiffeomorph_homeomorph,
    smul_homeomorph]
  rfl

/-- The inverse composition comparison intertwines fibrewise scalar multiplication. -/
theorem pullbackCompDiffeomorph_symm_smul (g : C(B', B)) (f : C(B'', B')) (a : A)
    (x : ManifoldTotalSpace F ((f : B'' → B') *ᵖ ((g : B' → B) *ᵖ E))) :
    (pullbackCompDiffeomorph (n := n) (F := F) (E := E) IB'' IF g f).symm (a • x) =
      a • (pullbackCompDiffeomorph (n := n) (F := F) (E := E) IB'' IF g f).symm x := by
  obtain ⟨p, rfl⟩ := (homeomorph F ((f : B'' → B') *ᵖ ((g : B' → B) *ᵖ E))).surjective x
  rw [smul_homeomorph, pullbackCompDiffeomorph_symm_homeomorph,
    pullbackCompDiffeomorph_symm_homeomorph, smul_homeomorph]
  rfl

end Actions

end TauCeti.ManifoldTotalSpace

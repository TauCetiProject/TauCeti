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
  {K K' : Type*} [FunLike K B' B] [ContinuousMapClass K B' B]
  [FunLike K' B'' B'] [ContinuousMapClass K' B'' B']

variable (n F E IB IF) in
/-- Pullback along the identity is canonically diffeomorphic to the original total space.
The comparison is the identity on each fibre. -/
noncomputable def pullbackIdDiffeomorph :
    Diffeomorph (IB.prod IF) (IB.prod IF)
      (ManifoldTotalSpace F ((ContinuousMap.id B : B → B) *ᵖ E))
      (ManifoldTotalSpace F E) n where
  toFun := fiberwiseMap (E' := E) fun _ ↦ id
  invFun := fiberwiseMap (E' := (ContinuousMap.id B : B → B) *ᵖ E) fun _ ↦ id
  left_inv := congrFun ((fiberwiseMap_comp _ _).symm.trans fiberwiseMap_id)
  right_inv := congrFun ((fiberwiseMap_comp _ _).symm.trans fiberwiseMap_id)
  contMDiff_toFun := (contMDiff_pullbackLift n IF (ContinuousMap.id B) contMDiff_id).congr
    fun x ↦ (homeomorph F _).symm.injective <|
      (homeomorph_symm_fiberwiseMap _ x).trans (Homeomorph.symm_apply_apply _ _).symm
  contMDiff_invFun := ((contMDiff_pullback_iff (ContinuousMap.id B) contMDiff_id).2
    ⟨contMDiff_proj n F E IB IF, contMDiff_id.congr fun x ↦ Homeomorph.apply_symm_apply _ x⟩).congr
    fun x ↦ (homeomorph F _).symm.injective <|
      (homeomorph_symm_fiberwiseMap _ x).trans (Homeomorph.symm_apply_apply _ _).symm

/-- The identity comparison is the fibrewise identity map. -/
theorem coe_pullbackIdDiffeomorph :
    ⇑(pullbackIdDiffeomorph (n := n) (F := F) (E := E) IB IF) =
      fiberwiseMap (E := ((ContinuousMap.id B : B → B) *ᵖ E))
        (E' := E) (fun _ ↦ id) :=
  funext fun _ ↦ rfl

/-- The inverse identity comparison is the fibrewise identity map. -/
theorem coe_pullbackIdDiffeomorph_symm :
    ⇑(pullbackIdDiffeomorph (n := n) (F := F) (E := E) IB IF).symm =
      fiberwiseMap (E := E)
        (E' := ((ContinuousMap.id B : B → B) *ᵖ E)) (fun _ ↦ id) :=
  funext fun _ ↦ rfl

-- Use the computation and equivariance lemmas explicitly: default simp normalizes the
-- continuous-map coercions in their dependent bundle types before it can match these rules.
/-- The identity comparison preserves the displayed base point and fibre element. -/
theorem pullbackIdDiffeomorph_homeomorph (p : TotalSpace F ((ContinuousMap.id B : B → B) *ᵖ E)) :
    pullbackIdDiffeomorph (n := n) (F := F) (E := E) IB IF
        (homeomorph F ((ContinuousMap.id B : B → B) *ᵖ E) p) =
      homeomorph F E ⟨p.proj, p.2⟩ :=
  fiberwiseMap_homeomorph _ p

/-- The inverse identity comparison preserves the displayed base point and fibre element. -/
theorem pullbackIdDiffeomorph_symm_homeomorph (p : TotalSpace F E) :
    (pullbackIdDiffeomorph (n := n) (F := F) (E := E) IB IF).symm (homeomorph F E p) =
      homeomorph F ((ContinuousMap.id B : B → B) *ᵖ E) ⟨p.proj, p.2⟩ :=
  fiberwiseMap_homeomorph _ p

/-- Reading the identity comparison in the original total space preserves both components. -/
theorem homeomorph_symm_pullbackIdDiffeomorph
    (x : ManifoldTotalSpace F ((ContinuousMap.id B : B → B) *ᵖ E)) :
    (homeomorph F E).symm (pullbackIdDiffeomorph (n := n) (F := F) (E := E) IB IF x) =
      ⟨((homeomorph F _).symm x).proj, ((homeomorph F _).symm x).2⟩ :=
  homeomorph_symm_fiberwiseMap _ x

/-- Reading the inverse identity comparison in the pullback preserves both components. -/
theorem homeomorph_symm_pullbackIdDiffeomorph_symm (x : ManifoldTotalSpace F E) :
    (homeomorph F ((ContinuousMap.id B : B → B) *ᵖ E)).symm
        ((pullbackIdDiffeomorph (n := n) (F := F) (E := E) IB IF).symm x) =
      ⟨((homeomorph F E).symm x).proj, ((homeomorph F E).symm x).2⟩ :=
  homeomorph_symm_fiberwiseMap _ x

/-- The identity comparison agrees with the canonical lift from the identity pullback. -/
theorem pullbackIdDiffeomorph_eq_pullbackLift
    (x : ManifoldTotalSpace F ((ContinuousMap.id B : B → B) *ᵖ E)) :
    pullbackIdDiffeomorph (n := n) (F := F) (E := E) IB IF x =
      homeomorph F E (Pullback.lift (ContinuousMap.id B) ((homeomorph F _).symm x)) := by
  obtain ⟨⟨b, y⟩, rfl⟩ := (homeomorph F ((ContinuousMap.id B : B → B) *ᵖ E)).surjective x
  rw [pullbackIdDiffeomorph_homeomorph, Homeomorph.symm_apply_apply]
  exact congrArg (homeomorph F E) (Pullback.lift_mk _ b y).symm

variable (n F E IB'' IF) in
/-- Pullback along a composite and successive pullback have canonically diffeomorphic
total spaces. Both atlases read the same original fibre coordinates, so the comparison is
`C^n` even when the continuous base maps are not smooth. -/
noncomputable def pullbackCompDiffeomorph (g : K) (f : K') :
    Diffeomorph (IB''.prod IF) (IB''.prod IF)
      (ManifoldTotalSpace F (((g : C(B', B)).comp (f : C(B'', B')) : B'' → B) *ᵖ E))
      (ManifoldTotalSpace F ((f : B'' → B') *ᵖ ((g : B' → B) *ᵖ E))) n where
  toFun := fiberwiseMap (E' := (f : B'' → B') *ᵖ ((g : B' → B) *ᵖ E)) fun _ ↦ id
  invFun := fiberwiseMap (E' := ((g : C(B', B)).comp (f : C(B'', B')) : B'' → B) *ᵖ E) fun _ ↦ id
  left_inv := congrFun ((fiberwiseMap_comp _ _).symm.trans fiberwiseMap_id)
  right_inv := congrFun ((fiberwiseMap_comp _ _).symm.trans fiberwiseMap_id)
  contMDiff_toFun := ContMDiff.congr (fun x ↦ by
    refine ManifoldTotalSpace.contMDiffAt_iff.2
      ⟨contMDiff_proj n F _ IB'' IF x, ?_⟩
    exact (contMDiffAt_trivializationAt_snd n IB'' IF x).congr_of_eventuallyEq
      (.of_forall fun y ↦ Pullback.trivializationAt_pullback_snd g f _ _))
    fun x ↦ (homeomorph F _).symm.injective <|
      (homeomorph_symm_fiberwiseMap _ x).trans (Homeomorph.symm_apply_apply _ _).symm
  contMDiff_invFun := ContMDiff.congr (fun x ↦ by
    refine ManifoldTotalSpace.contMDiffAt_iff.2
      ⟨contMDiff_proj n F _ IB'' IF x, ?_⟩
    exact (contMDiffAt_trivializationAt_snd n IB'' IF x).congr_of_eventuallyEq
      (.of_forall fun y ↦ (Pullback.trivializationAt_pullback_snd g f _ _).symm))
    fun x ↦ (homeomorph F _).symm.injective <|
      (homeomorph_symm_fiberwiseMap _ x).trans (Homeomorph.symm_apply_apply _ _).symm

/-- The composition comparison is the fibrewise identity map. -/
theorem coe_pullbackCompDiffeomorph (g : K) (f : K') :
    ⇑(pullbackCompDiffeomorph (n := n) (F := F) (E := E) IB'' IF g f) =
      fiberwiseMap (E := (((g : C(B', B)).comp (f : C(B'', B')) : B'' → B) *ᵖ E))
        (E' := ((f : B'' → B') *ᵖ ((g : B' → B) *ᵖ E))) (fun _ ↦ id) :=
  funext fun _ ↦ rfl

/-- The inverse composition comparison is the fibrewise identity map. -/
theorem coe_pullbackCompDiffeomorph_symm (g : K) (f : K') :
    ⇑(pullbackCompDiffeomorph (n := n) (F := F) (E := E) IB'' IF g f).symm =
      fiberwiseMap (E := ((f : B'' → B') *ᵖ ((g : B' → B) *ᵖ E)))
        (E' := (((g : C(B', B)).comp (f : C(B'', B')) : B'' → B) *ᵖ E)) (fun _ ↦ id) :=
  funext fun _ ↦ rfl

/-- The composition comparison preserves the displayed base point and fibre element. -/
theorem pullbackCompDiffeomorph_homeomorph (g : K) (f : K')
    (p : TotalSpace F (((g : C(B', B)).comp (f : C(B'', B')) : B'' → B) *ᵖ E)) :
    pullbackCompDiffeomorph (n := n) (F := F) (E := E) IB'' IF g f
        (homeomorph F (((g : C(B', B)).comp (f : C(B'', B')) : B'' → B) *ᵖ E) p) =
      homeomorph F ((f : B'' → B') *ᵖ ((g : B' → B) *ᵖ E)) ⟨p.proj, p.2⟩ :=
  fiberwiseMap_homeomorph _ p

/-- The inverse composition comparison preserves the displayed base point and fibre element. -/
theorem pullbackCompDiffeomorph_symm_homeomorph (g : K) (f : K')
    (p : TotalSpace F ((f : B'' → B') *ᵖ ((g : B' → B) *ᵖ E))) :
    (pullbackCompDiffeomorph (n := n) (F := F) (E := E) IB'' IF g f).symm
        (homeomorph F ((f : B'' → B') *ᵖ ((g : B' → B) *ᵖ E)) p) =
      homeomorph F (((g : C(B', B)).comp (f : C(B'', B')) : B'' → B) *ᵖ E) ⟨p.proj, p.2⟩ :=
  fiberwiseMap_homeomorph _ p

/-- Reading the composition comparison in the iterated pullback preserves both components. -/
theorem homeomorph_symm_pullbackCompDiffeomorph (g : K) (f : K')
    (x : ManifoldTotalSpace F (((g : C(B', B)).comp (f : C(B'', B')) : B'' → B) *ᵖ E)) :
    (homeomorph F ((f : B'' → B') *ᵖ ((g : B' → B) *ᵖ E))).symm
        (pullbackCompDiffeomorph (n := n) (F := F) (E := E) IB'' IF g f x) =
      ⟨((homeomorph F _).symm x).proj, ((homeomorph F _).symm x).2⟩ :=
  homeomorph_symm_fiberwiseMap _ x

/-- Reading the inverse composition comparison in the composite pullback preserves both
components. -/
theorem homeomorph_symm_pullbackCompDiffeomorph_symm (g : K) (f : K')
    (x : ManifoldTotalSpace F ((f : B'' → B') *ᵖ ((g : B' → B) *ᵖ E))) :
    (homeomorph F (((g : C(B', B)).comp (f : C(B'', B')) : B'' → B) *ᵖ E)).symm
        ((pullbackCompDiffeomorph (n := n) (F := F) (E := E) IB'' IF g f).symm x) =
      ⟨((homeomorph F _).symm x).proj, ((homeomorph F _).symm x).2⟩ :=
  homeomorph_symm_fiberwiseMap _ x

/-- The comparison intertwines the lift from a composite pullback with the two successive
lifts to the original bundle. This identity does not require smoothness of the base maps. -/
theorem pullbackLift_pullbackLift_homeomorph_symm_pullbackCompDiffeomorph
    (g : K) (f : K')
    (x : ManifoldTotalSpace F (((g : C(B', B)).comp (f : C(B'', B')) : B'' → B) *ᵖ E)) :
    Pullback.lift g (Pullback.lift f
      ((homeomorph F ((f : B'' → B') *ᵖ ((g : B' → B) *ᵖ E))).symm
        (pullbackCompDiffeomorph (n := n) (F := F) (E := E) IB'' IF g f x))) =
        Pullback.lift ((g : C(B', B)).comp (f : C(B'', B')))
          ((homeomorph F (((g : C(B', B)).comp (f : C(B'', B')) : B'' → B) *ᵖ E)).symm x) := by
  obtain ⟨⟨b, y⟩, rfl⟩ :=
    (homeomorph F (((g : C(B', B)).comp (f : C(B'', B')) : B'' → B) *ᵖ E)).surjective x
  rw [homeomorph_symm_pullbackCompDiffeomorph, Homeomorph.symm_apply_apply]
  exact (congrArg (Pullback.lift g) (Pullback.lift_mk f b y)).trans
    ((Pullback.lift_mk g (f b) y).trans
      (Pullback.lift_mk ((g : C(B', B)).comp (f : C(B'', B'))) b y).symm)

/-- The inverse comparison intertwines the composite lift with the two successive lifts. -/
theorem pullbackLift_homeomorph_symm_pullbackCompDiffeomorph_symm
    (g : K) (f : K')
    (x : ManifoldTotalSpace F ((f : B'' → B') *ᵖ ((g : B' → B) *ᵖ E))) :
    Pullback.lift ((g : C(B', B)).comp (f : C(B'', B')))
      ((homeomorph F (((g : C(B', B)).comp (f : C(B'', B')) : B'' → B) *ᵖ E)).symm
        ((pullbackCompDiffeomorph (n := n) (F := F) (E := E) IB'' IF g f).symm x)) =
      Pullback.lift g (Pullback.lift f ((homeomorph F _).symm x)) := by
  obtain ⟨⟨b, y⟩, rfl⟩ := (homeomorph F ((f : B'' → B') *ᵖ ((g : B' → B) *ᵖ E))).surjective x
  rw [homeomorph_symm_pullbackCompDiffeomorph_symm, Homeomorph.symm_apply_apply]
  exact ((congrArg (Pullback.lift g) (Pullback.lift_mk f b y)).trans
    ((Pullback.lift_mk g (f b) y).trans
      (Pullback.lift_mk ((g : C(B', B)).comp (f : C(B'', B'))) b y).symm)).symm

/-- Composing a base map on the right with the identity gives the inverse of the identity
comparison on the pulled-back bundle. This is the right unit law for the composition
comparison. -/
@[simp]
theorem pullbackCompDiffeomorph_id_right (g : K) :
    pullbackCompDiffeomorph (n := n) (F := F) (E := E) IB' IF g (ContinuousMap.id B') =
      (pullbackIdDiffeomorph (n := n) (F := F) (E := (g : B' → B) *ᵖ E) IB' IF).symm := by
  -- Both comparisons keep the point in the same fibre; composition with the identity
  -- reduces to the same continuous base map and hence the same pullback topology.
  ext x
  rfl

section Actions

variable {A : Type*} [∀ b, SMul A (E b)]

-- Each comparison is the fibrewise identity, and the scalar action on a pullback fibre is by
-- definition (`Bundle.Pullback.instSMul`) the action on the original fibre, so the fibre maps
-- are equivariant by `rfl`.

/-- The identity comparison intertwines fibrewise scalar multiplication. In particular it is an
equivariant isomorphism for the right action of a principal bundle. -/
theorem pullbackIdDiffeomorph_smul (a : A)
    (x : ManifoldTotalSpace F ((ContinuousMap.id B : B → B) *ᵖ E)) :
    pullbackIdDiffeomorph (n := n) (F := F) (E := E) IB IF (a • x) =
      a • pullbackIdDiffeomorph (n := n) (F := F) (E := E) IB IF x :=
  fiberwiseMap_smul _ a (fun _ _ ↦ by rfl) x

/-- The inverse identity comparison intertwines fibrewise scalar multiplication. -/
theorem pullbackIdDiffeomorph_symm_smul (a : A) (x : ManifoldTotalSpace F E) :
    (pullbackIdDiffeomorph (n := n) (F := F) (E := E) IB IF).symm (a • x) =
      a • (pullbackIdDiffeomorph (n := n) (F := F) (E := E) IB IF).symm x :=
  fiberwiseMap_smul _ a (fun _ _ ↦ by rfl) x

/-- The composition comparison intertwines fibrewise scalar multiplication. In particular it is an
equivariant isomorphism between the composite and iterated pullbacks of a principal bundle. -/
theorem pullbackCompDiffeomorph_smul (g : K) (f : K') (a : A)
    (x : ManifoldTotalSpace F (((g : C(B', B)).comp (f : C(B'', B')) : B'' → B) *ᵖ E)) :
    pullbackCompDiffeomorph (n := n) (F := F) (E := E) IB'' IF g f (a • x) =
      a • pullbackCompDiffeomorph (n := n) (F := F) (E := E) IB'' IF g f x :=
  fiberwiseMap_smul _ a (fun _ _ ↦ by rfl) x

/-- The inverse composition comparison intertwines fibrewise scalar multiplication. -/
theorem pullbackCompDiffeomorph_symm_smul (g : K) (f : K') (a : A)
    (x : ManifoldTotalSpace F ((f : B'' → B') *ᵖ ((g : B' → B) *ᵖ E))) :
    (pullbackCompDiffeomorph (n := n) (F := F) (E := E) IB'' IF g f).symm (a • x) =
      a • (pullbackCompDiffeomorph (n := n) (F := F) (E := E) IB'' IF g f).symm x :=
  fiberwiseMap_smul _ a (fun _ _ ↦ by rfl) x

end Actions

end TauCeti.ManifoldTotalSpace

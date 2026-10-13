/-
Copyright (c) 2026 Wentao Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wentao Li
-/
module

public import TauCeti.Algebra.Homology.Curved.Module.Right.Biproduct
public import TauCeti.Algebra.Homology.Curved.Module.Right.Homotopy
public import TauCeti.Algebra.Homology.Curved.Module.Right.Shift
public import TauCeti.Algebra.Homology.SquareZero

/-!
# Mapping cones of curved differential graded right modules

The cone of a closed map `f : M ⟶ N` has underlying graded right module `M[1] × N` and
differential `(x, y) ↦ (-dM x, f x + dN y)`. The two off-diagonal terms in its square cancel
because `f` commutes with the differentials. Its curvature is therefore the same as the
curvature of `M` and `N`, without a centrality assumption.

The right action is unchanged. The canonical inclusion of `N` and projection to `M[1]` are
closed maps, and the adjacent composites vanish in the existing homotopy category.

## References

* L. Positselski, *Differential graded Koszul duality: an introductory survey*, Sections 6.2
  and 7.6. His curvature is the negative of the right-module curvature stored here.
* The Tau Ceti contributors, `TauCeti.Algebra.Homology.Curved.Cone.Basic`: the curved-duplex
  cone formalization is the precedent for the cone, its maps and its contraction interface.
-/

public section

open CategoryTheory MulOpposite

namespace TauCeti.CurvedDGRightModuleCat

universe u

-- The closed category retains its enriched object carriers.
attribute [local implicit_reducible] ForgetEnrichment EnrichedFunctor.ofDGMap

variable {R A : Type u} [CommRing R] [Ring A] [Algebra R A]
  {𝒜 : ℤ → Submodule R A} [GradedAlgebra 𝒜] {d : A →ₗ[R] A} {w : A}
  {h : IsCurvedDGAlgebra 𝒜 d w} {M N : CurvedDGRightModuleCat.{u, u, u} h}

variable (f : ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) M ⟶
  ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) N)

/-- The cone differential uses the linear mapping-cone construction on the ground-ring maps. -/
noncomputable def coneDifferential : M × N →ₗ[R] M × N :=
  LinearMap.mappingCone M.differential N.differential ((closedHom f).restrictScalars R)

/-- The cone differential has diagonal entries `-dM` and `dN` and lower-left entry `f`. -/
@[simp]
theorem coneDifferential_apply (x : M × N) :
    coneDifferential f x = (-M.differential x.1, closedHom f x.1 + N.differential x.2) := by
  simp only [coneDifferential, LinearMap.mappingCone_apply, LinearMap.restrictScalars_apply]

/-- The cone of a closed map, with grading `M[1] × N` and the original curvature. -/
@[expose, implicit_reducible]
noncomputable def cone : CurvedDGRightModuleCat.{u, u, u} h := by
  let P := (M.shift 1).prod N
  letI : DirectSum.Decomposition P.grading := P.decomposition
  letI : SetLike.GradedSMul (InternalGrading.ofDecomposition 𝒜).opposite.piece P.grading :=
    P.gradedSMul
  refine
    { carrier := M × N
      grading := P.grading
      differential := coneDifferential f
      isCurvedDGRightModule := ?_ }
  refine ⟨?_, ?_, ?_⟩
  · apply LinearMap.isHomogeneous_def.mpr
    intro p x hx
    simp only [P, prod_grading, shift_grading, Submodule.mem_prod] at hx ⊢
    rw [coneDifferential_apply]
    exact ⟨(M.grading ((p + 1) + 1)).neg_mem
        (M.isCurvedDGRightModule.isHomogeneous.map_mem hx.1),
      (N.grading (p + 1)).add_mem (closedHom_mem f hx.1)
        (N.isCurvedDGRightModule.isHomogeneous.map_mem hx.2)⟩
  · intro p x hx a
    simp only [P, prod_grading, shift_grading, Submodule.mem_prod] at hx
    simp only [coneDifferential_apply]
    apply Prod.ext
    · -- The cone inherits the product action, so its first component is the original
      -- action on `M`; the shift changes the grading and differential only.
      change -M.differential (op a • x.1) =
        op a • (-M.differential x.1) + p.negOnePow • (op (d a) • x.1)
      rw [M.isCurvedDGRightModule.leibniz hx.1 a, Int.negOnePow_add, Int.negOnePow_one]
      simp [add_comm]
    · -- The second component inherits the action on `N`. This reduction aligns the
      -- bundled cone's action with the componentwise right-linear and Leibniz formulas.
      change closedHom f (op a • x.1) + N.differential (op a • x.2) =
        op a • (closedHom f x.1 + N.differential x.2) +
          p.negOnePow • (op (d a) • x.2)
      rw [map_smul, N.isCurvedDGRightModule.leibniz hx.2 a, smul_add]
      abel
  · intro x
    simp only [coneDifferential_apply, map_neg, map_add, differential_closedHom,
      M.isCurvedDGRightModule.sq_eq, N.isCurvedDGRightModule.sq_eq, neg_neg,
      neg_add_cancel_left]
    -- The square is right multiplication by the same curvature in both components;
    -- the inherited product action computes componentwise on the bundled cone.
    rfl

/-- The degree-`p` part of the cone is `Mᵖ⁺¹ × Nᵖ`. -/
@[simp]
theorem cone_grading (p : ℤ) :
    (cone f).grading p = (M.grading (p + 1)).prod (N.grading p) := by
  simp only [cone, prod_grading, shift_grading]

/-- The differential on the cone acts by the usual block formula. -/
@[simp]
theorem cone_differential_apply (x : M × N) :
    (cone f).differential x = (-M.differential x.1, closedHom f x.1 + N.differential x.2) :=
  coneDifferential_apply f x

/-- The closed inclusion of the codomain into its cone. -/
noncomputable def coneInclusion :
    ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) N ⟶
      ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) (cone f) :=
  closedHomOf (LinearMap.inr Aᵐᵒᵖ M N)
    (fun p x hx ↦ by rw [cone_grading]; exact ⟨(M.grading (p + 1)).zero_mem, hx⟩)
    (fun x ↦ by
      -- The right-linear inclusion is the second inclusion of the cone's product carrier.
      change (cone f).differential (0, x) = (0, N.differential x)
      rw [cone_differential_apply]
      simp)

/-- The closed projection from the cone to the cohomological shift of its domain. -/
noncomputable def coneProjection :
    ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) (cone f) ⟶
      ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) (M.shift 1) :=
  closedHomOf (LinearMap.fst Aᵐᵒᵖ M N)
    (fun p x hx ↦ by rw [cone_grading] at hx; rw [shift_grading]; exact hx.1)
    (fun x ↦ by
      -- Evaluate the first projection before comparing the two differential formulas.
      change (M.shift 1).differential x.1 = ((cone f).differential x).1
      rw [shift_one_differential_apply, cone_differential_apply])

/-- The cone inclusion is the usual second linear inclusion. -/
@[simp]
theorem closedHom_coneInclusion : closedHom (coneInclusion f) = LinearMap.inr Aᵐᵒᵖ M N := by
  dsimp only [coneInclusion]
  exact closedHom_closedHomOf _ _ _

/-- The cone projection is the usual first linear projection. -/
@[simp]
theorem closedHom_coneProjection : closedHom (coneProjection f) = LinearMap.fst Aᵐᵒᵖ M N := by
  dsimp only [coneProjection]
  exact closedHom_closedHomOf _ _ _

/-- The inclusion followed by the projection vanishes already in the closed category. -/
@[reassoc (attr := simp), simp]
theorem coneInclusion_comp_coneProjection : coneInclusion f ≫ coneProjection f = 0 := by
  apply closedHom_ext
  intro x
  simp only [closedHom_comp, closedHom_coneInclusion, closedHom_coneProjection, closedHom_zero]
  rfl

/-- The first linear inclusion, viewed as a degree-minus-one homotopy into the cone. -/
noncomputable def coneInclusionHomotopy :
    dgRightModuleCochains (R := R) (A := A) (ℳ := M.grading) (ℳN := (cone f).grading) (-1) := by
  refine ⟨LinearMap.inl Aᵐᵒᵖ M N, dgRightModuleCochains.mem_iff.mpr ?_⟩
  apply LinearMap.isHomogeneous_def.mpr
  intro p x hx
  rw [cone_grading]
  -- Evaluate the first linear inclusion; degree minus one cancels the cone's domain shift.
  change (x, 0) ∈ (M.grading ((p + -1) + 1)).prod (N.grading (p + -1))
  simpa using And.intro hx ((N.grading (p + -1)).zero_mem)

/-- The homotopy for the first adjacent composite sends `x` to `(x, 0)`. -/
@[simp]
theorem coneInclusionHomotopy_apply (x : M) : (coneInclusionHomotopy f).1 x = (x, 0) :=
  (rfl)

/-- The first adjacent composite is the boundary of the first inclusion homotopy. -/
theorem comp_coneInclusion_boundary (x : M) :
    closedHom (f ≫ coneInclusion f) x =
      (cone f).differential ((coneInclusionHomotopy f).1 x) +
        (coneInclusionHomotopy f).1 (M.differential x) := by
  rw [closedHom_comp, LinearMap.comp_apply, closedHom_coneInclusion]
  simp only [coneInclusionHomotopy_apply, cone_differential_apply, map_zero, add_zero]
  -- The bundled cone inherits the product addition, so the boundary is componentwise.
  change (0, closedHom f x) = (-M.differential x, closedHom f x) + (M.differential x, 0)
  exact Prod.ext (neg_add_cancel _).symm (add_zero _).symm

/-- The second projection, viewed as a degree-minus-one homotopy to the shifted codomain. -/
noncomputable def coneProjectionHomotopy :
    dgRightModuleCochains (R := R) (A := A) (ℳ := (cone f).grading)
      (ℳN := (N.shift 1).grading) (-1) := by
  refine ⟨LinearMap.snd Aᵐᵒᵖ M N, dgRightModuleCochains.mem_iff.mpr ?_⟩
  apply LinearMap.isHomogeneous_def.mpr
  intro p x hx
  rw [cone_grading] at hx
  rw [shift_grading]
  -- Evaluate the second linear projection into the shifted codomain's homogeneous piece.
  change x.2 ∈ N.grading ((p + -1) + 1)
  simpa using hx.2

/-- The homotopy for the third adjacent composite sends `(x, y)` to `y`. -/
@[simp]
theorem coneProjectionHomotopy_apply (x : M × N) : (coneProjectionHomotopy f).1 x = x.2 :=
  (rfl)

/-- The projection followed by the shifted map is the boundary of the second projection. -/
theorem coneProjection_comp_shift_boundary (x : M × N) :
    closedHom (coneProjection f ≫ (closedShiftFunctor 1).map f) x =
      (N.shift 1).differential ((coneProjectionHomotopy f).1 x) +
        (coneProjectionHomotopy f).1 ((cone f).differential x) := by
  simp only [closedHom_comp, closedHom_coneProjection, closedHom_closedShiftFunctor_map,
    LinearMap.comp_apply, coneProjectionHomotopy_apply, cone_differential_apply,
    shift_one_differential_apply]
  -- Evaluate the first projection and the degree-zero shifted map on the product carrier.
  change closedHom f x.1 = -N.differential x.2 + (closedHom f x.1 + N.differential x.2)
  abel

-- The quotient keeps the objects, so its map has the same closed representative.
attribute [local implicit_reducible] dgClosedToHomotopy
  DGHomotopyCategory.of DGHomotopyCategory.underlying

/-- The first adjacent composite vanishes in the curved homotopy category. -/
-- Reduce the zero composite before dgClosedToHomotopy_map expands its representatives.
@[reassoc (attr := simp↓), simp↓]
theorem quotient_map_comp_coneInclusion :
    (dgClosedToHomotopy R).map f ≫ (dgClosedToHomotopy R).map (coneInclusion f) = 0 := by
  rw [← Functor.map_comp, dgClosedToHomotopy_map_eq_zero_iff, mem_dgBoundaries_iff]
  refine ⟨coneInclusionHomotopy f, fun x ↦ ?_⟩
  rw [← closedHom_eq]
  exact comp_coneInclusion_boundary f x

/-- The third adjacent composite also vanishes in the curved homotopy category. -/
-- Reduce the zero composite before dgClosedToHomotopy_map expands its representatives.
@[reassoc (attr := simp↓), simp↓]
theorem quotient_map_coneProjection_comp_shift :
    (dgClosedToHomotopy R).map (coneProjection f) ≫
      (dgClosedToHomotopy R).map ((closedShiftFunctor 1).map f) = 0 := by
  rw [← Functor.map_comp, dgClosedToHomotopy_map_eq_zero_iff, mem_dgBoundaries_iff]
  refine ⟨coneProjectionHomotopy f, fun x ↦ ?_⟩
  rw [← closedHom_eq]
  exact coneProjection_comp_shift_boundary f x

/-- The contracting homotopy of the cone of an isomorphism applies its inverse to the
second component and includes the result into the first component. -/
noncomputable def coneContraction [IsIso f] :
    dgRightModuleCochains (R := R) (A := A) (ℳ := (cone f).grading)
      (ℳN := (cone f).grading) (-1) := by
  refine ⟨(LinearMap.inl Aᵐᵒᵖ M N).comp
    ((closedHom (inv f)).comp (LinearMap.snd Aᵐᵒᵖ M N)),
      dgRightModuleCochains.mem_iff.mpr ?_⟩
  apply LinearMap.isHomogeneous_def.mpr
  intro p x hx
  rw [cone_grading] at hx ⊢
  -- Evaluate the composed projection, inverse and inclusion on the product carrier.
  change (closedHom (inv f) x.2, 0) ∈
    (M.grading ((p + -1) + 1)).prod (N.grading (p + -1))
  simpa using And.intro (closedHom_mem (inv f) hx.2) ((N.grading (p + -1)).zero_mem)

/-- The contraction sends `(x, y)` to `(f⁻¹ y, 0)`. -/
@[simp]
theorem coneContraction_apply [IsIso f] (x : M × N) :
    (coneContraction f).1 x = (closedHom (inv f) x.2, 0) :=
  (rfl)

variable
  (g : ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) N ⟶
    ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) M)
  (α : dgRightModuleCochains (R := R) (A := A) (ℳ := M.grading) (ℳN := M.grading) (-1))
  (β : dgRightModuleCochains (R := R) (A := A) (ℳ := N.grading) (ℳN := N.grading) (-1))

/-- A corrected degree-minus-one cochain for a closed map `g` and cochains `α`, `β`.
For `t = f ∘ α - β ∘ f`, its matrix is `(α - g ∘ t, g; β ∘ t, -β)`.
It is a contraction when the inverse-homotopy equations in
`coneHomotopyContraction_boundary` hold. -/
noncomputable def coneHomotopyContraction :
    dgRightModuleCochains (R := R) (A := A) (ℳ := (cone f).grading)
      (ℳN := (cone f).grading) (-1) := by
  let t : M →ₗ[Aᵐᵒᵖ] N := (closedHom f).comp α.1 - β.1.comp (closedHom f)
  refine ⟨((α.1.comp (LinearMap.fst Aᵐᵒᵖ M N) -
      (closedHom g).comp (t.comp (LinearMap.fst Aᵐᵒᵖ M N))) +
      (closedHom g).comp (LinearMap.snd Aᵐᵒᵖ M N)).prod
    (β.1.comp (t.comp (LinearMap.fst Aᵐᵒᵖ M N)) -
      β.1.comp (LinearMap.snd Aᵐᵒᵖ M N)), dgRightModuleCochains.mem_iff.mpr ?_⟩
  apply LinearMap.isHomogeneous_def.mpr
  intro p x hx
  rw [cone_grading] at hx ⊢
  have hαx : α.1 x.1 ∈ M.grading p := by
    simpa [add_assoc] using dgRightModuleCochains.map_mem α hx.1
  have htx : t x.1 ∈ N.grading p := by
    dsimp only [t, LinearMap.sub_apply, LinearMap.comp_apply]
    exact (N.grading p).sub_mem (closedHom_mem f hαx)
      (by simpa [add_assoc] using dgRightModuleCochains.map_mem β (closedHom_mem f hx.1))
  -- The block map is evaluated on the product carrier; its first output has degree `p`
  -- in `M`, which is degree `p - 1` in the shifted domain component of the cone.
  change (α.1 x.1 - closedHom g (t x.1) + closedHom g x.2,
    β.1 (t x.1) - β.1 x.2) ∈
      (M.grading ((p + -1) + 1)).prod (N.grading (p + -1))
  simpa [add_assoc] using And.intro
    ((M.grading p).add_mem ((M.grading p).sub_mem hαx (closedHom_mem g htx))
      (closedHom_mem g hx.2))
    ((N.grading (p + -1)).sub_mem (dgRightModuleCochains.map_mem β htx)
      (dgRightModuleCochains.map_mem β hx.2))

/-- The corrected degree-minus-one cochain has this block formula on the cone carrier. -/
@[simp]
theorem coneHomotopyContraction_apply (x : M × N) :
    (coneHomotopyContraction f g α β).1 x =
      (α.1 x.1 - closedHom g (closedHom f (α.1 x.1) - β.1 (closedHom f x.1)) +
        closedHom g x.2,
      β.1 (closedHom f (α.1 x.1) - β.1 (closedHom f x.1)) - β.1 x.2) := by
  -- The cochain stores this product linear map; computing its two fields evaluates
  -- the block formula without rewriting through the bundled cone’s module instances.
  dsimp only [coneHomotopyContraction]
  rfl

variable
  (hα : ∀ x : M, closedHom g (closedHom f x) - x =
    M.differential (α.1 x) + α.1 (M.differential x))
  (hβ : ∀ x : N, closedHom f (closedHom g x) - x =
    N.differential (β.1 x) + β.1 (N.differential x))

include hα hβ in
/-- Inverse homotopies make the corrected contraction a boundary of the identity.
The correction uses the closed odd map `t = f ∘ α - β ∘ f`, so no coherence between the
chosen inverse homotopies, or zero-curvature hypothesis, is required. -/
theorem coneHomotopyContraction_boundary (x : M × N) :
    (cone f).differential ((coneHomotopyContraction f g α β).1 x) +
      (coneHomotopyContraction f g α β).1 ((cone f).differential x) = x := by
  let t : M →ₗ[Aᵐᵒᵖ] N := (closedHom f).comp α.1 - β.1.comp (closedHom f)
  have ht (z : M) : N.differential (t z) + t (M.differential z) = 0 := by
    have h₁ := congrArg (closedHom f) (hα z)
    simp only [map_sub, map_add] at h₁
    have h₂ := hβ (closedHom f z)
    rw [differential_closedHom] at h₂
    have heq := h₁.symm.trans h₂
    dsimp only [t, LinearMap.sub_apply, LinearMap.comp_apply]
    simp only [map_sub, differential_closedHom]
    convert sub_eq_zero.mpr heq using 1
    abel
  have hK (z : M × N) : (coneHomotopyContraction f g α β).1 z =
      (α.1 z.1 - closedHom g (t z.1) + closedHom g z.2,
        β.1 (t z.1) - β.1 z.2) := by
    simpa only [t, LinearMap.sub_apply, LinearMap.comp_apply] using
      coneHomotopyContraction_apply f g α β z
  simp only [hK, cone_differential_apply]
  apply Prod.ext
  · -- The cone retains product addition; evaluate its first component before the group identities.
    change -M.differential (α.1 x.1 - closedHom g (t x.1) + closedHom g x.2) +
      (α.1 (-M.differential x.1) - closedHom g (t (-M.differential x.1)) +
        closedHom g (closedHom f x.1 + N.differential x.2)) = x.1
    calc
      _ = x.1 + closedHom g (N.differential (t x.1) + t (M.differential x.1)) := by
        simp only [map_add, map_sub, map_neg, differential_closedHom]
        rw [(sub_eq_iff_eq_add).mp (hα x.1)]
        abel
      _ = x.1 := by rw [ht, map_zero, add_zero]
  · -- Its second component uses the same inherited product addition.
    change closedHom f (α.1 x.1 - closedHom g (t x.1) + closedHom g x.2) +
      N.differential (β.1 (t x.1) - β.1 x.2) +
        (β.1 (t (-M.differential x.1)) -
          β.1 (closedHom f x.1 + N.differential x.2)) = x.2
    calc
      _ = t x.1 - closedHom f (closedHom g (t x.1)) +
          (N.differential (β.1 (t x.1)) + β.1 (N.differential (t x.1))) + x.2 -
          β.1 (N.differential (t x.1) + t (M.differential x.1)) := by
        simp only [map_add, map_sub, map_neg]
        rw [(sub_eq_iff_eq_add).mp (hβ x.2)]
        dsimp only [t, LinearMap.sub_apply, LinearMap.comp_apply]
        abel
      _ = x.2 := by rw [← hβ (t x.1), ht, map_zero]; abel

/-- A closed map which becomes an isomorphism in the homotopy category has a contractible cone. -/
theorem isZero_homotopy_cone_isIso [IsIso ((dgClosedToHomotopy R).map f)] :
    CategoryTheory.Limits.IsZero (DGHomotopyCategory.of R (cone f)) := by
  obtain ⟨g, hg⟩ := (dgClosedToHomotopy R).map_surjective (inv ((dgClosedToHomotopy R).map f))
  have hleft : (dgClosedToHomotopy R).map (f ≫ g) =
      (dgClosedToHomotopy R).map (𝟙 (ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) M)) := by
    rw [CategoryTheory.Functor.map_comp, hg, CategoryTheory.Functor.map_id]
    exact IsIso.hom_inv_id _
  have hright : (dgClosedToHomotopy R).map (g ≫ f) =
      (dgClosedToHomotopy R).map (𝟙 (ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) N)) := by
    rw [CategoryTheory.Functor.map_comp, hg, CategoryTheory.Functor.map_id]
    exact IsIso.inv_hom_id _
  obtain ⟨α, hα⟩ := (quotient_map_eq_iff_exists_homotopy _ _).mp hleft
  obtain ⟨β, hβ⟩ := (quotient_map_eq_iff_exists_homotopy _ _).mp hright
  have hα' (z : M) : closedHom g (closedHom f z) - z =
      M.differential (α.1 z) + α.1 (M.differential z) := by
    simpa only [closedHom_comp, closedHom_id, LinearMap.comp_apply, LinearMap.id_apply] using hα z
  have hβ' (z : N) : closedHom f (closedHom g z) - z =
      N.differential (β.1 z) + β.1 (N.differential z) := by
    simpa only [closedHom_comp, closedHom_id, LinearMap.comp_apply, LinearMap.id_apply] using hβ z
  apply (CategoryTheory.Limits.IsZero.iff_id_eq_zero _).mpr
  have hz : (dgClosedToHomotopy R).map
      (𝟙 (ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) (cone f))) = 0 := by
    rw [dgClosedToHomotopy_map_eq_zero_iff, mem_dgBoundaries_iff]
    refine ⟨coneHomotopyContraction f g α β, fun z ↦ ?_⟩
    erw [← closedHom_eq, closedHom_id]
    exact (coneHomotopyContraction_boundary f g α β hα' hβ' z).symm
  exact ((dgClosedToHomotopy (C := CurvedDGRightModuleCat.{u, u, u} h) R).map_id
    (ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) (cone f))).symm.trans hz

/-- The strict inverse contraction is the zero-homotopy case of the corrected contraction. -/
@[simp]
theorem coneHomotopyContraction_inv_zero [IsIso f] :
    coneHomotopyContraction f (inv f) 0 0 = coneContraction f := by
  apply Subtype.ext
  apply LinearMap.ext
  intro x
  simp [coneHomotopyContraction_apply, coneContraction_apply]

/-- The strict contraction boundary follows from the general inverse-homotopy formula. -/
theorem coneContraction_boundary [IsIso f] (x : M × N) :
    (cone f).differential ((coneContraction f).1 x) +
      (coneContraction f).1 ((cone f).differential x) = x := by
  simpa only [coneHomotopyContraction_inv_zero] using
    coneHomotopyContraction_boundary f (inv f) 0 0
      (fun z ↦ by
        simpa only [closedHom_comp, closedHom_id, LinearMap.comp_apply,
          LinearMap.id_apply, Submodule.coe_zero, LinearMap.zero_apply, map_zero,
          add_zero, sub_eq_zero] using
          congrArg (fun k ↦ closedHom k z) (IsIso.hom_inv_id f))
      (fun z ↦ by
        simpa only [closedHom_comp, closedHom_id, LinearMap.comp_apply,
          LinearMap.id_apply, Submodule.coe_zero, LinearMap.zero_apply, map_zero,
          add_zero, sub_eq_zero] using
          congrArg (fun k ↦ closedHom k z) (IsIso.inv_hom_id f)) x


variable {M' N' : CurvedDGRightModuleCat.{u, u, u} h}
  (g : ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) M' ⟶
    ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) N')
  (a : ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) M ⟶
    ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) M')
  (b : ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) N ⟶
    ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) N')
  (k : dgRightModuleCochains (R := R) (A := A) (ℳ := M.grading) (ℳN := N'.grading) (-1))
  (hsq : ∀ x : M, closedHom b (closedHom f x) - closedHom g (closedHom a x) =
    N'.differential (k.1 x) + k.1 (M.differential x))

/-- A square commuting up to the specified odd homotopy induces a closed map of cones. -/
noncomputable def coneMap :
    ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) (cone f) ⟶
      ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) (cone g) :=
  closedHomOf ((closedHom a).prodMap (closedHom b) +
    (LinearMap.inr Aᵐᵒᵖ M' N').comp (k.1.comp (LinearMap.fst Aᵐᵒᵖ M N)))
    (fun p x hx ↦ by
      rw [cone_grading] at hx ⊢
      -- Evaluate the sum of the diagonal product map and the off-diagonal homotopy map.
      change (closedHom a x.1 + 0, closedHom b x.2 + k.1 x.1) ∈ _
      rw [add_zero]
      exact ⟨closedHom_mem a hx.1,
        (N'.grading p).add_mem (closedHom_mem b hx.2)
          (by simpa using dgRightModuleCochains.map_mem k hx.1)⟩)
    (fun x ↦ by
      rw [cone_differential_apply, cone_differential_apply]
      -- Evaluate the same block map on both sides of the closedness equation.
      change (-M'.differential (closedHom a x.1 + 0),
          closedHom g (closedHom a x.1 + 0) +
            N'.differential (closedHom b x.2 + k.1 x.1)) =
        (closedHom a (-M.differential x.1) + 0,
          closedHom b (closedHom f x.1 + N.differential x.2) + k.1 (-M.differential x.1))
      simp only [add_zero, map_add, map_neg, differential_closedHom]
      apply Prod.ext
      · rfl
      · rw [(sub_eq_iff_eq_add).mp (hsq x.1)]
        abel_nf)

/-- The underlying cone map has the homotopy as its lower-left entry. -/
theorem closedHom_coneMap :
    closedHom (coneMap f g a b k hsq) = (closedHom a).prodMap (closedHom b) +
      (LinearMap.inr Aᵐᵒᵖ M' N').comp (k.1.comp (LinearMap.fst Aᵐᵒᵖ M N)) := by
  dsimp only [coneMap]
  exact closedHom_closedHomOf _ _ _

/-- A cone map sends `(x, y)` to `(a x, b y + k x)`. -/
@[simp]
theorem closedHom_coneMap_apply (x : M × N) :
    closedHom (coneMap f g a b k hsq) x =
      (closedHom a x.1, closedHom b x.2 + k.1 x.1) := by
  rw [closedHom_coneMap]
  -- The underlying map is a sum of product maps on the explicit product carrier.
  change (closedHom a x.1 + 0, closedHom b x.2 + k.1 x.1) = _
  rw [add_zero]

/-- Cone maps commute with the canonical inclusions. -/
@[reassoc (attr := simp), simp]
theorem coneInclusion_comp_coneMap :
    coneInclusion f ≫ coneMap f g a b k hsq = b ≫ coneInclusion g := by
  apply closedHom_ext
  intro x
  simp only [closedHom_comp, LinearMap.comp_apply, closedHom_coneInclusion]
  -- Evaluate both second inclusions before applying the cone-map computation.
  change closedHom (coneMap f g a b k hsq) (0, x) = (0, closedHom b x)
  rw [closedHom_coneMap_apply, map_zero, map_zero, add_zero]

/-- Cone maps commute with the canonical projections and the shifted domain map. -/
@[reassoc (attr := simp), simp]
theorem coneMap_comp_coneProjection :
    coneMap f g a b k hsq ≫ coneProjection g =
      coneProjection f ≫ (closedShiftFunctor 1).map a := by
  apply closedHom_ext
  intro x
  erw [closedHom_comp, closedHom_comp, closedHom_coneProjection,
    closedHom_coneProjection, closedHom_closedShiftFunctor_map]
  -- The cone projection is the first projection, and the shifted map has the same carrier map.
  change (closedHom (coneMap f g a b k hsq) x).1 = closedHom a x.1
  rw [closedHom_coneMap_apply]

variable {M'' N'' : CurvedDGRightModuleCat.{u, u, u} h}

/-- The homotopy for a composite of two cone-map squares is `b' ∘ k + k' ∘ a`. -/
noncomputable def coneMapCompHomotopy
    (b' : ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) N' ⟶
      ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) N'')
    (k' : dgRightModuleCochains (R := R) (A := A)
      (ℳ := M'.grading) (ℳN := N''.grading) (-1)) :
    dgRightModuleCochains (R := R) (A := A)
      (ℳ := M.grading) (ℳN := N''.grading) (-1) :=
  dgRightModuleCochains.comp (dgClosedHomEquivZeroCocycles N' N'' b').1 k (by omega) +
    dgRightModuleCochains.comp k' (dgClosedHomEquivZeroCocycles M M' a).1 (by omega)

/-- The composite square homotopy evaluates by post- and precomposition. -/
@[simp]
theorem coneMapCompHomotopy_apply
    (b' : ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) N' ⟶
      ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) N'')
    (k' : dgRightModuleCochains (R := R) (A := A)
      (ℳ := M'.grading) (ℳN := N''.grading) (-1)) (x : M) :
    (coneMapCompHomotopy a k b' k').1 x = closedHom b' (k.1 x) + k'.1 (closedHom a x) := by
  simp only [coneMapCompHomotopy, dgRightModuleCochains.comp_apply,
    Submodule.coe_add, LinearMap.add_apply, coe_dgClosedHomEquivZeroCocycles_apply,
    ← closedHom_eq]

include hsq in
/-- The sum of the two square homotopies witnesses the composite square. -/
theorem coneMapCompHomotopy_boundary
    (j : ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) M'' ⟶
      ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) N'')
    (a' : ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) M' ⟶
      ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) M'')
    (b' : ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) N' ⟶
      ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) N'')
    (k' : dgRightModuleCochains (R := R) (A := A)
      (ℳ := M'.grading) (ℳN := N''.grading) (-1))
    (hsq' : ∀ x : M', closedHom b' (closedHom g x) - closedHom j (closedHom a' x) =
      N''.differential (k'.1 x) + k'.1 (M'.differential x)) (x : M) :
    closedHom (b ≫ b') (closedHom f x) - closedHom j (closedHom (a ≫ a') x) =
      N''.differential ((coneMapCompHomotopy a k b' k').1 x) +
        (coneMapCompHomotopy a k b' k').1 (M.differential x) := by
  have h₁ := congrArg (closedHom b') (hsq x)
  simp only [map_sub, map_add] at h₁
  have h₂ := hsq' (closedHom a x)
  rw [differential_closedHom] at h₂
  simp only [closedHom_comp, LinearMap.comp_apply, coneMapCompHomotopy_apply,
    map_add, differential_closedHom]
  calc
    _ = (closedHom b' (closedHom b (closedHom f x)) -
        closedHom b' (closedHom g (closedHom a x))) +
        (closedHom b' (closedHom g (closedHom a x)) -
          closedHom j (closedHom a' (closedHom a x))) := by abel
    _ = _ := by rw [h₁, h₂]; abel

/-- Cone maps compose using the induced composite square homotopy. -/
@[reassoc (attr := simp), simp]
theorem coneMap_comp
    (j : ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) M'' ⟶
      ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) N'')
    (a' : ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) M' ⟶
      ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) M'')
    (b' : ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) N' ⟶
      ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) N'')
    (k' : dgRightModuleCochains (R := R) (A := A)
      (ℳ := M'.grading) (ℳN := N''.grading) (-1))
    (hsq' : ∀ x : M', closedHom b' (closedHom g x) - closedHom j (closedHom a' x) =
      N''.differential (k'.1 x) + k'.1 (M'.differential x)) :
    coneMap f g a b k hsq ≫ coneMap g j a' b' k' hsq' =
      coneMap f j (a ≫ a') (b ≫ b') (coneMapCompHomotopy a k b' k')
        (coneMapCompHomotopy_boundary f g a b k hsq j a' b' k' hsq') := by
  apply closedHom_ext
  intro x
  simp only [closedHom_comp, LinearMap.comp_apply, closedHom_coneMap_apply,
    coneMapCompHomotopy_apply, map_add, add_assoc]

/-- The cone map of the identity square with zero homotopy is the identity. -/
@[simp]
theorem coneMap_id :
    coneMap f f (𝟙 _) (𝟙 _) 0 (by intro x; simp) =
      𝟙 (ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) (cone f)) := by
  apply closedHom_ext
  intro x
  simp only [closedHom_coneMap_apply, closedHom_id, LinearMap.id_apply,
    Submodule.coe_zero, LinearMap.zero_apply, add_zero]
  exact Prod.mk.eta

end TauCeti.CurvedDGRightModuleCat

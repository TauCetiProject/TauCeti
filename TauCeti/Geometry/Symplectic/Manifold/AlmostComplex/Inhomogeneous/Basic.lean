/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Manifold.AlmostComplex.Restriction
public import TauCeti.Geometry.Manifold.VectorBundle.Hom
import TauCeti.Geometry.Manifold.VectorBundle.Pullback

/-!
# Finite-regularity inhomogeneous terms

An inhomogeneous term is a native `Cⁿ` section of the Hom bundle from the pulled-back domain
tangent bundle to the vertical target tangent bundle, constrained by the existing pointwise
complex-antilinearity predicate. The constraint defines a submodule of the ambient section
space. No smooth bundle of antilinear maps is assumed for a merely finite-regularity structure.

The projection onto these sections lifts the existing `complexAntilinearPart` operator.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Appendix B (inhomogeneous Cauchy--Riemann equations).
-/

public noncomputable section

open Bundle
open scoped ContDiff Manifold

namespace TauCeti

variable {E H M EP HP P : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [NormedAddCommGroup EP] [NormedSpace ℝ EP] [TopologicalSpace HP]
  {IP : ModelWithCorners ℝ EP HP} [TopologicalSpace P] [ChartedSpace HP P]
  [IsManifold IP ∞ P]

/-- The domain tangent bundle pulled back to the product of domain and target. -/
abbrev horizontalTangentBundle (I : ModelWithCorners ℝ E H) (M : Type*)
    [TopologicalSpace M] [ChartedSpace H M] (IP : ModelWithCorners ℝ EP HP) (P : Type*)
    [TopologicalSpace P] [ChartedSpace HP P] :=
  ((ContMDiffMap.fst : C^∞⟮IP.prod I, P × M; IP, P⟯) : P × M → P) *ᵖ (TangentSpace IP)

/-- The native ambient Hom-section space for a domain-dependent forcing term. -/
abbrev DomainDependentHomSection (I : ModelWithCorners ℝ E H) (M : Type*)
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    (IP : ModelWithCorners ℝ EP HP) (P : Type*) [TopologicalSpace P] [ChartedSpace HP P]
    [IsManifold IP ∞ P] (n : ℕ∞) :=
  Cₛ^n⟮IP.prod I; EP →L[ℝ] E,
    fun q : P × M ↦ horizontalTangentBundle I M IP P q →L[ℝ] verticalTangentBundle I M IP P q⟯

variable {n : ℕ∞}

namespace ContMDiffAlmostComplexStructure

/-- The source complex structure pulled back as a native horizontal endomorphism section. -/
def horizontalEndomorphism (j : ContMDiffAlmostComplexStructure IP n P) :
    Cₛ^n⟮IP.prod I; EP →L[ℝ] EP,
      fun q : P × M ↦ horizontalTangentBundle I M IP P q →L[ℝ]
        horizontalTangentBundle I M IP P q⟯ :=
  ⟨fun q ↦ j.toEndomorphism q.1,
    (Pullback.contMDiff_hom_section_iff
      (ContMDiffMap.fst : C^∞⟮IP.prod I, P × M; IP, P⟯) contMDiff_fst _).mpr
        (j.toEndomorphism.contMDiff.comp contMDiff_fst)⟩

omit [IsManifold I ∞ M] in
@[simp]
theorem horizontalEndomorphism_apply (j : ContMDiffAlmostComplexStructure IP n P) (q : P × M) :
    horizontalEndomorphism (I := I) (M := M) j q = j.toEndomorphism q.1 := (rfl)

omit [IsManifold I ∞ M] in
/-- The horizontal pullback retains the square-minus-identity equation. -/
theorem horizontalEndomorphism_apply_apply (j : ContMDiffAlmostComplexStructure IP n P)
    (q : P × M) (v : horizontalTangentBundle I M IP P q) :
    j.horizontalEndomorphism (I := I) (M := M) q
      (j.horizontalEndomorphism (I := I) (M := M) q v) = -v := by
  -- Pullback fibres inherit their operations from the original tangent-space type synonym.
  change j.toEndomorphism q.1 (j.toEndomorphism q.1 v) = -v
  exact j.apply_apply q.1 v

end ContMDiffAlmostComplexStructure

/-- The submodule of native Hom sections satisfying complex antilinearity in every fibre. -/
def inhomogeneousTerms (j : ContMDiffAlmostComplexStructure IP n P)
    (J : ContMDiffAlmostComplexStructureFamily I M IP P n) :
    Submodule ℝ (DomainDependentHomSection I M IP P n) where
  carrier := {ν | ∀ q, IsComplexAntilinear
    (j.horizontalEndomorphism (I := I) (M := M) q).toLinearMap
    (J.toEndomorphism q).toLinearMap (ν q).toLinearMap}
  zero_mem' q := by
    simpa only [ContMDiffSection.coe_zero, Pi.zero_apply,
      ContinuousLinearMap.toLinearMap_zero] using mem_complexAntilinearMaps.mp
      (complexAntilinearMaps (j.horizontalEndomorphism (I := I) (M := M) q).toLinearMap
        (J.toEndomorphism q).toLinearMap).zero_mem
  add_mem' hν hμ q := by
    simpa only [ContMDiffSection.coe_add, Pi.add_apply,
      ContinuousLinearMap.toLinearMap_add] using mem_complexAntilinearMaps.mp
      ((complexAntilinearMaps (j.horizontalEndomorphism (I := I) (M := M) q).toLinearMap
        (J.toEndomorphism q).toLinearMap).add_mem
          (mem_complexAntilinearMaps.mpr (hν q)) (mem_complexAntilinearMaps.mpr (hμ q)))
  smul_mem' c ν hν q := by
    simpa only [ContMDiffSection.coe_smul, Pi.smul_apply,
      ContinuousLinearMap.toLinearMap_smul] using mem_complexAntilinearMaps.mp
      ((complexAntilinearMaps (j.horizontalEndomorphism (I := I) (M := M) q).toLinearMap
        (J.toEndomorphism q).toLinearMap).smul_mem c (mem_complexAntilinearMaps.mpr (hν q)))

/-- A finite-regularity forcing term, using the native submodule carrier and its real module
operations. -/
abbrev InhomogeneousTerm (j : ContMDiffAlmostComplexStructure IP n P)
    (J : ContMDiffAlmostComplexStructureFamily I M IP P n) :=
  ↥(inhomogeneousTerms j J)

@[simp]
theorem mem_inhomogeneousTerms (j : ContMDiffAlmostComplexStructure IP n P)
    (J : ContMDiffAlmostComplexStructureFamily I M IP P n)
    (ν : DomainDependentHomSection I M IP P n) :
    ν ∈ inhomogeneousTerms j J ↔ ∀ q, IsComplexAntilinear
      (j.horizontalEndomorphism (I := I) (M := M) q).toLinearMap
      (J.toEndomorphism q).toLinearMap (ν q).toLinearMap :=
  Iff.rfl

namespace DomainDependentHomSection

/-- Read a native pulled-back Hom section between the original domain and target tangent
spaces. This bridge keeps its intrinsic and pulled-back fibre instances explicit. -/
def tangentHom (A : DomainDependentHomSection I M IP P n) (q : P × M) :
    TangentSpace IP q.1 →L[ℝ] TangentSpace I q.2 :=
  A q

/-- The two tangent-Hom presentations agree on vectors. -/
theorem tangentHom_apply (A : DomainDependentHomSection I M IP P n) (q : P × M)
    (v : TangentSpace IP q.1) : A.tangentHom q v = A q v := (rfl)

/-- Reading the original tangent fibres preserves native Hom-section regularity. -/
theorem contMDiff_tangentHom (A : DomainDependentHomSection I M IP P n) :
    ContMDiff (IP.prod I) ((IP.prod I).prod 𝓘(ℝ, EP →L[ℝ] E)) n
      (fun q : P × M ↦ TotalSpace.mk' (EP →L[ℝ] E)
        (E := fun q : P × M ↦ horizontalTangentBundle I M IP P q →L[ℝ]
          verticalTangentBundle I M IP P q) q (A.tangentHom q)) := by
  exact A.contMDiff.congr fun _ ↦ rfl

/-- Restrict a native ambient Hom section to the intrinsic tangent bundles of an open product. -/
def restrictOpen (A : DomainDependentHomSection I M IP P n)
    (U : TopologicalSpace.Opens P) (V : TopologicalSpace.Opens M) :
    DomainDependentHomSection I V IP U n :=
  ⟨Manifold.restrictOpenTangentSpaceHom A.tangentHom U V,
    Manifold.contMDiff_restrictOpenTangentSpaceHom A.tangentHom U V A.contMDiff_tangentHom⟩

@[simp]
theorem restrictOpen_apply (A : DomainDependentHomSection I M IP P n)
    (U : TopologicalSpace.Opens P) (V : TopologicalSpace.Opens M) (q : U × V) :
    A.restrictOpen U V q = Manifold.restrictOpenTangentSpaceHom A.tangentHom U V q := (rfl)

/-- Forget higher differentiability of a native domain-dependent Hom section. -/
def ofLE (A : DomainDependentHomSection I M IP P n) {m : ℕ∞} (hmn : m ≤ n) :
    DomainDependentHomSection I M IP P m :=
  ⟨A, A.contMDiff.of_le (by exact_mod_cast hmn)⟩

@[simp]
theorem ofLE_apply (A : DomainDependentHomSection I M IP P n) {m : ℕ∞} (hmn : m ≤ n)
    (q : P × M) : (A.ofLE hmn) q = A q := (rfl)

section Model

variable {D V : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- A genuinely jointly `Cⁿ` operator field on model spaces gives a native tangent Hom section. -/
def ofContDiff (A : D × V → D →L[ℝ] V) (hA : ContDiff ℝ n A) :
    DomainDependentHomSection 𝓘(ℝ, V) V 𝓘(ℝ, D) D n := by
  refine ⟨A, fun q ↦ ?_⟩
  rw [contMDiffAt_hom_bundle]
  refine ⟨contMDiffAt_id, ?_⟩
  have he : (fun y : D × V ↦ ContinuousLinearMap.inCoordinates D
      (horizontalTangentBundle 𝓘(ℝ, V) V 𝓘(ℝ, D) D) V
      (verticalTangentBundle 𝓘(ℝ, V) V 𝓘(ℝ, D) D) q y q y (A y)) = A := by
    funext y
    erw [ContinuousLinearMap.inCoordinates_pullback_of_mem
      (V := (TangentSpace 𝓘(ℝ, D) : D → Type _))
      (W := (TangentSpace 𝓘(ℝ, V) : V → Type _))
      (ContMDiffMap.fst : C^∞⟮𝓘(ℝ, D).prod 𝓘(ℝ, V), D × V; 𝓘(ℝ, D), D⟯)
      (ContMDiffMap.snd : C^∞⟮𝓘(ℝ, D).prod 𝓘(ℝ, V), D × V; 𝓘(ℝ, V), V⟯)
      q y (A y) (by simp [TangentBundle.trivializationAt_baseSet])
        (by simp [TangentBundle.trivializationAt_baseSet])]
    exact inCoordinates_tangent_bundle_core_model_space _ _ _ _ _
  have hA' : ContMDiffAt (𝓘(ℝ, D).prod 𝓘(ℝ, V)) 𝓘(ℝ, D →L[ℝ] V) n A q := by
    rw [← modelWithCornersSelf_prod, chartedSpaceSelf_prod]
    exact hA.contMDiff q
  exact hA'.congr_of_eventuallyEq (Filter.Eventually.of_forall fun y ↦ congrFun he y)

@[simp]
theorem ofContDiff_apply (A : D × V → D →L[ℝ] V) (hA : ContDiff ℝ n A) (q : D × V) :
    ofContDiff A hA q = A q := (rfl)

end Model

end DomainDependentHomSection

namespace InhomogeneousTerm

variable {j : ContMDiffAlmostComplexStructure IP n P}
  {J : ContMDiffAlmostComplexStructureFamily I M IP P n}

/-- Two forcing terms are equal when their evaluations on tangent vectors agree. -/
@[ext]
theorem ext {ν μ : InhomogeneousTerm j J}
    (h : ∀ q v, ν.val q v = μ.val q v) : ν = μ := by
  apply Subtype.ext
  ext q v
  exact h q v

/-- The pointwise antilinearity of a native inhomogeneous term. -/
theorem isComplexAntilinear (ν : InhomogeneousTerm j J) (q : P × M) :
    IsComplexAntilinear (j.horizontalEndomorphism (I := I) (M := M) q).toLinearMap
      (J.toEndomorphism q).toLinearMap (ν.val q).toLinearMap :=
  ν.property q

/-- The forcing term sends a complex rotation in the source to the negative target rotation. -/
theorem apply_j (ν : InhomogeneousTerm j J) (q : P × M)
    (v : horizontalTangentBundle I M IP P q) :
    ν.val q (j.horizontalEndomorphism (I := I) (M := M) q v) = -(J q (ν.val q v)) :=
  (ν.isComplexAntilinear q).apply v

/-- The antilinearity equation read in the original domain and target tangent spaces. -/
theorem tangentHom_apply_j (ν : InhomogeneousTerm j J) (q : P × M)
    (v : TangentSpace IP q.1) :
    ν.val.tangentHom q (j q.1 v) = -J.tangentEndomorphism q (ν.val.tangentHom q v) := by
  have h := ν.apply_j q v
  erw [ContMDiffAlmostComplexStructure.horizontalEndomorphism_apply] at h
  erw [DomainDependentHomSection.tangentHom_apply,
    ContMDiffAlmostComplexStructureFamily.tangentEndomorphism_apply,
    DomainDependentHomSection.tangentHom_apply]
  exact h

/-- The raw tangent Hom map is antilinear for the domain structure and frozen target structure. -/
theorem tangentHom_isComplexAntilinear (ν : InhomogeneousTerm j J) (q : P × M) :
    IsComplexAntilinear (j.almostComplexStructureAt q.1).toLinearMap
      ((J.freeze q.1).almostComplexStructureAt q.2).toLinearMap
      (ν.val.tangentHom q).toLinearMap := by
  apply isComplexAntilinear_of_apply
  intro v
  -- The goal applies the three underlying linear maps; the public evaluation laws below
  -- instead apply their bundled structures. Their function coercions are those projections,
  -- so identify only these wrappers to let the evaluation laws rewrite the actual structures.
  change ν.val.tangentHom q (j.almostComplexStructureAt q.1 v) =
    -(J.freeze q.1).almostComplexStructureAt q.2 (ν.val.tangentHom q v)
  rw [ContMDiffAlmostComplexStructure.almostComplexStructureAt_apply,
    ContMDiffAlmostComplexStructure.almostComplexStructureAt_apply,
    ContMDiffAlmostComplexStructureFamily.freeze_apply]
  exact ν.tangentHom_apply_j q v

/-- A forcing term remains antilinear after a regularity downgrade. -/
def ofLE (ν : InhomogeneousTerm j J) {m : ℕ∞} (hmn : m ≤ n) :
    InhomogeneousTerm (j.ofLE hmn) (J.ofLE hmn) :=
  ⟨ν.val.ofLE hmn, fun q ↦ by
    simpa only [DomainDependentHomSection.ofLE_apply,
      ContMDiffAlmostComplexStructure.horizontalEndomorphism_apply,
      ContMDiffAlmostComplexStructure.ofLE_toEndomorphism_apply,
      ContMDiffAlmostComplexStructureFamily.ofLE_toEndomorphism_apply] using
        ν.isComplexAntilinear q⟩

@[simp]
theorem ofLE_val_apply (ν : InhomogeneousTerm j J) {m : ℕ∞} (hmn : m ≤ n) (q : P × M) :
    (ν.ofLE hmn).val q = ν.val q := (rfl)

/-- Compose a forcing term with jointly regular complex-linear source and target bundle maps.
The domain and target structures may both change. -/
def compose (ν : InhomogeneousTerm j J)
    (j' : ContMDiffAlmostComplexStructure IP n P)
    (J' : ContMDiffAlmostComplexStructureFamily I M IP P n)
    (A : Cₛ^n⟮IP.prod I; EP →L[ℝ] EP,
      fun q : P × M ↦ horizontalTangentBundle I M IP P q →L[ℝ]
        horizontalTangentBundle I M IP P q⟯)
    (B : Cₛ^n⟮IP.prod I; E →L[ℝ] E,
      fun q : P × M ↦ verticalTangentBundle I M IP P q →L[ℝ]
        verticalTangentBundle I M IP P q⟯)
    (hA : ∀ q, IsComplexLinear (j'.horizontalEndomorphism (I := I) (M := M) q).toLinearMap
      (j.horizontalEndomorphism (I := I) (M := M) q).toLinearMap (A q).toLinearMap)
    (hB : ∀ q, IsComplexLinear (J.toEndomorphism q).toLinearMap
      (J'.toEndomorphism q).toLinearMap (B q).toLinearMap) : InhomogeneousTerm j' J' :=
  ⟨B.clmComp (ν.val.clmComp A), fun q ↦ by
    simpa only [ContMDiffSection.clmComp_apply, ContinuousLinearMap.toLinearMap_comp] using
      (hB q).comp_antilinear ((ν.isComplexAntilinear q).comp_linear (hA q))⟩

@[simp]
theorem compose_val_apply (ν : InhomogeneousTerm j J)
    (j' : ContMDiffAlmostComplexStructure IP n P)
    (J' : ContMDiffAlmostComplexStructureFamily I M IP P n)
    (A : Cₛ^n⟮IP.prod I; EP →L[ℝ] EP,
      fun q : P × M ↦ horizontalTangentBundle I M IP P q →L[ℝ]
        horizontalTangentBundle I M IP P q⟯)
    (B : Cₛ^n⟮IP.prod I; E →L[ℝ] E,
      fun q : P × M ↦ verticalTangentBundle I M IP P q →L[ℝ]
        verticalTangentBundle I M IP P q⟯)
    (hA : ∀ q, IsComplexLinear (j'.horizontalEndomorphism (I := I) (M := M) q).toLinearMap
      (j.horizontalEndomorphism (I := I) (M := M) q).toLinearMap (A q).toLinearMap)
    (hB : ∀ q, IsComplexLinear (J.toEndomorphism q).toLinearMap
      (J'.toEndomorphism q).toLinearMap (B q).toLinearMap)
    (q : P × M) (v : horizontalTangentBundle I M IP P q) :
    (ν.compose j' J' A B hA hB).val q v = B q (ν.val q (A q v)) := by
  simp only [compose, ContMDiffSection.clmComp_apply, ContinuousLinearMap.comp_apply]

/-- Restrict forcing data to an open product using the intrinsic tangent fibres of both
open submanifolds. The pointwise constraint and the exact finite order are preserved. -/
def restrictOpen (ν : InhomogeneousTerm j J) (U : TopologicalSpace.Opens P)
    (V : TopologicalSpace.Opens M) :
    InhomogeneousTerm (j.restrictOpen U) (J.restrictOpen U V) := by
  let B : DomainDependentHomSection I V IP U n := ν.val.restrictOpen U V
  refine ⟨B, (mem_inhomogeneousTerms _ _ B).mpr fun q ↦ ?_⟩
  apply isComplexAntilinear_of_apply
  intro v
  -- Normalize the two inherited pullback fibre instances before applying the original
  -- tangent-space restriction formulas.
  change Manifold.restrictOpenTangentSpaceHom ν.val.tangentHom U V q
      (j.restrictOpen U q.1 v) =
    -(J.restrictOpen U V q (Manifold.restrictOpenTangentSpaceHom ν.val.tangentHom U V q v))
  erw [Manifold.restrictOpenTangentSpaceHom_apply,
    ContMDiffAlmostComplexStructure.restrictOpen_apply,
    ContinuousLinearEquiv.apply_symm_apply,
    ContMDiffAlmostComplexStructureFamily.restrictOpen_apply,
    Manifold.restrictOpenTangentSpaceHom_apply, ContinuousLinearEquiv.apply_symm_apply]
  rw [DomainDependentHomSection.tangentHom_apply,
    ContMDiffAlmostComplexStructureFamily.tangentEndomorphism_apply]
  have hν := ν.apply_j ((q.1 : P), (q.2 : M))
    (Manifold.tangentSpaceOpenEquiv (I := IP) q.1 v)
  erw [ContMDiffAlmostComplexStructure.horizontalEndomorphism_apply] at hν
  erw [DomainDependentHomSection.tangentHom_apply]
  exact (congrArg (Manifold.tangentSpaceOpenEquiv (I := I) q.2).symm hν).trans
    ((Manifold.tangentSpaceOpenEquiv (I := I) q.2).symm.map_neg _)

/-- The restricted forcing term has the actual source and target tangent transport formula. -/
@[simp]
theorem restrictOpen_val_apply (ν : InhomogeneousTerm j J) (U : TopologicalSpace.Opens P)
    (V : TopologicalSpace.Opens M) (q : U × V) (v : TangentSpace IP q.1) :
    (ν.restrictOpen U V).val q v =
      (Manifold.tangentSpaceOpenEquiv (I := I) q.2).symm
        (ν.val ((q.1 : P), (q.2 : M)) (Manifold.tangentSpaceOpenEquiv (I := IP) q.1 v)) := by
  simp only [restrictOpen, DomainDependentHomSection.restrictOpen_apply]
  erw [Manifold.restrictOpenTangentSpaceHom_apply]
  rw [DomainDependentHomSection.tangentHom_apply]

/-- The canonical finite-regularity projection of an ambient Hom section to forcing terms.
Its fibrewise linear map is the existing `complexAntilinearPart` operator. -/
def project (j : ContMDiffAlmostComplexStructure IP n P)
    (J : ContMDiffAlmostComplexStructureFamily I M IP P n)
    (A : DomainDependentHomSection I M IP P n) : InhomogeneousTerm j J := by
  let B : DomainDependentHomSection I M IP P n :=
    (2⁻¹ : ℝ) • (A + J.toEndomorphism.clmComp
      (A.clmComp (j.horizontalEndomorphism (I := I) (M := M))))
  refine ⟨B, (mem_inhomogeneousTerms j J B).mpr fun q ↦ ?_⟩
  have he : (B q).toLinearMap = complexAntilinearPart
      (j.horizontalEndomorphism (I := I) (M := M) q).toLinearMap
      (J.toEndomorphism q).toLinearMap (A q).toLinearMap := by
    ext v
    simp only [B, ContMDiffSection.coe_smul, Pi.smul_apply, smul_apply,
      ContMDiffSection.coe_add, Pi.add_apply, add_apply, ContMDiffSection.clmComp_apply,
      ContinuousLinearMap.comp_apply, complexAntilinearPart_apply, ContinuousLinearMap.coe_coe]
  rw [he]
  apply complexAntilinearPart_isComplexAntilinear
  · ext v
    exact j.horizontalEndomorphism_apply_apply q v
  · ext v
    exact J.apply_apply q v

/-- The forcing projection has the pinned factor one half on actual tangent vectors. -/
@[simp]
theorem project_apply (j : ContMDiffAlmostComplexStructure IP n P)
    (J : ContMDiffAlmostComplexStructureFamily I M IP P n)
    (A : DomainDependentHomSection I M IP P n) (q : P × M)
    (v : horizontalTangentBundle I M IP P q) :
    (project j J A).val q v = (2⁻¹ : ℝ) •
      (A q v + J q (A q (j.horizontalEndomorphism (I := I) (M := M) q v))) := by
  simp only [project, ContMDiffSection.coe_smul, Pi.smul_apply, smul_apply,
    ContMDiffSection.coe_add, Pi.add_apply, add_apply, ContMDiffSection.clmComp_apply,
    ContinuousLinearMap.comp_apply]

/-- The native linear-algebra projection is the pointwise linear map of the section projection. -/
theorem project_toLinearMap_apply (j : ContMDiffAlmostComplexStructure IP n P)
    (J : ContMDiffAlmostComplexStructureFamily I M IP P n)
    (A : DomainDependentHomSection I M IP P n) (q : P × M) :
    ((project j J A).val q).toLinearMap = complexAntilinearPart
      (j.horizontalEndomorphism (I := I) (M := M) q).toLinearMap
      (J.toEndomorphism q).toLinearMap (A q).toLinearMap := by
  ext v
  exact project_apply j J A q v

/-- The projection is a retraction onto the native submodule of forcing terms. -/
@[simp]
theorem project_val (ν : InhomogeneousTerm j J) : project j J ν.val = ν := by
  apply Subtype.ext
  ext q v
  have hsq : (J.toEndomorphism q).toLinearMap ∘ₗ
      (J.toEndomorphism q).toLinearMap = -LinearMap.id := by
    ext w
    exact J.apply_apply q w
  exact LinearMap.congr_fun ((project_toLinearMap_apply j J ν.val q).trans
    ((ν.isComplexAntilinear q).complexAntilinearPart_eq hsq)) v

/-- Fixed points of the section projection are precisely the inhomogeneous sections. -/
theorem project_eq_self_iff (A : DomainDependentHomSection I M IP P n) :
    (project j J A).val = A ↔ A ∈ inhomogeneousTerms j J := by
  constructor
  · intro h
    exact h ▸ (project j J A).property
  · intro h
    exact congrArg Subtype.val (project_val (⟨A, h⟩ : InhomogeneousTerm j J))

/-- The canonical projection is real linear between the native section modules. -/
def projection (j : ContMDiffAlmostComplexStructure IP n P)
    (J : ContMDiffAlmostComplexStructureFamily I M IP P n) :
    DomainDependentHomSection I M IP P n →ₗ[ℝ] InhomogeneousTerm j J where
  toFun := project j J
  map_add' A B := by
    ext q v
    simp only [project_apply, Submodule.coe_add, ContMDiffSection.coe_add, Pi.add_apply,
      add_apply, map_add, smul_add]
    module
  map_smul' c A := by
    ext q v
    simp only [project_apply, Submodule.coe_smul, ContMDiffSection.coe_smul, Pi.smul_apply,
      smul_apply, map_smul, RingHom.id_apply]
    module

@[simp]
theorem projection_apply (j : ContMDiffAlmostComplexStructure IP n P)
    (J : ContMDiffAlmostComplexStructureFamily I M IP P n)
    (A : DomainDependentHomSection I M IP P n) : projection j J A = project j J A := (rfl)

/-- The canonical projection commutes with forgetting regularity. -/
@[simp]
theorem ofLE_project (j : ContMDiffAlmostComplexStructure IP n P)
    (J : ContMDiffAlmostComplexStructureFamily I M IP P n)
    (A : DomainDependentHomSection I M IP P n) {m : ℕ∞} (hmn : m ≤ n) :
    (project j J A).ofLE hmn = project (j.ofLE hmn) (J.ofLE hmn) (A.ofLE hmn) := by
  ext q v
  simp only [ofLE_val_apply, project_apply, DomainDependentHomSection.ofLE_apply,
    ContMDiffAlmostComplexStructureFamily.ofLE_toEndomorphism_apply,
    ContMDiffAlmostComplexStructure.horizontalEndomorphism_apply,
    ContMDiffAlmostComplexStructure.ofLE_toEndomorphism_apply]

section Naturality

variable (j' : ContMDiffAlmostComplexStructure IP n P)
  (J' : ContMDiffAlmostComplexStructureFamily I M IP P n)
  (A : Cₛ^n⟮IP.prod I; EP →L[ℝ] EP,
    fun q : P × M ↦ horizontalTangentBundle I M IP P q →L[ℝ]
      horizontalTangentBundle I M IP P q⟯)
  (B : Cₛ^n⟮IP.prod I; E →L[ℝ] E,
    fun q : P × M ↦ verticalTangentBundle I M IP P q →L[ℝ]
      verticalTangentBundle I M IP P q⟯)
  (hA : ∀ q, IsComplexLinear (j'.horizontalEndomorphism (I := I) (M := M) q).toLinearMap
    (j.horizontalEndomorphism (I := I) (M := M) q).toLinearMap (A q).toLinearMap)
  (hB : ∀ q, IsComplexLinear (J.toEndomorphism q).toLinearMap
    (J'.toEndomorphism q).toLinearMap (B q).toLinearMap)

/-- Antilinear projection is natural under jointly regular complex-linear source and target
bundle maps, with the source and target structures both allowed to change. -/
theorem compose_project (F : DomainDependentHomSection I M IP P n) :
    (project j J F).compose j' J' A B hA hB =
      project j' J' (B.clmComp (F.clmComp A)) := by
  ext q v
  have ha : A q (j'.horizontalEndomorphism (I := I) (M := M) q v) =
      j.horizontalEndomorphism (I := I) (M := M) q (A q v) := (hA q).apply v
  have hb (w : verticalTangentBundle I M IP P q) : B q (J q w) = J' q (B q w) :=
    (hB q).apply w
  simp only [compose_val_apply, project_apply, ContMDiffSection.clmComp_apply,
    ContinuousLinearMap.comp_apply, map_smul, map_add]
  rw [ha, hb]

end Naturality

end InhomogeneousTerm

end TauCeti

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.Curved.Algebra.Hom.Basic
public import TauCeti.Algebra.Homology.Curved.Module.Right.Graded
public import TauCeti.Algebra.Category.GradedModuleCat.RestrictScalars

/-!
# Restriction of scalars for curved right DG modules

A strict curved algebra morphism `f : A → B` restricts a curved right `B`-module to a
curved right `A`-module, with action `x · a = x · f(a)`. The grading and differential are
unchanged. Preservation of curvature is essential: it identifies the square of the original
differential with the new curvature action.

Restriction acts on all homogeneous right-linear maps and commutes with their Hom differential,
so it defines a DG functor and hence functors on closed morphisms and on homotopy categories.
No flatness or centrality hypothesis is needed. This is the restriction operation used in
change-of-rings adjunctions; no assertion about derived equivalences is made here.

The underlying graded restriction is `TauCeti.GradedModuleCat.restrictScalarsObj`; no new
module carrier or parallel category of curved modules is introduced. The DG functor is assembled
with `CategoryTheory.EnrichedFunctor.ofDGMap`. Objects support independent universes; the
functors use the existing DG enrichment, where the ground ring, algebra, and modules share a
universe.

## References

* L. Positselski, *Two kinds of derived categories, Koszul duality, and
  comodule-contramodule correspondence*, Section 3.1, for strict change of curved DG rings.
  The stored right-module curvature here is the negative of his curvature.
-/

public section

open CategoryTheory MulOpposite

namespace TauCeti.CurvedDGRightModuleCat

universe u uR uA uB uM

section Objects

variable {R : Type uR} {A : Type uA} {B : Type uB}
  [CommRing R] [Ring A] [Ring B] [Algebra R A] [Algebra R B]
  {𝒜 : ℤ → Submodule R A} {ℬ : ℤ → Submodule R B} [GradedAlgebra 𝒜] [GradedAlgebra ℬ]
  {dA : A →ₗ[R] A} {dB : B →ₗ[R] B} {wA : A} {wB : B}
  {hA : IsCurvedDGAlgebra 𝒜 dA wA} {hB : IsCurvedDGAlgebra ℬ dB wB}

/-- Restrict a curved right module along a strict curved algebra morphism. The underlying
module and differential are unchanged; the right action is through the morphism. -/
-- The carrier must reduce to M so the original ground-ring differential can be reused.
@[expose, implicit_reducible]
noncomputable def restrictScalarsObj (f : CurvedDGAlgHom hA hB)
    (M : CurvedDGRightModuleCat.{uR, uB, uM} hB) : CurvedDGRightModuleCat.{uR, uA, uM} hA := by
  have hf {i : ℤ} {a : Aᵐᵒᵖ}
      (ha : a ∈ (InternalGrading.ofDecomposition 𝒜).opposite.piece i) :
      AlgHom.op f.toGradedAlgHom.toAlgHom a ∈
        (InternalGrading.ofDecomposition ℬ).opposite.piece i := by
    rw [InternalGrading.mem_opposite_piece_iff, InternalGrading.ofDecomposition_piece] at ha ⊢
    simpa using Graded.map_mem f ha
  let N := GradedModuleCat.restrictScalarsObj (AlgHom.op f.toGradedAlgHom.toAlgHom)
    (fun {_ _} ha ↦ hf ha) (toGradedModuleCat M)
  letI : Module Aᵐᵒᵖ M := N.isModule
  letI : IsScalarTower R Aᵐᵒᵖ M := N.isScalarTower
  letI : SetLike.GradedSMul (InternalGrading.ofDecomposition 𝒜).opposite.piece M.grading :=
    ⟨fun _ _ _ _ ha hx ↦ M.gradedSMul.smul_mem (hf ha) hx⟩
  exact
    { carrier := M
      grading := M.grading
      decomposition := M.decomposition
      differential := M.differential
      isCurvedDGRightModule :=
        { isHomogeneous := M.isCurvedDGRightModule.isHomogeneous
          leibniz := by
            intro q x hx a
            -- Unfold the graded restriction's stored Module.compHom action.
            simpa [N, GradedModuleCat.restrictScalarsObj, MulAction.compHom_smul_def] using
              M.isCurvedDGRightModule.leibniz hx (f a)
          sq_eq := by
            intro x
            -- The bundled action is through f, whose curvature image is wB.
            simpa [N, GradedModuleCat.restrictScalarsObj, MulAction.compHom_smul_def] using
              M.isCurvedDGRightModule.sq_eq x } }

/-- Restriction retains the original ground-ring module. -/
noncomputable def restrictScalarsEquiv (f : CurvedDGAlgHom hA hB)
    (M : CurvedDGRightModuleCat.{uR, uB, uM} hB) : restrictScalarsObj f M ≃ₗ[R] M :=
  LinearEquiv.refl R M

/-- The restricted action is the original action of the image scalar. -/
@[simp]
theorem restrictScalarsEquiv_op_smul (f : CurvedDGAlgHom hA hB)
    (M : CurvedDGRightModuleCat.{uR, uB, uM} hB) (a : A) (x : restrictScalarsObj f M) :
    restrictScalarsEquiv f M (op a • x) = op (f a) • restrictScalarsEquiv f M x :=
  (rfl)

/-- Restriction keeps each homogeneous piece. -/
@[simp]
theorem mem_restrictScalarsObj_grading (f : CurvedDGAlgHom hA hB)
    (M : CurvedDGRightModuleCat.{uR, uB, uM} hB) (i : ℤ) (x : restrictScalarsObj f M) :
    x ∈ (restrictScalarsObj f M).grading i ↔ restrictScalarsEquiv f M x ∈ M.grading i := (Iff.rfl)

/-- Restriction retains the differential. -/
@[simp]
theorem restrictScalarsEquiv_differential (f : CurvedDGAlgHom hA hB)
    (M : CurvedDGRightModuleCat.{uR, uB, uM} hB) (x : restrictScalarsObj f M) :
    restrictScalarsEquiv f M ((restrictScalarsObj f M).differential x) =
      M.differential (restrictScalarsEquiv f M x) := (rfl)

end Objects

-- The existing DG enrichment has ground ring, algebra, and modules in one universe.
variable {R A B : Type u} [CommRing R] [Ring A] [Ring B] [Algebra R A] [Algebra R B]
  {𝒜 : ℤ → Submodule R A} {ℬ : ℤ → Submodule R B} [GradedAlgebra 𝒜] [GradedAlgebra ℬ]
  {dA : A →ₗ[R] A} {dB : B →ₗ[R] B} {wA : A} {wB : B}
  {hA : IsCurvedDGAlgebra 𝒜 dA wA} {hB : IsCurvedDGAlgebra ℬ dB wB}
  (f : CurvedDGAlgHom hA hB) {M N : CurvedDGRightModuleCat.{u, u, u} hB}

/-- Restrict a homogeneous right-linear map. Its degree and underlying function are unchanged. -/
noncomputable def restrictScalarsCochains (p : ℤ) :
    dgRightModuleCochains (R := R) (A := B) (ℳ := M.grading) (ℳN := N.grading) p →ₗ[R]
      dgRightModuleCochains (R := R) (A := A)
        (ℳ := (restrictScalarsObj f M).grading) (ℳN := (restrictScalarsObj f N).grading) p where
  toFun g :=
    ⟨{ toFun := g.1
       map_add' := g.1.map_add
       map_smul' a x := g.1.map_smul (AlgHom.op f.toGradedAlgHom.toAlgHom a) x },
      dgRightModuleCochains.mem_iff.mpr
        (LinearMap.isHomogeneous_def.mpr fun _ _ hx ↦ dgRightModuleCochains.map_mem g hx)⟩
  map_add' _ _ := Subtype.ext (LinearMap.ext fun _ ↦ rfl)
  map_smul' _ _ := Subtype.ext (LinearMap.ext fun _ ↦ rfl)

/-- Restriction of cochains retains the underlying function. -/
@[simp]
theorem restrictScalarsCochains_apply (p : ℤ)
    (g : dgRightModuleCochains (R := R) (A := B) (ℳ := M.grading) (ℳN := N.grading) p)
    (x : restrictScalarsObj f M) :
    restrictScalarsEquiv f N ((restrictScalarsCochains f p g).1 x) =
      g.1 (restrictScalarsEquiv f M x) := (rfl)

/-- Restriction commutes with the Hom differential, including the odd homotopy boundary. -/
@[simp]
theorem restrictScalarsCochains_curvedDifferential (p : ℤ)
    (g : dgRightModuleCochains (R := R) (A := B) (ℳ := M.grading) (ℳN := N.grading) p) :
    restrictScalarsCochains f (p + 1)
        (dgRightModuleCochains.curvedDifferential
          (hM := M.isCurvedDGRightModule) (hN := N.isCurvedDGRightModule) p g) =
      dgRightModuleCochains.curvedDifferential
        (hM := (restrictScalarsObj f M).isCurvedDGRightModule)
        (hN := (restrictScalarsObj f N).isCurvedDGRightModule) p
        (restrictScalarsCochains f p g) := by
  apply Subtype.ext
  ext x
  simp only [restrictScalarsCochains, dgRightModuleCochains.curvedDifferential_apply]
  exact dgRightModuleCochains.curvedDifferential_apply p g x

/-- Restriction on homogeneous morphisms of the DG enrichment. -/
noncomputable def restrictScalarsDGHom (p : ℤ) :
    DGHom R p M N →ₗ[R] DGHom R p (restrictScalarsObj f M) (restrictScalarsObj f N) :=
  (dgHomLinearEquivCochains _ _ p).symm.toLinearMap ∘ₗ
    restrictScalarsCochains f p ∘ₗ (dgHomLinearEquivCochains M N p).toLinearMap

/-- The homogeneous morphism restriction corresponds to restriction of cochains. -/
@[simp]
theorem dgHomLinearEquivCochains_restrictScalarsDGHom (p : ℤ) (g : DGHom R p M N) :
    dgHomLinearEquivCochains _ _ p (restrictScalarsDGHom f p g) =
      restrictScalarsCochains f p (dgHomLinearEquivCochains M N p g) := by
  simp only [restrictScalarsDGHom, LinearMap.comp_apply, LinearEquiv.coe_toLinearMap,
    LinearEquiv.apply_symm_apply]

/-- Restriction of scalars as a DG functor. Strict preservation of curvature ensures that
its objects have the required square equation; its map on each Hom complex is restriction
of homogeneous right-linear maps. -/
-- Expose the object map so the dependent homogeneous-map formula has the stated codomain.
@[expose]
noncomputable def restrictScalarsDG :
    EnrichedFunctor (CochainComplex (ModuleCat R) ℤ)
      (CurvedDGRightModuleCat.{u, u, u} hB) (CurvedDGRightModuleCat.{u, u, u} hA) :=
  EnrichedFunctor.ofDGMap (restrictScalarsObj f) (restrictScalarsDGHom f)
    (fun p g ↦ by
      apply (dgHomLinearEquivCochains _ _ (p + 1)).injective
      simp only [dgHomLinearEquivCochains_restrictScalarsDGHom, dgDifferential_eq,
        restrictScalarsCochains_curvedDifferential])
    (fun M ↦ by
      apply (dgHomLinearEquivCochains _ _ 0).injective
      simp only [dgHomLinearEquivCochains_restrictScalarsDGHom, dgId_eq]
      apply Subtype.ext
      ext x
      dsimp [restrictScalarsCochains]
      simp only [dgRightModuleCochains.id_apply]
      exact dgRightModuleCochains.id_apply (R := R) (A := B) (ℳ := M.grading) x)
    (fun {M N P p q n} g k hpq ↦ by
      apply (dgHomLinearEquivCochains _ _ n).injective
      simp only [dgHomLinearEquivCochains_restrictScalarsDGHom, dgComp_eq,
        Units.smul_def, map_zsmul]
      congr 1
      apply Subtype.ext
      ext x
      dsimp [restrictScalarsCochains]
      simp only [dgRightModuleCochains.comp_apply]
      exact dgRightModuleCochains.comp_apply
        (dgHomLinearEquivCochains N P q k) (dgHomLinearEquivCochains M N p g) _ x)

/-- The DG restriction acts on objects by the restricted module. -/
@[simp]
theorem restrictScalarsDG_obj (M : CurvedDGRightModuleCat.{u, u, u} hB) :
    (restrictScalarsDG f).obj M = restrictScalarsObj f M := (rfl)

/-- The homogeneous map of DG restriction is the restriction of the original cochain. -/
@[simp]
theorem restrictScalarsDG_dgMap (p : ℤ) (g : DGHom R p M N) :
    dgHomLinearEquivCochains _ _ p ((restrictScalarsDG f).dgMap p g) =
      restrictScalarsCochains f p (dgHomLinearEquivCochains M N p g) :=
  (congrArg (dgHomLinearEquivCochains _ _ p)
    (EnrichedFunctor.dgMap_ofDGMap _ _ _ _ _ p g)).trans
      (dgHomLinearEquivCochains_restrictScalarsDGHom f p g)

/-- Restriction of scalars on the closed degree-zero categories. -/
noncomputable abbrev restrictScalars :
    ForgetEnrichment (CochainComplex (ModuleCat R) ℤ) (CurvedDGRightModuleCat.{u, u, u} hB) ⥤
      ForgetEnrichment (CochainComplex (ModuleCat R) ℤ) (CurvedDGRightModuleCat.{u, u, u} hA) :=
  (restrictScalarsDG f).forget

/-- Restriction on closed morphisms keeps the underlying function. -/
-- Compute before the general enriched forgetful functor expands its map.
@[simp↓]
theorem restrictScalars_map_apply
    (g : ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) M ⟶
      ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) N)
    (x : restrictScalarsObj f M) :
    restrictScalarsEquiv f N (closedHom ((restrictScalars f).map g) x) =
      closedHom g (restrictScalarsEquiv f M x) := by
  simp only [closedHom_eq, EnrichedFunctor.forget_map,
    EnrichedFunctor.dgClosedHom_forget_map, restrictScalarsDG_dgMap]
  rfl

-- The closed category wraps, but does not alter, its module objects.
attribute [local implicit_reducible] ForgetEnrichment

instance : (restrictScalars f).Faithful where
  map_injective {M N} g k hgk := by
    apply closedHom_ext
    intro x
    have hx := congrArg (fun l ↦ restrictScalarsEquiv f (ForgetEnrichment.to _ N)
      (closedHom l ((restrictScalarsEquiv f (ForgetEnrichment.to _ M)).symm x))) hgk
    exact (restrictScalars_map_apply f g _).symm.trans
      (hx.trans (restrictScalars_map_apply f k _))

/-- Restriction of scalars on curved homotopy categories. -/
noncomputable abbrev restrictScalarsHomotopy :
    DGHomotopyCategory R (CurvedDGRightModuleCat.{u, u, u} hB) ⥤
      DGHomotopyCategory R (CurvedDGRightModuleCat.{u, u, u} hA) :=
  (restrictScalarsDG f).mapDGHomotopyCategory

/-- Restriction commutes with passage from closed morphisms to their homotopy classes. -/
noncomputable def restrictScalarsCompQuotientIso :
    restrictScalars f ⋙ dgClosedToHomotopy R ≅
      dgClosedToHomotopy R ⋙ restrictScalarsHomotopy f :=
  (restrictScalarsDG f).forgetCompDgClosedToHomotopyIso

/-- The comparison with the quotient has identity components. -/
@[simp]
theorem restrictScalarsCompQuotientIso_hom_app
    (M : ForgetEnrichment (CochainComplex (ModuleCat R) ℤ)
      (CurvedDGRightModuleCat.{u, u, u} hB)) :
    (restrictScalarsCompQuotientIso f).hom.app M = 𝟙 _ := (rfl)

/-- The inverse comparison with the quotient has identity components. -/
@[simp]
theorem restrictScalarsCompQuotientIso_inv_app
    (M : ForgetEnrichment (CochainComplex (ModuleCat R) ℤ)
      (CurvedDGRightModuleCat.{u, u, u} hB)) :
    (restrictScalarsCompQuotientIso f).inv.app M = 𝟙 _ := (rfl)

end TauCeti.CurvedDGRightModuleCat

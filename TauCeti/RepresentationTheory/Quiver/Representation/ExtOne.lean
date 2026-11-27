/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Quiver.PathAlgebra.StandardResolution
public import TauCeti.RepresentationTheory.Quiver.Representation.HomDifferential
public import TauCeti.RepresentationTheory.Quiver.Representation.AsModule
public import TauCeti.Algebra.Homology.Ext.Presentation
public import Mathlib.Algebra.Category.ModuleCat.Ext.HasExt
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.Algebra.Module.Shrink

/-!
# The cokernel of the Hom differential is Ext¹

For representations `M` and `N` of a quiver `Q`, the Hom differential
`(fᵥ)ᵥ ↦ (N(b) fᵢ - fⱼ M(b))_{b : i ⟶ j}` sends families of vertex maps to families of arrow maps
(`TauCeti.QuiverRep.homDifferential`). Its kernel is `Hom(M, N)`. This file identifies its
cokernel with `Ext¹(M, N)`, computed in the category of modules over the path algebra `kQ`, for a
quiver with finitely many vertices over a field. The quiver may have oriented cycles and
infinitely many arrows, and the vertex spaces may be infinite-dimensional. For finite-dimensional
representations of a finite quiver this turns
`TauCeti.QuiverRep.eulerForm_eq_finrank_hom_sub_finrank_coker` into the identity
`⟨dim M, dim N⟩ = dim Hom(M, N) - dim Ext¹(M, N)` for the Euler form, with no acyclicity
hypothesis.

The comparison applies `Hom(-, N)` to the standard resolution
`0 → ⨁_{b : i ⟶ j} kQ eⱼ ⊗_k eᵢ X → ⨁ᵥ kQ eᵥ ⊗_k eᵥ X → X → 0` of a `kQ`-module `X`
(`TauCeti.PathAlgebra.standardDifferential`). A `kQ`-linear map out of the vertex term is
determined by its values `g (eᵥ ⊗ m)` for `m ∈ eᵥ X`, and these form an arbitrary family of
`k`-linear maps `eᵥ X → eᵥ N`; likewise for the arrow term. Under these identifications,
precomposition with the differential `x ⊗ m ↦ x b ⊗ m - x ⊗ b m` is the Hom differential. The
middle term is projective, so the cokernel of that precomposition is `Ext¹(X, N)`
(`TauCeti.homCokernelEquivExt`). The terms of the resolution live in a larger universe than `X`,
so the comparison passes through small models of them.

## Main definitions

* `TauCeti.PathAlgebra.standardVertexTermHomEquiv`, `TauCeti.PathAlgebra.standardArrowTermHomEquiv`:
  maps out of the two terms of the standard resolution are families of vertex maps and of arrow
  maps.
* `TauCeti.PathAlgebra.homDifferentialCokerEquivExt`: for `kQ`-modules `X` and `N`, the cokernel of
  the Hom differential between the representations they carry is `k`-linearly `Ext¹(X, N)`.

## Main results

* `TauCeti.PathAlgebra.standardArrowTermHomEquiv_comp_standardDifferential`: precomposition with
  the differential of the standard resolution is the Hom differential.
* `TauCeti.QuiverRep.nonempty_homDifferential_coker_linearEquiv_ext`: for representations `M` and
  `N`, the cokernel of the Hom differential is `k`-linearly isomorphic to `Ext¹` of the
  corresponding modules over the path algebra.
* `TauCeti.QuiverRep.eulerForm_eq_finrank_hom_sub_finrank_ext`: for pointwise finite-dimensional
  representations of a finite quiver, the Euler form is `dim Hom(M, N) - dim Ext¹(M, N)`.

## References

* W. Crawley-Boevey, *Lectures on representations of quivers*, Section 1: the standard resolution
  and the exact sequence
  `0 → Hom(M, N) → ⊕ᵥ Hom(Mᵥ, Nᵥ) → ⊕_{b : i ⟶ j} Hom(Mᵢ, Nⱼ) → Ext¹(M, N) → 0`
  in the proof of its consequence (3).
-/

public section

namespace TauCeti

open CategoryTheory PathAlgebra TensorProduct

universe u v w t

namespace PathAlgebra

variable {k : Type u} {Q : Type v} [Quiver.{w} Q] [Fintype Q] {X N : Type t}

/-- The path algebra, in this file. -/
local notation "𝒜" => pathAlgebra k Q

/-- The vertex idempotent `eᵥ`, in this file. -/
local notation "ε" => vertexIdempotent k

section Generators

variable [CommRing k] [AddCommGroup X] [Module k X] [Module (pathAlgebra k Q) X]
  [IsScalarTower k (pathAlgebra k Q) X]

/-- For `m ∈ eᵥ X`, the tensor `eᵥ ⊗ m` lies in the vertex term of the standard resolution. -/
theorem vertexIdempotent_tmul_mem_standardVertexTerm {v : Q} {m : X}
    (hm : m ∈ vertexComponent k X v) :
    (ε v : 𝒜) ⊗ₜ[k] m ∈ standardVertexTerm k Q X := by
  rw [mem_standardVertexTerm_iff, standardVertexProjection_tmul, Finset.sum_eq_single v]
  · rw [vertexIdempotent_mul_self, vertexIdempotent_smul_eq_self_of_mem_vertexComponent hm]
  · intro u _ hu
    rw [vertexIdempotent_mul_vertexIdempotent_of_ne hu.symm, zero_tmul]
  · simp

/-- For an arrow `b : i ⟶ j` and `m ∈ eᵢ X`, the tensor `eⱼ ⊗ m` in the component of `b` lies
in the arrow term of the standard resolution. -/
theorem single_vertexIdempotent_tmul_mem_standardArrowTerm {i j : Q} (b : i ⟶ j) {m : X}
    (hm : m ∈ vertexComponent k X i) :
    Finsupp.single (⟨i, j, b⟩ : Σ i j : Q, i ⟶ j) ((ε j : 𝒜) ⊗ₜ[k] m) ∈
      standardArrowTerm k Q X := by
  rw [mem_standardArrowTerm_iff, standardArrowProjection_single_tmul, vertexIdempotent_mul_self,
    vertexIdempotent_smul_eq_self_of_mem_vertexComponent hm]

end Generators

variable [Field k] [AddCommGroup X] [Module k X] [Module (pathAlgebra k Q) X]
  [IsScalarTower k (pathAlgebra k Q) X] [AddCommGroup N] [Module k N]
  [Module (pathAlgebra k Q) N] [IsScalarTower k (pathAlgebra k Q) N]

section VertexTerm

/-- The generator `m ↦ eᵥ ⊗ m` of the vertex term at `v`. -/
private noncomputable def vertexGen (v : Q) :
    vertexComponent k X v →ₗ[k] standardVertexTerm k Q X :=
  ((TensorProduct.mk k 𝒜 X (ε v)).comp (vertexComponent k X v).subtype).codRestrict
    ((standardVertexTerm k Q X).restrictScalars k) fun m ↦
      vertexIdempotent_tmul_mem_standardVertexTerm m.property

private theorem coe_vertexGen (v : Q) (m : vertexComponent k X v) :
    (vertexGen v m : 𝒜 ⊗[k] X) = (ε v : 𝒜) ⊗ₜ[k] (m : X) := (rfl)

private theorem vertexIdempotent_smul_vertexGen (v : Q) (m : vertexComponent k X v) :
    (ε v : 𝒜) • vertexGen v m = vertexGen v m :=
  Subtype.ext (by rw [Submodule.coe_smul, coe_vertexGen, smul_tmul', smul_eq_mul,
    vertexIdempotent_mul_self])

/-- The `k`-linear map `X → N` gluing maps `eᵥ X → eᵥ N` along the vertex projections. -/
private noncomputable def glueVertex
    (f : ∀ v : Q, vertexComponent k X v →ₗ[k] vertexComponent k N v) : X →ₗ[k] N :=
  ∑ v : Q, (vertexComponent k N v).subtype ∘ₗ f v ∘ₗ vertexProjection k X v

private theorem glueVertex_apply
    (f : ∀ v : Q, vertexComponent k X v →ₗ[k] vertexComponent k N v) (m : X) :
    glueVertex f m = ∑ v : Q, (f v (vertexProjection k X v m) : N) := by
  simp [glueVertex]

private theorem glueVertex_apply_of_mem
    (f : ∀ v : Q, vertexComponent k X v →ₗ[k] vertexComponent k N v) {v : Q}
    (m : vertexComponent k X v) : glueVertex f m = f v m := by
  rw [glueVertex_apply, Finset.sum_eq_single v]
  · rw [show vertexProjection k X v m = m from
      Subtype.ext (coe_vertexProjection_apply_of_mem m.property)]
  · intro u _ hu
    rw [show vertexProjection k X u m = 0 from
      Subtype.ext (coe_vertexProjection_apply_eq_zero_of_ne hu m.property), map_zero,
      ZeroMemClass.coe_zero]
  · simp

/-- The value of a map out of the vertex term on a generator lies in the vertex component. -/
private theorem apply_vertexGen_mem (g : standardVertexTerm k Q X →ₗ[𝒜] N) (v : Q)
    (m : vertexComponent k X v) : g (vertexGen v m) ∈ vertexComponent k N v := by
  rw [mem_vertexComponent_iff_smul_eq_self, ← map_smul, vertexIdempotent_smul_vertexGen]

/-- The component at `v` of a map out of the vertex term: `m ↦ g (eᵥ ⊗ m)`. -/
private noncomputable def vertexTermComponent (g : standardVertexTerm k Q X →ₗ[𝒜] N) (v : Q) :
    vertexComponent k X v →ₗ[k] vertexComponent k N v :=
  ((g.restrictScalars k).comp (vertexGen v)).codRestrict _ (apply_vertexGen_mem g v)

private theorem coe_vertexTermComponent (g : standardVertexTerm k Q X →ₗ[𝒜] N) (v : Q)
    (m : vertexComponent k X v) : (vertexTermComponent g v m : N) = g (vertexGen v m) := (rfl)

/-- The `kQ`-linear map out of `kQ ⊗_k X` extending a glued family, `x ⊗ m ↦ x • f m`. -/
private noncomputable def liftVertex
    (f : ∀ v : Q, vertexComponent k X v →ₗ[k] vertexComponent k N v) : 𝒜 ⊗[k] X →ₗ[𝒜] N :=
  tensorSMul k 𝒜 N ∘ₗ AlgebraTensorModule.map LinearMap.id (glueVertex f)

private theorem liftVertex_tmul
    (f : ∀ v : Q, vertexComponent k X v →ₗ[k] vertexComponent k N v) (x : 𝒜) (m : X) :
    liftVertex f (x ⊗ₜ m) = x • glueVertex f m := by
  simp [liftVertex]

/-- Extending the components of `g` recovers `g` after the vertex projection. -/
private theorem liftVertex_vertexTermComponent (g : standardVertexTerm k Q X →ₗ[𝒜] N) :
    liftVertex (vertexTermComponent g) =
      g ∘ₗ (standardVertexProjection k Q X).codRestrict _
        standardVertexProjection_mem_standardVertexTerm := by
  refine AlgebraTensorModule.ext fun x m ↦ ?_
  have h : (standardVertexProjection k Q X).codRestrict _
      standardVertexProjection_mem_standardVertexTerm (x ⊗ₜ m) =
      x • ∑ v : Q, vertexGen v (vertexProjection k X v m) :=
    Subtype.ext (by simp [coe_vertexGen, Finset.smul_sum, smul_tmul'])
  simp only [liftVertex_tmul, glueVertex_apply, coe_vertexTermComponent, LinearMap.comp_apply, h,
    map_smul, map_sum]

/-- The components of the restriction of an extended family are the family. -/
private theorem vertexTermComponent_liftVertex
    (f : ∀ v : Q, vertexComponent k X v →ₗ[k] vertexComponent k N v) (v : Q) :
    vertexTermComponent ((liftVertex f).domRestrict (standardVertexTerm k Q X)) v = f v := by
  refine LinearMap.ext fun m ↦ Subtype.ext ?_
  rw [coe_vertexTermComponent, LinearMap.domRestrict_apply, coe_vertexGen, liftVertex_tmul,
    glueVertex_apply_of_mem,
    vertexIdempotent_smul_eq_self_of_mem_vertexComponent (f v m).property]

variable (k Q X N) in
/-- **Maps out of the vertex term of the standard resolution** `⨁ᵥ kQ eᵥ ⊗_k eᵥ X` are the
families of `k`-linear maps between the vertex spaces: a map `g` corresponds to the family
`m ↦ g (eᵥ ⊗ m)`. -/
noncomputable def standardVertexTermHomEquiv :
    (standardVertexTerm k Q X →ₗ[𝒜] N) ≃ₗ[k]
      QuiverRep.HomVertex (quiverRepOfModule k Q X) (quiverRepOfModule k Q N) where
  toFun g := vertexTermComponent g
  invFun f := (liftVertex f).domRestrict _
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv g := by
    refine LinearMap.ext fun z ↦ ?_
    rw [LinearMap.domRestrict_apply, liftVertex_vertexTermComponent, LinearMap.comp_apply]
    exact congrArg g (Subtype.ext (mem_standardVertexTerm_iff.1 z.property))
  right_inv f := funext fun v ↦ vertexTermComponent_liftVertex f v

end VertexTerm

section ArrowTerm

/-- The generator `m ↦ eⱼ ⊗ m` of the arrow term in the component of `b : i ⟶ j`. -/
private noncomputable def arrowGen {i j : Q} (b : i ⟶ j) :
    vertexComponent k X i →ₗ[k] standardArrowTerm k Q X :=
  (((Finsupp.lsingle (R := k) (⟨i, j, b⟩ : Σ i j : Q, i ⟶ j)).comp
    (TensorProduct.mk k 𝒜 X (ε j))).comp (vertexComponent k X i).subtype).codRestrict
    ((standardArrowTerm k Q X).restrictScalars k) fun m ↦
      single_vertexIdempotent_tmul_mem_standardArrowTerm b m.property

private theorem coe_arrowGen {i j : Q} (b : i ⟶ j) (m : vertexComponent k X i) :
    (arrowGen b m : (Σ i j : Q, i ⟶ j) →₀ 𝒜 ⊗[k] X) =
      Finsupp.single ⟨i, j, b⟩ ((ε j : 𝒜) ⊗ₜ[k] (m : X)) := (rfl)

private theorem vertexIdempotent_smul_arrowGen {i j : Q} (b : i ⟶ j)
    (m : vertexComponent k X i) : (ε j : 𝒜) • arrowGen b m = arrowGen b m :=
  Subtype.ext (by rw [Submodule.coe_smul, coe_arrowGen, Finsupp.smul_single, smul_tmul',
    smul_eq_mul, vertexIdempotent_mul_self])

/-- The value of a map out of the arrow term on a generator in the component of `b : i ⟶ j` lies
in the vertex component at `j`. -/
private theorem apply_arrowGen_mem (g : standardArrowTerm k Q X →ₗ[𝒜] N) {i j : Q} (b : i ⟶ j)
    (m : vertexComponent k X i) : g (arrowGen b m) ∈ vertexComponent k N j := by
  rw [mem_vertexComponent_iff_smul_eq_self, ← map_smul, vertexIdempotent_smul_arrowGen]

/-- The component at `b : i ⟶ j` of a map out of the arrow term: `m ↦ g (eⱼ ⊗ m)`. -/
private noncomputable def arrowTermComponent (g : standardArrowTerm k Q X →ₗ[𝒜] N) (i j : Q)
    (b : i ⟶ j) : vertexComponent k X i →ₗ[k] vertexComponent k N j :=
  ((g.restrictScalars k).comp (arrowGen b)).codRestrict _ (apply_arrowGen_mem g b)

private theorem coe_arrowTermComponent (g : standardArrowTerm k Q X →ₗ[𝒜] N) {i j : Q}
    (b : i ⟶ j) (m : vertexComponent k X i) :
    (arrowTermComponent g i j b m : N) = g (arrowGen b m) := (rfl)

/-- The `k`-linear map `X → N` at an arrow `b : i ⟶ j`, `m ↦ f (eᵢ m)`. -/
private noncomputable def glueArrow
    (f : ∀ i j : Q, (i ⟶ j) → (vertexComponent k X i →ₗ[k] vertexComponent k N j))
    (b : Σ i j : Q, i ⟶ j) : X →ₗ[k] N :=
  (vertexComponent k N b.2.1).subtype ∘ₗ f b.1 b.2.1 b.2.2 ∘ₗ vertexProjection k X b.1

/-- The `kQ`-linear map out of `(Σ i j, i ⟶ j) →₀ kQ ⊗_k X` extending a family of arrow maps,
`x ⊗ m ↦ x • f (eᵢ m)` in the component of `b : i ⟶ j`. -/
private noncomputable def liftArrow
    (f : ∀ i j : Q, (i ⟶ j) → (vertexComponent k X i →ₗ[k] vertexComponent k N j)) :
    ((Σ i j : Q, i ⟶ j) →₀ 𝒜 ⊗[k] X) →ₗ[𝒜] N :=
  Finsupp.lsum ℕ fun b ↦ tensorSMul k 𝒜 N ∘ₗ AlgebraTensorModule.map LinearMap.id (glueArrow f b)

private theorem liftArrow_single_tmul
    (f : ∀ i j : Q, (i ⟶ j) → (vertexComponent k X i →ₗ[k] vertexComponent k N j))
    {i j : Q} (b : i ⟶ j) (x : 𝒜) (m : X) :
    liftArrow f (Finsupp.single ⟨i, j, b⟩ (x ⊗ₜ m)) =
      x • (f i j b (vertexProjection k X i m) : N) := by
  simp [liftArrow, glueArrow]

/-- Extending the components of `g` recovers `g` after the arrow projection. -/
private theorem liftArrow_arrowTermComponent (g : standardArrowTerm k Q X →ₗ[𝒜] N) :
    liftArrow (arrowTermComponent g) =
      g ∘ₗ (standardArrowProjection k Q X).codRestrict _
        standardArrowProjection_mem_standardArrowTerm := by
  refine Finsupp.lhom_ext' fun ⟨i, j, b⟩ ↦ AlgebraTensorModule.ext fun x m ↦ ?_
  have h : (standardArrowProjection k Q X).codRestrict _
      standardArrowProjection_mem_standardArrowTerm (Finsupp.single ⟨i, j, b⟩ (x ⊗ₜ m)) =
      x • arrowGen b (vertexProjection k X i m) :=
    Subtype.ext (by simp [coe_arrowGen, Finsupp.smul_single, smul_tmul'])
  simp only [LinearMap.comp_apply, Finsupp.lsingle_apply]
  rw [liftArrow_single_tmul, coe_arrowTermComponent, h, map_smul]

/-- The components of the restriction of an extended family are the family. -/
private theorem arrowTermComponent_liftArrow
    (f : ∀ i j : Q, (i ⟶ j) → (vertexComponent k X i →ₗ[k] vertexComponent k N j))
    {i j : Q} (b : i ⟶ j) :
    arrowTermComponent ((liftArrow f).domRestrict (standardArrowTerm k Q X)) i j b = f i j b := by
  refine LinearMap.ext fun m ↦ Subtype.ext ?_
  rw [coe_arrowTermComponent, LinearMap.domRestrict_apply, coe_arrowGen, liftArrow_single_tmul,
    show vertexProjection k X i m = m from
      Subtype.ext (coe_vertexProjection_apply_of_mem m.property),
    vertexIdempotent_smul_eq_self_of_mem_vertexComponent (f i j b m).property]

variable (k Q X N) in
/-- **Maps out of the arrow term of the standard resolution** `⨁_{b : i ⟶ j} kQ eⱼ ⊗_k eᵢ X` are
the families of `k`-linear maps from the source space to the target space of each arrow: a map
`g` corresponds to the family `m ↦ g (eⱼ ⊗ m)` in the component of `b : i ⟶ j`. -/
noncomputable def standardArrowTermHomEquiv :
    (standardArrowTerm k Q X →ₗ[𝒜] N) ≃ₗ[k]
      QuiverRep.HomArrow (quiverRepOfModule k Q X) (quiverRepOfModule k Q N) where
  toFun g := arrowTermComponent g
  invFun f := (liftArrow f).domRestrict _
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv g := by
    refine LinearMap.ext fun y ↦ ?_
    rw [LinearMap.domRestrict_apply, liftArrow_arrowTermComponent, LinearMap.comp_apply]
    exact congrArg g (Subtype.ext (mem_standardArrowTerm_iff.1 y.property))
  right_inv f := funext fun i ↦ funext fun j ↦ funext fun b ↦ arrowTermComponent_liftArrow f b

end ArrowTerm

/-- **The standard resolution computes the Hom differential.** Under the identifications of maps
out of the two terms of the standard resolution with families of vertex maps and of arrow maps,
precomposition with the differential `x ⊗ m ↦ x b ⊗ m - x ⊗ b m` is the Hom differential
`(fᵥ) ↦ (N(b) fᵢ - fⱼ X(b))`. -/
theorem standardArrowTermHomEquiv_comp_standardDifferential
    (g : standardVertexTerm k Q X →ₗ[𝒜] N) :
    standardArrowTermHomEquiv k Q X N (g ∘ₗ standardDifferential k Q X) =
      QuiverRep.homDifferential _ _ (standardVertexTermHomEquiv k Q X N g) := by
  -- unfold the two identifications, so that the family the Hom differential is applied to is
  -- typed by the vertex components rather than by the vertex spaces of the representation
  change arrowTermComponent (g ∘ₗ standardDifferential k Q X) =
    QuiverRep.homDifferential (quiverRepOfModule k Q X) (quiverRepOfModule k Q N)
      (vertexTermComponent g)
  funext i j b
  -- the Hom differential between the representations carried by modules, with path maps
  have hd : QuiverRep.homDifferential (quiverRepOfModule k Q X) (quiverRepOfModule k Q N)
      (vertexTermComponent g) i j b = (pathMap k N b.toPath).comp (vertexTermComponent g i) -
        (vertexTermComponent g j).comp (pathMap k X b.toPath) :=
    QuiverRep.homDifferential_apply (quiverRepOfModule k Q X) (quiverRepOfModule k Q N)
      (vertexTermComponent g) b
  rw [hd]
  refine LinearMap.ext fun (m : vertexComponent k X i) ↦ Subtype.ext ?_
  have h : standardDifferential k Q X (arrowGen b m) =
      (ofPath ⟨i, j, b.toPath⟩ : 𝒜) • vertexGen i m - vertexGen j (pathMap k X b.toPath m) :=
    Subtype.ext (by
      simp [coe_arrowGen, coe_vertexGen, smul_tmul'])
  rw [coe_arrowTermComponent, LinearMap.comp_apply, h, LinearMap.sub_apply, LinearMap.comp_apply,
    LinearMap.comp_apply, Submodule.coe_sub, coe_pathMap_apply, coe_vertexTermComponent,
    coe_vertexTermComponent]
  exact (map_sub g _ _).trans (by rw [map_smul])

section Ext

open Abelian
open scoped ModuleCat

variable [Small.{t} (pathAlgebra k Q)]

/-- The vertex term of the standard resolution of a module is no larger than the path algebra and
the module. -/
instance small_standardVertexTerm : Small.{t} (standardVertexTerm k Q X) :=
  small_of_injective Subtype.val_injective

variable (k Q)

/-- The vertex term of the standard resolution of `X`, in the universe of `X`. -/
private noncomputable def vertexTermShrink (X : ModuleCat.{t} 𝒜) : ModuleCat.{t} 𝒜 :=
  ModuleCat.of 𝒜 (Shrink.{t} (standardVertexTerm k Q X))

/-- The small model of the vertex term is the vertex term. -/
private noncomputable def vertexTermShrinkEquiv (X : ModuleCat.{t} 𝒜) :
    (vertexTermShrink k Q X : Type t) ≃ₗ[𝒜] standardVertexTerm k Q X :=
  Shrink.linearEquiv 𝒜 (standardVertexTerm k Q X)

/-- The augmentation of the standard resolution on the small model of its vertex term. -/
private noncomputable def shrinkAugmentation (X : ModuleCat.{t} 𝒜) :
    (vertexTermShrink k Q X : Type t) →ₗ[𝒜] X :=
  standardAugmentation k Q X ∘ₗ (vertexTermShrinkEquiv k Q X).toLinearMap

variable {k Q}

private theorem shrinkAugmentation_surjective (X : ModuleCat.{t} 𝒜) :
    Function.Surjective (shrinkAugmentation k Q X) :=
  standardAugmentation_surjective.comp (vertexTermShrinkEquiv k Q X).surjective

/-- The arrow term of the standard resolution is the kernel of the augmentation on the small model
of the vertex term, through the differential. -/
private noncomputable def arrowTermEquivKer (X : ModuleCat.{t} 𝒜) :
    standardArrowTerm k Q X ≃ₗ[𝒜] LinearMap.ker (shrinkAugmentation k Q X) :=
  LinearEquiv.ofBijective
    (((vertexTermShrinkEquiv k Q X).symm.toLinearMap ∘ₗ standardDifferential k Q X).codRestrict _
      fun y ↦ by
        simp [shrinkAugmentation,
          exact_standardDifferential_standardAugmentation.apply_apply_eq_zero])
    ⟨fun y y' h ↦ standardDifferential_injective
        ((vertexTermShrinkEquiv k Q X).symm.injective (congrArg Subtype.val h)),
      fun z ↦ by
        obtain ⟨y, hy⟩ := (exact_standardDifferential_standardAugmentation
          ((vertexTermShrinkEquiv k Q X) z)).1 z.property
        exact ⟨y, Subtype.ext ((congrArg (vertexTermShrinkEquiv k Q X).symm hy).trans
          ((vertexTermShrinkEquiv k Q X).symm_apply_apply _))⟩⟩

/-- The small model of the vertex term is projective. -/
private instance (X : ModuleCat.{t} 𝒜) :
    Projective (shrinkAugmentation k Q X).shortComplexKer.X₂ :=
  haveI : Module.Projective 𝒜 (vertexTermShrink k Q X : Type t) :=
    Module.Projective.of_equiv (vertexTermShrinkEquiv k Q X).symm
  ModuleCat.projective_of_categoryTheory_projective _

/-- Maps out of the kernel of the shrunk augmentation are families of arrow maps. -/
private noncomputable def kerHomEquiv (X N : ModuleCat.{t} 𝒜) :
    ((shrinkAugmentation k Q X).shortComplexKer.X₁ ⟶ N) ≃ₗ[k]
      QuiverRep.HomArrow (quiverRepOfModule k Q X) (quiverRepOfModule k Q N) :=
  ModuleCat.homLinearEquiv.trans ((LinearEquiv.congrLeft N k (arrowTermEquivKer X).symm).trans
    (standardArrowTermHomEquiv k Q X N))

/-- Maps out of the shrunk vertex term are families of vertex maps. -/
private noncomputable def vertexTermShrinkHomEquiv (X N : ModuleCat.{t} 𝒜) :
    ((shrinkAugmentation k Q X).shortComplexKer.X₂ ⟶ N) ≃ₗ[k]
      QuiverRep.HomVertex (quiverRepOfModule k Q X) (quiverRepOfModule k Q N) :=
  ModuleCat.homLinearEquiv.trans ((LinearEquiv.congrLeft N k (vertexTermShrinkEquiv k Q X)).trans
    (standardVertexTermHomEquiv k Q X N))

private theorem kerHomEquiv_comp (X N : ModuleCat.{t} 𝒜)
    (g : (shrinkAugmentation k Q X).shortComplexKer.X₂ ⟶ N) :
    kerHomEquiv X N ((shrinkAugmentation k Q X).shortComplexKer.f ≫ g) =
      QuiverRep.homDifferential _ _ (vertexTermShrinkHomEquiv X N g) := by
  -- `kerHomEquiv` and `vertexTermShrinkHomEquiv` are composites of `ModuleCat.homLinearEquiv`,
  -- precomposition with a linear equivalence and the identifications above, and
  -- `arrowTermEquivKer` is the differential followed by the inverse of `vertexTermShrinkEquiv`,
  -- so the three equations below hold by unfolding these definitions
  have h : ((shrinkAugmentation k Q X).shortComplexKer.f ≫ g).hom ∘ₗ
      (arrowTermEquivKer X).toLinearMap =
      (g.hom ∘ₗ (vertexTermShrinkEquiv k Q X).symm.toLinearMap) ∘ₗ standardDifferential k Q X :=
    LinearMap.ext fun y ↦ rfl
  have hk : kerHomEquiv X N ((shrinkAugmentation k Q X).shortComplexKer.f ≫ g) =
      standardArrowTermHomEquiv k Q X N
        (((shrinkAugmentation k Q X).shortComplexKer.f ≫ g).hom ∘ₗ
          (arrowTermEquivKer X).toLinearMap) := rfl
  have hv : vertexTermShrinkHomEquiv X N g =
      standardVertexTermHomEquiv k Q X N
        (g.hom ∘ₗ (vertexTermShrinkEquiv k Q X).symm.toLinearMap) := rfl
  rw [hk, hv, ← standardArrowTermHomEquiv_comp_standardDifferential, h]

private theorem map_range_leftComp (X N : ModuleCat.{t} 𝒜) :
    (Linear.leftComp k N (shrinkAugmentation k Q X).shortComplexKer.f).range.map
        (kerHomEquiv X N : _ →ₗ[k] _) =
      (QuiverRep.homDifferential (quiverRepOfModule k Q X) (quiverRepOfModule k Q N)).range := by
  ext c
  constructor
  · rintro ⟨_, ⟨g, rfl⟩, rfl⟩
    exact ⟨vertexTermShrinkHomEquiv X N g, (kerHomEquiv_comp X N g).symm⟩
  · rintro ⟨f, rfl⟩
    refine ⟨_, ⟨(vertexTermShrinkHomEquiv X N).symm f, rfl⟩, ?_⟩
    rw [LinearEquiv.coe_coe, Linear.leftComp_apply, kerHomEquiv_comp, LinearEquiv.apply_symm_apply]

variable (k Q) in
/-- **The cokernel of the Hom differential is `Ext¹`.** For modules `X` and `N` over the path
algebra `kQ` of a quiver with finitely many vertices over a field, the cokernel of the Hom
differential `(fᵥ) ↦ (N(b) fᵢ - fⱼ X(b))` between the representations they carry is `k`-linearly
`Ext¹(X, N)`. There is no finiteness or acyclicity hypothesis on the quiver beyond the finite
vertex set, and the modules may be infinite-dimensional; the path algebra is assumed `t`-small,
so that `Ext` is defined in `ModuleCat.{t} kQ`.

The comparison applies `Hom(-, N)` to the standard resolution of `X`: maps out of its two terms
are the families of vertex maps and of arrow maps (`standardVertexTermHomEquiv`,
`standardArrowTermHomEquiv`), precomposition with its differential is the Hom differential
(`standardArrowTermHomEquiv_comp_standardDifferential`), and since its middle term is projective
the cokernel of that precomposition is `Ext¹(X, N)` (`TauCeti.homCokernelEquivExt`). -/
noncomputable def homDifferentialCokerEquivExt (X N : ModuleCat.{t} 𝒜) :
    (QuiverRep.HomArrow (quiverRepOfModule k Q X) (quiverRepOfModule k Q N) ⧸
      (QuiverRep.homDifferential (quiverRepOfModule k Q X) (quiverRepOfModule k Q N)).range) ≃ₗ[k]
      Ext X N 1 :=
  (Submodule.Quotient.equiv _ _ (kerHomEquiv X N) (map_range_leftComp X N)).symm.trans
    (homCokernelEquivExt k
      (LinearMap.shortExact_shortComplexKer (shrinkAugmentation_surjective X)) N)

end Ext

end PathAlgebra

namespace QuiverRep

open Abelian
open scoped ModuleCat

variable {k : Type u} [Field k] {Q : Type v} [Quiver.{w} Q] [Finite Q]
  [Small.{t} (pathAlgebra k Q)]

/-- **The cokernel of the Hom differential of two representations is `Ext¹`** of the
corresponding modules over the path algebra. For representations `M` and `N` of a quiver with
finitely many vertices over a field, `HomArrow M N` modulo the image of the Hom differential
`(fᵥ) ↦ (N(b) fᵢ - fⱼ M(b))` is `k`-linearly isomorphic to `Ext¹(M, N)`, computed in the category
of modules over the path algebra. There is no acyclicity hypothesis, and the vertex spaces may be
infinite-dimensional. The canonical comparison for modules over the path algebra is
`TauCeti.PathAlgebra.homDifferentialCokerEquivExt`. -/
theorem nonempty_homDifferential_coker_linearEquiv_ext (M N : QuiverRep.{u, v, w, t} k Q) :
    Nonempty ((HomArrow M N ⧸ (homDifferential M N).range) ≃ₗ[k]
      Ext ((quiverRepEquivalence k Q).functor.obj M)
        ((quiverRepEquivalence k Q).functor.obj N) 1) := by
  have := Fintype.ofFinite Q
  -- a representation is the representation carried by the module it corresponds to
  have e (P : QuiverRep.{u, v, w, t} k Q) :
      P ≅ quiverRepOfModule k Q ((quiverRepEquivalence k Q).functor.obj P) :=
    (quiverRepEquivalence k Q).unitIso.app P ≪≫ eqToIso (by
      rw [Functor.comp_obj, quiverRepEquivalence_inverse, quiverRepFunctor_obj])
  exact ⟨(homDifferentialCokerCongr (e M) (e N)).trans
    (PathAlgebra.homDifferentialCokerEquivExt k Q _ _)⟩

/-- **The Euler form is `dim Hom - dim Ext¹`.** For pointwise finite-dimensional representations
`M` and `N` of a finite quiver over a field, `⟨dim M, dim N⟩ = dim Hom(M, N) - dim Ext¹(M, N)`,
both dimensions cast to `ℤ`, with `Ext¹` computed over the path algebra. The quiver may have
oriented cycles, where the path algebra is infinite-dimensional. -/
theorem eulerForm_eq_finrank_hom_sub_finrank_ext [Fintype Q] [∀ i j : Q, Fintype (i ⟶ j)]
    (M N : QuiverRep.{u, v, w, t} k Q) (hM : ∀ i : Q, FiniteDimensional k (M.obj i))
    (hN : ∀ i : Q, FiniteDimensional k (N.obj i)) :
    eulerForm Q (fun i ↦ (dimVector M i : ℤ)) (fun i ↦ (dimVector N i : ℤ)) =
      (Module.finrank k (M ⟶ N) : ℤ) -
        Module.finrank k (Ext ((quiverRepEquivalence k Q).functor.obj M)
          ((quiverRepEquivalence k Q).functor.obj N) 1) := by
  obtain ⟨e⟩ := nonempty_homDifferential_coker_linearEquiv_ext M N
  rw [eulerForm_eq_finrank_hom_sub_finrank_coker M N hM hN, e.finrank_eq]

end QuiverRep

end TauCeti

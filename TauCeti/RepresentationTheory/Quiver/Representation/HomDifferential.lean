/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Quiver.Representation.FiniteDimensional
public import TauCeti.RepresentationTheory.Quiver.Representation.DimensionVector
public import TauCeti.RepresentationTheory.Quiver.EulerForm
public import Mathlib.CategoryTheory.Linear.FunctorCategory
public import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# The Hom differential of quiver representations

The Hom differential sends a family of vertex maps `fᵢ : Mᵢ → Nᵢ` to the arrowwise
commutativity defects `N(a) fᵢ - fⱼ M(a)`. Its kernel is the space of representation
morphisms. For finite-dimensional representations of a finite quiver, the difference
between the dimensions of its kernel and cokernel is the Euler form.

The cokernel measures the obstruction to making vertexwise splittings of extensions
compatible with the arrows; for a quiver with finitely many vertices, it is `Ext¹` of the
corresponding modules over the path algebra
(`TauCeti.QuiverRep.nonempty_homDifferential_coker_linearEquiv_ext`). The Hom differential is
natural in morphisms of both representations (`TauCeti.QuiverRep.homDifferential_naturality`).
Isomorphisms of the two representations identify the spaces of vertex maps and of arrow maps
compatibly with the Hom differential (`TauCeti.QuiverRep.homDifferential_homVertexCongr`), so the
cokernel depends on the representations only up to isomorphism
(`TauCeti.QuiverRep.homDifferentialCokerCongr`). The constructions here require no acyclicity
assumption.

## References

H. Derksen and J. Weyman, *An Introduction to Quiver Representations*, Chapter 1,
for the vertex-and-arrow Hom differential and the Euler form.
-/

public section

namespace TauCeti.QuiverRep

open CategoryTheory

universe u v w t

variable {k : Type u} {Q : Type v} [Field k] [Quiver.{w} Q]
variable (M N : QuiverRep.{u, v, w, t} k Q)

/-- Families of linear maps between corresponding vertex spaces. -/
abbrev HomVertex := ∀ i : Q, vertexSpace k Q M i →ₗ[k] vertexSpace k Q N i

/-- The vertex components of a morphism of representations, retyped between vertex spaces. -/
noncomputable def homVertex (f : M ⟶ N) : HomVertex M N :=
  fun i ↦ (f.app ((Paths.of Q).obj i)).hom

-- Keep the typed vertex family in normal form rather than reverting to path objects.
/-- The vertex family of a morphism evaluates to its components. -/
theorem homVertex_apply (f : M ⟶ N) (i : Q) (x : vertexSpace k Q M i) :
    homVertex M N f i x = (f.app ((Paths.of Q).obj i)).hom x := (rfl)

variable {M N} in
/-- Vertex components of a composite are the composites at each vertex. -/
@[simp]
theorem homVertex_comp {P : QuiverRep.{u, v, w, t} k Q} (f : M ⟶ N) (g : N ⟶ P) (i : Q) :
    homVertex M P (f ≫ g) i = (homVertex N P g i).comp (homVertex M N f i) := (rfl)

/-- The identity morphism has the identity linear map at each vertex. -/
@[simp]
theorem homVertex_id (i : Q) : homVertex M M (𝟙 M) i = LinearMap.id := (rfl)

/-- The zero morphism has the zero linear map at each vertex. -/
@[simp]
theorem homVertex_zero (i : Q) : homVertex M N 0 i = 0 := (rfl)

variable {M N} in
/-- Taking vertex components commutes with scalar multiplication. -/
@[simp]
theorem homVertex_smul (r : k) (f : M ⟶ N) (i : Q) :
    homVertex M N (r • f) i = r • homVertex M N f i := (rfl)

/-- The vertex components of a morphism commute with each arrow action. -/
theorem homVertex_naturality (f : M ⟶ N) (i j : Q) (a : i ⟶ j)
    (x : vertexSpace k Q M i) :
    homVertex M N f j (mapₗ k Q M a.toPath x) =
      mapₗ k Q N a.toPath (homVertex M N f i x) :=
  congrArg (fun p ↦ p x) (f.naturality ((Paths.of Q).map a))

/-- Families of linear maps from the source space of each arrow to its target space. -/
abbrev HomArrow := ∀ i j : Q, (i ⟶ j) → (vertexSpace k Q M i →ₗ[k] vertexSpace k Q N j)

/-- The arrowwise commutativity defect of a family of vertex maps. -/
noncomputable def homDifferential : HomVertex M N →ₗ[k] HomArrow M N where
  toFun f i j a := (mapₗ k Q N a.toPath).comp (f i) -
    (f j).comp (mapₗ k Q M a.toPath)
  map_add' f g := by
    ext i j a x
    simp only [Pi.add_apply, LinearMap.add_apply, LinearMap.comp_apply, map_add,
      LinearMap.sub_apply]
    abel
  map_smul' c f := by
    ext i j a x
    simp [smul_sub]

/-- Evaluation of the Hom differential on an arrow. -/
@[simp]
theorem homDifferential_apply (f : HomVertex M N) {i j : Q} (a : i ⟶ j) :
    homDifferential M N f i j a = (mapₗ k Q N a.toPath).comp (f i) -
      (f j).comp (mapₗ k Q M a.toPath) := (rfl)

/-- The Hom differential vanishes precisely when the vertex maps commute with every arrow. -/
@[simp]
theorem homDifferential_eq_zero_iff (f : HomVertex M N) :
    homDifferential M N f = 0 ↔ ∀ (i j : Q) (a : i ⟶ j),
      (mapₗ k Q N a.toPath).comp (f i) =
        (f j).comp (mapₗ k Q M a.toPath) := by
  simp only [funext_iff, homDifferential_apply, Pi.zero_apply,
    sub_eq_zero]

/-- The kernel of the Hom differential is the space of representation morphisms. -/
noncomputable def homEquivKerDifferential : (M ⟶ N) ≃ₗ[k] (homDifferential M N).ker where
  toFun f := ⟨homVertex M N f, LinearMap.mem_ker.mpr <|
    (homDifferential_eq_zero_iff M N _).mpr fun i j a ↦ by
    exact congrArg ModuleCat.Hom.hom (f.naturality ((Paths.of Q).map a)).symm⟩
  invFun f :=
    let app : ∀ i : Q, M.obj i ⟶ N.obj i := fun i ↦ ModuleCat.ofHom (f.val i)
    { app := app
      naturality := by
        intro i j p
        have ha := (homDifferential_eq_zero_iff M N f.val).mp (LinearMap.mem_ker.mp f.property)
        refine Paths.induction_fixed_source
          (P := fun {j} p ↦ M.map p ≫ app j = app i ≫ N.map p) (by simp) ?_ p
        intro a b p e hp
        have he : M.map ((Paths.of Q).map e) ≫ app b =
            app a ≫ N.map ((Paths.of Q).map e) :=
          ModuleCat.hom_ext (ha a b e).symm
        simp only [Functor.map_comp, Category.assoc]
        -- The inclusion into Paths is the identity on vertices; `erw` matches its retyping.
        erw [he, ← Category.assoc, hp, Category.assoc] }
  left_inv f := by ext; rfl
  right_inv f := by rfl
  map_add' f g := by rfl
  map_smul' c f := by rfl

/-- The kernel identification sends a morphism to its vertex components. -/
@[simp]
theorem homEquivKerDifferential_apply (f : M ⟶ N) (i : Q) :
    (homEquivKerDifferential M N f).val i = (f.app i).hom := (rfl)

/-- The inverse kernel identification has the prescribed vertex components. -/
@[simp]
theorem homEquivKerDifferential_symm_apply (f : (homDifferential M N).ker) (i : Q) :
    ((homEquivKerDifferential M N).symm f).app i = ModuleCat.ofHom (f.val i) := (rfl)

variable {M N} in
/-- Morphisms between pointwise finite-dimensional representations of a quiver with finitely
many vertices form a finite-dimensional vector space. No finiteness of the arrows is needed. -/
theorem finiteDimensional_hom [Finite Q] (hM : IsFinDim k Q M) (hN : IsFinDim k Q N) :
    FiniteDimensional k (M ⟶ N) := by
  let : ∀ i : Q, FiniteDimensional k (vertexSpace k Q M i) := fun i ↦ isFinDim_iff.mp hM i
  let : ∀ i : Q, FiniteDimensional k (vertexSpace k Q N i) := fun i ↦ isFinDim_iff.mp hN i
  exact (homEquivKerDifferential M N).symm.finiteDimensional

section Congr

variable {M N} {M' N' : QuiverRep.{u, v, w, t} k Q}

/-- **The Hom differential is natural** in morphisms `M' ⟶ M` and `N ⟶ N'`: conjugating a family
of vertex maps by their vertex components conjugates its arrowwise commutativity defects. -/
theorem homDifferential_naturality (g : M' ⟶ M) (h : N ⟶ N') (φ : HomVertex M N) :
    homDifferential M' N' (fun i ↦ homVertex N N' h i ∘ₗ φ i ∘ₗ homVertex M' M g i) =
      fun i j a ↦ homVertex N N' h j ∘ₗ homDifferential M N φ i j a ∘ₗ homVertex M' M g i := by
  funext i j a
  refine LinearMap.ext fun x ↦ ?_
  simp only [homDifferential_apply, LinearMap.sub_apply, LinearMap.comp_apply, map_sub]
  rw [homVertex_naturality M' M g, homVertex_naturality N N' h]

/-- Isomorphisms `M ≅ M'` and `N ≅ N'` identify the vertex-map families, by conjugating each
vertex map with the vertex components of the isomorphisms. -/
noncomputable def homVertexCongr (e : M ≅ M') (f : N ≅ N') : HomVertex M N ≃ₗ[k] HomVertex M' N' :=
  LinearEquiv.piCongrRight fun i ↦ LinearEquiv.arrowCongr
    (e.app ((Paths.of Q).obj i)).toLinearEquiv (f.app ((Paths.of Q).obj i)).toLinearEquiv

@[simp]
theorem homVertexCongr_apply (e : M ≅ M') (f : N ≅ N') (φ : HomVertex M N) (i : Q) :
    homVertexCongr e f φ i = homVertex N N' f.hom i ∘ₗ φ i ∘ₗ homVertex M' M e.inv i := (rfl)

/-- The inverse of `homVertexCongr e f` conjugates by the inverse isomorphisms. -/
@[simp]
theorem homVertexCongr_symm (e : M ≅ M') (f : N ≅ N') :
    (homVertexCongr e f).symm = homVertexCongr e.symm f.symm := (rfl)

/-- Isomorphisms `M ≅ M'` and `N ≅ N'` identify the arrow-map families, by conjugating the map at
an arrow with the vertex components of the isomorphisms at its source and target. -/
noncomputable def homArrowCongr (e : M ≅ M') (f : N ≅ N') : HomArrow M N ≃ₗ[k] HomArrow M' N' :=
  LinearEquiv.piCongrRight fun i ↦ LinearEquiv.piCongrRight fun j ↦ LinearEquiv.piCongrRight
    fun _ ↦ LinearEquiv.arrowCongr (e.app ((Paths.of Q).obj i)).toLinearEquiv
      (f.app ((Paths.of Q).obj j)).toLinearEquiv

@[simp]
theorem homArrowCongr_apply (e : M ≅ M') (f : N ≅ N') (φ : HomArrow M N) {i j : Q} (a : i ⟶ j) :
    homArrowCongr e f φ i j a = homVertex N N' f.hom j ∘ₗ φ i j a ∘ₗ homVertex M' M e.inv i :=
  (rfl)

/-- The inverse of `homArrowCongr e f` conjugates by the inverse isomorphisms. -/
@[simp]
theorem homArrowCongr_symm (e : M ≅ M') (f : N ≅ N') :
    (homArrowCongr e f).symm = homArrowCongr e.symm f.symm := (rfl)

/-- **The Hom differential is natural in isomorphisms of both representations.** -/
theorem homDifferential_homVertexCongr (e : M ≅ M') (f : N ≅ N') (φ : HomVertex M N) :
    homDifferential M' N' (homVertexCongr e f φ) = homArrowCongr e f (homDifferential M N φ) :=
  homDifferential_naturality e.inv f.hom φ

/-- **The cokernel of the Hom differential is invariant under isomorphisms** of both
representations. -/
noncomputable def homDifferentialCokerCongr (e : M ≅ M') (f : N ≅ N') :
    (HomArrow M N ⧸ (homDifferential M N).range) ≃ₗ[k]
      (HomArrow M' N' ⧸ (homDifferential M' N').range) :=
  Submodule.Quotient.equiv _ _ (homArrowCongr e f) <| by
    have h : (homArrowCongr e f).toLinearMap ∘ₗ homDifferential M N =
        homDifferential M' N' ∘ₗ (homVertexCongr e f).toLinearMap :=
      LinearMap.ext fun φ ↦ (homDifferential_homVertexCongr e f φ).symm
    rw [← LinearMap.range_comp, h, LinearMap.range_comp_of_range_eq_top _ (LinearEquiv.range _)]

@[simp]
theorem homDifferentialCokerCongr_mk (e : M ≅ M') (f : N ≅ N') (φ : HomArrow M N) :
    homDifferentialCokerCongr e f (Submodule.Quotient.mk φ) =
      Submodule.Quotient.mk (homArrowCongr e f φ) := (rfl)

/-- The inverse of `homDifferentialCokerCongr e f` is induced by the inverse isomorphisms. -/
@[simp]
theorem homDifferentialCokerCongr_symm (e : M ≅ M') (f : N ≅ N') :
    (homDifferentialCokerCongr e f).symm = homDifferentialCokerCongr e.symm f.symm := (rfl)

end Congr

section Dimension

variable [Fintype Q] [∀ i j : Q, Fintype (i ⟶ j)]
variable (hM : ∀ i : Q, FiniteDimensional k (M.obj i))
variable (hN : ∀ i : Q, FiniteDimensional k (N.obj i))

include hM hN

/-- The Euler form is the vertex-map dimension minus the arrow-map dimension. -/
theorem eulerForm_eq_finrank_homVertex_sub_finrank_homArrow :
    eulerForm Q (fun i ↦ (dimVector M i : ℤ)) (fun i ↦ (dimVector N i : ℤ)) =
      (Module.finrank k (HomVertex M N) : ℤ) - Module.finrank k (HomArrow M N) := by
  let : ∀ i, FiniteDimensional k (vertexSpace k Q M i) := hM
  let : ∀ i, FiniteDimensional k (vertexSpace k Q N i) := hN
  simp only [HomVertex, HomArrow, Module.finrank_pi_fintype, Module.finrank_linearMap,
    Nat.cast_sum, Nat.cast_mul]
  simp only [eulerForm_def, dimVector_apply, vertexSpace, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul]
  rfl

/-- The Euler form is the morphism dimension minus the cokernel dimension of the Hom
differential. -/
theorem eulerForm_eq_finrank_hom_sub_finrank_coker :
    eulerForm Q (fun i ↦ (dimVector M i : ℤ)) (fun i ↦ (dimVector N i : ℤ)) =
      (Module.finrank k (M ⟶ N) : ℤ) -
        Module.finrank k (HomArrow M N ⧸ (homDifferential M N).range) := by
  let : ∀ i, FiniteDimensional k (vertexSpace k Q M i) := hM
  let : ∀ i, FiniteDimensional k (vertexSpace k Q N i) := hN
  rw [eulerForm_eq_finrank_homVertex_sub_finrank_homArrow M N hM hN,
    (homEquivKerDifferential M N).finrank_eq]
  have hr := (homDifferential M N).finrank_range_add_finrank_ker
  have hc := (homDifferential M N).range.finrank_quotient_add_finrank
  omega

/-- Surjectivity of the Hom differential is detected by equality between the Euler form
and the dimension of the morphism space. -/
theorem homDifferential_surjective_iff :
    Function.Surjective (homDifferential M N) ↔
      eulerForm Q (fun i ↦ (dimVector M i : ℤ)) (fun i ↦ (dimVector N i : ℤ)) =
        (Module.finrank k (M ⟶ N) : ℤ) := by
  let : ∀ i, FiniteDimensional k (vertexSpace k Q M i) := hM
  let : ∀ i, FiniteDimensional k (vertexSpace k Q N i) := hN
  rw [eulerForm_eq_finrank_hom_sub_finrank_coker M N hM hN]
  rw [LinearMap.range_eq_top.symm]
  have hc := (homDifferential M N).range.finrank_quotient_add_finrank
  constructor
  · intro h
    have hd := congrArg (fun p : Submodule k (HomArrow M N) ↦ Module.finrank k p) h
    simp only [finrank_top] at hd
    omega
  · intro h
    exact Submodule.eq_top_of_finrank_eq (by omega)

end Dimension

end TauCeti.QuiverRep

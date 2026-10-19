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
compatible with the arrows. The constructions here require no acyclicity assumption.

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

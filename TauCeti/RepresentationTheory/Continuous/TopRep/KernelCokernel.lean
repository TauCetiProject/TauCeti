/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RepresentationTheory.Continuous.TopRep
public import TauCeti.RepresentationTheory.Continuous.Subrepresentation

/-!
# Kernels and cokernels in `TopRep k G`

For a morphism `f : A ⟶ B` of continuous representations, the kernel of the underlying linear
map is an invariant submodule of `A` and the range is an invariant submodule of `B`. With the
subspace and quotient topologies they carry continuous representations
(`ContRepresentation.subrepresentation`, `ContRepresentation.quotient`), and they are the kernel
and the cokernel of `f` in `TopRep k G`, as for `TopModuleCat.ker` and `TopModuleCat.coker` in
the category of topological modules.

## Main definitions

* `TopRep.ker`, `TopRep.kerι`: the kernel of a morphism, with its inclusion.
* `TopRep.coker`, `TopRep.cokerπ`: the cokernel of a morphism, with its projection.

## Main results

* `TopRep.isLimitKer`: `TopRep.kerι f` is a kernel of `f`.
* `TopRep.isColimitCoker`: `TopRep.cokerπ f` is a cokernel of `f`.
* `TopRep.exact_kerι`, `TopRep.exact_cokerπ`: the underlying maps of `kerι f, f` and of
  `f, cokerπ f` are exact.
-/

public section

namespace TopRep

open CategoryTheory Limits

variable {k G : Type*} [Ring k] [TopologicalSpace k] [Monoid G] {A B : TopRep k G} (f : A ⟶ B)

/-- The operators of `A` preserve the kernel of a morphism out of `A`. -/
theorem ρ_apply_mem_ker (g : G) (a : A) (ha : a ∈ f.hom.ker) :
    A.ρ g a ∈ f.hom.ker := by
  rw [LinearMap.mem_ker] at ha ⊢
  simp only [ContinuousLinearMap.coe_coe, ContIntertwiningMap.toContinuousLinearMap_apply] at ha ⊢
  rw [hom_comm_apply, ha, map_zero]

/-- The operators of `B` preserve the range of a morphism into `B`. -/
theorem ρ_apply_mem_range (g : G) (b : B) (hb : b ∈ f.hom.range) :
    B.ρ g b ∈ f.hom.range := by
  obtain ⟨a, rfl⟩ := hb
  exact ⟨A.ρ g a, hom_comm_apply f g a⟩

/-- The kernel of a morphism of continuous representations: the kernel of the underlying linear
map with the subspace topology and the restricted action. -/
abbrev ker : TopRep k G :=
  .of (A.ρ.subrepresentation _ (ρ_apply_mem_ker f))

/-- The inclusion of the kernel of a morphism. -/
def kerι : ker f ⟶ A :=
  ofHom
    { toContinuousLinearMap := (f.hom.ker).subtypeL
      isIntertwining' _ := by ext; simp }

-- `simp` reduces the `abbrev` carriers `(ker f).V` and `(coker f).V` in implicit type arguments
-- before it looks a term up, so the evaluation lemmas below state their left-hand sides through
-- `dsimp% only`, as in #8315.
/-- The inclusion of the kernel sends a vector to the same vector of `A`. -/
@[simp]
theorem kerι_apply (a : ker f) : dsimp% only ((kerι f).hom a) = a.1 :=
  (rfl)

/-- The inclusion of the kernel is injective. -/
theorem kerι_injective : Function.Injective (kerι f).hom :=
  Subtype.val_injective

/-- The inclusion of the kernel of `f` is exact at `A` with `f`. -/
theorem exact_kerι : Function.Exact (kerι f).hom f.hom :=
  LinearMap.exact_subtype_ker_map (f.hom : A →ₗ[k] B)

/-- The inclusion of the kernel of `f` composed with `f` is zero. -/
@[reassoc (attr := simp)]
theorem kerι_comp : kerι f ≫ f = 0 := by
  ext a
  exact LinearMap.mem_ker.1 a.2

/-- `TopRep.kerι f` is a kernel of `f` in `TopRep k G`. -/
def isLimitKer : IsLimit (KernelFork.ofι (kerι f) (kerι_comp f)) :=
  KernelFork.IsLimit.ofι _ _
    (fun {X} e he ↦ ofHom
      { toContinuousLinearMap := e.hom.toContinuousLinearMap.codRestrict _ fun x ↦
          congr($he x)
        isIntertwining' g := by
          ext x
          simpa [ContIntertwiningMap.toContinuousLinearMap_apply] using hom_comm_apply e g x })
    (fun _ _ ↦ rfl)
    (fun e he m hm ↦ by
      ext x
      exact congr($hm x))

/-- The cokernel of a morphism of continuous representations: the quotient by the range of the
underlying linear map, with the quotient topology and the descended action. -/
abbrev coker : TopRep k G :=
  .of (B.ρ.quotient _ (ρ_apply_mem_range f))

/-- The projection onto the cokernel of a morphism. -/
def cokerπ : B ⟶ coker f :=
  ofHom
    { toContinuousLinearMap := (f.hom.range).mkQL
      isIntertwining' _ := by ext; simp }

/-- The projection onto the cokernel sends a vector to its class. -/
@[simp]
theorem cokerπ_apply (b : B) : dsimp% only ((cokerπ f).hom b) = Submodule.Quotient.mk b :=
  (rfl)

/-- The projection onto the cokernel is surjective. -/
theorem cokerπ_surjective : Function.Surjective (cokerπ f).hom :=
  Submodule.mkQ_surjective _

/-- `f` is exact at `B` with the projection onto its cokernel. -/
theorem exact_cokerπ : Function.Exact f.hom (cokerπ f).hom :=
  LinearMap.exact_map_mkQ_range (f.hom : A →ₗ[k] B)

/-- `f` composed with the projection onto its cokernel is zero. -/
@[reassoc (attr := simp)]
theorem comp_cokerπ : f ≫ cokerπ f = 0 := by
  ext a
  exact (Submodule.Quotient.mk_eq_zero _).2 ⟨a, rfl⟩

/-- `TopRep.cokerπ f` is a cokernel of `f` in `TopRep k G`. -/
def isColimitCoker : IsColimit (CokernelCofork.ofπ (cokerπ f) (comp_cokerπ f)) :=
  CokernelCofork.IsColimit.ofπ _ _
    (fun {X} e he ↦ ofHom
      { toContinuousLinearMap := Submodule.liftQL _ e.hom.toContinuousLinearMap <| by
          rintro _ ⟨a, rfl⟩
          exact congr($he a)
        isIntertwining' g := by
          ext b
          obtain ⟨b, rfl⟩ := Submodule.mkQ_surjective _ b
          simpa [ContIntertwiningMap.toContinuousLinearMap_apply] using hom_comm_apply e g b })
    (fun _ _ ↦ rfl)
    (fun e he m hm ↦ by
      ext b
      induction b using Submodule.Quotient.induction_on
      exact congr($hm _))

end TopRep

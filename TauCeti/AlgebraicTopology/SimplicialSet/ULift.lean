/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicTopology.SimplicialSet.Monoidal
public import TauCeti.AlgebraicTopology.SimplicialSet.Horn

/-!
# Horn filling in universe lifts of simplicial sets

The universe lift `SSet.uliftFunctor.{v}.obj X` of a simplicial set `X : SSet.{u}` has the
simplices of `X`, wrapped in `ULift`. Horn-filling conditions only involve finitely many
simplices and their faces, so they do not see the universe: the lift of a map `p` has the
right lifting property with respect to a horn inclusion exactly when `p` has it
(`SSet.hasLiftingProperty_horn_ι_uliftFunctor_map_iff`). Consequently the universe lift
preserves and reflects Kan fibrations, inner fibrations, Kan complexes and quasicategories.

This is the universe control needed whenever a construction forces a simplicial set into a
larger universe than its simplices require. For instance, the differential graded nerve of a dg
category whose objects and morphisms live in different universes lies in the larger one, and its
mapping spaces are compared with universe lifts of small simplicial sets built from the Hom
complexes; likewise the mapping spaces of a quasicategory are compared with lifts of small Kan
models.

The comparison goes through compatible families of faces: by
`SSet.hasLiftingProperty_horn_ι_iff`, lifting against a horn inclusion is a statement about
simplices and their faces, and maps from a standard simplex into the universe lift of `X` are
the simplices of `X` (`SSet.uliftFunctorHomEquiv`), compatibly with faces and with maps of
simplicial sets.

## Main results

* `SSet.hasLiftingProperty_horn_ι_uliftFunctor_map_iff`: the universe lift of a map has the right
  lifting property with respect to a horn inclusion exactly when the map has it.
* `SSet.fibration_uliftFunctor_map_iff`, `SSet.innerFibration_uliftFunctor_map_iff`: the
  universe lift preserves and reflects Kan fibrations and inner fibrations.
* `SSet.kanComplex_uliftFunctor_obj_iff`, `SSet.quasicategory_uliftFunctor_obj_iff`: the
  universe lift preserves and reflects Kan complexes and quasicategories.
-/

public section

open CategoryTheory Limits Simplicial HomotopicalAlgebra
open SSet.modelCategoryQuillen

universe u v

namespace SSet

variable {X Y : SSet.{u}}

/-- Maps from a standard simplex into the universe lift of `X` are maps from the standard
simplex into `X`: both are the simplices of `X`. -/
def uliftFunctorHomEquiv (X : SSet.{u}) (n : SimplexCategory) :
    (stdSimplex.{max u v}.obj n ⟶ uliftFunctor.{v}.obj X) ≃ (stdSimplex.{u}.obj n ⟶ X) :=
  yonedaEquiv.trans (Equiv.ulift.trans yonedaEquiv.symm)

@[simp]
theorem yonedaEquiv_uliftFunctorHomEquiv {n : SimplexCategory}
    (f : stdSimplex.{max u v}.obj n ⟶ uliftFunctor.{v}.obj X) :
    yonedaEquiv (uliftFunctorHomEquiv X n f) = (yonedaEquiv f).down :=
  yonedaEquiv.apply_symm_apply _

theorem uliftFunctorHomEquiv_symm_apply {n : SimplexCategory} (f : stdSimplex.{u}.obj n ⟶ X) :
    (uliftFunctorHomEquiv.{u, v} X n).symm f = yonedaEquiv.symm (ULift.up (yonedaEquiv f)) :=
  (rfl)

/-- Lowering a constant map gives the constant map at the lowered vertex. -/
@[simp]
theorem uliftFunctorHomEquiv_const {n : ℕ} (x : (uliftFunctor.{v}.obj X) _⦋0⦌) :
    uliftFunctorHomEquiv X ⦋n⦌ (const x) = const x.down := by
  apply yonedaEquiv.injective
  rw [yonedaEquiv_uliftFunctorHomEquiv]
  rfl

/-- The bijection `SSet.uliftFunctorHomEquiv` is compatible with the simplicial operators. -/
theorem uliftFunctorHomEquiv_map_comp {m n : SimplexCategory} (g : m ⟶ n)
    (f : stdSimplex.{max u v}.obj n ⟶ uliftFunctor.{v}.obj X) :
    uliftFunctorHomEquiv X m (stdSimplex.map g ≫ f) =
      stdSimplex.map g ≫ uliftFunctorHomEquiv X n f := by
  apply yonedaEquiv.injective
  simp only [yonedaEquiv_uliftFunctorHomEquiv, ← yonedaEquiv_naturality]
  -- The simplicial operators of `uliftFunctor.obj X` are those of `X` under `ULift`.
  rfl

/-- The bijection `SSet.uliftFunctorHomEquiv` is compatible with the faces. -/
@[simp]
theorem uliftFunctorHomEquiv_δ_comp {n : ℕ} (j : Fin (n + 2))
    (f : (Δ[n + 1] : SSet.{max u v}) ⟶ uliftFunctor.{v}.obj X) :
    uliftFunctorHomEquiv X ⦋n⦌ (stdSimplex.δ j ≫ f) =
      stdSimplex.δ j ≫ uliftFunctorHomEquiv X ⦋n + 1⦌ f :=
  uliftFunctorHomEquiv_map_comp _ f

/-- The bijection `SSet.uliftFunctorHomEquiv` is natural in the simplicial set. -/
@[simp]
theorem uliftFunctorHomEquiv_comp_map {n : SimplexCategory}
    (f : stdSimplex.{max u v}.obj n ⟶ uliftFunctor.{v}.obj X) (p : X ⟶ Y) :
    uliftFunctorHomEquiv Y n (f ≫ uliftFunctor.map p) = uliftFunctorHomEquiv X n f ≫ p := by
  apply yonedaEquiv.injective
  simp only [yonedaEquiv_uliftFunctorHomEquiv, yonedaEquiv_comp]
  -- The components of `uliftFunctor.map p` are those of `p` under `ULift`.
  rfl

/-- A family of maps from standard simplices into the universe lift of `X` is compatible on a
horn exactly when the corresponding family of maps into `X` is. -/
theorem horn.isCompatible_uliftFunctorHomEquiv_iff {n : ℕ} {i : Fin (n + 2)}
    (f : ∀ (j : Fin (n + 2)) (_ : j ≠ i), (Δ[n] : SSet.{max u v}) ⟶ uliftFunctor.{v}.obj X) :
    horn.IsCompatible (fun j hj ↦ uliftFunctorHomEquiv X ⦋n⦌ (f j hj)) ↔
      horn.IsCompatible f := by
  obtain _ | n := n
  · simp
  · simp only [horn.isCompatible_iff, ← uliftFunctorHomEquiv_δ_comp,
      (uliftFunctorHomEquiv X _).apply_eq_iff_eq]

/-- The universe lift of a map has the right lifting property with respect to a horn inclusion
exactly when the map has it. -/
theorem hasLiftingProperty_horn_ι_uliftFunctor_map_iff (p : X ⟶ Y) {n : ℕ} (i : Fin (n + 2)) :
    HasLiftingProperty Λ[n + 1, i].ι (uliftFunctor.{v}.map p) ↔
      HasLiftingProperty Λ[n + 1, i].ι p := by
  rw [hasLiftingProperty_horn_ι_iff, hasLiftingProperty_horn_ι_iff]
  constructor
  · intro h f hf b comm
    obtain ⟨φ, hφ, hφp⟩ := h (fun j hj ↦ (uliftFunctorHomEquiv X _).symm (f j hj))
      ((horn.isCompatible_uliftFunctorHomEquiv_iff _).1 (by simpa using hf))
      ((uliftFunctorHomEquiv Y _).symm b) fun j hj ↦ (uliftFunctorHomEquiv Y _).injective
        (by simpa using comm j hj)
    refine ⟨uliftFunctorHomEquiv X _ φ, fun j hj ↦ ?_, ?_⟩
    · rw [← uliftFunctorHomEquiv_δ_comp, hφ, Equiv.apply_symm_apply]
    · rw [← uliftFunctorHomEquiv_comp_map, hφp, Equiv.apply_symm_apply]
  · intro h f hf b comm
    obtain ⟨φ, hφ, hφp⟩ := h (fun j hj ↦ uliftFunctorHomEquiv X _ (f j hj))
      ((horn.isCompatible_uliftFunctorHomEquiv_iff _).2 hf)
      (uliftFunctorHomEquiv Y _ b) fun j hj ↦ by
        rw [← uliftFunctorHomEquiv_comp_map, comm, uliftFunctorHomEquiv_δ_comp]
    refine ⟨(uliftFunctorHomEquiv X _).symm φ, fun j hj ↦ ?_, ?_⟩
    · apply (uliftFunctorHomEquiv X _).injective
      rw [uliftFunctorHomEquiv_δ_comp, Equiv.apply_symm_apply, hφ]
    · apply (uliftFunctorHomEquiv Y _).injective
      rw [uliftFunctorHomEquiv_comp_map, Equiv.apply_symm_apply, hφp]

/-- The universe lift preserves and reflects Kan fibrations. -/
theorem fibration_uliftFunctor_map_iff (p : X ⟶ Y) :
    Fibration (uliftFunctor.{v}.map p) ↔ Fibration p := by
  simp only [fibration_iff, rlp_J_iff, hasLiftingProperty_horn_ι_uliftFunctor_map_iff]

instance (p : X ⟶ Y) [Fibration p] : Fibration (uliftFunctor.{v}.map p) :=
  (fibration_uliftFunctor_map_iff p).2 inferInstance

/-- The universe lift preserves and reflects inner fibrations. -/
theorem innerFibration_uliftFunctor_map_iff (p : X ⟶ Y) :
    InnerFibration (uliftFunctor.{v}.map p) ↔ InnerFibration p := by
  simp only [innerFibration_iff, mem_innerFibrations_iff,
    hasLiftingProperty_horn_ι_uliftFunctor_map_iff]

instance (p : X ⟶ Y) [InnerFibration p] : InnerFibration (uliftFunctor.{v}.map p) :=
  (innerFibration_uliftFunctor_map_iff p).2 inferInstance

/-- The universe lift of the standard `0`-simplex is a terminal simplicial set. -/
def stdSimplex.isTerminalUliftFunctorObj₀ : IsTerminal (uliftFunctor.{v}.obj Δ[0]) :=
  IsTerminal.ofUniqueHom (fun _ ↦ SSet.const (ULift.up (stdSimplex.obj₀Equiv.symm 0)))
    fun _ _ ↦ by
      ext ⟨n⟩
      exact ULift.ext (stdSimplex.objEquiv.injective (by ext; simp))

/-- The universe lift preserves and reflects Kan complexes. -/
theorem kanComplex_uliftFunctor_obj_iff (X : SSet.{u}) :
    KanComplex (uliftFunctor.{v}.obj X) ↔ KanComplex X := by
  rw [KanComplex, KanComplex,
    isFibrant_iff_of_isTerminal (uliftFunctor.{v}.map (stdSimplex.isTerminalObj₀.from X))
      stdSimplex.isTerminalUliftFunctorObj₀, fibration_uliftFunctor_map_iff,
    ← isFibrant_iff_of_isTerminal _ stdSimplex.isTerminalObj₀]

instance (X : SSet.{u}) [KanComplex X] : KanComplex (uliftFunctor.{v}.obj X) :=
  (kanComplex_uliftFunctor_obj_iff X).2 inferInstance

/-- The universe lift preserves and reflects quasicategories. -/
theorem quasicategory_uliftFunctor_obj_iff (X : SSet.{u}) :
    Quasicategory (uliftFunctor.{v}.obj X) ↔ Quasicategory X := by
  rw [quasicategory_iff_of_isTerminal (uliftFunctor.{v}.map (stdSimplex.isTerminalObj₀.from X))
    stdSimplex.isTerminalUliftFunctorObj₀, innerFibration_uliftFunctor_map_iff,
    ← quasicategory_iff_of_isTerminal _ stdSimplex.isTerminalObj₀]

instance (X : SSet.{u}) [Quasicategory X] : Quasicategory (uliftFunctor.{v}.obj X) :=
  (quasicategory_uliftFunctor_obj_iff X).2 inferInstance

end SSet

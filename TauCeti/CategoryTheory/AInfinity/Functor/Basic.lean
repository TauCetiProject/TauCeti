/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.AInfinity.Induced
public import TauCeti.CategoryTheory.AInfinity.StrictFunctor.Basic

/-!
# A-infinity functors

An `A∞` functor `ℱ : ℬ ⟶ 𝒞` between nonunital `A∞` categories on graded linear quivers `C` and
`D` consists of a map of objects `F : C → D` and, for every composable string `X₀, …, Xₙ` of `C`
with `n ≥ 1`, a component

`fₙ : Hom(Xₙ₋₁, Xₙ) ⊗ ⋯ ⊗ Hom(X₀, X₁) ⟶ Hom(F X₀, F Xₙ)`

of degree `1 - n`, subject to the `A∞` functor equations on every composable string.

The components are stored as an `A∞` morphism from the total algebra of morphisms of `ℬ` to that of
the `A∞` category `𝒞.induced F` induced along the map of objects
(`TauCeti.AInfinityCategory.induced`), whose components are path-compatible along
`TauCeti.GradedLinearQuiver.InducedQuiver.mk`: they send a composable string of `C` to a morphism
between the images of its endpoints, and every other string to zero.  The target is the induced
category rather than `𝒞` itself because a string which is not composable in `C` can become
composable after applying `F`, and the operations of `𝒞` need not vanish on it, whereas the
operations of the induced category do.  On a string which is not composable every term of the
`A∞` morphism equation vanishes, so the `A∞` morphism equation of the total algebras amounts to the
`A∞` functor equations on composable strings.

The arity-one component gives a degree-preserving linear map `ℱ.map X Y` on each Hom module, and
it is a chain map for the differentials `m₁`.  In general it preserves the composition `m₂` only up
to the homotopy given by the arity-two component.  A strict functor is an `A∞` functor whose
components above arity one vanish (`TauCeti.AInfinityStrictFunctor.toAInfinityFunctor`); in
particular every `A∞` category has an identity `A∞` functor.

## Main definitions

* `TauCeti.AInfinityFunctor`: an `A∞` functor between nonunital `A∞` categories.
* `TauCeti.AInfinityFunctor.map`: the map of an `A∞` functor on a Hom module, its arity-one
  component.
* `TauCeti.AInfinityStrictFunctor.totalHom`: the strict morphism of total algebras of morphisms
  given by a strict functor.
* `TauCeti.AInfinityStrictFunctor.toAInfinityFunctor`: a strict functor as an `A∞` functor.
* `TauCeti.AInfinityFunctor.id`: the identity `A∞` functor.

## Main results

* `TauCeti.AInfinityFunctor.isPathCompatible_component`: every component of an `A∞` functor is
  path-compatible along its map of objects.
* `TauCeti.AInfinityFunctor.homInclusion_map`: the map on a Hom module is the linear part of the
  `A∞` morphism of total algebras.
* `TauCeti.AInfinityFunctor.map_mem`: the map on a Hom module preserves degrees.
* `TauCeti.AInfinityFunctor.map_homDifferential`: the map on a Hom module is a chain map.
* `TauCeti.AInfinityStrictFunctor.toAInfinityFunctor_map`: the map on Hom modules of a strict
  functor, as an `A∞` functor, is its map as a strict functor.

## References

* B. Keller, *Introduction to A-infinity algebras and modules*, Sections 3.4 and 7.
* V. Lyubashenko, *Category of A-infinity-categories*, Homology, Homotopy and Applications 5
  (2003), for `A∞` functors as morphisms of bar constructions over a map of objects.
-/

public section

namespace TauCeti

open GradedLinearQuiver GradedLinearQuiver.InducedQuiver

universe u₁ u₂ v₁ v₂ w

variable {R : Type w} [CommRing R] {C : Type u₁} {D : Type u₂}
  [GradedLinearQuiver.{u₁, v₁, w} R C] [GradedLinearQuiver.{u₂, v₂, w} R D]

/-- An **`A∞` functor** between nonunital `A∞` categories `ℬ` on `C` and `𝒞` on `D`: a map of
objects `obj : C → D` together with an `A∞` morphism from the total algebra of morphisms of `ℬ` to
that of the induced category `𝒞.induced obj`, whose components send a composable string of `C` to
a morphism between the images of its endpoints and every other string to zero.  Its component of
arity `n` on a composable string `X₀, …, Xₙ` is the functor component
`fₙ : Hom(Xₙ₋₁, Xₙ) ⊗ ⋯ ⊗ Hom(X₀, X₁) ⟶ Hom(obj X₀, obj Xₙ)` of degree `1 - n`. -/
structure AInfinityFunctor (ℬ : AInfinityCategory R C) (𝒞 : AInfinityCategory R D) where
  /-- The map on objects. -/
  obj : C → D
  /-- The components, as an `A∞` morphism of total algebras of morphisms into the induced
  category. -/
  toAInfinityHom : AInfinityHom ℬ.toAInfinityAlgebra (𝒞.induced obj).toAInfinityAlgebra
  /-- Every component of positive arity sends composable strings to morphisms between the images
  of their endpoints, and other strings to zero.  The component of arity zero vanishes, so it is
  path-compatible automatically (`TauCeti.AInfinityFunctor.isPathCompatible_component`). -/
  isPathCompatible_component_of_pos (n : ℕ) (hn : 0 < n) :
    IsPathCompatible (InducedQuiver.mk (F := obj)) (toAInfinityHom.component n)

namespace AInfinityHom

variable {ℬ : AInfinityCategory R C} {𝒞 : AInfinityCategory R D}
  (f : AInfinityHom ℬ.toAInfinityAlgebra 𝒞.toAInfinityAlgebra)

/-- On words of length `n`, the Taylor map of an `A∞` morphism of total algebras of morphisms is its
component `fₙ` after the Koszul twists of the suspension. -/
private theorem taylor_compMultilinearMap (n : ℕ) (hn : 0 < n) :
    (f.taylor ∘ₗ ReducedTensorWords.of R _ ⟨n, hn⟩).compMultilinearMap
        (PiTensorProduct.tprod R (s := fun _ : Fin n ↦ TotalHom R C)) =
      (f.component n).compLinearMap fun i ↦ (totalGrading R C).koszulTwist ((n : ℤ) - 1 - i) := by
  refine MultilinearMap.ext fun x ↦ ?_
  rw [LinearMap.compMultilinearMap_apply, LinearMap.comp_apply, MultilinearMap.compLinearMap_apply,
    f.component_apply n hn, ℬ.grading_eq]
  simp only [InternalGrading.koszulTwist_koszulTwist]

/-- In positive arity `n`, the component `fₙ` of an `A∞` morphism of total algebras of morphisms
is its Taylor map on words of length `n` after the Koszul twists of the suspension. -/
private theorem component_eq_compLinearMap (n : ℕ) (hn : 0 < n) :
    f.component n = ((f.taylor ∘ₗ ReducedTensorWords.of R _ ⟨n, hn⟩).compMultilinearMap
        (PiTensorProduct.tprod R (s := fun _ : Fin n ↦ TotalHom R C))).compLinearMap
      fun i ↦ (totalGrading R C).koszulTwist ((n : ℤ) - 1 - i) := by
  refine MultilinearMap.ext fun x ↦ ?_
  rw [f.component_apply n hn, ℬ.grading_eq]
  rfl

/-- **Path compatibility of the components of an `A∞` morphism is path compatibility of its Taylor
map on words.** -/
theorem isWordPathCompatible_taylor_iff {φ : C → D} :
    IsWordPathCompatible φ f.taylor ↔ ∀ n, 0 < n → IsPathCompatible φ (f.component n) := by
  rw [isWordPathCompatible_iff]
  refine ⟨fun h n hn ↦ ?_, fun h n hn ↦ ?_⟩
  · rw [f.component_eq_compLinearMap n hn]
    exact (h n hn).compLinearMap_koszulTwist _
  · rw [f.taylor_compMultilinearMap n hn]
    exact (h n hn).compLinearMap_koszulTwist _

end AInfinityHom

namespace AInfinityFunctor

variable {ℬ : AInfinityCategory R C} {𝒞 : AInfinityCategory R D}

/-- `A∞` functors are determined by their object maps and their `A∞` morphisms of total algebras.
The heterogeneous equality accounts for the target, which depends on the object map. -/
@[ext]
theorem ext {ℱ 𝒢 : AInfinityFunctor ℬ 𝒞} (hobj : ℱ.obj = 𝒢.obj)
    (h : HEq ℱ.toAInfinityHom 𝒢.toAInfinityHom) : ℱ = 𝒢 := by
  cases ℱ
  cases 𝒢
  cases hobj
  cases h
  rfl

variable (ℱ : AInfinityFunctor ℬ 𝒞)

/-- Every component of an `A∞` functor sends composable strings to morphisms between the images of
their endpoints, and other strings to zero. -/
theorem isPathCompatible_component (n : ℕ) :
    IsPathCompatible (InducedQuiver.mk (F := ℱ.obj)) (ℱ.toAInfinityHom.component n) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [AInfinityHom.component_zero]
    exact ⟨fun _ _ ↦ zero_mem _, fun _ _ _ _ _ _ _ ↦ rfl⟩
  · exact ℱ.isPathCompatible_component_of_pos n hn

/-- The Taylor map of an `A∞` functor sends composable words from `X` to `Y` to morphisms from
`⟨X⟩` to `⟨Y⟩` in the induced category, and non-composable words to zero. -/
theorem isWordPathCompatible_taylor :
    IsWordPathCompatible (InducedQuiver.mk (F := ℱ.obj)) ℱ.toAInfinityHom.taylor :=
  ℱ.toAInfinityHom.isWordPathCompatible_taylor_iff.2 fun n _ ↦ ℱ.isPathCompatible_component n

/-! ### The map on Hom modules -/

/-- The linear part of an `A∞` functor sends a morphism `X ⟶ Y` to a morphism between the images
of `X` and `Y`. -/
private theorem linearPart_homInclusion_mem_range (X Y : C) (f : homModule (R := R) X Y) :
    ℱ.toAInfinityHom.linearPart (homInclusion X Y f) ∈
      LinearMap.range (homInclusion (R := R) (C := InducedQuiver D ℱ.obj) ⟨X⟩ ⟨Y⟩) := by
  have h := (ℱ.isPathCompatible_component 1).mem_range_homInclusion ![X, Y]
    (Fin.cases (motive := fun i ↦ homModule (R := R) (![X, Y] i.rev.castSucc) (![X, Y] i.rev.succ))
      f fun i ↦ i.elim0)
  rw [AInfinityHom.component_one, MultilinearMap.ofSubsingleton_apply_apply] at h
  -- The single input of the string `![X, Y]` is the morphism `f : X ⟶ Y`, by computation on
  -- `Fin 2`.
  exact h

/-- The **map of an `A∞` functor on the Hom module** `X ⟶ Y`: the component between the images of
`X` and `Y` of its linear part, that is, its arity-one component `f₁`. -/
noncomputable def map (X Y : C) :
    homModule (R := R) X Y →ₗ[R] homModule (R := R) (ℱ.obj X) (ℱ.obj Y) :=
  homProjection (R := R) (C := InducedQuiver D ℱ.obj) ⟨X⟩ ⟨Y⟩ ∘ₗ ℱ.toAInfinityHom.linearPart ∘ₗ
    homInclusion X Y

/-- The map on a Hom module is the component of the linear part between the images of the
objects. -/
theorem map_apply (X Y : C) (f : homModule (R := R) X Y) :
    ℱ.map X Y f = homProjection (R := R) (C := InducedQuiver D ℱ.obj) ⟨X⟩ ⟨Y⟩
      (ℱ.toAInfinityHom.linearPart (homInclusion X Y f)) :=
  (rfl)

/-- **The map on a Hom module is the linear part.**  Including the image of a morphism into the
total module of the induced category gives the linear part of the included morphism. -/
@[simp]
theorem homInclusion_map (X Y : C) (f : homModule (R := R) X Y) :
    homInclusion (R := R) (C := InducedQuiver D ℱ.obj) ⟨X⟩ ⟨Y⟩ (ℱ.map X Y f) =
      ℱ.toAInfinityHom.linearPart (homInclusion X Y f) :=
  homInclusion_homProjection_of_mem_range (ℱ.linearPart_homInclusion_mem_range X Y f)

/-- The map of an `A∞` functor on a Hom module preserves degrees. -/
@[grind =>]
theorem map_mem (X Y : C) {p : ℤ} {f : homModule (R := R) X Y}
    (hf : f ∈ (grading (R := R) X Y).piece p) :
    ℱ.map X Y f ∈ (grading (R := R) (ℱ.obj X) (ℱ.obj Y)).piece p := by
  have h := ℱ.toAInfinityHom.linearPart_mem (p := p) (a := homInclusion X Y f)
    (by rwa [ℬ.grading_eq, homInclusion_mem_totalGrading_piece_iff])
  rwa [(𝒞.induced ℱ.obj).grading_eq, ← homInclusion_map,
    homInclusion_mem_totalGrading_piece_iff] at h

/-- The map of an `A∞` functor on a Hom module commutes with taking homogeneous components. -/
theorem map_decompose (X Y : C) (p : ℤ) (f : homModule (R := R) X Y) :
    ℱ.map X Y (DirectSum.decompose (grading (R := R) X Y).piece f p) =
      (DirectSum.decompose (grading (R := R) (ℱ.obj X) (ℱ.obj Y)).piece (ℱ.map X Y f) p :
        homModule (R := R) (ℱ.obj X) (ℱ.obj Y)) := by
  have h := LinearMap.IsHomogeneous.map_decompose (ℳ := (grading (R := R) X Y).piece)
    (𝓝 := (grading (R := R) (ℱ.obj X) (ℱ.obj Y)).piece) (r := 0)
    (LinearMap.isHomogeneous_def.mpr fun _ _ hx ↦ by simpa using ℱ.map_mem X Y hx) p f
  rwa [add_zero] at h

/-- **The map of an `A∞` functor on a Hom module is a chain map** for the differentials `m₁`: this
is the arity-one `A∞` functor equation. -/
@[simp]
theorem map_homDifferential (X Y : C) (f : homModule (R := R) X Y) :
    ℱ.map X Y (ℬ.homDifferential X Y f) =
      𝒞.homDifferential (ℱ.obj X) (ℱ.obj Y) (ℱ.map X Y f) := by
  rw [← AInfinityCategory.homDifferential_induced 𝒞 ℱ.obj ⟨X⟩ ⟨Y⟩]
  apply homInclusion_injective (C := InducedQuiver D ℱ.obj) ⟨X⟩ ⟨Y⟩
  rw [homInclusion_map, AInfinityCategory.homInclusion_homDifferential,
    AInfinityCategory.homInclusion_homDifferential, homInclusion_map,
    AInfinityAlgebra.differential_apply, AInfinityAlgebra.differential_apply,
    AInfinityHom.linearPart_m_one]

/-- The map of an `A∞` functor on a Hom module is a chain map, as an equation of linear maps. -/
theorem map_comp_homDifferential (X Y : C) :
    ℱ.map X Y ∘ₗ ℬ.homDifferential X Y = 𝒞.homDifferential (ℱ.obj X) (ℱ.obj Y) ∘ₗ ℱ.map X Y :=
  LinearMap.ext (ℱ.map_homDifferential X Y)

/-- The map of an `A∞` functor on a Hom module sends closed morphisms to closed morphisms. -/
theorem homDifferential_map_eq_zero {X Y : C} {f : homModule (R := R) X Y}
    (hf : ℬ.homDifferential X Y f = 0) :
    𝒞.homDifferential (ℱ.obj X) (ℱ.obj Y) (ℱ.map X Y f) = 0 := by
  rw [← map_homDifferential, hf, map_zero]

end AInfinityFunctor

/-! ### Strict functors as `A∞` functors -/

namespace AInfinityStrictFunctor

variable {ℬ : AInfinityCategory R C} {𝒞 : AInfinityCategory R D}
  (F : AInfinityStrictFunctor ℬ 𝒞)

/-- The underlying linear map of `TauCeti.AInfinityStrictFunctor.totalHom`: on the hom module of
`X` and `Y` it is the map of `F` followed by the inclusion of the hom module of `⟨X⟩` and `⟨Y⟩` in
the induced quiver. -/
private noncomputable def totalHomLinearMap :
    TotalHom R C →ₗ[R] TotalHom R (InducedQuiver D F.obj) :=
  letI := Classical.decEq (C × C)
  DirectSum.toModule R _ _ fun p ↦
    homInclusion (R := R) (C := InducedQuiver D F.obj) ⟨p.1⟩ ⟨p.2⟩ ∘ₗ F.map p.1 p.2

private theorem totalHomLinearMap_homInclusion (X Y : C) (f : homModule (R := R) X Y) :
    F.totalHomLinearMap (homInclusion X Y f) =
      homInclusion (R := R) (C := InducedQuiver D F.obj) ⟨X⟩ ⟨Y⟩ (F.map X Y f) := by
  classical
  rw [totalHomLinearMap, homInclusion_eq_lof]
  convert DirectSum.toModule_lof R (M := fun p : C × C ↦ homModule (R := R) p.1 p.2) (X, Y) f

/-- On a composable string, the map of total modules of a strict functor intertwines the
operations of `ℬ` with those of the induced category. -/
private theorem totalHomLinearMap_m_homInclusion {n : ℕ} (X : Fin (n + 1) → C)
    (x : ∀ i : Fin n, homModule (R := R) (X i.rev.castSucc) (X i.rev.succ)) :
    F.totalHomLinearMap (ℬ.m n fun i ↦ homInclusion _ _ (x i)) =
      (𝒞.induced F.obj).m n fun i ↦ F.totalHomLinearMap (homInclusion _ _ (x i)) := by
  simp only [totalHomLinearMap_homInclusion]
  rw [← homInclusion_homProjection_of_mem_range
      ((ℬ.isPathCompatible_m n).mem_range_homInclusion X x)]
  dsimp only [id_eq]
  rw [totalHomLinearMap_homInclusion, F.map_m,
    AInfinityCategory.induced_m_homInclusion 𝒞 F.obj (fun k ↦ ⟨X k⟩)]

/-- The **strict morphism of total algebras of morphisms** given by a strict functor `F`, from the
total algebra of `ℬ` to that of the category induced from `𝒞` along the object map of `F`: on the
hom module of `X` and `Y` it is the map of `F` on that hom module. -/
noncomputable def totalHom :
    AInfinityStrictHom ℬ.toAInfinityAlgebra (𝒞.induced F.obj).toAInfinityAlgebra where
  toLinearMap := F.totalHomLinearMap
  map_mem' {p} {a} ha := by
    rw [ℬ.grading_eq] at ha
    rw [(𝒞.induced F.obj).grading_eq]
    refine totalGrading_piece_induction (P := fun a ↦ F.totalHomLinearMap a ∈ _) ?_ ?_ ?_ ha
    · simp
    · intro x y hx hy
      simpa using add_mem hx hy
    · intro X Y f hf
      rw [totalHomLinearMap_homInclusion, homInclusion_mem_totalGrading_piece_iff]
      exact F.map_mem X Y hf
  map_m' n := by
    rcases n with _ | n
    · rw [ℬ.m_zero, (𝒞.induced F.obj).m_zero, LinearMap.compMultilinearMap_zero,
        MultilinearMap.zero_compLinearMap]
    refine MultilinearMap.ext fun y ↦ sub_eq_zero.1 <| (Submodule.mem_bot R).1 <|
      multilinearMap_apply_mem
        (f := F.totalHomLinearMap.compMultilinearMap (ℬ.m (n + 1)) -
          ((𝒞.induced F.obj).m (n + 1)).compLinearMap fun _ ↦ F.totalHomLinearMap)
        (fun X x ↦ ?_) (fun s t x i j hij hne ↦ ?_) y
    · rw [Submodule.mem_bot, sub_apply, LinearMap.compMultilinearMap_apply,
        MultilinearMap.compLinearMap_apply, sub_eq_zero]
      exact F.totalHomLinearMap_m_homInclusion X x
    · have hne' : (⟨t j⟩ : InducedQuiver D F.obj) ≠ ⟨s i⟩ := fun e ↦
        hne (congrArg InducedQuiver.obj e)
      simp only [sub_apply, LinearMap.compMultilinearMap_apply,
        MultilinearMap.compLinearMap_apply, totalHomLinearMap_homInclusion,
        (ℬ.isPathCompatible_m (n + 1)).eq_zero_of_ne s t x i j hij hne, map_zero,
        ((𝒞.induced F.obj).isPathCompatible_m (n + 1)).eq_zero_of_ne (fun k ↦ ⟨s k⟩)
          (fun k ↦ ⟨t k⟩) (fun k ↦ F.map _ _ (x k)) i j hij hne', sub_zero]

/-- The strict morphism of total algebras of a strict functor sends a morphism `X ⟶ Y` to its
image under the functor, between `⟨X⟩` and `⟨Y⟩` in the induced quiver. -/
@[simp]
theorem totalHom_homInclusion (X Y : C) (f : homModule (R := R) X Y) :
    F.totalHom (homInclusion X Y f) =
      homInclusion (R := R) (C := InducedQuiver D F.obj) ⟨X⟩ ⟨Y⟩ (F.map X Y f) :=
  F.totalHomLinearMap_homInclusion X Y f

/-- A **strict functor as an `A∞` functor**: its `A∞` morphism of total algebras is the strict
morphism `TauCeti.AInfinityStrictFunctor.totalHom`, so its components above arity one vanish. -/
-- Expose the object map so the types of the characteristic Hom-map equations reduce.
@[expose]
noncomputable def toAInfinityFunctor : AInfinityFunctor ℬ 𝒞 where
  obj := F.obj
  toAInfinityHom := F.totalHom.toAInfinityHom
  isPathCompatible_component_of_pos n hn := by
    rcases eq_or_ne n 1 with rfl | h₁
    · refine ⟨fun X x ↦ ?_, fun s t x i j hij hne ↦ by omega⟩
      rw [AInfinityHom.component_one, MultilinearMap.ofSubsingleton_apply_apply,
        AInfinityStrictHom.linearPart_toAInfinityHom, AInfinityStrictHom.coe_toLinearMap,
        totalHom_homInclusion]
      -- The endpoints of the single morphism are `X 0` and `X (Fin.last 1)` by computation on
      -- `Fin 2`.
      exact LinearMap.mem_range_self _ _
    · rw [AInfinityStrictHom.component_toAInfinityHom_eq_zero _ h₁]
      exact ⟨fun _ _ ↦ zero_mem _, fun _ _ _ _ _ _ _ ↦ rfl⟩

@[simp]
theorem toAInfinityFunctor_obj (X : C) : F.toAInfinityFunctor.obj X = F.obj X := (rfl)

@[simp]
theorem toAInfinityFunctor_toAInfinityHom :
    F.toAInfinityFunctor.toAInfinityHom = F.totalHom.toAInfinityHom := (rfl)

/-- The map on Hom modules of a strict functor, regarded as an `A∞` functor, is its map as a
strict functor. -/
@[simp]
theorem toAInfinityFunctor_map (X Y : C) : F.toAInfinityFunctor.map X Y = F.map X Y := by
  ext f
  apply homInclusion_injective (C := InducedQuiver D F.obj) ⟨X⟩ ⟨Y⟩
  -- The linear part of the `A∞` functor is that of the strict morphism of total algebras.
  exact (F.toAInfinityFunctor.homInclusion_map X Y f).trans <|
    (LinearMap.congr_fun F.totalHom.linearPart_toAInfinityHom _).trans
      (F.totalHom_homInclusion X Y f)

end AInfinityStrictFunctor

namespace AInfinityFunctor

/-- The **identity `A∞` functor** of an `A∞` category: the identity strict functor, whose
components above arity one vanish. -/
-- As for strict functors, the object map determines the types of the Hom-map equations.
@[expose]
protected noncomputable def id (𝒞 : AInfinityCategory R C) : AInfinityFunctor 𝒞 𝒞 :=
  (AInfinityStrictFunctor.id 𝒞).toAInfinityFunctor

@[simp]
theorem id_obj (𝒞 : AInfinityCategory R C) (X : C) : (AInfinityFunctor.id 𝒞).obj X = X := (rfl)

/-- The `A∞` morphism of total algebras of the identity `A∞` functor is the strict morphism of the
identity strict functor, so its components above arity one vanish. -/
@[simp]
theorem id_toAInfinityHom (𝒞 : AInfinityCategory R C) :
    (AInfinityFunctor.id 𝒞).toAInfinityHom =
      (AInfinityStrictFunctor.id 𝒞).totalHom.toAInfinityHom := (rfl)

-- Not `@[simp]`: the codomain of `LinearMap.id` here is only definitionally its domain, so
-- rewriting with this leaves terms `LinearMap.id f` that `LinearMap.id_apply` cannot simplify.
-- The pointwise form `TauCeti.AInfinityFunctor.id_map_apply` is the simp lemma instead.
theorem id_map (𝒞 : AInfinityCategory R C) (X Y : C) :
    (AInfinityFunctor.id 𝒞).map X Y = LinearMap.id :=
  (AInfinityStrictFunctor.id 𝒞).toAInfinityFunctor_map X Y

/-- The identity `A∞` functor fixes every morphism.  Unlike `TauCeti.AInfinityFunctor.id_map`,
this can be used to rewrite where the codomain of `LinearMap.id` is only definitionally its
domain. -/
@[simp]
theorem id_map_apply (𝒞 : AInfinityCategory R C) {X Y : C} (f : homModule (R := R) X Y) :
    (AInfinityFunctor.id 𝒞).map X Y f = f :=
  LinearMap.congr_fun (id_map 𝒞 X Y) f

end AInfinityFunctor

end TauCeti

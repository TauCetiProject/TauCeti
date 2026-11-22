/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.CategoryTheory.Linear.LinearFunctor
public import Mathlib.CategoryTheory.Subobject.Lattice
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import TauCeti.Algebra.Category.ModuleCat.Biproducts
public import TauCeti.Algebra.Category.ModuleCat.Kernels

/-!
# The representing object of a fibre functor on the hull of an object

Let `ω : C ⥤ ModuleCat K` be an exact faithful functor from an abelian category to vector spaces
over a field `K`; for the representability statements below, `C` and `ω` are also `K`-linear.
For an object `T` with finite-dimensional fibre and an element `t : ω T`,
`CategoryTheory.Functor.fiberSpan ω t` is the smallest subobject of `T` whose fibre contains `t`
(`CategoryTheory.Functor.fiberSpan_le_iff`). Write `P` for it and `p : ω P` for the element
mapping to `t`. Evaluation at `p`, `f ↦ ω f p`, is injective on `P ⟶ Y` for every `Y`, and the
objects `Y` on which it is also surjective are closed under subobjects, quotients and finite
direct sums.

For an object `X` with finite-dimensional fibre, take for `T` the power `X ^ n` with
`n = dim ω X`, and for `t` the point whose components form a basis of `ω X`. The resulting
subobject `CategoryTheory.Functor.hullRepresenting ω X` of `X ^ n` represents `ω` on every
quotient of a subobject of a finite direct sum of copies of `X`: for such `Y`, evaluation at `p`
is a linear bijection `(P ⟶ Y) → ω Y`
(`CategoryTheory.Functor.bijective_fiberSpanEval_hullBasisPoint`), natural in `Y`
(`CategoryTheory.Functor.map_fiberSpanEval`). In particular `ω P` is identified with the
endomorphisms of `P`. Moreover `P` is projective relative to these objects and every one of them
is a quotient of a finite direct sum of copies of `P`
(`CategoryTheory.Functor.exists_epi_biproduct_hullRepresenting`). This is the representing
object `P_X` of the fibre functor restricted to the hull `⟨X⟩` of subquotients of finite direct
sums of `X`, through which `⟨X⟩` is identified with finite-dimensional modules over the algebra
of endomorphisms of the restricted fibre functor.

## Main definitions and results

* `CategoryTheory.Functor.fiberSpan`, `CategoryTheory.Functor.fiberSpanPoint`: the smallest
  subobject whose fibre contains a given element, and the element of its fibre over it.
* `CategoryTheory.Functor.fiberSpan_le_iff`: its universal property.
* `CategoryTheory.Functor.map_fiberSpanPoint_eq_zero_iff`: evaluation at `fiberSpanPoint` is
  injective on morphisms out of `fiberSpan`, and
  `CategoryTheory.Functor.exists_comp_eq_of_map_fiberSpanPoint_mem` factors such a morphism
  through a monomorphism containing its value.
* `CategoryTheory.Functor.surjective_map_fiberSpanPoint_of_mono`, `…_of_epi`, `…_biproduct`:
  the objects on which evaluation is surjective are closed under subobjects, quotients and
  finite direct sums.
* `CategoryTheory.Functor.exists_comp_eq_of_epi`,
  `CategoryTheory.Functor.exists_epi_biproduct_fiberSpan`: relative projectivity of
  `fiberSpan`, and the objects it generates.
* `CategoryTheory.Functor.fiberSpanEval`: evaluation as a linear map, natural in the target.
* `CategoryTheory.Functor.hullBasisPoint`, `CategoryTheory.Functor.hullRepresenting`: the
  basis point of `ω (X ^ n)` and the representing subobject `P_X`.
* `CategoryTheory.Functor.bijective_fiberSpanEval_hullBasisPoint`: representability on
  quotients of subobjects of finite powers of `X`, and
  `CategoryTheory.Functor.exists_epi_biproduct_hullRepresenting`: `P_X` generates them.

## References

* P. Deligne, J. S. Milne, *Tannakian categories*, Lemma 2.13 and its proof.
-/

public section

namespace CategoryTheory.Functor

open Limits

universe w v u

variable {C : Type u} [Category.{v} C] {K : Type w} [Field K]

section FiberSpan

variable (ω : C ⥤ ModuleCat.{w} K) {T : C}

/-- The subobjects of `T` whose fibre contains `t`. -/
private def fiberSpanCandidates (t : ω.obj T) : Set (Subobject T) :=
  {Z | t ∈ LinearMap.range (ω.map Z.arrow).hom}

private lemma top_mem_fiberSpanCandidates (t : ω.obj T) : ⊤ ∈ fiberSpanCandidates ω t :=
  (ModuleCat.epi_iff_surjective _).1 inferInstance t

/-- The smallest subobject of `T` whose fibre contains `t`, chosen as a subobject of minimal
fibre dimension among those whose fibre contains `t`. When `C` is abelian, `ω` is faithful and
left exact and `ω T` is finite-dimensional, it is the least such subobject
(`CategoryTheory.Functor.fiberSpan_le_iff`). -/
noncomputable def fiberSpan (t : ω.obj T) : Subobject T :=
  Function.argminOn (fun Z : Subobject T ↦ Module.finrank K (ω.obj Z)) (fiberSpanCandidates ω t)
    ⟨⊤, top_mem_fiberSpanCandidates ω t⟩

/-- The fibre of `fiberSpan t` contains `t`. -/
theorem mem_range_map_fiberSpan_arrow (t : ω.obj T) :
    t ∈ LinearMap.range (ω.map (ω.fiberSpan t).arrow).hom :=
  (Function.argminOn_mem _ (fiberSpanCandidates ω t) _ :
    ω.fiberSpan t ∈ fiberSpanCandidates ω t)

/-- The element of the fibre of `fiberSpan t` lying over `t`. -/
noncomputable def fiberSpanPoint (t : ω.obj T) : ω.obj (ω.fiberSpan t) :=
  (ω.mem_range_map_fiberSpan_arrow t).choose

@[simp]
theorem map_arrow_fiberSpanPoint (t : ω.obj T) :
    (ω.map (ω.fiberSpan t).arrow).hom (ω.fiberSpanPoint t) = t :=
  (ω.mem_range_map_fiberSpan_arrow t).choose_spec

/-- Minimality of the fibre dimension of `fiberSpan t`. -/
private lemma finrank_fiberSpan_le (t : ω.obj T) {Z : C} (m : Z ⟶ T) [Mono m]
    (h : t ∈ LinearMap.range (ω.map m).hom) :
    Module.finrank K (ω.obj (ω.fiberSpan t)) ≤ Module.finrank K (ω.obj Z) := by
  have hmem : Subobject.mk m ∈ fiberSpanCandidates ω t := by
    obtain ⟨z, rfl⟩ := h
    exact ⟨(ω.map (Subobject.underlyingIso m).inv).hom z, by
      rw [← ModuleCat.comp_apply, ← ω.map_comp, Subobject.underlyingIso_arrow]⟩
  exact (Function.argminOn_le (fun Z : Subobject T ↦ Module.finrank K (ω.obj Z)) _ hmem).trans_eq
    (ω.mapIso (Subobject.underlyingIso m)).toLinearEquiv.finrank_eq

instance finiteDimensional_fiberSpan [ω.PreservesMonomorphisms] [FiniteDimensional K (ω.obj T)]
    (t : ω.obj T) : FiniteDimensional K (ω.obj (ω.fiberSpan t)) :=
  Module.Finite.of_injective (ω.map (ω.fiberSpan t).arrow).hom
    ((ModuleCat.mono_iff_injective _).1 inferInstance)

section Exact

variable [Abelian C] [ω.Faithful] [PreservesFiniteLimits ω] [FiniteDimensional K (ω.obj T)]
  {t : ω.obj T}

/-- A morphism out of `fiberSpan t` vanishes as soon as its value at `fiberSpanPoint t` does. -/
@[simp]
theorem map_fiberSpanPoint_eq_zero_iff {Y : C} (f : (ω.fiberSpan t : C) ⟶ Y) :
    (ω.map f).hom (ω.fiberSpanPoint t) = 0 ↔ f = 0 := by
  refine ⟨fun hf ↦ ?_, fun hf ↦ by simp [hf]⟩
  obtain ⟨k, hk⟩ := exists_map_kernel_ι_eq ω f _ hf
  have hle := finrank_fiberSpan_le ω t (kernel.ι f ≫ (ω.fiberSpan t).arrow)
    ⟨k, by rw [ω.map_comp, ModuleCat.comp_apply, hk, map_arrow_fiberSpanPoint]⟩
  have hinj : Function.Injective (ω.map (kernel.ι f)).hom :=
    (ModuleCat.mono_iff_injective _).1 inferInstance
  have : FiniteDimensional K (ω.obj (Limits.kernel f)) := Module.Finite.of_injective _ hinj
  have hsurj := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (le_antisymm (LinearMap.finrank_le_finrank_of_injective hinj) hle)).1 hinj
  refine ω.map_injective (ModuleCat.hom_ext (LinearMap.ext fun x ↦ ?_))
  obtain ⟨y, rfl⟩ := hsurj x
  rw [← ModuleCat.comp_apply, ← ω.map_comp, kernel.condition]
  simp

/-- Two morphisms out of `fiberSpan t` agree as soon as their values at `fiberSpanPoint t` do. -/
theorem injective_map_fiberSpanPoint (Y : C) :
    Function.Injective
      fun f : (ω.fiberSpan t : C) ⟶ Y ↦ (ω.map f).hom (ω.fiberSpanPoint t) := by
  have := ω.additive_of_preserves_binary_products
  exact fun f g h ↦ sub_eq_zero.1 <| (ω.map_fiberSpanPoint_eq_zero_iff _).1 <| by
    simpa [sub_eq_zero] using h

/-- A morphism out of `fiberSpan t` whose value at `fiberSpanPoint t` lies in the fibre of a
monomorphism `w` factors through `w`. -/
theorem exists_comp_eq_of_map_fiberSpanPoint_mem {W Y : C} (w : W ⟶ Y) [Mono w]
    (g : (ω.fiberSpan t : C) ⟶ Y)
    (h : (ω.map g).hom (ω.fiberSpanPoint t) ∈ LinearMap.range (ω.map w).hom) :
    ∃ g' : (ω.fiberSpan t : C) ⟶ W, g' ≫ w = g := by
  have hc : g ≫ cokernel.π w = 0 := by
    rw [← map_fiberSpanPoint_eq_zero_iff]
    obtain ⟨x, hx⟩ := h
    rw [ω.map_comp, ModuleCat.comp_apply, ← hx, ← ModuleCat.comp_apply, ← ω.map_comp,
      cokernel.condition]
    simp
  exact ⟨Abelian.monoLift w g hc, Abelian.monoLift_comp w g hc⟩

/-- `fiberSpan t` is the least subobject of `T` whose fibre contains `t`. -/
theorem fiberSpan_le_iff (W : Subobject T) :
    ω.fiberSpan t ≤ W ↔ t ∈ LinearMap.range (ω.map W.arrow).hom := by
  refine ⟨fun h ↦ ⟨(ω.map (Subobject.ofLE _ _ h)).hom (ω.fiberSpanPoint t), ?_⟩,
    fun h ↦ ?_⟩
  · rw [← ModuleCat.comp_apply, ← ω.map_comp, Subobject.ofLE_arrow, map_arrow_fiberSpanPoint]
  · obtain ⟨g', hg'⟩ := ω.exists_comp_eq_of_map_fiberSpanPoint_mem W.arrow
      (ω.fiberSpan t).arrow (by rwa [map_arrow_fiberSpanPoint])
    exact Subobject.le_of_comm g' hg'

/-- If evaluation at `fiberSpanPoint t` is surjective onto `ω Y`, it is surjective onto the fibre
of every subobject of `Y`. -/
theorem surjective_map_fiberSpanPoint_of_mono {Z Y : C} (i : Z ⟶ Y) [Mono i]
    (h : Function.Surjective
      fun f : (ω.fiberSpan t : C) ⟶ Y ↦ (ω.map f).hom (ω.fiberSpanPoint t)) :
    Function.Surjective
      fun f : (ω.fiberSpan t : C) ⟶ Z ↦ (ω.map f).hom (ω.fiberSpanPoint t) := by
  intro z
  obtain ⟨g, hg⟩ := h ((ω.map i).hom z)
  obtain ⟨g', rfl⟩ := ω.exists_comp_eq_of_map_fiberSpanPoint_mem i g ⟨z, hg.symm⟩
  refine ⟨g', (ModuleCat.mono_iff_injective (ω.map i)).1 inferInstance ?_⟩
  rw [← ModuleCat.comp_apply, ← ω.map_comp]
  exact hg

end Exact

/-- If evaluation at `fiberSpanPoint t` is surjective onto the fibre of `Z`, it is surjective
onto the fibre of every quotient of `Z`. -/
theorem surjective_map_fiberSpanPoint_of_epi [ω.PreservesEpimorphisms] {t : ω.obj T} {Z Y : C}
    (e : Z ⟶ Y) [Epi e]
    (h : Function.Surjective
      fun f : (ω.fiberSpan t : C) ⟶ Z ↦ (ω.map f).hom (ω.fiberSpanPoint t)) :
    Function.Surjective
      fun f : (ω.fiberSpan t : C) ⟶ Y ↦ (ω.map f).hom (ω.fiberSpanPoint t) := by
  intro y
  obtain ⟨z, rfl⟩ := (ModuleCat.epi_iff_surjective (ω.map e)).1 inferInstance y
  obtain ⟨g, rfl⟩ := h z
  exact ⟨g ≫ e, by simp⟩

/-- Evaluation at `fiberSpanPoint t` is surjective onto `ω Y` whenever every element of `ω Y` is
the value at `t` of a morphism `T ⟶ Y`. -/
theorem surjective_map_fiberSpanPoint_of_surjective {t : ω.obj T} {Y : C}
    (h : Function.Surjective fun g : T ⟶ Y ↦ (ω.map g).hom t) :
    Function.Surjective
      fun f : (ω.fiberSpan t : C) ⟶ Y ↦ (ω.map f).hom (ω.fiberSpanPoint t) := by
  intro y
  obtain ⟨g, rfl⟩ := h y
  exact ⟨(ω.fiberSpan t).arrow ≫ g, by simp⟩

end FiberSpan

section Biproduct

variable [Preadditive C] (ω : C ⥤ ModuleCat.{w} K) [ω.Additive]

/-- If evaluation at `fiberSpanPoint t` is surjective onto the fibre of each member of a finite
family, it is surjective onto the fibre of its biproduct. -/
theorem surjective_map_fiberSpanPoint_biproduct {T : C} {t : ω.obj T} {ι : Type*} [Finite ι]
    (F : ι → C) [HasBiproduct F]
    (h : ∀ j, Function.Surjective
      fun f : (ω.fiberSpan t : C) ⟶ F j ↦ (ω.map f).hom (ω.fiberSpanPoint t)) :
    Function.Surjective
      fun f : (ω.fiberSpan t : C) ⟶ ⨁ F ↦ (ω.map f).hom (ω.fiberSpanPoint t) := by
  have := Fintype.ofFinite ι
  intro v
  choose g hg using fun j ↦ h j ((ω.map (biproduct.π F j)).hom v)
  refine ⟨∑ j, g j ≫ biproduct.ι F j, ?_⟩
  conv_rhs => rw [← sum_map_ι_map_π_apply ω F v]
  beta_reduce at hg
  simp [ω.map_sum, hg]

end Biproduct

section Generator

variable (ω : C ⥤ ModuleCat.{w} K) {T : C} {t : ω.obj T}

/-- An object with finite-dimensional fibre onto which evaluation at `fiberSpanPoint t` is
surjective is a quotient of a finite direct sum of copies of `fiberSpan t`. -/
theorem exists_epi_biproduct_fiberSpan [Preadditive C] [HasFiniteBiproducts C] [ω.Faithful]
    {Y : C} [FiniteDimensional K (ω.obj Y)]
    (h : Function.Surjective
      fun f : (ω.fiberSpan t : C) ⟶ Y ↦ (ω.map f).hom (ω.fiberSpanPoint t)) :
    ∃ (n : ℕ) (q : (⨁ fun _ : Fin n ↦ (ω.fiberSpan t : C)) ⟶ Y), Epi q := by
  choose f hf using h
  let b := Module.finBasis K (ω.obj Y)
  refine ⟨_, biproduct.desc fun k ↦ f (b k), ω.epi_of_epi_map ?_⟩
  rw [ModuleCat.epi_iff_surjective, ← LinearMap.range_eq_top, eq_top_iff, ← b.span_eq,
    Submodule.span_le]
  rintro _ ⟨k, rfl⟩
  exact ⟨(ω.map (biproduct.ι _ k)).hom (ω.fiberSpanPoint t), by
    rw [← ModuleCat.comp_apply, ← ω.map_comp, biproduct.ι_desc]
    exact hf (b k)⟩

/-- `fiberSpan t` is projective relative to the objects onto whose fibre evaluation at
`fiberSpanPoint t` is surjective: every morphism from it to a quotient of such an object lifts. -/
theorem exists_comp_eq_of_epi [Abelian C] [ω.Faithful] [PreservesFiniteLimits ω]
    [FiniteDimensional K (ω.obj T)] [ω.PreservesEpimorphisms] {Y Y' : C} (e : Y ⟶ Y') [Epi e]
    (h : Function.Surjective
      fun f : (ω.fiberSpan t : C) ⟶ Y ↦ (ω.map f).hom (ω.fiberSpanPoint t))
    (f : (ω.fiberSpan t : C) ⟶ Y') : ∃ g, g ≫ e = f := by
  obtain ⟨y, hy⟩ := (ModuleCat.epi_iff_surjective (ω.map e)).1 inferInstance
    ((ω.map f).hom (ω.fiberSpanPoint t))
  obtain ⟨g, rfl⟩ := h y
  exact ⟨g, ω.injective_map_fiberSpanPoint Y' (by simpa using hy)⟩

end Generator

section Linear

variable [Preadditive C] [CategoryTheory.Linear K C] (ω : C ⥤ ModuleCat.{w} K) [ω.Additive]
  [ω.Linear K] {T : C}

/-- Evaluation at `fiberSpanPoint t`, as a linear map. It is natural in the target
(`CategoryTheory.Functor.map_fiberSpanEval`). -/
noncomputable def fiberSpanEval (t : ω.obj T) (Y : C) :
    ((ω.fiberSpan t : C) ⟶ Y) →ₗ[K] ω.obj Y where
  toFun f := (ω.map f).hom (ω.fiberSpanPoint t)
  map_add' f g := by simp
  map_smul' c f := by simp

@[simp]
theorem fiberSpanEval_apply (t : ω.obj T) {Y : C} (f : (ω.fiberSpan t : C) ⟶ Y) :
    ω.fiberSpanEval t Y f = (ω.map f).hom (ω.fiberSpanPoint t) :=
  (rfl)

/-- Evaluation at `fiberSpanPoint t` is natural in the target: applying `ω.map g` to the value
of `f` gives the value of `f ≫ g`. -/
theorem map_fiberSpanEval (t : ω.obj T) {Y Y' : C} (f : (ω.fiberSpan t : C) ⟶ Y)
    (g : Y ⟶ Y') : (ω.map g).hom (ω.fiberSpanEval t Y f) = ω.fiberSpanEval t Y' (f ≫ g) := by
  simp

end Linear

section HullBasisPoint

variable [Preadditive C] [HasFiniteBiproducts C] (ω : C ⥤ ModuleCat.{w} K) (X : C)
  [FiniteDimensional K (ω.obj X)]

/-- The point of `ω (X ^ n)`, for `n = dim ω X`, whose components form the basis
`Module.finBasis` of `ω X`. -/
noncomputable def hullBasisPoint :
    ω.obj (⨁ fun _ : Fin (Module.finrank K (ω.obj X)) ↦ X) :=
  ∑ i, (ω.map (biproduct.ι _ i)).hom (Module.finBasis K (ω.obj X) i)

@[simp]
theorem map_π_hullBasisPoint [ω.Additive] (i : Fin (Module.finrank K (ω.obj X))) :
    (ω.map (biproduct.π _ i)).hom (ω.hullBasisPoint X) = Module.finBasis K (ω.obj X) i := by
  rw [hullBasisPoint, _root_.map_sum, Finset.sum_eq_single i]
  · rw [← ModuleCat.comp_apply, ← ω.map_comp, biproduct.ι_π_self]
    simp
  · intro j _ hj
    rw [← ModuleCat.comp_apply, ← ω.map_comp, biproduct.ι_π_ne _ hj]
    simp
  · simp

/-- The subobject `fiberSpan (hullBasisPoint X)` of `X ^ n`, for `n = dim ω X`. When `C` is
abelian and `ω` is faithful and exact, it is the smallest subobject of `X ^ n` whose fibre contains
`hullBasisPoint` (`CategoryTheory.Functor.fiberSpan_le_iff`); if moreover `C` and `ω` are
`K`-linear, it is the representing object `P_X` of `ω` on the subquotients of finite direct sums
of `X` (`CategoryTheory.Functor.bijective_fiberSpanEval_hullBasisPoint`). -/
noncomputable abbrev hullRepresenting :
    Subobject (⨁ fun _ : Fin (Module.finrank K (ω.obj X)) ↦ X) :=
  ω.fiberSpan (ω.hullBasisPoint X)

end HullBasisPoint

section Hull

attribute [local instance] Abelian.hasFiniteBiproducts

variable [Abelian C] (ω : C ⥤ ModuleCat.{w} K) [ω.Additive] (X : C)
  [FiniteDimensional K (ω.obj X)] [CategoryTheory.Linear K C] [ω.Linear K]

/-- Every element of `ω X` is the value at `hullBasisPoint` of a linear combination of the
projections `X ^ n ⟶ X`. -/
private lemma surjective_map_hullBasisPoint :
    Function.Surjective fun g : (⨁ fun _ : Fin (Module.finrank K (ω.obj X)) ↦ X) ⟶ X ↦
      (ω.map g).hom (ω.hullBasisPoint X) := by
  intro y
  refine ⟨∑ i, (Module.finBasis K (ω.obj X)).repr y i • biproduct.π _ i, ?_⟩
  conv_rhs => rw [← (Module.finBasis K (ω.obj X)).sum_repr y]
  simp [ω.map_sum, ω.map_smul]

variable [ω.Faithful] [PreservesFiniteLimits ω] [ω.PreservesEpimorphisms]

/-- `P_X` represents `ω` on every quotient `Y` of a subobject `Z` of a finite direct sum of
copies of `X`: evaluation at its point is a linear bijection `(P_X ⟶ Y) → ω Y`, natural in `Y`
by `CategoryTheory.Functor.map_fiberSpanEval`. -/
theorem bijective_fiberSpanEval_hullBasisPoint {ι : Type*} [Finite ι] {Z Y : C}
    (i : Z ⟶ ⨁ fun _ : ι ↦ X) [Mono i] (e : Z ⟶ Y) [Epi e] :
    Function.Bijective (ω.fiberSpanEval (ω.hullBasisPoint X) Y) := by
  refine ⟨ω.injective_map_fiberSpanPoint Y, ?_⟩
  refine ω.surjective_map_fiberSpanPoint_of_epi e
    (ω.surjective_map_fiberSpanPoint_of_mono i
      (ω.surjective_map_fiberSpanPoint_biproduct _ fun _ ↦ ?_))
  exact ω.surjective_map_fiberSpanPoint_of_surjective (ω.surjective_map_hullBasisPoint X)

/-- The fibre of `P_X` is identified with its endomorphisms by evaluation at its point. -/
theorem bijective_fiberSpanEval_hullBasisPoint_hullRepresenting :
    Function.Bijective (ω.fiberSpanEval (ω.hullBasisPoint X) (ω.hullRepresenting X)) :=
  ω.bijective_fiberSpanEval_hullBasisPoint X (ω.hullRepresenting X).arrow (𝟙 _)

/-- `P_X` generates the subquotients of finite direct sums of `X`: every quotient `Y` of a
subobject `Z` of a finite direct sum of copies of `X` is a quotient of a finite direct sum of
copies of `P_X`. -/
theorem exists_epi_biproduct_hullRepresenting {ι : Type*} [Finite ι] {Z Y : C}
    (i : Z ⟶ ⨁ fun _ : ι ↦ X) [Mono i] (e : Z ⟶ Y) [Epi e] :
    ∃ (n : ℕ) (q : (⨁ fun _ : Fin n ↦ (ω.hullRepresenting X : C)) ⟶ Y), Epi q := by
  have : FiniteDimensional K (ω.obj Z) :=
    Module.Finite.of_injective _ ((ModuleCat.mono_iff_injective (ω.map i)).1 inferInstance)
  have : FiniteDimensional K (ω.obj Y) :=
    Module.Finite.of_surjective _ ((ModuleCat.epi_iff_surjective (ω.map e)).1 inferInstance)
  exact ω.exists_epi_biproduct_fiberSpan (ω.bijective_fiberSpanEval_hullBasisPoint X i e).2

end Hull

end CategoryTheory.Functor

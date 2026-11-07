/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.Embedding.Extend
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import TauCeti.Algebra.Homology.ModuleCat.Subobject

/-!
# Extending subcomplexes along an embedding of complex shapes

Extension along an embedding `e : c ↪ c'` of complex shapes (`HomologicalComplex.extend`) sends a
monomorphism of complexes to a monomorphism, so it sends a subcomplex `S` of `K` to a subcomplex
`S.extend e` of `K.extend e`. This is how a filtration of a chain complex indexed by `ℕ` becomes a
filtration of the cochain complex indexed by `ℤ` obtained by the regrading `C^{-n} = C_n` along
`ComplexShape.embeddingDownNat`, which is the form in which the spectral sequence of a filtered
complex is set up.

## Main definitions

* `CategoryTheory.Subobject.extend S e`: the subcomplex of `K.extend e` extended from a subcomplex
  `S` of `K`.

## Main results

* `HomologicalComplex.mono_extendMap`: extension preserves degreewise monomorphisms, and so
  monomorphisms when the category has pullbacks.
* `HomologicalComplex.mem_range_extendMap_f_iff`: for complexes of modules, in the degree `e.f i`
  the range of an extended chain map is the range of the chain map in degree `i`.
* `CategoryTheory.Subobject.extend_eq_mk`, `CategoryTheory.Subobject.mk_extend`: the extension of
  a subcomplex is the subcomplex of the extended inclusion, and that of `Subobject.mk f` is
  `Subobject.mk` of the extension of `f`.
* `CategoryTheory.Subobject.extend_mono`, `CategoryTheory.Subobject.extend_bot`,
  `CategoryTheory.Subobject.extend_top`: extension of subcomplexes is monotone and preserves `⊥`
  and `⊤`.
* `CategoryTheory.Subobject.epi_extend_arrow_f`,
  `CategoryTheory.Subobject.epi_extend_arrow_f_of_notMem`: the degrees in which the inclusion of
  the extended subcomplex is an epimorphism.
* `CategoryTheory.Subobject.extend_factors`: extension is compatible with chain maps.
* `CategoryTheory.Subobject.mem_range_extend_arrow_f_iff`: for complexes of modules, in the degree
  `e.f i` the extended subcomplex consists of the elements whose image in degree `i` lies in `S`.
-/

public section

noncomputable section

open CategoryTheory Limits

variable {C : Type*} [Category* C] [HasZeroMorphisms C] [HasZeroObject C] {ι ι' : Type*}
  {c : ComplexShape ι} {c' : ComplexShape ι'} (e : c.Embedding c')

namespace HomologicalComplex

variable {K L : HomologicalComplex C c}

/-- Extension along an embedding of complex shapes preserves degreewise monomorphisms. -/
theorem mono_extendMap (φ : K ⟶ L) [∀ i, Mono (φ.f i)] : Mono (extendMap φ e) := by
  refine mono_of_mono_f _ fun i' ↦ ?_
  by_cases hi' : ∃ i, e.f i = i'
  · obtain ⟨i, hi⟩ := hi'
    rw [extendMap_f φ e hi]
    infer_instance
  · simp only [not_exists] at hi'
    exact ⟨fun g h _ ↦ (K.isZero_extend_X e i' hi').eq_of_tgt g h⟩

/-- With pullbacks, the evaluations preserve monomorphisms, so extension along an embedding of
complex shapes preserves monomorphisms of complexes. -/
instance [HasPullbacks C] (φ : K ⟶ L) [Mono φ] : Mono (extendMap φ e) :=
  have (i : ι) : Mono (φ.f i) := (eval C c i).map_mono φ
  mono_extendMap e φ

/-- Extension along an embedding of complex shapes preserves isomorphisms. -/
instance (φ : K ⟶ L) [IsIso φ] : IsIso (extendMap φ e) :=
  (e.extendFunctor C).map_isIso φ

section ModuleCat

variable {R : Type*} [Ring R] {K L : HomologicalComplex (ModuleCat R) c}

/-- For complexes of modules, in the degree `e.f i` an element lies in the range of an extended
chain map exactly when its image in degree `i` under `L.extendXIso` lies in the range of the chain
map there. -/
theorem mem_range_extendMap_f_iff (φ : K ⟶ L) {i : ι} {i' : ι'} (hi : e.f i = i')
    (x : (L.extend e).X i') :
    x ∈ LinearMap.range ((extendMap φ e).f i').hom ↔
      (L.extendXIso e hi).hom x ∈ LinearMap.range (φ.f i).hom := by
  rw [extendMap_f φ e hi]
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨(K.extendXIso e hi).hom y, by simp⟩
  · rintro ⟨y, hy⟩
    exact ⟨(K.extendXIso e hi).inv y, by simp [hy]⟩

end ModuleCat

end HomologicalComplex

namespace CategoryTheory.Subobject

variable [HasPullbacks C] {K L : HomologicalComplex C c}

/-- The subcomplex of `K.extend e` extended from a subcomplex `S` of `K`: the image of the
extension of its inclusion. -/
def extend (S : Subobject K) : Subobject (K.extend e) :=
  Subobject.mk (HomologicalComplex.extendMap S.arrow e)

/-- The extension of a subcomplex is the subcomplex of the extension of its inclusion. -/
theorem extend_eq_mk (S : Subobject K) :
    S.extend e = Subobject.mk (HomologicalComplex.extendMap S.arrow e) :=
  (rfl)

/-- The extension of the subcomplex `Subobject.mk f` is the subcomplex of the extension of `f`. -/
@[simp]
theorem mk_extend {A : HomologicalComplex C c} (f : A ⟶ K) [Mono f] :
    (Subobject.mk f).extend e = Subobject.mk (HomologicalComplex.extendMap f e) :=
  Subobject.mk_eq_mk_of_comm _ _ ((e.extendFunctor C).mapIso (Subobject.underlyingIso f)) (by
    rw [Functor.mapIso_hom, ComplexShape.Embedding.extendFunctor_map,
      ← HomologicalComplex.extendMap_comp, Subobject.underlyingIso_hom_comp_eq_mk])

/-- Extension of subcomplexes is monotone. -/
theorem extend_mono {S T : Subobject K} (h : S ≤ T) : S.extend e ≤ T.extend e :=
  Subobject.mk_le_mk_of_comm (HomologicalComplex.extendMap (Subobject.ofLE S T h) e) (by
    rw [← HomologicalComplex.extendMap_comp, Subobject.ofLE_arrow])

/-- The extension of the zero subcomplex is the zero subcomplex. -/
@[simp]
theorem extend_bot : (⊥ : Subobject K).extend e = ⊥ := by
  rw [extend_eq_mk, Subobject.mk_eq_bot_iff_zero, Subobject.bot_arrow,
    HomologicalComplex.extendMap_zero]

/-- The extension of the whole complex is the whole extended complex. -/
@[simp]
theorem extend_top : (⊤ : Subobject K).extend e = ⊤ := by
  rw [extend_eq_mk]
  exact Subobject.mk_eq_top_of_isIso _

/-- In the degree `e.f i`, the inclusion of the extended subcomplex is an epimorphism as soon as
the inclusion of `S` is one in degree `i`. In an abelian category, this says that the extended
subcomplex is everything in degree `e.f i` when `S` is everything in degree `i`. -/
theorem epi_extend_arrow_f (S : Subobject K) {i : ι} {i' : ι'} (hi : e.f i = i')
    [Epi (S.arrow.f i)] : Epi ((S.extend e).arrow.f i') := by
  rw [extend_eq_mk, ← Subobject.underlyingIso_hom_comp_eq_mk, HomologicalComplex.comp_f,
    HomologicalComplex.extendMap_f _ e hi]
  infer_instance

/-- Outside the image of the embedding, the inclusion of the extended subcomplex is an
epimorphism, because the term of `K.extend e` there is zero. -/
theorem epi_extend_arrow_f_of_notMem (S : Subobject K) {i' : ι'} (hi' : ∀ i, e.f i ≠ i') :
    Epi ((S.extend e).arrow.f i') :=
  ⟨fun g h _ ↦ (K.isZero_extend_X e i' hi').eq_of_src g h⟩

/-- If the composite of the inclusion of `S` with a chain map `φ` factors through `T`, then the
same holds for the extended subcomplexes and the extended chain map. -/
theorem extend_factors (φ : K ⟶ L) {S : Subobject K} {T : Subobject L}
    (h : T.Factors (S.arrow ≫ φ)) :
    (T.extend e).Factors ((S.extend e).arrow ≫ HomologicalComplex.extendMap φ e) := by
  rw [extend_eq_mk e S, ← Subobject.underlyingIso_hom_comp_eq_mk, Category.assoc,
    ← HomologicalComplex.extendMap_comp, ← Subobject.factorThru_arrow _ _ h,
    HomologicalComplex.extendMap_comp, extend_eq_mk e T]
  exact Subobject.factors_of_factors_right _
    ((Subobject.mk_factors_iff _ _).2 ⟨HomologicalComplex.extendMap (T.factorThru _ h) e, rfl⟩)

section ModuleCat

variable {R : Type*} [Ring R] {K : HomologicalComplex (ModuleCat R) c}

/-- For a complex of modules, in the degree `e.f i` the extended subcomplex consists of the
elements whose image under the identification `K.extendXIso` with degree `i` lies in `S`. -/
theorem mem_range_extend_arrow_f_iff (S : Subobject K) {i : ι} {i' : ι'} (hi : e.f i = i')
    (x : (K.extend e).X i') :
    x ∈ LinearMap.range ((S.extend e).arrow.f i').hom ↔
      (K.extendXIso e hi).hom x ∈ LinearMap.range (S.arrow.f i).hom := by
  rw [extend_eq_mk, Subobject.range_mk_arrow_f,
    HomologicalComplex.mem_range_extendMap_f_iff e _ hi]

end ModuleCat

end CategoryTheory.Subobject

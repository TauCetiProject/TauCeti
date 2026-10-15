/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.Embedding.Extend
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.CategoryTheory.Subobject.Lattice

/-!
# Extending subcomplexes along an embedding of complex shapes

Extension along an embedding `e : c ↪ c'` of complex shapes (`HomologicalComplex.extend`) sends a
monomorphism of complexes to a monomorphism, so it sends a subcomplex `S` of `K` to a subcomplex
`S.extend e` of `K.extend e`.  This is how a filtration of a chain complex indexed by `ℕ` becomes a
filtration of the cochain complex indexed by `ℤ` obtained along
`ComplexShape.embeddingUpIntLE`, which is the form in which the spectral sequence of a filtered
complex is set up.

## Main definitions

* `CategoryTheory.Subobject.extend S e`: the subcomplex of `K.extend e` extended from a subcomplex
  `S` of `K`.

## Main results

* `HomologicalComplex.mono_extendMap`: extension preserves monomorphisms.
* `CategoryTheory.Subobject.extend_mono`, `CategoryTheory.Subobject.extend_bot`: extension of
  subcomplexes is monotone and preserves `⊥`.
* `CategoryTheory.Subobject.epi_extend_arrow_f`,
  `CategoryTheory.Subobject.epi_extend_arrow_f_of_notMem`: the degrees in which the extended
  subcomplex is everything.
* `CategoryTheory.Subobject.extend_factors`: extension is compatible with chain maps.
-/

public section

noncomputable section

open CategoryTheory Limits

variable {C : Type*} [Category* C] [Abelian C] {ι ι' : Type*} {c : ComplexShape ι}
  {c' : ComplexShape ι'} (e : c.Embedding c')

namespace HomologicalComplex

variable {K L : HomologicalComplex C c}

/-- Extension along an embedding of complex shapes preserves monomorphisms. -/
instance mono_extendMap (φ : K ⟶ L) [Mono φ] : Mono (extendMap φ e) := by
  refine mono_of_mono_f _ fun i' ↦ ?_
  by_cases hi' : ∃ i, e.f i = i'
  · obtain ⟨i, hi⟩ := hi'
    have : Mono (φ.f i) := (eval C c i).map_mono φ
    rw [extendMap_f φ e hi]
    infer_instance
  · simp only [not_exists] at hi'
    exact ⟨fun g h _ ↦ (K.isZero_extend_X e i' hi').eq_of_tgt g h⟩

end HomologicalComplex

namespace CategoryTheory.Subobject

variable {K L : HomologicalComplex C c}

/-- The subcomplex of `K.extend e` extended from a subcomplex `S` of `K`: the image of the
extension of its inclusion. -/
def extend (S : Subobject K) : Subobject (K.extend e) :=
  Subobject.mk (HomologicalComplex.extendMap S.arrow e)

/-- The extended subcomplex is the image of the extended inclusion. -/
theorem extend_eq_mk (S : Subobject K) :
    S.extend e = Subobject.mk (HomologicalComplex.extendMap S.arrow e) :=
  (rfl)

/-- Extension of subcomplexes is monotone. -/
theorem extend_mono {S T : Subobject K} (h : S ≤ T) : S.extend e ≤ T.extend e :=
  Subobject.mk_le_mk_of_comm (HomologicalComplex.extendMap (Subobject.ofLE S T h) e) (by
    rw [← HomologicalComplex.extendMap_comp, Subobject.ofLE_arrow])

/-- The extension of the zero subcomplex is the zero subcomplex. -/
@[simp]
theorem extend_bot : (⊥ : Subobject K).extend e = ⊥ := by
  rw [extend_eq_mk, Subobject.mk_eq_bot_iff_zero, Subobject.bot_arrow,
    HomologicalComplex.extendMap_zero]

/-- In the degree `e.f i`, the extended subcomplex is everything as soon as `S` is everything in
degree `i`. -/
theorem epi_extend_arrow_f (S : Subobject K) {i : ι} {i' : ι'} (hi : e.f i = i')
    [Epi (S.arrow.f i)] : Epi ((S.extend e).arrow.f i') := by
  rw [extend_eq_mk, ← Subobject.underlyingIso_hom_comp_eq_mk, HomologicalComplex.comp_f,
    HomologicalComplex.extendMap_f _ e hi]
  infer_instance

/-- Outside the image of the embedding, the extended subcomplex is everything (the term of
`K.extend e` there is zero). -/
theorem epi_extend_arrow_f_of_notMem (S : Subobject K) {i' : ι'} (hi' : ∀ i, e.f i ≠ i') :
    Epi ((S.extend e).arrow.f i') :=
  ⟨fun g h _ ↦ (K.isZero_extend_X e i' hi').eq_of_src g h⟩

/-- If the composite of the inclusion of `S` with a chain map `φ` factors through `T`, then the
same holds for the extended subcomplexes and the extended chain map. -/
theorem extend_factors (φ : K ⟶ L) {S : Subobject K} {T : Subobject L}
    (h : T.Factors (S.arrow ≫ φ)) :
    (T.extend e).Factors ((S.extend e).arrow ≫ HomologicalComplex.extendMap φ e) := by
  rw [extend_eq_mk e S, extend_eq_mk e T, Subobject.mk_factors_iff,
    ← Subobject.underlyingIso_hom_comp_eq_mk (HomologicalComplex.extendMap S.arrow e)]
  refine ⟨(Subobject.underlyingIso (HomologicalComplex.extendMap S.arrow e)).hom ≫
    HomologicalComplex.extendMap (T.factorThru _ h) e,
    (Category.assoc _ _ _).trans ((congrArg
      (fun k ↦ (Subobject.underlyingIso (HomologicalComplex.extendMap S.arrow e)).hom ≫ k)
        ?_).trans (Category.assoc _ _ _).symm)⟩
  change _ ≫ HomologicalComplex.extendMap T.arrow e = _
  rw [← HomologicalComplex.extendMap_comp, Subobject.factorThru_arrow,
    HomologicalComplex.extendMap_comp]

end CategoryTheory.Subobject

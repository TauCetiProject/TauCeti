/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.NumberField.Completion.InfinitePlace
public import TauCeti.NumberTheory.NumberField.CMField.AdelicLattice

/-!
# Complex conjugation as a star structure on the adeles of a CM field

Let `E` be a CM field. Its complex conjugation `x ↦ conj x` is Mathlib's star structure on `E`
(`NumberField.IsCMField.starRing`, with `NumberField.IsCMField.star_eq_complexConj`). Transported
to the finite adeles `𝔸_f` and to the infinite adeles `E_∞ = ∏_w E_w` of `E`, it gives star
structures on these rings (`NumberField.IsCMField.finiteAdeleConj`,
`NumberField.IsCMField.infiniteAdeleConj`), for which the diagonal embeddings of `E` are
`E`-linear star homomorphisms. With them, the matrix groups of hermitian forms over the adeles,
such as `{g ∈ GL_n(𝔸_f) : g* g = 1}`, are the groups `Matrix.unitaryGroupOf A` of Tau Ceti's
general theory of unitary groups over a ring with involution.

Place by place, the two star structures behave differently.

* Conjugation permutes the finite places: the conjugate `conj w` of a finite place `w`
  (`NumberField.IsCMField.conjPlace`) is the unique finite place with `|conj x|_{conj w} = |x|_w`
  for `x ∈ E`. The component of `conj a` at `conj w` is the image of `a_w` under the isomorphism
  `E_w ≃ E_{conj w}` extending the conjugation of `E`
  (`NumberField.IsCMField.finiteAdeleRing_star_apply`). At a finite place split in `E / E⁺`,
  `conj w ≠ w`, so conjugation exchanges the two completions `E_w` and `E_{conj w}` rather than
  acting within one of them.
* An infinite place `w` of a CM field is its own conjugate, and the component of `conj a` at `w`
  is the complex conjugate of that of `a` once `E_w` is identified with `ℂ` through the embedding
  attached to `w` (`NumberField.IsCMField.extensionEmbedding_infiniteAdeleRing_star_apply`). As
  conjugation of `ℂ` commutes with conjugation, the same holds for the other identification of
  `E_w` with `ℂ`, through the conjugate embedding.

## Main declarations

* `NumberField.IsCMField.infiniteAdeleConj`: complex conjugation on the infinite adeles.
* `NumberField.IsCMField.instStarRingInfiniteAdeleRing`: its star structure, and with the star
  structure `NumberField.IsCMField.instStarRingFiniteAdeleRing` on the finite adeles,
  `ContinuousStar` and `StarModule E` instances.
* `NumberField.IsCMField.conjPlace`: the conjugate of a finite place, with
  `NumberField.IsCMField.valuation_conjPlace`, `NumberField.IsCMField.eq_conjPlace_iff` and
  `NumberField.IsCMField.conjPlace_conjPlace`.
* `NumberField.IsCMField.finiteAdeleRing_star_apply`: the components of the conjugate of a finite
  adele.
* `NumberField.IsCMField.extensionEmbedding_infiniteAdeleRing_star_apply`: the components of the
  conjugate of an infinite adele.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter VI, §1.
-/

public section
noncomputable section

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField
open scoped NumberField.AdeleRing ComplexConjugate

namespace NumberField.IsCMField

open TauCeti.GlobalNumberFields

variable {E : Type*} [Field E] [NumberField E] [IsCMField E]

/-- The star structure of a CM field is its complex conjugation. -/
@[simp]
theorem star_eq_complexConj (x : E) : star x = complexConj E x :=
  (rfl)

/-! ### The finite adeles -/

instance : ContinuousStar 𝔸ᶠ[E] where
  continuous_star := by
    rw [← coe_finiteAdeleConj, finiteAdeleConj_def]
    exact continuous_finiteAdeleEquiv E E _

/-- The diagonal embedding of `E` in its finite adeles commutes with conjugation. -/
instance : StarModule E 𝔸ᶠ[E] :=
  ⟨fun r a ↦ by
    rw [Algebra.smul_def, Algebra.smul_def, star_mul', ← coe_finiteAdeleConj,
      finiteAdeleConj_algebraMap, star_eq_complexConj]⟩

/-- The **conjugate** `conj w` of a finite place `w` of a CM field: its image under complex
conjugation, the unique finite place with `|conj x|_{conj w} = |x|_w` for `x ∈ E`
(`valuation_conjPlace`, `eq_conjPlace_iff`). -/
def conjPlace (w : HeightOneSpectrum (𝓞 E)) : HeightOneSpectrum (𝓞 E) :=
  equivOfRingEquiv (RingOfIntegers.mapRingEquiv (complexConj E).toRingEquiv) w

/-- The conjugate place carries the valuation of `w` along conjugation:
`|conj x|_{conj w} = |x|_w`. -/
@[simp]
theorem valuation_conjPlace (w : HeightOneSpectrum (𝓞 E)) (x : E) :
    (conjPlace w).valuation E (complexConj E x) = w.valuation E x :=
  valuation_equivOfRingEquiv_mapRingEquiv _ w x

/-- **The conjugate place is characterised by its valuation**: `w'` is the conjugate of `w`
exactly when `|conj x|_{w'} = |x|_w` for all `x ∈ E`. -/
theorem eq_conjPlace_iff {w w' : HeightOneSpectrum (𝓞 E)} :
    w' = conjPlace w ↔ ∀ x : E, w'.valuation E (complexConj E x) = w.valuation E x :=
  eq_equivOfRingEquiv_mapRingEquiv_iff _

/-- Conjugation of finite places is an involution. -/
@[simp]
theorem conjPlace_conjPlace (w : HeightOneSpectrum (𝓞 E)) : conjPlace (conjPlace w) = w :=
  (eq_conjPlace_iff.2 fun x ↦ by
    rw [← valuation_conjPlace w (complexConj E x), complexConj_apply_apply]).symm

/-- **Conjugation of finite adeles at a place.** The component at the conjugate place `conj w` of
the conjugate of a finite adele `a` is the image of the component `a_w` under the isomorphism
`E_w ≃ E_{conj w}` extending the conjugation of `E`. -/
theorem finiteAdeleRing_star_apply (a : 𝔸ᶠ[E]) (w : HeightOneSpectrum (𝓞 E)) :
    (star a) (conjPlace w) =
      adicCompletionCongr w (conjPlace w) (complexConj E).toRingEquiv (valuation_conjPlace w)
        (a w) := by
  rw [← coe_finiteAdeleConj, finiteAdeleConj_def]
  exact finiteAdeleEquiv_apply_eq_adicCompletionCongr _ _ a

/-! ### The infinite adeles -/

variable (E) in
/-- Complex conjugation on the infinite adeles of a CM field: the transport of infinite adeles
along `complexConj E`. As conjugation fixes every infinite place of `E`, it acts on each completion
`E_w` separately, by the continuous extension of the conjugation of `E`. -/
def infiniteAdeleConj : InfiniteAdeleRing E ≃+* InfiniteAdeleRing E :=
  infiniteAdeleEquiv E E (complexConj E).toRingEquiv

variable (E) in
/-- Complex conjugation on the infinite adeles is the transport along `complexConj E`. -/
theorem infiniteAdeleConj_def :
    infiniteAdeleConj E = infiniteAdeleEquiv E E (complexConj E).toRingEquiv :=
  (rfl)

/-- Complex conjugation on the infinite adeles extends that of `E`. -/
@[simp]
theorem infiniteAdeleConj_algebraMap (x : E) :
    infiniteAdeleConj E (algebraMap E (InfiniteAdeleRing E) x) =
      algebraMap E (InfiniteAdeleRing E) (complexConj E x) :=
  infiniteAdeleEquiv_algebraMap E E _ x

/-- Complex conjugation on the infinite adeles is an involution. -/
@[simp]
theorem infiniteAdeleConj_infiniteAdeleConj (a : InfiniteAdeleRing E) :
    infiniteAdeleConj E (infiniteAdeleConj E a) = a := by
  rw [infiniteAdeleConj_def, ← RingEquiv.trans_apply, infiniteAdeleEquiv_trans,
    complexConj_trans_complexConj, infiniteAdeleEquiv_refl, RingEquiv.refl_apply]

/-- Complex conjugation `infiniteAdeleConj` is a star structure on the infinite adeles of a CM
field. -/
instance instStarRingInfiniteAdeleRing : StarRing (InfiniteAdeleRing E) where
  star := infiniteAdeleConj E
  star_involutive := infiniteAdeleConj_infiniteAdeleConj
  star_mul a b := by rw [map_mul, mul_comm]
  star_add := map_add _

variable (E) in
/-- The star structure on the infinite adeles is complex conjugation `infiniteAdeleConj`. -/
theorem coe_infiniteAdeleConj : ⇑(infiniteAdeleConj E) = star :=
  (rfl)

instance : ContinuousStar (InfiniteAdeleRing E) where
  continuous_star := by
    rw [← coe_infiniteAdeleConj, infiniteAdeleConj_def]
    exact continuous_infiniteAdeleEquiv E E _

/-- The diagonal embedding of `E` in its infinite adeles commutes with conjugation. -/
instance : StarModule E (InfiniteAdeleRing E) :=
  ⟨fun r a ↦ by
    rw [Algebra.smul_def, Algebra.smul_def, star_mul', ← coe_infiniteAdeleConj,
      infiniteAdeleConj_algebraMap, star_eq_complexConj]⟩

/-- **Conjugation of infinite adeles at a place.** Read in `ℂ` through the embedding attached to
an infinite place `w`, the component at `w` of the conjugate of an infinite adele is the complex
conjugate of its component at `w`. -/
theorem extensionEmbedding_infiniteAdeleRing_star_apply (a : InfiniteAdeleRing E)
    (w : InfinitePlace E) :
    InfinitePlace.Completion.extensionEmbedding w ((star a) w) =
      conj (InfinitePlace.Completion.extensionEmbedding w (a w)) := by
  -- Both sides are continuous in `a` and agree on the dense image of `E`.
  have he : Continuous (InfinitePlace.Completion.extensionEmbedding w) :=
    (InfinitePlace.Completion.isometry_extensionEmbedding w).continuous
  have hl : Continuous fun a : InfiniteAdeleRing E ↦
      InfinitePlace.Completion.extensionEmbedding w ((star a) w) :=
    he.comp ((continuous_apply w).comp continuous_star)
  have hr : Continuous fun a : InfiniteAdeleRing E ↦
      conj (InfinitePlace.Completion.extensionEmbedding w (a w)) :=
    Complex.continuous_conj.comp (he.comp (continuous_apply w))
  refine congr_fun ((InfiniteAdeleRing.denseRange_algebraMap E).equalizer hl hr
    (funext fun x ↦ ?_)) a
  simp only [Function.comp_apply, ← algebraMap_star_comm, InfiniteAdeleRing.algebraMap_apply]
  rw [InfinitePlace.Completion.extensionEmbedding_coe,
    InfinitePlace.Completion.extensionEmbedding_coe, star_eq_complexConj]
  exact complexEmbedding_complexConj E w.embedding _

end NumberField.IsCMField

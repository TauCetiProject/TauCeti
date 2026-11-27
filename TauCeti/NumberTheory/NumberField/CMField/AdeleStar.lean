/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.CMField.Basic
public import TauCeti.NumberTheory.NumberField.FinitePlace.Transport
public import TauCeti.NumberTheory.NumberField.Global.Adeles.GaloisAction

/-!
# Complex conjugation as a star structure on the adeles of a CM field

Let `E` be a CM field. Its complex conjugation `x ↦ conj x` is Mathlib's star structure on `E`
(`NumberField.IsCMField.starRing`, with `NumberField.IsCMField.star_eq_complexConj`). Transported
to the finite adeles `𝔸_f` and to the infinite adeles `E_∞ = ∏_w E_w` of `E`, it gives star
structures on these rings (`NumberField.IsCMField.finiteAdeleConj`,
`NumberField.IsCMField.infiniteAdeleConj`), semilinear over `E`: `conj (r • a) = conj r • conj a`
for `r ∈ E`. Conjugation preserves the integral finite adeles `Ô`, which inherit the star
structure. With them, the matrix groups of hermitian forms over the adeles, such as
`{g ∈ GL_n(𝔸_f) : g* g = 1}`, are the groups `Matrix.unitaryGroupOf A` of Tau Ceti's general
theory of unitary groups over a ring with involution.

Place by place, the two star structures behave differently.

* Conjugation permutes the finite places: the conjugate `conj w` of a finite place `w`
  (`IsDedekindDomain.HeightOneSpectrum.conjPlace`) is the unique finite place with
  `|conj x|_{conj w} = |x|_w` for `x ∈ E`. The component of `conj a` at `conj w` is the image of
  `a_w` under the isomorphism `E_w ≃ E_{conj w}` extending the conjugation of `E`
  (`IsDedekindDomain.FiniteAdeleRing.star_apply_conjPlace`). At a finite place split in `E / E⁺`,
  `conj w ≠ w`, so conjugation exchanges the two completions `E_w` and `E_{conj w}` rather than
  acting within one of them.
* An infinite place `w` of a CM field is its own conjugate, and the component of `conj a` at `w`
  is the complex conjugate of that of `a` once `E_w` is identified with `ℂ` through the embedding
  attached to `w` (`NumberField.InfiniteAdeleRing.extensionEmbedding_star_apply`). As
  conjugation of `ℂ` commutes with conjugation, the same holds for the other identification of
  `E_w` with `ℂ`, through the conjugate embedding.

The finite adeles are only defined here for number fields, but the star structure on the
infinite adeles only needs `E` to be an algebraic CM field.

## Main declarations

* `NumberField.IsCMField.finiteAdeleConj`, `NumberField.IsCMField.infiniteAdeleConj`: complex
  conjugation on the finite and on the infinite adeles.
* `NumberField.IsCMField.instStarRingFiniteAdeleRing`,
  `NumberField.IsCMField.instStarRingInfiniteAdeleRing`: the star structures, with
  `ContinuousStar` and `StarModule E` instances, and
  `NumberField.IsCMField.instStarRingIntegralAdeles` on the integral finite adeles, which
  conjugation preserves (`NumberField.IsCMField.star_mem_integralAdeles_iff`).
* `IsDedekindDomain.HeightOneSpectrum.conjPlace`: the conjugate of a finite place, with
  `IsDedekindDomain.HeightOneSpectrum.valuation_conjPlace`,
  `IsDedekindDomain.HeightOneSpectrum.eq_conjPlace_iff` and
  `IsDedekindDomain.HeightOneSpectrum.conjPlace_conjPlace`.
* `IsDedekindDomain.FiniteAdeleRing.star_apply_conjPlace`: the components of the conjugate of a
  finite adele.
* `NumberField.InfiniteAdeleRing.extensionEmbedding_star_apply`: the components of the conjugate
  of an infinite adele.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter VI, §1.

## Attribution

That complex conjugation preserves `Ô` (`NumberField.IsCMField.star_mem_integralAdeles_iff`) is
`New.star_mem_Ô` in `src/Lib/Adelic/Adeles/Basic.lean` of grh-lean
(https://github.com/lsernau/grh-lean, Apache 2.0, Copyright 2026 Anthropic, PBC).
-/

public section
noncomputable section

open IsDedekindDomain NumberField NumberField.IsCMField TauCeti.GlobalNumberFields
open scoped NumberField.AdeleRing ComplexConjugate

/-! ### The conjugate of a finite place -/

namespace IsDedekindDomain.HeightOneSpectrum

variable {E : Type*} [Field E] [NumberField E] [IsCMField E]

/-- The **conjugate** `conj w` of a finite place `w` of a CM field: its image under complex
conjugation, the unique finite place with `|conj x|_{conj w} = |x|_w` for `x ∈ E`
(`valuation_conjPlace`, `eq_conjPlace_iff`). -/
def conjPlace (w : HeightOneSpectrum (𝓞 E)) : HeightOneSpectrum (𝓞 E) :=
  equivOfRingEquiv (RingOfIntegers.mapRingEquiv (complexConj E).toRingEquiv) w

/-- The conjugate place carries the valuation of `w` along conjugation:
`|conj x|_{conj w} = |x|_w`. -/
@[simp]
theorem valuation_conjPlace (w : HeightOneSpectrum (𝓞 E)) (x : E) :
    w.conjPlace.valuation E (complexConj E x) = w.valuation E x :=
  valuation_equivOfRingEquiv_mapRingEquiv _ w x

/-- **The conjugate place is characterised by its valuation**: `w'` is the conjugate of `w`
exactly when `|conj x|_{w'} = |x|_w` for all `x ∈ E`. -/
theorem eq_conjPlace_iff {w w' : HeightOneSpectrum (𝓞 E)} :
    w' = w.conjPlace ↔ ∀ x : E, w'.valuation E (complexConj E x) = w.valuation E x :=
  eq_equivOfRingEquiv_mapRingEquiv_iff _

/-- Conjugation of finite places is an involution. -/
@[simp]
theorem conjPlace_conjPlace (w : HeightOneSpectrum (𝓞 E)) : w.conjPlace.conjPlace = w :=
  (eq_conjPlace_iff.2 fun x ↦ by
    rw [← valuation_conjPlace w (complexConj E x), complexConj_apply_apply]).symm

end IsDedekindDomain.HeightOneSpectrum

/-! ### The finite adeles -/

namespace NumberField.IsCMField

section FiniteAdeleRing

variable {E : Type*} [Field E] [NumberField E] [IsCMField E]

variable (E) in
/-- Complex conjugation on the finite adeles of a CM field: the transport of finite adeles along
`complexConj E`, which sends the component at a finite place `w` to the component at `conj w`. -/
def finiteAdeleConj : 𝔸ᶠ[E] ≃+* 𝔸ᶠ[E] :=
  finiteAdeleEquiv E E (complexConj E).toRingEquiv

theorem finiteAdeleConj_def :
    finiteAdeleConj E = finiteAdeleEquiv E E (complexConj E).toRingEquiv :=
  (rfl)

/-- Complex conjugation on the finite adeles extends that of `E`. -/
@[simp]
theorem finiteAdeleConj_algebraMap (x : E) :
    finiteAdeleConj E (algebraMap E 𝔸ᶠ[E] x) = algebraMap E 𝔸ᶠ[E] (complexConj E x) :=
  finiteAdeleEquiv_algebraMap E E _ x

/-- Complex conjugation on the finite adeles is an involution. -/
@[simp]
theorem finiteAdeleConj_finiteAdeleConj (a : 𝔸ᶠ[E]) :
    finiteAdeleConj E (finiteAdeleConj E a) = a := by
  rw [finiteAdeleConj_def, ← RingEquiv.trans_apply, finiteAdeleEquiv_trans,
    complexConj_trans_complexConj, finiteAdeleEquiv_refl, RingEquiv.refl_apply]

/-- Complex conjugation `finiteAdeleConj` is a star structure on the finite adeles of a CM field. -/
instance instStarRingFiniteAdeleRing : StarRing 𝔸ᶠ[E] where
  star := finiteAdeleConj E
  star_involutive := finiteAdeleConj_finiteAdeleConj
  star_mul a b := by rw [map_mul, mul_comm]
  star_add := map_add _

variable (E) in
/-- The star structure on the finite adeles is complex conjugation `finiteAdeleConj`. -/
theorem coe_finiteAdeleConj : ⇑(finiteAdeleConj E) = star :=
  (rfl)

/-- Conjugation preserves the integral finite adeles. It takes priority over the place-by-place
unfolding `IsDedekindDomain.FiniteAdeleRing.mem_integralAdeles` as a `simp` lemma. -/
@[simp high]
theorem star_mem_integralAdeles_iff {a : 𝔸ᶠ[E]} :
    star a ∈ FiniteAdeleRing.integralAdeles (𝓞 E) E ↔
      a ∈ FiniteAdeleRing.integralAdeles (𝓞 E) E := by
  rw [← coe_finiteAdeleConj, finiteAdeleConj_def]
  exact finiteAdeleEquiv_mem_integralAdeles_iff _

/-- The integral finite adeles `Ô` of a CM field inherit the star structure of the finite adeles:
complex conjugation preserves `Ô` (`star_mem_integralAdeles_iff`). -/
instance instStarRingIntegralAdeles : StarRing (FiniteAdeleRing.integralAdeles (𝓞 E) E) where
  star a := ⟨star (a : 𝔸ᶠ[E]), star_mem_integralAdeles_iff.2 a.property⟩
  star_involutive a := Subtype.ext (star_star (a : 𝔸ᶠ[E]))
  star_mul a b := Subtype.ext (star_mul (a : 𝔸ᶠ[E]) b)
  star_add a b := Subtype.ext (star_add (a : 𝔸ᶠ[E]) b)

/-- The inclusion of the integral finite adeles in the finite adeles commutes with conjugation. -/
@[simp, norm_cast]
theorem coe_star_integralAdeles (a : FiniteAdeleRing.integralAdeles (𝓞 E) E) :
    ((star a : FiniteAdeleRing.integralAdeles (𝓞 E) E) : 𝔸ᶠ[E]) = star (a : 𝔸ᶠ[E]) :=
  (rfl)

instance : ContinuousStar 𝔸ᶠ[E] where
  continuous_star := by
    rw [← coe_finiteAdeleConj, finiteAdeleConj_def]
    exact continuous_finiteAdeleEquiv E E _

/-- Conjugation of finite adeles is semilinear over `E`: `star (r • a) = star r • star a` for
`r ∈ E` and a finite adele `a`. In particular the diagonal embedding of `E` commutes with
conjugation. -/
instance : StarModule E 𝔸ᶠ[E] :=
  ⟨fun r a ↦ by
    rw [Algebra.smul_def, Algebra.smul_def, star_mul', ← coe_finiteAdeleConj,
      finiteAdeleConj_algebraMap, star_eq_complexConj]⟩

end FiniteAdeleRing

end NumberField.IsCMField

namespace IsDedekindDomain.FiniteAdeleRing

variable {E : Type*} [Field E] [NumberField E] [IsCMField E]

/-- **Conjugation of finite adeles at a place.** The component at the conjugate place `conj w` of
the conjugate of a finite adele `a` is the image of the component `a_w` under the isomorphism
`E_w ≃ E_{conj w}` extending the conjugation of `E`. -/
theorem star_apply_conjPlace (a : 𝔸ᶠ[E]) (w : HeightOneSpectrum (𝓞 E)) :
    (star a) w.conjPlace =
      HeightOneSpectrum.adicCompletionCongr w w.conjPlace (complexConj E).toRingEquiv
        (HeightOneSpectrum.valuation_conjPlace w) (a w) := by
  rw [← coe_finiteAdeleConj, finiteAdeleConj_def]
  exact finiteAdeleEquiv_apply_eq_adicCompletionCongr _ _ a

end IsDedekindDomain.FiniteAdeleRing

/-! ### The infinite adeles -/

namespace NumberField.IsCMField

section InfiniteAdeleRing

variable {E : Type*} [Field E] [CharZero E] [Algebra.IsIntegral ℚ E] [IsCMField E]

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

/-- Conjugation of infinite adeles is semilinear over `E`: `star (r • a) = star r • star a` for
`r ∈ E` and an infinite adele `a`. In particular the diagonal embedding of `E` commutes with
conjugation. -/
instance : StarModule E (InfiniteAdeleRing E) :=
  ⟨fun r a ↦ by
    rw [Algebra.smul_def, Algebra.smul_def, star_mul', ← coe_infiniteAdeleConj,
      infiniteAdeleConj_algebraMap, star_eq_complexConj]⟩

end InfiniteAdeleRing

end NumberField.IsCMField

namespace NumberField.InfiniteAdeleRing

variable {E : Type*} [Field E] [CharZero E] [Algebra.IsIntegral ℚ E] [IsCMField E]

/-- The component at an infinite place `w` of the conjugate of an infinite adele only depends on
its component at `w`, as conjugation fixes `w`. -/
private theorem star_apply_eq_of_apply_eq {a b : InfiniteAdeleRing E} {w : InfinitePlace E}
    (h : a w = b w) : (star a) w = (star b) w := by
  rw [← coe_infiniteAdeleConj, infiniteAdeleConj_def, infiniteAdeleEquiv_apply,
    infiniteAdeleEquiv_apply]
  have key : ∀ u : InfinitePlace E, u = w → a u = b u := by rintro u rfl; exact h
  congr 1
  refine key _ (InfinitePlace.ext _ _ fun x ↦ ?_)
  rw [InfinitePlace.comap_apply]
  exact infinitePlace_complexConj E w x

/-- **Conjugation of infinite adeles at a place.** Read in `ℂ` through the embedding attached to
an infinite place `w`, the component at `w` of the conjugate of an infinite adele is the complex
conjugate of its component at `w`. -/
theorem extensionEmbedding_star_apply (a : InfiniteAdeleRing E) (w : InfinitePlace E) :
    InfinitePlace.Completion.extensionEmbedding w ((star a) w) =
      conj (InfinitePlace.Completion.extensionEmbedding w (a w)) := by
  classical
  have he : Continuous (InfinitePlace.Completion.extensionEmbedding w) :=
    (InfinitePlace.Completion.isometry_extensionEmbedding w).continuous
  -- The infinite adele with component `z` at `w` and `0` elsewhere.
  let s : w.Completion → InfiniteAdeleRing E := fun z ↦ Function.update 0 w z
  have hs : Continuous s := continuous_const.update w continuous_id
  have hsw (z : w.Completion) : s z w = z := Function.update_self w z 0
  -- Both sides, as functions of the component `z` at `w`, are continuous on the completion
  -- `E_w` and agree on its dense subfield `E`.
  have key := AbsoluteValue.Completion.ext
    (f := fun z ↦ InfinitePlace.Completion.extensionEmbedding w ((star (s z)) w))
    (g := fun z ↦ conj (InfinitePlace.Completion.extensionEmbedding w z))
    (he.comp ((continuous_apply w).comp ((continuous_star (R := InfiniteAdeleRing E)).comp hs)))
    (Complex.continuous_conj.comp he) fun x ↦ by
      rw [star_apply_eq_of_apply_eq (b := algebraMap E (InfiniteAdeleRing E) (WithAbs.ofAbs x))
          (by rw [hsw, algebraMap_apply, WithAbs.toAbs_ofAbs]),
        ← algebraMap_star_comm, algebraMap_apply, star_eq_complexConj,
        InfinitePlace.Completion.extensionEmbedding_coe,
        InfinitePlace.Completion.extensionEmbedding_coe]
      exact complexEmbedding_complexConj E w.embedding _
  rw [star_apply_eq_of_apply_eq (hsw (a w)).symm]
  exact congr_fun key (a w)

end NumberField.InfiniteAdeleRing

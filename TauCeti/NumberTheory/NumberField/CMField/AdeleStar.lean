/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Star.Subsemiring
public import TauCeti.NumberTheory.NumberField.CMField.FinitePlace
public import TauCeti.NumberTheory.NumberField.Global.Adeles.GaloisAction
public import TauCeti.RingTheory.DedekindDomain.FiniteAdeleRing.LocalUnits

/-!
# Complex conjugation as a star structure on the adeles of a CM field

Let `E` be a CM field. Its complex conjugation `x ↦ conj x` is Mathlib's star structure on `E`
(`NumberField.IsCMField.starRing`, with `NumberField.IsCMField.star_eq_complexConj`). Transported
to the finite adeles `𝔸_f` and to the infinite adeles `E_∞ = ∏_w E_w` of `E`, it gives star
structures on these rings (`NumberField.IsCMField.finiteAdeleConj`,
`NumberField.IsCMField.infiniteAdeleConj`), semilinear over `E`: `conj (r • a) = conj r • conj a`
for `r ∈ E`; `star` is the `simp` normal form of both conjugations
(`NumberField.IsCMField.finiteAdeleConj_apply`, `NumberField.IsCMField.infiniteAdeleConj_apply`),
also on the diagonal copy of `E`, where `simp` rewrites the image of `complexConj E x` to
`star (algebraMap E _ x)` (`IsDedekindDomain.FiniteAdeleRing.algebraMap_complexConj`,
`NumberField.InfiniteAdeleRing.algebraMap_complexConj`).
Conjugation preserves the integral finite adeles `Ô`, which form a star subsemiring and inherit the
star structure. With them, the matrix groups of hermitian forms over the adeles, such as
`{g ∈ GL_n(𝔸_f) : g* g = 1}`, are the groups `Matrix.unitaryGroupOf A` of Tau Ceti's general
theory of unitary groups over a ring with involution.

Place by place, the two star structures behave differently.

* Conjugation permutes the finite places: the conjugate `conj w` of a finite place `w`
  (`IsDedekindDomain.HeightOneSpectrum.conjPlace`) is the unique finite place with
  `|conj x|_{conj w} = |x|_w` for `x ∈ E`. The component of `conj a` at `conj w` is the image of
  `a_w` under the isomorphism `E_w ≃ E_{conj w}` extending the conjugation of `E`
  (`IsDedekindDomain.FiniteAdeleRing.star_apply_conjPlace`). When `conj w ≠ w`, that is when the
  place of `E⁺` below `w` splits in `E`, conjugation exchanges the two completions `E_w` and
  `E_{conj w}` rather than acting within one of them.
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
* `IsDedekindDomain.FiniteAdeleRing.finiteAdeleConj_finiteAdeleConj`,
  `NumberField.InfiniteAdeleRing.infiniteAdeleConj_infiniteAdeleConj`: the conjugations are
  involutions.
* `IsDedekindDomain.FiniteAdeleRing.star_apply_conjPlace`: the components of the conjugate of a
  finite adele.
* `IsDedekindDomain.FiniteAdeleRing.unitsProj_star_eq_one_iff`: the corresponding criterion
  for a conjugate finite idele to have component `1` at a place, via `coe_unitsProj_apply`.
* `RingEquiv.finiteAdeleEquiv_star`: transport of finite adeles along an
  isomorphism of CM fields commutes with conjugation.
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
theorem finiteAdeleConj_algebraMap (x : E) :
    finiteAdeleConj E (algebraMap E 𝔸ᶠ[E] x) = algebraMap E 𝔸ᶠ[E] (complexConj E x) :=
  finiteAdeleEquiv_algebraMap E E _ x

end FiniteAdeleRing

end NumberField.IsCMField

/-- Complex conjugation on the finite adeles of a CM field is an involution. -/
theorem IsDedekindDomain.FiniteAdeleRing.finiteAdeleConj_finiteAdeleConj {E : Type*} [Field E]
    [NumberField E] [IsCMField E] (a : 𝔸ᶠ[E]) : finiteAdeleConj E (finiteAdeleConj E a) = a := by
  rw [finiteAdeleConj_def, ← RingEquiv.trans_apply, finiteAdeleEquiv_trans,
    complexConj_trans_complexConj, finiteAdeleEquiv_refl, RingEquiv.refl_apply]

namespace NumberField.IsCMField

section FiniteAdeleRing

variable {E : Type*} [Field E] [NumberField E] [IsCMField E]

/-- Complex conjugation `finiteAdeleConj` is a star structure on the finite adeles of a CM field. -/
instance instStarRingFiniteAdeleRing : StarRing 𝔸ᶠ[E] where
  star := finiteAdeleConj E
  star_involutive := FiniteAdeleRing.finiteAdeleConj_finiteAdeleConj
  star_mul a b := by rw [map_mul, mul_comm]
  star_add := map_add _

variable (E) in
/-- The star structure on the finite adeles is complex conjugation `finiteAdeleConj`. -/
theorem coe_finiteAdeleConj : ⇑(finiteAdeleConj E) = star :=
  (rfl)

/-- Complex conjugation on the finite adeles is the star structure: `star` is the `simp` normal
form. -/
@[simp]
theorem finiteAdeleConj_apply (a : 𝔸ᶠ[E]) : finiteAdeleConj E a = star a :=
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
complex conjugation preserves `Ô` (`star_mem_integralAdeles_iff`), so `Ô` is a star subsemiring of
the finite adeles, and this is the star structure `StarSubsemiring.starRing` of that star
subsemiring. -/
instance instStarRingIntegralAdeles : StarRing (FiniteAdeleRing.integralAdeles (𝓞 E) E) :=
  inferInstanceAs <| StarRing
    ({ (FiniteAdeleRing.integralAdeles (𝓞 E) E).toSubsemiring with
        star_mem' := star_mem_integralAdeles_iff.2 } : StarSubsemiring 𝔸ᶠ[E])

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

namespace RingEquiv

variable {E E' : Type*} [Field E] [NumberField E] [IsCMField E] [Field E'] [NumberField E']
  [IsCMField E']

/-- Transport of finite adeles along an isomorphism of CM fields commutes with complex conjugation:
the isomorphism intertwines the complex conjugations of the two fields
(`NumberField.IsCMField.complexConj_algebraMap`). -/
@[simp]
theorem finiteAdeleEquiv_star (e : E ≃+* E') (a : 𝔸ᶠ[E]) :
    finiteAdeleEquiv E E' e (star a) = star (finiteAdeleEquiv E E' e a) := by
  let : Algebra E E' := e.toRingHom.toAlgebra
  have h : (complexConj E).toRingEquiv.trans e = e.trans (complexConj E').toRingEquiv :=
    RingEquiv.ext fun x ↦ (complexConj_algebraMap E E' x).symm
  rw [← finiteAdeleConj_apply, ← finiteAdeleConj_apply, finiteAdeleConj_def, finiteAdeleConj_def,
    ← RingEquiv.trans_apply, ← RingEquiv.trans_apply, finiteAdeleEquiv_trans,
    finiteAdeleEquiv_trans, h]

end RingEquiv

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

/-- **Conjugation of finite adeles at a place, for any presentation of the conjugate place.** If
`|conj x|_{w'} = |x|_w` for all `x ∈ E`, so that `w'` is the conjugate place `conj w`, the component
at `w'` of the conjugate of a finite adele `a` is the image of `a_w` under the isomorphism
`E_w ≃ E_{w'}` extending the conjugation of `E`. With `w = conj w'` this computes every component
of `star a`, and at a place `w` with `conj w = w` it reads `(star a)_w = conj (a_w)` for the
automorphism `t ↦ conj t` of `E_w`. -/
theorem star_apply_eq_adicCompletionCongr {w w' : HeightOneSpectrum (𝓞 E)}
    (hw : ∀ x, w'.valuation E ((complexConj E).toRingEquiv x) = w.valuation E x) (a : 𝔸ᶠ[E]) :
    (star a) w' =
      HeightOneSpectrum.adicCompletionCongr w w' (complexConj E).toRingEquiv hw (a w) := by
  obtain rfl := HeightOneSpectrum.eq_conjPlace_iff.2 hw
  exact star_apply_conjPlace a w

/-- A conjugate finite idele has component `1` at a place if and only if the original
idele has component `1` at the conjugate place. -/
@[simp]
theorem unitsProj_star_eq_one_iff
    {v : HeightOneSpectrum (𝓞 E)} {a : (𝔸ᶠ[E])ˣ} :
    unitsProj E v (star a) = 1 ↔ unitsProj E v.conjPlace a = 1 := by
  have h (w : HeightOneSpectrum (𝓞 E)) :
      unitsProj E w.conjPlace (star a) = 1 ↔ unitsProj E w a = 1 := by
    simp only [← Units.val_eq_one, coe_unitsProj_apply, Units.coe_star, star_apply_conjPlace,
      RingEquiv.map_eq_one_iff]
  have hv := h v.conjPlace
  rw [HeightOneSpectrum.conjPlace_conjPlace] at hv
  exact hv

/-- The diagonal embedding of a CM field in its finite adeles commutes with conjugation. As
`star_eq_complexConj` makes `complexConj E` the `simp` normal form of conjugation on `E` and
`finiteAdeleConj_apply` makes `star` the normal form on the finite adeles, this is the `simp`
lemma joining them. -/
@[simp]
theorem algebraMap_complexConj (x : E) :
    algebraMap E 𝔸ᶠ[E] (complexConj E x) = star (algebraMap E 𝔸ᶠ[E] x) := by
  rw [← finiteAdeleConj_apply, finiteAdeleConj_algebraMap]

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
theorem infiniteAdeleConj_algebraMap (x : E) :
    infiniteAdeleConj E (algebraMap E (InfiniteAdeleRing E) x) =
      algebraMap E (InfiniteAdeleRing E) (complexConj E x) :=
  infiniteAdeleEquiv_algebraMap E E _ x

end InfiniteAdeleRing

end NumberField.IsCMField

/-- Complex conjugation on the infinite adeles of an algebraic CM field is an involution. -/
theorem NumberField.InfiniteAdeleRing.infiniteAdeleConj_infiniteAdeleConj {E : Type*} [Field E]
    [CharZero E] [Algebra.IsIntegral ℚ E] [IsCMField E] (a : InfiniteAdeleRing E) :
    infiniteAdeleConj E (infiniteAdeleConj E a) = a := by
  rw [infiniteAdeleConj_def, ← RingEquiv.trans_apply, infiniteAdeleEquiv_trans,
    complexConj_trans_complexConj, infiniteAdeleEquiv_refl, RingEquiv.refl_apply]

namespace NumberField.IsCMField

section InfiniteAdeleRing

variable {E : Type*} [Field E] [CharZero E] [Algebra.IsIntegral ℚ E] [IsCMField E]

/-- Complex conjugation `infiniteAdeleConj` is a star structure on the infinite adeles of a CM
field. -/
instance instStarRingInfiniteAdeleRing : StarRing (InfiniteAdeleRing E) where
  star := infiniteAdeleConj E
  star_involutive := InfiniteAdeleRing.infiniteAdeleConj_infiniteAdeleConj
  star_mul a b := by rw [map_mul, mul_comm]
  star_add := map_add _

variable (E) in
/-- The star structure on the infinite adeles is complex conjugation `infiniteAdeleConj`. -/
theorem coe_infiniteAdeleConj : ⇑(infiniteAdeleConj E) = star :=
  (rfl)

/-- Complex conjugation on the infinite adeles is the star structure: `star` is the `simp`
normal form. -/
@[simp]
theorem infiniteAdeleConj_apply (a : InfiniteAdeleRing E) : infiniteAdeleConj E a = star a :=
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

/-- The diagonal embedding of a CM field in its infinite adeles commutes with conjugation. As
`star_eq_complexConj` makes `complexConj E` the `simp` normal form of conjugation on `E` and
`infiniteAdeleConj_apply` makes `star` the normal form on the infinite adeles, this is the `simp`
lemma joining them. -/
@[simp]
theorem algebraMap_complexConj (x : E) :
    algebraMap E (InfiniteAdeleRing E) (complexConj E x) =
      star (algebraMap E (InfiniteAdeleRing E) x) := by
  rw [← infiniteAdeleConj_apply, infiniteAdeleConj_algebraMap]

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

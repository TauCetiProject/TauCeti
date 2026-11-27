/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.NumberField.Completion.InfinitePlace
public import TauCeti.NumberTheory.NumberField.CMField.AdelicLattice
public import TauCeti.RingTheory.DedekindDomain.AdicValuation.Transport
public import TauCeti.RingTheory.DedekindDomain.FiniteAdeleRing.Place
import TauCeti.RingTheory.DedekindDomain.Ideal.Basic

/-!
# Complex conjugation as a star structure on the adeles of a CM field

Let `E` be a CM field. Its complex conjugation `x ↦ conj x` is Mathlib's star structure on `E`
(`NumberField.IsCMField.starRing`). Transported to the finite adeles `𝔸_f` and to the infinite
adeles `E_∞ = ∏_w E_w` of `E`, it gives star structures on these rings
(`NumberField.IsCMField.finiteAdeleConj`, `NumberField.IsCMField.infiniteAdeleConj`), for which
the diagonal embeddings of `E` are `E`-linear star homomorphisms. With them, the matrix groups of
hermitian forms over the adeles, such as `{g ∈ GL_n(𝔸_f) : g* g = 1}`, are the groups
`Matrix.unitaryGroupOf A` of Tau Ceti's general theory of unitary groups over a ring with
involution.

The two star structures are complex conjugation at every place.

* At a finite place `w`, conjugation carries the component at `w` to the component at the
  conjugate place `conj w`: if `w'` is a finite place with `|conj x|_{w'} = |x|_w` for `x ∈ E`
  (that is, `w' = conj w`), then `(conj a)_{w'}` is the image of `a_w` under the isomorphism
  `E_w ≃ E_{w'}` extending the conjugation of `E`
  (`NumberField.IsCMField.finiteAdeleRing_star_apply`).
* An infinite place `w` of a CM field is its own conjugate, and the component of `conj a` at `w`
  is the complex conjugate of that of `a` once `E_w` is identified with `ℂ` through the embedding
  attached to `w` (`NumberField.IsCMField.extensionEmbedding_infiniteAdeleRing_star_apply`). As
  conjugation of `ℂ` commutes with conjugation, the same holds for the other identification of
  `E_w` with `ℂ`, through the conjugate embedding.

## Main declarations

* `NumberField.IsCMField.infiniteAdeleConj`: complex conjugation on the infinite adeles.
* `NumberField.IsCMField.instStarRingFiniteAdeleRing`,
  `NumberField.IsCMField.instStarRingInfiniteAdeleRing`: the star structures, with
  `ContinuousStar` and `StarModule E` instances.
* `NumberField.IsCMField.exists_valuation_complexConj_eq`: every finite place has a conjugate
  place, and `NumberField.IsCMField.finiteAdeleRing_star_apply`: the components of the conjugate
  of a finite adele.
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

/-! ### The finite adeles -/

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

instance : ContinuousStar 𝔸ᶠ[E] where
  continuous_star := by
    rw [← coe_finiteAdeleConj, finiteAdeleConj_def]
    exact continuous_finiteAdeleEquiv E E _

/-- The diagonal embedding of `E` in its finite adeles commutes with conjugation. -/
instance : StarModule E 𝔸ᶠ[E] :=
  ⟨fun r a ↦ by
    rw [Algebra.smul_def, Algebra.smul_def, star_mul', ← coe_finiteAdeleConj,
      finiteAdeleConj_algebraMap]
    -- the star of `E` is `complexConj E` by definition (`NumberField.IsCMField.starRing`)
    rfl⟩

/-- Conjugation preserves the integral finite adeles. It takes priority over the place-by-place
unfolding `IsDedekindDomain.FiniteAdeleRing.mem_integralAdeles` as a `simp` lemma. -/
@[simp high]
theorem star_mem_integralAdeles_iff {a : 𝔸ᶠ[E]} :
    star a ∈ FiniteAdeleRing.integralAdeles (𝓞 E) E ↔ a ∈ FiniteAdeleRing.integralAdeles (𝓞 E) E :=
  finiteAdeleConj_mem_integralAdeles_iff

/-- **Conjugate places.** Every finite place `w` of a CM field has a conjugate place `conj w`, the
image of `w` under conjugation, characterised by `|conj x|_{conj w} = |x|_w` for `x ∈ E`. -/
theorem exists_valuation_complexConj_eq (w : HeightOneSpectrum (𝓞 E)) :
    ∃ w' : HeightOneSpectrum (𝓞 E), ∀ x : E,
      w'.valuation E (complexConj E x) = w.valuation E x := by
  let e : 𝓞 E ≃+* 𝓞 E := (ringOfIntegersComplexConj E).toRingEquiv
  -- The conjugation of `E` is the isomorphism of fraction fields induced by that of `𝓞 E`.
  have he : (IsFractionRing.ringEquivOfRingEquiv e : E ≃+* E) = (complexConj E).toRingEquiv := by
    apply RingEquiv.toRingHom_injective
    exact IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 E)) (RingHom.ext fun r ↦ by simp [e])
  refine ⟨equivOfRingEquiv e w, fun x ↦ ?_⟩
  have h := valuation_ringEquivOfRingEquiv (K := E) (K' := E) e (asIdeal_equivOfRingEquiv e w) x
  rwa [he] at h

/-- **Conjugation of finite adeles at a place.** If the finite place `w'` is the conjugate of `w`,
that is `|conj x|_{w'} = |x|_w` for `x ∈ E`, then the component at `w'` of the conjugate of a finite
adele `a` is the image of the component `a_w` under the isomorphism `E_w ≃ E_{w'}` extending the
conjugation of `E`. -/
theorem finiteAdeleRing_star_apply {w w' : HeightOneSpectrum (𝓞 E)}
    (hw : ∀ x : E, w'.valuation E (complexConj E x) = w.valuation E x) (a : 𝔸ᶠ[E]) :
    (star a) w' = adicCompletionCongr w w' (complexConj E).toRingEquiv hw (a w) := by
  -- Both sides are continuous in `a` and agree on the dense image of `E`.
  have hl : Continuous fun a : 𝔸ᶠ[E] ↦ FiniteAdeleRing.proj E w' (star a) :=
    (FiniteAdeleRing.proj E w').continuous.comp continuous_star
  have hr : Continuous fun a : 𝔸ᶠ[E] ↦
      adicCompletionCongr w w' (complexConj E).toRingEquiv hw (FiniteAdeleRing.proj E w a) :=
    (continuous_adicCompletionCongr hw).comp (FiniteAdeleRing.proj E w).continuous
  have h := congr_fun ((FiniteAdeleRing.denseRange_algebraMap (R := 𝓞 E) E).equalizer hl hr
    (funext fun x ↦ ?_)) a
  · simpa only [FiniteAdeleRing.proj_apply] using h
  simp only [Function.comp_apply, ← algebraMap_star_comm, AlgHomClass.commutes]
  rw [adicCompletionCongr_algebraMap]
  -- the star of `E` is `complexConj E` by definition (`NumberField.IsCMField.starRing`)
  rfl

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
  have h : (complexConj E).toRingEquiv.trans (complexConj E).toRingEquiv = RingEquiv.refl E :=
    RingEquiv.ext fun x ↦ complexConj_apply_apply (K := E) x
  rw [infiniteAdeleConj_def, ← RingEquiv.trans_apply, infiniteAdeleEquiv_trans, h,
    infiniteAdeleEquiv_refl, RingEquiv.refl_apply]

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
      infiniteAdeleConj_algebraMap]
    -- the star of `E` is `complexConj E` by definition (`NumberField.IsCMField.starRing`)
    rfl⟩

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
    InfinitePlace.Completion.extensionEmbedding_coe]
  -- the star of `E` is `complexConj E` by definition (`NumberField.IsCMField.starRing`)
  exact complexEmbedding_complexConj E w.embedding _

end NumberField.IsCMField

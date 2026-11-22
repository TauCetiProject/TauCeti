/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.ReesAlgebra.AssociatedGraded

/-!
# Change of coefficients for the Rees algebra and the Rees quotient

Let `f : R →+* S` be a ring homomorphism and let `I ⊆ R`, `J ⊆ S` be ideals with `I ≤ J.comap f`,
for instance `J = I.map f`. Applying `f` to the coefficients of a Rees polynomial `∑ aₙ tⁿ` with
`aₙ ∈ Iⁿ` gives a Rees polynomial `∑ f(aₙ) tⁿ` with `f(aₙ) ∈ Jⁿ`; this is the ring homomorphism
`R[It] → S[Jt]`. It carries the extended ideal `I R[It]` into `J S[Jt]` and so induces a ring
homomorphism of Rees quotients

`R[It] ⧸ I R[It] → S[Jt] ⧸ J S[Jt]`, `[x tⁿ] ↦ [f(x) tⁿ]`.

Under the identifications of both Rees quotients with associated graded rings, this map is the
map `gr_I R → gr_J S` of `Ideal.AssociatedGraded.map`, and it inherits the properties of that map:
it is injective exactly when `Iⁿ ∩ f⁻¹(Jⁿ⁺¹) = Iⁿ⁺¹` for every `n`, and surjective when `f` is
surjective and `J = I.map f`; a ring isomorphism induces an isomorphism of Rees quotients.
Injectivity of `f` does not suffice for injectivity of the induced map: for `k[[t²,t³]] ⊆ k[[t]]`
with `I = (t²)` and `J = I.map f`, the element `t⁵ ∈ I \ I²` maps into `J² = (t⁴)`.

## Main definitions

* `reesAlgebra.map f h`: the ring homomorphism `R[It] →+* S[Jt]` applying `f` to coefficients.
* `Ideal.ReesQuotient.map f h`: the induced ring homomorphism of Rees quotients.
* `Ideal.ReesQuotient.mapEquiv e h`: for a ring isomorphism `e` with `I.map e = J`, the induced
  ring isomorphism of Rees quotients.

## Main results

* `Ideal.ReesQuotient.map_mk`: the class of `x ∈ Iⁿ` in degree `n` goes to the class of `f x`.
* `Ideal.ReesQuotient.equivAssociatedGraded_map`: the comparison square with
  `Ideal.AssociatedGraded.map` commutes.
* `Ideal.ReesQuotient.coeff_map` and `Ideal.ReesQuotient.map_of`: in each degree `n`, the map is
  `Ideal.gradedPieceMap f h n` on coefficients and on homogeneous pieces.
* `Ideal.ReesQuotient.map_id` and `Ideal.ReesQuotient.map_comp`: functoriality.
* `Ideal.ReesQuotient.map_injective_iff` and `Ideal.ReesQuotient.map_surjective`: the injectivity
  criterion and surjectivity for surjective `f`.

## References

* The Stacks Project, Chapter 10 (Commutative Algebra), section *Associated graded ring*.
* M. F. Atiyah and I. G. Macdonald, *Introduction to Commutative Algebra*, Chapter 10.
-/

public section

open Polynomial

universe u v w

variable {R : Type u} [CommRing R] {S : Type v} [CommRing S] {I : Ideal R} {J : Ideal S}

namespace reesAlgebra

/-- The ring homomorphism `R[It] →+* S[Jt]` applying a ring homomorphism `f : R →+* S` with
`I ≤ J.comap f` to the coefficients of a Rees polynomial (`reesAlgebra.coe_map`). -/
noncomputable def map (f : R →+* S) (h : I ≤ J.comap f) : reesAlgebra I →+* reesAlgebra J :=
  ((mapRingHom f).comp (reesAlgebra I).val.toRingHom).codRestrict (reesAlgebra J) fun g ↦ by
    rw [mem_reesAlgebra_iff]
    intro n
    simpa using Ideal.map_mem_pow_of_le_comap f h ((mem_reesAlgebra_iff I _).mp g.property n)

/-- `reesAlgebra.map f h` applies `f` to the coefficients. -/
@[simp]
theorem coe_map (f : R →+* S) (h : I ≤ J.comap f) (g : reesAlgebra I) :
    (map f h g : S[X]) = (g : R[X]).map f :=
  (rfl)

end reesAlgebra

namespace Ideal.ReesQuotient

/-- The coefficient map `R[It] → S[Jt]` carries `I R[It]` into `J S[Jt]`. -/
private theorem map_le_comap (f : R →+* S) (h : I ≤ J.comap f) :
    I.map (algebraMap R (reesAlgebra I)) ≤
      (J.map (algebraMap S (reesAlgebra J))).comap (reesAlgebra.map f h) := by
  intro g hg
  rw [mem_comap, mem_map_algebraMap_reesAlgebra_iff]
  rw [mem_map_algebraMap_reesAlgebra_iff] at hg
  intro n
  simpa using map_mem_pow_of_le_comap f h (hg n)

/-- The ring homomorphism `R[It] ⧸ I R[It] →+* S[Jt] ⧸ J S[Jt]` of Rees quotients induced by a ring
homomorphism `f : R →+* S` with `I ≤ J.comap f`. It sends the class of a Rees polynomial to the
class of the polynomial obtained by applying `f` to its coefficients
(`Ideal.ReesQuotient.map_quotientMk`), and the class of `x ∈ Iⁿ` in degree `n` to the class of
`f x` (`Ideal.ReesQuotient.map_mk`). -/
noncomputable def map (f : R →+* S) (h : I ≤ J.comap f) : I.ReesQuotient →+* J.ReesQuotient :=
  quotientMap _ (reesAlgebra.map f h) (map_le_comap f h)

/-- `ReesQuotient.map` is induced by applying `f` to the coefficients of a Rees polynomial. -/
@[simp]
theorem map_quotientMk (f : R →+* S) (h : I ≤ J.comap f) (g : reesAlgebra I) :
    map f h (Ideal.Quotient.mk _ g) = Ideal.Quotient.mk _ (reesAlgebra.map f h g) :=
  quotientMap_mk

/-- `ReesQuotient.map` sends the class of `x ∈ Iⁿ` in degree `n` to the class of `f x ∈ Jⁿ`. -/
@[simp]
theorem map_mk (f : R →+* S) (h : I ≤ J.comap f) {n : ℕ} (x : ↥(I ^ n)) :
    map f h (mk I n x) = mk J n ⟨f x, map_mem_pow_of_le_comap f h x.property⟩ := by
  rw [mk_apply, mk_apply, map_quotientMk]
  congr 1
  ext1
  simp

/-- `ReesQuotient.map` is compatible with the algebra maps from `R` and `S`. -/
@[simp]
theorem map_algebraMap (f : R →+* S) (h : I ≤ J.comap f) (r : R) :
    map f h (algebraMap R I.ReesQuotient r) = algebraMap S J.ReesQuotient (f r) := by
  rw [← mk_zero ⟨r, I.mem_pow_zero r⟩, map_mk, mk_zero]

/-- **The comparison square commutes.** Under the identifications of the Rees quotients with the
associated graded rings, `ReesQuotient.map` is `Ideal.AssociatedGraded.map`. -/
@[simp]
theorem equivAssociatedGraded_map (f : R →+* S) (h : I ≤ J.comap f) (q : I.ReesQuotient) :
    equivAssociatedGraded J (map f h q) = AssociatedGraded.map f h (equivAssociatedGraded I q) := by
  suffices (equivAssociatedGraded J : J.ReesQuotient →+* J.AssociatedGraded).comp (map f h) =
      (AssociatedGraded.map f h).comp (equivAssociatedGraded I : I.ReesQuotient →+* _) from
    DFunLike.congr_fun this q
  refine ringHom_ext (fun r ↦ ?_) (fun x ↦ ?_)
  · rw [← mk_zero ⟨r, I.mem_pow_zero r⟩]
    simp only [RingHom.comp_apply, map_mk, RingHom.coe_coe, equivAssociatedGraded_mk,
      AssociatedGraded.map_mk]
  · simp

/-- `ReesQuotient.map` is `Ideal.AssociatedGraded.map`, conjugated by the identifications of the
Rees quotients with the associated graded rings. -/
private theorem coe_map_eq (f : R →+* S) (h : I ≤ J.comap f) :
    ⇑(map f h) =
      (equivAssociatedGraded J).symm ∘ AssociatedGraded.map f h ∘ equivAssociatedGraded I :=
  funext fun q ↦ by simp [AlgEquiv.eq_symm_apply]

/-- The degree-`n` coefficient of `ReesQuotient.map f h q` is the image of the degree-`n`
coefficient of `q` under `Ideal.gradedPieceMap f h n`. -/
@[simp]
theorem coeff_map (f : R →+* S) (h : I ≤ J.comap f) (q : I.ReesQuotient) (n : ℕ) :
    coeff J n (map f h q) = gradedPieceMap f h n (coeff I n q) := by
  rw [coeff_apply, coeff_apply, equivAssociatedGraded_map, AssociatedGraded.map_apply]

/-- `ReesQuotient.map f h` sends the degree-`n` piece to the degree-`n` piece, by
`Ideal.gradedPieceMap f h n`. -/
@[simp]
theorem map_of (f : R →+* S) (h : I ≤ J.comap f) (n : ℕ) (x : I.GradedPiece n) :
    map f h (of I n x) = of J n (gradedPieceMap f h n x) := by
  apply (equivAssociatedGraded J).injective
  rw [equivAssociatedGraded_map, equivAssociatedGraded_of, equivAssociatedGraded_of,
    AssociatedGraded.map_of]

/-- The identity of `R` induces the identity of `R[It] ⧸ I R[It]`. -/
@[simp]
theorem map_id (h : I ≤ I.comap (RingHom.id R)) : map (RingHom.id R) h = RingHom.id _ :=
  Ideal.Quotient.ringHom_ext <| RingHom.ext fun g ↦ by
    simp only [RingHom.comp_apply, map_quotientMk, RingHom.id_apply]
    congr 1
    ext1
    simp

/-- The map induced by a composite is the composite of the induced maps. -/
theorem map_comp {T : Type w} [CommRing T] {K : Ideal T} (g : S →+* T) (f : R →+* S)
    (hJK : J ≤ K.comap g) (hIJ : I ≤ J.comap f) (hIK : I ≤ K.comap (g.comp f)) :
    (map g hJK).comp (map f hIJ) = map (g.comp f) hIK :=
  Ideal.Quotient.ringHom_ext <| RingHom.ext fun p ↦ by
    simp only [RingHom.comp_apply, map_quotientMk]
    congr 1
    ext1
    simp [Polynomial.map_map]

/-- **Injectivity of the induced map.** `R[It] ⧸ I R[It] → S[Jt] ⧸ J S[Jt]` is injective exactly
when, for every `n`, an element `x ∈ Iⁿ` with `f x ∈ Jⁿ⁺¹` already lies in `Iⁿ⁺¹`. -/
theorem map_injective_iff (f : R →+* S) (h : I ≤ J.comap f) :
    Function.Injective (map f h) ↔ ∀ n, I ^ n ⊓ (J ^ (n + 1)).comap f ≤ I ^ (n + 1) := by
  rw [← AssociatedGraded.map_injective_iff, coe_map_eq,
    (equivAssociatedGraded J).symm.injective.of_comp_iff,
    Function.Injective.of_comp_iff' _ (equivAssociatedGraded I).bijective]

/-- If `f` is surjective and `J ≤ I.map f`, for instance `J = I.map f`, then
`R[It] ⧸ I R[It] → S[Jt] ⧸ J S[Jt]` is surjective. -/
theorem map_surjective {f : R →+* S} (hf : Function.Surjective f) (h : I ≤ J.comap f)
    (hJ : J ≤ I.map f) : Function.Surjective (map f h) := by
  rw [coe_map_eq]
  exact (equivAssociatedGraded J).symm.surjective.comp
    ((AssociatedGraded.map_surjective hf h hJ).comp (equivAssociatedGraded I).surjective)

/-- The ring isomorphism `R[It] ⧸ I R[It] ≃+* S[Jt] ⧸ J S[Jt]` induced by a ring isomorphism
`e : R ≃+* S` with `I.map e = J`. Its forward map is `ReesQuotient.map e` and its inverse is
`ReesQuotient.map e.symm` (`Ideal.ReesQuotient.coe_mapEquiv`,
`Ideal.ReesQuotient.mapEquiv_symm`). -/
noncomputable def mapEquiv (e : R ≃+* S) (hIJ : I.map e = J) :
    I.ReesQuotient ≃+* J.ReesQuotient :=
  RingEquiv.ofRingHom (map (e : R →+* S) (hIJ ▸ le_comap_map))
    (map (e.symm : S →+* R) (by rw [← hIJ, comap_coe, comap_symm]))
    ((map_comp _ _ _ _ (by simp)).trans (by simp))
    ((map_comp _ _ _ _ (by simp)).trans (by simp))

/-- The forward map of `ReesQuotient.mapEquiv e h` is `ReesQuotient.map e`. -/
@[simp]
theorem coe_mapEquiv (e : R ≃+* S) (hIJ : I.map e = J) :
    ⇑(mapEquiv e hIJ) = map (e : R →+* S) (hIJ ▸ le_comap_map) :=
  (rfl)

/-- The inverse of `ReesQuotient.mapEquiv e h` is the isomorphism induced by `e.symm`. -/
@[simp]
theorem mapEquiv_symm (e : R ≃+* S) (hIJ : I.map e = J) :
    (mapEquiv e hIJ).symm = mapEquiv e.symm (by rw [← hIJ, map_symm, comap_map_of_bijective _
      e.bijective]) :=
  (rfl)

end Ideal.ReesQuotient

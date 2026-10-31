/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Dynamic.Unipotent.Representability

/-!
# Closed subgroups stable under conjugation by a cocharacter

Let `λ : 𝔾ₘ → G` be a cocharacter of an affine group `G = Spec H`. A closed subgroup `K ⊆ G`, cut
out by a Hopf ideal `I`, is stable under conjugation by `λ` when `I` is stable under the
coefficients of universal conjugation `h ↦ ∑ₙ hₙ Tⁿ` (`TauCeti.HopfIdeal.IsCocharacterStable`):
equivalently, `I` is homogeneous for the grading of `H` by `λ`-weights. On points this says that
conjugation by `λ(t)` preserves `K` for every unit `t`, over every value algebra.

The dynamic unipotent subgroup `U(λ)` is `λ`-stable, and if `λ` factors through the dynamic
parabolic `P(μ)` of a second cocharacter `μ`, for instance when `λ` and `μ` are cocharacters of a
common torus, then `U(μ)` is `λ`-stable too. For a point `g` of a stable closed subgroup that lies
in `P(λ)`, the extension of the conjugation family `t ↦ λ(t) g λ(t)⁻¹` over the origin stays inside
the subgroup, because a polynomial whose Laurent image vanishes is zero.

## Main declarations

* `TauCeti.HopfIdeal.IsCocharacterStable`: stability of a closed subgroup under conjugation by a
  cocharacter.
* `TauCeti.HopfIdeal.isCocharacterStable_iff_coeff_mem`: the defining coefficient condition.
* `TauCeti.HopfIdeal.isCocharacterStable_iff_forall_conjugate_mem`: stability means that generic
  conjugation preserves the points of the subgroup.
* `TauCeti.HopfIdeal.IsCocharacterStable.pointsHom_mul_mul_inv_mem`: a stable subgroup is
  normalized by the points `λ(t)`.
* `TauCeti.HopfIdeal.IsCocharacterStable.sup`: intersections of stable subgroups are stable.
* `TauCeti.HopfIdeal.isCocharacterStable_of_le_ker`: a closed subgroup through which `λ` factors
  is `λ`-stable.
* `TauCeti.HopfIdeal.isCocharacterStable_unipotentDefiningHopfIdeal` and
  `TauCeti.HopfIdeal.isCocharacterStable_unipotentDefiningHopfIdeal_of_le_ker`: `U(λ)` is
  `λ`-stable, and `U(μ)` is `λ`-stable when `λ` factors through `P(μ)`.
* `TauCeti.Cocharacter.extend_mem_quotientPointsSubgroup`: the extended conjugation family of a
  point of a stable closed subgroup stays inside it.

## References

* B. Conrad, O. Gabber, G. Prasad, *Pseudo-reductive Groups*, §2.1.
* J. S. Milne, *Algebraic Groups* (2017), Chapter 13.
-/

public section

open CategoryTheory WithConv

universe u v w

noncomputable section

namespace TauCeti

open Cocharacter

namespace HopfIdeal

section Ring

variable {R : Type u} {H : Type v} {A : Type w}
variable [CommRing R] [CommRing H] [HopfAlgebra R H] [CommRing A] [Algebra R A]

/-- A closed subgroup, cut out by the Hopf ideal `I`, is **stable under conjugation by the
cocharacter `l`** when every coefficient of the universal conjugation `l(T) h l(T)⁻¹` of an element
`h ∈ I` again lies in `I`. Equivalently, `I` is homogeneous for the grading of the coordinate
algebra by `l`-weights; on points, conjugation by `l(t)` preserves the subgroup
(`TauCeti.HopfIdeal.IsCocharacterStable.pointsHom_mul_mul_inv_mem`). -/
def IsCocharacterStable (I : HopfIdeal R H) (l : H →ₐc[R] LaurentPolynomial R) : Prop :=
  ∀ x ∈ I, ∀ n : ℤ, (conjugationAlgHom l x).coeff n ∈ I

variable {I J : HopfIdeal R H} {l : H →ₐc[R] LaurentPolynomial R}

/-- Stability under a cocharacter, stated on the coefficients of universal conjugation. -/
theorem isCocharacterStable_iff_coeff_mem :
    I.IsCocharacterStable l ↔ ∀ x ∈ I, ∀ n : ℤ, (conjugationAlgHom l x).coeff n ∈ I :=
  Iff.rfl

/-- Generic conjugation by a cocharacter preserves the points of a stable closed subgroup. -/
theorem IsCocharacterStable.conjugate_mem (hI : I.IsCocharacterStable l)
    {g : WithConv (H →ₐ[R] A)}
    (hg : g ∈ CommHopfAlgCat.quotientPointsSubgroup (_root_.CommHopfAlgCat.of R H) I
      (CommAlgCat.of R A)) :
    conjugate A l g ∈ CommHopfAlgCat.quotientPointsSubgroup (_root_.CommHopfAlgCat.of R H) I
      (CommAlgCat.of R (LaurentPolynomial A)) := by
  rw [CommHopfAlgCat.mem_quotientPointsSubgroup_iff] at hg ⊢
  intro x hx
  refine AddMonoidAlgebra.coeff_injective (Finsupp.ext fun n ↦ ?_)
  rw [coeff_conjugate, hg _ (hI x hx n)]
  simp

/-- **Stability is preservation of points by generic conjugation.** A closed subgroup is stable
under conjugation by `l` exactly when generic conjugation `g ↦ l(T) g l(T)⁻¹` carries its
`A`-points to its `A[T;T⁻¹]`-points for every value algebra `A`. Testing on the universal point
of the subgroup suffices. -/
theorem isCocharacterStable_iff_forall_conjugate_mem :
    I.IsCocharacterStable l ↔ ∀ (A : Type v) [CommRing A] [Algebra R A]
      (g : WithConv (H →ₐ[R] A)),
      g ∈ CommHopfAlgCat.quotientPointsSubgroup (_root_.CommHopfAlgCat.of R H) I
          (CommAlgCat.of R A) →
        conjugate A l g ∈ CommHopfAlgCat.quotientPointsSubgroup (_root_.CommHopfAlgCat.of R H) I
          (CommAlgCat.of R (LaurentPolynomial A)) := by
  refine ⟨fun hI A _ _ g hg ↦ hI.conjugate_mem hg, fun h x hx n ↦ ?_⟩
  -- Conjugate the universal point of the subgroup, the quotient map `H → H ⧸ I`.
  let q : WithConv (H →ₐ[R] H ⧸ I.toIdeal) := toConv (Ideal.Quotient.mkₐ R I.toIdeal)
  have hq : q ∈ CommHopfAlgCat.quotientPointsSubgroup (_root_.CommHopfAlgCat.of R H) I
      (CommAlgCat.of R (H ⧸ I.toIdeal)) := by
    rw [CommHopfAlgCat.mem_quotientPointsSubgroup_iff]
    intro y hy
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (HopfIdeal.mem_toIdeal.mpr hy)
  have hc := h _ q hq
  rw [CommHopfAlgCat.mem_quotientPointsSubgroup_iff] at hc
  have hn := congrArg (fun p : LaurentPolynomial (H ⧸ I.toIdeal) ↦ p.coeff n) (hc x hx)
  simp only [coeff_conjugate] at hn
  exact HopfIdeal.mem_toIdeal.mp (Ideal.Quotient.eq_zero_iff_mem.mp hn)

/-- **A stable closed subgroup is normalized by the points of the cocharacter**: conjugation by
`l(t)`, for a unit `t` of the value algebra, preserves its points. -/
theorem IsCocharacterStable.pointsHom_mul_mul_inv_mem (hI : I.IsCocharacterStable l) (t : Aˣ)
    {g : WithConv (H →ₐ[R] A)}
    (hg : g ∈ CommHopfAlgCat.quotientPointsSubgroup (_root_.CommHopfAlgCat.of R H) I
      (CommAlgCat.of R A)) :
    pointsHom A l t * g * (pointsHom A l t)⁻¹ ∈
      CommHopfAlgCat.quotientPointsSubgroup (_root_.CommHopfAlgCat.of R H) I
        (CommAlgCat.of R A) := by
  -- Specialize generic conjugation along the evaluation `T ↦ t`.
  set e : LaurentPolynomial A →ₐ[R] A := (laurentEval (R := A) t).restrictScalars R
  have ht : Units.map e.toMonoidHom (LaurentPolynomial.genericUnit A) = t := by
    ext
    simp [e]
  have he : e.comp (IsScalarTower.toAlgHom R A (LaurentPolynomial A)) = AlgHom.id R A := by
    ext a
    simp [e]
  have hmap := mapValue_conjugate l e g
  rw [ht, he, AlgHom.mapValue_id, MonoidHom.id_apply] at hmap
  rw [← hmap]
  exact CommHopfAlgCat.mapValue_mem_quotientPointsSubgroup (_root_.CommHopfAlgCat.of R H) I e
    (hI.conjugate_mem hg)

/-- **Intersections of stable closed subgroups are stable.** -/
theorem IsCocharacterStable.sup (hI : I.IsCocharacterStable l) (hJ : J.IsCocharacterStable l) :
    (I ⊔ J).IsCocharacterStable l := by
  rw [isCocharacterStable_iff_forall_conjugate_mem] at hI hJ ⊢
  intro A _ _ g hg
  rw [CommHopfAlgCat.quotientPointsSubgroup_sup] at hg ⊢
  exact ⟨hI A g hg.1, hJ A g hg.2⟩

/-- If the cocharacter `l` factors through the closed subgroup cut out by `J`, its generic point
`l(T)` is a point of that subgroup. -/
theorem genericPoint_mem_quotientPointsSubgroup_of_le_ker
    (hJ : J.toIdeal ≤ RingHom.ker l.toAlgHom.toRingHom) :
    genericPoint A l ∈ CommHopfAlgCat.quotientPointsSubgroup (_root_.CommHopfAlgCat.of R H) J
      (CommAlgCat.of R (LaurentPolynomial A)) := by
  rw [CommHopfAlgCat.mem_quotientPointsSubgroup_iff]
  intro x hx
  have hl : l x = 0 := RingHom.mem_ker.mp (hJ (HopfIdeal.mem_toIdeal.mpr hx))
  rw [genericPoint_ofConv, AlgHom.comp_apply]
  simp [hl]

/-- **A closed subgroup through which the cocharacter factors is stable under it**: conjugation
by points of the subgroup preserves the subgroup. -/
theorem isCocharacterStable_of_le_ker (hJ : J.toIdeal ≤ RingHom.ker l.toAlgHom.toRingHom) :
    J.IsCocharacterStable l := by
  rw [isCocharacterStable_iff_forall_conjugate_mem]
  intro A _ _ g hg
  have hl := genericPoint_mem_quotientPointsSubgroup_of_le_ker (A := A) hJ
  have hc : constPoint A g ∈ CommHopfAlgCat.quotientPointsSubgroup
      (_root_.CommHopfAlgCat.of R H) J (CommAlgCat.of R (LaurentPolynomial A)) := by
    rw [constPoint_apply, ← AlgHom.mapValue_apply]
    exact CommHopfAlgCat.mapValue_mem_quotientPointsSubgroup (_root_.CommHopfAlgCat.of R H) J
      (IsScalarTower.toAlgHom R A (LaurentPolynomial A)) hg
  rw [conjugate_apply]
  exact mul_mem (mul_mem hl hc) (inv_mem hl)

/-- **The dynamic unipotent subgroup `U(l)` is stable under conjugation by `l`.** -/
theorem isCocharacterStable_unipotentDefiningHopfIdeal :
    l.unipotentDefiningHopfIdeal.IsCocharacterStable l := by
  rw [isCocharacterStable_iff_forall_conjugate_mem]
  intro A _ _ g hg
  rw [BialgHom.quotientPointsSubgroup_unipotentDefiningHopfIdeal] at hg ⊢
  exact conjugate_mem_unipotent hg

/-- **`U(m)` is stable under conjugation by `l` when `l` factors through `P(m)`**, because `U(m)`
is normal in `P(m)`. This applies in particular when `l` factors through the Levi subgroup `Z(m)`,
for instance when `l` and `m` are cocharacters of a common torus. -/
theorem isCocharacterStable_unipotentDefiningHopfIdeal_of_le_ker
    {m : H →ₐc[R] LaurentPolynomial R}
    (hlm : (parabolicDefiningHopfIdeal m).toIdeal ≤ RingHom.ker l.toAlgHom.toRingHom) :
    m.unipotentDefiningHopfIdeal.IsCocharacterStable l := by
  rw [isCocharacterStable_iff_forall_conjugate_mem]
  intro A _ _ g hg
  have hl := genericPoint_mem_quotientPointsSubgroup_of_le_ker (A := A) hlm
  rw [quotientPointsSubgroup_parabolicDefiningHopfIdeal] at hl
  rw [BialgHom.quotientPointsSubgroup_unipotentDefiningHopfIdeal] at hg ⊢
  rw [conjugate_apply]
  exact conj_mem_unipotent hl (constPoint_mem_unipotent hg)

end Ring

end HopfIdeal

namespace Cocharacter

section Ring

variable {R : Type u} {H : Type v} {A : Type w}
variable [CommRing R] [CommRing H] [HopfAlgebra R H] [CommRing A] [Algebra R A]
variable {l : H →ₐc[R] LaurentPolynomial R}

/-- **The extended conjugation family stays in a stable closed subgroup.** For a point `g` of the
dynamic parabolic lying in a closed subgroup stable under `l`, the polynomial extension of
`t ↦ l(t) g l(t)⁻¹` over the origin is a point of that subgroup, including at the origin. -/
theorem extend_mem_quotientPointsSubgroup {I : HopfIdeal R H} (hI : I.IsCocharacterStable l)
    (g : parabolic A l)
    (hg : (g : WithConv (H →ₐ[R] A)) ∈
      CommHopfAlgCat.quotientPointsSubgroup (_root_.CommHopfAlgCat.of R H) I
        (CommAlgCat.of R A)) :
    extend A l g ∈ CommHopfAlgCat.quotientPointsSubgroup (_root_.CommHopfAlgCat.of R H) I
      (CommAlgCat.of R (Polynomial A)) := by
  have hc := hI.conjugate_mem hg
  rw [CommHopfAlgCat.mem_quotientPointsSubgroup_iff] at hc ⊢
  intro h hh
  apply Polynomial.toLaurent_injective
  have hz := hc h hh
  rw [← ofPolyPoint_extend g, ofPolyPoint_apply] at hz
  simpa only [ofConv_toConv, AlgHom.comp_apply, AlgHom.restrictScalars_apply,
    Polynomial.coe_toLaurentAlg, map_zero] using hz

end Ring

end Cocharacter

end TauCeti

end

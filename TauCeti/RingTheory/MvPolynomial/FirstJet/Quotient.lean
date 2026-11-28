/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.MvPolynomial.FirstJet.DoublePoint
public import TauCeti.RingTheory.MvPolynomial.FirstJet.Evaluation

/-!
# Comparison of bounded first-jet evaluation and double-point quotients

This file connects the double-point quotient
(`TauCeti.RingTheory.MvPolynomial.FirstJet.DoublePoint`) with bounded-degree first-jet
evaluation (`TauCeti.RingTheory.MvPolynomial.FirstJet.Evaluation`).

For a finite family of points whose evaluation ideals are pairwise comaximal, the kernel of
`TauCeti.firstJetMap P d` consists of the elements of `TauCeti.doubleIdeal P` of total degree at
most `d` (`TauCeti.mem_ker_firstJetMap_iff_mem_doubleIdeal`). When in addition the variable type is
finite, `TauCeti.firstJetMap P d` factors through `TauCeti.doublePointQuotientEquiv` and
`TauCeti.jetEquivOption` (`TauCeti.firstJetMap_eq_doublePointQuotientEquiv`), so `P` is well poised
in degree `d` if and only if the quotient map `R[X] → R[X] ⧸ doubleIdeal P` is surjective on
`restrictTotalDegree σ R d` (`TauCeti.wellPoised_iff_surjective_quotientMk`).

## Main results

* `TauCeti.mem_ker_firstJetMap_iff_mem_doubleIdeal`: for finitely many points with pairwise
  comaximal evaluation ideals, `LinearMap.ker (firstJetMap P d)` consists of the elements of
  `doubleIdeal P` of total degree at most `d`.
* `TauCeti.firstJetMap_eq_doublePointQuotientEquiv`: for finitely many points in finitely many
  variables with pairwise comaximal evaluation ideals, `firstJetMap P d` factors through the
  quotient by `doubleIdeal P`, `doublePointQuotientEquiv`, and `jetEquivOption`.
* `TauCeti.wellPoised_iff_surjective_quotientMk`: for finitely many points in finitely many
  variables with pairwise comaximal evaluation ideals, well-poisedness in degree `d` is
  surjectivity of the quotient map on `restrictTotalDegree σ R d`.
-/

public section

namespace TauCeti

open MvPolynomial

variable {σ ι R : Type*} [CommRing R]

/-- For a finite family of points with pairwise comaximal evaluation ideals, a bounded polynomial
lies in the kernel of `firstJetMap P d` if and only if it lies in `doubleIdeal P`. -/
theorem mem_ker_firstJetMap_iff_mem_doubleIdeal [Finite ι] {P : ι → σ → R}
    (hP : Pairwise (Function.onFun IsCoprime fun i ↦ RingHom.ker (eval (P i)))) {d : ℕ}
    {f : restrictTotalDegree σ R d} :
    f ∈ LinearMap.ker (firstJetMap P d) ↔ (f : MvPolynomial σ R) ∈ doubleIdeal P := by
  rw [mem_ker_firstJetMap, mem_doubleIdeal_iff hP]

/-- For finitely many points in finitely many variables with pairwise comaximal evaluation ideals,
`firstJetMap P d` factors as the bounded quotient map followed by `doublePointQuotientEquiv` and
pointwise conversion `jetEquivOption`. -/
theorem firstJetMap_eq_doublePointQuotientEquiv [Finite σ] [Finite ι] [DecidableEq σ]
    {P : ι → σ → R}
    (hP : Pairwise (Function.onFun IsCoprime fun i ↦ RingHom.ker (eval (P i)))) (d : ℕ) :
    firstJetMap P d =
      (LinearEquiv.piCongrRight fun _ ↦ jetEquivOption R σ).toLinearMap ∘ₗ
        (doublePointQuotientEquiv hP).toLinearMap ∘ₗ
        (Ideal.Quotient.mkₐ R (doubleIdeal P)).toLinearMap ∘ₗ
        (restrictTotalDegree σ R d).subtype := by
  ext f i z
  cases z <;> simp

/-- For a finite family of points in finitely many variables whose evaluation ideals are pairwise
comaximal, well-poisedness in degree `d` is equivalent to surjectivity of the quotient map
`MvPolynomial σ R → MvPolynomial σ R ⧸ doubleIdeal P` restricted to `restrictTotalDegree σ R d`. -/
theorem wellPoised_iff_surjective_quotientMk [Finite σ] [Finite ι] {P : ι → σ → R}
    (hP : Pairwise (Function.onFun IsCoprime fun i ↦ RingHom.ker (eval (P i)))) (d : ℕ) :
    WellPoised P d ↔
      Function.Surjective
        ((Ideal.Quotient.mkₐ R (doubleIdeal P)).toLinearMap ∘ₗ
          (restrictTotalDegree σ R d).subtype) := by
  classical
  rw [wellPoised_iff, firstJetMap_eq_doublePointQuotientEquiv hP d,
    LinearMap.coe_comp, LinearMap.coe_comp, LinearEquiv.coe_toLinearMap,
    LinearEquiv.coe_toLinearMap, EquivLike.comp_surjective, EquivLike.comp_surjective]

end TauCeti

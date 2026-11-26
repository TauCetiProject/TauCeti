/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Legendre.Equation
public import TauCeti.AlgebraicGeometry.EllipticCurve.MordellWeil.XSubT

import Mathlib.Algebra.Ring.Fin
import TauCeti.Algebra.Group.PowMonoidHom
import TauCeti.Algebra.Polynomial.RingDivision
import TauCeti.RingTheory.NormTrace.Pi

/-!
# Two-descent on the scaled Legendre equation

The cubic algebra of `y² = x (x - d) (x - d l)` splits by evaluation at its three distinct roots
`0`, `d` and `d l` in that order. This identifies the target of the native `x - T` map with a
triple of square classes over the base field. At a root, the corresponding representative is the
product of the other two differences. The three descent classes have product one, and an affine
point is divisible by two exactly when all three uncorrected differences are squares.

## Main results

* `scaledLegendreRootEval_mk` computes the ordered evaluations of a polynomial class.
* `scaledLegendreSquareClassEquiv_mk` computes the three classes of a polynomial unit.
* `scaledLegendre_halving_iff_squares` gives the criterion for halving an affine point.

## References

* J. H. Silverman, *The Arithmetic of Elliptic Curves*, 2nd ed., X.1, Proposition 1.4.
* M. A. Bennett and S. Siksek, *A conjecture of Erdős, supersingular primes and short character
  sums*, Ann. of Math. 191 (2020), 355–392, §6.
-/

public section

namespace TauCeti

open Polynomial WeierstrassCurve WeierstrassCurve.Affine

section Cubic

variable {R : Type*} [CommRing R]

/-- The cubic of a scaled Legendre equation factors over the coefficient ring. -/
theorem f_scaledLegendre (d l : R) :
    (scaledLegendre d l).toAffine.f = X * (X - C d) * (X - C (d * l)) := by
  simp only [Affine.f, scaledLegendre_a₂, scaledLegendre_a₄, scaledLegendre_a₆, map_neg,
    map_mul, map_add, map_one, map_pow, map_zero, add_zero]
  ring

end Cubic

variable {K : Type*} [Field K] {d l : K}

private theorem scaledLegendre_roots_injective (hd : d ≠ 0) (hl₀ : l ≠ 0) (hl₁ : l ≠ 1) :
    Function.Injective (![0, d, d * l] : Fin 3 → K) := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all [mul_ne_zero hd hl₀]

variable (hd : d ≠ 0) (hl₀ : l ≠ 0) (hl₁ : l ≠ 1)

open Function in
private noncomputable def scaledLegendreRootEvalPi :
    (scaledLegendre d l).toAffine.A ≃ₐ[K] (Fin 3 → K) := by
  let roots : Fin 3 → K := ![0, d, d * l]
  let I (i : Fin 3) : Ideal K[X] := Ideal.span {X - C (roots i)}
  have hI : Pairwise (IsCoprime on I) := fun i j hij ↦
    (Ideal.isCoprime_span_singleton_iff _ _).2
      (pairwise_coprime_X_sub_C (scaledLegendre_roots_injective hd hl₀ hl₁) hij)
  have hf : Ideal.span {(scaledLegendre d l).toAffine.f} = ⨅ i, I i := by
    have hprod := Ideal.prod_eq_iInf_of_pairwise_isCoprime (s := Finset.univ)
      (fun i _ j _ hij ↦ hI hij)
    simp only [Finset.mem_univ, iInf_pos] at hprod
    rw [← hprod]
    simp [I, Ideal.prod_span_singleton, Fin.prod_univ_three, roots, f_scaledLegendre]
  let e : (scaledLegendre d l).toAffine.A ≃+* (Fin 3 → K) :=
    (Ideal.quotEquivOfEq hf).trans <|
      (Ideal.quotientInfRingEquivPiQuotient I hI).trans <|
        RingEquiv.piCongrRight fun i ↦ (quotientSpanXSubCAlgEquiv (roots i)).toRingEquiv
  have he (p : K[X]) (i : Fin 3) : e (AdjoinRoot.mk _ p) i = p.eval (roots i) := (rfl)
  refine AlgEquiv.ofRingEquiv (f := e) fun a ↦ ?_
  funext i
  rw [AdjoinRoot.algebraMap_eq, ← AdjoinRoot.mk_C, he, eval_C]
  rfl

private theorem scaledLegendreRootEvalPi_mk (p : K[X]) (i : Fin 3) :
    scaledLegendreRootEvalPi hd hl₀ hl₁ (AdjoinRoot.mk _ p) i =
      p.eval (![0, d, d * l] i) :=
  (rfl)

/-- The split cubic algebra of the scaled Legendre equation, in the order 0, d, d l.
The three roots must be distinct. -/
noncomputable def scaledLegendreRootEval : (scaledLegendre d l).toAffine.A ≃+* K × (K × K) :=
  (scaledLegendreRootEvalPi hd hl₀ hl₁).toRingEquiv.trans <|
    (RingEquiv.piCongrLeft (fun _ ↦ K) (finSuccEquiv 2)).trans <|
      RingEquiv.piOptionEquivProd.trans
        (RingEquiv.prodCongr (RingEquiv.refl K) (RingEquiv.piFinTwo fun _ ↦ K))

/-- Evaluation on the class of a polynomial is evaluation at each of the three ordered roots. -/
@[simp]
theorem scaledLegendreRootEval_mk (p : K[X]) :
    scaledLegendreRootEval hd hl₀ hl₁ (AdjoinRoot.mk _ p) =
      (p.eval 0, p.eval d, p.eval (d * l)) :=
  (rfl)

/-- The image of the native root of the cubic algebra is the triple of ordered roots. -/
@[simp]
theorem scaledLegendreRootEval_root :
    scaledLegendreRootEval hd hl₀ hl₁ (AdjoinRoot.root _) = (0, d, d * l) := by
  rw [← AdjoinRoot.mk_X, scaledLegendreRootEval_mk]
  simp

include hd hl₀ hl₁ in
/-- Equality of cubic algebra classes is detected by the three root evaluations. -/
theorem scaledLegendre_mk_eq_mk_iff {p q : K[X]} :
    AdjoinRoot.mk (scaledLegendre d l).toAffine.f p = AdjoinRoot.mk _ q ↔
      p.eval 0 = q.eval 0 ∧ p.eval d = q.eval d ∧ p.eval (d * l) = q.eval (d * l) := by
  let e := scaledLegendreRootEval hd hl₀ hl₁
  rw [← e.injective.eq_iff]
  simp only [e, scaledLegendreRootEval_mk, Prod.mk.injEq]

/-- A class is a unit exactly when all three root evaluations are nonzero, even for repeated
roots. -/
theorem isUnit_scaledLegendre_mk_iff (p : K[X]) :
    IsUnit (AdjoinRoot.mk (scaledLegendre d l).toAffine.f p) ↔
      p.eval 0 ≠ 0 ∧ p.eval d ≠ 0 ∧ p.eval (d * l) ≠ 0 := by
  have hX : IsCoprime X p ↔ IsUnit (p.eval 0) := by
    simpa only [map_zero, sub_zero] using (isCoprime_X_sub_C_iff_isUnit_eval p (a := 0))
  rw [AdjoinRoot.isUnit_mk_iff_isCoprime, f_scaledLegendre]
  simp only [IsCoprime.mul_left_iff, hX, isCoprime_X_sub_C_iff_isUnit_eval, isUnit_iff_ne_zero,
    and_assoc]

local notation "S" => Kˣ ⧸ MonoidHom.range (powMonoidHom 2 : Kˣ →* Kˣ)

private noncomputable def scaledLegendreSquareClassEquivPi :
    (scaledLegendre d l).toAffine.M ≃* (Fin 3 → S) :=
  (QuotientGroup.congrRangePowMonoidHom
    (Units.mapEquiv (scaledLegendreRootEvalPi hd hl₀ hl₁).toMulEquiv) 2).trans
      (Units.modPowPiEquiv (fun _ : Fin 3 ↦ K) 2)

private theorem scaledLegendreSquareClassEquivPi_mk (u : (scaledLegendre d l).toAffine.Aˣ)
    (i : Fin 3) :
    scaledLegendreSquareClassEquivPi hd hl₀ hl₁ (QuotientGroup.mk u) i =
      QuotientGroup.mk (MulEquiv.piUnits
        (Units.map (scaledLegendreRootEvalPi hd hl₀ hl₁).toMonoidHom u) i) := by
  simp only [scaledLegendreSquareClassEquivPi, MulEquiv.trans_apply,
    QuotientGroup.congrRangePowMonoidHom_mk, Units.modPowPiEquiv_mk]
  rfl

/-- The square classes of the scaled Legendre cubic algebra are the triples of square classes
over the base field, in the root order 0, d, d l. -/
noncomputable def scaledLegendreSquareClassEquiv :
    (scaledLegendre d l).toAffine.M ≃* S × (S × S) :=
  (scaledLegendreSquareClassEquivPi hd hl₀ hl₁).trans
    { toEquiv := (Equiv.piCongrLeft (fun _ ↦ S) (finSuccEquiv 2)).trans <|
        Equiv.piOptionEquivProd.trans (Equiv.prodCongr (Equiv.refl S) (finTwoArrowEquiv S))
      map_mul' := fun _ _ ↦ rfl }

private theorem scaledLegendreSquareClassEquiv_apply (a : (scaledLegendre d l).toAffine.M) :
    scaledLegendreSquareClassEquiv hd hl₀ hl₁ a =
      let v := scaledLegendreSquareClassEquivPi hd hl₀ hl₁ a
      (v 0, v 1, v 2) := (rfl)

/-- The three square classes of a polynomial unit are the classes of its three evaluations. -/
@[simp]
theorem scaledLegendreSquareClassEquiv_mk (p : K[X])
    (hu : IsUnit (AdjoinRoot.mk (scaledLegendre d l).toAffine.f p)) :
    scaledLegendreSquareClassEquiv hd hl₀ hl₁ (QuotientGroup.mk hu.unit) =
      let he := (isUnit_scaledLegendre_mk_iff (d := d) (l := l) p).mp hu
      (QuotientGroup.mk (Units.mk0 (p.eval 0) he.1),
       QuotientGroup.mk (Units.mk0 (p.eval d) he.2.1),
       QuotientGroup.mk (Units.mk0 (p.eval (d * l)) he.2.2)) := by
  have h (i : Fin 3) :
      scaledLegendreSquareClassEquivPi hd hl₀ hl₁ (QuotientGroup.mk hu.unit) i =
        QuotientGroup.mk (Units.mk0 (p.eval (![0, d, d * l] i)) (by
          have he := (isUnit_scaledLegendre_mk_iff (d := d) (l := l) p).mp hu
          fin_cases i
          · exact he.1
          · exact he.2.1
          · exact he.2.2)) := by
    rw [scaledLegendreSquareClassEquivPi_mk]
    apply congrArg QuotientGroup.mk
    apply Units.ext
    exact (congrArg (fun a ↦ scaledLegendreRootEvalPi hd hl₀ hl₁ a i) hu.unit_spec).trans
      (scaledLegendreRootEvalPi_mk hd hl₀ hl₁ p i)
  simp only [scaledLegendreSquareClassEquiv_apply, h]
  rfl

private theorem scaledLegendreSquareClassEquiv_mk_of_evals (p : K[X])
    (hu : IsUnit (AdjoinRoot.mk (scaledLegendre d l).toAffine.f p))
    {a b c : K} (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (h : (p.eval 0, p.eval d, p.eval (d * l)) = (a, b, c)) :
    scaledLegendreSquareClassEquiv hd hl₀ hl₁ (QuotientGroup.mk hu.unit) =
      (QuotientGroup.mk (Units.mk0 a ha), QuotientGroup.mk (Units.mk0 b hb),
       QuotientGroup.mk (Units.mk0 c hc)) := by
  rw [scaledLegendreSquareClassEquiv_mk]
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · exact congrArg QuotientGroup.mk (Units.ext (congrArg Prod.fst h))
  · exact congrArg QuotientGroup.mk (Units.ext (congrArg (fun t ↦ t.2.1) h))
  · exact congrArg QuotientGroup.mk (Units.ext (congrArg (fun t ↦ t.2.2) h))

private theorem eval_f_scaledLegendre (x : K) :
    (scaledLegendre d l).toAffine.f.eval x = x * (x - d) * (x - d * l) := by
  simp [f_scaledLegendre]

/-- The native norm of a cubic-algebra square class is the product of the three root classes. -/
theorem normM_eq_scaledLegendreSquareClassEquiv_prod (a : (scaledLegendre d l).toAffine.M) :
    (scaledLegendre d l).toAffine.normM a =
      let v := scaledLegendreSquareClassEquiv hd hl₀ hl₁ a
      v.1 * v.2.1 * v.2.2 := by
  induction a using QuotientGroup.induction_on with
  | H u =>
    simp only [normM_mk, scaledLegendreSquareClassEquiv_apply,
      scaledLegendreSquareClassEquivPi_mk, ← QuotientGroup.mk_mul]
    apply congrArg QuotientGroup.mk
    have h := Algebra.normUnits_eq_finprod_of_algEquiv (scaledLegendreRootEvalPi hd hl₀ hl₁) u
    rw [finprod_eq_prod_of_fintype, Fin.prod_univ_three] at h
    apply Units.ext
    simpa only [Algebra.coe_normUnits, Algebra.norm_self, MonoidHom.id_apply, Units.val_mul,
      Units.coe_map] using congrArg Units.val h

section Descent

variable [(scaledLegendre d l).IsElliptic]

/-- Away from the three roots, the split descent reads the three differences from the roots. -/
theorem scaledLegendreSquareClassEquiv_μX_of_ne {x : K} (hx₀ : x ≠ 0) (hx₁ : x ≠ d)
    (hx₂ : x ≠ d * l) :
    scaledLegendreSquareClassEquiv hd hl₀ hl₁ ((scaledLegendre d l).toAffine.μX x) =
      (QuotientGroup.mk (Units.mk0 x hx₀),
       QuotientGroup.mk (Units.mk0 (x - d) (sub_ne_zero.mpr hx₁)),
       QuotientGroup.mk (Units.mk0 (x - d * l) (sub_ne_zero.mpr hx₂))) := by
  have hx : (scaledLegendre d l).toAffine.f.eval x ≠ 0 := by
    rw [eval_f_scaledLegendre]
    exact mul_ne_zero (mul_ne_zero hx₀ (sub_ne_zero.mpr hx₁)) (sub_ne_zero.mpr hx₂)
  rw [μX_of_eval_f_ne_zero hx]
  exact scaledLegendreSquareClassEquiv_mk_of_evals hd hl₀ hl₁ _ _
    hx₀ (sub_ne_zero.mpr hx₁) (sub_ne_zero.mpr hx₂) (by simp)

/-- At the zero root, the first representative is the product of the two other differences. -/
@[simp]
theorem scaledLegendreSquareClassEquiv_μX_zero :
    scaledLegendreSquareClassEquiv hd hl₀ hl₁ ((scaledLegendre d l).toAffine.μX 0) =
      (QuotientGroup.mk (Units.mk0 (d ^ 2 * l) (mul_ne_zero (pow_ne_zero 2 hd) hl₀)),
       QuotientGroup.mk (Units.mk0 (-d) (neg_ne_zero.mpr hd)),
       QuotientGroup.mk (Units.mk0 (-(d * l)) (neg_ne_zero.mpr (mul_ne_zero hd hl₀)))) := by
  have hx : (scaledLegendre d l).toAffine.f.eval 0 = 0 := by
    rw [eval_f_scaledLegendre]
    simp
  rw [μX_of_eval_f_eq_zero hx]
  refine scaledLegendreSquareClassEquiv_mk_of_evals hd hl₀ hl₁ _ _ _ _ _ ?_
  refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> simp [Affine.fCofactor] <;> ring

/-- At the root d, the middle representative is the product of the two other differences. -/
@[simp]
theorem scaledLegendreSquareClassEquiv_μX_scale :
    scaledLegendreSquareClassEquiv hd hl₀ hl₁ ((scaledLegendre d l).toAffine.μX d) =
      (QuotientGroup.mk (Units.mk0 d hd),
       QuotientGroup.mk (Units.mk0 (d ^ 2 * (1 - l))
         (mul_ne_zero (pow_ne_zero 2 hd) (sub_ne_zero.mpr hl₁.symm))),
       QuotientGroup.mk (Units.mk0 (d * (1 - l))
         (mul_ne_zero hd (sub_ne_zero.mpr hl₁.symm)))) := by
  have hx : (scaledLegendre d l).toAffine.f.eval d = 0 := by
    rw [eval_f_scaledLegendre]
    simp
  rw [μX_of_eval_f_eq_zero hx]
  refine scaledLegendreSquareClassEquiv_mk_of_evals hd hl₀ hl₁ _ _ _ _ _ ?_
  refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> simp [Affine.fCofactor] <;> ring

/-- At the root d l, the last representative is the product of the two other differences. -/
@[simp]
theorem scaledLegendreSquareClassEquiv_μX_scale_mul :
    scaledLegendreSquareClassEquiv hd hl₀ hl₁ ((scaledLegendre d l).toAffine.μX (d * l)) =
      (QuotientGroup.mk (Units.mk0 (d * l) (mul_ne_zero hd hl₀)),
       QuotientGroup.mk (Units.mk0 (d * (l - 1)) (mul_ne_zero hd (sub_ne_zero.mpr hl₁))),
       QuotientGroup.mk (Units.mk0 (d ^ 2 * l * (l - 1))
         (mul_ne_zero (mul_ne_zero (pow_ne_zero 2 hd) hl₀) (sub_ne_zero.mpr hl₁)))) := by
  have hx : (scaledLegendre d l).toAffine.f.eval (d * l) = 0 := by
    rw [eval_f_scaledLegendre]
    simp
  rw [μX_of_eval_f_eq_zero hx]
  refine scaledLegendreSquareClassEquiv_mk_of_evals hd hl₀ hl₁ _ _ _ _ _ ?_
  refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> simp [Affine.fCofactor] <;> ring

/-- The split descent classes of a point have product one, including at the origin. -/
theorem scaledLegendreSquareClassEquiv_μ₀_prod (P : (scaledLegendre d l).toAffine.Point) :
    let v := scaledLegendreSquareClassEquiv hd hl₀ hl₁ ((scaledLegendre d l).toAffine.μ₀ P)
    v.1 * v.2.1 * v.2.2 = 1 := by
  exact (normM_eq_scaledLegendreSquareClassEquiv_prod hd hl₀ hl₁ _).symm.trans
    (normM_μ₀_eq_one P)

include hd hl₀ hl₁ in
private theorem scaledLegendre_μX_eq_one_iff (x : K) :
    (scaledLegendre d l).toAffine.μX x = 1 ↔
      IsSquare x ∧ IsSquare (x - d) ∧ IsSquare (x - d * l) := by
  have hsq (a : K) (ha : a ≠ 0) : (QuotientGroup.mk (Units.mk0 a ha) : S) = 1 ↔ IsSquare a := by
    simpa only [isSquare_iff_exists_sq, Units.val_mk0, eq_comm] using
      powMonoidHom_range_mk_eq_one_iff_exists_pow 2 (Units.mk0 a ha)
  let e := scaledLegendreSquareClassEquiv hd hl₀ hl₁
  have he : (scaledLegendre d l).toAffine.μX x = 1 ↔
      scaledLegendreSquareClassEquiv hd hl₀ hl₁ ((scaledLegendre d l).toAffine.μX x) = 1 :=
    ⟨fun h ↦ (congrArg e h).trans (map_one e),
      fun h ↦ e.injective (h.trans (map_one e).symm)⟩
  rw [he]
  rcases eq_or_ne x 0 with rfl | hx₀
  · simp only [scaledLegendreSquareClassEquiv_μX_zero, Prod.ext_iff, Prod.fst_one, Prod.snd_one,
      hsq, IsSquare.zero, zero_sub, true_and]
    have h : (-d) * (-(d * l)) = d ^ 2 * l := by ring
    rw [← h]
    exact ⟨fun H ↦ H.2, fun H ↦ ⟨H.1.mul H.2, H⟩⟩
  rcases eq_or_ne x d with hx | hx₁
  · subst x
    simp only [scaledLegendreSquareClassEquiv_μX_scale, Prod.ext_iff, Prod.fst_one, Prod.snd_one,
      hsq, sub_self, IsSquare.zero, true_and]
    have hdif : d - d * l = d * (1 - l) := by ring
    rw [hdif, pow_two, mul_assoc]
    exact ⟨fun H ↦ ⟨H.1, H.2.2⟩, fun H ↦ ⟨H.1, H.1.mul H.2, H.2⟩⟩
  rcases eq_or_ne x (d * l) with rfl | hx₂
  · simp only [scaledLegendreSquareClassEquiv_μX_scale_mul, Prod.ext_iff, Prod.fst_one,
      Prod.snd_one, hsq, sub_self, IsSquare.zero, and_true]
    have hdif : d * l - d = d * (l - 1) := by ring
    have h : (d * l) * (d * (l - 1)) = d ^ 2 * l * (l - 1) := by ring
    rw [hdif, ← h]
    exact ⟨fun H ↦ ⟨H.1, H.2.1⟩, fun H ↦ ⟨H.1, H.2, H.1.mul H.2⟩⟩
  simp only [scaledLegendreSquareClassEquiv_μX_of_ne hd hl₀ hl₁ hx₀ hx₁ hx₂,
    Prod.ext_iff, Prod.fst_one, Prod.snd_one, hsq]

/-- A nonsingular affine point of a scaled Legendre curve is a double exactly when all three
differences from the roots are squares in the base field. A zero difference is a square. -/
theorem scaledLegendre_halving_iff_squares [DecidableEq K] {x y : K}
    (h : (scaledLegendre d l).toAffine.Nonsingular x y) :
    (∃ Q : (scaledLegendre d l).toAffine.Point, 2 • Q = .some x y h) ↔
      IsSquare x ∧ IsSquare (x - d) ∧ IsSquare (x - d * l) := by
  obtain ⟨⟨⟨_, hd⟩, hl₀⟩, hl₁⟩ :
      (((2 : K) ≠ 0 ∧ d ≠ 0) ∧ l ≠ 0) ∧ l ≠ 1 := by
    simpa only [isUnit_iff_ne_zero, mul_ne_zero_iff, sub_ne_zero] using
      (isElliptic_scaledLegendre_iff d l).mp ‹_›
  rw [← scaledLegendre_μX_eq_one_iff hd hl₀ hl₁]
  constructor
  · rintro ⟨Q, hQ⟩
    simpa only [hQ, μ₀_some] using (scaledLegendre d l).toAffine.μ₀_two_nsmul Q
  · intro hμ
    exact (eq_two_smul_of_μ_eq_one h (by simpa only [μ_apply, μ₀_some] using hμ)).imp
      fun Q hQ ↦ hQ.symm

end Descent

end TauCeti

end

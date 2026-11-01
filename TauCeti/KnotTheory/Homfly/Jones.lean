/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.BraidWord.Jones
public import TauCeti.KnotTheory.Homfly.Reduced

/-!
# The Jones specialization of the HOMFLY polynomial

The HOMFLY polynomial `P` of a braid closure (`TauCeti.MarkovBraid.homfly`), with skein relation
`a P(L₊) - a⁻¹ P(L₋) = z P(L₀)`, specializes to the Jones polynomial: at `a = t⁻¹` and
`z = t ^ (1/2) - t ^ (-1/2)` its skein relation becomes the Jones skein relation
`t⁻¹ V(L₊) - t V(L₋) = (t ^ (1/2) - t ^ (-1/2)) V(L₀)`. In the Kauffman bracket variable `A`, with
`t = A⁻⁴`, the substitution is `a = A⁴` and `z = A⁻² - A²`.

This file proves the specialization for every braid closure, comparing the HOMFLY polynomial with
the braid route to the Jones polynomial, the writhe-normalized Markov trace of the Jones
representation `TauCeti.MarkovBraid.jonesTrace`, and through it with the diagram route, the
Jones polynomial of the closed braid diagram. The HOMFLY polynomial lies in
`K[a, a⁻¹, z, z⁻¹]` for a field `K`, with `z` the inner and `a` the outer Laurent variable. The
target is any commutative ring `R` receiving a ring homomorphism `φ : K →+* R`, with a unit `A`
for which `A⁻² - A²` is a unit `u`, so that `z⁻¹` can be evaluated. The substitution is then
`LaurentPolynomial.eval₂ (LaurentPolynomial.eval₂ φ u) (A ^ 4)`.

Both sides are Markov invariants satisfying the same skein relation, both are multiplied by the
loop value `δ = -(A² + A⁻²)` when an uncrossed strand is added, and both take the value `δ` on the
unknot: the quantum dimension `(a - a⁻¹) z⁻¹` specializes to `δ`
(`TauCeti.KnotTheory.eval₂_homflyUnknot_jones`). By the uniqueness of skein invariants,
`TauCeti.MarkovBraid.eq_of_skein`, they agree (`TauCeti.MarkovBraid.eval₂_homfly_jones`).

The unknot has unreduced HOMFLY polynomial `(a - a⁻¹) z⁻¹` and Jones trace `δ`, while the reduced
HOMFLY polynomial `TauCeti.MarkovBraid.reducedHomfly` and the Jones polynomial give it the value
`1`. So for the reduced polynomial the braid comparison reads `δ * P(A⁴, A⁻² - A²) = jonesTrace`
(`TauCeti.MarkovBraid.jonesDelta_mul_eval₂_reducedHomfly_jones`). The diagram route,
`TauCeti.BraidWord.jonesTrace_toBraid_eq_eval₂_jonesPolynomial`, is `jonesTrace = δ * V(t)` at
`t ^ (1/2) = A⁻²` for the Jones polynomial `V` of the closed diagram of a braid word. Cancelling
`δ` gives the classical statement `P(t⁻¹, t ^ (1/2) - t ^ (-1/2)) = V(t)`
(`TauCeti.BraidWord.eval₂_reducedHomfly_toBraid`). It holds without any condition on `δ`: the
cancellation is made in the universal coefficient ring, `K[A, A⁻¹]` with `A⁻² - A²` inverted, which
is a domain in which `δ ≠ 0`, and the result is then mapped to `R`. Mapping commutes with the
evaluation of Laurent polynomials by `LaurentPolynomial.hom_eval₂`.

## Main results

* `TauCeti.KnotTheory.eval₂_homflyUnknot_jones`: the quantum dimension specializes to `δ`.
* `TauCeti.MarkovBraid.eval₂_homfly_jones`: the specialized HOMFLY polynomial of a braid closure
  is the writhe-normalized Markov trace of the Jones representation.
* `TauCeti.MarkovBraid.jonesDelta_mul_eval₂_reducedHomfly_jones`: the same for the reduced HOMFLY
  polynomial, up to the unknot normalization `δ`.
* `TauCeti.BraidWord.eval₂_reducedHomfly_toBraid`: the specialized reduced HOMFLY polynomial of the
  closure of a braid word is the Jones polynomial of the closed diagram.

## References

* P. Freyd, D. Yetter, J. Hoste, W. B. R. Lickorish, K. Millett, A. Ocneanu, *A new polynomial
  invariant of knots and links*, Bull. Amer. Math. Soc. 12 (1985), 239–246.
* V. F. R. Jones, *Hecke algebra representations of braid groups and link polynomials*,
  Ann. of Math. 126 (1987), 335–388, Sections 4–6 (the two-variable polynomial from Hecke
  algebra traces, and its specializations).
* W. B. R. Lickorish, *An Introduction to Knot Theory*, Springer GTM 175 (1997), Chapter 15 (the
  HOMFLY polynomial and its specialization to the Jones polynomial).
-/

public section

noncomputable section

namespace TauCeti

open LaurentPolynomial TemperleyLieb

variable {K : Type*} [Field K] {R : Type*} [CommRing R]

namespace KnotTheory

/-- **The quantum dimension specializes to the loop value.** At `a = A⁴` and `z = A⁻² - A²` the
HOMFLY unknot value `(a - a⁻¹) z⁻¹` is `δ = -(A² + A⁻²)`. -/
theorem eval₂_homflyUnknot_jones (φ : K →+* R) (A u : Rˣ)
    (hu : (u : R) = ((A⁻¹ : Rˣ) : R) ^ 2 - (A : R) ^ 2) :
    eval₂ (eval₂ φ u) (A ^ 4) (homflyUnknot K) = jonesDelta A := by
  simp only [homflyUnknot_def, map_mul, map_sub, eval₂_C, eval₂_T, zpow_one, zpow_neg_one]
  rw [Units.mul_inv_eq_iff_eq_mul, hu, jonesDelta_def]
  simp only [Units.val_pow_eq_pow_val, ← inv_pow]
  ring

end KnotTheory

namespace MarkovBraid

open KnotTheory

/-- **The Jones specialization of the HOMFLY polynomial.** At `a = A⁴` and `z = A⁻² - A²`, that is
`a = t⁻¹` and `z = t ^ (1/2) - t ^ (-1/2)` for `t = A⁻⁴`, the HOMFLY polynomial of the closure of a
braid is the writhe-normalized Markov trace of its Jones representation. Both have the value
`δ = -(A² + A⁻²)` on the unknot. -/
theorem eval₂_homfly_jones (φ : K →+* R) (A u : Rˣ)
    (hu : (u : R) = ((A⁻¹ : Rˣ) : R) ^ 2 - (A : R) ^ 2) (β : MarkovBraid) :
    eval₂ (eval₂ φ u) (A ^ 4) (β.homfly K) = β.jonesTrace A := by
  have hδ := eval₂_homflyUnknot_jones φ A u hu
  refine congrFun (eq_of_skein (A ^ 4) (((A⁻¹ : Rˣ) : R) ^ 2 - (A : R) ^ 2) (jonesDelta A)
    (F := fun β ↦ eval₂ (eval₂ φ u) (A ^ 4) (β.homfly K)) (G := fun β ↦ β.jonesTrace A)
    (fun β γ h ↦ by rw [h.homfly_eq K]) (fun β γ h ↦ h.jonesTrace_eq A)
    (fun n c i ↦ ?_) (fun n c i ↦ by simpa using jonesTrace_skein A 1 c i)
    (fun n b ↦ by simp only [homfly_strandIncl, map_mul, hδ, smul_eq_mul])
    (fun n b ↦ jonesTrace_strandIncl A b)
    (by simp only [homfly_one, zero_add, pow_one, hδ, jonesTrace_one_strand])) β
  -- The HOMFLY skein relation, specialized.
  have h := congrArg (eval₂ (eval₂ φ u) (A ^ 4)) (homfly_skein K 1 c i)
  simp only [map_sub, map_mul, eval₂_T, eval₂_C, zpow_one, zpow_neg_one, one_mul] at h
  simpa only [smul_eq_mul, ← hu] using h

/-- **The Jones specialization of the reduced HOMFLY polynomial.** At `a = A⁴` and `z = A⁻² - A²`,
the reduced HOMFLY polynomial of the closure of a braid, multiplied by the loop value
`δ = -(A² + A⁻²)`, is the writhe-normalized Markov trace of its Jones representation. -/
theorem jonesDelta_mul_eval₂_reducedHomfly_jones (φ : K →+* R) (A u : Rˣ)
    (hu : (u : R) = ((A⁻¹ : Rˣ) : R) ^ 2 - (A : R) ^ 2) (β : MarkovBraid) :
    jonesDelta A * eval₂ (eval₂ φ u) (A ^ 4) (β.reducedHomfly K) = β.jonesTrace A := by
  rw [← eval₂_homfly_jones φ A u hu, ← homflyUnknot_mul_reducedHomfly, map_mul,
    eval₂_homflyUnknot_jones φ A u hu]

end MarkovBraid

namespace BraidWord

open KnotTheory

/-- Where the loop value `δ` is not a zero divisor, the specialized reduced HOMFLY polynomial of a
closed braid word is the evaluated Jones polynomial of the closed diagram: both are `jonesTrace`
divided by `δ`. -/
private theorem eval₂_reducedHomfly_toBraid_of_isLeftRegular (φ : K →+* R) (A u : Rˣ)
    (hu : (u : R) = ((A⁻¹ : Rˣ) : R) ^ 2 - (A : R) ^ 2) (hδ : IsLeftRegular (jonesDelta A))
    {n : ℕ} (w : BraidWord (n + 1)) :
    eval₂ (eval₂ φ u) (A ^ 4) ((⟨n, w.toBraid⟩ : MarkovBraid).reducedHomfly K) =
      eval₂ (Int.castRingHom R) (A⁻¹ ^ 2) w.closure.jonesPolynomial :=
  hδ <| (MarkovBraid.jonesDelta_mul_eval₂_reducedHomfly_jones φ A u hu _).trans
    (jonesTrace_toBraid_eq_eval₂_jonesPolynomial A w)

/-- **The reduced HOMFLY polynomial specializes to the Jones polynomial.** At `a = A⁴` and
`z = A⁻² - A²`, that is `a = t⁻¹` and `z = t ^ (1/2) - t ^ (-1/2)` for `t = A⁻⁴`, the reduced HOMFLY
polynomial of the closure of the braid represented by a braid word `w` is the Jones polynomial of
the closed diagram of `w`, evaluated at `t ^ (1/2) = A⁻²`. This holds in every commutative ring
receiving the coefficient field, with no condition on the loop value `δ = -(A² + A⁻²)`. -/
theorem eval₂_reducedHomfly_toBraid (φ : K →+* R) (A u : Rˣ)
    (hu : (u : R) = ((A⁻¹ : Rˣ) : R) ^ 2 - (A : R) ^ 2) {n : ℕ} (w : BraidWord (n + 1)) :
    eval₂ (eval₂ φ u) (A ^ 4) ((⟨n, w.toBraid⟩ : MarkovBraid).reducedHomfly K) =
      eval₂ (Int.castRingHom R) (A⁻¹ ^ 2) w.closure.jonesPolynomial := by
  -- The universal case: `K[A, A⁻¹]` with `A⁻² - A²` inverted is a domain in which `δ ≠ 0`.
  set s : LaurentPolynomial K := T (-2) - T 2 with hs_def
  have hs : s ≠ 0 := fun h ↦ by simpa [s] using congrArg (fun p ↦ p.coeff 2) h
  have hinj := IsLocalization.injective (Localization.Away s)
    (powers_le_nonZeroDivisors_of_noZeroDivisors hs)
  have : IsDomain (Localization.Away s) := Localization.Away.isDomain hs
  set ι := algebraMap (LaurentPolynomial K) (Localization.Away s)
  set a : (Localization.Away s)ˣ := Units.map (ι : _ →* _) (genericUnit K)
  set v : (Localization.Away s)ˣ := (IsLocalization.Away.algebraMap_isUnit s).unit
  have ha : (a : Localization.Away s) = ι (T 1) := by simp [a]
  have ha' : ((a⁻¹ : (Localization.Away s)ˣ) : Localization.Away s) = ι (T (-1)) := by simp [a]
  have hT (m : ℤ) : (T m : LaurentPolynomial K) ^ 2 = T (2 * m) := by
    rw [T_pow]
    norm_cast
  have hv : (v : Localization.Away s) = ((a⁻¹ : (Localization.Away s)ˣ) : _) ^ 2 - (a : _) ^ 2 := by
    rw [IsUnit.unit_spec, ha, ha', ← map_pow, ← map_pow, ← map_sub, hT, hT]
    exact congrArg ι (by norm_num [s])
  have hδ : IsLeftRegular (jonesDelta a) := by
    refine (IsRegular.of_ne_zero fun h ↦ ?_).left
    rw [jonesDelta_def, ha, ha', ← map_pow, ← map_pow, ← map_add, ← map_neg, ← map_zero ι,
      hT, hT] at h
    simpa using congrArg (fun p ↦ p.coeff 2) (hinj h)
  have key := eval₂_reducedHomfly_toBraid_of_isLeftRegular (ι.comp C) a v hv hδ w
  -- Transport along the map from the universal ring sending `A` to `A`.
  have hes : eval₂ φ A s = u := by
    simp [hs_def, hu, ← inv_pow]
  set ψ : Localization.Away s →+* R := IsLocalization.Away.lift s (hes ▸ u.isUnit)
  have hψι (p : LaurentPolynomial K) : ψ (ι p) = eval₂ φ A p := IsLocalization.Away.lift_eq s _ p
  have hψa : Units.map (ψ : _ →* R) a = A := Units.ext (by simp [a, hψι])
  have hψv : Units.map (ψ : _ →* R) v = u :=
    Units.ext (by simpa [v] using (hψι s).trans hes)
  have hψC : ψ.comp (ι.comp C) = φ := RingHom.ext fun k ↦ by simp [hψι]
  have hinner : ψ.comp (eval₂ (ι.comp C) v) = eval₂ φ u :=
    RingHom.ext fun p ↦ by rw [RingHom.comp_apply, hom_eval₂, hψC, hψv]
  have h := congrArg ψ key
  rw [hom_eval₂, hom_eval₂, hinner, RingHom.ext_int (ψ.comp (Int.castRingHom _))] at h
  simpa [hψa] using h

end BraidWord

end TauCeti

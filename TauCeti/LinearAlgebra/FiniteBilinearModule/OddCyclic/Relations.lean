/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wentao Li
-/
module

public import TauCeti.LinearAlgebra.FiniteBilinearModule.OddCyclic.Basic
import TauCeti.Data.ZMod.SumSquares
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# Relations between odd cyclic generators

For a fixed power of an odd prime, doubling an odd cyclic generator removes its
unit coefficient's square class: any two nondegenerate odd cyclic generators of
that order have isometric orthogonal doubles. A sum-of-two-squares representation
of the coefficient ratio gives the rotation between them.

The rotation preserves the half-norm quadratic form, and canonical conversion
to a bilinear isometry gives the corresponding discriminant relation.

## References

* V. V. Nikulin, *Integral symmetric bilinear forms and some of their applications*,
  Proposition 1.8.2(a), (k).
-/

public section

namespace TauCeti.FiniteQuadraticModule

private def oddCyclicPairRotation (m : ℕ) (a b : ZMod m) :
    (ZMod m × ZMod m) →+ (ZMod m × ZMod m) where
  toFun x := (a * x.1 - b * x.2, b * x.1 + a * x.2)
  map_zero' := by simp
  map_add' x y := by
    ext <;> simp only [Prod.fst_add, Prod.snd_add] <;> ring

private theorem oddCyclicPairRotation_quadratic (m : ℕ) (hm : Odd m) (θ η : ℤ)
    (a b : ZMod m) (hscale : (θ : ZMod m) * (a ^ 2 + b ^ 2) = η)
    (x : ((oddCyclic m hm η).prod (oddCyclic m hm η)).carrier) :
    ((oddCyclic m hm θ).prod (oddCyclic m hm θ)).quadratic
        (oddCyclicPairRotation m a b x) =
      ((oddCyclic m hm η).prod (oddCyclic m hm η)).quadratic x := by
  -- Expose both cyclic carriers for the polynomial calculation in `ZMod m`.
  change ZMod m × ZMod m at x
  rcases x with ⟨x, y⟩
  dsimp [oddCyclicPairRotation]
  erw [prod_quadratic, prod_quadratic, oddCyclic_quadratic, oddCyclic_quadratic,
    oddCyclic_quadratic, oddCyclic_quadratic]
  rw [← map_add, ← map_add]
  congr 1
  linear_combination (((m + 1) / 2 : ℕ) : ZMod m) * (x ^ 2 + y ^ 2) * hscale

/-- The doubled odd cyclic relation of Nikulin 1.8.2(a): any two unit coefficients
at the same odd prime-power order give isometric orthogonal doubles.
The exponent-zero case is included. -/
noncomputable def oddCyclicProdSelfIsometry (p k : ℕ) [Fact p.Prime] (hp : Odd p)
    {θ η : ℤ} (hθ : IsCoprime ((p ^ k : ℕ) : ℤ) θ)
    (hη : IsCoprime ((p ^ k : ℕ) : ℤ) η) :
    Isometry ((oddCyclic (p ^ k) hp.pow θ).prod (oddCyclic (p ^ k) hp.pow θ))
      ((oddCyclic (p ^ k) hp.pow η).prod (oddCyclic (p ^ k) hp.pow η)) :=
  Classical.choice <| by
    obtain ⟨Θ, hΘ⟩ := (ZMod.coe_int_isUnit_iff_isCoprime θ (p ^ k)).mpr hθ
    obtain ⟨Η, hΗ⟩ := (ZMod.coe_int_isUnit_iff_isCoprime η (p ^ k)).mpr hη
    obtain ⟨a, b, hab⟩ := ZMod.exists_sq_add_sq_eq_of_isUnit_prime_pow p k hp
      ((Units.isUnit Η).mul (Units.isUnit Θ⁻¹))
    have hscale : (θ : ZMod (p ^ k)) * (a ^ 2 + b ^ 2) = η := by
      rw [hab, ← hΘ, ← hΗ, mul_left_comm, Units.mul_inv, mul_one]
    let g : Hom ((oddCyclic (p ^ k) hp.pow η).prod (oddCyclic (p ^ k) hp.pow η))
        ((oddCyclic (p ^ k) hp.pow θ).prod (oddCyclic (p ^ k) hp.pow θ)) :=
      { toLinearMap := (oddCyclicPairRotation (p ^ k) a b).toIntLinearMap
        map_app' := fun x ↦ by
          simpa only [LinearMap.toFun_eq_coe, AddMonoidHom.coe_toIntLinearMap] using
            oddCyclicPairRotation_quadratic (p ^ k) hp.pow θ η a b hscale x }
    have hsource : ((oddCyclic (p ^ k) hp.pow η).prod
        (oddCyclic (p ^ k) hp.pow η)).IsNondegenerate :=
      (isNondegenerate_prod _ _).mpr
        ⟨(isNondegenerate_oddCyclic_iff _ _ _).mpr hη,
          (isNondegenerate_oddCyclic_iff _ _ _).mpr hη⟩
    exact ⟨(g.toIsometryOfNondegenerate hsource rfl).symm⟩

end TauCeti.FiniteQuadraticModule

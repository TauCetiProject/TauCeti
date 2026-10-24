/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wentao Li
-/
module

public import Mathlib.NumberTheory.LegendreSymbol.Basic
public import TauCeti.LinearAlgebra.FiniteBilinearModule.OddCyclic.Basic
import TauCeti.LinearAlgebra.FiniteBilinearModule.OddCyclic.Classification
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

Combined with the isometry of generators with the same Legendre symbol, the doubled
relation shows that orthogonal sums `q_a ⊕ q_b` and `q_c ⊕ q_d` of generators of the same
order, with coefficients prime to `p`, are isometric whenever `(a/p)(b/p) = (c/p)(d/p)`.

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

/-- **The binary relation at an odd prime.** Orthogonal sums `q_a ⊕ q_b` and `q_c ⊕ q_d` of odd
cyclic generators of the same order `p^e` are isometric as soon as `(a/p)(b/p) = (c/p)(d/p)`.
It follows from Nikulin's doubled relation `q_θ ⊕ q_θ ≅ q_η ⊕ q_η`. -/
theorem nonempty_isometry_oddCyclic_prod {p : ℕ} [Fact p.Prime] (hp : Odd p) (e : ℕ)
    {a b c d : ℤ} (ha : IsCoprime (p : ℤ) a) (hb : IsCoprime (p : ℤ) b)
    (hc : IsCoprime (p : ℤ) c) (hd : IsCoprime (p : ℤ) d)
    (h : legendreSym p a * legendreSym p b = legendreSym p c * legendreSym p d) :
    Nonempty (Isometry ((oddCyclic (p ^ e) hp.pow a).prod (oddCyclic (p ^ e) hp.pow b))
      ((oddCyclic (p ^ e) hp.pow c).prod (oddCyclic (p ^ e) hp.pow d))) := by
  have hχ (t : ℤ) (ht : IsCoprime (p : ℤ) t) : legendreSym p t = 1 ∨ legendreSym p t = -1 :=
    legendreSym.eq_one_or_neg_one p ((ZMod.coe_int_isUnit_iff_isCoprime t p).2 ht).ne_zero
  have hcyc := fun {s t : ℤ} (hs : IsCoprime (p : ℤ) s) (ht : IsCoprime (p : ℤ) t)
    (hst : legendreSym p s = legendreSym p t) ↦
      nonempty_isometry_oddCyclic_of_legendreSym_eq hp e hs ht hst
  -- Every `q_s ⊕ q_t` is isometric to `q_1 ⊕ q_{st}`.
  have key (s t : ℤ) (hs : IsCoprime (p : ℤ) s) (ht : IsCoprime (p : ℤ) t) :
      Nonempty (Isometry ((oddCyclic (p ^ e) hp.pow s).prod (oddCyclic (p ^ e) hp.pow t))
        ((oddCyclic (p ^ e) hp.pow 1).prod (oddCyclic (p ^ e) hp.pow (s * t)))) := by
    have h1 : IsCoprime (p : ℤ) 1 := isCoprime_one_right
    have hst : IsCoprime (p : ℤ) (s * t) := hs.mul_right ht
    rcases hχ s hs with hs1 | hs1
    · obtain ⟨f⟩ := hcyc hs h1 (by rw [hs1, legendreSym.at_one])
      obtain ⟨g⟩ := hcyc ht hst (by rw [legendreSym.mul, hs1, one_mul])
      exact ⟨f.prod g⟩
    rcases hχ t ht with ht1 | ht1
    · obtain ⟨f⟩ := hcyc ht h1 (by rw [ht1, legendreSym.at_one])
      obtain ⟨g⟩ := hcyc hs hst (by rw [legendreSym.mul, ht1, mul_one])
      exact ⟨(QuadraticMap.IsometryEquiv.prodComm _ _).trans (f.prod g)⟩
    · obtain ⟨f⟩ := hcyc ht hs (by rw [hs1, ht1])
      obtain ⟨g⟩ := hcyc h1 hst (by rw [legendreSym.mul, hs1, ht1, legendreSym.at_one]; norm_num)
      have hpe (u : ℤ) (hu : IsCoprime (p : ℤ) u) : IsCoprime ((p ^ e : ℕ) : ℤ) u := by
        simpa using hu.pow_left
      exact ⟨((QuadraticMap.IsometryEquiv.refl _).prod f).trans
        ((oddCyclicProdSelfIsometry p e hp (hpe s hs) (hpe 1 h1)).trans
          ((QuadraticMap.IsometryEquiv.refl _).prod g))⟩
  obtain ⟨f⟩ := key a b ha hb
  obtain ⟨g⟩ := key c d hc hd
  obtain ⟨u⟩ := hcyc (ha.mul_right hb) (hc.mul_right hd)
    (by rw [legendreSym.mul, legendreSym.mul, h])
  exact ⟨f.trans (((QuadraticMap.IsometryEquiv.refl _).prod u).trans g.symm)⟩

end TauCeti.FiniteQuadraticModule

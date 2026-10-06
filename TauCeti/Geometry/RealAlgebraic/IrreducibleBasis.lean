/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Polynomial.IrreducibleBasis
public import TauCeti.Geometry.RealAlgebraic.SignInvariant
public import TauCeti.RingTheory.MvPolynomial.OrderAt
import TauCeti.Algebra.MvPolynomial.Equiv
import Mathlib.Algebra.MvPolynomial.Nilpotent
import Mathlib.Basic.Sign.Basic

/-!
# Reconstructing signs and orders from an irreducible basis

An irreducible basis reconstructs each input polynomial as its content, a unit, and a
product of powers of basis members. Over a polynomial coefficient ring over a domain,
that unit is a nonzero scalar. Thus the signs of the content and the basis determine
the sign of the input, and its ambient Taylor order is the order of its content plus
the weighted sum of the orders of its basis factors.

The distinguished variable is coordinate zero, through `MvPolynomial.finSuccEquiv`.
The content is evaluated at the remaining coordinates. In particular, constant signs
or constant ambient orders for the basis and contents transfer to the original family.
The statements include zero inputs, vanishing contents, and empty bases. Orders are
ambient Taylor orders, including infinity for the zero polynomial; no restriction to
a cell is taken before computing them.

## References

S. McCallum, *An improved projection operation for cylindrical algebraic decomposition*,
Springer (1998), 242–268, Sections 2–3 (basis preprocessing and order-invariance).
-/

public section

open MvPolynomial Polynomial

namespace Finset.IsIrreducibleBasis

variable {R : Type*} [CommRing R] [UniqueFactorizationMonoid R] {n : ℕ}
  [NormalizedGCDMonoid (MvPolynomial (Fin n) R)]
  {F B : Finset (Polynomial (MvPolynomial (Fin n) R))}

section Orders

variable [IsDomain R]

/-- The ambient order of an input is the order of its content plus the sum of the
orders of the basis factors, weighted by their exponents in its factorization.
The same exponents work at every point, including where the content vanishes. -/
theorem exists_orderAt_eq_content_add_sum (hB : F.IsIrreducibleBasis B)
    {f : Polynomial (MvPolynomial (Fin n) R)} (hf : f ∈ F) :
    ∃ e : Polynomial (MvPolynomial (Fin n) R) → ℕ, ∀ a : Fin (n + 1) → R,
      ((finSuccEquiv R n).symm f).orderAt a =
        f.content.orderAt (Fin.tail a) +
          ∑ b ∈ B, e b • ((finSuccEquiv R n).symm b).orderAt a := by
  obtain ⟨u, e, hfe⟩ := hB.exists_eq_C_content_mul_unit_mul_prod hf
  refine ⟨e, fun a ↦ ?_⟩
  have hC (g : MvPolynomial (Fin n) R) :
      (finSuccEquiv R n).symm (Polynomial.C g) = rename Fin.succ g := by
    simpa only [MvPolynomial.finSuccEquiv'_zero, Fin.succAbove_zero] using
      finSuccEquiv'_symm_C (0 : Fin (n + 1)) g
  have hu : (rename Fin.succ (u : MvPolynomial (Fin n) R)).orderAt a = 0 :=
    orderAt_eq_zero_iff.mpr ((u.isUnit.map (rename Fin.succ)).map (MvPolynomial.eval a)).ne_zero
  conv_lhs => rw [hfe]
  simp only [map_mul, hC, map_prod, map_pow, orderAt_mul, orderAt_prod,
    orderAt_pow, hu, add_zero, orderAt_rename (Fin.succ_injective n),
    Fin.tail_def, Function.comp_def]

/-- Constant ambient orders for the content and basis factors imply constant ambient
order for each input polynomial. No connectedness assumption is needed. -/
theorem orderAt_eq (hB : F.IsIrreducibleBasis B)
    {f : Polynomial (MvPolynomial (Fin n) R)} (hf : f ∈ F)
    {a a' : Fin (n + 1) → R}
    (hc : f.content.orderAt (Fin.tail a) = f.content.orderAt (Fin.tail a'))
    (hb : ∀ b ∈ B, ((finSuccEquiv R n).symm b).orderAt a =
      ((finSuccEquiv R n).symm b).orderAt a') :
    ((finSuccEquiv R n).symm f).orderAt a =
      ((finSuccEquiv R n).symm f).orderAt a' := by
  obtain ⟨e, he⟩ := hB.exists_orderAt_eq_content_add_sum hf
  rw [he a, he a', hc]
  exact congrArg (_ + ·) (Finset.sum_congr rfl fun b hmem ↦ congrArg (e b • ·) (hb b hmem))

end Orders

section Signs

variable [LinearOrder R] [IsStrictOrderedRing R]

/-- The signs of the content and the basis factors reconstruct the sign of each
input, with one fixed nonzero scalar sign and fixed exponents. The identity holds
also on zero fibers, so nullified inputs need no separate sign convention. -/
theorem exists_sign_eval_eq_content_mul_prod (hB : F.IsIrreducibleBasis B)
    {f : Polynomial (MvPolynomial (Fin n) R)} (hf : f ∈ F) :
    ∃ ε : SignType, ε ≠ 0 ∧ ∃ e : Polynomial (MvPolynomial (Fin n) R) → ℕ,
      ∀ a : Fin (n + 1) → R,
        SignType.sign (MvPolynomial.eval a ((finSuccEquiv R n).symm f)) =
          SignType.sign (MvPolynomial.eval (Fin.tail a) f.content) * ε *
            ∏ b ∈ B, SignType.sign (MvPolynomial.eval a ((finSuccEquiv R n).symm b)) ^ e b := by
  obtain ⟨u, e, hfe⟩ := hB.exists_eq_C_content_mul_unit_mul_prod hf
  obtain ⟨r, hr, hur⟩ := isUnit_iff_eq_C_of_isReduced.mp u.isUnit
  refine ⟨SignType.sign r, by simpa using hr.ne_zero, e, fun a ↦ ?_⟩
  have hC (g : MvPolynomial (Fin n) R) :
      (finSuccEquiv R n).symm (Polynomial.C g) = rename Fin.succ g := by
    simpa only [MvPolynomial.finSuccEquiv'_zero, Fin.succAbove_zero] using
      finSuccEquiv'_symm_C (0 : Fin (n + 1)) g
  conv_lhs => rw [hfe, hur, map_mul, hC, map_prod]
  simp only [map_pow, MvPolynomial.eval_mul, eval_rename, MvPolynomial.eval_prod,
    MvPolynomial.eval_C, sign_mul, Fin.tail_def, Function.comp_def]
  simp only [← signHom_apply, map_prod, map_pow]

/-- Sign-invariance of the content and the basis on a set implies sign-invariance
of every input on that set. The set may be disconnected, and may contain points
at which some basis members or the content vanish. -/
theorem signInvariant_eval (hB : F.IsIrreducibleBasis B)
    {f : Polynomial (MvPolynomial (Fin n) R)} (hf : f ∈ F)
    {S : Set (Fin (n + 1) → R)}
    (hc : TauCeti.SignInvariant (fun a ↦ MvPolynomial.eval (Fin.tail a) f.content) S)
    (hb : ∀ b ∈ B,
      TauCeti.SignInvariant (fun a ↦ MvPolynomial.eval a ((finSuccEquiv R n).symm b)) S) :
    TauCeti.SignInvariant (fun a ↦ MvPolynomial.eval a ((finSuccEquiv R n).symm f)) S := by
  obtain ⟨ε, _, e, he⟩ := hB.exists_sign_eval_eq_content_mul_prod hf
  simp only [TauCeti.signInvariant_def] at hc hb ⊢
  intro a ha a' ha'
  rw [he a, he a', hc a ha a' ha']
  exact congrArg (_ * ·) (Finset.prod_congr rfl fun b hmem ↦
    congrArg (· ^ e b) (hb b hmem a ha a' ha'))

end Signs

end Finset.IsIrreducibleBasis

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Polynomial.IrreducibleBasis.Basic
public import TauCeti.RingTheory.MvPolynomial.OrderAt
import TauCeti.Algebra.MvPolynomial.Equiv

/-!
# Reconstructing ambient orders from an irreducible basis

An irreducible basis reconstructs each input polynomial as its content, a unit, and a
product of powers of basis members. Over a polynomial coefficient ring over a domain,
the unit has order zero, so the ambient Taylor order of the input is the order of its
content plus the weighted sum of the orders of its basis factors. Thus constant ambient
orders for the content and basis transfer to the input family.

The distinguished variable is coordinate zero, through `MvPolynomial.finSuccEquiv`.
The content is evaluated at the remaining coordinates. The statements include zero
inputs, vanishing contents, and empty bases. Orders are ambient Taylor orders, including
infinity for the zero polynomial; no restriction to a cell is taken before computing them.

## References

S. McCallum, *An improved projection operation for cylindrical algebraic decomposition*,
Springer (1998), 242–268, Sections 2–3 (basis preprocessing and order-invariance).
-/

public section

open MvPolynomial Polynomial

namespace Finset.IsIrreducibleBasis

variable {R : Type*} [CommRing R] {n : ℕ}
  [UniqueFactorizationMonoid (MvPolynomial (Fin n) R)]
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

end Finset.IsIrreducibleBasis

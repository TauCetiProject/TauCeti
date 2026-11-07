/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.LocalRing.ResidueField.Fiber
public import Mathlib.RingTheory.Smooth.Basic
import Mathlib.RingTheory.Smooth.Flat
import TauCeti.Algebra.Regular.SMul
import TauCeti.RingTheory.Flat.FiberRegular
import TauCeti.RingTheory.Smooth.NoetherianDescent

/-!
# Nonzerodivisors on the fibres of a smooth algebra

Let `B` be a smooth algebra over a commutative ring `R`, and let `b ∈ B`. If `1 ⊗ b` is a
nonzerodivisor on the fibre ring `κ(p) ⊗[R] B` for every prime `p` of `R`, then `b` is a
nonzerodivisor on `B` (`Algebra.Smooth.isSMulRegular_of_forall_isSMulRegular_fiber`). No
noetherian hypothesis is made on `R` or `B`.

Geometrically, for a smooth morphism `X ⟶ S`, a function on `X` which is a nonzerodivisor on every
fibre is a nonzerodivisor on `X`. This is the local algebra behind the fibre criterion for relative
effective Cartier divisors over an arbitrary base.

Over a noetherian base this is the local flatness argument of
`Module.Flat.isSMulRegular_of_isSMulRegular_quotient`. The general case is reduced to it by a
noetherian model, which is where smoothness is used: `B` is the base change `R ⊗[A] B₀` of a
smooth algebra `B₀` over a noetherian ring `A`, in such a way that `b` is the image of some
`b₀ ∈ B₀` (`Algebra.Smooth.exists_isNoetherianRing_and_eq_one_tmul`). Then `B₀` is noetherian and
flat over `A`, and `Module.Flat.isSMulRegular_one_tmul_of_forall_isSMulRegular_fiber` applies to
the model.

## Main results

* `Algebra.Smooth.isSMulRegular_of_forall_isSMulRegular_fiber`: the statement for smooth
  algebras.

## References

* H. Matsumura, *Commutative Ring Theory*, Theorem 22.5 and its Corollary, for the noetherian
  case.
* The Stacks Project, *Divisors*, section *Relative effective Cartier divisors*, for the fibre
  criterion this serves.
-/

public section

open TensorProduct Algebra.TensorProduct

universe u

namespace Algebra.Smooth

/-- **Nonzerodivisors on the fibres of a smooth algebra.** Let `B` be a smooth `R`-algebra and
`b ∈ B`. If `1 ⊗ b` is a nonzerodivisor on the fibre ring `κ(p) ⊗[R] B` for every prime `p` of
`R`, then `b` is a nonzerodivisor on `B`. -/
theorem isSMulRegular_of_forall_isSMulRegular_fiber {R B : Type u} [CommRing R] [CommRing B]
    [Algebra R B] [Smooth R B] {b : B}
    (h : ∀ (p : Ideal R) [p.IsPrime], IsSMulRegular (p.Fiber B) ((1 : p.ResidueField) ⊗ₜ[R] b)) :
    IsSMulRegular B b := by
  -- A noetherian model `R ⊗[A] B₀` of `B` in which `b` is `1 ⊗ b₀`.
  obtain ⟨A, B₀, _, _, _, _, _, _, e, b₀, heb⟩ := exists_isNoetherianRing_and_eq_one_tmul (A := R) b
  have : IsNoetherianRing B₀ := FiniteType.isNoetherianRing A B₀
  rw [← TauCeti.isSMulRegular_map_iff e, heb]
  refine Module.Flat.isSMulRegular_one_tmul_of_forall_isSMulRegular_fiber fun p _ ↦ ?_
  have := (TauCeti.isSMulRegular_map_iff
    (congr (AlgEquiv.refl : p.ResidueField ≃ₐ[R] _) e) _).mpr (h p)
  simpa [heb] using this

end Algebra.Smooth

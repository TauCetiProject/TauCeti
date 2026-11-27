/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.DeRham.Differential
import TauCeti.RingTheory.Derivation.Basic

/-!
# Frobenius linearity of the de Rham differential

`TauCeti.DeRham.d_pow_smul_of_natCast_eq_zero` gives the scalar identity for powers whose
exponent vanishes in the ring. In prime characteristic, `TauCeti.DeRham.d_frobenius_smul`
gives the scalar identity for the action through relative Frobenius in Bhatt,
*p-adic derived de Rham cohomology*, Notation 3.1.

The underlying scalar law is `TauCeti.DeRham.d_smul_of_D_eq_zero` for scalars with vanishing
Kähler differential. The vanishing on powers follows from
`Derivation.map_pow_eq_zero_of_natCast_eq_zero`.
-/

public section

namespace TauCeti.DeRham

open KaehlerDifferential

variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B] {n : ℕ}

/-- If `m` vanishes in `B`, the de Rham differential commutes with multiplication by
`b ^ m`. In prime characteristic this is linearity for the action through Frobenius. -/
theorem d_pow_smul_of_natCast_eq_zero {m : ℕ} (b : B) (ω : Forms A B n) (hm : (m : B) = 0) :
    d A B n (b ^ m • ω) = b ^ m • d A B n ω :=
  d_smul_of_D_eq_zero ((D A B).map_pow_eq_zero_of_natCast_eq_zero b hm) ω

/-- In characteristic `p`, the de Rham differential commutes with multiplication by
`p`-th powers. This gives the scalar identity for the action through Frobenius in prime
characteristic. -/
theorem d_frobenius_smul (p : ℕ) [CharP B p] (b : B) (ω : Forms A B n) :
    d A B n (b ^ p • ω) = b ^ p • d A B n ω :=
  d_pow_smul_of_natCast_eq_zero b ω (CharP.cast_eq_zero B p)

end TauCeti.DeRham

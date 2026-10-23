/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.Galois.AbsoluteGaloisGroup.ProP
public import TauCeti.Topology.Algebra.Group.Profinite.ProP.Inflation

/-!
# Inflation from the maximal pro-p quotient of an absolute Galois group

For a field `K` and a prime `p`, pullback along the quotient
`G_K → G_K(p)` identifies degree-one continuous cohomology with trivial `𝔽_p` coefficients.
In degree two the same inflation map is injective. These are the low-degree comparison results
between the absolute Galois group and its maximal pro-`p` quotient, specialized from the
statements `TauCeti.inflH1MaximalProP` and `TauCeti.inflH2MaximalProP_injective` for an arbitrary
profinite group.

## Main results

* `TauCeti.inflH1AbsoluteGaloisProP`: degree-one inflation from `G_K(p)` to `G_K` is a linear
  equivalence.
* `TauCeti.inflH2AbsoluteGaloisProP_injective`: degree-two inflation from `G_K(p)` to `G_K` is
  injective.

## References

* J.-P. Serre, *Galois Cohomology*, Chapter I, §2.6 and §4.3.
* J. Neukirch, A. Schmidt and K. Wingberg, *Cohomology of Number Fields*, I §1.6.
-/

public section

namespace TauCeti

universe u

variable (p : ℕ) [Fact p.Prime] (K : Type u) [Field K]

/-- **Degree-one inflation from the maximal pro-`p` quotient.** Pullback along
`G_K → G_K(p)` identifies `H¹(G_K(p), 𝔽_p)` with `H¹(G_K, 𝔽_p)`. -/
noncomputable def inflH1AbsoluteGaloisProP :
    cohomFp p (absoluteGaloisGroupProP p K) 1 ≃ₗ[ZMod p]
      cohomFp p (Field.absoluteGaloisGroup K) 1 :=
  inflH1MaximalProP p (Field.absoluteGaloisGroup K)

/-- The degree-one equivalence is the usual contravariant cohomology map along `G_K → G_K(p)`. -/
@[simp]
theorem inflH1AbsoluteGaloisProP_apply
    (x : cohomFp p (absoluteGaloisGroupProP p K) 1) :
    inflH1AbsoluteGaloisProP p K x =
      cohomFpMap p (absoluteGaloisGroupProPQuotientMap p K) 1 x :=
  inflH1MaximalProP_apply p (Field.absoluteGaloisGroup K) x

/-- **Degree-two inflation from `G_K(p)` to `G_K` is injective.** The inflation map
`H²(G_K(p), 𝔽_p) → H²(G_K, 𝔽_p)` is injective. -/
theorem inflH2AbsoluteGaloisProP_injective :
    Function.Injective (cohomFpMap p (absoluteGaloisGroupProPQuotientMap p K) 2) :=
  inflH2MaximalProP_injective p (Field.absoluteGaloisGroup K)

end TauCeti

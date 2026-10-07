/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.Galois.AbsoluteGaloisGroup.Inflation
public import TauCeti.NumberTheory.ClassFieldTheory.Local.Duality.TrivialZMod

/-!
# Degree-two inflation for local maximal pro-`p` Galois groups

Let `K` be a nonarchimedean local field containing a primitive `p`th root of unity, for a prime
`p`. Inflation along `G_K → G_K(p)` is injective on `H²(-, 𝔽_p)` for every field
(`TauCeti.inflH2AbsoluteGaloisProP_injective`). This file proves that it is also surjective: by
local duality `H²(G_K, 𝔽_p)` is one-dimensional and spanned by cup products of classes in
`H¹(G_K, 𝔽_p)`, all of which are inflated from `G_K(p)`, since degree-one inflation is bijective
and inflation commutes with the cup product.

The resulting isomorphisms in degrees one and two transport the cohomological invariants of `G_K`
to its maximal pro-`p` quotient: `H²(G_K(p), 𝔽_p)` is one-dimensional, and the cup square on
`H¹(G_K(p), 𝔽_p)` is perfect. These are the cohomological clauses of the Demushkin property of
`G_K(p)`; the dimension of `H¹(G_K(p), 𝔽_p)` is
`TauCeti.finrank_cohomFp_one_absoluteGaloisGroupProP_of_exists_isPrimitiveRoot`.

## Main definitions

* `TauCeti.inflH2AbsoluteGaloisProP`: degree-two inflation `H²(G_K(p), 𝔽_p) ≃ H²(G_K, 𝔽_p)`, as
  a linear equivalence.

## Main results

* `TauCeti.inflH2AbsoluteGaloisProP_surjective_of_mu`: degree-two inflation from `G_K(p)` to `G_K`
  is surjective.
* `TauCeti.finrank_cohomFp_two_absoluteGaloisGroupProP_of_mu`: `H²(G_K(p), 𝔽_p)` is
  one-dimensional.
* `TauCeti.cupFp_bijective_absoluteGaloisGroupProP_of_mu`: the cup square on
  `H¹(G_K(p), 𝔽_p)` is a perfect pairing.

## References

* J.-P. Serre, *Galois Cohomology*, Chapter II, §5.6.
* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., (7.5.11).
-/

public section

namespace TauCeti

variable (p : ℕ) [Fact p.Prime] (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

/-- **Degree-two inflation from `G_K(p)` to `G_K` is surjective** when the nonarchimedean local
field `K` contains a primitive `p`th root of unity: every class of `H²(G_K, 𝔽_p)` is inflated from
`H²(G_K(p), 𝔽_p)`. -/
theorem inflH2AbsoluteGaloisProP_surjective_of_mu (hmu : ∃ ζ : K, IsPrimitiveRoot ζ p) :
    Function.Surjective (cohomFpMap p (absoluteGaloisGroupProPQuotientMap p K) 2) :=
  let ⟨_, hζ⟩ := hmu
  inflH2MaximalProP_surjective_of_map₂_cupFp_eq_top p (Field.absoluteGaloisGroup K)
    (ClassFieldTheory.map₂_cupFp_absoluteGaloisGroup_eq_top_of_isPrimitiveRoot hζ)

/-- **Degree-two inflation from the maximal pro-`p` quotient** of the absolute Galois group of a
nonarchimedean local field `K` containing a primitive `p`th root of unity: pullback along
`G_K → G_K(p)` identifies `H²(G_K(p), 𝔽_p)` with `H²(G_K, 𝔽_p)`. -/
noncomputable def inflH2AbsoluteGaloisProP (hmu : ∃ ζ : K, IsPrimitiveRoot ζ p) :
    cohomFp p (absoluteGaloisGroupProP p K) 2 ≃ₗ[ZMod p]
      cohomFp p (Field.absoluteGaloisGroup K) 2 :=
  LinearEquiv.ofBijective (cohomFpMap p (absoluteGaloisGroupProPQuotientMap p K) 2).hom.toLinearMap
    ⟨inflH2AbsoluteGaloisProP_injective p K, inflH2AbsoluteGaloisProP_surjective_of_mu p K hmu⟩

/-- The degree-two equivalence is the usual contravariant cohomology map along `G_K → G_K(p)`. -/
@[simp]
theorem inflH2AbsoluteGaloisProP_apply (hmu : ∃ ζ : K, IsPrimitiveRoot ζ p)
    (x : cohomFp p (absoluteGaloisGroupProP p K) 2) :
    inflH2AbsoluteGaloisProP p K hmu x =
      cohomFpMap p (absoluteGaloisGroupProPQuotientMap p K) 2 x :=
  LinearEquiv.ofBijective_apply _ x

/-- If a nonarchimedean local field `K` contains a primitive `p`th root of unity, then
`H²(G_K(p), 𝔽_p)` is one-dimensional. -/
theorem finrank_cohomFp_two_absoluteGaloisGroupProP_of_mu
    (hmu : ∃ ζ : K, IsPrimitiveRoot ζ p) :
    Module.finrank (ZMod p) (cohomFp p (absoluteGaloisGroupProP p K) 2) = 1 :=
  let ⟨_, hζ⟩ := hmu
  (inflH2AbsoluteGaloisProP p K hmu).finrank_eq.trans
    (ClassFieldTheory.finrank_cohomFp_two_absoluteGaloisGroup_of_isPrimitiveRoot hζ)

/-- **The cup square on `H¹(G_K(p), 𝔽_p)` is a perfect pairing** when the nonarchimedean local
field `K` contains a primitive `p`th root of unity: `a ↦ (b ↦ a ⌣ b)` is a bijection from
`H¹(G_K(p), 𝔽_p)` onto the `𝔽_p`-linear maps `H¹(G_K(p), 𝔽_p) → H²(G_K(p), 𝔽_p)`. -/
theorem cupFp_bijective_absoluteGaloisGroupProP_of_mu (hmu : ∃ ζ : K, IsPrimitiveRoot ζ p) :
    Function.Bijective (cupFp p (absoluteGaloisGroupProP p K)) :=
  let ⟨_, hζ⟩ := hmu
  have h₁ : Function.Bijective (cohomFpMap p (absoluteGaloisGroupProPQuotientMap p K) 1) :=
    funext (inflH1AbsoluteGaloisProP_apply p K) ▸ (inflH1AbsoluteGaloisProP p K).bijective
  (cupFp_bijective_iff_of_bijective p _ (absoluteGaloisGroupProPQuotientMap p K) h₁
    ⟨inflH2AbsoluteGaloisProP_injective p K, inflH2AbsoluteGaloisProP_surjective_of_mu p K hmu⟩).2
      (ClassFieldTheory.cupFp_bijective_of_isPrimitiveRoot hζ)

end TauCeti

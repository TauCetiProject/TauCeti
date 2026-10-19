/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import TauCeti.Algebra.CharP.Frobenius.Finite
public import TauCeti.AlgebraicGeometry.Frobenius.Basic

/-!
# Finiteness of the absolute Frobenius

Let `p` be a prime and `X` a scheme locally of finite type over `Spec R`, where `R` is a perfect
ring of characteristic `p` (for instance a perfect field). Then the absolute Frobenius
`F_X : X ⟶ X` is a finite morphism (`AlgebraicGeometry.Scheme.isFinite_frobenius`). On an affine
open `U` it is the `p`-th power map of `Γ(X, U)`, which is finite because `Γ(X, U)` is of finite
type over `R` and every element of `R` is a `p`-th power
(`TauCeti.powRingHom_finite`).

The finite-type hypothesis cannot be dropped: the absolute Frobenius of the spectrum of the field
of rational functions over `𝔽_p` in infinitely many variables is not finite.

## References

* The Stacks Project, [Tag 0CC6](https://stacks.math.columbia.edu/tag/0CC6), Frobenii.
-/

public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme

variable {X : Scheme.{u}} {p : ℕ} [Fact p.Prime]

/-- **The absolute Frobenius of a scheme locally of finite type over a perfect ring is finite.**
For a scheme `X` locally of finite type over `Spec R`, with `R` a perfect ring of characteristic
`p`, the absolute Frobenius `F_X : X ⟶ X` is a finite morphism. -/
theorem isFinite_frobenius {R : Type u} [CommRing R] [ExpChar R p] [PerfectRing R p]
    (f : X ⟶ Spec (.of R)) [LocallyOfFiniteType f] (hX : (p : Γ(X, ⊤)) = 0) :
    IsFinite (X.frobenius p hX) where
  isAffine_preimage U hU := by
    simpa only [frobenius_preimage] using hU
  finite_app U hU := by
    rw [Scheme.Hom.app_eq_appLE, (X.frobenius p hX).appLE_congr _ rfl (frobenius_preimage hX U)
      (fun f ↦ f.hom.Finite)]
    have hF : ((X.frobenius p hX).appLE U U (frobenius_preimage hX U).ge).hom =
        TauCeti.powRingHom Γ(X, U) p (natCast_app_eq_zero hX U) := by
      ext s
      simp
    -- `Γ(X, U)` is of finite type over `R`, through `R ≅ Γ(Spec R, ⊤)` followed by `f`
    have hf := HasRingHomProperty.appLE @LocallyOfFiniteType f inferInstance
      ⟨⊤, isAffineOpen_top _⟩ ⟨U, hU⟩ le_top
    rw [hF]
    exact TauCeti.powRingHom_finite _ _ <| hf.comp <|
      .of_surjective _ (ΓSpecIso (.of R)).commRingCatIsoToRingEquiv.symm.surjective

end AlgebraicGeometry.Scheme

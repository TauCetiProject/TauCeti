/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EffectiveCartierDivisor.Basic
public import TauCeti.AlgebraicGeometry.IdealSheaf.BaseChange

/-!
# Relative effective Cartier divisors

An effective Cartier divisor on `X` relative to `S` is an effective Cartier divisor whose
closed subscheme is flat over `S`. This file records the base-change ideal and identifies its
closed subscheme with the expected fibre product. Consequently, the relative flatness condition
is preserved by arbitrary base change.

## Main results

* `Scheme.IdealSheafData.IsRelativeEffectiveCartier`: an effective Cartier divisor flat over
  the base.
* `Scheme.IdealSheafData.IsRelativeEffectiveCartier.comap_iff`: after arbitrary base change,
  relativity reduces to the effective Cartier condition on the pulled-back ideal.
* `Scheme.IdealSheafData.IsRelativeEffectiveCartier.comap`: a relative effective Cartier
  divisor remains one after a flat base change.

## References

* Stacks Project, *Divisors*, Relative effective Cartier divisors.
-/

public section

open CategoryTheory Limits

universe u

namespace AlgebraicGeometry.Scheme.IdealSheafData

variable {S T X : Scheme.{u}}

/-- An effective Cartier divisor relative to `S` is an effective Cartier divisor whose closed
subscheme is flat over `S`. -/
def IsRelativeEffectiveCartier (I : X.IdealSheafData) (f : X ⟶ S) : Prop :=
  I.IsEffectiveCartier ∧ Flat (I.subschemeι ≫ f)

/-- A divisor is relative effective Cartier exactly when it is effective Cartier and its closed
subscheme is flat over the base. -/
theorem isRelativeEffectiveCartier_iff (I : X.IdealSheafData) (f : X ⟶ S) :
    I.IsRelativeEffectiveCartier f ↔ I.IsEffectiveCartier ∧ Flat (I.subschemeι ≫ f) :=
  Iff.rfl

/-- A relative effective Cartier divisor is an effective Cartier divisor on its ambient scheme. -/
theorem IsRelativeEffectiveCartier.isEffectiveCartier {I : X.IdealSheafData} {f : X ⟶ S}
    (hI : I.IsRelativeEffectiveCartier f) : I.IsEffectiveCartier :=
  hI.1

/-- The closed subscheme of a relative effective Cartier divisor is flat over the base. -/
theorem IsRelativeEffectiveCartier.flat {I : X.IdealSheafData} {f : X ⟶ S}
    (hI : I.IsRelativeEffectiveCartier f) : Flat (I.subschemeι ≫ f) :=
  hI.2

/-- If the original closed subscheme is flat over the base, its arbitrary base change is relative
effective Cartier if and only if the pulled-back ideal is effective Cartier. -/
theorem IsRelativeEffectiveCartier.comap_iff (I : X.IdealSheafData) (f : X ⟶ S)
    (g : T ⟶ S) [Flat (I.subschemeι ≫ f)] :
    (I.comap (pullback.fst f g)).IsRelativeEffectiveCartier (pullback.snd f g) ↔
      (I.comap (pullback.fst f g)).IsEffectiveCartier := by
  constructor
  · exact IsRelativeEffectiveCartier.isEffectiveCartier
  · exact fun h ↦ ⟨h, flat_comap_subschemeι_comp_snd I f g⟩

/-- A relative effective Cartier divisor remains relative effective Cartier after flat pullback. -/
theorem IsRelativeEffectiveCartier.comap {I : X.IdealSheafData}
    {f : X ⟶ S} (hI : I.IsRelativeEffectiveCartier f) (g : T ⟶ S) [Flat g] :
    (I.comap (pullback.fst f g)).IsRelativeEffectiveCartier (pullback.snd f g) := by
  let _ : Flat (I.subschemeι ≫ f) := hI.flat
  rw [IsRelativeEffectiveCartier.comap_iff]
  exact hI.isEffectiveCartier.comap (pullback.fst f g)

end AlgebraicGeometry.Scheme.IdealSheafData

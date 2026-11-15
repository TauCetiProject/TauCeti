/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.LineBundle.Class
public import TauCeti.AlgebraicGeometry.LineBundle.NonvanishingLocus

/-!
# Nonvanishing loci on line bundles of trivial class

Line bundles usually enter as representatives of a class in the Picard group: ampleness, for
instance, provides some line bundle `L` with `mk L = (mk M) ^ n`, not a specific sheaf. When that
class is trivial, `L` is only isomorphic to `𝒪_X`, not equal to it. Since nonvanishing loci depend
only on the isomorphism class (`Scheme.Modules.range_nonvanishingLocus_eq_of_iso`), the
nonvanishing loci of the sections of such an `L` over an open `U` are still exactly the basic open
sets `X_r` of the regular functions `r` on `U`. When the global functions on `X` form a field, as
on an integral scheme universally closed over a field
(`AlgebraicGeometry.isField_of_universallyClosed`), a global section of `L` therefore vanishes
either everywhere or nowhere: its nonvanishing locus is `⊥` or `⊤`.

These facts feed the characterization of ampleness of the trivial class by quasi-affineness
(`TauCeti.AlgebraicGeometry.LineBundleClass.isAmple_one_iff`) and the positivity of the degree of
an ample line bundle on an integral proper curve
(`TauCeti.AlgebraicGeometry.LineBundleClass.IsAmple.eulerDegree_pos`).

## Main results

* `InvertibleSheaf.range_nonvanishingLocus_eq_range_basicOpen_of_mk_eq_one`:
  the nonvanishing loci of sections of a line bundle of trivial class are the basic open sets.
* `InvertibleSheaf.nonvanishingLocus_eq_bot_or_eq_top_of_isField_of_mk_eq_one`:
  when `Γ(X, ⊤)` is a field, a global section of a line bundle of trivial class vanishes
  everywhere or nowhere.
-/

public section

open CategoryTheory AlgebraicGeometry

namespace TauCeti.AlgebraicGeometry

universe u

variable {X : Scheme.{u}}

namespace InvertibleSheaf

/-- The nonvanishing loci of the sections over `U` of a line bundle of trivial class are exactly the
basic open sets of the regular functions on `U`. -/
theorem range_nonvanishingLocus_eq_range_basicOpen_of_mk_eq_one {L : InvertibleSheaf X}
    (hL : LineBundleClass.mk L = 1) (U : X.Opens) :
    Set.range (L.obj.nonvanishingLocus (U := U)) = Set.range (X.basicOpen (U := U)) := by
  -- The tensor unit `𝟙_ X.Modules` is by definition the structure sheaf `SheafOfModules.unit`.
  obtain ⟨e⟩ : Nonempty (L.obj ≅ SheafOfModules.unit X.ringCatSheaf) :=
    LineBundleClass.mk_eq_one_iff.mp hL
  rw [Scheme.Modules.range_nonvanishingLocus_eq_of_iso e U]
  exact congrArg Set.range (funext Scheme.Modules.nonvanishingLocus_unit)

/-- When the global functions on `X` form a field, for instance on an integral scheme universally
closed over a field, a global section of a line bundle of trivial class vanishes either everywhere
or nowhere. -/
theorem nonvanishingLocus_eq_bot_or_eq_top_of_isField_of_mk_eq_one (hX : IsField Γ(X, ⊤))
    {L : InvertibleSheaf X} (hL : LineBundleClass.mk L = 1) (s : Γ(L.obj, ⊤)) :
    L.obj.nonvanishingLocus s = ⊥ ∨ L.obj.nonvanishingLocus s = ⊤ := by
  obtain ⟨r, hr⟩ : L.obj.nonvanishingLocus s ∈ Set.range (X.basicOpen (U := ⊤)) := by
    rw [← range_nonvanishingLocus_eq_range_basicOpen_of_mk_eq_one hL ⊤]
    exact ⟨s, rfl⟩
  let := hX.toField
  rw [← hr]
  obtain rfl | hr₀ := eq_or_ne r 0
  · exact Or.inl (X.basicOpen_zero ⊤)
  · exact Or.inr (X.basicOpen_of_isUnit hr₀.isUnit)

end InvertibleSheaf

end TauCeti.AlgebraicGeometry

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.SimplicialSet.Cochains.IntegralComparison

/-!
# Integral comparison for singular cohomology

If `M` is a module over a ring `k`, cochains `Hom_k(C_*(X; k), M)` and
`Hom_ℤ(C_*(X; ℤ), M)` are naturally isomorphic as complexes of abelian groups. Both assign
values in `M` to singular simplices and use the same alternating-face differential. Applying
`TauCeti.simplicialCochainComplexIntegralIso` to the singular simplicial set gives the
comparison and its induced cohomology isomorphism, keeping the pullback maps visible.

The ring may be noncommutative, and no flatness or projectivity is required. The scalar ring
of both cochain complexes is `ℤ`; the target regards `M` as an abelian group. In particular,
cohomology with values in a finite field can be computed using integral chains, as needed
when comparing integral universal coefficients with finite-field calculations. Spaces and
modules are small, so the regular integral coefficient object can be used without lifting.

## References

* A. Hatcher, *Algebraic Topology*, Section 3.1.
-/

public section

noncomputable section

open CategoryTheory

namespace TauCeti

variable (k : Type) [Ring k] (M : ModuleCat.{0} k) (X : TopCat.{0})

/-- Singular cochains over `k` with values in `M` agree naturally with integral cochains
with values in the underlying abelian group of `M`. -/
abbrev singularCochainComplexIntegralIso :
    X.singularCochainComplex (ModuleCat.of k k) ℤ M ≅
      X.singularCochainComplex (ModuleCat.of ℤ ℤ) ℤ (ModuleCat.of ℤ M) :=
  simplicialCochainComplexIntegralIso k M (TopCat.toSSet.obj X)

/-- The singular integral comparison commutes with pullback along continuous maps. -/
@[reassoc]
lemma singularCochainComplexIntegralIso_hom_naturality {Y : TopCat.{0}} (f : X ⟶ Y) :
    TopCat.singularCochainComplexMap (R := ModuleCat.of k k) (k := ℤ) (M := M) f ≫
        (singularCochainComplexIntegralIso k M X).hom =
      (singularCochainComplexIntegralIso k M Y).hom ≫
        TopCat.singularCochainComplexMap (R := ModuleCat.of ℤ ℤ) (k := ℤ)
          (M := ModuleCat.of ℤ M) f :=
  simplicialCochainComplexIntegralIso_hom_naturality k M _ (TopCat.toSSet.map f)

/-- Singular cohomology computed over `k` is naturally isomorphic, as an abelian group, to
singular cohomology computed from integral chains with values in the same module. -/
def singularCohomologyIntegralIso (n : ℕ) :
    X.singularCohomology (ModuleCat.of k k) ℤ M n ≅
      X.singularCohomology (ModuleCat.of ℤ ℤ) ℤ (ModuleCat.of ℤ M) n :=
  (HomologicalComplex.homologyFunctor _ _ n).mapIso (singularCochainComplexIntegralIso k M X)

/-- The cohomology comparison is induced by the cochain comparison. -/
lemma singularCohomologyIntegralIso_hom (n : ℕ) :
    (singularCohomologyIntegralIso k M X n).hom =
      HomologicalComplex.homologyMap (singularCochainComplexIntegralIso k M X).hom n :=
  (rfl)

/-- The inverse cohomology comparison is induced by the inverse cochain comparison. -/
lemma singularCohomologyIntegralIso_inv (n : ℕ) :
    (singularCohomologyIntegralIso k M X n).inv =
      HomologicalComplex.homologyMap (singularCochainComplexIntegralIso k M X).inv n :=
  (rfl)

/-- The integral cohomology comparison commutes with pullback along continuous maps. -/
@[reassoc]
lemma singularCohomologyIntegralIso_hom_naturality {Y : TopCat.{0}} (f : X ⟶ Y) (n : ℕ) :
    TopCat.singularCohomologyMap (R := ModuleCat.of k k) (k := ℤ) (M := M) f n ≫
        (singularCohomologyIntegralIso k M X n).hom =
      (singularCohomologyIntegralIso k M Y n).hom ≫
        TopCat.singularCohomologyMap (R := ModuleCat.of ℤ ℤ) (k := ℤ)
          (M := ModuleCat.of ℤ M) f n := by
  simpa [singularCohomologyIntegralIso, TopCat.singularCohomologyMap,
    ← HomologicalComplex.homologyMap_comp] using
    congrArg (fun g ↦ HomologicalComplex.homologyMap g n)
      (singularCochainComplexIntegralIso_hom_naturality k M X f)

end TauCeti

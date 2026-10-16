/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.FGModuleCat.Frobenius
public import TauCeti.CategoryTheory.Exact.Resolution.Complete
public import TauCeti.Algebra.Homology.ShortComplex.Splice
public import TauCeti.Algebra.Homology.TotallyAcyclic.SelfInjective

/-!
# Gorenstein-projective modules over self-injective algebras

Every finite-dimensional right module over a finite-dimensional algebra that is self-injective on
both sides has a complete resolution by finite projective modules. The Frobenius structure on
finitely generated modules supplies successive projective presentations and copresentations;
their spliced complex is acyclic. Injectivity of the regular module gives dual acyclicity.

The construction concerns finitely generated modules in the ring's universe. It does not
assert that arbitrary modules have complete resolutions with finite terms. Right modules over
`A` are left `Aᵐᵒᵖ`-modules. The self-injectivity hypotheses use the regular left and right
modules of `Aᵐᵒᵖ`, as in `FGModuleCat.abelian_isFrobenius`.

## References

* Ragnar-Olaf Buchweitz, *Maximal Cohen–Macaulay Modules and Tate Cohomology*, Section 4.
* T. Y. Lam, *Lectures on Modules and Rings*, Sections 3 and 15.
-/

public section

open CategoryTheory

universe u w

namespace TauCeti

/-- Every finitely generated right module over a finite-dimensional, two-sided self-injective
algebra is Gorenstein-projective. Its complete resolution has finite projective terms in every
degree. No restriction on the characteristic of the field is needed. -/
theorem isGorensteinProjective_of_moduleInjective_self
    (k : Type w) [Field k] {A : Type u} [Ring A] [Algebra k A] [FiniteDimensional k A]
    (hr : Module.Injective Aᵐᵒᵖ Aᵐᵒᵖ) (hl : Module.Injective (Aᵐᵒᵖ)ᵐᵒᵖ Aᵐᵒᵖ)
    (M : ModuleCat.{u} Aᵐᵒᵖ) [Module.Finite Aᵐᵒᵖ M] : IsGorensteinProjective Aᵐᵒᵖ M := by
  let : IsNoetherianRing Aᵐᵒᵖ := isNoetherian_of_tower k inferInstance
  let F := forget₂ (FGModuleCat.{u} Aᵐᵒᵖ) (ModuleCat.{u} Aᵐᵒᵖ)
  obtain ⟨S, hS, hproj, he, ⟨eM⟩⟩ :=
    (FGModuleCat.abelian_isFrobenius k hr hl).exists_projective_conflation_sequence
      (FGModuleCat.of Aᵐᵒᵖ M)
  let T (n : ℤ) := (S n).map F
  let e (n : ℤ) := F.mapIso (he n).some
  have hT (n : ℤ) : (T n).ShortExact :=
    ((ExactStructure.abelian_conflation _).mp (hS n)).map_of_exact F
  let P := CochainComplex.splice T e
  have hfinite (n : ℤ) : Module.Finite Aᵐᵒᵖ (P.X n) := (S n).X₂.property
  have hprojective (n : ℤ) : Projective (P.X n) := by
    have : Projective (S n).X₂ := (ExactStructure.abelian_isProjective_iff _).mp (hproj n)
    have : Module.Projective Aᵐᵒᵖ (S n).X₂ := FGModuleCat.moduleProjective_of_projective _
    exact ModuleCat.projective_of_categoryTheory_projective (R := Aᵐᵒᵖ) (P := (S n).X₂.obj)
  refine (isGorensteinProjective_iff M).mpr ⟨P,
    P.isTotallyAcyclic_of_acyclic_of_moduleInjective_self hr hfinite hprojective
      (CochainComplex.acyclic_splice T e hT), ?_⟩
  exact ⟨(CochainComplex.spliceCyclesIso T e hT 0).symm ≪≫ F.mapIso eM⟩

end TauCeti

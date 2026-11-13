/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.FGModuleCat.Frobenius
public import TauCeti.Algebra.Homology.TotallyAcyclic.Abelian.FrobeniusAbelian
public import TauCeti.Algebra.Homology.TotallyAcyclic.FGModuleCat

/-!
# Gorenstein-projective modules over self-injective algebras

Every finite-dimensional right module over a finite-dimensional algebra that is self-injective on
both sides has a complete resolution by finite projective modules. The abelian exact structure on
finitely generated modules is Frobenius (`FGModuleCat.abelian_isFrobenius`), so every object is a
Gorenstein-projective object of `FGModuleCat`
(`CategoryTheory.isGorensteinProjective_of_isFrobenius`), which is the same as a
Gorenstein-projective module (`FGModuleCat.isGorensteinProjective_iff`).

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
  exact (FGModuleCat.isGorensteinProjective_iff (FGModuleCat.of Aᵐᵒᵖ M)).mp
    (isGorensteinProjective_of_isFrobenius (FGModuleCat.abelian_isFrobenius k hr hl) _)

end TauCeti

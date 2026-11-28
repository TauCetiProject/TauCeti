/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.ModuleCat.Sheaf.TensorProduct.KFlat
public import TauCeti.Algebra.Homology.Monoidal.TorAmplitude

/-!
# Flat representatives for complexes of module sheaves

On a small ringed site, an object of the derived category of module sheaves has Tor-amplitude
in `[a, b]` if and only if it has a representative by flat module sheaves whose terms vanish
outside `[a, b]`.
The lower truncation of a bounded-above flat resolution works because the Tor-amplitude
hypothesis makes the quotient in its new lowest degree flat.
For a scheme `X`, specialize to `R := X.sheaf` with the `HasDerivedCategory` instance written
on `SheafOfModules X.ringCatSheaf`.

## References

* [The Stacks Project, Lemma 20.48.2](https://stacks.math.columbia.edu/tag/08CH)
* [The Stacks Project, Lemma 20.48.3](https://stacks.math.columbia.edu/tag/08CI)
-/

public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory
open TauCeti.SheafOfModules

universe u v

namespace DerivedCategory

variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat RingCat.{u})]
  [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  {R : Sheaf J CommRingCat.{u}} [HasDerivedCategory.{v} (SheafOfModules.{u} (ringCatSheaf R))]

/-- An object of the unbounded derived category of module sheaves on a small ringed site has
Tor-amplitude in `[a, b]` if and only if it is represented by flat module sheaves in degrees
`a` through `b`. -/
theorem hasTorAmplitude_iff_exists_flat_model
    {K : DerivedCategory (SheafOfModules.{u} (ringCatSheaf R))} {a b : ℤ} :
    K.HasTorAmplitude a b ↔
      ∃ P : CochainComplex (SheafOfModules.{u} (ringCatSheaf R)) ℤ,
        P.IsStrictlyGE a ∧ P.IsStrictlyLE b ∧
          (∀ i, PreservesFiniteLimits (tensorLeft (P.X i))) ∧ Nonempty (Q.obj P ≅ K) :=
  hasTorAmplitude_iff_exists_flat_model_of_exists_quasiIso fun L _ ↦
    CochainComplex.exists_quasiIso_isKFlat_sheafOfModules_of_isStrictlyLE (R := R) L b

end DerivedCategory

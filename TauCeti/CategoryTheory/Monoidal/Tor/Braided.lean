/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Monoidal.Braided.Basic
public import TauCeti.CategoryTheory.Monoidal.Tor.Basic

/-!
# Balance of `Tor₁` in a braided category

Mathlib's `CategoryTheory.Tor C n` derives the tensor product in its second variable and
`CategoryTheory.Tor' C n` in its first. In a braided monoidal abelian category, the two agree in
degree one on an object `M` with a projective presentation `0 ⟶ P₁ ⟶ P₀ ⟶ M ⟶ 0`:
`Tor₁(X, M)` is the kernel of `X ◁ S.f` and `Tor'₁(M, X)` the kernel of `S.f ▷ X`
(`CategoryTheory.ShortComplex.ShortExact.torOneIsoKernel`,
`CategoryTheory.ShortComplex.ShortExact.tor'OneIsoKernel`), and the braiding identifies these two
maps. This gives `Tor₁(X, M) ≅ Tor'₁(M, X)`
(`CategoryTheory.ShortComplex.ShortExact.torOneIsoTor'One`), and hence the same for every `M` of
projective dimension at most one (`CategoryTheory.torOneIsoTor'OneOfHasProjectiveDimensionLEOne`),
for instance every module over a principal ideal ring.

## References

* C. A. Weibel, *An Introduction to Homological Algebra*, Cambridge Studies in Advanced
  Mathematics 38, Cambridge University Press (1994), Section 3.1.
-/

public section

noncomputable section

namespace CategoryTheory

open Limits MonoidalCategory

universe v u

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C] [Abelian C]
  [MonoidalPreadditive C] [HasProjectiveResolutions C] {S : ShortComplex C}

namespace ShortComplex.ShortExact

variable (hS : S.ShortExact) [Projective S.X₁] [Projective S.X₂]

/-- **Balance of `Tor₁`.** For a projective presentation `0 ⟶ P₁ ⟶ P₀ ⟶ M ⟶ 0` in a braided
category, `Tor₁(X, M) ≅ Tor'₁(M, X)`: both are kernels of the map induced by `P₁ ⟶ P₀`, tensored
with `X` on either side, and the braiding identifies the two maps. -/
def torOneIsoTor'One (X : C) : ((Tor C 1).obj X).obj S.X₃ ≅ ((Tor' C 1).obj S.X₃).obj X :=
  hS.torOneIsoKernel X ≪≫
    kernel.mapIso (X ◁ S.f) (S.f ▷ X) (β_ X S.X₁) (β_ X S.X₂)
      (BraidedCategory.braiding_naturality_right X S.f) ≪≫
    (hS.tor'OneIsoKernel X).symm

/-- Under the kernel descriptions of `Tor₁(X, M)` and `Tor'₁(M, X)`, the balance isomorphism is
the braiding `X ⊗ P₁ ≅ P₁ ⊗ X`. -/
@[reassoc]
lemma torOneIsoTor'One_hom_comp_tor'OneIsoKernel_hom_comp_ι (X : C) :
    (hS.torOneIsoTor'One X).hom ≫ (hS.tor'OneIsoKernel X).hom ≫ kernel.ι (S.f ▷ X) =
      (hS.torOneIsoKernel X).hom ≫ kernel.ι (X ◁ S.f) ≫ (β_ X S.X₁).hom := by
  simp [torOneIsoTor'One]

end ShortComplex.ShortExact

/-- **Balance of `Tor₁` in projective dimension at most one.** In a braided category with enough
projectives, `Tor₁(X, Y) ≅ Tor'₁(Y, X)` for every `Y` of projective dimension at most one,
computed on the presentation `0 ⟶ ker π ⟶ P ⟶ Y ⟶ 0` of a projective cover `π : P ⟶ Y`. -/
def torOneIsoTor'OneOfHasProjectiveDimensionLEOne [EnoughProjectives C] (X Y : C)
    [HasProjectiveDimensionLE Y 1] : ((Tor C 1).obj X).obj Y ≅ ((Tor' C 1).obj Y).obj X :=
  -- the kernel of the projective cover `P ⟶ Y` is projective, as `Y` has projective dimension `< 2`
  have : HasProjectiveDimensionLT (Projective.kernelShortComplex Y).X₁ 1 :=
    (Projective.kernelShortComplex_shortExact Y).hasProjectiveDimensionLT_X₁ 1
      inferInstance ‹_›
  (Projective.kernelShortComplex_shortExact Y).torOneIsoTor'One X

end CategoryTheory

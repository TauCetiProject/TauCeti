/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Cohomology.Twisted.Cap
public import TauCeti.Topology.VectorBundle.Thom.TwistedRankDegreeHomology

/-!
# The homology Thom map with coefficients in the orientation system

Let `E → B` be a real vector bundle of rank `r` with Thom pair `(E, E₀)` and projection `π`, let
`R` be a commutative ring, and let `o(E)` be the orientation local system of `E`
(`TauCeti.VectorBundleOrientationCover.signLocalSystem`), pulled back to the total space as
`π^*o(E)` (`TauCeti.thomPairSignLocalSystem`). No orientation of `E` is chosen. For a local
system `L` on `B` and a relative class `u ∈ Hⁿ(E, E₀; π^*o(E), R)` this file defines the
**homology Thom map with orientation-twisted coefficients**

`Hₘ(E, E₀; π^*L) ⟶ Hₚ(B; o(E) ⊗ L)`,  `x ↦ π_*(x ⌢ u)`,  `n + p = m`

(`TauCeti.twistedHomologyThomMap`), `R`-linear in `u`. A chain twisted by `π^*L` is read as a
chain twisted by `π^*o(E) ⊗ π^*(o(E) ⊗ L)` through the inverse of the canonical pairing
`o(E) ⊗ o(E) ≅ R` (`TauCeti.VectorBundleOrientationCover.signLocalSystemTensorIso`), which
evaluates both factors at either orientation of a fibre and multiplies, so it needs no orientation
of the bundle. The relative cap product with `u` consumes the first factor and leaves homology
twisted by `π^*(o(E) ⊗ L)`, which the projection pushes forward to `Hₚ(B; o(E) ⊗ L)`. This is
`TopPair.twistedPushforwardCap` for the Thom pair, its projection, `o(E)` and the pairing tensored
with `L`. For the constant system with fibre an `R`-module `A`, the source is the singular
homology `Hₘ(E, E₀; A)` (`TopPair.twistedHomologyConstantIso`).

When `u` is a Thom class of `E` with coefficients in its orientation system, taking the value `1`
on the fibre class over every point, the Thom isomorphism with local coefficients asserts that this
map is bijective for `n = r`, giving `Hₚ₊ᵣ(E, E₀; π^*L) ≅ Hₚ(B; o(E) ⊗ L)` over every commutative
ring, `ℤ` included (Spanier, Chapter 5, Section 7). For the negative normal bundle `ν⁻` of a
Morse–Bott critical submanifold `C`, whose Thom pair carries the relative homology across the
critical level, this is the map to `H_{j-λ}(C; o(ν⁻) ⊗ A)` for constant coefficients `A`. Over a
ring in which `2` is invertible the same groups are identified through the orientation double
cover instead (`TauCeti.VectorBundleOrientationCover.thomPairSingularHomologyEquivTwistedHomology`).

## Main definitions

* `TauCeti.twistedHomologyThomMap`: the homology Thom map `x ↦ π_*(x ⌢ u)` with coefficients in a
  local system `L` on the base twisted by the orientation system, `R`-linear in `u`.

## References

* E. H. Spanier, *Algebraic Topology*, Chapter 5, Section 7 (the Thom isomorphism with local
  coefficients).
* J. W. Milnor, J. D. Stasheff, *Characteristic Classes*, Annals of Mathematics Studies 76,
  Princeton (1974), §10 and §12.
* A. Hatcher, *Algebraic Topology*, Section 3.H (local coefficients and the orientation double
  cover).
-/

public section

noncomputable section

open Bundle CategoryTheory MonoidalCategory Module
open TauCeti.LocalCoefficientSystem (constantFunctor constantTensorIso)
open TauCeti.VectorBundleOrientationCover (signLocalSystem signLocalSystemTensorIso)

universe w

namespace TauCeti

variable {B : Type w} [TopologicalSpace B] {F : Type w} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F] {E : B → Type w} [TopologicalSpace (TotalSpace F E)]
  [∀ b, AddCommMonoid (E b)] [∀ b, Module ℝ (E b)] [∀ b, TopologicalSpace (E b)] [FiberBundle F E]
  [VectorBundle ℝ F E] {ι : Type w} [Fintype ι] {R : Type w} [CommRing R]
  (hι : Fintype.card ι = finrank ℝ F)

variable (F E R) in
/-- **The homology Thom map with coefficients twisted by the orientation system.** For a real vector
bundle `E → B` with Thom pair `(E, E₀)`, projection `π` and orientation local system `o(E)`, a local
system `L` on `B`, and a class `u ∈ Hⁿ(E, E₀; π^*o(E), R)`, the morphism
`Hₘ(E, E₀; π^*L) ⟶ Hₚ(B; o(E) ⊗ L)`, `x ↦ π_*(x ⌢ u)` (`n + p = m`), `R`-linear in `u`. A chain
twisted by `π^*L` is read as a chain twisted by `π^*o(E) ⊗ π^*(o(E) ⊗ L)` through the inverse of
the canonical pairing `o(E) ⊗ o(E) ≅ R`, so no orientation of `E` is needed. For the constant system
with fibre an `R`-module `A`, the source is the singular homology `Hₘ(E, E₀; A)`
(`TopPair.twistedHomologyConstantIso`, `TauCeti.LocalCoefficientSystem.pullbackConstantIso`). -/
def twistedHomologyThomMap (L : LocalCoefficientSystem.{w, w, w} R (TopCat.of B)) (n p m : ℕ)
    (h : n + p = m) :
    (thomPair F E).twistedCohomology (thomPairSignLocalSystem F E R hι) R (ModuleCat.of R R) n
      →ₗ[R] ((thomPair F E).twistedHomology
          ((LocalCoefficientSystem.pullback
            (TopCat.ofHom ⟨π F E, FiberBundle.continuous_proj F E⟩).hom).obj L) m ⟶
        (signLocalSystem F E R hι ⊗ L).twistedHomology p) :=
  (thomPair F E).twistedPushforwardCap (TopCat.ofHom ⟨π F E, FiberBundle.continuous_proj F E⟩)
      (signLocalSystem F E R hι)
      ((constantTensorIso L).inv ≫
        (((constantFunctor (TopCat.of B)).map
            (ULift.moduleEquiv (R := R) (M := R)).toModuleIso.inv ≫
          (signLocalSystemTensorIso hι).inv) ▷ L) ≫
        (α_ _ _ _).hom) n p m h ∘ₗ
    ((thomPair F E).twistedCohomologyCoefficientMap R (ModuleCat.of R R)
      (eqToHom (thomPairSignLocalSystem_def hι).symm) n).hom

/-- `TauCeti.twistedHomologyThomMap` is the twisted push-forward cap product of the Thom pair, its
projection and the orientation system. -/
lemma twistedHomologyThomMap_apply (L : LocalCoefficientSystem.{w, w, w} R (TopCat.of B))
    {n p m : ℕ} (h : n + p = m)
    (u : (thomPair F E).twistedCohomology (thomPairSignLocalSystem F E R hι) R
      (ModuleCat.of R R) n) :
    twistedHomologyThomMap F E R hι L n p m h u =
      (thomPair F E).twistedPushforwardCap
        (TopCat.ofHom ⟨π F E, FiberBundle.continuous_proj F E⟩) (signLocalSystem F E R hι)
        ((constantTensorIso L).inv ≫
          (((constantFunctor (TopCat.of B)).map
              (ULift.moduleEquiv (R := R) (M := R)).toModuleIso.inv ≫
            (signLocalSystemTensorIso hι).inv) ▷ L) ≫
          (α_ _ _ _).hom) n p m h
        ((thomPair F E).twistedCohomologyCoefficientMap R (ModuleCat.of R R)
          (eqToHom (thomPairSignLocalSystem_def hι).symm) n u) :=
  (rfl)

end TauCeti

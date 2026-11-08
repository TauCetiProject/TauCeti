/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.ModuleCat.Colimits
public import TauCeti.AlgebraicTopology.Singular.Reduced
public import TauCeti.Topology.PathSpace.Moore.Comparison.HomotopyGroup

/-!
# Reduced homology of double loop spaces and the first nonvanishing higher homotopy group

The reduced homology `H~_*(Ω²X)` of a double loop space is the kernel of the map
`H_*(Ω²X) → H_*(pt)` induced by the map to a point. This file proves the degree-zero part of the
statement that it detects the first nontrivial higher homotopy group `π_k(X, x)`, `k ≥ 2`, of a
pointed space: the path components of `Ω²X` are the elements of `π₂(X, x)`, so the reduced
zeroth homology `H~₀(Ω²X; R)` is the coproduct of copies of `R` indexed by the nontrivial
elements of `π₂(X, x)`, the generator at `a` being `[γ] - [1]` for a double loop `γ` of class `a`.
If `π₂(X, x)` is nontrivial, `H~₀(Ω²X; R)` therefore contains a copy of `R`; for `R = ℤ` this is
an infinite cyclic subgroup.

For context, the positive-degree part is proved in other files. In positive degrees reduced and
ordinary homology agree (`TauCeti.reducedSingularHomologySuccIso`), and if `π_j(X, x)` vanishes
for `2 ≤ j < k` and `k ≥ 3`, then `H_{k-2}(Ω²X; ℤ) ≅ π_k(X, x)` by the Hurewicz theorem for the
`(k - 3)`-connected space `Ω²X`: this is
`TauCeti.MooreLoopSpace.doubleFirstHomologyAddEquiv` for `k = 3` and
`TauCeti.MooreLoopSpace.doubleHomologyAddEquiv` (or `TauCeti.doubleLoopSpaceHomologyAddEquiv`)
for `k ≥ 4`.

These are the homological facts behind the first part of Proposition 5.11 of
Barraud--Damian--Humilière--Oancea. In the paper's argument, the map
`i_{Q*} : H_*(Q; i_Q^*𝓕) → H_*(𝓛₀Q; 𝓕)`, for the DG local system `𝓕 = C_*(Ω𝓛₀Q)`, is
identified with the map `H_*(Ω²Q) → H_*(pt)`, whose kernel is `H~_*(Ω²Q)`; that identification is
not formalized here, so the results of this file are statements about `H~₀(Ω²Q)` rather than about
`ker i_{Q*}`. The case of the sphere `S²` is
`TauCeti.MooreLoopSpace.doubleReducedHomology₀SphereIso`, with the homotopy groups of spheres.

Both the fixed-interval double loop space `Ω (Ω X x) (Path.refl x)` and the double Moore loop
space `MooreLoopSpace (MooreLoopSpace X x) 1` are treated. The statements with coefficients in a
ring `R` take `R` and `X` in the same universe, so that `R`-modules live in the universe of the
space.

The path components of `Ω²X` and `ΩᴹΩᴹX` are identified with the elements of `π₂(X, x)` by
`TauCeti.zerothHomotopyDoubleLoopSpaceEquiv` and `TauCeti.MooreLoopSpace.zerothHomotopyDoubleEquiv`.

## Main definitions

* `TauCeti.doubleLoopSpaceReducedHomology₀Iso`, `TauCeti.MooreLoopSpace.doubleReducedHomology₀Iso`:
  `H~₀(Ω²X; R) ≅ ∐_{a ∈ π₂(X, x), a ≠ 1} R`.

## Main results

* `TauCeti.exists_injective_doubleLoopSpaceReducedHomology₀`,
  `TauCeti.MooreLoopSpace.exists_injective_doubleReducedHomology₀`: if `π₂(X, x)` is nontrivial,
  the reduced zeroth homology of the double loop space with coefficients in a ring `R` contains a
  copy of `R`, so an infinite cyclic subgroup for `R = ℤ`.

## References

* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, Proposition 5.11.
* A. Hatcher, *Algebraic Topology*, Proposition 2.7.
-/

public section

noncomputable section

open CategoryTheory Limits AlgebraicTopology HomotopyGroup
open scoped Topology Topology.Homotopy

namespace TauCeti

universe w v u

/-! ### Reduced zeroth homology -/

section DegreeZero

variable {C : Type u} [Category.{v} C] [HasCoproducts.{w} C] [Preadditive C]
  [CategoryWithHomology C] [HasKernels C] (R : C) {X : Type w} [TopologicalSpace X]

/-- **Reduced zeroth homology of the double loop space.** `H~₀(Ω²X; R)` is the coproduct of
copies of `R` indexed by the nontrivial elements of `π₂(X, x)`. -/
def doubleLoopSpaceReducedHomology₀Iso (x : X) :
    (reducedSingularHomologyFunctor R 0).obj (TopCat.of (Ω (Ω X x) (Path.refl x))) ≅
      ∐ fun _ : {a : π_ 2 X x // a ≠ 1} ↦ R :=
  reducedSingularHomology₀IsoOfEquiv R (Y := TopCat.of (Ω (Ω X x) (Path.refl x)))
    (Path.refl (Path.refl x)) (zerothHomotopyDoubleLoopSpaceEquiv x)
    (zerothHomotopyDoubleLoopSpaceEquiv_mk_refl x)

/-- The generator of `TauCeti.doubleLoopSpaceReducedHomology₀Iso` at the class of a double loop
`γ` is `[γ] - [1]`. -/
@[reassoc]
theorem ι_doubleLoopSpaceReducedHomology₀Iso_inv_ι (x : X) (γ : Ω (Ω X x) (Path.refl x))
    (h : zerothHomotopyDoubleLoopSpaceEquiv x (.mk γ) ≠ 1) :
    Sigma.ι (fun _ : {a : π_ 2 X x // a ≠ 1} ↦ R)
        ⟨zerothHomotopyDoubleLoopSpaceEquiv x (.mk γ), h⟩ ≫
        (doubleLoopSpaceReducedHomology₀Iso R x).inv ≫
          (reducedSingularHomologyι R 0).app (TopCat.of (Ω (Ω X x) (Path.refl x))) =
      singularHomology₀Section R (X := TopCat.of (Ω (Ω X x) (Path.refl x))) γ -
        singularHomology₀Section R (X := TopCat.of (Ω (Ω X x) (Path.refl x)))
          (Path.refl (Path.refl x)) :=
  ι_reducedSingularHomology₀IsoOfEquiv_inv_ι R (Y := TopCat.of (Ω (Ω X x) (Path.refl x))) _ γ _
    _ h

namespace MooreLoopSpace

/-- **Reduced zeroth homology of the double Moore loop space.** `H~₀(ΩᴹΩᴹX; R)` is the coproduct of
copies of `R` indexed by the nontrivial elements of `π₂(X, x)`. -/
def doubleReducedHomology₀Iso (x : X) :
    (reducedSingularHomologyFunctor R 0).obj
        (TopCat.of (MooreLoopSpace (MooreLoopSpace X x) 1)) ≅
      ∐ fun _ : {a : π_ 2 X x // a ≠ 1} ↦ R :=
  reducedSingularHomology₀IsoOfEquiv R (Y := TopCat.of (MooreLoopSpace (MooreLoopSpace X x) 1))
    1 (zerothHomotopyDoubleEquiv x) (zerothHomotopyDoubleEquiv_mk_one x)

/-- The generator of `TauCeti.MooreLoopSpace.doubleReducedHomology₀Iso` at the class of a double
Moore loop `γ` is `[γ] - [1]`. -/
@[reassoc]
theorem ι_doubleReducedHomology₀Iso_inv_ι (x : X) (γ : MooreLoopSpace (MooreLoopSpace X x) 1)
    (h : zerothHomotopyDoubleEquiv x (.mk γ) ≠ 1) :
    Sigma.ι (fun _ : {a : π_ 2 X x // a ≠ 1} ↦ R) ⟨zerothHomotopyDoubleEquiv x (.mk γ), h⟩ ≫
        (doubleReducedHomology₀Iso R x).inv ≫
          (reducedSingularHomologyι R 0).app
            (TopCat.of (MooreLoopSpace (MooreLoopSpace X x) 1)) =
      singularHomology₀Section R (X := TopCat.of (MooreLoopSpace (MooreLoopSpace X x) 1)) γ -
        singularHomology₀Section R (X := TopCat.of (MooreLoopSpace (MooreLoopSpace X x) 1)) 1 :=
  ι_reducedSingularHomology₀IsoOfEquiv_inv_ι R
    (Y := TopCat.of (MooreLoopSpace (MooreLoopSpace X x) 1)) _ γ _ _ h

end MooreLoopSpace

end DegreeZero

/-! ### Statements with coefficients in a ring -/

section Ring

variable {R : Type u} [Ring R] {X : Type u} [TopologicalSpace X]

/-- **The degree-zero homological input to Proposition 5.11 of Barraud--Damian--Humilière--Oancea
(case `k = 2`).** If `π₂(X, x)` is nontrivial, the reduced zeroth homology of the double loop
space with coefficients in `R`, the kernel of `H₀(Ω²X; R) → H₀(pt; R)`, contains a copy of `R`; for
`R = ℤ` this is an infinite cyclic subgroup. The identification of this kernel with `ker i_{Q*}` is
not formalized here. -/
theorem exists_injective_doubleLoopSpaceReducedHomology₀ (x : X) [Nontrivial (π_ 2 X x)] :
    ∃ f : R →ₗ[R] (reducedSingularHomologyFunctor (ModuleCat.of R R) 0).obj
        (TopCat.of (Ω (Ω X x) (Path.refl x))),
      Function.Injective f :=
  have := nonempty_subtype.2 (exists_ne (1 : π_ 2 X x))
  ModuleCat.exists_injective_of_iso_sigma (doubleLoopSpaceReducedHomology₀Iso _ x)

namespace MooreLoopSpace

/-- **The degree-zero homological input to Proposition 5.11 of Barraud--Damian--Humilière--Oancea
(case `k = 2`), for Moore double loops.** If `π₂(X, x)` is nontrivial, the reduced zeroth homology
of the double Moore loop space with coefficients in `R` contains a copy of `R`; for `R = ℤ` this is
an infinite cyclic subgroup. -/
theorem exists_injective_doubleReducedHomology₀ (x : X) [Nontrivial (π_ 2 X x)] :
    ∃ f : R →ₗ[R] (reducedSingularHomologyFunctor (ModuleCat.of R R) 0).obj
        (TopCat.of (MooreLoopSpace (MooreLoopSpace X x) 1)),
      Function.Injective f :=
  have := nonempty_subtype.2 (exists_ne (1 : π_ 2 X x))
  ModuleCat.exists_injective_of_iso_sigma (doubleReducedHomology₀Iso _ x)

end MooreLoopSpace

end Ring

end TauCeti

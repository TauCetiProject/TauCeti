/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.Additivity
public import TauCeti.AlgebraicTopology.Singular.Homotopy.Invariance
public import TauCeti.AlgebraicTopology.Singular.Sphere
public import TauCeti.AlgebraicTopology.UniversalCover.Circle.FreeLoop.HomotopyEquiv
public import TauCeti.Topology.PathSpace.Moore.Comparison.FreeLoop

/-!
# The homology of the free loop space of the circle

The free loop space `𝓛S¹ = C(S¹, S¹)` of the circle is homotopy equivalent to the disjoint union
`Σ n : ℤ, S¹` of circles indexed by the degree (`Circle.freeLoopHomotopyEquiv`). Consequently the
singular homology of `𝓛S¹`, with coefficients in any object `R` of an abelian category with exact
coproducts indexed by `ℤ`, is a coproduct of copies of the homology of the circle, one for each
degree (`Circle.freeLoopSingularHomologyIso`):

`H_k(𝓛S¹; R) ≅ ∐_{n ∈ ℤ} H_k(S¹; R)`.

The summand of index `n` is the image of the homology of the circle under the map `w ↦ (z ↦ w zⁿ)`
onto the free loops of degree `n` (`Circle.ι_freeLoopSingularHomologyIso_inv`). The homology
vanishes in degrees `k ≥ 2` (`Circle.isZero_singularHomology_freeLoop_of_two_le`). The same holds
for the Moore free loop space, which is homotopy equivalent to `C(S¹, S¹)`
(`Circle.mooreFreeLoopSingularHomologyIso`, `Circle.ι_mooreFreeLoopSingularHomologyIso_inv`,
`Circle.isZero_singularHomology_mooreFreeLoopSpace_of_two_le`). With
integer coefficients, since `H₀(S¹; ℤ)` and `H₁(S¹; ℤ)` are infinite cyclic, this describes the
right-hand side of the Viterbo isomorphism `SH_k(T*S¹) ≅ H_k(𝓛S¹; ℤ)` for the circle: a direct sum
of copies of `ℤ` indexed by the degree, that is, a copy of `ℤ[ℤ]`, in degrees `0` and `1`, and zero
in degrees `k ≥ 2`.

## Main declarations

* `Circle.freeLoopSingularHomologyIso`: `H_k(C(S¹, S¹); R) ≅ ∐_{n ∈ ℤ} H_k(S¹; R)`.
* `Circle.ι_freeLoopSingularHomologyIso_inv`: the summand of index `n` comes from the loops of
  degree `n`.
* `Circle.isZero_singularHomology_freeLoop_of_two_le`: `H_k(C(S¹, S¹); R) = 0` for `k ≥ 2`.
* `Circle.mooreFreeLoopSingularHomologyIso`, `Circle.ι_mooreFreeLoopSingularHomologyIso_inv`,
  `Circle.isZero_singularHomology_mooreFreeLoopSpace_of_two_le`: the same for the Moore free loop
  space.

## References

* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, §4 (the Viterbo isomorphism for `T*S¹`).
-/

public section

noncomputable section

open CategoryTheory Limits AlgebraicTopology TauCeti

namespace Circle

/-! ### Singular homology -/

variable {C : Type*} [Category C] [HasCoproducts.{0} C] [Abelian C]
  [HasExactColimitsOfShape (Discrete ℤ) C] (R : C) (k : ℕ)

/-- **The homology of the free loop space of the circle.** With coefficients in any object of an
abelian category with exact coproducts indexed by `ℤ`, `H_k(C(S¹, S¹); R)` is the coproduct, over
the degrees `n ∈ ℤ`, of copies of `H_k(S¹; R)`. -/
def freeLoopSingularHomologyIso :
    ((singularHomologyFunctor C k).obj R).obj (TopCat.of C(Circle, Circle)) ≅
      ∐ fun _ : ℤ ↦ ((singularHomologyFunctor C k).obj R).obj (TopCat.of Circle) :=
  freeLoopHomotopyEquiv.singularHomologyIso R k ≪≫
    (isColimitCofanSingularHomology (fun _ : ℤ ↦ TopCat.of Circle) C R k).coconePointUniqueUpToIso
      (colimit.isColimit _)

/-- The summand of index `n` of `Circle.freeLoopSingularHomologyIso` is the homology of the circle
mapped into `C(S¹, S¹)` by `w ↦ (z ↦ w zⁿ)`, onto the free loops of degree `n`. -/
theorem ι_freeLoopSingularHomologyIso_inv (n : ℤ) :
    Sigma.ι _ n ≫ (freeLoopSingularHomologyIso R k).inv =
      ((singularHomologyFunctor C k).obj R).map
        (TopCat.ofHom (freeLoopHomotopyEquiv.symm.toFun.comp (.sigmaMk n))) := by
  rw [freeLoopSingularHomologyIso, Iso.trans_inv, ← Category.assoc]
  refine (IsColimit.comp_coconePointUniqueUpToIso_inv
    (isColimitCofanSingularHomology (fun _ : ℤ ↦ TopCat.of Circle) C R k)
    (colimit.isColimit _) ⟨n⟩ =≫ _).trans ?_
  rw [Cofan.mk_ι_app, ContinuousMap.HomotopyEquiv.singularHomologyIso_inv, ← Functor.map_comp]
  -- `TopCat.sigmaι _ n` is `ContinuousMap.sigmaMk n` by construction, and `invFun` is the
  -- forward map of `symm`, so both sides are the same composite of continuous maps.
  rfl

/-- **The free loop space of the circle has no homology in degrees `k ≥ 2`.** -/
theorem isZero_singularHomology_freeLoop_of_two_le {k : ℕ} (hk : 2 ≤ k) :
    IsZero (((singularHomologyFunctor C k).obj R).obj (TopCat.of C(Circle, Circle))) :=
  ((isColimitCofanSingularHomology (fun _ : ℤ ↦ TopCat.of Circle) C R k).isZero_pt
    (Functor.isZero _ fun _ ↦ isZero_singularHomology_circle_of_two_le R hk)).of_iso
      (freeLoopHomotopyEquiv.singularHomologyIso R k)

/-- **The homology of the Moore free loop space of the circle**: `H_k(𝓛S¹; R)` is the coproduct,
over the degrees `n ∈ ℤ`, of copies of `H_k(S¹; R)`. -/
def mooreFreeLoopSingularHomologyIso :
    ((singularHomologyFunctor C k).obj R).obj (TopCat.of (MooreFreeLoopSpace Circle)) ≅
      ∐ fun _ : ℤ ↦ ((singularHomologyFunctor C k).obj R).obj (TopCat.of Circle) :=
  (MooreFreeLoopSpace.homotopyEquivCircleMap Circle).singularHomologyIso R k ≪≫
    freeLoopSingularHomologyIso R k

/-- The summand of index `n` of `Circle.mooreFreeLoopSingularHomologyIso` is the homology of the
circle mapped into the Moore free loop space by `w ↦ (z ↦ w zⁿ)`, followed by the homotopy inverse
of `MooreFreeLoopSpace.homotopyEquivCircleMap`. -/
theorem ι_mooreFreeLoopSingularHomologyIso_inv (n : ℤ) :
    Sigma.ι _ n ≫ (mooreFreeLoopSingularHomologyIso R k).inv =
      ((singularHomologyFunctor C k).obj R).map
        (TopCat.ofHom ((MooreFreeLoopSpace.homotopyEquivCircleMap Circle).symm.toFun.comp
          (freeLoopHomotopyEquiv.symm.toFun.comp (.sigmaMk n)))) := by
  rw [mooreFreeLoopSingularHomologyIso, Iso.trans_inv, ← Category.assoc,
    ι_freeLoopSingularHomologyIso_inv, ContinuousMap.HomotopyEquiv.singularHomologyIso_inv,
    ← Functor.map_comp]
  -- `invFun` is the forward map of `symm`, so both sides are the same composite.
  rfl

/-- The Moore free loop space of the circle has no homology in degrees `k ≥ 2`. -/
theorem isZero_singularHomology_mooreFreeLoopSpace_of_two_le {k : ℕ} (hk : 2 ≤ k) :
    IsZero (((singularHomologyFunctor C k).obj R).obj
      (TopCat.of (MooreFreeLoopSpace Circle))) :=
  (isZero_singularHomology_freeLoop_of_two_le R hk).of_iso
    ((MooreFreeLoopSpace.homotopyEquivCircleMap Circle).singularHomologyIso R k)

end Circle

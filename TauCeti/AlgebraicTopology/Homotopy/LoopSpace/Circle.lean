/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.AB
public import Mathlib.Algebra.Category.ModuleCat.Products
public import Mathlib.Algebra.DirectSum.Finsupp
public import Mathlib.AlgebraicTopology.SingularHomology.HomologyZero
public import TauCeti.AlgebraicTopology.Singular.Additivity
public import TauCeti.AlgebraicTopology.Singular.Circle
public import TauCeti.AlgebraicTopology.Singular.Homotopy.Invariance
public import TauCeti.AlgebraicTopology.Singular.Sphere
public import TauCeti.Topology.Circle.FreeLoop
public import TauCeti.Topology.PathSpace.Moore.Comparison.FreeLoop

/-!
# The singular homology of the free loop space of the circle

The free loop space `𝓛S¹ = C(S¹, S¹)` is homotopy equivalent to `ℤ × S¹`, a loop going to its
degree and its value at `1` (`Circle.freeLoopHomotopyEquiv`). So its singular homology is a
coproduct, indexed by the degree, of copies of the homology of the circle. The summand of
degree `m` is included by the map `z ↦ (w ↦ z * w ^ m)` from the circle onto the component of the
loops of degree `m` (`Circle.isColimitCofanSingularHomologyFreeLoop`). This holds for
coefficients in any abelian category in which coproducts indexed by `ℤ` are exact.

Consequently `Hₙ(𝓛S¹; R)` is a coproduct of copies of `R`, one for each integer, in degrees `0`
and `1`, and vanishes in degrees `n ≥ 2`. For coefficients in a module `M` over a commutative ring
`k` this is `Hₙ(𝓛S¹; M) ≃ (ℤ →₀ M)` for `n ≤ 1`; for `M = k = ℤ` both groups are the group ring
`ℤ[ℤ]`. The same holds for the free Moore loop space `MooreFreeLoopSpace S¹`, which is homotopy
equivalent to `C(S¹, S¹)` (`TauCeti.MooreFreeLoopSpace.homotopyEquivCircleMap`).

## Main results

* `Circle.isColimitCofanSingularHomologyFreeLoop`: `Hₙ(𝓛S¹; R)` is the coproduct over `m : ℤ`
  of `Hₙ(S¹; R)`, along the inclusions of the components of degree `m`.
* `Circle.singularHomologyFreeLoopIso`: the resulting isomorphism `Hₙ(𝓛S¹; R) ≅ ∐_ℤ Hₙ(S¹; R)`,
  and `Circle.singularHomologyMooreFreeLoopIso` for the Moore model.
* `Circle.singularHomologyZeroFreeLoopIso`, `Circle.singularHomologyOneFreeLoopIso`:
  `H₀(𝓛S¹; R) ≅ ∐_ℤ R` and `H₁(𝓛S¹; R) ≅ ∐_ℤ R`, through the augmentation and
  `Circle.singularHomologyOneIso : H₁(S¹; R) ≅ R` on each component.
* `Circle.isZero_singularHomology_freeLoop`: `Hₙ(𝓛S¹; R) = 0` for `n ≥ 2`.
* `Circle.singularHomologyZeroFreeLoopLinearEquiv`, `Circle.singularHomologyOneFreeLoopLinearEquiv`:
  `H₀(𝓛S¹; M) ≃ₗ[k] (ℤ →₀ M)` and `H₁(𝓛S¹; M) ≃ₗ[k] (ℤ →₀ M)`.

## References

* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, §4, where `SH_*(T*S¹)` is compared with
  `H_*(𝓛S¹)`.
* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, §2.1 and Proposition 1.30.
-/

public section

noncomputable section

open CategoryTheory Limits AlgebraicTopology TauCeti

universe u v

namespace Circle

variable {C : Type u} [Category.{v} C] [HasCoproducts.{0} C] [Abelian C]
  [HasExactColimitsOfShape (Discrete ℤ) C] (R : C)

/-- **The homology of the free loop space of the circle.** With coefficients in an abelian
category in which coproducts indexed by `ℤ` are exact, `Hₙ(C(S¹, S¹); R)` is the coproduct over
`m : ℤ` of copies of `Hₙ(S¹; R)`, the copy of index `m` being included along the map
`z ↦ (w ↦ z * w ^ m)` onto the loops of degree `m`. -/
def isColimitCofanSingularHomologyFreeLoop (n : ℕ) :
    IsColimit (Cofan.mk (((singularHomologyFunctor C n).obj R).obj (TopCat.of C(Circle, Circle)))
      (fun m : ℤ ↦ ((singularHomologyFunctor C n).obj R).map
        (TopCat.ofHom (freeLoopComponentInclusion m)))) :=
  (isColimitCofanSingularHomology (fun _ : ℤ ↦ TopCat.of Circle) C R n).ofIsoColimit
    (Cofan.ext (sigmaFreeLoopHomotopyEquiv.singularHomologyIso R n) fun m ↦ by
      rw [cofan_mk_inj, cofan_mk_inj, ContinuousMap.HomotopyEquiv.singularHomologyIso_hom,
        ← Functor.map_comp]
      congr 1
      ext z w
      simp)

/-- The homology of the free loop space of the circle is the coproduct over the degree of copies
of the homology of the circle. -/
def singularHomologyFreeLoopIso (n : ℕ) :
    ((singularHomologyFunctor C n).obj R).obj (TopCat.of C(Circle, Circle)) ≅
      ∐ fun _ : ℤ ↦ ((singularHomologyFunctor C n).obj R).obj (TopCat.of Circle) :=
  (isColimitCofanSingularHomologyFreeLoop R n).coconePointUniqueUpToIso (colimit.isColimit _)

/-- The inclusion of the component of degree `m` followed by `Circle.singularHomologyFreeLoopIso`
is the inclusion of the summand of index `m`. -/
@[reassoc (attr := simp)]
theorem map_freeLoopComponentInclusion_singularHomologyFreeLoopIso_hom (n : ℕ) (m : ℤ) :
    ((singularHomologyFunctor C n).obj R).map (TopCat.ofHom (freeLoopComponentInclusion m)) ≫
      (singularHomologyFreeLoopIso R n).hom =
        Sigma.ι (fun _ : ℤ ↦ ((singularHomologyFunctor C n).obj R).obj (TopCat.of Circle)) m :=
  (isColimitCofanSingularHomologyFreeLoop R n).comp_coconePointUniqueUpToIso_hom
    (colimit.isColimit _) ⟨m⟩

/-- The homology of the free Moore loop space of the circle is the coproduct over the degree of
copies of the homology of the circle. -/
def singularHomologyMooreFreeLoopIso (n : ℕ) :
    ((singularHomologyFunctor C n).obj R).obj (TopCat.of (MooreFreeLoopSpace Circle)) ≅
      ∐ fun _ : ℤ ↦ ((singularHomologyFunctor C n).obj R).obj (TopCat.of Circle) :=
  (MooreFreeLoopSpace.homotopyEquivCircleMap Circle).singularHomologyIso R n ≪≫
    singularHomologyFreeLoopIso R n

/-- `H₀(𝓛S¹; R)` is a coproduct of copies of `R`, one for each degree. -/
def singularHomologyZeroFreeLoopIso :
    ((singularHomologyFunctor C 0).obj R).obj (TopCat.of C(Circle, Circle)) ≅ ∐ fun _ : ℤ ↦ R :=
  singularHomologyFreeLoopIso R 0 ≪≫
    Sigma.mapIso fun _ ↦ asIso ((TopCat.of Circle).singularHomology₀ε R)

/-- On the component of degree `m`, the isomorphism `Circle.singularHomologyZeroFreeLoopIso` is the
augmentation of the circle into the summand of index `m`. -/
@[reassoc (attr := simp)]
theorem map_freeLoopComponentInclusion_singularHomologyZeroFreeLoopIso_hom (m : ℤ) :
    ((singularHomologyFunctor C 0).obj R).map (TopCat.ofHom (freeLoopComponentInclusion m)) ≫
      (singularHomologyZeroFreeLoopIso R).hom =
        (TopCat.of Circle).singularHomology₀ε R ≫ Sigma.ι (fun _ : ℤ ↦ R) m := by
  simp [singularHomologyZeroFreeLoopIso]

/-- `H₁(𝓛S¹; R)` is a coproduct of copies of `R`, one for each degree. -/
def singularHomologyOneFreeLoopIso :
    ((singularHomologyFunctor C 1).obj R).obj (TopCat.of C(Circle, Circle)) ≅ ∐ fun _ : ℤ ↦ R :=
  singularHomologyFreeLoopIso R 1 ≪≫ Sigma.mapIso fun _ ↦ singularHomologyOneIso R

/-- On the component of degree `m`, the isomorphism `Circle.singularHomologyOneFreeLoopIso` is
`Circle.singularHomologyOneIso` into the summand of index `m`. -/
@[reassoc (attr := simp)]
theorem map_freeLoopComponentInclusion_singularHomologyOneFreeLoopIso_hom (m : ℤ) :
    ((singularHomologyFunctor C 1).obj R).map (TopCat.ofHom (freeLoopComponentInclusion m)) ≫
      (singularHomologyOneFreeLoopIso R).hom =
        (singularHomologyOneIso R).hom ≫ Sigma.ι (fun _ : ℤ ↦ R) m := by
  simp [singularHomologyOneFreeLoopIso]

/-- The homology of the free loop space of the circle vanishes in degrees at least two. -/
theorem isZero_singularHomology_freeLoop (j : ℕ) :
    IsZero (((singularHomologyFunctor C (j + 2)).obj R).obj (TopCat.of C(Circle, Circle))) :=
  (isColimitCofanSingularHomologyFreeLoop R (j + 2)).isZero_pt
    (Functor.isZero _ fun _ ↦ (isZero_singularHomologyFunctor_topCatSphere_of_ne R
      (n := 1) (q := j + 1) (by omega)).of_iso
        (((singularHomologyFunctor C (j + 2)).obj R).mapIso sphereOneIsoCircleUnlifted).symm)

section ModuleCat

variable {k : Type u} [CommRing k] (M : ModuleCat.{u} k)

/-- An isomorphism onto `∐_ℤ M` in `ModuleCat`, read as a linear equivalence with `ℤ →₀ M`. -/
private def coprodLinearEquiv {X : ModuleCat.{u} k} (e : X ≅ ∐ fun _ : ℤ ↦ M) :
    X ≃ₗ[k] (ℤ →₀ M) :=
  (e ≪≫ ModuleCat.coprodIsoDirectSum _).toLinearEquiv.trans (finsuppLEquivDirectSum k M ℤ).symm

/-- If `f ≫ e.hom` is `g` into the summand of index `m`, then `coprodLinearEquiv M e` sends `f y`
to `g y` placed at `m`. -/
private theorem coprodLinearEquiv_apply {X Y : ModuleCat.{u} k} (e : X ≅ ∐ fun _ : ℤ ↦ M)
    {f : Y ⟶ X} {g : Y ⟶ M} {m : ℤ} (h : f ≫ e.hom = g ≫ Sigma.ι (fun _ : ℤ ↦ M) m) (y : Y) :
    coprodLinearEquiv M e (f y) = Finsupp.single m (g y) := by
  have h' := congr(($h ≫ (ModuleCat.coprodIsoDirectSum _).hom).hom y)
  simp only [Category.assoc, ModuleCat.ι_coprodIsoDirectSum_hom, ModuleCat.hom_comp,
    LinearMap.comp_apply, ModuleCat.hom_ofHom] at h'
  simp only [coprodLinearEquiv, LinearEquiv.trans_apply]
  -- the linear equivalence of a composite isomorphism applies the two isomorphisms in turn
  exact (congrArg _ h').trans (finsuppLEquivDirectSum_symm_lof k M (ι := ℤ) m _)

/-- `H₀(𝓛S¹; M)` is the module `ℤ →₀ M` of finitely supported families indexed by the degree; for
`M = k` this is the group algebra `k[ℤ]`. -/
def singularHomologyZeroFreeLoopLinearEquiv :
    ((singularHomologyFunctor (ModuleCat.{u} k) 0).obj M).obj (TopCat.of C(Circle, Circle)) ≃ₗ[k]
      (ℤ →₀ M) :=
  coprodLinearEquiv M (singularHomologyZeroFreeLoopIso M)

/-- `H₁(𝓛S¹; M)` is the module `ℤ →₀ M` of finitely supported families indexed by the degree; for
`M = k` this is the group algebra `k[ℤ]`. -/
def singularHomologyOneFreeLoopLinearEquiv :
    ((singularHomologyFunctor (ModuleCat.{u} k) 1).obj M).obj (TopCat.of C(Circle, Circle)) ≃ₗ[k]
      (ℤ →₀ M) :=
  coprodLinearEquiv M (singularHomologyOneFreeLoopIso M)

/-- On the component of degree `m`, `Circle.singularHomologyZeroFreeLoopLinearEquiv` sends a class
to its augmentation placed at `m`. -/
@[simp]
theorem singularHomologyZeroFreeLoopLinearEquiv_map (m : ℤ)
    (x : ((singularHomologyFunctor (ModuleCat.{u} k) 0).obj M).obj (TopCat.of Circle)) :
    singularHomologyZeroFreeLoopLinearEquiv M
        (((singularHomologyFunctor (ModuleCat.{u} k) 0).obj M).map
          (TopCat.ofHom (freeLoopComponentInclusion m)) x) =
      Finsupp.single m ((TopCat.of Circle).singularHomology₀ε M x) :=
  coprodLinearEquiv_apply M _
    (map_freeLoopComponentInclusion_singularHomologyZeroFreeLoopIso_hom M m) x

/-- On the component of degree `m`, `Circle.singularHomologyOneFreeLoopLinearEquiv` sends a class
to its image under `Circle.singularHomologyOneIso` placed at `m`. -/
@[simp]
theorem singularHomologyOneFreeLoopLinearEquiv_map (m : ℤ)
    (x : ((singularHomologyFunctor (ModuleCat.{u} k) 1).obj M).obj (TopCat.of Circle)) :
    singularHomologyOneFreeLoopLinearEquiv M
        (((singularHomologyFunctor (ModuleCat.{u} k) 1).obj M).map
          (TopCat.ofHom (freeLoopComponentInclusion m)) x) =
      Finsupp.single m ((singularHomologyOneIso M).hom x) :=
  coprodLinearEquiv_apply M _
    (map_freeLoopComponentInclusion_singularHomologyOneFreeLoopIso_hom M m) x

end ModuleCat

end Circle

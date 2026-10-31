/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Module.ZLattice.Quotient
public import TauCeti.AlgebraicTopology.Singular.Torus.Exterior
public import TauCeti.AlgebraicTopology.Singular.Torus.Lattice
public import TauCeti.Topology.Category.TopCat.MonObj
public import TauCeti.Topology.Circle.AddCircle

/-!
# The homology of a lattice quotient is the exterior algebra on the lattice

Let `L : Submodule ℤ E` be a full lattice, `IsZLattice ℝ L`, in a finite-dimensional real normed
space `E`, and let `E / L` be the standard orbit space `AddAction.orbitRel.Quotient L E`, for
instance a complex torus. This file proves that its integral singular homology is the exterior
algebra on the lattice: `Hₙ(E / L; ℤ) ≃ ⋀ⁿ L` for every `n`
(`Submodule.orbitRelQuotientHomologyEquiv`), naturally in the maps of quotients induced by
continuous lattice-preserving additive maps
(`Submodule.orbitRelQuotientHomologyEquiv_singularHomologyMap`).

The quotient `E / L` is a commutative topological group
(`Submodule.instIsTopologicalAddGroupOrbitRelQuotient`). Monoid objects of `TopCat` are
multiplicative, so its Pontryagin product lives on `TopCat.of (Multiplicative (E / L))`, which is
the same topological space as `E / L`. The Pontryagin map `⋀ⁿ H₁(E / L; ℤ) → Hₙ(E / L; ℤ)`
(`TopCat.pontryaginExteriorPower`) is bijective
(`Submodule.bijective_pontryaginExteriorPower_orbitRelQuotient`): the circle coordinates of a
lattice basis (`Module.Basis.orbitRelQuotientLatticeEquiv`) identify `E / L` with the torus `ι → S¹`
as topological groups, and for the torus this is `TauCeti.bijective_pontryaginExteriorPower_torus`.
Composing with the exterior powers of `H₁(E / L; ℤ) ≃ L`
(`AddSubgroup.orbitRelQuotientFirstHomologyEquiv`) gives the isomorphism. Its inverse sends
`l₁ ∧ ⋯ ∧ lₙ` to the Pontryagin product of the classes of `l₁, …, lₙ`
(`Submodule.orbitRelQuotientHomologyEquiv_symm_ιMulti`), and in degree one it is the
identification of first homology with `L` (`Submodule.coe_oneEquiv_orbitRelQuotientHomologyEquiv`).

For complex tori, the naturality covers the holomorphic homomorphisms `E / L → E' / L'` induced
by complex linear maps `f` with `f(L) ⊆ L'`: their restriction of scalars to `ℤ` is continuous
since `E` is finite-dimensional.

Singular chains with integer coefficients are defined on spaces in the lowest universe, so `E` is a
type in `Type`.

## Main results

* `Submodule.bijective_pontryaginExteriorPower_orbitRelQuotient`: the Pontryagin map
  `⋀ⁿ H₁(E / L; ℤ) → Hₙ(E / L; ℤ)` is bijective.
* `Submodule.orbitRelQuotientHomologyEquiv`: the isomorphism `Hₙ(E / L; ℤ) ≃ₗ[ℤ] ⋀ⁿ L`.
* `Submodule.orbitRelQuotientHomologyEquiv_symm_ιMulti`,
  `Submodule.coe_oneEquiv_orbitRelQuotientHomologyEquiv`: the inverse on exterior products, and
  agreement with `AddSubgroup.orbitRelQuotientFirstHomologyEquiv` in degree one.
* `Submodule.orbitRelQuotientHomologyEquiv_singularHomologyMap`: naturality in lattice-preserving
  maps.

## References

* Christina Birkenhake and Herbert Lange, *Complex Abelian Varieties*, second edition,
  Grundlehren der mathematischen Wissenschaften 302, Springer, 2004, Chapter 1, Section 1.3,
  for the dual statement in cohomology.
* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 3.C, the Pontryagin ring of a torus.
-/

public section

noncomputable section

open CategoryTheory MonoidalCategory AlgebraicTopology TauCeti

namespace Submodule

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] (L : Submodule ℤ E)
  [DiscreteTopology L]

/-! ### The exterior powers of the lattice in homology -/

/-- `AddSubgroup.orbitRelQuotientFirstHomologyEquiv`, with values in `L` itself and read on the
multiplicative form of `E / L`, the commutative monoid object carrying the Pontryagin product. -/
private def firstHomologyEquiv :
    ((singularHomologyFunctor (ModuleCat.{0} ℤ) 1).obj (𝟙_ _)).obj
      (TopCat.of (Multiplicative (AddAction.orbitRel.Quotient L E))) ≃ₗ[ℤ] L :=
  L.toAddSubgroup.orbitRelQuotientFirstHomologyEquiv

/-- The map `⋀ⁿ L → Hₙ(E / L; ℤ)` sending `l₁ ∧ ⋯ ∧ lₙ` to the Pontryagin product of the classes
of `l₁, …, lₙ`. -/
private def exteriorPowerToHomology (n : ℕ) :
    ⋀[ℤ]^n L →ₗ[ℤ] ((singularHomologyFunctor (ModuleCat.{0} ℤ) n).obj (𝟙_ _)).obj
      (TopCat.of (Multiplicative (AddAction.orbitRel.Quotient L E))) :=
  TopCat.pontryaginExteriorPower ℤ (TopCat.of (Multiplicative (AddAction.orbitRel.Quotient L E)))
      n ∘ₗ
    exteriorPower.map n (firstHomologyEquiv L).symm.toLinearMap

private theorem exteriorPowerToHomology_ιMulti {n : ℕ} (v : Fin n → L) :
    exteriorPowerToHomology L n (exteriorPower.ιMulti ℤ n v) =
      TopCat.pontryaginMultilinear ℤ
        (TopCat.of (Multiplicative (AddAction.orbitRel.Quotient L E))) n
        fun i ↦ (firstHomologyEquiv L).symm (v i) := by
  simp [exteriorPowerToHomology, exteriorPower.map_apply_ιMulti, Function.comp_def]

private theorem firstHomologyEquiv_exteriorPowerToHomology_one (w : ⋀[ℤ]^1 L) :
    firstHomologyEquiv L (exteriorPowerToHomology L 1 w) = exteriorPower.oneEquiv ℤ L w := by
  have : (firstHomologyEquiv L).toLinearMap ∘ₗ exteriorPowerToHomology L 1 =
      (exteriorPower.oneEquiv ℤ L).toLinearMap :=
    exteriorPower.linearMap_ext (AlternatingMap.ext fun v ↦ by
      simp [exteriorPowerToHomology_ιMulti, TopCat.pontryaginMultilinear_one_apply,
        exteriorPower.oneEquiv_ιMulti])
  exact LinearMap.congr_fun this w

section Naturality

variable {E' : Type} [NormedAddCommGroup E'] [NormedSpace ℝ E'] (L' : Submodule ℤ E')
  [DiscreteTopology L'] {f : E →ₗ[ℤ] E'} (hf : Continuous f) (hfL : L ≤ L'.comap f)

/-- The map of quotients induced by `f`, as a morphism of the monoid objects of `TopCat` given by
the multiplicative forms of the quotients. -/
private abbrev orbitRelQuotientMapTop :
    TopCat.of (Multiplicative (AddAction.orbitRel.Quotient L E)) ⟶
      TopCat.of (Multiplicative (AddAction.orbitRel.Quotient L' E')) :=
  TopCat.ofHom (({ toMonoidHom := (L.orbitRelQuotientMap L' f hfL).toMultiplicative
                   continuous_toFun := L.continuous_orbitRelQuotientMap L' hfL hf } :
      Multiplicative (AddAction.orbitRel.Quotient L E) →ₜ*
        Multiplicative (AddAction.orbitRel.Quotient L' E')) :
    C(Multiplicative (AddAction.orbitRel.Quotient L E),
      Multiplicative (AddAction.orbitRel.Quotient L' E')))

private theorem exteriorPowerToHomology_naturality (n : ℕ) (w : ⋀[ℤ]^n L) :
    ((singularHomologyFunctor (ModuleCat.{0} ℤ) n).obj (𝟙_ _)).map
        (orbitRelQuotientMapTop L L' hf hfL) (exteriorPowerToHomology L n w) =
      exteriorPowerToHomology L' n (exteriorPower.map n (f.restrict hfL) w) := by
  -- on first homology, the induced map is the restriction of `f` to the lattices
  have h₁ : (((singularHomologyFunctor (ModuleCat.{0} ℤ) 1).obj (𝟙_ _)).map
        (orbitRelQuotientMapTop L L' hf hfL)).hom ∘ₗ (firstHomologyEquiv L).symm.toLinearMap =
      (firstHomologyEquiv L').symm.toLinearMap ∘ₗ f.restrict hfL := by
    ext l
    apply (firstHomologyEquiv L').injective
    apply Subtype.ext
    simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
      LinearEquiv.apply_symm_apply, LinearMap.coe_restrict_apply]
    exact (L.toAddSubgroup.orbitRelQuotientFirstHomologyEquiv_singularHomologyMap
      L'.toAddSubgroup f.toAddMonoidHom hf ⟨_, L.continuous_orbitRelQuotientMap L' hfL hf⟩
      (fun v ↦ L.orbitRelQuotientMap_mk L' f hfL v) _).trans
        (congrArg f (congrArg Subtype.val ((firstHomologyEquiv L).apply_symm_apply l)))
  -- hence on its exterior powers, the exterior powers of the restriction of `f`
  have h₂ := LinearMap.congr_fun (congrArg (exteriorPower.map n) h₁) w
  simp only [exteriorPower.map_comp, LinearMap.comp_apply] at h₂
  have := LinearMap.congr_fun (TopCat.pontryaginExteriorPower_naturality (k := ℤ)
    (orbitRelQuotientMapTop L L' hf hfL) n)
    (exteriorPower.map n (firstHomologyEquiv L).symm.toLinearMap w)
  simp only [LinearMap.comp_apply, h₂] at this
  exact this

end Naturality

/-! ### Full lattices -/

variable [FiniteDimensional ℝ E] [IsZLattice ℝ L]

section CircleCoordinates

variable {ι : Type} [Fintype ι] (b : Module.Basis ι ℤ L)

/-- Circle coordinates, as a continuous homomorphism from the multiplicative form of `E / L`: the
identification `Module.Basis.orbitRelQuotientLatticeEquiv` of `E / L` with the additive torus, read
on the unit circles through `TauCeti.unitAddTorusEquivPiCircle`. -/
private def circleCoordMul :
    Multiplicative (AddAction.orbitRel.Quotient L E) →ₜ* (ι → ULift Circle) where
  toMonoidHom := (MonoidHom.compLeft MulEquiv.ulift.symm.toMonoidHom ι).comp <| MulEquiv.toMonoidHom
    (b.orbitRelQuotientLatticeEquiv.trans unitAddTorusEquivPiCircle).toAddEquiv.toMultiplicative
  continuous_toFun := continuous_pi fun i ↦ continuous_uliftUp.comp <|
    (continuous_apply i).comp <| continuous_toMul.comp <|
      (b.orbitRelQuotientLatticeEquiv.trans unitAddTorusEquivPiCircle).continuous.comp
        continuous_toAdd

end CircleCoordinates

/-- **The homology of `E / L` is the exterior algebra on its first homology.** For a full lattice
`L` in a finite-dimensional real normed space `E`, the Pontryagin map
`⋀ⁿ H₁(E / L; ℤ) → Hₙ(E / L; ℤ)` of the commutative topological group `E / L`, sending
`a₁ ∧ ⋯ ∧ aₙ` to the Pontryagin product `a₁ ⋯ aₙ`, is bijective. -/
theorem bijective_pontryaginExteriorPower_orbitRelQuotient (n : ℕ) :
    Function.Bijective (TopCat.pontryaginExteriorPower ℤ
      (TopCat.of (Multiplicative (AddAction.orbitRel.Quotient L E))) n) := by
  let b := Module.Free.chooseBasis ℤ L
  -- circle coordinates identify `E / L` with the torus `ι → S¹` as topological groups
  let f := TopCat.ofHom (circleCoordMul L b : C(Multiplicative (AddAction.orbitRel.Quotient L E),
    Module.Free.ChooseBasisIndex ℤ L → ULift Circle))
  -- `Multiplicative (E / L)` is a type synonym carrying the topology of `E / L`
  have : IsIso f := (TopCat.isIso_iff_isHomeomorph f).2 <|
    (isHomeomorph_iff_continuous_bijective (X := AddAction.orbitRel.Quotient L E)).2
      ⟨(circleCoordMul L b).continuous,
        (Equiv.piCongrRight fun _ ↦ Equiv.ulift.symm).bijective.comp
          (b.orbitRelQuotientLatticeEquiv.trans unitAddTorusEquivPiCircle).bijective⟩
  exact TopCat.bijective_pontryaginExteriorPower_of_isIso f
    (bijective_pontryaginExteriorPower_torus ℤ _ n)

private theorem bijective_exteriorPowerToHomology (n : ℕ) :
    Function.Bijective (exteriorPowerToHomology L n) :=
  (bijective_pontryaginExteriorPower_orbitRelQuotient L n).comp
    (exteriorPower.map_bijective (firstHomologyEquiv L).symm.bijective)

/-- **The integral homology of `E / L` is the exterior algebra on `L`.** For a full lattice `L`
in a finite-dimensional real normed space `E`, for instance the period lattice of a complex torus,
`Hₙ(E / L; ℤ) ≃ ⋀ⁿ L` for every `n`. The inverse sends `l₁ ∧ ⋯ ∧ lₙ` to the Pontryagin product of
the classes of `l₁, …, lₙ` (`Submodule.orbitRelQuotientHomologyEquiv_symm_ιMulti`). -/
def orbitRelQuotientHomologyEquiv (n : ℕ) :
    ((singularChains ℤ).obj (TopCat.of (AddAction.orbitRel.Quotient L E))).homology n ≃ₗ[ℤ]
      ⋀[ℤ]^n L :=
  (LinearEquiv.ofBijective _ (bijective_exteriorPowerToHomology L n)).symm

/-- The inverse of `Submodule.orbitRelQuotientHomologyEquiv` sends `l₁ ∧ ⋯ ∧ lₙ` to the
Pontryagin product of the classes of `l₁, …, lₙ` under
`AddSubgroup.orbitRelQuotientFirstHomologyEquiv`. The Pontryagin product is taken on the
multiplicative form of `E / L`; the classes are carried there and back along `ofAdd` and `toAdd`.
-/
@[simp]
theorem orbitRelQuotientHomologyEquiv_symm_ιMulti {n : ℕ} (v : Fin n → L) :
    (L.orbitRelQuotientHomologyEquiv n).symm (exteriorPower.ιMulti ℤ n v) =
      ContinuousMap.singularHomologyMap ℤ n
        (⟨Multiplicative.toAdd, continuous_toAdd⟩ :
          C(Multiplicative (AddAction.orbitRel.Quotient L E), AddAction.orbitRel.Quotient L E))
        (TopCat.pontryaginMultilinear ℤ
          (TopCat.of (Multiplicative (AddAction.orbitRel.Quotient L E))) n
          fun i ↦ ContinuousMap.singularHomologyMap ℤ 1
            (⟨Multiplicative.ofAdd, continuous_ofAdd⟩ :
              C(AddAction.orbitRel.Quotient L E, Multiplicative (AddAction.orbitRel.Quotient L E)))
            (L.toAddSubgroup.orbitRelQuotientFirstHomologyEquiv.symm (v i))) :=
  -- `toAdd` and `ofAdd` are the identity map of the underlying type of `E / L`
  (exteriorPowerToHomology_ιMulti L v).trans <|
    (congrArg (TopCat.pontryaginMultilinear ℤ _ n) <|
      funext fun _ ↦ (ContinuousMap.singularHomologyMap_id _).symm).trans
    (ContinuousMap.singularHomologyMap_id _).symm

/-- In degree one, `Submodule.orbitRelQuotientHomologyEquiv` is the identification
`AddSubgroup.orbitRelQuotientFirstHomologyEquiv` of first homology with the lattice. -/
@[simp]
theorem coe_oneEquiv_orbitRelQuotientHomologyEquiv
    (c : ((singularChains ℤ).obj (TopCat.of (AddAction.orbitRel.Quotient L E))).homology 1) :
    (exteriorPower.oneEquiv ℤ L (L.orbitRelQuotientHomologyEquiv 1 c) : E) =
      L.toAddSubgroup.orbitRelQuotientFirstHomologyEquiv c := by
  obtain ⟨w, rfl⟩ := (L.orbitRelQuotientHomologyEquiv 1).symm.surjective c
  rw [LinearEquiv.apply_symm_apply]
  exact congrArg Subtype.val (firstHomologyEquiv_exteriorPowerToHomology_one L w).symm

variable {E' : Type} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  (L' : Submodule ℤ E') [DiscreteTopology L'] [IsZLattice ℝ L'] {f : E →ₗ[ℤ] E'}

/-- **Naturality.** Let `f : E → E'` be a continuous additive map carrying the full lattice `L`
into the full lattice `L'`. On integral homology, the induced map `E / L → E' / L'` acts as the
exterior powers of the restriction of `f` to the lattices. -/
theorem orbitRelQuotientHomologyEquiv_singularHomologyMap (hf : Continuous f)
    (hfL : L ≤ L'.comap f) (n : ℕ)
    (c : ((singularChains ℤ).obj (TopCat.of (AddAction.orbitRel.Quotient L E))).homology n) :
    L'.orbitRelQuotientHomologyEquiv n (ContinuousMap.singularHomologyMap ℤ n
        ⟨L.orbitRelQuotientMap L' f hfL, L.continuous_orbitRelQuotientMap L' hfL hf⟩ c) =
      exteriorPower.map n (f.restrict hfL) (L.orbitRelQuotientHomologyEquiv n c) := by
  obtain ⟨w, rfl⟩ := (L.orbitRelQuotientHomologyEquiv n).symm.surjective c
  rw [LinearEquiv.apply_symm_apply, ← LinearEquiv.eq_symm_apply]
  -- both sides are read on the multiplicative forms of the quotients, the same spaces
  exact exteriorPowerToHomology_naturality L L' hf hfL n w

end Submodule

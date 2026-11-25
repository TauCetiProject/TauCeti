/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Cohomology.AddCircle
import TauCeti.Algebra.Category.ModuleCat.Monoidal.Unit

/-!
# Line labels on `(ℝ / pℤ) × Y`: integral pullback and dimension

Let `Y` be a space and `X = (ℝ / pℤ) × Y`. A `Spinᶜ` structure on `X` twisted by a Hermitian line
`E` has determinant class `l = 2e - κ`, where `e = c₁(E)` and `κ` is the canonical class, and the
expected dimension of its Seiberg–Witten moduli space is `d(e) = e · e - κ · e`. When `Y` is a
closed oriented three-manifold, the canonical class of the product structure is pulled back from
`Y`, and the energy identity for the unperturbed equations on `X` shows that the moduli space is
empty for a label that is not pulled back from `Y` and has `d(e) ≥ 0`; so the Seiberg–Witten
invariant is supported on labels pulled back from `Y` (Baldridge, Theorem A). The second
cohomology splits as
`H²(X; ℤ) = pr₂^* H²(Y; ℤ) ⊕ θ_p ⌣ pr₂^* H¹(Y; ℤ)`
(`TopCat.singularCohomologyAddCircleProdSlantEquiv`), and the cross summand `H¹(Y; ℤ)` is
torsion-free. This file proves the consequences for labels, for an arbitrary space `Y` and with
every torsion class kept:

* if `κ` is pulled back from `Y`, then `l = 2e - κ` is pulled back from `Y` if and only if `e` is
  (`TauCeti.SeibergWitten.two_smul_sub_mem_range_singularCohomologyMap_snd_addCircle_iff`): the
  cross class of `l` is twice that of `e`, and `H¹(Y; ℤ)` has no `2`-torsion. So a pulled-back
  determinant class forces a pulled-back label, two-torsion of `H²(Y; ℤ)` included;
* the same holds after an injective change of coefficients, such as `ℤ → ℝ`: `e` is pulled back
  from `Y` if and only if the real class of `l` is
  (`homologyMap_two_smul_sub_mem_range_singularCohomologyMap_snd_addCircle_iff`). For a label
  that is not pulled back, the real class of `l` therefore has a nonzero cross component;
* for `κ` pulled back and a homology class `y ∈ H₃(Y; ℤ)`, the pairing against `[ℝ / pℤ] × y`
  gives `d(e) = ⟨(2 b - b_κ) ⌣ c, y⟩`, where `b = e / [s₀]`, `b_κ = κ / [s₀]` are the components
  pulled back from `Y` and `c = e / [ℝ / pℤ]` is the cross component of `e`
  (`TauCeti.SeibergWitten.singularCupPairing_self_sub_addCircle_singularHomologyCross`). In
  particular `d(e) = 0` for every pulled-back label
  (`TauCeti.SeibergWitten.singularCupPairing_self_sub_eq_zero_of_mem_range`), and
  `l · l = 4 d(e)` for every label
  (`TauCeti.SeibergWitten.singularCupPairing_two_smul_sub_self_addCircle_singularHomologyCross`).

When `y = [Y]` is the fundamental class of a closed oriented three-manifold, `[ℝ / pℤ] × [Y]` is
a fundamental class of `X`, the pairing against it is the intersection form of `X`, and these are
the statements that pulled-back labels have `e · e = κ · e = 0` and that `d(e) = l · l / 4`,
which on `X` also follows from `χ(X) = σ(X) = 0`.

## References

* A. Hatcher, *Algebraic Topology*, Theorem 3.15 (the Künneth formula).
* S. Baldridge, *Seiberg–Witten invariants, orbifolds, and circle actions*, Trans. Amer. Math.
  Soc. 355 (2003), 1669–1697.
-/

public section

noncomputable section

open CategoryTheory Limits MonoidalCategory AlgebraicTopology

-- As in `TauCeti.AlgebraicTopology.Cohomology.AddCircle`: for `k = ℤ`, instance search would
-- otherwise find the `ℤ`-linear structure `Linear.preadditiveIntLinear` of a preadditive category.
attribute [local instance 1100] ModuleCat.instLinear

namespace TauCeti.SeibergWitten

variable {p : ℝ} [Fact (0 < p)] {Y : TopCat.{0}}
  {e κ : (TopCat.of (AddCircle p) ⊗ Y).singularCohomology (𝟙_ (ModuleCat.{0} ℤ)) ℤ
    (𝟙_ (ModuleCat.{0} ℤ)) 2}

/-- **Integral pullback of labels on `(ℝ / pℤ) × Y`**: if the class `κ ∈ H²((ℝ / pℤ) × Y; ℤ)` is
pulled back from `Y`, then `l = 2e - κ` is pulled back from `Y` if and only if `e` is. The cross
class of `l` is twice that of `e`, and `H¹(Y; ℤ)` is torsion-free. -/
theorem two_smul_sub_mem_range_singularCohomologyMap_snd_addCircle_iff
    (hκ : κ ∈ LinearMap.range (TopCat.singularCohomologyMap (R := 𝟙_ (ModuleCat.{0} ℤ)) (k := ℤ)
      (M := 𝟙_ (ModuleCat.{0} ℤ)) (CartesianMonoidalCategory.snd (TopCat.of (AddCircle p)) Y)
        2).hom) :
    (2 : ℤ) • e - κ ∈ LinearMap.range (TopCat.singularCohomologyMap (R := 𝟙_ (ModuleCat.{0} ℤ))
        (k := ℤ) (M := 𝟙_ (ModuleCat.{0} ℤ))
        (CartesianMonoidalCategory.snd (TopCat.of (AddCircle p)) Y) 2).hom ↔
      e ∈ LinearMap.range (TopCat.singularCohomologyMap (R := 𝟙_ (ModuleCat.{0} ℤ)) (k := ℤ)
        (M := 𝟙_ (ModuleCat.{0} ℤ)) (CartesianMonoidalCategory.snd (TopCat.of (AddCircle p)) Y)
          2).hom := by
  rw [Submodule.sub_mem_iff_left _ hκ]
  exact TopCat.zsmul_mem_range_singularCohomologyMap_snd_addCircle_iff _ Y (n := 1) two_ne_zero e

/-- **Pullback of labels on `(ℝ / pℤ) × Y` through an injective change of coefficients**: let
`g : ℤ ⟶ M'` be injective, for instance `ℤ → ℝ`, and let `κ ∈ H²((ℝ / pℤ) × Y; ℤ)` be pulled back
from `Y`. Then `e` is pulled back from `Y` if and only if the image of `l = 2e - κ` in
`H²((ℝ / pℤ) × Y; M')` is. So the real determinant class of a label that is not pulled back has a
nonzero cross component. -/
theorem homologyMap_two_smul_sub_mem_range_singularCohomologyMap_snd_addCircle_iff
    {M' : ModuleCat.{0} ℤ} (g : 𝟙_ (ModuleCat.{0} ℤ) ⟶ M') (hg : Function.Injective g)
    (hκ : κ ∈ LinearMap.range (TopCat.singularCohomologyMap (R := 𝟙_ (ModuleCat.{0} ℤ)) (k := ℤ)
      (M := 𝟙_ (ModuleCat.{0} ℤ)) (CartesianMonoidalCategory.snd (TopCat.of (AddCircle p)) Y)
        2).hom) :
    HomologicalComplex.homologyMap (((TopCat.toSSet.obj (TopCat.of (AddCircle p) ⊗ Y)).chainComplex
        (𝟙_ (ModuleCat.{0} ℤ))).linearYonedaObjMap ℤ g) 2 ((2 : ℤ) • e - κ) ∈
      LinearMap.range (TopCat.singularCohomologyMap (R := 𝟙_ (ModuleCat.{0} ℤ)) (k := ℤ)
        (M := M') (CartesianMonoidalCategory.snd (TopCat.of (AddCircle p)) Y) 2).hom ↔
      e ∈ LinearMap.range (TopCat.singularCohomologyMap (R := 𝟙_ (ModuleCat.{0} ℤ)) (k := ℤ)
        (M := 𝟙_ (ModuleCat.{0} ℤ)) (CartesianMonoidalCategory.snd (TopCat.of (AddCircle p)) Y)
          2).hom := by
  exact (TopCat.homologyMap_linearYonedaObjMap_mem_range_singularCohomologyMap_snd_addCircle_iff
    (n := 1) Y g (Y.injective_homologyMap_linearYonedaObjMap_one g hg) _).trans
      (two_smul_sub_mem_range_singularCohomologyMap_snd_addCircle_iff hκ)

/-- **The dimension of a label on `(ℝ / pℤ) × Y`**: let `κ ∈ H²((ℝ / pℤ) × Y; ℤ)` be pulled back
from `Y`, and pair against `[ℝ / pℤ] × y` for a class `y ∈ H₃(Y; ℤ)`. Write
`e = pr₂^* b + θ_p ⌣ pr₂^* c` and `κ = pr₂^* b_κ` in the decomposition
`TopCat.singularCohomologyAddCircleProdSlantEquiv` at `s₀`. Then
`d(e) = e · e - κ · e = ⟨(2 b - b_κ) ⌣ c, y⟩`: the dimension of the label is the pairing of the
component of `l = 2e - κ` pulled back from `Y` with the cross component of `e`. -/
theorem singularCupPairing_self_sub_addCircle_singularHomologyCross (s₀ : AddCircle p)
    (y : ((singularHomologyFunctor (ModuleCat.{0} ℤ) 3).obj (𝟙_ (ModuleCat.{0} ℤ))).obj Y)
    (hκ : κ ∈ LinearMap.range (TopCat.singularCohomologyMap (R := 𝟙_ (ModuleCat.{0} ℤ)) (k := ℤ)
      (M := 𝟙_ (ModuleCat.{0} ℤ)) (CartesianMonoidalCategory.snd (TopCat.of (AddCircle p)) Y)
        2).hom) :
    (TopCat.of (AddCircle p) ⊗ Y).singularCupPairing ℤ (p := 2) (q := 2) (n := 4) rfl
        (((singularHomologyFunctor (ModuleCat.{0} ℤ) 4).map (λ_ (𝟙_ (ModuleCat.{0} ℤ))).hom).app
          (TopCat.of (AddCircle p) ⊗ Y)
          (TopCat.singularHomologyCross (TopCat.of (AddCircle p)) Y (𝟙_ (ModuleCat.{0} ℤ))
            (𝟙_ (ModuleCat.{0} ℤ)) 1 3 4 rfl (AddCircle.fundamentalClass p ⊗ₜ y))) e e -
      (TopCat.of (AddCircle p) ⊗ Y).singularCupPairing ℤ (p := 2) (q := 2) (n := 4) rfl
        (((singularHomologyFunctor (ModuleCat.{0} ℤ) 4).map (λ_ (𝟙_ (ModuleCat.{0} ℤ))).hom).app
          (TopCat.of (AddCircle p) ⊗ Y)
          (TopCat.singularHomologyCross (TopCat.of (AddCircle p)) Y (𝟙_ (ModuleCat.{0} ℤ))
            (𝟙_ (ModuleCat.{0} ℤ)) 1 3 4 rfl (AddCircle.fundamentalClass p ⊗ₜ y))) κ e =
      Y.singularCupPairing ℤ (p := 2) (q := 1) (n := 3) rfl y
        ((2 : ℤ) • (TopCat.singularCohomologyAddCircleProdSlantEquiv _ Y s₀ 1 e).1 -
          (TopCat.singularCohomologyAddCircleProdSlantEquiv _ Y s₀ 1 κ).1)
        (TopCat.singularCohomologyAddCircleProdSlantEquiv _ Y s₀ 1 e).2 := by
  obtain ⟨bκ, rfl⟩ := hκ
  obtain ⟨⟨b, c⟩, rfl⟩ :=
    (TopCat.singularCohomologyAddCircleProdSlantEquiv _ Y s₀ 1).symm.surjective e
  rw [← TopCat.singularCohomologyAddCircleProdSlantEquiv_symm_mk_zero _ Y s₀,
    AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply,
    TopCat.singularCohomologyAddCircleProdSlantEquiv_symm_apply,
    TopCat.singularCohomologyAddCircleProdSlantEquiv_symm_apply,
    TopCat.singularCupPairing_addCircle_singularHomologyCross,
    TopCat.singularCupPairing_addCircle_singularHomologyCross]
  simp only [map_sub, map_zsmul, map_zero, LinearMap.sub_apply, LinearMap.smul_apply]
  ring

/-- **Pulled-back labels on `(ℝ / pℤ) × Y` have dimension zero**: if `e` and `κ` are pulled back
from `Y`, then `e · e - κ · e = 0` against `[ℝ / pℤ] × y`, for every class `y ∈ H₃(Y; ℤ)`. -/
theorem singularCupPairing_self_sub_eq_zero_of_mem_range
    (y : ((singularHomologyFunctor (ModuleCat.{0} ℤ) 3).obj (𝟙_ (ModuleCat.{0} ℤ))).obj Y)
    (he : e ∈ LinearMap.range (TopCat.singularCohomologyMap (R := 𝟙_ (ModuleCat.{0} ℤ)) (k := ℤ)
      (M := 𝟙_ (ModuleCat.{0} ℤ)) (CartesianMonoidalCategory.snd (TopCat.of (AddCircle p)) Y)
        2).hom)
    (hκ : κ ∈ LinearMap.range (TopCat.singularCohomologyMap (R := 𝟙_ (ModuleCat.{0} ℤ)) (k := ℤ)
      (M := 𝟙_ (ModuleCat.{0} ℤ)) (CartesianMonoidalCategory.snd (TopCat.of (AddCircle p)) Y)
        2).hom) :
    (TopCat.of (AddCircle p) ⊗ Y).singularCupPairing ℤ (p := 2) (q := 2) (n := 4) rfl
        (((singularHomologyFunctor (ModuleCat.{0} ℤ) 4).map (λ_ (𝟙_ (ModuleCat.{0} ℤ))).hom).app
          (TopCat.of (AddCircle p) ⊗ Y)
          (TopCat.singularHomologyCross (TopCat.of (AddCircle p)) Y (𝟙_ (ModuleCat.{0} ℤ))
            (𝟙_ (ModuleCat.{0} ℤ)) 1 3 4 rfl (AddCircle.fundamentalClass p ⊗ₜ y))) e e -
      (TopCat.of (AddCircle p) ⊗ Y).singularCupPairing ℤ (p := 2) (q := 2) (n := 4) rfl
        (((singularHomologyFunctor (ModuleCat.{0} ℤ) 4).map (λ_ (𝟙_ (ModuleCat.{0} ℤ))).hom).app
          (TopCat.of (AddCircle p) ⊗ Y)
          (TopCat.singularHomologyCross (TopCat.of (AddCircle p)) Y (𝟙_ (ModuleCat.{0} ℤ))
            (𝟙_ (ModuleCat.{0} ℤ)) 1 3 4 rfl (AddCircle.fundamentalClass p ⊗ₜ y))) κ e = 0 := by
  rw [singularCupPairing_self_sub_addCircle_singularHomologyCross 0 y hκ,
    TopCat.singularCohomologyAddCircleProdSlantEquiv_apply,
    (TopCat.mem_range_singularCohomologyMap_snd_addCircle_iff _ Y e).1 he, map_zero]

/-- **The square of the determinant class of a label on `(ℝ / pℤ) × Y`**: if `κ` is pulled back
from `Y`, then `l = 2e - κ` has `l · l = 4 (e · e - κ · e) = 4 d(e)` against `[ℝ / pℤ] × y`, for
every class `y ∈ H₃(Y; ℤ)`. -/
theorem singularCupPairing_two_smul_sub_self_addCircle_singularHomologyCross
    (y : ((singularHomologyFunctor (ModuleCat.{0} ℤ) 3).obj (𝟙_ (ModuleCat.{0} ℤ))).obj Y)
    (hκ : κ ∈ LinearMap.range (TopCat.singularCohomologyMap (R := 𝟙_ (ModuleCat.{0} ℤ)) (k := ℤ)
      (M := 𝟙_ (ModuleCat.{0} ℤ)) (CartesianMonoidalCategory.snd (TopCat.of (AddCircle p)) Y)
        2).hom) :
    (TopCat.of (AddCircle p) ⊗ Y).singularCupPairing ℤ (p := 2) (q := 2) (n := 4) rfl
        (((singularHomologyFunctor (ModuleCat.{0} ℤ) 4).map (λ_ (𝟙_ (ModuleCat.{0} ℤ))).hom).app
          (TopCat.of (AddCircle p) ⊗ Y)
          (TopCat.singularHomologyCross (TopCat.of (AddCircle p)) Y (𝟙_ (ModuleCat.{0} ℤ))
            (𝟙_ (ModuleCat.{0} ℤ)) 1 3 4 rfl (AddCircle.fundamentalClass p ⊗ₜ y)))
        ((2 : ℤ) • e - κ) ((2 : ℤ) • e - κ) =
      4 * ((TopCat.of (AddCircle p) ⊗ Y).singularCupPairing ℤ (p := 2) (q := 2) (n := 4) rfl
        (((singularHomologyFunctor (ModuleCat.{0} ℤ) 4).map (λ_ (𝟙_ (ModuleCat.{0} ℤ))).hom).app
          (TopCat.of (AddCircle p) ⊗ Y)
          (TopCat.singularHomologyCross (TopCat.of (AddCircle p)) Y (𝟙_ (ModuleCat.{0} ℤ))
            (𝟙_ (ModuleCat.{0} ℤ)) 1 3 4 rfl (AddCircle.fundamentalClass p ⊗ₜ y))) e e -
        (TopCat.of (AddCircle p) ⊗ Y).singularCupPairing ℤ (p := 2) (q := 2) (n := 4) rfl
          (((singularHomologyFunctor (ModuleCat.{0} ℤ) 4).map (λ_ (𝟙_ (ModuleCat.{0} ℤ))).hom).app
            (TopCat.of (AddCircle p) ⊗ Y)
            (TopCat.singularHomologyCross (TopCat.of (AddCircle p)) Y (𝟙_ (ModuleCat.{0} ℤ))
              (𝟙_ (ModuleCat.{0} ℤ)) 1 3 4 rfl (AddCircle.fundamentalClass p ⊗ₜ y))) κ e) := by
  have hκ0 := (TopCat.mem_range_singularCohomologyMap_snd_addCircle_iff _ Y κ).1 hκ
  rw [TopCat.singularCupPairing_self_addCircle_singularHomologyCross 0,
    singularCupPairing_self_sub_addCircle_singularHomologyCross 0 y hκ]
  simp only [map_sub, map_zsmul, TopCat.singularCohomologyAddCircleProdSlantEquiv_apply, hκ0,
    Prod.fst_sub, Prod.snd_sub, Prod.smul_fst, Prod.smul_snd, sub_zero, LinearMap.sub_apply,
    LinearMap.smul_apply, smul_eq_mul]
  ring

end TauCeti.SeibergWitten

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.Basic
public import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.SymmetricAlgebra
public import TauCeti.Geometry.Toric.Algebraic.Fan.Over
public import TauCeti.Geometry.Toric.Algebraic.Fan.ProjectiveSpace.Coordinates
public import TauCeti.LinearAlgebra.SymmetricAlgebra.Grading
public import TauCeti.RingTheory.GradedAlgebra.HomogeneousLocalization.Basic
import TauCeti.RingTheory.Localization.Away

/-!
# The toric scheme of the fan of projective space is `Proj`

Let `b` be an integral basis of the lattice `N`, indexed by `ι`, and let `X_j`, for `j : Option ι`,
be the homogeneous coordinates of projective space `Proj ℂ[X_j]`, the projective spectrum of the
symmetric algebra of `Option ι → ℂ`. The coordinate `X_j` corresponds to the ray generator of the
fan of projective space indexed by `j`. This file identifies the toric scheme of that fan,
`TauCeti.Toric.Fan.algebraicRealization`, with `Proj ℂ[X_j]` over `Spec ℂ`.

On the affine chart of a cone contained in the maximal cone omitting the ray `k`, the ratio
`X_j / X_k` is the monomial of the character `TauCeti.Toric.projectiveSpaceRatioCharacter`. These
monomials are homogeneous coordinates normalized by `X_k = 1`, so they define a morphism from the
chart to the standard open `D₊(X_k)` of `Proj`. Changing the normalizing coordinate rescales the
homogeneous coordinates by a unit, so the morphism does not depend on `k`, and it is compatible
with restriction to faces. The morphisms therefore glue to a morphism from the toric scheme.

On the maximal cone omitting `k`, the ratios `X_j / X_k`, for `j ≠ k`, freely generate the dual
semigroup (`TauCeti.Toric.projectiveSpaceDualSemigroupEquiv`), so the coordinate ring of its chart
is the degree-zero part of the localization of `ℂ[X_j]` away from `X_k`, and its chart maps
isomorphically onto `D₊(X_k)`. Over `D₊(X_l)`, the chart of the maximal cone omitting `k` is the
locus where `X_l / X_k` does not vanish, which is the chart of the common face of the two maximal
cones. Hence the glued morphism is injective, so it is an open immersion, and it is surjective
because the opens `D₊(X_k)` cover `Proj`.

## Main declarations

* `TauCeti.Toric.projectiveSpaceHomogeneousCoordinates`: the homogeneous coordinates on the chart
  of a cone contained in the maximal cone omitting `k`, normalized by `X_k = 1`.
* `TauCeti.Toric.projectiveSpaceAwayEquiv`: the ring of the standard chart `D₊(X_k)` is the
  coordinate ring of the maximal cone omitting `k`.
* `TauCeti.Toric.projectiveSpaceChartToProj`: the morphism from the chart of a cone to `Proj`,
  independent of the normalizing coordinate by `TauCeti.Toric.projectiveSpaceChartToProj_eq`;
  for a maximal cone it is an open immersion onto `D₊(X_k)`
  (`TauCeti.Toric.opensRange_projectiveSpaceChartToProj`).
* `TauCeti.Toric.Fan.projectiveSpaceToProj`: the morphism from the toric scheme of the fan of
  projective space to `Proj ℂ[X_j]`, computed on charts by
  `TauCeti.Toric.Fan.affineToricChartι_comp_projectiveSpaceToProj`, a morphism over `Spec ℂ`
  (`TauCeti.Toric.Fan.isOver_projectiveSpaceToProj`).
* `TauCeti.Toric.Fan.isIso_projectiveSpaceToProj`: this morphism is an isomorphism.

## References

* W. Fulton, *Introduction to Toric Varieties*, §1.4.
* D. Cox, J. Little and H. Schenck, *Toric Varieties*, §3.1.
* R. Hartshorne, *Algebraic Geometry*, GTM 52, Springer, 1977, Proposition II.2.5.
-/

public section

open AlgebraicGeometry CategoryTheory Limits HomogeneousLocalization Multiplicative

namespace TauCeti.Toric

/-! ### Ratios of homogeneous coordinates -/

section Ratio

variable {N V ι : Type*} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  [Fintype ι] (b : Module.Basis ι ℤ N) {i : N →+ V} (hi : IsIntegralLattice i)
  {σ : PointedCone ℝ V}

/-- The monomial of the homogeneous-coordinate ratio `X_j / X_k` on the affine chart of a cone
contained in the maximal cone omitting the ray `k`. -/
noncomputable def projectiveSpaceRatioMonomial {k : Option ι}
    (hσ : σ ≤ projectiveSpaceCone b i {k}ᶜ) (j : Option ι) : affineCoordinateRing hi σ :=
  MonoidAlgebra.single (ofAdd ⟨projectiveSpaceRatioCharacter b j k,
    dualSemigroup_anti hi hσ
      (projectiveSpaceRatioCharacter_mem_dualSemigroup b hi j k (by simp))⟩) 1

variable {b hi}

/-- The ratio `X_k / X_k` is `1`. -/
@[simp]
theorem projectiveSpaceRatioMonomial_self {k : Option ι}
    (hσ : σ ≤ projectiveSpaceCone b i {k}ᶜ) : projectiveSpaceRatioMonomial b hi hσ k = 1 := by
  rw [projectiveSpaceRatioMonomial, MonoidAlgebra.one_def, ← ofAdd_zero]
  congr
  ext1
  simp

/-- The ratio monomials multiply as the ratios do: `(X_k / X_l) (X_j / X_k) = X_j / X_l`. -/
theorem projectiveSpaceRatioMonomial_mul {k l : Option ι}
    (hk : σ ≤ projectiveSpaceCone b i {k}ᶜ) (hl : σ ≤ projectiveSpaceCone b i {l}ᶜ)
    (j : Option ι) :
    projectiveSpaceRatioMonomial b hi hl k * projectiveSpaceRatioMonomial b hi hk j =
      projectiveSpaceRatioMonomial b hi hl j := by
  rw [projectiveSpaceRatioMonomial, projectiveSpaceRatioMonomial, projectiveSpaceRatioMonomial,
    MonoidAlgebra.single_mul_single, one_mul, ← ofAdd_add]
  congr
  exact Subtype.ext ((add_comm _ _).trans (projectiveSpaceRatioCharacter_add b j k l))

/-- On a cone contained in the maximal cones omitting `k` and `l`, the ratio `X_l / X_k` is a
unit. -/
theorem isUnit_projectiveSpaceRatioMonomial {k l : Option ι}
    (hk : σ ≤ projectiveSpaceCone b i {k}ᶜ) (hl : σ ≤ projectiveSpaceCone b i {l}ᶜ) :
    IsUnit (projectiveSpaceRatioMonomial b hi hk l) :=
  .of_mul_eq_one (projectiveSpaceRatioMonomial b hi hl k) <| by
    rw [mul_comm, projectiveSpaceRatioMonomial_mul hk hl, projectiveSpaceRatioMonomial_self]

/-- Restricting a ratio monomial to a face gives the same ratio monomial. -/
@[simp]
theorem faceAffineCoordinateRingMap_projectiveSpaceRatioMonomial {τ : PointedCone ℝ V}
    {k : Option ι} (hτσ : τ.IsFaceOf σ) (hσ : σ ≤ projectiveSpaceCone b i {k}ᶜ)
    (j : Option ι) :
    faceAffineCoordinateRingMap hi hτσ (projectiveSpaceRatioMonomial b hi hσ j) =
      projectiveSpaceRatioMonomial b hi (hτσ.le.trans hσ) j := by
  rw [projectiveSpaceRatioMonomial, faceAffineCoordinateRingMap_single]
  rfl

end Ratio

/-! ### Homogeneous coordinates on the affine charts -/

section HomogeneousCoordinates

variable {N V ι : Type*} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  [Fintype ι] (b : Module.Basis ι ℤ N) {i : N →+ V} (hi : IsIntegralLattice i)
  {σ : PointedCone ℝ V}

local notation "𝒜" => SymmetricAlgebra.homogeneousSubmodule ℂ (Option ι → ℂ)
local notation "X" j => _root_.SymmetricAlgebra.ι ℂ (Option ι → ℂ) (Pi.single j 1)

/-- The homogeneous coordinates on the affine chart of a cone contained in the maximal cone
omitting the ray `k`, normalized by `X_k = 1`: the coordinate `X_j` is the monomial of the ratio
`X_j / X_k`. -/
noncomputable def projectiveSpaceHomogeneousCoordinates {k : Option ι}
    (hσ : σ ≤ projectiveSpaceCone b i {k}ᶜ) :
    _root_.SymmetricAlgebra ℂ (Option ι → ℂ) →ₐ[ℂ] affineCoordinateRing hi σ :=
  _root_.SymmetricAlgebra.lift
    ((Pi.basisFun ℂ (Option ι)).constr ℂ (projectiveSpaceRatioMonomial b hi hσ))

variable {b hi}

/-- The homogeneous coordinate `X_j` is the monomial of the ratio `X_j / X_k`. -/
@[simp]
theorem projectiveSpaceHomogeneousCoordinates_coord [DecidableEq ι] {k : Option ι}
    (hσ : σ ≤ projectiveSpaceCone b i {k}ᶜ) (j : Option ι) :
    projectiveSpaceHomogeneousCoordinates b hi hσ (X j) =
      projectiveSpaceRatioMonomial b hi hσ j := by
  rw [projectiveSpaceHomogeneousCoordinates, _root_.SymmetricAlgebra.lift_ι_apply,
    ← Pi.basisFun_apply ℂ, Module.Basis.constr_basis]

/-- On a cone contained in the maximal cone omitting `l`, the homogeneous coordinate `X_l` is
invertible. -/
theorem isUnit_projectiveSpaceHomogeneousCoordinates_coord [DecidableEq ι] {k l : Option ι}
    (hk : σ ≤ projectiveSpaceCone b i {k}ᶜ) (hl : σ ≤ projectiveSpaceCone b i {l}ᶜ) :
    IsUnit (projectiveSpaceHomogeneousCoordinates b hi hk (X l)) := by
  rw [projectiveSpaceHomogeneousCoordinates_coord]
  exact isUnit_projectiveSpaceRatioMonomial hk hl

/-- Changing the normalizing coordinate from `X_k` to `X_l` multiplies the linear homogeneous
coordinates by the ratio `X_k / X_l`. -/
theorem projectiveSpaceHomogeneousCoordinates_ι_eq_mul {k l : Option ι}
    (hk : σ ≤ projectiveSpaceCone b i {k}ᶜ) (hl : σ ≤ projectiveSpaceCone b i {l}ᶜ)
    (m : Option ι → ℂ) :
    projectiveSpaceHomogeneousCoordinates b hi hl (_root_.SymmetricAlgebra.ι ℂ _ m) =
      projectiveSpaceRatioMonomial b hi hl k *
        projectiveSpaceHomogeneousCoordinates b hi hk (_root_.SymmetricAlgebra.ι ℂ _ m) := by
  classical
  have h : (projectiveSpaceHomogeneousCoordinates b hi hl).toLinearMap ∘ₗ
      _root_.SymmetricAlgebra.ι ℂ _ =
      LinearMap.mulLeft ℂ (projectiveSpaceRatioMonomial b hi hl k) ∘ₗ
        (projectiveSpaceHomogeneousCoordinates b hi hk).toLinearMap ∘ₗ
          _root_.SymmetricAlgebra.ι ℂ _ :=
    (Pi.basisFun ℂ (Option ι)).ext fun j ↦ by
      simp [projectiveSpaceRatioMonomial_mul hk hl]
  exact LinearMap.congr_fun h m

/-- Changing the normalizing coordinate from `X_k` to `X_l` multiplies the homogeneous
polynomials of degree `n` by the `n`-th power of the ratio `X_k / X_l`. -/
theorem projectiveSpaceHomogeneousCoordinates_eq_pow_mul {k l : Option ι}
    (hk : σ ≤ projectiveSpaceCone b i {k}ᶜ) (hl : σ ≤ projectiveSpaceCone b i {l}ᶜ) {n : ℕ}
    {a : _root_.SymmetricAlgebra ℂ (Option ι → ℂ)} (ha : a ∈ 𝒜 n) :
    projectiveSpaceHomogeneousCoordinates b hi hl a =
      projectiveSpaceRatioMonomial b hi hl k ^ n *
        projectiveSpaceHomogeneousCoordinates b hi hk a :=
  AlgHom.apply_eq_pow_mul_of_forall_ι_eq _ _ _
    (projectiveSpaceHomogeneousCoordinates_ι_eq_mul hk hl) ha

/-- Restricting the homogeneous coordinates of a chart to a face gives the homogeneous
coordinates of the face. -/
@[simp]
theorem faceAffineCoordinateRingMap_comp_projectiveSpaceHomogeneousCoordinates
    {τ : PointedCone ℝ V} {k : Option ι} (hτσ : τ.IsFaceOf σ)
    (hσ : σ ≤ projectiveSpaceCone b i {k}ᶜ) :
    (faceAffineCoordinateRingMap hi hτσ).comp (projectiveSpaceHomogeneousCoordinates b hi hσ) =
      projectiveSpaceHomogeneousCoordinates b hi (hτσ.le.trans hσ) :=
  _root_.SymmetricAlgebra.algHom_ext <| (Pi.basisFun ℂ (Option ι)).ext fun j ↦ by
    classical
    simp


/-! ### The chart of a maximal cone -/

variable [DecidableEq ι] (b hi) (k : Option ι)

omit [Fintype ι] in
/-- The homogeneous coordinate `X_j` has degree one. -/
private theorem coord_mem (j : Option ι) : (X j) ∈ 𝒜 1 :=
  SymmetricAlgebra.ι_mem_homogeneousSubmodule ℂ _ _

/-- The fraction `X_j / X_k` in the ring of the standard chart `D₊(X_k)`. -/
private noncomputable def awayRatio (j : Option ι) : Away 𝒜 (X k) :=
  Away.mk 𝒜 (coord_mem k) 1 (X j) (by simp)

omit [Fintype ι] in
private theorem val_awayRatio (j : Option ι) :
    (awayRatio k j).val =
      IsLocalization.Away.invSelf (X k) * algebraMap _ (Localization.Away (X k)) (X j) := by
  rw [awayRatio, Away.val_mk, Localization.mk_eq_mk', ← pow_one (IsLocalization.Away.invSelf _),
    ← TauCeti.Localization.mk'_pow_eq_invSelf_pow_mul]

omit [Fintype ι] in
private theorem awayRatio_self : awayRatio k k = 1 := by
  apply val_injective
  rw [val_awayRatio, val_one, mul_comm, IsLocalization.Away.mul_invSelf]

/-- The characters of the maximal cone omitting `k` act on the chart `D₊(X_k)`: a character with
exponents `a_j` along the rays `j ≠ k` goes to `∏ (X_j / X_k) ^ a_j`. -/
private noncomputable def awayMonoidHom :
    Multiplicative (dualSemigroup hi (projectiveSpaceCone b i {k}ᶜ)) →* Away 𝒜 (X k) where
  toFun m := ∏ j, awayRatio k j.1 ^ projectiveSpaceDualSemigroupEquiv b hi k (toAdd m) j
  map_one' := by simp
  map_mul' m m' := by
    simp only [toAdd_mul, map_add, Pi.add_apply, pow_add, Finset.prod_mul_distrib]

/-- The homomorphism from the coordinate ring of the maximal cone omitting `k` to the ring of the
chart `D₊(X_k)`. -/
private noncomputable def toAway :
    affineCoordinateRing hi (projectiveSpaceCone b i {k}ᶜ) →ₐ[ℂ] Away 𝒜 (X k) :=
  MonoidAlgebra.lift ℂ _ _ (awayMonoidHom b hi k)

private theorem awayMonoidHom_apply
    (m : dualSemigroup hi (projectiveSpaceCone b i {k}ᶜ)) :
    awayMonoidHom b hi k (ofAdd m) =
      ∏ j, awayRatio k j.1 ^ projectiveSpaceDualSemigroupEquiv b hi k m j :=
  (rfl)

omit [DecidableEq ι] in
private theorem projectiveSpaceRatioMonomial_eq_single {j : Option ι} (hj : j ≠ k) :
    projectiveSpaceRatioMonomial b hi le_rfl j =
      MonoidAlgebra.single (ofAdd (projectiveSpaceChartCharacter b hi k ⟨j, hj⟩)) 1 := by
  rw [projectiveSpaceRatioMonomial]
  exact congrArg (fun m ↦ MonoidAlgebra.single (ofAdd m) 1)
    (Subtype.ext (coe_projectiveSpaceChartCharacter b hi k ⟨j, hj⟩).symm)

private theorem toAway_projectiveSpaceRatioMonomial (j : Option ι) :
    toAway b hi k (projectiveSpaceRatioMonomial b hi le_rfl j) = awayRatio k j := by
  by_cases hj : j = k
  · subst hj
    rw [projectiveSpaceRatioMonomial_self, map_one, awayRatio_self]
  · rw [projectiveSpaceRatioMonomial_eq_single b hi k hj, toAway, MonoidAlgebra.lift_single,
      one_smul, awayMonoidHom_apply, projectiveSpaceDualSemigroupEquiv_chartCharacter,
      Finset.prod_eq_single ⟨j, hj⟩ (fun l _ hl ↦ by simp [hl]) (by simp)]
    simp

/-- The homomorphism from the ring of the chart `D₊(X_k)` to the coordinate ring of the maximal
cone omitting `k`, given by the homogeneous coordinates with `X_k = 1`. -/
private noncomputable def ofAway :
    Away 𝒜 (X k) →ₐ[ℂ] affineCoordinateRing hi (projectiveSpaceCone b i {k}ᶜ) where
  __ := Away.lift 𝒜 (projectiveSpaceHomogeneousCoordinates b hi (le_refl _)).toRingHom
    (isUnit_projectiveSpaceHomogeneousCoordinates_coord le_rfl le_rfl)
  commutes' c := by
    rw [HomogeneousLocalization.algebraMap_eq_comp, RingHom.comp_apply,
      ← HomogeneousLocalization.algebraMap_eq]
    exact (Away.lift_algebraMap _ _ _).trans (by simp)

private theorem ofAway_mk {n : ℕ} {a : _root_.SymmetricAlgebra ℂ (Option ι → ℂ)}
    (ha : a ∈ 𝒜 (n • 1)) :
    ofAway b hi k (Away.mk 𝒜 (coord_mem k) n a ha) =
      projectiveSpaceHomogeneousCoordinates b hi le_rfl a := by
  simp [ofAway]

/-- A product of powers of the ratios `X_j / X_k` is the monomial of the corresponding sum of
ratio characters. -/
private theorem prod_projectiveSpaceRatioMonomial_pow (a : {j : Option ι // j ≠ k} → ℕ) :
    ∏ j, projectiveSpaceRatioMonomial b hi le_rfl j.1 ^ a j =
      MonoidAlgebra.single (ofAdd ((projectiveSpaceDualSemigroupEquiv b hi k).symm a)) 1 := by
  rw [projectiveSpaceDualSemigroupEquiv_symm_apply, ofAdd_sum, ← MonoidAlgebra.of_apply, map_prod]
  -- The general formula sums over `univ` built from classical decidable equality.
  refine Finset.prod_congr (by congr!) fun j _ ↦ ?_
  rw [projectiveSpaceRatioMonomial_eq_single b hi k j.2, ofAdd_nsmul, map_pow,
    MonoidAlgebra.of_apply]

private theorem ofAway_comp_toAway : (ofAway b hi k).comp (toAway b hi k) = AlgHom.id ℂ _ := by
  refine MonoidAlgebra.algHom_ext (fun m ↦ ?_) (Subsingleton.elim _ _)
  rw [AlgHom.comp_apply, toAway, MonoidAlgebra.lift_single, one_smul, ← ofAdd_toAdd m,
    awayMonoidHom_apply, map_prod]
  simp_rw [map_pow, awayRatio, ofAway_mk, projectiveSpaceHomogeneousCoordinates_coord]
  rw [prod_projectiveSpaceRatioMonomial_pow, AddEquiv.symm_apply_apply, AlgHom.id_apply]

private theorem toAway_comp_ofAway : (toAway b hi k).comp (ofAway b hi k) = AlgHom.id ℂ _ := by
  ext z
  obtain ⟨n, a, ha, rfl⟩ := Away.mk_surjective 𝒜 (coord_mem k) z
  rw [AlgHom.comp_apply, ofAway_mk, AlgHom.id_apply, Away.val_mk, Localization.mk_eq_mk',
    TauCeti.Localization.mk'_pow_eq_invSelf_pow_mul]
  let f := IsScalarTower.toAlgHom ℂ (_root_.SymmetricAlgebra ℂ (Option ι → ℂ))
    (Localization.Away (X k))
  let g := (IsScalarTower.toAlgHom ℂ (Away 𝒜 (X k)) (Localization.Away (X k))).comp
    ((toAway b hi k).comp (projectiveSpaceHomogeneousCoordinates b hi le_rfl))
  refine AlgHom.apply_eq_pow_mul_of_forall_ι_eq f g _ (fun m ↦ ?_) (by simpa using ha)
  have h : g.toLinearMap ∘ₗ _root_.SymmetricAlgebra.ι ℂ _ =
      LinearMap.mulLeft ℂ (IsLocalization.Away.invSelf (X k)) ∘ₗ f.toLinearMap ∘ₗ
        _root_.SymmetricAlgebra.ι ℂ _ :=
    (Pi.basisFun ℂ (Option ι)).ext fun j ↦ by
      simp [g, f, toAway_projectiveSpaceRatioMonomial, HomogeneousLocalization.algebraMap_apply,
        val_awayRatio]
  exact LinearMap.congr_fun h m

/-- **The affine chart of the maximal cone omitting `k` is the standard chart `D₊(X_k)` of
projective space**: the ring of `D₊(X_k)`, the degree-zero part of the localization of the
homogeneous coordinate ring away from `X_k`, is the coordinate ring of the cone. A fraction
`a / X_kⁿ` goes to the value of `a` at the homogeneous coordinates with `X_k = 1`. -/
noncomputable def projectiveSpaceAwayEquiv :
    Away 𝒜 (X k) ≃ₐ[ℂ] affineCoordinateRing hi (projectiveSpaceCone b i {k}ᶜ) :=
  AlgEquiv.ofAlgHom (ofAway b hi k) (toAway b hi k) (ofAway_comp_toAway b hi k)
    (toAway_comp_ofAway b hi k)

/-- The isomorphism `projectiveSpaceAwayEquiv` sends `a / X_kⁿ` to the value of `a` at the
homogeneous coordinates with `X_k = 1`. -/
@[simp]
theorem projectiveSpaceAwayEquiv_mk {n : ℕ} {a : _root_.SymmetricAlgebra ℂ (Option ι → ℂ)}
    (ha : a ∈ 𝒜 (n • 1)) :
    projectiveSpaceAwayEquiv b hi k
        (Away.mk 𝒜 (SymmetricAlgebra.ι_mem_homogeneousSubmodule ℂ _ _) n a ha) =
      projectiveSpaceHomogeneousCoordinates b hi le_rfl a :=
  ofAway_mk b hi k ha

/-- The isomorphism `projectiveSpaceAwayEquiv` is the homomorphism `Away.lift` induced by the
homogeneous coordinates with `X_k = 1`. -/
theorem projectiveSpaceAwayEquiv_toRingHom :
    (projectiveSpaceAwayEquiv b hi k).toAlgHom.toRingHom =
      Away.lift 𝒜 (projectiveSpaceHomogeneousCoordinates b hi le_rfl).toRingHom
        (isUnit_projectiveSpaceHomogeneousCoordinates_coord le_rfl le_rfl) :=
  (rfl)

/-- The inverse of `projectiveSpaceAwayEquiv` sends the monomial of the ratio `X_j / X_k` to the
fraction `X_j / X_k`. -/
@[simp]
theorem projectiveSpaceAwayEquiv_symm_projectiveSpaceRatioMonomial (j : Option ι) :
    (projectiveSpaceAwayEquiv b hi k).symm (projectiveSpaceRatioMonomial b hi le_rfl j) =
      Away.mk 𝒜 (SymmetricAlgebra.ι_mem_homogeneousSubmodule ℂ _ _) 1 (X j)
        (by simp) :=
  toAway_projectiveSpaceRatioMonomial b hi k j

end HomogeneousCoordinates

/-! ### The morphism to `Proj` -/

section Scheme

variable {N ι : Type} {V : Type*} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℤ N) {i : N →+ V} (hi : IsIntegralLattice i)
  {σ : PointedCone ℝ V}

local notation "𝒜" => SymmetricAlgebra.homogeneousSubmodule ℂ (Option ι → ℂ)
local notation "X" j => _root_.SymmetricAlgebra.ι ℂ (Option ι → ℂ) (Pi.single j 1)

/-- The morphism from the affine toric scheme of a cone contained in the maximal cone omitting
`k` to projective space `Proj ℂ[X_j]`: the point with the homogeneous coordinates of the chart,
read on the standard chart `D₊(X_k)`. By `projectiveSpaceChartToProj_eq` it does not depend
on `k`. -/
noncomputable def projectiveSpaceChartToProj {k : Option ι}
    (hσ : σ ≤ projectiveSpaceCone b i {k}ᶜ) : affineToricScheme hi σ ⟶ Proj 𝒜 :=
  Spec.map (CommRingCat.ofHom
    (Away.lift 𝒜 (projectiveSpaceHomogeneousCoordinates b hi hσ).toRingHom
      (isUnit_projectiveSpaceHomogeneousCoordinates_coord hσ hσ))) ≫
    Proj.awayι 𝒜 (X k) (SymmetricAlgebra.ι_mem_homogeneousSubmodule ℂ _ _) one_pos

variable {b hi}

/-- The morphism `projectiveSpaceChartToProj` does not depend on the normalizing coordinate. -/
theorem projectiveSpaceChartToProj_eq {k l : Option ι}
    (hk : σ ≤ projectiveSpaceCone b i {k}ᶜ) (hl : σ ≤ projectiveSpaceCone b i {l}ᶜ) :
    projectiveSpaceChartToProj b hi hk = projectiveSpaceChartToProj b hi hl := by
  rw [projectiveSpaceChartToProj, projectiveSpaceChartToProj,
    Proj.SpecMap_awayLift_awayι_eq _ _ one_pos
      (SymmetricAlgebra.ι_mem_homogeneousSubmodule ℂ _ _) one_pos _
      (isUnit_projectiveSpaceHomogeneousCoordinates_coord hk hl)]
  congr 3
  exact (Away.lift_eq_of_forall_mem _ _ (isUnit_projectiveSpaceRatioMonomial hl hk).unit
    (fun n a ha ↦ by simpa using projectiveSpaceHomogeneousCoordinates_eq_pow_mul hk hl ha)
    (SymmetricAlgebra.ι_mem_homogeneousSubmodule ℂ _ _) _ _).symm

/-- Restricting `projectiveSpaceChartToProj` to the chart of a face gives the morphism of the
face. -/
@[reassoc (attr := simp)]
theorem faceAffineToricSchemeMap_comp_projectiveSpaceChartToProj {τ : PointedCone ℝ V}
    {k : Option ι} (hτσ : τ.IsFaceOf σ) (hσ : σ ≤ projectiveSpaceCone b i {k}ᶜ) :
    faceAffineToricSchemeMap hi hτσ ≫ projectiveSpaceChartToProj b hi hσ =
      projectiveSpaceChartToProj b hi (hτσ.le.trans hσ) := by
  rw [faceAffineToricSchemeMap_def, projectiveSpaceChartToProj, projectiveSpaceChartToProj,
    ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
    RingHom.comp_homogeneousLocalizationAwayLift]
  congr 4
  exact congrArg AlgHom.toRingHom
    (faceAffineCoordinateRingMap_comp_projectiveSpaceHomogeneousCoordinates hτσ hσ)

/-- On the chart of the maximal cone omitting `k`, the morphism to `Proj` is the spectrum of the
isomorphism `projectiveSpaceAwayEquiv` followed by the standard chart `D₊(X_k)`. -/
theorem projectiveSpaceChartToProj_self (k : Option ι) :
    projectiveSpaceChartToProj b hi (le_refl (projectiveSpaceCone b i {k}ᶜ)) =
      Spec.map (CommRingCat.ofHom (projectiveSpaceAwayEquiv b hi k).toAlgHom.toRingHom) ≫
        Proj.awayι 𝒜 (X k) (SymmetricAlgebra.ι_mem_homogeneousSubmodule ℂ _ _) one_pos := by
  rw [projectiveSpaceChartToProj, projectiveSpaceAwayEquiv_toRingHom]

/-- The chart-ring isomorphism `projectiveSpaceAwayEquiv` is an isomorphism in `CommRingCat`. -/
private instance isIso_ofHom_projectiveSpaceAwayEquiv (k : Option ι) :
    IsIso (CommRingCat.ofHom (projectiveSpaceAwayEquiv b hi k).toAlgHom.toRingHom) :=
  (ConcreteCategory.isIso_iff_bijective _).2 (projectiveSpaceAwayEquiv b hi k).bijective

/-- The affine chart of the maximal cone omitting `k` is an open subscheme of projective space. -/
instance isOpenImmersion_projectiveSpaceChartToProj (k : Option ι) :
    IsOpenImmersion (projectiveSpaceChartToProj b hi (le_refl (projectiveSpaceCone b i {k}ᶜ))) := by
  rw [projectiveSpaceChartToProj_self]
  infer_instance

/-- The affine chart of the maximal cone omitting `k` is the standard open `D₊(X_k)` of projective
space. -/
theorem opensRange_projectiveSpaceChartToProj (k : Option ι) :
    (projectiveSpaceChartToProj b hi (le_refl (projectiveSpaceCone b i {k}ᶜ))).opensRange =
      Proj.basicOpen 𝒜 (X k) := by
  simp only [projectiveSpaceChartToProj_self, Scheme.Hom.opensRange_comp_of_isIso,
    Proj.opensRange_awayι]

/-- In the chart of the maximal cone omitting `k`, the standard open `D₊(X_l)` of projective space
is the locus where the ratio `X_l / X_k` does not vanish. -/
theorem projectiveSpaceChartToProj_preimage_basicOpen (k l : Option ι) :
    projectiveSpaceChartToProj b hi (le_refl (projectiveSpaceCone b i {k}ᶜ)) ⁻¹ᵁ
        Proj.basicOpen 𝒜 (X l) =
      PrimeSpectrum.basicOpen (projectiveSpaceRatioMonomial b hi le_rfl l) := by
  rw [projectiveSpaceChartToProj_self, Scheme.Hom.comp_preimage,
    Proj.awayι_preimage_basicOpen 𝒜 (SymmetricAlgebra.ι_mem_homogeneousSubmodule ℂ _ _) one_pos
      (SymmetricAlgebra.ι_mem_homogeneousSubmodule ℂ _ _) one_pos,
    SpecMap_preimage_basicOpen]
  simp only [AlgHom.toRingHom_eq_coe, AlgEquiv.toAlgHom_toRingHom, ConcreteCategory.hom_ofHom,
    RingHom.coe_coe, projectiveSpaceAwayEquiv_mk, pow_one,
    projectiveSpaceHomogeneousCoordinates_coord]
  -- The two sides differ only in the ring structure of the coordinate ring seen through
  -- `CommRingCat.of`.
  rfl

end Scheme

/-! ### The toric scheme of the fan of projective space -/

namespace Fan

variable {N ι : Type} {V : Type*} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℤ N) {i : N →+ V} (hi : IsIntegralLattice i)

local notation "𝒜" => SymmetricAlgebra.homogeneousSubmodule ℂ (Option ι → ℂ)
local notation "X" j => _root_.SymmetricAlgebra.ι ℂ (Option ι → ℂ) (Pi.single j 1)

/-- The compatible morphisms from the affine charts of the fan of projective space to `Proj`. -/
private noncomputable def projCocone : Cocone (projectiveSpace b hi).affineToricDiagram where
  pt := Proj 𝒜
  ι :=
    { app σ := projectiveSpaceChartToProj b hi
        (exists_le_projectiveSpaceCone_compl b hi σ.2).choose_spec
      naturality _ _ _ :=
        (faceAffineToricSchemeMap_comp_projectiveSpaceChartToProj _ _).trans
          ((projectiveSpaceChartToProj_eq _ _).trans (Category.comp_id _).symm) }

/-- The morphism from the toric scheme of the fan of projective space to projective space
`Proj ℂ[X_j]`, given on the chart of each cone by its homogeneous coordinates. -/
noncomputable def projectiveSpaceToProj :
    (projectiveSpace b hi).algebraicRealization ⟶ Proj 𝒜 :=
  (projectiveSpace b hi).isColimitAffineToricCocone.desc (projCocone b hi)

variable {b hi}

/-- On the chart of a cone contained in the maximal cone omitting `k`, the morphism to `Proj` is
given by the homogeneous coordinates normalized by `X_k = 1`. -/
@[reassoc]
theorem affineToricChartι_comp_projectiveSpaceToProj (σ : (projectiveSpace b hi).cones)
    {k : Option ι} (hσ : σ.1 ≤ projectiveSpaceCone b i {k}ᶜ) :
    (projectiveSpace b hi).affineToricChartι σ ≫ projectiveSpaceToProj b hi =
      projectiveSpaceChartToProj b hi hσ := by
  have h := (projectiveSpace b hi).isColimitAffineToricCocone.fac (projCocone b hi) σ
  rw [affineToricCocone_ι_app] at h
  exact h.trans (projectiveSpaceChartToProj_eq _ _)

/-- The morphism from the toric scheme of the fan of projective space to `Proj` is a morphism over
`Spec ℂ`. -/
instance isOver_projectiveSpaceToProj :
    (projectiveSpaceToProj b hi).IsOver (Spec (.of ℂ)) where
  comp_over := by
    refine algebraicRealization_hom_ext _ fun σ ↦ ?_
    obtain ⟨k, hk⟩ := exists_le_projectiveSpaceCone_compl b hi σ.2
    rw [affineToricChartι_comp_projectiveSpaceToProj_assoc σ hk,
      SymmetricAlgebra.over_eq_projToSpec, projectiveSpaceChartToProj, Category.assoc,
      SymmetricAlgebra.awayι_projToSpec, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
      algebraicRealization_over, affineToricChartι_comp_algebraicRealizationStructureMap]
    congr 2
    ext c
    simp [← HomogeneousLocalization.algebraMap_eq]

omit [DecidableEq ι] in
/-- Every point of the toric scheme of the fan of projective space lies in the chart of a maximal
cone. -/
private theorem exists_affineToricChartι_projectiveSpaceMaximalCone_apply_eq
    (x : (projectiveSpace b hi).algebraicRealization) :
    ∃ k y, (projectiveSpace b hi).affineToricChartι (projectiveSpaceMaximalCone b hi k) y = x := by
  obtain ⟨σ, y, rfl⟩ := (projectiveSpace b hi).exists_affineToricChartι_apply_eq x
  obtain ⟨k, hk⟩ := exists_le_projectiveSpaceCone_compl b hi σ.2
  have hσk := (projectiveSpace b hi).isFaceOf_of_le (projectiveSpaceMaximalCone b hi k).2 σ.2 hk
  exact ⟨k, faceAffineToricSchemeMap _ hσk y, by
    rw [← Scheme.Hom.comp_apply, faceAffineToricSchemeMap_comp_affineToricChartι]⟩

/-- A point of the chart of the maximal cone omitting `k` that lies over the standard open
`D₊(X_l)` lies in the chart of the maximal cone omitting `l`: it lies in the chart of the
common face, cut out by the ratio `X_l / X_k`. -/
private theorem affineToricChartι_mem_range_of_mem_basicOpen {k : Option ι}
    (y : affineToricScheme hi (projectiveSpaceCone b i {k}ᶜ)) {l : Option ι}
    (hy : projectiveSpaceChartToProj b hi le_rfl y ∈ Proj.basicOpen 𝒜 (X l)) :
    (projectiveSpace b hi).affineToricChartι (projectiveSpaceMaximalCone b hi k) y ∈
      Set.range ((projectiveSpace b hi).affineToricChartι (projectiveSpaceMaximalCone b hi l)) := by
  let Φ := projectiveSpace b hi
  let m : dualSemigroup hi (projectiveSpaceCone b i {k}ᶜ) :=
    ⟨projectiveSpaceRatioCharacter b l k,
      projectiveSpaceRatioCharacter_mem_dualSemigroup b hi l k (by simp)⟩
  have hk := (projectiveSpaceMaximalCone b hi k).2
  have hl := (projectiveSpaceMaximalCone b hi l).2
  have hy' : y ∈ Set.range (faceAffineToricSchemeMap hi
      (PointedCone.isFaceOf_inf_ker ((mem_dualSemigroup hi m).1 m.2))) := by
    rw [range_faceAffineToricSchemeMap hi (Φ.isToricCone hk).fg m]
    exact (projectiveSpaceChartToProj_preimage_basicOpen k l).le hy
  obtain ⟨z, rfl⟩ := hy'
  have hT := projectiveSpaceCone_inf_ker_ratioCharacter b hi k l
  have hTmem : projectiveSpaceCone b i {k}ᶜ ⊓
      PointedCone.ofSubmodule (LinearMap.ker (hi.realCharacter m)) ∈ Φ.cones := by
    rw [hT]
    exact Φ.inf_mem hk hl
  have hTl := Φ.isFaceOf_of_le hl hTmem (hT ▸ inf_le_right)
  refine ⟨faceAffineToricSchemeMap hi hTl z, ?_⟩
  rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply,
    faceAffineToricSchemeMap_comp_affineToricChartι (τ := ⟨_, hTmem⟩)
      (σ := projectiveSpaceMaximalCone b hi l),
    faceAffineToricSchemeMap_comp_affineToricChartι (τ := ⟨_, hTmem⟩)
      (σ := projectiveSpaceMaximalCone b hi k)]

/-- The morphism from the toric scheme of the fan of projective space to `Proj` is injective. -/
private theorem projectiveSpaceToProj_injective :
    Function.Injective (projectiveSpaceToProj b hi) := by
  intro x y hxy
  obtain ⟨k, x, rfl⟩ := exists_affineToricChartι_projectiveSpaceMaximalCone_apply_eq x
  obtain ⟨l, y, rfl⟩ := exists_affineToricChartι_projectiveSpaceMaximalCone_apply_eq y
  rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply,
    affineToricChartι_comp_projectiveSpaceToProj _ le_rfl,
    affineToricChartι_comp_projectiveSpaceToProj _ le_rfl] at hxy
  have hx : projectiveSpaceChartToProj b hi le_rfl x ∈ Proj.basicOpen 𝒜 (X l) := by
    rw [hxy, ← opensRange_projectiveSpaceChartToProj (b := b) (hi := hi) l]
    exact ⟨y, rfl⟩
  obtain ⟨z, hz⟩ := affineToricChartι_mem_range_of_mem_basicOpen x hx
  have h := congrArg (projectiveSpaceToProj b hi) hz
  rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply,
    affineToricChartι_comp_projectiveSpaceToProj _ le_rfl,
    affineToricChartι_comp_projectiveSpaceToProj _ le_rfl] at h
  rw [← hz, (projectiveSpaceChartToProj b hi
    (le_refl (projectiveSpaceCone b i {l}ᶜ))).isOpenEmbedding.injective (h.trans hxy)]

/-- The morphism from the toric scheme of the fan of projective space to `Proj` is surjective: the
standard opens `D₊(X_k)` cover projective space. -/
private theorem projectiveSpaceToProj_surjective :
    Function.Surjective (projectiveSpaceToProj b hi) := by
  intro p
  have hp : p ∈ (⊤ : (Proj 𝒜).Opens) := trivial
  rw [← SymmetricAlgebra.iSup_basicOpen_ι_eq_top ℂ (Option ι → ℂ) (fun j ↦ Pi.single j 1)
    (by rw [← funext (Pi.basisFun_apply ℂ (Option ι)), (Pi.basisFun ℂ (Option ι)).span_eq])] at hp
  obtain ⟨k, hk⟩ := TopologicalSpace.Opens.mem_iSup.1 hp
  rw [← opensRange_projectiveSpaceChartToProj (b := b) (hi := hi) k] at hk
  obtain ⟨y, rfl⟩ := hk
  exact ⟨(projectiveSpace b hi).affineToricChartι (projectiveSpaceMaximalCone b hi k) y, by
    rw [← Scheme.Hom.comp_apply, affineToricChartι_comp_projectiveSpaceToProj _ le_rfl]⟩

/-- The morphism from the toric scheme of the fan of projective space to `Proj` is an open
immersion: it is injective, and an open immersion on the chart of every maximal cone. -/
instance isOpenImmersion_projectiveSpaceToProj : IsOpenImmersion (projectiveSpaceToProj b hi) :=
  .of_forall_source_exists _ projectiveSpaceToProj_injective fun x ↦ by
    obtain ⟨k, y, rfl⟩ := exists_affineToricChartι_projectiveSpaceMaximalCone_apply_eq x
    refine ⟨_, (projectiveSpace b hi).affineToricChartι (projectiveSpaceMaximalCone b hi k),
      inferInstance, ⟨y, rfl⟩, ?_⟩
    rw [affineToricChartι_comp_projectiveSpaceToProj _ le_rfl]
    infer_instance

/-- **The toric scheme of the fan of projective space is projective space** `Proj ℂ[X_j]`. -/
instance isIso_projectiveSpaceToProj : IsIso (projectiveSpaceToProj b hi) :=
  (isIso_iff_isOpenImmersion_and_surjective _).2
    ⟨inferInstance, ⟨projectiveSpaceToProj_surjective⟩⟩

end Fan

end TauCeti.Toric

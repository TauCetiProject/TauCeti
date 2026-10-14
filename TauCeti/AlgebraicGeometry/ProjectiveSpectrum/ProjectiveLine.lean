/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.RatFunc.Basic
public import Mathlib.LinearAlgebra.SymmetricAlgebra.Basis
public import Mathlib.RingTheory.RegularLocalRing.Polynomial
public import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.Integral
public import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.SymmetricAlgebra
public import TauCeti.AlgebraicGeometry.Scheme.BaseAlgebra
public import TauCeti.AlgebraicGeometry.Scheme.RegularLocalRing
public import TauCeti.RingTheory.GradedAlgebra.HomogeneousLocalization.Basic

/-!
# The projective line over a commutative ring

The projective line over a commutative ring `R` is `ℙ¹_R = Proj R[X₀, X₁]`, written here, following
the convention of `TauCeti.SymmetricAlgebra.projToSpec`, as the projective spectrum of the
symmetric algebra of `R²`, whose two standard basis vectors are the homogeneous coordinates `X₀` and
`X₁`.

It is covered by the two standard affine charts `D₊(Xᵢ)`. The chart `D₊(Xᵢ)` is the spectrum of
the degree-zero part `R[X₀, X₁]_(Xᵢ)` of the localization away from `Xᵢ`, and dehomogenization,
setting `Xᵢ = 1` and the other coordinate to `X`, identifies it with the polynomial ring `R[X]`:
the fraction `p / Xᵢⁿ` of a form `p` of degree `n` goes to `p` with `Xᵢ = 1`. So `ℙ¹_R` is proper
over `R`; it is integral when `R` is a domain, and its local rings are regular when `R` is a regular
ring. Over a domain, its function field is the fraction field `R(X)` of the ring `R[X]` of
functions on the chart `D₊(X₀)`, the function `X₁ / X₀` on that chart going to `X`.

## Main definitions

* `TauCeti.AlgebraicGeometry.projectiveLine R`: the projective line over `R`, a scheme over
  `Spec R`.
* `TauCeti.AlgebraicGeometry.projectiveLine.coord R i`: the homogeneous coordinate `Xᵢ`.
* `TauCeti.AlgebraicGeometry.projectiveLine.dehomogenize R i`: setting `Xᵢ = 1` and the other
  coordinate to `X`, an `R`-algebra map `R[X₀, X₁] → R[X]`.
* `TauCeti.AlgebraicGeometry.projectiveLine.awayEquivPolynomial R i`: the ring of the chart
  `D₊(Xᵢ)` is `R[X]`.
* `TauCeti.AlgebraicGeometry.projectiveLine.awayι R i`: the open immersion of that chart.
* `TauCeti.AlgebraicGeometry.projectiveLine.chartSectionsEquiv R i`: the functions on the chart
  `D₊(Xᵢ)` are the polynomials `R[X]`.
* `TauCeti.AlgebraicGeometry.projectiveLine.functionFieldEquiv R`: over a domain `R`, the function
  field of `ℙ¹_R` is `R(X)`, as an `R`-algebra.

## Main results

* `TauCeti.AlgebraicGeometry.projectiveLine.awayEquivPolynomial_mk`: the chart isomorphism
  sends `p / Xᵢⁿ` to the dehomogenization of `p`.
* `TauCeti.AlgebraicGeometry.projectiveLine.exists_eq_awayι`: the two charts cover `ℙ¹_R`.
* `TauCeti.AlgebraicGeometry.projectiveLine.isIntegral`: `ℙ¹_R` is integral over a domain.
* `TauCeti.AlgebraicGeometry.projectiveLine.isRegularLocalRing_stalk`: its local rings are
  regular over a regular ring.
* `TauCeti.AlgebraicGeometry.projectiveLine.functionFieldEquiv_germToFunctionField`: on the chart
  `D₊(X₀)`, the identification of the function field with `R(X)` is `chartSectionsEquiv`.

## References

* R. Hartshorne, *Algebraic Geometry*, GTM 52, Springer, 1977, Section II.2.
* The Stacks Project, Section 27.8 (the projective spectrum of a graded ring).
-/

public section

open CategoryTheory AlgebraicGeometry HomogeneousLocalization Polynomial

universe u

namespace TauCeti.AlgebraicGeometry

variable (R : Type u) [CommRing R]

/-- **The projective line** `ℙ¹_R = Proj R[X₀, X₁]` over a commutative ring `R`: the projective
spectrum of the symmetric algebra of `R²`, whose standard basis vectors are the homogeneous
coordinates. It is a scheme over `Spec R` through `TauCeti.SymmetricAlgebra.projToSpec`, proper
by `TauCeti.SymmetricAlgebra.instIsProperOver`. -/
noncomputable abbrev projectiveLine : Scheme.{u} :=
  Proj (SymmetricAlgebra.homogeneousSubmodule R (Fin 2 → R))

namespace projectiveLine

local notation "𝒜" => SymmetricAlgebra.homogeneousSubmodule R (Fin 2 → R)

/-- The homogeneous coordinate `Xᵢ` of the projective line: the `i`-th standard basis vector of
`R²`, in degree one of the symmetric algebra. -/
noncomputable def coord (i : Fin 2) : _root_.SymmetricAlgebra R (Fin 2 → R) :=
  _root_.SymmetricAlgebra.ι R (Fin 2 → R) (Pi.single i 1)

/-- The homogeneous coordinates have degree one. -/
theorem coord_mem (i : Fin 2) : coord R i ∈ 𝒜 1 :=
  SymmetricAlgebra.ι_mem_homogeneousSubmodule R _ _

/-- A linear form is the combination of the two homogeneous coordinates with its coefficients. -/
theorem ι_eq_smul_coord_add_smul_coord (i : Fin 2) (m : Fin 2 → R) :
    _root_.SymmetricAlgebra.ι R (Fin 2 → R) m = m i • coord R i + m i.rev • coord R i.rev := by
  have hm : m = m i • Pi.single i 1 + m i.rev • Pi.single i.rev 1 := by
    ext j
    fin_cases i <;> fin_cases j <;> simp
  conv_lhs => rw [hm]
  simp [coord]

/-- **Dehomogenization** at `Xᵢ`: the `R`-algebra map `R[X₀, X₁] → R[X]` setting `Xᵢ = 1` and the
other homogeneous coordinate to `X`. -/
noncomputable def dehomogenize (i : Fin 2) : _root_.SymmetricAlgebra R (Fin 2 → R) →ₐ[R] R[X] :=
  _root_.SymmetricAlgebra.lift ((Pi.basisFun R (Fin 2)).constr R fun j ↦ if j = i then 1 else X)

/-- Dehomogenization at `Xᵢ` sends `Xᵢ` to `1`. -/
@[simp]
theorem dehomogenize_coord_self (i : Fin 2) : dehomogenize R i (coord R i) = 1 := by
  fin_cases i <;> simp [dehomogenize, coord]

/-- Dehomogenization at `Xᵢ` sends the other homogeneous coordinate to `X`. -/
@[simp]
theorem dehomogenize_coord_rev (i : Fin 2) : dehomogenize R i (coord R i.rev) = X := by
  fin_cases i <;> simp [dehomogenize, coord]

/-! ### The standard affine charts -/

/-- Dehomogenization inverts `Xᵢ`, so it induces a map out of the chart ring
`R[X₀, X₁]_(Xᵢ)`. -/
private theorem isUnit_dehomogenize_coord (i : Fin 2) : IsUnit (dehomogenize R i (coord R i)) := by
  simp

/-- The map `R[X₀, X₁]_(Xᵢ) → R[X]`, `p / Xᵢⁿ ↦ p(Xᵢ = 1)`, induced by dehomogenization. -/
private noncomputable def awayToPolynomial (i : Fin 2) : Away 𝒜 (coord R i) →ₐ[R] R[X] where
  __ := Away.lift 𝒜 (dehomogenize R i).toRingHom (isUnit_dehomogenize_coord R i)
  commutes' c := by
    rw [HomogeneousLocalization.algebraMap_eq_comp, RingHom.comp_apply,
      ← HomogeneousLocalization.algebraMap_eq]
    -- the constants of the chart ring are the fractions `c / Xᵢ⁰`
    exact (Away.lift_algebraMap _ _ _).trans (by simp)

private theorem awayToPolynomial_mk (i : Fin 2) {n : ℕ}
    {a : _root_.SymmetricAlgebra R (Fin 2 → R)} (ha : a ∈ 𝒜 (n • 1)) :
    awayToPolynomial R i (Away.mk 𝒜 (coord_mem R i) n a ha) = dehomogenize R i a := by
  simp [awayToPolynomial]

/-- The map `R[X] → R[X₀, X₁]_(Xᵢ)` sending `X` to the other coordinate over `Xᵢ`. -/
private noncomputable def polynomialToAway (i : Fin 2) : R[X] →ₐ[R] Away 𝒜 (coord R i) :=
  aeval (Away.mk 𝒜 (coord_mem R i) 1 (coord R i.rev) (by simpa using coord_mem R i.rev))

/-- In the localization away from `Xᵢ`, the fraction `a / Xᵢⁿ` is `a` times the `n`-th power of
the inverse of `Xᵢ`. -/
private theorem localization_mk_eq (i : Fin 2) (n : ℕ)
    (a : _root_.SymmetricAlgebra R (Fin 2 → R)) :
    Localization.mk a (⟨coord R i ^ n, n, rfl⟩ : Submonoid.powers (coord R i)) =
      IsLocalization.Away.invSelf (coord R i) ^ n *
        algebraMap _ (Localization.Away (coord R i)) a := by
  rw [Localization.mk_eq_mk', IsLocalization.mk'_eq_iff_eq_mul, mul_right_comm, map_pow,
    ← mul_pow, mul_comm (IsLocalization.Away.invSelf _), IsLocalization.Away.mul_invSelf, one_pow,
    one_mul]

/-- Rehomogenizing the dehomogenization of a form `a` of degree `n` gives back `a / Xᵢⁿ`, read in
the localization away from `Xᵢ`. Both sides are algebra maps of `a` agreeing, up to the factor
`Xᵢ⁻¹`, on the linear forms. -/
private theorem val_polynomialToAway_dehomogenize (i : Fin 2) {n : ℕ}
    {a : _root_.SymmetricAlgebra R (Fin 2 → R)} (ha : a ∈ 𝒜 n) :
    (polynomialToAway R i (dehomogenize R i a)).val =
      IsLocalization.Away.invSelf (coord R i) ^ n *
        algebraMap _ (Localization.Away (coord R i)) a := by
  let f := IsScalarTower.toAlgHom R (_root_.SymmetricAlgebra R (Fin 2 → R))
    (Localization.Away (coord R i))
  let g := (IsScalarTower.toAlgHom R (Away 𝒜 (coord R i)) (Localization.Away (coord R i))).comp
    ((polynomialToAway R i).comp (dehomogenize R i))
  refine AlgHom.apply_eq_pow_mul_of_forall_ι_eq f g _ (fun m ↦ ?_) ha
  have h1 := localization_mk_eq R i 1 (coord R i.rev)
  simp only [g, f, AlgHom.comp_apply, IsScalarTower.coe_toAlgHom',
    ι_eq_smul_coord_add_smul_coord R i m, map_add, map_smul, dehomogenize_coord_self,
    dehomogenize_coord_rev, polynomialToAway, aeval_X, map_one]
  rw [HomogeneousLocalization.algebraMap_apply, Away.val_mk, h1, pow_one, mul_add, mul_smul_comm,
    mul_smul_comm, mul_comm _ (algebraMap _ _ (coord R i)), IsLocalization.Away.mul_invSelf]

/-- **The chart ring of `D₊(Xᵢ)` is a polynomial ring**: dehomogenization identifies the
degree-zero part `R[X₀, X₁]_(Xᵢ)` of the localization away from `Xᵢ` with `R[X]`. -/
noncomputable def awayEquivPolynomial (i : Fin 2) : Away 𝒜 (coord R i) ≃ₐ[R] R[X] :=
  AlgEquiv.ofAlgHom (awayToPolynomial R i) (polynomialToAway R i)
    (Polynomial.algHom_ext (by simp [polynomialToAway, awayToPolynomial_mk]))
    (AlgHom.ext fun z ↦ by
      obtain ⟨n, a, ha, rfl⟩ := Away.mk_surjective 𝒜 (coord_mem R i) z
      apply HomogeneousLocalization.val_injective
      simp only [AlgHom.comp_apply, awayToPolynomial_mk, AlgHom.id_apply, Away.val_mk]
      rw [val_polynomialToAway_dehomogenize R i (by simpa using ha), localization_mk_eq])

/-- The chart isomorphism sends `p / Xᵢⁿ` to the dehomogenization of `p`. -/
@[simp]
theorem awayEquivPolynomial_mk (i : Fin 2) {n : ℕ} {a : _root_.SymmetricAlgebra R (Fin 2 → R)}
    (ha : a ∈ 𝒜 (n • 1)) :
    awayEquivPolynomial R i (Away.mk 𝒜 (coord_mem R i) n a ha) = dehomogenize R i a :=
  awayToPolynomial_mk R i ha

/-- The inverse of the chart isomorphism sends `X` to the other coordinate over `Xᵢ`. -/
@[simp]
theorem awayEquivPolynomial_symm_X (i : Fin 2) :
    (awayEquivPolynomial R i).symm X =
      Away.mk 𝒜 (coord_mem R i) 1 (coord R i.rev) (by simpa using coord_mem R i.rev) :=
  aeval_X _

/-- The open immersion of the standard affine chart `D₊(Xᵢ) = Spec R[X₀, X₁]_(Xᵢ)` into the
projective line. -/
noncomputable abbrev awayι (i : Fin 2) : Spec (.of (Away 𝒜 (coord R i))) ⟶ projectiveLine R :=
  Proj.awayι 𝒜 (coord R i) (coord_mem R i) one_pos

/-- On the chart `D₊(Xᵢ)`, the structure morphism of the projective line is `Spec` of the
inclusion of the constants. -/
@[reassoc (attr := simp)]
theorem awayι_over (i : Fin 2) :
    awayι R i ≫ (projectiveLine R ↘ Spec (.of R)) =
      Spec.map (CommRingCat.ofHom (algebraMap R (Away 𝒜 (coord R i)))) := by
  rw [SymmetricAlgebra.over_eq_projToSpec, SymmetricAlgebra.awayι_projToSpec]

/-- **The two standard charts cover the projective line.** -/
theorem exists_eq_awayι (p : projectiveLine R) : ∃ i q, awayι R i q = p := by
  have h : ⨆ i, Proj.basicOpen 𝒜 (coord R i) = ⊤ := by
    refine Proj.iSup_basicOpen_eq_top' 𝒜 _ (fun i ↦ ⟨1, coord_mem R i⟩) (top_unique ?_)
    -- the homogeneous coordinates generate the symmetric algebra
    rintro a -
    induction a using _root_.SymmetricAlgebra.induction with
    | algebraMap r =>
      exact Subalgebra.algebraMap_mem _ (algebraMap R (𝒜 0) r)
    | ι m =>
      rw [ι_eq_smul_coord_add_smul_coord R 0 m, Algebra.smul_def, Algebra.smul_def]
      refine add_mem (mul_mem ?_ (Algebra.subset_adjoin ⟨0, rfl⟩))
        (mul_mem ?_ (Algebra.subset_adjoin ⟨Fin.rev 0, rfl⟩)) <;>
      exact Subalgebra.algebraMap_mem _ (algebraMap R (𝒜 0) _)
    | mul a b ha hb => exact mul_mem ha hb
    | add a b ha hb => exact add_mem ha hb
  have hp : p ∈ (⊤ : (projectiveLine R).Opens) := trivial
  rw [← h] at hp
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hp
  rw [← Proj.opensRange_awayι 𝒜 _ (coord_mem R i) one_pos] at hi
  obtain ⟨q, rfl⟩ := hi
  exact ⟨i, q, rfl⟩

/-- **The projective line over a domain is integral**: `R[X₀, X₁]` is a domain with a nonzero form
of positive degree. -/
instance isIntegral [IsDomain R] : IsIntegral (projectiveLine R) := by
  refine Proj.isIntegral_of_isDomain 𝒜 fun h ↦ ?_
  have : coord R 0 ∈ HomogeneousIdeal.irrelevant 𝒜 := by
    rw [HomogeneousIdeal.mem_irrelevant_iff, GradedRing.proj_apply,
      DirectSum.decompose_of_mem_ne 𝒜 (coord_mem R 0) one_ne_zero]
  rw [h, ← HomogeneousIdeal.mem_iff, HomogeneousIdeal.toIdeal_bot, Ideal.mem_bot] at this
  simpa [coord] using
    congrFun (SymmetricAlgebra.ι_injective R (Fin 2 → R) (this.trans (map_zero _).symm)) 0

/-- **The local rings of the projective line over a regular ring are regular**: each is a local
ring of a chart `Spec R[X]`, and `R[X]` is a regular ring. -/
instance isRegularLocalRing_stalk [IsRegularRing R] (p : projectiveLine R) :
    IsRegularLocalRing ((projectiveLine R).presheaf.stalk p) := by
  obtain ⟨i, q, rfl⟩ := exists_eq_awayι R p
  have : IsRegularRing (Away 𝒜 (coord R i)) :=
    .of_ringEquiv (awayEquivPolynomial R i).symm.toRingEquiv
  exact (isRegularLocalRing_stalk_iff_of_isOpenImmersion _ q).mpr inferInstance

/-! ### Functions on the charts -/

instance [Nontrivial R] (i : Fin 2) : Nonempty (Spec (.of (Away 𝒜 (coord R i)))) :=
  haveI : Nontrivial (Away 𝒜 (coord R i)) := (awayEquivPolynomial R i).toEquiv.nontrivial
  inferInstanceAs (Nonempty (PrimeSpectrum _))

instance [Nontrivial R] (i : Fin 2) : Nonempty (awayι R i ''ᵁ ⊤) := by
  obtain ⟨p⟩ : Nonempty (Spec (.of (Away 𝒜 (coord R i)))) := inferInstance
  exact ⟨⟨awayι R i p, p, trivial, rfl⟩⟩

/-- The chart `D₊(Xᵢ)` is an affine open subscheme of the projective line. -/
theorem isAffineOpen_image_awayι_top (i : Fin 2) : IsAffineOpen (awayι R i ''ᵁ ⊤) := by
  rw [Scheme.Hom.image_top_eq_opensRange]
  exact isAffineOpen_opensRange _

/-- **The functions on the chart `D₊(Xᵢ)` are the polynomials in `X`**, the other coordinate over
`Xᵢ`: restrict along the chart and dehomogenize. -/
noncomputable def chartSectionsEquiv (i : Fin 2) : Γ(projectiveLine R, awayι R i ''ᵁ ⊤) ≃+* R[X] :=
  ((awayι R i).appIso ⊤ ≪≫ Scheme.ΓSpecIso _).commRingCatIsoToRingEquiv.trans
    (awayEquivPolynomial R i).toRingEquiv

/-- `chartSectionsEquiv` restricts a function on the chart `D₊(Xᵢ)` along the chart and
dehomogenizes it. -/
theorem chartSectionsEquiv_apply (i : Fin 2) (a : Γ(projectiveLine R, awayι R i ''ᵁ ⊤)) :
    chartSectionsEquiv R i a =
      awayEquivPolynomial R i ((Scheme.ΓSpecIso _).hom (((awayι R i).appIso ⊤).hom a)) :=
  (rfl)

/-- On the chart `D₊(Xᵢ)`, the functions on `Spec R` pulled back along the structure morphism are
the constant polynomials. -/
@[simp]
theorem chartSectionsEquiv_appLE (i : Fin 2) (a : Γ(Spec (.of R), ⊤)) :
    chartSectionsEquiv R i ((projectiveLine R ↘ Spec (.of R)).appLE ⊤ _ le_top a) =
      C ((Scheme.ΓSpecIso (.of R)).hom a) := by
  suffices h : (projectiveLine R ↘ Spec (.of R)).appLE ⊤ _ le_top ≫
        ((awayι R i).appIso ⊤).hom ≫ (Scheme.ΓSpecIso _).hom =
      (Scheme.ΓSpecIso (.of R)).hom ≫ CommRingCat.ofHom (algebraMap R (Away 𝒜 (coord R i))) by
    rw [chartSectionsEquiv_apply, ← CommRingCat.comp_apply, ← CommRingCat.comp_apply, h]
    simp
  rw [← cancel_epi (Scheme.ΓSpecIso (.of R)).inv, Iso.inv_hom_id_assoc, Scheme.Hom.appIso_hom',
    reassoc_of% Scheme.Hom.appLE_comp_appLE (awayι R i)
    (projectiveLine R ↘ Spec (.of R)) ⊤ (awayι R i ''ᵁ ⊤) ⊤ le_top
    (Scheme.Hom.preimage_image_eq _ _).ge]
  -- The composite of the chart with the structure morphism is `Spec` of the inclusion of `R`.
  rw [show Scheme.Hom.appLE _ ⊤ ⊤ _ = Scheme.Hom.appTop _ from Scheme.Hom.appLE_eq_app _,
    awayι_over, Scheme.ΓSpecIso_naturality, Iso.inv_hom_id_assoc]

/-! ### The function field -/

variable [IsDomain R]

/-- **The function field of the projective line over a domain `R` is `R(X)`**, as an `R`-algebra:
it is the fraction field of the ring `R[X]` of functions on the chart `D₊(X₀)`, the function
`X₁ / X₀` on that chart going to `X` (`functionFieldEquiv_germToFunctionField`). -/
noncomputable def functionFieldEquiv : (projectiveLine R).functionField ≃ₐ[R] RatFunc R :=
  haveI := functionField_isFractionRing_of_isAffineOpen _ _ (isAffineOpen_image_awayι_top R 0)
  AlgEquiv.ofRingEquiv (f := IsFractionRing.ringEquivOfRingEquiv (chartSectionsEquiv R 0))
    fun c ↦ by
      rw [Scheme.algebraMap_functionField_eq_baseRingToFunctionField,
        Scheme.baseRingToFunctionField_eq_comp_appLE R _ (awayι R 0 ''ᵁ ⊤), RingHom.comp_apply]
      -- `germToFunctionField` is by definition the algebra map of `Γ(X, U)` to `R(X)`.
      refine (IsFractionRing.ringEquivOfRingEquiv_algebraMap _ _).trans ?_
      rw [CommRingCat.comp_apply, chartSectionsEquiv_appLE, Iso.inv_hom_id_apply,
        ← Polynomial.algebraMap_eq]
      exact (IsScalarTower.algebraMap_apply R _ (RatFunc R) c).symm

/-- On the chart `D₊(X₀)`, the identification of the function field of the projective line with
`R(X)` is `chartSectionsEquiv`, that is, dehomogenization at `X₀`. -/
@[simp]
theorem functionFieldEquiv_germToFunctionField (a : Γ(projectiveLine R, awayι R 0 ''ᵁ ⊤)) :
    functionFieldEquiv R ((projectiveLine R).germToFunctionField _ a) =
      algebraMap R[X] (RatFunc R) (chartSectionsEquiv R 0 a) := by
  have := functionField_isFractionRing_of_isAffineOpen _ _ (isAffineOpen_image_awayι_top R 0)
  -- `germToFunctionField` is by definition the algebra map of `Γ(X, U)` to `R(X)`.
  exact IsFractionRing.ringEquivOfRingEquiv_algebraMap _ a

end projectiveLine

end TauCeti.AlgebraicGeometry

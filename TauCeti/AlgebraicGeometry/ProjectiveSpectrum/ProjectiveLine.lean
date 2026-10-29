/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
public import Mathlib.FieldTheory.RatFunc.AsPolynomial
public import Mathlib.LinearAlgebra.SymmetricAlgebra.Basis
public import Mathlib.RingTheory.RegularLocalRing.Polynomial
public import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.Integral
public import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.LinearAction
public import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.SymmetricAlgebra
public import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.SymmetricBaseChange
public import TauCeti.AlgebraicGeometry.Scheme.BaseAlgebra
public import TauCeti.AlgebraicGeometry.Scheme.Regular.LocalRing
public import TauCeti.RingTheory.GradedAlgebra.HomogeneousLocalization.Basic
public import TauCeti.RingTheory.Localization.Away.Basic
import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.SchemeTheoreticallyDominant
import TauCeti.RingTheory.Spectrum.Prime.Polynomial

/-!
# The projective line over a commutative ring

The projective line over a commutative ring `R` is `ℙ¹_R = Proj R[X₀, X₁]`, written here, following
the convention of `TauCeti.SymmetricAlgebra.projToSpec`, as the projective spectrum of the
symmetric algebra of `R²`, whose two standard basis vectors are the homogeneous coordinates `X₀` and
`X₁`.

It is covered by the two standard affine charts `D₊(Xᵢ)`. The chart `D₊(Xᵢ)` is the spectrum of
the degree-zero part `R[X₀, X₁]_(Xᵢ)` of the localization away from `Xᵢ`, and dehomogenization,
setting `Xᵢ = 1` and the other coordinate to `X`, identifies it with the polynomial ring `R[X]`:
the fraction `p / Xᵢⁿ` of a form `p` of degree `n` goes to `p` with `Xᵢ = 1`.
Each chart `Spec R[X] ⟶ ℙ¹_R` is a schematically dense open immersion over any ring.
The projective line `ℙ¹_R` is proper over `R`, as the Proj of the symmetric algebra of a finite
module
(`TauCeti.SymmetricAlgebra.instIsProperOver`), and smooth of relative dimension one over `R`, since
each chart is the affine line `Spec R[X]`; it is integral when `R` is a domain, and its local
rings are regular when `R` is a regular ring. Its formation commutes with every change of base
ring `R → S`: `ℙ¹_S` is the fibre product `ℙ¹_R ×_{Spec R} Spec S`. Over a domain, its function
field is the fraction field `R(X)` of the ring `R[X]` of functions on the chart `D₊(X₀)`, the
function `X₁ / X₀` on that chart going to `X`.

## Main definitions

* `TauCeti.AlgebraicGeometry.projectiveLine R`: the projective line over `R`, a scheme over
  `Spec R`.
* `TauCeti.AlgebraicGeometry.projectiveLine.coord R i`: the homogeneous coordinate `Xᵢ`.
* `TauCeti.AlgebraicGeometry.projectiveLine.dehomogenize R i`: setting `Xᵢ = 1` and the other
  coordinate to `X`, an `R`-algebra map `R[X₀, X₁] → R[X]`.
* `TauCeti.AlgebraicGeometry.projectiveLine.awayEquivPolynomial R i`: the ring of the chart
  `D₊(Xᵢ)` is `R[X]`.
* `TauCeti.AlgebraicGeometry.projectiveLine.awayι R i`: the open immersion of that chart.
* `TauCeti.AlgebraicGeometry.projectiveLine.polynomialChartι R i`: that chart with source
  literally `Spec R[X]`.
* `TauCeti.AlgebraicGeometry.projectiveLine.infinitySection R`: the section `[0 : 1]`; over a
  field `K`, `TauCeti.AlgebraicGeometry.projectiveLine.infinity K` is its single image point.
* `TauCeti.AlgebraicGeometry.projectiveLine.chartSectionsEquiv R i`: the functions on the chart
  `D₊(Xᵢ)` are the polynomials `R[X]`.
* `TauCeti.AlgebraicGeometry.projectiveLine.baseChangeProjection R S`: for an `R`-algebra `S`, the
  projection `ℙ¹_S ⟶ ℙ¹_R`.
* `TauCeti.AlgebraicGeometry.projectiveLine.functionFieldEquiv R`: over a domain `R`, the function
  field of `ℙ¹_R` is `R(X)`, as an `R`-algebra.

## Main results

* `TauCeti.AlgebraicGeometry.projectiveLine.coord_mem_nonZeroDivisors`: homogeneous coordinates
  are nonzerodivisors over any ring, so every `polynomialChartι` is schematically dense.
* `TauCeti.AlgebraicGeometry.projectiveLine.opensRange_polynomialChartι` and
  `TauCeti.AlgebraicGeometry.projectiveLine.polynomialChartι_preimage_basicOpen_rev`: the chart
  ranges are the standard basic opens and their overlap is the locus where `X` is invertible.
* `TauCeti.AlgebraicGeometry.projectiveLine.range_polynomialChartι_union_range_polynomialChartι`:
  the two ranges cover.
* `TauCeti.AlgebraicGeometry.projectiveLine.range_infinitySection`: the infinity section is the
  complement of the zeroth chart over any ring; it is a closed immersion and misses that chart
  by `TauCeti.AlgebraicGeometry.projectiveLine.infinitySection_notMem_range_polynomialChartι`.
* `TauCeti.AlgebraicGeometry.projectiveLine.compl_range_polynomialChartι`: over a field the
  complement is the singleton `infinity`.
* `TauCeti.AlgebraicGeometry.projectiveLine.awayEquivPolynomial_mk`: the chart isomorphism
  sends `p / Xᵢⁿ` to the dehomogenization of `p`.
* `TauCeti.AlgebraicGeometry.projectiveLine.iSup_basicOpen_coord_eq_top`,
  `TauCeti.AlgebraicGeometry.projectiveLine.exists_eq_awayι` and
  `TauCeti.AlgebraicGeometry.projectiveLine.basicOpen_coord_sup_eq_top`: the two charts cover
  `ℙ¹_R`, and by `TauCeti.AlgebraicGeometry.projectiveLine.isAffineOpen_basicOpen_coord` each
  chart is affine.
* `TauCeti.AlgebraicGeometry.projectiveLine.chartSectionsEquiv_awayToSection`: on the chart
  `D₊(Xᵢ)`, `chartSectionsEquiv` agrees with the chart isomorphism on the fractions
  `Proj.awayToSection a`, and `TauCeti.AlgebraicGeometry.projectiveLine.awayToSection_algebraMap`:
  the constants restrict to the fractions `c / 1`.
* `TauCeti.AlgebraicGeometry.projectiveLine.isIntegral`: `ℙ¹_R` is integral over a domain.
* `TauCeti.AlgebraicGeometry.projectiveLine.isRegularLocalRing_stalk`: its local rings are
  regular over a regular ring.
* `TauCeti.AlgebraicGeometry.projectiveLine.smoothOfRelativeDimension`: `ℙ¹_R` is smooth of
  relative dimension one over `Spec R`.
* `TauCeti.AlgebraicGeometry.projectiveLine.isPullback_baseChangeProjection`: `ℙ¹_S` is the base
  change of `ℙ¹_R` along `Spec S ⟶ Spec R`.
* `TauCeti.AlgebraicGeometry.projectiveLine.functionFieldEquiv_germToFunctionField`: on the chart
  `D₊(X₀)`, the identification of the function field with `R(X)` is `chartSectionsEquiv`.
* `TauCeti.AlgebraicGeometry.projectiveLine.functionFieldEquiv_symm_X`: that identification sends
  the function `X₁ / X₀` to `X`.

## References

* R. Hartshorne, *Algebraic Geometry*, GTM 52, Springer, 1977, Section II.2.
* The Stacks Project, Section 27.8 (the projective spectrum of a graded ring).
-/

public section

open CategoryTheory Limits AlgebraicGeometry HomogeneousLocalization Polynomial
open scoped TensorProduct

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

/-- Each homogeneous coordinate is a nonzerodivisor, even over a nonreduced base ring. -/
theorem coord_mem_nonZeroDivisors (i : Fin 2) : coord R i ∈ nonZeroDivisors _ := by
  apply mem_nonZeroDivisors_of_injective
    (_root_.SymmetricAlgebra.equivMvPolynomial (Pi.basisFun R (Fin 2))).injective
  -- Identify the coordinate with the image of its standard basis vector.
  rw [coord, ← Pi.basisFun_apply R (Fin 2) i,
    _root_.SymmetricAlgebra.equivMvPolynomial_ι_apply]
  exact MvPolynomial.isRegular_X.mem_nonZeroDivisors

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
  have h1 := TauCeti.Localization.mk'_pow_eq_invSelf_pow_mul (S := Localization.Away (coord R i))
    (coord R i.rev) (coord R i) 1
  simp only [g, f, AlgHom.comp_apply, IsScalarTower.coe_toAlgHom',
    ι_eq_smul_coord_add_smul_coord R i m, map_add, map_smul, dehomogenize_coord_self,
    dehomogenize_coord_rev, polynomialToAway, aeval_X, map_one]
  rw [HomogeneousLocalization.algebraMap_apply, Away.val_mk, Localization.mk_eq_mk', h1, pow_one,
    mul_add, mul_smul_comm, mul_smul_comm, mul_comm _ (algebraMap _ _ (coord R i)),
    IsLocalization.Away.mul_invSelf]

/-- **The chart ring of `D₊(Xᵢ)` is a polynomial ring**: dehomogenization identifies the
degree-zero part `R[X₀, X₁]_(Xᵢ)` of the localization away from `Xᵢ` with `R[X]`. -/
noncomputable def awayEquivPolynomial (i : Fin 2) : Away 𝒜 (coord R i) ≃ₐ[R] R[X] :=
  AlgEquiv.ofAlgHom (awayToPolynomial R i) (polynomialToAway R i)
    (Polynomial.algHom_ext (by simp [polynomialToAway, awayToPolynomial_mk]))
    (AlgHom.ext fun z ↦ by
      obtain ⟨n, a, ha, rfl⟩ := Away.mk_surjective 𝒜 (coord_mem R i) z
      apply HomogeneousLocalization.val_injective
      simp only [AlgHom.comp_apply, awayToPolynomial_mk, AlgHom.id_apply, Away.val_mk]
      rw [val_polynomialToAway_dehomogenize R i (by simpa using ha), Localization.mk_eq_mk',
        TauCeti.Localization.mk'_pow_eq_invSelf_pow_mul])

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

/-- The standard affine chart of the projective line, with source literally `Spec R[X]`. -/
noncomputable def polynomialChartι (i : Fin 2) : Spec (.of R[X]) ⟶ projectiveLine R :=
  Spec.map (awayEquivPolynomial R i).toRingEquiv.toCommRingCatIso.hom ≫ awayι R i

/-- The polynomial chart is the chart-ring equivalence followed by the standard open immersion. -/
theorem polynomialChartι_def (i : Fin 2) :
    polynomialChartι R i =
      Spec.map (awayEquivPolynomial R i).toRingEquiv.toCommRingCatIso.hom ≫ awayι R i :=
  (rfl)

instance (i : Fin 2) : IsOpenImmersion (polynomialChartι R i) := by
  unfold polynomialChartι
  infer_instance

/-- Every standard polynomial chart of the projective line is schematically dense. -/
instance (i : Fin 2) : IsSchemeTheoreticallyDominant (polynomialChartι R i) := by
  have : IsSchemeTheoreticallyDominant (awayι R i) :=
    Proj.isSchemeTheoreticallyDominant_awayι 𝒜 (coord_mem R i) one_pos
      (coord_mem_nonZeroDivisors R i)
  rw [polynomialChartι_def]
  infer_instance

/-- Each polynomial chart is a morphism over `Spec R`. -/
@[reassoc (attr := simp)]
theorem polynomialChartι_over (i : Fin 2) :
    polynomialChartι R i ≫ (projectiveLine R ↘ Spec (.of R)) =
      Spec.map (CommRingCat.ofHom (algebraMap R R[X])) := by
  rw [polynomialChartι, Category.assoc, awayι_over, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro c
  exact (awayEquivPolynomial R i).commutes c

/-- The image of the polynomial chart is the standard projective basic open. -/
theorem opensRange_polynomialChartι (i : Fin 2) :
    (polynomialChartι R i).opensRange = Proj.basicOpen 𝒜 (coord R i) := by
  -- Present the composite together with its open-immersion instance before changing its range.
  change (Spec.map (awayEquivPolynomial R i).toRingEquiv.toCommRingCatIso.hom ≫
    awayι R i).opensRange = _
  rw [Scheme.Hom.opensRange_comp_of_isIso, Proj.opensRange_awayι]

/-- The two polynomial charts meet where their polynomial coordinate is invertible. -/
theorem polynomialChartι_preimage_basicOpen_rev (i : Fin 2) :
    polynomialChartι R i ⁻¹ᵁ Proj.basicOpen 𝒜 (coord R i.rev) =
      PrimeSpectrum.basicOpen (X : R[X]) := by
  -- The preimage notation projects to the continuous map; this `change` exposes the
  -- composite and its iterated preimage without rewriting the dependent open carriers.
  change Spec.map (awayEquivPolynomial R i).toRingEquiv.toCommRingCatIso.hom ⁻¹ᵁ
    (awayι R i ⁻¹ᵁ Proj.basicOpen 𝒜 (coord R i.rev)) = _
  rw [Proj.awayι_preimage_basicOpen 𝒜 (coord_mem R i) one_pos (coord_mem R i.rev) one_pos,
    SpecMap_preimage_basicOpen]
  congr 1
  simp only [RingEquiv.toCommRingCatIso_hom, CommRingCat.hom_ofHom,
    RingEquiv.coe_toRingHom, AlgEquiv.coe_toRingEquiv, Away.isLocalizationElem, pow_one,
    awayEquivPolynomial_mk, dehomogenize_coord_rev]

/-- A point of one polynomial chart lies in the other chart exactly off its zero locus. -/
theorem polynomialChartι_mem_range_iff (i : Fin 2) (q : Spec (.of R[X])) :
    polynomialChartι R i q ∈ Set.range (polynomialChartι R i.rev) ↔ X ∉ q.asIdeal := by
  rw [← Scheme.Hom.coe_opensRange, opensRange_polynomialChartι]
  -- Open preimage membership is definitionally membership of the image point.
  change q ∈ polynomialChartι R i ⁻¹ᵁ Proj.basicOpen 𝒜 (coord R i.rev) ↔ _
  rw [polynomialChartι_preimage_basicOpen_rev]
  -- `Spec` has the prime-spectrum carrier, with its native basic-open membership.
  exact PrimeSpectrum.mem_basicOpen X q

/-- **The standard charts `D₊(Xᵢ)` cover the projective line.** -/
theorem iSup_basicOpen_coord_eq_top : ⨆ i, Proj.basicOpen 𝒜 (coord R i) = ⊤ :=
  SymmetricAlgebra.iSup_basicOpen_ι_eq_top R (Fin 2 → R) (fun i ↦ Pi.single i 1) (by
    rw [← funext (Pi.basisFun_apply R (Fin 2)), (Pi.basisFun R (Fin 2)).span_eq])

/-- **The two standard charts cover the projective line.** -/
theorem exists_eq_awayι (p : projectiveLine R) : ∃ i q, awayι R i q = p := by
  have hp : p ∈ (⊤ : (projectiveLine R).Opens) := trivial
  rw [← iSup_basicOpen_coord_eq_top R] at hp
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hp
  rw [← Proj.opensRange_awayι 𝒜 _ (coord_mem R i) one_pos] at hi
  obtain ⟨q, rfl⟩ := hi
  exact ⟨i, q, rfl⟩

/-- **The standard charts `D₊(X₀)` and `D₊(X₁)` cover the projective line.** -/
theorem basicOpen_coord_sup_eq_top :
    Proj.basicOpen 𝒜 (coord R 0) ⊔ Proj.basicOpen 𝒜 (coord R 1) = ⊤ := by
  refine eq_top_iff.mpr fun p _ ↦ TopologicalSpace.Opens.mem_sup.mpr ?_
  have hp : p ∈ (⊤ : (projectiveLine R).Opens) := trivial
  rwa [← iSup_basicOpen_coord_eq_top R, TopologicalSpace.Opens.mem_iSup, Fin.exists_fin_two] at hp

/-- The two polynomial chart ranges cover the projective line. -/
theorem range_polynomialChartι_union_range_polynomialChartι :
    Set.range (polynomialChartι R 0) ∪ Set.range (polynomialChartι R 1) = Set.univ := by
  rw [← Scheme.Hom.coe_opensRange, ← Scheme.Hom.coe_opensRange,
    opensRange_polynomialChartι, opensRange_polynomialChartι,
    ← TopologicalSpace.Opens.coe_sup, basicOpen_coord_sup_eq_top]
  exact TopologicalSpace.Opens.coe_top

/-- The infinity section of the projective line, given by the zero point of the chart
`D₊(X₁)`, with homogeneous coordinates `[0 : 1]`. -/
noncomputable def infinitySection : Spec (.of R) ⟶ projectiveLine R :=
  Spec.map (CommRingCat.ofHom (evalRingHom (0 : R))) ≫ polynomialChartι R 1

/-- The infinity section factors through the zero section of the opposite polynomial chart. -/
theorem infinitySection_def : infinitySection R =
    Spec.map (CommRingCat.ofHom (evalRingHom (0 : R))) ≫ polynomialChartι R 1 :=
  (rfl)

/-- The point at infinity is a section over the base ring. -/
@[simp]
theorem infinitySection_over :
    infinitySection R ≫ (projectiveLine R ↘ Spec (.of R)) = 𝟙 _ := by
  rw [infinitySection_def, Category.assoc, polynomialChartι_over, ← Spec.map_comp]
  rw [← Spec.map_id (.of R)]
  congr 1
  ext c
  simp

instance : IsClosedImmersion (infinitySection R) := by
  have : IsClosedImmersion (infinitySection R ≫ (projectiveLine R ↘ Spec (.of R))) := by
    rw [infinitySection_over]
    infer_instance
  exact IsClosedImmersion.of_comp _ (projectiveLine R ↘ Spec (.of R))

/-- The boundary of the affine-line chart is precisely the infinity section, over any base ring. -/
theorem range_infinitySection :
    Set.range (infinitySection R) = (Set.range (polynomialChartι R 0))ᶜ := by
  have hzero : Set.range (Spec.map (CommRingCat.ofHom (evalRingHom (0 : R)))) =
      {q : Spec (.of R[X]) | X ∈ q.asIdeal} := by
    -- The affine spectrum has the prime-spectrum carrier; identify it explicitly before
    -- applying the ring-theoretic image equation to the scheme map.
    change Set.range (PrimeSpectrum.comap (evalRingHom (0 : R))) =
      {q : PrimeSpectrum R[X] | X ∈ q.asIdeal}
    exact Polynomial.range_comap_evalRingHom_zero R
  ext p
  constructor
  · rintro ⟨q, rfl⟩ hp
    have hq := (Set.ext_iff.mp hzero _).mp ⟨q, rfl⟩
    exact (polynomialChartι_mem_range_iff R 1 _).mp
      (by simpa only [infinitySection_def, Scheme.Hom.comp_apply,
        show (1 : Fin 2).rev = 0 from Fin.rev_last 1] using hp) hq
  · intro hp
    have hc : p ∈ Set.range (polynomialChartι R 0) ∪ Set.range (polynomialChartι R 1) := by
      rw [range_polynomialChartι_union_range_polynomialChartι]
      trivial
    obtain ⟨q, rfl⟩ := hc.resolve_left hp
    have hq : X ∈ q.asIdeal := not_not.mp (fun hn ↦
      hp ((polynomialChartι_mem_range_iff R 1 q).mpr hn))
    obtain ⟨r, hr⟩ := (Set.ext_iff.mp hzero q).mpr hq
    exact ⟨r, by simp only [infinitySection_def, Scheme.Hom.comp_apply, hr]⟩

/-- Every point of the infinity section lies outside the affine-line chart. -/
@[simp↓]
theorem infinitySection_notMem_range_polynomialChartι (x : Spec (.of R)) :
    infinitySection R x ∉ Set.range (polynomialChartι R 0) := by
  exact (Set.ext_iff.mp (range_infinitySection R) _).mp ⟨x, rfl⟩

variable (K : Type u) [Field K]

/-- The point `[0 : 1]` at infinity on the projective line over a field. -/
noncomputable def infinity : projectiveLine K := infinitySection K default

/-- Over a field the affine-line chart has exactly one boundary point. -/
theorem compl_range_polynomialChartι :
    (Set.range (polynomialChartι K 0))ᶜ = {infinity K} := by
  rw [← range_infinitySection]
  ext p
  constructor
  · rintro ⟨q, rfl⟩
    exact congrArg (infinitySection K) (Subsingleton.elim q default)
  · rintro rfl
    exact ⟨default, rfl⟩

/-- The affine-line chart misses the point at infinity. -/
@[simp↓]
theorem infinity_notMem_range_polynomialChartι :
    infinity K ∉ Set.range (polynomialChartι K 0) :=
  infinitySection_notMem_range_polynomialChartι K default

/-- The standard chart `D₊(Xᵢ)` is an affine open of the projective line. -/
theorem isAffineOpen_basicOpen_coord (i : Fin 2) :
    IsAffineOpen (Proj.basicOpen 𝒜 (coord R i)) :=
  Proj.isAffineOpen_basicOpen 𝒜 _ (coord_mem R i) one_pos

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

/-- The function `X` on the chart `D₊(Xᵢ)` restricts along the chart to the other coordinate over
`Xᵢ`. -/
theorem chartSectionsEquiv_symm_X (i : Fin 2) :
    (Scheme.ΓSpecIso _).hom (((awayι R i).appIso ⊤).hom ((chartSectionsEquiv R i).symm X)) =
      Away.mk 𝒜 (coord_mem R i) 1 (coord R i.rev) (by simpa using coord_mem R i.rev) := by
  rw [← awayEquivPolynomial_symm_X, AlgEquiv.eq_symm_apply, ← chartSectionsEquiv_apply,
    RingEquiv.apply_symm_apply]

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
  -- The `show` reads `appLE ⊤ ⊤` as `appTop` through `appLE_eq_app`, relying on the
  -- definitional equalities `f ⁻¹ᵁ ⊤ = ⊤` (`Scheme.Hom.preimage_top`, proved by `rfl`) and
  -- `f.app ⊤ = f.appTop` (`appTop` is an abbreviation); a plain `rw` cannot match the preimage.
  -- Then the composite of the chart with the structure morphism is `Spec` of the inclusion of `R`.
  rw [show Scheme.Hom.appLE _ ⊤ ⊤ _ = Scheme.Hom.appTop _ from Scheme.Hom.appLE_eq_app _,
    awayι_over, Scheme.ΓSpecIso_naturality, Iso.inv_hom_id_assoc]

/-- The chart `D₊(Xᵢ)`, as the image of `awayι`, is the basic open set of `Xᵢ`. -/
theorem image_awayι_top (i : Fin 2) : awayι R i ''ᵁ ⊤ = Proj.basicOpen 𝒜 (coord R i) := by
  rw [Scheme.Hom.image_top_eq_opensRange, Proj.opensRange_awayι]

/-- `chartSectionsEquiv` sends the function `Proj.awayToSection a` on `D₊(Xᵢ)` to the
dehomogenization of the fraction `a`. -/
theorem chartSectionsEquiv_awayToSection (i : Fin 2) (a : Away 𝒜 (coord R i)) :
    chartSectionsEquiv R i ((projectiveLine R).presheaf.map (eqToHom (image_awayι_top R i)).op
      (Proj.awayToSection 𝒜 (coord R i) a)) = awayEquivPolynomial R i a := by
  suffices h : ∀ e, Proj.awayToSection 𝒜 (coord R i) ≫
      (awayι R i).appLE (Proj.basicOpen 𝒜 (coord R i)) ⊤ e = (Scheme.ΓSpecIso _).inv by
    rw [chartSectionsEquiv_apply, Scheme.Hom.appIso_hom',
      ← CommRingCat.comp_apply ((projectiveLine R).presheaf.map _), Scheme.Hom.map_appLE',
      ← CommRingCat.comp_apply (Proj.awayToSection 𝒜 _), h, Iso.inv_hom_id_apply]
    rw [← image_awayι_top]
    exact (Scheme.Hom.preimage_image_eq _ _).ge
  -- `awayToSection` is invertible, and a left inverse is `awayι` followed by `Γ(Spec -) ≅ -`
  intro e
  have := (Proj.basicOpenIsoAway 𝒜 _ (coord_mem R i) one_pos).isIso_hom
  rw [Proj.basicOpenIsoAway_hom] at this
  rw [← IsIso.eq_inv_comp, Iso.eq_comp_inv]
  refine IsIso.eq_inv_of_inv_hom_id ?_
  rw [← cancel_mono (Proj.basicOpen 𝒜 (coord R i)).topIso.inv]
  simp only [Category.assoc, Category.id_comp]
  rw [← Proj.basicOpenToSpec_app_top, ← Proj.basicOpenIsoSpec_hom 𝒜 _ (coord_mem R i) one_pos,
    Scheme.Hom.app_eq_appLE]
  -- composing the chart with `D₊(Xᵢ) ≅ Spec R[X₀, X₁]_(Xᵢ)` gives the inclusion of `D₊(Xᵢ)`
  refine (Scheme.Hom.appLE_comp_appLE _ (awayι R i) _ ⊤ _ e le_rfl).trans ?_
  simp only [awayι, Proj.awayι, Iso.hom_inv_id_assoc]
  rfl

/-- On the chart `D₊(Xᵢ)`, the functions on `Spec R` pulled back along the structure morphism are
the fractions `c / 1` of the constants. -/
theorem awayToSection_algebraMap (i : Fin 2) (c : R) :
    Proj.awayToSection 𝒜 (coord R i) (algebraMap R _ c) =
      (projectiveLine R ↘ Spec (.of R)).appLE ⊤ _ le_top ((Scheme.ΓSpecIso (.of R)).inv c) := by
  -- restricting to the image of the chart and applying `chartSectionsEquiv` is injective
  have hinj : Function.Injective fun x ↦ chartSectionsEquiv R i
      ((projectiveLine R).presheaf.map (eqToHom (image_awayι_top R i)).op x) :=
    (chartSectionsEquiv R i).injective.comp (ConcreteCategory.bijective_of_isIso _).1
  have h := chartSectionsEquiv_appLE R i ((Scheme.ΓSpecIso (.of R)).inv c)
  rw [Iso.inv_hom_id_apply] at h
  -- both sides go to the constant polynomial `c`
  refine hinj <| (chartSectionsEquiv_awayToSection R i _).trans <|
    ((awayEquivPolynomial R i).commutes c).trans <|
      (congrFun (congrArg DFunLike.coe Polynomial.algebraMap_eq) c).trans <|
        h.symm.trans (congrArg _ ?_)
  exact (ConcreteCategory.congr_hom (Scheme.Hom.appLE_map _ _ _) _).symm

/-! ### Smoothness -/

/-- The chart ring `R[X₀, X₁]_(Xᵢ)` is standard smooth of relative dimension one over `R`: it is
the polynomial ring `R[X]` (`awayEquivPolynomial`). -/
instance isStandardSmoothOfRelativeDimension_away (i : Fin 2) :
    Algebra.IsStandardSmoothOfRelativeDimension 1 R (Away 𝒜 (coord R i)) := by
  have := Algebra.IsStandardSmoothOfRelativeDimension.mvPolynomial R PUnit.{u + 1}
  rw [Nat.card_unique] at this
  exact .of_algEquiv 1
    ((MvPolynomial.uniqueAlgEquiv (R := R) PUnit.{u + 1}).trans (awayEquivPolynomial R i).symm)

/-- On the chart `D₊(Xᵢ)`, the structure morphism of the projective line is smooth of relative
dimension one. -/
theorem smoothOfRelativeDimension_awayι (i : Fin 2) :
    SmoothOfRelativeDimension 1 (awayι R i ≫ (projectiveLine R ↘ Spec (.of R))) := by
  rw [awayι_over, HasRingHomProperty.Spec_iff (P := @SmoothOfRelativeDimension 1)]
  exact RingHom.locally_of RingHom.isStandardSmoothOfRelativeDimension_respectsIso _
    ((RingHom.isStandardSmoothOfRelativeDimension_algebraMap 1).mpr inferInstance)

/-- **The projective line is smooth of relative dimension one** over `Spec R`: it is covered by
the two charts `D₊(Xᵢ)`, each of which is the affine line `Spec R[X]` over `Spec R`. -/
instance smoothOfRelativeDimension :
    SmoothOfRelativeDimension 1 (projectiveLine R ↘ Spec (.of R)) := by
  let 𝒰 : (projectiveLine R).OpenCover :=
    Scheme.Cover.mkOfCovers (Fin 2) _ (awayι R) (exists_eq_awayι R)
  have (i : 𝒰.I₀) : IsAffine (𝒰.X i) := inferInstanceAs (IsAffine (Spec _))
  exact HasRingHomProperty.of_source_openCover (P := @SmoothOfRelativeDimension 1) 𝒰
    fun i ↦ (HasRingHomProperty.iff_of_isAffine (P := @SmoothOfRelativeDimension 1)).mp
      (smoothOfRelativeDimension_awayι R i)

/-! ### Base change -/

section BaseChange

variable (S : Type u) [CommRing S] [Algebra R S]

/-- The projection `ℙ¹_S ⟶ ℙ¹_R` for an `R`-algebra `S`: the coordinates `S²` of `ℙ¹_S` are
identified with `S ⊗[R] R²`, and `Proj (Sym_S (S ⊗[R] R²))` maps to `Proj (Sym_R R²)` by extension
of scalars. -/
noncomputable def baseChangeProjection : projectiveLine S ⟶ projectiveLine R :=
  (Proj.symmetricAlgebraMapIso S (TensorProduct.piScalarRight R S S (Fin 2))).hom ≫
    (Proj.symmetricAlgebraScalarTensorIso R S (Fin 2 → R)).hom ≫
      Proj.baseChangeProjection 𝒜 S

/-- **Base change of the projective line**: for an `R`-algebra `S`, the square formed by the
projection `ℙ¹_S ⟶ ℙ¹_R`, the structure morphisms, and `Spec S ⟶ Spec R` is a pullback, that is,
`ℙ¹_S = ℙ¹_R ×_{Spec R} Spec S`. -/
theorem isPullback_baseChangeProjection :
    IsPullback (baseChangeProjection R S) (projectiveLine S ↘ Spec (.of S))
      (projectiveLine R ↘ Spec (.of R)) (Spec.map (CommRingCat.ofHom (algebraMap R S))) := by
  rw [SymmetricAlgebra.over_eq_projToSpec, SymmetricAlgebra.over_eq_projToSpec]
  refine (Proj.isPullback_symmetricAlgebra_baseChange R S (Fin 2 → R)).of_iso
    (Proj.symmetricAlgebraMapIso S (TensorProduct.piScalarRight R S S (Fin 2))).symm
    (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ (by simp) (by simp)
  · rw [Iso.refl_hom, Category.comp_id, Iso.symm_hom, baseChangeProjection, Iso.inv_hom_id_assoc]
  · rw [Iso.refl_hom, Category.comp_id, Iso.symm_hom, Iso.eq_inv_comp,
      Proj.symmetricAlgebraMapIso_hom_projToSpec]

end BaseChange

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

/-- The identification of the function field of the projective line with `R(X)` sends the
function `X₁ / X₀`, the function on the chart `D₊(X₀)` restricting to `X₁ / X₀`
(`chartSectionsEquiv_symm_X`), to `X`. -/
theorem functionFieldEquiv_symm_X :
    (functionFieldEquiv R).symm RatFunc.X =
      (projectiveLine R).germToFunctionField _ ((chartSectionsEquiv R 0).symm X) := by
  rw [AlgEquiv.symm_apply_eq, functionFieldEquiv_germToFunctionField, RingEquiv.apply_symm_apply,
    RatFunc.algebraMap_X]

end projectiveLine

end TauCeti.AlgebraicGeometry

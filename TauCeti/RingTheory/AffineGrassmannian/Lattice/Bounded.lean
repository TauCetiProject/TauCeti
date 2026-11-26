/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Module.ProjectiveLattice
public import TauCeti.RingTheory.AffineGrassmannian.Lattice.Filtration
public import TauCeti.RingTheory.LaurentSeries.Basic
public import TauCeti.RingTheory.LaurentSeries.Lattice
public import TauCeti.RingTheory.PowerSeries.TorsionQuotient

/-!
# Lattices of bounded pole order

Let `R` be a commutative ring and `ι` a finite type. The `R`-points of the loop Grassmannian of
`GL_ι` are the finite projective lattices `Λ ⊆ R⸨X⸩^ι` over `R⟦X⟧`
(`TauCeti.ProjectiveLattice R⟦X⟧ R⸨X⸩ (ι → R⸨X⸩)`). Such a lattice is *bounded by* `N`
(`TauCeti.ProjectiveLattice.IsBounded`) when

`X ^ N R⟦X⟧^ι ⊆ Λ ⊆ X ^ (-N) R⟦X⟧^ι`,

where `X ^ a R⟦X⟧^ι` (`TauCeti.LaurentSeries.piLattice`) is the lattice `TauCeti.diagonalLattice`
of the constant cocharacter `a`.
The bounded lattices are the points of the chart of pole order `N` of the loop Grassmannian.
This file identifies them with linear-algebra data on the finite free `R`-module

`M_N = X ^ (-N) R⟦X⟧^ι / X ^ N R⟦X⟧^ι` (`TauCeti.LaurentSeries.boundedLatticeQuotient`),

whose coordinates are the Laurent coefficients at the exponents `-N ≤ n < N`
(`TauCeti.LaurentSeries.boundedLatticeQuotientEquiv`, built from
`TauCeti.LaurentSeries.latticeQuotientEquiv`), so that it is free of rank `2 N · #ι`.

`TauCeti.ProjectiveLattice.boundedEquiv` is a bijection between the lattices bounded by `N` and
the `R`-submodules `W ⊆ M_N` that multiplication by `X` preserves and whose quotient `M_N ⧸ W` is
finite projective over `R`: it sends `Λ` to its image `Λ / X ^ N R⟦X⟧^ι`. The coefficient ring is
arbitrary; nonreduced rings are allowed. The content is that the finite projectivity of `Λ` over
`R⟦X⟧` corresponds exactly to the finite projectivity of `M_N ⧸ W ≅ X ^ (-N) R⟦X⟧^ι / Λ` over `R`,
which is `PowerSeries.projective_of_projective_quotient` and `PowerSeries.flat_quotient_of_flat`.

Every lattice is bounded by some `N` (`TauCeti.ProjectiveLattice.exists_isBounded`), and the
standard lattice is the only lattice bounded by `0`
(`TauCeti.ProjectiveLattice.isBounded_zero_iff`).

This file uses the `R⟦X⟧`-algebra structure of `R⸨X⸩` from Mathlib, the one making `R⸨X⸩` the
localization of `R⟦X⟧` at the powers of `X`, and the coefficientwise action of `R` on `R⸨X⸩`; it
records as instances that they form a scalar tower `R → R⟦X⟧ → R⸨X⸩` and that `R⟦X⟧ → R⸨X⸩` is
injective.

## Main declarations

* `TauCeti.LaurentSeries.piLattice R ι a`: the lattice `X ^ a R⟦X⟧^ι`.
* `TauCeti.ProjectiveLattice.IsBounded N Λ`: `X ^ N R⟦X⟧^ι ⊆ Λ ⊆ X ^ (-N) R⟦X⟧^ι`.
* `TauCeti.LaurentSeries.boundedLatticeQuotient R ι N`: the `R⟦X⟧`-module `M_N`.
* `TauCeti.LaurentSeries.boundedLatticeQuotientEquiv`: the coefficients of `M_N`.
* `TauCeti.ProjectiveLattice.boundedEquiv`: lattices bounded by `N` correspond to the
  `X`-stable `R`-submodules of `M_N` with finite projective quotient.
* `TauCeti.LaurentSeries.fg_and_projective_iff_finite_and_projective_quotient`: a submodule
  between `X ^ N R⟦X⟧^ι` and `X ^ (-N) R⟦X⟧^ι` is finite projective over `R⟦X⟧` exactly when its
  cokernel in `M_N` is finite projective over `R`.
* `TauCeti.ProjectiveLattice.exists_isBounded`: every lattice is bounded by some `N`.
* `TauCeti.diagonalLattice_eq_toSubmodule_map`: the lattice of a cocharacter is the image of the
  standard lattice, so it is finite projective.

## References

* X. Zhu, *An introduction to affine Grassmannians and the geometric Satake equivalence*,
  §1.1.
-/

public section

open scoped LaurentSeries PowerSeries
open HahnSeries

namespace TauCeti.LaurentSeries

variable (R : Type*) [CommRing R]

/-- Power series act on Laurent series compatibly with the coefficientwise action of `R`. -/
instance : IsScalarTower R R⟦X⟧ R⸨X⸩ where
  smul_assoc r p f := by
    rw [Algebra.smul_def (r • p) f, Algebra.smul_def p f, LaurentSeries.coe_algebraMap,
      PowerSeries.coe_smul, smul_mul_assoc]

/-- Power series embed into Laurent series. -/
instance : FaithfulSMul R⟦X⟧ R⸨X⸩ :=
  (faithfulSMul_iff_algebraMap_injective _ _).mpr ofPowerSeries_injective

variable {R}

/-- The unit `X` of `R⸨X⸩`, the localization of `R⟦X⟧` at the powers of `X`, is `unitX`. -/
private theorem isUnit_unit_eq_unitX :
    (IsLocalization.Away.algebraMap_isUnit (PowerSeries.X : R⟦X⟧) (S := R⸨X⸩)).unit = unitX :=
  Units.ext (by simp)

variable (ι : Type*)

variable (R) in
/-- The lattice `X ^ a R⟦X⟧^ι ⊆ R⸨X⸩^ι` of the vectors whose coordinates have vanishing
coefficients below `a`: the lattice `TauCeti.diagonalLattice` of the constant cocharacter `a`,
evaluated at the unit `X`. -/
noncomputable abbrev piLattice (a : ℤ) : Submodule R⟦X⟧ (ι → R⸨X⸩) :=
  diagonalLattice (fun _ : ι ↦ a) (IsLocalization.Away.algebraMap_isUnit (PowerSeries.X : R⟦X⟧))

variable {ι}

/-- Membership in `X ^ a R⟦X⟧^ι`, the lattice of the constant cocharacter `a`: every coordinate has
vanishing coefficients below `a`. -/
theorem mem_piLattice_iff {a : ℤ} {v : ι → R⸨X⸩} :
    v ∈ piLattice R ι a ↔
      ∀ i, v i ∈ TauCeti.LaurentSeries.lattice R R a := by
  simp only [mem_diagonalLattice, isUnit_unit_eq_unitX, val_unitX_zpow, mem_lattice_iff_exists,
    LaurentSeries.coe_algebraMap]
  exact forall_congr' fun i ↦ ⟨fun ⟨b, hb⟩ ↦ ⟨b, hb.symm⟩, fun ⟨b, hb⟩ ↦ ⟨b, hb.symm⟩⟩

end TauCeti.LaurentSeries

namespace TauCeti

section Diagonal

variable {B K : Type*} [CommRing B] [CommRing K] [Algebra B K] [FaithfulSMul B K] {ξ : B}
  {n : Type*} [Finite n]

/-- The lattice `μ(ξ) Bⁿ` of a cocharacter `μ = (k_i)` is the image of the standard lattice under
the diagonal automorphism `μ(ξ)`, which multiplies the `i`-th coordinate by the unit `ξ ^ k_i`. -/
theorem diagonalLattice_eq_toSubmodule_map (k : n → ℤ) (hξ : IsUnit (algebraMap B K ξ)) :
    diagonalLattice k hξ =
      ((ProjectiveLattice.standard B K n).map
        (LinearEquiv.piCongrRight fun i ↦ LinearEquiv.smulOfUnit (hξ.unit ^ k i))).toSubmodule := by
  ext v
  rw [ProjectiveLattice.mem_toSubmodule, ProjectiveLattice.mem_map,
    ProjectiveLattice.mem_standard, mem_diagonalLattice]
  refine forall_congr' fun i ↦ ⟨fun ⟨b, hb⟩ ↦ ⟨b, ?_⟩, fun ⟨b, hb⟩ ↦ ⟨b, ?_⟩⟩
  · simp [LinearEquiv.smulOfUnit, Units.smul_def, hb]
  · exact (Units.inv_mul_eq_iff_eq_mul _).mp
      (by simpa [LinearEquiv.smulOfUnit, Units.smul_def] using hb.symm)

/-- The lattice of a cocharacter is projective, as the image of the standard lattice. -/
instance (k : n → ℤ) (hξ : IsUnit (algebraMap B K ξ)) :
    Module.Projective B (diagonalLattice k hξ) :=
  .of_equiv (LinearEquiv.ofEq _ _ (diagonalLattice_eq_toSubmodule_map k hξ).symm)

/-- The lattice of a cocharacter is finitely generated. -/
theorem fg_diagonalLattice (k : n → ℤ) (hξ : IsUnit (algebraMap B K ξ)) :
    (diagonalLattice k hξ).FG := by
  rw [diagonalLattice_eq_toSubmodule_map]
  exact ProjectiveLattice.fg _

/-- The lattice of a cocharacter spans `Kⁿ`. -/
theorem span_diagonalLattice (k : n → ℤ) (hξ : IsUnit (algebraMap B K ξ)) :
    Submodule.span K (diagonalLattice k hξ : Set (n → K)) = ⊤ := by
  rw [diagonalLattice_eq_toSubmodule_map, ProjectiveLattice.coe_toSubmodule]
  exact ProjectiveLattice.span_coe_eq_top _

variable (n) in
/-- The standard lattice is the lattice of the zero cocharacter. -/
theorem toSubmodule_standard_eq_diagonalLattice_zero (hξ : IsUnit (algebraMap B K ξ)) :
    (ProjectiveLattice.standard B K n).toSubmodule = diagonalLattice (fun _ : n ↦ (0 : ℤ)) hξ := by
  ext v
  simp only [ProjectiveLattice.mem_toSubmodule, ProjectiveLattice.mem_standard, Set.mem_range,
    mem_diagonalLattice, zpow_zero, Units.val_one, one_mul]
  exact forall_congr' fun i ↦ ⟨fun ⟨b, hb⟩ ↦ ⟨b, hb.symm⟩, fun ⟨b, hb⟩ ↦ ⟨b, hb.symm⟩⟩

end Diagonal

end TauCeti

namespace TauCeti.LaurentSeries

variable {R : Type*} [CommRing R] {ι : Type*}

/-- The lattices `X ^ a R⟦X⟧^ι` decrease in `a`. -/
theorem piLattice_antitone :
    Antitone fun a : ℤ ↦ piLattice R ι a :=
  fun _ _ hab _ hv ↦ mem_piLattice_iff.mpr fun i ↦
    lattice_antitone hab (mem_piLattice_iff.mp hv i)

variable (R ι) in
/-- The finite-jet module `M_N = X ^ (-N) R⟦X⟧^ι / X ^ N R⟦X⟧^ι` over `R⟦X⟧`. Its `R`-module
structure is free of rank `2 N · #ι`, with coordinates the Laurent coefficients at the exponents
`-N ≤ n < N` (`TauCeti.LaurentSeries.boundedLatticeQuotientEquiv`). -/
abbrev boundedLatticeQuotient (N : ℕ) :=
  piLattice R ι (-N : ℤ) ⧸
    (piLattice R ι (N : ℤ)).comap
      (piLattice R ι (-N : ℤ)).subtype

/-- A coordinate of a vector of `X ^ (-N) R⟦X⟧^ι`, as an element of `X ^ (-N) R⟦X⟧`. -/
private noncomputable def boundedCoord (N : ℕ) (i : ι) :
    piLattice R ι (-N : ℤ) →ₗ[R] lattice R R (-N) :=
  (LinearMap.proj i ∘ₗ
      (piLattice R ι (-N : ℤ)).subtype.restrictScalars R
    ).codRestrict (lattice R R (-N)) fun v ↦ mem_piLattice_iff.mp v.property i

private theorem coe_boundedCoord (N : ℕ) (i : ι)
    (v : piLattice R ι (-N : ℤ)) :
    (boundedCoord N i v : R⸨X⸩) = (v : ι → R⸨X⸩) i :=
  rfl

/-- The coefficients at `-N ≤ n < N` of the coordinates of a vector of `X ^ (-N) R⟦X⟧^ι`. -/
private noncomputable def boundedCoeff (N : ℕ) :
    piLattice R ι (-N : ℤ) →ₗ[R]
      (ι → Finset.Ico (-N : ℤ) N → R) :=
  LinearMap.pi fun i ↦
    (latticeQuotientEquiv R R (-N) N).toLinearMap ∘ₗ Submodule.mkQ _ ∘ₗ boundedCoord N i

private theorem boundedCoeff_apply (N : ℕ)
    (v : piLattice R ι (-N : ℤ)) (i : ι)
    (m : Finset.Ico (-N : ℤ) N) : boundedCoeff N v i m = ((v : ι → R⸨X⸩) i).coeff m := by
  simp [boundedCoeff, latticeQuotientEquiv_mk, coe_boundedCoord]

private theorem ker_boundedCoeff (N : ℕ) :
    LinearMap.ker (boundedCoeff (R := R) (ι := ι) N) =
      ((piLattice R ι (N : ℤ)).comap
        (piLattice R ι (-N : ℤ)).subtype).restrictScalars
          R := by
  ext v
  simp only [LinearMap.mem_ker, Submodule.restrictScalars_mem, Submodule.mem_comap,
    Submodule.subtype_apply, mem_piLattice_iff]
  rw [funext_iff]
  refine forall_congr' fun i ↦ ?_
  simp [boundedCoeff, Submodule.Quotient.mk_eq_zero, coe_boundedCoord]

private theorem boundedCoeff_surjective (N : ℕ) :
    Function.Surjective (boundedCoeff (R := R) (ι := ι) N) := by
  intro g
  choose f hf using fun i ↦
    Submodule.Quotient.mk_surjective _ ((latticeQuotientEquiv R R (-N) N).symm (g i))
  refine ⟨⟨fun i ↦ f i, mem_piLattice_iff.mpr fun i ↦ (f i).property⟩, ?_⟩
  funext i
  rw [boundedCoeff, LinearMap.pi_apply, LinearMap.comp_apply, LinearMap.comp_apply,
    show boundedCoord N i _ = f i from Subtype.ext (coe_boundedCoord N i _), Submodule.mkQ_apply,
    hf, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]

variable (R ι) in
/-- The coordinates of `M_N = X ^ (-N) R⟦X⟧^ι / X ^ N R⟦X⟧^ι`: the Laurent coefficients of the
coordinates at the exponents `-N ≤ n < N`, through `TauCeti.LaurentSeries.latticeQuotientEquiv`. -/
noncomputable def boundedLatticeQuotientEquiv (N : ℕ) :
    boundedLatticeQuotient R ι N ≃ₗ[R] (ι → Finset.Ico (-N : ℤ) N → R) :=
  (Submodule.Quotient.restrictScalarsEquiv R _).symm.trans <|
    (Submodule.quotEquivOfEq _ _ (ker_boundedCoeff N).symm).trans <|
      (boundedCoeff N).quotKerEquivOfSurjective (boundedCoeff_surjective N)

/-- The coordinates of the class of `v` are the coefficients of the coordinates of `v`. -/
@[simp]
theorem boundedLatticeQuotientEquiv_mk (N : ℕ)
    (v : piLattice R ι (-N : ℤ)) (i : ι)
    (m : Finset.Ico (-N : ℤ) N) :
    boundedLatticeQuotientEquiv R ι N (Submodule.Quotient.mk v) i m =
      ((v : ι → R⸨X⸩) i).coeff m := by
  simp [boundedLatticeQuotientEquiv, Submodule.Quotient.restrictScalarsEquiv_symm_mk,
    boundedCoeff_apply]

/-- `M_N` is free over `R`, with the basis of its coefficients. -/
instance [Finite ι] (N : ℕ) : Module.Free R (boundedLatticeQuotient R ι N) :=
  .of_equiv (boundedLatticeQuotientEquiv R ι N).symm

/-- `M_N` is finite over `R`. -/
instance [Finite ι] (N : ℕ) : Module.Finite R (boundedLatticeQuotient R ι N) :=
  .equiv (boundedLatticeQuotientEquiv R ι N).symm

/-- `M_N` is free of rank `2 N · #ι`. -/
theorem finrank_boundedLatticeQuotient [Fintype ι] [StrongRankCondition R] (N : ℕ) :
    Module.finrank R (boundedLatticeQuotient R ι N) = 2 * N * Fintype.card ι := by
  rw [(boundedLatticeQuotientEquiv R ι N).finrank_eq, ← (LinearEquiv.curry R R ι _).finrank_eq,
    Module.finrank_fintype_fun_eq_card, Fintype.card_prod, Fintype.card_coe, Int.card_Ico]
  rw [mul_comm]
  congr 1
  omega

/-- Multiplication by `X ^ (2 N)` carries `X ^ (-N) R⟦X⟧^ι` into `X ^ N R⟦X⟧^ι`. -/
theorem X_pow_smul_mem_piLattice (N : ℕ) {v : ι → R⸨X⸩}
    (hv : v ∈ piLattice R ι (-N : ℤ)) :
    (PowerSeries.X ^ (2 * N) : R⟦X⟧) • v ∈
      piLattice R ι (N : ℤ) := by
  rw [mem_piLattice_iff] at hv ⊢
  intro i
  have h := mul_mem_lattice (single_mem_lattice (R := R) (le_refl ((2 * N : ℕ) : ℤ)) 1) (hv i)
  rw [show ((2 * N : ℕ) : ℤ) + -N = N by push_cast; ring] at h
  simpa [Algebra.smul_def, ofPowerSeries_X_pow] using h

/-- `M_N` is killed by `X ^ (2 N)`. -/
theorem X_pow_smul_boundedLatticeQuotient (N : ℕ) (q : boundedLatticeQuotient R ι N) :
    (PowerSeries.X ^ (2 * N) : R⟦X⟧) • q = 0 := by
  induction q using Submodule.Quotient.induction_on with
  | _ v =>
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero, Submodule.mem_comap,
      Submodule.subtype_apply, Submodule.coe_smul]
    exact X_pow_smul_mem_piLattice N v.property

variable (N : ℕ)

/-- The image `Λ / X ^ N R⟦X⟧^ι` in `M_N` of a submodule `Λ ⊆ R⸨X⸩^ι`. -/
noncomputable def jetSubmodule (Λ : Submodule R⟦X⟧ (ι → R⸨X⸩)) :
    Submodule R⟦X⟧ (boundedLatticeQuotient R ι N) :=
  (Λ.comap (piLattice R ι (-N : ℤ)).subtype).map
    (Submodule.mkQ _)

/-- The preimage in `X ^ (-N) R⟦X⟧^ι ⊆ R⸨X⸩^ι` of a submodule of `M_N`. -/
noncomputable def jetPreimage (W : Submodule R⟦X⟧ (boundedLatticeQuotient R ι N)) :
    Submodule R⟦X⟧ (ι → R⸨X⸩) :=
  (W.comap (Submodule.mkQ _)).map
    (piLattice R ι (-N : ℤ)).subtype

variable {N}

/-- For `X ^ N R⟦X⟧^ι ⊆ Λ`, the class of `v` lies in the image of `Λ` exactly when `v ∈ Λ`. -/
theorem mk_mem_jetSubmodule_iff {Λ : Submodule R⟦X⟧ (ι → R⸨X⸩)}
    (hΛ : piLattice R ι (N : ℤ) ≤ Λ)
    (v : piLattice R ι (-N : ℤ)) :
    (Submodule.Quotient.mk v : boundedLatticeQuotient R ι N) ∈ jetSubmodule N Λ ↔
      (v : ι → R⸨X⸩) ∈ Λ := by
  rw [jetSubmodule, ← Submodule.mkQ_apply, ← Submodule.mem_comap, Submodule.comap_map_mkQ,
    sup_eq_right.mpr fun w hw ↦ hΛ hw, Submodule.mem_comap, Submodule.subtype_apply]

/-- A vector lies in the preimage of `W` when it lies in `X ^ (-N) R⟦X⟧^ι` with class in `W`. -/
theorem mem_jetPreimage_iff {W : Submodule R⟦X⟧ (boundedLatticeQuotient R ι N)}
    {v : ι → R⸨X⸩} :
    v ∈ jetPreimage N W ↔
      ∃ hv : v ∈ piLattice R ι (-N : ℤ),
        (Submodule.Quotient.mk ⟨v, hv⟩ : boundedLatticeQuotient R ι N) ∈ W := by
  simp [jetPreimage]

/-- The preimage of a submodule of `M_N` lies in `X ^ (-N) R⟦X⟧^ι`. -/
theorem jetPreimage_le (W : Submodule R⟦X⟧ (boundedLatticeQuotient R ι N)) :
    jetPreimage N W ≤ piLattice R ι (-N : ℤ) :=
  Submodule.map_subtype_le _ _

/-- The preimage of a submodule of `M_N` contains `X ^ N R⟦X⟧^ι`. -/
theorem le_jetPreimage (W : Submodule R⟦X⟧ (boundedLatticeQuotient R ι N)) :
    piLattice R ι (N : ℤ) ≤ jetPreimage N W := by
  intro v hv
  have hv' : v ∈ piLattice R ι (-N : ℤ) :=
    piLattice_antitone (by omega : (-N : ℤ) ≤ N) hv
  refine mem_jetPreimage_iff.mpr ⟨hv', ?_⟩
  convert W.zero_mem
  exact (Submodule.Quotient.mk_eq_zero _).mpr hv

/-- The image of the preimage of a submodule of `M_N` is that submodule. -/
@[simp]
theorem jetSubmodule_jetPreimage (W : Submodule R⟦X⟧ (boundedLatticeQuotient R ι N)) :
    jetSubmodule N (jetPreimage N W) = W := by
  rw [jetSubmodule, jetPreimage,
    Submodule.comap_map_eq_of_injective (Submodule.injective_subtype _),
    Submodule.map_comap_eq_of_surjective (Submodule.mkQ_surjective _)]

/-- A submodule between `X ^ N R⟦X⟧^ι` and `X ^ (-N) R⟦X⟧^ι` is the preimage of its image. -/
theorem jetPreimage_jetSubmodule {Λ : Submodule R⟦X⟧ (ι → R⸨X⸩)}
    (h₀ : piLattice R ι (N : ℤ) ≤ Λ)
    (h₁ : Λ ≤ piLattice R ι (-N : ℤ)) :
    jetPreimage N (jetSubmodule N Λ) = Λ := by
  rw [jetPreimage, jetSubmodule, Submodule.comap_map_mkQ, sup_eq_right.mpr fun w hw ↦ h₀ hw,
    Submodule.map_comap_subtype, inf_eq_right.mpr h₁]

section Projectivity

variable [Finite ι] {Λ : Submodule R⟦X⟧ (ι → R⸨X⸩)}

/-- For `X ^ N R⟦X⟧^ι ⊆ Λ`, the quotient of `M_N` by the image of `Λ` is
`X ^ (-N) R⟦X⟧^ι / Λ`. -/
private noncomputable def quotientJetEquiv
    (h₀ : piLattice R ι (N : ℤ) ≤ Λ) :
    (boundedLatticeQuotient R ι N ⧸ (jetSubmodule N Λ).restrictScalars R) ≃ₗ[R]
      piLattice R ι (-N : ℤ) ⧸
        Λ.comap (piLattice R ι (-N : ℤ)).subtype :=
  (Submodule.Quotient.restrictScalarsEquiv R _).trans
    ((Submodule.quotientQuotientEquivQuotient
      ((piLattice R ι (N : ℤ)).comap
        (piLattice R ι (-N : ℤ)).subtype)
      (Λ.comap (piLattice R ι (-N : ℤ)).subtype)
      fun _ hw ↦ h₀ hw).restrictScalars R)

/-- **Finite projectivity of a bounded lattice.** Let `X ^ N R⟦X⟧^ι ⊆ Λ ⊆ X ^ (-N) R⟦X⟧^ι`. Then
`Λ` is finitely generated and projective over `R⟦X⟧` exactly when the quotient of `M_N` by the
image of `Λ`, that is `X ^ (-N) R⟦X⟧^ι / Λ`, is finite and projective over `R`. -/
theorem fg_and_projective_iff_finite_and_projective_quotient
    (h₀ : piLattice R ι (N : ℤ) ≤ Λ)
    (h₁ : Λ ≤ piLattice R ι (-N : ℤ)) :
    Λ.FG ∧ Module.Projective R⟦X⟧ Λ ↔
      Module.Finite R (boundedLatticeQuotient R ι N ⧸ (jetSubmodule N Λ).restrictScalars R) ∧
        Module.Projective R
          (boundedLatticeQuotient R ι N ⧸ (jetSubmodule N Λ).restrictScalars R) := by
  set F := piLattice R ι (-N : ℤ)
  set Λ₀ := (piLattice R ι (N : ℤ)).comap F.subtype
  set Λ' := Λ.comap F.subtype
  set W := jetSubmodule N Λ
  have hle : Λ₀ ≤ Λ' := fun _ hw ↦ h₀ hw
  let e := quotientJetEquiv h₀
  let eΛ : Λ' ≃ₗ[R⟦X⟧] Λ := Submodule.comapSubtypeEquivOfLe h₁
  have hk (f : F) : (PowerSeries.X ^ (2 * N) : R⟦X⟧) • f ∈ Λ' :=
    h₀ (X_pow_smul_mem_piLattice N f.property)
  have hW : W = Λ'.map Λ₀.mkQ := rfl
  constructor
  · rintro ⟨hfg, hproj⟩
    have : Module.Flat R⟦X⟧ Λ' := have := Module.Projective.of_equiv eΛ.symm; inferInstance
    have : Module.Flat R (F ⧸ Λ') := PowerSeries.flat_quotient_of_flat hle hk
    have : Module.Finite R⟦X⟧ Λ := Module.Finite.iff_fg.mpr hfg
    have hW' : W.FG := hW ▸ (Module.Finite.iff_fg.mp (Module.Finite.equiv eΛ.symm)).map _
    have : Module.FinitePresentation R
        (boundedLatticeQuotient R ι N ⧸ W.restrictScalars R) :=
      Module.finitePresentation_of_free_of_surjective _ (W.restrictScalars R).mkQ_surjective
        (by rw [Submodule.ker_mkQ]
            exact PowerSeries.fg_restrictScalars_of_fg (X_pow_smul_boundedLatticeQuotient N) hW')
    have : Module.Flat R (boundedLatticeQuotient R ι N ⧸ W.restrictScalars R) :=
      Module.Flat.of_linearEquiv e
    exact ⟨inferInstance, Module.Flat.projective_of_finitePresentation⟩
  · rintro ⟨hfin, hproj⟩
    have : Module.Projective R (F ⧸ Λ') := .of_equiv e
    have : Module.Projective R⟦X⟧ Λ' := PowerSeries.projective_of_projective_quotient hk
    refine ⟨?_, .of_equiv eΛ⟩
    have : Module.FinitePresentation R (boundedLatticeQuotient R ι N ⧸ W.restrictScalars R) :=
      Module.finitePresentation_of_projective _ _
    have hWR : (W.restrictScalars R).FG := by
      simpa using Module.FinitePresentation.fg_ker _ (W.restrictScalars R).mkQ_surjective
    have hΛ₀ : Λ₀.FG := by
      have : Module.Finite R⟦X⟧
          (piLattice R ι (N : ℤ)) :=
        Module.Finite.iff_fg.mpr (fg_diagonalLattice _ _)
      exact Module.Finite.iff_fg.mp (Module.Finite.equiv
        (Submodule.comapSubtypeEquivOfLe (piLattice_antitone (by omega))).symm)
    have hΛ' : Λ'.FG := Submodule.fg_of_fg_map_of_fg_inf_ker Λ₀.mkQ
      (hW ▸ Submodule.FG.of_restrictScalars R hWR)
      (by rwa [Submodule.ker_mkQ, inf_eq_right.mpr hle])
    rw [← inf_eq_right.mpr h₁, ← Submodule.map_comap_subtype]
    exact hΛ'.map _

end Projectivity

end TauCeti.LaurentSeries

namespace TauCeti.ProjectiveLattice

open TauCeti.LaurentSeries

variable {R : Type*} [CommRing R] {ι : Type*}

/-- A lattice `Λ ⊆ R⸨X⸩^ι` is *bounded by* `N` when `X ^ N R⟦X⟧^ι ⊆ Λ ⊆ X ^ (-N) R⟦X⟧^ι`. -/
def IsBounded (N : ℕ) (Λ : ProjectiveLattice R⟦X⟧ R⸨X⸩ (ι → R⸨X⸩)) : Prop :=
  piLattice R ι (N : ℤ) ≤ Λ.toSubmodule ∧
    Λ.toSubmodule ≤ piLattice R ι (-N : ℤ)

variable [Finite ι] {N : ℕ}

/-- The lattice `jetPreimage N W` of an `X`-stable `R`-submodule `W ⊆ M_N` with finite projective
quotient. -/
private noncomputable def ofJet
    (W : {W : Submodule R (boundedLatticeQuotient R ι N) //
      (∀ w ∈ W, (PowerSeries.X : R⟦X⟧) • w ∈ W) ∧
        Module.Finite R (boundedLatticeQuotient R ι N ⧸ W) ∧
          Module.Projective R (boundedLatticeQuotient R ι N ⧸ W)}) :
    ProjectiveLattice R⟦X⟧ R⸨X⸩ (ι → R⸨X⸩) :=
  have key := (fg_and_projective_iff_finite_and_projective_quotient (le_jetPreimage
    (PowerSeries.submoduleOfXSMulMem (X_pow_smul_boundedLatticeQuotient N) W.val W.property.1))
    (jetPreimage_le _)).mpr (by
      rw [jetSubmodule_jetPreimage, PowerSeries.restrictScalars_submoduleOfXSMulMem]
      exact W.property.2)
  { toSubmodule :=
      jetPreimage N (PowerSeries.submoduleOfXSMulMem (X_pow_smul_boundedLatticeQuotient N) W.val
        W.property.1)
    fg := key.1
    projective := key.2
    span_eq_top := eq_top_iff.mpr <| (span_diagonalLattice _ _).ge.trans
      (Submodule.span_mono (le_jetPreimage _)) }

variable (R ι N) in
/-- **Lattices of bounded pole order are subspaces of finite jets.** The lattices `Λ ⊆ R⸨X⸩^ι`
with `X ^ N R⟦X⟧^ι ⊆ Λ ⊆ X ^ (-N) R⟦X⟧^ι` correspond to the `R`-submodules `W` of
`M_N = X ^ (-N) R⟦X⟧^ι / X ^ N R⟦X⟧^ι` that multiplication by `X` preserves and whose quotient
is finite projective over `R`. A lattice goes to its image in `M_N`
(`TauCeti.ProjectiveLattice.mk_mem_boundedEquiv_apply_iff`), and a submodule to its preimage. -/
noncomputable def boundedEquiv :
    {Λ : ProjectiveLattice R⟦X⟧ R⸨X⸩ (ι → R⸨X⸩) // Λ.IsBounded N} ≃
      {W : Submodule R (boundedLatticeQuotient R ι N) //
        (∀ w ∈ W, (PowerSeries.X : R⟦X⟧) • w ∈ W) ∧
          Module.Finite R (boundedLatticeQuotient R ι N ⧸ W) ∧
            Module.Projective R (boundedLatticeQuotient R ι N ⧸ W)} where
  toFun Λ := ⟨(jetSubmodule N Λ.val.toSubmodule).restrictScalars R,
    fun _ hw ↦ (jetSubmodule N Λ.val.toSubmodule).smul_mem _ hw,
    (fg_and_projective_iff_finite_and_projective_quotient Λ.property.1 Λ.property.2).mp
      ⟨Λ.val.fg, Λ.val.projective⟩⟩
  invFun W := ⟨ofJet W, le_jetPreimage _, jetPreimage_le _⟩
  left_inv Λ := Subtype.ext <| toSubmodule_injective <| by
    simp only [ofJet, PowerSeries.submoduleOfXSMulMem_restrictScalars]
    exact jetPreimage_jetSubmodule Λ.property.1 Λ.property.2
  right_inv W := Subtype.ext <| by
    simp only [ofJet, jetSubmodule_jetPreimage, PowerSeries.restrictScalars_submoduleOfXSMulMem]

/-- The submodule of `M_N` of a bounded lattice is its image. -/
@[simp]
theorem coe_boundedEquiv_apply (Λ : {Λ : ProjectiveLattice R⟦X⟧ R⸨X⸩ (ι → R⸨X⸩) // Λ.IsBounded N}) :
    (boundedEquiv R ι N Λ : Submodule R (boundedLatticeQuotient R ι N)) =
      (jetSubmodule N Λ.val.toSubmodule).restrictScalars R :=
  (rfl)

/-- The submodule of `M_N` of a lattice `Λ` bounded by `N` is its image `Λ / X ^ N R⟦X⟧^ι`. -/
theorem mk_mem_boundedEquiv_apply_iff
    (Λ : {Λ : ProjectiveLattice R⟦X⟧ R⸨X⸩ (ι → R⸨X⸩) // Λ.IsBounded N})
    (v : piLattice R ι (-N : ℤ)) :
    (Submodule.Quotient.mk v : boundedLatticeQuotient R ι N) ∈ (boundedEquiv R ι N Λ).val ↔
      (v : ι → R⸨X⸩) ∈ Λ.val :=
  mk_mem_jetSubmodule_iff Λ.property.1 v

/-- The lattice of an `X`-stable submodule of `M_N` is its preimage. -/
theorem toSubmodule_boundedEquiv_symm_apply
    (W : {W : Submodule R (boundedLatticeQuotient R ι N) //
      (∀ w ∈ W, (PowerSeries.X : R⟦X⟧) • w ∈ W) ∧
        Module.Finite R (boundedLatticeQuotient R ι N ⧸ W) ∧
          Module.Projective R (boundedLatticeQuotient R ι N ⧸ W)}) :
    ((boundedEquiv R ι N).symm W).val.toSubmodule =
      jetPreimage N (PowerSeries.submoduleOfXSMulMem (X_pow_smul_boundedLatticeQuotient N) W.val
        W.property.1) :=
  (rfl)

/-- The lattice of an `X`-stable submodule `W ⊆ M_N` is its preimage in `X ^ (-N) R⟦X⟧^ι`. -/
theorem mem_boundedEquiv_symm_apply_iff
    (W : {W : Submodule R (boundedLatticeQuotient R ι N) //
      (∀ w ∈ W, (PowerSeries.X : R⟦X⟧) • w ∈ W) ∧
        Module.Finite R (boundedLatticeQuotient R ι N ⧸ W) ∧
          Module.Projective R (boundedLatticeQuotient R ι N ⧸ W)}) {v : ι → R⸨X⸩} :
    v ∈ ((boundedEquiv R ι N).symm W).val ↔
      ∃ hv : v ∈ piLattice R ι (-N : ℤ),
        (Submodule.Quotient.mk ⟨v, hv⟩ : boundedLatticeQuotient R ι N) ∈ W.val := by
  rw [← mem_toSubmodule, toSubmodule_boundedEquiv_symm_apply, mem_jetPreimage_iff]
  simp only [PowerSeries.mem_submoduleOfXSMulMem]

/-- The lattices bounded by `0` are the standard lattice only. -/
theorem isBounded_zero_iff {Λ : ProjectiveLattice R⟦X⟧ R⸨X⸩ (ι → R⸨X⸩)} :
    Λ.IsBounded 0 ↔ Λ = standard R⟦X⟧ R⸨X⸩ ι := by
  rw [IsBounded, ← toSubmodule_inj, toSubmodule_standard_eq_diagonalLattice_zero ι
    (IsLocalization.Away.algebraMap_isUnit (PowerSeries.X : R⟦X⟧)), Nat.cast_zero, neg_zero,
    le_antisymm_iff, and_comm]

/-- **Every lattice has bounded pole order.** A finite projective lattice in `R⸨X⸩^ι` is bounded by
some `N`: it is commensurable with the standard lattice. -/
theorem exists_isBounded (Λ : ProjectiveLattice R⟦X⟧ R⸨X⸩ (ι → R⸨X⸩)) : ∃ N, Λ.IsBounded N := by
  have hX := IsLocalization.Away.algebraMap_isUnit (PowerSeries.X : R⟦X⟧) (S := R⸨X⸩)
  have hstd := toSubmodule_standard_eq_diagonalLattice_zero ι hX
  obtain ⟨_, ⟨a, rfl⟩, ha⟩ :=
    Λ.exists_smul_mem (Submonoid.powers PowerSeries.X) (standard R⟦X⟧ R⸨X⸩ ι)
  obtain ⟨_, ⟨b, rfl⟩, hb⟩ :=
    (standard R⟦X⟧ R⸨X⸩ ι).exists_smul_mem (Submonoid.powers PowerSeries.X) Λ
  refine ⟨max a b, fun v hv ↦ ?_, fun v hv ↦ ?_⟩
  · -- `v = X ^ b • w` with `w = X ^ (-b) • v` in the standard lattice.
    set w : ι → R⸨X⸩ := (hX.unit ^ (-(b : ℤ))) • v
    have hw : (PowerSeries.X ^ b : R⟦X⟧) • w = v := by
      funext i
      rw [Pi.smul_apply, Algebra.smul_def, show w i = single (-(b : ℤ)) 1 * v i by
          simp only [w]
          rw [Pi.smul_apply, Units.smul_def, isUnit_unit_eq_unitX, val_unitX_zpow, smul_eq_mul],
        ← mul_assoc, LaurentSeries.coe_algebraMap,
        ofPowerSeries_X_pow, single_mul_single]
      simp
    rw [← hw]
    refine hb w (mem_toSubmodule.mp (hstd ▸ ?_))
    have hv' := piLattice_antitone (show (b : ℤ) ≤ (max a b : ℕ) by omega) hv
    rw [← hw, pow_smul_mem_diagonalLattice_iff] at hv'
    simpa using hv'
  · have hv' := (pow_smul_mem_diagonalLattice_iff hX (fun _ : ι ↦ (0 : ℤ)) a).mp
      (hstd ▸ mem_toSubmodule.mpr (ha v hv))
    exact piLattice_antitone (show -((max a b : ℕ) : ℤ) ≤ 0 - a by omega) hv'

end TauCeti.ProjectiveLattice

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Module.ProjectiveLattice
public import TauCeti.RingTheory.AffineGrassmannian.Lattice.Filtration
public import TauCeti.RingTheory.LaurentSeries.Basic
public import TauCeti.RingTheory.LaurentSeries.Module.Lattice
public import TauCeti.RingTheory.LaurentSeries.ModuleTopology
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
localization of `R⟦X⟧` at the powers of `X`, and the coefficientwise action of `R` on `R⸨X⸩`, which
form a scalar tower `R → R⟦X⟧ → R⸨X⸩` by an instance of `TauCeti.RingTheory.LaurentSeries.Basic`.

## Main declarations

* `TauCeti.LaurentSeries.piLattice R ι a`: the lattice `X ^ a R⟦X⟧^ι`.
* `TauCeti.ProjectiveLattice.IsBounded N Λ`: `X ^ N R⟦X⟧^ι ⊆ Λ ⊆ X ^ (-N) R⟦X⟧^ι`.
* `TauCeti.LaurentSeries.boundedLatticeQuotient R ι N`: the `R⟦X⟧`-module `M_N`.
* `TauCeti.LaurentSeries.piLatticeQuotientHahnEquiv`: the power-series-linear comparison of
  coordinate jets and vector-valued Hahn jets on any interval `[a,b)` for finite `ι`.
* `TauCeti.LaurentSeries.boundedLatticeQuotientEquiv`: the coefficients of `M_N`.
* `TauCeti.ProjectiveLattice.boundedEquiv`: lattices bounded by `N` correspond to the
  `X`-stable `R`-submodules of `M_N` with finite projective quotient.
* `TauCeti.LaurentSeries.fg_and_projective_iff_projective_quotient`: a submodule
  between `X ^ N R⟦X⟧^ι` and `X ^ (-N) R⟦X⟧^ι` is finite projective over `R⟦X⟧` exactly when its
  cokernel in `M_N` is projective over `R` (its finiteness is automatic).
* `TauCeti.ProjectiveLattice.exists_isBounded`: every lattice is bounded by some `N`.

## References

* X. Zhu, *An introduction to affine Grassmannians and the geometric Satake equivalence*,
  §1.1.
-/

public section

open scoped LaurentSeries PowerSeries
open HahnSeries

namespace TauCeti.LaurentSeries

variable {R : Type*} [CommRing R]

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

namespace TauCeti.LaurentSeries

variable {R : Type*} [CommRing R] {ι : Type*}

/-- The lattices `X ^ a R⟦X⟧^ι` decrease in `a`. -/
theorem piLattice_antitone :
    Antitone fun a : ℤ ↦ piLattice R ι a :=
  fun _ _ hab _ hv ↦ mem_piLattice_iff.mpr fun i ↦
    lattice_antitone hab (mem_piLattice_iff.mp hv i)

variable (R ι) in
/-- The finite-jet module `M_N = X ^ (-N) R⟦X⟧^ι / X ^ N R⟦X⟧^ι` over `R⟦X⟧`. As an `R`-module its
coordinates are the Laurent coefficients at the exponents `-N ≤ n < N`
(`TauCeti.LaurentSeries.boundedLatticeQuotientEquiv`); for finite `ι` it is free of rank
`2 N · #ι`. -/
abbrev boundedLatticeQuotient (N : ℕ) :=
  piLattice R ι (-N : ℤ) ⧸
    (piLattice R ι (N : ℤ)).comap
      (piLattice R ι (-N : ℤ)).subtype

/-- A coordinate of a vector of `X ^ a R⟦X⟧^ι`, as an element of `X ^ a R⟦X⟧`. -/
private noncomputable def latticeCoord (a : ℤ) (i : ι) :
    piLattice R ι a →ₗ[R] lattice R R a :=
  (LinearMap.proj i ∘ₗ
      (piLattice R ι a).subtype.restrictScalars R
    ).codRestrict (lattice R R a) fun v ↦ mem_piLattice_iff.mp v.property i

private theorem coe_latticeCoord (a : ℤ) (i : ι)
    (v : piLattice R ι a) :
    (latticeCoord a i v : R⸨X⸩) = (v : ι → R⸨X⸩) i :=
  rfl

/-- The coefficients at `a ≤ n < b` of the coordinates of a vector of `X ^ a R⟦X⟧^ι`. -/
private noncomputable def latticeCoeff (a b : ℤ) :
    piLattice R ι a →ₗ[R]
      (ι → Finset.Ico a b → R) :=
  LinearMap.pi fun i ↦
    (latticeQuotientEquiv R R a b).toLinearMap ∘ₗ Submodule.mkQ _ ∘ₗ latticeCoord a i

private theorem latticeCoeff_apply (a b : ℤ)
    (v : piLattice R ι a) (i : ι)
    (m : Finset.Ico a b) : latticeCoeff a b v i m = ((v : ι → R⸨X⸩) i).coeff m := by
  simp [latticeCoeff, latticeQuotientEquiv_mk, coe_latticeCoord]

private theorem ker_latticeCoeff (a b : ℤ) :
    LinearMap.ker (latticeCoeff (R := R) (ι := ι) a b) =
      ((piLattice R ι b).comap
        (piLattice R ι a).subtype).restrictScalars
          R := by
  rw [latticeCoeff, LinearMap.ker_pi]
  ext v
  simp only [Submodule.mem_iInf, LinearMap.mem_ker, Submodule.restrictScalars_mem,
    Submodule.mem_comap, Submodule.subtype_apply, mem_piLattice_iff]
  refine forall_congr' fun i ↦ ?_
  simp [Submodule.Quotient.mk_eq_zero, coe_latticeCoord]

private theorem latticeCoeff_surjective (a b : ℤ) :
    Function.Surjective (latticeCoeff (R := R) (ι := ι) a b) := by
  have h : Function.Surjective (LinearMap.piMap fun _ : ι ↦
      (latticeQuotientEquiv R R a b).toLinearMap ∘ₗ Submodule.mkQ _) :=
    Function.Surjective.piMap fun _ ↦
      (latticeQuotientEquiv R R a b).surjective.comp (Submodule.mkQ_surjective _)
  intro g
  obtain ⟨f, hf⟩ := h g
  refine ⟨⟨fun i ↦ f i, mem_piLattice_iff.mpr fun i ↦ (f i).property⟩, ?_⟩
  exact hf

variable (R ι) in
/-- For arbitrary coordinate types, the coefficients of a jet on `[a,b)` are its coordinates
at those exponents, through `TauCeti.LaurentSeries.latticeQuotientEquiv`. -/
noncomputable def piLatticeQuotientEquiv (a b : ℤ) :
    (piLattice R ι a ⧸ (piLattice R ι b).comap (piLattice R ι a).subtype) ≃ₗ[R]
      (ι → Finset.Ico a b → R) :=
  (Submodule.Quotient.restrictScalarsEquiv R _).symm.trans <|
    (Submodule.quotEquivOfEq _ _ (ker_latticeCoeff a b).symm).trans <|
      (latticeCoeff a b).quotKerEquivOfSurjective (latticeCoeff_surjective a b)

/-- The coordinates of the class of `v` are the coefficients of the coordinates of `v`. -/
@[simp]
theorem piLatticeQuotientEquiv_mk (a b : ℤ)
    (v : piLattice R ι a) (i : ι)
    (m : Finset.Ico a b) :
    piLatticeQuotientEquiv R ι a b (Submodule.Quotient.mk v) i m =
      ((v : ι → R⸨X⸩) i).coeff m := by
  simp [piLatticeQuotientEquiv, Submodule.Quotient.restrictScalarsEquiv_symm_mk,
    latticeCoeff_apply]

-- Cache these instances before forming quotients: synthesis through the hidden scalar action
-- of `HahnModule` does not unfold the function-module instance at reducible transparency.
/-- The additive group on coordinate-valued Hahn series, cached for quotient synthesis. -/
private local instance hahnCoordinateAddCommGroup :
    AddCommGroup (_root_.HahnModule ℤ R (ι → R)) := inferInstance

/-- The additive group on a coordinate-valued Hahn lattice, cached for quotient synthesis. -/
private noncomputable local instance hahnCoordinateLatticeAddCommGroup (a : ℤ) :
    AddCommGroup (TauCeti.HahnModule.powerSeriesLattice R (ι → R) a) := inferInstance

/-- For finite coordinate types, the vector-valued and coordinate lattices agree over
`R⟦X⟧`. This comparison retains arbitrary pole orders. -/
noncomputable def piLatticeHahnEquiv [Finite ι] (a : ℤ) :
    piLattice R ι a ≃ₗ[R⟦X⟧] TauCeti.HahnModule.powerSeriesLattice R (ι → R) a := by
  let b := Pi.basisFun R ι
  let e := b.laurentSeriesEquiv
  have he (f : _root_.HahnModule ℤ R (ι → R)) :
      f ∈ TauCeti.HahnModule.powerSeriesLattice R (ι → R) a ↔ e f ∈ piLattice R ι a := by
    rw [TauCeti.HahnModule.mem_powerSeriesLattice, mem_piLattice_iff]
    exact b.mem_lattice_iff_laurentSeriesEquiv f a
  let e' : _root_.HahnModule ℤ R (ι → R) ≃ₗ[R⟦X⟧] (ι → R⸨X⸩) :=
    { e.toAddEquiv with
      map_smul' p f := by
        -- Expose the additive-equivalence coercion so the Laurent-linear map lemma applies.
        change e ((p : R⸨X⸩) • f) = p • e f
        rw [e.map_smul]
        rfl }
  exact
    { toFun v := ⟨e'.symm v, (he _).mpr (by
        -- The auxiliary equivalence has the same function as `e`; name that function for rewriting.
        change e' (e'.symm v.val) ∈ piLattice R ι a
        rw [e'.apply_symm_apply]
        exact v.property)⟩
      invFun f := ⟨e' f, (he _).mp f.property⟩
      left_inv v := Subtype.ext (e'.apply_symm_apply v)
      right_inv f := Subtype.ext (e'.symm_apply_apply f)
      map_add' v w := Subtype.ext (e'.symm.map_add v w)
      map_smul' p v := Subtype.ext (e'.symm.map_smul p v) }

/-- The coefficient of the vector-valued comparison is the corresponding coordinate
coefficient. -/
@[simp]
theorem coeff_piLatticeHahnEquiv [Finite ι] (a : ℤ) (v : piLattice R ι a) (n : ℤ) (i : ι) :
    ((_root_.HahnModule.of R).symm (piLatticeHahnEquiv a v :
      _root_.HahnModule ℤ R (ι → R))).coeff n i = (v.val i).coeff n := by
  -- Read the subtype comparison on its underlying Hahn series before using the basis API.
  change ((_root_.HahnModule.of R).symm
    ((Pi.basisFun R ι).laurentSeriesEquiv.symm v.val)).coeff n i = _
  exact (Pi.basisFun_repr R ι _ i).symm.trans
    ((Pi.basisFun R ι).repr_coeff_laurentSeriesEquiv_symm v.val i n)

/-- For arbitrary endpoints, a coordinate jet is a vector-valued Hahn jet. -/
noncomputable def piLatticeQuotientHahnEquiv [Finite ι] (a b : ℤ) :
    (piLattice R ι a ⧸ (piLattice R ι b).comap (piLattice R ι a).subtype) ≃ₗ[R⟦X⟧]
      TauCeti.HahnModule.latticeQuotient R (ι → R) a b :=
  -- The Hahn jet carries the quotient action from its power-series lattices.
  (Submodule.Quotient.equiv _ _ (piLatticeHahnEquiv a) (by
    rw [Submodule.map_equiv_eq_comap_symm]
    ext f
    have hc (n : ℤ) (i : ι) :=
      coeff_piLatticeHahnEquiv a ((piLatticeHahnEquiv a).symm f) n i
    simp only [LinearEquiv.apply_symm_apply] at hc
    simp only [Submodule.mem_comap, Submodule.coe_subtype, mem_piLattice_iff,
      mem_lattice_iff, TauCeti.HahnModule.mem_powerSeriesLattice,
      TauCeti.HahnModule.mem_lattice_iff]
    constructor
    · intro h n hn
      funext i
      rw [hc]
      exact h i n hn
    · intro h i n hn
      exact (hc n i).symm.trans (congrFun (h n hn) i)) :
    (piLattice R ι a ⧸ (piLattice R ι b).comap (piLattice R ι a).subtype) ≃ₗ[R⟦X⟧]
      (TauCeti.HahnModule.powerSeriesLattice R (ι → R) a ⧸
        (TauCeti.HahnModule.powerSeriesLattice R (ι → R) b).comap
          (TauCeti.HahnModule.powerSeriesLattice R (ι → R) a).subtype)) ≪≫ₗ
    TauCeti.HahnModule.powerSeriesLatticeQuotientEquiv R (ι → R) a b

/-- The coordinate-to-Hahn comparison sends a coordinate representative to the corresponding
vector-valued representative. -/
@[simp]
theorem piLatticeQuotientHahnEquiv_mk [Finite ι] (a b : ℤ) (v : piLattice R ι a) :
    piLatticeQuotientHahnEquiv a b (Submodule.Quotient.mk v) =
      Submodule.Quotient.mk
        (⟨(piLatticeHahnEquiv a v).val,
          (TauCeti.HahnModule.mem_powerSeriesLattice R (ι → R)).mp
            (piLatticeHahnEquiv a v).property⟩ : TauCeti.HahnModule.lattice R (ι → R) a) := by
  simp [piLatticeQuotientHahnEquiv, Submodule.Quotient.equiv_apply]

variable (R ι) in
/-- The coefficients of a bounded coordinate jet. For finite `ι`, this is transported from
vector-valued Hahn jets; the coordinate construction also covers arbitrary `ι`. -/
noncomputable def boundedLatticeQuotientEquiv (N : ℕ) :
    boundedLatticeQuotient R ι N ≃ₗ[R] (ι → Finset.Ico (-N : ℤ) N → R) := by
  classical
  -- Finite charts use vector-valued Hahn jets. The coordinate construction also supports
  -- infinite coordinate types, for which a global Hahn-coordinate comparison does not exist.
  exact if h : Finite ι then
    have := h
    (piLatticeQuotientHahnEquiv (-N : ℤ) N).restrictScalars R ≪≫ₗ
      TauCeti.HahnModule.latticeQuotientEquiv R (ι → R) (-N) N ≪≫ₗ
        (LinearEquiv.curry R R _ _).symm ≪≫ₗ
          LinearEquiv.funCongrLeft R R (Equiv.prodComm _ _) ≪≫ₗ LinearEquiv.curry R R _ _
  else piLatticeQuotientEquiv R ι (-N : ℤ) N

/-- The coordinates of the class of `v` are the coefficients of the coordinates of `v`. -/
@[simp]
theorem boundedLatticeQuotientEquiv_mk (N : ℕ)
    (v : piLattice R ι (-N : ℤ)) (i : ι) (m : Finset.Ico (-N : ℤ) N) :
    boundedLatticeQuotientEquiv R ι N (Submodule.Quotient.mk v) i m =
      ((v : ι → R⸨X⸩) i).coeff m := by
  classical
  unfold boundedLatticeQuotientEquiv
  split_ifs with h
  · have := h
    simp
  · exact piLatticeQuotientEquiv_mk _ _ _ _ _

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
  rw [piLattice, pow_smul_mem_diagonalLattice_iff]
  convert hv using 1
  congr 1
  funext i
  push_cast
  ring

/-- `M_N` is killed by `X ^ (2 N)`. -/
theorem X_pow_smul_boundedLatticeQuotient (N : ℕ) (q : boundedLatticeQuotient R ι N) :
    (PowerSeries.X ^ (2 * N) : R⟦X⟧) • q = 0 := by
  classical
  by_cases h : Finite ι
  · have := h
    apply (piLatticeQuotientHahnEquiv (-N : ℤ) N).injective
    rw [map_smul, map_zero]
    exact TauCeti.HahnModule.X_pow_smul_latticeQuotient_eq_zero R (ι → R)
      (-N : ℤ) N (2 * N) (by omega) _
  · -- Preserve the arbitrary-coordinate result beyond the finite Hahn comparison.
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
image of `Λ`, that is `X ^ (-N) R⟦X⟧^ι / Λ`, is projective over `R`.
Its finiteness follows from that of `M_N`. -/
theorem fg_and_projective_iff_projective_quotient
    (h₀ : piLattice R ι (N : ℤ) ≤ Λ)
    (h₁ : Λ ≤ piLattice R ι (-N : ℤ)) :
    Λ.FG ∧ Module.Projective R⟦X⟧ Λ ↔
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
    exact Module.Flat.projective_of_finitePresentation
  · intro hproj
    have := hproj
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

/-- A lattice is bounded by `N` exactly when `X ^ N R⟦X⟧^ι ⊆ Λ ⊆ X ^ (-N) R⟦X⟧^ι`. -/
theorem isBounded_iff {N : ℕ} {Λ : ProjectiveLattice R⟦X⟧ R⸨X⸩ (ι → R⸨X⸩)} :
    Λ.IsBounded N ↔
      piLattice R ι (N : ℤ) ≤ Λ.toSubmodule ∧ Λ.toSubmodule ≤ piLattice R ι (-N : ℤ) :=
  Iff.rfl

variable [Finite ι] {N : ℕ}

/-- The lattice `jetPreimage N W` of an `X`-stable `R`-submodule `W ⊆ M_N` with finite projective
quotient. -/
private noncomputable def ofJet
    (W : {W : Submodule R (boundedLatticeQuotient R ι N) //
      (∀ w ∈ W, (PowerSeries.X : R⟦X⟧) • w ∈ W) ∧
        Module.Projective R (boundedLatticeQuotient R ι N ⧸ W)}) :
    ProjectiveLattice R⟦X⟧ R⸨X⸩ (ι → R⸨X⸩) :=
  have key := (fg_and_projective_iff_projective_quotient (le_jetPreimage
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
          Module.Projective R (boundedLatticeQuotient R ι N ⧸ W)} where
  toFun Λ := ⟨(jetSubmodule N Λ.val.toSubmodule).restrictScalars R,
    fun _ hw ↦ (jetSubmodule N Λ.val.toSubmodule).smul_mem _ hw,
    (fg_and_projective_iff_projective_quotient Λ.property.1 Λ.property.2).mp
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
        Module.Projective R (boundedLatticeQuotient R ι N ⧸ W)}) :
    ((boundedEquiv R ι N).symm W).val.toSubmodule =
      jetPreimage N (PowerSeries.submoduleOfXSMulMem (X_pow_smul_boundedLatticeQuotient N) W.val
        W.property.1) :=
  (rfl)

/-- The lattice of an `X`-stable submodule `W ⊆ M_N` is its preimage in `X ^ (-N) R⟦X⟧^ι`. -/
theorem mem_boundedEquiv_symm_apply_iff
    (W : {W : Submodule R (boundedLatticeQuotient R ι N) //
      (∀ w ∈ W, (PowerSeries.X : R⟦X⟧) • w ∈ W) ∧
        Module.Projective R (boundedLatticeQuotient R ι N ⧸ W)}) {v : ι → R⸨X⸩} :
    v ∈ ((boundedEquiv R ι N).symm W).val ↔
      ∃ hv : v ∈ piLattice R ι (-N : ℤ),
        (Submodule.Quotient.mk ⟨v, hv⟩ : boundedLatticeQuotient R ι N) ∈ W.val := by
  rw [← mem_toSubmodule, toSubmodule_boundedEquiv_symm_apply, mem_jetPreimage_iff]
  simp only [PowerSeries.mem_submoduleOfXSMulMem]

/-- The lattices bounded by `0` are the standard lattice only. -/
theorem isBounded_zero_iff {Λ : ProjectiveLattice R⟦X⟧ R⸨X⸩ (ι → R⸨X⸩)} :
    Λ.IsBounded 0 ↔ Λ = standard R⟦X⟧ R⸨X⸩ ι := by
  rw [isBounded_iff, ← toSubmodule_inj, toSubmodule_standard_eq_diagonalLattice_zero ι
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
  have hb' : (b : ℤ) ≤ (max a b : ℕ) := by omega
  have ha' : -((max a b : ℕ) : ℤ) ≤ 0 - a := by omega
  refine ⟨max a b, isBounded_iff.mpr ⟨fun v hv ↦ ?_, fun v hv ↦ ?_⟩⟩
  · -- `v = X ^ b • w` with `w = X ^ (-b) • v` in the standard lattice.
    set w : ι → R⸨X⸩ := (hX.unit ^ (-(b : ℤ))) • v
    have hwi (i : ι) : w i = single (-(b : ℤ)) 1 * v i := by
      simp only [w]
      rw [Pi.smul_apply, Units.smul_def, isUnit_unit_eq_unitX, val_unitX_zpow, smul_eq_mul]
    have hw : (PowerSeries.X ^ b : R⟦X⟧) • w = v := by
      funext i
      rw [Pi.smul_apply, Algebra.smul_def, hwi, ← mul_assoc, LaurentSeries.coe_algebraMap,
        ofPowerSeries_X_pow, single_mul_single]
      simp
    rw [← hw]
    refine hb w (mem_toSubmodule.mp (hstd ▸ ?_))
    have hv' := piLattice_antitone hb' hv
    rw [← hw, pow_smul_mem_diagonalLattice_iff] at hv'
    simpa using hv'
  · have hv' := (pow_smul_mem_diagonalLattice_iff hX (fun _ : ι ↦ (0 : ℤ)) a).mp
      (hstd ▸ mem_toSubmodule.mpr (ha v hv))
    exact piLattice_antitone ha' hv'

end TauCeti.ProjectiveLattice

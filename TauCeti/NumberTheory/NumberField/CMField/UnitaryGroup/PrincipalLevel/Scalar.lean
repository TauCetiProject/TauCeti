/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.CMField.UnitaryGroup.PrincipalLevel
public import TauCeti.RingTheory.DedekindDomain.FiniteAdeleRing.Residue.Level
import TauCeti.Algebra.Star.Unitary
import TauCeti.LinearAlgebra.Matrix.UnitaryGroup.Projective
import TauCeti.NumberTheory.NumberField.CMField.SplitIdele

/-!
# Scalar matrices at principal unitary levels

An integral norm-one scalar gives a central element of the integral finite adelic unitary
subgroup. Its principal congruence condition is the scalar congruence. At squarefree level a
scalar supported on a split pair can therefore have order exactly `Nm(w) - 1` modulo the
level, while being trivial modulo the auxiliary primes outside that pair.

The power test follows `New.Data.scalarFin_scalingGenerator_pow_mem_levelX_iff` in
`grh/src/New/UpperBound/Size/ShortColumns.lean` of lsernau/grh-lean (revision `72fead1`).
-/

public section

open IsDedekindDomain Matrix NumberField NumberField.IsCMField
open scoped NumberField.AdeleRing

namespace TauCeti

open FiniteAdeleRing

variable (E : Type*) [Field E] [NumberField E] [IsCMField E]
  (ι : Type*) [Fintype ι] [DecidableEq ι]

/-- Send an integral norm-one scalar to its scalar matrix in the finite adelic unitary group. -/
noncomputable def finiteAdelicUnitaryGroup.integralScalar :
    unitary (integralAdeles (𝓞 E) E) →* finiteAdelicUnitaryGroup E ι :=
  (integralAdelicUnitaryGroup E ι).subtype.comp
    ((integralAdelicUnitaryGroupEquiv E ι).toMonoidHom.comp
      (unitarySubgroupUnitsEquiv.symm.toMonoidHom.comp (UnitaryGroup.scalarHom ι _)))

variable {E ι}

/-- The integral scalar map is the usual scalar matrix over the finite adeles. -/
@[simp] theorem finiteAdelicUnitaryGroup.coe_integralScalar
    (z : unitary (integralAdeles (𝓞 E) E)) :
    (integralScalar E ι z : GL ι 𝔸ᶠ[E]) =
      integralGL E ι (GeneralLinearGroup.scalar ι (Unitary.toUnits z)) := by
  rw [integralScalar]
  simp only [MonoidHom.comp_apply, Subgroup.coe_subtype, MulEquiv.coe_toMonoidHom,
    coe_integralAdelicUnitaryGroupEquiv, coe_unitarySubgroupUnitsEquiv_symm_apply]
  congr 1
  apply Units.ext
  rw [Unitary.val_toUnits_apply, UnitaryGroup.coe_scalarHom, GeneralLinearGroup.coe_scalar,
    Unitary.val_toUnits_apply]

/-- The scalar matrix of an integral norm-one scalar belongs to the integral subgroup. -/
@[simp] theorem finiteAdelicUnitaryGroup.integralScalar_mem_integralAdelicUnitaryGroup
    (z : unitary (integralAdeles (𝓞 E) E)) :
    integralScalar E ι z ∈ integralAdelicUnitaryGroup E ι :=
  mem_integralAdelicUnitaryGroup_iff_mem_range_integralGL.2
    ⟨_, coe_integralScalar z |>.symm⟩

/-- An integral norm-one scalar commutes with every finite adelic unitary matrix. -/
theorem finiteAdelicUnitaryGroup.commute_integralScalar
    (z : unitary (integralAdeles (𝓞 E) E)) (g : finiteAdelicUnitaryGroup E ι) :
    Commute (integralScalar E ι z) g := by
  rw [commute_iff_eq]
  apply Subtype.ext
  simp only [Subgroup.coe_mul, coe_integralScalar, integralGL_def, GeneralLinearGroup.map_scalar]
  exact GeneralLinearGroup.scalar_commute _ _

/-- In positive rank, a scalar matrix belongs to a principal level exactly when the scalar
is congruent to one modulo the completed ideal. -/
theorem finiteAdelicUnitaryGroup.integralScalar_mem_principalUnitaryLevel_iff [Nonempty ι]
    (z : unitary (integralAdeles (𝓞 E) E)) (N : Ideal (𝓞 E)) :
    integralScalar E ι z ∈ principalUnitaryLevel E ι N ↔
      (z : integralAdeles (𝓞 E) E) - 1 ∈ completedIdeal E N := by
  rw [mem_principalUnitaryLevel_iff, coe_integralScalar]
  simp only [(integralGL_injective E ι).eq_iff, exists_eq_left]
  simp only [GeneralLinearGroup.coe_scalar, Unitary.val_toUnits_apply]
  refine ⟨fun h ↦ ?_, fun h i j ↦ ?_⟩
  · obtain ⟨i⟩ := ‹Nonempty ι›
    simpa using h i i
  · by_cases hij : i = j
    · subst j
      simpa using h
    · simp [Matrix.scalar_apply, hij]

/-- At squarefree principal level, a scalar matrix is in the level exactly when its scalar
reduces to one at each prime of the level. -/
theorem finiteAdelicUnitaryGroup.integralScalar_mem_principalUnitaryLevel_prod_iff [Nonempty ι]
    (z : unitary (integralAdeles (𝓞 E) E)) (S : Finset (HeightOneSpectrum (𝓞 E))) :
    integralScalar E ι z ∈ principalUnitaryLevel E ι (∏ v ∈ S, v.asIdeal) ↔
      ∀ v ∈ S, IsLocalRing.residue _ (v.integralAdelesProj (z : integralAdeles (𝓞 E) E)) = 1 := by
  rw [integralScalar_mem_principalUnitaryLevel_iff, mem_completedIdeal_prod_asIdeal_iff]
  simp only [map_sub, map_one, sub_eq_zero]

/-- A split place contributes a central scalar of exact order `Nm(w) - 1` modulo a squarefree
principal level that includes `w` but not its conjugate. The scalar is one away from the
conjugate pair, and its residue at `w` detects the same powers as the full level. In
particular, the latter test also applies to the diagonal entry in any specified row. -/
theorem _root_.IsDedekindDomain.HeightOneSpectrum.exists_integralScalar_pow_mem_principalLevel_iff
    [Nonempty ι] (w : HeightOneSpectrum (𝓞 E)) (hw : w.conjPlace ≠ w)
    (S : Finset (HeightOneSpectrum (𝓞 E))) (hS : w ∉ S) (hSc : w.conjPlace ∉ S) :
    ∃ z : unitary (integralAdeles (𝓞 E) E),
      finiteAdelicUnitaryGroup.integralScalar E ι z ∈
        principalUnitaryLevel E ι (∏ v ∈ S, v.asIdeal) ∧
      (∀ v, v ≠ w → v ≠ w.conjPlace → ((z : integralAdeles (𝓞 E) E) : 𝔸ᶠ[E]) v = 1) ∧
      ∀ i : ℕ,
        (IsLocalRing.residue _ (w.integralAdelesProj (↑(z ^ i) : integralAdeles (𝓞 E) E)) = 1 ↔
          Ideal.absNorm w.asIdeal - 1 ∣ i) ∧
        ((finiteAdelicUnitaryGroup.integralScalar E ι z) ^ i ∈
          principalUnitaryLevel E ι (∏ v ∈ S.cons w hS, v.asIdeal) ↔
          Ideal.absNorm w.asIdeal - 1 ∣ i) := by
  classical
  obtain ⟨x, hx, hsupp, horder⟩ := w.exists_unitary_integral_idele_residue_generator hw
  obtain ⟨u, hu⟩ : (x : (𝔸ᶠ[E])ˣ) ∈ (Units.map
      ((integralAdeles (𝓞 E) E).val.toRingHom : integralAdeles (𝓞 E) E →* 𝔸ᶠ[E])).range := by
    rw [range_units_map_val_eq_integralUnits]
    exact x.property
  have hunit : (u : integralAdeles (𝓞 E) E) ∈ unitary (integralAdeles (𝓞 E) E) := by
    rw [Units.unitary_eq, Submonoid.mem_comap, Units.coeHom_apply] at hx
    have he : ((u : integralAdeles (𝓞 E) E) : 𝔸ᶠ[E]) = (x : (𝔸ᶠ[E])ˣ) :=
      congrArg Units.val hu
    rw [Unitary.mem_iff] at hx ⊢
    refine ⟨Subtype.ext ?_, Subtype.ext ?_⟩
    · simpa only [Subalgebra.coe_mul, coe_star_integralAdeles, Subalgebra.coe_one, he] using hx.1
    · simpa only [Subalgebra.coe_mul, coe_star_integralAdeles, Subalgebra.coe_one, he] using hx.2
  let z : unitary (integralAdeles (𝓞 E) E) := ⟨u, hunit⟩
  have hres (v : HeightOneSpectrum (𝓞 E)) :
      IsLocalRing.residue _ (v.integralAdelesProj (z : integralAdeles (𝓞 E) E)) =
        (v.integralUnitsReduction x : IsLocalRing.ResidueField (v.adicCompletionIntegers E)) :=
    v.residue_integralAdelesProj_units u x hu
  have hresS (v : HeightOneSpectrum (𝓞 E)) (hv : v ∈ S) :
      v.integralUnitsReduction x = 1 := by
    rw [v.integralUnitsReduction_eq_of_unitsProj_eq x 1
      (hsupp v (ne_of_mem_of_not_mem hv hS) (ne_of_mem_of_not_mem hv hSc))]
    exact map_one _
  refine ⟨z, (finiteAdelicUnitaryGroup.integralScalar_mem_principalUnitaryLevel_prod_iff z S).2
    (fun v hv ↦ by rw [hres v, hresS v hv, Units.val_one]), ?_, fun i ↦ ?_⟩
  · intro v hv hvc
    refine (congrArg (fun a : (𝔸ᶠ[E])ˣ ↦ (a : 𝔸ᶠ[E]) v) hu).trans ?_
    simpa only [coe_unitsProj_apply, Units.val_one] using congrArg Units.val (hsupp v hv hvc)
  have hpow (v : HeightOneSpectrum (𝓞 E)) :
      IsLocalRing.residue _ (v.integralAdelesProj (↑(z ^ i) : integralAdeles (𝓞 E) E)) = 1 ↔
        v.integralUnitsReduction x ^ i = 1 := by
    simp only [SubmonoidClass.coe_pow, map_pow, hres]
    simpa only [Units.val_pow_eq_pow_val, Units.val_one] using
      (Units.ext_iff : v.integralUnitsReduction x ^ i = 1 ↔ _).symm
  have hw' := (hpow w).trans (orderOf_dvd_iff_pow_eq_one (x := w.integralUnitsReduction x)).symm
  rw [horder] at hw'
  refine ⟨hw', ?_⟩
  rw [← map_pow, finiteAdelicUnitaryGroup.integralScalar_mem_principalUnitaryLevel_prod_iff]
  rw [Finset.forall_mem_cons, hw']
  exact and_iff_left (fun v hv ↦ (hpow v).2 (by rw [hresS v hv, one_pow]))

end TauCeti

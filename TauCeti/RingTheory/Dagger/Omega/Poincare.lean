/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.ExteriorAlgebra.Contraction
public import TauCeti.RingTheory.Dagger.Omega.DeRham
public import TauCeti.RingTheory.Dagger.Poincare

/-!
# The Poincaré lemma on a dagger polydisc

Over a complete ultrametric normed field `K` of characteristic zero, the overconvergent de Rham
complex `0 → W → Ω¹_W → Ω²_W → ⋯` of the Monsky–Washnitzer algebra `W = K⟨X_σ⟩†` in finitely many
variables `σ` has cohomology `H⁰_dR(W/K) ≃ₗ[K] K` in degree zero and vanishes in every positive
degree `q + 1`: every closed `(q + 1)`-form is exact, `(deRhamComplex K W).ExactAt (q + 1)`, and
`deRhamCohomology K W (q + 1)` is subsingleton.

First we express `exteriorDeriv K W r` in coordinates with respect to the exterior-power basis
`(washnitzerBasis σ K).exteriorPower r` in arbitrary characteristic
(`washnitzerBasis_exteriorPower_repr_exteriorDeriv`). In degree zero this identifies `ker d` with
the series killed by all partial derivatives, hence with the scalars `K` in characteristic zero,
yielding `deRhamCohomologyZeroWashnitzerEquiv : K ≃ₗ[K] deRhamCohomology K W 0`. In degree one it
identifies closed `1`-forms with curl-free coordinate families (`∂ᵢ fⱼ = ∂ⱼ fᵢ`), recovering
potentials and unique normalized potentials from `washnitzerAlgebra.exists_pderiv_eq_iff` and
`washnitzerAlgebra.existsUnique_pderiv_eq`. In arbitrary positive degree `q + 1`, we prove exactness
by inducting across an enumeration of `σ`, successively eliminating the lowest active coordinate of
a closed form via `washnitzerAlgebra.primitive`.

Finally, over a complete ultrametric field `K` of prime characteristic `p`, we show that both halves
of the polydisc Poincaré lemma fail already in one variable `W = K⟨X₀⟩†`: `X₀ ^ p` is a nonconstant
element in `ker d`, and `X₀ ^ (p - 1) dX₀` is a closed `1`-form with no potential in `W`, so
`deRhamComplex K W` is not exact in degree `1` and `H¹_dR(W/K)` is nontrivial. This failure is why
`p`-adic cohomology of varieties in characteristic `p` lifts to dagger algebras in characteristic
zero (Monsky–Washnitzer and rigid cohomology).

## Main definitions

* `TauCeti.Dagger.Omega.closedFormsZeroWashnitzerEquiv`: `K ≃ₗ[K] closedForms K W 0` in
  characteristic zero.
* `TauCeti.Dagger.Omega.deRhamCohomologyZeroWashnitzerEquiv`:
  `K ≃ₗ[K] deRhamCohomology K W 0` in characteristic zero.

## Main results

* `TauCeti.Dagger.Omega.d_eq_zero_iff_mem_range_algebraMap`: in characteristic zero, `d K W f = 0`
  iff `f` is a scalar from `K`.
* `TauCeti.Dagger.Omega.washnitzerBasis_exteriorPower_repr_exteriorDeriv`: coordinate formula for
  `exteriorDeriv K W r` in the basis `(washnitzerBasis σ K).exteriorPower`.
* `TauCeti.Dagger.Omega.exteriorDeriv_one_eq_zero_iff`: a `1`-form on `W` is closed iff its
  coordinates satisfy `∂ᵢ fⱼ = ∂ⱼ fᵢ` (in any characteristic).
* `TauCeti.Dagger.Omega.exists_d_eq_iff_exteriorDeriv_one_eq_zero` and
  `TauCeti.Dagger.Omega.existsUnique_d_eq_of_exteriorDeriv_one_eq_zero`: exactness and unique
  normalized potentials for closed `1`-forms in characteristic zero.
* `TauCeti.Dagger.Omega.exists_exteriorDeriv_eq_of_exteriorDeriv_eq_zero`,
  `TauCeti.Dagger.Omega.exactForms_washnitzer_succ`,
  `TauCeti.Dagger.Omega.exactAt_deRhamComplex_washnitzer_succ`, and
  `TauCeti.Dagger.Omega.instSubsingletonDeRhamCohomologyWashnitzerSucc`: the Poincaré lemma on
  `W = K⟨X_σ⟩†` in all positive degrees `q + 1` in characteristic zero.
* `TauCeti.Dagger.Omega.d_X_pow_charP`,
  `TauCeti.Dagger.Omega.not_exists_d_eq_X_pow_sub_one_smul_d_X_charP`,
  `TauCeti.Dagger.Omega.not_exactAt_deRhamComplex_washnitzer_one_charP`, and
  `TauCeti.Dagger.Omega.nontrivial_deRhamCohomology_washnitzer_one_charP`: failure of the degree-`0`
  and degree-`1` Poincaré lemma on `K⟨X₀⟩†` in characteristic `p > 0`.

## References

* E. Grosse-Klönne, *Rigid analytic spaces with overconvergent structure sheaf*,
  J. reine angew. Math. 519 (2000), §1–§2.
* E. Grosse-Klönne, *Finiteness of de Rham cohomology in rigid analysis*,
  Duke Math. J. 113 (2002), §2, Lemma 2.1.
* K. S. Kedlaya, *Finiteness of rigid cohomology with coefficients*,
  Duke Math. J. 134 (2006), §2–§3.
-/

public section

open scoped BigOperators

namespace TauCeti.Dagger.Omega

open TauCeti.Dagger.washnitzerAlgebra

/-! ### Degree zero: kernel of `d` and `H⁰_dR(W/K) ≃ₗ[K] K` -/

section DegreeZero

variable {σ K : Type*} [Finite σ] [NormedField K] [IsUltrametricDist K] [CompleteSpace K]

/-- On `W = K⟨X_σ⟩†` in any characteristic, `d f = 0` iff all partial derivatives `∂f/∂Xᵢ`
vanish. -/
theorem d_eq_zero_iff_forall_pderiv_eq_zero (f : washnitzerAlgebra σ K) :
    d K (washnitzerAlgebra σ K) f = 0 ↔ ∀ i, pderiv σ K i f = 0 := by
  rw [← (washnitzerBasis σ K).repr.map_eq_zero_iff, Finsupp.ext_iff]
  simp [washnitzerBasis_repr_d]

variable [CharZero K]

/-- Over a complete ultrametric field of characteristic zero, `d f = 0` in `Ω¹_{W/K}` iff `f` lies
in the image of `algebraMap K W`. -/
theorem d_eq_zero_iff_mem_range_algebraMap (f : washnitzerAlgebra σ K) :
    d K (washnitzerAlgebra σ K) f = 0 ↔
      f ∈ Set.range (algebraMap K (washnitzerAlgebra σ K)) := by
  rw [d_eq_zero_iff_forall_pderiv_eq_zero, forall_pderiv_eq_zero_iff]
  rfl

/-- Over a complete ultrametric field of characteristic zero, `d f = 0` iff `f` equals its constant
coefficient viewed in `W`. -/
theorem d_eq_zero_iff_eq_algebraMap_constantCoeff (f : washnitzerAlgebra σ K) :
    d K (washnitzerAlgebra σ K) f = 0 ↔
      f = algebraMap K (washnitzerAlgebra σ K) (MvPowerSeries.constantCoeff f.1) := by
  rw [d_eq_zero_iff_mem_range_algebraMap]
  refine ⟨?_, fun h ↦ ⟨MvPowerSeries.constantCoeff f.1, h.symm⟩⟩
  rintro ⟨c, rfl⟩
  simp [MvPowerSeries.algebraMap_apply]

omit [CharZero K] in
private theorem algebraMap_zeroEquiv_symm_mem_closedForms (c : K) :
    (exteriorPower.zeroEquiv (washnitzerAlgebra σ K)
        (Omega K (washnitzerAlgebra σ K))).symm
        (algebraMap K (washnitzerAlgebra σ K) c) ∈
      closedForms K (washnitzerAlgebra σ K) 0 := by
  rw [mem_closedForms, exteriorDeriv_zero_symm, (d K (washnitzerAlgebra σ K)).map_algebraMap,
    map_zero]

private theorem closedForms_zero_eq_constantCoeff
    (ω : closedForms K (washnitzerAlgebra σ K) 0) :
    (exteriorPower.zeroEquiv (washnitzerAlgebra σ K)
        (Omega K (washnitzerAlgebra σ K))).symm
        (algebraMap K (washnitzerAlgebra σ K)
          (MvPowerSeries.constantCoeff
            (exteriorPower.zeroEquiv (washnitzerAlgebra σ K)
              (Omega K (washnitzerAlgebra σ K)) ω.1).1)) =
      ω.1 := by
  set f := exteriorPower.zeroEquiv (washnitzerAlgebra σ K)
    (Omega K (washnitzerAlgebra σ K)) ω.1
  have hω : ω.1 = (exteriorPower.zeroEquiv (washnitzerAlgebra σ K)
      (Omega K (washnitzerAlgebra σ K))).symm f := by
    simp [f]
  have hdf : d K (washnitzerAlgebra σ K) f = 0 := by
    have h0 := (mem_closedForms K (washnitzerAlgebra σ K) ω.1).mp ω.2
    rw [hω, exteriorDeriv_zero_symm] at h0
    exact (exteriorPower.oneEquiv (washnitzerAlgebra σ K) _).symm.injective
      (by simpa using h0)
  rw [← (d_eq_zero_iff_eq_algebraMap_constantCoeff f).mp hdf, ← hω]

variable (σ K) in
/-- In characteristic zero, closed `0`-forms on `W = K⟨X_σ⟩†` are `K`-linearly equivalent to `K`. -/
noncomputable def closedFormsZeroWashnitzerEquiv :
    K ≃ₗ[K] closedForms K (washnitzerAlgebra σ K) 0 where
  toFun c :=
    ⟨(exteriorPower.zeroEquiv (washnitzerAlgebra σ K) _).symm
        (algebraMap K (washnitzerAlgebra σ K) c),
      algebraMap_zeroEquiv_symm_mem_closedForms c⟩
  map_add' a b := Subtype.ext (by simp [map_add])
  map_smul' a b := Subtype.ext <| by
    simp only [smul_eq_mul, RingHom.id_apply, SetLike.val_smul]
    rw [map_mul, ← Algebra.smul_def,
      ← IsScalarTower.algebraMap_smul (washnitzerAlgebra σ K) a,
      LinearEquiv.map_smul, IsScalarTower.algebraMap_smul]
  invFun ω :=
    MvPowerSeries.constantCoeff
      (exteriorPower.zeroEquiv (washnitzerAlgebra σ K) _ ω.1).1
  left_inv c := by
    simp [MvPowerSeries.algebraMap_apply]
  right_inv ω := Subtype.ext (closedForms_zero_eq_constantCoeff ω)

@[simp]
theorem coe_closedFormsZeroWashnitzerEquiv_apply (c : K) :
    (closedFormsZeroWashnitzerEquiv σ K c).1 =
      (exteriorPower.zeroEquiv (washnitzerAlgebra σ K) _).symm
        (algebraMap K (washnitzerAlgebra σ K) c) :=
  (rfl)

@[simp]
theorem closedFormsZeroWashnitzerEquiv_symm_apply
    (ω : closedForms K (washnitzerAlgebra σ K) 0) :
    (closedFormsZeroWashnitzerEquiv σ K).symm ω =
      MvPowerSeries.constantCoeff
        (exteriorPower.zeroEquiv (washnitzerAlgebra σ K) _ ω.1).1 :=
  (rfl)

variable (σ K) in
/-- **Degree-zero overconvergent de Rham cohomology of a dagger polydisc.** In characteristic zero,
`H⁰_dR(K⟨X_σ⟩† / K)` is canonically `K`-linearly equivalent to `K`. -/
noncomputable def deRhamCohomologyZeroWashnitzerEquiv :
    K ≃ₗ[K] deRhamCohomology K (washnitzerAlgebra σ K) 0 :=
  (closedFormsZeroWashnitzerEquiv σ K).trans
    (deRhamCohomology.zeroEquivClosedForms K (washnitzerAlgebra σ K))

@[simp]
theorem deRhamCohomologyZeroWashnitzerEquiv_apply (c : K) :
    deRhamCohomologyZeroWashnitzerEquiv σ K c =
      deRhamCohomology.mk K (washnitzerAlgebra σ K) 0
        (closedFormsZeroWashnitzerEquiv σ K c) := by
  simp [deRhamCohomologyZeroWashnitzerEquiv]

@[simp]
theorem deRhamCohomologyZeroWashnitzerEquiv_symm_mk
    (ω : closedForms K (washnitzerAlgebra σ K) 0) :
    (deRhamCohomologyZeroWashnitzerEquiv σ K).symm
        (deRhamCohomology.mk K (washnitzerAlgebra σ K) 0 ω) =
      MvPowerSeries.constantCoeff
        (exteriorPower.zeroEquiv (washnitzerAlgebra σ K) _ ω.1).1 := by
  rw [← deRhamCohomology.zeroEquivClosedForms_apply, deRhamCohomologyZeroWashnitzerEquiv,
    LinearEquiv.trans_symm, LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply]
  rfl

end DegreeZero

/-! ### Coordinate formula for `exteriorDeriv` and exactness in degree one -/

section CoordinateFormula

variable {σ K : Type*} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]

private theorem exteriorAlgebra_repr_coe_eq [Finite σ] [LinearOrder σ]
    (r : ℕ) (ω : ⋀[washnitzerAlgebra σ K]^r (Omega K (washnitzerAlgebra σ K)))
    (u : Set.powersetCard σ r) :
    (washnitzerBasis σ K).ExteriorAlgebra.repr ω.1 u.1 =
      ((washnitzerBasis σ K).exteriorPower r).repr ω u := by
  classical
  let : Fintype σ := Fintype.ofFinite σ
  let : Fintype (Set.powersetCard σ r) := Fintype.ofFinite _
  rw [← Module.Basis.coord_apply]
  conv_lhs => rw [← ((washnitzerBasis σ K).exteriorPower r).sum_repr ω]
  simp only [Submodule.coe_sum, Submodule.coe_smul, ← ExteriorAlgebra.basis_eq_coe_basis,
    map_sum, map_smul, Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply,
    smul_eq_mul, mul_boole]
  rw [Finset.sum_eq_single u]
  · simp
  · intro t _ htu
    have hne : t.1 ≠ u.1 := Subtype.ext_iff.not.mp htu
    simp [hne]
  · intro hu
    exact absurd (Finset.mem_univ u) hu

/-- Basis monomials `dX_{i₀} ∧ ⋯ ∧ dX_{i_{r-1}}` of `(washnitzerBasis σ K).exteriorPower r` are
killed by `exteriorDeriv` in every characteristic. -/
theorem exteriorDeriv_washnitzerBasis_exteriorPower [Finite σ] [LinearOrder σ] (r : ℕ)
    (t : Set.powersetCard σ r) :
    exteriorDeriv K (washnitzerAlgebra σ K) r
        ((washnitzerBasis σ K).exteriorPower r t) = 0 := by
  rw [exteriorPower.basis_apply, exteriorPower.ιMulti_family]
  have hcomp :
      (washnitzerBasis σ K) ∘ (Set.powersetCard.ofFinEmbEquiv.symm t) =
        (d K (washnitzerAlgebra σ K)) ∘
          (fun i ↦ X σ K (Set.powersetCard.ofFinEmbEquiv.symm t i)) := by
    ext i
    simp [washnitzerBasis_apply]
  rw [hcomp]
  exact exteriorDeriv_ιMulti_comp_d _

private theorem washnitzerBasis_exteriorPower_repr_exteriorDeriv_smul
    [Fintype σ] [LinearOrder σ] (r : ℕ) (t : Set.powersetCard σ r)
    (c : washnitzerAlgebra σ K) (u : Set.powersetCard σ (r + 1)) :
    ((washnitzerBasis σ K).exteriorPower (r + 1)).repr
        (exteriorDeriv K (washnitzerAlgebra σ K) r
          (c • (washnitzerBasis σ K).exteriorPower r t)) u =
      ∑ k : σ,
        if k ∉ t.1 ∧ insert k t.1 = u.1 then
          TauCeti.ExteriorAlgebra.basisEraseSign k u.1 • pderiv σ K k c
        else 0 := by
  rw [← exteriorAlgebra_repr_coe_eq, ← Module.Basis.coord_apply,
    exteriorDeriv_smul, exteriorDeriv_washnitzerBasis_exteriorPower, smul_zero, add_zero,
    TauCeti.ExteriorAlgebra.coe_wedgeLeft_apply, ← ExteriorAlgebra.basis_eq_coe_basis]
  conv_lhs =>
    rw [← (washnitzerBasis σ K).sum_repr (d K (washnitzerAlgebra σ K) c)]
  rw [map_sum, Finset.sum_mul, map_sum]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  rw [washnitzerBasis_repr_d, LinearMap.map_smul, smul_mul_assoc, LinearMap.map_smul,
    TauCeti.ExteriorAlgebra.ι_mul_basis]
  by_cases hkt : k ∈ t.1
  · have hnot : ¬(k ∉ t.1 ∧ insert k t.1 = u.1) := fun h ↦ h.1 hkt
    rw [ite_eq_left hkt, ite_eq_right hnot,
      ((washnitzerBasis σ K).ExteriorAlgebra.coord u.1).map_zero, smul_zero]
  · rw [ite_eq_right hkt]
    by_cases hins : insert k t.1 = u.1
    · have hcond : k ∉ t.1 ∧ insert k t.1 = u.1 := ⟨hkt, hins⟩
      rw [ite_eq_left hcond, hins, Units.smul_def, Units.smul_def,
        ← Int.cast_smul_eq_zsmul (washnitzerAlgebra σ K),
        ← Int.cast_smul_eq_zsmul (washnitzerAlgebra σ K),
        LinearMap.map_smul, Module.Basis.coord_apply, Module.Basis.repr_self,
        Finsupp.single_eq_same, smul_eq_mul, smul_eq_mul, smul_eq_mul, mul_one, mul_comm]
    · have hnot : ¬(k ∉ t.1 ∧ insert k t.1 = u.1) := fun h ↦ hins h.2
      rw [ite_eq_right hnot, Units.smul_def,
        ← Int.cast_smul_eq_zsmul (washnitzerAlgebra σ K),
        LinearMap.map_smul, Module.Basis.coord_apply, Module.Basis.repr_self,
        Finsupp.single_eq_of_ne' hins, smul_zero, smul_zero]

/-- **Coordinate formula for the overconvergent exterior derivative** in the basis
`(washnitzerBasis σ K).exteriorPower` (valid in any characteristic). -/
theorem washnitzerBasis_exteriorPower_repr_exteriorDeriv [Finite σ] [LinearOrder σ]
    (r : ℕ) (ω : ⋀[washnitzerAlgebra σ K]^r (Omega K (washnitzerAlgebra σ K)))
    (u : Set.powersetCard σ (r + 1)) :
    ((washnitzerBasis σ K).exteriorPower (r + 1)).repr
        (exteriorDeriv K (washnitzerAlgebra σ K) r ω) u =
      ∑ k ∈ u.1.attach,
        TauCeti.ExteriorAlgebra.basisEraseSign k.1 u.1 •
          pderiv σ K k.1 (((washnitzerBasis σ K).exteriorPower r).repr ω
            (Set.powersetCard.ofCard (s := u.1.erase k.1) (by
              have h1 := Finset.card_erase_add_one k.2
              have h2 := Set.powersetCard.card_eq u
              omega))) := by
  let : Fintype σ := Fintype.ofFinite σ
  let : Fintype (Set.powersetCard σ r) := Fintype.ofFinite _
  rw [← Module.Basis.coord_apply]
  conv_lhs => rw [← ((washnitzerBasis σ K).exteriorPower r).sum_repr ω]
  rw [map_sum, map_sum,
    Finset.sum_congr rfl fun t _ ↦ by
      rw [Module.Basis.coord_apply, washnitzerBasis_exteriorPower_repr_exteriorDeriv_smul],
    Finset.sum_comm]
  have houter (k : σ) :
      (∑ t : Set.powersetCard σ r,
          if k ∉ t.1 ∧ insert k t.1 = u.1 then
            TauCeti.ExteriorAlgebra.basisEraseSign k u.1 •
              pderiv σ K k (((washnitzerBasis σ K).exteriorPower r).repr ω t)
          else 0) =
        if hk : k ∈ u.1 then
          TauCeti.ExteriorAlgebra.basisEraseSign k u.1 •
            pderiv σ K k (((washnitzerBasis σ K).exteriorPower r).repr ω
              (Set.powersetCard.ofCard (s := u.1.erase k) (by
                have h1 := Finset.card_erase_add_one hk
                have h2 := Set.powersetCard.card_eq u
                omega)))
        else 0 := by
    by_cases hk : k ∈ u.1
    · rw [dite_eq_left hk]
      let tk : Set.powersetCard σ r := Set.powersetCard.ofCard (s := u.1.erase k) (by
        have h1 := Finset.card_erase_add_one hk
        have h2 := Set.powersetCard.card_eq u
        omega)
      rw [Finset.sum_eq_single tk]
      · have hcond : k ∉ tk.1 ∧ insert k tk.1 = u.1 :=
          ⟨Finset.notMem_erase k u.1, Finset.insert_erase hk⟩
        rw [ite_eq_left hcond]
      · intro t _ hne
        have hnot : ¬(k ∉ t.1 ∧ insert k t.1 = u.1) := by
          rintro ⟨hkt, hins⟩
          apply hne
          apply Subtype.ext
          change t.1 = u.1.erase k
          rw [← hins, Finset.erase_insert hkt]
        rw [ite_eq_right hnot]
      · exact fun hmem ↦ absurd (Finset.mem_univ tk) hmem
    · rw [dite_eq_right hk]
      refine Finset.sum_eq_zero fun t _ ↦ ?_
      have hnot : ¬(k ∉ t.1 ∧ insert k t.1 = u.1) := by
        rintro ⟨_, hins⟩
        exact hk (hins ▸ Finset.mem_insert_self k t.1)
      rw [ite_eq_right hnot]
  rw [Finset.sum_congr rfl fun k _ ↦ houter k,
    ← Finset.sum_subset (Finset.subset_univ u.1) fun k _ hku ↦ dite_eq_right hku,
    ← Finset.sum_attach u.1 fun k ↦
      if hk : k ∈ u.1 then
        TauCeti.ExteriorAlgebra.basisEraseSign k u.1 •
          pderiv σ K k (((washnitzerBasis σ K).exteriorPower r).repr ω
            (Set.powersetCard.ofCard (s := u.1.erase k) (by
              have h1 := Finset.card_erase_add_one hk
              have h2 := Set.powersetCard.card_eq u
              omega)))
      else 0]
  exact Finset.sum_congr rfl fun k _ ↦ dite_eq_left k.2

private theorem washnitzerBasis_exteriorPower_one_repr [Finite σ] [LinearOrder σ]
    (ω : Omega K (washnitzerAlgebra σ K)) (k : σ) :
    ((washnitzerBasis σ K).exteriorPower 1).repr
        ((exteriorPower.oneEquiv (washnitzerAlgebra σ K) _).symm ω)
        (Set.powersetCard.ofCard (Finset.card_singleton k)) =
      (washnitzerBasis σ K).repr ω k := by
  let : Fintype σ := Fintype.ofFinite σ
  have hcoe :
      (((exteriorPower.oneEquiv (washnitzerAlgebra σ K)
          (Omega K (washnitzerAlgebra σ K))).symm ω) :
        ExteriorAlgebra (washnitzerAlgebra σ K) (Omega K (washnitzerAlgebra σ K))) =
      ExteriorAlgebra.ι (washnitzerAlgebra σ K) ω := by
    simp [exteriorPower.oneEquiv_symm_apply, ExteriorAlgebra.ιMulti_succ_apply]
  rw [← exteriorAlgebra_repr_coe_eq, hcoe, ← Module.Basis.coord_apply]
  conv_lhs => rw [← (washnitzerBasis σ K).sum_repr ω]
  simp only [Set.powersetCard.ofCard, map_sum, LinearMap.map_smul,
    ← TauCeti.ExteriorAlgebra.basis_singleton (washnitzerBasis σ K),
    Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply, Finset.singleton_inj,
    smul_eq_mul, mul_boole, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]

/-- **Curl-free characterization of closed `1`-forms** on `W = K⟨X_σ⟩†` (valid in any
characteristic): a `1`-form `ω = ∑ᵢ fᵢ dXᵢ` satisfies `dω = 0` in `Ω²_{W/K}` if and only if
`∂ᵢ fⱼ = ∂ⱼ fᵢ` for all `i, j : σ`. -/
theorem exteriorDeriv_one_eq_zero_iff [Finite σ] (ω : Omega K (washnitzerAlgebra σ K)) :
    exteriorDeriv K (washnitzerAlgebra σ K) 1
        ((exteriorPower.oneEquiv (washnitzerAlgebra σ K) _).symm ω) = 0 ↔
      ∀ i j, pderiv σ K i ((washnitzerBasis σ K).repr ω j) =
        pderiv σ K j ((washnitzerBasis σ K).repr ω i) := by
  obtain ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin σ
  let : LinearOrder σ := LinearOrder.lift' e e.injective
  let : Fintype σ := Fintype.ofFinite σ
  let b := washnitzerBasis σ K
  let η := (exteriorPower.oneEquiv (washnitzerAlgebra σ K) _).symm ω
  have hpair {i j : σ} (hij : i < j) :
      (b.exteriorPower 2).repr (exteriorDeriv K (washnitzerAlgebra σ K) 1 η)
          (Set.powersetCard.ofCard (Finset.card_pair hij.ne)) =
        pderiv σ K i (b.repr ω j) - pderiv σ K j (b.repr ω i) := by
    rw [washnitzerBasis_exteriorPower_repr_exteriorDeriv]
    have hatt : (Set.powersetCard.ofCard (Finset.card_pair hij.ne)).1.attach =
        {⟨i, by simp [Set.powersetCard.ofCard]⟩, ⟨j, by simp [Set.powersetCard.ofCard]⟩} := by
      ext ⟨x, hx⟩
      simp only [Finset.mem_attach, Finset.mem_insert, Finset.mem_singleton, Subtype.ext_iff,
        true_iff]
      simpa [Set.powersetCard.ofCard] using hx
    have hne_sub :
        (⟨i, by simp [Set.powersetCard.ofCard]⟩ :
          {x // x ∈ (Set.powersetCard.ofCard (Finset.card_pair hij.ne)).1}) ≠
        ⟨j, by simp [Set.powersetCard.ofCard]⟩ :=
      fun h ↦ hij.ne (congrArg Subtype.val h)
    rw [hatt, Finset.sum_pair hne_sub]
    have herase_i (hc : ((Set.powersetCard.ofCard (Finset.card_pair hij.ne)).1.erase i).card = 1) :
        Set.powersetCard.ofCard hc = Set.powersetCard.ofCard (Finset.card_singleton j) := by
      apply Subtype.ext
      simp [Set.powersetCard.ofCard, hij.ne]
    have herase_j (hc : ((Set.powersetCard.ofCard (Finset.card_pair hij.ne)).1.erase j).card = 1) :
        Set.powersetCard.ofCard hc = Set.powersetCard.ofCard (Finset.card_singleton i) := by
      apply Subtype.ext
      simp only [Set.powersetCard.ofCard]
      rw [Finset.pair_comm i j]
      simp [hij.ne']
    have hfilt_i : ((Set.powersetCard.ofCard (Finset.card_pair hij.ne)).1.filter fun x ↦ x < i) =
        ∅ := by
      ext x
      simp only [Set.powersetCard.ofCard, Finset.mem_filter, Finset.mem_insert,
        Finset.mem_singleton, Finset.notMem_empty, iff_false, not_and]
      rintro (hxi | hxj)
      · rw [hxi]; exact lt_irrefl i
      · rw [hxj]; exact asymm hij
    have hfilt_j : ((Set.powersetCard.ofCard (Finset.card_pair hij.ne)).1.filter fun x ↦ x < j) =
        {i} := by
      ext x
      simp only [Set.powersetCard.ofCard, Finset.mem_filter, Finset.mem_insert,
        Finset.mem_singleton]
      refine ⟨?_, ?_⟩
      · rintro ⟨hxi | hxj, hlt⟩
        · exact hxi
        · rw [hxj] at hlt; exact absurd hlt (lt_irrefl j)
      · rintro rfl
        exact ⟨Or.inl rfl, hij⟩
    rw [herase_i, herase_j, washnitzerBasis_exteriorPower_one_repr,
      washnitzerBasis_exteriorPower_one_repr,
      TauCeti.ExteriorAlgebra.basisEraseSign_eq_neg_one_pow_card_filter_lt,
      TauCeti.ExteriorAlgebra.basisEraseSign_eq_neg_one_pow_card_filter_lt,
      hfilt_i, hfilt_j]
    simp [sub_eq_add_neg]
    rfl
  rw [← (b.exteriorPower 2).repr.map_eq_zero_iff, Finsupp.ext_iff]
  constructor
  · intro h i j
    rcases lt_trichotomy i j with hij | rfl | hji
    · have h0 := h (Set.powersetCard.ofCard (Finset.card_pair hij.ne))
      rw [hpair hij, Finsupp.coe_zero, Pi.zero_apply] at h0
      exact sub_eq_zero.mp h0
    · rfl
    · have h0 := h (Set.powersetCard.ofCard (Finset.card_pair hji.ne))
      rw [hpair hji, Finsupp.coe_zero, Pi.zero_apply] at h0
      exact (sub_eq_zero.mp h0).symm
  · intro h u
    obtain ⟨i, j, hij, hu⟩ := Finset.card_eq_two.mp (Set.powersetCard.card_eq u)
    rcases lt_or_gt_of_ne hij with hlt | hgt
    · have hu' : u = Set.powersetCard.ofCard (Finset.card_pair hlt.ne) := Subtype.ext hu
      rw [hu', hpair hlt, h i j, sub_self, Finsupp.coe_zero, Pi.zero_apply]
    · have hu' : u = Set.powersetCard.ofCard (Finset.card_pair hgt.ne) :=
        Subtype.ext (hu.trans (Finset.pair_comm i j))
      rw [hu', hpair hgt, h j i, sub_self, Finsupp.coe_zero, Pi.zero_apply]

/-- **Degree-one Poincaré lemma on `W = K⟨X_σ⟩†` in characteristic zero**: a `1`-form `ω ∈ Ω¹_{W/K}`
is of the form `d g` for some `g ∈ W` if and only if `dω = 0`. -/
theorem exists_d_eq_iff_exteriorDeriv_one_eq_zero [Finite σ] [CharZero K]
    (ω : Omega K (washnitzerAlgebra σ K)) :
    (∃ g : washnitzerAlgebra σ K, d K (washnitzerAlgebra σ K) g = ω) ↔
      exteriorDeriv K (washnitzerAlgebra σ K) 1
        ((exteriorPower.oneEquiv (washnitzerAlgebra σ K) _).symm ω) = 0 := by
  rw [exteriorDeriv_one_eq_zero_iff, ← exists_pderiv_eq_iff]
  refine exists_congr fun g ↦ ?_
  rw [← (washnitzerBasis σ K).repr.injective.eq_iff, Finsupp.ext_iff]
  simp [washnitzerBasis_repr_d]

/-- **Unique normalized potential of a closed `1`-form**: over a complete ultrametric field `K` of
characteristic zero, every closed `1`-form `ω ∈ Ω¹_{W/K}` on `W = K⟨X_σ⟩†` admits a unique potential
`g ∈ W` (`d g = ω`) with prescribed constant coefficient `c ∈ K`. -/
theorem existsUnique_d_eq_of_exteriorDeriv_one_eq_zero [Finite σ] [CharZero K]
    {ω : Omega K (washnitzerAlgebra σ K)}
    (hω : exteriorDeriv K (washnitzerAlgebra σ K) 1
      ((exteriorPower.oneEquiv (washnitzerAlgebra σ K) _).symm ω) = 0)
    (c : K) :
    ∃! g : washnitzerAlgebra σ K,
      d K (washnitzerAlgebra σ K) g = ω ∧ MvPowerSeries.constantCoeff g.1 = c := by
  have hcurl := (exteriorDeriv_one_eq_zero_iff ω).mp hω
  have hex := existsUnique_pderiv_eq (fun i ↦ (washnitzerBasis σ K).repr ω i) hcurl c
  have hiff (g : washnitzerAlgebra σ K) :
      d K (washnitzerAlgebra σ K) g = ω ↔
        ∀ i, pderiv σ K i g = (washnitzerBasis σ K).repr ω i := by
    rw [← (washnitzerBasis σ K).repr.injective.eq_iff, Finsupp.ext_iff]
    simp [washnitzerBasis_repr_d]
  simpa only [hiff] using hex

end CoordinateFormula

/-! ### The Poincaré lemma in all positive degrees -/

section AllPositiveDegrees

variable {σ K : Type*} [Finite σ] [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  [CharZero K]

omit [Finite σ] [CompleteSpace K] [CharZero K] in
private theorem units_smul_zero_washnitzer (u : ℤˣ) :
    u • (0 : washnitzerAlgebra σ K) = 0 := by
  rw [Units.smul_def, zsmul_zero]

omit [Finite σ] [CompleteSpace K] [CharZero K] in
private theorem units_one_smul_washnitzer (x : washnitzerAlgebra σ K) :
    (1 : ℤˣ) • x = x :=
  one_smul ℤˣ x

omit [Finite σ] [CompleteSpace K] [CharZero K] in
private theorem units_smul_eq_zero_washnitzer {u : ℤˣ} {x : washnitzerAlgebra σ K}
    (h : u • x = 0) : x = 0 := by
  have hinv := congrArg (fun y ↦ u⁻¹ • y) h
  rwa [inv_smul_smul, units_smul_zero_washnitzer] at hinv

omit [CharZero K] in
private theorem pderiv_repr_eq_zero_of_lt [LinearOrder σ] (q : ℕ) {i₀ k₀ : σ}
    {ω : ⋀[washnitzerAlgebra σ K]^(q + 1) (Omega K (washnitzerAlgebra σ K))}
    (hdω : exteriorDeriv K (washnitzerAlgebra σ K) (q + 1) ω = 0)
    (hsupp : ∀ s : Set.powersetCard σ (q + 1),
      ((washnitzerBasis σ K).exteriorPower (q + 1)).repr ω s ≠ 0 → ∀ i ∈ s.1, i₀ ≤ i)
    (hk₀ : k₀ < i₀) (s : Set.powersetCard σ (q + 1)) (hkn_s : k₀ ∉ s.1) :
    pderiv σ K k₀ (((washnitzerBasis σ K).exteriorPower (q + 1)).repr ω s) = 0 := by
  let w : Set.powersetCard σ (q + 2) :=
    Set.powersetCard.ofCard (s := insert k₀ s.1)
      (by rw [Finset.card_insert_of_notMem hkn_s, Set.powersetCard.card_eq s])
  have hdw :
      ((washnitzerBasis σ K).exteriorPower (q + 2)).repr
        (exteriorDeriv K (washnitzerAlgebra σ K) (q + 1) ω) w = 0 := by
    rw [hdω, LinearEquiv.map_zero, Finsupp.coe_zero, Pi.zero_apply]
  rw [washnitzerBasis_exteriorPower_repr_exteriorDeriv] at hdw
  have hkw : k₀ ∈ w.1 := Finset.mem_insert_self k₀ s.1
  rw [Finset.sum_eq_single ⟨k₀, hkw⟩] at hdw
  · have herase_w :
        (Set.powersetCard.ofCard (s := w.1.erase k₀) (by
          have h1 := Finset.card_erase_add_one hkw
          have h2 := Set.powersetCard.card_eq w
          omega) : Set.powersetCard σ (q + 1)) = s :=
      Subtype.ext (Finset.erase_insert hkn_s)
    rw [herase_w] at hdw
    exact units_smul_eq_zero_washnitzer hdw
  · intro l _ hlk
    have hkl : k₀ ≠ l.1 := fun heq ↦ hlk (Subtype.ext heq.symm)
    have hkw_erase : k₀ ∈ w.1.erase l.1 := Finset.mem_erase.mpr ⟨hkl, hkw⟩
    suffices hl0 : ∀ t' : Set.powersetCard σ (q + 1),
        t'.1 = w.1.erase l.1 →
        TauCeti.ExteriorAlgebra.basisEraseSign l.1 w.1 •
          pderiv σ K l.1 (((washnitzerBasis σ K).exteriorPower (q + 1)).repr ω t') = 0 by
      refine hl0 _ ?_
      rfl
    intro t' ht'_val
    have hzero_l : ((washnitzerBasis σ K).exteriorPower (q + 1)).repr ω t' = 0 := by
      by_contra hne
      exact not_le_of_gt hk₀ (hsupp t' hne k₀ (ht'_val.symm ▸ hkw_erase))
    rw [hzero_l, (pderiv σ K l.1).map_zero, units_smul_zero_washnitzer]
  · intro hmem
    exact absurd (Finset.mem_attach w.1 ⟨k₀, hkw⟩) hmem

private theorem poincare_caseB [LinearOrder σ] (q : ℕ) (i₀ : σ)
    (ω : ⋀[washnitzerAlgebra σ K]^(q + 1) (Omega K (washnitzerAlgebra σ K)))
    (η₀ : ⋀[washnitzerAlgebra σ K]^q (Omega K (washnitzerAlgebra σ K)))
    (g : Set.powersetCard σ q → washnitzerAlgebra σ K)
    (hrepr_η₀ : ∀ t, ((washnitzerBasis σ K).exteriorPower q).repr η₀ t = g t)
    (hg_ofCard : ∀ {s₀ : Finset σ} (hs₀ : s₀.card = q),
      g (Set.powersetCard.ofCard hs₀) =
        if hgt : ∀ j ∈ s₀, i₀ < j then
          primitive σ K i₀ (((washnitzerBasis σ K).exteriorPower (q + 1)).repr ω
            (Set.powersetCard.ofCard (s := insert i₀ s₀)
              (by
                have hnot : i₀ ∉ s₀ := fun hi₀ ↦ lt_irrefl i₀ (hgt i₀ hi₀)
                rw [Finset.card_insert_of_notMem hnot, hs₀])))
        else 0)
    (u : Set.powersetCard σ (q + 1)) (hi₀u : i₀ ∈ u.1)
    (hex_lt : ∀ j ∈ u.1, i₀ ≤ j) :
    ((washnitzerBasis σ K).exteriorPower (q + 1)).repr ω u =
      ((washnitzerBasis σ K).exteriorPower (q + 1)).repr
        (exteriorDeriv K (washnitzerAlgebra σ K) q η₀) u := by
  rw [washnitzerBasis_exteriorPower_repr_exteriorDeriv]
  symm
  rw [Finset.sum_eq_single ⟨i₀, hi₀u⟩]
  · rw [hrepr_η₀, hg_ofCard]
    have hgt : ∀ j ∈ u.1.erase i₀, i₀ < j := fun j hj ↦
      lt_of_le_of_ne (hex_lt j (Finset.mem_of_mem_erase hj))
        (Ne.symm (Finset.ne_of_mem_erase hj))
    rw [dite_eq_left hgt, pderiv_primitive]
    suffices hins0 : ∀ t' : Set.powersetCard σ (q + 1),
        t'.1 = insert i₀ (u.1.erase i₀) →
        TauCeti.ExteriorAlgebra.basisEraseSign i₀ u.1 •
          ((washnitzerBasis σ K).exteriorPower (q + 1)).repr ω t' =
        ((washnitzerBasis σ K).exteriorPower (q + 1)).repr ω u by
      refine hins0 _ ?_
      rfl
    intro t' ht'_val
    have ht'_eq : t' = u := Subtype.ext (ht'_val.trans (Finset.insert_erase hi₀u))
    have hfilt : (u.1.filter fun j ↦ j < i₀) = ∅ := by
      ext j
      simp only [Finset.mem_filter, Finset.notMem_empty, iff_false, not_and]
      exact fun hju ↦ not_lt_of_ge (hex_lt j hju)
    have hsign : TauCeti.ExteriorAlgebra.basisEraseSign i₀ u.1 = 1 := by
      rw [TauCeti.ExteriorAlgebra.basisEraseSign_eq_neg_one_pow_card_filter_lt, hfilt,
        Finset.card_empty, pow_zero]
    rw [ht'_eq]
    exact (congrArg
      (fun z : ℤˣ ↦ z • ((washnitzerBasis σ K).exteriorPower (q + 1)).repr ω u) hsign).trans
      (units_one_smul_washnitzer _)
  · intro k _ hki₀
    rw [hrepr_η₀, hg_ofCard]
    have hki₀' : i₀ ≠ k.1 := fun heq ↦ hki₀ (Subtype.ext heq.symm)
    have hi₀_erase : i₀ ∈ u.1.erase k.1 := Finset.mem_erase.mpr ⟨hki₀', hi₀u⟩
    have hnot_gt : ¬∀ j ∈ u.1.erase k.1, i₀ < j := fun hgt ↦
      lt_irrefl i₀ (hgt i₀ hi₀_erase)
    rw [dite_eq_right hnot_gt, (pderiv σ K k.1).map_zero, units_smul_zero_washnitzer]
  · intro hmem
    exact absurd (Finset.mem_attach u.1 ⟨i₀, hi₀u⟩) hmem

private theorem poincare_step [LinearOrder σ] (q : ℕ) (i₀ : σ)
    {ω : ⋀[washnitzerAlgebra σ K]^(q + 1) (Omega K (washnitzerAlgebra σ K))}
    (hdω : exteriorDeriv K (washnitzerAlgebra σ K) (q + 1) ω = 0)
    (hsupp : ∀ s : Set.powersetCard σ (q + 1),
      ((washnitzerBasis σ K).exteriorPower (q + 1)).repr ω s ≠ 0 → ∀ i ∈ s.1, i₀ ≤ i) :
    ∃ η₀ : ⋀[washnitzerAlgebra σ K]^q (Omega K (washnitzerAlgebra σ K)),
      exteriorDeriv K (washnitzerAlgebra σ K) (q + 1)
          (ω - exteriorDeriv K (washnitzerAlgebra σ K) q η₀) = 0 ∧
        ∀ u : Set.powersetCard σ (q + 1),
          ((washnitzerBasis σ K).exteriorPower (q + 1)).repr
              (ω - exteriorDeriv K (washnitzerAlgebra σ K) q η₀) u ≠ 0 →
            ∀ i ∈ u.1, i₀ < i := by
  let b := washnitzerBasis σ K
  let g : Set.powersetCard σ q → washnitzerAlgebra σ K := fun t ↦
    if hgt : ∀ j ∈ t.1, i₀ < j then
      have hnot : i₀ ∉ t.1 := fun hi₀ ↦ lt_irrefl i₀ (hgt i₀ hi₀)
      primitive σ K i₀ ((b.exteriorPower (q + 1)).repr ω
        (Set.powersetCard.ofCard (s := insert i₀ t.1)
          (by rw [Finset.card_insert_of_notMem hnot, Set.powersetCard.card_eq t])))
    else 0
  have hg_ofCard {s₀ : Finset σ} (hs₀ : s₀.card = q) :
      g (Set.powersetCard.ofCard hs₀) =
        if hgt : ∀ j ∈ s₀, i₀ < j then
          primitive σ K i₀ ((b.exteriorPower (q + 1)).repr ω
            (Set.powersetCard.ofCard (s := insert i₀ s₀)
              (by
                have hnot : i₀ ∉ s₀ := fun hi₀ ↦ lt_irrefl i₀ (hgt i₀ hi₀)
                rw [Finset.card_insert_of_notMem hnot, hs₀])))
        else 0 := by
    dsimp only [g]
    by_cases hgt : ∀ j ∈ s₀, i₀ < j
    · have hgt' : ∀ j ∈ (Set.powersetCard.ofCard hs₀).1, i₀ < j := by
        simpa only [Set.powersetCard.val_ofCard] using hgt
      rw [dite_eq_left hgt', dite_eq_left hgt]
      congr 2
    · have hgt' : ¬∀ j ∈ (Set.powersetCard.ofCard hs₀).1, i₀ < j := by
        simpa only [Set.powersetCard.val_ofCard] using hgt
      rw [dite_eq_right hgt', dite_eq_right hgt]
  have : Finite (Set.powersetCard σ q) := by
    let : Fintype σ := Fintype.ofFinite σ
    infer_instance
  let η₀ : ⋀[washnitzerAlgebra σ K]^q (Omega K (washnitzerAlgebra σ K)) :=
    (b.exteriorPower q).repr.symm (Finsupp.equivFunOnFinite.symm g)
  have hrepr_η₀ (t : Set.powersetCard σ q) :
      (b.exteriorPower q).repr η₀ t = g t := by
    rw [LinearEquiv.apply_symm_apply]
    rfl
  refine ⟨η₀, ?_, ?_⟩
  · rw [map_sub, hdω, exteriorDeriv_exteriorDeriv_apply, sub_zero]
  · intro u hu i hi
    by_contra! hle_i₀
    apply hu
    rw [← Module.Basis.coord_apply, LinearMap.map_sub, sub_eq_zero,
      Module.Basis.coord_apply, Module.Basis.coord_apply]
    by_cases hex_lt : ∃ j₀ ∈ u.1, j₀ < i₀
    · obtain ⟨j₀, hj₀u, hj₀m⟩ := hex_lt
      have hωu : (b.exteriorPower (q + 1)).repr ω u = 0 := by
        by_contra hne
        exact not_le_of_gt hj₀m (hsupp u hne j₀ hj₀u)
      rw [hωu, washnitzerBasis_exteriorPower_repr_exteriorDeriv]
      symm
      refine Finset.sum_eq_zero fun k _ ↦ ?_
      rw [hrepr_η₀, hg_ofCard]
      by_cases hkj₀ : k.1 = j₀
      · by_cases hgt : ∀ j ∈ u.1.erase k.1, i₀ < j
        · have hji₀ : i₀ ≠ k.1 := ne_of_gt (hkj₀ ▸ hj₀m)
          rw [dite_eq_left hgt, pderiv_primitive_of_ne hji₀]
          suffices hp0 : ∀ s : Set.powersetCard σ (q + 1),
              s.1 = insert i₀ (u.1.erase k.1) →
              TauCeti.ExteriorAlgebra.basisEraseSign k.1 u.1 •
                primitive σ K i₀ (pderiv σ K k.1 ((b.exteriorPower (q + 1)).repr ω s)) = 0 by
            refine hp0 _ ?_
            rfl
          intro s hs_val
          have hkn_s : k.1 ∉ s.1 := by
            rw [hs_val]
            simp only [Finset.mem_insert, Finset.mem_erase, not_or, not_and]
            exact ⟨Ne.symm hji₀, fun h ↦ absurd rfl h⟩
          rw [pderiv_repr_eq_zero_of_lt q hdω hsupp (hkj₀ ▸ hj₀m) s hkn_s,
            (primitive σ K i₀).map_zero, units_smul_zero_washnitzer]
        · rw [dite_eq_right hgt, (pderiv σ K k.1).map_zero, units_smul_zero_washnitzer]
      · have hj₀_erase : j₀ ∈ u.1.erase k.1 := Finset.mem_erase.mpr ⟨Ne.symm hkj₀, hj₀u⟩
        have hnot_gt : ¬∀ j ∈ u.1.erase k.1, i₀ < j :=
          fun hgt ↦ asymm hj₀m (hgt j₀ hj₀_erase)
        rw [dite_eq_right hnot_gt, (pderiv σ K k.1).map_zero, units_smul_zero_washnitzer]
    · simp only [not_exists, not_and, not_lt] at hex_lt
      have hi_eq : i = i₀ := le_antisymm hle_i₀ (hex_lt i hi)
      exact poincare_caseB q i₀ ω η₀ g hrepr_η₀ hg_ofCard u (hi_eq ▸ hi) hex_lt

/-- **The Poincaré lemma on a dagger polydisc (Grosse-Klönne).** Over a complete ultrametric
field `K` of characteristic zero, every closed `(q + 1)`-form on `W = K⟨X_σ⟩†` (`[Finite σ]`) is
exact. -/
theorem exists_exteriorDeriv_eq_of_exteriorDeriv_eq_zero (q : ℕ)
    {ω₀ : ⋀[washnitzerAlgebra σ K]^(q + 1) (Omega K (washnitzerAlgebra σ K))}
    (hω₀ : exteriorDeriv K (washnitzerAlgebra σ K) (q + 1) ω₀ = 0) :
    ∃ η : ⋀[washnitzerAlgebra σ K]^q (Omega K (washnitzerAlgebra σ K)),
      exteriorDeriv K (washnitzerAlgebra σ K) q η = ω₀ := by
  obtain ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin σ
  let : LinearOrder σ := LinearOrder.lift' e e.injective
  let b := washnitzerBasis σ K
  -- Induct on `k = n - m`: any closed `(q + 1)`-form whose active coordinates all satisfy
  -- `m ≤ (e i : ℕ)` is exact.
  suffices hstep : ∀ k (m : ℕ), m + k = n →
      ∀ (ω : ⋀[washnitzerAlgebra σ K]^(q + 1) (Omega K (washnitzerAlgebra σ K))),
        exteriorDeriv K (washnitzerAlgebra σ K) (q + 1) ω = 0 →
        (∀ s : Set.powersetCard σ (q + 1),
          (b.exteriorPower (q + 1)).repr ω s ≠ 0 → ∀ i ∈ s.1, m ≤ (e i : ℕ)) →
        ∃ η : ⋀[washnitzerAlgebra σ K]^q (Omega K (washnitzerAlgebra σ K)),
          exteriorDeriv K (washnitzerAlgebra σ K) q η = ω by
    exact hstep n 0 (Nat.zero_add n) ω₀ hω₀ fun _ _ _ _ ↦ Nat.zero_le _
  intro k
  induction k with
  | zero =>
    intro m hm ω _ hsupp
    refine ⟨0, ?_⟩
    rw [map_zero]
    symm
    rw [← (b.exteriorPower (q + 1)).repr.map_eq_zero_iff, Finsupp.ext_iff]
    intro s
    by_contra hne
    obtain ⟨i, hi⟩ := Finset.card_pos.mp
      (by rw [Set.powersetCard.card_eq s]; exact Nat.succ_pos q)
    have hle := hsupp s hne i hi
    have := (e i).2
    omega
  | succ k ih =>
    intro m hm ω hdω hsupp
    have hmn : m < n := by omega
    let i₀ : σ := e.symm ⟨m, hmn⟩
    have hei₀ : (e i₀ : ℕ) = m := by simp [i₀]
    have hsupp_i₀ (s : Set.powersetCard σ (q + 1))
        (hs : (b.exteriorPower (q + 1)).repr ω s ≠ 0) (i : σ) (hi : i ∈ s.1) : i₀ ≤ i := by
      change e i₀ ≤ e i
      rw [Fin.le_def, hei₀]
      exact hsupp s hs i hi
    obtain ⟨η₀, hdω', hsupp'⟩ := poincare_step q i₀ hdω hsupp_i₀
    have hsupp'_m (s : Set.powersetCard σ (q + 1))
        (hs : (b.exteriorPower (q + 1)).repr
          (ω - exteriorDeriv K (washnitzerAlgebra σ K) q η₀) s ≠ 0)
        (i : σ) (hi : i ∈ s.1) : m + 1 ≤ (e i : ℕ) := by
      have hlt : e i₀ < e i := hsupp' s hs i hi
      rw [Fin.lt_def, hei₀] at hlt
      omega
    obtain ⟨η₁, hη₁⟩ := ih (m + 1) (by omega) _ hdω' hsupp'_m
    refine ⟨η₀ + η₁, ?_⟩
    rw [map_add, hη₁, add_sub_cancel]

/-- In characteristic zero, exact and closed `(q + 1)`-forms on `W = K⟨X_σ⟩†` coincide. -/
theorem exactForms_washnitzer_succ (q : ℕ) :
    exactForms K (washnitzerAlgebra σ K) (q + 1) =
      closedForms K (washnitzerAlgebra σ K) (q + 1) := by
  refine le_antisymm (exactForms_le_closedForms K (washnitzerAlgebra σ K) (q + 1)) fun ω hω ↦ ?_
  rw [exactForms_succ, LinearMap.mem_range]
  exact exists_exteriorDeriv_eq_of_exteriorDeriv_eq_zero q
    ((mem_closedForms K (washnitzerAlgebra σ K) ω).mp hω)

/-- **Exactness of the overconvergent de Rham complex of a dagger polydisc** in every positive
degree `q + 1` over a complete ultrametric field of characteristic zero. -/
theorem exactAt_deRhamComplex_washnitzer_succ (q : ℕ) :
    (deRhamComplex K (washnitzerAlgebra σ K)).ExactAt (q + 1) :=
  (exactAt_deRhamComplex_succ_iff K (washnitzerAlgebra σ K) q).mpr
    (exactForms_washnitzer_succ q)

/-- **Vanishing of positive-degree overconvergent de Rham cohomology on a dagger polydisc** in
characteristic zero. -/
instance instSubsingletonDeRhamCohomologyWashnitzerSucc (q : ℕ) :
    Subsingleton (deRhamCohomology K (washnitzerAlgebra σ K) (q + 1)) :=
  subsingleton_deRhamCohomology_of_closedForms_le_exactForms K (washnitzerAlgebra σ K)
    (exactForms_washnitzer_succ q).ge

end AllPositiveDegrees

/-! ### Failure of the polydisc Poincaré lemma in positive characteristic -/

section CharP

variable {K : Type*} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]

omit [CompleteSpace K] in
/-- In characteristic `p`, `d (X₀ ^ p) = 0` in `Ω¹_{K⟨X₀⟩† / K}`. -/
theorem d_X_pow_charP (p : ℕ) [CharP K p] :
    d K (washnitzerAlgebra (Fin 1) K) (X (Fin 1) K 0 ^ p) = 0 := by
  rw [(d K (washnitzerAlgebra (Fin 1) K)).leibniz_pow, ← Nat.cast_smul_eq_nsmul K,
    CharP.cast_eq_zero, zero_smul]

omit [CompleteSpace K] in
/-- For every `m > 0`, `X₀ ^ m` in `K⟨X₀⟩†` does not lie in the image of `algebraMap K _`. -/
theorem X_pow_notMem_range_algebraMap {m : ℕ} (hm : 0 < m) :
    X (Fin 1) K 0 ^ m ∉ Set.range (algebraMap K (washnitzerAlgebra (Fin 1) K)) := by
  rintro ⟨c, hc⟩
  have hcoeff :=
    congrArg (fun f : washnitzerAlgebra (Fin 1) K ↦
      MvPowerSeries.coeff (Finsupp.single (0 : Fin 1) m) f.1) hc
  have hlhs :
      MvPowerSeries.coeff (Finsupp.single (0 : Fin 1) m)
        (algebraMap K (washnitzerAlgebra (Fin 1) K) c).1 = 0 := by
    have hne : Finsupp.single (0 : Fin 1) m ≠ 0 :=
      Finsupp.single_ne_zero.mpr hm.ne'
    simp [MvPowerSeries.algebraMap_apply, MvPowerSeries.coeff_C, hne]
  have hrhs :
      MvPowerSeries.coeff (Finsupp.single (0 : Fin 1) m)
        (X (Fin 1) K 0 ^ m).1 = 1 := by
    simp only [SubmonoidClass.coe_pow, coe_X, MvPowerSeries.coeff_X_pow, ↓reduceIte]
  rw [hlhs, hrhs] at hcoeff
  exact zero_ne_one hcoeff

omit [CompleteSpace K] in
/-- **Failure of the degree-zero Poincaré lemma in characteristic `p > 0`**: on `W = K⟨X₀⟩†`,
`X₀ ^ p` satisfies `d (X₀ ^ p) = 0` while `X₀ ^ p ∉ range (algebraMap K W)`. -/
theorem exists_d_eq_zero_and_notMem_range_algebraMap_charP (p : ℕ) [CharP K p] [Fact p.Prime] :
    ∃ f : washnitzerAlgebra (Fin 1) K,
      d K (washnitzerAlgebra (Fin 1) K) f = 0 ∧
        f ∉ Set.range (algebraMap K (washnitzerAlgebra (Fin 1) K)) :=
  ⟨X (Fin 1) K 0 ^ p, d_X_pow_charP p,
    X_pow_notMem_range_algebraMap (Fact.out : p.Prime).pos⟩

/-- **Failure of the degree-one Poincaré lemma in characteristic `p > 0`**: on `W = K⟨X₀⟩†`, the
`1`-form `X₀ ^ (p - 1) • d X₀` has no potential `g ∈ W` with `d g = X₀ ^ (p - 1) • d X₀`. -/
theorem not_exists_d_eq_X_pow_sub_one_smul_d_X_charP (p : ℕ) [CharP K p] [Fact p.Prime] :
    ¬∃ g : washnitzerAlgebra (Fin 1) K,
      d K (washnitzerAlgebra (Fin 1) K) g =
        X (Fin 1) K 0 ^ (p - 1) • d K (washnitzerAlgebra (Fin 1) K) (X (Fin 1) K 0) := by
  rintro ⟨g, hg⟩
  have hp : 0 < p := (Fact.out : p.Prime).pos
  have hrepr := congrArg (fun ω ↦ (washnitzerBasis (Fin 1) K).repr ω 0) hg
  rw [washnitzerBasis_repr_d, LinearEquiv.map_smul, ← washnitzerBasis_apply,
    Module.Basis.repr_self, Finsupp.smul_single_one, Finsupp.single_eq_same] at hrepr
  have hcoeff := congrArg (fun f : washnitzerAlgebra (Fin 1) K ↦
    MvPowerSeries.coeff (Finsupp.single (0 : Fin 1) (p - 1)) f.1) hrepr
  have hlhs :
      MvPowerSeries.coeff (Finsupp.single (0 : Fin 1) (p - 1))
        (pderiv (Fin 1) K 0 g).1 = 0 := by
    rw [coe_pderiv, MvPowerSeries.coeff_pderiv, Finsupp.single_eq_same,
      ← Nat.cast_add_one, Nat.sub_add_cancel hp, CharP.cast_eq_zero, mul_zero]
  have hrhs :
      MvPowerSeries.coeff (Finsupp.single (0 : Fin 1) (p - 1))
        (X (Fin 1) K 0 ^ (p - 1)).1 = 1 := by
    simp only [SubmonoidClass.coe_pow, coe_X, MvPowerSeries.coeff_X_pow, ↓reduceIte]
  rw [hlhs, hrhs] at hcoeff
  exact zero_ne_one hcoeff

/-- In characteristic `p > 0`, the overconvergent de Rham complex of the one-variable dagger disc
`K⟨X₀⟩†` is not exact in degree `1`. -/
theorem not_exactAt_deRhamComplex_washnitzer_one_charP (p : ℕ) [CharP K p] [Fact p.Prime] :
    ¬(deRhamComplex K (washnitzerAlgebra (Fin 1) K)).ExactAt 1 := by
  rw [exactAt_deRhamComplex_succ_iff K (washnitzerAlgebra (Fin 1) K) 0]
  intro hex
  let ω : ⋀[washnitzerAlgebra (Fin 1) K]^1 (Omega K (washnitzerAlgebra (Fin 1) K)) :=
    (exteriorPower.oneEquiv (washnitzerAlgebra (Fin 1) K) _).symm
      (X (Fin 1) K 0 ^ (p - 1) • d K (washnitzerAlgebra (Fin 1) K) (X (Fin 1) K 0))
  have hclosed : ω ∈ closedForms K (washnitzerAlgebra (Fin 1) K) 1 := by
    have : Subsingleton
        (⋀[washnitzerAlgebra (Fin 1) K]^2 (Omega K (washnitzerAlgebra (Fin 1) K))) :=
      subsingleton_forms_washnitzer_of_card_lt (σ := Fin 1) (K := K) (q := 2) (by simp)
    rw [mem_closedForms]
    exact Subsingleton.elim _ 0
  rw [← hex, exactForms_succ, LinearMap.mem_range] at hclosed
  obtain ⟨f₀, hf₀⟩ := hclosed
  obtain ⟨c, rfl⟩ :=
    (exteriorPower.zeroEquiv (washnitzerAlgebra (Fin 1) K) _).symm.surjective f₀
  rw [exteriorDeriv_zero_symm] at hf₀
  have hd : d K (washnitzerAlgebra (Fin 1) K) c =
      X (Fin 1) K 0 ^ (p - 1) • d K (washnitzerAlgebra (Fin 1) K) (X (Fin 1) K 0) :=
    (exteriorPower.oneEquiv (washnitzerAlgebra (Fin 1) K) _).symm.injective hf₀
  exact not_exists_d_eq_X_pow_sub_one_smul_d_X_charP p ⟨c, hd⟩

/-- In characteristic `p > 0`, the first overconvergent de Rham cohomology `H¹_dR(K⟨X₀⟩† / K)` is
nontrivial. -/
theorem nontrivial_deRhamCohomology_washnitzer_one_charP (p : ℕ) [CharP K p] [Fact p.Prime] :
    Nontrivial (deRhamCohomology K (washnitzerAlgebra (Fin 1) K) 1) := by
  by_contra h
  rw [not_nontrivial_iff_subsingleton] at h
  apply not_exactAt_deRhamComplex_washnitzer_one_charP (K := K) p
  rw [exactAt_deRhamComplex_succ_iff K (washnitzerAlgebra (Fin 1) K) 0]
  refine le_antisymm (exactForms_le_closedForms K _ 1) fun ω hω ↦ ?_
  have hmk : deRhamCohomology.mk K (washnitzerAlgebra (Fin 1) K) 1 ⟨ω, hω⟩ = 0 :=
    Subsingleton.elim _ 0
  exact (deRhamCohomology.mk_eq_zero_iff K _ 1 ⟨ω, hω⟩).mp hmk

end CharP

end TauCeti.Dagger.Omega

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.ExteriorAlgebra.Contraction
public import TauCeti.RingTheory.Dagger.Omega.DeRham
public import TauCeti.RingTheory.Dagger.Poincare
import TauCeti.LinearAlgebra.ExteriorPower.Basis

/-!
# The Poincaré lemma on a dagger polydisc

Over a complete ultrametric normed field `K` of characteristic zero, the overconvergent de Rham
complex of `W = K⟨X_σ⟩†` (`[Finite σ]`) has `H⁰_dR(W/K) ≃ₗ[K] K` and is exact in every positive
degree `q + 1`, so `deRhamCohomology K W (q + 1)` is subsingleton.

We prove the coordinate formula `washnitzerBasis_exteriorPower_repr_exteriorDeriv` (valid in any
characteristic), deduce the curl-free characterization of closed `1`-forms and unique potentials
with prescribed constant coefficient, establish positive-degree exactness by induction over `σ` via
`washnitzerAlgebra.primitive`, and prove failure in degrees `0` and `1` on `K⟨X₀⟩†` in prime
characteristic `p`.

## References

* E. Grosse-Klönne, *Finiteness of de Rham cohomology in rigid analysis*, Duke Math. J. 113
  (2002), §2, Lemma 2.1.
* K. Kedlaya, *Finiteness of rigid cohomology with coefficients*, Duke Math. J. 134 (2006), §2–§3.
-/

public section

open scoped BigOperators

namespace TauCeti.Dagger.Omega

open TauCeti.Dagger.washnitzerAlgebra TauCeti.ExteriorAlgebra

/-! ### Degree zero: kernel of `d` and `H⁰_dR(W/K) ≃ₗ[K] K` -/

section DegreeZero

variable {σ K : Type*} [Finite σ] [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  [CharZero K]

/-- In characteristic zero, `d f = 0` in `Ω¹_{W/K}` iff `f ∈ range (algebraMap K W)`. -/
theorem d_eq_zero_iff_mem_range_algebraMap (f : washnitzerAlgebra σ K) :
    d K (washnitzerAlgebra σ K) f = 0 ↔ f ∈ Set.range (algebraMap K (washnitzerAlgebra σ K)) := by
  rw [d_eq_zero_iff_forall_pderiv_eq_zero, forall_pderiv_eq_zero_iff]; rfl

/-- In characteristic zero, `d f = 0` iff `f` equals its constant coefficient viewed in `W`. -/
theorem d_eq_zero_iff_eq_algebraMap_constantCoeff (f : washnitzerAlgebra σ K) :
    d K (washnitzerAlgebra σ K) f = 0 ↔
      f = algebraMap K (washnitzerAlgebra σ K) (MvPowerSeries.constantCoeff f.1) := by
  rw [d_eq_zero_iff_mem_range_algebraMap]
  exact ⟨by rintro ⟨c, rfl⟩; simp [MvPowerSeries.algebraMap_apply],
    fun h ↦ ⟨MvPowerSeries.constantCoeff f.1, h.symm⟩⟩

variable (σ K) in
/-- In characteristic zero, closed `0`-forms on `W = K⟨X_σ⟩†` are `K`-linearly equivalent to `K`. -/
noncomputable def closedFormsZeroWashnitzerEquiv :
    K ≃ₗ[K] closedForms K (washnitzerAlgebra σ K) 0 where
  toFun c := ⟨(exteriorPower.zeroEquiv (washnitzerAlgebra σ K) _).symm (algebraMap K _ c), by
    rw [mem_closedForms, exteriorDeriv_zero_symm, (d K _).map_algebraMap, LinearEquiv.map_zero]⟩
  map_add' _ _ := Subtype.ext (by simp [map_add])
  map_smul' a _ := Subtype.ext <| by
    simp only [smul_eq_mul, RingHom.id_apply, SetLike.val_smul]
    rw [map_mul, ← Algebra.smul_def, ← IsScalarTower.algebraMap_smul (washnitzerAlgebra σ K) a,
      LinearEquiv.map_smul, IsScalarTower.algebraMap_smul]
  invFun ω := MvPowerSeries.constantCoeff (exteriorPower.zeroEquiv _ _ ω.1).1
  left_inv _ := by simp [MvPowerSeries.algebraMap_apply]
  right_inv ω := Subtype.ext <| by
    dsimp only; set f := exteriorPower.zeroEquiv _ _ ω.1
    have hdf : d K (washnitzerAlgebra σ K) f = 0 := by
      rw [← oneEquiv_exteriorDeriv_zero, (mem_closedForms K _ ω.1).mp ω.2, LinearEquiv.map_zero]
    rw [← (d_eq_zero_iff_eq_algebraMap_constantCoeff f).mp hdf, LinearEquiv.symm_apply_apply]

@[simp] theorem coe_closedFormsZeroWashnitzerEquiv_apply (c : K) :
    (closedFormsZeroWashnitzerEquiv σ K c).1 =
      (exteriorPower.zeroEquiv (washnitzerAlgebra σ K) _).symm (algebraMap K _ c) := (rfl)
@[simp] theorem closedFormsZeroWashnitzerEquiv_symm_apply
    (ω : closedForms K (washnitzerAlgebra σ K) 0) :
    (closedFormsZeroWashnitzerEquiv σ K).symm ω =
      MvPowerSeries.constantCoeff (exteriorPower.zeroEquiv _ _ ω.1).1 := (rfl)

variable (σ K) in
/-- **Degree-zero de Rham cohomology of a dagger polydisc**: `H⁰_dR(K⟨X_σ⟩† / K) ≃ₗ[K] K`. -/
noncomputable def deRhamCohomologyZeroWashnitzerEquiv :
    K ≃ₗ[K] deRhamCohomology K (washnitzerAlgebra σ K) 0 :=
  (closedFormsZeroWashnitzerEquiv σ K).trans
    (deRhamCohomology.zeroEquivClosedForms K (washnitzerAlgebra σ K))

@[simp] theorem deRhamCohomologyZeroWashnitzerEquiv_apply (c : K) :
    deRhamCohomologyZeroWashnitzerEquiv σ K c =
      deRhamCohomology.mk K (washnitzerAlgebra σ K) 0 (closedFormsZeroWashnitzerEquiv σ K c) :=
  deRhamCohomology.zeroEquivClosedForms_apply _ _ _
@[simp] theorem deRhamCohomologyZeroWashnitzerEquiv_symm_mk
    (ω : closedForms K (washnitzerAlgebra σ K) 0) :
    (deRhamCohomologyZeroWashnitzerEquiv σ K).symm
        (deRhamCohomology.mk K (washnitzerAlgebra σ K) 0 ω) =
      MvPowerSeries.constantCoeff (exteriorPower.zeroEquiv _ _ ω.1).1 := by
  rw [← deRhamCohomology.zeroEquivClosedForms_apply, deRhamCohomologyZeroWashnitzerEquiv,
    LinearEquiv.trans_symm, LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply]; rfl

end DegreeZero

/-! ### Coordinate formula for `exteriorDeriv` and exactness in degree one -/

section CoordinateFormula

variable {σ K : Type*} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]

/-- Basis monomials `dX_{i₀} ∧ ⋯ ∧ dX_{i_{r-1}}` are killed by `exteriorDeriv`. -/
theorem exteriorDeriv_washnitzerBasis_exteriorPower [Finite σ] [LinearOrder σ] (r : ℕ)
    (t : Set.powersetCard σ r) :
    exteriorDeriv K (washnitzerAlgebra σ K) r ((washnitzerBasis σ K).exteriorPower r t) = 0 := by
  have hcomp : (washnitzerBasis σ K) ∘ (Set.powersetCard.ofFinEmbEquiv.symm t) =
      (d K (washnitzerAlgebra σ K)) ∘ (X σ K ∘ Set.powersetCard.ofFinEmbEquiv.symm t) :=
    funext fun _ ↦ washnitzerBasis_apply ..
  rw [exteriorPower.basis_apply, exteriorPower.ιMulti_family, hcomp]
  exact exteriorDeriv_ιMulti_comp_d _

private theorem washnitzerBasis_exteriorPower_repr_exteriorDeriv_smul
    [Fintype σ] [LinearOrder σ] (r : ℕ) (t : Set.powersetCard σ r)
    (c : washnitzerAlgebra σ K) (u : Set.powersetCard σ (r + 1)) :
    ((washnitzerBasis σ K).exteriorPower (r + 1)).repr
        (exteriorDeriv K (washnitzerAlgebra σ K) r
          (c • (washnitzerBasis σ K).exteriorPower r t)) u =
      ∑ k : σ, if k ∉ t.1 ∧ insert k t.1 = u.1 then
        basisEraseSign k u.1 • pderiv σ K k c else 0 := by
  rw [← (washnitzerBasis σ K).exteriorAlgebra_repr_coe_eq, ← Module.Basis.coord_apply,
    exteriorDeriv_smul, exteriorDeriv_washnitzerBasis_exteriorPower, smul_zero, add_zero,
    coe_wedgeLeft_apply, ← ExteriorAlgebra.basis_eq_coe_basis]
  conv_lhs => rw [← (washnitzerBasis σ K).sum_repr (d K (washnitzerAlgebra σ K) c)]
  rw [map_sum, Finset.sum_mul, map_sum]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  rw [washnitzerBasis_repr_d, LinearMap.map_smul, smul_mul_assoc, LinearMap.map_smul, ι_mul_basis]
  by_cases hkt : k ∈ t.1
  · simp [hkt]
  · rw [ite_eq_right hkt, Units.smul_def, ← Int.cast_smul_eq_zsmul (washnitzerAlgebra σ K),
      LinearMap.map_smul, Module.Basis.coord_apply, Module.Basis.repr_self]
    by_cases hins : insert k t.1 = u.1
    · rw [ite_eq_left ⟨hkt, hins⟩, hins, Units.smul_def,
        ← Int.cast_smul_eq_zsmul (washnitzerAlgebra σ K), Finsupp.single_eq_same]; simp [mul_comm]
    · rw [ite_eq_right fun h ↦ hins h.2, Finsupp.single_eq_of_ne' hins]; simp

/-- **Coordinate formula for the overconvergent exterior derivative** in any characteristic. -/
theorem washnitzerBasis_exteriorPower_repr_exteriorDeriv [Finite σ] [LinearOrder σ]
    (r : ℕ) (ω : ⋀[washnitzerAlgebra σ K]^r (Omega K (washnitzerAlgebra σ K)))
    (u : Set.powersetCard σ (r + 1)) :
    ((washnitzerBasis σ K).exteriorPower (r + 1)).repr
        (exteriorDeriv K (washnitzerAlgebra σ K) r ω) u =
      ∑ k ∈ u.1.attach, basisEraseSign k.1 u.1 •
        pderiv σ K k.1 (((washnitzerBasis σ K).exteriorPower r).repr ω
          (Set.powersetCard.ofCard (s := u.1.erase k.1)
            (by rw [Finset.card_erase_of_mem k.2, Set.powersetCard.card_eq u]; rfl))) := by
  let : Fintype σ := Fintype.ofFinite σ; let : Fintype (Set.powersetCard σ r) := Fintype.ofFinite _
  rw [← Module.Basis.coord_apply]
  conv_lhs => rw [← ((washnitzerBasis σ K).exteriorPower r).sum_repr ω]
  rw [map_sum, map_sum, Finset.sum_congr rfl fun t _ ↦ by
      rw [Module.Basis.coord_apply, washnitzerBasis_exteriorPower_repr_exteriorDeriv_smul],
    Finset.sum_comm, ← Finset.sum_subset (Finset.subset_univ u.1)]
  · rw [← Finset.sum_attach u.1]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    let tk : Set.powersetCard σ r := Set.powersetCard.ofCard (s := u.1.erase k.1)
      (by rw [Finset.card_erase_of_mem k.2, Set.powersetCard.card_eq u]; rfl)
    rw [Finset.sum_eq_single tk
      (fun t _ hne ↦ ite_eq_right fun ⟨hkt, hins⟩ ↦ hne <| Subtype.ext <|
        (Finset.erase_insert hkt).symm.trans (congrArg (·.erase k.1) hins))
      (fun h ↦ absurd (Finset.mem_univ tk) h),
      ite_eq_left ⟨Finset.notMem_erase k.1 u.1, Finset.insert_erase k.2⟩]
  · exact fun k _ hku ↦ Finset.sum_eq_zero fun t _ ↦ by
      rw [ite_eq_right]; rintro ⟨_, hins⟩; exact hku (hins ▸ Finset.mem_insert_self k t.1)

/-- For `i < j`, the `{i, j}`-coordinate of `dω` for a `1`-form `ω` is `∂ᵢ ωⱼ - ∂ⱼ ωᵢ`. -/
private theorem washnitzerBasis_exteriorPower_two_repr_exteriorDeriv_one [Finite σ] [LinearOrder σ]
    (ω : Omega K (washnitzerAlgebra σ K)) {i j : σ} (hij : i < j) :
    ((washnitzerBasis σ K).exteriorPower 2).repr
        (exteriorDeriv K (washnitzerAlgebra σ K) 1
          ((exteriorPower.oneEquiv (washnitzerAlgebra σ K) _).symm ω))
        (Set.powersetCard.ofCard (Finset.card_pair hij.ne)) =
      pderiv σ K i ((washnitzerBasis σ K).repr ω j) -
        pderiv σ K j ((washnitzerBasis σ K).repr ω i) := by
  set u := Set.powersetCard.ofCard (Finset.card_pair hij.ne)
  rw [washnitzerBasis_exteriorPower_repr_exteriorDeriv]
  have hatt : u.1.attach = {⟨i, by simp [u]⟩, ⟨j, by simp [u]⟩} := by
    ext ⟨x, hx⟩; simp only [Finset.mem_attach, Finset.mem_insert, Finset.mem_singleton,
      Subtype.ext_iff, true_iff]; simpa [u, Set.powersetCard.ofCard] using hx
  rw [hatt, Finset.sum_pair (fun h ↦ hij.ne (congrArg Subtype.val h))]
  have hei (hc : (u.1.erase i).card = 1) :
      Set.powersetCard.ofCard hc = Set.powersetCard.ofCard (Finset.card_singleton j) :=
    Subtype.ext (by simp [u, Set.powersetCard.ofCard, hij.ne])
  have hej (hc : (u.1.erase j).card = 1) :
      Set.powersetCard.ofCard hc = Set.powersetCard.ofCard (Finset.card_singleton i) :=
    Subtype.ext (by simp only [u, Set.powersetCard.ofCard]; rw [Finset.pair_comm]; simp [hij.ne'])
  -- Since `i < j`, `i` has sign `+1` (`{x ∈ u | x < i} = ∅`) and `j` has sign `-1` (`{i}`).
  have hfi : u.1.filter (· < i) = ∅ := by
    simp [u, Set.powersetCard.val_ofCard, Finset.filter_insert, hij.le]
  have hfj : u.1.filter (· < j) = {i} := by
    simp [u, Set.powersetCard.val_ofCard, Finset.filter_insert, Finset.filter_singleton, hij]
  rw [hei, hej, (washnitzerBasis σ K).exteriorPower_one_repr_oneEquiv_symm,
    (washnitzerBasis σ K).exteriorPower_one_repr_oneEquiv_symm,
    basisEraseSign_eq_neg_one_pow_card_filter_lt, basisEraseSign_eq_neg_one_pow_card_filter_lt,
    hfi, hfj]; simp [sub_eq_add_neg]

/-- **Curl-free characterization of closed `1`-forms** on `W = K⟨X_σ⟩†` (any characteristic):
`d(∑ᵢ fᵢ dXᵢ) = 0` iff `∂ᵢ fⱼ = ∂ⱼ fᵢ` for all `i, j : σ`. -/
theorem exteriorDeriv_one_eq_zero_iff [Finite σ] (ω : Omega K (washnitzerAlgebra σ K)) :
    exteriorDeriv K (washnitzerAlgebra σ K) 1
        ((exteriorPower.oneEquiv (washnitzerAlgebra σ K) _).symm ω) = 0 ↔
      ∀ i j, pderiv σ K i ((washnitzerBasis σ K).repr ω j) =
        pderiv σ K j ((washnitzerBasis σ K).repr ω i) := by
  obtain ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin σ
  let : LinearOrder σ := LinearOrder.lift' e e.injective
  rw [← ((washnitzerBasis σ K).exteriorPower 2).repr.map_eq_zero_iff, Finsupp.ext_iff]
  refine ⟨fun h i j ↦ ?_, fun h u ↦ ?_⟩
  · have hlt {a b : σ} (hab : a < b) : pderiv σ K a ((washnitzerBasis σ K).repr ω b) =
        pderiv σ K b ((washnitzerBasis σ K).repr ω a) := sub_eq_zero.mp <| by
      simpa [washnitzerBasis_exteriorPower_two_repr_exteriorDeriv_one ω hab] using
        h (Set.powersetCard.ofCard (Finset.card_pair hab.ne))
    rcases lt_trichotomy i j with hij | rfl | hji; exacts [hlt hij, rfl, (hlt hji).symm]
  · obtain ⟨i, j, hij, hu⟩ := Finset.card_eq_two.mp (Set.powersetCard.card_eq u)
    wlog hlt : i < j generalizing i j
    · exact this j i hij.symm (hu.trans (Finset.pair_comm i j))
        (lt_of_le_of_ne (le_of_not_gt hlt) hij.symm)
    have hu' : u = Set.powersetCard.ofCard (Finset.card_pair hlt.ne) := Subtype.ext hu
    rw [hu', washnitzerBasis_exteriorPower_two_repr_exteriorDeriv_one ω hlt, h i j, sub_self]; rfl

/-- **Degree-one Poincaré lemma on `W = K⟨X_σ⟩†` in characteristic zero**: `ω ∈ Ω¹_{W/K}` is
`d g` for some `g ∈ W` iff `dω = 0`. -/
theorem exists_d_eq_iff_exteriorDeriv_one_eq_zero [Finite σ] [CharZero K]
    (ω : Omega K (washnitzerAlgebra σ K)) :
    (∃ g : washnitzerAlgebra σ K, d K (washnitzerAlgebra σ K) g = ω) ↔
      exteriorDeriv K (washnitzerAlgebra σ K) 1
        ((exteriorPower.oneEquiv (washnitzerAlgebra σ K) _).symm ω) = 0 := by
  rw [exteriorDeriv_one_eq_zero_iff, ← exists_pderiv_eq_iff]
  exact exists_congr fun g ↦ d_eq_iff_forall_pderiv_eq g ω

/-- **Unique potential with prescribed constant coefficient**: for every closed `1`-form `ω` on
`W = K⟨X_σ⟩†` in characteristic zero and every `c : K`, there is a unique `g ∈ W` with
`d g = ω` and constant coefficient `c`. -/
theorem existsUnique_d_eq_of_exteriorDeriv_one_eq_zero [Finite σ] [CharZero K]
    {ω : Omega K (washnitzerAlgebra σ K)}
    (hω : exteriorDeriv K (washnitzerAlgebra σ K) 1
      ((exteriorPower.oneEquiv (washnitzerAlgebra σ K) _).symm ω) = 0) (c : K) :
    ∃! g : washnitzerAlgebra σ K,
      d K (washnitzerAlgebra σ K) g = ω ∧ MvPowerSeries.constantCoeff g.1 = c := by
  simpa only [d_eq_iff_forall_pderiv_eq] using
    existsUnique_pderiv_eq (fun i ↦ (washnitzerBasis σ K).repr ω i)
      ((exteriorDeriv_one_eq_zero_iff ω).mp hω) c

end CoordinateFormula

/-! ### The Poincaré lemma in all positive degrees -/

section AllPositiveDegrees

variable {σ K : Type*} [Finite σ] [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  [CharZero K]

omit [CharZero K] in
private theorem pderiv_repr_eq_zero_of_lt [LinearOrder σ] (q : ℕ) {i₀ k₀ : σ}
    {ω : ⋀[washnitzerAlgebra σ K]^(q + 1) (Omega K (washnitzerAlgebra σ K))}
    (hdω : exteriorDeriv K (washnitzerAlgebra σ K) (q + 1) ω = 0)
    (hsupp : ∀ s : Set.powersetCard σ (q + 1),
      ((washnitzerBasis σ K).exteriorPower (q + 1)).repr ω s ≠ 0 → ∀ i ∈ s.1, i₀ ≤ i)
    (hk₀ : k₀ < i₀) (s : Set.powersetCard σ (q + 1)) (hkn_s : k₀ ∉ s.1) :
    pderiv σ K k₀ (((washnitzerBasis σ K).exteriorPower (q + 1)).repr ω s) = 0 := by
  let w : Set.powersetCard σ (q + 2) := Set.powersetCard.ofCard (s := insert k₀ s.1)
    (by rw [Finset.card_insert_of_notMem hkn_s, Set.powersetCard.card_eq s])
  have hdw : ((washnitzerBasis σ K).exteriorPower (q + 2)).repr
      (exteriorDeriv K (washnitzerAlgebra σ K) (q + 1) ω) w = 0 := by
    rw [hdω, LinearEquiv.map_zero, Finsupp.coe_zero, Pi.zero_apply]
  rw [washnitzerBasis_exteriorPower_repr_exteriorDeriv] at hdw
  have hkw : k₀ ∈ w.1 := Finset.mem_insert_self k₀ s.1
  rw [Finset.sum_eq_single ⟨k₀, hkw⟩] at hdw
  · have hwk : Set.powersetCard.ofCard (s := w.1.erase k₀)
        (by rw [Finset.card_erase_of_mem hkw, Set.powersetCard.card_eq w]; rfl) = s :=
      Subtype.ext (Finset.erase_insert hkn_s)
    rw [hwk] at hdw
    have hinv := congrArg ((basisEraseSign k₀ w.1)⁻¹ • ·) hdw
    rwa [inv_smul_smul, Units.smul_def, zsmul_zero] at hinv
  · intro l _ hlk
    have hzero (hc : (w.1.erase l.1).card = q + 1) :
        ((washnitzerBasis σ K).exteriorPower (q + 1)).repr ω (Set.powersetCard.ofCard hc) = 0 :=
      by_contra fun hne ↦ not_le_of_gt hk₀ <| hsupp _ hne k₀ <| Set.powersetCard.val_ofCard _ ▸
        Finset.mem_erase.mpr ⟨fun h ↦ hlk (Subtype.ext h.symm), hkw⟩
    rw [hzero, map_zero, Units.smul_def, zsmul_zero]
  · exact fun h ↦ absurd (Finset.mem_attach w.1 ⟨k₀, hkw⟩) h

section PoincareStep

variable [LinearOrder σ] {q : ℕ} {i₀ : σ}
  {ω : ⋀[washnitzerAlgebra σ K]^(q + 1) (Omega K (washnitzerAlgebra σ K))}

/-- The `q`-form integrating the `i₀`-components of `ω` along `X_{i₀}` on `q`-subsets strictly
above `i₀`, and vanishing on all other basis multi-indices. -/
private noncomputable def poincarePrimitive (q : ℕ) (i₀ : σ)
    (ω : ⋀[washnitzerAlgebra σ K]^(q + 1) (Omega K (washnitzerAlgebra σ K))) :
    ⋀[washnitzerAlgebra σ K]^q (Omega K (washnitzerAlgebra σ K)) :=
  let : Finite (Set.powersetCard σ q) := let : Fintype σ := Fintype.ofFinite σ; inferInstance
  ((washnitzerBasis σ K).exteriorPower q).repr.symm <| Finsupp.equivFunOnFinite.symm fun t ↦
    if hgt : ∀ j ∈ t.1, i₀ < j then
      primitive σ K i₀ (((washnitzerBasis σ K).exteriorPower (q + 1)).repr ω
        (Set.powersetCard.ofCard (s := insert i₀ t.1)
          (by rw [Finset.card_insert_of_notMem fun h ↦ lt_irrefl i₀ (hgt i₀ h),
            Set.powersetCard.card_eq t])))
    else 0

private theorem poincarePrimitive_repr_of_forall_lt {t : Set.powersetCard σ q}
    (hgt : ∀ j ∈ t.1, i₀ < j) (hc : (insert i₀ t.1).card = q + 1) :
    ((washnitzerBasis σ K).exteriorPower q).repr (poincarePrimitive q i₀ ω) t =
      primitive σ K i₀ (((washnitzerBasis σ K).exteriorPower (q + 1)).repr ω
        (Set.powersetCard.ofCard hc)) := by
  simp only [poincarePrimitive, LinearEquiv.apply_symm_apply, Finsupp.coe_equivFunOnFinite_symm,
    dite_eq_left hgt]

private theorem poincarePrimitive_repr_of_not_forall_lt {t : Set.powersetCard σ q}
    (hnot : ¬∀ j ∈ t.1, i₀ < j) :
    ((washnitzerBasis σ K).exteriorPower q).repr (poincarePrimitive q i₀ ω) t = 0 := by
  simp only [poincarePrimitive, LinearEquiv.apply_symm_apply, Finsupp.coe_equivFunOnFinite_symm,
    dite_eq_right hnot]

/-- For a closed form supported on indices `≥ i₀`, `d (poincarePrimitive q i₀ ω)` vanishes on
every multi-index containing an index strictly below `i₀`. -/
private theorem exteriorDeriv_poincarePrimitive_repr_of_exists_lt
    (hdω : exteriorDeriv K (washnitzerAlgebra σ K) (q + 1) ω = 0)
    (hsupp : ∀ s : Set.powersetCard σ (q + 1),
      ((washnitzerBasis σ K).exteriorPower (q + 1)).repr ω s ≠ 0 → ∀ i ∈ s.1, i₀ ≤ i)
    {u : Set.powersetCard σ (q + 1)} (hex_lt : ∃ j₀ ∈ u.1, j₀ < i₀) :
    ((washnitzerBasis σ K).exteriorPower (q + 1)).repr
        (exteriorDeriv K (washnitzerAlgebra σ K) q (poincarePrimitive q i₀ ω)) u = 0 := by
  obtain ⟨j₀, hj₀u, hj₀m⟩ := hex_lt
  rw [washnitzerBasis_exteriorPower_repr_exteriorDeriv]
  refine Finset.sum_eq_zero fun k _ ↦ ?_
  by_cases hgt : ∀ j ∈ u.1.erase k.1, i₀ < j
  · -- Erasing `k` leaves indices `> i₀`, so `k = j₀ < i₀` and `∂_k` commutes past `primitive i₀`.
    have hkj₀ : k.1 = j₀ := by_contra fun hne ↦
      asymm hj₀m (hgt j₀ (Finset.mem_erase.mpr ⟨Ne.symm hne, hj₀u⟩))
    have hji₀ : i₀ ≠ k.1 := ne_of_gt (hkj₀ ▸ hj₀m)
    let t : Set.powersetCard σ q := Set.powersetCard.ofCard (s := u.1.erase k.1)
      (by rw [Finset.card_erase_of_mem k.2, Set.powersetCard.card_eq u]; rfl)
    have hgt' : ∀ j ∈ t.1, i₀ < j := by simpa only [t, Set.powersetCard.val_ofCard] using hgt
    rw [poincarePrimitive_repr_of_forall_lt (t := t) hgt'
        (by rw [Finset.card_insert_of_notMem fun h ↦ lt_irrefl i₀ (hgt' i₀ h),
          Set.powersetCard.card_eq]),
      pderiv_primitive_of_ne hji₀,
      pderiv_repr_eq_zero_of_lt q hdω hsupp (hkj₀ ▸ hj₀m) _
        (by simp [t, Set.powersetCard.val_ofCard, Ne.symm hji₀]),
      map_zero, Units.smul_def, zsmul_zero]
  · rw [poincarePrimitive_repr_of_not_forall_lt (by simpa using hgt),
      map_zero, Units.smul_def, zsmul_zero]

/-- On a multi-index `u` with minimum element `i₀`, `d (poincarePrimitive q i₀ ω)` reproduces the
`u`-coordinate of `ω`. -/
private theorem exteriorDeriv_poincarePrimitive_repr_of_mem_of_forall_le
    {u : Set.powersetCard σ (q + 1)} (hi₀u : i₀ ∈ u.1) (hle : ∀ j ∈ u.1, i₀ ≤ j) :
    ((washnitzerBasis σ K).exteriorPower (q + 1)).repr
        (exteriorDeriv K (washnitzerAlgebra σ K) q (poincarePrimitive q i₀ ω)) u =
      ((washnitzerBasis σ K).exteriorPower (q + 1)).repr ω u := by
  rw [washnitzerBasis_exteriorPower_repr_exteriorDeriv, Finset.sum_eq_single ⟨i₀, hi₀u⟩]
  · -- Only the `k = i₀` term survives; since `i₀ = min u`, `basisEraseSign i₀ u.1 = 1`.
    let t : Set.powersetCard σ q := Set.powersetCard.ofCard (s := u.1.erase i₀)
      (by rw [Finset.card_erase_of_mem hi₀u, Set.powersetCard.card_eq u]; rfl)
    have hgt : ∀ j ∈ t.1, i₀ < j := fun j hj ↦ by
      rw [Set.powersetCard.val_ofCard] at hj
      exact lt_of_le_of_ne (hle j (Finset.mem_of_mem_erase hj)) (Finset.ne_of_mem_erase hj).symm
    have hc : (insert i₀ t.1).card = q + 1 := by
      simp [t, Set.powersetCard.val_ofCard, Finset.insert_erase hi₀u, Set.powersetCard.card_eq u]
    have htu : Set.powersetCard.ofCard hc = u :=
      Subtype.ext (by simp [t, Set.powersetCard.val_ofCard, Finset.insert_erase hi₀u])
    have hsign : basisEraseSign i₀ u.1 = 1 := by
      rw [basisEraseSign_eq_neg_one_pow_card_filter_lt,
        Finset.filter_eq_empty_iff.mpr fun j hj ↦ not_lt_of_ge (hle j hj),
        Finset.card_empty, pow_zero]
    rw [poincarePrimitive_repr_of_forall_lt (t := t) hgt hc, pderiv_primitive, htu, hsign,
      Units.smul_def, Units.val_one, one_zsmul]
  · intro k _ hki₀
    rw [poincarePrimitive_repr_of_not_forall_lt (fun hgt ↦ lt_irrefl i₀ <| hgt i₀ <|
      Set.powersetCard.val_ofCard _ ▸
        Finset.mem_erase.mpr ⟨fun h ↦ hki₀ (Subtype.ext h.symm), hi₀u⟩),
      map_zero, Units.smul_def, zsmul_zero]
  · exact fun h ↦ absurd (Finset.mem_attach u.1 ⟨i₀, hi₀u⟩) h

private theorem poincare_step (q : ℕ) (i₀ : σ)
    {ω : ⋀[washnitzerAlgebra σ K]^(q + 1) (Omega K (washnitzerAlgebra σ K))}
    (hdω : exteriorDeriv K (washnitzerAlgebra σ K) (q + 1) ω = 0)
    (hsupp : ∀ s : Set.powersetCard σ (q + 1),
      ((washnitzerBasis σ K).exteriorPower (q + 1)).repr ω s ≠ 0 → ∀ i ∈ s.1, i₀ ≤ i) :
    ∃ η₀ : ⋀[washnitzerAlgebra σ K]^q (Omega K (washnitzerAlgebra σ K)),
      exteriorDeriv K (washnitzerAlgebra σ K) (q + 1)
          (ω - exteriorDeriv K (washnitzerAlgebra σ K) q η₀) = 0 ∧
        ∀ u, ((washnitzerBasis σ K).exteriorPower (q + 1)).repr
            (ω - exteriorDeriv K (washnitzerAlgebra σ K) q η₀) u ≠ 0 → ∀ i ∈ u.1, i₀ < i := by
  refine ⟨poincarePrimitive q i₀ ω,
    by rw [map_sub, hdω, exteriorDeriv_exteriorDeriv_apply, sub_zero], fun u hu i hi ↦ ?_⟩
  by_contra! hle_i₀; apply hu
  rw [← Module.Basis.coord_apply, LinearMap.map_sub, sub_eq_zero, Module.Basis.coord_apply,
    Module.Basis.coord_apply]
  by_cases hex_lt : ∃ j₀ ∈ u.1, j₀ < i₀
  · -- Both `ω` (by `hsupp`) and `d η₀` vanish on multi-indices containing an index `< i₀`.
    have hωu : ((washnitzerBasis σ K).exteriorPower (q + 1)).repr ω u = 0 :=
      by_contra fun hne ↦ hex_lt.elim fun j₀ ⟨hj₀u, hj₀m⟩ ↦ not_le_of_gt hj₀m (hsupp u hne j₀ hj₀u)
    rw [hωu, exteriorDeriv_poincarePrimitive_repr_of_exists_lt hdω hsupp hex_lt]
  · -- Otherwise `i₀ = min u`, so `d η₀` reproduces and cancels the `u`-coordinate of `ω`.
    simp only [not_exists, not_and, not_lt] at hex_lt
    have hi₀u : i₀ ∈ u.1 := le_antisymm hle_i₀ (hex_lt i hi) ▸ hi
    exact (exteriorDeriv_poincarePrimitive_repr_of_mem_of_forall_le hi₀u hex_lt).symm

end PoincareStep

/-- **The Poincaré lemma on a dagger polydisc (Grosse-Klönne)**: every closed `(q + 1)`-form on
`W = K⟨X_σ⟩†` (`[Finite σ]`, `CharZero K`) is exact. -/
theorem exists_exteriorDeriv_eq_of_exteriorDeriv_eq_zero (q : ℕ)
    {ω₀ : ⋀[washnitzerAlgebra σ K]^(q + 1) (Omega K (washnitzerAlgebra σ K))}
    (hω₀ : exteriorDeriv K (washnitzerAlgebra σ K) (q + 1) ω₀ = 0) :
    ∃ η : ⋀[washnitzerAlgebra σ K]^q (Omega K (washnitzerAlgebra σ K)),
      exteriorDeriv K (washnitzerAlgebra σ K) q η = ω₀ := by
  obtain ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin σ
  let : LinearOrder σ := LinearOrder.lift' e e.injective
  let b := washnitzerBasis σ K
  suffices hstep : ∀ (k m : ℕ), m + k = n →
      ∀ (ω : ⋀[washnitzerAlgebra σ K]^(q + 1) (Omega K (washnitzerAlgebra σ K))),
        exteriorDeriv K (washnitzerAlgebra σ K) (q + 1) ω = 0 →
        (∀ s, (b.exteriorPower (q + 1)).repr ω s ≠ 0 → ∀ i ∈ s.1, m ≤ (e i : ℕ)) →
        ∃ η, exteriorDeriv K (washnitzerAlgebra σ K) q η = ω from
    hstep n 0 (Nat.zero_add n) ω₀ hω₀ fun _ _ _ _ ↦ Nat.zero_le _
  intro k; induction k with
  | zero =>
    intro m hm ω _ hsupp; refine ⟨0, ?_⟩
    rw [map_zero]; symm; rw [← (b.exteriorPower (q + 1)).repr.map_eq_zero_iff, Finsupp.ext_iff]
    intro s; by_contra hne
    obtain ⟨i, hi⟩ := Finset.card_pos.mp (by rw [Set.powersetCard.card_eq s]; exact Nat.succ_pos q)
    have := hsupp s hne i hi; have := (e i).2; omega
  | succ k ih =>
    intro m hm ω hdω hsupp
    let i₀ : σ := e.symm ⟨m, by omega⟩
    have hei₀ : (e i₀ : ℕ) = m := by simp [i₀]
    -- Under `LinearOrder.lift' e`, `i₀ ≤ i` is definitionally `e i₀ ≤ e i`.
    obtain ⟨η₀, hdω', hsupp'⟩ := poincare_step q i₀ hdω fun s hs i hi ↦
      Fin.le_def.mpr (hei₀.symm ▸ hsupp s hs i hi)
    obtain ⟨η₁, hη₁⟩ := ih (m + 1) (by omega) _ hdω' fun s hs i hi ↦ by
      have hlt : e i₀ < e i := hsupp' s hs i hi; rw [Fin.lt_def, hei₀] at hlt; omega
    exact ⟨η₀ + η₁, by rw [map_add, hη₁, add_sub_cancel]⟩

/-- In characteristic zero, exact and closed `(q + 1)`-forms on `W = K⟨X_σ⟩†` coincide. -/
theorem exactForms_washnitzer_succ (q : ℕ) :
    exactForms K (washnitzerAlgebra σ K) (q + 1) =
      closedForms K (washnitzerAlgebra σ K) (q + 1) :=
  le_antisymm (exactForms_le_closedForms K _ (q + 1)) fun ω hω ↦
    (exactForms_succ K (washnitzerAlgebra σ K) q).symm ▸ LinearMap.mem_range.mpr
      (exists_exteriorDeriv_eq_of_exteriorDeriv_eq_zero q ((mem_closedForms K _ ω).mp hω))

/-- **Exactness of the overconvergent de Rham complex of a dagger polydisc** in positive degree. -/
theorem exactAt_deRhamComplex_washnitzer_succ (q : ℕ) :
    (deRhamComplex K (washnitzerAlgebra σ K)).ExactAt (q + 1) :=
  (exactAt_deRhamComplex_succ_iff K (washnitzerAlgebra σ K) q).mpr (exactForms_washnitzer_succ q)

/-- **Vanishing of positive-degree overconvergent de Rham cohomology on a dagger polydisc.** -/
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
/-- **Failure of the degree-zero Poincaré lemma in characteristic `p > 0`.** -/
theorem exists_d_eq_zero_and_notMem_range_algebraMap_charP (p : ℕ) [CharP K p] [Fact p.Prime] :
    ∃ f : washnitzerAlgebra (Fin 1) K,
      d K (washnitzerAlgebra (Fin 1) K) f = 0 ∧
        f ∉ Set.range (algebraMap K (washnitzerAlgebra (Fin 1) K)) :=
  ⟨X (Fin 1) K 0 ^ p, d_X_pow_charP p, X_pow_notMem_range_algebraMap 0 (Fact.out : p.Prime).pos⟩

/-- **Failure of the degree-one Poincaré lemma in characteristic `p > 0`**: `X₀ ^ (p - 1) • d X₀`
has no potential `g ∈ K⟨X₀⟩†`. -/
theorem not_exists_d_eq_X_pow_sub_one_smul_d_X_charP (p : ℕ) [CharP K p] [Fact p.Prime] :
    ¬∃ g : washnitzerAlgebra (Fin 1) K,
      d K (washnitzerAlgebra (Fin 1) K) g =
        X (Fin 1) K 0 ^ (p - 1) • d K (washnitzerAlgebra (Fin 1) K) (X (Fin 1) K 0) := by
  rintro ⟨g, hg⟩
  have hrepr := congrArg (fun ω ↦ (washnitzerBasis (Fin 1) K).repr ω 0) hg
  rw [washnitzerBasis_repr_d, LinearEquiv.map_smul, ← washnitzerBasis_apply,
    Module.Basis.repr_self, Finsupp.smul_single_one, Finsupp.single_eq_same] at hrepr
  let e : Fin 1 →₀ ℕ := Finsupp.single 0 (p - 1)
  have hcoeff := congrArg (fun f : washnitzerAlgebra (Fin 1) K ↦ MvPowerSeries.coeff e f.1) hrepr
  have hlhs : MvPowerSeries.coeff e (pderiv (Fin 1) K 0 g).1 = 0 := by
    rw [coe_pderiv, MvPowerSeries.coeff_pderiv, Finsupp.single_eq_same, ← Nat.cast_add_one,
      Nat.sub_add_cancel (Fact.out : p.Prime).pos, CharP.cast_eq_zero, mul_zero]
  rw [hlhs, SubmonoidClass.coe_pow, coe_X, MvPowerSeries.coeff_X_pow, ite_eq_left rfl] at hcoeff
  exact zero_ne_one hcoeff

/-- In characteristic `p > 0`, `deRhamComplex K (K⟨X₀⟩†)` is not exact in degree `1`. -/
theorem not_exactAt_deRhamComplex_washnitzer_one_charP (p : ℕ) [CharP K p] [Fact p.Prime] :
    ¬(deRhamComplex K (washnitzerAlgebra (Fin 1) K)).ExactAt 1 := by
  rw [exactAt_deRhamComplex_succ_iff K (washnitzerAlgebra (Fin 1) K) 0]; intro hex
  let W := washnitzerAlgebra (Fin 1) K
  let ω : ⋀[W]^1 (Omega K W) := (exteriorPower.oneEquiv W _).symm
    (X (Fin 1) K 0 ^ (p - 1) • d K W (X (Fin 1) K 0))
  have hclosed : ω ∈ closedForms K W 1 := by
    have := subsingleton_forms_washnitzer_of_card_lt (σ := Fin 1) (K := K) (q := 2) (by simp)
    rw [mem_closedForms]; exact Subsingleton.elim _ 0
  obtain ⟨f₀, hf₀⟩ := LinearMap.mem_range.mp ((exactForms_succ K W 0) ▸ hex.symm ▸ hclosed)
  obtain ⟨c, rfl⟩ := (exteriorPower.zeroEquiv W _).symm.surjective f₀
  exact not_exists_d_eq_X_pow_sub_one_smul_d_X_charP p
    ⟨c, (exteriorPower.oneEquiv W _).symm.injective (by rwa [exteriorDeriv_zero_symm] at hf₀)⟩

/-- In characteristic `p > 0`, `H¹_dR(K⟨X₀⟩† / K)` is nontrivial. -/
theorem nontrivial_deRhamCohomology_washnitzer_one_charP (p : ℕ) [CharP K p] [Fact p.Prime] :
    Nontrivial (deRhamCohomology K (washnitzerAlgebra (Fin 1) K) 1) :=
  not_subsingleton_iff_nontrivial.mp fun _ ↦
    not_exactAt_deRhamComplex_washnitzer_one_charP (K := K) p <|
      (HomologicalComplex.exactAt_iff_isZero_homology _ 1).mpr
        (ModuleCat.isZero_iff_subsingleton.mpr ‹_›)
end CharP

end TauCeti.Dagger.Omega

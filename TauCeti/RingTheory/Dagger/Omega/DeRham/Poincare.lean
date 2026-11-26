/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Dagger.Omega.DeRham.Basic
public import TauCeti.RingTheory.Dagger.Omega.DeRham.Coordinates
public import TauCeti.RingTheory.Dagger.Poincare

/-!
# The Poincaré lemma on a dagger polydisc

Over a complete ultrametric normed field `K` of characteristic zero, the overconvergent de Rham
complex of `W = K⟨X_σ⟩†` (`[Finite σ]`) has `H⁰_dR(W/K) ≃ₗ[K] K` and is exact in every positive
degree `q + 1`, so `deRhamCohomology K W (q + 1)` is subsingleton.

Using the coordinate formula `washnitzerBasis_exteriorPower_repr_extDerivPow` and the
curl-free characterization `extDerivPow_one_eq_zero_iff_washnitzer`, we deduce degree-one
exactness and unique potentials with prescribed constant coefficient, and establish positive-degree
exactness by induction over `σ` via `washnitzerAlgebra.primitive`. Positive-characteristic
counterexamples live in `TauCeti.RingTheory.Dagger.Omega.DeRham.CharP`.

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

variable (σ K) in
/-- In characteristic zero, closed `0`-forms on `W = K⟨X_σ⟩†` are `K`-linearly equivalent to `K`. -/
noncomputable def closedFormsZeroWashnitzerEquiv :
    K ≃ₗ[K] closedForms K (washnitzerAlgebra σ K) 0 where
  toFun c := ⟨(exteriorPower.zeroEquiv (washnitzerAlgebra σ K) _).symm (algebraMap K _ c), by
    rw [mem_closedForms, extDerivPow_zero_zeroEquiv_symm, (d K _).map_algebraMap,
      LinearEquiv.map_zero]⟩
  map_add' _ _ := Subtype.ext (by simp [map_add])
  map_smul' a _ := Subtype.ext <| by
    simp only [smul_eq_mul, RingHom.id_apply, SetLike.val_smul]
    rw [map_mul, ← Algebra.smul_def, ← IsScalarTower.algebraMap_smul (washnitzerAlgebra σ K) a,
      LinearEquiv.map_smul, IsScalarTower.algebraMap_smul]
  invFun ω := MvPowerSeries.constantCoeff (exteriorPower.zeroEquiv _ _ ω.val).val
  left_inv _ := by simp [MvPowerSeries.algebraMap_apply]
  right_inv ω := Subtype.ext <| by
    dsimp only; set f := exteriorPower.zeroEquiv _ _ ω.val
    have hdf : d K (washnitzerAlgebra σ K) f = 0 := by
      rw [← oneEquiv_extDerivPow_zero, (mem_closedForms K _ ω.val).mp ω.property,
        LinearEquiv.map_zero]
    rw [← (d_eq_zero_iff_eq_algebraMap_constantCoeff f).mp hdf, LinearEquiv.symm_apply_apply]

@[simp] theorem coe_closedFormsZeroWashnitzerEquiv_apply (c : K) :
    (closedFormsZeroWashnitzerEquiv σ K c).val =
      (exteriorPower.zeroEquiv (washnitzerAlgebra σ K) _).symm (algebraMap K _ c) := (rfl)
@[simp] theorem closedFormsZeroWashnitzerEquiv_symm_apply
    (ω : closedForms K (washnitzerAlgebra σ K) 0) :
    (closedFormsZeroWashnitzerEquiv σ K).symm ω =
      MvPowerSeries.constantCoeff (exteriorPower.zeroEquiv _ _ ω.val).val := (rfl)

variable (σ K) in
/-- **Degree-zero de Rham cohomology of a dagger polydisc in characteristic zero**:
`H⁰_dR(K⟨X_σ⟩† / K) ≃ₗ[K] K`. -/
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
      MvPowerSeries.constantCoeff (exteriorPower.zeroEquiv _ _ ω.val).val := by
  rw [← deRhamCohomology.zeroEquivClosedForms_apply, deRhamCohomologyZeroWashnitzerEquiv,
    LinearEquiv.trans_symm, LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply,
    closedFormsZeroWashnitzerEquiv_symm_apply]
end DegreeZero
/-! ### Degree one: exactness and unique potentials -/
section DegreeOne
variable {σ K : Type*} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]

/-- **Degree-one Poincaré lemma on `W = K⟨X_σ⟩†` in characteristic zero**: `ω ∈ Ω¹_{W/K}` is
`d g` for some `g ∈ W` iff `dω = 0`. -/
theorem exists_d_eq_iff_extDerivPow_one_eq_zero_washnitzer [Finite σ] [CharZero K]
    (ω : Omega K (washnitzerAlgebra σ K)) :
    (∃ g : washnitzerAlgebra σ K, d K (washnitzerAlgebra σ K) g = ω) ↔
      extDerivPow K (washnitzerAlgebra σ K) 1
        ((exteriorPower.oneEquiv (washnitzerAlgebra σ K) _).symm ω) = 0 := by
  rw [extDerivPow_one_eq_zero_iff_washnitzer, ← exists_pderiv_eq_iff]
  exact exists_congr fun g ↦ d_eq_iff_forall_pderiv_eq g ω

/-- **Unique potential with prescribed constant coefficient**: for every closed `1`-form `ω` on
`W = K⟨X_σ⟩†` in characteristic zero and every `c : K`, there is a unique `g ∈ W` with
`d g = ω` and constant coefficient `c`. -/
theorem existsUnique_d_eq_of_extDerivPow_one_eq_zero_washnitzer [Finite σ] [CharZero K]
    {ω : Omega K (washnitzerAlgebra σ K)}
    (hω : extDerivPow K (washnitzerAlgebra σ K) 1
      ((exteriorPower.oneEquiv (washnitzerAlgebra σ K) _).symm ω) = 0) (c : K) :
    ∃! g : washnitzerAlgebra σ K,
      d K (washnitzerAlgebra σ K) g = ω ∧ MvPowerSeries.constantCoeff g.val = c := by
  simpa only [d_eq_iff_forall_pderiv_eq] using
    existsUnique_pderiv_eq (fun i ↦ (washnitzerBasis σ K).repr ω i)
      ((extDerivPow_one_eq_zero_iff_washnitzer ω).mp hω) c
end DegreeOne
/-! ### The Poincaré lemma in all positive degrees -/
section AllPositiveDegrees
variable {σ K : Type*} [Finite σ] [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  [CharZero K]

omit [CharZero K] in
private theorem pderiv_repr_eq_zero_of_lt [LinearOrder σ] (q : ℕ) {i₀ k₀ : σ}
    {ω : ⋀[washnitzerAlgebra σ K]^(q + 1) (Omega K (washnitzerAlgebra σ K))}
    (hdω : extDerivPow K (washnitzerAlgebra σ K) (q + 1) ω = 0)
    (hsupp : ∀ s : Set.powersetCard σ (q + 1),
      ((washnitzerBasis σ K).exteriorPower (q + 1)).repr ω s ≠ 0 → ∀ i ∈ s.val, i₀ ≤ i)
    (hk₀ : k₀ < i₀) (s : Set.powersetCard σ (q + 1)) (hkn_s : k₀ ∉ s.val) :
    pderiv σ K k₀ (((washnitzerBasis σ K).exteriorPower (q + 1)).repr ω s) = 0 := by
  let w : Set.powersetCard σ (q + 2) := Set.powersetCard.ofCard (s := insert k₀ s.val)
    (by rw [Finset.card_insert_of_notMem hkn_s, Set.powersetCard.card_eq s])
  have hdw : ((washnitzerBasis σ K).exteriorPower (q + 2)).repr
      (extDerivPow K (washnitzerAlgebra σ K) (q + 1) ω) w = 0 := by
    rw [hdω, LinearEquiv.map_zero, Finsupp.coe_zero, Pi.zero_apply]
  rw [washnitzerBasis_exteriorPower_repr_extDerivPow] at hdw
  have hkw : k₀ ∈ w.val := Finset.mem_insert_self k₀ s.val
  rw [Finset.sum_eq_single ⟨k₀, hkw⟩] at hdw
  · have hwk : Set.powersetCard.ofCard (s := w.val.erase k₀)
        (by rw [Finset.card_erase_of_mem hkw, Set.powersetCard.card_eq w]; rfl) = s :=
      Subtype.ext (Finset.erase_insert hkn_s)
    rw [hwk] at hdw
    have hinv := congrArg ((basisEraseSign k₀ w.val)⁻¹ • ·) hdw
    rwa [inv_smul_smul, Units.smul_def, zsmul_zero] at hinv
  · intro l _ hlk
    have hzero (hc : (w.val.erase l.val).card = q + 1) :
        ((washnitzerBasis σ K).exteriorPower (q + 1)).repr ω (Set.powersetCard.ofCard hc) = 0 :=
      by_contra fun hne ↦ not_le_of_gt hk₀ <| hsupp _ hne k₀ <| Set.powersetCard.val_ofCard _ ▸
        Finset.mem_erase.mpr ⟨fun h ↦ hlk (Subtype.ext h.symm), hkw⟩
    rw [hzero, map_zero, Units.smul_def, zsmul_zero]
  · exact fun h ↦ absurd (Finset.mem_attach w.val ⟨k₀, hkw⟩) h

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
    if hgt : ∀ j ∈ t.val, i₀ < j then
      primitive σ K i₀ (((washnitzerBasis σ K).exteriorPower (q + 1)).repr ω
        (Set.powersetCard.ofCard (s := insert i₀ t.val)
          (by rw [Finset.card_insert_of_notMem fun h ↦ lt_irrefl i₀ (hgt i₀ h),
            Set.powersetCard.card_eq t])))
    else 0

private theorem poincarePrimitive_repr_of_forall_lt {t : Set.powersetCard σ q}
    (hgt : ∀ j ∈ t.val, i₀ < j) (hc : (insert i₀ t.val).card = q + 1) :
    ((washnitzerBasis σ K).exteriorPower q).repr (poincarePrimitive q i₀ ω) t =
      primitive σ K i₀ (((washnitzerBasis σ K).exteriorPower (q + 1)).repr ω
        (Set.powersetCard.ofCard hc)) := by
  simp only [poincarePrimitive, LinearEquiv.apply_symm_apply, Finsupp.coe_equivFunOnFinite_symm,
    dite_eq_left hgt]

private theorem poincarePrimitive_repr_of_not_forall_lt {t : Set.powersetCard σ q}
    (hnot : ¬∀ j ∈ t.val, i₀ < j) :
    ((washnitzerBasis σ K).exteriorPower q).repr (poincarePrimitive q i₀ ω) t = 0 := by
  simp only [poincarePrimitive, LinearEquiv.apply_symm_apply, Finsupp.coe_equivFunOnFinite_symm,
    dite_eq_right hnot]

/-- For a closed form supported on indices `≥ i₀`, `d (poincarePrimitive q i₀ ω)` vanishes on
every multi-index containing an index strictly below `i₀`. -/
private theorem extDerivPow_poincarePrimitive_repr_of_exists_lt
    (hdω : extDerivPow K (washnitzerAlgebra σ K) (q + 1) ω = 0)
    (hsupp : ∀ s : Set.powersetCard σ (q + 1),
      ((washnitzerBasis σ K).exteriorPower (q + 1)).repr ω s ≠ 0 → ∀ i ∈ s.val, i₀ ≤ i)
    {u : Set.powersetCard σ (q + 1)} (hex_lt : ∃ j₀ ∈ u.val, j₀ < i₀) :
    ((washnitzerBasis σ K).exteriorPower (q + 1)).repr
        (extDerivPow K (washnitzerAlgebra σ K) q (poincarePrimitive q i₀ ω)) u = 0 := by
  obtain ⟨j₀, hj₀u, hj₀m⟩ := hex_lt
  rw [washnitzerBasis_exteriorPower_repr_extDerivPow]
  refine Finset.sum_eq_zero fun k _ ↦ ?_
  by_cases hgt : ∀ j ∈ u.val.erase k.val, i₀ < j
  · -- Erasing `k` leaves indices `> i₀`, so `k = j₀ < i₀` and `∂_k` commutes past `primitive i₀`.
    have hkj₀ : k.val = j₀ := by_contra fun hne ↦
      asymm hj₀m (hgt j₀ (Finset.mem_erase.mpr ⟨Ne.symm hne, hj₀u⟩))
    have hji₀ : i₀ ≠ k.val := ne_of_gt (hkj₀ ▸ hj₀m)
    let t : Set.powersetCard σ q := Set.powersetCard.ofCard (s := u.val.erase k.val)
      (by rw [Finset.card_erase_of_mem k.property, Set.powersetCard.card_eq u]; rfl)
    have hgt' : ∀ j ∈ t.val, i₀ < j := by simpa only [t, Set.powersetCard.val_ofCard] using hgt
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
private theorem extDerivPow_poincarePrimitive_repr_of_mem_of_forall_le
    {u : Set.powersetCard σ (q + 1)} (hi₀u : i₀ ∈ u.val) (hle : ∀ j ∈ u.val, i₀ ≤ j) :
    ((washnitzerBasis σ K).exteriorPower (q + 1)).repr
        (extDerivPow K (washnitzerAlgebra σ K) q (poincarePrimitive q i₀ ω)) u =
      ((washnitzerBasis σ K).exteriorPower (q + 1)).repr ω u := by
  rw [washnitzerBasis_exteriorPower_repr_extDerivPow, Finset.sum_eq_single ⟨i₀, hi₀u⟩]
  · -- Only the `k = i₀` term survives; since `i₀ = min u`, `basisEraseSign i₀ u.val = 1`.
    let t : Set.powersetCard σ q := Set.powersetCard.ofCard (s := u.val.erase i₀)
      (by rw [Finset.card_erase_of_mem hi₀u, Set.powersetCard.card_eq u]; rfl)
    have hgt : ∀ j ∈ t.val, i₀ < j := fun j hj ↦ by
      rw [Set.powersetCard.val_ofCard] at hj
      exact lt_of_le_of_ne (hle j (Finset.mem_of_mem_erase hj)) (Finset.ne_of_mem_erase hj).symm
    have hc : (insert i₀ t.val).card = q + 1 := by
      simp [t, Set.powersetCard.val_ofCard, Finset.insert_erase hi₀u, Set.powersetCard.card_eq u]
    have htu : Set.powersetCard.ofCard hc = u :=
      Subtype.ext (by simp [t, Set.powersetCard.val_ofCard, Finset.insert_erase hi₀u])
    have hsign : basisEraseSign i₀ u.val = 1 := by
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
  · exact fun h ↦ absurd (Finset.mem_attach u.val ⟨i₀, hi₀u⟩) h

private theorem poincare_step (q : ℕ) (i₀ : σ)
    {ω : ⋀[washnitzerAlgebra σ K]^(q + 1) (Omega K (washnitzerAlgebra σ K))}
    (hdω : extDerivPow K (washnitzerAlgebra σ K) (q + 1) ω = 0)
    (hsupp : ∀ s : Set.powersetCard σ (q + 1),
      ((washnitzerBasis σ K).exteriorPower (q + 1)).repr ω s ≠ 0 → ∀ i ∈ s.val, i₀ ≤ i) :
    ∃ η₀ : ⋀[washnitzerAlgebra σ K]^q (Omega K (washnitzerAlgebra σ K)),
      extDerivPow K (washnitzerAlgebra σ K) (q + 1)
          (ω - extDerivPow K (washnitzerAlgebra σ K) q η₀) = 0 ∧
        ∀ u, ((washnitzerBasis σ K).exteriorPower (q + 1)).repr
            (ω - extDerivPow K (washnitzerAlgebra σ K) q η₀) u ≠ 0 →
              ∀ i ∈ u.val, i₀ < i := by
  refine ⟨poincarePrimitive q i₀ ω,
    by rw [map_sub, hdω, extDerivPow_extDerivPow_apply, sub_zero], fun u hu i hi ↦ ?_⟩
  by_contra! hle_i₀; apply hu
  rw [← Module.Basis.coord_apply, LinearMap.map_sub, sub_eq_zero, Module.Basis.coord_apply,
    Module.Basis.coord_apply]
  by_cases hex_lt : ∃ j₀ ∈ u.val, j₀ < i₀
  · -- Both `ω` (by `hsupp`) and `d η₀` vanish on multi-indices containing an index `< i₀`.
    have hωu : ((washnitzerBasis σ K).exteriorPower (q + 1)).repr ω u = 0 :=
      by_contra fun hne ↦ hex_lt.elim fun j₀ ⟨hj₀u, hj₀m⟩ ↦ not_le_of_gt hj₀m (hsupp u hne j₀ hj₀u)
    rw [hωu, extDerivPow_poincarePrimitive_repr_of_exists_lt hdω hsupp hex_lt]
  · -- Otherwise `i₀ = min u`, so `d η₀` reproduces and cancels the `u`-coordinate of `ω`.
    simp only [not_exists, not_and, not_lt] at hex_lt
    have hi₀u : i₀ ∈ u.val := le_antisymm hle_i₀ (hex_lt i hi) ▸ hi
    exact (extDerivPow_poincarePrimitive_repr_of_mem_of_forall_le hi₀u hex_lt).symm
end PoincareStep
/-- **The Poincaré lemma on a dagger polydisc (Grosse-Klönne)**: every closed `(q + 1)`-form on
`W = K⟨X_σ⟩†` (`[Finite σ]`, `CharZero K`) is exact. -/
theorem exists_extDerivPow_eq_of_extDerivPow_eq_zero_washnitzer (q : ℕ)
    {ω₀ : ⋀[washnitzerAlgebra σ K]^(q + 1) (Omega K (washnitzerAlgebra σ K))}
    (hω₀ : extDerivPow K (washnitzerAlgebra σ K) (q + 1) ω₀ = 0) :
    ∃ η : ⋀[washnitzerAlgebra σ K]^q (Omega K (washnitzerAlgebra σ K)),
      extDerivPow K (washnitzerAlgebra σ K) q η = ω₀ := by
  obtain ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin σ
  let : LinearOrder σ := LinearOrder.lift' e e.injective
  let b := washnitzerBasis σ K
  suffices hstep : ∀ (k m : ℕ), m + k = n →
      ∀ (ω : ⋀[washnitzerAlgebra σ K]^(q + 1) (Omega K (washnitzerAlgebra σ K))),
        extDerivPow K (washnitzerAlgebra σ K) (q + 1) ω = 0 →
        (∀ s, (b.exteriorPower (q + 1)).repr ω s ≠ 0 → ∀ i ∈ s.val, m ≤ (e i : ℕ)) →
        ∃ η, extDerivPow K (washnitzerAlgebra σ K) q η = ω from
    hstep n 0 (Nat.zero_add n) ω₀ hω₀ fun _ _ _ _ ↦ Nat.zero_le _
  intro k; induction k with
  | zero =>
    intro m hm ω _ hsupp; refine ⟨0, ?_⟩
    rw [map_zero]; symm; rw [← (b.exteriorPower (q + 1)).repr.map_eq_zero_iff, Finsupp.ext_iff]
    intro s; by_contra hne
    obtain ⟨i, hi⟩ := Finset.card_pos.mp (by rw [Set.powersetCard.card_eq s]; exact Nat.succ_pos q)
    have := hsupp s hne i hi; have := (e i).isLt; omega
  | succ k ih =>
    intro m hm ω hdω hsupp; let i₀ : σ := e.symm ⟨m, by omega⟩
    have hei₀ : (e i₀ : ℕ) = m := by simp [i₀]
    -- Under `LinearOrder.lift' e`, `i₀ ≤ i` is definitionally `e i₀ ≤ e i`.
    obtain ⟨η₀, hdω', hsupp'⟩ := poincare_step q i₀ hdω fun s hs i hi ↦
      Fin.le_def.mpr (hei₀.symm ▸ hsupp s hs i hi)
    obtain ⟨η₁, hη₁⟩ := ih (m + 1) (by omega) _ hdω' fun s hs i hi ↦ by
      have hlt : e i₀ < e i := hsupp' s hs i hi; rw [Fin.lt_def, hei₀] at hlt; omega
    exact ⟨η₀ + η₁, by rw [map_add, hη₁, add_sub_cancel]⟩

/-- In characteristic zero, exact and closed `(q + 1)`-forms on `W = K⟨X_σ⟩†` coincide. -/
theorem exactForms_washnitzer_succ (q : ℕ) :
    exactForms K (washnitzerAlgebra σ K) (q + 1) = closedForms K (washnitzerAlgebra σ K) (q + 1) :=
  le_antisymm (exactForms_le_closedForms K _ (q + 1)) fun ω hω ↦
    (exactForms_succ K (washnitzerAlgebra σ K) q).symm ▸ LinearMap.mem_range.mpr
      (exists_extDerivPow_eq_of_extDerivPow_eq_zero_washnitzer q
        ((mem_closedForms K _ ω).mp hω))

/-- **Exactness of the overconvergent de Rham complex of a dagger polydisc** in positive degree
in characteristic zero. -/
theorem exactAt_deRhamComplex_washnitzer_succ (q : ℕ) :
    (deRhamComplex K (washnitzerAlgebra σ K)).ExactAt (q + 1) :=
  (exactAt_deRhamComplex_succ_iff K (washnitzerAlgebra σ K) q).mpr (exactForms_washnitzer_succ q)

/-- **Vanishing of positive-degree overconvergent de Rham cohomology on a dagger polydisc in
characteristic zero.** -/
instance instSubsingletonDeRhamCohomologyWashnitzerSucc (q : ℕ) :
    Subsingleton (deRhamCohomology K (washnitzerAlgebra σ K) (q + 1)) :=
  subsingleton_deRhamCohomology_of_closedForms_le_exactForms K _ (exactForms_washnitzer_succ q).ge
end AllPositiveDegrees

end TauCeti.Dagger.Omega

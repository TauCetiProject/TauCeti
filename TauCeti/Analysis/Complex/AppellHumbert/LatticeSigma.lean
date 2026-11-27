/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.AppellHumbert.ComplexLattice
public import TauCeti.Analysis.Complex.AppellHumbert.Positive
public import Mathlib.Analysis.SpecialFunctions.Elliptic.Weierstrass
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.GroupTheory.IndexNSmul
import TauCeti.Analysis.Complex.AppellHumbert.BasePoints
import TauCeti.Analysis.Complex.AppellHumbert.Frobenius
import TauCeti.Analysis.SpecialFunctions.Elliptic.Period.Pair

/-!
# Theta functions of one variable and the sigma function of a lattice

Let `Λ ⊂ ℂ` be a lattice with Hermitian form `H` and Riemann form `E = Im H`
(`ZLattice.hermitianForm`), and let `χ` be an Appell–Humbert multiplier for `H`. The theta
functions of degree `m` for `χ` are the elements of `Th_m(Λ, χ)`, the theta space of the datum
`m • ZLattice.appellHumbertData Λ χ hχ`.

* **Dimension.** The lattice is its own dual for `E`
  (`ZLattice.mem_of_forall_im_hermitianForm_eq_intCast`), so the dual of `Λ` for `m E` is
  `m⁻¹ Λ` (`ZLattice.mem_dualSubmodule_riemannForm_nsmul_appellHumbertData_iff`), of index `m²`.
  Frobenius' dimension formula then gives `dim Th_m(Λ, χ) = m` for `m ≥ 1`
  (`ZLattice.finrank_thetaSpace_nsmul_appellHumbertData`).
* **Zeros.** For a period pair `L` with lattice `Λ` and a nonzero `f ∈ Th_1(Λ, χ)` with
  `f (0) = 0`, the function `℘ f²`, extended to `Λ` by `f′ (l)²` (`PeriodPair.weierstrassPMulSq`),
  is entire and lies in `Th_2(Λ, χ)`; with `f²` it spans that space of dimension two
  (`PeriodPair.thetaSpace_two_eq_span_weierstrassPMulSq`). Since `Th_2(Λ, χ)` has no base
  point, the zeros of `f` are exactly the points of `Λ`
  (`PeriodPair.apply_eq_zero_iff_mem_lattice_of_mem_thetaSpace`) and they are simple
  (`PeriodPair.deriv_ne_zero_of_mem_thetaSpace`).
* **The sigma function.** For the sign `ε` (`ZLattice.sigmaSign`), there is an element of
  `Th_1(Λ, ε)` with derivative `1` at `0`
  (`PeriodPair.exists_mem_thetaSpace_sigmaSignData_deriv_eq_one`), and only one
  (`PeriodPair.eq_of_mem_thetaSpace_sigmaSignData_of_deriv_eq_one`): the sigma function `σ_Λ` of
  `Λ`. Like every element of `Th_1(Λ, ε)` it is odd
  (`PeriodPair.apply_neg_of_mem_thetaSpace_sigmaSignData`), and it
  satisfies the **addition formula** `σ(u + v) σ(u - v) = (℘(v) - ℘(u)) σ(u)² σ(v)²`
  (`PeriodPair.apply_add_mul_apply_sub_of_mem_thetaSpace_sigmaSignData`) and the **duplication
  formula** `σ(2z) = -℘′(z) σ(z)⁴` (`PeriodPair.apply_two_mul_of_mem_thetaSpace_sigmaSignData`)
  for `u, v ∉ Λ` and all `z`.

The results on `σ_Λ` are stated for an arbitrary `f ∈ Th_1(Λ, ε)` with `f′ (0) = 1`, which by
uniqueness is `σ_Λ`; this file does not name that function. Classically `σ_Λ (z)` is
`σ_W (z) exp (-s₂ z² / 2)` for the Weierstrass product `σ_W` (`PeriodPair.weierstrassSigma`) and a
constant `s₂` given by Legendre's relation; nothing here uses that description.

## Main results

* `ZLattice.isPositive_appellHumbertData`, `ZLattice.isPositive_sigmaSignData`: the Riemann
  forms of `(H, χ)` and `(H, ε)` are positive.
* `ZLattice.finrank_thetaSpace_nsmul_appellHumbertData`: `dim Th_m(Λ, χ) = m` for `m ≠ 0`.
* `PeriodPair.weierstrassPMulSq_mem_thetaSpace`,
  `PeriodPair.thetaSpace_two_eq_span_weierstrassPMulSq`: `Th_2(Λ, χ)` is spanned by `℘ f²`
  and `f²`.
* `PeriodPair.apply_eq_zero_iff_mem_lattice_of_mem_thetaSpace`,
  `PeriodPair.deriv_ne_zero_of_mem_thetaSpace`: the zeros of `f` are the points of `Λ`, all
  simple.
* `PeriodPair.exists_mem_thetaSpace_sigmaSignData_deriv_eq_one`,
  `PeriodPair.eq_of_mem_thetaSpace_sigmaSignData_of_deriv_eq_one`,
  `PeriodPair.apply_neg_of_mem_thetaSpace_sigmaSignData`: existence, uniqueness and oddness of
  the sigma function.
* `PeriodPair.apply_add_mul_apply_sub_of_mem_thetaSpace_sigmaSignData`,
  `PeriodPair.apply_two_mul_of_mem_thetaSpace_sigmaSignData`: addition and duplication.

## Provenance

Adapted from `New.addSubgroupOf_dualLattice_nsmul_eq_range`,
`New.IsAppellHumbert.finrank_thetaSpace_nsmul`, `PeriodPair.weierstrassPMulSq`,
`New.differentiable_weierstrassPMulSq`, `New.weierstrassPMulSq_mem_thetaSpace`,
`New.linearIndependent_sq_weierstrassPMulSq`, `New.IsAppellHumbert.thetaSpace_two_eq_span_pair`,
`New.IsAppellHumbert.theta_eq_zero_iff_mem_lattice`, `New.IsAppellHumbert.deriv_theta_ne_zero`,
`New.not_even_of_mem_thetaSpace`, `New.exists_odd_mem_thetaSpace_deriv_eq_one`,
`New.sigma_add_mul_sigma_sub_mem_thetaSpace`, `New.sigma_add_mul_sigma_sub` and
`New.sigma_two_mul` (file `src/Lib/CM/Sigma/Basic.lean`) in
grh-lean (https://github.com/lsernau/grh-lean, commit `72fead1`, Apache 2.0, Copyright 2026
Anthropic, PBC). There the sigma function is a chosen odd normalised theta function; here
existence, uniqueness and the formulas are stated for every normalised theta function, the data
are the Appell–Humbert data of `TauCeti.AppellHumbertData`, the dimension formula comes from
Tau Ceti's `TauCeti.AppellHumbertData.IsPositive.finrank_thetaSpace_sq`, the absence of base
points from `TauCeti.AppellHumbertData.exists_mem_thetaSpace_nsmul_apply_ne_zero`, and the
products `f (z + v) f (z - v)` from
`TauCeti.AppellHumbertData.apply_add_mul_apply_sub_mem_thetaSpace_two_nsmul`.

## References

* A. Weil, *Elliptic Functions according to Eisenstein and Kronecker*, Springer, 1976.
* J. H. Silverman, *The Arithmetic of Elliptic Curves*, 2nd ed., GTM 106, Springer, 2009, VI;
  *Advanced Topics in the Arithmetic of Elliptic Curves*, GTM 151, Springer, 1994, I.5.
* C. Birkenhake, H. Lange, *Complex Abelian Varieties*, 2nd ed., Springer, 2004, Chapter 3.
-/

public section

open Complex Module Set Submodule TauCeti ZLattice
open scoped Real ComplexConjugate

namespace ZLattice

/-! ### Positivity -/

variable {Λ : Submodule ℤ ℂ} [DiscreteTopology Λ] [IsZLattice ℝ Λ]

variable {χ : Λ → Circle} (hχ : IsAppellHumbertMultiplier Λ χ)

/-- The Riemann form `E = Im H` of the Appell–Humbert datum `(H, χ)` of a lattice is positive. -/
theorem isPositive_appellHumbertData : (appellHumbertData Λ χ hχ).IsPositive :=
  (AppellHumbertData.isPositive_iff _).mpr fun _ hu ↦ by
    simpa [smul_eq_mul] using riemannForm_appellHumbertData_I_mul_self_pos hχ hu

variable (Λ) in
/-- The Riemann form of the datum `(H, ε)` of a lattice is positive. -/
theorem isPositive_sigmaSignData : (sigmaSignData Λ).IsPositive := by
  rw [sigmaSignData_def]
  exact isPositive_appellHumbertData _

/-! ### The dimension of the theta spaces -/

/-- The Riemann form of `m • (H, χ)` is `E (m x, y)`. -/
private theorem riemannForm_nsmul_appellHumbertData (m : ℕ) (x y : ℂ) :
    (m • appellHumbertData Λ χ hχ).riemannForm x y = (hermitianForm Λ ((m : ℂ) * x) y).im := by
  rw [AppellHumbertData.riemannForm_nsmul, LinearMap.smul_apply, LinearMap.smul_apply,
    riemannForm_appellHumbertData_apply, im_hermitianForm, nsmul_eq_mul, mul_assoc,
    ← ofReal_natCast, im_ofReal_mul, mul_div_assoc]

/-- **The dual lattice of degree `m`**: the dual of `Λ` for the Riemann form of `m • (H, χ)` is
`{x | m x ∈ Λ}`, that is `m⁻¹ Λ` for `m ≠ 0`. -/
theorem mem_dualSubmodule_riemannForm_nsmul_appellHumbertData_iff {m : ℕ} {x : ℂ} :
    x ∈ (m • appellHumbertData Λ χ hχ).riemannForm.dualSubmodule Λ ↔ (m : ℂ) * x ∈ Λ := by
  simp only [LinearMap.BilinForm.mem_dualSubmodule, Submodule.mem_one,
    riemannForm_nsmul_appellHumbertData, algebraMap_int_eq, eq_intCast]
  refine ⟨fun h ↦ mem_of_forall_im_hermitianForm_eq_intCast fun l hl ↦ ?_, fun h l hl ↦ ?_⟩
  · obtain ⟨n, hn⟩ := h l hl
    exact ⟨n, hn.symm⟩
  · obtain ⟨n, hn⟩ := exists_im_hermitianForm_eq_intCast Λ ⟨_, h⟩ ⟨l, hl⟩
    exact ⟨n, hn.symm⟩

/-- **The dimension of the theta spaces in one variable**: for `m ≠ 0`, the theta functions of
degree `m` for an Appell–Humbert multiplier `χ` form a space of dimension `m`. This is Frobenius'
dimension formula `(dim Θ)² = [Λ^⊥ : Λ]` for `m • (H, χ)`, whose dual lattice is `m⁻¹ Λ`. -/
theorem finrank_thetaSpace_nsmul_appellHumbertData {m : ℕ} (hm : m ≠ 0) :
    finrank ℂ (m • appellHumbertData Λ χ hχ).thetaSpace = m := by
  set D := m • appellHumbertData Λ χ hχ
  have hD : D.IsPositive := (isPositive_appellHumbertData hχ).nsmul hm
  set Λ' := D.riemannForm.dualSubmodule Λ
  have hmem (x : Λ') : (m : ℂ) * x ∈ Λ :=
    (mem_dualSubmodule_riemannForm_nsmul_appellHumbertData_iff hχ).mp x.property
  have hm' : (m : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hm
  -- Multiplication by `m` is an isomorphism `Λ' ≃ Λ`, so `Λ'` is free of rank two.
  let e : Λ' ≃ₗ[ℤ] Λ := LinearEquiv.ofBijective
    { toFun x := ⟨(m : ℂ) * x, hmem x⟩
      map_add' x y := by ext; simp [mul_add]
      map_smul' c x := by ext; simp [mul_left_comm] }
    ⟨fun x y hxy ↦ Subtype.ext (mul_left_cancel₀ hm' (congrArg Subtype.val hxy)), fun y ↦
      ⟨⟨(m : ℂ)⁻¹ * y, (mem_dualSubmodule_riemannForm_nsmul_appellHumbertData_iff hχ).mpr
        (by simp [mul_inv_cancel_left₀ hm'])⟩,
        Subtype.ext (mul_inv_cancel_left₀ hm' _)⟩⟩
  have : Module.Free ℤ Λ' := Module.Free.of_equiv e.symm
  have : Module.Finite ℤ Λ' := Module.Finite.equiv e.symm
  have hrank : finrank ℤ Λ' = 2 := by
    rw [e.finrank_eq, ZLattice.rank ℝ Λ, Complex.finrank_real_complex]
  -- `Λ = m Λ'` inside `Λ'`.
  have hsub : Λ.toAddSubgroup.addSubgroupOf Λ'.toAddSubgroup =
      (nsmulAddMonoidHom (α := Λ') m).range := by
    ext x
    simp only [AddSubgroup.mem_addSubgroupOf, AddMonoidHom.mem_range, nsmulAddMonoidHom_apply,
      Submodule.mem_toAddSubgroup]
    refine ⟨fun hx ↦ ⟨e.symm ⟨x, hx⟩, Subtype.ext ?_⟩, ?_⟩
    · have h : (m : ℂ) * (e.symm ⟨x, hx⟩ : ℂ) = x :=
        congrArg Subtype.val (e.apply_symm_apply ⟨x, hx⟩)
      rw [Submodule.coe_smul_of_tower, nsmul_eq_mul]
      exact h
    · rintro ⟨y, rfl⟩
      simpa [nsmul_eq_mul] using hmem y
  have hidx : (nsmulAddMonoidHom (α := Λ') m).range.index = m ^ 2 := by
    rw [AddSubgroup.index_range_nsmul, hrank]
  exact Nat.pow_left_injective two_ne_zero <| hD.finrank_thetaSpace_sq.trans <| by
    rw [AddSubgroup.relIndex, hsub]
    exact hidx

end ZLattice

namespace PeriodPair

variable (L : PeriodPair)

/-! ### The function `℘ f²` -/

open Classical in
/-- The function `℘ f²` for the lattice of `L`, extended to the lattice by the value `f′ (l)²`.
For an entire `f` vanishing on the lattice it is entire
(`PeriodPair.differentiable_weierstrassPMulSq`). -/
noncomputable def weierstrassPMulSq (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  if z ∈ L.lattice then deriv f z ^ 2 else ℘[L] z * f z ^ 2

variable {L}

/-- On the lattice, `℘ f²` takes the value `f′ (l)²`. -/
theorem weierstrassPMulSq_of_mem {f : ℂ → ℂ} {z : ℂ} (hz : z ∈ L.lattice) :
    L.weierstrassPMulSq f z = deriv f z ^ 2 := by
  simp [weierstrassPMulSq, hz]

/-- Off the lattice, `℘ f²` is the product of `℘` and `f²`. -/
theorem weierstrassPMulSq_of_notMem {f : ℂ → ℂ} {z : ℂ} (hz : z ∉ L.lattice) :
    L.weierstrassPMulSq f z = ℘[L] z * f z ^ 2 := by
  simp [weierstrassPMulSq, hz]

/-- For an entire `f` vanishing on the lattice, `℘ f²`, extended to the lattice by `f′ (l)²`, is
entire. -/
theorem differentiable_weierstrassPMulSq {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (h_zero : ∀ l ∈ L.lattice, f l = 0) : Differentiable ℂ (L.weierstrassPMulSq f) := by
  intro z
  by_cases hz : z ∈ L.lattice
  · -- Near `z`, `℘ (w) = 1 / (w - z)² - 1 / z² + ℘_z (w)` with `℘_z` analytic at `z`, and
    -- `f (w) / (w - z)` is the slope `dslope f z w`.
    have h_slope : AnalyticAt ℂ (dslope f z) z :=
      let ⟨_, hp⟩ := Differentiable.analyticAt hf z
      hp.dslope_fslope.analyticAt
    have h_except : AnalyticAt ℂ ℘[L - z] z := L.analyticAt_weierstrassPExcept z
    have near : L.weierstrassPMulSq f =ᶠ[nhds z]
        dslope f z ^ 2 - (z⁻¹ • f) ^ 2 + ℘[L - z] * f ^ 2 := by
      filter_upwards [L.compl_lattice_sdiff_singleton_mem_nhds z] with w hw
      obtain rfl | hwz := eq_or_ne w z
      · simp [weierstrassPMulSq_of_mem hz, h_zero w hz]
      · have hw' : w ∉ L.lattice := fun hw_mem ↦ hw ⟨hw_mem, hwz⟩
        have h_eq : dslope f z w = f w / (w - z) := by
          simp [dslope_of_ne f hwz, slope_def_field, h_zero z hz]
        simp only [weierstrassPMulSq_of_notMem hw', Pi.add_apply, Pi.sub_apply, Pi.pow_apply,
          Pi.mul_apply, Pi.smul_apply, smul_eq_mul, h_eq, ← L.weierstrassPExcept_add ⟨z, hz⟩ w]
        have : w - z ≠ 0 := sub_ne_zero.mpr hwz
        field_simp
        ring
    have hfz := Differentiable.analyticAt hf z
    exact ((h_slope.pow 2).sub ((analyticAt_const.smul hfz).pow 2) |>.add
      (h_except.mul (hfz.pow 2))).differentiableAt.congr_of_eventuallyEq near
  · have h_wp : AnalyticAt ℂ ℘[L] z := L.analyticOnNhd_weierstrassP z hz
    have near : L.weierstrassPMulSq f =ᶠ[nhds z] ℘[L] * f ^ 2 := by
      filter_upwards [L.isClosed_lattice.isOpen_compl.mem_nhds hz] with w hw
      exact weierstrassPMulSq_of_notMem hw
    exact (h_wp.mul ((Differentiable.analyticAt hf z).pow 2)).differentiableAt.congr_of_eventuallyEq
      near

/-! ### Theta functions vanishing at the origin -/

variable {χ : L.lattice → Circle} {hχ : IsAppellHumbertMultiplier L.lattice χ} {f : ℂ → ℂ}

/-- **`℘ f²` is a theta function of degree two**: for a theta function `f` of an Appell–Humbert
datum `D` on the lattice with `f (0) = 0`, the function `℘ f²`, extended to the lattice by
`f′ (l)²`, is a theta function of `2 • D`. In particular `f ∈ Th_1(Λ, χ)` gives `℘ f² ∈ Th_2(Λ, χ)`.
-/
theorem weierstrassPMulSq_mem_thetaSpace {D : AppellHumbertData L.lattice}
    (hf : f ∈ D.thetaSpace) (hf0 : f 0 = 0) :
    L.weierstrassPMulSq f ∈ (2 • D).thetaSpace := by
  have entire : Differentiable ℂ (L.weierstrassPMulSq f) :=
    differentiable_weierstrassPMulSq (AppellHumbertData.differentiable_of_mem_thetaSpace hf)
      fun _ hl ↦ AppellHumbertData.apply_coe_eq_zero_of_mem_thetaSpace hf hf0 ⟨_, hl⟩
  refine (AppellHumbertData.mem_thetaSpace_iff _).mpr ⟨entire, fun l ↦ ?_⟩
  have h_factor : Differentiable ℂ fun z ↦ (2 • D).factor l z := by
    simp only [AppellHumbertData.factor_def]
    fun_prop
  -- Both sides are entire in `z`, so it suffices to compare them off the lattice, where this is
  -- the square of the functional equation of `f` times the periodic `℘`.
  refine congrFun (L.eq_of_eqOn_compl_lattice
    (entire.comp (differentiable_id.add_const _)).continuous (h_factor.mul entire).continuous
    fun z hz ↦ ?_)
  have hzl : z + l ∉ L.lattice := by rwa [add_mem_cancel_right l.property]
  simp only [weierstrassPMulSq_of_notMem hzl,
    weierstrassPMulSq_of_notMem hz, L.weierstrassP_add_coe,
    AppellHumbertData.apply_add_of_mem_thetaSpace hf, AppellHumbertData.factor_nsmul]
  ring

/-- For an entire `f ≠ 0`, the functions `f²` and `℘ f²` (extended to the lattice by `f′ (l)²`)
are linearly independent. -/
theorem linearIndependent_sq_weierstrassPMulSq (hf : Differentiable ℂ f) (hf_ne : f ≠ 0) :
    LinearIndependent ℂ ![f ^ 2, L.weierstrassPMulSq f] := by
  -- If `℘ f² = c f²`, then `f` vanishes off the lattice wherever `℘ ≠ c`, so near the pole `0`;
  -- hence `f = 0`.
  rw [LinearIndependent.pair_iff' (pow_ne_zero 2 hf_ne)]
  intro c hc
  have vanishes (z : ℂ) (hz : z ∉ L.lattice) (hz_ne : ℘[L] z ≠ c) : f z = 0 := by
    have := congrFun hc z
    simp only [Pi.smul_apply, Pi.pow_apply, smul_eq_mul, weierstrassPMulSq_of_notMem hz] at this
    exact pow_eq_zero_iff two_ne_zero |>.mp
      ((mul_eq_mul_right_iff.mp this).resolve_left (Ne.symm hz_ne))
  have pole : Filter.Tendsto ℘[L] (nhdsWithin 0 {0}ᶜ) (Bornology.cobounded ℂ) :=
    tendsto_cobounded_of_meromorphicOrderAt_neg
      (by simp +decide [L.order_weierstrassP 0 (zero_mem _)])
  have frequently_zero : ∃ᶠ z in nhdsWithin 0 {0}ᶜ, f z = 0 :=
    ((pole.eventually_ne_cobounded c).and (L.eventually_notMem_lattice 0)).frequently.mono
      fun z hz ↦ vanishes z hz.2 hz.1
  exact hf_ne ((Differentiable.contDiff hf).analyticOnNhd.eq_of_frequently_eq analyticOnNhd_const
    frequently_zero)

/-- **The theta functions of degree two**: for a nonzero `f ∈ Th_1(Λ, χ)` with `f (0) = 0`,
`Th_2(Λ, χ)` is spanned by `℘ f²` (extended to the lattice by `f′ (l)²`) and `f²`. -/
theorem thetaSpace_two_eq_span_weierstrassPMulSq
    (hf : f ∈ (appellHumbertData L.lattice χ hχ).thetaSpace) (hf_ne : f ≠ 0) (hf0 : f 0 = 0) :
    (2 • appellHumbertData L.lattice χ hχ).thetaSpace = span ℂ {L.weierstrassPMulSq f, f ^ 2} := by
  -- `f²` and `℘ f²` are independent elements of a space of dimension two.
  set Θ₂ := (2 • appellHumbertData L.lattice χ hχ).thetaSpace
  have h_dim : finrank ℂ Θ₂ = 2 := finrank_thetaSpace_nsmul_appellHumbertData hχ two_ne_zero
  have : FiniteDimensional ℂ Θ₂ := .of_finrank_pos (by omega)
  have h_le : span ℂ {L.weierstrassPMulSq f, f ^ 2} ≤ Θ₂ := span_le.mpr <|
    pair_subset (weierstrassPMulSq_mem_thetaSpace hf hf0)
      (by simpa using AppellHumbertData.pow_mem_thetaSpace_nsmul hf 2)
  have h_ind := linearIndependent_sq_weierstrassPMulSq (L := L)
    (AppellHumbertData.differentiable_of_mem_thetaSpace hf) hf_ne
  have h_span : finrank ℂ (span ℂ {L.weierstrassPMulSq f, f ^ 2}) = 2 := by
    rw [pair_comm, ← Matrix.range_cons_cons_empty (f ^ 2) (L.weierstrassPMulSq f) ![],
      finrank_span_eq_card h_ind, Fintype.card_fin]
  exact (eq_of_le_of_finrank_le h_le (by omega)).symm

/-- `℘ f²` (extended to the lattice by `f′ (l)²`) does not vanish where `f` does. -/
private theorem weierstrassPMulSq_ne_zero (hf : f ∈ (appellHumbertData L.lattice χ hχ).thetaSpace)
    (hf_ne : f ≠ 0) (hf0 : f 0 = 0) {z : ℂ} (hz : f z = 0) : L.weierstrassPMulSq f z ≠ 0 := by
  -- `Th_2(Λ, χ)` has no base point: some `a ℘ f² + b f²` does not vanish at `z`.
  obtain ⟨g, hg, hg_ne⟩ :=
    AppellHumbertData.exists_mem_thetaSpace_nsmul_apply_ne_zero hf hf_ne le_rfl z
  obtain ⟨a, b, rfl⟩ :=
    mem_span_pair.mp ((thetaSpace_two_eq_span_weierstrassPMulSq hf hf_ne hf0).le hg)
  exact fun h ↦ hg_ne (by simp [h, hz])

/-- **The zeros of a theta function**: a nonzero `f ∈ Th_1(Λ, χ)` with `f (0) = 0` vanishes
exactly on the lattice. -/
theorem apply_eq_zero_iff_mem_lattice_of_mem_thetaSpace
    (hf : f ∈ (appellHumbertData L.lattice χ hχ).thetaSpace) (hf_ne : f ≠ 0) (hf0 : f 0 = 0)
    {z : ℂ} : f z = 0 ↔ z ∈ L.lattice := by
  refine ⟨fun hz ↦ by_contra fun hz' ↦ ?_,
    fun hz ↦ AppellHumbertData.apply_coe_eq_zero_of_mem_thetaSpace hf hf0 ⟨z, hz⟩⟩
  exact weierstrassPMulSq_ne_zero hf hf_ne hf0 hz (by simp [weierstrassPMulSq_of_notMem hz', hz])

/-- **The zeros are simple**: a nonzero `f ∈ Th_1(Λ, χ)` with `f (0) = 0` has nonzero
derivative at every point of the lattice. -/
theorem deriv_ne_zero_of_mem_thetaSpace (hf : f ∈ (appellHumbertData L.lattice χ hχ).thetaSpace)
    (hf_ne : f ≠ 0) (hf0 : f 0 = 0) {z : ℂ} (hz : z ∈ L.lattice) : deriv f z ≠ 0 := by
  simpa [weierstrassPMulSq_of_mem hz] using weierstrassPMulSq_ne_zero hf hf_ne hf0
    (AppellHumbertData.apply_coe_eq_zero_of_mem_thetaSpace hf hf0 ⟨z, hz⟩)

/-! ### The sigma function of a lattice -/

/-- At a half-period `l / 2 ∉ Λ`, a theta function of `(H, ε)` has `f (l / 2) = -f (-l / 2)`. -/
private theorem apply_div_two_eq_neg (hf : f ∈ (sigmaSignData L.lattice).thetaSpace) {l : ℂ}
    (hl : l ∈ L.lattice) (hl2 : l / 2 ∉ L.lattice) : f (l / 2) = -f (-(l / 2)) := by
  -- At `z = -l / 2` the exponent of the factor of automorphy is `0` and `ε (l) = -1`.
  have h := AppellHumbertData.apply_add_of_mem_thetaSpace hf ⟨l, hl⟩ (-(l / 2))
  have h_exp : -(l / 2) * conj l + ‖l‖ ^ 2 / 2 = (0 : ℂ) := by
    rw [← mul_conj']
    ring
  rw [factor_sigmaSignData, sigmaSign_of_div_two_notMem hl2, h_exp] at h
  have h_half : -(l / 2) + l = l / 2 := by ring
  simpa [h_half] using h

/-- A nonzero theta function of `(H, ε)` is not even. -/
private theorem not_even_of_mem_thetaSpace_sigmaSignData
    (hf : f ∈ (sigmaSignData L.lattice).thetaSpace) (hf_ne : f ≠ 0) : ¬ ∀ z, f (-z) = f z := by
  -- If `f` were even it would vanish at the half-periods `ω₂ / 2` and `(ω₁ + ω₂) / 2`; its
  -- twisted translate by `ω₂ / 2`, a theta function for another multiplier, would vanish at `0`
  -- and at `ω₁ / 2 ∉ Λ`, against `apply_eq_zero_iff_mem_lattice_of_mem_thetaSpace`.
  intro h_even
  have half_zero {l : ℂ} (hl : l ∈ L.lattice) (hl2 : l / 2 ∉ L.lattice) : f (l / 2) = 0 := by
    have h := apply_div_two_eq_neg hf hl hl2
    rw [h_even] at h
    exact self_eq_neg.mp h
  set D := sigmaSignData L.lattice
  set a : ℂ := L.ω₂ / 2
  have hg := AppellHumbertData.twistedTranslate_mem_thetaSpace hf a
  obtain ⟨hχ, hD⟩ := exists_eq_appellHumbertData (D := D + .ofAddChar (D.riemannChar a))
    fun l z ↦ by simp [AppellHumbertData.form_ofAddChar, D]
  rw [hD] at hg
  have hg_ne : D.twistedTranslate a f ≠ 0 := fun h ↦ hf_ne <| funext fun z ↦ by
    simpa [exp_ne_zero] using congrFun h (z - a)
  have h12 : (L.ω₁ + L.ω₂) / 2 ∉ L.lattice := by
    simpa using L.div_two_mem_lattice_iff 1 1
  have hg0 : D.twistedTranslate a f 0 = 0 := by
    simp [a, half_zero L.ω₂_mem_lattice L.ω₂_div_two_notMem_lattice]
  have hg1 : D.twistedTranslate a f (L.ω₁ / 2) = 0 := by
    simp [a, ← add_div, half_zero (add_mem L.ω₁_mem_lattice L.ω₂_mem_lattice) h12]
  exact L.ω₁_div_two_notMem_lattice <|
    (apply_eq_zero_iff_mem_lattice_of_mem_thetaSpace hg hg_ne hg0).mp hg1

/-- **Theta functions of `(H, ε)` are odd**: every `f ∈ Th_1(Λ, ε)` satisfies
`f (-z) = -f (z)`; in particular the sigma function is odd. -/
theorem apply_neg_of_mem_thetaSpace_sigmaSignData (hf : f ∈ (sigmaSignData L.lattice).thetaSpace)
    (z : ℂ) : f (-z) = -f z := by
  -- `z ↦ f (z) + f (-z)` is an even theta function of `(H, ε)`, so it vanishes.
  have h : (f + fun z ↦ f (-z)) ∈ (sigmaSignData L.lattice).thetaSpace :=
    add_mem hf (comp_neg_mem_thetaSpace_sigmaSignData hf)
  by_contra h_ne
  refine not_even_of_mem_thetaSpace_sigmaSignData h (fun h0 ↦ h_ne ?_) fun w ↦ ?_
  · have := congrFun h0 z
    simp only [Pi.add_apply, Pi.zero_apply] at this
    linear_combination this
  · simp only [Pi.add_apply, neg_neg]
    ring

/-- Every `f ∈ Th_1(Λ, ε)` vanishes at `0`, as it is odd. -/
theorem apply_zero_of_mem_thetaSpace_sigmaSignData
    (hf : f ∈ (sigmaSignData L.lattice).thetaSpace) : f 0 = 0 :=
  self_eq_neg.mp (by simpa using apply_neg_of_mem_thetaSpace_sigmaSignData hf 0)

/-- A function with derivative `1` at `0` is not zero. -/
private theorem ne_zero_of_deriv_eq_one (hf1 : deriv f 0 = 1) : f ≠ 0 := by
  rintro rfl
  simp at hf1

/-- `Th_1(Λ, ε)` is the theta space of the datum `(H, ε)` as an Appell–Humbert datum. -/
private theorem mem_thetaSpace_appellHumbertData_of_mem_sigmaSignData
    (hf : f ∈ (sigmaSignData L.lattice).thetaSpace) :
    f ∈ (appellHumbertData L.lattice (sigmaSign L.lattice)
      (isAppellHumbertMultiplier_sigmaSign L.lattice)).thetaSpace := by
  rwa [← sigmaSignData_def]

/-- **Existence of the sigma function**: some theta function of degree one for `(H, ε)` has
derivative `1` at `0`. -/
theorem exists_mem_thetaSpace_sigmaSignData_deriv_eq_one :
    ∃ f ∈ (sigmaSignData L.lattice).thetaSpace, deriv f 0 = 1 := by
  -- A nonzero theta function is odd, so it vanishes at `0`, and its derivative there is not zero.
  obtain ⟨g, hg, hg_ne⟩ := AppellHumbertData.IsPositive.exists_mem_thetaSpace_ne_zero
    (L := L.lattice) (isPositive_sigmaSignData L.lattice)
  have h_deriv := deriv_ne_zero_of_mem_thetaSpace
    (mem_thetaSpace_appellHumbertData_of_mem_sigmaSignData hg) hg_ne
    (apply_zero_of_mem_thetaSpace_sigmaSignData hg) (zero_mem _)
  refine ⟨(deriv g 0)⁻¹ • g, Submodule.smul_mem _ _ hg, ?_⟩
  rw [deriv_const_smul_field, smul_eq_mul]
  exact inv_mul_cancel₀ h_deriv

/-- **Uniqueness of the sigma function**: two theta functions of degree one for `(H, ε)` with
derivative `1` at `0` are equal. So the function of
`PeriodPair.exists_mem_thetaSpace_sigmaSignData_deriv_eq_one` is unique: it is the sigma function
`σ_Λ` of the lattice. -/
theorem eq_of_mem_thetaSpace_sigmaSignData_of_deriv_eq_one {g : ℂ → ℂ}
    (hf : f ∈ (sigmaSignData L.lattice).thetaSpace) (hg : g ∈ (sigmaSignData L.lattice).thetaSpace)
    (hf1 : deriv f 0 = 1) (hg1 : deriv g 0 = 1) : f = g := by
  -- `Th_1(Λ, ε)` is a line, so `g = c f`, and comparing derivatives at `0` gives `c = 1`.
  have h_dim : finrank ℂ (sigmaSignData L.lattice).thetaSpace = 1 := by
    have := finrank_thetaSpace_nsmul_appellHumbertData
      (isAppellHumbertMultiplier_sigmaSign L.lattice) one_ne_zero
    rwa [one_nsmul, ← sigmaSignData_def] at this
  have hf_ne : (⟨f, hf⟩ : (sigmaSignData L.lattice).thetaSpace) ≠ 0 := fun h ↦
    ne_zero_of_deriv_eq_one hf1 (congrArg Subtype.val h)
  obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_ne_zero' _ hf_ne).mp h_dim ⟨g, hg⟩
  have hc' : g = fun z ↦ c * f z := funext fun z ↦ by
    simpa [smul_eq_mul] using (congrFun (congrArg Subtype.val hc) z).symm
  rw [hc', deriv_const_mul_field'] at hg1
  simp only [hf1, mul_one] at hg1
  rw [hc', hg1]
  simp

/-- **The addition formula of the sigma function**: for the sigma function `f` of `Λ` (a theta
function of degree one for `(H, ε)` with derivative `1` at `0`) and `u, v ∉ Λ`,
`f (u + v) f (u - v) = (℘ (v) - ℘ (u)) f (u)² f (v)²`. -/
theorem apply_add_mul_apply_sub_of_mem_thetaSpace_sigmaSignData
    (hf : f ∈ (sigmaSignData L.lattice).thetaSpace) (hf1 : deriv f 0 = 1) {u v : ℂ}
    (hu : u ∉ L.lattice) (hv : v ∉ L.lattice) :
    f (u + v) * f (u - v) = (℘[L] v - ℘[L] u) * (f u ^ 2 * f v ^ 2) := by
  -- As a function of `z`, `f (z + v) f (z - v)` lies in `Th_2(Λ, ε)`, so it is `a ℘ f² + b f²`;
  -- the values at `0` and at `v` give `a` and `b`.
  have hf' := mem_thetaSpace_appellHumbertData_of_mem_sigmaSignData hf
  have hf_ne := ne_zero_of_deriv_eq_one hf1
  have hf0 := apply_zero_of_mem_thetaSpace_sigmaSignData hf
  have h_mem := AppellHumbertData.apply_add_mul_apply_sub_mem_thetaSpace_two_nsmul hf' v
  obtain ⟨a, b, hab⟩ := mem_span_pair.mp
    ((thetaSpace_two_eq_span_weierstrassPMulSq hf' hf_ne hf0).le h_mem)
  have hneg := apply_neg_of_mem_thetaSpace_sigmaSignData hf v
  have at_zero : a = -f v ^ 2 := by
    have := congrFun hab 0
    simp only [Pi.add_apply, Pi.smul_apply, Pi.pow_apply, smul_eq_mul,
      weierstrassPMulSq_of_mem (zero_mem _), hf1, hf0, zero_add, zero_sub, hneg] at this
    linear_combination this
  have at_v : a * (℘[L] v * f v ^ 2) + b * f v ^ 2 = 0 := by
    simpa [weierstrassPMulSq_of_notMem hv, hf0] using congrFun hab v
  have at_u : a * (℘[L] u * f u ^ 2) + b * f u ^ 2 = f (u + v) * f (u - v) := by
    simpa [weierstrassPMulSq_of_notMem hu] using congrFun hab u
  have hfv : f v ^ 2 ≠ 0 :=
    pow_ne_zero 2 fun h ↦ hv ((apply_eq_zero_iff_mem_lattice_of_mem_thetaSpace hf' hf_ne hf0).mp h)
  have b_eq : b = -a * ℘[L] v := mul_right_cancel₀ hfv (by linear_combination at_v)
  linear_combination -at_u + f u ^ 2 * b_eq + f u ^ 2 * (℘[L] u - ℘[L] v) * at_zero

/-- **The duplication formula of the sigma function**: for the sigma function `f` of `Λ` (a theta
function of degree one for `(H, ε)` with derivative `1` at `0`),
`f (2 z) = -℘′ (z) f (z)⁴`. Off the lattice this is the derivative of the addition formula; on the
lattice both sides vanish. -/
theorem apply_two_mul_of_mem_thetaSpace_sigmaSignData
    (hf : f ∈ (sigmaSignData L.lattice).thetaSpace) (hf1 : deriv f 0 = 1) (z : ℂ) :
    f (2 * z) = -℘'[L] z * f z ^ 4 := by
  -- Differentiate the addition formula in `v` at `v = z`: as `f (0) = 0`, `f′ (0) = 1` and
  -- `℘ (v) - ℘ (z)` vanishes at `v = z`, one term is left on each side.
  have hdiff := AppellHumbertData.differentiable_of_mem_thetaSpace hf
  have hf0 := apply_zero_of_mem_thetaSpace_sigmaSignData hf
  by_cases hz : z ∈ L.lattice
  · -- On the lattice both sides vanish.
    have h_zero {l : ℂ} (hl : l ∈ L.lattice) : f l = 0 :=
      AppellHumbertData.apply_coe_eq_zero_of_mem_thetaSpace hf hf0 ⟨l, hl⟩
    rw [h_zero (by simpa [two_mul] using add_mem hz hz), h_zero hz]
    ring
  have h_wp : DifferentiableAt ℂ ℘[L] z :=
    (L.analyticOnNhd_weierstrassP z hz).differentiableAt
  have h_deriv : deriv (fun v ↦ f (z + v) * f (z - v)) z =
      deriv (fun v ↦ (℘[L] v - ℘[L] z) * (f z ^ 2 * f v ^ 2)) z :=
    Filter.EventuallyEq.deriv_eq <| Filter.eventually_of_mem
      (L.isClosed_lattice.isOpen_compl.mem_nhds hz)
      fun v hv ↦ apply_add_mul_apply_sub_of_mem_thetaSpace_sigmaSignData hf hf1 hz hv
  have hA : HasDerivAt (fun v ↦ f (z + v)) (deriv f (z + z)) z := by
    exact (hdiff (z + z)).hasDerivAt.comp_const_add z z
  have hB : HasDerivAt (fun v ↦ f (z - v)) (-deriv f (z - z)) z := by
    exact (hdiff (z - z)).hasDerivAt.comp_const_sub z z
  have hl : deriv (fun v ↦ f (z + v) * f (z - v)) z = -f (2 * z) := by
    rw [(hA.fun_mul hB).deriv, sub_self, hf0, hf1, two_mul]
    ring
  have hC : HasDerivAt (fun v ↦ ℘[L] v - ℘[L] z) (℘'[L] z) z := by
    simpa using h_wp.hasDerivAt.sub_const (℘[L] z)
  have hD : HasDerivAt (fun v ↦ f z ^ 2 * f v ^ 2) (f z ^ 2 * (2 * f z * deriv f z)) z := by
    convert ((hdiff z).hasDerivAt.pow 2).const_mul (f z ^ 2) using 1
    ring
  have hr : deriv (fun v ↦ (℘[L] v - ℘[L] z) * (f z ^ 2 * f v ^ 2)) z = ℘'[L] z * f z ^ 4 := by
    rw [(hC.fun_mul hD).deriv, sub_self]
    ring
  linear_combination -(hl.symm.trans (h_deriv.trans hr))

end PeriodPair

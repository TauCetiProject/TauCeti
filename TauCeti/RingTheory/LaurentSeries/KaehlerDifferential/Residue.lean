/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.LaurentSeries.CoefficientDuality
public import TauCeti.RingTheory.LaurentSeries.KaehlerDifferential.Map
public import TauCeti.RingTheory.LaurentSeries.Primitive
public import TauCeti.RingTheory.LaurentSeries.ResiduePairing

/-!
# The residue of continuous one-forms on `K⸨X⸩`

Let `K` be a field and `Ω¹_cont(K⸨X⸩/K)` the continuous one-forms
`TauCeti.ContinuousKaehlerDifferential K`, every one of which is uniquely `f dX`. The residue
`Res (f dX)` is the coefficient of `X⁻¹` in `f`. This file packages it as the `K`-linear
functional `TauCeti.ContinuousKaehlerDifferential.residue K` on one-forms and proves its basic
calculus:

* it vanishes on the forms `f dX` with `f` a power series, and its kernel is open, so it is
  continuous for the discrete topology on `K`;
* exact forms have residue zero, `Res (dg) = 0`, and integration by parts
  `Res (f dg) = -Res (g df)` holds;
* the residue pairing `(f, ω) ↦ Res (f ω)` between `K⸨X⸩` and the one-forms is nondegenerate;
* substituting a power series `φ` of order `e` multiplies residues by `e`, so formal coordinate
  changes preserve residues;
* extending coefficients along a field embedding `σ : K → L` applies `σ` to residues;
* in characteristic zero the residue-zero forms are exactly the exact forms `dg`, and `g` is
  determined by `dg` up to a constant; in every characteristic `dX / X` is not exact.

## Main definitions

* `TauCeti.ContinuousKaehlerDifferential.residue K`: the residue `Res (f dX) = f₋₁`.

## Main results

* `TauCeti.ContinuousKaehlerDifferential.residue_D`: `Res (dg) = 0`.
* `TauCeti.ContinuousKaehlerDifferential.residue_smul_D_eq_neg`: `Res (f dg) = -Res (g df)`.
* `TauCeti.ContinuousKaehlerDifferential.residue_coe_powerSeries_smul_D_single_one`: the
  residue vanishes on `K⟦X⟧ dX`.
* `TauCeti.ContinuousKaehlerDifferential.isOpen_ker_residue`: the kernel of the residue is open.
* `TauCeti.ContinuousKaehlerDifferential.eq_zero_of_forall_residue_smul_eq_zero`:
  nondegeneracy of the residue pairing.
* `TauCeti.ContinuousKaehlerDifferential.residue_subst`: `Res (ω (φ)) = ord φ • Res ω`.
* `TauCeti.ContinuousKaehlerDifferential.residue_substEquiv`: formal coordinate changes preserve
  residues.
* `TauCeti.ContinuousKaehlerDifferential.residue_map`: residues commute with extension of
  coefficients.
* `TauCeti.ContinuousKaehlerDifferential.ker_residue`: in characteristic zero, the kernel of the
  residue is the subspace spanned by the exact forms.
* `TauCeti.ContinuousKaehlerDifferential.D_eq_D_iff`: in characteristic zero, primitives are
  unique up to a constant.

## References

* E. Frenkel, *Langlands Correspondence for Loop Groups*, §1.2.
-/

public section

open HahnSeries
open scoped LaurentSeries PowerSeries

namespace TauCeti.ContinuousKaehlerDifferential

variable (K : Type*) [Field K]

/-- The **residue** of a continuous one-form: `Res (f dX)` is the coefficient of `X⁻¹` in `f`. -/
noncomputable def residue : ContinuousKaehlerDifferential K →ₗ[K] K :=
  (coeff.linearMap (-1)).comp ((equivLaurentSeries K).toLinearMap.restrictScalars K)

variable {K}

/-- The residue of `ω` is the coefficient of `X⁻¹` in the coordinate of `ω` in the basis `dX`. -/
theorem residue_apply (ω : ContinuousKaehlerDifferential K) :
    residue K ω = (equivLaurentSeries K ω).coeff (-1) :=
  (rfl)

/-- `Res (f dX)` is the coefficient of `X⁻¹` in `f`. -/
@[simp]
theorem residue_smul_D_single_one (f : K⸨X⸩) :
    residue K (f • D K (single 1 1)) = f.coeff (-1) := by
  rw [residue_apply, map_smul, equivLaurentSeries_D_single_one, smul_eq_mul, mul_one]

/-- **Exact forms have residue zero**: `Res (dg) = 0`, in every characteristic. -/
@[simp]
theorem residue_D (g : K⸨X⸩) : residue K (D K g) = 0 := by
  rw [residue_apply, equivLaurentSeries_D, LaurentSeries.coeff_neg_one_derivative]

/-- `Res (f dg)` is the residue pairing of `f` and `g`. -/
theorem residue_smul_D (f g : K⸨X⸩) :
    residue K (f • D K g) = LaurentSeries.residuePairing K f g := by
  rw [residue_apply, map_smul, equivLaurentSeries_D, smul_eq_mul,
    LaurentSeries.residuePairing_apply]

/-- **Integration by parts**: `Res (f dg) = -Res (g df)`. -/
theorem residue_smul_D_eq_neg (f g : K⸨X⸩) :
    residue K (f • D K g) = -residue K (g • D K f) := by
  rw [residue_smul_D, residue_smul_D, LaurentSeries.residuePairing_eq_neg_swap]

/-- The residue of `a X⁻¹ dX` is `a`. -/
theorem residue_single_neg_one_smul_D_single_one (a : K) :
    residue K (single (-1) a • D K (single 1 1)) = a := by
  rw [residue_smul_D_single_one, coeff_single_same]

/-- **The residue vanishes on `K⟦X⟧ dX`**: forms `f dX` with `f` a power series have residue
zero. -/
theorem residue_coe_powerSeries_smul_D_single_one (f : K⟦X⟧) :
    residue K ((f : K⸨X⸩) • D K (single 1 1)) = 0 := by
  rw [residue_smul_D_single_one, PowerSeries.coeff_coe]
  simp

/-- The residue of a logarithmic form `f⁻¹ df` is the order of `f`. -/
theorem residue_inv_smul_D (f : K⸨X⸩) : residue K (f⁻¹ • D K f) = f.order := by
  rw [residue_apply, map_smul, equivLaurentSeries_D, smul_eq_mul, mul_comm,
    LaurentSeries.coeff_neg_one_derivative_mul_inv]

/-- **The kernel of the residue is open**: it contains the open set of forms `f dX` with `f` a
power series. This is the continuity of the residue for the discrete topology on `K`. -/
theorem isOpen_ker_residue :
    IsOpen (LinearMap.ker (residue K) : Set (ContinuousKaehlerDifferential K)) := by
  refine AddSubgroup.isOpen_of_mem_nhds (LinearMap.ker (residue K)).toAddSubgroup (g := 0) ?_
  refine Filter.mem_of_superset ((equivLaurentSeries K).continuous.continuousAt.preimage_mem_nhds
    ((Valued.isOpen_integer K⸨X⸩).mem_nhds (by simp))) fun ω hω ↦ ?_
  -- `ω = f dX` with `f` of valuation at most one, that is, a power series.
  obtain ⟨f, hf⟩ := (LaurentSeries.val_le_one_iff_eq_coe K (equivLaurentSeries K ω)).mp hω
  rw [Submodule.coe_toAddSubgroup, SetLike.mem_coe, LinearMap.mem_ker,
    ← equivLaurentSeries_smul_D_single_one K ω, ← hf, residue_coe_powerSeries_smul_D_single_one]

/-- **The residue pairing is nondegenerate**: a one-form `ω` with `Res (f ω) = 0` for every
`f ∈ K⸨X⸩` is zero. -/
theorem eq_zero_of_forall_residue_smul_eq_zero {ω : ContinuousKaehlerDifferential K}
    (h : ∀ f : K⸨X⸩, residue K (f • ω) = 0) : ω = 0 := by
  refine (equivLaurentSeries K).map_eq_zero_iff.mp
    (LaurentSeries.residueForm_nondegenerate.2 _ fun f ↦ ?_)
  rw [LaurentSeries.residueForm_apply, ← smul_eq_mul, ← map_smul, ← residue_apply, h]

/-- One-forms are determined by their residue pairings with `K⸨X⸩`. -/
theorem ext_residue_smul {ω η : ContinuousKaehlerDifferential K}
    (h : ∀ f : K⸨X⸩, residue K (f • ω) = residue K (f • η)) : ω = η :=
  sub_eq_zero.mp <| eq_zero_of_forall_residue_smul_eq_zero fun f ↦ by
    rw [smul_sub, map_sub, h, sub_self]

/-! ### Substitution and extension of coefficients -/

section Subst

open TauCeti.LaurentSeries PowerSeries

variable {φ : K⟦X⟧} (hφ : constantCoeff φ = 0) (hφ₀ : φ ≠ 0)

/-- **Residues of substituted one-forms.** Substituting a power series `φ` multiplies the residue
of a one-form by the order of `φ`: `Res (ω (φ)) = ord φ • Res ω`, in every characteristic. -/
theorem residue_subst (ω : ContinuousKaehlerDifferential K) :
    residue K (subst hφ hφ₀ ω) = φ.order.toNat • residue K ω := by
  rw [residue_apply, residue_apply, equivLaurentSeries_subst,
    coeff_neg_one_substAlgHom_mul_derivative_eq_nsmul]

end Subst

/-- **Formal coordinate changes preserve residues of one-forms.** -/
@[simp]
theorem residue_substEquiv (φ : FormalCoordinate K) (ω : ContinuousKaehlerDifferential K) :
    residue K (substEquiv φ ω) = residue K ω := by
  rw [substEquiv_apply, residue_subst, FormalCoordinate.order_toPowerSeries, ENat.toNat_one,
    one_smul]

/-- Extension of coefficients along a field embedding `σ : K → L` applies `σ` to residues. -/
@[simp]
theorem residue_map {L : Type*} [Field L] (σ : K →+* L) (ω : ContinuousKaehlerDifferential K) :
    residue L (map σ ω) = σ (residue K ω) := by
  rw [residue_apply, residue_apply, equivLaurentSeries_map, coeff_mapRingHom]

/-! ### Exactness -/

/-- **`dX / X` is not exact**, in every characteristic: for `a ≠ 0`, the form `a X⁻¹ dX` is not
`dg` for any `g`. -/
theorem D_ne_single_neg_one_smul_D_single_one {a : K} (ha : a ≠ 0) (g : K⸨X⸩) :
    D K g ≠ single (-1) a • D K (single 1 1) := fun h ↦
  ha <| by rw [← residue_single_neg_one_smul_D_single_one a, ← h, residue_D]

variable [CharZero K]

/-- **Residue-zero forms are exact.** In characteristic zero, a one-form is `dg` for some
Laurent series `g` exactly when its residue vanishes. -/
theorem exists_D_eq_iff (ω : ContinuousKaehlerDifferential K) :
    (∃ g, D K g = ω) ↔ residue K ω = 0 := by
  rw [residue_apply, ← mem_range_laurentSeries_derivative_iff (R := K)]
  refine exists_congr fun g ↦ ?_
  rw [← (equivLaurentSeries K).injective.eq_iff, equivLaurentSeries_D]

/-- In characteristic zero, the kernel of the residue is the subspace spanned by the exact forms
`dg`; by `exists_D_eq_iff` every element of it is itself exact. -/
theorem ker_residue : LinearMap.ker (residue K) = Submodule.span K (Set.range (D K)) := by
  refine le_antisymm (fun ω hω ↦ Submodule.subset_span ((exists_D_eq_iff ω).2 hω)) ?_
  rw [Submodule.span_le]
  rintro _ ⟨g, rfl⟩
  exact residue_D g

/-- **Primitives are unique up to a constant.** In characteristic zero, `df = dg` exactly when
`f` and `g` differ by a constant. -/
theorem D_eq_D_iff {f g : K⸨X⸩} : D K f = D K g ↔ ∃ c : K, f = g + HahnSeries.C c := by
  rw [← sub_eq_zero, ← map_sub, ← (equivLaurentSeries K).map_eq_zero_iff, equivLaurentSeries_D,
    LaurentSeries.derivative_eq_zero_iff_exists_C]
  exact exists_congr fun c ↦ by rw [eq_comm, sub_eq_iff_eq_add']

end TauCeti.ContinuousKaehlerDifferential

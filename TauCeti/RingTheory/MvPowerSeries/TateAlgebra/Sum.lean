/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.MvPowerSeries.Equiv
public import TauCeti.RingTheory.MvPowerSeries.TateAlgebra.Basic

/-!
# Restricted series in two families of variables

For positive polyradii `c` on `σ` and `d` on `τ`, a power series in `σ ⊕ τ` is restricted at the
polyradii `Sum.elim c d` exactly when, viewed through `MvPowerSeries.sumAlgEquiv` as a
power series in `σ` over power series in `τ`, each coefficient is restricted at `d` and the
Gauss norms of these coefficients make the series restricted at `c`. This identifies

```text
R{X/c, Y/d} ≅ R{Y/d}{X/c}
```

as normed rings, with the Gauss norms on both sides. Unlike
`TauCeti.Huber.restrictedOptionEquiv`, which separates a single variable into a univariate
series, both families of variables are arbitrary. Arbitrary radii are needed to present
restricted series over a quotient of a ring of restricted series, as in Kedlaya's proof that the
interval rings of the Fargues–Fontaine curve are strongly noetherian.

## Main results

* `TauCeti.MvPowerSeries.isRestricted_coeff_sumAlgEquiv`: the coefficients in `σ` of a restricted
  series in `σ ⊕ τ` are restricted series in `τ`.
* `TauCeti.MvPowerSeries.restrictedSumEquiv`: the ring isomorphism `R{X/c, Y/d} ≃+* R{Y/d}{X/c}`,
  and `TauCeti.MvPowerSeries.restrictedSumAlgEquiv`: the same map as an algebra isomorphism over
  every algebra `S` of coefficients.
* `TauCeti.MvPowerSeries.coeff_coeff_restrictedSumEquiv` and
  `TauCeti.MvPowerSeries.coeff_restrictedSumEquiv_symm`: its coefficients.
* `TauCeti.MvPowerSeries.norm_restrictedSumEquiv` and
  `TauCeti.MvPowerSeries.isometry_restrictedSumEquiv`: it preserves the Gauss norms.

## References

* Bosch, Güntzer, Remmert, *Non-Archimedean Analysis*, §5.1.
* K. S. Kedlaya, *Noetherian properties of Fargues–Fontaine curves*, IMRN 2016, no. 8,
  2544–2567; arXiv:1410.5160v3, Theorem 4.10 and Remark 4.11.
-/

public section

namespace TauCeti.MvPowerSeries

open Filter _root_.MvPowerSeries
open scoped Topology

variable {σ τ R : Type*} [NormedCommRing R] [IsUltrametricDist R] {c : σ → ℝ} {d : τ → ℝ}
  [∀ i, Fact (0 < c i)] [∀ j, Fact (0 < d j)]

/-- The polyradii `Sum.elim c d` are positive when `c` and `d` are. -/
instance instFactPosSumElim : ∀ k, Fact (0 < Sum.elim c d k)
  | .inl i => ‹∀ i, Fact (0 < c i)› i
  | .inr j => ‹∀ j, Fact (0 < d j)› j

local notation "Inner" => IsRestricted.subring (R := R) d
local notation "Flat" => IsRestricted.subring (R := R) (Sum.elim c d)
local notation "Iter" => IsRestricted.subring (R := Inner) c

omit [∀ i, Fact (0 < c i)] [∀ j, Fact (0 < d j)] in
/-- Rearranging a weighted coefficient norm in `σ ⊕ τ` as a weighted norm in `τ`, weighted again
in `σ`. -/
private theorem mul_prod_sumElim (x : ℝ) (a : σ →₀ ℕ) (b : τ →₀ ℕ) :
    x * (a.sumElim b).prod (Sum.elim c d · ^ ·) = x * b.prod (d · ^ ·) * a.prod (c · ^ ·) := by
  rw [Finsupp.prod_sumElim]
  simp only [Function.comp_def, Sum.elim_inl, Sum.elim_inr]
  ring

omit [IsUltrametricDist R] [∀ j, Fact (0 < d j)] in
/-- Each coefficient of a restricted series in `σ ⊕ τ`, viewed as a series in `σ` over series in
`τ`, is restricted. -/
theorem isRestricted_coeff_sumAlgEquiv {f : MvPowerSeries (σ ⊕ τ) R}
    (hf : IsRestricted (Sum.elim c d) f) (a : σ →₀ ℕ) :
    IsRestricted d (coeff a (sumAlgEquiv R σ τ f)) := by
  have hi : Function.Injective (a.sumElim : (τ →₀ ℕ) → σ ⊕ τ →₀ ℕ) := fun b b' h ↦ by
    simpa using congrArg (Finsupp.comapDomain Sum.inr · Sum.inr_injective.injOn) h
  have h := (hf.comp hi.tendsto_cofinite).const_mul (a.prod (c · ^ ·))⁻¹
  rw [mul_zero] at h
  refine h.congr fun b ↦ ?_
  rw [Function.comp_apply, coeff_coeff_sumAlgEquiv, mul_prod_sumElim]
  field_simp [(prod_pow_pos (c := c) a).ne']

/-- The coefficients of a restricted series in `σ ⊕ τ`, as a formal series in `σ` over the
restricted series in `τ`. -/
private noncomputable def sumSlices (f : Flat) : MvPowerSeries σ Inner :=
  fun a ↦ ⟨coeff a (sumAlgEquiv R σ τ f), isRestricted_coeff_sumAlgEquiv f.2 a⟩

omit [∀ j, Fact (0 < d j)] in
private theorem coe_coeff_sumSlices (f : Flat) (a : σ →₀ ℕ) :
    ((coeff a (sumSlices f) : Inner) : MvPowerSeries τ R) = coeff a (sumAlgEquiv R σ τ f) :=
  (rfl)

private theorem isRestricted_sumSlices (f : Flat) : IsRestricted c (sumSlices f) := by
  classical
  refine tendsto_order.mpr ⟨fun _ hb ↦ .of_forall fun a ↦
    hb.trans_le (mul_nonneg (norm_nonneg _) (prod_pow_pos a).le), fun ε hε ↦ ?_⟩
  -- only finitely many weighted coefficients of `f` reach `ε / 2`; the exponents in `σ` of these
  -- are the only ones at which the weighted Gauss norm of the slice can reach `ε`
  have hbad : {k | ε / 2 ≤ ‖coeff k (f : MvPowerSeries (σ ⊕ τ) R)‖ *
      k.prod (Sum.elim c d · ^ ·)}.Finite := by
    simpa [eventually_cofinite, not_lt] using f.2.eventually (gt_mem_nhds (half_pos hε))
  rw [eventually_cofinite]
  refine (hbad.image fun k ↦ k.comapDomain Sum.inl Sum.inl_injective.injOn).subset fun a ha ↦ ?_
  by_contra hna
  have hpos : 0 < a.prod (c · ^ ·) := prod_pow_pos a
  refine (half_lt_self hε).not_ge ((not_lt.mp ha).trans ?_)
  rw [← le_div_iff₀ hpos, norm_le_iff (div_nonneg (half_pos hε).le hpos.le)]
  intro b
  rw [le_div_iff₀ hpos, coe_coeff_sumSlices, coeff_coeff_sumAlgEquiv, ← mul_prod_sumElim]
  by_contra hlt
  exact hna ⟨a.sumElim b, (not_le.mp hlt).le, Finsupp.comapDomain_inl_sumElim a b⟩

/-- Flattening a restricted series in `σ` over the restricted series in `τ` gives a restricted
series in `σ ⊕ τ`. -/
private theorem isRestricted_sumAlgEquiv_symm (g : Iter) :
    IsRestricted (Sum.elim c d) ((sumAlgEquiv R σ τ).symm (map (Inner).subtype g)) := by
  classical
  set h := (sumAlgEquiv R σ τ).symm (map (Inner).subtype g)
  have hcoeff (a : σ →₀ ℕ) (b : τ →₀ ℕ) :
      coeff (a.sumElim b) h =
        coeff b ((coeff a (g : MvPowerSeries σ Inner) : Inner) : MvPowerSeries τ R) := by
    simp [h]
  refine tendsto_order.mpr ⟨fun _ hb ↦ .of_forall fun k ↦
    hb.trans_le (mul_nonneg (norm_nonneg _) (prod_pow_pos k).le), fun ε hε ↦ ?_⟩
  -- a weighted coefficient of `h` reaching `ε` comes from one of the finitely many coefficients
  -- of `g` whose weighted norm reaches `ε`, and from one of the finitely many coefficients of
  -- that slice whose weighted norm, weighted again, reaches `ε`
  have houter : {a | ε ≤ ‖coeff a (g : MvPowerSeries σ Inner)‖ * a.prod (c · ^ ·)}.Finite := by
    simpa [eventually_cofinite, not_lt] using g.2.eventually (gt_mem_nhds hε)
  have hinner (a : σ →₀ ℕ) : {b | ε / a.prod (c · ^ ·) ≤
      ‖coeff b ((coeff a (g : MvPowerSeries σ Inner) : Inner) : MvPowerSeries τ R)‖ *
        b.prod (d · ^ ·)}.Finite := by
    simpa [eventually_cofinite, not_lt] using (coeff a (g : MvPowerSeries σ Inner)).2.eventually
      (gt_mem_nhds (div_pos hε (prod_pow_pos a)))
  rw [eventually_cofinite]
  refine (houter.biUnion fun a _ ↦ (hinner a).image a.sumElim).subset fun k hk ↦ ?_
  set a := k.comapDomain Sum.inl Sum.inl_injective.injOn
  set b := k.comapDomain Sum.inr Sum.inr_injective.injOn
  have hk' : ε ≤ ‖coeff (a.sumElim b) h‖ * (a.sumElim b).prod (Sum.elim c d · ^ ·) := by
    rw [Finsupp.comapDomain_sumElim_comapDomain]
    exact not_lt.mp hk
  rw [mul_prod_sumElim, hcoeff] at hk'
  refine Set.mem_biUnion (x := a) ?_ ⟨b, ?_, Finsupp.comapDomain_sumElim_comapDomain k⟩
  · exact hk'.trans (mul_le_mul_of_nonneg_right (norm_coeff_mul_prod_le _ b) (prod_pow_pos a).le)
  · exact (div_le_iff₀ (prod_pow_pos a)).mpr hk'

/-- Flattening, as a ring homomorphism from `R{Y/d}{X/c}` to `R{X/c, Y/d}`. -/
private noncomputable def sumFlatten : Iter →+* Flat :=
  (((sumAlgEquiv R σ τ).symm.toRingEquiv.toRingHom.comp (map (Inner).subtype)).comp
    (Iter).subtype).codRestrict _ isRestricted_sumAlgEquiv_symm

private theorem sumFlatten_sumSlices (f : Flat) :
    sumFlatten ⟨sumSlices f, isRestricted_sumSlices f⟩ = f := by
  refine Subtype.ext ((sumAlgEquiv R σ τ).injective ?_)
  ext a : 1
  simpa [sumFlatten] using coe_coeff_sumSlices f a

private theorem sumFlatten_bijective :
    Function.Bijective (sumFlatten (R := R) (c := c) (d := d)) := by
  refine ⟨fun g h hgh ↦ Subtype.ext ?_, fun f ↦ ⟨_, sumFlatten_sumSlices f⟩⟩
  have := (sumAlgEquiv R σ τ).symm.injective (congrArg Subtype.val hgh)
  ext a : 1
  exact Subtype.ext (by simpa using congrArg (coeff a) this)

/-- **Restricted series in `σ ⊕ τ` are restricted series in `σ` over restricted series in `τ`.**
For positive polyradii `c` and `d`, this is the ring isomorphism `R{X/c, Y/d} ≃+* R{Y/d}{X/c}`
induced by `MvPowerSeries.sumAlgEquiv`. No completeness of `R` and no finiteness of `σ`
or `τ` is needed. -/
noncomputable def restrictedSumEquiv : Flat ≃+* Iter :=
  (RingEquiv.ofBijective _ (sumFlatten_bijective (R := R) (c := c) (d := d))).symm

private theorem restrictedSumEquiv_apply (f : Flat) :
    restrictedSumEquiv f = ⟨sumSlices f, isRestricted_sumSlices f⟩ := by
  rw [restrictedSumEquiv, RingEquiv.symm_apply_eq, RingEquiv.ofBijective_apply,
    sumFlatten_sumSlices]

/-- The coefficients of `restrictedSumEquiv`: the coefficient of `yᵇ` in the coefficient of `xᵃ`
of the image of `f` is the coefficient of `xᵃ yᵇ` in `f`. -/
@[simp]
theorem coeff_coeff_restrictedSumEquiv (f : Flat) (a : σ →₀ ℕ) (b : τ →₀ ℕ) :
    coeff b ((coeff a (restrictedSumEquiv f : MvPowerSeries σ Inner) : Inner) :
      MvPowerSeries τ R) =
      coeff (a.sumElim b) (f : MvPowerSeries (σ ⊕ τ) R) := by
  rw [restrictedSumEquiv_apply]
  exact (congrArg (coeff b) (coe_coeff_sumSlices f a)).trans (coeff_coeff_sumAlgEquiv _ a b)

/-- The coefficients of the inverse of `restrictedSumEquiv`: the coefficient of `xᵃ yᵇ` is the
coefficient of `yᵇ` in the coefficient of `xᵃ`. -/
@[simp]
theorem coeff_restrictedSumEquiv_symm (g : Iter) (a : σ →₀ ℕ) (b : τ →₀ ℕ) :
    coeff (a.sumElim b) (restrictedSumEquiv.symm g : MvPowerSeries (σ ⊕ τ) R) =
      coeff b ((coeff a (g : MvPowerSeries σ Inner) : Inner) : MvPowerSeries τ R) := by
  rw [← coeff_coeff_restrictedSumEquiv, RingEquiv.apply_symm_apply]

/-- `restrictedSumEquiv` sends constants to constants: the constant `r` in `σ ⊕ τ` goes to the
constant series in `σ` whose value is the constant `r` in `τ`. -/
@[simp]
theorem restrictedSumEquiv_algebraMap {S : Type*} [CommSemiring S] [Algebra S R] (s : S) :
    restrictedSumEquiv (algebraMap S Flat s) = algebraMap S Iter s := by
  rw [restrictedSumEquiv, RingEquiv.symm_apply_eq, RingEquiv.ofBijective_apply]
  refine Subtype.ext ((sumAlgEquiv R σ τ).injective ?_)
  simpa [sumFlatten, coe_algebraMap_isRestrictedSubring_apply, algebraMap_apply,
    -AlgEquiv.commutes] using (sumAlgEquiv R σ τ).commutes (algebraMap S R s)

/-- **Iteration of restricted series as an algebra isomorphism**: over every algebra `S` of
coefficients, `restrictedSumEquiv` is an `S`-algebra isomorphism `R{X/c, Y/d} ≃ₐ[S] R{Y/d}{X/c}`.
-/
noncomputable def restrictedSumAlgEquiv {S : Type*} [CommSemiring S] [Algebra S R] :
    Flat ≃ₐ[S] Iter :=
  AlgEquiv.ofRingEquiv restrictedSumEquiv_algebraMap

/-- `restrictedSumAlgEquiv` has the same underlying map as `restrictedSumEquiv`. -/
@[simp]
theorem coe_restrictedSumAlgEquiv {S : Type*} [CommSemiring S] [Algebra S R] :
    ⇑(restrictedSumAlgEquiv (S := S) (R := R) (c := c) (d := d)) = restrictedSumEquiv := (rfl)

/-- `restrictedSumEquiv` preserves the Gauss norms. -/
@[simp]
theorem norm_restrictedSumEquiv (f : Flat) : ‖restrictedSumEquiv f‖ = ‖f‖ := by
  apply le_antisymm
  · rw [norm_le_iff (norm_nonneg _)]
    intro a
    rw [← le_div_iff₀ (prod_pow_pos a), norm_le_iff (div_nonneg (norm_nonneg _)
      (prod_pow_pos a).le)]
    intro b
    rw [le_div_iff₀ (prod_pow_pos a), coeff_coeff_restrictedSumEquiv, ← mul_prod_sumElim]
    exact norm_coeff_mul_prod_le f _
  · rw [norm_le_iff (norm_nonneg _)]
    intro k
    rw [← Finsupp.comapDomain_sumElim_comapDomain k, mul_prod_sumElim,
      ← coeff_coeff_restrictedSumEquiv]
    exact (mul_le_mul_of_nonneg_right (norm_coeff_mul_prod_le _ _) (prod_pow_pos _).le).trans
      (norm_coeff_mul_prod_le (restrictedSumEquiv f) _)

/-- `restrictedSumEquiv` is an isometry for the Gauss norms. -/
theorem isometry_restrictedSumEquiv :
    Isometry (restrictedSumEquiv (R := R) (c := c) (d := d)) :=
  AddMonoidHomClass.isometry_iff_norm _ |>.mpr norm_restrictedSumEquiv

end TauCeti.MvPowerSeries

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.MvPowerSeries.Equiv
public import TauCeti.RingTheory.MvPowerSeries.TateAlgebra.Module.Sum

import TauCeti.RingTheory.MvPowerSeries.Rename

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
`MvPowerSeries.restrictedOptionEquiv`, which separates a single variable into a univariate
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
* `TauCeti.MvPowerSeries.map_subtype_restrictedSumEquiv`: on the underlying formal series it is
  `MvPowerSeries.sumAlgEquiv`.
* `TauCeti.MvPowerSeries.restrictedSumEquiv_X_inl`, `TauCeti.MvPowerSeries.restrictedSumEquiv_X_inr`
  and `TauCeti.MvPowerSeries.restrictedSumEquiv_polynomialToRestricted`: its values on the
  variables and on polynomials.
* `TauCeti.MvPowerSeries.restrictedSumAssoc` and
  `TauCeti.MvPowerSeries.map_restrictedSumEquiv_restrictedSumAssoc`: reassociating three families
  of variables, and the associativity of iteration.
* `TauCeti.MvPowerSeries.restrictedSumCongr` and
  `TauCeti.MvPowerSeries.coe_restrictedSumEquiv_restrictedSumCongr`: renaming each family of
  variables, and the compatibility of iteration with these renamings.

Its compatibility with bounded coefficient maps is
`TauCeti.MvPowerSeries.coe_restrictedSumEquiv_restrictedMap`, in
`TauCeti.RingTheory.MvPowerSeries.TateAlgebra.Map`.

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

local notation "Inner" => IsRestricted.subring (R := R) d
local notation "Flat" => IsRestricted.subring (R := R) (Sum.elim c d)
local notation "Iter" => IsRestricted.subring (R := Inner) c

omit [IsUltrametricDist R] [∀ j, Fact (0 < d j)] in
/-- Each coefficient of a restricted series in `σ ⊕ τ`, viewed as a series in `σ` over series in
`τ`, is restricted. -/
theorem isRestricted_coeff_sumAlgEquiv {f : MvPowerSeries (σ ⊕ τ) R}
    (hf : IsRestricted (Sum.elim c d) f) (a : σ →₀ ℕ) :
    IsRestricted d (coeff a (sumAlgEquiv R σ τ f)) := by
  apply (isRestrictedFamily_coeff_iff _).mp
  simpa only [coeff_coeff_sumAlgEquiv] using
    ((isRestrictedFamily_coeff_iff f).mpr hf).comp_sumElim a

/-- The coefficients of a restricted series in `σ ⊕ τ`, as a formal series in `σ` over the
restricted series in `τ`. -/
private noncomputable def sumSlices (f : Flat) : MvPowerSeries σ Inner :=
  fun a ↦ ⟨coeff a (sumAlgEquiv R σ τ f), isRestricted_coeff_sumAlgEquiv f.2 a⟩

omit [∀ j, Fact (0 < d j)] in
private theorem coe_coeff_sumSlices (f : Flat) (a : σ →₀ ℕ) :
    ((coeff a (sumSlices f) : Inner) : MvPowerSeries τ R) = coeff a (sumAlgEquiv R σ τ f) :=
  (rfl)

private theorem sumAddEquiv_subringLinearEquiv (f : Flat) (s : σ →₀ ℕ) :
    IsRestrictedFamily.Gauss.sumAddEquiv
        (IsRestrictedFamily.Gauss.ofAddSubgroup (IsRestrictedFamily.subringLinearEquiv f)) s =
      IsRestrictedFamily.Gauss.ofAddSubgroup
        (IsRestrictedFamily.subringLinearEquiv (coeff s (sumSlices f))) := by
  ext t
  simp [coe_coeff_sumSlices, coeff_coeff_sumAlgEquiv]

private theorem norm_sumAddEquiv_subringLinearEquiv (f : Flat) (s : σ →₀ ℕ) :
    ‖IsRestrictedFamily.Gauss.sumAddEquiv
        (IsRestrictedFamily.Gauss.ofAddSubgroup (IsRestrictedFamily.subringLinearEquiv f)) s‖ =
      ‖coeff s (sumSlices f)‖ := by
  rw [sumAddEquiv_subringLinearEquiv, IsRestrictedFamily.Gauss.norm_subringLinearEquiv]

private theorem isRestricted_sumSlices (f : Flat) : IsRestricted c (sumSlices f) := by
  have h := IsRestrictedFamily.mem_addSubgroup.mp
    (IsRestrictedFamily.Gauss.sumAddEquiv
      (IsRestrictedFamily.Gauss.ofAddSubgroup
        (IsRestrictedFamily.subringLinearEquiv f))).toAddSubgroup.2
  apply (isRestrictedFamily_coeff_iff _).mp
  apply isRestrictedFamily_iff.mpr
  simpa only [norm_sumAddEquiv_subringLinearEquiv] using isRestrictedFamily_iff.mp h

/-- Flattening a restricted series in `σ` over the restricted series in `τ` gives a restricted
series in `σ ⊕ τ`. -/
private theorem isRestricted_sumAlgEquiv_symm (g : Iter) :
    IsRestricted (Sum.elim c d) ((sumAlgEquiv R σ τ).symm (map (Inner).subtype g)) := by
  let a : (σ →₀ ℕ) → IsRestrictedFamily.Gauss d R := fun s ↦
    .ofAddSubgroup (IsRestrictedFamily.subringLinearEquiv
      (coeff s (g : MvPowerSeries σ Inner)))
  have ha : IsRestrictedFamily c a := by
    apply isRestrictedFamily_iff.mpr
    have hg := (isRestrictedFamily_coeff_iff _).mpr (IsRestricted.mem_subring.mp g.2)
    simpa only [a, IsRestrictedFamily.Gauss.norm_subringLinearEquiv] using
      isRestrictedFamily_iff.mp hg
  have h := IsRestrictedFamily.Gauss.isRestrictedFamily_flatten
    (.ofAddSubgroup ⟨a, IsRestrictedFamily.mem_addSubgroup.mpr ha⟩)
  apply (isRestrictedFamily_coeff_iff _).mp
  apply isRestrictedFamily_iff.mpr
  refine (isRestrictedFamily_iff.mp h).congr fun k ↦ ?_
  rw [← Finsupp.comapDomain_sumElim_comapDomain k, coeff_sumAlgEquiv_symm]
  simp [a]

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
  calc
    ‖restrictedSumEquiv f‖ = ‖IsRestrictedFamily.Gauss.sumAddEquiv
        (IsRestrictedFamily.Gauss.ofAddSubgroup (IsRestrictedFamily.subringLinearEquiv f))‖ := by
      rw [← IsRestrictedFamily.Gauss.norm_subringLinearEquiv (restrictedSumEquiv f),
        IsRestrictedFamily.Gauss.norm_eq_iSup, IsRestrictedFamily.Gauss.norm_eq_iSup]
      simp only [IsRestrictedFamily.coe_subringLinearEquiv,
        norm_sumAddEquiv_subringLinearEquiv, restrictedSumEquiv_apply]
    _ = ‖f‖ := by
      rw [IsRestrictedFamily.Gauss.norm_sumAddEquiv,
        IsRestrictedFamily.Gauss.norm_subringLinearEquiv]

/-- `restrictedSumEquiv` is an isometry for the Gauss norms. -/
theorem isometry_restrictedSumEquiv :
    Isometry (restrictedSumEquiv (R := R) (c := c) (d := d)) :=
  AddMonoidHomClass.isometry_iff_norm _ |>.mpr norm_restrictedSumEquiv

/-- On the underlying formal series, `restrictedSumEquiv` is `MvPowerSeries.sumAlgEquiv`. -/
@[simp]
theorem map_subtype_restrictedSumEquiv (f : Flat) :
    map (Inner).subtype (restrictedSumEquiv f : MvPowerSeries σ Inner) =
      sumAlgEquiv R σ τ (f : MvPowerSeries (σ ⊕ τ) R) := by
  ext a b
  simp [coeff_map]

omit [∀ i, Fact (0 < c i)] in
/-- Iterated restricted series are determined by their underlying formal series. -/
private theorem eq_of_map_subtype_eq {F G : Iter}
    (h : map (Inner).subtype (F : MvPowerSeries σ Inner) = map (Inner).subtype G) : F = G :=
  Subtype.ext (MvPowerSeries.ext fun a ↦ Subtype.ext (by simpa using congrArg (coeff a) h))

/-- `restrictedSumEquiv` sends a variable of the first family to the corresponding variable. -/
@[simp]
theorem restrictedSumEquiv_X_inl (i : σ) :
    restrictedSumEquiv (⟨X (.inl i), isRestricted_X _ _⟩ : Flat) = ⟨X i, isRestricted_X c i⟩ := by
  apply eq_of_map_subtype_eq
  rw [map_subtype_restrictedSumEquiv, sumAlgEquiv_X_inl, map_X]

/-- `restrictedSumEquiv` sends a variable of the second family to the corresponding constant. -/
@[simp]
theorem restrictedSumEquiv_X_inr (j : τ) :
    restrictedSumEquiv (⟨X (.inr j), isRestricted_X _ _⟩ : Flat) =
      algebraMap Inner Iter ⟨X j, isRestricted_X d j⟩ := by
  apply eq_of_map_subtype_eq
  rw [map_subtype_restrictedSumEquiv, sumAlgEquiv_X_inr, coe_algebraMap_isRestrictedSubring_apply,
    map_C, Algebra.algebraMap_self_apply, Subring.subtype_apply]

/-- `restrictedSumEquiv` is compatible with the polynomial inclusions: a polynomial in `σ ⊕ τ` goes
to the polynomial in `σ` whose coefficients are its coefficients in `τ`, read through
`MvPolynomial.sumAlgEquiv`. -/
theorem restrictedSumEquiv_polynomialToRestricted (p : MvPolynomial (σ ⊕ τ) R) :
    restrictedSumEquiv (polynomialToRestricted (Sum.elim c d) p) =
      polynomialToRestricted c ((MvPolynomial.sumAlgEquiv R σ τ p).map
        (polynomialToRestricted (R := R) d : MvPolynomial τ R →+* Inner)) := by
  refine DFunLike.congr_fun (MvPolynomial.ringHom_ext
    (f := (restrictedSumEquiv : Flat ≃+* Iter).toRingHom.comp
      (polynomialToRestricted (R := R) (Sum.elim c d) : MvPolynomial (σ ⊕ τ) R →+* Flat))
    (g := ((polynomialToRestricted (R := Inner) c : MvPolynomial σ Inner →+* Iter).comp
      (MvPolynomial.map (polynomialToRestricted (R := R) d : MvPolynomial τ R →+* Inner))).comp
        (MvPolynomial.sumAlgEquiv R σ τ : MvPolynomial (σ ⊕ τ) R →+* _)) (fun r ↦ ?_) ?_) p
  · refine Subtype.ext ?_
    simp [← MvPolynomial.algebraMap_eq, coe_algebraMap_isRestrictedSubring_apply]
  · rintro (i | j)
    · simp
    · simp [← MvPolynomial.algebraMap_eq]

/-! ### Renaming and reassociating the families of variables -/

section Rename

variable {σ' τ' υ : Type*} {ρ : υ → ℝ} [∀ k, Fact (0 < ρ k)]

/-- **Reassociating three families of variables.** Renaming along `Equiv.sumAssoc` is an
`R`-algebra isomorphism `R{(X, Y)/(c, d), Z/ρ} ≃ R{X/c, (Y, Z)/(d, ρ)}`, preserving the Gauss
norms. -/
noncomputable def restrictedSumAssoc :
    IsRestricted.subring (R := R) (Sum.elim (Sum.elim c d) ρ) ≃ₐ[R]
      IsRestricted.subring (R := R) (Sum.elim c (Sum.elim d ρ)) :=
  IsRestricted.renameAlgEquivOfEq (Equiv.sumAssoc σ τ υ) _
    (by funext x; rcases x with (i | j) | k <;> rfl)

omit [∀ i, Fact (0 < c i)] [∀ j, Fact (0 < d j)] [∀ k, Fact (0 < ρ k)] in
/-- `restrictedSumAssoc` renames the underlying series along `Equiv.sumAssoc`. -/
@[simp]
theorem coe_restrictedSumAssoc (f : IsRestricted.subring (R := R) (Sum.elim (Sum.elim c d) ρ)) :
    (restrictedSumAssoc f : MvPowerSeries (σ ⊕ (τ ⊕ υ)) R) =
      rename (Equiv.sumAssoc σ τ υ) (f : MvPowerSeries ((σ ⊕ τ) ⊕ υ) R) :=
  IsRestricted.coe_renameAlgEquivOfEq _ _ _ f

/-- `restrictedSumAssoc` preserves the Gauss norms. -/
@[simp]
theorem norm_restrictedSumAssoc (f : IsRestricted.subring (R := R) (Sum.elim (Sum.elim c d) ρ)) :
    ‖restrictedSumAssoc f‖ = ‖f‖ :=
  IsRestricted.norm_renameAlgEquivOfEq _ _ _ f

/-- `restrictedSumAssoc` is an isometry for the Gauss norms. -/
theorem isometry_restrictedSumAssoc :
    Isometry (restrictedSumAssoc (R := R) (c := c) (d := d) (ρ := ρ)) :=
  AddMonoidHomClass.isometry_iff_norm _ |>.mpr norm_restrictedSumAssoc

/-- **Iteration is associative.** Separating the last family `Z` from `R{X/c, Y/d, Z/ρ}` and then
`Y` from the remaining outer family `(X, Y)`, over the coefficient ring `R{Z/ρ}`, gives the same
series in `X` over `R{Z/ρ}{Y/d}` as reassociating, separating `(Y, Z)` and then separating `Z`
coefficientwise. -/
theorem map_restrictedSumEquiv_restrictedSumAssoc
    (f : IsRestricted.subring (R := R) (Sum.elim (Sum.elim c d) ρ)) :
    map (restrictedSumEquiv (R := R) (c := d) (d := ρ) :
        IsRestricted.subring (R := R) (Sum.elim d ρ) →+*
          IsRestricted.subring (R := IsRestricted.subring (R := R) ρ) d)
        (restrictedSumEquiv (restrictedSumAssoc f) :
          MvPowerSeries σ (IsRestricted.subring (R := R) (Sum.elim d ρ))) =
      (restrictedSumEquiv (R := IsRestricted.subring (R := R) ρ) (c := c) (d := d)
          (restrictedSumEquiv (R := R) (c := Sum.elim c d) (d := ρ) f) :
        MvPowerSeries σ (IsRestricted.subring (R := IsRestricted.subring (R := R) ρ) d)) := by
  refine MvPowerSeries.ext fun a ↦ Subtype.ext <| MvPowerSeries.ext fun b ↦ Subtype.ext <|
    MvPowerSeries.ext fun k ↦ ?_
  have hk : ((a.sumElim b).sumElim k).equivMapDomain (Equiv.sumAssoc σ τ υ) =
      a.sumElim (b.sumElim k) :=
    Finsupp.ext fun x ↦ by rcases x with i | j | l <;> simp [Finsupp.equivMapDomain_apply]
  simp only [coeff_map, RingHom.coe_coe, coeff_coeff_restrictedSumEquiv, coe_restrictedSumAssoc,
    ← hk, coeff_equivMapDomain_rename]

variable (e₁ : σ' ≃ σ) (e₂ : τ' ≃ τ)

/-- **Renaming each family of variables.** For `e₁ : σ' ≃ σ` and `e₂ : τ' ≃ τ`, renaming along
`Equiv.sumCongr e₁ e₂` is an `R`-algebra isomorphism `R{X'/(c ∘ e₁), Y'/(d ∘ e₂)} ≃ R{X/c, Y/d}`,
preserving the Gauss norms. -/
noncomputable def restrictedSumCongr :
    IsRestricted.subring (R := R) (Sum.elim (c ∘ e₁) (d ∘ e₂)) ≃ₐ[R] Flat :=
  IsRestricted.renameAlgEquivOfEq (Equiv.sumCongr e₁ e₂) _
    (by funext x; rcases x with i | j <;> rfl)

omit [∀ i, Fact (0 < c i)] [∀ j, Fact (0 < d j)] in
/-- `restrictedSumCongr` renames the underlying series along `Equiv.sumCongr`. -/
@[simp]
theorem coe_restrictedSumCongr (f : IsRestricted.subring (R := R) (Sum.elim (c ∘ e₁) (d ∘ e₂))) :
    (restrictedSumCongr e₁ e₂ f : MvPowerSeries (σ ⊕ τ) R) =
      rename (Equiv.sumCongr e₁ e₂) (f : MvPowerSeries (σ' ⊕ τ') R) :=
  IsRestricted.coe_renameAlgEquivOfEq _ _ _ f

/-- `restrictedSumCongr` preserves the Gauss norms. -/
@[simp]
theorem norm_restrictedSumCongr (f : IsRestricted.subring (R := R) (Sum.elim (c ∘ e₁) (d ∘ e₂))) :
    ‖restrictedSumCongr e₁ e₂ f‖ = ‖f‖ :=
  IsRestricted.norm_renameAlgEquivOfEq _ _ _ f

/-- `restrictedSumCongr` is an isometry for the Gauss norms. -/
theorem isometry_restrictedSumCongr :
    Isometry (restrictedSumCongr (R := R) (c := c) (d := d) e₁ e₂) :=
  AddMonoidHomClass.isometry_iff_norm _ |>.mpr (norm_restrictedSumCongr e₁ e₂)

/-- **Iteration commutes with renaming.** Renaming both families and then separating `Y` is
separating `Y'` first, renaming the coefficients along `e₂` and then the outer variables along
`e₁`. -/
theorem coe_restrictedSumEquiv_restrictedSumCongr
    (f : IsRestricted.subring (R := R) (Sum.elim (c ∘ e₁) (d ∘ e₂))) :
    (restrictedSumEquiv (restrictedSumCongr e₁ e₂ f) : MvPowerSeries σ Inner) =
      rename e₁ (map (IsRestricted.renameAlgEquiv (R := R) e₂ d :
          IsRestricted.subring (R := R) (d ∘ e₂) →+* Inner)
        (restrictedSumEquiv f : MvPowerSeries σ' (IsRestricted.subring (R := R) (d ∘ e₂)))) := by
  refine MvPowerSeries.ext fun a ↦ Subtype.ext <| MvPowerSeries.ext fun b ↦ ?_
  obtain ⟨a, rfl⟩ := (Finsupp.equivCongrLeft e₁).surjective a
  obtain ⟨b, rfl⟩ := (Finsupp.equivCongrLeft e₂).surjective b
  have hab : (a.equivMapDomain e₁).sumElim (b.equivMapDomain e₂) =
      (a.sumElim b).equivMapDomain (Equiv.sumCongr e₁ e₂) :=
    Finsupp.ext fun x ↦ by rcases x with i | j <;> simp [Finsupp.equivMapDomain_apply]
  simp [hab]

end Rename

end TauCeti.MvPowerSeries

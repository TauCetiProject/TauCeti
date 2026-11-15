/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.FormalGroup.Isogeny
public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.MulByInt.Hom
public import TauCeti.RingTheory.FormalGroup.ZSMul

/-!
# The formal power series of a morphism and of multiplication by `n`

Extending `Isogeny.formalSeries` by `0 ↦ 0` defines `Hom.formalSeries : Hom W₁ W₂ → K⟦X⟧` on the
full additive group of morphisms of elliptic curves.

Using `Isogeny.formalSeries_eq_subst_of_ofIsogeny_add_eq`, this file shows that `Hom.formalSeries`
is injective (`Hom.formalSeries_injective`), sends sums in `Hom W₁ W₂` to formal-group sums in
`formalGroup W₂` (`Hom.formalSeries_add`), and hence upgrades to an additive group homomorphism
`Hom.formalPointAddHom : Hom W₁ W₂ →+ (formalGroup W₂).Point Unit`. In particular, `n • f` expands
to `(formalGroup W₂).zsmulSeries n` evaluated at `f.formalSeries` (`Hom.formalSeries_zsmul`), and
the multiplication-by-`n` isogeny `[n] : W → W` expands to `(formalGroup W).zsmulSeries n`
(`Isogeny.formalSeries_mulByIntIsogeny`, `Isogeny.formalSeries_mulByIntIsogenyOfNeZero`).

## Main definitions

* `TauCeti.Isogeny.Hom.formalSeries`: the formal series of a morphism, `0` on the zero morphism.
* `TauCeti.Isogeny.Hom.formalPointAddHom`: `Hom.formalSeries` as an additive group homomorphism
  into `(formalGroup W₂).Point Unit`.
* `TauCeti.Isogeny.Hom.formalGroupHom`: the `FormalGroupHom` induced by a morphism.

## Main results

* `TauCeti.Isogeny.Hom.formalSeries_injective`: a morphism is determined by its formal series.
* `TauCeti.Isogeny.Hom.formalSeries_add`, `TauCeti.Isogeny.Hom.formalSeries_zsmul`,
  `TauCeti.Isogeny.Hom.formalSeries_nsmul`: additivity and linearity of `Hom.formalSeries` in the
  target formal group law.
* `TauCeti.Isogeny.formalSeries_mulByIntIsogeny`,
  `TauCeti.Isogeny.formalSeries_mulByIntIsogenyOfNeZero`,
  `TauCeti.Isogeny.formalGroupHom_mulByIntIsogeny`,
  `TauCeti.Isogeny.formalGroupHom_mulByIntIsogenyOfNeZero`: `[n]` expands to
  `(formalGroup W).zsmulSeries n` and induces `(formalGroup W).zsmulHom n`.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], IV.4.
-/

public section

open WeierstrassCurve
open scoped PowerSeries

namespace TauCeti.Isogeny

namespace Hom

variable {K : Type*} [Field K] {W W₁ W₂ W₃ : WeierstrassCurve K}

open scoped Classical in
/-- **The formal power series of a morphism** `f : Hom W₁ W₂`, equal to
`(toIsogeny hf).formalSeries` when `f ≠ 0` and `0` on the zero morphism. -/
noncomputable def formalSeries (f : Hom W₁.toAffine W₂.toAffine) : K⟦X⟧ :=
  if hf : f = 0 then 0 else (toIsogeny hf).formalSeries

open scoped Classical in
/-- Unfolding `Hom.formalSeries`. -/
theorem formalSeries_def (f : Hom W₁.toAffine W₂.toAffine) :
    f.formalSeries = if hf : f = 0 then 0 else (toIsogeny hf).formalSeries :=
  (rfl)

/-- The formal series of the zero morphism is `0`. -/
@[simp]
theorem formalSeries_zero : (0 : Hom W₁.toAffine W₂.toAffine).formalSeries = 0 := by
  classical
  simp [formalSeries]

/-- On `ofIsogeny φ`, `Hom.formalSeries` agrees with `Isogeny.formalSeries`. -/
@[simp]
theorem formalSeries_ofIsogeny (φ : Isogeny W₁.toAffine W₂.toAffine) :
    (ofIsogeny φ).formalSeries = φ.formalSeries := by
  classical
  simp [formalSeries]

/-- The formal series of a morphism vanishes if and only if the morphism is zero. -/
@[simp]
theorem formalSeries_eq_zero_iff {f : Hom W₁.toAffine W₂.toAffine} :
    f.formalSeries = 0 ↔ f = 0 := by
  rcases eq_zero_or_exists_ofIsogeny f with rfl | ⟨φ, rfl⟩
  · simp
  · simp [φ.formalSeries_ne_zero]

/-- **A morphism is determined by its formal series.** -/
theorem formalSeries_injective :
    Function.Injective (formalSeries (W₁ := W₁) (W₂ := W₂)) := by
  intro f g h
  rcases eq_zero_or_exists_ofIsogeny f with rfl | ⟨φ, rfl⟩
  · exact (formalSeries_eq_zero_iff.mp (by simpa using h.symm)).symm
  rcases eq_zero_or_exists_ofIsogeny g with rfl | ⟨ψ, rfl⟩
  · exact formalSeries_eq_zero_iff.mp (by simpa using h)
  · rw [formalSeries_ofIsogeny, formalSeries_ofIsogeny] at h
    exact congrArg ofIsogeny (Isogeny.formalSeries_injective h)

/-- Two morphisms have equal formal series if and only if they are equal. -/
@[simp]
theorem formalSeries_inj {f g : Hom W₁.toAffine W₂.toAffine} :
    f.formalSeries = g.formalSeries ↔ f = g :=
  formalSeries_injective.eq_iff

/-- Every morphism's formal series has zero constant coefficient. -/
@[simp↓]
theorem constantCoeff_formalSeries (f : Hom W₁.toAffine W₂.toAffine) :
    PowerSeries.constantCoeff f.formalSeries = 0 := by
  rcases eq_zero_or_exists_ofIsogeny f with rfl | ⟨φ, rfl⟩ <;> simp

/-- Every morphism's formal series is valid for power-series substitution. -/
theorem hasSubst_formalSeries (f : Hom W₁.toAffine W₂.toAffine) :
    PowerSeries.HasSubst f.formalSeries :=
  .of_constantCoeff_zero' f.constantCoeff_formalSeries

/-- The formal series of `Hom.id` is `X`. -/
@[simp]
theorem formalSeries_id (W : WeierstrassCurve K) :
    (Hom.id W.toAffine).formalSeries = PowerSeries.X := by
  rw [Hom.id_def, formalSeries_ofIsogeny, Isogeny.formalSeries_id]

/-- The formal series of `1 : Hom W W` is `X`. -/
theorem formalSeries_one (W : WeierstrassCurve K) :
    (1 : Hom W.toAffine W.toAffine).formalSeries = PowerSeries.X :=
  formalSeries_id W

/-- **Composition of morphisms corresponds to substitution of formal series.** -/
@[simp]
theorem formalSeries_comp (g : Hom W₂.toAffine W₃.toAffine) (f : Hom W₁.toAffine W₂.toAffine) :
    (g.comp f).formalSeries = PowerSeries.subst f.formalSeries g.formalSeries := by
  rcases eq_zero_or_exists_ofIsogeny g with rfl | ⟨ψ, rfl⟩
  · rw [zero_comp, formalSeries_zero, formalSeries_zero,
      ← PowerSeries.coe_substAlgHom f.hasSubst_formalSeries, map_zero]
  rcases eq_zero_or_exists_ofIsogeny f with rfl | ⟨φ, rfl⟩
  · rw [comp_zero, formalSeries_zero, formalSeries_zero, formalSeries_ofIsogeny,
      PowerSeries.subst_zero_of_constantCoeff_zero ψ.constantCoeff_formalSeries]
  · rw [ofIsogeny_comp_ofIsogeny, formalSeries_ofIsogeny, formalSeries_ofIsogeny,
      formalSeries_ofIsogeny, φ.formalSeries_comp ψ]

/-- **Negation of a morphism substitutes into `W₂.formalInverse`.** -/
@[simp]
theorem formalSeries_neg (f : Hom W₁.toAffine W₂.toAffine) :
    (-f).formalSeries = PowerSeries.subst f.formalSeries W₂.formalInverse := by
  rw [neg_def, formalSeries_comp, formalSeries_ofIsogeny, formalSeries_negIsogeny]

/-- **The formal series of a sum of morphisms is the formal-group sum of their formal series.** -/
@[simp]
theorem formalSeries_add [W₂.IsElliptic] (f g : Hom W₁.toAffine W₂.toAffine) :
    (f + g).formalSeries =
      (formalGroup W₂).toPowerSeries.subst ![f.formalSeries, g.formalSeries] := by
  rcases eq_zero_or_exists_ofIsogeny f with rfl | ⟨φ, rfl⟩
  · rw [zero_add, formalSeries_zero, (formalGroup W₂).zero_add g.hasSubst_formalSeries]
  rcases eq_zero_or_exists_ofIsogeny g with rfl | ⟨ψ, rfl⟩
  · rw [add_zero, formalSeries_zero,
      (formalGroup W₂).add_zero (ofIsogeny φ).hasSubst_formalSeries]
  rcases eq_zero_or_exists_ofIsogeny (ofIsogeny φ + ofIsogeny ψ) with hfg0 | ⟨χ, hχ⟩
  · have hneg : ofIsogeny φ = -ofIsogeny ψ := add_eq_zero_iff_eq_neg.mp hfg0
    rw [hfg0, formalSeries_zero, hneg, formalSeries_neg, formalSeries_ofIsogeny,
      ← formalGroup_addInvX, FormalGroup.subst_addInvX_self_eq_zero
        (formalGroup W₂) (.of_constantCoeff_zero' ψ.constantCoeff_formalSeries)]
  · rw [hχ, formalSeries_ofIsogeny, formalSeries_ofIsogeny, formalSeries_ofIsogeny,
      formalSeries_eq_subst_of_ofIsogeny_add_eq hχ]

/-- **A morphism viewed as a point of `(formalGroup W₂).Point Unit`**, as an additive group
homomorphism `Hom W₁ W₂ →+ (formalGroup W₂).Point Unit`. -/
noncomputable def formalPointAddHom [W₂.IsElliptic] :
    Hom W₁.toAffine W₂.toAffine →+ (formalGroup W₂).Point Unit where
  toFun f := ⟨f.formalSeries, f.hasSubst_formalSeries⟩
  map_zero' := Subtype.ext formalSeries_zero
  map_add' f g := Subtype.ext (formalSeries_add f g)

/-- Applying `formalPointAddHom` wraps `f.formalSeries` as a formal-group point. -/
@[simp]
theorem formalPointAddHom_apply [W₂.IsElliptic] (f : Hom W₁.toAffine W₂.toAffine) :
    formalPointAddHom f = ⟨f.formalSeries, f.hasSubst_formalSeries⟩ :=
  (rfl)

/-- The underlying power series of `formalPointAddHom f` is `f.formalSeries`. -/
theorem val_formalPointAddHom [W₂.IsElliptic] (f : Hom W₁.toAffine W₂.toAffine) :
    (formalPointAddHom f).val = f.formalSeries :=
  (rfl)

/-- **The formal series of `n • f` is `[n](f.formalSeries)`** for every integer `n`. -/
@[simp]
theorem formalSeries_zsmul [W₂.IsElliptic] (n : ℤ) (f : Hom W₁.toAffine W₂.toAffine) :
    (n • f).formalSeries = PowerSeries.subst f.formalSeries ((formalGroup W₂).zsmulSeries n) := by
  have h := congrArg Subtype.val ((formalPointAddHom (W₁ := W₁) (W₂ := W₂)).map_zsmul n f)
  rw [val_formalPointAddHom, ← (formalGroup W₂).subst_zsmulSeries (formalPointAddHom f) n,
    val_formalPointAddHom] at h
  exact h

/-- **The formal series of `n • f` is `[n](f.formalSeries)`** for every natural `n`. -/
@[simp]
theorem formalSeries_nsmul [W₂.IsElliptic] (n : ℕ) (f : Hom W₁.toAffine W₂.toAffine) :
    (n • f).formalSeries = PowerSeries.subst f.formalSeries ((formalGroup W₂).nsmulSeries n) := by
  rw [← natCast_zsmul, formalSeries_zsmul, FormalGroup.zsmulSeries_natCast]

/-- **The formal group homomorphism induced by a morphism** `f : Hom W₁ W₂`, sending the zero
morphism to the zero series. -/
noncomputable def formalGroupHom [W₂.IsElliptic] (f : Hom W₁.toAffine W₂.toAffine) :
    FormalGroupHom (formalGroup W₁) (formalGroup W₂) where
  toPowerSeries := f.formalSeries
  zero_constantCoeff := f.constantCoeff_formalSeries
  hom := by
    rcases eq_zero_or_exists_ofIsogeny f with rfl | ⟨φ, rfl⟩
    · rw [formalSeries_zero]
      exact (FormalGroup.homDefect_eq_zero_iff _ _).mp FormalGroup.homDefect_zero
    · rw [formalSeries_ofIsogeny]
      exact φ.subst_formalGroup_formalSeries

/-- The underlying power series of `Hom.formalGroupHom f` is `f.formalSeries`. -/
@[simp]
theorem formalGroupHom_toPowerSeries [W₂.IsElliptic] (f : Hom W₁.toAffine W₂.toAffine) :
    f.formalGroupHom.toPowerSeries = f.formalSeries :=
  (rfl)

end Hom

/-! ### Formal series of multiplication by `n` -/

section MulByInt

variable {K : Type*} [Field K] (W : WeierstrassCurve K) [W.IsElliptic]

/-- **Multiplication by `n` expands to `(formalGroup W).zsmulSeries n`.** -/
@[simp]
theorem formalSeries_mulByIntIsogeny {n : ℤ} (hn : psiFunctionField W.toAffine n ≠ 0) :
    (mulByIntIsogeny W.toAffine hn).formalSeries = (formalGroup W).zsmulSeries n := by
  rw [← Hom.formalSeries_ofIsogeny, ofIsogeny_mulByIntIsogeny, Hom.formalSeries_zsmul,
    Hom.formalSeries_id, PowerSeries.X_subst]

/-- **Multiplication by a nonzero integer `n` expands to `(formalGroup W).zsmulSeries n`.** -/
theorem formalSeries_mulByIntIsogenyOfNeZero {n : ℤ} (hn : n ≠ 0) :
    (mulByIntIsogenyOfNeZero W.toAffine hn).formalSeries = (formalGroup W).zsmulSeries n :=
  formalSeries_mulByIntIsogeny W _

/-- **Multiplication by `n` induces `(formalGroup W).zsmulHom n` on the formal group.** -/
@[simp]
theorem formalGroupHom_mulByIntIsogeny {n : ℤ} (hn : psiFunctionField W.toAffine n ≠ 0) :
    (mulByIntIsogeny W.toAffine hn).formalGroupHom = (formalGroup W).zsmulHom n := by
  ext : 1
  rw [formalGroupHom_toPowerSeries, FormalGroup.zsmulHom_toPowerSeries]
  exact formalSeries_mulByIntIsogeny W hn

/-- **Multiplication by a nonzero integer `n` induces `(formalGroup W).zsmulHom n` on the formal
group.** -/
theorem formalGroupHom_mulByIntIsogenyOfNeZero {n : ℤ} (hn : n ≠ 0) :
    (mulByIntIsogenyOfNeZero W.toAffine hn).formalGroupHom = (formalGroup W).zsmulHom n :=
  formalGroupHom_mulByIntIsogeny W _

end MulByInt

end TauCeti.Isogeny

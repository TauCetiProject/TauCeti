/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.FormalSeries
public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.Hom.BaseChange

/-!
# The formal power series of a morphism of Weierstrass curves

`Isogeny.formalSeries` extends from nonzero isogenies to the pointed-morphism carrier `Hom W₁ W₂`
by stipulating `0` for the zero morphism (`TauCeti.Isogeny.Hom.formalSeries`). Because every
isogeny has a nonzero formal series (`TauCeti.Isogeny.formalSeries_ne_zero`) and is determined by
it (`TauCeti.Isogeny.formalSeries_injective`), this extension is faithful on arbitrary Weierstrass
curves over a field `K`, preserves identity and composition, and commutes with coefficient-field
homomorphisms (`TauCeti.Isogeny.Hom.formalSeries_map`). No ellipticity hypothesis is placed on `W₁`
or `W₂` here; compatibility with addition when `W₂` is elliptic is proved in
`TauCeti.AlgebraicGeometry.EllipticCurve.FormalGroup.Isogeny`.

## Main definitions

* `TauCeti.Isogeny.Hom.formalSeries`: the formal power series of `f : Hom W₁ W₂`, sending `0` to
  `0` and a nonzero morphism to `(toIsogeny hf).formalSeries`.

## Main results

* `TauCeti.Isogeny.Hom.formalSeries_zero`, `TauCeti.Isogeny.Hom.formalSeries_ofIsogeny`, and
  `TauCeti.Isogeny.Hom.formalSeries_toIsogeny`: values on `0` and on nonzero morphisms.
* `TauCeti.Isogeny.Hom.formalSeries_eq_zero_iff`, `TauCeti.Isogeny.Hom.formalSeries_injective`, and
  `TauCeti.Isogeny.Hom.formalSeries_inj`: faithfulness of the formal-series expansion.
* `TauCeti.Isogeny.Hom.formalSeries_id`, `TauCeti.Isogeny.Hom.formalSeries_comp`, and
  `TauCeti.Isogeny.Hom.formalSeries_map`: functoriality under composition and base change.

## References

* [J. H. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], IV.4.
-/

public section

open WeierstrassCurve
open scoped PowerSeries

namespace TauCeti.Isogeny.Hom

variable {K : Type*} [Field K] {W₁ W₂ W₃ : WeierstrassCurve K}

open scoped Classical in
/-- **The formal power series of a morphism `f : Hom W₁ W₂`**, stipulating `0` for the zero
morphism and `(toIsogeny hf).formalSeries` for a nonzero morphism. -/
noncomputable def formalSeries (f : Hom W₁.toAffine W₂.toAffine) : K⟦X⟧ :=
  if hf : f = 0 then 0 else (toIsogeny hf).formalSeries

/-- The zero morphism induces the zero formal series. -/
@[simp]
theorem formalSeries_zero : (0 : Hom W₁.toAffine W₂.toAffine).formalSeries = 0 := by
  classical simp [formalSeries]

/-- The formal series of `Hom.ofIsogeny φ` is `φ.formalSeries`. -/
@[simp]
theorem formalSeries_ofIsogeny (φ : Isogeny W₁.toAffine W₂.toAffine) :
    (ofIsogeny φ).formalSeries = φ.formalSeries := by
  classical simp [formalSeries]

/-- Extracting the isogeny of a nonzero morphism preserves its formal series. -/
@[simp]
theorem formalSeries_toIsogeny {f : Hom W₁.toAffine W₂.toAffine} (hf : f ≠ 0) :
    (toIsogeny hf).formalSeries = f.formalSeries := by
  classical simp [formalSeries, hf]

/-- **A morphism's formal series vanishes if and only if the morphism is zero.** -/
@[simp]
theorem formalSeries_eq_zero_iff {f : Hom W₁.toAffine W₂.toAffine} :
    f.formalSeries = 0 ↔ f = 0 := by
  rcases eq_zero_or_exists_ofIsogeny f with rfl | ⟨φ, rfl⟩
  · simp
  · simp [φ.formalSeries_ne_zero]

/-- **A morphism of Weierstrass curves is determined by its formal power series.** -/
theorem formalSeries_injective :
    Function.Injective (formalSeries (W₁ := W₁) (W₂ := W₂)) := by
  intro f g h
  rcases eq_zero_or_exists_ofIsogeny f with rfl | ⟨φ, rfl⟩
  · rw [formalSeries_zero, eq_comm, formalSeries_eq_zero_iff] at h
    exact h.symm
  rcases eq_zero_or_exists_ofIsogeny g with rfl | ⟨ψ, rfl⟩
  · rw [formalSeries_ofIsogeny, formalSeries_zero] at h
    exact absurd h φ.formalSeries_ne_zero
  rw [formalSeries_ofIsogeny, formalSeries_ofIsogeny] at h
  exact congrArg ofIsogeny (Isogeny.formalSeries_injective h)

/-- Two morphisms have the same formal power series if and only if they are equal. -/
@[simp]
theorem formalSeries_inj {f g : Hom W₁.toAffine W₂.toAffine} :
    f.formalSeries = g.formalSeries ↔ f = g :=
  formalSeries_injective.eq_iff

/-- **Every morphism's formal series has zero constant coefficient.** -/
@[simp]
theorem constantCoeff_formalSeries (f : Hom W₁.toAffine W₂.toAffine) :
    PowerSeries.constantCoeff f.formalSeries = 0 := by
  rcases eq_zero_or_exists_ofIsogeny f with rfl | ⟨φ, rfl⟩ <;> simp

/-- **The identity morphism induces the formal series `X`.** -/
@[simp]
theorem formalSeries_id (W : WeierstrassCurve K) :
    (Hom.id W.toAffine).formalSeries = PowerSeries.X := by
  rw [Hom.id_def, formalSeries_ofIsogeny, Isogeny.formalSeries_id]

/-- **Composition of morphisms induces composition of their formal series.** -/
@[simp]
theorem formalSeries_comp (g : Hom W₂.toAffine W₃.toAffine) (f : Hom W₁.toAffine W₂.toAffine) :
    (g.comp f).formalSeries = PowerSeries.subst f.formalSeries g.formalSeries := by
  rcases eq_zero_or_exists_ofIsogeny g with rfl | ⟨ψ, rfl⟩
  · simp [PowerSeries.subst_zero]
  rcases eq_zero_or_exists_ofIsogeny f with rfl | ⟨φ, rfl⟩
  · simp [PowerSeries.subst_zero_of_constantCoeff_zero ψ.constantCoeff_formalSeries]
  · rw [ofIsogeny_comp_ofIsogeny, formalSeries_ofIsogeny, formalSeries_ofIsogeny,
      formalSeries_ofIsogeny, Isogeny.formalSeries_comp]

/-- **Base change of a morphism maps the coefficients of its formal series.** -/
@[simp]
theorem formalSeries_map {L : Type*} [Field L] (f : Hom W₁.toAffine W₂.toAffine) (σ : K →+* L) :
    (f.map σ).formalSeries = PowerSeries.map σ f.formalSeries := by
  rcases eq_zero_or_exists_ofIsogeny f with rfl | ⟨φ, rfl⟩
  · simp [zero_map]
  · rw [ofIsogeny_map, formalSeries_ofIsogeny, formalSeries_ofIsogeny, Isogeny.formalSeries_map]

end TauCeti.Isogeny.Hom

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Crystal.Basic

/-!
# Direct sums of normal crystals

The direct sum of a family of normal crystals is the disjoint union of the underlying types, on
which the root operators act within each summand. It is the coproduct for strict morphisms.

## Main definitions

* `TauCeti.NormalCrystal.sigma`: the direct sum of a family of normal crystals.
* `TauCeti.NormalCrystal.StrictHom.sigmaMk`: the inclusions of the summands.
* `TauCeti.NormalCrystal.StrictHom.sigmaElim`: the strict morphism out of the sum induced by
  strict morphisms out of the summands.

## Main results

* `TauCeti.NormalCrystal.StrictHom.sigmaElim_comp_sigmaMk`,
  `TauCeti.NormalCrystal.StrictHom.sigma_ext`: the universal property of the direct sum.

## References

* M. Kashiwara, *On crystal bases*, CMS Conf. Proc. 16 (1995), §7.
* D. Bump and A. Schilling, *Crystal bases: representations and combinatorics*, World Scientific
  (2017), Ch. 2.
-/

public section

namespace TauCeti

namespace NormalCrystal

universe u v w x₁

variable {ι : Type u} {X : Type v} {Y : Type w} [AddCommGroup X] [AddCommGroup Y]
  {P : RootDatum ι X Y} {b : P.Base} {B' : Type x₁}

section Sigma

variable {κ : Type*} {β : κ → Type*} (c : ∀ k, NormalCrystal P b (β k))

/-- The **direct sum** of a family of normal crystals: the disjoint union of the underlying types,
on which the root operators act within each summand. -/
def sigma : NormalCrystal P b (Σ k, β k) where
  wt x := (c x.1).wt x.2
  e i x := ((c x.1).e i x.2).map (Sigma.mk x.1)
  f i x := ((c x.1).f i x.2).map (Sigma.mk x.1)
  ε i x := (c x.1).ε i x.2
  φ i x := (c x.1).φ i x.2
  f_eq_some_iff {i x y} := by
    obtain ⟨k, x⟩ := x
    obtain ⟨l, y⟩ := y
    simp only [Option.map_eq_some_iff, Sigma.mk.injEq]
    constructor
    · rintro ⟨z, hz, rfl, hzy⟩
      obtain rfl := eq_of_heq hzy
      exact ⟨x, (c k).f_eq_some_iff.1 hz, rfl, .rfl⟩
    · rintro ⟨z, hz, rfl, hzy⟩
      obtain rfl := eq_of_heq hzy
      exact ⟨y, (c l).f_eq_some_iff.2 hz, rfl, .rfl⟩
  wt_of_e_eq_some {i x y} h := by
    obtain ⟨z, hz, rfl⟩ := Option.map_eq_some_iff.1 h
    exact (c x.1).wt_of_e_eq_some hz
  ε_eq_zero_iff := by simp [(c _).ε_eq_zero_iff]
  ε_of_e_eq_some {i x y} h := by
    obtain ⟨z, hz, rfl⟩ := Option.map_eq_some_iff.1 h
    exact (c x.1).ε_of_e_eq_some hz
  φ_eq_zero_iff := by simp [(c _).φ_eq_zero_iff]
  φ_sub_ε i x := (c x.1).φ_sub_ε i x.2

variable {c} {i : b.support} {k : κ} (x : β k)

@[simp]
theorem sigma_wt : (sigma c).wt ⟨k, x⟩ = (c k).wt x := (rfl)

@[simp]
theorem sigma_e : (sigma c).e i ⟨k, x⟩ = ((c k).e i x).map (Sigma.mk k) := (rfl)

@[simp]
theorem sigma_f : (sigma c).f i ⟨k, x⟩ = ((c k).f i x).map (Sigma.mk k) := (rfl)

@[simp]
theorem sigma_ε : (sigma c).ε i ⟨k, x⟩ = (c k).ε i x := (rfl)

@[simp]
theorem sigma_φ : (sigma c).φ i ⟨k, x⟩ = (c k).φ i x := (rfl)

namespace StrictHom

variable (c) in
/-- The inclusion of a summand into a direct sum. -/
def sigmaMk (k : κ) : StrictHom (c k) (sigma c) where
  toFun := Sigma.mk k
  wt_toFun _ := rfl
  e_toFun _ _ := rfl

@[simp]
theorem sigmaMk_apply : sigmaMk c k x = ⟨k, x⟩ := (rfl)

variable {d : NormalCrystal P b B'}

/-- The strict morphism out of a direct sum induced by strict morphisms out of the summands. -/
def sigmaElim (ψ : ∀ k, StrictHom (c k) d) : StrictHom (sigma c) d where
  toFun x := ψ x.1 x.2
  wt_toFun x := (ψ x.1).wt_apply x.2
  e_toFun i := fun ⟨k, x⟩ => by simp [Option.map_map, Function.comp_def]

@[simp]
theorem sigmaElim_apply (ψ : ∀ k, StrictHom (c k) d) : sigmaElim ψ ⟨k, x⟩ = ψ k x := (rfl)

@[simp]
theorem sigmaElim_comp_sigmaMk (ψ : ∀ k, StrictHom (c k) d) (k : κ) :
    (sigmaElim ψ).comp (sigmaMk c k) = ψ k :=
  ext fun _ => by simp

/-- Strict morphisms out of a direct sum are determined by their restrictions to the summands. -/
theorem sigma_ext {ψ χ : StrictHom (sigma c) d}
    (h : ∀ k, ψ.comp (sigmaMk c k) = χ.comp (sigmaMk c k)) : ψ = χ :=
  ext fun ⟨k, x⟩ => by simpa using DFunLike.congr_fun (h k) x

end StrictHom

end Sigma

end NormalCrystal

end TauCeti

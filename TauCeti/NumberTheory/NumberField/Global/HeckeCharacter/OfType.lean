/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.Global.Ideles.FiniteOpenSubgroup
public import TauCeti.RingTheory.DedekindDomain.FiniteAdeleRing.IdealCharacter

/-!
# Hecke characters of type `n` on the finite ideles

Let `K` be a number field. A character `ψ` of the finite ideles `𝔸_{K,f}ˣ` is a *Hecke character
of type `n`* (`MonoidHom.IsHeckeOfType`), for integers `n_w` indexed by the infinite places `w` of
`K`, if its kernel is open and `ψ(x) ∏_w (Φ_w(x) / |Φ_w(x)|) ^ n_w = 1` for every `x ∈ Kˣ`, where
`Φ_w : K → ℂ` is an embedding inducing `w`: on the principal ideles, `ψ` is inverse to the angular
character `∏_w (Φ_w / |Φ_w|) ^ n_w` at the infinite places.

Such a character is unitary (`MonoidHom.IsHeckeOfType.norm_eq_one`): `|ψ|` is trivial on `Kˣ` and
on an open subgroup, which together generate a subgroup of finite index. In particular its Euler
coefficients have modulus one (`MonoidHom.IsHeckeOfType.norm_heckeCoeff`), which is the bound under
which the Dirichlet series of its ideal character converges for `Re s > 1`.

## Main definitions

* `MonoidHom.IsHeckeOfType`: Hecke characters of type `n` on the finite ideles.

## Main results

* `MonoidHom.IsHeckeOfType.norm_eq_one`: a Hecke character of type `n` is unitary.
* `MonoidHom.IsHeckeOfType.norm_heckeCoeff`: its Euler coefficients have modulus one.

## Provenance

The unitarity of Hecke characters of type `n` corresponds to `New.IsHeckeOfType.norm_eq_one` and
`New.IsHeckeOfType.norm_heckeCoeff_le` of grh-lean (https://github.com/lsernau/grh-lean,
Apache 2.0, Copyright 2026 Anthropic PBC), file `src/Lib/ClassField/HeckeL/ContinuationAtOne.lean`.

## References

* J. Tate, *Fourier analysis in number fields and Hecke's zeta-functions*, in J. W. S. Cassels and
  A. Fröhlich (eds.), *Algebraic Number Theory*, Chapter XV.
* J. Neukirch, *Algebraic Number Theory*, Chapter VII, §6.
-/

public section

open IsDedekindDomain IsDedekindDomain.FiniteAdeleRing NumberField

namespace MonoidHom

section HeckeType

variable {K : Type*} [Field K] [NumberField K]

/-- A character `ψ` of the finite ideles of a number field `K` is a **Hecke character of type `n`**,
for integers `n w` indexed by the infinite places `w` of `K`, when its kernel is open and
`ψ(x) ∏_w (Φ_w(x) / |Φ_w(x)|) ^ n_w = 1` for every `x ∈ Kˣ`, where `Φ_w = w.embedding` is the
embedding `K → ℂ` inducing `w` chosen by Mathlib. Replacing `Φ_w` by its complex conjugate replaces
`n_w` by `-n_w`. -/
structure IsHeckeOfType (ψ : (FiniteAdeleRing (𝓞 K) K)ˣ →* ℂˣ) (n : InfinitePlace K → ℤ) :
    Prop where
  /-- The kernel of `ψ` is open. -/
  isOpen_ker : IsOpen (ψ.ker : Set (FiniteAdeleRing (𝓞 K) K)ˣ)
  /-- On the principal finite ideles, `ψ` inverts the angular character of type `n`. -/
  map_unitEmbedding_mul_prod_eq_one (x : Kˣ) :
    (ψ (unitEmbedding (𝓞 K) K x) : ℂ) *
      ∏ w, (w.embedding (x : K) / (‖w.embedding (x : K)‖ : ℂ)) ^ n w = 1

variable {ψ : (FiniteAdeleRing (𝓞 K) K)ˣ →* ℂˣ} {n : InfinitePlace K → ℤ}

/-- **A Hecke character of type `n` is unitary**: `|ψ(x)| = 1` for every finite idele `x`. The
finite ideles where `ψ` has modulus one form an open subgroup, as it contains the open kernel of
`ψ`, and it contains the principal finite ideles, on which `ψ` is a product of complex numbers of
modulus one. Such a subgroup has finite index
(`NumberField.finiteIndex_of_isOpen_of_totallyPositiveUnits_le`), so some power of every `x` lies
in it. -/
theorem IsHeckeOfType.norm_eq_one (hψ : ψ.IsHeckeOfType n) (x : (FiniteAdeleRing (𝓞 K) K)ˣ) :
    ‖(ψ x : ℂ)‖ = 1 := by
  -- the finite ideles where `ψ` has modulus one
  let H : Subgroup (FiniteAdeleRing (𝓞 K) K)ˣ :=
    { carrier := {y | ‖(ψ y : ℂ)‖ = 1}
      mul_mem' := fun {a b} ha hb ↦ by
        simp only [Set.mem_ofPred_eq, map_mul, Units.val_mul, norm_mul] at ha hb ⊢
        rw [ha, hb, one_mul]
      one_mem' := by simp
      inv_mem' := fun {a} ha ↦ by
        simp only [Set.mem_ofPred_eq, map_inv, Units.val_inv_eq_inv_val, norm_inv] at ha ⊢
        rw [ha, inv_one] }
  -- membership in `H` is its defining condition
  have hmem (y : (FiniteAdeleRing (𝓞 K) K)ˣ) : y ∈ H ↔ ‖(ψ y : ℂ)‖ = 1 := Iff.rfl
  have hopen : IsOpen (H : Set (FiniteAdeleRing (𝓞 K) K)ˣ) :=
    Subgroup.isOpen_mono (fun y hy ↦ (hmem y).mpr (by
      rw [MonoidHom.mem_ker.mp hy, Units.val_one, norm_one])) hψ.isOpen_ker
  have hpos : totallyPositiveUnits ≤ H.comap (unitEmbedding (𝓞 K) K) := fun y _ ↦ by
    refine (hmem _).mpr ?_
    -- every factor `Φ_w(y) / |Φ_w(y)|` of the product has modulus one
    have hprod : ‖∏ w, (w.embedding (y : K) / (‖w.embedding (y : K)‖ : ℂ)) ^ n w‖ = 1 := by
      rw [norm_prod]
      refine Finset.prod_eq_one fun w _ ↦ ?_
      have hne : ‖w.embedding (y : K)‖ ≠ 0 :=
        norm_ne_zero_iff.mpr ((map_ne_zero _).mpr y.ne_zero)
      rw [norm_zpow, norm_div, Complex.norm_real, norm_norm, div_self hne, one_zpow]
    have h := congrArg norm (hψ.map_unitEmbedding_mul_prod_eq_one y)
    rwa [norm_mul, hprod, mul_one, norm_one] at h
  have := finiteIndex_of_isOpen_of_totallyPositiveUnits_le hopen hpos
  have hx := (hmem _).mp (H.pow_index_mem x)
  rw [map_pow, Units.val_pow_eq_pow_val, norm_pow] at hx
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) Subgroup.FiniteIndex.index_ne_zero).mp hx

/-- The Euler coefficients of a Hecke character of type `n` have modulus one. -/
theorem IsHeckeOfType.norm_heckeCoeff (hψ : ψ.IsHeckeOfType n)
    (ϖ : ∀ v : HeightOneSpectrum (𝓞 K), (v.adicCompletion K)ˣ) (v : HeightOneSpectrum (𝓞 K)) :
    ‖ψ.heckeCoeff ϖ v‖ = 1 := by
  rw [heckeCoeff_def]
  exact hψ.norm_eq_one _

end HeckeType

end MonoidHom

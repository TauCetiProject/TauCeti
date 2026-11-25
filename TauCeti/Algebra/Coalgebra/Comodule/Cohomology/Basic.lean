/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.ConcreteCategory
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.RingTheory.Bialgebra.Basic
public import TauCeti.Algebra.Coalgebra.Comodule.Fixed
public import TauCeti.Algebra.Coalgebra.Comodule.Hom
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Module

/-!
# The Hochschild complex of a comodule

Let `H` be a bialgebra over a commutative ring `R` and `M` a right `H`-comodule with coaction `ρ`.
The Hochschild cochains of degree `n` are `Cⁿ(H, M) = M ⊗ H^⊗n`, bracketed to the left. There are
`n + 2` cofaces `δᵢ : Cⁿ(H, M) → Cⁿ⁺¹(H, M)`:

* `δ₀` applies `ρ` to the coefficient factor;
* for `1 ≤ i ≤ n`, `δᵢ` applies the comultiplication `Δ` to the `i`-th factor of `H`;
* `δₙ₊₁` appends the unit `1` of `H` at the end.

The differential is the alternating sum `d = ∑ᵢ (-1)ⁱ δᵢ`, in this order. This file proves
`d ∘ d = 0` (`d_comp_d`), assembles the cochain complex `cochainComplex R H M`, makes it functorial
in coefficient morphisms, which act on the first tensor factor (`cochainComplexMap`), and identifies
its cohomology in degree zero with the invariants `Mᴴ = {m | ρ m = m ⊗ 1}`, naturally in `M`
(`cohomologyZeroIso`).

For the coordinate Hopf algebra `H = O(G)` of an affine group scheme, an element of `Cⁿ(H, M)` is
a regular function of `n` points of `G` with values in `M`, and `d` is the inhomogeneous
differential of group cohomology. This complex is the invariant complex of the cofree resolution
`M → M ⊗ H → M ⊗ H ⊗ H → ⋯`; when `H` is flat over `R` its cohomology is the rational cohomology
`Hⁿ(G, M)`, the right derived functors of `M ↦ Mᴴ` (Jantzen, I.4.14–4.16). That comparison, which
needs the acyclicity of cofree comodules, is not part of this file.

## Main definitions

* `TauCeti.Comodule.Cohomology.cochains`: the modules `M ⊗ H^⊗n`.
* `TauCeti.Comodule.Cohomology.coface`: the cofaces `δᵢ`.
* `TauCeti.Comodule.Cohomology.d`: the differential `∑ᵢ (-1)ⁱ δᵢ`.
* `TauCeti.Comodule.Cohomology.cochainComplex`: the Hochschild cochain complex.
* `TauCeti.Comodule.Cohomology.cochainComplexMap`: the cochain map induced by a comodule morphism.
* `TauCeti.Comodule.Cohomology.cocyclesMk`: a cochain with zero differential, as a cocycle.
* `TauCeti.Comodule.Cohomology.cohomologyZeroIso`: the degree-zero cohomology is `Mᴴ`.

## Main results

* `TauCeti.Comodule.Cohomology.d_succ_tmul`: on `x ⊗ h`, the differential in degree `n + 1` is
  `d x ⊗ h + (-1)ⁿ⁺¹ x ⊗ (Δ h - 1 ⊗ h - h ⊗ 1)`.
* `TauCeti.Comodule.Cohomology.d_comp_d`: `d ∘ d = 0`.
* `TauCeti.Comodule.Cohomology.ker_d_zero`: the kernel of `d : M → M ⊗ H` is `Mᴴ`.
* `TauCeti.Comodule.Cohomology.homologyMap_comp_cohomologyZeroIso_hom`: the identification of
  `H⁰` with `Mᴴ` is natural in `M`.

## Implementation notes

The cofaces and the differential are defined directly, but `d ∘ d = 0` is proved by induction
on the degree through `d_succ_tmul` rather than from the cosimplicial identities: the inductive
step reduces to coassociativity of the reduced comultiplication `h ↦ Δ h - 1 ⊗ h - h ⊗ 1`, and
the base case to coassociativity of the coaction.

The cochains form a family of objects of `ModuleCat R` built by recursion on the degree, so `H`
and `M` live in the same universe.

## References

* J. C. Jantzen, *Representations of Algebraic Groups*, 2nd ed., Part I, §§4.14–4.16.
-/

public section

open CategoryTheory TensorProduct

namespace TauCeti.Comodule.Cohomology

universe u v

variable (R : Type u) [CommRing R] (H : Type v) [Ring H] [Bialgebra R H]
variable (M : Type v) [AddCommGroup M] [Module R M] [Comodule R H M]

/-- The module of Hochschild cochains of degree `n`, `Cⁿ(H, M) = M ⊗ H^⊗n`, bracketed to the
left: `C⁰(H, M) = M` and `Cⁿ⁺¹(H, M) = Cⁿ(H, M) ⊗ H`. It is reducible, so that elements of
`Cⁿ⁺¹(H, M)` are elements of `Cⁿ(H, M) ⊗ H`. -/
noncomputable abbrev cochains : ℕ → ModuleCat.{v} R
  | 0 => ModuleCat.of R M
  | n + 1 => ModuleCat.of R (cochains n ⊗[R] H)

/-! ### The reduced comultiplication of the last factor -/

section LastFactor

variable {X Y : Type*} [AddCommGroup X] [Module R X] [AddCommGroup Y] [Module R Y]

/-- The reduced comultiplication `h ↦ Δ h - 1 ⊗ h - h ⊗ 1`. -/
private noncomputable def reducedComul : H →ₗ[R] H ⊗[R] H :=
  (Coalgebra.comul : H →ₗ[R] H ⊗[R] H) - TensorProduct.mk R H H 1 - (TensorProduct.mk R H H).flip 1

private theorem reducedComul_apply (h : H) :
    reducedComul R H h = Coalgebra.comul h - 1 ⊗ₜ h - h ⊗ₜ 1 :=
  rfl

/-- Coassociativity of the reduced comultiplication. -/
private theorem assoc_rTensor_reducedComul (h : H) :
    TensorProduct.assoc R H H H ((reducedComul R H).rTensor H (reducedComul R H h)) =
      (reducedComul R H).lTensor H (reducedComul R H h) := by
  -- The terms of `Δ h` in which a unit is inserted agree on both sides; this is linear in `Δ h`.
  have hk : ∀ t : H ⊗[R] H,
      TensorProduct.assoc R H H H ((TensorProduct.mk R H H 1).rTensor H t) +
          TensorProduct.assoc R H H H (((TensorProduct.mk R H H).flip 1).rTensor H t) +
          TensorProduct.assoc R H H H (t ⊗ₜ 1) =
        (TensorProduct.mk R H H 1).lTensor H t + ((TensorProduct.mk R H H).flip 1).lTensor H t +
          1 ⊗ₜ t := by
    intro t
    induction t with
    | tmul a b =>
      simp only [LinearMap.rTensor_tmul, TensorProduct.mk_apply, TensorProduct.assoc_tmul,
        LinearMap.flip_apply, LinearMap.lTensor_tmul]
      abel
    | add s t hs ht =>
      simp only [map_add, TensorProduct.add_tmul, TensorProduct.tmul_add] at hs ht ⊢
      linear_combination (norm := module) hs + ht
  have hc := Coalgebra.coassoc_apply (R := R) h
  have hk' := hk (Coalgebra.comul h)
  simp only [reducedComul, LinearMap.sub_apply, LinearMap.rTensor_sub, LinearMap.lTensor_sub,
    map_sub, LinearMap.rTensor_tmul, LinearMap.lTensor_tmul, TensorProduct.mk_apply,
    LinearMap.flip_apply, Bialgebra.comul_one, Algebra.TensorProduct.one_def,
    TensorProduct.assoc_tmul] at hc hk' ⊢
  linear_combination (norm := module) hc - hk'

variable (X) in
/-- The reduced comultiplication of the last tensor factor of `X ⊗ H`. -/
private noncomputable def lastComul : X ⊗[R] H →ₗ[R] (X ⊗[R] H) ⊗[R] H :=
  (TensorProduct.assoc R X H H).symm.toLinearMap ∘ₗ (reducedComul R H).lTensor X

private theorem lastComul_tmul (x : X) (h : H) :
    lastComul R H X (x ⊗ₜ h) =
      (TensorProduct.assoc R X H H).symm (x ⊗ₜ Coalgebra.comul h) - (x ⊗ₜ 1) ⊗ₜ h -
        (x ⊗ₜ h) ⊗ₜ 1 := by
  simp [lastComul, reducedComul_apply, TensorProduct.tmul_sub]

private theorem lastComul_eq :
    lastComul R H X = (TensorProduct.assoc R X H H).symm.toLinearMap ∘ₗ
      (Coalgebra.comul (R := R) (A := H)).lTensor X - ((TensorProduct.mk R X H).flip 1).rTensor H -
        (TensorProduct.mk R (X ⊗[R] H) H).flip 1 :=
  TensorProduct.ext' fun x h ↦ by simp [lastComul_tmul]

/-- The reduced comultiplication of the last factor is natural in the other factors. -/
private theorem lastComul_comp_rTensor (f : X →ₗ[R] Y) :
    lastComul R H Y ∘ₗ f.rTensor H = (f.rTensor H).rTensor H ∘ₗ lastComul R H X := by
  refine TensorProduct.ext' fun x h ↦ ?_
  simp only [lastComul, LinearMap.comp_apply, LinearMap.rTensor_tmul, LinearMap.lTensor_tmul,
    LinearEquiv.coe_coe]
  rw [LinearMap.rTensor_def, LinearMap.rTensor_def, TensorProduct.map_map_assoc_symm]
  simp

/-- Coassociativity of the reduced comultiplication, transported to the last two factors. -/
private theorem lastComul_comp_lastComul :
    lastComul R H (X ⊗[R] H) ∘ₗ lastComul R H X =
      (lastComul R H X).rTensor H ∘ₗ lastComul R H X := by
  set Ψ : X ⊗[R] (H ⊗[R] (H ⊗[R] H)) →ₗ[R] ((X ⊗[R] H) ⊗[R] H) ⊗[R] H :=
    (TensorProduct.assoc R (X ⊗[R] H) H H).symm.toLinearMap ∘ₗ
      (TensorProduct.assoc R X H (H ⊗[R] H)).symm.toLinearMap with hΨ
  clear_value Ψ
  have h₁ : lastComul R H (X ⊗[R] H) ∘ₗ (TensorProduct.assoc R X H H).symm.toLinearMap =
      Ψ ∘ₗ ((reducedComul R H).lTensor H).lTensor X := by
    refine TensorProduct.ext_threefold' fun x a b ↦ ?_
    simp only [lastComul, hΨ, LinearMap.comp_apply, LinearEquiv.coe_coe,
      TensorProduct.assoc_symm_tmul, LinearMap.lTensor_tmul]
  have h₂ : (lastComul R H X).rTensor H ∘ₗ (TensorProduct.assoc R X H H).symm.toLinearMap =
      Ψ ∘ₗ ((TensorProduct.assoc R H H H).toLinearMap ∘ₗ
        (reducedComul R H).rTensor H).lTensor X := by
    refine TensorProduct.ext_threefold' fun x a b ↦ ?_
    simp only [lastComul, hΨ, LinearMap.comp_apply, LinearEquiv.coe_coe,
      TensorProduct.assoc_symm_tmul, LinearMap.lTensor_tmul, LinearMap.rTensor_tmul]
    induction reducedComul R H a with
    | tmul c e => simp
    | add s t hs ht =>
      simp only [TensorProduct.tmul_add, TensorProduct.add_tmul, map_add, hs, ht]
  have h₃ : (reducedComul R H).lTensor H ∘ₗ reducedComul R H =
      (TensorProduct.assoc R H H H).toLinearMap ∘ₗ (reducedComul R H).rTensor H ∘ₗ
        reducedComul R H :=
    (LinearMap.ext (assoc_rTensor_reducedComul R H)).symm
  calc lastComul R H (X ⊗[R] H) ∘ₗ lastComul R H X
      = (lastComul R H (X ⊗[R] H) ∘ₗ (TensorProduct.assoc R X H H).symm.toLinearMap) ∘ₗ
          (reducedComul R H).lTensor X := rfl
    _ = Ψ ∘ₗ ((reducedComul R H).lTensor H ∘ₗ reducedComul R H).lTensor X := by
      rw [h₁, LinearMap.comp_assoc, LinearMap.lTensor_comp]
    _ = Ψ ∘ₗ ((TensorProduct.assoc R H H H).toLinearMap ∘ₗ (reducedComul R H).rTensor H ∘ₗ
          reducedComul R H).lTensor X := by rw [h₃]
    _ = ((lastComul R H X).rTensor H ∘ₗ (TensorProduct.assoc R X H H).symm.toLinearMap) ∘ₗ
          (reducedComul R H).lTensor X := by
      rw [h₂, LinearMap.comp_assoc, ← LinearMap.lTensor_comp, LinearMap.comp_assoc]
    _ = (lastComul R H X).rTensor H ∘ₗ lastComul R H X := rfl

end LastFactor

/-! ### Cofaces and the differential -/

/-- The coface `δᵢ : Cⁿ(H, M) → Cⁿ⁺¹(H, M)`, for `0 ≤ i ≤ n + 1`. The coface `δ₀` applies the
coaction `ρ` to the coefficient factor, `δᵢ` for `1 ≤ i ≤ n` applies the comultiplication to
the `i`-th factor of `H`, and `δₙ₊₁` appends the unit `1` of `H`. -/
noncomputable def coface : (n : ℕ) → Fin (n + 2) → (cochains R H M n →ₗ[R] cochains R H M (n + 1))
  | 0, i => Fin.lastCases ((TensorProduct.mk R M H).flip 1)
      (fun _ ↦ Comodule.coact (R := R) (C := H) (M := M)) i
  | n + 1, i => Fin.lastCases ((TensorProduct.mk R (cochains R H M (n + 1)) H).flip 1)
      (fun j ↦ Fin.lastCases
        ((TensorProduct.assoc R (cochains R H M n) H H).symm.toLinearMap ∘ₗ
          (Coalgebra.comul (R := R) (A := H)).lTensor (cochains R H M n))
        (fun k ↦ (coface n k.castSucc).rTensor H) j) i

/-- The coface `δ₀ : M → M ⊗ H` is the coaction. -/
@[simp]
theorem coface_zero_zero : coface R H M 0 0 = Comodule.coact (R := R) (C := H) (M := M) := by
  rfl

/-- The last coface appends the unit of `H`. -/
@[simp]
theorem coface_last_apply (n : ℕ) (x : cochains R H M n) :
    coface R H M n (Fin.last (n + 1)) x = (x ⊗ₜ[R] (1 : H) : cochains R H M (n + 1)) := by
  cases n <;> rw [coface, Fin.lastCases_last, LinearMap.flip_apply, TensorProduct.mk_apply]

/-- In degree `n + 1`, the coface `δₙ₊₁` comultiplies the last factor of `H`. -/
@[simp]
theorem coface_succ_castSucc_last_apply (n : ℕ) (x : cochains R H M n) (h : H) :
    coface R H M (n + 1) (Fin.last (n + 1)).castSucc (x ⊗ₜ h) =
      ((TensorProduct.assoc R (cochains R H M n) H H).symm (x ⊗ₜ Coalgebra.comul h) :
        cochains R H M (n + 2)) := by
  rw [coface, Fin.lastCases_castSucc, Fin.lastCases_last, LinearMap.comp_apply,
    LinearMap.lTensor_tmul, LinearEquiv.coe_coe]

/-- In degree `n + 1`, the cofaces `δ₀, …, δₙ` act on all but the last factor. -/
@[simp]
theorem coface_succ_castSucc_castSucc (n : ℕ) (i : Fin (n + 1)) :
    coface R H M (n + 1) i.castSucc.castSucc = (coface R H M n i.castSucc).rTensor H := by
  rw [coface, Fin.lastCases_castSucc, Fin.lastCases_castSucc]

/-- The differential `d = ∑ᵢ (-1)ⁱ δᵢ : Cⁿ(H, M) → Cⁿ⁺¹(H, M)` of the Hochschild complex. -/
noncomputable def d (n : ℕ) : cochains R H M n →ₗ[R] cochains R H M (n + 1) :=
  ∑ i : Fin (n + 2), ((-1 : R) ^ (i : ℕ)) • coface R H M n i

/-- The differential is the alternating sum of the cofaces. -/
theorem d_eq_sum (n : ℕ) : d R H M n = ∑ i : Fin (n + 2), ((-1 : R) ^ (i : ℕ)) • coface R H M n i :=
  (rfl)

/-- The differential is the alternating sum of the cofaces, evaluated at a cochain. -/
theorem d_apply (n : ℕ) (x : cochains R H M n) :
    d R H M n x = ∑ i : Fin (n + 2), ((-1 : R) ^ (i : ℕ)) • coface R H M n i x := by
  rw [d_eq_sum, LinearMap.sum_apply]
  simp only [LinearMap.smul_apply]

/-- The differential in degree zero is `m ↦ ρ m - m ⊗ 1`. -/
theorem d_zero :
    d R H M 0 = Comodule.coact (R := R) (C := H) (M := M) - (TensorProduct.mk R M H).flip 1 := by
  refine LinearMap.ext fun m ↦ ?_
  have h₁ : coface R H M 0 1 m = m ⊗ₜ[R] (1 : H) := coface_last_apply R H M 0 m
  simp [d, Fin.sum_univ_two, h₁, sub_eq_add_neg]

/-- The differential in degree zero is `m ↦ ρ m - m ⊗ 1`. -/
@[simp]
theorem d_zero_apply (m : M) :
    d R H M 0 m = Comodule.coact (R := R) (C := H) (M := M) m - m ⊗ₜ[R] (1 : H) := by
  simp [d_zero]

/-- The differential in degree `n + 1` is `d ⊗ id` plus `(-1)ⁿ⁺¹` times the reduced
comultiplication `h ↦ Δ h - 1 ⊗ h - h ⊗ 1` of the last factor. -/
theorem d_succ_tmul (n : ℕ) (x : cochains R H M n) (h : H) :
    d R H M (n + 1) (x ⊗ₜ h) = (d R H M n x ⊗ₜ h : cochains R H M (n + 2)) +
      ((-1 : R) ^ (n + 1)) • ((TensorProduct.assoc R (cochains R H M n) H H).symm
        (x ⊗ₜ Coalgebra.comul h) - (x ⊗ₜ 1) ⊗ₜ h - (x ⊗ₜ h) ⊗ₜ 1 : cochains R H M (n + 2)) := by
  simp only [d, LinearMap.add_apply, LinearMap.sum_apply, LinearMap.smul_apply,
    Fin.sum_univ_castSucc (n := n + 2), Fin.sum_univ_castSucc (n := n + 1),
    coface_succ_castSucc_castSucc, LinearMap.rTensor_tmul, Fin.val_castSucc, Fin.val_last]
  rw [coface_succ_castSucc_last_apply, coface_last_apply R H M (n + 1), coface_last_apply,
    TensorProduct.add_tmul, TensorProduct.sum_tmul, pow_succ (-1 : R) (n + 1)]
  simp only [← TensorProduct.smul_tmul']
  module

private theorem d_succ_eq (n : ℕ) :
    d R H M (n + 1) = (d R H M n).rTensor H + ((-1 : R) ^ (n + 1)) •
      lastComul R H (cochains R H M n) :=
  TensorProduct.ext' fun x h ↦ by
    rw [d_succ_tmul]
    simp [lastComul_tmul]

/-- If `f = g ⊗ id + s • E` and `f' = f ⊗ id + (-s) • E`, where `E` is the reduced comultiplication
of the last factor, then `f' ∘ f = (f ∘ g) ⊗ id`: the cross terms cancel by naturality of `E`, and
the terms `E ∘ E` by its coassociativity. -/
private theorem rTensor_add_neg_smul_lastComul_comp {X : Type*} [AddCommGroup X] [Module R X]
    (g : X →ₗ[R] X ⊗[R] H) (f : X ⊗[R] H →ₗ[R] (X ⊗[R] H) ⊗[R] H) (s : R)
    (hf : f = g.rTensor H + s • lastComul R H X) :
    (f.rTensor H + (-s) • lastComul R H (X ⊗[R] H)) ∘ₗ f = (f ∘ₗ g).rTensor H := by
  have hnat := lastComul_comp_rTensor R H g
  have hcoassoc := lastComul_comp_lastComul R H (X := X)
  conv_lhs => rw [hf]
  simp only [LinearMap.rTensor_add, LinearMap.rTensor_smul, LinearMap.add_comp,
    LinearMap.comp_add, LinearMap.smul_comp, LinearMap.comp_smul, ← LinearMap.rTensor_comp,
    hnat, hcoassoc]
  rw [hf]
  simp only [LinearMap.add_comp, LinearMap.smul_comp, LinearMap.rTensor_add,
    LinearMap.rTensor_smul, LinearMap.rTensor_comp]
  module

/-- The differential squares to zero. -/
theorem d_comp_d (n : ℕ) : d R H M (n + 1) ∘ₗ d R H M n = 0 := by
  induction n with
  | zero =>
    rw [d_succ_eq, d_zero, lastComul_eq]
    refine LinearMap.ext fun m ↦ ?_
    -- The key step is coassociativity of the coaction, `coassoc_symm_apply`, together with
    -- `Δ 1 = 1 ⊗ 1`. After these rewrites the remaining terms cancel in pairs.
    simp [coassoc_symm_apply, Bialgebra.comul_one, Algebra.TensorProduct.one_def]
    abel
  | succ n ih =>
    rw [d_succ_eq R H M (n + 1), pow_succ, mul_neg_one,
      rTensor_add_neg_smul_lastComul_comp R H _ _ _ (d_succ_eq R H M n), ih, LinearMap.rTensor_zero]

/-- The differential squares to zero, evaluated at a cochain. -/
@[simp]
theorem d_d (n : ℕ) (x : cochains R H M n) : d R H M (n + 1) (d R H M n x) = 0 :=
  LinearMap.congr_fun (d_comp_d R H M n) x

/-! ### The cochain complex and its cohomology -/

/-- The Hochschild cochain complex of the comodule `M`, with terms `M ⊗ H^⊗n` and the differential
`∑ᵢ (-1)ⁱ δᵢ`. -/
@[expose] noncomputable def cochainComplex : CochainComplex (ModuleCat.{v} R) ℕ :=
  CochainComplex.of (cochains R H M) (fun n ↦ ModuleCat.ofHom (d R H M n)) fun n ↦ by
    rw [← ModuleCat.ofHom_comp, d_comp_d, ModuleCat.ofHom_zero]

/-- The degree `n` term of the Hochschild complex is `M ⊗ H^⊗n`. -/
@[simp]
theorem cochainComplex_X (n : ℕ) : (cochainComplex R H M).X n = cochains R H M n :=
  (rfl)

/-- The differential of the Hochschild complex from degree `n` to degree `n + 1`. -/
@[simp]
theorem cochainComplex_d_succ (n : ℕ) :
    (cochainComplex R H M).d n (n + 1) = ModuleCat.ofHom (d R H M n) := by
  simp [cochainComplex]

/-- The `n`-th cohomology `Hⁿ(H, M)` of the Hochschild complex of `M`. -/
noncomputable abbrev cohomology (n : ℕ) : ModuleCat.{v} R :=
  (cochainComplex R H M).homology n

/-- The kernel of the differential `d : M → M ⊗ H` is the submodule of invariants
`Mᴴ = {m | ρ m = m ⊗ 1}`. -/
theorem ker_d_zero :
    LinearMap.ker (d R H M 0) = (fixedSubcomodule R H M).toSubmodule := by
  ext m
  rw [LinearMap.mem_ker, d_zero_apply, sub_eq_zero, Subcomodule.mem_toSubmodule,
    mem_fixedSubcomodule]

/-- The kernel of the differential `M → M ⊗ H` of the complex is the module of invariants. The
kernels agree since `(cochainComplex R H M).d 0 1` is `ModuleCat.ofHom (d R H M 0)`
(`cochainComplex_d_succ`). -/
private noncomputable def kernelEquivFixed :
    LinearMap.ker ((cochainComplex R H M).d 0 (0 + 1)).hom ≃ₗ[R] fixedSubcomodule R H M :=
  LinearEquiv.ofEq _ _ <| by
    -- After `cochainComplex_d_succ`, the map is `(ModuleCat.ofHom (d R H M 0)).hom`, which is
    -- `d R H M 0` by `ModuleCat.hom_ofHom`; the lemma cannot be rewritten here because the source
    -- and target are spelled `(cochainComplex R H M).X n`, so `exact` applies it by unfolding.
    rw [cochainComplex_d_succ]
    exact ker_d_zero R H M

/-- The degree-zero cohomology of the Hochschild complex is the module of invariants
`Mᴴ = {m | ρ m = m ⊗ 1}`. -/
noncomputable def cohomologyZeroIso :
    cohomology R H M 0 ≅ ModuleCat.of R (fixedSubcomodule R H M) :=
  (cochainComplex R H M).isoHomologyπ₀.symm ≪≫
    Limits.IsLimit.conePointUniqueUpToIso
      ((cochainComplex R H M).cyclesIsKernel 0 (0 + 1) (by simp))
      (ModuleCat.kernelIsLimit _) ≪≫
    (kernelEquivFixed R H M).toModuleIso

/-- A degree-zero cocycle, viewed in cohomology, is sent by `cohomologyZeroIso` to itself as an
invariant vector. -/
@[simp]
theorem coe_cohomologyZeroIso_hom_homologyπ (x : (cochainComplex R H M).cycles 0) :
    ((cohomologyZeroIso R H M).hom.hom (((cochainComplex R H M).homologyπ 0).hom x) : M) =
      ((cochainComplex R H M).iCycles 0).hom x := by
  have h := Limits.IsLimit.conePointUniqueUpToIso_hom_comp
    ((cochainComplex R H M).cyclesIsKernel 0 (0 + 1) (by simp)) (ModuleCat.kernelIsLimit _)
    Limits.WalkingParallelPair.zero
  have hx := congr(ModuleCat.Hom.hom $h x)
  have hπ : (cochainComplex R H M).isoHomologyπ₀.inv.hom
      (((cochainComplex R H M).homologyπ 0).hom x) = x :=
    (cochainComplex R H M).isoHomologyπ₀.hom_inv_id_apply x
  simp only [ModuleCat.kernelCone, Limits.Fork.app_zero_eq_ι, Limits.Fork.ι_ofι,
    ModuleCat.hom_comp, ModuleCat.hom_ofHom, LinearMap.comp_apply] at hx
  simp only [cohomologyZeroIso, Iso.trans_hom, Iso.symm_hom, ModuleCat.hom_comp,
    LinearMap.comp_apply, hπ]
  -- The remaining step is `(kernelEquivFixed R H M).toModuleIso`, which is `LinearEquiv.ofEq`
  -- and so the identity on elements (`LinearEquiv.coe_ofEq_apply`). That lemma cannot be
  -- rewritten here: the kernel lives in `(cochainComplex R H M).X 0`, which is `M` only by
  -- unfolding (`cochainComplex_X`), so `exact` closes the goal with `hx` up to that
  -- identification.
  exact hx

section Cocycles

variable {R H M}

/-- An invariant vector has zero Hochschild differential. -/
theorem d_zero_eq_zero_of_mem_fixedSubcomodule {m : M} (hm : m ∈ fixedSubcomodule R H M) :
    d R H M 0 m = 0 := by
  rw [← LinearMap.mem_ker, ker_d_zero]
  exact hm

/-- An `n`-cochain whose differential vanishes, as an `n`-cocycle of the Hochschild complex. -/
noncomputable def cocyclesMk {n : ℕ} (x : cochains R H M n) (hx : d R H M n x = 0) :
    (cochainComplex R H M).cycles n :=
  (cochainComplex R H M).cyclesMk x (n + 1) (by simp) (by
    rw [cochainComplex_d_succ]
    exact hx)

/-- `cocyclesMk` is Mathlib's cycle constructor `HomologicalComplex.cyclesMk` for the Hochschild
complex. -/
theorem cocyclesMk_eq_cyclesMk {n : ℕ} (x : cochains R H M n) (hx : d R H M n x = 0) :
    cocyclesMk x hx = (cochainComplex R H M).cyclesMk x (n + 1) (by simp) (by
      rw [cochainComplex_d_succ]
      exact hx) :=
  (rfl)

/-- The cocycle `cocyclesMk x hx` is the cochain `x`. -/
@[simp]
theorem iCycles_cocyclesMk {n : ℕ} (x : cochains R H M n) (hx : d R H M n x = 0) :
    ((cochainComplex R H M).iCycles n).hom (cocyclesMk x hx) = x :=
  (cochainComplex R H M).i_cyclesMk x (n + 1) (by simp) _

/-- In degree zero, the class of an invariant vector, as a cocycle, is its preimage under
`cohomologyZeroIso`. -/
theorem homologyπ_cocyclesMk_zero (m : fixedSubcomodule R H M) :
    ((cochainComplex R H M).homologyπ 0).hom
        (cocyclesMk (n := 0) (m : M) (d_zero_eq_zero_of_mem_fixedSubcomodule m.property)) =
      (cohomologyZeroIso R H M).inv.hom m := by
  have h : (cohomologyZeroIso R H M).hom.hom (((cochainComplex R H M).homologyπ 0).hom
      (cocyclesMk (n := 0) (m : M) (d_zero_eq_zero_of_mem_fixedSubcomodule m.property))) = m :=
    Subtype.ext ((coe_cohomologyZeroIso_hom_homologyπ R H M _).trans (iCycles_cocyclesMk _ _))
  conv_rhs => rw [← h]
  exact ((cohomologyZeroIso R H M).hom_inv_id_apply _).symm

end Cocycles

/-! ### Functoriality in the coefficients -/

section Functoriality

variable {R H M} {N P : Type v} [AddCommGroup N] [Module R N] [Comodule R H N]
  [AddCommGroup P] [Module R P] [Comodule R H P]

/-- The map `f ⊗ id : M ⊗ H^⊗n → N ⊗ H^⊗n` induced on Hochschild cochains by a comodule morphism
`f : M → N`, which acts on the first tensor factor. -/
noncomputable def cochainsMap (f : Hom R H M N) :
    (n : ℕ) → (cochains R H M n →ₗ[R] cochains R H N n)
  | 0 => f.toLinearMap
  | n + 1 => (cochainsMap f n).rTensor H

/-- In degree zero, the induced map on cochains is the comodule morphism itself. -/
theorem cochainsMap_zero (f : Hom R H M N) : cochainsMap f 0 = f.toLinearMap :=
  (rfl)

/-- In degree `n + 1`, the induced map on cochains is the map in degree `n` tensored with the
identity of `H`. -/
theorem cochainsMap_succ (f : Hom R H M N) (n : ℕ) :
    cochainsMap f (n + 1) = (cochainsMap f n).rTensor H :=
  (rfl)

/-- In degree zero, the induced map on cochains is the comodule morphism itself. -/
@[simp]
theorem cochainsMap_zero_apply (f : Hom R H M N) (m : M) : cochainsMap f 0 m = f m :=
  (rfl)

/-- In degree `n + 1`, the induced map on cochains is the map in degree `n` tensored with the
identity of `H`. -/
@[simp]
theorem cochainsMap_succ_tmul (f : Hom R H M N) (n : ℕ) (x : cochains R H M n) (h : H) :
    cochainsMap f (n + 1) (x ⊗ₜ h) = (cochainsMap f n x ⊗ₜ h : cochains R H N (n + 1)) :=
  (rfl)

/-- The identity comodule morphism induces the identity on cochains. -/
-- Simplify before `ComoduleCat.ofHom_id` and `ComoduleCat.ofHom_comp` rewrite the bare
-- comodule morphism in categorical form.
@[simp↓]
theorem cochainsMap_id (n : ℕ) : cochainsMap (Hom.id R H M) n = LinearMap.id := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [cochainsMap_succ, ih, LinearMap.rTensor_id]

/-- The map induced on cochains by a composite is the composite of the induced maps. -/
-- Simplify before `ComoduleCat.ofHom_id` and `ComoduleCat.ofHom_comp` rewrite the bare
-- comodule morphism in categorical form.
@[simp↓]
theorem cochainsMap_comp (g : Hom R H N P) (f : Hom R H M N) (n : ℕ) :
    cochainsMap (g.comp f) n = cochainsMap g n ∘ₗ cochainsMap f n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [cochainsMap_succ, cochainsMap_succ, cochainsMap_succ, ih, LinearMap.rTensor_comp]

/-- The map induced on cochains by a sum of comodule morphisms is the sum of the induced maps. -/
@[simp]
theorem cochainsMap_add (f f' : Hom R H M N) (n : ℕ) :
    cochainsMap (f + f') n = cochainsMap f n + cochainsMap f' n := by
  induction n with
  | zero =>
    rw [cochainsMap_zero, cochainsMap_zero, cochainsMap_zero]
    exact Hom.add_toLinearMap f f'
  | succ n ih =>
    rw [cochainsMap_succ, cochainsMap_succ, cochainsMap_succ, ih, LinearMap.rTensor_add]

/-- The map induced by a comodule morphism commutes with the Hochschild differential. -/
theorem d_comp_cochainsMap (f : Hom R H M N) (n : ℕ) :
    d R H N n ∘ₗ cochainsMap f n = cochainsMap f (n + 1) ∘ₗ d R H M n := by
  induction n with
  | zero =>
    rw [d_zero, d_zero, cochainsMap_succ, cochainsMap_zero]
    refine LinearMap.ext fun (m : M) ↦ ?_
    simp [LinearMap.rTensor_def]
  | succ n ih =>
    have h₁ : (d R H N n).rTensor H ∘ₗ cochainsMap f (n + 1) =
        cochainsMap f (n + 2) ∘ₗ (d R H M n).rTensor H :=
      by simpa only [cochainsMap_succ, LinearMap.rTensor_comp] using congrArg (·.rTensor H) ih
    have h₂ : lastComul R H (cochains R H N n) ∘ₗ cochainsMap f (n + 1) =
        cochainsMap f (n + 2) ∘ₗ lastComul R H (cochains R H M n) :=
      lastComul_comp_rTensor R H (cochainsMap f n)
    rw [d_succ_eq, d_succ_eq, LinearMap.add_comp, LinearMap.comp_add, LinearMap.smul_comp,
      LinearMap.comp_smul, h₁, h₂]

/-- The cochain map between Hochschild complexes induced by a comodule morphism. -/
noncomputable def cochainComplexMap (f : Hom R H M N) :
    cochainComplex R H M ⟶ cochainComplex R H N :=
  CochainComplex.ofHom (fun n ↦ ModuleCat.ofHom (cochainsMap f n)) fun n ↦ by
    rw [cochainComplex_d_succ, cochainComplex_d_succ]
    exact ModuleCat.hom_ext (d_comp_cochainsMap f n)

/-- The components of the cochain map induced by a comodule morphism. -/
@[simp]
theorem cochainComplexMap_f (f : Hom R H M N) (n : ℕ) :
    (cochainComplexMap f).f n = ModuleCat.ofHom (cochainsMap f n) :=
  (rfl)

/-- The identity comodule morphism induces the identity cochain map. -/
-- Simplify before `ComoduleCat.ofHom_id` and `ComoduleCat.ofHom_comp` rewrite the bare
-- comodule morphism in categorical form.
@[simp↓]
theorem cochainComplexMap_id : cochainComplexMap (Hom.id R H M) = 𝟙 _ := by
  ext n : 1
  rw [cochainComplexMap_f, cochainsMap_id, HomologicalComplex.id_f]
  -- `𝟙 ((cochainComplex R H M).X n)` is `𝟙 (ModuleCat.of R (cochains R H M n))` only by unfolding
  -- `CochainComplex.of` (`cochainComplex_X`), so `exact` closes the goal up to that identification.
  exact ModuleCat.ofHom_id

/-- The cochain map induced by a composite is the composite of the induced cochain maps. -/
-- Simplify before `ComoduleCat.ofHom_id` and `ComoduleCat.ofHom_comp` rewrite the bare
-- comodule morphism in categorical form.
@[simp↓]
theorem cochainComplexMap_comp (g : Hom R H N P) (f : Hom R H M N) :
    cochainComplexMap (g.comp f) = cochainComplexMap f ≫ cochainComplexMap g := by
  ext n : 1
  rw [cochainComplexMap_f, cochainsMap_comp, HomologicalComplex.comp_f, cochainComplexMap_f,
    cochainComplexMap_f]
  -- As in `cochainComplexMap_id`, the objects of the composite are the modules
  -- `ModuleCat.of R (cochains _ n)` only by unfolding `CochainComplex.of` (`cochainComplex_X`).
  exact ModuleCat.ofHom_comp _ _

/-- The cochain map induced by a sum of comodule morphisms is the sum of the induced cochain
maps. -/
@[simp]
theorem cochainComplexMap_add (f f' : Hom R H M N) :
    cochainComplexMap (f + f') = cochainComplexMap f + cochainComplexMap f' := by
  ext n : 1
  rw [cochainComplexMap_f, cochainsMap_add, HomologicalComplex.add_f_apply, cochainComplexMap_f,
    cochainComplexMap_f]
  -- As in `cochainComplexMap_id`, the objects are the modules `ModuleCat.of R (cochains _ n)` only
  -- by unfolding `CochainComplex.of` (`cochainComplex_X`).
  exact ModuleCat.ofHom_add _ _

/-- The identification of degree-zero cohomology with the invariants is natural in the
coefficients: a comodule morphism acts on invariant vectors by restriction. -/
theorem homologyMap_comp_cohomologyZeroIso_hom (f : Hom R H M N) :
    HomologicalComplex.homologyMap (cochainComplexMap f) 0 ≫ (cohomologyZeroIso R H N).hom =
      (cohomologyZeroIso R H M).hom ≫ ModuleCat.ofHom f.fixedMap := by
  rw [← cancel_epi ((cochainComplex R H M).homologyπ 0),
    HomologicalComplex.homologyπ_naturality_assoc]
  ext x
  have hx := congr(ModuleCat.Hom.hom $(HomologicalComplex.cyclesMap_i (cochainComplexMap f) 0) x)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at hx ⊢
  rw [coe_cohomologyZeroIso_hom_homologyπ, ModuleCat.hom_ofHom, Hom.fixedMap_apply,
    coe_cohomologyZeroIso_hom_homologyπ]
  -- `hx`, with `(cochainComplexMap f).f 0` unfolded to `f` (`cochainComplexMap_f`,
  -- `cochainsMap_zero_apply`) up to the identification of `(cochainComplex R H M).X 0` with `M`.
  exact hx

end Functoriality

end TauCeti.Comodule.Cohomology

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Representation.PointsAction.Basic
public import TauCeti.Algebra.AlgebraicGroup.Tangent.OneParameter
public import TauCeti.LinearAlgebra.End.Exp

/-!
# Action of exponential points on comodule representations

Let `H` be a commutative Hopf `ℚ`-algebra over `R` and `d` a tangent vector at the identity whose
left-invariant derivation `D = TauCeti.Bialgebra.leftInvariantDerivation d` is locally nilpotent.
Since the differentiated action `ρ'(d) = TauCeti.Comodule.differential d` on any right `H`-comodule
`M` intertwines the coaction with `id ⊗ D` (`TauCeti.Comodule.coact_differential`,
`TauCeti.Comodule.pow_differential_apply`), `ρ'(d)` is locally nilpotent on `M`
(`TauCeti.Comodule.exists_pow_differential_eq_zero`).

This file identifies the action of the exponential rational point
`exp d = TauCeti.Bialgebra.expPoint d hd` and the exponential one-parameter subgroup
`TauCeti.Bialgebra.expPointAt d hd t` on any `H`-comodule `M` carrying a `ℚ`-module structure:

* `TauCeti.Comodule.basePointsRepresentation_expPoint`: `exp d` acts as the linear exponential
  `Module.End.locallyNilpotentExp (ρ'(d))`.
* `TauCeti.Comodule.basePointsRepresentation_expPoint_of_isNilpotent`: when `ρ'(d)` is nilpotent,
  `exp d` acts as `IsNilpotent.exp (ρ'(d))`.
* `TauCeti.Comodule.basePointsRepresentation_expPointAt` and
  `TauCeti.Comodule.basePointsRepresentation_expPointAt_of_isNilpotent`: at parameter `t : R`, the
  one-parameter subgroup `expPointAt d hd t` acts as the exponential of `t • ρ'(d)`.

## References

* J. S. Milne, *Algebraic Groups* (2017), Chapters 10 and 14.
* W. C. Waterhouse, *Introduction to Affine Group Schemes*, Chapters 11 and 12.
-/

public section

open TensorProduct LinearMap

namespace TauCeti.Comodule

section HopfAlgebra

variable {R H M : Type*} [CommRing R] [CommRing H] [HopfAlgebra R H]
  [AddCommGroup M] [Module R M] [Comodule R H M] [Algebra ℚ H] [Module ℚ M]

attribute [local instance 100] LieRing.ofAssociativeRing

omit [Comodule R H M] in
private theorem exists_pow_lTensor_and_tensorComponent_expPoint_eq_sum
    (d : Derivation R H (Bialgebra.CounitAlgebra R H R))
    (hd : ∀ h : H, ∃ n, (Bialgebra.leftInvariantDerivation d)^[n] h = 0)
    (t : M ⊗[R] H) :
    ∃ N : ℕ, ((Bialgebra.leftInvariantDerivation d).toLinearMap ^ N).lTensor M t = 0 ∧
      tensorComponent (Bialgebra.expPoint d hd).toLinearMap t =
        ∑ k ∈ Finset.range N, (k.factorial : ℚ)⁻¹ •
          tensorComponent
            (Coalgebra.counit (R := R) ∘ₗ (Bialgebra.leftInvariantDerivation d).toLinearMap ^ k)
            t := by
  let : Algebra ℚ R :=
    ((_root_.Bialgebra.counitAlgHom R H).toRingHom.comp (algebraMap ℚ H)).toAlgebra
  set D := Bialgebra.leftInvariantDerivation d
  have hvanish : ∀ {u : M ⊗[R] H} {n k : ℕ}, n ≤ k → (D.toLinearMap ^ n).lTensor M u = 0 →
      tensorComponent (Coalgebra.counit (R := R) ∘ₗ D.toLinearMap ^ k) u = 0 := by
    intro u n k hnk hu
    have huk : (D.toLinearMap ^ k).lTensor M u = 0 := by
      rw [← LinearMap.lTensor_pow] at hu ⊢
      exact Module.End.pow_map_zero_of_le hnk hu
    have hcomp := (tensorComponent_map (Coalgebra.counit (R := R)) (LinearMap.id : M →ₗ[R] M)
      (D.toLinearMap ^ k) u).symm
    simpa only [LinearMap.id_apply, ← LinearMap.lTensor_def, huk, map_zero] using hcomp
  induction t using TensorProduct.inductionOn with
  | tmul m h =>
    obtain ⟨N, hN⟩ := hd h
    refine ⟨N, ?_, ?_⟩
    · rw [LinearMap.lTensor_tmul, FunLike.coe_pow_eq_iterate, Derivation.coeFn_coe, hN,
        TensorProduct.tmul_zero]
    · rw [tensorComponent_tmul, AlgHom.toLinearMap_apply, Bialgebra.expPoint_apply,
        D.taylorExp_apply_eq_sum hd hN, map_sum, Finset.sum_smul]
      refine Finset.sum_congr rfl fun k _ ↦ ?_
      have hrat : ∀ (q : ℚ) (r : R), (q • r) • m = q • (r • m) := fun q r ↦
        map_rat_smul (AddMonoidHom.mk' (fun s : R ↦ s • m) (fun a b ↦ add_smul a b m)) q r
      rw [map_rat_smul, hrat, tensorComponent_tmul, LinearMap.comp_apply,
        FunLike.coe_pow_eq_iterate, Derivation.coeFn_coe]
  | add x y hx hy =>
    obtain ⟨N₁, hN₁, he₁⟩ := hx
    obtain ⟨N₂, hN₂, he₂⟩ := hy
    refine ⟨max N₁ N₂, ?_, ?_⟩
    · rw [← LinearMap.lTensor_pow] at hN₁ hN₂ ⊢
      rw [map_add, Module.End.pow_map_zero_of_le (le_max_left N₁ N₂) hN₁,
        Module.End.pow_map_zero_of_le (le_max_right N₁ N₂) hN₂, add_zero]
    · have he₁' : tensorComponent (Bialgebra.expPoint d hd).toLinearMap x =
          ∑ k ∈ Finset.range (max N₁ N₂), (k.factorial : ℚ)⁻¹ •
            tensorComponent (Coalgebra.counit (R := R) ∘ₗ D.toLinearMap ^ k) x := by
        rw [he₁]
        refine Finset.sum_subset (Finset.range_mono (le_max_left N₁ N₂)) fun k _ hk₁ ↦ ?_
        rw [hvanish (Nat.le_of_not_lt (Finset.mem_range.not.mp hk₁)) hN₁, smul_zero]
      have he₂' : tensorComponent (Bialgebra.expPoint d hd).toLinearMap y =
          ∑ k ∈ Finset.range (max N₁ N₂), (k.factorial : ℚ)⁻¹ •
            tensorComponent (Coalgebra.counit (R := R) ∘ₗ D.toLinearMap ^ k) y := by
        rw [he₂]
        refine Finset.sum_subset (Finset.range_mono (le_max_right N₁ N₂)) fun k _ hk₂ ↦ ?_
        rw [hvanish (Nat.le_of_not_lt (Finset.mem_range.not.mp hk₂)) hN₂, smul_zero]
      rw [map_add, he₁', he₂', ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun k _ ↦ by rw [map_add, smul_add]

/-- **The exponential point acts on any comodule as the exponential of its differentiated
action.** -/
theorem basePointsRepresentation_expPoint
    (d : Derivation R H (Bialgebra.CounitAlgebra R H R))
    (hd : ∀ h : H, ∃ n, (Bialgebra.leftInvariantDerivation d)^[n] h = 0) (m : M) :
    basePointsRepresentation (H := H) M (WithConv.toConv (Bialgebra.expPoint d hd)) m =
      Module.End.locallyNilpotentExp (differential (R := R) (H := H) (M := M) d)
        (exists_pow_differential_eq_zero hd) m := by
  obtain ⟨N, hN, hexp⟩ := exists_pow_lTensor_and_tensorComponent_expPoint_eq_sum d hd
    (coact (R := R) (C := H) m)
  have hpowN : (differential (R := R) (H := H) (M := M) d ^ N) m = 0 :=
    coact_eq_zero.mp ((coact_pow_differential d N m).trans hN)
  rw [basePointsRepresentation_apply_eq_tensorComponent, WithConv.ofConv_toConv, hexp,
    Module.End.locallyNilpotentExp_apply_eq_sum _ _ hpowN]
  exact Finset.sum_congr rfl fun k _ ↦ by rw [pow_differential_apply]

/-- **When the differentiated action is nilpotent, `expPoint` acts as `IsNilpotent.exp`.** -/
theorem basePointsRepresentation_expPoint_of_isNilpotent
    (d : Derivation R H (Bialgebra.CounitAlgebra R H R))
    (hd : ∀ h : H, ∃ n, (Bialgebra.leftInvariantDerivation d)^[n] h = 0)
    (hnil : IsNilpotent (differential (R := R) (H := H) (M := M) d)) :
    basePointsRepresentation (H := H) M (WithConv.toConv (Bialgebra.expPoint d hd)) =
      IsNilpotent.exp (differential (R := R) (H := H) (M := M) d) := by
  ext m
  rw [basePointsRepresentation_expPoint]
  exact LinearMap.congr_fun (Module.End.locallyNilpotentExp_eq_exp _ hnil) m

/-- **The exponential one-parameter subgroup acts as the exponential of `t • differential d`.** -/
theorem basePointsRepresentation_expPointAt
    (d : Derivation R H (Bialgebra.CounitAlgebra R H R))
    (hd : ∀ h : H, ∃ n, (Bialgebra.leftInvariantDerivation d)^[n] h = 0) (t : R) (m : M) :
    basePointsRepresentation (H := H) M (Bialgebra.expPointAt d hd t) m =
      Module.End.locallyNilpotentExp (t • differential (R := R) (H := H) (M := M) d)
        (Module.End.exists_pow_smul_apply_eq_zero (exists_pow_differential_eq_zero hd) t) m := by
  rw [Bialgebra.expPointAt_eq_toConv_expPoint, basePointsRepresentation_expPoint]
  have hd_smul : differential (R := R) (H := H) (M := M) (t • d) =
      t • differential (R := R) (H := H) (M := M) d :=
    (differential (R := R) (H := H) (M := M)).toLinearMap.map_smul t d
  congr!

/-- **When the differentiated action is nilpotent, `expPointAt d hd t` acts as
`IsNilpotent.exp (t • differential d)`.** -/
theorem basePointsRepresentation_expPointAt_of_isNilpotent
    (d : Derivation R H (Bialgebra.CounitAlgebra R H R))
    (hd : ∀ h : H, ∃ n, (Bialgebra.leftInvariantDerivation d)^[n] h = 0)
    (hnil : IsNilpotent (differential (R := R) (H := H) (M := M) d)) (t : R) :
    basePointsRepresentation (H := H) M (Bialgebra.expPointAt d hd t) =
      IsNilpotent.exp (t • differential (R := R) (H := H) (M := M) d) := by
  ext m
  rw [basePointsRepresentation_expPointAt]
  exact LinearMap.congr_fun (Module.End.locallyNilpotentExp_eq_exp _ (hnil.smul t)) m

end HopfAlgebra

end TauCeti.Comodule

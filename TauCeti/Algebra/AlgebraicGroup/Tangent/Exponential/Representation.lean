/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Representation.PointsAction.Basic
public import TauCeti.Algebra.AlgebraicGroup.Tangent.OneParameter
public import TauCeti.Algebra.Coalgebra.Subcomodule.Finite
public import TauCeti.Algebra.Coalgebra.Subcomodule.Induced
public import TauCeti.LinearAlgebra.End.Exp

/-!
# Action of exponential points on comodule representations

Let `H` be a commutative bialgebra over `R` and `d` a tangent vector at the identity with
left-invariant derivation `D = TauCeti.Bialgebra.leftInvariantDerivation d`. On any right
`H`-comodule `M`, the differentiated action `ρ'(d) = TauCeti.Comodule.differential d` intertwines
the coaction with `1 ⊗ D`:

```text
coact (ρ'(d) m) = (id ⊗ D) (coact m),      ρ'(d)ⁿ m = ∑ m₍₀₎ ε(Dⁿ m₍₁₎).
```

From this identity we deduce two complementary bridges between the invariant vector field on `H`
and the differentiated representations of `H`:

1. **Local nilpotence.** If `D` is locally nilpotent on `H`, then `ρ'(d)` is locally nilpotent on
   every right `H`-comodule (`TauCeti.Comodule.exists_pow_differential_eq_zero`). Conversely, when
   `H` is projective as an `R`-module, every element of `H` lies in a finite subcomodule of the
   regular comodule (`TauCeti.Subcomodule.exists_finite_subcomodule_mem`), so local nilpotence of
   `ρ'(d)` on all finite subcomodules of `H` implies local nilpotence of `D` on `H`
   (`TauCeti.Bialgebra.exists_iterate_leftInvariantDerivation_eq_zero_of_forall_subcomodule`).
2. **Exponential action.** Over a commutative Hopf `ℚ`-algebra `H`, the rational point
   `exp d = TauCeti.Bialgebra.expPoint d hd` acts on any `H`-comodule `M` (carrying a `ℚ`-module
   structure) as the linear exponential `Module.End.locallyNilpotentExp (ρ'(d))`
   (`TauCeti.Comodule.basePointsRepresentation_expPoint`), and when `ρ'(d)` is nilpotent it acts as
   `IsNilpotent.exp (ρ'(d))` (`TauCeti.Comodule.basePointsRepresentation_expPoint_of_isNilpotent`).
   More generally, the one-parameter subgroup `expPointAt d hd t` at `t : R` acts as the exponential
   of `t • ρ'(d)`.

## Main results

* `TauCeti.Comodule.coact_differential`, `TauCeti.Comodule.coact_pow_differential`, and
  `TauCeti.Comodule.pow_differential_apply`: coaction equivariance and contraction formula for
  powers of `Comodule.differential d`.
* `TauCeti.Comodule.exists_pow_differential_eq_zero`: local nilpotence of
  `leftInvariantDerivation d` implies local nilpotence of `Comodule.differential d` on every
  comodule.
* `TauCeti.Bialgebra.exists_iterate_leftInvariantDerivation_eq_zero_of_forall_subcomodule` and
  `TauCeti.Bialgebra.exists_iterate_leftInvariantDerivation_eq_zero_of_forall_isNilpotent`:
  conversely, when `H` is projective over `R`, nilpotence on finite subcomodules of `H` implies
  local nilpotence of `leftInvariantDerivation d`.
* `TauCeti.Comodule.basePointsRepresentation_expPoint`,
  `TauCeti.Comodule.basePointsRepresentation_expPoint_of_isNilpotent`, and
  `TauCeti.Comodule.basePointsRepresentation_expPointAt_of_isNilpotent`: the exponential point and
  one-parameter subgroup act on representations as the operator exponential of the differentiated
  action.

## References

* J. S. Milne, *Algebraic Groups* (2017), Chapters 10 and 14.
* W. C. Waterhouse, *Introduction to Affine Group Schemes*, Chapters 11 and 12.
-/

public section

open TensorProduct LinearMap

namespace TauCeti.Comodule

section Bialgebra

variable {R H M : Type*} [CommRing R] [CommRing H] [_root_.Bialgebra R H]
  [AddCommGroup M] [Module R M] [Comodule R H M]

/-- **The coaction intertwines the differentiated action with the left-invariant derivation**:
`coact (differential d m) = (id ⊗ D) (coact m)`. -/
theorem coact_differential (d : Derivation R H (Bialgebra.CounitAlgebra R H R)) (m : M) :
    coact (R := R) (C := H) (differential (R := R) (H := H) d m) =
      (Bialgebra.leftInvariantDerivation d).toLinearMap.lTensor M (coact (R := R) (C := H) m) := by
  have hD : (Bialgebra.leftInvariantDerivation d).toLinearMap =
      tensorComponent ((Bialgebra.CounitAlgebra.algEquivSelf R H R).toLinearMap ∘ₗ d.toLinearMap) ∘ₗ
        Coalgebra.comul (R := R) :=
    LinearMap.ext (Bialgebra.leftInvariantDerivation_apply d)
  rw [differential_apply, ← coactComponent_apply, coact_coactComponent, hD]

/-- **Powers of the differentiated action intertwine with powers of the left-invariant derivation**:
`coact ((differential d ^ n) m) = (id ⊗ Dⁿ) (coact m)`. -/
theorem coact_pow_differential (d : Derivation R H (Bialgebra.CounitAlgebra R H R)) (n : ℕ)
    (m : M) :
    coact (R := R) (C := H) ((differential (R := R) (H := H) d ^ n) m) =
      ((Bialgebra.leftInvariantDerivation d).toLinearMap ^ n).lTensor M
        (coact (R := R) (C := H) m) := by
  induction n with
  | zero => simp [Module.End.one_eq_id]
  | succ n ih =>
    rw [pow_succ', mul_apply_eq_comp, coact_differential, ih, pow_succ', LinearMap.lTensor_mul,
      mul_apply_eq_comp]

/-- **Iterated differentiated action by contraction**:
`(differential d ^ n) m = ∑ m₍₀₎ ε(Dⁿ m₍₁₎)`. -/
theorem pow_differential_apply (d : Derivation R H (Bialgebra.CounitAlgebra R H R)) (n : ℕ)
    (m : M) :
    (differential (R := R) (H := H) (M := M) d ^ n) m =
      tensorComponent
        (Coalgebra.counit (R := R) ∘ₗ (Bialgebra.leftInvariantDerivation d).toLinearMap ^ n)
        (coact (R := R) (C := H) m) := by
  have hcounit := congrArg (TensorProduct.rid R M)
    (lTensor_counit_coact (R := R) (C := H) ((differential (R := R) (H := H) d ^ n) m))
  rw [TensorProduct.rid_tmul, one_smul] at hcounit
  rw [← hcounit, coact_pow_differential, ← LinearMap.lTensor_comp_apply, tensorComponent_def,
    LinearMap.comp_apply, LinearEquiv.coe_coe]

omit [Comodule R H M] in
private theorem lTensor_pow_eq_pow_lTensor (f : Module.End R H) (n : ℕ) :
    (f ^ n).lTensor M = (f.lTensor M) ^ n := by
  induction n with
  | zero => simp [Module.End.one_eq_id]
  | succ n ih => rw [pow_succ', LinearMap.lTensor_mul, ih, pow_succ']

omit [Comodule R H M] in
private theorem exists_pow_lTensor_leftInvariantDerivation_eq_zero
    {d : Derivation R H (Bialgebra.CounitAlgebra R H R)}
    (hd : ∀ h : H, ∃ n, (Bialgebra.leftInvariantDerivation d)^[n] h = 0) (t : M ⊗[R] H) :
    ∃ n, ((Bialgebra.leftInvariantDerivation d).toLinearMap ^ n).lTensor M t = 0 := by
  induction t using TensorProduct.inductionOn with
  | tmul m h =>
    obtain ⟨n, hn⟩ := hd h
    refine ⟨n, ?_⟩
    rw [LinearMap.lTensor_tmul, FunLike.coe_pow_eq_iterate, Derivation.coeFn_coe, hn,
      TensorProduct.tmul_zero]
  | add x y hx hy =>
    obtain ⟨k, hk⟩ := hx
    obtain ⟨l, hl⟩ := hy
    refine ⟨max k l, ?_⟩
    rw [lTensor_pow_eq_pow_lTensor] at hk hl ⊢
    rw [map_add, Module.End.pow_map_zero_of_le (le_max_left k l) hk,
      Module.End.pow_map_zero_of_le (le_max_right k l) hl, add_zero]

/-- **Local nilpotence passes to every comodule.** If the left-invariant derivation of `d` is
locally nilpotent on `H`, then `Comodule.differential d` is locally nilpotent on every right
`H`-comodule `M`. -/
theorem exists_pow_differential_eq_zero {d : Derivation R H (Bialgebra.CounitAlgebra R H R)}
    (hd : ∀ h : H, ∃ n, (Bialgebra.leftInvariantDerivation d)^[n] h = 0) (m : M) :
    ∃ n, (differential (R := R) (H := H) (M := M) d ^ n) m = 0 := by
  obtain ⟨n, hn⟩ := exists_pow_lTensor_leftInvariantDerivation_eq_zero hd
    (coact (R := R) (C := H) m)
  refine ⟨n, ?_⟩
  have hcomp := (tensorComponent_map (Coalgebra.counit (R := R)) (LinearMap.id : M →ₗ[R] M)
    ((Bialgebra.leftInvariantDerivation d).toLinearMap ^ n) (coact (R := R) (C := H) m)).symm
  rw [pow_differential_apply]
  simpa only [LinearMap.id_apply, ← LinearMap.lTensor_def, hn, map_zero] using hcomp

end Bialgebra

end TauCeti.Comodule

namespace TauCeti.Bialgebra

section Converse

variable {R H : Type*} [CommRing R] [CommRing H] [_root_.Bialgebra R H] [Module.Projective R H]

/-- **Local nilpotence on finite subcomodules implies local nilpotence of the invariant vector
field.** When `H` is projective over `R`, every element of `H` belongs to a finite subcomodule of
the regular comodule, so local nilpotence of `Comodule.differential d` on all finite subcomodules of
`H` implies local nilpotence of `leftInvariantDerivation d` on `H`. -/
theorem exists_iterate_leftInvariantDerivation_eq_zero_of_forall_subcomodule
    {d : Derivation R H (CounitAlgebra R H R)}
    (hd : ∀ N : Subcomodule R H H, Module.Finite R N.toSubmodule →
      ∀ x : N, ∃ n, (Comodule.differential (R := R) (H := H) (M := N) d ^ n) x = 0)
    (h : H) : ∃ n, (leftInvariantDerivation d)^[n] h = 0 := by
  obtain ⟨N, hN, hh⟩ := Subcomodule.exists_finite_subcomodule_mem (R := R) (C := H) h
  obtain ⟨n, hn⟩ := hd N hN ⟨h, hh⟩
  have hmap : ∀ (k : ℕ) (x : N),
      (((Comodule.differential (R := R) (H := H) (M := N) d ^ k) x : N) : H) =
        (leftInvariantDerivation d)^[k] (x : H) := by
    intro k
    induction k with
    | zero => intro x; rfl
    | succ k ih =>
      intro x
      have hsub := (Subcomodule.subtype N).map_differential d
        ((Comodule.differential (R := R) (H := H) (M := N) d ^ k) x)
      simp only [Subcomodule.subtype_apply, ← toLinearMap_leftInvariantDerivation,
        Derivation.coeFn_coe] at hsub
      rw [pow_succ', mul_apply_eq_comp, hsub, ih, Function.iterate_succ_apply']
  refine ⟨n, ?_⟩
  simpa only [hn, ZeroMemClass.coe_zero] using (hmap n ⟨h, hh⟩).symm

/-- **Nilpotence on finite subcomodules implies local nilpotence of the invariant vector field.** -/
theorem exists_iterate_leftInvariantDerivation_eq_zero_of_forall_isNilpotent
    {d : Derivation R H (CounitAlgebra R H R)}
    (hd : ∀ N : Subcomodule R H H, Module.Finite R N.toSubmodule →
      IsNilpotent (Comodule.differential (R := R) (H := H) (M := N) d))
    (h : H) : ∃ n, (leftInvariantDerivation d)^[n] h = 0 :=
  exists_iterate_leftInvariantDerivation_eq_zero_of_forall_subcomodule
    (fun N hN ↦ (hd N hN).exists_pow_apply_eq_zero) h

end Converse

end TauCeti.Bialgebra

namespace TauCeti.Comodule

section HopfAlgebra

variable {R H M : Type*} [CommRing R] [CommRing H] [HopfAlgebra R H]
  [AddCommGroup M] [Module R M] [Comodule R H M]

attribute [local instance 100] LieRing.ofAssociativeRing

/-- A base-valued point acts on `m` by contracting the right factor of `coact m`. -/
theorem basePointsRepresentation_apply_eq_tensorComponent
    (g : WithConv (H →ₐ[R] R)) (m : M) :
    basePointsRepresentation (H := H) M g m =
      tensorComponent g.ofConv.toLinearMap (coact (R := R) (C := H) m) := by
  rw [basePointsRepresentation_apply, endOfPoint_tmul, one_smul, TensorProduct.lid_comm,
    tensorComponent_def, LinearMap.comp_apply, LinearEquiv.coe_coe]

variable [Algebra ℚ H] [Module ℚ M]

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
      rw [lTensor_pow_eq_pow_lTensor] at hu ⊢
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
    · rw [lTensor_pow_eq_pow_lTensor] at hN₁ hN₂ ⊢
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
  have hpowN : (differential (R := R) (H := H) (M := M) d ^ N) m = 0 := by
    have hcomp := (tensorComponent_map (Coalgebra.counit (R := R)) (LinearMap.id : M →ₗ[R] M)
      ((Bialgebra.leftInvariantDerivation d).toLinearMap ^ N) (coact (R := R) (C := H) m)).symm
    rw [pow_differential_apply]
    simpa only [LinearMap.id_apply, ← LinearMap.lTensor_def, hN, map_zero] using hcomp
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
        (by
          have hsmul : Bialgebra.leftInvariantDerivation (t • d) =
              t • Bialgebra.leftInvariantDerivation d :=
            (Bialgebra.leftInvariantDerivation (R := R) (H := H)).toLinearMap.map_smul t d
          have ht : ∀ h : H, ∃ n, (Bialgebra.leftInvariantDerivation (t • d))^[n] h = 0 := by
            simpa only [hsmul] using
              (Bialgebra.leftInvariantDerivation d).exists_iterate_smul_eq_zero hd t
          have hd_smul : differential (R := R) (H := H) (M := M) (t • d) =
              t • differential (R := R) (H := H) (M := M) d :=
            (differential (R := R) (H := H) (M := M)).toLinearMap.map_smul t d
          simpa only [hd_smul] using exists_pow_differential_eq_zero (M := M) ht) m := by
  have hsmul : Bialgebra.leftInvariantDerivation (t • d) =
      t • Bialgebra.leftInvariantDerivation d :=
    (Bialgebra.leftInvariantDerivation (R := R) (H := H)).toLinearMap.map_smul t d
  have ht : ∀ h : H, ∃ n, (Bialgebra.leftInvariantDerivation (t • d))^[n] h = 0 := by
    simpa only [hsmul] using
      (Bialgebra.leftInvariantDerivation d).exists_iterate_smul_eq_zero hd t
  have he : Bialgebra.expPointAt d hd t = WithConv.toConv (Bialgebra.expPoint (t • d) ht) := by
    apply WithConv.ext
    ext x
    rw [Bialgebra.expPointAt_apply_eq_counit_taylorExpAt, Bialgebra.expPoint_apply]
    simp only [hsmul]
    rw [Derivation.taylorExpAt_eq_taylorExp_smul]
  have hd_smul : differential (R := R) (H := H) (M := M) (t • d) =
      t • differential (R := R) (H := H) (M := M) d :=
    (differential (R := R) (H := H) (M := M)).toLinearMap.map_smul t d
  rw [he, basePointsRepresentation_expPoint]
  congr!

/-- **When the differentiated action is nilpotent, `expPointAt d hd t` acts as
`IsNilpotent.exp (t • differential d)`.** -/
theorem basePointsRepresentation_expPointAt_of_isNilpotent
    (d : Derivation R H (Bialgebra.CounitAlgebra R H R))
    (hd : ∀ h : H, ∃ n, (Bialgebra.leftInvariantDerivation d)^[n] h = 0)
    (hnil : IsNilpotent (differential (R := R) (H := H) (M := M) d)) (t : R) :
    basePointsRepresentation (H := H) M (Bialgebra.expPointAt d hd t) =
      IsNilpotent.exp (t • differential (R := R) (H := H) (M := M) d) := by
  have htnil : IsNilpotent (t • differential (R := R) (H := H) (M := M) d) := by
    rw [Algebra.smul_def]
    exact Commute.isNilpotent_mul_left (Algebra.commute_algebraMap_left t _) hnil
  ext m
  rw [basePointsRepresentation_expPointAt]
  exact LinearMap.congr_fun (Module.End.locallyNilpotentExp_eq_exp _ htnil) m

end HopfAlgebra

end TauCeti.Comodule

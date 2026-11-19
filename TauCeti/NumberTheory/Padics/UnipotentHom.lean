/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.Padics.RingHoms
public import Mathlib.Topology.Algebra.Module.ModuleTopology
public import TauCeti.RingTheory.Nilpotent.Log
import TauCeti.Topology.Algebra.Module.ModuleTopology

/-!
# Unipotent homomorphisms from the `ℓ`-adic integers

Let `E` be a topological commutative `ℚ_[ℓ]`-algebra, for instance a complete normed field
extension of `ℚ_[ℓ]`, and `V` a Hausdorff topological `E`-module. A homomorphism `h` from the
additive group of `ℤ_[ℓ]` to the automorphisms of `V` whose value at `1` is unipotent and which is
continuous in each vector is determined by that value: `h x = exp (x • log (h 1))` for every
`x : ℤ_[ℓ]`, with the finite exponential and logarithm of `IsNilpotent.exp` and
`IsNilpotent.log`. At integers this is `Units.exp_zsmul_log`; the general case follows from
density of `ℤ` in `ℤ_[ℓ]`, because the right-hand side is a polynomial in `x`. As in
`TauCeti.LinearAlgebra.End.Exponential`, the rational structure of `V` used by `IsNilpotent.exp`
is an instance argument `[Module ℚ V]`; an additive group has at most one.

The main results are:

* `MonoidHom.padicInt_coe_apply_eq_exp_smul_log`: the identity when multiplication in `E`, the
  scalar action of `ℚ_[ℓ]` on `E`, addition in `V` and the scalar action of `E` on `V` are
  continuous and `V` is Hausdorff, assuming only that `x ↦ h x v` is continuous for each `v : V`;
* `MonoidHom.padicInt_coe_apply_eq_exp_smul_log_of_isModuleTopology`: the case of a free
  `E`-module `V` with its module topology, over a Hausdorff topological ring `E`; over a field
  every `V` is free. Continuity of `h` for any of the usual topologies on `GL_E(V)` implies
  continuity in each vector.

Neither a norm nor completeness of `E` is needed. By Grothendieck's `ℓ`-adic monodromy theorem, a
quasi-unipotent `ℓ`-adic representation of the inertia group, such as the restriction of an
`ℓ`-adic Galois representation of a local field of residue characteristic different from `ℓ`,
acts on an open subgroup of the inertia group as `σ ↦ exp (t_ℓ(σ) • N)` for a nilpotent `N`, where
`t_ℓ` is the `ℓ`-adic tame character ([Del73], Theorem 8.2 and §8.4.2, pp. 566–569). The results
here give this formula for a homomorphism from `ℤ_[ℓ]` once its value at `1` is unipotent.

## References

* [Del73] P. Deligne, *Les constantes des équations fonctionnelles des fonctions L*, in
  *Modular Functions of One Variable II*, Lecture Notes in Math. 349, Springer (1973),
  pp. 501–597.
-/

public section

namespace MonoidHom

open IsNilpotent Multiplicative

variable {ℓ : ℕ} [Fact ℓ.Prime] {E V : Type*} [CommRing E] [TopologicalSpace E]
  [Algebra ℚ_[ℓ] E] [ContinuousSMul ℚ_[ℓ] E] [AddCommGroup V] [Module E V] [Module ℚ V]

/-- **Unipotent homomorphisms from `ℤ_[ℓ]`.** Let `V` be a Hausdorff topological module over a
topological commutative `ℚ_[ℓ]`-algebra `E`, and `h` a homomorphism from the additive group of
`ℤ_[ℓ]` to the automorphisms of `V` that is continuous in each vector. If `h 1` is unipotent,
then `h x = exp (x • log (h 1))` for every `x : ℤ_[ℓ]`. -/
theorem padicInt_coe_apply_eq_exp_smul_log [ContinuousMul E] [TopologicalSpace V]
    [ContinuousAdd V] [ContinuousSMul E V] [T2Space V]
    (h : Multiplicative ℤ_[ℓ] →* (Module.End E V)ˣ)
    (hcont : ∀ v : V, Continuous fun x : ℤ_[ℓ] ↦ (h (ofAdd x) : Module.End E V) v)
    (hu : IsNilpotent ((h (ofAdd 1) : Module.End E V) - 1)) (x : ℤ_[ℓ]) :
    (h (ofAdd x) : Module.End E V) =
      exp (algebraMap ℚ_[ℓ] E x • log (h (ofAdd 1) : Module.End E V)) := by
  -- `E` need not be a field: its rational structure, and that of `V` over it, come from `ℚ_[ℓ]`.
  let : Algebra ℚ E := ((algebraMap ℚ_[ℓ] E).comp (algebraMap ℚ ℚ_[ℓ])).toAlgebra
  let : Module ℚ_[ℓ] V := .compHom V (algebraMap ℚ_[ℓ] E)
  have : IsScalarTower ℚ E V :=
    ⟨fun q e w ↦ by rw [Algebra.smul_def, mul_smul]; exact Rat.cast_smul_eq_qsmul ℚ_[ℓ] q _⟩
  set L := log (h (ofAdd 1) : Module.End E V)
  have hL : IsNilpotent L := isNilpotent_log hu
  obtain ⟨b, hb⟩ := hL
  let c : ℤ_[ℓ] → E := fun y ↦ algebraMap ℚ_[ℓ] E y
  have hc : Continuous c := (continuous_algebraMap ℚ_[ℓ] E).comp continuous_subtype_val
  have hpow (y : ℤ_[ℓ]) : (c y • L) ^ b = 0 := by rw [smul_pow, hb, smul_zero]
  have hexp (y : ℤ_[ℓ]) (v : V) : exp (c y • L) v =
      ∑ i ∈ Finset.range b, (i.factorial : ℚ)⁻¹ • (c y ^ i • (L ^ i) v) := by
    rw [exp_eq_sum (hpow y), LinearMap.sum_apply]
    simp [smul_pow]
  refine LinearMap.ext fun v ↦ ?_
  have hψ : Continuous fun y ↦ exp (c y • L) v := by
    simp only [hexp]
    refine continuous_finsetSum _ fun i _ ↦ ?_
    simp only [← Rat.cast_smul_eq_qsmul ℚ_[ℓ] (i.factorial : ℚ)⁻¹]
    exact continuous_const.smul (M := E) ((hc.pow i).smul continuous_const)
  refine congrFun (PadicInt.denseRange_intCast.equalizer (hcont v) hψ (funext fun n ↦ ?_)) x
  have hcn : c n = n := by simp [c, PadicInt.coe_intCast, map_intCast]
  have hn : ofAdd (n : ℤ_[ℓ]) = ofAdd 1 ^ n := by rw [← ofAdd_zsmul, zsmul_one]
  simp only [Function.comp_apply, hcn, Int.cast_smul_eq_zsmul, hn, map_zpow, L,
    Units.exp_zsmul_log _ hu]

/-- **Unipotent homomorphisms from `ℤ_[ℓ]`, module topology case.** Let `V` be a free module over
a Hausdorff topological commutative `ℚ_[ℓ]`-algebra `E`, with its module topology, and `h` a
homomorphism from the additive group of `ℤ_[ℓ]` to `GL_E(V)` that is continuous in each vector.
If `h 1` is unipotent, then `h x = exp (x • log (h 1))` for every `x : ℤ_[ℓ]`. -/
theorem padicInt_coe_apply_eq_exp_smul_log_of_isModuleTopology [IsTopologicalSemiring E]
    [T2Space E] [Module.Free E V] [TopologicalSpace V] [IsModuleTopology E V]
    (h : Multiplicative ℤ_[ℓ] →* (Module.End E V)ˣ)
    (hcont : ∀ v : V, Continuous fun x : ℤ_[ℓ] ↦ (h (ofAdd x) : Module.End E V) v)
    (hu : IsNilpotent ((h (ofAdd 1) : Module.End E V) - 1)) (x : ℤ_[ℓ]) :
    (h (ofAdd x) : Module.End E V) =
      exp (algebraMap ℚ_[ℓ] E x • log (h (ofAdd 1) : Module.End E V)) := by
  have := IsModuleTopology.toContinuousAdd E V
  have := IsModuleTopology.toContinuousSMul E V
  have := TauCeti.ModuleTopology.t2Space (Module.Free.chooseBasis E V)
  exact h.padicInt_coe_apply_eq_exp_smul_log hcont hu x

end MonoidHom

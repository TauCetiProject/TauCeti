/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Tangent.InvariantDerivation
public import TauCeti.RingTheory.Derivation.TaylorExp
import Mathlib.Algebra.Module.Rat

/-!
# Exponentials of locally nilpotent tangent vectors

Let `H` be a commutative bialgebra over `R`, the coordinate ring of an affine monoid, which is
also a `ℚ`-algebra, and let `d` be a tangent vector at the identity. Suppose its left-invariant
vector field `D` is locally nilpotent; this is the situation of nilpotent tangent vectors of
unipotent groups in characteristic zero. Then the Taylor exponential `exp D = ∑ Dⁿ / n!` is an
algebra endomorphism of `H`, and composing it with the counit gives a rational point

```text
exp d = ε ∘ exp D : H →ₐ[R] R.
```

The invariance `Δ ∘ D = (id ⊗ D) ∘ Δ` shows that `exp D` is right translation by this point:
`exp D h = ∑ h₍₁₎ (exp d)(h₍₂₎)`. Thus the flow of the invariant vector field is the finite
Taylor series, and its value at the identity is the exponential of the tangent vector.

## Main declarations

* `TauCeti.Bialgebra.expPoint`: the exponential `ε ∘ exp D` of a tangent vector whose
  left-invariant derivation is locally nilpotent.
* `TauCeti.Bialgebra.expPoint_zero`: the exponential of the zero tangent vector is the identity
  point.
* `TauCeti.Bialgebra.taylorExp_leftInvariantDerivation_apply`: the Taylor exponential of the
  invariant vector field is right translation by the exponential point.

## References

* J. S. Milne, *Algebraic Groups* (2017), Chapters 10 and 14.
* G. Freudenburg, *Algebraic Theory of Locally Nilpotent Derivations*, Encyclopaedia of
  Mathematical Sciences 136, Springer (2006), Chapter 1.
-/

public section

open TensorProduct LinearMap

namespace TauCeti.Bialgebra

variable {R H : Type*} [CommRing R] [CommRing H] [_root_.Bialgebra R H]

variable [Algebra ℚ H]

/-- The **exponential of a tangent vector** `d` whose left-invariant derivation `D` is locally
nilpotent: the rational point `ε ∘ exp D`, where `exp D = ∑ Dⁿ / n!` is the Taylor exponential. -/
noncomputable def expPoint (d : Derivation R H (CounitAlgebra R H R))
    (hd : ∀ h, ∃ n, (leftInvariantDerivation d)^[n] h = 0) : H →ₐ[R] R :=
  (_root_.Bialgebra.counitAlgHom R H).comp ((leftInvariantDerivation d).taylorExp hd)

/-- The exponential point is the counit of the Taylor exponential of the invariant vector
field. -/
theorem expPoint_apply (d : Derivation R H (CounitAlgebra R H R))
    (hd : ∀ h, ∃ n, (leftInvariantDerivation d)^[n] h = 0) (h : H) :
    expPoint d hd h = Coalgebra.counit (R := R) ((leftInvariantDerivation d).taylorExp hd h) :=
  (rfl)

/-- The exponential of the zero tangent vector is the identity point, the counit. -/
@[simp]
theorem expPoint_zero (hd : ∀ h, ∃ n, (leftInvariantDerivation (0 : Derivation R H
      (CounitAlgebra R H R)))^[n] h = 0) :
    expPoint 0 hd = _root_.Bialgebra.counitAlgHom R H := by
  ext h
  rw [expPoint_apply, Derivation.taylorExp_apply_eq_sum _ hd (n := 1) (by simp)]
  simp

/-- **The Taylor exponential of an invariant vector field is right translation by the
exponential point**: `exp D h = ∑ h₍₁₎ (exp d)(h₍₂₎)`. -/
theorem taylorExp_leftInvariantDerivation_apply
    (d : Derivation R H (CounitAlgebra R H R))
    (hd : ∀ h, ∃ n, (leftInvariantDerivation d)^[n] h = 0) (h : H) :
    (leftInvariantDerivation d).taylorExp hd h =
      tensorComponent (expPoint d hd).toLinearMap (Coalgebra.comul (R := R) h) := by
  classical
  -- The counit makes `R` a `ℚ`-algebra, which lets the rational Taylor coefficients pass through
  -- the counit.
  let : Algebra ℚ R :=
    ((_root_.Bialgebra.counitAlgHom R H).toRingHom.comp (algebraMap ℚ H)).toAlgebra
  set D := leftInvariantDerivation d
  let 𝓡 := Coalgebra.Repr.arbitrary R h
  -- A single truncation `N` computes the Taylor exponential of `h` and of every right
  -- comultiplication factor of `h`.
  choose m hm using hd
  let N := m h + ∑ i ∈ 𝓡.index, m (𝓡.right i)
  have hN : ∀ x, m x ≤ N → D^[N] x = 0 := fun x hx => by
    simpa [Module.End.pow_apply] using Module.End.pow_map_zero_of_le (f := D.toLinearMap) hx
      (by simpa [Module.End.pow_apply] using hm x)
  have hright : ∀ i ∈ 𝓡.index, D^[N] (𝓡.right i) = 0 := fun i hi =>
    hN _ (le_add_left (Finset.single_le_sum (fun j _ => Nat.zero_le (m (𝓡.right j))) hi))
  have hexp : ∀ i ∈ 𝓡.index, expPoint d hd (𝓡.right i) =
      ∑ k ∈ Finset.range N,
        (k.factorial : ℚ)⁻¹ • Coalgebra.counit (R := R) (D^[k] (𝓡.right i)) := by
    intro i hi
    rw [expPoint_apply, D.taylorExp_apply_eq_sum hd (hright i hi), map_sum]
    simp only [map_rat_smul]
  calc D.taylorExp hd h
      = ∑ k ∈ Finset.range N, (k.factorial : ℚ)⁻¹ • D^[k] h :=
        D.taylorExp_apply_eq_sum hd (hN h (Nat.le_add_right _ _))
    _ = ∑ k ∈ Finset.range N, ∑ i ∈ 𝓡.index,
          ((k.factorial : ℚ)⁻¹ • Coalgebra.counit (R := R) (D^[k] (𝓡.right i))) • 𝓡.left i := by
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [iterate_leftInvariantDerivation_apply, ← 𝓡.eq, map_sum, Finset.smul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [tensorComponent_tmul, smul_assoc, LinearMap.comp_apply, Module.End.coe_pow,
          Derivation.coeFn_coe]
    _ = ∑ i ∈ 𝓡.index, expPoint d hd (𝓡.right i) • 𝓡.left i := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun i hi => ?_
        rw [hexp i hi, Finset.sum_smul]
    _ = tensorComponent (expPoint d hd).toLinearMap (Coalgebra.comul (R := R) h) := by
        rw [← 𝓡.eq, map_sum]
        simp only [tensorComponent_tmul, AlgHom.toLinearMap_apply]

end TauCeti.Bialgebra

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.NumberTheory.Padics.RingHoms
public import TauCeti.NumberTheory.Padics.FreeModuleReduction
public import TauCeti.RepresentationTheory.Invariants
import Mathlib.Algebra.Module.Submodule.Pointwise

/-!
# Invariants of projective `p`-adic group-algebra modules

Let `X` be an integral representation of a finite group and let `Y` be a projective modular
representation obtained from `X` by reduction modulo `p`. Taking invariants commutes with this
reduction: every invariant of `Y` has an invariant lift, and an invariant vector of `X` that is
divisible by `p` in `X` is already divisible by `p` inside `X^G`. Consequently

```
#Y^G = p ^ rank_{ℤ_p}(X^G).
```

This is the numerical bridge between modular Hom spaces and the ordinary characters of their
projective `ℤ_p[G]`-lifts. The latter determine `rank(X^G)` by the character-average formula.
Together these facts are the fixed-point calculation in Swan's rational detection theorem for
projective integral representations.

## Main results

* `Representation.natCard_invariants_eq_pow_finrank_of_reduction`: the invariant count
  above, for an arbitrary equivariant semilinear reduction map with the expected kernel. The
  cardinality of the reduction of a finite free `ℤ_p`-module is
  `TauCeti.natCard_quotient_padicInt_smul_top`.

## References

* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, second edition,
  Proposition (5.6.10).
* J.-P. Serre, *Linear Representations of Finite Groups*, Part III, §15–16.
* R. G. Swan, *Induced representations and projective modules*, Ann. of Math. 71 (1960).
-/

public section

open scoped MonoidAlgebra Pointwise

universe u v w

namespace Representation

section Reduction

variable (p : ℕ) [Fact p.Prime] {G : Type u} [Group G] [Finite G]
variable {V : Type v} [AddCommGroup V] [Module ℤ_[p] V] [Module.Finite ℤ_[p] V]
  [Module.IsTorsionFree ℤ_[p] V]
variable {W : Type w} [AddCommGroup W] [Module (ZMod p) W]

/-- **Invariant vectors commute numerically with projective reduction modulo `p`.** Let `ρ` be
an integral representation and `σ` a projective modular representation. Suppose that the
equivariant semilinear surjection `f : V → W` has kernel `pV`. Then
`#(σ^G) = p ^ rank_{ℤ_p}(ρ^G)`.

More precisely, `f` restricts to a surjection `ρ^G → σ^G` with kernel `p ρ^G`, so `σ^G` is the
reduction modulo `p` of the finite free `ℤ_p`-module `ρ^G`. -/
theorem natCard_invariants_eq_pow_finrank_of_reduction
    (ρ : Representation ℤ_[p] G V) (σ : Representation (ZMod p) G W)
    [Module.Projective (MonoidAlgebra (ZMod p) G) σ.asModule]
    (f : V →ₛₗ[PadicInt.toZMod (p := p)] W) (hf : Function.Surjective f)
    (hfg : ∀ g x, f (ρ g x) = σ g (f x))
    (hker : ∀ x, f x = 0 ↔ x ∈ (p : ℤ_[p]) • (⊤ : Submodule ℤ_[p] V)) :
    Nat.card σ.invariants = p ^ Module.finrank ℤ_[p] ρ.invariants := by
  let _ : Module ℤ_[p] W := Module.compHom W (PadicInt.toZMod (p := p))
  let _ : Module ℤ_[p] σ.invariants :=
    Module.compHom σ.invariants (PadicInt.toZMod (p := p))
  let F : ρ.invariants →ₗ[ℤ_[p]] σ.invariants :=
    { toFun := fun x ↦ ⟨f x, fun g ↦ by
          rw [← hfg g x]
          exact congrArg f (x.property g)⟩
      map_add' := fun x y ↦ Subtype.ext (f.map_add x y)
      map_smul' := fun r x ↦ by
        apply Subtype.ext
        -- Unfold the restricted scalar actions so the semilinear map law applies.
        change f (r • (x : V)) = (PadicInt.toZMod (p := p)) r • f x
        exact f.map_smulₛₗ r x }
  have hFsurj : Function.Surjective F := by
    intro y
    obtain ⟨x, hx⟩ := Representation.exists_invariant_preimage_of_surjective_of_projective
      ρ σ f.toAddMonoidHom hf hfg y
    exact ⟨x, Subtype.ext hx⟩
  have hp : (p : ℤ_[p]) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
  have hFker : LinearMap.ker F = (p : ℤ_[p]) • (⊤ : Submodule ℤ_[p] ρ.invariants) := by
    ext x
    constructor
    · intro hx
      have hfx : f x = 0 := congrArg Subtype.val (LinearMap.mem_ker.mp hx)
      have hxdiv := (hker x).mp hfx
      rw [Submodule.mem_smul_pointwise_iff_exists] at hxdiv ⊢
      obtain ⟨z, -, hz⟩ := hxdiv
      refine ⟨⟨z, fun g ↦ ?_⟩, Submodule.mem_top, ?_⟩
      · apply smul_right_injective V hp
        calc
          (p : ℤ_[p]) • ρ g z = ρ g ((p : ℤ_[p]) • z) := (map_smul (ρ g) _ _).symm
          _ = ρ g x := congrArg (ρ g) hz
          _ = x := x.property g
          _ = (p : ℤ_[p]) • z := hz.symm
      exact Subtype.ext hz
    · intro hx
      rw [Submodule.mem_smul_pointwise_iff_exists] at hx
      obtain ⟨z, -, hz⟩ := hx
      apply LinearMap.mem_ker.mpr
      rw [← hz]
      apply Subtype.ext
      -- Unfold the two restricted maps so reduction sends the scalar `p` to zero.
      change f ((p : ℤ_[p]) • (z : V)) = 0
      rw [f.map_smulₛₗ]
      simp
  have : Module.Free ℤ_[p] ρ.invariants := Module.free_of_finite_type_torsion_free'
  rw [← Nat.card_congr (F.quotKerEquivOfSurjective hFsurj).toEquiv,
    hFker, TauCeti.natCard_quotient_padicInt_smul_top p ρ.invariants]

end Reduction

end Representation

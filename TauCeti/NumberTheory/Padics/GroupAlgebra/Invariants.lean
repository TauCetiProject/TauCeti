/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.NumberTheory.Padics.RingHoms
public import TauCeti.NumberTheory.Padics.FreeModuleReduction
public import TauCeti.RepresentationTheory.BaseChange
public import TauCeti.RepresentationTheory.Invariants
import Mathlib.Algebra.Module.Submodule.Pointwise
import Mathlib.RingTheory.Flat.Localization
import TauCeti.NumberTheory.Padics.GroupAlgebra.Reduction
import TauCeti.RepresentationTheory.AsModule
import TauCeti.RepresentationTheory.OfModule

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

* `Representation.finrank_invariants_baseChange_ratPadic`: extending scalars from `ℤ_p` to
  `ℚ_p` preserves the rank of the invariant submodule.
* `Representation.natCard_invariants_eq_pow_finrank_of_reduction`: the invariant count
  above, for an arbitrary equivariant semilinear reduction map with the expected kernel. The
  cardinality of the reduction of a finite free `ℤ_p`-module is
  `TauCeti.natCard_quotient_padicInt_smul_top`.
* `Representation.natCard_invariants_eq_pow_finrank_of_bijective`: the same count when
  the projective modular representation is identified with the reduction of a `ℤ_p[G]`-module.
* `Representation.natCard_invariants_eq_of_trace_eq`: two such reductions of finitely generated
  projective `ℤ_p`-modules with the same character have equally many invariants.

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

/-- Extending a finite torsion-free `ℤ_p`-representation to `ℚ_p` preserves the rank of its
invariant submodule. This is the rational counterpart to invariant lifting modulo `p`: it lets
the integral invariant count be read from the rationalized representation. -/
theorem finrank_invariants_baseChange_ratPadic (ρ : Representation ℤ_[p] G V) :
    Module.finrank ℚ_[p] (Representation.baseChange ℚ_[p] ρ).invariants =
      Module.finrank ℤ_[p] ρ.invariants := by
  let _ : Module.Flat ℤ_[p] ℚ_[p] :=
    IsLocalization.flat ℚ_[p] (nonZeroDivisors ℤ_[p])
  let _ : Module.Free ℤ_[p] ρ.invariants := Module.free_of_finite_type_torsion_free'
  exact (LinearEquiv.finrank_eq
    (_root_.Representation.invariantsBaseChangeEquiv (A := ℚ_[p]) ρ)).symm.trans
      Module.finrank_baseChange

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

open TauCeti TauCeti.Representation

namespace Representation

/-- **Invariant counts of projective lifts.** If a projective `𝔽_p[G]`-representation `η` is the
reduction of a `ℤ_p[G]`-module `X`, then `#η^G = p ^ rank (X^G)`. -/
theorem natCard_invariants_eq_pow_finrank_of_bijective
    (p : ℕ) [Fact p.Prime] {G : Type*} [Group G] [Finite G] {W : Type*} [AddCommGroup W]
    [Module (ZMod p) W] (η : _root_.Representation (ZMod p) G W)
    [Module.Projective (MonoidAlgebra (ZMod p) G) η.asModule]
    (X : Type*) [AddCommGroup X] [Module ℤ_[p] X] [Module (MonoidAlgebra ℤ_[p] G) X]
    [IsScalarTower ℤ_[p] (MonoidAlgebra ℤ_[p] G) X] [Module.Finite ℤ_[p] X]
    [Module.IsTorsionFree ℤ_[p] X]
    (f : (X ⧸ Ideal.span {(p : MonoidAlgebra ℤ_[p] G)} •
      (⊤ : Submodule (MonoidAlgebra ℤ_[p] G) X)) →ₛₗ[MonoidAlgebra.mapRingHom G
        (PadicInt.toZMod (p := p))] η.asModule)
    (hf : Function.Bijective f) :
    Nat.card η.invariants = p ^ Module.finrank ℤ_[p]
      (_root_.Representation.ofModule' (k := ℤ_[p]) (G := G) X).invariants := by
  -- Compare `η` with the representation `Representation.ofModule' η.asModule`, which the
  -- reduction map intertwines with `Representation.ofModule' X`.
  let e := ofModule'AsModuleEquiv (k := ZMod p) (G := G) η.asModule
  let _ : Module.Projective (MonoidAlgebra (ZMod p) G)
      (_root_.Representation.ofModule' (k := ZMod p) (G := G) η.asModule).asModule :=
    Module.Projective.of_equiv' e.symm
  rw [← Nat.card_congr (equivOfAsModuleLinearEquiv e).invariantsLinearEquiv.toEquiv]
  exact _root_.Representation.natCard_invariants_eq_pow_finrank_of_reduction p _ _
    (compPadicReductionMk p G f) (compPadicReductionMk_surjective p G f hf.2)
    (compPadicReductionMk_ofModule' p G f) (compPadicReductionMk_eq_zero_iff p G f hf.1)


/-- **Invariant counts from characters.** Projective `𝔽_p[G]`-representations that are the
reductions of `ℤ_p[G]`-lattices with the same characters have equally many invariants: both
counts are `p` to the rank of the invariants of the lattice, which is the average of the
character. -/
theorem natCard_invariants_eq_of_trace_eq (p : ℕ) [Fact p.Prime] {G : Type u} [Group G]
    [Finite G] {W₁ W₂ : Type*} [AddCommGroup W₁] [Module (ZMod p) W₁] [AddCommGroup W₂]
    [Module (ZMod p) W₂] (η₁ : Representation (ZMod p) G W₁) (η₂ : Representation (ZMod p) G W₂)
    [Module.Projective (MonoidAlgebra (ZMod p) G) η₁.asModule]
    [Module.Projective (MonoidAlgebra (ZMod p) G) η₂.asModule]
    (X₁ X₂ : Type*) [AddCommGroup X₁] [Module ℤ_[p] X₁] [Module (MonoidAlgebra ℤ_[p] G) X₁]
    [IsScalarTower ℤ_[p] (MonoidAlgebra ℤ_[p] G) X₁] [Module.Finite ℤ_[p] X₁]
    [Module.Projective ℤ_[p] X₁] [AddCommGroup X₂] [Module ℤ_[p] X₂]
    [Module (MonoidAlgebra ℤ_[p] G) X₂] [IsScalarTower ℤ_[p] (MonoidAlgebra ℤ_[p] G) X₂]
    [Module.Finite ℤ_[p] X₂] [Module.Projective ℤ_[p] X₂]
    (f₁ : (X₁ ⧸ Ideal.span {(p : MonoidAlgebra ℤ_[p] G)} •
      (⊤ : Submodule (MonoidAlgebra ℤ_[p] G) X₁)) →ₛₗ[MonoidAlgebra.mapRingHom G
        (PadicInt.toZMod (p := p))] η₁.asModule) (hf₁ : Function.Bijective f₁)
    (f₂ : (X₂ ⧸ Ideal.span {(p : MonoidAlgebra ℤ_[p] G)} •
      (⊤ : Submodule (MonoidAlgebra ℤ_[p] G) X₂)) →ₛₗ[MonoidAlgebra.mapRingHom G
        (PadicInt.toZMod (p := p))] η₂.asModule) (hf₂ : Function.Bijective f₂)
    (htr : ∀ g : G, LinearMap.trace ℤ_[p] X₁ (ofModule' (k := ℤ_[p]) (G := G) X₁ g) =
      LinearMap.trace ℤ_[p] X₂ (ofModule' (k := ℤ_[p]) (G := G) X₂ g)) :
    Nat.card η₁.invariants = Nat.card η₂.invariants := by
  classical
  rw [natCard_invariants_eq_pow_finrank_of_bijective p η₁ X₁ f₁ hf₁,
    natCard_invariants_eq_pow_finrank_of_bijective p η₂ X₂ f₂ hf₂]
  congr 1
  rw [← finrank_invariants_baseChange_ratPadic p (ofModule' (k := ℤ_[p]) (G := G) X₁),
    ← finrank_invariants_baseChange_ratPadic p (ofModule' (k := ℤ_[p]) (G := G) X₂)]
  let _ := Fintype.ofFinite G
  let _ : Invertible (Nat.card G : ℚ_[p]) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  apply Nat.cast_injective (R := ℚ_[p])
  rw [← (Representation.baseChange ℚ_[p]
      (ofModule' (k := ℤ_[p]) (G := G) X₁)).card_inv_mul_sum_char_eq_finrank,
    ← (Representation.baseChange ℚ_[p]
      (ofModule' (k := ℤ_[p]) (G := G) X₂)).card_inv_mul_sum_char_eq_finrank]
  congr 1
  refine Finset.sum_congr rfl fun g _ ↦ ?_
  simp only [Representation.character, Representation.baseChange_apply,
    LinearMap.trace_baseChange]
  exact congrArg _ (htr g)

end Representation

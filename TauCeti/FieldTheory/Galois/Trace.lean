/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.IsGaloisGroup.Defs
public import Mathlib.RingTheory.Norm.Transitivity
public import Mathlib.RingTheory.Trace.Basic
import Mathlib.FieldTheory.Galois.IsGaloisGroup
import Mathlib.FieldTheory.Normal.Basic
import Mathlib.LinearAlgebra.LinearIndependent.Basic
import TauCeti.GroupTheory.Coset.Fiber

/-!
# Sums and products of Galois automorphisms: the trace and the norm

Mathlib's `trace_eq_sum_automorphisms` writes the trace of a finite Galois extension as the sum of
its automorphisms, and `Algebra.norm_eq_prod_automorphisms` writes the norm as their product. This
file states the first for an abstract finite Galois group and records consequences for a tower
`K ⊆ L ⊆ M`.

## Main results

* `IsGaloisGroup.algebraMap_trace_eq_sum`: for a finite Galois group `G` of `L/K`, the trace of
  `x` is the sum of the `g • x` over `g : G`.
* `Algebra.trace_eq_zero_of_apply_eq_neg`: an element negated by an automorphism of order two has
  trace zero.
* `MonoidHom.prod_fiber_eq_prod_liftNormal_mul` (and `MonoidHom.sum_fiber_eq_sum_liftNormal_mul`):
  for `f : Gal(M/K) → Gal(L/K)` compatible with the inclusion `L ⊆ M`, the fibre of `f` over `σ`
  is the coset `σ.liftNormal M · Gal(M/L)`, so a product over it is a product over `Gal(M/L)`.
* `MonoidHom.sum_fiber_apply_eq_algebraMap_trace`: for `f : Gal(M/K) → Gal(L/K)` compatible with the
  inclusion `L ⊆ M`, the automorphisms in the fibre of `f` over `σ` sum to `σ ∘ Tr_{M/L}`, because
  that fibre is a coset of `Gal(M/L)`.
* `MonoidHom.prod_fiber_apply_eq_algebraMap_norm`: in the same situation, the product of the
  conjugates `g z` over that fibre is `σ ∘ N_{M/L}`.
* `Module.Basis.sum_traceDual_mul_apply`: for an `L`-basis `m` of a finite Galois extension `M/L`
  with trace-dual basis `m*`, `∑ᵢ m*ᵢ · g(mᵢ)` is `1` if `g = 1` and `0` for every other
  `g ∈ Gal(M/L)`, by Dedekind's independence of characters.
-/

public section

open Module

namespace IsGaloisGroup

variable (G K : Type*) {L : Type*} [Group G] [Field K] [Field L] [Algebra K L]
  [MulSemiringAction G L] [IsGaloisGroup G K L] [Fintype G]

/-- For a finite Galois group `G` of `L/K`, the trace of `x` is the sum of the `g • x` over
`g : G`. This is `trace_eq_sum_automorphisms` for an abstract Galois group. -/
theorem algebraMap_trace_eq_sum (x : L) :
    algebraMap K L (Algebra.trace K L x) = ∑ g : G, g • x := by
  have := finiteDimensional G K L
  have := isGalois G K L
  rw [trace_eq_sum_automorphisms]
  exact (Fintype.sum_equiv (mulEquivAlgEquiv G K L).toEquiv _ _ fun _ ↦ by simp).symm

end IsGaloisGroup

namespace Algebra

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

/-- In a Galois extension `L/K`, the trace of an `x` negated by an automorphism `τ` of
order two vanishes: the automorphisms `g` and `g τ` pair off and `g x + (g τ) x = 0`. In
characteristic two this says that `τ`-fixed elements have trace zero. Both hypotheses on `τ` are
needed in characteristic two, for `τ = 1` on `L = K = 𝔽₂` and for the Frobenius of `𝔽₈/𝔽₂`, of
order three, each with `x = 1`. -/
theorem trace_eq_zero_of_apply_eq_neg [IsGalois K L] {τ : Gal(L/K)} (hτ : τ ≠ 1)
    (hττ : τ * τ = 1) {x : L} (hx : τ x = -x) : trace K L x = 0 := by
  by_cases hfin : FiniteDimensional K L
  swap
  · rw [trace_eq_zero_of_not_exists_basis K fun ⟨_, ⟨b⟩⟩ ↦ hfin (Module.Finite.of_basis b),
      LinearMap.zero_apply]
  refine FaithfulSMul.algebraMap_injective K L ?_
  rw [trace_eq_sum_automorphisms, map_zero]
  refine Finset.sum_involution (fun g _ ↦ g * τ) (fun g _ ↦ ?_) (fun g _ _ ↦ ?_)
    (fun _ _ ↦ Finset.mem_univ _) (fun g _ ↦ by rw [mul_assoc, hττ, mul_one])
  · rw [AlgEquiv.mul_apply, hx, map_neg, add_neg_cancel]
  · simpa using hτ

end Algebra

namespace MonoidHom

variable {K L M : Type*} [Field K] [Field L] [Field M] [Algebra K L] [Algebra K M] [Algebra L M]
  [IsScalarTower K L M]

/-- **The fibre of restriction is a coset of `Gal(M/L)`**, in product form: for
`f : Gal(M/K) → Gal(L/K)` compatible with the inclusion `L ⊆ M`, the product of `φ` over the
fibre of `f` above `σ` is the product of `φ (σ.liftNormal M * τ)` over `τ ∈ Gal(M/L)`. -/
theorem prod_fiber_eq_prod_liftNormal_mul {R : Type*} [CommMonoid R] [FiniteDimensional K M]
    [FiniteDimensional L M] [Normal K M] [DecidableEq Gal(L/K)] (f : Gal(M/K) →* Gal(L/K))
    (hf : ∀ g x, algebraMap L M (f g x) = g (algebraMap L M x)) (σ : Gal(L/K))
    (φ : Gal(M/K) → R) :
    ∏ g ∈ Finset.univ.filter (fun g ↦ f g = σ), φ g =
      ∏ τ : Gal(M/L), φ (σ.liftNormal M * τ.restrictScalars K) := by
  classical
  have hg₀ : f (σ.liftNormal M) = σ := AlgEquiv.ext fun x ↦
    (algebraMap L M).injective ((hf _ x).trans (σ.liftNormal_commutes M x))
  -- `f` is trivial exactly on the automorphisms fixing `L`
  have hker (g : Gal(M/K)) : f g = 1 ↔ ∀ x, g (algebraMap L M x) = algebraMap L M x := by
    refine ⟨fun h x ↦ by rw [← hf, h, AlgEquiv.one_apply], fun h ↦ AlgEquiv.ext fun x ↦
      (algebraMap L M).injective ?_⟩
    rw [hf, h, AlgEquiv.one_apply]
  -- the kernel of `f` is `Gal(M/L)`, viewed inside `Gal(M/K)`
  let e : f.ker ≃ Gal(M/L) :=
    { toFun t := AlgEquiv.ofRingEquiv (f := (t : Gal(M/K)).toRingEquiv) ((hker _).1 t.property)
      invFun τ := ⟨τ.restrictScalars K, (hker _).2 τ.commutes⟩
      left_inv _ := Subtype.ext <| AlgEquiv.ext fun _ ↦ rfl
      right_inv _ := AlgEquiv.ext fun _ ↦ rfl }
  rw [Finset.prod_subtype (p := fun g ↦ f g = σ) _ (fun _ ↦ by simp),
    f.prod_fiber_eq_prod_ker_mul_left hg₀]
  exact Fintype.prod_equiv e _ _ fun _ ↦ rfl

/-- **The fibre of restriction is a coset of `Gal(M/L)`**, in sum form: for
`f : Gal(M/K) → Gal(L/K)` compatible with the inclusion `L ⊆ M`, the sum of `φ` over the fibre
of `f` above `σ` is the sum of `φ (σ.liftNormal M * τ)` over `τ ∈ Gal(M/L)`. -/
theorem sum_fiber_eq_sum_liftNormal_mul {R : Type*} [AddCommMonoid R] [FiniteDimensional K M]
    [FiniteDimensional L M] [Normal K M] [DecidableEq Gal(L/K)] (f : Gal(M/K) →* Gal(L/K))
    (hf : ∀ g x, algebraMap L M (f g x) = g (algebraMap L M x)) (σ : Gal(L/K))
    (φ : Gal(M/K) → R) :
    ∑ g ∈ Finset.univ.filter (fun g ↦ f g = σ), φ g =
      ∑ τ : Gal(M/L), φ (σ.liftNormal M * τ.restrictScalars K) := by
  simpa only [toAdd_prod, Function.comp_apply, toAdd_ofAdd] using
    congrArg Multiplicative.toAdd
      (prod_fiber_eq_prod_liftNormal_mul f hf σ (Multiplicative.ofAdd ∘ φ))

/-- For a finite Galois extension `M/K`, an intermediate field `L` and a homomorphism
`f : Gal(M/K) → Gal(L/K)` compatible with the inclusion `L ⊆ M`, the automorphisms in the fibre of
`f` over `σ` sum to `σ` composed with the trace of `M/L`. -/
theorem sum_fiber_apply_eq_algebraMap_trace [FiniteDimensional K M] [IsGalois K M]
    [DecidableEq Gal(L/K)] (f : Gal(M/K) →* Gal(L/K))
    (hf : ∀ g x, algebraMap L M (f g x) = g (algebraMap L M x)) (σ : Gal(L/K)) (z : M) :
    ∑ g ∈ Finset.univ.filter (fun g ↦ f g = σ), g z =
      algebraMap L M (σ (Algebra.trace L M z)) := by
  have : FiniteDimensional L M := Module.Finite.of_restrictScalars_finite K L M
  have : IsGalois L M := IsGalois.tower_top_of_isGalois K L M
  rw [sum_fiber_eq_sum_liftNormal_mul f hf σ, ← σ.liftNormal_commutes M,
    trace_eq_sum_automorphisms, map_sum]
  simp

/-- For a finite Galois extension `M/K`, an intermediate field `L` and a homomorphism
`f : Gal(M/K) → Gal(L/K)` compatible with the inclusion `L ⊆ M`, the product of the conjugates
`g z` over the automorphisms `g` in the fibre of `f` over `σ` is `σ` applied to the norm of
`M/L`. For `σ = 1` this is `Algebra.norm_eq_prod_automorphisms`. -/
theorem prod_fiber_apply_eq_algebraMap_norm [FiniteDimensional K M] [IsGalois K M]
    [DecidableEq Gal(L/K)] (f : Gal(M/K) →* Gal(L/K))
    (hf : ∀ g x, algebraMap L M (f g x) = g (algebraMap L M x)) (σ : Gal(L/K)) (z : M) :
    ∏ g ∈ Finset.univ.filter (fun g ↦ f g = σ), g z =
      algebraMap L M (σ (Algebra.norm L z)) := by
  have : FiniteDimensional L M := Module.Finite.of_restrictScalars_finite K L M
  have : IsGalois L M := IsGalois.tower_top_of_isGalois K L M
  rw [prod_fiber_eq_prod_liftNormal_mul f hf σ, ← σ.liftNormal_commutes M,
    Algebra.norm_eq_prod_automorphisms, map_prod]
  simp

end MonoidHom

open Classical in
/-- For an `L`-basis `m` of a finite Galois extension `M/L` and `g ∈ Gal(M/L)`, the sum
`∑ᵢ m*ᵢ · g(mᵢ)` against the trace-dual basis is `1` if `g = 1` and `0` otherwise. This is
Dedekind's independence of characters applied to
`x = ∑ᵢ m*ᵢ · Tr(mᵢ x) = ∑_g (∑ᵢ m*ᵢ · g(mᵢ)) · g(x)`. -/
theorem Module.Basis.sum_traceDual_mul_apply {L M : Type*} [Field L] [Field M] [Algebra L M]
    [FiniteDimensional L M] [IsGalois L M] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (m : Basis ι L M) (g : Gal(M/L)) :
    ∑ i, m.traceDual i * g (m i) = if g = 1 then 1 else 0 := by
  classical
  set C : Gal(M/L) → M := fun g ↦ ∑ i, m.traceDual i * g (m i)
  have hC (x : M) : ∑ g, C g * g x = x := by
    calc ∑ g, C g * g x
        = ∑ i, m.traceDual i * ∑ g : Gal(M/L), g (m i * x) := by
          simp only [C, Finset.sum_mul, Finset.mul_sum, map_mul, mul_assoc]
          exact Finset.sum_comm
      _ = ∑ i, Algebra.trace L M (x * m i) • m.traceDual i := by
          refine Finset.sum_congr rfl fun i _ ↦ ?_
          rw [← trace_eq_sum_automorphisms, Algebra.smul_def, mul_comm, mul_comm x]
      _ = x := by
          conv_rhs => rw [← m.traceDual.sum_repr x]
          simp [Algebra.traceForm_apply]
  have hli := (linearIndependent_monoidHom M M).comp (fun g : Gal(M/L) ↦ (g : M →* M))
    fun g g' h ↦ AlgEquiv.ext fun x ↦ by simpa using DFunLike.congr_fun h x
  have := Fintype.linearIndependent_iffₛ.1 hli C (fun g ↦ if g = 1 then 1 else 0) (by
    funext x
    simp [Finset.sum_apply, hC, ite_apply])
  simpa [C] using this g

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.Weight.Basis
public import TauCeti.LinearAlgebra.GeneralLinearGroup.InvariantRestrict
import TauCeti.LinearAlgebra.Eigenspace.Transport

/-!
# Cartan symmetries and integral weight components

A linear equivalence intertwining the designated Cartan operators through a permutation `σ`
carries the weight component of `μ` onto that of `μ ∘ σ.symm`. If it preserves an integral
lattice, the same assertion holds for the weight sublattices. No choice of weight basis is needed
for this transport.

In a weight basis, a lattice symmetry can consequently have a nonzero matrix entry only between
these corresponding weight components. This is the coordinate-support condition used to descend
numbered symmetries to the toral-closure group scheme. It allows an arbitrary integral change of
basis inside each weight component, rather than requiring a monomial action on the basis.

## Main results

* `isCartanWeightVector_equiv_iff`: transport of integral weights along a Cartan intertwiner.
* `map_weightSublattice_invariantRestrict`: the induced lattice automorphism maps each weight
  sublattice onto its permuted weight sublattice.
* `weight_eq_of_repr_invariantRestrict_ne_zero`: the coordinate-support condition for a weight
  basis, deduced from Cartan intertwining.

All declarations are in `TauCeti.UniversalEnvelopingAlgebra`.

## References

* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, §27.1.
* R. Steinberg, *Lectures on Chevalley Groups*, Chapter 2 (admissible lattices and weights).
-/

public section

namespace TauCeti.UniversalEnvelopingAlgebra

universe u v w

variable {L : Type u} [LieRing L] [LieAlgebra ℚ L] {κ : Type*}
variable {V : Type v} [AddCommGroup V] [Module ℚ V]
variable {W : Type w} [AddCommGroup W] [Module ℚ W]
variable (h : κ → L)
  (ρ : _root_.UniversalEnvelopingAlgebra ℚ L →ₐ[ℚ] Module.End ℚ V)

/-- A Cartan intertwiner transports an integral weight contragrediently. This is an equivalence
of weight-vector conditions, including the zero vector; it does not assert that the weight occurs.
-/
theorem isCartanWeightVector_equiv_iff
    (ρ' : _root_.UniversalEnvelopingAlgebra ℚ L →ₐ[ℚ] Module.End ℚ W)
    (θ : V ≃ₗ[ℚ] W) (σ : Equiv.Perm κ)
    (hθ : ∀ k v, θ (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (h k)) v) =
      ρ' (_root_.UniversalEnvelopingAlgebra.ι ℚ (h (σ k))) (θ v))
    (μ : κ → ℤ) (v : V) :
    IsCartanWeightVector h ρ' (μ ∘ σ.symm) (θ v) ↔ IsCartanWeightVector h ρ μ v := by
  have heig (k : κ) :
      θ v ∈ Module.End.eigenspace
          (ρ' (_root_.UniversalEnvelopingAlgebra.ι ℚ (h (σ k)))) (μ k : ℚ) ↔
        v ∈ Module.End.eigenspace
          (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (h k))) (μ k : ℚ) := by
    rw [TauCeti.eigenspace_eq_comap_of_intertwine (hθ k)]
    rfl
  simp only [isCartanWeightVector_iff_mem_eigenspace]
  constructor
  · intro hv k
    exact (heig k).1 (by simpa using hv (σ k))
  · intro hv k
    simpa using (heig (σ.symm k)).2 (hv (σ.symm k))

variable (M : AddSubgroup V) (θ : V ≃ₗ[ℚ] V)
  (hθM : ∀ v, θ v ∈ M ↔ v ∈ M) (σ : Equiv.Perm κ)
  (hθ : ∀ k v, θ (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (h k)) v) =
    ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (h (σ k))) (θ v))

include hθ

/-- The restriction of a Cartan symmetry to an invariant lattice carries each weight sublattice
onto the contragrediently permuted weight sublattice. Weight multiplicities are unrestricted. -/
theorem map_weightSublattice_invariantRestrict (μ : κ → ℤ) :
    (weightSublattice h ρ M μ).map
        (θ.toAddEquiv.invariantRestrict M hθM).toLinearMap =
      weightSublattice h ρ M (μ ∘ σ.symm) := by
  ext v
  rw [Submodule.mem_map_equiv]
  simp only [mem_weightSublattice_iff, AddEquiv.coe_invariantRestrict_symm_apply,
    LinearEquiv.coe_toAddEquiv]
  exact (isCartanWeightVector_equiv_iff h ρ ρ θ σ hθ μ
    (θ.symm (v : V))).symm.trans (by rw [θ.apply_symm_apply])

/-- A nonzero coordinate of a lattice symmetry in a weight basis joins the corresponding weight
components. This supplies the weight-compatibility hypothesis of
`TauCeti.UniversalEnvelopingAlgebra.kostantToralNumberedSymmetryIso` without assuming that the
symmetry acts monomially on the basis. -/
theorem weight_eq_of_repr_invariantRestrict_ne_zero
    {ι η : Type*} (e : ι → L)
    (hM : ∀ u ∈ kostantForm e h, ∀ v ∈ M, ρ u v ∈ M)
    (b : Module.Basis η ℤ M) (wt : η → κ → ℤ)
    (hwt : ∀ j, IsCartanWeightVector h ρ (wt j) (b j : V)) {i j : η}
    (hij : b.repr (θ.toAddEquiv.invariantRestrict M hθM (b j)) i ≠ 0) :
    ∀ k, wt i (σ k) = wt j k := by
  have hv : IsCartanWeightVector h ρ (wt j ∘ σ.symm)
      ((θ.toAddEquiv.invariantRestrict M hθM (b j) : M) : V) := by
    rw [AddEquiv.coe_invariantRestrict_apply]
    exact (isCartanWeightVector_equiv_iff h ρ ρ θ σ hθ (wt j) (b j : V)).2 (hwt j)
  have hw : wt i = wt j ∘ σ.symm := by
    by_contra hne
    exact hij (repr_eq_zero_of_isCartanWeightVector e h ρ M hM b wt hwt hv hne)
  intro k
  simpa using congr_fun hw (σ k)

end TauCeti.UniversalEnvelopingAlgebra

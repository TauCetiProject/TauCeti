/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.RootSubgroup.Torus.Basic
public import TauCeti.LinearAlgebra.End.IntegralExp
public import TauCeti.LinearAlgebra.End.Prod
public import Mathlib.LinearAlgebra.Basis.Prod

/-!
# Direct sums of Kostant-stable lattices

Two rational representations of the same Lie algebra combine by a binary direct sum, realized
as a product. The product of Kostant-stable lattices is stable, and the union of their integral
weight bases is a weight basis of the product. The root subgroup action after any scalar
extension is the componentwise action on the two summands.

These results allow a representation with the required weights to be added to a faithful
representation while retaining explicit integral root subgroup actions. The representation,
lattice, and basis use Mathlib's product constructions directly.
-/

public section

open TensorProduct

namespace TauCeti.UniversalEnvelopingAlgebra

variable {L V W : Type*} [LieRing L] [LieAlgebra ℚ L]
variable [AddCommGroup V] [Module ℚ V] [AddCommGroup W] [Module ℚ W]
variable {ι κ : Type*} (e : ι → L) (h : κ → L)
variable (ρ : _root_.UniversalEnvelopingAlgebra ℚ L →ₐ[ℚ] Module.End ℚ V)
variable (σ : _root_.UniversalEnvelopingAlgebra ℚ L →ₐ[ℚ] Module.End ℚ W)
variable (M : AddSubgroup V) (N : AddSubgroup W)

/-- The product of two Kostant-stable lattices is stable in the direct sum representation. -/
theorem _root_.UniversalEnvelopingAlgebra.kostantForm_apply_mem_prod
    (u : _root_.UniversalEnvelopingAlgebra ℚ L) (e : ι → L) (h : κ → L)
    (ρ : _root_.UniversalEnvelopingAlgebra ℚ L →ₐ[ℚ] Module.End ℚ V)
    (σ : _root_.UniversalEnvelopingAlgebra ℚ L →ₐ[ℚ] Module.End ℚ W)
    (M : AddSubgroup V) (N : AddSubgroup W)
    (hM : ∀ u ∈ kostantForm e h, ∀ v ∈ M, ρ u v ∈ M)
    (hN : ∀ u ∈ kostantForm e h, ∀ w ∈ N, σ u w ∈ N)
    (hu : u ∈ kostantForm e h)
    (v : V × W) (hv : v ∈ M.prod N) :
    ((LinearMap.prodMapAlgHom ℚ V W).comp (ρ.prod σ)) u v ∈ M.prod N :=
  ⟨hM u hu v.1 hv.1, hN u hu v.2 hv.2⟩

/-- A vector in the direct sum has a given Cartan weight exactly when both components have
that weight. Zero components are allowed. -/
@[simp]
theorem isCartanWeightVector_prod_iff (μ : κ → ℤ) (v : V × W) :
    IsCartanWeightVector h ((LinearMap.prodMapAlgHom ℚ V W).comp (ρ.prod σ)) μ v ↔
      IsCartanWeightVector h ρ μ v.1 ∧ IsCartanWeightVector h σ μ v.2 := by
  rcases v with ⟨v, w⟩
  simp only [isCartanWeightVector_iff, AlgHom.comp_apply, AlgHom.prod_apply,
    LinearMap.prodMapAlgHom_apply_apply, Prod.smul_mk, Prod.ext_iff,
    forall_and]

/-- The disjoint union of two integral weight bases is a weight basis of the product lattice. -/
theorem isCartanWeightVector_prod_basis {η θ : Type*}
    (b : Module.Basis η ℤ M) (c : Module.Basis θ ℤ N)
    (wt : η → κ → ℤ) (wt' : θ → κ → ℤ)
    (hb : ∀ i, IsCartanWeightVector h ρ (wt i) (b i : V))
    (hc : ∀ j, IsCartanWeightVector h σ (wt' j) (c j : W)) (i : η ⊕ θ) :
    IsCartanWeightVector h ((LinearMap.prodMapAlgHom ℚ V W).comp (ρ.prod σ))
      (Sum.elim wt wt' i)
      (((b.prod c).map (M.prodEquiv N).toIntLinearEquiv.symm i : M.prod N) : V × W) := by
  -- Compute the carrier of the subgroup equivalence explicitly: its coercion API does not
  -- otherwise reduce the transported product basis to the two summands.
  have hcoe (p : M × N) :
      (((M.prodEquiv N).symm p : M.prod N) : V × W) =
        ((p.1 : V), (p.2 : W)) := rfl
  rw [Module.Basis.map_apply, AddEquiv.coe_symm_toIntLinearEquiv, hcoe,
    isCartanWeightVector_prod_iff]
  cases i with
  | inl i =>
      simpa using And.intro (hb i) (IsCartanWeightVector.zero (h := h) (ρ := σ) (wt i))
  | inr i =>
      simpa using And.intro (IsCartanWeightVector.zero (h := h) (ρ := ρ) (wt' i)) (hc i)

-- Keep scalar extensions compatible with the supplied integer algebra structure.
attribute [local instance high] Algebra.toModule

/-- Root subgroup actions on the product lattice agree with the actions on the two summands,
after extension to any commutative coefficient ring. -/
@[simp]
theorem prodRight_baseChangeKostantExpHom
    {R : Type*} [CommRing R] [Algebra ℤ R]
    (hM : ∀ u ∈ kostantForm e h, ∀ v ∈ M, ρ u v ∈ M)
    (hN : ∀ u ∈ kostantForm e h, ∀ w ∈ N, σ u w ∈ N) (i : ι)
    (hρ : IsNilpotent (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e i))))
    (hσ : IsNilpotent (σ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e i))))
    (t : Multiplicative R) (z : R ⊗[ℤ] M.prod N) :
    let E := fun z => TensorProduct.prodRight ℤ R R M N
      (((M.prodEquiv N).toIntLinearEquiv.baseChange ℤ R _ _) z)
    E (baseChangeKostantExpHom e h
      ((LinearMap.prodMapAlgHom ℚ V W).comp (ρ.prod σ)) (M.prod N)
      (fun u => u.kostantForm_apply_mem_prod e h ρ σ M N hM hN)
      i (hρ.prodMap hσ) t z) =
      (baseChangeKostantExpHom e h ρ M hM i hρ t (E z).1,
        baseChangeKostantExpHom e h σ N hN i hσ t (E z).2) := by
  dsimp only
  rw [coe_baseChangeKostantExpHom e h
    ((LinearMap.prodMapAlgHom ℚ V W).comp (ρ.prod σ)) (M.prod N)
    (fun u => u.kostantForm_apply_mem_prod e h ρ σ M N hM hN)
    i (hρ.prodMap hσ) t]
  simp only [coe_baseChangeKostantExpHom]
  exact Module.End.prodRight_baseChangeExp _ _ M N _ _ hρ hσ _ z

end TauCeti.UniversalEnvelopingAlgebra

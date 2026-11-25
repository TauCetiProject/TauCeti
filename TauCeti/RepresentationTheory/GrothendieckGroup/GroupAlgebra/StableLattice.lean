/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Module.Lattice
public import TauCeti.LinearAlgebra.TensorProduct.Quotient
public import TauCeti.RepresentationTheory.GrothendieckGroup.GroupAlgebra.Reduction
public import TauCeti.RepresentationTheory.Lattice
-- Non-public: `IsSMulRegular.submodule` and `Subrepresentation.toSubmodule_le_toSubmodule` are
-- used only in proofs.
import Mathlib.RingTheory.Regular.IsSMulRegular
import TauCeti.RepresentationTheory.Subrepresentation

/-!
# Reductions of stable lattices

Let `O` be a discrete valuation ring with fraction field `K` and residue field `k`, and `G` a
monoid. The **reduction** of a `G`-stable `O`-lattice `L` is the representation `k ⊗_O L` of `G`
over `k`, with class `TauCeti.reductionK0 k` in the Grothendieck group `G₀(k[G])` of finitely
generated `k[G]`-modules.

Different lattices can have non-isomorphic reductions, but the class of the reduction does not
depend on the lattice
(`TauCeti.reductionK0_residueField_eq_of_nonempty_equiv_baseChange`): two `G`-stable lattices,
finitely generated and torsion-free over `O`, whose scalar extensions to `K` are equivalent have
reductions with the same class. For two full lattices in the same representation `ρ` over `K`
this is `TauCeti.reductionK0_residueField_eq_of_isFullLattice`; such lattices exist when `G` is
finite (`TauCeti.exists_isFullLattice_subrepresentation`). This is what makes the reduction of
lattices a well-defined map from representations over `K` to `G₀(k[G])`, the decomposition map of
modular representation theory.

The argument is Serre's. Clearing denominators in an equivalence `K ⊗_O L₁ ≃ K ⊗_O L₂`
(`Representation.Equiv.exists_intertwiningMap_comp_eq_smul`) embeds `L₁` in `L₂` with image
containing `ϖⁿ L₂`, for a uniformizer `ϖ`. Between `L₁` and `L₂` lies the chain of `G`-stable
lattices `L₁ + ϖⁱ L₂`, each containing `ϖ` times the next one
(`TauCeti.reductionK0_eq_of_pow_smul_le`). For a single step `ϖ T ≤ P ≤ T`, the inclusion
`a : P → T` and multiplication by `ϖ`, `b : T → P`, compose in both orders to `ϖ`. Their
reductions modulo `ϖ` therefore form a periodic exact sequence
`k ⊗ P → k ⊗ T → k ⊗ P → k ⊗ T` (`LinearMap.exact_lTensor_of_ker_eq_span_singleton`), so each of
`[k ⊗ P]` and `[k ⊗ T]` is the sum of the classes of the images of the two reduced maps
(`TauCeti.reductionK0_eq_of_comp_eq_smul`).

For `O = ℤ` (not a discrete valuation ring) the same independence is
`TauCeti.reductionK0_eq_of_nonempty_equiv_baseChange_rat`, proved through the lattice defect. For
continuous representations over a field with a valuative topology, stable lattices are the
integral models `TauCeti.GaloisLattice.IntegralModel`; the lattices here carry no topology, and
`K` is the fraction field of an arbitrary discrete valuation ring, with no completeness needed.

## Main results

* `TauCeti.reductionK0_eq_of_comp_eq_smul`: intertwining maps composing in both orders to a
  regular scalar `r` give reductions modulo `r` with the same class.
* `TauCeti.reductionK0_eq_of_pow_smul_le`: two `G`-stable submodules `P ≤ Q` with `rⁿ Q ≤ P` have
  reductions with the same class.
* `TauCeti.reductionK0_residueField_eq_of_nonempty_equiv_baseChange`: over a discrete valuation
  ring, lattices with equivalent scalar extensions to the fraction field have reductions to the
  residue field with the same class.
* `TauCeti.reductionK0_residueField_eq_of_isFullLattice`: two `G`-stable full lattices in the
  same representation have reductions with the same class.

## References

* J.-P. Serre, *Linear Representations of Finite Groups*, Graduate Texts in Mathematics 42,
  Springer (1977), Part III, §15.2.
* P. Webb, *A Course in Finite Group Representation Theory*, Cambridge University Press (2016),
  Theorem 9.4.8.
-/

public section

open TensorProduct

namespace TauCeti

open scoped MonoidAlgebra Pointwise
open _root_.Representation (IntertwiningMap)

universe u

variable {O G : Type u} [CommRing O] [Monoid G]
  {M N : Type u} [AddCommGroup M] [Module O M] [AddCommGroup N] [Module O N]
  {ρ : Representation O G M} {σ : Representation O G N}

/-! ### Reductions of representations over a commutative ring -/

section Reduction

variable {k : Type u} [CommRing k] [Algebra O k]

/-- **Reductions along a factorization of a scalar.** Let `a : ρ → σ` and `b : σ → ρ` be
intertwining maps composing in both orders to multiplication by `r`, with `r` regular on `M` and
on `N`, and let `k` be an `O`-algebra whose structure map is surjective with kernel `(r)`. Then
the reductions `k ⊗_O M` and `k ⊗_O N` have the same class in `G₀(k[G])`, although they need not
be isomorphic. -/
theorem reductionK0_eq_of_comp_eq_smul {r : O} (hk : Function.Surjective (algebraMap O k))
    (hker : RingHom.ker (algebraMap O k) = Ideal.span {r}) [Module.Finite k (k ⊗[O] M)]
    [Module.Finite k (k ⊗[O] N)] (a : IntertwiningMap ρ σ) (b : IntertwiningMap σ ρ)
    (hab : ∀ w, a (b w) = r • w) (hba : ∀ v, b (a v) = r • v) (hM : IsSMulRegular M r)
    (hN : IsSMulRegular N r) :
    reductionK0 k ρ = reductionK0 k σ := by
  have hab' : a.toLinearMap ∘ₗ b.toLinearMap = r • LinearMap.id := LinearMap.ext hab
  have hba' : b.toLinearMap ∘ₗ a.toLinearMap = r • LinearMap.id := LinearMap.ext hba
  let A := IntertwiningMap.equivLinearMapAsModule _ _ (a.baseChange k)
  let B := IntertwiningMap.equivLinearMapAsModule _ _ (b.baseChange k)
  have hBA : Function.Exact B A := by
    rw [IntertwiningMap.coe_equivLinearMapAsModule_baseChange,
      IntertwiningMap.coe_equivLinearMapAsModule_baseChange]
    exact LinearMap.exact_lTensor_of_ker_eq_span_singleton hk hker _ _ hab' hba' hM
  have hAB : Function.Exact A B := by
    rw [IntertwiningMap.coe_equivLinearMapAsModule_baseChange,
      IntertwiningMap.coe_equivLinearMapAsModule_baseChange]
    exact LinearMap.exact_lTensor_of_ker_eq_span_singleton hk hker _ _ hba' hab' hN
  -- Each class is the sum of the classes of the images of `k ⊗ a` and `k ⊗ b`.
  -- The module types are given explicitly: the instances of `Representation.asModule` used by
  -- `equivLinearMapAsModule` differ syntactically from those `FGModuleCat.of` asks for.
  rw [reductionK0_def, reductionK0_def,
    exactK0_of_eq_range_add_range (M := (σ.baseChange k).asModule)
      (N := (ρ.baseChange k).asModule) (P := (σ.baseChange k).asModule) _ hBA,
    exactK0_of_eq_range_add_range (M := (ρ.baseChange k).asModule)
      (N := (σ.baseChange k).asModule) (P := (ρ.baseChange k).asModule) _ hAB, add_comm]

variable (k)

/-- **Reductions of nested stable submodules.** Let `r` be regular on `N` and `k` an `O`-algebra
whose structure map is surjective with kernel `(r)`. For `G`-stable submodules `P ≤ Q` of `N`
with `rⁿ Q ≤ P`, the reductions `k ⊗_O P` and `k ⊗_O Q` have the same class in `G₀(k[G])`. -/
theorem reductionK0_eq_of_pow_smul_le [IsNoetherianRing O] [Module.Finite O N] {r : O}
    (hk : Function.Surjective (algebraMap O k))
    (hker : RingHom.ker (algebraMap O k) = Ideal.span {r}) (hN : IsSMulRegular N r) (n : ℕ) :
    ∀ {P Q : Subrepresentation σ}, P ≤ Q → r ^ n • Q.toSubmodule ≤ P.toSubmodule →
      reductionK0 k P.toRepresentation = reductionK0 k Q.toRepresentation := by
  -- Induction on `n`: the submodule `P + rⁿ⁻¹ Q` is one step from `P` and `n - 1` steps from `Q`.
  induction n with
  | zero =>
    intro P Q hPQ hQP
    rw [pow_zero, one_smul, Subrepresentation.toSubmodule_le_toSubmodule] at hQP
    obtain rfl : P = Q := le_antisymm hPQ hQP
    rfl
  | succ n ih =>
    intro P Q hPQ hQP
    -- `rⁿ Q` is a subrepresentation, and so is `T = P + rⁿ Q`, with `r T ≤ P` and `rⁿ Q ≤ T`.
    let S : Subrepresentation σ :=
      ⟨r ^ n • Q.toSubmodule, fun g v hv ↦ by
        obtain ⟨w, hw, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).mp hv
        rw [map_smul]
        exact Submodule.smul_mem_pointwise_smul _ _ _ (Q.apply_mem_toSubmodule g hw)⟩
    let T := P ⊔ S
    have hrT : r • T.toSubmodule ≤ P.toSubmodule := by
      rw [Subrepresentation.toSubmodule_sup, Submodule.smul_sup', smul_smul, ← pow_succ']
      exact sup_le (Submodule.smul_le_self_of_tower _ _) hQP
    have hTQ : T ≤ Q := sup_le hPQ <|
      Subrepresentation.toSubmodule_le_toSubmodule.mp (Submodule.smul_le_self_of_tower _ _)
    have hPT : P.toSubmodule ≤ T.toSubmodule :=
      Subrepresentation.toSubmodule_le_toSubmodule.mpr le_sup_left
    -- The inclusion `P → T` and multiplication by `r` from `T` to `P` compose to `r`.
    let a : IntertwiningMap P.toRepresentation T.toRepresentation :=
      ⟨Submodule.inclusion hPT, fun g ↦ rfl⟩
    let b : IntertwiningMap T.toRepresentation P.toRepresentation :=
      ⟨(r • T.toSubmodule.subtype).codRestrict P.toSubmodule fun v ↦
        hrT (Submodule.smul_mem_pointwise_smul _ _ _ v.property), fun g ↦ by
        ext v
        exact (map_smul (σ g) r (v : N)).symm⟩
    have hab (w : T.toSubmodule) : a (b w) = r • w := Subtype.ext <| by
      simp [a, b, ← IntertwiningMap.toLinearMap_apply]
    have hba (v : P.toSubmodule) : b (a v) = r • v := Subtype.ext <| by
      simp [a, b, ← IntertwiningMap.toLinearMap_apply]
    exact (reductionK0_eq_of_comp_eq_smul hk hker a b hab hba
      (IsSMulRegular.submodule P.toSubmodule r hN)
      (IsSMulRegular.submodule T.toSubmodule r hN)).trans (ih hTQ le_sup_right)

end Reduction

/-! ### Lattices over a discrete valuation ring -/

/-- **The reduction of a stable lattice is well defined in `G₀(k[G])`.** Let `O` be a discrete
valuation ring with fraction field `K` and residue field `k`, and let `ρ` and `σ` be
representations of `G` on finitely generated torsion-free `O`-modules, for instance `G`-stable
lattices, whose scalar extensions to `K` are equivalent. Then the reductions `k ⊗_O M` and
`k ⊗_O N` have the same class in `G₀(k[G])`. They need not be isomorphic. -/
theorem reductionK0_residueField_eq_of_nonempty_equiv_baseChange [IsDomain O]
    [IsDiscreteValuationRing O] (K : Type*) [Field K] [Algebra O K] [IsFractionRing O K]
    [Module.Finite O M] [Module.IsTorsionFree O M] [Module.Finite O N] [Module.IsTorsionFree O N]
    (h : Nonempty ((ρ.baseChange K).Equiv (σ.baseChange K))) :
    reductionK0 (IsLocalRing.ResidueField O) ρ = reductionK0 (IsLocalRing.ResidueField O) σ := by
  obtain ⟨e⟩ := h
  -- Clear denominators: `f' ∘ f` and `f ∘ f'` are multiplication by some `s ≠ 0`.
  obtain ⟨f, f', s, hf'f, hff'⟩ := e.exists_intertwiningMap_comp_eq_smul (nonZeroDivisors O)
    (fun s ↦ .of_ne_zero (nonZeroDivisors.coe_ne_zero s))
    (fun s ↦ .of_ne_zero (nonZeroDivisors.coe_ne_zero s))
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  obtain ⟨n, u, hs⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible
    (nonZeroDivisors.coe_ne_zero s) hϖ
  have hker : RingHom.ker (algebraMap O (IsLocalRing.ResidueField O)) = Ideal.span {ϖ} :=
    IsLocalRing.ker_residue.trans hϖ.maximalIdeal_eq
  have hf : Function.Injective f := fun v w hvw ↦
    IsSMulRegular.of_ne_zero (M := M) (nonZeroDivisors.coe_ne_zero s) <| by
      simp only [← hf'f, hvw]
  -- The image of `f` contains `ϖⁿ N`, so it is joined to `N` by a chain of lattices.
  have hle : ϖ ^ n • (⊤ : Subrepresentation σ).toSubmodule ≤ f.range.toSubmodule := by
    intro w hw
    obtain ⟨x, -, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).mp hw
    refine ⟨f' ((u⁻¹ : Oˣ) • x), ?_⟩
    simp [hff', hs, mul_comm (u : O), mul_smul, ← Units.smul_def]
  let k := IsLocalRing.ResidueField O
  let eρ : ρ.Equiv f.range.toRepresentation :=
    .mk (LinearEquiv.ofInjective f.toLinearMap hf) fun g ↦ by
      ext v
      exact f.isIntertwining _ _ g v
  let eσ : (⊤ : Subrepresentation σ).toRepresentation.Equiv σ :=
    .mk Submodule.topEquiv fun g ↦ rfl
  exact (reductionK0_congr k eρ).trans <|
    (reductionK0_eq_of_pow_smul_le k IsLocalRing.residue_surjective hker
      (.of_ne_zero hϖ.ne_zero) n le_top hle).trans (reductionK0_congr k eσ)

variable {K : Type*} [Field K] [Algebra O K] [IsFractionRing O K] [IsDomain O]

/-- **Stable full lattices in one representation have reductions with the same class.** Let
`O` be a discrete valuation ring with fraction field `K` and residue field `k`, and `L₁`, `L₂`
two `G`-stable full `O`-lattices in a representation `ρ` over `K`. Then `[k ⊗_O L₁]` and
`[k ⊗_O L₂]` agree in `G₀(k[G])`. -/
theorem reductionK0_residueField_eq_of_isFullLattice [IsDiscreteValuationRing O]
    {V : Type u} [AddCommGroup V] [Module K V] [Module O V] [IsScalarTower O K V]
    {ρ : Representation K G V} (L₁ L₂ : Subrepresentation (ρ.restrictScalars O))
    [L₁.toSubmodule.IsFullLattice K] [L₂.toSubmodule.IsFullLattice K] :
    letI := Submodule.IsLattice.finite K L₁.toSubmodule
    letI := Submodule.IsLattice.finite K L₂.toSubmodule
    reductionK0 (IsLocalRing.ResidueField O) L₁.toRepresentation =
      reductionK0 (IsLocalRing.ResidueField O) L₂.toRepresentation :=
  letI := Submodule.IsLattice.finite K L₁.toSubmodule
  letI := Submodule.IsLattice.finite K L₂.toSubmodule
  haveI := Submodule.IsLattice.free K L₁.toSubmodule
  haveI := Submodule.IsLattice.free K L₂.toSubmodule
  haveI := Module.IsTorsionFree.trans_faithfulSMul O K V
  reductionK0_residueField_eq_of_nonempty_equiv_baseChange K
    ⟨L₁.rationalizationEquiv.trans L₂.rationalizationEquiv.symm⟩

end TauCeti

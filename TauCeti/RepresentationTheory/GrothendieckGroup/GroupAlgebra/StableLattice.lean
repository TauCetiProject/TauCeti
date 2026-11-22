/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RepresentationTheory.Subrepresentation
public import TauCeti.Algebra.Category.ModuleCat.CartanMap.Basic
public import TauCeti.Algebra.Module.Lattice
public import TauCeti.LinearAlgebra.TensorProduct.Quotient
public import TauCeti.RepresentationTheory.AsModule
public import TauCeti.RepresentationTheory.BaseChange
public import TauCeti.RepresentationTheory.Lattice
public import TauCeti.RepresentationTheory.RestrictScalars

/-!
# Stable lattices and their reductions

Let `O` be a discrete valuation ring with fraction field `K` and residue field `k`, and `G` a
monoid. A finite-dimensional representation `ρ` of `G` over `K` contains a `G`-stable full
`O`-lattice when `G` is finite: the `O`-span of the translates of a `K`-basis
(`TauCeti.exists_isFullLattice_subrepresentation`). A `G`-stable free full lattice `L` recovers
`ρ` by scalar extension, `K ⊗_O L ≃ ρ` (`Subrepresentation.rationalizationEquiv`, the equivariant
form of `Submodule.rationalizationEquiv`). Its **reduction** is the representation
`k ⊗_O L` of `G` over `k`.

Different lattices can have non-isomorphic reductions, but the class of the reduction in the
Grothendieck group `G₀(k[G])` of finitely generated `k[G]`-modules does not depend on the lattice
(`TauCeti.exactK0_baseChange_residueField_eq_of_nonempty_equiv_baseChange`): two `G`-stable
lattices, finitely generated and torsion-free over `O`, whose scalar extensions to `K` are
equivalent have reductions with the same class. For two full lattices in the same `ρ` this is
`TauCeti.exactK0_baseChange_residueField_eq_of_isFullLattice`. This is what makes the reduction
of lattices a well-defined map from representations over `K` to `G₀(k[G])`, the decomposition
map of modular representation theory.

The argument is Serre's. Clearing denominators in an equivalence `K ⊗_O L₁ ≃ K ⊗_O L₂`
(`Representation.Equiv.exists_intertwiningMap_comp_eq_smul`) embeds `L₁` in `L₂` with image
containing `ϖⁿ L₂`, for a uniformizer `ϖ`. Between `L₁` and `L₂` lies the chain of `G`-stable
lattices `L₁ + ϖⁱ L₂`, each containing `ϖ` times the previous one
(`TauCeti.exactK0_baseChange_eq_of_pow_smul_le`). For a single step `ϖ P ≤ T`, `P ≤ T`, the
inclusion `a : P → T` and multiplication by `ϖ`, `b : T → P`, compose in both orders to `ϖ`. Their
reductions modulo `ϖ` therefore form a periodic exact sequence
`k ⊗ P → k ⊗ T → k ⊗ P → k ⊗ T` (`LinearMap.exact_lTensor_of_ker_eq_span_singleton`), so each of
`[k ⊗ P]` and `[k ⊗ T]` is the sum of the classes of the images of the two reduced maps
(`TauCeti.exactK0_baseChange_eq_of_comp_eq_smul`).

For `O = ℤ` (not a discrete valuation ring) the same independence is
`TauCeti.reductionK0_eq_of_nonempty_equiv_baseChange_rat`, proved through the lattice defect. For
continuous representations over a field with a valuative topology, stable lattices are the
integral models `TauCeti.GaloisLattice.IntegralModel`; the lattices here carry no topology, and
`K` is the fraction field of an arbitrary domain.

## Main results

* `LinearMap.exact_lTensor_of_ker_eq_span_singleton`: maps `a`, `b` composing in both orders to
  a regular scalar `r` give an exact pair after scalar extension to any quotient of the base ring
  by `(r)`.
* `TauCeti.exactK0_baseChange_eq_of_comp_eq_smul`: such intertwining maps give reductions with
  the same class.
* `TauCeti.exactK0_baseChange_eq_of_pow_smul_le`: two `G`-stable submodules `P ≤ Q` with
  `rⁿ Q ≤ P` have reductions with the same class.
* `TauCeti.exactK0_baseChange_residueField_eq_of_nonempty_equiv_baseChange`: over a discrete
  valuation ring, lattices with equivalent scalar extensions to the fraction field have
  reductions to the residue field with the same class.
* `TauCeti.exists_isFullLattice_subrepresentation`: a finite-dimensional representation of a
  finite group over the fraction field contains a `G`-stable full lattice.
* `Subrepresentation.rationalizationEquiv`: a `G`-stable free full lattice `L` satisfies
  `K ⊗_O L ≃ ρ` as representations.
* `TauCeti.exactK0_baseChange_residueField_eq_of_isFullLattice`: two `G`-stable full lattices in
  the same representation have reductions with the same class.

## References

* J.-P. Serre, *Linear Representations of Finite Groups*, Graduate Texts in Mathematics 42,
  Springer (1977), Part III, §15.2.
* P. Webb, *A Course in Finite Group Representation Theory*, Cambridge University Press (2016),
  Theorem 9.4.8.
-/

public section

open TensorProduct

namespace LinearMap

/-- **Reductions of a factorization of a regular scalar are exact.** Let `a : M → N` and
`b : N → M` compose in both orders to multiplication by `r`, with `r` regular on `M`, and let `S`
be an `R`-algebra whose structure map is surjective with kernel `(r)`. Then `S ⊗ b` and `S ⊗ a`
form an exact pair. This generalizes `LinearMap.exact_lTensor_quotient_span_singleton`, the case
`S = R ⧸ (r)`, to the residue field of a discrete valuation ring and a uniformizer, for
instance. -/
theorem exact_lTensor_of_ker_eq_span_singleton {R M N S : Type*} [CommRing R] [AddCommGroup M]
    [Module R M] [AddCommGroup N] [Module R N] [CommRing S] [Algebra R S] {r : R}
    (hS : Function.Surjective (algebraMap R S))
    (hker : RingHom.ker (algebraMap R S) = Ideal.span {r}) (a : M →ₗ[R] N) (b : N →ₗ[R] M)
    (hab : a ∘ₗ b = r • id) (hba : b ∘ₗ a = r • id) (hr : IsSMulRegular M r) :
    Function.Exact (b.lTensor S) (a.lTensor S) := by
  let e : (R ⧸ Ideal.span {r}) ≃ₗ[R] S :=
    ((Ideal.quotientEquivAlgOfEq R hker).symm.trans
      (Ideal.quotientKerAlgEquivOfSurjective (f := Algebra.ofId R S) hS)).toLinearEquiv
  refine (Function.Exact.iff_of_ladder_linearEquiv (e₁ := e.rTensor N) (e₂ := e.rTensor M)
    (e₃ := e.rTensor N) ?_ ?_).mpr (exact_lTensor_quotient_span_singleton a b hab hba hr) <;>
  · rw [LinearEquiv.coe_rTensor, LinearEquiv.coe_rTensor, lTensor_comp_rTensor,
      rTensor_comp_lTensor]

end LinearMap

namespace TauCeti

open scoped MonoidAlgebra Pointwise
open _root_.Representation (IntertwiningMap)

universe u

variable {O G : Type u} [CommRing O] [Monoid G]
  {M N : Type u} [AddCommGroup M] [Module O M] [AddCommGroup N] [Module O N]
  {ρ : Representation O G M} {σ : Representation O G N}

/-! ### Reductions of representations over a commutative ring -/

section Reduction

variable (k : Type u) [CommRing k] [Algebra O k]

/-- **Equivalent representations have reductions with the same class**: an equivalence `ρ ≃ σ`
over `O` gives `[k ⊗_O M] = [k ⊗_O N]` in `G₀(k[G])`. -/
theorem exactK0_baseChange_congr [Module.Finite k (k ⊗[O] M)] [Module.Finite k (k ⊗[O] N)]
    (e : ρ.Equiv σ) :
    letI := Module.Finite.of_restrictScalars_finite k k[G] (ρ.baseChange k).asModule
    letI := Module.Finite.of_restrictScalars_finite k k[G] (σ.baseChange k).asModule
    (ExactK0.of (FGModuleCat.of k[G] (ρ.baseChange k).asModule) :
        ExactK0 (finiteModulesExactStructure k[G])) =
      ExactK0.of (FGModuleCat.of k[G] (σ.baseChange k).asModule) :=
  letI := Module.Finite.of_restrictScalars_finite k k[G] (ρ.baseChange k).asModule
  letI := Module.Finite.of_restrictScalars_finite k k[G] (σ.baseChange k).asModule
  ExactK0.of_congr (Representation.asModuleLinearEquivOfEquiv (e.baseChange k)).toFGModuleCatIso

variable {k}

/-- **Reductions along a factorization of a scalar.** Let `a : ρ → σ` and `b : σ → ρ` be
intertwining maps composing in both orders to multiplication by `r`, with `r` regular on `M` and
on `N`, and let `k` be an `O`-algebra whose structure map is surjective with kernel `(r)`. Then
the reductions `k ⊗_O M` and `k ⊗_O N` have the same class in `G₀(k[G])`, although they need not
be isomorphic. -/
theorem exactK0_baseChange_eq_of_comp_eq_smul {r : O} (hk : Function.Surjective (algebraMap O k))
    (hker : RingHom.ker (algebraMap O k) = Ideal.span {r}) [Module.Finite k (k ⊗[O] M)]
    [Module.Finite k (k ⊗[O] N)] (a : IntertwiningMap ρ σ) (b : IntertwiningMap σ ρ)
    (hab : ∀ w, a (b w) = r • w) (hba : ∀ v, b (a v) = r • v) (hM : IsSMulRegular M r)
    (hN : IsSMulRegular N r) :
    letI := Module.Finite.of_restrictScalars_finite k k[G] (ρ.baseChange k).asModule
    letI := Module.Finite.of_restrictScalars_finite k k[G] (σ.baseChange k).asModule
    (ExactK0.of (FGModuleCat.of k[G] (ρ.baseChange k).asModule) :
        ExactK0 (finiteModulesExactStructure k[G])) =
      ExactK0.of (FGModuleCat.of k[G] (σ.baseChange k).asModule) := by
  let := Module.Finite.of_restrictScalars_finite k k[G] (ρ.baseChange k).asModule
  let := Module.Finite.of_restrictScalars_finite k k[G] (σ.baseChange k).asModule
  have hab' : a.toLinearMap ∘ₗ b.toLinearMap = r • LinearMap.id := LinearMap.ext hab
  have hba' : b.toLinearMap ∘ₗ a.toLinearMap = r • LinearMap.id := LinearMap.ext hba
  let A := IntertwiningMap.equivLinearMapAsModule _ _ (a.baseChange k)
  let B := IntertwiningMap.equivLinearMapAsModule _ _ (b.baseChange k)
  -- `equivLinearMapAsModule` keeps the underlying function, that of `k ⊗ a` and `k ⊗ b`.
  have hA : ⇑A = a.toLinearMap.lTensor k := by
    have h : ⇑A = ⇑(a.baseChange k).toLinearMap := rfl
    rw [h, IntertwiningMap.toLinearMap_baseChange, LinearMap.baseChange_eq_lTensor]
  have hB : ⇑B = b.toLinearMap.lTensor k := by
    have h : ⇑B = ⇑(b.baseChange k).toLinearMap := rfl
    rw [h, IntertwiningMap.toLinearMap_baseChange, LinearMap.baseChange_eq_lTensor]
  have hBA : Function.Exact B A := by
    rw [hA, hB]
    exact LinearMap.exact_lTensor_of_ker_eq_span_singleton hk hker _ _ hab' hba' hM
  have hAB : Function.Exact A B := by
    rw [hA, hB]
    exact LinearMap.exact_lTensor_of_ker_eq_span_singleton hk hker _ _ hba' hab' hN
  -- Each class is the sum of the classes of the images of `k ⊗ a` and `k ⊗ b`.
  -- The module types are given explicitly: the instances of `Representation.asModule` used by
  -- `equivLinearMapAsModule` differ syntactically from those `FGModuleCat.of` asks for.
  rw [exactK0_of_eq_range_add_range (M := (σ.baseChange k).asModule)
      (N := (ρ.baseChange k).asModule) (P := (σ.baseChange k).asModule) _ hBA,
    exactK0_of_eq_range_add_range (M := (ρ.baseChange k).asModule)
      (N := (σ.baseChange k).asModule) (P := (ρ.baseChange k).asModule) _ hAB, add_comm]

variable (k)

/-- **Reductions of nested stable submodules.** Let `r` be regular on `N` and `k` an `O`-algebra
whose structure map is surjective with kernel `(r)`. For `G`-stable submodules `P ≤ Q` of `N`
with `rⁿ Q ≤ P`, the reductions `k ⊗_O P` and `k ⊗_O Q` have the same class in `G₀(k[G])`. -/
theorem exactK0_baseChange_eq_of_pow_smul_le [IsNoetherianRing O] [Module.Finite O N] {r : O}
    (hk : Function.Surjective (algebraMap O k))
    (hker : RingHom.ker (algebraMap O k) = Ideal.span {r}) (hN : IsSMulRegular N r) (n : ℕ) :
    ∀ {P Q : Subrepresentation σ}, P ≤ Q → r ^ n • Q.toSubmodule ≤ P.toSubmodule →
    letI := Module.Finite.of_restrictScalars_finite k k[G]
      (P.toRepresentation.baseChange k).asModule
    letI := Module.Finite.of_restrictScalars_finite k k[G]
      (Q.toRepresentation.baseChange k).asModule
    (ExactK0.of (FGModuleCat.of k[G] (P.toRepresentation.baseChange k).asModule) :
        ExactK0 (finiteModulesExactStructure k[G])) =
      ExactK0.of (FGModuleCat.of k[G] (Q.toRepresentation.baseChange k).asModule) := by
  -- Induction on `n`: the submodule `P + rⁿ⁻¹ Q` is one step from `P` and `n - 1` steps from `Q`.
  have hreg (P : Subrepresentation σ) : IsSMulRegular P.toSubmodule r :=
    fun x y hxy ↦ Subtype.ext (hN (congrArg Subtype.val hxy))
  induction n with
  | zero =>
    intro P Q hPQ hQP
    rw [pow_zero, one_smul] at hQP
    obtain rfl : P = Q := le_antisymm hPQ hQP
    rfl
  | succ n ih =>
    intro P Q hPQ hQP
    -- The intermediate representation `T = P + rⁿ Q` has `r T ≤ P` and `rⁿ Q ≤ T`.
    let T : Subrepresentation σ :=
      ⟨P.toSubmodule ⊔ r ^ n • Q.toSubmodule, fun g v hv ↦ by
        obtain ⟨p, hp, q, hq, rfl⟩ := Submodule.mem_sup.mp hv
        obtain ⟨w, hw, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).mp hq
        rw [map_add, map_smul]
        exact Submodule.add_mem_sup (P.apply_mem_toSubmodule g hp)
          (Submodule.smul_mem_pointwise_smul _ _ _ (Q.apply_mem_toSubmodule g hw))⟩
    have hPT : P.toSubmodule ≤ T.toSubmodule := le_sup_left
    have hrT : ∀ v ∈ T.toSubmodule, r • v ∈ P.toSubmodule := fun v hv ↦ by
      obtain ⟨p, hp, q, hq, rfl⟩ := Submodule.mem_sup.mp hv
      obtain ⟨w, hw, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).mp hq
      rw [smul_add, smul_smul, ← pow_succ']
      exact P.toSubmodule.add_mem (P.toSubmodule.smul_mem r hp)
        (hQP (Submodule.smul_mem_pointwise_smul _ _ _ hw))
    have hTQ : T ≤ Q := fun v hv ↦ by
      obtain ⟨p, hp, q, hq, rfl⟩ := Submodule.mem_sup.mp hv
      exact Q.toSubmodule.add_mem (hPQ hp) (Submodule.smul_le_self_of_tower _ _ hq)
    -- The inclusion `P → T` and multiplication by `r` from `T` to `P` compose to `r`.
    let a : IntertwiningMap P.toRepresentation T.toRepresentation :=
      ⟨Submodule.inclusion hPT, fun g ↦ rfl⟩
    let b : IntertwiningMap T.toRepresentation P.toRepresentation :=
      ⟨(r • T.toSubmodule.subtype).codRestrict P.toSubmodule fun v ↦ hrT _ v.property, fun g ↦ by
        ext v
        exact (map_smul (σ g) r (v : N)).symm⟩
    exact (exactK0_baseChange_eq_of_comp_eq_smul hk hker a b (fun _ ↦ rfl) (fun _ ↦ rfl)
      (hreg P) (hreg T)).trans (ih hTQ le_sup_right)

end Reduction

/-! ### Lattices over a discrete valuation ring -/

/-- **The reduction of a stable lattice is well defined in `G₀(k[G])`.** Let `O` be a discrete
valuation ring with fraction field `K` and residue field `k`, and let `ρ` and `σ` be
representations of `G` on finitely generated torsion-free `O`-modules, for instance `G`-stable
lattices, whose scalar extensions to `K` are equivalent. Then the reductions `k ⊗_O M` and
`k ⊗_O N` have the same class in `G₀(k[G])`. They need not be isomorphic. -/
theorem exactK0_baseChange_residueField_eq_of_nonempty_equiv_baseChange [IsDomain O]
    [IsDiscreteValuationRing O] (K : Type*) [Field K] [Algebra O K] [IsFractionRing O K]
    [Module.Finite O M] [Module.IsTorsionFree O M] [Module.Finite O N] [Module.IsTorsionFree O N]
    (h : Nonempty ((ρ.baseChange K).Equiv (σ.baseChange K))) :
    letI := Module.Finite.of_restrictScalars_finite (IsLocalRing.ResidueField O)
      (IsLocalRing.ResidueField O)[G] (ρ.baseChange (IsLocalRing.ResidueField O)).asModule
    letI := Module.Finite.of_restrictScalars_finite (IsLocalRing.ResidueField O)
      (IsLocalRing.ResidueField O)[G] (σ.baseChange (IsLocalRing.ResidueField O)).asModule
    (ExactK0.of (FGModuleCat.of (IsLocalRing.ResidueField O)[G]
        (ρ.baseChange (IsLocalRing.ResidueField O)).asModule) :
        ExactK0 (finiteModulesExactStructure (IsLocalRing.ResidueField O)[G])) =
      ExactK0.of (FGModuleCat.of (IsLocalRing.ResidueField O)[G]
        (σ.baseChange (IsLocalRing.ResidueField O)).asModule) := by
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
    rw [IntertwiningMap.toLinearMap_apply, hff', hs, mul_comm (u : O), mul_smul,
      ← Units.smul_def, smul_inv_smul]
  let k := IsLocalRing.ResidueField O
  let eρ : ρ.Equiv f.range.toRepresentation :=
    .mk (LinearEquiv.ofInjective f.toLinearMap hf) fun g ↦ by
      ext v
      exact f.isIntertwining _ _ g v
  let eσ : (⊤ : Subrepresentation σ).toRepresentation.Equiv σ :=
    .mk Submodule.topEquiv fun g ↦ rfl
  exact (exactK0_baseChange_congr k eρ).trans <|
    (exactK0_baseChange_eq_of_pow_smul_le k IsLocalRing.residue_surjective hker
      (.of_ne_zero hϖ.ne_zero) n le_top hle).trans (exactK0_baseChange_congr k eσ)

/-! ### Rationalization of a stable lattice -/

section Rationalization

variable {K : Type*} [CommRing K] [Algebra O K] {V : Type*} [AddCommGroup V] [Module K V]
  [Module O V] [IsScalarTower O K V]

/-- **A stable full lattice recovers the representation.** For a `G`-stable free full lattice
`L` in a representation `ρ` over `K`, the rationalization `K ⊗_O L ≃ V`, `a ⊗ v ↦ a • v`
(`Submodule.rationalizationEquiv`), is an equivalence of representations. -/
noncomputable def _root_.Subrepresentation.rationalizationEquiv
    {ρ : Representation K G V} (L : Subrepresentation (ρ.restrictScalars O))
    [Module.Free O L.toSubmodule] [L.toSubmodule.IsFullLattice K] :
    (L.toRepresentation.baseChange K).Equiv ρ :=
  .mk (Submodule.rationalizationEquiv L.toSubmodule) fun g ↦
    TensorProduct.AlgebraTensorModule.ext fun a v ↦ by simp [Representation.baseChange_apply]

/-- The rationalization of a stable lattice sends a pure tensor to scalar multiplication of the
embedded lattice vector. -/
@[simp]
theorem _root_.Subrepresentation.rationalizationEquiv_tmul
    {ρ : Representation K G V} (L : Subrepresentation (ρ.restrictScalars O))
    [Module.Free O L.toSubmodule] [L.toSubmodule.IsFullLattice K] (a : K) (v : L.toSubmodule) :
    L.rationalizationEquiv (a ⊗ₜ[O] v) = a • (v : V) := by
  simp [Subrepresentation.rationalizationEquiv]

end Rationalization

/-! ### Stable lattices in a representation over the fraction field -/

section Existence

variable (K : Type*) [Field K] [Algebra O K] [IsFractionRing O K]

/-- **Existence of stable lattices.** A finite-dimensional representation `ρ` of a finite group
(or monoid) over the fraction field `K` of `O` contains a `G`-stable full `O`-lattice: the
`O`-span of the translates `ρ g bᵢ` of a `K`-basis `(bᵢ)`. -/
theorem exists_isFullLattice_subrepresentation [Finite G] {V : Type*} [AddCommGroup V]
    [Module K V] [Module O V] [IsScalarTower O K V] [FiniteDimensional K V]
    (ρ : Representation K G V) :
    ∃ L : Subrepresentation (ρ.restrictScalars O), L.toSubmodule.IsFullLattice K := by
  let b := Module.finBasis K V
  let L : Submodule O V := Submodule.span O (Set.range fun p : G × Fin _ ↦ ρ p.1 (b p.2))
  have hstab (g : G) : L ≤ L.comap ((ρ g).restrictScalars O) := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨⟨h, i⟩, rfl⟩
    refine Submodule.subset_span ⟨(g * h, i), ?_⟩
    simp
  refine ⟨⟨L, fun g _ hv ↦ by rw [Representation.restrictScalars_apply]; exact hstab g hv⟩, ?_⟩
  refine { Submodule.IsLattice.of_fg K (Submodule.fg_span (Set.finite_range _)) with
    span_eq_top := top_le_iff.mp (b.span_eq ▸ Submodule.span_mono ?_) }
  rintro _ ⟨i, rfl⟩
  refine Submodule.subset_span ⟨(1, i), ?_⟩
  simp

variable {K} [IsDomain O]

/-- **Stable full lattices in one representation have reductions with the same class.** Let
`O` be a discrete valuation ring with fraction field `K` and residue field `k`, and `L₁`, `L₂`
two `G`-stable full `O`-lattices in a representation `ρ` over `K`. Then `[k ⊗_O L₁]` and
`[k ⊗_O L₂]` agree in `G₀(k[G])`. -/
theorem exactK0_baseChange_residueField_eq_of_isFullLattice [IsDiscreteValuationRing O]
    {V : Type u} [AddCommGroup V] [Module K V] [Module O V] [IsScalarTower O K V]
    {ρ : Representation K G V} (L₁ L₂ : Subrepresentation (ρ.restrictScalars O))
    [L₁.toSubmodule.IsFullLattice K] [L₂.toSubmodule.IsFullLattice K] :
    letI := Submodule.IsLattice.finite K L₁.toSubmodule
    letI := Submodule.IsLattice.finite K L₂.toSubmodule
    letI := Module.Finite.of_restrictScalars_finite (IsLocalRing.ResidueField O)
      (IsLocalRing.ResidueField O)[G]
      (L₁.toRepresentation.baseChange (IsLocalRing.ResidueField O)).asModule
    letI := Module.Finite.of_restrictScalars_finite (IsLocalRing.ResidueField O)
      (IsLocalRing.ResidueField O)[G]
      (L₂.toRepresentation.baseChange (IsLocalRing.ResidueField O)).asModule
    (ExactK0.of (FGModuleCat.of (IsLocalRing.ResidueField O)[G]
        (L₁.toRepresentation.baseChange (IsLocalRing.ResidueField O)).asModule) :
        ExactK0 (finiteModulesExactStructure (IsLocalRing.ResidueField O)[G])) =
      ExactK0.of (FGModuleCat.of (IsLocalRing.ResidueField O)[G]
        (L₂.toRepresentation.baseChange (IsLocalRing.ResidueField O)).asModule) :=
  letI := Submodule.IsLattice.finite K L₁.toSubmodule
  letI := Submodule.IsLattice.finite K L₂.toSubmodule
  haveI := Submodule.IsLattice.free K L₁.toSubmodule
  haveI := Submodule.IsLattice.free K L₂.toSubmodule
  haveI := Module.IsTorsionFree.trans_faithfulSMul O K V
  exactK0_baseChange_residueField_eq_of_nonempty_equiv_baseChange K
    ⟨L₁.rationalizationEquiv.trans L₂.rationalizationEquiv.symm⟩

end Existence

end TauCeti

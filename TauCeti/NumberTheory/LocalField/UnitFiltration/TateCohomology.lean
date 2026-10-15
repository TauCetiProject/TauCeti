/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LocalField.UnitFiltration.Lattice
public import TauCeti.RepresentationTheory.Homological.TateCohomology.Coinduced
public import TauCeti.RepresentationTheory.Homological.TateCohomology.Filtration

/-!
# The Herbrand quotient of the units of a local field

Let `L/K` be a finite Galois extension of nonarchimedean local fields whose Galois group
`G = L ≃ₐ[K] L` is cyclic. This file proves that the Herbrand quotient of the unit group
`𝒪[L]ˣ = U(L, 0)`, with its Galois action and read as an integral representation of `G`, is `1`
(`TauCeti.TateCohomology.herbrandQuotient_unitFiltration_zero`). Together with the Herbrand
quotient `|G|` of the trivial module `ℤ` and the valuation sequence `0 → 𝒪[L]ˣ → Lˣ → ℤ → 0`, this
is the cyclic computation `h(Lˣ) = [L : K]` from which the order of `H²(G, Lˣ)` is bounded by the
degree.

The unit group is replaced by a commensurable one on which the computation can be carried out.
For a uniformizer `ϖ` of `K`, a scaled normal basis element spans a Galois-stable lattice
`A ⊆ 𝒪[L]`, free of rank one over `𝒪[K][G]`, whose unit filtration `1 + ϖ ^ n • A`
(`TauCeti.IsUnitFiltrationLattice.filtration`) consists of open subgroups of `𝒪[L]ˣ`. Its step
zero `1 + A` has finite index in `𝒪[L]ˣ`, so by invariance of the Herbrand quotient under maps
with finite cokernel it suffices to show that the Herbrand quotient of `1 + A` is `1`. The
filtration of `1 + A` is separated and complete, and each graded piece is `A ⧸ ϖ • A`, free of
rank one over `(𝒪[K] ⧸ ϖ)[G]`, hence with vanishing Tate cohomology; successive approximation
(`TauCeti.TateCohomology.herbrandQuotient_eq_one_of_filtration`) then gives the claim. The
filtration is used instead of the unit filtration `U(L, i)` of `L`, whose graded pieces are the
residue field of `L` and are in general not free over the group ring.

## Main results

* `TauCeti.TateCohomology.herbrandQuotient_unitFiltration_zero`: the Herbrand quotient of `𝒪[L]ˣ`
  is `1` for a cyclic extension `L/K` of nonarchimedean local fields.

## References

* J.-P. Serre, *Local Fields*, Chapter IX, §3, Lemma 2 and Proposition 3.
* J.-P. Serre, *Local class field theory*, in J. W. S. Cassels and A. Fröhlich (eds.),
  *Algebraic Number Theory*, Chapter VI, §1.4.
* J. Neukirch, *Algebraic Number Theory*, Chapter V, Proposition 1.2.
-/

public section
noncomputable section

open CategoryTheory Limits ValuativeRel Submodule MulAction

namespace TauCeti

variable {K L : Type} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [Field L] [ValuativeRel L] [TopologicalSpace L]
  [IsNonarchimedeanLocalField L] [Algebra K L] [ValuativeExtension K L] [Module.Finite K L]

namespace IsUnitFiltrationLattice

/-! ### Step zero of the filtration as an integral representation -/

variable {ϖ : 𝒪[K]} {A : Submodule 𝒪[K] 𝒪[L]} (hA : IsUnitFiltrationLattice ϖ A)
  (hσ : ∀ σ : L ≃ₐ[K] L,
    A ≤ A.comap (Representation.ofDistribMulAction 𝒪[K] (L ≃ₐ[K] L) 𝒪[L] σ))

/-- The Galois action on step zero `1 + A` of the unit filtration of a Galois-stable lattice. -/
@[instance_reducible]
private def mulDistribMulAction : MulDistribMulAction (L ≃ₐ[K] L) (hA.filtration 0) :=
  letI : SMul (L ≃ₐ[K] L) (hA.filtration 0) :=
    ⟨fun σ x ↦ ⟨σ • (x : Lˣ), by
      simpa only [AlgEquiv.smul_units_def] using
        hA.unitsMap_mem_filtration σ (fun _ ha ↦ hσ σ ha) x.2⟩⟩
  Subtype.coe_injective.mulDistribMulAction (hA.filtration 0).subtype fun _ _ ↦ rfl

/-- The Galois action on step zero `1 + A` is the restriction of the Galois action on `Lˣ`. -/
private theorem coe_smul (σ : L ≃ₐ[K] L) (x : hA.filtration 0) :
    letI := hA.mulDistribMulAction hσ
    ((σ • x : hA.filtration 0) : Lˣ) = σ • (x : Lˣ) :=
  rfl

/-- Step zero `1 + A` of the unit filtration of a Galois-stable lattice, written additively, as an
integral representation of the Galois group. -/
private abbrev rep : Rep ℤ (L ≃ₐ[K] L) :=
  letI := hA.mulDistribMulAction hσ
  Rep.of (Representation.ofMulDistribMulAction (L ≃ₐ[K] L) (hA.filtration 0))

/-- The unit of `L` underlying an element of `hA.rep hσ`. -/
private def toUnits (x : hA.rep hσ) : Lˣ :=
  (Additive.toMul x : hA.filtration 0)

private theorem toUnits_mem (x : hA.rep hσ) : hA.toUnits hσ x ∈ hA.filtration 0 :=
  (Additive.toMul x).2

private theorem toUnits_injective : Function.Injective (hA.toUnits hσ) := fun _ _ h ↦
  Additive.toMul.injective (Subtype.ext h)

private theorem toUnits_ρ (σ : L ≃ₐ[K] L) (x : hA.rep hσ) :
    hA.toUnits hσ ((hA.rep hσ).ρ σ x) = σ • hA.toUnits hσ x := by
  simp only [toUnits, Representation.ofMulDistribMulAction_apply_apply, toMul_ofMul]
  exact hA.coe_smul hσ σ _

private theorem toUnits_sub (x y : hA.rep hσ) :
    hA.toUnits hσ (x - y) = hA.toUnits hσ x / hA.toUnits hσ y := by
  simp [toUnits]

private theorem toUnits_sum (s : Finset ℕ) (x : ℕ → hA.rep hσ) :
    hA.toUnits hσ (∑ i ∈ s, x i) = ∏ i ∈ s, hA.toUnits hσ (x i) := by
  simp [toUnits]

/-- The `n`-th step `1 + ϖ ^ n • A` of the filtration, as a submodule of `hA.rep hσ`. -/
private def step (n : ℕ) : Submodule ℤ (hA.rep hσ) :=
  (Subgroup.toAddSubgroup ((hA.filtration n).subgroupOf (hA.filtration 0))).toIntSubmodule

private theorem mem_step {n : ℕ} {x : hA.rep hσ} :
    x ∈ hA.step hσ n ↔ hA.toUnits hσ x ∈ hA.filtration n := by
  rw [step, ← Submodule.mem_toAddSubgroup, AddSubgroup.toIntSubmodule_toAddSubgroup,
    Additive.mem_toAddSubgroup, Subgroup.mem_subgroupOf, toUnits]

private theorem step_zero : hA.step hσ 0 = ⊤ :=
  eq_top_iff.2 fun x _ ↦ (hA.mem_step hσ).2 (hA.toUnits_mem hσ x)

private theorem step_le_comap (n : ℕ) (σ : L ≃ₐ[K] L) :
    hA.step hσ n ≤ (hA.step hσ n).comap ((hA.rep hσ).ρ σ) := fun _ hx ↦ by
  rw [Submodule.mem_comap, mem_step, toUnits_ρ, AlgEquiv.smul_units_def]
  exact hA.unitsMap_mem_filtration σ (fun _ ha ↦ hσ σ ha) ((hA.mem_step hσ).1 hx)

/-- The filtration by the steps is separated. -/
private theorem eq_zero_of_forall_mem_step (x : hA.rep hσ) (hx : ∀ n, x ∈ hA.step hσ n) :
    x = 0 := by
  have h : hA.toUnits hσ x ∈ ⨅ n, hA.filtration n :=
    Subgroup.mem_iInf.2 fun n ↦ (hA.mem_step hσ).1 (hx n)
  rw [hA.iInf_filtration, Subgroup.mem_bot] at h
  exact hA.toUnits_injective hσ (h.trans (by simp [toUnits]))

/-- The filtration by the steps is complete. -/
private theorem exists_forall_sub_sum_mem_step (x : ℕ → hA.rep hσ)
    (hx : ∀ n, x n ∈ hA.step hσ n) :
    ∃ s : hA.rep hσ, ∀ n, s - ∑ i ∈ Finset.range n, x i ∈ hA.step hσ n := by
  obtain ⟨s, hs0, hs⟩ := hA.exists_forall_div_prod_mem_filtration
    (fun n ↦ hA.toUnits hσ (x n)) fun n ↦ (hA.mem_step hσ).1 (hx n)
  refine ⟨Additive.ofMul (α := hA.filtration 0) ⟨s, hs0⟩, fun n ↦ (hA.mem_step hσ).2 ?_⟩
  rw [toUnits_sub, toUnits_sum]
  simpa [toUnits] using hs n

/-! ### The graded pieces -/

/-- The lattice `A` as a representation of the Galois group over `𝒪[K]`. -/
private abbrev latticeRep : Representation 𝒪[K] (L ≃ₐ[K] L) A :=
  (Representation.ofDistribMulAction 𝒪[K] (L ≃ₐ[K] L) 𝒪[L]).subrepresentation A hσ

/-- The map `1 + ϖ ^ n • a ↦ a mod ϖ • A` from the `n`-th step onto the graded piece
`A ⧸ ϖ • A`, additively. -/
private def gradedMap (n : ℕ) : hA.step hσ n →+ QuotSMulTop ϖ A :=
  (hA.filtrationToQuotient n).toAdditive.comp
    (AddMonoidHom.mk'
      (fun x ↦ Additive.ofMul (⟨hA.toUnits hσ x, (hA.mem_step hσ).1 x.2⟩ : hA.filtration n))
      fun _ _ ↦ rfl)

/-- `gradedMap` is `filtrationToQuotient` applied to the underlying unit of `1 + ϖ ^ n • A`. -/
private theorem gradedMap_eq_toAdd_filtrationToQuotient {n : ℕ} (x : hA.step hσ n) :
    hA.gradedMap hσ n x = Multiplicative.toAdd
      (hA.filtrationToQuotient n ⟨hA.toUnits hσ x, (hA.mem_step hσ).1 x.2⟩) :=
  rfl

private theorem gradedMap_apply {n : ℕ} (x : hA.step hσ n) {a : 𝒪[L]} (ha : a ∈ A)
    (hx : (hA.toUnits hσ x : L) = ((1 + ϖ ^ n • a : 𝒪[L]) : L)) :
    hA.gradedMap hσ n x = Submodule.Quotient.mk ⟨a, ha⟩ :=
  (hA.gradedMap_eq_toAdd_filtrationToQuotient hσ x).trans
    (congrArg Multiplicative.toAdd (hA.filtrationToQuotient_apply _ ha hx))

private theorem gradedMap_ρ {n : ℕ} (σ : L ≃ₐ[K] L) (x : hA.step hσ n) :
    hA.gradedMap hσ n ⟨(hA.rep hσ).ρ σ x, hA.step_le_comap hσ n σ x.2⟩ =
      ((latticeRep hσ).quotSMulTop ϖ).restrictScalarsInt σ (hA.gradedMap hσ n x) := by
  obtain ⟨a, ha, hx⟩ := hA.mem_filtration_iff.1 ((hA.mem_step hσ).1 x.2)
  have hσx : (hA.toUnits hσ ((hA.rep hσ).ρ σ x) : L) = ((1 + ϖ ^ n • (σ • a) : 𝒪[L]) : L) := by
    rw [toUnits_ρ, AlgEquiv.smul_units_def, Units.coe_map, MonoidHom.coe_ofClass, hx,
      ← AlgEquiv.coe_smul_integerRing, smul_add, smul_one, smul_comm]
  rw [hA.gradedMap_apply hσ x ha hx, hA.gradedMap_apply hσ _ (hσ σ ha) hσx,
    Representation.restrictScalarsInt_apply, Representation.quotSMulTop_apply_mk]
  simp [LinearMap.restrict_apply]

/-- The map `1 + ϖ ^ n • a ↦ a mod ϖ • A` onto the graded piece, as a morphism of integral
representations. -/
private def gradedHom (n : ℕ) :
    (hA.rep hσ).subrepresentation (hA.step hσ n) (hA.step_le_comap hσ n) ⟶
      Rep.of ((latticeRep hσ).quotSMulTop ϖ).restrictScalarsInt :=
  Rep.ofHom
    { toFun := hA.gradedMap hσ n
      map_add' := map_add _
      map_smul' := map_zsmul _
      isIntertwining' σ := LinearMap.ext fun x ↦ hA.gradedMap_ρ hσ σ x }

private theorem gradedHom_hom_apply (n : ℕ) (x : hA.step hσ n) :
    (hA.gradedHom hσ n).hom x = hA.gradedMap hσ n x := by
  simp [gradedHom]

private theorem gradedHom_surjective (n : ℕ) : Function.Surjective (hA.gradedHom hσ n).hom := by
  intro q
  obtain ⟨y, hy⟩ := hA.filtrationToQuotient_surjective n (Multiplicative.ofAdd q)
  exact ⟨⟨Additive.ofMul ⟨y, hA.filtration_antitone (Nat.zero_le n) y.2⟩, y.2⟩,
    congrArg Multiplicative.toAdd hy⟩

private theorem mem_step_succ_of_gradedHom_eq_zero (n : ℕ) (x : hA.step hσ n)
    (hx : (hA.gradedHom hσ n).hom x = 0) : (x : hA.rep hσ) ∈ hA.step hσ (n + 1) := by
  rw [gradedHom_hom_apply, gradedMap_eq_toAdd_filtrationToQuotient, toAdd_eq_zero] at hx
  exact (hA.mem_step hσ).2 (Subgroup.mem_subgroupOf.1 ((hA.ker_filtrationToQuotient n).le hx))

/-- **The Herbrand quotient of `1 + A` is `1`** when `A` is free of rank one over `𝒪[K][G]`: the
filtration `1 + ϖ ^ n • A` is separated and complete, and its graded pieces have vanishing Tate
cohomology. -/
private theorem herbrandQuotient_rep
    (e : (Representation.leftRegular 𝒪[K] (L ≃ₐ[K] L)).Equiv (latticeRep hσ)) :
    TateCohomology.herbrandQuotient (hA.rep hσ) = 1 :=
  TateCohomology.herbrandQuotient_eq_one_of_filtration (hA.step_le_comap hσ) (hA.gradedHom hσ)
    (hA.step_zero hσ) (hA.eq_zero_of_forall_mem_step hσ) (hA.exists_forall_sub_sum_mem_step hσ)
    (hA.gradedHom_surjective hσ) (hA.mem_step_succ_of_gradedHom_eq_zero hσ)
    (fun _ ↦ TateCohomology.isZero_restrictScalarsInt_quotSMulTop_of_equiv_leftRegular e ϖ 0)
    (fun _ ↦ TateCohomology.isZero_restrictScalarsInt_quotSMulTop_of_equiv_leftRegular e ϖ (-1))

/-! ### Comparison with the unit group -/

omit [Module.Finite K L] in
private theorem filtration_zero_le : hA.filtration 0 ≤ unitFiltration L 0 :=
  (hA.filtration_le_unitFiltration_succ 0).trans (unitFiltration_antitone (Nat.zero_le 1))

/-- The inclusion of `1 + A` into `𝒪[L]ˣ = U(L, 0)`, additively. -/
private def inclusionHom : hA.rep hσ →+ Additive (unitFiltration L 0) :=
  MonoidHom.toAdditive (α := hA.filtration 0) (Subgroup.inclusion hA.filtration_zero_le)

private theorem coe_inclusionHom (x : hA.rep hσ) :
    ((Additive.toMul (hA.inclusionHom hσ x) : unitFiltration L 0) : Lˣ) = hA.toUnits hσ x := by
  rw [inclusionHom, MonoidHom.coe_toAdditive, Function.comp_apply, Function.comp_apply,
    toMul_ofMul, Subgroup.coe_inclusion, toUnits]

private theorem inclusionHom_ρ (σ : L ≃ₐ[K] L) (x : hA.rep hσ) :
    hA.inclusionHom hσ ((hA.rep hσ).ρ σ x) =
      (Rep.ofMulDistribMulAction (L ≃ₐ[K] L) (unitFiltration L 0)).ρ σ
        (hA.inclusionHom hσ x) := by
  rw [Rep.ofMulDistribMulAction_ρ_apply_apply]
  refine Additive.toMul.injective (Subtype.ext ?_)
  rw [toMul_ofMul, AlgEquiv.coe_smul_unitFiltration, coe_inclusionHom, coe_inclusionHom,
    toUnits_ρ]

/-- The inclusion of `1 + A` into `𝒪[L]ˣ = U(L, 0)`, as a morphism of integral representations. -/
private def inclusion :
    hA.rep hσ ⟶ Rep.ofMulDistribMulAction (L ≃ₐ[K] L) (unitFiltration L 0) :=
  Rep.ofHom
    { toFun := hA.inclusionHom hσ
      map_add' := map_add _
      map_smul' := map_zsmul _
      isIntertwining' σ := LinearMap.ext fun x ↦ hA.inclusionHom_ρ hσ σ x }

private theorem inclusion_injective : Function.Injective (hA.inclusion hσ).hom := fun x y h ↦
  hA.toUnits_injective hσ <| by
    rw [← coe_inclusionHom, ← coe_inclusionHom]
    exact congrArg (fun z ↦ ((Additive.toMul z : unitFiltration L 0) : Lˣ)) h

/-- The image of `1 + A` has finite index in `𝒪[L]ˣ`: it contains some `U(L, m)`. -/
private theorem finiteIndex_range_inclusion :
    (LinearMap.range ((forget₂ (Rep ℤ (L ≃ₐ[K] L)) (ModuleCat ℤ)).map
      (hA.inclusion hσ)).hom).toAddSubgroup.FiniteIndex := by
  obtain ⟨m, hm⟩ := hA.exists_unitFiltration_le_filtration 0
  have : (Subgroup.toAddSubgroup
      ((unitFiltration L m).subgroupOf (unitFiltration L 0))).FiniteIndex :=
    ⟨by rw [Subgroup.index_toAddSubgroup]; exact Subgroup.FiniteIndex.index_ne_zero⟩
  refine AddSubgroup.finiteIndex_of_le (H := Subgroup.toAddSubgroup
    ((unitFiltration L m).subgroupOf (unitFiltration L 0))) fun x hx ↦ ?_
  exact ⟨Additive.ofMul (α := hA.filtration 0) ⟨_, hm hx⟩,
    Additive.toMul.injective (Subtype.ext rfl)⟩

private theorem finite_cokernel_inclusion : Finite ↑(cokernel (hA.inclusion hσ)) := by
  have := hA.finiteIndex_range_inclusion hσ
  -- The cokernel is computed in `ModuleCat ℤ`, as the quotient by the range.
  have : Finite (Additive (unitFiltration L 0) ⧸ LinearMap.range
      ((forget₂ (Rep ℤ (L ≃ₐ[K] L)) (ModuleCat ℤ)).map (hA.inclusion hσ)).hom) :=
    inferInstanceAs (Finite (_ ⧸ (LinearMap.range
      ((forget₂ (Rep ℤ (L ≃ₐ[K] L)) (ModuleCat ℤ)).map (hA.inclusion hσ)).hom).toAddSubgroup))
  exact Finite.of_equiv _ (PreservesCokernel.iso (forget₂ _ (ModuleCat ℤ)) (hA.inclusion hσ) ≪≫
    ModuleCat.cokernelIsoRangeQuotient _).toLinearEquiv.toEquiv.symm

end IsUnitFiltrationLattice

namespace TateCohomology

/-- **The Herbrand quotient of the local units.** For a finite Galois extension `L/K` of
nonarchimedean local fields with cyclic Galois group `G`, the Herbrand quotient of the unit group
`𝒪[L]ˣ = U(L, 0)`, with its Galois action and read as an integral representation of `G`, is `1`:
its Tate cohomology groups in degrees `0` and `-1` are finite of the same order. -/
@[simp]
theorem herbrandQuotient_unitFiltration_zero [IsGalois K L] [IsCyclic (L ≃ₐ[K] L)] :
    TateCohomology.herbrandQuotient
      (Rep.ofMulDistribMulAction (L ≃ₐ[K] L) (unitFiltration L 0)) = 1 := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[K]
  obtain ⟨α, hα, hA⟩ := exists_isUnitFiltrationLattice_span_orbit (L := L) hϖ.ne_zero
    ((IsLocalRing.mem_maximalIdeal _).2 hϖ.not_isUnit)
  have hσ (σ : L ≃ₐ[K] L) : span 𝒪[K] (orbit (L ≃ₐ[K] L) α) ≤
      (span 𝒪[K] (orbit (L ≃ₐ[K] L) α)).comap
        (Representation.ofDistribMulAction 𝒪[K] (L ≃ₐ[K] L) 𝒪[L] σ) :=
    (Module.End.mem_invtSubmodule _).1 <| Module.End.span_orbit_mem_invtSubmodule _ α σ
  have := hA.finite_cokernel_inclusion hσ
  have := (Rep.mono_iff_injective _).2 (hA.inclusion_injective hσ)
  rw [← TateCohomology.herbrandQuotient_eq_of_mono_of_finite_cokernel (hA.inclusion hσ)]
  exact hA.herbrandQuotient_rep hσ (spanOrbitEquiv hα)

end TateCohomology

end TauCeti

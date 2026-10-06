/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.GroupAction.TypeTags
public import TauCeti.Algebra.Module.Torsion.Snake
public import TauCeti.NumberTheory.LocalField.PowerSubgroup.Basic
public import TauCeti.NumberTheory.LocalField.UnitFiltration.GaloisAction
public import TauCeti.NumberTheory.LocalField.UnitFiltration.Graded
public import TauCeti.NumberTheory.LocalField.UnitsDecomposition
public import TauCeti.RepresentationTheory.GrothendieckGroup.GroupAlgebra.LatticeDefect.Finite
public import TauCeti.RepresentationTheory.GrothendieckGroup.GroupAlgebra.LatticeDefect.Trivial
public import TauCeti.RingTheory.RootsOfUnity.Basic

/-!
# The class of `Lˣ ⧸ (Lˣ)^ℓ` in `G₀(k[Gal(L/K)])`

Let `L/K` be a finite extension of nonarchimedean local fields with automorphism group
`G = L ≃ₐ[K] L`, let `ℓ` be a prime which is nonzero in `L`, and let `k` be a field of
characteristic `ℓ`. The multiplicative group `Lˣ`, written additively, is a `G`-module. This file
computes the class of its reduction `Lˣ ⧸ (Lˣ)^ℓ` in the Grothendieck group `G₀(k[G])` of finitely
generated `k[G]`-modules, in terms of the lattice defect `TauCeti.latticeDefect` of the unit
filtration:

`[Lˣ ⧸ (Lˣ)^ℓ] = [k] + [μ_ℓ(L)] + latticeDefect (U(L,i))`

for every `i`, where `μ_ℓ(L)` is the `ℓ`-torsion of `Lˣ` (`TauCeti.reductionK0_quotSMulTop_units`).
Since `[Lˣ ⧸ (Lˣ)^ℓ] - [μ_ℓ(L)]` is by definition the defect of `Lˣ`, this is the statement
`latticeDefect Lˣ = 1 + latticeDefect (U(L,i))` (`TauCeti.latticeDefect_units_eq_one_add`). It
follows from the additivity of the defect along the valuation sequence
`0 → 𝒪[L]ˣ → Lˣ → ℤ → 0`, whose quotient `ℤ` has the trivial action and defect `1`
(`TauCeti.latticeDefect_int_eq_one`), and from the invariance of the defect under the inclusions
`U(L,i) ⊆ 𝒪[L]ˣ`, which have finite index (`TauCeti.latticeDefect_unitFiltration_eq`). When `ℓ` is
a unit of `𝒪[L]`, raising to the `ℓ`-th power is bijective on the principal units, whose defect
therefore vanishes, and `[Lˣ ⧸ (Lˣ)^ℓ] = [k] + [μ_ℓ(L)]`
(`TauCeti.reductionK0_quotSMulTop_units_of_isUnit`).

This is the computation of the units of `L` that enters the proof of the local Euler characteristic
formula, where Kummer theory identifies `H¹(L, μ_ℓ)` with `Lˣ ⧸ (Lˣ)^ℓ`.

The finiteness of the reductions and torsion subgroups, which the definition of the defect asks
for, is recorded by instances: `Lˣ ⧸ (Lˣ)^ℓ` is finite since `(Lˣ)^ℓ` has finite index
(`TauCeti.finiteIndex_range_powMonoidHom`), and the reductions of the `U(L,i)` are then finite by
the snake lemma (`TauCeti.finite_quotSMulTop_of_exact`).

## Main results

* `TauCeti.latticeDefect_unitFiltration_eq`: all steps of the unit filtration have the same defect.
* `TauCeti.latticeDefect_units_eq_one_add`: the defect of `Lˣ` is `1` plus that of `U(L,i)`.
* `TauCeti.latticeDefect_unitFiltration_succ_eq_zero_of_isUnit`: away from the residue
  characteristic, the positive-depth steps have zero defect.
* `TauCeti.reductionK0_quotSMulTop_units` and `TauCeti.reductionK0_quotSMulTop_units_of_isUnit`:
  the class of `Lˣ ⧸ (Lˣ)^ℓ`.

## References

* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., Springer (2008),
  §VII.3, (7.3.3) and the proof of (7.3.1).
* J. S. Milne, *Arithmetic Duality Theorems*, 2nd ed., Chapter I, proof of Theorem 2.8.
-/

public section

open Function ValuativeRel
open scoped Pointwise

namespace TauCeti

/-! ### Finiteness of the torsion and of the reductions modulo `ℓ` -/

section LocalField

variable {L : Type*} [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]

/-- The inclusion of `U(L,i)` in `Lˣ`, written additively, as a `ℤ`-linear map. -/
private noncomputable abbrev unitFiltrationSubtypeInt (i : ℕ) :
    Additive (unitFiltration L i) →ₗ[ℤ] Additive Lˣ :=
  (unitFiltration L i).subtype.toAdditive.toIntLinearMap

/-- The `n`-torsion of every step of the unit filtration, written additively, is finite. -/
instance finite_torsionBy_additive_unitFiltration (n : ℕ) [NeZero n] (i : ℕ) :
    Finite (Submodule.torsionBy ℤ (Additive (unitFiltration L i)) (n : ℤ)) :=
  Finite.of_injective _ (injective_torsionByMap (r := (n : ℤ)) (f := unitFiltrationSubtypeInt i)
    fun _ _ h ↦ Additive.toMul.injective (Subtype.ext (congrArg Additive.toMul h)))

/-- When `n` is nonzero in `L`, the reduction `Lˣ ⧸ (Lˣ)^n` of the multiplicative group, written
additively, is finite. -/
instance finite_quotSMulTop_additive_units (n : ℕ) [NeZero (n : L)] :
    Finite (QuotSMulTop (n : ℤ) (Additive Lˣ)) := by
  have := finiteIndex_range_powMonoidHom (K := L) (NeZero.ne (n : L))
  -- the quotient map kills the `n`-th powers, so it factors through `Lˣ ⧸ (Lˣ)^n`
  let N : Submodule ℤ (Additive Lˣ) := (n : ℤ) • ⊤
  let φ : Lˣ →* Multiplicative (QuotSMulTop (n : ℤ) (Additive Lˣ)) :=
    AddMonoidHom.toMultiplicativeRight N.mkQ.toAddMonoidHom
  have hφ : (powMonoidHom n : Lˣ →* Lˣ).range ≤ φ.ker := by
    rintro _ ⟨x, rfl⟩
    rw [MonoidHom.mem_ker]
    exact congrArg Multiplicative.ofAdd <| (Submodule.Quotient.mk_eq_zero _).2 <|
      (Submodule.mem_smul_pointwise_iff_exists _ _ _).2
        ⟨Additive.ofMul x, Submodule.mem_top, by rw [natCast_zsmul, powMonoidHom_apply, ofMul_pow]⟩
  have := Finite.of_surjective _ (QuotientGroup.lift_surjective_of_surjective _ φ
    N.mkQ_surjective hφ)
  exact Finite.of_equiv _ Multiplicative.toAdd

/-- The normalized valuation `Lˣ → ℤ`, written additively, as a `ℤ`-linear map. -/
private noncomputable abbrev valuationInt : Additive Lˣ →ₗ[ℤ] ℤ :=
  (normalizedValuation L).toAdditiveLeft.toIntLinearMap

private theorem exact_unitFiltrationSubtypeInt_valuationInt :
    Exact (unitFiltrationSubtypeInt (L := L) 0) valuationInt := fun x ↦ by
  rw [AddMonoidHom.coe_toIntLinearMap, MonoidHom.coe_toAdditiveLeft, comp_apply, comp_apply,
    toAdd_eq_zero,
    ← MonoidHom.mem_ker, ker_normalizedValuation]
  exact ⟨fun hx ↦ ⟨Additive.ofMul ⟨x.toMul, hx⟩, rfl⟩, by rintro ⟨y, rfl⟩; exact y.toMul.2⟩

private theorem surjective_valuationInt : Surjective (valuationInt (L := L)) := fun n ↦
  (normalizedValuation_surjective (K := L) (Multiplicative.ofAdd n)).imp fun _ hx ↦
    congrArg Multiplicative.toAdd hx

/-- When `n` is nonzero in `L`, the reduction `𝒪[L]ˣ ⧸ (𝒪[L]ˣ)^n` of the unit group, written
additively, is finite: along the valuation sequence it injects into `Lˣ ⧸ (Lˣ)^n`. -/
private theorem finite_quotSMulTop_additive_unitFiltration_zero (n : ℕ) [NeZero (n : L)] :
    Finite (QuotSMulTop (n : ℤ) (Additive (unitFiltration L 0))) := by
  have : NeZero n := ⟨fun h ↦ NeZero.ne (n : L) (by simp [h])⟩
  exact finite_quotSMulTop_of_exact exact_unitFiltrationSubtypeInt_valuationInt
    (fun _ _ h ↦ Additive.toMul.injective (Subtype.ext (congrArg Additive.toMul h)))
    surjective_valuationInt

/-- The inclusion of `U(L,j)` in `U(L,i)` for `i ≤ j`, written additively, as a `ℤ`-linear map. -/
private noncomputable abbrev unitFiltrationInclusionInt {i j : ℕ} (h : i ≤ j) :
    Additive (unitFiltration L j) →ₗ[ℤ] Additive (unitFiltration L i) :=
  (Subgroup.inclusion (unitFiltration_antitone h)).toAdditive.toIntLinearMap

private theorem injective_unitFiltrationInclusionInt {i j : ℕ} (h : i ≤ j) :
    Injective (unitFiltrationInclusionInt (L := L) h) := fun _ _ hxy ↦
  Additive.toMul.injective <|
    Subgroup.inclusion_injective (unitFiltration_antitone h) (congrArg Additive.toMul hxy)

/-- `U(L,i)`, written additively, has finite index in `U(L,0)`. -/
private theorem finiteIndex_toAddSubgroup_unitFiltration (i : ℕ) :
    (Subgroup.toAddSubgroup ((unitFiltration L i).subgroupOf (unitFiltration L 0))).FiniteIndex :=
  ⟨by
    rw [Subgroup.index_toAddSubgroup]
    exact (Subgroup.isFiniteRelIndex_iff_finiteIndex.mp inferInstance).index_ne_zero⟩

/-- When `n` is nonzero in `L`, the reduction `U(L,i) ⧸ U(L,i)^n` of every step of the unit
filtration, written additively, is finite. -/
instance finite_quotSMulTop_additive_unitFiltration (n : ℕ) [NeZero (n : L)] (i : ℕ) :
    Finite (QuotSMulTop (n : ℤ) (Additive (unitFiltration L i))) := by
  have : NeZero n := ⟨fun h ↦ NeZero.ne (n : L) (by simp [h])⟩
  have := finite_quotSMulTop_additive_unitFiltration_zero (L := L) n
  -- `U(L,i)` has finite index in `U(L,0)`
  let H := Subgroup.toAddSubgroup ((unitFiltration L i).subgroupOf (unitFiltration L 0))
  have : H.FiniteIndex := finiteIndex_toAddSubgroup_unitFiltration i
  let g : Additive (unitFiltration L 0) →ₗ[ℤ] Additive (unitFiltration L 0) ⧸ H :=
    (QuotientAddGroup.mk' H).toIntLinearMap
  refine finite_quotSMulTop_of_exact (g := g)
    (fun x ↦ ?_) (injective_unitFiltrationInclusionInt (Nat.zero_le i))
    (QuotientAddGroup.mk'_surjective H ·)
  rw [AddMonoidHom.coe_toIntLinearMap, QuotientAddGroup.mk'_apply, QuotientAddGroup.eq_zero_iff,
    Additive.mem_toAddSubgroup, Subgroup.mem_subgroupOf]
  exact ⟨fun hx ↦ ⟨Additive.ofMul ⟨_, hx⟩, rfl⟩, by rintro ⟨y, rfl⟩; exact y.toMul.2⟩

end LocalField

/-! ### The Galois module `Lˣ` -/

section Galois

variable (K L : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [Field L] [ValuativeRel L] [TopologicalSpace L]
  [IsNonarchimedeanLocalField L] [Algebra K L] [ValuativeExtension K L] [Module.Finite K L]

/-- The inclusion of `U(L,i)` in `Lˣ`, written additively, is Galois-equivariant. -/
private noncomputable def unitFiltrationSubtypeHom (i : ℕ) :
    Additive (unitFiltration L i) →+[L ≃ₐ[K] L] Additive Lˣ :=
  { (unitFiltrationSubtypeInt i).toAddMonoidHom with map_smul' := fun _ _ ↦ rfl }

/-- The inclusion of `U(L,j)` in `U(L,i)` for `i ≤ j`, written additively, is Galois-equivariant. -/
private noncomputable def unitFiltrationInclusionHom {i j : ℕ} (h : i ≤ j) :
    Additive (unitFiltration L j) →+[L ≃ₐ[K] L] Additive (unitFiltration L i) :=
  { (unitFiltrationInclusionInt h).toAddMonoidHom with map_smul' := fun _ _ ↦ rfl }

/-- The trivial action of the Galois group on `ℤ`, the value group of `L`. -/
@[instance_reducible]
private noncomputable def trivialDistribMulActionInt : DistribMulAction (L ≃ₐ[K] L) ℤ :=
  DistribMulAction.compHom ℤ (1 : (L ≃ₐ[K] L) →* ℤ)

attribute [local instance] trivialDistribMulActionInt

/-- The normalized valuation `Lˣ → ℤ`, written additively, is invariant under the Galois group. -/
private noncomputable def valuationHom : Additive Lˣ →+[L ≃ₐ[K] L] ℤ :=
  { (valuationInt (L := L)).toAddMonoidHom with
    map_smul' := fun σ x ↦ by
      simp only [AddMonoidHom.toFun_eq_coe, LinearMap.toAddMonoidHom_coe,
        AddMonoidHom.coe_toIntLinearMap, MonoidHom.coe_toAdditiveLeft, comp_apply,
        Additive.toMul_smul, AlgEquiv.smul_units_def, AlgEquiv.normalizedValuation_unitsMap]
      exact (one_smul ℤ _).symm }

variable (k : Type) (ℓ : ℕ)

/-- **The defect does not depend on the step of the unit filtration**: all the `U(L,i)` have finite
index in `U(L,0) = 𝒪[L]ˣ`, so they have the same lattice defect. -/
theorem latticeDefect_unitFiltration_eq [CommRing k] [Fact ℓ.Prime] [NeZero (ℓ : L)] (i j : ℕ) :
    latticeDefect k (L ≃ₐ[K] L) ℓ (Additive (unitFiltration L i)) =
      latticeDefect k (L ≃ₐ[K] L) ℓ (Additive (unitFiltration L j)) := by
  suffices h : ∀ i, latticeDefect k (L ≃ₐ[K] L) ℓ (Additive (unitFiltration L i)) =
      latticeDefect k (L ≃ₐ[K] L) ℓ (Additive (unitFiltration L 0)) by rw [h i, h j]
  intro i
  have : ((unitFiltrationInclusionHom K L (Nat.zero_le i) :
      Additive (unitFiltration L i) →+ Additive (unitFiltration L 0)).range).FiniteIndex :=
    have := finiteIndex_toAddSubgroup_unitFiltration (L := L) i
    AddSubgroup.finiteIndex_of_le
      (H := Subgroup.toAddSubgroup ((unitFiltration L i).subgroupOf (unitFiltration L 0)))
      fun x hx ↦ ⟨Additive.ofMul ⟨_, hx⟩, rfl⟩
  exact latticeDefect_eq_of_finiteIndex k _ ℓ (unitFiltrationInclusionHom K L (Nat.zero_le i))
    (injective_unitFiltrationInclusionInt (Nat.zero_le i))

/-- **The lattice defect of `Lˣ`**: along the valuation sequence `0 → 𝒪[L]ˣ → Lˣ → ℤ → 0`, whose
quotient `ℤ` carries the trivial action, and the inclusions of finite index `U(L,i) ⊆ 𝒪[L]ˣ`,
the defect of `Lˣ` is that of any step `U(L,i)` of the unit filtration plus the class `1 = [k]` of
the trivial line. -/
theorem latticeDefect_units_eq_one_add [Field k] [Fact ℓ.Prime] [CharP k ℓ] [NeZero (ℓ : L)]
    (i : ℕ) :
    latticeDefect k (L ≃ₐ[K] L) ℓ (Additive Lˣ) =
      1 + latticeDefect k (L ≃ₐ[K] L) ℓ (Additive (unitFiltration L i)) := by
  rw [latticeDefect_add_of_exact k _ ℓ (unitFiltrationSubtypeHom K L 0) (valuationHom K L)
      (fun _ _ h ↦ Additive.toMul.injective (Subtype.ext (congrArg Additive.toMul h)))
      exact_unitFiltrationSubtypeInt_valuationInt surjective_valuationInt,
    latticeDefect_int_eq_one k _ ℓ (fun _ _ ↦ one_smul ℤ _), add_comm,
    latticeDefect_unitFiltration_eq K L k ℓ 0 i]

/-- **Away from the residue characteristic the principal units have zero defect**: if `ℓ` is a
unit of `𝒪[L]`, raising to the `ℓ`-th power is bijective on every positive-depth step
`U(L,i+1)`, so its reduction modulo `ℓ` and its `ℓ`-torsion both vanish. -/
theorem latticeDefect_unitFiltration_succ_eq_zero_of_isUnit [CommRing k]
    (hℓ : IsUnit (ℓ : 𝒪[L])) (i : ℕ) :
    haveI : NeZero (ℓ : L) := ⟨natCast_ne_zero_of_isUnit hℓ⟩
    haveI : NeZero ℓ := .of_neZero_natCast L
    latticeDefect k (L ≃ₐ[K] L) ℓ (Additive (unitFiltration L (i + 1))) = 0 := by
  have : NeZero (ℓ : L) := ⟨natCast_ne_zero_of_isUnit hℓ⟩
  have : NeZero ℓ := .of_neZero_natCast L
  refine latticeDefect_eq_zero_of_bijective_zsmul k _ ℓ _ ?_
  have h : (fun x : Additive (unitFiltration L (i + 1)) ↦ (ℓ : ℤ) • x) =
      Additive.ofMul ∘ powMonoidHom ℓ ∘ Additive.toMul := funext fun x ↦ by
    simp [natCast_zsmul]
  rw [h]
  exact Additive.ofMul.bijective.comp
    ((powMonoidHom_unitFiltration_succ_bijective_of_isUnit hℓ i).comp Additive.toMul.bijective)

/-- **The class of `Lˣ ⧸ (Lˣ)^ℓ`** in `G₀(k[Gal(L/K)])`, for `k` of characteristic `ℓ`: it is
`[k] + [μ_ℓ(L)] + latticeDefect (U(L,i))` for every step `U(L,i)` of the unit filtration, where
`μ_ℓ(L)` is the `ℓ`-torsion of `Lˣ`. -/
theorem reductionK0_quotSMulTop_units [Field k] [Fact ℓ.Prime] [CharP k ℓ] [NeZero (ℓ : L)]
    (i : ℕ) :
    reductionK0 k
        ((Representation.ofDistribMulAction ℤ (L ≃ₐ[K] L) (Additive Lˣ)).quotSMulTop ℓ) =
      1 + reductionK0 k
          ((Representation.ofDistribMulAction ℤ (L ≃ₐ[K] L) (Additive Lˣ)).torsionBy ℓ) +
        latticeDefect k (L ≃ₐ[K] L) ℓ (Additive (unitFiltration L i)) := by
  have h := latticeDefect_units_eq_one_add K L k ℓ i
  rw [latticeDefect_def] at h
  rw [sub_eq_iff_eq_add.mp h]
  abel

/-- **The class of `Lˣ ⧸ (Lˣ)^ℓ` away from the residue characteristic**: if `ℓ` is a unit of
`𝒪[L]`, then `[Lˣ ⧸ (Lˣ)^ℓ] = [k] + [μ_ℓ(L)]` in `G₀(k[Gal(L/K)])`. -/
theorem reductionK0_quotSMulTop_units_of_isUnit [Field k] [Fact ℓ.Prime] [CharP k ℓ]
    (hℓ : IsUnit (ℓ : 𝒪[L])) :
    haveI : NeZero (ℓ : L) := ⟨natCast_ne_zero_of_isUnit hℓ⟩
    reductionK0 k
        ((Representation.ofDistribMulAction ℤ (L ≃ₐ[K] L) (Additive Lˣ)).quotSMulTop ℓ) =
      1 + reductionK0 k
          ((Representation.ofDistribMulAction ℤ (L ≃ₐ[K] L) (Additive Lˣ)).torsionBy ℓ) := by
  have : NeZero (ℓ : L) := ⟨natCast_ne_zero_of_isUnit hℓ⟩
  rw [reductionK0_quotSMulTop_units K L k ℓ (0 + 1),
    latticeDefect_unitFiltration_succ_eq_zero_of_isUnit K L k ℓ hℓ 0, add_zero]

end Galois

end TauCeti

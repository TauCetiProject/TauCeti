/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.Weight.Basis
public import TauCeti.Algebra.Module.Lattice
public import TauCeti.Algebra.Module.Submodule.Finite
public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.LieAlgebra.Fundamental.Lattice
public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.LieAlgebra.SimplyConnectedModule
-- Non-public: these supply the inputs of the proofs, never the vocabulary of a statement.
import TauCeti.Algebra.Lie.DirectSum
import TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.Weight.DirectSum
import TauCeti.Algebra.Lie.UniversalEnveloping.Module

/-!
# The admissible lattice of the full-weight module

For a valid Dynkin type `t`, the **full-weight lattice** `TauCeti.DynkinType.scLattice t ht` is the
direct sum `⨁ᵢ U_ℤ · v⁺ᵢ` of the fundamental lattices inside the full-weight module
`V_sc(t) = ⨁ᵢ L(ϖᵢ)`: the vectors of `V_sc(t)` whose `i`-th component lies in the fundamental
lattice of `L(ϖᵢ)` for every `i`. It is the integral structure on `V_sc(t)` from which the simply
connected Chevalley group of type `t` is built.

This file proves that it is an admissible lattice and equips it with a weight basis whose weights
span the whole weight lattice:

* it is stable under the simple-generator Kostant form, because the enveloping algebra acts on a
  direct sum summand by summand;
* it is a full lattice: finitely generated over `ℤ`, and spanning `V_sc(t)` over `ℚ`;
* it lies in the span of the integral weight spaces of the Cartan generators `hⱼ`.

These are the inputs of `TauCeti.UniversalEnvelopingAlgebra.kostantWeightBasis`, which gives the
weight basis `TauCeti.DynkinType.scWeightBasis`, numbered by `Fin`. The weight
`TauCeti.DynkinType.scWeight x` of its `x`-th vector is read in the coordinates `μ ↦ (μ(hⱼ))ⱼ` of
`Fin t.rank → ℤ`, which are the fundamental-weight coordinates. The highest weight vector `v⁺ᵢ` of
the `i`-th summand lies in the lattice and has weight `ϖᵢ`, the `i`-th standard basis vector, so
these weights span `Fin t.rank → ℤ`. This is the spanning condition under which the torus of a
weight basis is a closed subgroup scheme of `GLₙ`
(`TauCeti.GeneralLinear.isClosedImmersion_weightTorus`).

## Main declarations

* `TauCeti.DynkinType.scLattice`: the direct sum of the fundamental lattices in `V_sc(t)`, with
  `TauCeti.DynkinType.mem_scLattice_iff` describing it componentwise.
* `TauCeti.DynkinType.representation_mem_scLattice`: its stability under the Kostant form.
* `TauCeti.DynkinType.instIsLatticeScLattice`: it is a full lattice in `V_sc(t)`.
* `TauCeti.DynkinType.mem_iSup_jointWeightSpace_of_mem_scLattice`: it lies in the span of the
  integral weight spaces.
* `TauCeti.DynkinType.scWeightBasis` and `TauCeti.DynkinType.scWeight`: its numbered weight basis
  and the weights of the basis vectors.
* `TauCeti.DynkinType.span_range_scWeight_eq_top`: those weights span `Fin t.rank → ℤ`.

## References

* R. Steinberg, *Lectures on Chevalley Groups*, AMS University Lecture Series 66 (2016),
  Chapter 2, Corollary 1 to Theorem 2, and Chapter 3, the remark after Lemma 27.
* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, GTM 9, §27.
-/

public section

namespace TauCeti.DynkinType

open _root_.DirectSum _root_.TauCeti.UniversalEnvelopingAlgebra

noncomputable section

variable (t : DynkinType) (ht : t.Valid)

/-! ### The lattice and its admissibility -/

/-- **The full-weight lattice** `⨁ᵢ U_ℤ · v⁺ᵢ` in `V_sc(t) = ⨁ᵢ L(ϖᵢ)`: the direct sum of the
fundamental lattices, that is, the vectors whose every component lies in the corresponding
fundamental lattice. -/
def scLattice : Submodule ℤ (t.scModule ht) :=
  (Submodule.pi Set.univ (t.fundamentalLattice ht)).map
    (((linearEquivFunOnFintype ℚ (Fin t.rank) (t.fundamentalModule ht)).symm :
      (∀ i, t.fundamentalModule ht i) →ₗ[ℚ] t.scModule ht).restrictScalars ℤ)

variable {t ht} in
/-- A vector of `V_sc(t)` lies in the full-weight lattice exactly when each of its components lies
in the corresponding fundamental lattice. -/
theorem mem_scLattice_iff {x : t.scModule ht} :
    x ∈ t.scLattice ht ↔ ∀ i, x i ∈ t.fundamentalLattice ht i := by
  rw [scLattice, Submodule.mem_map]
  refine ⟨?_, fun hx => ⟨x, fun i _ => hx i, by simp⟩⟩
  rintro ⟨y, hy, rfl⟩ i
  have h := congr_fun
    ((linearEquivFunOnFintype ℚ (Fin t.rank) (t.fundamentalModule ht)).apply_symm_apply y) i
  rw [linearEquivFunOnFintype_apply] at h
  rw [LinearMap.coe_restrictScalars, LinearEquiv.coe_coe, h]
  exact hy i (Set.mem_univ i)

variable {t ht} in
/-- A vector of the `i`-th summand lies in the full-weight lattice exactly when it lies in the
fundamental lattice of `L(ϖᵢ)`. -/
@[simp]
theorem lof_mem_scLattice_iff {i : Fin t.rank} {m : t.fundamentalModule ht i} :
    lof ℚ _ (t.fundamentalModule ht) i m ∈ t.scLattice ht ↔ m ∈ t.fundamentalLattice ht i := by
  rw [mem_scLattice_iff]
  refine ⟨fun h => by simpa using h i, fun hm j => ?_⟩
  by_cases hij : i = j
  · subst hij
    simpa using hm
  · rw [lof_eq_of, of_eq_of_ne i j m (Ne.symm hij)]
    exact zero_mem _

/-- **The full-weight lattice is stable under the Kostant form**: the enveloping algebra acts on
`V_sc(t)` summand by summand, and each fundamental lattice is stable. -/
theorem representation_mem_scLattice
    {u : _root_.UniversalEnvelopingAlgebra ℚ (t.lieAlgebra ht)} (hu : u ∈ t.kostantForm ht)
    {x : t.scModule ht} (hx : x ∈ t.scLattice ht) :
    representation ℚ (t.lieAlgebra ht) (t.scModule ht) u x ∈ t.scLattice ht := by
  rw [mem_scLattice_iff] at hx ⊢
  intro i
  have h := map_representation ℚ (t.lieAlgebra ht) (t.scModule ht) (t.fundamentalModule ht i)
    (lieModuleComponent ℚ (Fin t.rank) (t.lieAlgebra ht) (t.fundamentalModule ht) i) u x
  simp only [lieModuleComponent_apply] at h
  rw [h]
  exact t.representation_mem_fundamentalLattice ht hu (hx i)

/-- **The full-weight lattice is a full lattice in `V_sc(t)`**: it is finitely generated over `ℤ`
and spans `V_sc(t)` over `ℚ`, being the direct sum of full lattices of the summands. -/
instance instIsLatticeScLattice : (t.scLattice ht).IsLattice ℚ :=
  Submodule.isLattice_map _ _
    (linearEquivFunOnFintype ℚ (Fin t.rank) (t.fundamentalModule ht)).symm.surjective

/-- **The full-weight lattice lies in the span of the integral weight spaces** of the Cartan
generators: each component does, and the inclusion of a summand preserves weight vectors
(`TauCeti.UniversalEnvelopingAlgebra.lof_mem_iSup_jointWeightSpace`). -/
theorem mem_iSup_jointWeightSpace_of_mem_scLattice {x : t.scModule ht}
    (hx : x ∈ t.scLattice ht) :
    x ∈ ⨆ μ : Fin t.rank → ℤ, jointWeightSpace (t.lieBasis ht).h
      (representation ℚ (t.lieAlgebra ht) (t.scModule ht)) μ := by
  rw [← sum_univ_of x]
  refine Submodule.sum_mem _ fun i _ => ?_
  rw [← lof_eq_of ℚ]
  exact lof_mem_iSup_jointWeightSpace _
    (t.mem_iSup_jointWeightSpace_of_mem_fundamentalLattice ht (mem_scLattice_iff.mp hx i))

/-! ### The weight basis -/

/-- **The full-weight lattice is stable under the Kostant form**, in the shape
`TauCeti.UniversalEnvelopingAlgebra.kostantWeightBasis` consumes: the generic Kostant form of the
pinned raising, lowering and Cartan generators, acting on the underlying additive subgroup. -/
theorem kostantForm_apply_mem_scLattice :
    ∀ u ∈ UniversalEnvelopingAlgebra.kostantForm (LieAlgebra.Basis.rootGenerator (t.lieBasis ht))
        (t.lieBasis ht).h, ∀ x ∈ (t.scLattice ht).toAddSubgroup,
      representation ℚ (t.lieAlgebra ht) (t.scModule ht) u x ∈ (t.scLattice ht).toAddSubgroup :=
  fun _ hu _ hx => t.representation_mem_scLattice ht
    (by rwa [kostantForm_def, LieAlgebra.Basis.kostantForm_def]) hx

/-- The number of vectors of the weight basis of the full-weight lattice, that is, the number of
index values of `TauCeti.UniversalEnvelopingAlgebra.kostantWeightBasis` for it. -/
noncomputable abbrev scWeightBasisCard : ℕ :=
  Nat.card (Σ μ : Fin t.rank → ℤ, Module.Free.ChooseBasisIndex ℤ
    (weightSublattice (t.lieBasis ht).h (representation ℚ (t.lieAlgebra ht) (t.scModule ht))
      (t.scLattice ht).toAddSubgroup μ))

/-- **The weight basis of the full-weight lattice**, numbered by `Fin`: the Kostant weight basis of
the admissible lattice `scLattice`, in the shape in which the split torus, the matrix coordinates
and the generated group scheme read a basis. -/
noncomputable def scWeightBasis :
    Module.Basis (Fin (t.scWeightBasisCard ht)) ℤ (t.scLattice ht).toAddSubgroup :=
  kostantWeightBasisFin (LieAlgebra.Basis.rootGenerator (t.lieBasis ht)) (t.lieBasis ht).h
    (representation ℚ (t.lieAlgebra ht) (t.scModule ht)) (t.scLattice ht).toAddSubgroup
    (t.kostantForm_apply_mem_scLattice ht)
    (fun x => t.mem_iSup_jointWeightSpace_of_mem_scLattice ht x.2)

/-- The defining equation of `TauCeti.DynkinType.scWeightBasis`, through which
`TauCeti.UniversalEnvelopingAlgebra.kostantWeightBasisFin_apply` and the rest of the numbered-basis
API apply to it. -/
theorem scWeightBasis_def :
    t.scWeightBasis ht =
      kostantWeightBasisFin (LieAlgebra.Basis.rootGenerator (t.lieBasis ht)) (t.lieBasis ht).h
        (representation ℚ (t.lieAlgebra ht) (t.scModule ht)) (t.scLattice ht).toAddSubgroup
        (t.kostantForm_apply_mem_scLattice ht)
        (fun x => t.mem_iSup_jointWeightSpace_of_mem_scLattice ht x.2) :=
  (rfl)

/-- The weight of each vector of the weight basis of the full-weight lattice, in the
fundamental-weight coordinates `μ ↦ (μ(hⱼ))ⱼ`. -/
noncomputable def scWeight : Fin (t.scWeightBasisCard ht) → Fin t.rank → ℤ :=
  kostantWeightFin (LieAlgebra.Basis.rootGenerator (t.lieBasis ht)) (t.lieBasis ht).h
    (representation ℚ (t.lieAlgebra ht) (t.scModule ht)) (t.scLattice ht).toAddSubgroup
    (t.kostantForm_apply_mem_scLattice ht)
    (fun x => t.mem_iSup_jointWeightSpace_of_mem_scLattice ht x.2)

/-- The defining equation of `TauCeti.DynkinType.scWeight`. -/
theorem scWeight_def :
    t.scWeight ht =
      kostantWeightFin (LieAlgebra.Basis.rootGenerator (t.lieBasis ht)) (t.lieBasis ht).h
        (representation ℚ (t.lieAlgebra ht) (t.scModule ht)) (t.scLattice ht).toAddSubgroup
        (t.kostantForm_apply_mem_scLattice ht)
        (fun x => t.mem_iSup_jointWeightSpace_of_mem_scLattice ht x.2) :=
  (rfl)

/-- **The weight basis of the full-weight lattice consists of weight vectors**: the Cartan
generator `hⱼ` acts on the `x`-th basis vector by the scalar `scWeight x j`. -/
theorem isCartanWeightVector_scWeightBasis (x : Fin (t.scWeightBasisCard ht)) :
    IsCartanWeightVector (t.lieBasis ht).h (representation ℚ (t.lieAlgebra ht) (t.scModule ht))
      (t.scWeight ht x) ((t.scWeightBasis ht x : (t.scLattice ht).toAddSubgroup) : t.scModule ht) :=
  isCartanWeightVector_kostantWeightBasisFin _ _ _ _ _ _ x

/-- **The weights of the full-weight lattice span the weight lattice**: the weights carried by the
weight basis span `Fin t.rank → ℤ` over `ℤ`, since the highest weight vector of the `i`-th summand
lies in the lattice with weight the `i`-th standard basis vector. This is the spanning condition
of `TauCeti.GeneralLinear.isClosedImmersion_weightTorus`. -/
theorem span_range_scWeight_eq_top :
    Submodule.span ℤ (Set.range (t.scWeight ht)) = ⊤ := by
  refine eq_top_iff.mpr
    ((Pi.basisFun ℤ (Fin t.rank)).span_eq.ge.trans (Submodule.span_mono ?_))
  rintro _ ⟨i, rfl⟩
  rw [Pi.basisFun_apply, scWeight_def, mem_range_kostantWeightFin_iff, Submodule.ne_bot_iff]
  have hl : lof ℚ _ (t.fundamentalModule ht) i (t.fundamentalModuleGenerator ht i) ∈
      (t.scLattice ht).toAddSubgroup :=
    lof_mem_scLattice_iff.mpr (t.fundamentalModuleGenerator_mem_fundamentalLattice ht i)
  refine ⟨⟨_, hl⟩, ?_, ?_⟩
  · rw [mem_weightSublattice_iff]
    exact isCartanWeightVector_lof (t.isCartanWeightVector_fundamentalModuleGenerator ht i)
  · rw [ne_eq, AddSubgroup.mk_eq_zero]
    exact (t.isHighestWeightVector_lof_fundamentalModuleGenerator ht i).ne_zero

end

end TauCeti.DynkinType

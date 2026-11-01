/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Module.Submodule.Finite
public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.LieAlgebra.Fundamental.Lattice
public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.LieAlgebra.SimplyConnected.Module
-- Non-public: these supply the inputs of the proofs, never the vocabulary of a statement.
import TauCeti.Algebra.Lie.UniversalEnveloping.Module
import TauCeti.Algebra.Module.Lattice

/-!
# The admissible lattice of the full-weight module

For a valid Dynkin type `t`, the **full-weight lattice** `TauCeti.DynkinType.scLattice t ht` is
the orbit `U_ℤ · {v⁺ᵢ}` of the highest weight vectors of the summands of the full-weight module
`V_sc(t) = ⨁ᵢ L(ϖᵢ)` under the simple-generator Kostant form `TauCeti.DynkinType.kostantForm` of
the pinned rational Lie algebra. Since the Kostant form acts summand by summand, it is the direct
sum `⨁ᵢ U_ℤ · v⁺ᵢ` of the fundamental lattices `TauCeti.DynkinType.fundamentalLattice`: an element
of `V_sc(t)` lies in it exactly when each of its components lies in the corresponding fundamental
lattice.

It is an admissible lattice: stable under the Kostant form, finitely generated over `ℤ`, spanning
`V_sc(t)` over `ℚ`, and contained in the span of the integral weight spaces of the Cartan
generators. `TauCeti.UniversalEnvelopingAlgebra.kostantWeightBasisFin` therefore gives it a
`Fin`-indexed basis of weight vectors, `TauCeti.DynkinType.scWeightBasis`, with weights
`TauCeti.DynkinType.scWeight` read against the Bourbaki-numbered Cartan generators `hⱼ`, that is,
in the coordinates of the fundamental weights. These are the module, lattice, weight basis and
weights from which the simply connected Chevalley group of type `t` is built.

The weights of this basis span the whole lattice `Fin t.rank → ℤ`: the highest weight vector
`v⁺ᵢ` of the `i`-th summand is a nonzero lattice vector of weight `ϖᵢ`, whose coordinate vector is
the `i`-th standard basis vector (Steinberg, Chapter 3, the remark after Lemma 27). This is the
span hypothesis of `TauCeti.GeneralLinear.isClosedImmersion_weightTorus`, under which the weight
torus of `V_sc(t)` is a closed subgroup of `GLₙ` with the full weight lattice as character lattice.

## Main declarations

* `TauCeti.DynkinType.scLattice`: the orbit `U_ℤ · {v⁺ᵢ}` in `V_sc(t)`.
* `TauCeti.DynkinType.representation_mem_scLattice`: its stability under the Kostant form.
* `TauCeti.DynkinType.mem_scLattice_iff` and `TauCeti.DynkinType.lof_mem_scLattice_iff`: it is the
  direct sum of the fundamental lattices.
* `TauCeti.DynkinType.instIsLatticeScLattice`: it is a full lattice in `V_sc(t)`.
* `TauCeti.DynkinType.mem_iSup_jointWeightSpace_of_mem_scLattice`: it lies in the span of the
  integral weight spaces.
* `TauCeti.DynkinType.scWeightBasis` and `TauCeti.DynkinType.scWeight`: its `Fin`-indexed weight
  basis and the weights of the basis vectors.
* `TauCeti.DynkinType.span_range_scWeight_eq_top`: these weights span `Fin t.rank → ℤ`.

## References

* R. Steinberg, *Lectures on Chevalley Groups*, AMS University Lecture Series 66 (2016),
  Chapter 2, Corollary 1 to Theorem 2, and Chapter 3, the remark after Lemma 27.
* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, GTM 9, §27.1.
-/

public section

namespace TauCeti.DynkinType

open Set DirectSum _root_.TauCeti.UniversalEnvelopingAlgebra

noncomputable section

variable (t : DynkinType) (ht : t.Valid)

/-- **The full-weight lattice** `U_ℤ · {v⁺ᵢ}`: the integral orbit of the highest weight vectors of
the summands of the full-weight module `V_sc(t) = ⨁ᵢ L(ϖᵢ)` under the simple-generator Kostant
form of the pinned rational Lie algebra. It is the direct sum of the fundamental lattices
(`TauCeti.DynkinType.mem_scLattice_iff`). -/
def scLattice : Submodule ℤ (t.scModule ht) :=
  Subring.orbitOfRep (t.kostantForm ht) (representation ℚ (t.lieAlgebra ht) (t.scModule ht))
    (range fun i => lof ℚ _ (t.fundamentalModule ht) i (t.fundamentalModuleGenerator ht i))

/-- The full-weight lattice is the represented orbit of the summand highest weight vectors. -/
theorem scLattice_def :
    t.scLattice ht = Subring.orbitOfRep (t.kostantForm ht)
      (representation ℚ (t.lieAlgebra ht) (t.scModule ht))
      (range fun i => lof ℚ _ (t.fundamentalModule ht) i (t.fundamentalModuleGenerator ht i)) :=
  (rfl)

/-- The highest weight vector `v⁺ᵢ`, placed in the `i`-th summand, lies in the full-weight
lattice. -/
theorem lof_fundamentalModuleGenerator_mem_scLattice (i : Fin t.rank) :
    lof ℚ _ (t.fundamentalModule ht) i (t.fundamentalModuleGenerator ht i) ∈ t.scLattice ht :=
  Subring.subset_orbitOfRep _ _ _ (mem_range_self i)

/-- **The full-weight lattice is stable under the Kostant form.** -/
theorem representation_mem_scLattice
    {u : _root_.UniversalEnvelopingAlgebra ℚ (t.lieAlgebra ht)} (hu : u ∈ t.kostantForm ht)
    {x : t.scModule ht} (hx : x ∈ t.scLattice ht) :
    representation ℚ (t.lieAlgebra ht) (t.scModule ht) u x ∈ t.scLattice ht :=
  Subring.apply_mem_orbitOfRep_of_mem _ _ _ hu hx

/-- Each component of a vector of the full-weight lattice lies in the corresponding fundamental
lattice. -/
private theorem apply_mem_fundamentalLattice_of_mem_scLattice {x : t.scModule ht}
    (hx : x ∈ t.scLattice ht) (i : Fin t.rank) : x i ∈ t.fundamentalLattice ht i := by
  rw [scLattice_def, Subring.orbitOfRep_def] at hx
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨u, hu, _, ⟨j, rfl⟩, rfl⟩ := hy
    rw [representation_lof]
    by_cases hji : j = i
    · subst hji
      rw [lof_apply]
      exact t.representation_mem_fundamentalLattice ht hu
        (t.fundamentalModuleGenerator_mem_fundamentalLattice ht j)
    · simp [lof_eq_of ℚ, of_apply, hji]
  | zero => exact zero_mem _
  | add y z _ _ hy hz =>
    rw [DirectSum.add_apply]
    exact add_mem hy hz
  | smul n y _ hy =>
    rw [DirectSum.smul_apply]
    exact Submodule.smul_mem _ n hy

/-- A vector of the `i`-th fundamental lattice, placed in the `i`-th summand, lies in the
full-weight lattice. -/
private theorem lof_mem_scLattice {i : Fin t.rank} {x : t.fundamentalModule ht i}
    (hx : x ∈ t.fundamentalLattice ht i) :
    lof ℚ _ (t.fundamentalModule ht) i x ∈ t.scLattice ht := by
  rw [fundamentalLattice_def, Subring.orbitOfRep_def] at hx
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨u, hu, _, rfl, rfl⟩ := hy
    rw [← representation_lof]
    exact t.representation_mem_scLattice ht hu (t.lof_fundamentalModuleGenerator_mem_scLattice ht i)
  | zero =>
    rw [map_zero]
    exact zero_mem _
  | add y z _ _ hy hz =>
    rw [map_add]
    exact add_mem hy hz
  | smul n y _ hy =>
    rw [map_zsmul]
    exact Submodule.smul_mem _ n hy

/-- **The full-weight lattice is the direct sum of the fundamental lattices**: a vector of
`V_sc(t)` lies in it exactly when each of its components lies in the corresponding fundamental
lattice. -/
theorem mem_scLattice_iff {x : t.scModule ht} :
    x ∈ t.scLattice ht ↔ ∀ i, x i ∈ t.fundamentalLattice ht i := by
  refine ⟨t.apply_mem_fundamentalLattice_of_mem_scLattice ht, fun hx => ?_⟩
  rw [← sum_univ_of x]
  exact sum_mem fun i _ => by
    rw [← lof_eq_of ℚ]
    exact t.lof_mem_scLattice ht (hx i)

/-- A vector of the `i`-th summand lies in the full-weight lattice exactly when it lies in the
`i`-th fundamental lattice. -/
@[simp]
theorem lof_mem_scLattice_iff {i : Fin t.rank} {x : t.fundamentalModule ht i} :
    lof ℚ _ (t.fundamentalModule ht) i x ∈ t.scLattice ht ↔ x ∈ t.fundamentalLattice ht i := by
  refine ⟨fun hx => ?_, t.lof_mem_scLattice ht⟩
  simpa using t.apply_mem_fundamentalLattice_of_mem_scLattice ht hx i

/-- A weight vector of the `i`-th summand, placed in the `i`-th summand, is a weight vector of
`V_sc(t)` of the same weight. -/
private theorem isCartanWeightVector_lof {i : Fin t.rank} {μ : Fin t.rank → ℤ}
    {x : t.fundamentalModule ht i}
    (hx : IsCartanWeightVector (t.lieBasis ht).h
      (representation ℚ (t.lieAlgebra ht) (t.fundamentalModule ht i)) μ x) :
    IsCartanWeightVector (t.lieBasis ht).h (representation ℚ (t.lieAlgebra ht) (t.scModule ht)) μ
      (lof ℚ _ (t.fundamentalModule ht) i x) :=
  (isCartanWeightVector_iff _ _).2 fun j => by
    have hj := (isCartanWeightVector_iff _ _).1 hx j
    simp only [representation_ι_apply] at hj
    rw [representation_lof]
    simp only [representation_ι_apply, hj, map_smul]

/-- The full-weight lattice is the supremum of the images of the fundamental lattices under the
inclusions of the summands. -/
private theorem scLattice_eq_iSup :
    t.scLattice ht = ⨆ i, (t.fundamentalLattice ht i).map
      ((lof ℚ _ (t.fundamentalModule ht) i).restrictScalars ℤ) := by
  refine le_antisymm (fun x hx => ?_)
    (iSup_le fun i => Submodule.map_le_iff_le_comap.2 fun y hy => ?_)
  · rw [← sum_univ_of x]
    exact sum_mem fun i _ => Submodule.mem_iSup_of_mem i
      ⟨x i, (t.mem_scLattice_iff ht).1 hx i, (lof_eq_of ℚ _ _ i (x i)).symm⟩
  · exact (t.lof_mem_scLattice_iff ht).2 hy

/-- The full-weight lattice is the product of the fundamental lattices, carried to the direct sum
by `DirectSum.linearEquivFunOnFintype`. -/
private theorem scLattice_eq_map_pi :
    t.scLattice ht = (Submodule.pi univ (t.fundamentalLattice ht)).map
      ((linearEquivFunOnFintype ℚ _ (t.fundamentalModule ht)).symm.toLinearMap.restrictScalars
        ℤ) := by
  refine le_antisymm (fun x hx => ?_) (Submodule.map_le_iff_le_comap.2 fun y hy => ?_)
  · exact ⟨fun i => x i, fun i _ => (t.mem_scLattice_iff ht).1 hx i,
      (linearEquivFunOnFintype ℚ _ _).symm_apply_apply x⟩
  · exact (t.mem_scLattice_iff ht).2 fun i => hy i (mem_univ i)

/-- **The full-weight lattice is a full lattice in `V_sc(t)`**: it is the image of the product of
the fundamental lattices, each a full lattice in its summand. -/
instance instIsLatticeScLattice : Submodule.IsLattice ℚ (t.scLattice ht) := by
  rw [scLattice_eq_map_pi]
  exact Submodule.isLattice_map _ _ (linearEquivFunOnFintype ℚ _ _).symm.surjective

/-- **The full-weight lattice lies in the span of the integral weight spaces** of the Cartan
generators. With finite generation and stability under the Kostant form, this is what
`TauCeti.UniversalEnvelopingAlgebra.kostantWeightBasis` needs to give the full-weight lattice a
basis of weight vectors. -/
theorem mem_iSup_jointWeightSpace_of_mem_scLattice {x : t.scModule ht}
    (hx : x ∈ t.scLattice ht) :
    x ∈ ⨆ μ : Fin t.rank → ℤ, jointWeightSpace (t.lieBasis ht).h
      (representation ℚ (t.lieAlgebra ht) (t.scModule ht)) μ := by
  rw [scLattice_eq_iSup] at hx
  refine Submodule.iSup_induction _ (motive := (· ∈ ⨆ μ : Fin t.rank → ℤ, jointWeightSpace
    (t.lieBasis ht).h (representation ℚ (t.lieAlgebra ht) (t.scModule ht)) μ)) hx
    (fun i y hy => ?_) (zero_mem _) fun _ _ => add_mem
  obtain ⟨z, hz, rfl⟩ := hy
  -- `z` lies in the span of the integral weight spaces of the `i`-th summand, and the inclusion of
  -- the summand sends each of them into the same weight space of `V_sc(t)`.
  have hmap := Submodule.mem_map_of_mem (f := lof ℚ _ (t.fundamentalModule ht) i)
    (t.mem_iSup_jointWeightSpace_of_mem_fundamentalLattice ht hz)
  rw [Submodule.map_iSup] at hmap
  refine iSup_mono (fun μ => Submodule.map_le_iff_le_comap.2 fun w hw => ?_) hmap
  exact (mem_jointWeightSpace_iff _ _).2
    (t.isCartanWeightVector_lof ht ((mem_jointWeightSpace_iff _ _).1 hw))

/-! ### The weight basis -/

/-- The Kostant-form stability of the full-weight lattice, in the shape
`TauCeti.UniversalEnvelopingAlgebra.kostantWeightBasis` consumes. -/
theorem kostantForm_apply_mem_scLattice :
    ∀ u ∈ TauCeti.UniversalEnvelopingAlgebra.kostantForm (t.lieBasis ht).rootGenerator
        (t.lieBasis ht).h,
      ∀ x ∈ (t.scLattice ht).toAddSubgroup,
        representation ℚ (t.lieAlgebra ht) (t.scModule ht) u x ∈ (t.scLattice ht).toAddSubgroup :=
  fun _ hu _ hx => t.representation_mem_scLattice ht
    (by rwa [kostantForm_def, LieAlgebra.Basis.kostantForm_def]) hx

/-- The number of vectors of the weight basis of the full-weight lattice: the cardinality of the
index of `TauCeti.UniversalEnvelopingAlgebra.kostantWeightBasis`, which is the rank of the lattice
(`TauCeti.DynkinType.scWeightBasisCard_eq_finrank`). -/
noncomputable abbrev scWeightBasisCard : ℕ :=
  Nat.card (Σ μ : Fin t.rank → ℤ, Module.Free.ChooseBasisIndex ℤ
    (weightSublattice (t.lieBasis ht).h (representation ℚ (t.lieAlgebra ht) (t.scModule ht))
      (t.scLattice ht).toAddSubgroup μ))

/-- **The weight basis of the full-weight lattice**, numbered by `Fin`: the Kostant weight basis
`TauCeti.UniversalEnvelopingAlgebra.kostantWeightBasisFin` of `TauCeti.DynkinType.scLattice`. It
consists of weight vectors for the Cartan generators `hⱼ`
(`TauCeti.DynkinType.isCartanWeightVector_scWeightBasis`); the bases of the individual weight
sublattices are chosen. -/
def scWeightBasis :
    Module.Basis (Fin (t.scWeightBasisCard ht)) ℤ (t.scLattice ht).toAddSubgroup :=
  kostantWeightBasisFin (t.lieBasis ht).rootGenerator (t.lieBasis ht).h _ _
    (t.kostantForm_apply_mem_scLattice ht)
    fun x => t.mem_iSup_jointWeightSpace_of_mem_scLattice ht x.2

/-- The defining equation of `TauCeti.DynkinType.scWeightBasis`, through which the
numbered-weight-basis API applies to it. -/
theorem scWeightBasis_def :
    t.scWeightBasis ht =
      kostantWeightBasisFin (t.lieBasis ht).rootGenerator (t.lieBasis ht).h
        (representation ℚ (t.lieAlgebra ht) (t.scModule ht)) (t.scLattice ht).toAddSubgroup
        (t.kostantForm_apply_mem_scLattice ht)
    fun x => t.mem_iSup_jointWeightSpace_of_mem_scLattice ht x.2 :=
  (rfl)

/-- **The weights of the full-weight lattice**: `scWeight x` is the weight of the `x`-th vector of
`TauCeti.DynkinType.scWeightBasis` against the Bourbaki-numbered Cartan generators `hⱼ`, that is,
its coordinate vector in the fundamental weights. -/
def scWeight : Fin (t.scWeightBasisCard ht) → Fin t.rank → ℤ :=
  kostantWeightFin (t.lieBasis ht).rootGenerator (t.lieBasis ht).h _ _
    (t.kostantForm_apply_mem_scLattice ht)
    fun x => t.mem_iSup_jointWeightSpace_of_mem_scLattice ht x.2

/-- The defining equation of `TauCeti.DynkinType.scWeight`. -/
theorem scWeight_def :
    t.scWeight ht =
      kostantWeightFin (t.lieBasis ht).rootGenerator (t.lieBasis ht).h
        (representation ℚ (t.lieAlgebra ht) (t.scModule ht)) (t.scLattice ht).toAddSubgroup
        (t.kostantForm_apply_mem_scLattice ht)
    fun x => t.mem_iSup_jointWeightSpace_of_mem_scLattice ht x.2 :=
  (rfl)

/-- **The weight basis consists of weight vectors**: the `x`-th vector of
`TauCeti.DynkinType.scWeightBasis` is a weight vector of weight `scWeight x` for the Cartan
generators `hⱼ`. -/
theorem isCartanWeightVector_scWeightBasis (x : Fin (t.scWeightBasisCard ht)) :
    IsCartanWeightVector (t.lieBasis ht).h (representation ℚ (t.lieAlgebra ht) (t.scModule ht))
      (t.scWeight ht x) ((t.scWeightBasis ht x : (t.scLattice ht).toAddSubgroup) : t.scModule ht) :=
  isCartanWeightVector_kostantWeightBasisFin _ _ _ _ _ _ x

/-- The rank of the full-weight lattice is the number of vectors of its weight basis. -/
theorem scWeightBasisCard_eq_finrank :
    t.scWeightBasisCard ht = Module.finrank ℤ (t.scLattice ht).toAddSubgroup :=
  nat_card_kostantWeightBasis_index_eq_finrank _ _ _ _
    (t.kostantForm_apply_mem_scLattice ht)
    fun x => t.mem_iSup_jointWeightSpace_of_mem_scLattice ht x.2

/-- **Each fundamental weight is a weight of the weight basis**: its coordinate vector, the `i`-th
standard basis vector of `Fin t.rank → ℤ`, is `scWeight x` for some `x`, since `v⁺ᵢ` is a nonzero
vector of the full-weight lattice of weight `ϖᵢ`. -/
theorem single_mem_range_scWeight (i : Fin t.rank) :
    (Pi.single i 1 : Fin t.rank → ℤ) ∈ range (t.scWeight ht) := by
  rw [scWeight_def, mem_range_kostantWeightFin_iff]
  refine (Submodule.ne_bot_iff _).2 ⟨⟨_, t.lof_fundamentalModuleGenerator_mem_scLattice ht i⟩,
    (mem_weightSublattice_iff _ _ _).2
      (t.isCartanWeightVector_lof ht (t.isCartanWeightVector_fundamentalModuleGenerator ht i)),
    fun h => ?_⟩
  exact (t.isHighestWeightVector_lof_fundamentalModuleGenerator ht i).ne_zero
    (congrArg Subtype.val h)

/-- **The weights of the full-weight lattice span the weight lattice**: over `ℤ`, the weights of
`TauCeti.DynkinType.scWeightBasis`, written in the coordinates of the fundamental weights, span
all of `Fin t.rank → ℤ`. -/
theorem span_range_scWeight_eq_top :
    Submodule.span ℤ (range (t.scWeight ht)) = ⊤ := by
  refine top_unique ((Pi.basisFun ℤ (Fin t.rank)).span_eq.ge.trans (Submodule.span_mono ?_))
  rintro _ ⟨i, rfl⟩
  rw [Pi.basisFun_apply]
  exact t.single_mem_range_scWeight ht i

end

end TauCeti.DynkinType

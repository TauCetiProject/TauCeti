/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.BesselPotential.Inclusion
public import TauCeti.Geometry.Manifold.VectorBundle.Sobolev.BesselPotential
import TauCeti.Analysis.Distribution.Sobolev
import TauCeti.Analysis.Normed.Operator.Banach
import TauCeti.Analysis.Sobolev.BesselPotential.Besov

/-!
# Bessel-potential spaces `H^{s,p}` of distributions on bundle tests

Let `V → M` be a smooth real vector bundle with model fibre `F`, and let `A` be a square chart
partition of `V` (`TauCeti.SquareChartPartition`): finitely many charts `cᵢ` with frames `tᵢ` over
their sources and cutoffs `χᵢ` with `∑ᵢ χᵢ² = 1`. A real functional `T` on the bundle tests
`TauCeti.BundleTest I F V`, for instance a distributional section `TauCeti.BundleDistribution`
of a bundle whose dual density bundle is `V`, has finitely many **localizations** `χᵢ Tᵢⱼ`
(`TauCeti.SquareChartPartition.localization`): compactly supported tempered distributions on the
model space `E`, one for each chart and each vector of the fixed basis of `F`. They determine `T`
through the reconstruction (`TauCeti.SquareChartPartition.reconstruction_localization`).

This file builds the **Bessel-potential spaces `H^{s,p}`** of such functionals, for real `s` and
`1 ≤ p ≤ ∞`, from Mathlib's Euclidean Bessel-potential spaces `H^{s,p}(E, ℂ)`, in the same way as
the Sobolev spaces `TauCeti.SquareChartPartition.sobolevSpace` (the case `p = 2`, with a Hilbert
norm) and the Besov spaces `TauCeti.SquareChartPartition.besovSpace` are built.

* `T` is **`H^{s,p}` with respect to `A`** (`TauCeti.SquareChartPartition.MemBesselPotential`)
  when all its localizations lie in `H^{s,p}(E, ℂ)`. For `p = 2` this is being `H^s` with respect
  to `A` (`TauCeti.SquareChartPartition.memBesselPotential_two_iff_memSobolev`), and for
  `1 < p < ∞` every functional is `H^{s,p}` for some `s`
  (`TauCeti.SquareChartPartition.exists_memBesselPotential`).
* The **Bessel-potential space** `TauCeti.SquareChartPartition.besselPotentialSpace` is the real
  subspace of the tuples `(uᵢⱼ)` of elements of `H^{s,p}(E, ℂ)` that are reproduced by localizing
  their reconstruction, that is, the tuples of localizations of a functional on bundle tests. It is
  closed in the product (`TauCeti.SquareChartPartition.isClosed_besselPotentialSpace`), so it is a
  Banach space, with the norm `‖T‖ = maxᵢⱼ ‖χᵢ Tᵢⱼ‖_{H^{s,p}}` of the product
  (`TauCeti.SquareChartPartition.norm_ofMemBesselPotential_le_iff`). It is linearly equivalent to
  the functionals that are `H^{s,p}` with respect to `A`
  (`TauCeti.SquareChartPartition.besselPotentialSpaceEquiv`), through the reconstruction
  `TauCeti.SquareChartPartition.besselPotentialToDistribution`. For `p = 2` it is isomorphic to the
  Sobolev space `H^s` of the same partition, whose norm is the `ℓ²` and not the maximum norm of the
  components (`TauCeti.SquareChartPartition.besselPotentialSpaceTwoEquivSobolevSpace`).

**Independence of the partition.** Let `1 < p < ∞`. Then `T` is `H^{s,p}` with respect to `A`
exactly when it is `H^{s,p}` near every point of `M`
(`TauCeti.SquareChartPartition.memBesselPotential_iff_forall_isLocallyMemSobolevAt`), in the sense
of `TauCeti.BundleTest.IsLocallyMemSobolevAt`, which does not depend on charts and frames. Indeed,
`χᵢ Tᵢⱼ ∈ H^{s,p}` makes `Tᵢⱼ` locally `H^{s,p}` wherever `χᵢ ≠ 0`
(`Distribution.isLocallyMemSobolevAt_iff_exists_memSobolev_cutoffTempered`), and every point has
such an `i` since `∑ᵢ χᵢ² = 1`; conversely, if all `Tᵢⱼ` are locally `H^{s,p}` on the support of
`χᵢ`, then `χᵢ Tᵢⱼ ∈ H^{s,p}`
(`Distribution.memSobolev_cutoffTempered_of_forall_isLocallyMemSobolevAt`). So two square chart
partitions of `V` have the same `H^{s,p}` functionals
(`TauCeti.SquareChartPartition.memBesselPotential_iff_memBesselPotential`). Their
Bessel-potential spaces are then isomorphic as Banach spaces
(`TauCeti.SquareChartPartition.besselPotentialSpaceCongr`), so that their norms are equivalent
(`TauCeti.SquareChartPartition.exists_norm_ofMemBesselPotential_le`): the identification is a
linear bijection between Banach spaces whose graph is closed, because the represented functional
depends continuously on an element of either space, test by test, and the closed graph theorem
applies. The invariance of local `H^{s,p}` regularity under changes of variables, which needs
`1 < p < ∞`, is the only analytic input.

## Main declarations

* `TauCeti.SquareChartPartition.MemBesselPotential`: `H^{s,p}` regularity with respect to the
  partition, with `TauCeti.SquareChartPartition.exists_memBesselPotential` (finite order) and
  `TauCeti.SquareChartPartition.memBesselPotential_two_iff_memSobolev`.
* `TauCeti.SquareChartPartition.besselPotentialSpace`: the Bessel-potential space, with
  `TauCeti.SquareChartPartition.isClosed_besselPotentialSpace` and its `CompleteSpace` instance.
* `TauCeti.SquareChartPartition.besselPotentialToDistribution`,
  `TauCeti.SquareChartPartition.ofMemBesselPotential`,
  `TauCeti.SquareChartPartition.range_besselPotentialToDistribution` and
  `TauCeti.SquareChartPartition.besselPotentialSpaceEquiv`: the Bessel-potential space represents
  exactly the functionals that are `H^{s,p}` with respect to the partition.
* `TauCeti.SquareChartPartition.besselPotentialInclusion`: the inclusion `H^{s,p} ⊆ H^{r,p}` for
  `r ≤ s`, and `TauCeti.SquareChartPartition.besselPotentialSpaceTwoEquivSobolevSpace`, the
  comparison with the Sobolev space for `p = 2`.
* `TauCeti.SquareChartPartition.memBesselPotential_iff_forall_isLocallyMemSobolevAt` and
  `TauCeti.SquareChartPartition.memBesselPotential_iff_memBesselPotential`: for `1 < p < ∞`, being
  `H^{s,p}` with respect to a partition is local `H^{s,p}` regularity, and does not depend on the
  partition.
* `TauCeti.SquareChartPartition.besselPotentialSpaceCongr` and
  `TauCeti.SquareChartPartition.exists_norm_ofMemBesselPotential_le`: for `1 < p < ∞`, the
  Bessel-potential spaces of two partitions are isomorphic Banach spaces, and their norms are
  equivalent.

## References

* H. Triebel, *Theory of Function Spaces II*, Birkhäuser, 1992, Chapter 7 (function spaces on
  manifolds, defined through localization in charts).
* M. E. Taylor, *Pseudodifferential Operators: Four Lectures at MSRI*, September 2008,
  Lecture II (the spaces `H^{s,p}`).
-/

public section

noncomputable section

open Bundle Set TopologicalSpace Complex ContMDiffSection TemperedDistribution
open scoped Manifold ContDiff Distributions SchwartzMap CompactConvergenceCLM ENNReal
  BesselPotentialSpace

namespace TauCeti

namespace SquareChartPartition

attribute [local instance] ContMDiffSection.ChartTestData.memTrivializationAtlas

variable {ι : Type*} [Fintype ι]
  {E H M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {V : M → Type*} [∀ x, TopologicalSpace (V x)] [TopologicalSpace (TotalSpace F V)]
  [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)] [FiberBundle F V] [VectorBundle ℝ F V]
  [ContMDiffVectorBundle ∞ F V I]

variable (A : SquareChartPartition ι I F V)

/-! ### `H^{s,p}` regularity -/

section MemBesselPotential

variable (s : ℝ) (p : ℝ≥0∞) [Fact (1 ≤ p)]

/-- A real functional `T` on bundle tests of `V`, for instance a distributional section of a bundle
whose dual density bundle is `V`, is **`H^{s,p}` with respect to the square chart partition `A`**
when each of its localizations `χᵢ Tᵢⱼ` (`TauCeti.SquareChartPartition.localization`) lies in the
Bessel-potential space `H^{s,p}(E, ℂ)`. -/
def MemBesselPotential (T : BundleTest I F V →L_c[ℝ] ℝ) : Prop :=
  ∀ i j, (A.localization i j T).MemSobolev s p

variable {A s p} {T : BundleTest I F V →L_c[ℝ] ℝ}

theorem memBesselPotential_iff :
    A.MemBesselPotential s p T ↔ ∀ i j, (A.localization i j T).MemSobolev s p :=
  Iff.rfl

theorem MemBesselPotential.localization (hT : A.MemBesselPotential s p T) (i : ι)
    (j : Fin (Module.finrank ℝ F)) : (A.localization i j T).MemSobolev s p :=
  hT i j

/-- `H^{s,p} ⊆ H^{r,p}` for `r ≤ s`. -/
theorem MemBesselPotential.of_le {r : ℝ} (hT : A.MemBesselPotential s p T) (h : r ≤ s) :
    A.MemBesselPotential r p T :=
  fun i j ↦ (hT.localization i j).of_le h

theorem MemBesselPotential.zero : A.MemBesselPotential s p 0 := fun i j ↦ by
  rw [map_zero]
  exact memSobolev_fun_zero E ℂ s p

theorem MemBesselPotential.add {T' : BundleTest I F V →L_c[ℝ] ℝ} (hT : A.MemBesselPotential s p T)
    (hT' : A.MemBesselPotential s p T') : A.MemBesselPotential s p (T + T') := fun i j ↦ by
  rw [map_add]
  exact (hT i j).add (hT' i j)

theorem MemBesselPotential.smul (hT : A.MemBesselPotential s p T) (a : ℝ) :
    A.MemBesselPotential s p (a • T) := fun i j ↦ by
  rw [map_smul]
  exact (hT.localization i j).smul_of_tower a

/-- For `p = 2`, being `H^{s,2}` with respect to `A` is being `H^s` with respect to `A`. -/
theorem memBesselPotential_two_iff_memSobolev :
    A.MemBesselPotential s 2 T ↔ A.MemSobolev s T := by
  rw [memBesselPotential_iff, memSobolev_iff]

variable (A p) in
/-- **Finite order.** Let `1 < p < ∞`. Every real functional on bundle tests of `V`, for instance
every distributional section of a bundle whose dual density bundle is `V`, is `H^{s,p}` with
respect to `A` for some real `s`: its finitely many localizations are compactly supported
distributions, each of which lies in some `H^{s,p}(E, ℂ)`. -/
theorem exists_memBesselPotential (hp : 1 < p) (hp_top : p ≠ (∞ : ℝ≥0∞))
    (T : BundleTest I F V →L_c[ℝ] ℝ) : ∃ s, A.MemBesselPotential s p T := by
  choose r hr using fun k : ι × Fin (Module.finrank ℝ F) ↦
    Distribution.exists_memSobolev_cutoffTempered_of_one_lt hp hp_top
      ((A.chartData k.1).trivialization.chartComponent (A.chartData k.1).chart
        (A.chartData k.1).contMDiffOn_chart (A.chartData k.1).source_subset T
        (Module.finBasis ℝ F k.2)) (A.chartCutoff k.1)
  -- A common lower bound of the finitely many orders `rᵢⱼ` works for every localization.
  obtain ⟨s, hs⟩ := (Set.finite_range r).bddBelow
  refine ⟨s, fun i j ↦ ?_⟩
  rw [localization_apply]
  exact MemSobolev.of_le (hr (i, j)) (hs ⟨(i, j), rfl⟩)

variable (A s p)

/-- The functionals on bundle tests that are `H^{s,p}` with respect to `A`, as a real
subspace. -/
def memBesselPotentialSubmodule : Submodule ℝ (BundleTest I F V →L_c[ℝ] ℝ) where
  carrier := {T | A.MemBesselPotential s p T}
  add_mem' := MemBesselPotential.add
  zero_mem' := MemBesselPotential.zero
  smul_mem' a _ hT := hT.smul a

@[simp]
theorem mem_memBesselPotentialSubmodule :
    T ∈ A.memBesselPotentialSubmodule s p ↔ A.MemBesselPotential s p T :=
  Iff.rfl

end MemBesselPotential

/-! ### The Bessel-potential spaces -/

section BesselPotentialSpace

variable (s : ℝ) (p : ℝ≥0∞) [Fact (1 ≤ p)]

/-- The **Bessel-potential space `H^{s,p}` of functionals on bundle tests of `V`** with respect to
the square chart partition `A`, for instance of distributional sections of a bundle whose dual
density bundle is `V`, realized as the tuples `(uᵢⱼ)` in the product of copies of `H^{s,p}(E, ℂ)`
that are localizations of a functional on bundle tests: those reproduced by localizing their
reconstruction. It is a closed subspace
(`TauCeti.SquareChartPartition.isClosed_besselPotentialSpace`), hence complete, and its norm is the
norm `‖u‖ = maxᵢⱼ ‖uᵢⱼ‖_{H^{s,p}}` of the product. The functional represented by `u` is
`TauCeti.SquareChartPartition.besselPotentialToDistribution`. -/
def besselPotentialSpace :
    Submodule ℝ (ι × Fin (Module.finrank ℝ F) → H^{s, p}(E, ℂ)) where
  carrier := {u | ∀ k, A.localization k.1 k.2 (A.reconstruction fun l ↦ (u l).toDistr) =
    (u k).toDistr}
  add_mem' {u u'} hu hu' k := by
    simp only [Pi.add_apply, BesselPotentialSpace.toDistr_add]
    rw [← Pi.add_def, map_add, map_add, hu k, hu' k]
  zero_mem' k := by
    simp only [Pi.zero_apply, BesselPotentialSpace.toDistr_zero]
    rw [← Pi.zero_def, map_zero, map_zero]
  smul_mem' a u hu k := by
    simp only [Pi.smul_apply, BesselPotentialSpace.toDistr_real_smul]
    rw [← Pi.smul_def, map_smul, map_smul, hu k]

variable {s p} in
theorem mem_besselPotentialSpace {u : ι × Fin (Module.finrank ℝ F) → H^{s, p}(E, ℂ)} :
    u ∈ A.besselPotentialSpace s p ↔
      ∀ k, A.localization k.1 k.2 (A.reconstruction fun l ↦ (u l).toDistr) = (u k).toDistr :=
  Iff.rfl

variable {s p} in
/-- The Bessel-potential space is the image of the localization map: `u` lies in it exactly when
its components are the localizations of some functional on bundle tests. -/
theorem mem_besselPotentialSpace_iff_exists_localization
    {u : ι × Fin (Module.finrank ℝ F) → H^{s, p}(E, ℂ)} :
    u ∈ A.besselPotentialSpace s p ↔
      ∃ T : BundleTest I F V →L_c[ℝ] ℝ, ∀ k, A.localization k.1 k.2 T = (u k).toDistr := by
  refine ⟨fun hu ↦ ⟨_, hu⟩, ?_⟩
  rintro ⟨T, hT⟩ k
  have h : (fun l : ι × Fin (Module.finrank ℝ F) ↦ (u l).toDistr) =
      fun l ↦ A.localization l.1 l.2 T := funext fun l ↦ (hT l).symm
  rw [h, reconstruction_localization, hT k]

/-- The `H^{s,p}` spaces of `A` are closed in the product of copies of `H^{s,p}(E, ℂ)`. -/
theorem isClosed_besselPotentialSpace :
    IsClosed (A.besselPotentialSpace s p :
      Set (ι × Fin (Module.finrank ℝ F) → H^{s, p}(E, ℂ))) :=
  A.isClosed_setOf_forall_localization_reconstruction_eq
    (fun (u : ι × Fin (Module.finrank ℝ F) → H^{s, p}(E, ℂ)) l ↦ (u l).toDistr)
    fun k ψ ↦ (ContinuousEvalConst.continuous_eval_const ψ).comp
      (BesselPotentialSpace.continuous_toDistr.comp (continuous_apply k))

instance : CompleteSpace (A.besselPotentialSpace s p) :=
  (A.isClosed_besselPotentialSpace s p).completeSpace_coe

/-- The functional on bundle tests represented by an element of the Bessel-potential space
`TauCeti.SquareChartPartition.besselPotentialSpace`: the reconstruction of its components. -/
def besselPotentialToDistribution :
    A.besselPotentialSpace s p →ₗ[ℝ] (BundleTest I F V →L_c[ℝ] ℝ) where
  toFun u := A.reconstruction fun l ↦ (u.val l).toDistr
  map_add' u u' := by
    simp only [Submodule.coe_add, Pi.add_apply, BesselPotentialSpace.toDistr_add]
    rw [← Pi.add_def, map_add]
  map_smul' a u := by
    simp only [Submodule.coe_smul, Pi.smul_apply, BesselPotentialSpace.toDistr_real_smul,
      RingHom.id_apply]
    rw [← Pi.smul_def, map_smul]

variable {s p}

theorem besselPotentialToDistribution_apply (u : A.besselPotentialSpace s p) :
    A.besselPotentialToDistribution s p u = A.reconstruction fun l ↦ (u.val l).toDistr :=
  (rfl)

/-- The localizations of the functional represented by `u` are the components of `u`. -/
@[simp]
theorem localization_besselPotentialToDistribution (u : A.besselPotentialSpace s p)
    (k : ι × Fin (Module.finrank ℝ F)) :
    A.localization k.1 k.2 (A.besselPotentialToDistribution s p u) = (u.val k).toDistr :=
  u.property k

theorem memBesselPotential_besselPotentialToDistribution (u : A.besselPotentialSpace s p) :
    A.MemBesselPotential s p (A.besselPotentialToDistribution s p u) := fun i j ↦ by
  rw [A.localization_besselPotentialToDistribution u (i, j)]
  exact BesselPotentialSpace.memSobolev_toDistr _

theorem besselPotentialToDistribution_injective :
    Function.Injective (A.besselPotentialToDistribution s p) := fun u u' h ↦
  Subtype.ext <| funext fun k ↦ BesselPotentialSpace.ext <| by
    rw [← A.localization_besselPotentialToDistribution u k,
      ← A.localization_besselPotentialToDistribution u' k, h]

/-- The element of the Bessel-potential space representing a functional which is `H^{s,p}` with
respect to `A`: the tuple of its localizations. -/
def ofMemBesselPotential {T : BundleTest I F V →L_c[ℝ] ℝ} (hT : A.MemBesselPotential s p T) :
    A.besselPotentialSpace s p :=
  ⟨fun k ↦ (hT.localization k.1 k.2).toBesselPotentialSpace, fun k ↦ by
    simp only [MemSobolev.toBesselPotentialSpace_toDistr, reconstruction_localization]⟩

@[simp]
theorem ofMemBesselPotential_apply {T : BundleTest I F V →L_c[ℝ] ℝ}
    (hT : A.MemBesselPotential s p T) (k : ι × Fin (Module.finrank ℝ F)) :
    (A.ofMemBesselPotential hT).val k = (hT.localization k.1 k.2).toBesselPotentialSpace :=
  (rfl)

@[simp]
theorem besselPotentialToDistribution_ofMemBesselPotential {T : BundleTest I F V →L_c[ℝ] ℝ}
    (hT : A.MemBesselPotential s p T) :
    A.besselPotentialToDistribution s p (A.ofMemBesselPotential hT) = T := by
  simp only [besselPotentialToDistribution_apply, ofMemBesselPotential_apply,
    MemSobolev.toBesselPotentialSpace_toDistr, reconstruction_localization]

@[simp]
theorem ofMemBesselPotential_besselPotentialToDistribution (u : A.besselPotentialSpace s p) :
    A.ofMemBesselPotential (A.memBesselPotential_besselPotentialToDistribution u) = u :=
  A.besselPotentialToDistribution_injective
    (A.besselPotentialToDistribution_ofMemBesselPotential _)

variable (s p) in
/-- The functionals represented by the Bessel-potential space are exactly those which are
`H^{s,p}` with respect to `A`. -/
theorem range_besselPotentialToDistribution :
    LinearMap.range (A.besselPotentialToDistribution s p) = A.memBesselPotentialSubmodule s p :=
  Submodule.ext fun _ ↦
    ⟨by rintro ⟨u, rfl⟩; exact A.memBesselPotential_besselPotentialToDistribution u,
    fun hT ↦ ⟨_, A.besselPotentialToDistribution_ofMemBesselPotential hT⟩⟩

variable (s p) in
/-- The Bessel-potential space is linearly equivalent to the space of functionals on bundle tests
that are `H^{s,p}` with respect to `A`. -/
def besselPotentialSpaceEquiv :
    A.besselPotentialSpace s p ≃ₗ[ℝ] A.memBesselPotentialSubmodule s p :=
  (LinearEquiv.ofInjective _ A.besselPotentialToDistribution_injective).trans
    (LinearEquiv.ofEq _ _ (A.range_besselPotentialToDistribution s p))

@[simp]
theorem coe_besselPotentialSpaceEquiv_apply (u : A.besselPotentialSpace s p) :
    (A.besselPotentialSpaceEquiv s p u : BundleTest I F V →L_c[ℝ] ℝ) =
      A.besselPotentialToDistribution s p u :=
  (rfl)

@[simp]
theorem besselPotentialSpaceEquiv_symm_apply (T : A.memBesselPotentialSubmodule s p) :
    (A.besselPotentialSpaceEquiv s p).symm T =
      A.ofMemBesselPotential ((A.mem_memBesselPotentialSubmodule s p).1 T.property) :=
  (A.besselPotentialSpaceEquiv s p).symm_apply_eq.2 <|
    Subtype.ext (A.besselPotentialToDistribution_ofMemBesselPotential _).symm

/-- Each component of an element of the Bessel-potential space has norm at most the norm of the
element. -/
theorem norm_besselPotentialSpace_val_apply_le (u : A.besselPotentialSpace s p)
    (k : ι × Fin (Module.finrank ℝ F)) : ‖u.val k‖ ≤ ‖u‖ := by
  rw [← Submodule.norm_coe]
  exact norm_le_pi_norm (u : ι × Fin (Module.finrank ℝ F) → H^{s, p}(E, ℂ)) k

/-- The norm of an element of the Bessel-potential space is the largest norm of its
components. -/
theorem norm_besselPotentialSpace_le_iff {u : A.besselPotentialSpace s p} {C : ℝ} (hC : 0 ≤ C) :
    ‖u‖ ≤ C ↔ ∀ k, ‖u.val k‖ ≤ C := by
  rw [← Submodule.norm_coe]
  exact pi_norm_le_iff_of_nonneg hC

/-- **The pinned norm.** The `H^{s,p}` norm of a functional which is `H^{s,p}` with respect to `A`
is the largest `H^{s,p}(E, ℂ)` norm of its localizations `χᵢ Tᵢⱼ`. -/
theorem norm_ofMemBesselPotential_le_iff {T : BundleTest I F V →L_c[ℝ] ℝ}
    (hT : A.MemBesselPotential s p T) {C : ℝ} (hC : 0 ≤ C) :
    ‖A.ofMemBesselPotential hT‖ ≤ C ↔
      ∀ i j, ‖(hT.localization i j).toBesselPotentialSpace‖ ≤ C := by
  rw [A.norm_besselPotentialSpace_le_iff hC, Prod.forall]
  simp only [ofMemBesselPotential_apply]

/-! ### The inclusions between the Bessel-potential spaces -/

variable {r : ℝ}

/-- The **inclusion `H^{s,p} ⊆ H^{r,p}`** of the Bessel-potential spaces of `A`, for `r ≤ s`: the
inclusion `H^{s,p}(E, ℂ) ⊆ H^{r,p}(E, ℂ)` (`BesselPotentialSpace.inclusion`) in every component
(`TauCeti.SquareChartPartition.besselPotentialInclusion_apply`). It represents the same functional
on bundle tests
(`TauCeti.SquareChartPartition.besselPotentialToDistribution_besselPotentialInclusion`). -/
def besselPotentialInclusion (h : r ≤ s) :
    A.besselPotentialSpace s p →L[ℝ] A.besselPotentialSpace r p :=
  (((ContinuousLinearMap.pi fun k : ι × Fin (Module.finrank ℝ F) ↦
      BesselPotentialSpace.inclusion h ∘L
        ContinuousLinearMap.proj (R := ℂ) (φ := fun _ ↦ H^{s, p}(E, ℂ)) k).restrictScalars ℝ) ∘L
    (A.besselPotentialSpace s p).subtypeL).codRestrict (A.besselPotentialSpace r p) fun u ↦
    (A.mem_besselPotentialSpace).2 fun k ↦ by
      simpa [BesselPotentialSpace.toDistr_inclusion] using u.property k

@[simp]
theorem besselPotentialInclusion_apply (h : r ≤ s) (u : A.besselPotentialSpace s p)
    (k : ι × Fin (Module.finrank ℝ F)) :
    (A.besselPotentialInclusion h u).val k = BesselPotentialSpace.inclusion h (u.val k) :=
  (rfl)

/-- The inclusion `H^{s,p} ⊆ H^{r,p}` does not change the represented functional on bundle
tests. -/
@[simp]
theorem besselPotentialToDistribution_besselPotentialInclusion (h : r ≤ s)
    (u : A.besselPotentialSpace s p) :
    A.besselPotentialToDistribution r p (A.besselPotentialInclusion h u) =
      A.besselPotentialToDistribution s p u := by
  simp [besselPotentialToDistribution_apply]

@[simp]
theorem besselPotentialInclusion_ofMemBesselPotential (h : r ≤ s)
    {T : BundleTest I F V →L_c[ℝ] ℝ} (hT : A.MemBesselPotential s p T) :
    A.besselPotentialInclusion h (A.ofMemBesselPotential hT) =
      A.ofMemBesselPotential (hT.of_le h) :=
  A.besselPotentialToDistribution_injective (by simp)

@[simp]
theorem besselPotentialInclusion_self (u : A.besselPotentialSpace s p) :
    A.besselPotentialInclusion le_rfl u = u :=
  A.besselPotentialToDistribution_injective (by simp)

@[simp]
theorem besselPotentialInclusion_besselPotentialInclusion {t : ℝ} (h₁ : r ≤ s) (h₂ : t ≤ r)
    (u : A.besselPotentialSpace s p) :
    A.besselPotentialInclusion h₂ (A.besselPotentialInclusion h₁ u) =
      A.besselPotentialInclusion (h₂.trans h₁) u :=
  A.besselPotentialToDistribution_injective (by simp)

theorem besselPotentialInclusion_injective (h : r ≤ s) :
    Function.Injective (A.besselPotentialInclusion (p := p) h) := fun u u' huu' ↦
  A.besselPotentialToDistribution_injective <| by
    rw [← A.besselPotentialToDistribution_besselPotentialInclusion h u,
      ← A.besselPotentialToDistribution_besselPotentialInclusion h u', huu']

/-! ### Comparison with the Sobolev spaces -/

variable (s) in
/-- **`H^{s,2} = H^s` with equivalent norms.** The Bessel-potential space `H^{s,2}` of `A`, with
the maximum norm of the components, is isomorphic as a Banach space to the Sobolev space `H^s` of
`A`, with the `ℓ²` norm of the components, through the identity on components
(`TauCeti.SquareChartPartition.besselPotentialSpaceTwoEquivSobolevSpace_apply`). It does not change
the represented functional on bundle tests
(`TauCeti.SquareChartPartition.toDistribution_besselPotentialSpaceTwoEquivSobolevSpace`). -/
def besselPotentialSpaceTwoEquivSobolevSpace :
    A.besselPotentialSpace s 2 ≃L[ℝ] A.sobolevSpace s :=
  ContinuousLinearEquiv.ofContinuousLinearMap
    ((((PiLp.continuousLinearEquiv 2 ℂ fun _ : ι × Fin (Module.finrank ℝ F) ↦
        H^{s}(E, ℂ)).symm.toContinuousLinearMap).restrictScalars ℝ ∘L
        (A.besselPotentialSpace s 2).subtypeL).codRestrict (A.sobolevSpace s) fun u ↦
      (A.mem_sobolevSpace s).2 fun k ↦ by simpa using u.property k)
    ((((PiLp.continuousLinearEquiv 2 ℂ fun _ : ι × Fin (Module.finrank ℝ F) ↦
        H^{s}(E, ℂ)).toContinuousLinearMap).restrictScalars ℝ ∘L
        (A.sobolevSpace s).subtypeL).codRestrict (A.besselPotentialSpace s 2) fun v ↦
      (A.mem_besselPotentialSpace).2 fun k ↦ by simpa using (A.mem_sobolevSpace s).1 v.property k)
    (ContinuousLinearMap.ext fun _ ↦ Subtype.ext (by simp [PiLp.coe_continuousLinearEquiv]))
    (ContinuousLinearMap.ext fun _ ↦ Subtype.ext (by simp [PiLp.coe_continuousLinearEquiv]))

@[simp]
theorem besselPotentialSpaceTwoEquivSobolevSpace_apply (u : A.besselPotentialSpace s 2)
    (k : ι × Fin (Module.finrank ℝ F)) :
    (A.besselPotentialSpaceTwoEquivSobolevSpace s u).val k = u.val k :=
  (rfl)

@[simp]
theorem besselPotentialSpaceTwoEquivSobolevSpace_symm_apply (v : A.sobolevSpace s)
    (k : ι × Fin (Module.finrank ℝ F)) :
    ((A.besselPotentialSpaceTwoEquivSobolevSpace s).symm v).val k = v.val k :=
  (rfl)

/-- The isomorphism `H^{s,2} ≃ H^s` does not change the represented functional. -/
@[simp]
theorem toDistribution_besselPotentialSpaceTwoEquivSobolevSpace (u : A.besselPotentialSpace s 2) :
    A.toDistribution s (A.besselPotentialSpaceTwoEquivSobolevSpace s u) =
      A.besselPotentialToDistribution s 2 u := by
  simp [toDistribution_apply, besselPotentialToDistribution_apply]

@[simp]
theorem besselPotentialSpaceTwoEquivSobolevSpace_ofMemBesselPotential
    {T : BundleTest I F V →L_c[ℝ] ℝ} (hT : A.MemBesselPotential s 2 T) :
    A.besselPotentialSpaceTwoEquivSobolevSpace s (A.ofMemBesselPotential hT) =
      A.ofMemSobolev s (A.memBesselPotential_two_iff_memSobolev.1 hT) :=
  A.toDistribution_injective s (by simp)

/-- The inverse isomorphism `H^s ≃ H^{s,2}` does not change the represented functional. -/
@[simp]
theorem besselPotentialToDistribution_besselPotentialSpaceTwoEquivSobolevSpace_symm
    (v : A.sobolevSpace s) :
    A.besselPotentialToDistribution s 2 ((A.besselPotentialSpaceTwoEquivSobolevSpace s).symm v) =
      A.toDistribution s v := by
  rw [← toDistribution_besselPotentialSpaceTwoEquivSobolevSpace,
    ContinuousLinearEquiv.apply_symm_apply]

@[simp]
theorem besselPotentialSpaceTwoEquivSobolevSpace_symm_ofMemSobolev
    {T : BundleTest I F V →L_c[ℝ] ℝ} (hT : A.MemSobolev s T) :
    (A.besselPotentialSpaceTwoEquivSobolevSpace s).symm (A.ofMemSobolev s hT) =
      A.ofMemBesselPotential (A.memBesselPotential_two_iff_memSobolev.2 hT) :=
  A.besselPotentialToDistribution_injective (by simp)

end BesselPotentialSpace

/-! ### Independence of the partition -/

section Independence

variable {κ : Type*} [Fintype κ] {s : ℝ} {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- **`H^{s,p}` with respect to a partition is local `H^{s,p}` regularity.** Let `1 < p < ∞`. A
real functional `T` on bundle tests is `H^{s,p}` with respect to the square chart partition `A`
exactly when it is `H^{s,p}` near every point of `M`
(`TauCeti.BundleTest.IsLocallyMemSobolevAt`). In particular this does not depend on the partition
(`TauCeti.SquareChartPartition.memBesselPotential_iff_memBesselPotential`). -/
theorem memBesselPotential_iff_forall_isLocallyMemSobolevAt (hp : 1 < p) (hp_top : p ≠ (∞ : ℝ≥0∞))
    {T : BundleTest I F V →L_c[ℝ] ℝ} :
    A.MemBesselPotential s p T ↔ ∀ x, BundleTest.IsLocallyMemSobolevAt s p T x := by
  constructor
  · intro hT x
    -- Some cutoff does not vanish at `x`, since their squares sum to one.
    obtain ⟨i, hi⟩ : ∃ i, A.cutoff i x ≠ 0 := by
      by_contra! h
      simpa [h] using A.sum_sq_cutoff x
    have hx : x ∈ (A.chartData i).chart.source :=
      A.tsupport_cutoff_subset i (subset_tsupport _ hi)
    have hcx := (A.chartData i).chart.map_source hx
    refine (BundleTest.isLocallyMemSobolevAt_iff hp hp_top T (A.chartData i).contMDiffOn_chart
      (A.contMDiffOn_chart_symm i) (A.chartData i).source_subset hx).2
      (Bundle.Trivialization.chartComponent_of_basis
        (Distribution.isInvariantLocalRegularity_isLocallyMemSobolevAt s hp
          hp_top).toIsLocalRegularity
        (Module.finBasis ℝ F) T hcx fun j ↦ ?_)
    -- The localization `χᵢ Tᵢⱼ` is `H^{s,p}`, and the chart cutoff does not vanish at `cᵢ x`.
    refine (Distribution.isLocallyMemSobolevAt_iff_exists_memSobolev_cutoffTempered hp
      hp_top).2 ⟨A.chartCutoff i, ?_, by simpa only [localization_apply] using hT i j⟩
    rwa [A.chartCutoff_apply_of_mem hcx, (A.chartData i).chart.left_inv hx, ofReal_ne_zero]
  · intro hT i j
    rw [localization_apply]
    refine Distribution.memSobolev_cutoffTempered_of_forall_isLocallyMemSobolevAt fun y hy ↦ ?_
    -- A point of the support of the chart cutoff is `cᵢ x` for `x` in the support of `χᵢ`.
    obtain ⟨x, hx, rfl⟩ : y ∈ (A.chartData i).chart '' tsupport (A.cutoff i) := by
      rw [← A.coe_chartSupport]
      exact A.tsupport_chartCutoff_subset i hy
    exact (BundleTest.isLocallyMemSobolevAt_iff hp hp_top T (A.chartData i).contMDiffOn_chart
      (A.contMDiffOn_chart_symm i) (A.chartData i).source_subset
      (A.tsupport_cutoff_subset i hx)).1 (hT x) _

/-- **Independence of the partition.** Let `1 < p < ∞`. A real functional on bundle tests is
`H^{s,p}` with respect to one square chart partition of `V` exactly when it is `H^{s,p}` with
respect to any other. -/
theorem memBesselPotential_iff_memBesselPotential (B : SquareChartPartition κ I F V) (hp : 1 < p)
    (hp_top : p ≠ (∞ : ℝ≥0∞)) {T : BundleTest I F V →L_c[ℝ] ℝ} :
    A.MemBesselPotential s p T ↔ B.MemBesselPotential s p T := by
  rw [A.memBesselPotential_iff_forall_isLocallyMemSobolevAt hp hp_top,
    B.memBesselPotential_iff_forall_isLocallyMemSobolevAt hp hp_top]

/-- Let `1 < p < ∞`. Two square chart partitions of `V` have the same `H^{s,p}` functionals. -/
theorem memBesselPotentialSubmodule_eq (B : SquareChartPartition κ I F V) (hp : 1 < p)
    (hp_top : p ≠ (∞ : ℝ≥0∞)) :
    A.memBesselPotentialSubmodule s p = B.memBesselPotentialSubmodule s p :=
  Submodule.ext fun _ ↦ A.memBesselPotential_iff_memBesselPotential B hp hp_top

variable (s p) in
/-- The value of the functional represented by an element of the Bessel-potential space at a fixed
bundle test depends continuously on the element. -/
theorem continuous_besselPotentialToDistribution_apply (φ : BundleTest I F V) :
    Continuous fun u : A.besselPotentialSpace s p ↦ A.besselPotentialToDistribution s p u φ := by
  simp only [besselPotentialToDistribution_apply, reconstruction_apply]
  exact continuous_finsetSum _ fun k _ ↦ continuous_re.comp
    ((ContinuousEvalConst.continuous_eval_const _).comp
      (BesselPotentialSpace.continuous_toDistr.comp
        ((continuous_apply k).comp continuous_subtypeVal)))

/-- The identification of the Bessel-potential spaces of two square chart partitions as a linear
equivalence: an element of one goes to the element of the other representing the same
functional. -/
private def besselPotentialSpaceLinearEquiv (B : SquareChartPartition κ I F V) (s : ℝ)
    (hp : 1 < p) (hp_top : p ≠ (∞ : ℝ≥0∞)) :
    A.besselPotentialSpace s p ≃ₗ[ℝ] B.besselPotentialSpace s p :=
  (A.besselPotentialSpaceEquiv s p).trans
    ((LinearEquiv.ofEq _ _ (A.memBesselPotentialSubmodule_eq B hp hp_top)).trans
      (B.besselPotentialSpaceEquiv s p).symm)

private theorem besselPotentialToDistribution_besselPotentialSpaceLinearEquiv
    (B : SquareChartPartition κ I F V) (s : ℝ) (hp : 1 < p) (hp_top : p ≠ (∞ : ℝ≥0∞))
    (u : A.besselPotentialSpace s p) :
    B.besselPotentialToDistribution s p (A.besselPotentialSpaceLinearEquiv B s hp hp_top u) =
      A.besselPotentialToDistribution s p u := by
  simp [besselPotentialSpaceLinearEquiv]

/-- **Equivalence of the Bessel-potential spaces of two partitions.** Let `1 < p < ∞`. The
Bessel-potential spaces `H^{s,p}` of two square chart partitions `A` and `B` of `V` are isomorphic
as Banach spaces, through the map sending an element of `A.besselPotentialSpace s p` to the element
of `B.besselPotentialSpace s p` representing the same functional on bundle tests
(`TauCeti.SquareChartPartition.besselPotentialToDistribution_besselPotentialSpaceCongr_apply`). So
the norms of the two partitions are equivalent
(`TauCeti.SquareChartPartition.exists_norm_ofMemBesselPotential_le`). Continuity comes from the
closed graph theorem. -/
def besselPotentialSpaceCongr (B : SquareChartPartition κ I F V) (s : ℝ) (hp : 1 < p)
    (hp_top : p ≠ (∞ : ℝ≥0∞)) :
    A.besselPotentialSpace s p ≃L[ℝ] B.besselPotentialSpace s p :=
  (A.besselPotentialSpaceLinearEquiv B s hp hp_top).toContinuousLinearEquivOfContinuous
    ((A.besselPotentialSpaceLinearEquiv B s hp hp_top).toLinearMap.continuous_of_injective_comp_eq
      (continuous_pi (A.continuous_besselPotentialToDistribution_apply s p))
      (continuous_pi (B.continuous_besselPotentialToDistribution_apply s p))
      (DFunLike.coe_injective.comp B.besselPotentialToDistribution_injective) fun u ↦
        congrArg DFunLike.coe
          (A.besselPotentialToDistribution_besselPotentialSpaceLinearEquiv B s hp hp_top u))

/-- The identification of the Bessel-potential spaces of two partitions preserves the represented
functional. -/
@[simp]
theorem besselPotentialToDistribution_besselPotentialSpaceCongr_apply
    (B : SquareChartPartition κ I F V) (hp : 1 < p) (hp_top : p ≠ (∞ : ℝ≥0∞))
    (u : A.besselPotentialSpace s p) :
    B.besselPotentialToDistribution s p (A.besselPotentialSpaceCongr B s hp hp_top u) =
      A.besselPotentialToDistribution s p u :=
  A.besselPotentialToDistribution_besselPotentialSpaceLinearEquiv B s hp hp_top u

/-- The identification sends the tuple of localizations of `T` with respect to `A` to its tuple of
localizations with respect to `B`. -/
@[simp]
theorem besselPotentialSpaceCongr_ofMemBesselPotential (B : SquareChartPartition κ I F V)
    (hp : 1 < p) (hp_top : p ≠ (∞ : ℝ≥0∞)) {T : BundleTest I F V →L_c[ℝ] ℝ}
    (hT : A.MemBesselPotential s p T) :
    A.besselPotentialSpaceCongr B s hp hp_top (A.ofMemBesselPotential hT) =
      B.ofMemBesselPotential ((A.memBesselPotential_iff_memBesselPotential B hp hp_top).1 hT) :=
  B.besselPotentialToDistribution_injective (by simp)

/-- The identification of the Bessel-potential spaces of a partition with itself is the
identity. -/
@[simp]
theorem besselPotentialSpaceCongr_refl (hp : 1 < p) (hp_top : p ≠ (∞ : ℝ≥0∞)) :
    A.besselPotentialSpaceCongr A s hp hp_top =
      ContinuousLinearEquiv.refl ℝ (A.besselPotentialSpace s p) :=
  ContinuousLinearEquiv.ext <| funext fun _ ↦ A.besselPotentialToDistribution_injective (by simp)

/-- The inverse of the identification from `A` to `B` is the identification from `B` to `A`. -/
@[simp]
theorem besselPotentialSpaceCongr_symm (B : SquareChartPartition κ I F V) (hp : 1 < p)
    (hp_top : p ≠ (∞ : ℝ≥0∞)) :
    (A.besselPotentialSpaceCongr B s hp hp_top).symm =
      B.besselPotentialSpaceCongr A s hp hp_top :=
  ContinuousLinearEquiv.ext <| funext fun _ ↦
    (A.besselPotentialSpaceCongr B s hp hp_top).symm_apply_eq.2 <|
      B.besselPotentialToDistribution_injective (by simp)

/-- The identifications compose: going from `A` to `B` and then to `C` is going from `A` to
`C`. -/
@[simp]
theorem besselPotentialSpaceCongr_trans {ν : Type*} [Fintype ν] (B : SquareChartPartition κ I F V)
    (C : SquareChartPartition ν I F V) (hp : 1 < p) (hp_top : p ≠ (∞ : ℝ≥0∞)) :
    (A.besselPotentialSpaceCongr B s hp hp_top).trans
        (B.besselPotentialSpaceCongr C s hp hp_top) =
      A.besselPotentialSpaceCongr C s hp hp_top :=
  ContinuousLinearEquiv.ext <| funext fun _ ↦ C.besselPotentialToDistribution_injective (by simp)

/-- **Equivalence of the norms.** Let `1 < p < ∞`. For two square chart partitions `A` and `B` of
`V`, the `H^{s,p}` norm of a functional with respect to `B` is bounded by a constant multiple of
its `H^{s,p}` norm with respect to `A`. -/
theorem exists_norm_ofMemBesselPotential_le (B : SquareChartPartition κ I F V) (hp : 1 < p)
    (hp_top : p ≠ (∞ : ℝ≥0∞)) :
    ∃ C, ∀ (T : BundleTest I F V →L_c[ℝ] ℝ) (hA : A.MemBesselPotential s p T)
      (hB : B.MemBesselPotential s p T),
      ‖B.ofMemBesselPotential hB‖ ≤ C * ‖A.ofMemBesselPotential hA‖ :=
  ⟨‖(A.besselPotentialSpaceCongr B s hp hp_top :
      A.besselPotentialSpace s p →L[ℝ] B.besselPotentialSpace s p)‖, fun T hA hB ↦ by
    simpa using (A.besselPotentialSpaceCongr B s hp hp_top :
      A.besselPotentialSpace s p →L[ℝ] B.besselPotentialSpace s p).le_opNorm
        (A.ofMemBesselPotential hA)⟩

end Independence

end SquareChartPartition

end TauCeti

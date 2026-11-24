/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.BesselPotential.Besov
public import TauCeti.Geometry.Manifold.VectorBundle.Sobolev.BesselPotential
import TauCeti.Analysis.FunctionalSpaces.BesovSpace.Local

/-!
# Besov spaces of distributions on bundle tests

Let `V → M` be a smooth real vector bundle with model fibre `F`, and let `A` be a square chart
partition of `V` (`TauCeti.SquareChartPartition`): finitely many charts `cᵢ` with frames `tᵢ` over
their sources and cutoffs `χᵢ` with `∑ᵢ χᵢ² = 1`. A real functional `T` on the bundle tests
`TauCeti.BundleTest I F V`, for instance a distributional section `TauCeti.BundleDistribution`
of a bundle whose dual density bundle is `V`, has finitely many **localizations** `χᵢ Tᵢⱼ`
(`TauCeti.SquareChartPartition.localization`): compactly supported tempered distributions on the
model space `E`, one for each chart and each vector of the fixed basis of `F`. They determine `T`
through the reconstruction (`TauCeti.SquareChartPartition.reconstruction_localization`).

This file builds the inhomogeneous **Besov spaces** `B^s_{p,q}` of such functionals, for real `s`
and `1 ≤ p, q ≤ ∞`, from the Euclidean Besov spaces `TauCeti.BesovSpace` built from the
Littlewood–Paley partition of a bump function `φ`, in the same way as the Sobolev spaces
`TauCeti.SquareChartPartition.sobolevSpace` are built from the Bessel-potential spaces `H^s`. For
`p = q = ∞` they are the Hölder–Zygmund spaces `𝒞^s = B^s_{∞,∞}` of such functionals.

* `T` is **`B^s_{p,q}` with respect to `A`** (`TauCeti.SquareChartPartition.MemBesov`) when all
  its localizations lie in `B^s_{p,q}(E, ℂ)`. This does not depend on the bump function
  (`TauCeti.SquareChartPartition.MemBesov.of_bump`), it follows the inclusions of the Euclidean
  scale, and every functional lies in some `B^s_{p,q}` for `1 < p` and `q ≠ 0`
  (`TauCeti.SquareChartPartition.exists_memBesov`). For `p = 2` it is compared with the Sobolev
  scale: `H^s ⊆ B^s_{2,∞}`, `B^s_{2,1} ⊆ H^s` and `B^s_{2,2} = H^s`
  (`TauCeti.SquareChartPartition.memBesov_two_two_iff_memSobolev`).
* The **Besov space** `TauCeti.SquareChartPartition.besovSpace` is the real subspace of the tuples
  `(uᵢⱼ)` of elements of `B^s_{p,q}(E, ℂ)` that are reproduced by localizing their reconstruction,
  that is, the tuples of localizations of a functional on bundle tests. It is closed in the
  product (`TauCeti.SquareChartPartition.isClosed_besovSpace`), so it is a Banach space, with the
  norm `‖T‖ = maxᵢⱼ ‖χᵢ Tᵢⱼ‖_{B^s_{p,q}}` of the product
  (`TauCeti.SquareChartPartition.norm_ofMemBesov_le_iff`). It is linearly equivalent to the
  functionals that are `B^s_{p,q}` with respect to `A`
  (`TauCeti.SquareChartPartition.besovSpaceEquiv`), through the reconstruction
  `TauCeti.SquareChartPartition.besovToDistribution`.

The Euclidean comparisons pass to these spaces componentwise, as continuous linear maps which do
not change the represented functional: the inclusions `B^s_{p,q} ⊆ B^{s'}_{p,q'}` for `s' ≤ s`,
`q ≤ q'` and for `s' < s` (`TauCeti.SquareChartPartition.besovInclusion`,
`TauCeti.SquareChartPartition.besovInclusionOfLT`), the change of bump function
(`TauCeti.SquareChartPartition.besovBumpEquiv`), and the isomorphism `B^s_{2,2} ≃ H^s` with the
Sobolev space of the same partition (`TauCeti.SquareChartPartition.besovSpaceEquivSobolevSpace`).

The independence of these spaces from the partition, up to equivalent norms, needs the Besov
estimates for multiplication by cutoffs and for chart changes, and is not proved here.

## Main declarations

* `TauCeti.SquareChartPartition.MemBesov`: `B^s_{p,q}` regularity with respect to the partition,
  with `TauCeti.SquareChartPartition.exists_memBesov` (finite order) and the Sobolev comparisons
  `TauCeti.SquareChartPartition.MemSobolev.memBesov`,
  `TauCeti.SquareChartPartition.MemBesov.memSobolev` and
  `TauCeti.SquareChartPartition.memBesov_two_two_iff_memSobolev`.
* `TauCeti.SquareChartPartition.besovSpace`: the Besov space, with
  `TauCeti.SquareChartPartition.isClosed_besovSpace` and its `CompleteSpace` instance.
* `TauCeti.SquareChartPartition.besovToDistribution`, `TauCeti.SquareChartPartition.ofMemBesov`,
  `TauCeti.SquareChartPartition.range_besovToDistribution` and
  `TauCeti.SquareChartPartition.besovSpaceEquiv`: the Besov space represents exactly the
  functionals that are `B^s_{p,q}` with respect to the partition.
* `TauCeti.SquareChartPartition.besovInclusion`, `TauCeti.SquareChartPartition.besovInclusionOfLT`,
  `TauCeti.SquareChartPartition.besovBumpEquiv` and
  `TauCeti.SquareChartPartition.besovSpaceEquivSobolevSpace`.

## References

* H. Triebel, *Theory of Function Spaces II*, Birkhäuser, 1992, Chapter 7 (function spaces on
  manifolds, defined through localization in charts).
* J. Bergh and J. Löfström, *Interpolation Spaces: An Introduction*, Springer, 1976, §6.2 (the
  Euclidean Besov spaces).
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

variable (A : SquareChartPartition ι I F V) (φ : ContDiffBump (0 : E))

/-! ### Besov regularity -/

section MemBesov

variable (s : ℝ) (p q : ℝ≥0∞) [Fact (1 ≤ p)]

/-- A real functional `T` on bundle tests of `V`, for instance a distributional section of a bundle
whose dual density bundle is `V`, is **`B^s_{p,q}` with respect to the square chart partition `A`**
when each of its localizations `χᵢ Tᵢⱼ` (`TauCeti.SquareChartPartition.localization`) lies in the
Besov space `B^s_{p,q}(E, ℂ)` built from the Littlewood–Paley partition of `φ`. For `p = q = ∞`
this is membership in the Hölder–Zygmund space `𝒞^s`. -/
def MemBesov (T : BundleTest I F V →L_c[ℝ] ℝ) : Prop :=
  ∀ i j, (A.localization i j T).MemBesov φ s p q

variable {A φ s p q} {T : BundleTest I F V →L_c[ℝ] ℝ}

theorem memBesov_iff :
    A.MemBesov φ s p q T ↔ ∀ i j, (A.localization i j T).MemBesov φ s p q :=
  Iff.rfl

theorem MemBesov.localization (hT : A.MemBesov φ s p q T) (i : ι)
    (j : Fin (Module.finrank ℝ F)) : (A.localization i j T).MemBesov φ s p q :=
  hT i j

/-- **Monotonicity of the Besov scale.** `B^s_{p,q} ⊆ B^{s'}_{p,q'}` for `s' ≤ s` and `q ≤ q'`. -/
theorem MemBesov.mono {s' : ℝ} {q' : ℝ≥0∞} (hT : A.MemBesov φ s p q T) (hs : s' ≤ s)
    (hq : q ≤ q') : A.MemBesov φ s' p q' T :=
  fun i j ↦ (hT i j).mono hs hq

/-- **Strict monotonicity of the Besov scale.** `B^s_{p,q} ⊆ B^{s'}_{p,q'}` for `s' < s`, every
`q` and every `q' ≠ 0`. -/
theorem MemBesov.of_lt {s' : ℝ} {q' : ℝ≥0∞} (hT : A.MemBesov φ s p q T) (hs : s' < s)
    (hq' : q' ≠ 0) : A.MemBesov φ s' p q' T :=
  fun i j ↦ (hT i j).of_lt hs hq'

/-- **The Bernstein embedding.** For `p ≤ r`, `B^s_{p,q} ⊆ B^{s - n (1/p - 1/r)}_{r,q}`, where `n`
is the dimension of the model space `E` and `1/∞ = 0`. -/
theorem MemBesov.mono_exponent {r : ℝ≥0∞} [Fact (1 ≤ r)] (hT : A.MemBesov φ s p q T)
    (hpr : p ≤ r) :
    A.MemBesov φ (s - Module.finrank ℝ E * (p.toReal⁻¹ - r.toReal⁻¹)) r q T :=
  fun i j ↦ (hT i j).mono_exponent hpr

/-- **Independence of the bump function.** Being `B^s_{p,q}` with respect to `A` does not depend on
the bump function of the Littlewood–Paley partition. -/
theorem MemBesov.of_bump (hT : A.MemBesov φ s p q T) (φ' : ContDiffBump (0 : E)) :
    A.MemBesov φ' s p q T :=
  fun i j ↦ (hT i j).of_bump φ'

theorem MemBesov.zero : A.MemBesov φ s p q 0 := fun i j ↦ by
  rw [map_zero]
  exact TemperedDistribution.MemBesov.zero

theorem MemBesov.add {T' : BundleTest I F V →L_c[ℝ] ℝ} (hT : A.MemBesov φ s p q T)
    (hT' : A.MemBesov φ s p q T') : A.MemBesov φ s p q (T + T') := fun i j ↦ by
  rw [map_add]
  exact (hT i j).add (hT' i j)

theorem MemBesov.smul (hT : A.MemBesov φ s p q T) (a : ℝ) : A.MemBesov φ s p q (a • T) :=
  fun i j ↦ by
    -- The real action on tempered distributions is the restriction of the complex one.
    have h : A.localization i j (a • T) = (a : ℂ) • A.localization i j T := by
      ext ψ
      simp [Complex.real_smul]
    rw [h]
    exact (hT i j).smul (a : ℂ)

/-- **`H^s ⊆ B^s_{2,∞}`.** A functional which is `H^s` with respect to `A` is `B^s_{2,∞}` with
respect to `A`. -/
theorem MemSobolev.memBesov (hT : A.MemSobolev s T) (φ : ContDiffBump (0 : E)) :
    A.MemBesov φ s 2 ∞ T :=
  fun i j ↦ (hT.localization i j).memBesov φ

/-- **`B^s_{2,1} ⊆ H^s`.** A functional which is `B^s_{2,1}` with respect to `A` is `H^s` with
respect to `A`. -/
theorem MemBesov.memSobolev (hT : A.MemBesov φ s 2 1 T) : A.MemSobolev s T :=
  A.memSobolev_iff.2 fun i j ↦ (hT i j).memSobolev

variable (φ) in
/-- **`B^s_{2,2} = H^s`.** A functional is `B^s_{2,2}` with respect to `A` exactly when it is `H^s`
with respect to `A`. -/
theorem memBesov_two_two_iff_memSobolev : A.MemBesov φ s 2 2 T ↔ A.MemSobolev s T := by
  rw [memSobolev_iff]
  exact forall₂_congr fun _ _ ↦ TemperedDistribution.memBesov_two_two_iff_memSobolev φ

variable (A φ p q) in
/-- **Finite order.** Let `1 < p ≤ ∞` and `q ≠ 0`. Every real functional on bundle tests of `V`,
for instance every distributional section of a bundle whose dual density bundle is `V`, is
`B^s_{p,q}` with respect to `A` for some real `s`: its finitely many localizations are compactly
supported distributions, each of which lies in some `B^s_{p,q}(E, ℂ)`. -/
theorem exists_memBesov (hp : 1 < p) (hq : q ≠ 0) (T : BundleTest I F V →L_c[ℝ] ℝ) :
    ∃ s, A.MemBesov φ s p q T := by
  choose r hr using fun k : ι × Fin (Module.finrank ℝ F) ↦
    Distribution.exists_memBesov_cutoffTempered φ hp hq
      ((A.chartData k.1).trivialization.chartComponent (A.chartData k.1).chart
        (A.chartData k.1).contMDiffOn_chart (A.chartData k.1).source_subset T
        (Module.finBasis ℝ F k.2)) (A.chartCutoff k.1)
  -- A common lower bound of the finitely many orders `rᵢⱼ` works for every localization.
  obtain ⟨s, hs⟩ := (Set.finite_range r).bddBelow
  refine ⟨s, fun i j ↦ ?_⟩
  rw [localization_apply]
  exact (hr (i, j)).mono (hs ⟨(i, j), rfl⟩) le_rfl

variable (A φ s p q)

/-- The functionals on bundle tests that are `B^s_{p,q}` with respect to `A`, as a real
subspace. -/
def memBesovSubmodule : Submodule ℝ (BundleTest I F V →L_c[ℝ] ℝ) where
  carrier := {T | A.MemBesov φ s p q T}
  add_mem' := MemBesov.add
  zero_mem' := MemBesov.zero
  smul_mem' a _ hT := hT.smul a

@[simp]
theorem mem_memBesovSubmodule : T ∈ A.memBesovSubmodule φ s p q ↔ A.MemBesov φ s p q T :=
  Iff.rfl

end MemBesov

/-! ### The Besov spaces -/

section BesovSpace

variable (s : ℝ) (p q : ℝ≥0∞) [Fact (1 ≤ p)] [Fact (1 ≤ q)]

/-- The **Besov space `B^s_{p,q}` of functionals on bundle tests of `V`** with respect to the
square chart partition `A`, for instance of distributional sections of a bundle whose dual density
bundle is `V`, realized as the tuples `(uᵢⱼ)` in the product of copies of `B^s_{p,q}(E, ℂ)` that
are localizations of a functional on bundle tests: those reproduced by localizing their
reconstruction. It is a closed subspace (`TauCeti.SquareChartPartition.isClosed_besovSpace`),
hence complete, and its norm is the norm `‖u‖ = maxᵢⱼ ‖uᵢⱼ‖_{B^s_{p,q}}` of the product. The
functional represented by `u` is `TauCeti.SquareChartPartition.besovToDistribution`. -/
def besovSpace :
    Submodule ℝ (ι × Fin (Module.finrank ℝ F) → BesovSpace ℂ φ s p q) where
  carrier := {u | ∀ k, A.localization k.1 k.2 (A.reconstruction fun l ↦ (u l).toDistr) =
    (u k).toDistr}
  add_mem' {u u'} hu hu' k := by
    simp only [Pi.add_apply, BesovSpace.toDistr_add]
    rw [← Pi.add_def, map_add, map_add, hu k, hu' k]
  zero_mem' k := by
    simp only [Pi.zero_apply, BesovSpace.toDistr_zero]
    rw [← Pi.zero_def, map_zero, map_zero]
  smul_mem' a u hu k := by
    -- The real action on `B^s_{p,q}(E, ℂ)` is the restriction of the complex one, so
    -- `BesovSpace.toDistr_smul` applies at `(a : ℂ)`.
    simp only [Pi.smul_apply, ← Complex.coe_smul, BesovSpace.toDistr_smul]
    simp only [Complex.coe_smul]
    rw [← Pi.smul_def, map_smul, map_smul, hu k]

variable {s p q} in
theorem mem_besovSpace {u : ι × Fin (Module.finrank ℝ F) → BesovSpace ℂ φ s p q} :
    u ∈ A.besovSpace φ s p q ↔
      ∀ k, A.localization k.1 k.2 (A.reconstruction fun l ↦ (u l).toDistr) = (u k).toDistr :=
  Iff.rfl

variable {s p q} in
/-- The Besov space is the image of the localization map: `u` lies in it exactly when its
components are the localizations of some functional on bundle tests. -/
theorem mem_besovSpace_iff_exists_localization
    {u : ι × Fin (Module.finrank ℝ F) → BesovSpace ℂ φ s p q} :
    u ∈ A.besovSpace φ s p q ↔
      ∃ T : BundleTest I F V →L_c[ℝ] ℝ, ∀ k, A.localization k.1 k.2 T = (u k).toDistr := by
  refine ⟨fun hu ↦ ⟨_, hu⟩, ?_⟩
  rintro ⟨T, hT⟩ k
  have h : (fun l : ι × Fin (Module.finrank ℝ F) ↦ (u l).toDistr) =
      fun l ↦ A.localization l.1 l.2 T := funext fun l ↦ (hT l).symm
  rw [h, reconstruction_localization, hT k]

/-- The `B^s_{p,q}` spaces of `A` are closed in the product of copies of `B^s_{p,q}(E, ℂ)`. -/
theorem isClosed_besovSpace :
    IsClosed (A.besovSpace φ s p q :
      Set (ι × Fin (Module.finrank ℝ F) → BesovSpace ℂ φ s p q)) :=
  A.isClosed_setOf_forall_localization_reconstruction_eq
    (fun (u : ι × Fin (Module.finrank ℝ F) → BesovSpace ℂ φ s p q) l ↦ (u l).toDistr)
    fun k ψ ↦ (ContinuousEvalConst.continuous_eval_const ψ).comp
      (BesovSpace.continuous_toDistr.comp (continuous_apply k))

instance : CompleteSpace (A.besovSpace φ s p q) :=
  (A.isClosed_besovSpace φ s p q).completeSpace_coe

/-- The functional on bundle tests represented by an element of the Besov space
`TauCeti.SquareChartPartition.besovSpace`: the reconstruction of its components. -/
def besovToDistribution : A.besovSpace φ s p q →ₗ[ℝ] (BundleTest I F V →L_c[ℝ] ℝ) where
  toFun u := A.reconstruction fun l ↦ (u.val l).toDistr
  map_add' u u' := by
    simp only [Submodule.coe_add, Pi.add_apply, BesovSpace.toDistr_add]
    rw [← Pi.add_def, map_add]
  map_smul' a u := by
    -- As in `besovSpace`, `BesovSpace.toDistr_smul` applies at `(a : ℂ)`.
    simp only [Submodule.coe_smul, Pi.smul_apply, ← Complex.coe_smul, BesovSpace.toDistr_smul,
      RingHom.id_apply]
    simp only [Complex.coe_smul]
    rw [← Pi.smul_def, map_smul]

variable {s p q}

theorem besovToDistribution_apply (u : A.besovSpace φ s p q) :
    A.besovToDistribution φ s p q u = A.reconstruction fun l ↦ (u.val l).toDistr :=
  (rfl)

/-- The localizations of the functional represented by `u` are the components of `u`. -/
@[simp]
theorem localization_besovToDistribution (u : A.besovSpace φ s p q)
    (k : ι × Fin (Module.finrank ℝ F)) :
    A.localization k.1 k.2 (A.besovToDistribution φ s p q u) = (u.val k).toDistr :=
  u.property k

theorem memBesov_besovToDistribution (u : A.besovSpace φ s p q) :
    A.MemBesov φ s p q (A.besovToDistribution φ s p q u) := fun i j ↦ by
  rw [A.localization_besovToDistribution φ u (i, j)]
  exact (u.val (i, j)).memBesov_toDistr

theorem besovToDistribution_injective : Function.Injective (A.besovToDistribution φ s p q) :=
  fun u u' h ↦ Subtype.ext <| funext fun k ↦ BesovSpace.ext <| by
    rw [← A.localization_besovToDistribution φ u k, ← A.localization_besovToDistribution φ u' k, h]

/-- The element of the Besov space representing a functional which is `B^s_{p,q}` with respect to
`A`: the tuple of its localizations. -/
def ofMemBesov {T : BundleTest I F V →L_c[ℝ] ℝ} (hT : A.MemBesov φ s p q T) :
    A.besovSpace φ s p q :=
  ⟨fun k ↦ (hT.localization k.1 k.2).toBesovSpace, fun k ↦ by
    simp only [MemBesov.toDistr_toBesovSpace, reconstruction_localization]⟩

@[simp]
theorem ofMemBesov_apply {T : BundleTest I F V →L_c[ℝ] ℝ} (hT : A.MemBesov φ s p q T)
    (k : ι × Fin (Module.finrank ℝ F)) :
    (A.ofMemBesov φ hT).val k = (hT.localization k.1 k.2).toBesovSpace :=
  (rfl)

@[simp]
theorem besovToDistribution_ofMemBesov {T : BundleTest I F V →L_c[ℝ] ℝ}
    (hT : A.MemBesov φ s p q T) : A.besovToDistribution φ s p q (A.ofMemBesov φ hT) = T := by
  simp only [besovToDistribution_apply, ofMemBesov_apply, MemBesov.toDistr_toBesovSpace,
    reconstruction_localization]

@[simp]
theorem ofMemBesov_besovToDistribution (u : A.besovSpace φ s p q) :
    A.ofMemBesov φ (A.memBesov_besovToDistribution φ u) = u :=
  A.besovToDistribution_injective φ (A.besovToDistribution_ofMemBesov φ _)

variable (s p q) in
/-- The functionals represented by the Besov space are exactly those which are `B^s_{p,q}` with
respect to `A`. -/
theorem range_besovToDistribution :
    LinearMap.range (A.besovToDistribution φ s p q) = A.memBesovSubmodule φ s p q :=
  Submodule.ext fun _ ↦ ⟨by rintro ⟨u, rfl⟩; exact A.memBesov_besovToDistribution φ u,
    fun hT ↦ ⟨_, A.besovToDistribution_ofMemBesov φ hT⟩⟩

variable (s p q) in
/-- The Besov space is linearly equivalent to the space of functionals on bundle tests that are
`B^s_{p,q}` with respect to `A`. -/
def besovSpaceEquiv : A.besovSpace φ s p q ≃ₗ[ℝ] A.memBesovSubmodule φ s p q :=
  (LinearEquiv.ofInjective _ (A.besovToDistribution_injective φ)).trans
    (LinearEquiv.ofEq _ _ (A.range_besovToDistribution φ s p q))

@[simp]
theorem coe_besovSpaceEquiv_apply (u : A.besovSpace φ s p q) :
    (A.besovSpaceEquiv φ s p q u : BundleTest I F V →L_c[ℝ] ℝ) =
      A.besovToDistribution φ s p q u :=
  (rfl)

@[simp]
theorem besovSpaceEquiv_symm_apply (T : A.memBesovSubmodule φ s p q) :
    (A.besovSpaceEquiv φ s p q).symm T =
      A.ofMemBesov φ ((A.mem_memBesovSubmodule φ s p q).1 T.property) :=
  (A.besovSpaceEquiv φ s p q).symm_apply_eq.2 <|
    Subtype.ext (A.besovToDistribution_ofMemBesov φ _).symm

/-- Each component of an element of the Besov space has norm at most the norm of the element. -/
theorem norm_besovSpace_val_apply_le (u : A.besovSpace φ s p q) (k : ι × Fin (Module.finrank ℝ F)) :
    ‖u.val k‖ ≤ ‖u‖ := by
  rw [← Submodule.norm_coe]
  exact norm_le_pi_norm (u : ι × Fin (Module.finrank ℝ F) → BesovSpace ℂ φ s p q) k

/-- The norm of an element of the Besov space is the largest norm of its components. -/
theorem norm_besovSpace_le_iff {u : A.besovSpace φ s p q} {C : ℝ} (hC : 0 ≤ C) :
    ‖u‖ ≤ C ↔ ∀ k, ‖u.val k‖ ≤ C := by
  rw [← Submodule.norm_coe]
  exact pi_norm_le_iff_of_nonneg hC

/-- **The pinned norm.** The `B^s_{p,q}` norm of a functional which is `B^s_{p,q}` with respect to
`A` is the largest `B^s_{p,q}(E, ℂ)` norm of its localizations `χᵢ Tᵢⱼ`. -/
theorem norm_ofMemBesov_le_iff {T : BundleTest I F V →L_c[ℝ] ℝ} (hT : A.MemBesov φ s p q T)
    {C : ℝ} (hC : 0 ≤ C) :
    ‖A.ofMemBesov φ hT‖ ≤ C ↔ ∀ i j, ‖(hT.localization i j).toBesovSpace‖ ≤ C := by
  rw [A.norm_besovSpace_le_iff φ hC, Prod.forall]
  simp only [ofMemBesov_apply]

/-! ### Componentwise maps -/

/-- The componentwise application of a continuous linear map `f` between Euclidean Besov spaces
which does not change the underlying tempered distribution, as a continuous linear map between the
Besov spaces of `A`. -/
private def mapOfToDistrEq {φ' : ContDiffBump (0 : E)} {s' : ℝ} {p' q' : ℝ≥0∞} [Fact (1 ≤ p')]
    [Fact (1 ≤ q')] (f : BesovSpace ℂ φ s p q →L[ℂ] BesovSpace ℂ φ' s' p' q')
    (hf : ∀ u, (f u).toDistr = u.toDistr) :
    A.besovSpace φ s p q →L[ℝ] A.besovSpace φ' s' p' q' :=
  (((ContinuousLinearMap.pi fun k : ι × Fin (Module.finrank ℝ F) ↦
      f ∘L ContinuousLinearMap.proj k).restrictScalars ℝ) ∘L
    (A.besovSpace φ s p q).subtypeL).codRestrict (A.besovSpace φ' s' p' q') fun u ↦
    (A.mem_besovSpace φ').2 fun k ↦ by simpa [hf] using u.property k

private theorem mapOfToDistrEq_apply {φ' : ContDiffBump (0 : E)} {s' : ℝ} {p' q' : ℝ≥0∞}
    [Fact (1 ≤ p')] [Fact (1 ≤ q')] (f : BesovSpace ℂ φ s p q →L[ℂ] BesovSpace ℂ φ' s' p' q')
    (hf : ∀ u, (f u).toDistr = u.toDistr) (u : A.besovSpace φ s p q)
    (k : ι × Fin (Module.finrank ℝ F)) :
    (A.mapOfToDistrEq φ f hf u).val k = f (u.val k) :=
  (rfl)

private theorem besovToDistribution_mapOfToDistrEq {φ' : ContDiffBump (0 : E)} {s' : ℝ}
    {p' q' : ℝ≥0∞} [Fact (1 ≤ p')] [Fact (1 ≤ q')]
    (f : BesovSpace ℂ φ s p q →L[ℂ] BesovSpace ℂ φ' s' p' q')
    (hf : ∀ u, (f u).toDistr = u.toDistr) (u : A.besovSpace φ s p q) :
    A.besovToDistribution φ' s' p' q' (A.mapOfToDistrEq φ f hf u) =
      A.besovToDistribution φ s p q u := by
  simp only [besovToDistribution_apply, mapOfToDistrEq_apply, hf]

/-- A componentwise map whose components are bounded by `C` is bounded by `C`. -/
private theorem norm_mapOfToDistrEq_apply_le {φ' : ContDiffBump (0 : E)} {s' : ℝ} {p' q' : ℝ≥0∞}
    [Fact (1 ≤ p')] [Fact (1 ≤ q')] (f : BesovSpace ℂ φ s p q →L[ℂ] BesovSpace ℂ φ' s' p' q')
    (hf : ∀ u, (f u).toDistr = u.toDistr) {C : ℝ} (hC : 0 ≤ C) (hfC : ∀ u, ‖f u‖ ≤ C * ‖u‖)
    (u : A.besovSpace φ s p q) : ‖A.mapOfToDistrEq φ f hf u‖ ≤ C * ‖u‖ :=
  (A.norm_besovSpace_le_iff φ' (by positivity)).2 fun k ↦ by
    rw [mapOfToDistrEq_apply]
    exact (hfC _).trans (mul_le_mul_of_nonneg_left (A.norm_besovSpace_val_apply_le φ u k) hC)

/-! ### The inclusions between the Besov spaces -/

variable {s' : ℝ} {q' : ℝ≥0∞} [Fact (1 ≤ q')]

variable (p) in
/-- The **inclusion `B^s_{p,q} ⊆ B^{s'}_{p,q'}`** of the Besov spaces of `A`, for `s' ≤ s` and
`q ≤ q'`: the inclusion `B^s_{p,q}(E, ℂ) ⊆ B^{s'}_{p,q'}(E, ℂ)` (`TauCeti.BesovSpace.inclusion`)
in every component (`TauCeti.SquareChartPartition.besovInclusion_apply`). It represents the same
functional on bundle tests (`TauCeti.SquareChartPartition.besovToDistribution_besovInclusion`)
and does not increase the norm (`TauCeti.SquareChartPartition.norm_besovInclusion_le`). -/
def besovInclusion (hs : s' ≤ s) (hq : q ≤ q') :
    A.besovSpace φ s p q →L[ℝ] A.besovSpace φ s' p q' :=
  A.mapOfToDistrEq φ (BesovSpace.inclusion ℂ φ p hs hq) (BesovSpace.toDistr_inclusion hs hq)

@[simp]
theorem besovInclusion_apply (hs : s' ≤ s) (hq : q ≤ q') (u : A.besovSpace φ s p q)
    (k : ι × Fin (Module.finrank ℝ F)) :
    (A.besovInclusion φ p hs hq u).val k = BesovSpace.inclusion ℂ φ p hs hq (u.val k) :=
  (rfl)

/-- The inclusion `B^s_{p,q} ⊆ B^{s'}_{p,q'}` does not change the represented functional. -/
@[simp]
theorem besovToDistribution_besovInclusion (hs : s' ≤ s) (hq : q ≤ q')
    (u : A.besovSpace φ s p q) :
    A.besovToDistribution φ s' p q' (A.besovInclusion φ p hs hq u) =
      A.besovToDistribution φ s p q u :=
  A.besovToDistribution_mapOfToDistrEq φ _ _ u

@[simp]
theorem besovInclusion_ofMemBesov (hs : s' ≤ s) (hq : q ≤ q') {T : BundleTest I F V →L_c[ℝ] ℝ}
    (hT : A.MemBesov φ s p q T) :
    A.besovInclusion φ p hs hq (A.ofMemBesov φ hT) = A.ofMemBesov φ (hT.mono hs hq) :=
  A.besovToDistribution_injective φ (by simp)

theorem besovInclusion_injective (hs : s' ≤ s) (hq : q ≤ q') :
    Function.Injective (A.besovInclusion φ p hs hq) := fun u u' huu' ↦
  A.besovToDistribution_injective φ <| by
    rw [← A.besovToDistribution_besovInclusion φ hs hq u,
      ← A.besovToDistribution_besovInclusion φ hs hq u', huu']

/-- The inclusion `B^s_{p,q} ⊆ B^{s'}_{p,q'}` does not increase the norm. -/
theorem norm_besovInclusion_le (hs : s' ≤ s) (hq : q ≤ q') : ‖A.besovInclusion φ p hs hq‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one <|
    A.norm_mapOfToDistrEq_apply_le φ _ _ zero_le_one fun u ↦
      (BesovSpace.norm_inclusion_le hs hq u).trans_eq (one_mul _).symm

variable (p q q') in
/-- The **inclusion `B^s_{p,q} ⊆ B^{s'}_{p,q'}`** of the Besov spaces of `A`, for `s' < s` and
arbitrary fine indices `q, q'`: the inclusion `TauCeti.BesovSpace.inclusionOfLT` in every
component. It represents the same functional on bundle tests and has norm at most
`(1 - 2^{s' - s})⁻¹` (`TauCeti.SquareChartPartition.norm_besovInclusionOfLT_le`). -/
def besovInclusionOfLT (hs : s' < s) : A.besovSpace φ s p q →L[ℝ] A.besovSpace φ s' p q' :=
  A.mapOfToDistrEq φ (BesovSpace.inclusionOfLT ℂ φ p q q' hs) (BesovSpace.toDistr_inclusionOfLT hs)

@[simp]
theorem besovInclusionOfLT_apply (hs : s' < s) (u : A.besovSpace φ s p q)
    (k : ι × Fin (Module.finrank ℝ F)) :
    (A.besovInclusionOfLT φ p q q' hs u).val k =
      BesovSpace.inclusionOfLT ℂ φ p q q' hs (u.val k) :=
  (rfl)

/-- The inclusion `B^s_{p,q} ⊆ B^{s'}_{p,q'}`, `s' < s`, does not change the represented
functional. -/
@[simp]
theorem besovToDistribution_besovInclusionOfLT (hs : s' < s) (u : A.besovSpace φ s p q) :
    A.besovToDistribution φ s' p q' (A.besovInclusionOfLT φ p q q' hs u) =
      A.besovToDistribution φ s p q u :=
  A.besovToDistribution_mapOfToDistrEq φ _ _ u

@[simp]
theorem besovInclusionOfLT_ofMemBesov (hs : s' < s) {T : BundleTest I F V →L_c[ℝ] ℝ}
    (hT : A.MemBesov φ s p q T) :
    A.besovInclusionOfLT φ p q q' hs (A.ofMemBesov φ hT) =
      A.ofMemBesov φ (hT.of_lt hs (zero_lt_one.trans_le Fact.out).ne') :=
  A.besovToDistribution_injective φ (by simp)

/-- The inclusion `B^s_{p,q} ⊆ B^{s'}_{p,q'}`, `s' < s`, has norm at most `(1 - 2^{s' - s})⁻¹`. -/
theorem norm_besovInclusionOfLT_le (hs : s' < s) :
    ‖A.besovInclusionOfLT φ p q q' hs‖ ≤ (1 - 2 ^ (s' - s))⁻¹ := by
  have hC : (0 : ℝ) ≤ (1 - 2 ^ (s' - s))⁻¹ :=
    inv_nonneg.2 (sub_nonneg.2 (Real.rpow_le_one_of_one_le_of_nonpos one_le_two
      (sub_nonpos.2 hs.le)))
  exact ContinuousLinearMap.opNorm_le_bound _ hC <|
    A.norm_mapOfToDistrEq_apply_le φ _ _ hC fun u ↦ BesovSpace.norm_inclusionOfLT_le hs u

/-! ### Change of bump function -/

variable (s p q) in
/-- **Independence of the bump function.** The Besov spaces of `A` built from two bump functions
`φ` and `φ'` represent the same functionals on bundle tests, with equivalent norms: the
componentwise isomorphism `TauCeti.BesovSpace.bumpEquiv` is an isomorphism of Banach spaces
between them which does not change the represented functional
(`TauCeti.SquareChartPartition.besovToDistribution_besovBumpEquiv`). -/
def besovBumpEquiv (φ' : ContDiffBump (0 : E)) :
    A.besovSpace φ s p q ≃L[ℝ] A.besovSpace φ' s p q :=
  ContinuousLinearEquiv.ofContinuousLinearMap
    (A.mapOfToDistrEq φ (BesovSpace.bumpEquiv ℂ φ φ' s p q).toContinuousLinearMap
      (BesovSpace.toDistr_bumpEquiv φ'))
    (A.mapOfToDistrEq φ' (BesovSpace.bumpEquiv ℂ φ' φ s p q).toContinuousLinearMap
      (BesovSpace.toDistr_bumpEquiv φ))
    (ContinuousLinearMap.ext fun _ ↦ A.besovToDistribution_injective φ' <|
      (A.besovToDistribution_mapOfToDistrEq φ
          (BesovSpace.bumpEquiv ℂ φ φ' s p q).toContinuousLinearMap
          (BesovSpace.toDistr_bumpEquiv φ') _).trans
        (A.besovToDistribution_mapOfToDistrEq φ'
          (BesovSpace.bumpEquiv ℂ φ' φ s p q).toContinuousLinearMap
          (BesovSpace.toDistr_bumpEquiv φ) _))
    (ContinuousLinearMap.ext fun _ ↦ A.besovToDistribution_injective φ <|
      (A.besovToDistribution_mapOfToDistrEq φ'
          (BesovSpace.bumpEquiv ℂ φ' φ s p q).toContinuousLinearMap
          (BesovSpace.toDistr_bumpEquiv φ) _).trans
        (A.besovToDistribution_mapOfToDistrEq φ
          (BesovSpace.bumpEquiv ℂ φ φ' s p q).toContinuousLinearMap
          (BesovSpace.toDistr_bumpEquiv φ') _))

private theorem coe_besovBumpEquiv (φ' : ContDiffBump (0 : E)) :
    ⇑(A.besovBumpEquiv φ s p q φ') =
      A.mapOfToDistrEq φ (BesovSpace.bumpEquiv ℂ φ φ' s p q).toContinuousLinearMap
        (BesovSpace.toDistr_bumpEquiv φ') := by
  rw [besovBumpEquiv, ContinuousLinearEquiv.coe_ofContinuousLinearMap]

@[simp]
theorem besovBumpEquiv_apply (φ' : ContDiffBump (0 : E)) (u : A.besovSpace φ s p q)
    (k : ι × Fin (Module.finrank ℝ F)) :
    (A.besovBumpEquiv φ s p q φ' u).val k = BesovSpace.bumpEquiv ℂ φ φ' s p q (u.val k) := by
  rw [coe_besovBumpEquiv]
  exact A.mapOfToDistrEq_apply φ _ _ u k

/-- The change of bump function does not change the represented functional. -/
@[simp]
theorem besovToDistribution_besovBumpEquiv (φ' : ContDiffBump (0 : E))
    (u : A.besovSpace φ s p q) :
    A.besovToDistribution φ' s p q (A.besovBumpEquiv φ s p q φ' u) =
      A.besovToDistribution φ s p q u := by
  rw [coe_besovBumpEquiv]
  exact A.besovToDistribution_mapOfToDistrEq φ _ _ u

@[simp]
theorem besovBumpEquiv_symm (φ' : ContDiffBump (0 : E)) :
    (A.besovBumpEquiv φ s p q φ').symm = A.besovBumpEquiv φ' s p q φ := by
  refine ContinuousLinearEquiv.ext (funext fun u ↦ A.besovToDistribution_injective φ ?_)
  rw [besovToDistribution_besovBumpEquiv, ← A.besovToDistribution_besovBumpEquiv φ φ',
    ContinuousLinearEquiv.apply_symm_apply]

/-! ### Comparison with the Sobolev spaces -/

variable (s) in
/-- **`B^s_{2,2} = H^s` with equivalent norms.** The componentwise isomorphism
`TauCeti.BesovSpace.besselPotentialSpaceEquiv` between `B^s_{2,2}(E, ℂ)` and `H^s(E, ℂ)` is an
isomorphism of Banach spaces between the Besov space `B^s_{2,2}` and the Sobolev space `H^s` of
the same partition `A`, which does not change the represented functional on bundle tests
(`TauCeti.SquareChartPartition.toDistribution_besovSpaceEquivSobolevSpace`). -/
def besovSpaceEquivSobolevSpace : A.besovSpace φ s 2 2 ≃L[ℝ] A.sobolevSpace s :=
  ContinuousLinearEquiv.ofContinuousLinearMap
    ((((PiLp.continuousLinearEquiv 2 ℂ _).symm.toContinuousLinearMap ∘L
        ContinuousLinearMap.pi fun k : ι × Fin (Module.finrank ℝ F) ↦
          (BesovSpace.besselPotentialSpaceEquiv ℂ φ s).toContinuousLinearMap ∘L
            ContinuousLinearMap.proj k).restrictScalars ℝ ∘L
        (A.besovSpace φ s 2 2).subtypeL).codRestrict (A.sobolevSpace s) fun u ↦
      (A.mem_sobolevSpace s).2 fun k ↦ by simpa using u.property k)
    ((((ContinuousLinearMap.pi fun k : ι × Fin (Module.finrank ℝ F) ↦
          (BesovSpace.besselPotentialSpaceEquiv ℂ φ s).symm.toContinuousLinearMap ∘L
            ContinuousLinearMap.proj k) ∘L
        (PiLp.continuousLinearEquiv 2 ℂ _).toContinuousLinearMap).restrictScalars ℝ ∘L
        (A.sobolevSpace s).subtypeL).codRestrict (A.besovSpace φ s 2 2) fun v ↦
      (A.mem_besovSpace φ).2 fun k ↦ by simpa using (A.mem_sobolevSpace s).1 v.property k)
    (ContinuousLinearMap.ext fun v ↦ Subtype.ext <| PiLp.ext fun k ↦
      BesselPotentialSpace.ext (by simp))
    (ContinuousLinearMap.ext fun u ↦ Subtype.ext <| funext fun k ↦ BesovSpace.ext (by simp))

@[simp]
theorem besovSpaceEquivSobolevSpace_apply (u : A.besovSpace φ s 2 2)
    (k : ι × Fin (Module.finrank ℝ F)) :
    (A.besovSpaceEquivSobolevSpace φ s u).val k =
      BesovSpace.besselPotentialSpaceEquiv ℂ φ s (u.val k) :=
  (rfl)

@[simp]
theorem besovSpaceEquivSobolevSpace_symm_apply (v : A.sobolevSpace s)
    (k : ι × Fin (Module.finrank ℝ F)) :
    ((A.besovSpaceEquivSobolevSpace φ s).symm v).val k =
      (BesovSpace.besselPotentialSpaceEquiv ℂ φ s).symm (v.val k) :=
  (rfl)

/-- The isomorphism `B^s_{2,2} ≃ H^s` does not change the represented functional. -/
@[simp]
theorem toDistribution_besovSpaceEquivSobolevSpace (u : A.besovSpace φ s 2 2) :
    A.toDistribution s (A.besovSpaceEquivSobolevSpace φ s u) =
      A.besovToDistribution φ s 2 2 u := by
  simp [toDistribution_apply, besovToDistribution_apply]

@[simp]
theorem besovSpaceEquivSobolevSpace_ofMemBesov {T : BundleTest I F V →L_c[ℝ] ℝ}
    (hT : A.MemBesov φ s 2 2 T) :
    A.besovSpaceEquivSobolevSpace φ s (A.ofMemBesov φ hT) =
      A.ofMemSobolev s ((A.memBesov_two_two_iff_memSobolev φ).1 hT) :=
  A.toDistribution_injective s (by simp)

end BesovSpace

end SquareChartPartition

end TauCeti

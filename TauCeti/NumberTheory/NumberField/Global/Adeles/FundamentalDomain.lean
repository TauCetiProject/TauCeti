/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Group.FundamentalDomain
public import Mathlib.NumberTheory.NumberField.Discriminant.Basic
public import TauCeti.NumberTheory.NumberField.Global.Adeles.Basic
public import TauCeti.NumberTheory.NumberField.Global.Adeles.BorelSpace
import TauCeti.MeasureTheory.Group.FundamentalDomain
import TauCeti.RingTheory.DedekindDomain.AdicValuation.ValuativeRel

/-!
# A fundamental domain for a number field in its adeles

Let `K` be a number field, `K_∞` its infinite adele ring, identified with the Minkowski mixed
space `ℝ^{r₁} × ℂ^{r₂}` by `NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace`, and
`Ô = ∏_v 𝒪_v` the integral finite adeles. Let `F` be the half-open fundamental parallelotope
`ZSpan.fundamentalDomain` of the image of `𝓞_K` in the mixed space, for the basis
`NumberField.mixedEmbedding.latticeBasis K`.

The set `F × Ô` of adeles whose infinite part lies in `F` and whose finite part is integral meets
every coset of the diagonal copy of `K` exactly once. Strong approximation subtracts an element
of `K` that makes the finite part integral; what remains free is an algebraic integer, since
`K ∩ Ô = 𝓞_K`, and it is fixed uniquely by moving the infinite part into `F`. So `F × Ô` is a
measurable fundamental domain for `K` acting on the adeles, for every measure, and its closure
is compact.

For the product of Lebesgue measure on the mixed space (transported to `K_∞`) and any measure
`μ_f` on the finite adeles, `F × Ô` has measure `2^{−r₂} √|d_K| · μ_f(Ô)`, the covolume of
`𝓞_K` in the mixed space (`NumberField.mixedEmbedding.volume_fundamentalDomain_latticeBasis`)
times the mass of `Ô`. In particular it has measure one when `μ_f(Ô) = 2^{r₂} / √|d_K|`, the
normalization of Haar measure on the finite adeles for which `K` has covolume one.

The same holds coordinatewise for the vectors `K^ι ⊂ 𝔸_K^ι` over a finite type `ι`, with the
fundamental domain `(F × Ô)^ι`.

The explicit domain for `K = ℚ`, with `[0, 1)` in place of `F`, is
`TauCeti.GlobalNumberFields.ratFundamentalDomain`.

## Main definitions

* `TauCeti.GlobalNumberFields.infiniteAdeleFundamentalDomain`: the fundamental parallelotope `F`
  of `𝓞_K`, as a set of infinite adeles.
* `TauCeti.GlobalNumberFields.adeleFundamentalDomain`: the set `F × Ô` of adeles.

## Main results

* `TauCeti.GlobalNumberFields.existsUnique_sub_algebraMap_mem_adeleFundamentalDomain`: every adele
  has exactly one translate by an element of `K` in `F × Ô`.
* `TauCeti.GlobalNumberFields.isAddFundamentalDomain_adeleFundamentalDomain`: `F × Ô` is a
  fundamental domain for the diagonal copy of `K`, for every measure on the adeles.
* `TauCeti.GlobalNumberFields.isCompact_closure_adeleFundamentalDomain`: `F × Ô` is relatively
  compact.
* `TauCeti.GlobalNumberFields.measure_adeleFundamentalDomain`,
  `TauCeti.GlobalNumberFields.measure_adeleFundamentalDomain_eq_one`: the measure of `F × Ô`, and
  its value one for the self-dual normalization of `Ô`.
* `TauCeti.GlobalNumberFields.isAddFundamentalDomain_pi_adeleFundamentalDomain`,
  `TauCeti.GlobalNumberFields.measure_pi_adeleFundamentalDomain`: the same for `K^ι ⊂ 𝔸_K^ι`.

## References

* J. Tate, *Fourier analysis in number fields and Hecke's zeta-functions*, Theorem 4.1.4.
* J. W. S. Cassels and A. Fröhlich, eds., *Algebraic Number Theory*, Chapter II, §14.
-/

public section

noncomputable section

open IsDedekindDomain NumberField MeasureTheory
open scoped NumberField.AdeleRing ENNReal

namespace TauCeti.GlobalNumberFields

variable (K : Type*) [Field K] [NumberField K]

/-! ### The infinite part -/

open Classical in
/-- The half-open fundamental parallelotope of the image of `𝓞_K` in the Minkowski mixed space,
as a set of infinite adeles: the infinite adeles whose image in the mixed space lies in
`ZSpan.fundamentalDomain (mixedEmbedding.latticeBasis K)`. -/
def infiniteAdeleFundamentalDomain : Set K∞ :=
  InfiniteAdeleRing.ringEquiv_mixedSpace K ⁻¹'
    ZSpan.fundamentalDomain (mixedEmbedding.latticeBasis K)

open Classical in
variable {K} in
/-- An infinite adele lies in `F` exactly when its image in the mixed space lies in the
fundamental parallelotope of `𝓞_K`. -/
@[simp]
theorem mem_infiniteAdeleFundamentalDomain_iff {z : K∞} :
    z ∈ infiniteAdeleFundamentalDomain K ↔
      InfiniteAdeleRing.ringEquiv_mixedSpace K z ∈
        ZSpan.fundamentalDomain (mixedEmbedding.latticeBasis K) :=
  Iff.rfl

open Classical in
/-- The fundamental parallelotope `F` is a measurable set of infinite adeles. -/
theorem measurableSet_infiniteAdeleFundamentalDomain :
    MeasurableSet (infiniteAdeleFundamentalDomain K) :=
  (InfiniteAdeleRing.continuous_ringEquiv_mixedSpace K).measurable
    (ZSpan.fundamentalDomain_measurableSet _)

open Classical in
/-- The image of an algebraic integer in the mixed space, as a point of the lattice spanned by
`mixedEmbedding.latticeBasis K`. -/
private def latticePoint (y : 𝓞 K) :
    Submodule.span ℤ (Set.range (mixedEmbedding.latticeBasis K)) :=
  ⟨mixedEmbedding K (algebraMap (𝓞 K) K y),
    (mixedEmbedding.mem_span_latticeBasis K).2 ⟨y, rfl⟩⟩

private theorem coe_latticePoint (y : 𝓞 K) :
    (latticePoint K y : mixedEmbedding.mixedSpace K) = mixedEmbedding K (algebraMap (𝓞 K) K y) :=
  (rfl)

private theorem latticePoint_injective : Function.Injective (latticePoint K) := fun _ _ h ↦
  FaithfulSMul.algebraMap_injective (𝓞 K) K <|
    mixedEmbedding_injective K (congrArg Subtype.val h)

private theorem latticePoint_surjective : Function.Surjective (latticePoint K) := by
  rintro ⟨v, hv⟩
  obtain ⟨y, rfl⟩ := (mixedEmbedding.mem_span_latticeBasis K).1 hv
  exact ⟨y, rfl⟩

open Classical in
/-- Translating an infinite adele by an algebraic integer `y` moves its image in the mixed space
by the lattice point of `-y`. -/
private theorem sub_algebraMap_mem_infiniteAdeleFundamentalDomain_iff (z : K∞) (y : 𝓞 K) :
    z - algebraMap K K∞ (algebraMap (𝓞 K) K y) ∈ infiniteAdeleFundamentalDomain K ↔
      latticePoint K (-y) +ᵥ InfiniteAdeleRing.ringEquiv_mixedSpace K z ∈
        ZSpan.fundamentalDomain (mixedEmbedding.latticeBasis K) := by
  rw [mem_infiniteAdeleFundamentalDomain_iff, Submodule.vadd_def, vadd_eq_add, coe_latticePoint,
    map_sub, ← InfiniteAdeleRing.mixedEmbedding_eq_algebraMap_comp, map_neg, map_neg,
    neg_add_eq_sub]

open Classical in
/-- Every infinite adele has exactly one translate by an algebraic integer in the fundamental
parallelotope of `𝓞_K`. -/
theorem existsUnique_sub_algebraMap_mem_infiniteAdeleFundamentalDomain (z : K∞) :
    ∃! y : 𝓞 K,
      z - algebraMap K K∞ (algebraMap (𝓞 K) K y) ∈ infiniteAdeleFundamentalDomain K := by
  obtain ⟨v, hv, hvu⟩ := ZSpan.exist_unique_vadd_mem_fundamentalDomain
    (mixedEmbedding.latticeBasis K) (InfiniteAdeleRing.ringEquiv_mixedSpace K z)
  obtain ⟨y, rfl⟩ := latticePoint_surjective K v
  refine ⟨-y, ?_, fun y' hy' ↦ ?_⟩
  · beta_reduce
    rwa [sub_algebraMap_mem_infiniteAdeleFundamentalDomain_iff, neg_neg]
  · beta_reduce at hy'
    rw [sub_algebraMap_mem_infiniteAdeleFundamentalDomain_iff] at hy'
    exact neg_eq_iff_eq_neg.mp (latticePoint_injective K (hvu _ hy'))

/-! ### The fundamental domain in the adeles -/

/-- The fundamental domain `F × Ô` of `K` in its adeles: the adeles whose infinite part lies in
the fundamental parallelotope of `𝓞_K` and whose finite part is integral. -/
def adeleFundamentalDomain : Set 𝔸[K] :=
  infiniteAdeleFundamentalDomain K ×ˢ
    (FiniteAdeleRing.integralAdeles (𝓞 K) K : Set 𝔸ᶠ[K])

variable {K} in
/-- An adele lies in `F × Ô` exactly when its infinite part lies in `F` and its finite part is
integral. -/
@[simp]
theorem mem_adeleFundamentalDomain_iff {a : 𝔸[K]} :
    a ∈ adeleFundamentalDomain K ↔
      a.1 ∈ infiniteAdeleFundamentalDomain K ∧ a.2 ∈ FiniteAdeleRing.integralAdeles (𝓞 K) K :=
  Iff.rfl

/-- **A fundamental domain for `K` in its adeles.** Every adele has exactly one translate by an
element of `K` in `F × Ô`. -/
theorem existsUnique_sub_algebraMap_mem_adeleFundamentalDomain (a : 𝔸[K]) :
    ∃! x : K, a - algebraMap K 𝔸[K] x ∈ adeleFundamentalDomain K := by
  simp only [mem_adeleFundamentalDomain_iff, AdeleRing.fst_sub, AdeleRing.snd_sub,
    AdeleRing.algebraMap_fst_def, AdeleRing.algebraMap_snd_def]
  -- Strong approximation makes the finite part integral after subtracting some `x ∈ K`.
  obtain ⟨x, hx⟩ := FiniteAdeleRing.exists_sub_algebraMap_mem_integralAdeles a.2
  -- The remaining freedom is an algebraic integer, which is fixed by the infinite part.
  obtain ⟨y, hy, hyu⟩ :=
    existsUnique_sub_algebraMap_mem_infiniteAdeleFundamentalDomain K (a.1 - algebraMap K K∞ x)
  refine ⟨x + algebraMap (𝓞 K) K y, ⟨?_, ?_⟩, fun x' hx' ↦ ?_⟩
  · rwa [map_add, sub_add_eq_sub_sub]
  · exact FiniteAdeleRing.sub_algebraMap_add_algebraMap_mem_integralAdeles hx y
  · obtain ⟨hx'i, hx'f⟩ := hx'
    -- `x' - x` is integral at every finite place, so it is an algebraic integer `y'`.
    have hint : algebraMap K 𝔸ᶠ[K] (x' - x) ∈ FiniteAdeleRing.integralAdeles (𝓞 K) K := by
      have := sub_mem hx hx'f
      rwa [sub_sub_sub_cancel_left, ← map_sub] at this
    obtain ⟨y', hy'⟩ := (FiniteAdeleRing.algebraMap_mem_integralAdeles_iff (x' - x)).mp hint
    rw [eq_sub_iff_add_eq'] at hy'
    rw [← hy', map_add, ← sub_sub] at hx'i
    rw [← hy', hyu y' hx'i]

/-- The fundamental domain `F × Ô` is measurable. -/
theorem measurableSet_adeleFundamentalDomain : MeasurableSet (adeleFundamentalDomain K) :=
  (measurableSet_infiniteAdeleFundamentalDomain K).prod
    (FiniteAdeleRing.isClosed_integralAdeles (𝓞 K) K).measurableSet

/-- **`F × Ô` is a fundamental domain for `K` acting on its adeles**, for every measure on the
adeles. -/
theorem isAddFundamentalDomain_adeleFundamentalDomain (μ : Measure 𝔸[K]) :
    IsAddFundamentalDomain (AdeleRing.principalSubgroup (𝓞 K) K) (adeleFundamentalDomain K) μ :=
  .of_existsUnique_sub (algebraMap K 𝔸[K]) (fun _ ↦ Iff.rfl)
    (measurableSet_adeleFundamentalDomain K).nullMeasurableSet
    (existsUnique_sub_algebraMap_mem_adeleFundamentalDomain K)

/-- The fundamental domain `F × Ô` is relatively compact: it lies in the product of the closed
fundamental parallelepiped of `𝓞_K` with `Ô`, which is compact. -/
theorem isCompact_closure_adeleFundamentalDomain :
    IsCompact (closure (adeleFundamentalDomain K)) := by
  classical
  let e := InfiniteAdeleRing.ringEquiv_mixedSpace K
  let C : Set 𝔸[K] := (e.symm '' parallelepiped (mixedEmbedding.latticeBasis K)) ×ˢ
    (FiniteAdeleRing.integralAdeles (𝓞 K) K : Set 𝔸ᶠ[K])
  have hC : IsCompact C :=
    ((mixedEmbedding.latticeBasis K).parallelepiped.isCompact.image
      (InfiniteAdeleRing.continuous_ringEquiv_mixedSpace_symm K)).prod
      FiniteAdeleRing.isCompact_integralAdeles
  have hDC : adeleFundamentalDomain K ⊆ C := by
    intro a ha
    rw [mem_adeleFundamentalDomain_iff] at ha
    refine Set.mem_prod.mpr ⟨⟨e a.1, ?_, e.symm_apply_apply _⟩, ha.2⟩
    exact ZSpan.fundamentalDomain_subset_parallelepiped _ ha.1
  exact hC.of_isClosed_subset isClosed_closure (closure_minimal hDC hC.isClosed)

/-! ### The measure of the fundamental domain -/

open Classical in
/-- **The measure of `F × Ô`.** For Lebesgue measure on the mixed space, transported to the
infinite adeles, and any s-finite measure `μ` on the finite adeles, the fundamental domain
`F × Ô` has measure `2^{−r₂} √|d_K| · μ(Ô)`. -/
theorem measure_adeleFundamentalDomain (μ : Measure 𝔸ᶠ[K]) [SFinite μ] :
    ((volume.map (InfiniteAdeleRing.ringEquiv_mixedSpace K).symm).prod μ)
        (adeleFundamentalDomain K) =
      (2 : ℝ≥0∞)⁻¹ ^ InfinitePlace.nrComplexPlaces K * NNReal.sqrt ‖discr K‖₊ *
        μ (FiniteAdeleRing.integralAdeles (𝓞 K) K) := by
  rw [adeleFundamentalDomain, Measure.prod_prod,
    Measure.map_apply (InfiniteAdeleRing.continuous_ringEquiv_mixedSpace_symm K).measurable
      (measurableSet_infiniteAdeleFundamentalDomain K),
    infiniteAdeleFundamentalDomain, Set.preimage_preimage]
  simp only [RingEquiv.apply_symm_apply, Set.preimage_id',
    mixedEmbedding.volume_fundamentalDomain_latticeBasis]

open Classical in
/-- **`K` has covolume one in its adeles** for the normalization `μ(Ô) = 2^{r₂} / √|d_K|` of the
measure on the finite adeles: then `F × Ô` has measure one. -/
theorem measure_adeleFundamentalDomain_eq_one (μ : Measure 𝔸ᶠ[K]) [SFinite μ]
    (hμ : μ (FiniteAdeleRing.integralAdeles (𝓞 K) K) =
      2 ^ InfinitePlace.nrComplexPlaces K / NNReal.sqrt ‖discr K‖₊) :
    ((volume.map (InfiniteAdeleRing.ringEquiv_mixedSpace K).symm).prod μ)
        (adeleFundamentalDomain K) = 1 := by
  have hd : (NNReal.sqrt ‖discr K‖₊ : ℝ≥0∞) ≠ 0 := by
    simpa using discr_ne_zero K
  rw [measure_adeleFundamentalDomain, hμ, mul_assoc, ENNReal.mul_div_cancel hd ENNReal.coe_ne_top,
    ← ENNReal.inv_pow, ENNReal.inv_mul_cancel (pow_ne_zero _ two_ne_zero)
      (ENNReal.pow_ne_top ENNReal.ofNat_ne_top)]

/-! ### Vectors -/

variable {ι : Type*}

/-- Every adelic vector has exactly one translate by a vector over `K` in `(F × Ô)^ι`. -/
theorem existsUnique_sub_algebraMap_mem_pi_adeleFundamentalDomain (a : ι → 𝔸[K]) :
    ∃! x : ι → K, (fun i ↦ a i - algebraMap K 𝔸[K] (x i)) ∈
      Set.univ.pi fun _ ↦ adeleFundamentalDomain K := by
  choose x hx hxu using fun i ↦ existsUnique_sub_algebraMap_mem_adeleFundamentalDomain K (a i)
  exact ⟨x, fun i _ ↦ hx i, fun x' hx' ↦ funext fun i ↦ hxu i (x' i) (hx' i trivial)⟩

/-- **`(F × Ô)^ι` is a fundamental domain for `K^ι` acting on `𝔸_K^ι`**, for every measure. -/
theorem isAddFundamentalDomain_pi_adeleFundamentalDomain [Countable ι]
    (μ : Measure (ι → 𝔸[K])) :
    IsAddFundamentalDomain
      (AddSubgroup.pi Set.univ fun _ : ι ↦ AdeleRing.principalSubgroup (𝓞 K) K)
      (Set.univ.pi fun _ ↦ adeleFundamentalDomain K) μ := by
  refine .of_existsUnique_sub ((algebraMap K 𝔸[K]).toAddMonoidHom.compLeft ι) (fun g ↦ ?_)
    (MeasurableSet.univ_pi fun _ ↦ measurableSet_adeleFundamentalDomain K).nullMeasurableSet
    (existsUnique_sub_algebraMap_mem_pi_adeleFundamentalDomain K)
  refine (AddSubgroup.mem_pi _).trans ⟨fun hg ↦ ?_, fun ⟨x, hx⟩ i _ ↦ ⟨x i, congrFun hx i⟩⟩
  choose x hx using fun i ↦ hg i trivial
  exact ⟨x, funext hx⟩

open Classical in
/-- **The measure of `(F × Ô)^ι`** is the `#ι`-th power of that of `F × Ô`. -/
theorem measure_pi_adeleFundamentalDomain [Fintype ι] (μ : Measure 𝔸ᶠ[K]) [SigmaFinite μ] :
    Measure.pi (fun _ : ι ↦ (volume.map (InfiniteAdeleRing.ringEquiv_mixedSpace K).symm).prod μ)
        (Set.univ.pi fun _ ↦ adeleFundamentalDomain K) =
      ((2 : ℝ≥0∞)⁻¹ ^ InfinitePlace.nrComplexPlaces K * NNReal.sqrt ‖discr K‖₊ *
        μ (FiniteAdeleRing.integralAdeles (𝓞 K) K)) ^ Fintype.card ι := by
  rw [Measure.pi_pi, measure_adeleFundamentalDomain, Finset.prod_const, Finset.card_univ]

end TauCeti.GlobalNumberFields

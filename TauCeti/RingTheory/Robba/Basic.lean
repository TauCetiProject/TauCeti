/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.Subalgebra.Lattice
public import TauCeti.RingTheory.Robba.LaurentGauss
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Topology.Instances.Int
import TauCeti.Analysis.Normed.Group.Pi

/-!
# The Robba ring and its annular coefficient algebras

Let `R` be a normed ring with an ultrametric norm. A two-sided coefficient family `a : ℤ → R`
gives a formal Laurent series `∑_{n ∈ ℤ} aₙ tⁿ`. This file constructs the rings of such series
converging on half-open annuli `r < |t| < 1` and their union, the Robba ring.

* At a radius `ρ`, `TauCeti.LaurentConvergesAt ρ a` says `‖aₙ‖ ρⁿ → 0` as `|n| → ∞`, the condition
  for `∑ aₙ tⁿ` to converge on the circle `|t| = ρ`, and `TauCeti.laurentGaussNorm ρ a` is the
  Gauss norm `|a|_ρ = sup_n ‖aₙ‖ ρⁿ`.
* `TauCeti.annularCoeff R r` is the `R`-module of families converging at every radius `ρ` with
  `0 < ρ`, `r < ρ < 1`: the series on the annulus `r < |t| < 1` (the punctured open unit disc when
  `r ≤ 0`).
* `TauCeti.robbaCoeff R` is the directed union of these modules over `r < 1`: the series converging
  on some annulus `r < |t| < 1`.
* `TauCeti.RobbaRing R` is `robbaCoeff R` with the convolution product
  `(ab)ₙ = ∑_{i ∈ ℤ} aᵢ bₙ₋ᵢ`, a ring when `R` is a complete ultrametric normed ring, and a
  commutative `R`-algebra when `R` is moreover commutative: over a complete ultrametric
  seminormed ring `robbaCoeff R` satisfies
  `TauCeti.IsConvolutionRing`, which supplies these structures, the monomials and the integral
  subring `TauCeti.IsConvolutionRing.integral (robbaCoeff R)` (`R^int`). It contains the annular
  algebras `TauCeti.RobbaRing.annulus R r` and the subalgebra `TauCeti.RobbaRing.bounded R` of
  series with bounded coefficients (the bounded Robba ring, written `R^bd` or `E†`).

The radiuswise convergence and Gauss bounds for convolution come from
`TauCeti.RingTheory.Robba.LaurentGauss`. The Fréchet and inductive-limit topologies are not
constructed here.

## Main definitions

* `TauCeti.LaurentConvergesAt`, `TauCeti.laurentGaussNorm`: convergence and the Gauss norm at a
  radius.
* `TauCeti.annularCoeff`, `TauCeti.robbaCoeff`: the coefficient modules of an annulus and of the
  Robba ring.
* `TauCeti.RobbaRing`: the Robba ring, with its `Ring`, `CommRing` and `Algebra` instances from
  `TauCeti.instIsConvolutionRingRobbaCoeff`.
* `TauCeti.RobbaRing.annulus`, `TauCeti.RobbaRing.bounded`: the annular and bounded subrings.

## Main results

* `TauCeti.RobbaRing.isUnit_monomial_bounded`: `t` is a unit of the bounded Robba ring.
* `TauCeti.RobbaRing.iSup_annulus`: the Robba ring is the union of its annular algebras.

## References

* K. S. Kedlaya, *Local monodromy of p-adic differential equations: an overview*, Int. J. Number
  Theory 1 (2005), Definition 3.5.1.
* K. S. Kedlaya, *A p-adic local monodromy theorem*, Ann. of Math. 160 (2004), §2.3.
* M. Lazard, *Les zéros des fonctions analytiques d'une variable sur un corps valué complet*,
  Publ. Math. IHÉS 14 (1962), §2.
-/

public section

open Filter Topology
open scoped DiscreteConvolution

namespace TauCeti

variable {R : Type*}

/-! ### The annular coefficient modules and the Robba coefficient module -/

section Coeff

variable (R) [SeminormedRing R]

/-- The `R`-module of coefficient families `a : ℤ → R` whose Laurent series converge on the annulus
`r < |t| < 1`: `‖aₙ‖ ρⁿ → 0` as `|n| → ∞` for every radius `0 < ρ` with `r < ρ < 1`. For `r ≤ 0`
the annulus is the punctured open unit disc. -/
def annularCoeff (r : ℝ) : Submodule R (ℤ → R) where
  carrier := {a | ∀ ρ, 0 < ρ → r < ρ → ρ < 1 → LaurentConvergesAt ρ a}
  zero_mem' _ _ _ _ := laurentConvergesAt_zero _
  add_mem' ha hb ρ h₀ hr h₁ := (ha ρ h₀ hr h₁).add (hb ρ h₀ hr h₁)
  smul_mem' c _ ha ρ h₀ hr h₁ := (ha ρ h₀ hr h₁).smul c

variable {R}

theorem mem_annularCoeff {r : ℝ} {a : ℤ → R} :
    a ∈ annularCoeff R r ↔ ∀ ρ, 0 < ρ → r < ρ → ρ < 1 → LaurentConvergesAt ρ a :=
  (Iff.rfl)

/-- A smaller inner radius is a larger annulus, so it has fewer convergent series. -/
theorem annularCoeff_mono {r s : ℝ} (h : r ≤ s) : annularCoeff R r ≤ annularCoeff R s :=
  fun _ ha ρ h₀ hs h₁ ↦ ha ρ h₀ (h.trans_lt hs) h₁

theorem single_mem_annularCoeff (r : ℝ) (n : ℤ) (c : R) :
    Pi.single n c ∈ annularCoeff R r :=
  fun ρ _ _ _ ↦ laurentConvergesAt_single ρ n c

variable (R) in
/-- The `R`-module of coefficient families of the Robba ring: the families whose Laurent series
converge on some annulus `r < |t| < 1`. It is the directed union of the modules
`TauCeti.annularCoeff R r` over `r < 1` (`TauCeti.iSup_annularCoeff`). -/
def robbaCoeff : Submodule R (ℤ → R) where
  carrier := {a | ∃ r < 1, a ∈ annularCoeff R r}
  zero_mem' := ⟨0, zero_lt_one, zero_mem _⟩
  add_mem' := fun ⟨r, hr, ha⟩ ⟨s, hs, hb⟩ ↦ ⟨max r s, max_lt hr hs,
    add_mem (annularCoeff_mono (le_max_left r s) ha) (annularCoeff_mono (le_max_right r s) hb)⟩
  smul_mem' c _ := fun ⟨r, hr, ha⟩ ↦ ⟨r, hr, Submodule.smul_mem _ c ha⟩

theorem mem_robbaCoeff {a : ℤ → R} : a ∈ robbaCoeff R ↔ ∃ r < 1, a ∈ annularCoeff R r :=
  (Iff.rfl)

theorem annularCoeff_le_robbaCoeff {r : ℝ} (hr : r < 1) : annularCoeff R r ≤ robbaCoeff R :=
  fun _ ha ↦ ⟨r, hr, ha⟩

/-- The Robba coefficient module is the union of the annular coefficient modules over the inner
radii `r < 1`. -/
theorem iSup_annularCoeff : ⨆ r : Set.Iio (1 : ℝ), annularCoeff R r = robbaCoeff R :=
  le_antisymm (iSup_le fun r ↦ annularCoeff_le_robbaCoeff r.property) fun _ ⟨r, hr, ha⟩ ↦
    Submodule.mem_iSup_of_mem (⟨r, hr⟩ : Set.Iio (1 : ℝ)) ha

/-- **A Robba coefficient family is one converging at every radius `ρ < 1` close enough to `1`.** -/
theorem mem_robbaCoeff_iff_eventually {a : ℤ → R} :
    a ∈ robbaCoeff R ↔ ∀ᶠ ρ in 𝓝[<] (1 : ℝ), LaurentConvergesAt ρ a := by
  refine ⟨fun ⟨r, hr, ha⟩ ↦ ?_, fun h ↦ ?_⟩
  · filter_upwards [Ioo_mem_nhdsLT (max_lt hr zero_lt_one)] with ρ hρ
    exact ha ρ ((le_max_right r 0).trans_lt hρ.1) ((le_max_left r 0).trans_lt hρ.1) hρ.2
  · obtain ⟨l, hl, hsub⟩ := mem_nhdsLT_iff_exists_Ioo_subset.1 h
    exact ⟨l, hl, fun ρ _ hlρ hρ ↦ hsub ⟨hlρ, hρ⟩⟩

/-- A property holding at every radius close enough to `1` holds at some positive radius. -/
private theorem exists_pos_of_eventually {p : ℝ → Prop} (h : ∀ᶠ ρ in 𝓝[<] (1 : ℝ), p ρ) :
    ∃ ρ, 0 < ρ ∧ p ρ :=
  have h₀ : ∀ᶠ ρ in 𝓝[<] (1 : ℝ), ρ ∈ Set.Ioo 0 1 := Ioo_mem_nhdsLT zero_lt_one
  (h₀.and h).exists.imp fun _ h ↦ ⟨h.1.1, h.2⟩

/-- The coefficients of a Robba coefficient family tend to zero at `-∞`. -/
theorem tendsto_atBot_of_mem_robbaCoeff {a : ℤ → R} (ha : a ∈ robbaCoeff R) :
    Tendsto a atBot (𝓝 0) := by
  obtain ⟨ρ, h₀, ha, h₁⟩ := exists_pos_of_eventually <|
    (mem_robbaCoeff_iff_eventually.1 ha).and self_mem_nhdsWithin
  exact ha.tendsto_atBot h₀ (le_of_lt h₁)

/-- The family equal to `1` in every negative degree and to `0` elsewhere does not tend to zero at
`-∞`. -/
theorem not_tendsto_indicator_Iio_one_atBot [NormOneClass R] :
    ¬ Tendsto ((Set.Iio (0 : ℤ)).indicator (1 : ℤ → R)) atBot (𝓝 0) := fun h ↦ by
  have h₁ : Tendsto (fun n ↦ ‖(Set.Iio (0 : ℤ)).indicator (1 : ℤ → R) n‖) atBot (𝓝 1) :=
    tendsto_const_nhds.congr' <| (eventually_lt_atBot 0).mono fun n hn ↦ by
      beta_reduce
      rw [Set.indicator_of_mem (Set.mem_Iio.2 hn), Pi.one_apply, norm_one]
  exact one_ne_zero <| tendsto_nhds_unique h₁ (by simpa using Tendsto.norm h)

/-- The family equal to `1` in every negative degree and to `0` elsewhere converges on no annulus:
its coefficients do not tend to zero at `-∞`. -/
theorem indicator_Iio_one_notMem_robbaCoeff [NormOneClass R] :
    (Set.Iio 0).indicator 1 ∉ robbaCoeff R := fun h ↦
  not_tendsto_indicator_Iio_one_atBot (tendsto_atBot_of_mem_robbaCoeff h)

end Coeff

section Mul

variable [SeminormedRing R] [IsUltrametricDist R]

/-- The convolution of two families converging on the annulus `r < |t| < 1` converges there. -/
theorem addRingConvolution_mem_annularCoeff {r : ℝ} {a b : ℤ → R} (ha : a ∈ annularCoeff R r)
    (hb : b ∈ annularCoeff R r) : a ⋆ᵣ₊ b ∈ annularCoeff R r :=
  fun ρ h₀ hr h₁ ↦ (ha ρ h₀ hr h₁).addRingConvolution h₀ (hb ρ h₀ hr h₁)

theorem addRingConvolution_mem_robbaCoeff {a b : ℤ → R} (ha : a ∈ robbaCoeff R)
    (hb : b ∈ robbaCoeff R) : a ⋆ᵣ₊ b ∈ robbaCoeff R := by
  obtain ⟨r, hr, ha⟩ := ha
  obtain ⟨s, hs, hb⟩ := hb
  exact annularCoeff_le_robbaCoeff (max_lt hr hs) <| addRingConvolution_mem_annularCoeff
    (annularCoeff_mono (le_max_left r s) ha) (annularCoeff_mono (le_max_right r s) hb)

theorem addConvolutionExists_of_mem_robbaCoeff [CompleteSpace R] {a b : ℤ → R}
    (ha : a ∈ robbaCoeff R) (hb : b ∈ robbaCoeff R) :
    DiscreteConvolution.AddConvolutionExists (.mul ℕ R) a b := by
  obtain ⟨ρ, h₀, ha, hb⟩ := exists_pos_of_eventually <|
    (mem_robbaCoeff_iff_eventually.1 ha).and (mem_robbaCoeff_iff_eventually.1 hb)
  exact ha.addConvolutionExists h₀ hb

/-- Over a complete ultrametric seminormed ring the Robba coefficient families satisfy the
`IsConvolutionRing` hypotheses; they form a ring under convolution when `R` is moreover normed
(hence `T3`). -/
instance instIsConvolutionRingRobbaCoeff [CompleteSpace R] : IsConvolutionRing (robbaCoeff R) where
  single_mem n c := annularCoeff_le_robbaCoeff zero_lt_one (single_mem_annularCoeff 0 n c)
  addRingConvolution_mem := addRingConvolution_mem_robbaCoeff
  addConvolutionExists := addConvolutionExists_of_mem_robbaCoeff
  summable_sigma_addFiber_mul_mul ha hb hc := by
    obtain ⟨ρ, h₀, ha, hb, hc⟩ := exists_pos_of_eventually <|
      (mem_robbaCoeff_iff_eventually.1 ha).and <|
        (mem_robbaCoeff_iff_eventually.1 hb).and (mem_robbaCoeff_iff_eventually.1 hc)
    exact ha.summable_sigma_addFiber_mul_mul h₀ hb hc

end Mul

/-! ### The Robba ring -/

variable (R) in
/-- **The Robba ring** `R_R`: the Laurent series `∑_{n ∈ ℤ} aₙ tⁿ` with coefficients in `R`
converging on some annulus `r < |t| < 1`, with the convolution product
`(ab)ₙ = ∑_{i ∈ ℤ} aᵢ bₙ₋ᵢ`. Its ring structure needs `R` normed (not just seminormed), complete
and ultrametric (`TauCeti.instIsConvolutionRingRobbaCoeff` and
`TauCeti.IsConvolutionRing.instRing`). -/
abbrev RobbaRing [SeminormedRing R] : Type _ :=
  robbaCoeff R

namespace RobbaRing

open IsConvolutionRing

section CommRing

variable [NormedCommRing R] [IsUltrametricDist R] [CompleteSpace R]

/-! ### Annular, bounded and integral subrings -/

variable (R) in
/-- The subalgebra `A(r, 1)` of the Robba ring of series converging on the annulus
`r < |t| < 1`. -/
def annulus (r : ℝ) : Subalgebra R (RobbaRing R) where
  carrier := {f | (f : ℤ → R) ∈ annularCoeff R r}
  mul_mem' hf hg := addRingConvolution_mem_annularCoeff hf hg
  add_mem' {f g} hf hg := (Submodule.add_mem _ hf hg : (f : ℤ → R) + g ∈ annularCoeff R r)
  algebraMap_mem' c := by simpa using single_mem_annularCoeff r 0 c

@[simp]
theorem mem_annulus {r : ℝ} {f : RobbaRing R} : f ∈ annulus R r ↔ (f : ℤ → R) ∈ annularCoeff R r :=
  (Iff.rfl)

theorem annulus_mono {r s : ℝ} (h : r ≤ s) : annulus R r ≤ annulus R s :=
  fun _ hf ↦ annularCoeff_mono h hf

/-- Every monomial `c tⁿ` converges on every annulus. -/
theorem monomial_mem_annulus (r : ℝ) (n : ℤ) (c : R) : monomial n c ∈ annulus R r := by
  simpa using single_mem_annularCoeff r n c

/-- **The Robba ring is the directed union of its annular subalgebras** over the inner radii
`r < 1`. -/
theorem iSup_annulus : ⨆ r : Set.Iio (1 : ℝ), annulus R r = ⊤ :=
  eq_top_iff.2 fun f _ ↦ by
    obtain ⟨r, hr, hf⟩ := f.property
    exact Algebra.mem_iSup_of_mem (⟨r, hr⟩ : Set.Iio (1 : ℝ)) hf

variable (R) in
/-- **The bounded Robba ring** `R^bd`, also written `E†`: the subalgebra of series with bounded
coefficients. -/
def bounded : Subalgebra R (RobbaRing R) where
  carrier := {f | BddAbove (Set.range fun n ↦ ‖(f : ℤ → R) n‖)}
  mul_mem' := by
    rintro f g ⟨A, hA⟩ ⟨B, hB⟩
    exact ⟨A * B, Set.forall_mem_range.2 <|
      DiscreteConvolution.norm_addRingConvolution_apply_le (fun n ↦ hA ⟨n, rfl⟩)
        (fun n ↦ hB ⟨n, rfl⟩)⟩
  add_mem' := by
    rintro f g ⟨A, hA⟩ ⟨B, hB⟩
    refine ⟨max A B, Set.forall_mem_range.2 fun n ↦ ?_⟩
    exact (IsUltrametricDist.norm_add_le_max _ _).trans
      (max_le_max (hA ⟨n, rfl⟩) (hB ⟨n, rfl⟩))
  algebraMap_mem' c := ⟨‖c‖, Set.forall_mem_range.2 fun n ↦ by
    simpa using Pi.norm_single_apply_le (E := fun _ ↦ R) 0 n c⟩

@[simp]
theorem mem_bounded {f : RobbaRing R} :
    f ∈ bounded R ↔ BddAbove (Set.range fun n ↦ ‖(f : ℤ → R) n‖) :=
  (Iff.rfl)

/-- Every monomial `c tⁿ` has bounded coefficients. -/
theorem monomial_mem_bounded (n : ℤ) (c : R) : monomial n c ∈ bounded R :=
  ⟨‖c‖, Set.forall_mem_range.2 fun m ↦ by
    simpa using Pi.norm_single_apply_le (E := fun _ ↦ R) n m c⟩

/-- A monomial `a tⁿ` with a unit coefficient is a unit of the bounded Robba ring: its inverse
`a⁻¹ t⁻ⁿ` is bounded too. In particular `t` is a unit of `R^bd`. -/
theorem isUnit_monomial_bounded (n : ℤ) {a : R} (ha : IsUnit a) :
    IsUnit (⟨monomial n a, monomial_mem_bounded n a⟩ : bounded R) := by
  obtain ⟨u, rfl⟩ := ha
  exact isUnit_iff_exists.2 ⟨⟨monomial (-n) ↑u⁻¹, monomial_mem_bounded _ _⟩,
    Subtype.ext (by simp), Subtype.ext (by simp)⟩

variable [NormOneClass R]

/-- Integral series have bounded coefficients. -/
theorem integral_le_bounded : integral (robbaCoeff R) ≤ (bounded R).toSubring :=
  fun _ hf ↦ ⟨1, Set.forall_mem_range.2 (mem_integral.1 hf)⟩

end CommRing

end RobbaRing

end TauCeti

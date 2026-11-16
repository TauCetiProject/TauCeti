/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Vortex.Divisor
public import TauCeti.Analysis.PDE.Vortex.FramedGauge.Limit
public import TauCeti.Analysis.Sobolev.BesselPotential.Inclusion
import TauCeti.Analysis.Sobolev.BesselPotential.Embedding

/-!
# The Sobolev topology on framed plane vortex fields and the closed gauge orbit relation

Framed degree-`m` plane vortex fields form the affine space `A_m^s = x_m + H^s(ℂ; ℝ⁴)`
(`TauCeti.Vortex.framedFieldSpace`), centred at the smooth reference field `x_m`
(`TauCeti.Vortex.referenceField`). Its elements are pointwise representatives, and for `s > 1`
every one of them agrees almost everywhere with a continuous field, by the Sobolev embedding
(`TemperedDistribution.exists_contDiff_ae_eq_of_mem_realSobolevFunctions`). The
continuous fields of `A_m^s` therefore represent its classes exactly once. They form the type
`TauCeti.Vortex.SobolevFieldSpace f m s`, and this file gives it the topology of `A_m^s` as an
affine Hilbert space: a field `x` is recorded by the four coordinates of `x - x_m` in `H^s(ℂ)`
(`TauCeti.Vortex.SobolevFieldSpace.subRef`), each the complexification of a real coordinate
function, and the topology is the one induced by this injective map
(`TauCeti.Vortex.SobolevFieldSpace.isEmbedding_subRef`). It is Hausdorff.

For `s > 1`, convergence in this topology is uniform convergence of the fields
(`TauCeti.Vortex.SobolevFieldSpace.tendstoUniformly_of_tendsto`), by the quantitative Sobolev
embedding `|g(z)| ≤ C ‖g‖_{H^s}` for continuous representatives
(`TemperedDistribution.tendstoUniformly_of_tendsto_toBesselPotentialSpace`). Two consequences
for the gauge theory of `A_m^k` follow from the locally uniform statements already available.

* **The divisor is continuous.** If fields converge in `A_m^s`, `s > 1`, the zero divisors of
  their sections converge in `Sym ℂ m`
  (`TauCeti.Vortex.SobolevFieldSpace.tendsto_of_tendsto`), by Hurwitz's theorem
  (`TauCeti.Vortex.tendsto_of_tendstoLocallyUniformly`).
* **The gauge orbit relation is closed.** For an integer `k ≥ 3`, the pairs `(x, y)` of
  continuous fields of `A_m^k` with `y = u · x` for some `u` in the Sobolev gauge group `G_(k+1)`
  (`TauCeti.Vortex.sobolevGaugeGroup`) form a closed subset of the product
  (`TauCeti.Vortex.SobolevFieldSpace.isClosed_setOf_exists_gaugeTransform_eq`), by the limit
  theorem for gauge equivalences
  (`TauCeti.Vortex.exists_mem_sobolevGaugeGroup_gaugeTransform_eq_and_tendstoLocallyUniformly`).
  This is the Hausdorff property of the quotient `A_m^k / G_(k+1)` once the quotient map is
  known to be open.

Continuity of the gauge action on `A_m^k`, the slice theorem and the openness of the quotient map
are not treated here.

## Main definitions

* `TauCeti.Vortex.SobolevFieldSpace f m s`: the continuous fields of `A_m^s`, with the topology
  of `A_m^s`.
* `TauCeti.Vortex.SobolevFieldSpace.subRef`: the coordinates of `x - x_m` in `H^s(ℂ)`.

## References

* A. Jaffe and C. H. Taubes, *Vortices and Monopoles*, Progress in Physics 2, Birkhäuser, 1980,
  Chapter III.
* C. H. Taubes, *Gr ⇒ SW: From pseudo-holomorphic curves to Seiberg–Witten solutions*,
  J. Differential Geom. 51 (1999), 203–334.
-/

public section

noncomputable section

namespace TauCeti.Vortex

open Filter MeasureTheory Module TemperedDistribution BesselPotentialSpace Topology
open scoped SchwartzMap BesselPotentialSpace

variable {f : ContDiffBump (0 : ℝ)} {m : ℕ} {s : ℝ}

/-- **The continuous framed degree-`m` plane vortex fields of `A_m^s`**, to be given the topology
of `A_m^s` as an affine Hilbert space (`SobolevFieldSpace.isEmbedding_subRef`). For `s > 1` every
field of `A_m^s` agrees almost everywhere with exactly one of them: with at most one since they
are continuous, and with one by the Sobolev embedding
(`TemperedDistribution.exists_contDiff_ae_eq_of_mem_realSobolevFunctions`, coordinate by
coordinate). -/
structure SobolevFieldSpace (f : ContDiffBump (0 : ℝ)) (m : ℕ) (s : ℝ) : Type where
  /-- The field. -/
  toFun : ℂ → EuclideanSpace ℝ (Fin 4)
  mem_framedFieldSpace' : toFun ∈ framedFieldSpace f m s
  continuous' : Continuous toFun

namespace SobolevFieldSpace

instance : CoeFun (SobolevFieldSpace f m s) fun _ ↦ ℂ → EuclideanSpace ℝ (Fin 4) where
  coe x := x.toFun

@[simp]
theorem coe_mk (x : ℂ → EuclideanSpace ℝ (Fin 4)) (hx : x ∈ framedFieldSpace f m s)
    (hc : Continuous x) : ⇑(SobolevFieldSpace.mk x hx hc) = x :=
  rfl

/-- A field of `SobolevFieldSpace` is continuous. -/
theorem continuous (x : SobolevFieldSpace f m s) : Continuous x := x.continuous'

/-- A field of `SobolevFieldSpace` lies in `A_m^s`. -/
theorem mem_framedFieldSpace (x : SobolevFieldSpace f m s) : ⇑x ∈ framedFieldSpace f m s :=
  x.mem_framedFieldSpace'

/-- A field of `SobolevFieldSpace` is determined by its values. -/
@[ext]
theorem ext {x y : SobolevFieldSpace f m s} (h : ⇑x = ⇑y) : x = y := by
  cases x
  cases y
  cases h
  rfl

/-- The `j`-th coordinate of the difference `x - x_m` of a field from the reference field, as a
real function. -/
private theorem mem_realSobolevFunctions_sub (x : SobolevFieldSpace f m s) (j : Fin 4) :
    (fun z ↦ x z j - referenceField f m z j) ∈ realSobolevFunctions ℂ s 2 :=
  mem_sobolevFields.1 (_root_.TauCeti.Vortex.mem_framedFieldSpace.1 x.mem_framedFieldSpace) j

/-- **The `j`-th coordinate of `x - x_m` in `H^s(ℂ)`**: the element of the Bessel-potential space
whose `L²` function is the complexification of `z ↦ x(z)ⱼ - x_m(z)ⱼ`
(`SobolevFieldSpace.coeFn_toLp_inclusion_subRef`). -/
def subRef (x : SobolevFieldSpace f m s) (j : Fin 4) : H^{s}(ℂ) :=
  (mem_realSobolevFunctions.1
    (mem_realSobolevFunctions_sub x j)).choose_spec.2.toBesselPotentialSpace

/-- The coordinate `subRef x j` is the `H^s` element of the complexification of an `L²` function
agreeing almost everywhere with `z ↦ x(z)ⱼ - x_m(z)ⱼ`. -/
private theorem exists_eq_subRef (x : SobolevFieldSpace f m s) (j : Fin 4) :
    ∃ (u : Lp ℂ 2 (volume : Measure ℂ)) (hu : MemSobolev s 2 (u : 𝓢'(ℂ, ℂ))),
      hu.toBesselPotentialSpace = subRef x j ∧
        u =ᵐ[volume] fun z ↦ ((x z j - referenceField f m z j : ℝ) : ℂ) := by
  obtain ⟨hae, hS⟩ := (mem_realSobolevFunctions.1 (mem_realSobolevFunctions_sub x j)).choose_spec
  refine ⟨_, hS, rfl, ?_⟩
  filter_upwards [Complex.ofRealCLM.coeFn_compLp (p := 2) (μ := volume)
    (mem_realSobolevFunctions.1 (mem_realSobolevFunctions_sub x j)).choose, hae] with z h₁ h₂
  rw [h₁, Complex.ofRealCLM_apply, h₂]

/-- The `L²` function of `subRef x j` is the complexification of `z ↦ x(z)ⱼ - x_m(z)ⱼ`. -/
theorem coeFn_toLp_inclusion_subRef (h : 0 ≤ s) (x : SobolevFieldSpace f m s) (j : Fin 4) :
    ⇑(inclusion h (subRef x j)).toLp =ᵐ[volume]
      fun z ↦ ((x z j - referenceField f m z j : ℝ) : ℂ) := by
  obtain ⟨u, hu, hux, hae⟩ := exists_eq_subRef x j
  rw [← hux, toLp_inclusion_toBesselPotentialSpace h _ rfl]
  exact hae

/-- For `s > 1`, a continuous field of `A_m^s` is determined by the coordinates of `x - x_m` in
`H^s(ℂ)`. -/
theorem subRef_injective (hs : 1 < s) :
    Function.Injective (subRef : SobolevFieldSpace f m s → Fin 4 → H^{s}(ℂ)) := by
  intro x y hxy
  have h : 0 ≤ s := zero_le_one.trans hs.le
  ext z j
  -- The complexified coordinates of `x - x_m` and `y - x_m` agree almost everywhere, and they are
  -- continuous, so they agree everywhere.
  have hae := (coeFn_toLp_inclusion_subRef h x j).symm.trans
    ((congrArg (fun a ↦ ⇑(inclusion h (a j)).toLp) hxy).eventuallyEq.trans
      (coeFn_toLp_inclusion_subRef h y j))
  have hcont (w : SobolevFieldSpace f m s) :
      Continuous fun z ↦ ((w z j - referenceField f m z j : ℝ) : ℂ) :=
    Complex.continuous_ofReal.comp
      (((EuclideanSpace.proj j).continuous.comp w.continuous).sub
        ((EuclideanSpace.proj j).continuous.comp (contDiff_referenceField f m).continuous))
  have heq := congrFun ((hcont x).ae_eq_iff_eq volume (hcont y) |>.1 hae) z
  exact sub_left_inj.1 (Complex.ofReal_injective heq)

/-- **The topology of `A_m^s`** on its continuous fields: the topology induced by the coordinates
of `x - x_m` in `H^s(ℂ)`, that is, by the distance `‖x - y‖_{H^s}`. -/
instance : TopologicalSpace (SobolevFieldSpace f m s) :=
  TopologicalSpace.induced subRef inferInstance

/-- The topology of `SobolevFieldSpace` is induced by the coordinates `subRef`; for `s > 1` it is
an embedding. -/
theorem isEmbedding_subRef (hs : 1 < s) :
    IsEmbedding (subRef : SobolevFieldSpace f m s → Fin 4 → H^{s}(ℂ)) :=
  ⟨⟨rfl⟩, subRef_injective hs⟩

/-- The coordinates `subRef` are continuous. -/
theorem continuous_subRef : Continuous (subRef : SobolevFieldSpace f m s → Fin 4 → H^{s}(ℂ)) :=
  continuous_induced_dom

/-- Fields converge in `A_m^s` exactly when each coordinate of `x - x_m` converges in `H^s(ℂ)`. -/
theorem tendsto_iff {ι : Type*} {l : Filter ι} {xs : ι → SobolevFieldSpace f m s}
    {x : SobolevFieldSpace f m s} :
    Tendsto xs l (𝓝 x) ↔ ∀ j, Tendsto (fun i ↦ subRef (xs i) j) l (𝓝 (subRef x j)) := by
  rw [nhds_induced, tendsto_comap_iff, tendsto_pi_nhds]
  simp only [Function.comp_apply]

/-- For `s > 1`, the topology of `A_m^s` on its continuous fields is Hausdorff. -/
theorem t2Space (hs : 1 < s) : T2Space (SobolevFieldSpace f m s) :=
  (isEmbedding_subRef hs).t2Space

/-- **Convergence in `A_m^s`, `s > 1`, is uniform convergence of the fields.** -/
theorem tendstoUniformly_of_tendsto (hs : 1 < s) {ι : Type*} {l : Filter ι}
    {xs : ι → SobolevFieldSpace f m s} {x : SobolevFieldSpace f m s} (h : Tendsto xs l (𝓝 x)) :
    TendstoUniformly (fun i ↦ ⇑(xs i)) x l := by
  have hfin := finrank_real_complex_lt_two_mul hs
  -- Each coordinate of `x - x_m` converges uniformly, by the Sobolev embedding.
  have hj (j : Fin 4) : TendstoUniformly (fun i z ↦ ((xs i z j - referenceField f m z j : ℝ) : ℂ))
      (fun z ↦ ((x z j - referenceField f m z j : ℝ) : ℂ)) l := by
    choose u hu hux hae using fun i ↦ exists_eq_subRef (xs i) j
    obtain ⟨v, hv, hvx, hvae⟩ := exists_eq_subRef x j
    have hcont (w : SobolevFieldSpace f m s) :
        Continuous fun z ↦ ((w z j - referenceField f m z j : ℝ) : ℂ) :=
      Complex.continuous_ofReal.comp
        (((EuclideanSpace.proj j).continuous.comp w.continuous).sub
          ((EuclideanSpace.proj j).continuous.comp (contDiff_referenceField f m).continuous))
    refine tendstoUniformly_of_tendsto_toBesselPotentialSpace hfin hu hv ?_
      (fun i ↦ hcont (xs i)) (hcont x) hae hvae
    simp only [hux, hvx]
    exact tendsto_iff.1 h j
  rw [Metric.tendstoUniformly_iff]
  intro ε hε
  have hε2 : 0 < ε / 2 := by positivity
  filter_upwards [eventually_all.2 fun j ↦ Metric.tendstoUniformly_iff.1 (hj j) _ hε2]
    with i hi z
  -- A field whose four coordinates are within `ε / 2` is within `ε`.
  rw [EuclideanSpace.dist_eq, Real.sqrt_lt' hε]
  calc ∑ j, dist (x z j) (xs i z j) ^ 2 < ∑ _j : Fin 4, (ε / 2) ^ 2 := by
        refine Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty fun j _ ↦ ?_
        have hd := hi j z
        rw [Complex.dist_eq, ← Complex.ofReal_sub, sub_sub_sub_cancel_right,
          Complex.norm_real, Real.norm_eq_abs, ← Real.dist_eq] at hd
        exact pow_lt_pow_left₀ hd dist_nonneg two_ne_zero
    _ = ε ^ 2 := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring

/-- **Continuity of the divisor on `A_m^s`**, `s > 1`. If fields `xs i` converge to `x` in `A_m^s`,
and the zero multiplicities of their sections are the counts of `E i` and of `D` in `Sym ℂ m`,
then `E i → D` in `Sym ℂ m`. -/
theorem tendsto_of_tendsto (hs : 1 < s) {ι : Type*} {l : Filter ι}
    {xs : ι → SobolevFieldSpace f m s} {x : SobolevFieldSpace f m s} (h : Tendsto xs l (𝓝 x))
    {D : Sym ℂ m} {E : ι → Sym ℂ m}
    (hx : IsZeroMultiplicity (sectionValue x) fun z ↦ (D : Multiset ℂ).count z)
    (hxs : ∀ᶠ i in l, IsZeroMultiplicity (sectionValue (xs i))
      fun z ↦ (E i : Multiset ℂ).count z) :
    Tendsto E l (𝓝 D) :=
  Vortex.tendsto_of_tendstoLocallyUniformly hx hxs
    (tendstoUniformly_of_tendsto hs h).tendstoLocallyUniformly

/-- **The gauge orbit relation on `A_m^k` is closed**, for an integer `k ≥ 3`: the pairs `(x, y)`
of continuous fields of `A_m^k` with `y = u · x` for some `u` in the Sobolev gauge group
`G_(k+1)` form a closed subset of the product. -/
theorem isClosed_setOf_exists_gaugeTransform_eq {k : ℕ} (hk : 2 < k) :
    IsClosed {p : SobolevFieldSpace f m k × SobolevFieldSpace f m k |
      ∃ u ∈ sobolevGaugeGroup (s := k + 1) (by norm_cast; omega),
        gaugeTransform u p.1 = p.2} := by
  set S := {p : SobolevFieldSpace f m k × SobolevFieldSpace f m k |
    ∃ u ∈ sobolevGaugeGroup (s := k + 1) (by norm_cast; omega), gaugeTransform u p.1 = p.2}
  have hs : (1 : ℝ) < k := by exact_mod_cast (by omega : 1 < k)
  have h2 : 2 < (k : ℝ) + 1 := by
    have : (2 : ℝ) < k := by exact_mod_cast hk
    linarith
  refine closure_subset_iff_isClosed.1 fun p hp ↦ ?_
  -- Approach `p` along the pairs of `S`, indexed by `S` itself.
  have := mem_closure_iff_comap_neBot.1 hp
  set l := comap ((↑) : S → SobolevFieldSpace f m k × SobolevFieldSpace f m k) (𝓝 p)
  have hl : Tendsto ((↑) : S → SobolevFieldSpace f m k × SobolevFieldSpace f m k) l (𝓝 p) :=
    tendsto_comap
  choose us hus hxy using fun i : S ↦ i.2
  have hconv (q : SobolevFieldSpace f m k × SobolevFieldSpace f m k → SobolevFieldSpace f m k)
      (hq : Continuous q) :
      TendstoLocallyUniformly (fun i : S ↦ ⇑(q i)) (q p) l :=
    (tendstoUniformly_of_tendsto hs ((hq.tendsto p).comp hl)).tendstoLocallyUniformly
  obtain ⟨v, hvG, hv, -⟩ :=
    exists_mem_sobolevGaugeGroup_gaugeTransform_eq_and_tendstoLocallyUniformly hk
      (fun i ↦ differentiable_of_mem_sobolevGaugeGroup h2 (hus i)) hxy
      (hconv Prod.fst continuous_fst) (hconv Prod.snd continuous_snd) p.1.continuous
      p.2.continuous p.1.mem_framedFieldSpace p.2.mem_framedFieldSpace
  exact ⟨v, hvG, hv⟩

end SobolevFieldSpace

end TauCeti.Vortex

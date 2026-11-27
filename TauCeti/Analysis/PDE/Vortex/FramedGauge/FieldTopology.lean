/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Vortex.Divisor.Basic
public import TauCeti.Analysis.PDE.Vortex.FramedGauge.Limit
public import TauCeti.Analysis.Sobolev.BesselPotential.Inclusion
import TauCeti.Analysis.Normed.Lp.PiLp.Basic
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
function, and the topology is the one induced by this map. For `s ≥ 0` this map is injective
(`TauCeti.Vortex.SobolevFieldSpace.isEmbedding_subRef`) and the space is Hausdorff
(`TauCeti.Vortex.SobolevFieldSpace.t2Space`).

For `s > 1`, convergence in this topology implies uniform convergence of the fields
(`TauCeti.Vortex.SobolevFieldSpace.tendstoUniformly_of_tendsto`), by the quantitative Sobolev
embedding `|g(z)| ≤ C ‖g‖_{H^s}` for continuous representatives
(`TemperedDistribution.tendstoUniformly_of_tendsto_toBesselPotentialSpace`). For `s ≥ 0`,
convergence gives `L²` convergence of the coordinates of the fields
(`TauCeti.Vortex.SobolevFieldSpace.tendsto_eLpNorm_sub_of_tendsto`). For `s > 1`, the points
where the section of a field has modulus at most `c < 1` form a compact set
(`TauCeti.Vortex.SobolevFieldSpace.isCompact_setOf_norm_sectionValue_le`), since `|α| → 1` at
infinity. Two consequences for the gauge theory of `A_m^k` follow from the locally uniform
statements already available.

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

The continuity of the gauge action on `A_m^k` and the resulting Hausdorff quotient are in
`TauCeti.Analysis.PDE.Vortex.FramedGauge.Quotient`; the slice theorem is not treated here.

## Main definitions

* `TauCeti.Vortex.SobolevFieldSpace f m s`: the continuous fields of `A_m^s`, with the topology
  of `A_m^s`.
* `TauCeti.Vortex.SobolevFieldSpace.subRef`: the coordinates of `x - x_m` in `H^s(ℂ)`, each
  determined by its `L²` function (`TauCeti.Vortex.SobolevFieldSpace.subRef_eq_iff`).
* `TauCeti.Vortex.SobolevFieldSpace.toFramedFieldSpace`: a continuous field as an element of
  `A_m^s`.
* `TauCeti.Vortex.SobolevFieldSpace.congrOrder`: the identity of fields between `A_m^s` and
  `A_m^s'` for equal orders `s = s'`, as a homeomorphism.

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
coordinate; `SobolevFieldSpace.exists_ae_eq`). -/
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

/-- A field of `SobolevFieldSpace`, as an element of `A_m^s`. -/
@[expose] def toFramedFieldSpace (x : SobolevFieldSpace f m s) : framedFieldSpace f m s :=
  ⟨x, x.mem_framedFieldSpace⟩

/-- The field underlying `x.toFramedFieldSpace` is `x`. -/
@[simp]
theorem coe_toFramedFieldSpace (x : SobolevFieldSpace f m s) :
    (x.toFramedFieldSpace : ℂ → EuclideanSpace ℝ (Fin 4)) = x :=
  rfl

/-- For `s > 1`, every field of `A_m^s` agrees almost everywhere with a field of
`SobolevFieldSpace`, by the Sobolev embedding applied to each coordinate of `x - x_m`. -/
theorem exists_ae_eq (hs : 1 < s) {x : ℂ → EuclideanSpace ℝ (Fin 4)}
    (hx : x ∈ framedFieldSpace f m s) : ∃ y : SobolevFieldSpace f m s, x =ᵐ[volume] ⇑y := by
  have hfin : finrank ℝ ℂ + 2 * ((0 : ℕ) : ℝ) < 2 * s := by
    simpa using finrank_real_complex_lt_two_mul hs
  choose g hg hxg using fun j ↦ exists_contDiff_ae_eq_of_mem_realSobolevFunctions hfin
    (mem_sobolevFields.1 (_root_.TauCeti.Vortex.mem_framedFieldSpace.1 hx) j)
  set y : ℂ → EuclideanSpace ℝ (Fin 4) := referenceField f m + fun z ↦ WithLp.toLp 2 fun j ↦ g j z
  have hxy : x =ᵐ[volume] y := by
    filter_upwards [ae_all_iff.2 hxg] with z hz
    ext j
    simpa [y, sub_eq_iff_eq_add'] using hz j
  have hy : y ∈ framedFieldSpace f m s := by
    refine _root_.TauCeti.Vortex.mem_framedFieldSpace.2 (mem_sobolevFields_of_ae_eq
      (_root_.TauCeti.Vortex.mem_framedFieldSpace.1 hx) ?_)
    filter_upwards [hxy] with z hz
    simp [hz]
  refine ⟨⟨y, hy, (contDiff_referenceField f m).continuous.add ?_⟩, hxy⟩
  exact (PiLp.continuous_toLp 2 _).comp (continuous_pi fun j ↦ (hg j).continuous)

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

/-- **The coordinate `subRef x j`** is the `H^s` element of any `L²` function agreeing almost
everywhere with the complexification of `z ↦ x(z)ⱼ - x_m(z)ⱼ`. -/
theorem subRef_eq_toBesselPotentialSpace (x : SobolevFieldSpace f m s) (j : Fin 4)
    {u : Lp ℂ 2 (volume : Measure ℂ)} (hu : MemSobolev s 2 (u : 𝓢'(ℂ, ℂ)))
    (hae : u =ᵐ[volume] fun z ↦ ((x z j - referenceField f m z j : ℝ) : ℂ)) :
    subRef x j = hu.toBesselPotentialSpace := by
  obtain ⟨v, hv, hvx, hvae⟩ := exists_eq_subRef x j
  obtain rfl : v = u := Lp.ext (hvae.trans hae.symm)
  exact hvx.symm

/-- The complexified `j`-th coordinate of `x - x_m` is continuous. -/
private theorem continuous_ofReal_sub (x : SobolevFieldSpace f m s) (j : Fin 4) :
    Continuous fun z ↦ ((x z j - referenceField f m z j : ℝ) : ℂ) :=
  Complex.continuous_ofReal.comp
    (((EuclideanSpace.proj j).continuous.comp x.continuous).sub
      ((EuclideanSpace.proj j).continuous.comp (contDiff_referenceField f m).continuous))

/-- The `L²` function of `subRef x j` is the complexification of `z ↦ x(z)ⱼ - x_m(z)ⱼ`. -/
theorem coeFn_toLp_inclusion_subRef (h : 0 ≤ s) (x : SobolevFieldSpace f m s) (j : Fin 4) :
    ⇑(inclusion h (subRef x j)).toLp =ᵐ[volume]
      fun z ↦ ((x z j - referenceField f m z j : ℝ) : ℂ) := by
  obtain ⟨u, hu, hux, hae⟩ := exists_eq_subRef x j
  rw [← hux, toLp_inclusion_toBesselPotentialSpace h _ rfl]
  exact hae

/-- **The coordinate `subRef x j` is characterized by its `L²` function**: for `s ≥ 0`, an element
`e ∈ H^s(ℂ)` is the coordinate `j` of `x - x_m` exactly when its `L²` function is almost
everywhere the complexification of `z ↦ x(z)ⱼ - x_m(z)ⱼ`. -/
theorem subRef_eq_iff (h : 0 ≤ s) (x : SobolevFieldSpace f m s) (j : Fin 4) (e : H^{s}(ℂ)) :
    subRef x j = e ↔
      ⇑(inclusion h e).toLp =ᵐ[volume] fun z ↦ ((x z j - referenceField f m z j : ℝ) : ℂ) := by
  refine ⟨fun hxe ↦ hxe ▸ coeFn_toLp_inclusion_subRef h x j, fun he ↦ ?_⟩
  rw [subRef_eq_toBesselPotentialSpace x j (memSobolev_inclusionLp h e) (by rwa [← toLp_inclusion])]
  exact toBesselPotentialSpace_memSobolev_inclusionLp h e

/-- For `s ≥ 0`, a continuous field of `A_m^s` is determined by the coordinates of `x - x_m` in
`H^s(ℂ)`. -/
theorem subRef_injective (h : 0 ≤ s) :
    Function.Injective (subRef : SobolevFieldSpace f m s → Fin 4 → H^{s}(ℂ)) := by
  intro x y hxy
  ext z j
  -- The complexified coordinates of `x - x_m` and `y - x_m` agree almost everywhere, and they are
  -- continuous, so they agree everywhere.
  have hae := (coeFn_toLp_inclusion_subRef h x j).symm.trans
    ((congrArg (fun a ↦ ⇑(inclusion h (a j)).toLp) hxy).eventuallyEq.trans
      (coeFn_toLp_inclusion_subRef h y j))
  have heq := congrFun
    ((continuous_ofReal_sub x j).ae_eq_iff_eq volume (continuous_ofReal_sub y j) |>.1 hae) z
  exact sub_left_inj.1 (Complex.ofReal_injective heq)

/-- **The topology of `A_m^s`** on its continuous fields: the topology induced by the coordinates
of `x - x_m` in `H^s(ℂ)`, that is, by the distance `‖x - y‖_{H^s}`. -/
instance : TopologicalSpace (SobolevFieldSpace f m s) :=
  TopologicalSpace.induced subRef inferInstance

/-- The topology of `SobolevFieldSpace` is induced by the coordinates `subRef`; for `s ≥ 0` it is
an embedding. -/
theorem isEmbedding_subRef (h : 0 ≤ s) :
    IsEmbedding (subRef : SobolevFieldSpace f m s → Fin 4 → H^{s}(ℂ)) :=
  ⟨⟨rfl⟩, subRef_injective h⟩

/-- The coordinates `subRef` are continuous. -/
theorem continuous_subRef : Continuous (subRef : SobolevFieldSpace f m s → Fin 4 → H^{s}(ℂ)) :=
  continuous_induced_dom

/-- Fields converge in `A_m^s` exactly when each coordinate of `x - x_m` converges in `H^s(ℂ)`. -/
theorem tendsto_iff {ι : Type*} {l : Filter ι} {xs : ι → SobolevFieldSpace f m s}
    {x : SobolevFieldSpace f m s} :
    Tendsto xs l (𝓝 x) ↔ ∀ j, Tendsto (fun i ↦ subRef (xs i) j) l (𝓝 (subRef x j)) := by
  rw [nhds_induced, tendsto_comap_iff, tendsto_pi_nhds]
  simp only [Function.comp_apply]

/-- For `s ≥ 0`, the topology of `A_m^s` on its continuous fields is Hausdorff. -/
theorem t2Space (h : 0 ≤ s) : T2Space (SobolevFieldSpace f m s) :=
  (isEmbedding_subRef h).t2Space

/-- **Equal orders give the same fields.** For `s = s'`, the continuous fields of `A_m^s` and of
`A_m^s'` are the same functions, and this is the identity on them as a homeomorphism. It
identifies, for instance, the spaces of order `↑(k + 1)` and `↑k + 1`, whose orders are equal but
not definitionally. -/
def congrOrder {s' : ℝ} (h : s = s') : SobolevFieldSpace f m s ≃ₜ SobolevFieldSpace f m s' where
  toFun x := ⟨x, h ▸ x.mem_framedFieldSpace, x.continuous⟩
  invFun x := ⟨x, h.symm ▸ x.mem_framedFieldSpace, x.continuous⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := by subst h; exact continuous_id
  continuous_invFun := by subst h; exact continuous_id

@[simp]
theorem coe_congrOrder {s' : ℝ} (h : s = s') (x : SobolevFieldSpace f m s) :
    ⇑(congrOrder h x) = ⇑x :=
  (rfl)

@[simp]
theorem congrOrder_symm {s' : ℝ} (h : s = s') :
    (congrOrder (f := f) (m := m) h).symm = congrOrder h.symm :=
  (rfl)

/-- **Convergence in `A_m^s`, `s > 1`, implies uniform convergence of the fields.** -/
theorem tendstoUniformly_of_tendsto (hs : 1 < s) {ι : Type*} {l : Filter ι}
    {xs : ι → SobolevFieldSpace f m s} {x : SobolevFieldSpace f m s} (h : Tendsto xs l (𝓝 x)) :
    TendstoUniformly (fun i ↦ ⇑(xs i)) x l := by
  have hfin := finrank_real_complex_lt_two_mul hs
  refine PiLp.tendstoUniformly_iff.2 fun j ↦ ?_
  -- The `j`-th coordinate of `x - x_m` converges uniformly, by the Sobolev embedding.
  choose u hu hux hae using fun i ↦ exists_eq_subRef (xs i) j
  obtain ⟨v, hv, hvx, hvae⟩ := exists_eq_subRef x j
  have hj := tendstoUniformly_of_tendsto_toBesselPotentialSpace hfin hu hv
    (by simpa only [hux, hvx] using tendsto_iff.1 h j)
    (fun i ↦ continuous_ofReal_sub (xs i) j) (continuous_ofReal_sub x j) hae hvae
  -- Complexifying and translating by `x_m` preserves distances.
  have hdist (a b r : ℝ) : dist ((a - r : ℝ) : ℂ) ((b - r : ℝ) : ℂ) = dist a b := by
    rw [Complex.isometry_ofReal.dist_eq, dist_sub_right]
  rw [Metric.tendstoUniformly_iff] at hj ⊢
  simpa only [hdist] using hj

/-- The `j`-th coordinate of the difference of two continuous fields of `A_m^s` is continuous. -/
theorem continuous_apply_sub (x y : SobolevFieldSpace f m s) (j : Fin 4) :
    Continuous fun z ↦ x z j - y z j :=
  ((EuclideanSpace.proj j).continuous.comp x.continuous).sub
    ((EuclideanSpace.proj j).continuous.comp y.continuous)

/-- The `L²` function of `subRef x j - subRef y j` is the complexification of the coordinate
difference `z ↦ x(z)ⱼ - y(z)ⱼ`. -/
theorem coeFn_inclusionLp_subRef_sub_subRef (h : 0 ≤ s) (x y : SobolevFieldSpace f m s)
    (j : Fin 4) :
    ⇑(inclusionLp h (subRef x j - subRef y j)) =ᵐ[volume] fun z ↦ ((x z j - y z j : ℝ) : ℂ) := by
  filter_upwards [coeFn_toLp_inclusion_subRef h x j, coeFn_toLp_inclusion_subRef h y j,
    Lp.coeFn_sub (inclusionLp h (subRef x j)) (inclusionLp h (subRef y j))] with z h₁ h₂ h₃
  rw [toLp_inclusion] at h₁ h₂
  rw [map_sub, h₃, Pi.sub_apply, h₁, h₂]
  push_cast
  ring

/-- **Convergence in `A_m^s` gives `L²` convergence of the coordinates**, for `s ≥ 0`: if fields
`xᵢ → x` in `A_m^s`, then each coordinate `xᵢ(z)ⱼ - x(z)ⱼ` tends to zero in `L²`. -/
theorem tendsto_eLpNorm_sub_of_tendsto (h : 0 ≤ s) {ι : Type*} {l : Filter ι}
    {xs : ι → SobolevFieldSpace f m s} {x : SobolevFieldSpace f m s} (hx : Tendsto xs l (𝓝 x))
    (j : Fin 4) : Tendsto (fun i ↦ eLpNorm (fun z ↦ xs i z j - x z j) 2 volume) l (𝓝 0) := by
  set T : ι → Lp ℂ 2 (volume : Measure ℂ) := fun i ↦
    (inclusion h (subRef (xs i) j - subRef x j)).toLp
  have hT : Tendsto T l (𝓝 0) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have hsub := tendsto_iff_norm_sub_tendsto_zero.1 (tendsto_iff.1 hx j)
    refine squeeze_zero (fun _ ↦ norm_nonneg _) (fun i ↦ ?_) hsub
    rw [sub_zero, norm_toLp_eq]
    exact norm_inclusion_apply_le h _
  have hae (i : ι) : (T i : ℂ → ℂ) =ᵐ[volume] fun z ↦ ((xs i z j - x z j : ℝ) : ℂ) := by
    simpa only [T, toLp_inclusion] using coeFn_inclusionLp_subRef_sub_subRef h (xs i) x j
  have hlim := ((continuous_eNorm.tendsto 0).comp hT)
  rw [eNorm_zero] at hlim
  refine hlim.congr fun i ↦ ?_
  simp only [Function.comp_apply, Lp.eNorm_def]
  rw [eLpNorm_congr_ae (hae i)]
  have hc := continuous_apply_sub (xs i) x j
  exact eLpNorm_congr_norm_ae (Complex.continuous_ofReal.comp hc).aestronglyMeasurable
    hc.aestronglyMeasurable (Eventually.of_forall fun z ↦ by rw [Complex.norm_real])

/-- **The set where the section is small is compact.** For `s > 1` and `c < 1`, the points where
the section of a field of `A_m^s` has modulus at most `c` form a compact set, since `|α| → 1` at
infinity. -/
theorem isCompact_setOf_norm_sectionValue_le (hs : 1 < s) (x : SobolevFieldSpace f m s)
    {c : ℝ} (hc : c < 1) : IsCompact {z | ‖sectionValue x z‖ ≤ c} := by
  have hev : ∀ᶠ z in cocompact ℂ, c < ‖sectionValue x z‖ := by
    rcases lt_or_ge c 0 with hc0 | hc0
    · exact Eventually.of_forall fun z ↦ hc0.trans_le (norm_nonneg _)
    filter_upwards [(tendsto_normSq_of_mem_framedFieldSpace hs x.mem_framedFieldSpace
      x.continuous).eventually (lt_mem_nhds (by nlinarith : c ^ 2 < 1))] with z hz
    exact lt_norm_sectionValue_of_sq_lt hz
  obtain ⟨t, ht, hts⟩ := mem_cocompact.1 hev
  refine ht.of_isClosed_subset
    (isClosed_le (continuous_sectionValue x.continuous).norm continuous_const) fun z hz ↦ ?_
  by_contra hzt
  have h1 : c < ‖sectionValue x z‖ := hts hzt
  exact absurd hz (not_le.2 h1)

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
  have : Fact (1 < k) := ⟨by omega⟩
  have hs : (1 : ℝ) < k := by exact_mod_cast (by omega : 1 < k)
  refine closure_subset_iff_isClosed.1 fun p hp ↦ ?_
  -- Approach `p` along the pairs of `S`, indexed by `S` itself.
  have := mem_closure_iff_comap_neBot.1 hp
  set l := comap ((↑) : S → SobolevFieldSpace f m k × SobolevFieldSpace f m k) (𝓝 p)
  have hl : Tendsto ((↑) : S → SobolevFieldSpace f m k × SobolevFieldSpace f m k) l (𝓝 p) :=
    tendsto_comap
  have hconv (q : SobolevFieldSpace f m k × SobolevFieldSpace f m k → SobolevFieldSpace f m k)
      (hq : Continuous q) :
      TendstoLocallyUniformly (fun i : S ↦ ⇑(q i)) (q p) l :=
    (tendstoUniformly_of_tendsto hs ((hq.tendsto p).comp hl)).tendstoLocallyUniformly
  choose us hus hxy using fun i : S ↦ i.property
  obtain ⟨⟨v, hvG⟩, hv⟩ := mem_orbit_sobolevGaugeGroup_of_tendstoLocallyUniformly hk
    (xs := fun i : S ↦ (i : S).val.1.toFramedFieldSpace)
    (ys := fun i : S ↦ (i : S).val.2.toFramedFieldSpace)
    (x := p.1.toFramedFieldSpace) (y := p.2.toFramedFieldSpace)
    (fun i ↦ ⟨⟨us i, hus i⟩, Subtype.ext (hxy i)⟩)
    (hconv Prod.fst continuous_fst) (hconv Prod.snd continuous_snd) p.1.continuous p.2.continuous
  exact ⟨v, hvG, congrArg Subtype.val hv⟩

end SobolevFieldSpace

end TauCeti.Vortex

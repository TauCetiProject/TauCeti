/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.AdaptedChart
public import TauCeti.Geometry.Manifold.Complex.TotallyReal.Basic
public import TauCeti.Geometry.Symplectic.Manifold.AlmostComplex.Chart
import TauCeti.Geometry.Manifold.MFDeriv.Chart.Basic

/-!
# Adapted charts along a totally real embedding

Let `ι : N → M` be a totally real embedding for a `C^ℓ` almost complex structure `J` on a
boundaryless manifold `M`, where `N` is modelled on `F` and `M` on `E`, and let `x₀ ∈ N`. This
file constructs a `C^ℓ` chart `ψ` of `M` near `ι x₀` with values in `F × F`, in which the zero
section `F × {0}` plays the role of `ℝⁿ ⊆ ℂⁿ` and `(v, w) ↦ (-w, v)` the role of multiplication
by `i`, such that

* `ψ` flattens `ι`: a point of the source of `ψ` lies on `ι (N)` exactly when its image lies on
  the zero section, so `ψ (ι (N)) = ψ (U) ∩ (F × {0})` on the source `U` of `ψ`;
* along `ι (N)` the derivative of `ψ` turns `J` into the standard structure;
* the pushed-forward structure `ψ_* J = dψ ∘ J ∘ dψ⁻¹` is `C^(ℓ-1)` on the target of `ψ` and
  equals the standard structure on the zero section.

This is McDuff–Salamon Exercise B.4.10. The chart is read off from the model construction of
`TauCeti.exists_adaptedChart`: with `χ` the extended chart of `M` at `ι x₀`, `φ` that of `N` at
`x₀`, `γ = χ ∘ ι ∘ φ⁻¹` and `J_χ` the structure read in `χ`, the inverse of `ψ` is
`χ⁻¹ ∘ Φ` for the adapted normal extension `Φ (x, y) = γ x + J_χ (γ x) (Dγ x y)`. The topological
embedding hypothesis is what allows the source of `ψ` to be shrunk so that it meets `ι (N)` only
in the image of a neighbourhood of `x₀`. The step from a model adapted extension and a shrinking
set to the manifold chart is stated separately, so that the converging families of
`TauCeti.Geometry.Manifold.Complex.TotallyReal.AdaptedChart.Family` can reuse it.

## Main declarations

* `TauCeti.IsAdaptedChart`: the properties of an adapted chart listed above.
* `TauCeti.exists_isAdaptedChart_of_coe_eq_adaptedNormalExtension`: the adapted chart built
  from a model adapted extension.
* `TauCeti.IsTotallyRealEmbedding.exists_adaptedChart`: the adapted chart.
* `TauCeti.adaptedNormalExtension_writtenInExtChartAt_inl`: in the flat model `V ⊆ V × V` with
  the standard structure the adapted extension is the identity.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Exercise B.4.10.
-/

public noncomputable section

open Set Filter Manifold
open scoped Topology Manifold ContDiff

namespace TauCeti

variable {E H M F H' N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [I.Boundaryless] [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F] [TopologicalSpace H']
  {I' : ModelWithCorners ℝ F H'} [I'.Boundaryless] [TopologicalSpace N] [ChartedSpace H' N]
  {ℓ : ℕ∞} {k : ℕ∞ω} {J : ContMDiffAlmostComplexStructure I ℓ M} {ι : N → M}

variable (J ι) in
/-- **Adapted charts along a map.** A chart `ψ` of `M` with values in `F × F` is adapted to
`ι : N → M` and the `C^ℓ` almost complex structure `J` when

* `ψ` is `C^ℓ` with `C^ℓ` inverse;
* `ψ` flattens `ι`: a point of the source of `ψ` lies on `ι (N)` exactly when its image lies on
  the zero section `F × {0}`;
* at points of `ι (N)` the derivative of `ψ` intertwines `J` with the standard structure
  `(v, w) ↦ (-w, v)`;
* the pushed-forward structure `ψ_* J = dψ ∘ J ∘ dψ⁻¹` is `C^(ℓ-1)` on the target of `ψ` and
  standard on its zero section. -/
structure IsAdaptedChart (ψ : OpenPartialHomeomorph M (F × F)) : Prop where
  /-- The chart is `C^ℓ` on its source. -/
  contMDiffOn : ContMDiffOn I 𝓘(ℝ, F × F) ℓ ψ ψ.source
  /-- The inverse chart is `C^ℓ` on its target. -/
  contMDiffOn_symm : ContMDiffOn 𝓘(ℝ, F × F) I ℓ ψ.symm ψ.target
  /-- The chart flattens the image of `ι` onto the zero section. -/
  isImage : ψ.IsImage (range ι) {p | p.2 = 0}
  /-- Along the image of `ι` the derivative of the chart turns `J` into the standard
  structure. -/
  mfderiv_comp_toEndomorphism : ∀ x ∈ ψ.source ∩ range ι,
    (mfderiv I 𝓘(ℝ, F × F) ψ x).comp (J.toEndomorphism x) =
      ((-ContinuousLinearMap.snd ℝ F F).prod (ContinuousLinearMap.fst ℝ F F)).comp
        (mfderiv I 𝓘(ℝ, F × F) ψ x)
  /-- The pushed-forward structure loses at most one derivative. -/
  contDiffOn_chartPushforward :
    ContDiffOn ℝ ((ℓ - 1 : ℕ∞) : ℕ∞ω) (J.chartPushforward ψ) ψ.target
  /-- The pushed-forward structure is standard on the zero section. -/
  chartPushforward_of_snd_eq_zero : ∀ p ∈ ψ.target, p.2 = 0 →
    J.chartPushforward ψ p = (-ContinuousLinearMap.snd ℝ F F).prod (ContinuousLinearMap.fst ℝ F F)

omit [FiniteDimensional ℝ E] [I.Boundaryless] [IsManifold I ∞ M] [FiniteDimensional ℝ F] in
/-- Read in the extended charts at `x₀` and `ι x₀`, the derivative at `x₀` of a map that is
differentiable at `x₀` is its manifold derivative. -/
private theorem fderiv_writtenInExtChartAt_eq_mfderiv {x₀ : N}
    (hι : MDifferentiableAt I' I ι x₀) :
    fderiv ℝ (writtenInExtChartAt I' I x₀ ι) (extChartAt I' x₀ x₀) = mfderiv I' I ι x₀ :=
  (hι.mfderiv_eq_fderiv_extChartAt_conj rfl).symm

omit [I.Boundaryless] in
/-- Read in the extended charts at `x₀` and `ι x₀`, the derivative at `x₀` of a `C^k` totally
real embedding, `1 ≤ k`, is injective. -/
theorem IsTotallyRealEmbedding.injective_fderiv_writtenInExtChartAt [IsManifold I' k N]
    {A : ∀ y : M, AlmostComplexStructure (TangentSpace I y)}
    (h : IsTotallyRealEmbedding I' I k A ι) (hk : 1 ≤ k) (x₀ : N) :
    Function.Injective (fderiv ℝ (writtenInExtChartAt I' I x₀ ι) (extChartAt I' x₀ x₀)) := by
  have : IsManifold I 1 M := IsManifold.of_le (n := ∞) (by exact_mod_cast le_top)
  have : IsManifold I' 1 N := IsManifold.of_le hk
  rw [fderiv_writtenInExtChartAt_eq_mfderiv
    ((h.isSmoothEmbedding.contMDiff.of_le hk x₀).mdifferentiableAt one_ne_zero)]
  exact h.mfderiv_injective x₀

omit [I.Boundaryless] in
/-- Read in the extended charts at `x₀` and `ι x₀`, the tangent image at `x₀` of a `C^k`
totally real embedding for `J`, `1 ≤ k`, is maximal totally real for `J` read in the chart at
`ι x₀`. -/
theorem IsTotallyRealEmbedding.isMaximalTotallyReal_range_fderiv_writtenInExtChartAt
    [IsManifold I' k N] (h : IsTotallyRealEmbedding I' I k J.almostComplexStructureAt ι)
    (hk : 1 ≤ k) (x₀ : N) :
    IsMaximalTotallyReal
      (J.inChart (ι x₀) (writtenInExtChartAt I' I x₀ ι (extChartAt I' x₀ x₀))).toLinearMap
      (fderiv ℝ (writtenInExtChartAt I' I x₀ ι) (extChartAt I' x₀ x₀)).range := by
  have : IsManifold I 1 M := IsManifold.of_le (n := ∞) (by exact_mod_cast le_top)
  have : IsManifold I' 1 N := IsManifold.of_le hk
  have hγx₀ : writtenInExtChartAt I' I x₀ ι (extChartAt I' x₀ x₀) = extChartAt I (ι x₀) (ι x₀) := by
    simp only [writtenInExtChartAt, Function.comp_apply,
      (extChartAt I' x₀).left_inv (mem_extChartAt_source x₀)]
  rw [fderiv_writtenInExtChartAt_eq_mfderiv
    ((h.isSmoothEmbedding.contMDiff.of_le hk x₀).mdifferentiableAt one_ne_zero), hγx₀,
    J.inChart_extChartAt_self]
  have := isMaximalTotallyRealMap_iff.1 h.isMaximalTotallyRealMap x₀
  rwa [ContMDiffAlmostComplexStructure.almostComplexStructureAt_toLinearMap] at this

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
/-- **Adapted charts from adapted extensions.** Let `ι` be a `C^k` map, `J` a `C^ℓ` almost
complex structure, with `1 ≤ ℓ` and `ℓ + 1 ≤ k`, and write `φ` and `χ` for the extended charts
at `x₀` and `ι x₀`. Let `e` be a partial homeomorphism, `C^ℓ` with `C^ℓ` inverse,
whose underlying map is the adapted normal extension of `ι` and `J` read in `φ` and `χ`, with
source over the parameters `z` with `φ⁻¹ z ∈ ι⁻¹ (χ.source)`. Let `O ∋ ι x₀` be open in `M` such
that a point `z` of `N` with `ι z ∈ O` lies in the source of `φ` with `(φ z, 0)` in the source
of `e`. Then `x ↦ e⁻¹ (χ x)`, restricted to `O`, is an adapted chart for `ι` and `J`, sending
`ι x₀` to `(φ x₀, 0)`.

Several extensions with one source, as produced by `TauCeti.exists_adaptedChart_family`, can share
one `O`; this is how converging families of adapted charts are built. -/
theorem exists_isAdaptedChart_of_coe_eq_adaptedNormalExtension
    [IsManifold I' k N] (hι : ContMDiff I' I k ι) (hℓ : 1 ≤ ℓ) (hk : (ℓ : ℕ∞ω) + 1 ≤ k)
    {x₀ : N} {e : OpenPartialHomeomorph (F × F) E}
    (he : ⇑e = adaptedNormalExtension (writtenInExtChartAt I' I x₀ ι) (J.inChart (ι x₀)))
    (hec : ContDiffOn ℝ ℓ e e.source) (hesc : ContDiffOn ℝ ℓ e.symm e.target)
    (heU : e.source ⊆ ((extChartAt I' x₀).target ∩
      (extChartAt I' x₀).symm ⁻¹' (ι ⁻¹' (extChartAt I (ι x₀)).source)) ×ˢ univ)
    {O : Set M} (hO : IsOpen O) (hx₀O : ι x₀ ∈ O)
    (hOe : ∀ z, ι z ∈ O → z ∈ (extChartAt I' x₀).source ∧ (extChartAt I' x₀ z, 0) ∈ e.source) :
    ∃ ψ : OpenPartialHomeomorph M (F × F),
      (∀ x, ψ x = e.symm (extChartAt I (ι x₀) x)) ∧
      (∀ p, ψ.symm p = (extChartAt I (ι x₀)).symm (e p)) ∧
      (∀ x, x ∈ ψ.source ↔
        x ∈ (extChartAt I (ι x₀)).source ∧ extChartAt I (ι x₀) x ∈ e.target ∧ x ∈ O) ∧
      (∀ p, p ∈ ψ.target ↔
        p ∈ e.source ∧ e p ∈ (extChartAt I (ι x₀)).target ∧
          (extChartAt I (ι x₀)).symm (e p) ∈ O) ∧
      ι x₀ ∈ ψ.source ∧ ψ (ι x₀) = (extChartAt I' x₀ x₀, 0) ∧ IsAdaptedChart J ι ψ := by
  -- Regularity bookkeeping: everything happens at order `ℓ + 1`.
  have hkM : ((ℓ : ℕ∞ω) + 1) ≤ ∞ := by exact_mod_cast le_top
  have : IsManifold I' ((ℓ : ℕ∞ω) + 1) N := IsManifold.of_le hk
  have : IsManifold I ((ℓ : ℕ∞ω) + 1) M := IsManifold.of_le hkM
  have hℓ' : (1 : ℕ∞ω) ≤ ℓ := by exact_mod_cast hℓ
  replace hι : ContMDiff I' I ((ℓ : ℕ∞ω) + 1) ι := hι.of_le hk
  set y := ι x₀
  set χ := extChartAt I y
  set φ := extChartAt I' x₀
  set γ := writtenInExtChartAt I' I x₀ ι
  set Jχ := J.inChart y
  have hγapp (z : F) : γ z = χ (ι (φ.symm z)) := rfl
  set U := φ.target ∩ φ.symm ⁻¹' (ι ⁻¹' χ.source)
  have hU : IsOpen U := (continuousOn_extChartAt_symm x₀).isOpen_inter_preimage
    (isOpen_extChartAt_target x₀) ((isOpen_extChartAt_source y).preimage hι.continuous)
  have hΩ : IsOpen χ.target := isOpen_extChartAt_target y
  have hγΩ : MapsTo γ U χ.target := fun z hz ↦ χ.map_source hz.2
  have hγ : ContDiffOn ℝ ((ℓ : ℕ∞ω) + 1) γ U := by
    have := (contMDiffOn_iff_of_subset_source' (x := x₀) (y := y)
      (s := φ.source ∩ ι ⁻¹' χ.source) inter_subset_left (fun z hz ↦ hz.2)).1 hι.contMDiffOn
    rwa [PartialEquiv.image_source_inter_eq'] at this
  have hJ : ContDiffOn ℝ (ℓ : ℕ∞ω) Jχ χ.target := J.contDiffOn_inChart y
  have hγe (q : F) : e (q, 0) = γ q := by rw [he, adaptedNormalExtension_zero]
  have he₀ : (φ x₀, (0 : F)) ∈ e.source := (hOe x₀ hx₀O).2
  have hγx₀ : γ (φ x₀) = χ y := by
    rw [hγapp, φ.left_inv (mem_extChartAt_source x₀)]
  -- The extended chart at `y` as an open partial homeomorphism, then `e⁻¹`, restricted to `O`.
  let ψ := (((chartAt H y).extendTrans I (Homeomorph.refl E)).trans e.symm).restrOpen O hO
  have hψcoe (x : M) : ψ x = e.symm (χ x) := by
    simp [ψ, χ]
  have hψsymm (p : F × F) : ψ.symm p = χ.symm (e p) := by
    simp [ψ, χ]
  have hψsrc (x : M) : x ∈ ψ.source ↔ x ∈ χ.source ∧ χ x ∈ e.target ∧ x ∈ O := by
    simp [ψ, χ, and_assoc]
  have hψtgt (p : F × F) :
      p ∈ ψ.target ↔ p ∈ e.source ∧ e p ∈ χ.target ∧ χ.symm (e p) ∈ O := by
    simp [ψ, χ, I.range_eq_univ, and_assoc]
  have hℓ0 : (ℓ : ℕ∞ω) ≠ 0 := (zero_lt_one.trans_le hℓ').ne'
  have : IsManifold I (ℓ : ℕ∞ω) M := IsManifold.of_le (n := ∞) (by exact_mod_cast le_top)
  have hed {p : F × F} (hp : p ∈ e.source) : DifferentiableAt ℝ e p :=
    (hec.contDiffAt (e.open_source.mem_nhds hp)).differentiableAt hℓ0
  have hesd {z : E} (hz : z ∈ e.target) : DifferentiableAt ℝ e.symm z :=
    (hesc.contDiffAt (e.open_target.mem_nhds hz)).differentiableAt hℓ0
  have htgt : ψ.target ⊆ e.source := fun p hp ↦ ((hψtgt p).1 hp).1
  have hsrc : ψ.source ⊆ χ.source := fun x hx ↦ ((hψsrc x).1 hx).1
  -- The base point.
  have hx₀ψ : y ∈ ψ.source := by
    refine (hψsrc y).2 ⟨mem_extChartAt_source y, ?_, hx₀O⟩
    rw [← hγx₀, ← hγe]
    exact e.map_source he₀
  have hψx₀ : ψ y = (φ x₀, 0) := by
    rw [hψcoe, ← hγx₀, ← hγe, e.left_inv he₀]
  -- Regularity of the chart and of its inverse.
  have hcont : ContMDiffOn I 𝓘(ℝ, F × F) ℓ ψ ψ.source := by
    refine (hesc.contMDiffOn.comp ((contMDiffOn_extChartAt (x := y)).mono fun x hx ↦ ?_)
      fun x hx ↦ ((hψsrc x).1 hx).2.1).congr fun x _ ↦ hψcoe x
    rw [← extChartAt_source I]
    exact hsrc hx
  have hcont_symm : ContMDiffOn 𝓘(ℝ, F × F) I ℓ ψ.symm ψ.target :=
    ((contMDiffOn_extChartAt_symm y).comp (hec.contMDiffOn.mono htgt)
      fun p hp ↦ ((hψtgt p).1 hp).2.1).congr fun p _ ↦ hψsymm p
  -- Flattening.
  have hImage : ψ.IsImage (range ι) {p | p.2 = 0} := by
    intro x hx
    simp only [mem_ofPred_eq]
    constructor
    · intro h0
      have hpe : ((ψ x).1, (0 : F)) ∈ e.source := by
        rw [← h0]
        exact htgt (ψ.map_source hx)
      have hqU := (heU hpe).1
      have hxt : χ x ∈ e.target := ((hψsrc x).1 hx).2.1
      have heq : χ x = χ (ι (φ.symm (ψ x).1)) := by
        rw [← hγapp, ← hγe, ← h0, hψcoe, e.right_inv hxt]
      exact ⟨φ.symm (ψ x).1, (χ.injOn (hsrc hx) hqU.2 heq).symm⟩
    · rintro ⟨z, rfl⟩
      obtain ⟨hzφ, hze⟩ := hOe z ((hψsrc _).1 hx).2.2
      rw [hψcoe, ← φ.left_inv hzφ, ← hγapp, ← hγe, e.left_inv hze]
  -- The restriction of `e` to the points it sends into the chart target.
  let e' := e.restrOpen (e.source ∩ e ⁻¹' χ.target) (e.isOpen_inter_preimage hΩ)
  have he'src : e'.source = e.source ∩ e ⁻¹' χ.target := by
    simp [e']
  have he'tgt {z : E} (hz : z ∈ e'.target) : e.symm z ∈ e.source ∩ e ⁻¹' χ.target := by
    rw [← he'src]
    exact e'.map_target hz
  have he'Ω : e'.target ⊆ χ.target := fun z hz ↦ by
    rw [← e'.right_inv hz]
    exact (he'tgt hz).2
  have htgt' : ψ.target ⊆ e'.source := fun p hp ↦
    he'src ▸ ⟨((hψtgt p).1 hp).1, ((hψtgt p).1 hp).2.1⟩
  -- The pushed-forward structure is the model pullback by `e`.
  have hK : ∀ p ∈ ψ.target, J.chartPushforward ψ p = e.pullbackEnd Jχ p := fun p hp ↦
    J.chartPushforward_eq_pullbackEnd_inChart y ψ e ((hψtgt p).1 hp).2.1
      (Eventually.of_forall hψcoe) (Eventually.of_forall hψsymm) (hed (htgt hp))
      (hesd (e.map_source (htgt hp)))
  have hK' : ∀ p ∈ ψ.target, J.chartPushforward ψ p = e'.pullbackEnd Jχ p :=
    fun p hp ↦ (hK p hp).trans (ContinuousLinearMap.ext fun v ↦ by simp [e'])
  -- On the zero section it is the standard structure.
  have hstd : ∀ p ∈ ψ.target, p.2 = 0 →
      J.chartPushforward ψ p =
        (-ContinuousLinearMap.snd ℝ F F).prod (ContinuousLinearMap.fst ℝ F F) := by
    intro p hp h0
    have hpq : p = (p.1, 0) := Prod.ext rfl h0
    have hqe : (p.1, (0 : F)) ∈ e.source := hpq ▸ htgt hp
    have hqU : p.1 ∈ U := (heU hqe).1
    rw [hK p hp, hpq]
    refine e.pullbackEnd_of_coe_eq_adaptedNormalExtension he hqe
      ((hγ.contDiffAt (hU.mem_nhds hqU)).of_le le_add_self)
      (hJ.continuousOn.continuousAt (hΩ.mem_nhds (hγΩ hqU))) (J.inChart_inChart y (hγΩ hqU))
      (hesd ?_)
    rw [← hγe]
    exact e.map_source hqe
  have hn : (((ℓ - 1 : ℕ∞) : ℕ∞ω) + 1) ≤ ℓ := by
    exact_mod_cast (tsub_add_cancel_of_le hℓ).le
  refine ⟨ψ, hψcoe, hψsymm, hψsrc, hψtgt, hx₀ψ, hψx₀,
    { contMDiffOn := hcont
      contMDiffOn_symm := hcont_symm
      isImage := hImage
      mfderiv_comp_toEndomorphism := ?_
      contDiffOn_chartPushforward :=
        ((e'.contDiffOn_pullbackEnd (hec.mono (he'src ▸ inter_subset_left)) (hesc.mono ?_)
          ((hJ.mono he'Ω).of_le (le_self_add.trans hn)) hn).mono htgt').congr hK'
      chartPushforward_of_snd_eq_zero := hstd }⟩
  · -- Intertwining along `ι (N)`: `dψ` turns `J` into `ψ_* J`, which is standard there.
    rintro x ⟨hx, hxι⟩
    have hpx := ψ.map_source hx
    rw [J.mfderiv_comp_toEndomorphism ψ hx
        ((hcont.contMDiffAt (ψ.open_source.mem_nhds hx)).mdifferentiableAt hℓ0)
        ((hcont_symm.contMDiffAt (ψ.open_target.mem_nhds hpx)).mdifferentiableAt hℓ0),
      hstd _ hpx ((hImage hx).2 hxι)]
  · intro z hz
    rw [← e'.right_inv hz]
    exact e.map_source (he'tgt hz).1

/-- **Adapted charts along a totally real embedding.** Let `ι` be a `C^k` totally real embedding
for a `C^ℓ` almost complex structure `J`, with `1 ≤ ℓ` and `ℓ + 1 ≤ k`. Near `ι x₀` there is an
adapted chart `ψ` of `M` into `F × F` (`TauCeti.IsAdaptedChart`): `C^ℓ` with `C^ℓ` inverse,

* a point of the source of `ψ` lies on `ι (N)` exactly when its image lies on `F × {0}`;
* at points of `ι (N)` the derivative of `ψ` intertwines `J` with `(v, w) ↦ (-w, v)`;
* the pushed-forward structure `ψ_* J = dψ ∘ J ∘ dψ⁻¹` is `C^(ℓ-1)` on the target of `ψ` and
  standard on its zero section.

Moreover `ψ⁻¹ = χ⁻¹ ∘ e` on the target of `ψ`, for the extended chart `χ` at `ι x₀` and a
partial homeomorphism `e` whose underlying map is the adapted normal extension of `ι` and `J`
read in the extended charts at `x₀` and `ι x₀`. -/
theorem IsTotallyRealEmbedding.exists_adaptedChart [IsManifold I' k N]
    (h : IsTotallyRealEmbedding I' I k J.almostComplexStructureAt ι) (hℓ : 1 ≤ ℓ)
    (hk : (ℓ : ℕ∞ω) + 1 ≤ k) (x₀ : N) :
    ∃ (ψ : OpenPartialHomeomorph M (F × F)) (e : OpenPartialHomeomorph (F × F) E),
      ⇑e = adaptedNormalExtension (writtenInExtChartAt I' I x₀ ι) (J.inChart (ι x₀)) ∧
      ψ.target ⊆ e.source ∧ (∀ p ∈ ψ.target, ψ.symm p = (extChartAt I (ι x₀)).symm (e p)) ∧
      ι x₀ ∈ ψ.source ∧ ψ.source ⊆ (extChartAt I (ι x₀)).source ∧ IsAdaptedChart J ι ψ := by
  have hk1 : 1 ≤ k := le_add_self.trans hk
  have : IsManifold I' ((ℓ : ℕ∞ω) + 1) N := IsManifold.of_le hk
  have : IsManifold I ((ℓ : ℕ∞ω) + 1) M := IsManifold.of_le (n := ∞) (by exact_mod_cast le_top)
  have hℓ' : (1 : ℕ∞ω) ≤ ℓ := by exact_mod_cast hℓ
  have hι : ContMDiff I' I ((ℓ : ℕ∞ω) + 1) ι := h.isSmoothEmbedding.contMDiff.of_le hk
  set y := ι x₀
  set χ := extChartAt I y
  set φ := extChartAt I' x₀
  set γ := writtenInExtChartAt I' I x₀ ι
  set U := φ.target ∩ φ.symm ⁻¹' (ι ⁻¹' χ.source)
  have hU : IsOpen U := (continuousOn_extChartAt_symm x₀).isOpen_inter_preimage
    (isOpen_extChartAt_target x₀) ((isOpen_extChartAt_source y).preimage hι.continuous)
  have hx₀U : φ x₀ ∈ U := by
    refine ⟨mem_extChartAt_target x₀, ?_⟩
    rw [mem_preimage, mem_preimage, φ.left_inv (mem_extChartAt_source x₀)]
    exact mem_extChartAt_source y
  have hγ : ContDiffOn ℝ ((ℓ : ℕ∞ω) + 1) γ U := by
    have := (contMDiffOn_iff_of_subset_source' (x := x₀) (y := y)
      (s := φ.source ∩ ι ⁻¹' χ.source) inter_subset_left (fun z hz ↦ hz.2)).1 hι.contMDiffOn
    rwa [PartialEquiv.image_source_inter_eq'] at this
  obtain ⟨e, he, he₀, heU, -, hec, hesc⟩ :=
    TauCeti.exists_adaptedChart hU (isOpen_extChartAt_target y) hx₀U hℓ' hγ
      (J.contDiffOn_inChart y) (fun z hz ↦ χ.map_source hz.2)
      (J.inChart_inChart y (χ.map_source hx₀U.2)) (h.injective_fderiv_writtenInExtChartAt hk1 x₀)
      (h.isMaximalTotallyReal_range_fderiv_writtenInExtChartAt hk1 x₀)
  -- The parameters whose zero-section point lies in the source of `e` are cut out by an open `O`.
  set S : Set N := (φ.source ∩ ι ⁻¹' χ.source) ∩ (fun z ↦ (φ z, (0 : F))) ⁻¹' e.source
  have hS : IsOpen S :=
    (((continuousOn_extChartAt x₀).mono inter_subset_left).prodMk
      continuousOn_const).isOpen_inter_preimage
      ((isOpen_extChartAt_source x₀).inter ((isOpen_extChartAt_source y).preimage hι.continuous))
      e.open_source
  obtain ⟨O, hO, hOS⟩ := h.isSmoothEmbedding.isEmbedding.isInducing.isOpen_iff.mp hS
  have hOe (z : N) (hz : ι z ∈ O) : z ∈ φ.source ∧ (φ z, (0 : F)) ∈ e.source := by
    have hzS : z ∈ S := hOS ▸ hz
    exact ⟨hzS.1.1, hzS.2⟩
  have hx₀O : y ∈ O := by
    rw [← mem_preimage, hOS]
    exact ⟨⟨mem_extChartAt_source x₀, mem_extChartAt_source y⟩, he₀⟩
  obtain ⟨ψ, -, hψsymm, hψsrc, hψtgt, hx₀ψ, -, hψ⟩ :=
    exists_isAdaptedChart_of_coe_eq_adaptedNormalExtension h.isSmoothEmbedding.contMDiff hℓ hk he
      hec hesc heU hO hx₀O hOe
  exact ⟨ψ, e, he, fun p hp ↦ ((hψtgt p).1 hp).1, fun p _ ↦ hψsymm p, hx₀ψ,
    fun x hx ↦ ((hψsrc x).1 hx).1, hψ⟩

/-- **Flat model.** For the inclusion `V → V × V`, `v ↦ (v, 0)`, and the standard structure
`(v, w) ↦ (-w, v)` on `V × V`, the adapted extension built from the extended charts is the
identity. -/
theorem adaptedNormalExtension_writtenInExtChartAt_inl {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] (x₀ : V) :
    adaptedNormalExtension
        (writtenInExtChartAt 𝓘(ℝ, V) 𝓘(ℝ, V × V) x₀ (ContinuousLinearMap.inl ℝ V V))
        ((SmoothAlmostComplexStructure.product V).inChart (ContinuousLinearMap.inl ℝ V V x₀)) =
      id := by
  have hJ : (SmoothAlmostComplexStructure.product V).inChart (ContinuousLinearMap.inl ℝ V V x₀) =
      fun _ ↦ (-ContinuousLinearMap.snd ℝ V V).prod (ContinuousLinearMap.fst ℝ V V) := by
    funext z
    rw [SmoothAlmostComplexStructure.inChart_def]
    exact (inCoordinates_tangent_bundle_core_model_space (I := 𝓘(ℝ, V × V))
      (I' := 𝓘(ℝ, V × V)) _ _ _ _ _).trans
        (ContinuousLinearMap.ext fun v ↦ (SmoothAlmostComplexStructure.product_apply z v).trans rfl)
  rw [writtenInExtChartAt_model_space, hJ, adaptedNormalExtension_inl]

end TauCeti

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
in the image of a neighbourhood of `x₀`.

The convergence of the charts under `C^ℓ` convergence of the structure is not treated here.

## Main declarations

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

/-- **Adapted charts along a totally real embedding.** Let `ι` be a `C^k` totally real embedding
for a `C^ℓ` almost complex structure `J`, with `1 ≤ ℓ` and `ℓ + 1 ≤ k`. Near `ι x₀` there is a
chart `ψ` of `M` into `F × F`, `C^ℓ` with `C^ℓ` inverse, such that

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
      ι x₀ ∈ ψ.source ∧ ψ.source ⊆ (extChartAt I (ι x₀)).source ∧
      ContMDiffOn I 𝓘(ℝ, F × F) ℓ ψ ψ.source ∧ ContMDiffOn 𝓘(ℝ, F × F) I ℓ ψ.symm ψ.target ∧
      ψ.IsImage (range ι) {p | p.2 = 0} ∧
      (∀ x ∈ ψ.source ∩ range ι,
        (mfderiv I 𝓘(ℝ, F × F) ψ x).comp (J.toEndomorphism x) =
          ((-ContinuousLinearMap.snd ℝ F F).prod (ContinuousLinearMap.fst ℝ F F)).comp
            (mfderiv I 𝓘(ℝ, F × F) ψ x)) ∧
      ContDiffOn ℝ ((ℓ - 1 : ℕ∞) : ℕ∞ω) (J.chartPushforward ψ) ψ.target ∧
      ∀ p ∈ ψ.target, p.2 = 0 →
        J.chartPushforward ψ p =
          (-ContinuousLinearMap.snd ℝ F F).prod (ContinuousLinearMap.fst ℝ F F) := by
  -- Regularity bookkeeping: everything happens at order `ℓ + 1`.
  have hkM : ((ℓ : ℕ∞ω) + 1) ≤ ∞ := by exact_mod_cast le_top
  have : IsManifold I' ((ℓ : ℕ∞ω) + 1) N := IsManifold.of_le hk
  have : IsManifold I ((ℓ : ℕ∞ω) + 1) M := IsManifold.of_le hkM
  have : IsManifold I' 1 N := IsManifold.of_le (n := (ℓ : ℕ∞ω) + 1) le_add_self
  have : IsManifold I 1 M := IsManifold.of_le (n := (ℓ : ℕ∞ω) + 1) le_add_self
  have hℓ' : (1 : ℕ∞ω) ≤ ℓ := by exact_mod_cast hℓ
  have hι : ContMDiff I' I ((ℓ : ℕ∞ω) + 1) ι := h.isSmoothEmbedding.contMDiff.of_le hk
  set y := ι x₀
  set χ := extChartAt I y
  set φ := extChartAt I' x₀
  set γ := writtenInExtChartAt I' I x₀ ι
  set Jχ := J.inChart y with hJχ
  have hγapp (z : F) : γ z = χ (ι (φ.symm z)) := rfl
  -- The parameter domain and the ambient chart target.
  set U := φ.target ∩ φ.symm ⁻¹' (ι ⁻¹' χ.source)
  have hU : IsOpen U := (continuousOn_extChartAt_symm x₀).isOpen_inter_preimage
    (isOpen_extChartAt_target x₀) ((isOpen_extChartAt_source y).preimage hι.continuous)
  have hΩ : IsOpen χ.target := isOpen_extChartAt_target y
  have hx₀U : φ x₀ ∈ U := by
    refine ⟨mem_extChartAt_target x₀, ?_⟩
    rw [mem_preimage, mem_preimage, φ.left_inv (mem_extChartAt_source x₀)]
    exact mem_extChartAt_source y
  have hγΩ : MapsTo γ U χ.target := fun z hz ↦ χ.map_source hz.2
  have hγ : ContDiffOn ℝ ((ℓ : ℕ∞ω) + 1) γ U := by
    have := (contMDiffOn_iff_of_subset_source' (x := x₀) (y := y)
      (s := φ.source ∩ ι ⁻¹' χ.source) inter_subset_left (fun z hz ↦ hz.2)).1 hι.contMDiffOn
    rwa [PartialEquiv.image_source_inter_eq'] at this
  have hJ : ContDiffOn ℝ (ℓ : ℕ∞ω) Jχ χ.target := J.contDiffOn_inChart y
  have hγx₀ : γ (φ x₀) = χ y := by
    rw [hγapp, φ.left_inv (mem_extChartAt_source x₀)]
  have hsq : ∀ v, Jχ (γ (φ x₀)) (Jχ (γ (φ x₀)) v) = -v :=
    J.inChart_inChart y (hγΩ hx₀U)
  have hιd : MDifferentiableAt I' I ι x₀ :=
    (hι x₀).mdifferentiableAt (by simp)
  have hDγ : fderiv ℝ γ (φ x₀) = mfderiv I' I ι x₀ :=
    (hιd.mfderiv_eq_fderiv_extChartAt_conj rfl).symm
  have hinj : Function.Injective (fderiv ℝ γ (φ x₀)) := by
    rw [hDγ]
    exact h.mfderiv_injective x₀
  have htr : IsMaximalTotallyReal (Jχ (γ (φ x₀))).toLinearMap (fderiv ℝ γ (φ x₀)).range := by
    rw [hDγ, hγx₀, hJχ, J.inChart_extChartAt_self]
    have := isMaximalTotallyRealMap_iff.1 h.isMaximalTotallyRealMap x₀
    rwa [ContMDiffAlmostComplexStructure.almostComplexStructureAt_toLinearMap] at this
  obtain ⟨e, he, he₀, heU, heΩ, hec, hesc⟩ :=
    TauCeti.exists_adaptedChart hU hΩ hx₀U hℓ' hγ hJ hγΩ hsq hinj htr
  -- The parameters whose zero-section point lies in the source of `e`.
  set S : Set N := (φ.source ∩ ι ⁻¹' χ.source) ∩ (fun z ↦ (φ z, (0 : F))) ⁻¹' e.source
  have hS : IsOpen S :=
    (((continuousOn_extChartAt x₀).mono inter_subset_left).prodMk
      continuousOn_const).isOpen_inter_preimage
      ((isOpen_extChartAt_source x₀).inter ((isOpen_extChartAt_source y).preimage hι.continuous))
      e.open_source
  obtain ⟨O, hO, hOS⟩ := h.isSmoothEmbedding.isEmbedding.isInducing.isOpen_iff.mp hS
  -- The extended chart at `y` as an open partial homeomorphism, then `e⁻¹`, restricted to `O`.
  let ψ := (((chartAt H y).extendTrans I (Homeomorph.refl E)).trans e.symm).restrOpen O hO
  have hψcoe (x : M) : ψ x = e.symm (χ x) := by
    simp [ψ, χ]
  have hψsymm (p : F × F) : ψ.symm p = χ.symm (e p) := by
    simp [ψ, χ]
  have hψsrc {x : M} : x ∈ ψ.source ↔ (x ∈ χ.source ∧ χ x ∈ e.target) ∧ x ∈ O := by
    simp [ψ, χ]
  have hψtgt {p : F × F} :
      p ∈ ψ.target ↔ (p ∈ e.source ∧ e p ∈ χ.target) ∧ χ.symm (e p) ∈ O := by
    simp [ψ, χ, I.range_eq_univ]
  have hℓ0 : (ℓ : ℕ∞ω) ≠ 0 := (zero_lt_one.trans_le hℓ').ne'
  have : IsManifold I (ℓ : ℕ∞ω) M := IsManifold.of_le (n := ∞) (by exact_mod_cast le_top)
  have hγe (q : F) : e (q, 0) = γ q := by rw [he, adaptedNormalExtension_zero]
  have hed {p : F × F} (hp : p ∈ e.source) : DifferentiableAt ℝ e p :=
    (hec.contDiffAt (e.open_source.mem_nhds hp)).differentiableAt hℓ0
  have hesd {z : E} (hz : z ∈ e.target) : DifferentiableAt ℝ e.symm z :=
    (hesc.contDiffAt (e.open_target.mem_nhds hz)).differentiableAt hℓ0
  have htgt : ψ.target ⊆ e.source := fun p hp ↦ (hψtgt.1 hp).1.1
  have hsrc : ψ.source ⊆ χ.source := fun x hx ↦ (hψsrc.1 hx).1.1
  -- The base point.
  have hx₀ψ : ι x₀ ∈ ψ.source := by
    refine hψsrc.2 ⟨⟨mem_extChartAt_source y, ?_⟩, ?_⟩
    · rw [← hγx₀, ← hγe]
      exact e.map_source he₀
    · rw [← mem_preimage, hOS]
      exact ⟨⟨mem_extChartAt_source x₀, mem_extChartAt_source y⟩, he₀⟩
  -- Regularity of the chart and of its inverse.
  have hcont : ContMDiffOn I 𝓘(ℝ, F × F) ℓ ψ ψ.source := by
    refine (hesc.contMDiffOn.comp ((contMDiffOn_extChartAt (x := y)).mono fun x hx ↦ ?_)
      fun x hx ↦ (hψsrc.1 hx).1.2).congr fun x _ ↦ hψcoe x
    rw [← extChartAt_source I]
    exact hsrc hx
  have hcont_symm : ContMDiffOn 𝓘(ℝ, F × F) I ℓ ψ.symm ψ.target :=
    (((contMDiffOn_extChartAt_symm y).comp hec.contMDiffOn
      fun p hp ↦ heΩ (e.map_source hp)).mono htgt).congr fun p _ ↦ hψsymm p
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
      have hxt : χ x ∈ e.target := (hψsrc.1 hx).1.2
      have heq : χ x = χ (ι (φ.symm (ψ x).1)) := by
        rw [← hγapp, ← hγe, ← h0, hψcoe, e.right_inv hxt]
      exact ⟨φ.symm (ψ x).1, (χ.injOn (hsrc hx) hqU.2 heq).symm⟩
    · rintro ⟨z, rfl⟩
      have hzS : z ∈ S := by
        rw [← hOS]
        exact (hψsrc.1 hx).2
      rw [hψcoe, ← φ.left_inv hzS.1.1, ← hγapp, ← hγe, e.left_inv hzS.2]
  -- The pushed-forward structure is the model pullback by `e`.
  have hK : ∀ p ∈ ψ.target, J.chartPushforward ψ p = e.pullbackEnd Jχ p := fun p hp ↦
    J.chartPushforward_eq_pullbackEnd_inChart y ψ e (hψtgt.1 hp).1.2
      (Eventually.of_forall hψcoe) (Eventually.of_forall hψsymm) (hed (htgt hp))
      (hesd (e.map_source (htgt hp)))
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
  refine ⟨ψ, e, he, htgt, fun p _ ↦ hψsymm p, hx₀ψ, hsrc, hcont, hcont_symm, hImage, ?_,
    ((e.contDiffOn_pullbackEnd hec hesc ((hJ.mono heΩ).of_le (le_self_add.trans hn)) hn).mono
      htgt).congr hK, hstd⟩
  -- Intertwining along `ι (N)`: `dψ` turns `J` into `ψ_* J`, which is standard there.
  rintro x ⟨hx, hxι⟩
  have hpx := ψ.map_source hx
  rw [J.mfderiv_comp_toEndomorphism ψ hx
      ((hcont.contMDiffAt (ψ.open_source.mem_nhds hx)).mdifferentiableAt hℓ0)
      ((hcont_symm.contMDiffAt (ψ.open_target.mem_nhds hpx)).mdifferentiableAt hℓ0),
    hstd _ hpx ((hImage hx).2 hxι)]

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

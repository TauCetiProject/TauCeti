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

* `TauCeti.ContMDiffAlmostComplexStructure.chartPushforward`: an almost complex structure read in
  the coordinates of a chart with values in a normed space.
* `TauCeti.IsTotallyRealEmbedding.exists_adaptedChart`: the adapted chart.
* `TauCeti.adaptedNormalExtension_writtenInExtChartAt_inl`: in the flat model `V ⊆ V × V` with
  the standard structure the adapted extension is the identity, so the construction loses no
  regularity there.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Exercise B.4.10.
-/

public noncomputable section

open Set Filter Manifold
open scoped Topology Manifold ContDiff

namespace TauCeti

namespace ContMDiffAlmostComplexStructure

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {ℓ : ℕ∞}

/-- The structure `J` pushed forward along a chart `ψ` of `M` with values in a normed space `G`:
at `p`, the endomorphism `dψ ∘ J ∘ dψ⁻¹` of `G`, taken at `ψ⁻¹ p` and written with the manifold
derivatives of `ψ` and of its inverse. On the target of `ψ` this is `J` in the coordinates
of `ψ`. -/
def chartPushforward {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    (J : ContMDiffAlmostComplexStructure I ℓ M) (ψ : OpenPartialHomeomorph M G) (p : G) :
    G →L[ℝ] G :=
  (mfderiv I 𝓘(ℝ, G) ψ (ψ.symm p)).comp
    ((J.toEndomorphism (ψ.symm p)).comp (mfderiv 𝓘(ℝ, G) I ψ.symm p))

/-- Evaluate a pushed-forward structure. -/
theorem chartPushforward_apply {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    (J : ContMDiffAlmostComplexStructure I ℓ M) (ψ : OpenPartialHomeomorph M G) (p w : G) :
    J.chartPushforward ψ p w =
      mfderiv I 𝓘(ℝ, G) ψ (ψ.symm p) (J (ψ.symm p) (mfderiv 𝓘(ℝ, G) I ψ.symm p w)) := by
  unfold chartPushforward
  rfl

end ContMDiffAlmostComplexStructure

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
  -- The extended chart at `y` as an open partial homeomorphism.
  let χ' : OpenPartialHomeomorph M E :=
    (chartAt H y).trans I.toHomeomorph.toOpenPartialHomeomorph
  have hχ'coe : ⇑χ' = χ := by
    funext x
    simp [χ', χ, extChartAt, OpenPartialHomeomorph.extend]
  have hχ'symm : ⇑χ'.symm = χ.symm := by
    funext x
    simp [χ', χ, extChartAt, OpenPartialHomeomorph.extend]
  have hχ'src : χ'.source = χ.source := by
    simp [χ', χ]
  have hχ'tgt : χ'.target = χ.target := by
    ext z
    simp [χ', χ, I.range_eq_univ]
  -- The parameters whose zero-section point lies in the source of `e`.
  set S : Set N := (φ.source ∩ ι ⁻¹' χ.source) ∩ (fun z ↦ (φ z, (0 : F))) ⁻¹' e.source
  have hS : IsOpen S :=
    (((continuousOn_extChartAt x₀).mono inter_subset_left).prodMk
      continuousOn_const).isOpen_inter_preimage
      ((isOpen_extChartAt_source x₀).inter ((isOpen_extChartAt_source y).preimage hι.continuous))
      e.open_source
  obtain ⟨O, hO, hOS⟩ := h.isSmoothEmbedding.isEmbedding.isInducing.isOpen_iff.mp hS
  let ψ := (χ'.trans e.symm).restrOpen O hO
  have hψcoe (x : M) : ψ x = e.symm (χ x) := by
    simp [ψ, hχ'coe]
  have hψsymm (p : F × F) : ψ.symm p = χ.symm (e p) := by
    simp [ψ, hχ'symm]
  have hψsrc {x : M} : x ∈ ψ.source ↔ (x ∈ χ.source ∧ χ x ∈ e.target) ∧ x ∈ O := by
    simp [ψ, hχ'coe, hχ'src]
  have hψtgt {p : F × F} :
      p ∈ ψ.target ↔ (p ∈ e.source ∧ e p ∈ χ.target) ∧ χ.symm (e p) ∈ O := by
    simp [ψ, hχ'symm, hχ'tgt]
  have hℓ0 : (ℓ : ℕ∞ω) ≠ 0 := (zero_lt_one.trans_le hℓ').ne'
  have : IsManifold I (ℓ : ℕ∞ω) M := IsManifold.of_le (n := ∞) (by exact_mod_cast le_top)
  have hγe (q : F) : e (q, 0) = γ q := by rw [he, adaptedNormalExtension_zero]
  have hed {p : F × F} (hp : p ∈ e.source) : DifferentiableAt ℝ e p :=
    (hec.contDiffAt (e.open_source.mem_nhds hp)).differentiableAt hℓ0
  have hesd {z : E} (hz : z ∈ e.target) : DifferentiableAt ℝ e.symm z :=
    (hesc.contDiffAt (e.open_target.mem_nhds hz)).differentiableAt hℓ0
  have htgt : ψ.target ⊆ e.source := fun p hp ↦ (hψtgt.1 hp).1.1
  have hsrc : ψ.source ⊆ χ.source := fun x hx ↦ (hψsrc.1 hx).1.1
  -- Facts about the zero section of `e` over a point of `U`.
  have hq {q : F} (hq : (q, 0) ∈ e.source) :
      q ∈ U ∧ ContDiffAt ℝ 1 γ q ∧ ContinuousAt Jχ (γ q) ∧
        (∀ v, Jχ (γ q) (Jχ (γ q) v) = -v) ∧ DifferentiableAt ℝ e.symm (γ q) := by
    have hqU : q ∈ U := (heU hq).1
    refine ⟨hqU, (hγ.contDiffAt (hU.mem_nhds hqU)).of_le le_add_self,
      hJ.continuousOn.continuousAt (hΩ.mem_nhds (hγΩ hqU)), J.inChart_inChart y (hγΩ hqU),
      hesd ?_⟩
    rw [← hγe]
    exact e.map_source hq
  -- The derivative of `ψ` is that of `e.symm` after the chart derivative.
  have hDψ {x : M} (hx : x ∈ ψ.source) (v : TangentSpace I x) :
      mfderiv I 𝓘(ℝ, F × F) ψ x v =
        fderiv ℝ e.symm (χ x) (mfderiv I 𝓘(ℝ, E) χ x v) := by
    have hxt : χ x ∈ e.target := (hψsrc.1 hx).1.2
    have heq : ⇑ψ ∘ χ.symm =ᶠ[𝓝 (χ x)] e.symm := by
      filter_upwards [hΩ.mem_nhds (χ.map_source (hsrc hx))] with z hz
      simp only [Function.comp_apply, hψcoe, χ.right_inv hz]
    rw [mfderiv_eq_fderiv_comp_mfderiv_extChartAt (hsrc hx)
      ((hesd hxt).congr_of_eventuallyEq heq), heq.fderiv_eq]
    rfl
  -- The derivative of `ψ.symm` is the chart derivative after that of `e`.
  have hDψs {p : F × F} (hp : p ∈ ψ.target) (w : F × F) :
      mfderiv 𝓘(ℝ, F × F) I ψ.symm p w =
        mfderivWithin 𝓘(ℝ, E) I χ.symm (range I) (e p) (fderiv ℝ e p w) := by
    have hpt := hψtgt.1 hp
    have hfun : ⇑ψ.symm = χ.symm ∘ e := funext hψsymm
    have hχs : MDifferentiableAt 𝓘(ℝ, E) I χ.symm (e p) := by
      have := mdifferentiableWithinAt_extChartAt_symm (I := I) (x := y) hpt.1.2
      rwa [I.range_eq_univ, mdifferentiableWithinAt_univ] at this
    rw [hfun, mfderiv_comp p hχs (hed hpt.1.1).mdifferentiableAt,
      I.range_eq_univ,
      mfderivWithin_univ, mfderiv_eq_fderiv]
    rfl
  -- The base point.
  have hx₀ψ : ι x₀ ∈ ψ.source := by
    refine hψsrc.2 ⟨⟨mem_extChartAt_source y, ?_⟩, ?_⟩
    · rw [← hγx₀, ← hγe]
      exact e.map_source he₀
    · change x₀ ∈ ι ⁻¹' O
      rw [hOS]
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
  -- Intertwining along `ι (N)`.
  have hint : ∀ x ∈ ψ.source ∩ range ι,
      (mfderiv I 𝓘(ℝ, F × F) ψ x).comp (J.toEndomorphism x) =
        ((-ContinuousLinearMap.snd ℝ F F).prod (ContinuousLinearMap.fst ℝ F F)).comp
          (mfderiv I 𝓘(ℝ, F × F) ψ x) := by
    rintro x ⟨hx, hxι⟩
    have h0 : (ψ x).2 = 0 := (hImage hx).2 hxι
    have hpq : ψ x = ((ψ x).1, 0) := Prod.ext rfl h0
    have hqe : ((ψ x).1, (0 : F)) ∈ e.source := hpq ▸ htgt (ψ.map_source hx)
    have hxt : χ x ∈ e.target := (hψsrc.1 hx).1.2
    have hχx : χ x = γ (ψ x).1 := by rw [← hγe, ← hpq, hψcoe, e.right_inv hxt]
    obtain ⟨-, hγ1, hJc, hsq', hs⟩ := hq hqe
    refine ContinuousLinearMap.ext fun v ↦ ?_
    have hinv := congr($(mfderivWithin_extChartAt_symm_comp_mfderiv_extChartAt' (I := I)
      (x := y) (hsrc hx)) v)
    have hJ' : mfderiv I 𝓘(ℝ, E) χ x (J x v) = Jχ (χ x) (mfderiv I 𝓘(ℝ, E) χ x v) := by
      have hc := J.inChart_apply_eq_mfderiv y (χ.map_source (hsrc hx)) (mfderiv I 𝓘(ℝ, E) χ x v)
      rw [χ.left_inv (hsrc hx)] at hc
      rw [hJχ, hc]
      exact congrArg _ (congrArg _ hinv.symm)
    have hP (w : E) : fderiv ℝ e.symm (χ x) (Jχ (χ x) w) =
        (-(fderiv ℝ e.symm (χ x) w).2, (fderiv ℝ e.symm (χ x) w).1) := by
      rw [hχx]
      exact e.fderiv_symm_apply_of_coe_eq_adaptedNormalExtension he hqe hγ1 hJc hsq' hs w
    have key : mfderiv I 𝓘(ℝ, F × F) ψ x (J x v) =
        ((-ContinuousLinearMap.snd ℝ F F).prod (ContinuousLinearMap.fst ℝ F F))
          (mfderiv I 𝓘(ℝ, F × F) ψ x v) := by
      rw [hDψ hx, hDψ hx, hJ']
      refine (hP _).trans ?_
      simp
    exact key
  -- The pushed-forward structure is the model pullback by `e`.
  have hK : ∀ p ∈ ψ.target, J.chartPushforward ψ p = e.pullbackEnd Jχ p := by
    intro p hp
    have hpt := hψtgt.1 hp
    have hxs : ψ.symm p ∈ ψ.source := ψ.map_target hp
    have hχx : χ (ψ.symm p) = e p := by rw [hψsymm, χ.right_inv hpt.1.2]
    refine ContinuousLinearMap.ext fun w ↦ ?_
    rw [ContMDiffAlmostComplexStructure.chartPushforward_apply, hDψ hxs, hDψs hp, hχx,
      OpenPartialHomeomorph.pullbackEnd_apply, hJχ, J.inChart_apply_eq_mfderiv y hpt.1.2,
      ← hψsymm]
    rfl
  have hn : (((ℓ - 1 : ℕ∞) : ℕ∞ω) + 1) ≤ ℓ := by
    exact_mod_cast (tsub_add_cancel_of_le hℓ).le
  refine ⟨ψ, e, he, htgt, fun p _ ↦ hψsymm p, hx₀ψ, hsrc, hcont, hcont_symm, hImage, hint,
    ((e.contDiffOn_pullbackEnd hec hesc ((hJ.mono heΩ).of_le (le_self_add.trans hn)) hn).mono
      htgt).congr hK,
    fun p hp h0 ↦ ?_⟩
  have hpq : p = (p.1, 0) := Prod.ext rfl h0
  have hqe : (p.1, (0 : F)) ∈ e.source := hpq ▸ htgt hp
  obtain ⟨-, hγ1, hJc, hsq', hs⟩ := hq hqe
  rw [hK p hp, hpq]
  exact e.pullbackEnd_of_coe_eq_adaptedNormalExtension he hqe hγ1 hJc hsq' hs

/-- **No loss of regularity in the flat case.** For the inclusion `V → V × V`, `v ↦ (v, 0)`, and
the constant standard structure `(v, w) ↦ (-w, v)`, the adapted extension built from the
extended charts is the identity. -/
theorem adaptedNormalExtension_writtenInExtChartAt_inl {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] (n : ℕ∞) (x₀ : V)
    (hsq : ∀ v, ((-ContinuousLinearMap.snd ℝ V V).prod (ContinuousLinearMap.fst ℝ V V))
      (((-ContinuousLinearMap.snd ℝ V V).prod (ContinuousLinearMap.fst ℝ V V)) v) = -v) :
    adaptedNormalExtension
        (writtenInExtChartAt 𝓘(ℝ, V) 𝓘(ℝ, V × V) x₀ (ContinuousLinearMap.inl ℝ V V))
        ((ContMDiffAlmostComplexStructure.const n
          ((-ContinuousLinearMap.snd ℝ V V).prod (ContinuousLinearMap.fst ℝ V V)) hsq).inChart
            (ContinuousLinearMap.inl ℝ V V x₀)) = id := by
  have hγ : writtenInExtChartAt 𝓘(ℝ, V) 𝓘(ℝ, V × V) x₀ (ContinuousLinearMap.inl ℝ V V) =
      ContinuousLinearMap.inl ℝ V V := by
    funext v
    simp [writtenInExtChartAt]
  have hJ : (ContMDiffAlmostComplexStructure.const n
      ((-ContinuousLinearMap.snd ℝ V V).prod (ContinuousLinearMap.fst ℝ V V)) hsq).inChart
        (ContinuousLinearMap.inl ℝ V V x₀) =
      fun _ ↦ (-ContinuousLinearMap.snd ℝ V V).prod (ContinuousLinearMap.fst ℝ V V) := by
    funext z
    rw [ContMDiffAlmostComplexStructure.inChart_def]
    exact (inCoordinates_tangent_bundle_core_model_space (I := 𝓘(ℝ, V × V))
      (I' := 𝓘(ℝ, V × V)) _ _ _ _ _).trans (by simp)
  rw [hγ, hJ, adaptedNormalExtension_inl]

end TauCeti

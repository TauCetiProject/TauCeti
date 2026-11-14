/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.FiberProduct.Manifold
public import TauCeti.Geometry.Manifold.Sard.Basic
public import TauCeti.Geometry.Manifold.Transversality.Basic
import TauCeti.Geometry.Manifold.ChartedSpace
import TauCeti.Geometry.Manifold.MFDeriv.Prod
import TauCeti.Geometry.Manifold.ModelTransport.Interior

/-!
# Parametric transversality on manifolds

Let `F : M × S → N` be a family of maps parametrized by a manifold `S`, and let `g : Z → N` be a
fixed target map. When the total family `F` is transverse to `g`, the parameter values `s : S` at
which the slice `x ↦ F (x, s)` fails to be transverse to `g` are precisely the critical values of
the parameter projection `{((x, s), z) // F (x, s) = g z} → S` on the transverse fibre product.
Applying Sard's theorem at its sharp regularity `n ≥ dim M + dim Z - dim N + 1` shows that these
non-transverse parameters form a chartwise null set (`TauCeti.IsNullSet`) in `S`, so the transverse
parameters are dense in `S`.

Two structural features make this directly usable in relative differential topology and cobordism:

* **No countability assumption on `S` or `N`.** Nullity in `S` is chartwise, so restricting `S` to
  the source of each preferred chart makes the local parameter space second countable; only `M` and
  `Z` need to be Lindelöf.
* **Corners in the models and half-space source manifolds.** Transporting boundaryless manifolds to
  their vector-space copies via `TauCeti.BoundarylessModel.interiorDiffeomorph` removes any
  `ModelWithCorners.Boundaryless` restriction on `M`, `S`, `Z`, or `N`. For a Lindelöf manifold `M`
  with boundary modelled on `𝓡∂ (m + 1)`, applying the boundaryless theorem separately to the open
  manifold interior and to the boundary `(∂M : Type*)` yields simultaneous interior and boundary
  transversality (hence global ambient transversality by
  `TauCeti.IsTransverse.of_interior_and_boundary`) outside a chartwise null set of parameters.

## Main results

* `TauCeti.isRegularPoint_snd_transverseFiberProduct_iff`,
  `TauCeti.isRegularValue_snd_transverseFiberProduct_iff`: on boundaryless models, regularity of
  the parameter projection on `{((x, s), z) // F (x, s) = g z}` is equivalent to transversality of
  the slice `x ↦ F (x, s)` to `g`.
* `TauCeti.isNullSet_not_isTransverse_slice`, `TauCeti.dense_isTransverse_slice`: parametric
  transversality at sharp Sard regularity `dim M + dim Z - dim N + 1 ≤ n` for boundaryless
  manifolds `M`, `S`, `Z`, `N` with `M` and `Z` Lindelöf.
* `TauCeti.isNullSet_not_isTransverse_slice_halfSpace`,
  `TauCeti.dense_isTransverse_slice_halfSpace`: facewise parametric transversality for a Lindelöf
  manifold `M` with boundary modelled on `𝓡∂ (m + 1)`.

## References

* M. Hirsch, *Differential Topology*, Graduate Texts in Mathematics 33, Springer, 1976, Chapter 3,
  §2, Theorem 2.7.
* V. Guillemin and A. Pollack, *Differential Topology*, Prentice-Hall, 1974, Chapter 2, §3
  (Transversality Theorem).
* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Graduate Texts in Mathematics 218,
  Springer, 2013, Theorem 6.35.
-/

public section

open Function Module MeasureTheory Set Topology TopologicalSpace
open scoped Manifold ContDiff

namespace TauCeti

section OpenSlice

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {EM HM M : Type*} [NormedAddCommGroup EM] [NormedSpace 𝕜 EM] [TopologicalSpace HM]
  {IM : ModelWithCorners 𝕜 EM HM} [TopologicalSpace M] [ChartedSpace HM M]
  {ES HS S : Type*} [NormedAddCommGroup ES] [NormedSpace 𝕜 ES] [TopologicalSpace HS]
  {IS : ModelWithCorners 𝕜 ES HS} [TopologicalSpace S] [ChartedSpace HS S]
  {EZ HZ Z : Type*} [NormedAddCommGroup EZ] [NormedSpace 𝕜 EZ] [TopologicalSpace HZ]
  {IZ : ModelWithCorners 𝕜 EZ HZ} [TopologicalSpace Z] [ChartedSpace HZ Z]
  {EN HN N : Type*} [NormedAddCommGroup EN] [NormedSpace 𝕜 EN] [TopologicalSpace HN]
  {IN : ModelWithCorners 𝕜 EN HN} [TopologicalSpace N] [ChartedSpace HN N]

private theorem mfderiv_slice_left_apply {F : M × S → N} {x : M} {s : S}
    (hF : MDifferentiableAt (IM.prod IS) IN F (x, s)) (u : TangentSpace IM x) :
    mfderiv IM IN (fun x' ↦ F (x', s)) x u =
      mfderiv (IM.prod IS) IN F (x, s) (u, (0 : TangentSpace IS s)) := by
  have hι : MDifferentiableAt IM (IM.prod IS) (fun x' ↦ (x', s)) x :=
    mdifferentiableAt_id.prodMk mdifferentiableAt_const
  have h := mfderiv_comp_apply x hF hι u
  rw [mfderiv_prod_left] at h
  exact h

private theorem isTransverseAt_prod_opens_left_iff {U : Opens M} {F : M × S → N} {g : Z → N}
    {x : U} {s : S} {z : Z} (hF : MDifferentiableAt (IM.prod IS) IN F (x, s)) :
    IsTransverseAt (IM.prod IS) IZ IN (fun q : U × S ↦ F (q.1, q.2)) g (x, s) z ↔
      IsTransverseAt (IM.prod IS) IZ IN F g (x, s) z := by
  let ι : U × S → M × S := fun q ↦ (q.1, q.2)
  have h1 : MDifferentiableAt (IM.prod IS) IM (fun q : U × S ↦ (q.1 : M)) (x, s) :=
    (contMDiff_subtype_val.mdifferentiableAt one_ne_zero).comp (x, s) mdifferentiableAt_fst
  have hι : MDifferentiableAt (IM.prod IS) (IM.prod IS) ι (x, s) := h1.prodMk mdifferentiableAt_snd
  have hid : ∀ v : TangentSpace (IM.prod IS) (x, s),
      mfderiv (IM.prod IS) (IM.prod IS) ι (x, s) v = v := fun v ↦ by
    rw [show ι = fun q : U × S ↦ ((q.1 : M), q.2) from rfl, mfderiv_prodMk h1 mdifferentiableAt_snd]
    refine Prod.ext ?_ ?_
    · change mfderiv (IM.prod IS) IM ((Subtype.val : U → M) ∘ Prod.fst) (x, s) v = v.1
      rw [mfderiv_comp_apply (x, s) (contMDiff_subtype_val.mdifferentiableAt one_ne_zero)
        mdifferentiableAt_fst, mfderiv_fst, TauCeti.Manifold.mfderiv_subtype_val]
      exact TauCeti.Manifold.tangentSpaceOpenEquiv_apply _ _
    · change mfderiv (IM.prod IS) IS Prod.snd (x, s) v = v.2
      rw [mfderiv_snd]
      rfl
  have hrange : (mfderiv (IM.prod IS) IN (F ∘ ι) (x, s)).range =
      (mfderiv (IM.prod IS) IN F (x, s)).range := by
    ext w
    simp only [LinearMap.mem_range, ContinuousLinearMap.coe_coe]
    refine exists_congr fun v ↦ ?_
    rw [mfderiv_comp_apply (x, s) hF hι, hid]
  rw [isTransverseAt_def, isTransverseAt_def]
  refine forall_congr' fun _ ↦ ?_
  change (mfderiv (IM.prod IS) IN (F ∘ ι) (x, s)).range ⊔ _ = ⊤ ↔ _
  rw [hrange]

private theorem isTransverseAt_prod_opens_right_iff {V : Opens S} {F : M × S → N} {g : Z → N}
    {x : M} {s : V} {z : Z} (hF : MDifferentiableAt (IM.prod IS) IN F (x, s)) :
    IsTransverseAt (IM.prod IS) IZ IN (fun q : M × V ↦ F (q.1, q.2)) g (x, s) z ↔
      IsTransverseAt (IM.prod IS) IZ IN F g (x, s) z := by
  let ι : M × V → M × S := fun q ↦ (q.1, q.2)
  have h2 : MDifferentiableAt (IM.prod IS) IS (fun q : M × V ↦ (q.2 : S)) (x, s) :=
    (contMDiff_subtype_val.mdifferentiableAt one_ne_zero).comp (x, s) mdifferentiableAt_snd
  have hι : MDifferentiableAt (IM.prod IS) (IM.prod IS) ι (x, s) :=
    mdifferentiableAt_fst.prodMk h2
  have hid : ∀ v : TangentSpace (IM.prod IS) (x, s),
      mfderiv (IM.prod IS) (IM.prod IS) ι (x, s) v = v := fun v ↦ by
    rw [show ι = fun q : M × V ↦ (q.1, (q.2 : S)) from rfl,
      mfderiv_prodMk mdifferentiableAt_fst h2]
    refine Prod.ext ?_ ?_
    · change mfderiv (IM.prod IS) IM Prod.fst (x, s) v = v.1
      rw [mfderiv_fst]
      rfl
    · change mfderiv (IM.prod IS) IS ((Subtype.val : V → S) ∘ Prod.snd) (x, s) v = v.2
      rw [mfderiv_comp_apply (x, s) (contMDiff_subtype_val.mdifferentiableAt one_ne_zero)
        mdifferentiableAt_snd, mfderiv_snd, TauCeti.Manifold.mfderiv_subtype_val]
      exact TauCeti.Manifold.tangentSpaceOpenEquiv_apply _ _
  have hrange : (mfderiv (IM.prod IS) IN (F ∘ ι) (x, s)).range =
      (mfderiv (IM.prod IS) IN F (x, s)).range := by
    ext w
    simp only [LinearMap.mem_range, ContinuousLinearMap.coe_coe]
    refine exists_congr fun v ↦ ?_
    rw [mfderiv_comp_apply (x, s) hF hι, hid]
  rw [isTransverseAt_def, isTransverseAt_def]
  refine forall_congr' fun _ ↦ ?_
  change (mfderiv (IM.prod IS) IN (F ∘ ι) (x, s)).range ⊔ _ = ⊤ ↔ _
  rw [hrange]

end OpenSlice

section FiberProduct

variable {EM HM M : Type*} [NormedAddCommGroup EM] [NormedSpace ℝ EM] [FiniteDimensional ℝ EM]
  [TopologicalSpace HM] {IM : ModelWithCorners ℝ EM HM} [IM.Boundaryless]
  [TopologicalSpace M] [ChartedSpace HM M]
  {ES HS S : Type*} [NormedAddCommGroup ES] [NormedSpace ℝ ES] [FiniteDimensional ℝ ES]
  [TopologicalSpace HS] {IS : ModelWithCorners ℝ ES HS} [IS.Boundaryless]
  [TopologicalSpace S] [ChartedSpace HS S]
  {EZ HZ Z : Type*} [NormedAddCommGroup EZ] [NormedSpace ℝ EZ] [FiniteDimensional ℝ EZ]
  [TopologicalSpace HZ] {IZ : ModelWithCorners ℝ EZ HZ} [IZ.Boundaryless]
  [TopologicalSpace Z] [ChartedSpace HZ Z]
  {EN HN N : Type*} [NormedAddCommGroup EN] [NormedSpace ℝ EN] [FiniteDimensional ℝ EN]
  [TopologicalSpace HN] {IN : ModelWithCorners ℝ EN HN} [IN.Boundaryless]
  [TopologicalSpace N] [ChartedSpace HN N]
  {n : ℕ∞ω} [IsManifold IM n M] [IsManifold IS n S] [IsManifold IZ n Z] [IsManifold IN n N]
  {F : M × S → N} {g : Z → N}

/-- On the transverse fibre product `{((x, s), z) // F (x, s) = g z}` of a `C^n` family
`F : M × S → N` (`1 ≤ n`) transverse to `g : Z → N`, a point `p` is regular for the parameter
projection `q ↦ q.1.1.2` if and only if the slice `x ↦ F (x, p.1.1.2)` is transverse to `g` at
`(p.1.1.1, p.1.2)`. -/
theorem isRegularPoint_snd_transverseFiberProduct_iff (hn : 1 ≤ n)
    (hF : ContMDiff (IM.prod IS) IN n F) (hg : ContMDiff IZ IN n g)
    (hFtrans : IsTransverse (IM.prod IS) IZ IN F g)
    (p : {p : (M × S) × Z // F p.1 = g p.2}) :
    letI := transverseFiberProductChartedSpace hn hF hg
      (fun q ↦ (hFtrans.isTransverseAt q.1 q.2).range_sup_eq_top)
    IsRegularPoint 𝓘(ℝ, Fin (finrank ℝ (EM × ES) + finrank ℝ EZ - finrank ℝ EN) → ℝ) IS
      (fun q : {p : (M × S) × Z // F p.1 = g p.2} ↦ q.1.1.2) p ↔
      IsTransverseAt IM IZ IN (fun x' ↦ F (x', p.1.1.2)) g p.1.1.1 p.1.2 := by
  let htr := fun q : (M × S) × Z ↦ (hFtrans.isTransverseAt q.1 q.2).range_sup_eq_top
  let := transverseFiberProductChartedSpace hn hF hg htr
  have := isManifold_transverseFiberProduct hn hF hg htr
  rcases p with ⟨⟨⟨x, s⟩, z⟩, hp⟩
  dsimp only at hp ⊢
  have hn0 : n ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one hn)
  have hval := ((isSmoothEmbedding_coe_transverseFiberProduct hn hF hg htr).contMDiff
    ⟨((x, s), z), hp⟩).mdifferentiableAt hn0
  have hFd : MDifferentiableAt (IM.prod IS) IN F (x, s) := (hF (x, s)).mdifferentiableAt hn0
  rw [isRegularPoint_iff, isTransverseAt_iff_forall]
  constructor
  · intro hreg _ v
    obtain ⟨z₀, w₀, hv⟩ :=
      isTransverseAt_iff_forall.1 (hFtrans.isTransverseAt (x, s) z) hp v
    let u₀ : TangentSpace IM x := z₀.1; let σ₀ : TangentSpace IS s := z₀.2
    obtain ⟨ξ, hξ⟩ := hreg σ₀
    set η := mfderiv 𝓘(ℝ, Fin (finrank ℝ (EM × ES) + finrank ℝ EZ - finrank ℝ EN) → ℝ)
      ((IM.prod IS).prod IZ) Subtype.val ⟨((x, s), z), hp⟩ ξ
    have hη2 : η.1.2 = σ₀ := by rwa [← hval.mfderiv_fst_apply, ← hval.fst.mfderiv_snd_apply]
    let u₁ : TangentSpace IM x := η.1.1; let z₁ : TangentSpace (IM.prod IS) (x, s) := η.1
    let z₂ : TangentSpace (IM.prod IS) (x, s) := (u₀ - u₁, (0 : TangentSpace IS s))
    let w₁ : TangentSpace IZ z := η.2
    have hηeq : mfderiv (IM.prod IS) IN F (x, s) z₁ =
        tangentSpaceCast IN (g z) (F (x, s)) (mfderiv IZ IN g z w₁) :=
      (mem_range_mfderiv_coe_transverseFiberProduct_iff hn hF hg htr
        ⟨((x, s), z), hp⟩ η).1 ⟨ξ, rfl⟩
    refine ⟨u₀ - u₁, w₀ + w₁, ?_⟩
    rw [mfderiv_slice_left_apply hFd (u₀ - u₁)]
    change mfderiv (IM.prod IS) IN F (x, s) z₂ + _ = v
    rw [show z₂ = z₀ - z₁ from Prod.ext rfl (sub_eq_zero.2 hη2.symm).symm,
      map_sub, map_add, map_add, hηeq, ← hv]
    abel
  · intro hslice σ
    let v₀ : TangentSpace (IM.prod IS) (x, s) := (0, σ)
    obtain ⟨u, w, huw⟩ := hslice hp (mfderiv (IM.prod IS) IN F (x, s) v₀)
    rw [mfderiv_slice_left_apply hFd] at huw
    let v₁ : TangentSpace (IM.prod IS) (x, s) := (-u, σ)
    let v₂ : TangentSpace (IM.prod IS) (x, s) := (u, 0)
    have heq : mfderiv (IM.prod IS) IN F (x, s) v₁ =
        tangentSpaceCast IN (g z) (F (x, s)) (mfderiv IZ IN g z w) := by
      rw [show v₁ = v₀ - v₂ from Prod.ext (zero_sub u).symm (sub_zero σ).symm, map_sub,
        ← show mfderiv (IM.prod IS) IN F (x, s) v₂ + _ = mfderiv (IM.prod IS) IN F (x, s) v₀
          from huw]
      abel
    obtain ⟨ξ, hξ₁, -⟩ := exists_mfderiv_eq_of_transverseFiberProduct hn hF hg htr
      ⟨((x, s), z), hp⟩ v₁ w heq
    exact ⟨ξ, by rw [hval.fst.mfderiv_snd_apply, hξ₁]⟩

/-- On the transverse fibre product `{((x, s), z) // F (x, s) = g z}`, a parameter `s : S` is a
regular value of the parameter projection `q ↦ q.1.1.2` if and only if the slice `x ↦ F (x, s)` is
globally transverse to `g`. -/
theorem isRegularValue_snd_transverseFiberProduct_iff (hn : 1 ≤ n)
    (hF : ContMDiff (IM.prod IS) IN n F) (hg : ContMDiff IZ IN n g)
    (hFtrans : IsTransverse (IM.prod IS) IZ IN F g) (s : S) :
    letI := transverseFiberProductChartedSpace hn hF hg
      (fun q ↦ (hFtrans.isTransverseAt q.1 q.2).range_sup_eq_top)
    IsRegularValue 𝓘(ℝ, Fin (finrank ℝ (EM × ES) + finrank ℝ EZ - finrank ℝ EN) → ℝ) IS
      (fun q : {p : (M × S) × Z // F p.1 = g p.2} ↦ q.1.1.2) s ↔
      IsTransverse IM IZ IN (fun x ↦ F (x, s)) g := by
  let := transverseFiberProductChartedSpace hn hF hg
    (fun q ↦ (hFtrans.isTransverseAt q.1 q.2).range_sup_eq_top)
  rw [isRegularValue_iff, isTransverse_def]
  constructor
  · intro hreg x z
    rw [isTransverseAt_def]
    intro hFxz
    exact ((isRegularPoint_snd_transverseFiberProduct_iff hn hF hg hFtrans
      ⟨((x, s), z), hFxz⟩).1 (hreg ⟨((x, s), z), hFxz⟩ rfl)).range_sup_eq_top hFxz
  · rintro htrans ⟨⟨⟨x, s'⟩, z⟩, hp⟩ (rfl : s' = s)
    exact (isRegularPoint_snd_transverseFiberProduct_iff hn hF hg hFtrans
      ⟨((x, s'), z), hp⟩).2 (htrans x z)

private theorem isNullSet_not_isTransverse_slice_of_secondCountable
    [SecondCountableTopology M] [SecondCountableTopology S] [SecondCountableTopology Z]
    [MeasurableSpace ES] [BorelSpace ES]
    (hF : ContMDiff (IM.prod IS) IN n F) (hg : ContMDiff IZ IN n g)
    (hFtrans : IsTransverse (IM.prod IS) IZ IN F g)
    (hk : ((finrank ℝ EM + finrank ℝ EZ - finrank ℝ EN + 1 : ℕ) : ℕ∞ω) ≤ n) :
    IsNullSet IS {s : S | ¬ IsTransverse IM IZ IN (fun x ↦ F (x, s)) g} := by
  have hn1 : 1 ≤ n := le_trans (by norm_cast; omega) hk
  let htr := fun q : (M × S) × Z ↦ (hFtrans.isTransverseAt q.1 q.2).range_sup_eq_top
  let := transverseFiberProductChartedSpace hn1 hF hg htr
  have := isManifold_transverseFiberProduct hn1 hF hg htr
  let πS : {p : (M × S) × Z // F p.1 = g p.2} → S := fun q ↦ q.1.1.2
  have hπS : ContMDiff
      𝓘(ℝ, Fin (finrank ℝ (EM × ES) + finrank ℝ EZ - finrank ℝ EN) → ℝ) IS n πS :=
    contMDiff_snd.comp (contMDiff_fst.comp
      (isSmoothEmbedding_coe_transverseFiberProduct hn1 hF hg htr).contMDiff)
  have hkW : ((finrank ℝ (Fin (finrank ℝ (EM × ES) + finrank ℝ EZ - finrank ℝ EN) → ℝ) -
      finrank ℝ ES + 1 : ℕ) : ℕ∞ω) ≤ n := by
    have hdim : finrank ℝ (Fin (finrank ℝ (EM × ES) + finrank ℝ EZ - finrank ℝ EN) → ℝ) -
        finrank ℝ ES + 1 = finrank ℝ EM + finrank ℝ EZ - finrank ℝ EN + 1 := by
      rw [Module.finrank_fin_fun, Module.finrank_prod]; omega
    rwa [hdim]
  refine (hπS.isNullSet_image_criticalPoints hkW).mono fun s hs ↦ ?_
  have hns := (isRegularValue_snd_transverseFiberProduct_iff hn1 hF hg hFtrans s).not.2 hs
  rw [isRegularValue_iff] at hns
  push Not at hns
  obtain ⟨p, rfl, hp⟩ := hns
  exact ⟨p, hp, rfl⟩

private theorem isNullSet_not_isTransverse_slice_of_modelBoundaryless
    [LindelofSpace M] [LindelofSpace Z] [MeasurableSpace ES] [BorelSpace ES]
    (hF : ContMDiff (IM.prod IS) IN n F) (hg : ContMDiff IZ IN n g)
    (hFtrans : IsTransverse (IM.prod IS) IZ IN F g)
    (hk : ((finrank ℝ EM + finrank ℝ EZ - finrank ℝ EN + 1 : ℕ) : ℕ∞ω) ≤ n) :
    IsNullSet IS {s : S | ¬ IsTransverse IM IZ IN (fun x ↦ F (x, s)) g} := by
  have hn1 : 1 ≤ n := le_trans (by norm_cast; omega) hk
  have hn0 : n ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one hn1)
  have : SecondCountableTopology HM := IM.secondCountableTopology
  have : SecondCountableTopology M := ChartedSpace.secondCountable_of_lindelof HM M
  have : SecondCountableTopology HZ := IZ.secondCountableTopology
  have : SecondCountableTopology Z := ChartedSpace.secondCountable_of_lindelof HZ Z
  have : SecondCountableTopology HS := IS.secondCountableTopology
  rw [isNullSet_iff]
  intro s₀ μ hμ
  let S₀ : Opens S := chartSource (H := HS) s₀
  let s₀' : S₀ := ⟨s₀, mem_chart_source HS s₀⟩
  have : SecondCountableTopology S₀ := (chartAt (H := HS) s₀).secondCountableTopology_source
  let F₀ : M × S₀ → N := fun q ↦ F (q.1, q.2)
  have hF₀ : ContMDiff (IM.prod IS) IN n F₀ :=
    hF.comp (contMDiff_fst.prodMk (contMDiff_subtype_val.comp contMDiff_snd))
  have hF₀trans : IsTransverse (IM.prod IS) IZ IN F₀ g :=
    isTransverse_def.2 fun ⟨x, s⟩ z ↦
      (isTransverseAt_prod_opens_right_iff ((hF (x, s)).mdifferentiableAt hn0)).2
        (hFtrans.isTransverseAt (x, s) z)
  have hnull₀ := isNullSet_not_isTransverse_slice_of_secondCountable hF₀ hg hF₀trans hk
  refine measure_mono_null ?_ (hnull₀.chartwise s₀' μ)
  rintro y ⟨s, ⟨hsbad, hssrc⟩, rfl⟩
  have hsS₀ : s ∈ (chartAt HS s₀).source := by simpa only [extChartAt_source] using hssrc
  exact ⟨⟨s, hsS₀⟩, ⟨hsbad, by simpa [s₀', S₀, Opens.chartAt_eq] using hsS₀⟩,
    by simp [s₀', S₀, extChartAt, Opens.chartAt_eq]⟩

end FiberProduct

section Boundaryless

variable {EM HM M : Type*} [NormedAddCommGroup EM] [NormedSpace ℝ EM] [FiniteDimensional ℝ EM]
  [TopologicalSpace HM] {IM : ModelWithCorners ℝ EM HM}
  [TopologicalSpace M] [ChartedSpace HM M] [BoundarylessManifold IM M] [LindelofSpace M]
  {ES HS S : Type*} [NormedAddCommGroup ES] [NormedSpace ℝ ES] [FiniteDimensional ℝ ES]
  [TopologicalSpace HS] {IS : ModelWithCorners ℝ ES HS}
  [TopologicalSpace S] [ChartedSpace HS S] [BoundarylessManifold IS S]
  {EZ HZ Z : Type*} [NormedAddCommGroup EZ] [NormedSpace ℝ EZ] [FiniteDimensional ℝ EZ]
  [TopologicalSpace HZ] {IZ : ModelWithCorners ℝ EZ HZ}
  [TopologicalSpace Z] [ChartedSpace HZ Z] [BoundarylessManifold IZ Z] [LindelofSpace Z]
  {EN HN N : Type*} [NormedAddCommGroup EN] [NormedSpace ℝ EN] [FiniteDimensional ℝ EN]
  [TopologicalSpace HN] {IN : ModelWithCorners ℝ EN HN}
  [TopologicalSpace N] [ChartedSpace HN N] [BoundarylessManifold IN N]
  {n : ℕ∞ω} [IsManifold IM n M] [IsManifold IS n S] [IsManifold IZ n Z] [IsManifold IN n N]
  {F : M × S → N} {g : Z → N}

/-- **Parametric transversality (nullity).** Let `M`, `S`, `Z`, `N` be boundaryless `C^n`
manifolds over finite-dimensional real spaces, with `M` and `Z` Lindelöf (their models with corners
need not be boundaryless, and no countability or separation is assumed on `S` or `N`). If
`F : M × S → N` and `g : Z → N` are `C^n`, `F` is transverse to `g`, and
`dim M + dim Z - dim N + 1 ≤ n` (in particular when `n = ∞`), then the parameters `s : S` at which
`x ↦ F (x, s)` fails to be transverse to `g` form a chartwise null set in `S`. -/
theorem isNullSet_not_isTransverse_slice [MeasurableSpace ES] [BorelSpace ES]
    (hF : ContMDiff (IM.prod IS) IN n F) (hg : ContMDiff IZ IN n g)
    (hFtrans : IsTransverse (IM.prod IS) IZ IN F g)
    (hk : ((finrank ℝ EM + finrank ℝ EZ - finrank ℝ EN + 1 : ℕ) : ℕ∞ω) ≤ n) :
    IsNullSet IS {s : S | ¬ IsTransverse IM IZ IN (fun x ↦ F (x, s)) g} := by
  have hn1 : 1 ≤ n := le_trans (by norm_cast; omega) hk
  have hn0 : n ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one hn1)
  have : IsManifold IM 1 M := .of_le hn1; have : IsManifold IS 1 S := .of_le hn1
  have : IsManifold IZ 1 Z := .of_le hn1; have : IsManifold IN 1 N := .of_le hn1
  let := BoundarylessModel.interiorChartedSpace IM (M := M)
  let := BoundarylessModel.interiorChartedSpace IS (M := S)
  let := BoundarylessModel.interiorChartedSpace IZ (M := Z)
  let := BoundarylessModel.interiorChartedSpace IN (M := N)
  have : LindelofSpace (BoundarylessModel IM M) := inferInstanceAs (LindelofSpace M)
  have : LindelofSpace (BoundarylessModel IZ Z) := inferInstanceAs (LindelofSpace Z)
  let φM := BoundarylessModel.interiorDiffeomorph IM (M := M) n
  let φS := BoundarylessModel.interiorDiffeomorph IS (M := S) n
  let φZ := BoundarylessModel.interiorDiffeomorph IZ (M := Z) n
  let φN := BoundarylessModel.interiorDiffeomorph IN (M := N) n
  have hF' : ContMDiff (𝓘(ℝ, EM).prod 𝓘(ℝ, ES)) 𝓘(ℝ, EN) n
      (φN ∘ F ∘ (φM.symm.prodCongr φS.symm)) :=
    φN.contMDiff.comp (hF.comp (φM.symm.prodCongr φS.symm).contMDiff)
  have hg' : ContMDiff 𝓘(ℝ, EZ) 𝓘(ℝ, EN) n (φN ∘ g ∘ φZ.symm) :=
    φN.contMDiff.comp (hg.comp φZ.symm.contMDiff)
  have hF'trans : IsTransverse (𝓘(ℝ, EM).prod 𝓘(ℝ, ES)) 𝓘(ℝ, EZ) 𝓘(ℝ, EN)
      (φN ∘ F ∘ (φM.symm.prodCongr φS.symm)) (φN ∘ g ∘ φZ.symm) := by
    rwa [isTransverse_diffeomorph_comp_iff φN hn0
      ((hF.comp (φM.symm.prodCongr φS.symm).contMDiff).mdifferentiable hn0)
      ((hg.comp φZ.symm.contMDiff).mdifferentiable hn0),
      isTransverse_comp_diffeomorph_left_iff (φM.symm.prodCongr φS.symm) hn0,
      isTransverse_comp_diffeomorph_right_iff φZ.symm hn0]
  have hnull' := isNullSet_not_isTransverse_slice_of_modelBoundaryless hF' hg' hF'trans hk
  rw [isNullSet_iff]
  intro s μ hμ
  have hchart := hnull'.chartwise (BoundarylessModel.homeomorph IS S s) μ
  rw [BoundarylessModel.interiorExtChartAt_eq IS, Homeomorph.symm_apply_apply] at hchart
  refine measure_mono_null ?_ hchart
  rintro _ ⟨t, ⟨ht, htsrc⟩, rfl⟩
  let t' : BoundarylessModel IS S := t
  refine ⟨t', ⟨fun hgood ↦ ht ?_, htsrc⟩, rfl⟩
  have ht_eq : φS.symm t' = t := by
    rw [show ⇑φS.symm = ⇑(BoundarylessModel.homeomorph IS S).symm from
      BoundarylessModel.coe_interiorDiffeomorph_symm IS n]
    exact BoundarylessModel.homeomorph_symm_apply IS S t'
  rw [← ht_eq]
  change IsTransverse 𝓘(ℝ, EM) 𝓘(ℝ, EZ) 𝓘(ℝ, EN)
    (φN ∘ ((fun x ↦ F (x, φS.symm t')) ∘ φM.symm)) (φN ∘ (g ∘ φZ.symm)) at hgood
  have hslice_diff : MDifferentiable 𝓘(ℝ, EM) IN ((fun x ↦ F (x, φS.symm t')) ∘ φM.symm) :=
    ((show ContMDiff IM IN n (fun x ↦ F (x, φS.symm t')) from
      hF.comp (contMDiff_id.prodMk contMDiff_const)).comp φM.symm.contMDiff).mdifferentiable hn0
  rwa [isTransverse_diffeomorph_comp_iff φN hn0 hslice_diff
    ((hg.comp φZ.symm.contMDiff).mdifferentiable hn0),
    isTransverse_comp_diffeomorph_left_iff φM.symm hn0,
    isTransverse_comp_diffeomorph_right_iff φZ.symm hn0] at hgood

/-- **Parametric transversality (density).** Under the hypotheses of
`TauCeti.isNullSet_not_isTransverse_slice`, the parameters `s : S` at which `x ↦ F (x, s)` is
transverse to `g` are dense in `S`. -/
theorem dense_isTransverse_slice
    (hF : ContMDiff (IM.prod IS) IN n F) (hg : ContMDiff IZ IN n g)
    (hFtrans : IsTransverse (IM.prod IS) IZ IN F g)
    (hk : ((finrank ℝ EM + finrank ℝ EZ - finrank ℝ EN + 1 : ℕ) : ℕ∞ω) ≤ n) :
    Dense {s : S | IsTransverse IM IZ IN (fun x ↦ F (x, s)) g} := by
  borelize ES
  simpa [compl_ofPred] using (isNullSet_not_isTransverse_slice hF hg hFtrans hk).dense_compl

end Boundaryless

section HalfSpace

variable {m : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace (m + 1)) M]
  [LindelofSpace M]
  {ES HS S : Type*} [NormedAddCommGroup ES] [NormedSpace ℝ ES] [FiniteDimensional ℝ ES]
  [TopologicalSpace HS] {IS : ModelWithCorners ℝ ES HS}
  [TopologicalSpace S] [ChartedSpace HS S] [BoundarylessManifold IS S]
  {EZ HZ Z : Type*} [NormedAddCommGroup EZ] [NormedSpace ℝ EZ] [FiniteDimensional ℝ EZ]
  [TopologicalSpace HZ] {IZ : ModelWithCorners ℝ EZ HZ}
  [TopologicalSpace Z] [ChartedSpace HZ Z] [BoundarylessManifold IZ Z] [LindelofSpace Z]
  {EN HN N : Type*} [NormedAddCommGroup EN] [NormedSpace ℝ EN] [FiniteDimensional ℝ EN]
  [TopologicalSpace HN] {IN : ModelWithCorners ℝ EN HN}
  [TopologicalSpace N] [ChartedSpace HN N] [BoundarylessManifold IN N]
  {n : ℕ∞ω} [IsManifold (𝓡∂ (m + 1)) 1 M] [IsManifold (𝓡∂ (m + 1)) n M]
  [IsManifold IS n S] [IsManifold IZ n Z] [IsManifold IN n N]
  {F : M × S → N} {g : Z → N}

/-- **Facewise parametric transversality on a half-space manifold (nullity).** Let `M` be a
Lindelöf `C^n` manifold with boundary modelled on `𝓡∂ (m + 1)`, and let `S`, `Z`, `N` be
boundaryless `C^n` manifolds with `Z` Lindelöf. Suppose `F : M × S → N` and `g : Z → N` are `C^n`
with `(m + 1) + dim Z - dim N + 1 ≤ n`, `F` is transverse to `g` along `interior M ×ˢ univ`, and
the boundary family `(p, s) ↦ F (p, s)` on `∂M × S` is transverse to `g`. Then the parameters
`s : S` at which either `x ↦ F (x, s)` fails ambient transversality on `M` or `(p : ∂M) ↦ F (p, s)`
fails boundary transversality on `∂M` form a chartwise null set in `S`. -/
theorem isNullSet_not_isTransverse_slice_halfSpace [MeasurableSpace ES] [BorelSpace ES]
    (hF : ContMDiff ((𝓡∂ (m + 1)).prod IS) IN n F) (hg : ContMDiff IZ IN n g)
    (hFint : IsTransverseOn ((𝓡∂ (m + 1)).prod IS) IZ IN F g (((𝓡∂ (m + 1)).interior M) ×ˢ univ))
    (hFbdy : IsTransverse (𝓘(ℝ, EuclideanSpace ℝ (Fin m)).prod IS) IZ IN
      (fun q : ↥((𝓡∂ (m + 1)).boundary M) × S ↦ F (q.1, q.2)) g)
    (hk : ((m + 1 + finrank ℝ EZ - finrank ℝ EN + 1 : ℕ) : ℕ∞ω) ≤ n) :
    IsNullSet IS {s : S | ¬ (IsTransverse (𝓡∂ (m + 1)) IZ IN (fun x ↦ F (x, s)) g ∧
      IsTransverse 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) IZ IN
        (fun p : ↥((𝓡∂ (m + 1)).boundary M) ↦ F (p, s)) g)} := by
  have hn1 : 1 ≤ n := le_trans (by norm_cast; omega) hk
  have hn0 : n ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one hn1)
  have : SecondCountableTopology (EuclideanHalfSpace (m + 1)) :=
    (𝓡∂ (m + 1)).secondCountableTopology
  have : SecondCountableTopology M :=
    ChartedSpace.secondCountable_of_lindelof (EuclideanHalfSpace (m + 1)) M
  have := isManifold_boundary (n := m) (k := n) M hn0
  -- Apply boundaryless parametric transversality on the open manifold interior `U_int`.
  let U_int : Opens M := ⟨(𝓡∂ (m + 1)).interior M, (𝓡∂ (m + 1)).isOpen_interior one_ne_zero⟩
  have : BoundarylessManifold (𝓡∂ (m + 1)) U_int :=
    ⟨fun x ↦ (𝓡∂ (m + 1)).isInteriorPoint_iff_isInteriorPoint_val.2 x.2⟩
  let F_int : U_int × S → N := fun q ↦ F (q.1, q.2)
  have hF_int : ContMDiff ((𝓡∂ (m + 1)).prod IS) IN n F_int :=
    hF.comp ((contMDiff_subtype_val.comp contMDiff_fst).prodMk contMDiff_snd)
  have hF_int_trans : IsTransverse ((𝓡∂ (m + 1)).prod IS) IZ IN F_int g :=
    isTransverse_def.2 fun ⟨x, s⟩ z ↦
      (isTransverseAt_prod_opens_left_iff ((hF (x, s)).mdifferentiableAt hn0)).2
        (hFint.isTransverseAt ⟨x.2, mem_univ s⟩ z)
  have hk_int : ((finrank ℝ (EuclideanSpace ℝ (Fin (m + 1))) + finrank ℝ EZ - finrank ℝ EN + 1 : ℕ)
      : ℕ∞ω) ≤ n := by
    simpa [finrank_euclideanSpace] using hk
  have hnull_int := isNullSet_not_isTransverse_slice hF_int hg hF_int_trans hk_int
  -- Apply boundaryless parametric transversality on the boundary manifold `∂M`.
  let F_bdy : ↥((𝓡∂ (m + 1)).boundary M) × S → N := fun q ↦ F (q.1, q.2)
  have hF_bdy : ContMDiff (𝓘(ℝ, EuclideanSpace ℝ (Fin m)).prod IS) IN n F_bdy :=
    hF.comp (((isSmoothEmbedding_subtypeVal_boundary (n := m) (k := n) M hn0).contMDiff.comp
      contMDiff_fst).prodMk contMDiff_snd)
  have hk_bdy : ((finrank ℝ (EuclideanSpace ℝ (Fin m)) + finrank ℝ EZ - finrank ℝ EN + 1 : ℕ) :
      ℕ∞ω) ≤ n := by
    refine le_trans ?_ hk
    norm_cast
    rw [finrank_euclideanSpace, Fintype.card_fin]
    omega
  have hnull_bdy := isNullSet_not_isTransverse_slice hF_bdy hg hFbdy hk_bdy
  refine (hnull_int.union hnull_bdy).mono fun s hs ↦ ?_
  rw [mem_union]
  by_contra hnot
  obtain ⟨h1, h2⟩ := not_or.1 hnot
  have hint_s : IsTransverseOn (𝓡∂ (m + 1)) IZ IN (fun x ↦ F (x, s)) g
      ((𝓡∂ (m + 1)).interior M) :=
    (isTransverse_comp_subtype_val_iff (U := U_int)).1 (not_not.1 h1)
  have hbdy_s : IsTransverse 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) IZ IN
      (fun p : ↥((𝓡∂ (m + 1)).boundary M) ↦ F (p, s)) g := not_not.1 h2
  have hFd_s : MDifferentiable (𝓡∂ (m + 1)) IN (fun x ↦ F (x, s)) :=
    (hF.comp (contMDiff_id.prodMk contMDiff_const)).mdifferentiable hn0
  exact hs ⟨IsTransverse.of_interior_and_boundary hFd_s hint_s hbdy_s, hbdy_s⟩

/-- **Facewise parametric transversality on a half-space manifold (density).** Under the hypotheses
of `TauCeti.isNullSet_not_isTransverse_slice_halfSpace`, the parameters `s : S` at which
`x ↦ F (x, s)` is transverse to `g` both ambiently on `M` and along `∂M` are dense in `S`. -/
theorem dense_isTransverse_slice_halfSpace
    (hF : ContMDiff ((𝓡∂ (m + 1)).prod IS) IN n F) (hg : ContMDiff IZ IN n g)
    (hFint : IsTransverseOn ((𝓡∂ (m + 1)).prod IS) IZ IN F g (((𝓡∂ (m + 1)).interior M) ×ˢ univ))
    (hFbdy : IsTransverse (𝓘(ℝ, EuclideanSpace ℝ (Fin m)).prod IS) IZ IN
      (fun q : ↥((𝓡∂ (m + 1)).boundary M) × S ↦ F (q.1, q.2)) g)
    (hk : ((m + 1 + finrank ℝ EZ - finrank ℝ EN + 1 : ℕ) : ℕ∞ω) ≤ n) :
    Dense {s : S | IsTransverse (𝓡∂ (m + 1)) IZ IN (fun x ↦ F (x, s)) g ∧
      IsTransverse 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) IZ IN
        (fun p : ↥((𝓡∂ (m + 1)).boundary M) ↦ F (p, s)) g} := by
  borelize ES
  simpa [compl_ofPred] using
    (isNullSet_not_isTransverse_slice_halfSpace hF hg hFint hFbdy hk).dense_compl

end HalfSpace

end TauCeti

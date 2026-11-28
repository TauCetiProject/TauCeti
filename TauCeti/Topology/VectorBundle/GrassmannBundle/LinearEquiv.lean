/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.VectorBundle.GrassmannBundle.Map
public import TauCeti.Topology.Grassmannian.LinearCongr
import TauCeti.Topology.VectorBundle.Hom

/-!
# Maps of Grassmann bundles induced by fibrewise linear equivalences

Let `E → B` and `E' → B'` be real vector bundles of finite rank whose fibres are real inner product
spaces, with Grassmann bundles `G_k(E)` and `G_k(E')` (`TauCeti.grassmannBundle`). A map
`f : B → B'` covered by continuous linear equivalences `L_x : E_x ≃L[ℝ] E'_{f x}`, not necessarily
isometric, carries a `k`-plane `S` of `E_x` to the `k`-plane `L_x S` of `E'_{f x}`. Recording planes
by their orthogonal projections, this is the map

`(x, P) ↦ (f x, P_{L_x (range P)})`

of Grassmann bundles (`TauCeti.grassmannBundle.mapLinearEquiv`), fibrewise the map
`ContinuousLinearEquiv.grassmannianMap` of Grassmannians. It is functorial
(`TauCeti.grassmannBundle.mapLinearEquiv_id`, `TauCeti.grassmannBundle.mapLinearEquiv_comp`),
and for fibrewise linear isometries it is the conjugation map `TauCeti.grassmannBundle.map`
(`TauCeti.grassmannBundle.mapLinearEquiv_toContinuousLinearEquiv`).

When `f` is continuous and `L` is continuous in the coordinates of the bundles, the map is
continuous (`TauCeti.grassmannBundle.continuous_mapLinearEquiv`). Read in the Gram–Schmidt charts
of `G_k(E)` and `G_k(E')` (`Bundle.Trivialization.grassmannBundle`), given by local orthonormal
frames `σ_x : V ≃ₗᵢ[ℝ] E_x` and `σ'_y : V' ≃ₗᵢ[ℝ] E'_y`, it is the image-plane map of the
operators `σ'_{f x}⁻¹ L_x σ_x : V → V'`, which depend continuously on `x`, so its continuity is
that of the image-plane map (`ContinuousAt.grassmannianMap`). Over a fixed base,
`L` and the fibrewise inverses `L_x⁻¹` therefore give a homeomorphism `G_k(E) ≃ₜ G_k(E')`
(`TauCeti.grassmannBundle.mapLinearEquivHomeomorph`). For two fibre metrics on one bundle, with
`L_x` the identity, this is the canonical homeomorphism between the Grassmann bundles of the two
metrics (`TauCeti.grassmannBundle.metricChangeHomeomorph` in
`TauCeti.Topology.VectorBundle.GrassmannBundle.MetricChange`).

## Main declarations

* `TauCeti.grassmannBundle.mapLinearEquiv`: the map `(x, P) ↦ (f x, P_{L_x (range P)})`.
* `TauCeti.grassmannBundle.continuous_mapLinearEquiv`: continuity.
* `TauCeti.grassmannBundle.mapLinearEquivHomeomorph`: the homeomorphism induced over a fixed base.

## References

* W. K. Allard, *On the first variation of a varifold*, Ann. of Math. (2) 95 (1972), 417–491,
  Section 3.
-/

public section

noncomputable section

open Bundle Filter Set Topology ContinuousLinearMap Module
open scoped InnerProductSpace

namespace TauCeti

namespace grassmannBundle

section Map

variable {B B' B'' F F' F'' : Type*} {E : B → Type*} {E' : B' → Type*} {E'' : B'' → Type*}
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup F'] [NormedSpace ℝ F']
  [NormedAddCommGroup F''] [NormedSpace ℝ F'']
  [∀ b, NormedAddCommGroup (E b)] [∀ b, InnerProductSpace ℝ (E b)]
  [∀ b, FiniteDimensional ℝ (E b)]
  [∀ b, NormedAddCommGroup (E' b)] [∀ b, InnerProductSpace ℝ (E' b)]
  [∀ b, FiniteDimensional ℝ (E' b)]
  [∀ b, NormedAddCommGroup (E'' b)] [∀ b, InnerProductSpace ℝ (E'' b)]
  [∀ b, FiniteDimensional ℝ (E'' b)] {k : ℕ}

/-- The map of Grassmann bundles `(x, P) ↦ (f x, P_{L_x (range P)})` induced by a map
`f : B → B'` of the bases covered by continuous linear equivalences `L_x : E_x ≃L[ℝ] E'_{f x}` of
the fibres: a plane `S` of `E_x`, recorded by its orthogonal projection, goes to the plane
`L_x S`, recorded by its orthogonal projection for the inner product of `E'_{f x}`. -/
def mapLinearEquiv (f : B → B') (L : ∀ x, E x ≃L[ℝ] E' (f x)) (p : grassmannBundle F E k) :
    grassmannBundle F' E' k :=
  ⟨⟨f p.val.proj, ((L p.val.proj).grassmannianMap k
      ⟨p.val.snd, mem_grassmannBundle.1 p.property⟩ : E' (f p.val.proj) →L[ℝ] E' (f p.val.proj))⟩,
    mem_grassmannBundle.2
      ((L p.val.proj).grassmannianMap k ⟨p.val.snd, mem_grassmannBundle.1 p.property⟩).property⟩

variable (f : B → B') (L : ∀ x, E x ≃L[ℝ] E' (f x))

theorem coe_mapLinearEquiv_apply (p : grassmannBundle F E k) :
    (mapLinearEquiv f L p : grassmannBundle F' E' k).val =
      ⟨f p.val.proj, ((L p.val.proj).grassmannianMap k
        ⟨p.val.snd, mem_grassmannBundle.1 p.property⟩ :
          E' (f p.val.proj) →L[ℝ] E' (f p.val.proj))⟩ :=
  (rfl)

/-- The induced map covers `f`. -/
@[simp]
theorem proj_mapLinearEquiv (p : grassmannBundle F E k) :
    proj (mapLinearEquiv f L p : grassmannBundle F' E' k) = f (proj p) := by
  rw [proj_apply, proj_apply, coe_mapLinearEquiv_apply]

/-- Over a point `b`, the induced map is the map of Grassmannians induced by `L_b`. -/
@[simp]
theorem mapLinearEquiv_fiberIncl [TopologicalSpace B] [TopologicalSpace B']
    [TopologicalSpace (TotalSpace F E)] [TopologicalSpace (TotalSpace F' E')]
    [FiberBundle F E] [VectorBundle ℝ F E] [FiberBundle F' E'] [VectorBundle ℝ F' E'] (b : B)
    (P : Euclidean.grassmannian ℝ (E b) k) :
    mapLinearEquiv f L (fiberIncl F E k b P) =
      fiberIncl F' E' k (f b) ((L b).grassmannianMap k P) := by
  have h : fiberIncl F E k b P = ⟨⟨b, P⟩, mem_grassmannBundle.2 P.property⟩ :=
    Subtype.ext (coe_fiberIncl_apply b P)
  rw [h]
  exact Subtype.ext (coe_fiberIncl_apply _ _).symm

/-- The identity of the base, covered by the identities of the fibres, induces the identity. -/
@[simp]
theorem mapLinearEquiv_id :
    (mapLinearEquiv id (fun x ↦ ContinuousLinearEquiv.refl ℝ (E x)) :
      grassmannBundle F E k → grassmannBundle F E k) = id := by
  funext ⟨⟨x, P⟩, hP⟩
  refine Subtype.ext ?_
  rw [coe_mapLinearEquiv_apply]
  exact TotalSpace.ext rfl (heq_of_eq (congrArg Subtype.val
    (ContinuousLinearEquiv.grassmannianMap_refl ⟨P, mem_grassmannBundle.1 hP⟩)))

/-- **Functoriality.** The map induced by a composite is the composite of the induced maps. -/
theorem mapLinearEquiv_comp (g : B' → B'') (L' : ∀ y, E' y ≃L[ℝ] E'' (g y)) :
    (mapLinearEquiv (g ∘ f) (fun x ↦ (L x).trans (L' (f x))) :
      grassmannBundle F E k → grassmannBundle F'' E'' k) =
      (mapLinearEquiv g L' : grassmannBundle F' E' k → grassmannBundle F'' E'' k) ∘
        mapLinearEquiv f L := by
  funext ⟨⟨x, P⟩, hP⟩
  refine Subtype.ext ?_
  simp only [Function.comp_apply, coe_mapLinearEquiv_apply]
  exact TotalSpace.ext rfl (heq_of_eq (congrArg Subtype.val
    ((L x).grassmannianMap_trans (L' (f x)) ⟨P, mem_grassmannBundle.1 hP⟩)))

/-- Over a fixed base, the map induced by the fibrewise inverses `L_x⁻¹` undoes the map induced
by `L`. -/
@[simp]
theorem mapLinearEquiv_symm_mapLinearEquiv {E₂ : B → Type*} [∀ b, NormedAddCommGroup (E₂ b)]
    [∀ b, InnerProductSpace ℝ (E₂ b)] [∀ b, FiniteDimensional ℝ (E₂ b)]
    (L : ∀ x, E x ≃L[ℝ] E₂ x) (p : grassmannBundle F E k) :
    mapLinearEquiv id (fun x ↦ (L x).symm) (mapLinearEquiv id L p : grassmannBundle F' E₂ k) =
      p := by
  obtain ⟨⟨x, P⟩, hP⟩ := p
  refine Subtype.ext ?_
  simp only [coe_mapLinearEquiv_apply]
  exact TotalSpace.ext rfl (heq_of_eq (congrArg Subtype.val
    ((L x).symm_grassmannianMap_grassmannianMap ⟨P, mem_grassmannBundle.1 hP⟩)))

/-- For fibrewise linear isometries, the induced map is the conjugation map
`TauCeti.grassmannBundle.map`: `P_{U_x (range P)} = U_x P U_x⁻¹`. -/
theorem mapLinearEquiv_toContinuousLinearEquiv (U : ∀ x, E x ≃ₗᵢ[ℝ] E' (f x)) :
    (mapLinearEquiv f (fun x ↦ (U x).toContinuousLinearEquiv) :
      grassmannBundle F E k → grassmannBundle F' E' k) = map f U := by
  funext ⟨⟨x, P⟩, hP⟩
  refine Subtype.ext ?_
  rw [coe_mapLinearEquiv_apply, coe_map_apply]
  exact TotalSpace.ext rfl (heq_of_eq ((congrArg Subtype.val
    ((U x).grassmannianMap_toContinuousLinearEquiv ⟨P, mem_grassmannBundle.1 hP⟩)).trans
      ((U x).coe_grassmannianCongr_apply _)))

/-- When every `L_x` multiplies inner products by the same constant `c²`, the induced
map is conjugation: `(x, P) ↦ (f x, L_x P L_x⁻¹)`, since `P_{L_x (range P)} = L_x P L_x⁻¹`. -/
theorem coe_mapLinearEquiv_of_inner_map_map {c : ℝ}
    (h : ∀ x u v, ⟪L x u, L x v⟫_ℝ = c ^ 2 * ⟪u, v⟫_ℝ) (p : grassmannBundle F E k) :
    (mapLinearEquiv f L p : grassmannBundle F' E' k).val =
      ⟨f p.val.proj, (L p.val.proj : E p.val.proj →L[ℝ] E' (f p.val.proj)) ∘L p.val.snd ∘L
        ((L p.val.proj).symm : E' (f p.val.proj) →L[ℝ] E p.val.proj)⟩ := by
  rw [coe_mapLinearEquiv_apply, ContinuousLinearEquiv.coe_grassmannianMap_of_inner_map_map _
    (h p.val.proj)]

end Map

section Continuity

variable {B B' F F' : Type*} {E : B → Type*} {E' : B' → Type*}
  [TopologicalSpace B] [TopologicalSpace B']
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup F'] [NormedSpace ℝ F']
  [TopologicalSpace (TotalSpace F E)] [TopologicalSpace (TotalSpace F' E')]
  [∀ b, NormedAddCommGroup (E b)] [∀ b, InnerProductSpace ℝ (E b)]
  [∀ b, FiniteDimensional ℝ (E b)]
  [∀ b, NormedAddCommGroup (E' b)] [∀ b, InnerProductSpace ℝ (E' b)]
  [∀ b, FiniteDimensional ℝ (E' b)]
  [FiberBundle F E] [VectorBundle ℝ F E] [FiberBundle F' E'] [VectorBundle ℝ F' E']
  [ContinuousFiberNorm F E] [ContinuousFiberNorm F' E'] {k : ℕ}
  {f : B → B'} {L : ∀ x, E x ≃L[ℝ] E' (f x)}

section Charts

variable [FiniteDimensional ℝ F] [FiniteDimensional ℝ F'] {V V' : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup V'] [InnerProductSpace ℝ V'] [FiniteDimensional ℝ V']
  (φ : Trivialization F (π F E)) [φ.IsLinear ℝ]
  (φ' : Trivialization F' (π F' E')) [φ'.IsLinear ℝ]
  {ι ι' : Type*} [Fintype ι] [LinearOrder ι] [LocallyFiniteOrderBot ι]
  [Fintype ι'] [LinearOrder ι'] [LocallyFiniteOrderBot ι']
  (c : Module.Basis ι ℝ F) (b : OrthonormalBasis ι ℝ V)
  (c' : Module.Basis ι' ℝ F') (b' : OrthonormalBasis ι' ℝ V')

/-- The fibre maps `L_x`, read in the local orthonormal frames of `φ` and `φ'`: the operators
`σ'_{f x}⁻¹ L_x σ_x : V → V'`. -/
private def frameRead (L : ∀ x, E x ≃L[ℝ] E' (f x)) (x : B) : V ≃L[ℝ] V' :=
  (φ.orthonormalFrameAt c b x).toContinuousLinearEquiv.trans
    ((L x).trans (φ'.orthonormalFrameAt c' b' (f x)).symm.toContinuousLinearEquiv)

/-- **The induced map in the Gram–Schmidt charts**: read in the charts of `G_k(E)` and `G_k(E')`
given by the local orthonormal frames of `φ` and `φ'`, the induced map is the image-plane map of
the operators `σ'_{f x}⁻¹ L_x σ_x`. -/
private theorem grassmannBundle_mapLinearEquiv (L : ∀ x, E x ≃L[ℝ] E' (f x))
    (p : grassmannBundle F E k) (hp : f (proj p) ∈ φ'.baseSet) :
    φ'.grassmannBundle c' b' k (mapLinearEquiv f L p) =
      (f p.val.proj, (frameRead φ φ' c b c' b' L p.val.proj).grassmannianMap k
        (φ.grassmannBundle c b k p).2) := by
  refine Prod.ext ?_ (Subtype.ext ?_)
  · rw [Trivialization.coe_fst' _
      (by rwa [Trivialization.grassmannBundle_baseSet, proj_mapLinearEquiv]),
      proj_mapLinearEquiv, proj_apply]
  have ht : (φ.grassmannBundle c b k p).2 =
      (φ.orthonormalFrameAt c b p.val.proj).symm.grassmannianCongr k
        ⟨p.val.snd, mem_grassmannBundle.1 p.property⟩ :=
    Subtype.ext (by
      rw [Trivialization.coe_grassmannBundle_apply_snd,
        LinearIsometryEquiv.coe_grassmannianCongr_apply])
  have hσ (U : V ≃ₗᵢ[ℝ] E p.val.proj) (Q : Euclidean.grassmannian ℝ (E p.val.proj) k) :
      U.grassmannianCongr k (U.symm.grassmannianCongr k Q) = Q := by
    rw [← LinearIsometryEquiv.grassmannianCongr_symm, Homeomorph.apply_symm_apply]
  rw [ht, frameRead, ContinuousLinearEquiv.grassmannianMap_trans,
    ContinuousLinearEquiv.grassmannianMap_trans,
    LinearIsometryEquiv.grassmannianMap_toContinuousLinearEquiv,
    LinearIsometryEquiv.grassmannianMap_toContinuousLinearEquiv, hσ,
    Trivialization.coe_grassmannBundle_apply_snd,
    LinearIsometryEquiv.coe_grassmannianCongr_apply, coe_mapLinearEquiv_apply]

omit [FiniteDimensional ℝ F] [∀ b, FiniteDimensional ℝ (E b)] [∀ b, FiniteDimensional ℝ (E' b)]
  [FiniteDimensional ℝ V'] in
/-- The operators `σ'_{f x}⁻¹ L_x σ_x` depend continuously on `x` at `x₀` when `f` is continuous,
`L` is continuous in coordinates at `x₀`, and `x₀`, `f x₀` lie in the base sets of the preferred
charts `φ`, `φ'` of `E`, `E'` there. -/
private theorem continuousAt_frameRead (hf : Continuous f) {L : ∀ x, E x ≃L[ℝ] E' (f x)} {x₀ : B}
    (hL : ContinuousAt (fun x ↦ inCoordinates F E F' E' x₀ x (f x₀) (f x)
      (L x : E x →L[ℝ] E' (f x))) x₀) :
    ContinuousAt (fun x ↦ (frameRead (trivializationAt F E x₀) (trivializationAt F' E' (f x₀))
      c b c' b' L x : V →L[ℝ] V')) x₀ := by
  let φ := trivializationAt F E x₀
  let φ' := trivializationAt F' E' (f x₀)
  have hx₀ : x₀ ∈ φ.baseSet := mem_baseSet_trivializationAt F E x₀
  have hfx₀ : f x₀ ∈ φ'.baseSet := mem_baseSet_trivializationAt F' E' (f x₀)
  have hA := (φ.continuousOn_continuousLinearMapAt_comp_orthonormalFrameAt c b φ).continuousAt
    ((φ.open_baseSet.inter φ.open_baseSet).mem_nhds ⟨hx₀, hx₀⟩)
  have hC := ((φ'.continuousOn_orthonormalFrameAt_symm_comp_symmL c' b' φ').continuousAt
    ((φ'.open_baseSet.inter φ'.open_baseSet).mem_nhds ⟨hfx₀, hfx₀⟩)).comp (f := f)
      hf.continuousAt
  refine (hC.clm_comp (hL.clm_comp hA)).congr ?_
  filter_upwards [φ.open_baseSet.mem_nhds hx₀,
    hf.continuousAt.preimage_mem_nhds (φ'.open_baseSet.mem_nhds hfx₀)] with x hx hfx
  refine ContinuousLinearMap.ext fun v ↦ ?_
  simp only [frameRead, inCoordinates, coe_comp, Function.comp_apply,
    ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.trans_apply]
  rw [Trivialization.symmL_continuousLinearMapAt _ hx,
    Trivialization.symmL_continuousLinearMapAt _ hfx]

end Charts

/-- **The induced map of Grassmann bundles is continuous** when `f` is continuous and the fibre
maps `L_x` are continuous in the coordinates of the bundles near each point. -/
theorem continuous_mapLinearEquiv (hf : Continuous f)
    (hL : ∀ x₀, ContinuousAt (fun x ↦ inCoordinates F E F' E' x₀ x (f x₀) (f x)
      (L x : E x →L[ℝ] E' (f x))) x₀) :
    Continuous (mapLinearEquiv f L : grassmannBundle F E k → grassmannBundle F' E' k) := by
  refine continuous_iff_continuousAt.2 fun p₀ ↦ ?_
  let x₀ := proj p₀
  -- The model fibres are finite-dimensional, being isomorphic to fibres of `E` and `E'`.
  have : FiniteDimensional ℝ F := (VectorBundle.continuousLinearEquivAt ℝ F E x₀).finiteDimensional
  have : FiniteDimensional ℝ F' :=
    (VectorBundle.continuousLinearEquivAt ℝ F' E' (f x₀)).finiteDimensional
  let φ := trivializationAt F E x₀
  let φ' := trivializationAt F' E' (f x₀)
  let b := EuclideanSpace.basisFun (Fin (finrank ℝ F)) ℝ
  let b' := EuclideanSpace.basisFun (Fin (finrank ℝ F')) ℝ
  let t := φ.grassmannBundle (Module.finBasis ℝ F) b k
  let t' := φ'.grassmannBundle (Module.finBasis ℝ F') b' k
  let M := frameRead φ φ' (Module.finBasis ℝ F) b (Module.finBasis ℝ F') b' L
  have hsrc : (mapLinearEquiv f L : grassmannBundle F E k → grassmannBundle F' E' k) ⁻¹'
      t'.source ∈ 𝓝 p₀ := by
    rw [t'.source_eq, Trivialization.grassmannBundle_baseSet, preimage_preimage]
    simp only [proj_mapLinearEquiv]
    exact (φ'.open_baseSet.preimage (hf.comp continuous_proj)).mem_nhds
      (mem_baseSet_trivializationAt F' E' (f x₀))
  rw [t'.toOpenPartialHomeomorph.continuousAt_iff_continuousAt_comp_left hsrc]
  -- In the Gram–Schmidt charts, the induced map is the image-plane map of `M`.
  refine ContinuousAt.congr (f := fun p : grassmannBundle F E k ↦
    (f p.val.proj, (M p.val.proj).grassmannianMap k (t p).2)) ?_ ?_
  rotate_left
  · filter_upwards [hsrc] with p hp
    refine (grassmannBundle_mapLinearEquiv φ φ' _ b _ b' L p ?_).symm
    rwa [mem_preimage, t'.mem_source, Trivialization.grassmannBundle_baseSet,
      proj_mapLinearEquiv] at hp
  have hπ : Continuous fun p : grassmannBundle F E k ↦ p.val.proj :=
    continuous_proj.congr proj_apply
  refine (hf.continuousAt.comp hπ.continuousAt).prodMk ?_
  exact ((continuousAt_frameRead _ b _ b' hf (hL x₀)).comp_of_eq hπ.continuousAt
    (proj_apply p₀).symm).grassmannianMap
    (continuous_snd.continuousAt.comp ((t.continuousAt (t.mem_source.2 (by
      rw [Trivialization.grassmannBundle_baseSet]
      exact mem_baseSet_trivializationAt F E x₀)))))

variable (k) in
/-- **The homeomorphism of Grassmann bundles induced by fibrewise linear equivalences** over a
fixed base, `(x, P) ↦ (x, P_{L_x (range P)})`, when `L` is continuous in the coordinates of the
bundles. Its inverse is induced by the inverses `L_x⁻¹`, which are continuous in coordinates
because `L` is. -/
def mapLinearEquivHomeomorph {E' : B → Type*} [TopologicalSpace (TotalSpace F' E')]
    [∀ b, NormedAddCommGroup (E' b)] [∀ b, InnerProductSpace ℝ (E' b)]
    [∀ b, FiniteDimensional ℝ (E' b)] [FiberBundle F' E'] [VectorBundle ℝ F' E']
    [ContinuousFiberNorm F' E'] (L : ∀ x, E x ≃L[ℝ] E' x)
    (hL : ∀ x₀, ContinuousAt (fun x ↦ inCoordinates F E F' E' x₀ x x₀ x
      (L x : E x →L[ℝ] E' x)) x₀) :
    grassmannBundle F E k ≃ₜ grassmannBundle F' E' k where
  toFun := mapLinearEquiv id L
  invFun := mapLinearEquiv id fun x ↦ (L x).symm
  left_inv := mapLinearEquiv_symm_mapLinearEquiv L
  right_inv p := by
    simpa only [ContinuousLinearEquiv.symm_symm] using
      mapLinearEquiv_symm_mapLinearEquiv (F' := F) (fun x ↦ (L x).symm) p
  continuous_toFun := continuous_mapLinearEquiv continuous_id hL
  continuous_invFun := by
    refine continuous_mapLinearEquiv continuous_id fun x₀ ↦ ?_
    -- The model fibre `F` is finite-dimensional, being isomorphic to the fibre over `x₀`.
    have : FiniteDimensional ℝ F :=
      (VectorBundle.continuousLinearEquivAt ℝ F E x₀).finiteDimensional
    have h := (hL x₀).inCoordinates_clm_inverse (b₁ := id) (b₂ := id)
      isInvertible_equiv
    simpa only [inverse_equiv, id_eq] using h

variable {E' : B → Type*} [TopologicalSpace (TotalSpace F' E')]
  [∀ b, NormedAddCommGroup (E' b)] [∀ b, InnerProductSpace ℝ (E' b)]
  [∀ b, FiniteDimensional ℝ (E' b)] [FiberBundle F' E'] [VectorBundle ℝ F' E']
  [ContinuousFiberNorm F' E'] (L : ∀ x, E x ≃L[ℝ] E' x)
  (hL : ∀ x₀, ContinuousAt (fun x ↦ inCoordinates F E F' E' x₀ x x₀ x
    (L x : E x →L[ℝ] E' x)) x₀)

@[simp]
theorem coe_mapLinearEquivHomeomorph :
    (mapLinearEquivHomeomorph k L hL : grassmannBundle F E k → grassmannBundle F' E' k) =
      mapLinearEquiv id L :=
  (rfl)

@[simp]
theorem coe_mapLinearEquivHomeomorph_symm :
    ((mapLinearEquivHomeomorph k L hL).symm : grassmannBundle F' E' k → grassmannBundle F E k) =
      mapLinearEquiv id fun x ↦ (L x).symm :=
  (rfl)

end Continuity

end grassmannBundle

end TauCeti

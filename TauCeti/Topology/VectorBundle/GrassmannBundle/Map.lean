/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.VectorBundle.GrassmannBundle.Basic
import TauCeti.Topology.VectorBundle.Hom
import TauCeti.Topology.FiberBundle.Separation

/-!
# Maps of Grassmann bundles induced by fibrewise linear isometries

Let `E → B` and `E' → B'` be real vector bundles whose fibres are real inner product spaces, with
Grassmann bundles `G_k(E)` and `G_k(E')` (`TauCeti.grassmannBundle`), whose points are pairs
`(x, P)` of a base point and an orthogonal projection of rank `k` of the fibre. A map `f : B → B'`
covered by linear isometry equivalences `U_x : E_x ≃ₗᵢ[ℝ] E'_{f x}` induces the map

`(x, P) ↦ (f x, U_x P U_x⁻¹)`

of Grassmann bundles (`TauCeti.grassmannBundle.map`). Over each point it is the homeomorphism
`LinearIsometryEquiv.grassmannianCongr` of the Grassmannians of the fibres
(`TauCeti.grassmannBundle.map_fiberIncl`), and it is functorial: the identity covered by identities
induces the identity (`TauCeti.grassmannBundle.map_id`), and composites induce composites
(`TauCeti.grassmannBundle.map_comp`).

When `f` is continuous and `U` is continuous in the coordinates of the bundles, that is,
`x ↦ e'_{f x} ∘ U_x ∘ e_x⁻¹` is continuous at each point for the local trivializations `e`, `e'`
there (`ContinuousLinearMap.inCoordinates`), the map is continuous
(`TauCeti.grassmannBundle.continuous_map`): in coordinates it is the product
`(e' U e⁻¹) (e P e⁻¹) (e U⁻¹ e'⁻¹)` of continuous families of operators, the inverses being
continuous in coordinates because `U` is. When moreover `f` is a homeomorphism, `B'` is Hausdorff
and `E` has finite rank and continuous fibre norm, the map is a homeomorphism `G_k(E) ≃ₜ G_k(E')`
(`TauCeti.grassmannBundle.mapHomeomorph`): it is a continuous bijection, and it is proper since its
composite with the continuous projection of `G_k(E')` is `f ∘ π`, proper because `f` is a
homeomorphism and the projection `π` of `G_k(E)` is proper.

For the tangent bundles of Riemannian manifolds and an isometry `f`, `U_x` is the differential
`df_x`, a linear isometry `T_xM ≃ₗᵢ[ℝ] T_{f x}M'`, and the map is
`(x, P) ↦ (f(x), df_x P df_x⁻¹)`.

## Main declarations

* `TauCeti.grassmannBundle.map`: the map `(x, P) ↦ (f x, U_x P U_x⁻¹)`.
* `TauCeti.grassmannBundle.map_id`, `TauCeti.grassmannBundle.map_comp`: functoriality.
* `TauCeti.grassmannBundle.continuous_map`: continuity.
* `TauCeti.grassmannBundle.mapHomeomorph`: the homeomorphism induced by a homeomorphism of the
  bases covered by fibrewise linear isometries.

## References

* L. Simon, *Lectures on Geometric Measure Theory*, Proceedings of the Centre for Mathematical
  Analysis, Australian National University 3, 1983, §38.
-/

public section

noncomputable section

open Bundle Filter Set Topology ContinuousLinearMap

namespace TauCeti

namespace grassmannBundle

section Map

variable {B B' B'' F F' F'' : Type*} {E : B → Type*} {E' : B' → Type*} {E'' : B'' → Type*}
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup F'] [NormedSpace ℝ F']
  [NormedAddCommGroup F''] [NormedSpace ℝ F'']
  [∀ b, NormedAddCommGroup (E b)] [∀ b, InnerProductSpace ℝ (E b)] [∀ b, CompleteSpace (E b)]
  [∀ b, NormedAddCommGroup (E' b)] [∀ b, InnerProductSpace ℝ (E' b)] [∀ b, CompleteSpace (E' b)]
  [∀ b, NormedAddCommGroup (E'' b)] [∀ b, InnerProductSpace ℝ (E'' b)]
  [∀ b, CompleteSpace (E'' b)] {k : ℕ}

/-- The map of Grassmann bundles `(x, P) ↦ (f x, U_x P U_x⁻¹)` induced by a map `f : B → B'` of
the bases covered by linear isometry equivalences `U_x : E_x ≃ₗᵢ[ℝ] E'_{f x}` of the fibres. -/
def map (f : B → B') (U : ∀ x, E x ≃ₗᵢ[ℝ] E' (f x)) (p : grassmannBundle F E k) :
    grassmannBundle F' E' k :=
  ⟨⟨f p.val.proj, (U p.val.proj).conjStarAlgEquiv p.val.snd⟩,
    mem_grassmannBundle.2 ((U p.val.proj).conjStarAlgEquiv_mem_grassmannian
      (mem_grassmannBundle.1 p.property))⟩

variable (f : B → B') (U : ∀ x, E x ≃ₗᵢ[ℝ] E' (f x))

@[simp]
theorem coe_map_apply (p : grassmannBundle F E k) :
    (map f U p : grassmannBundle F' E' k).val =
      ⟨f p.val.proj, (U p.val.proj).conjStarAlgEquiv p.val.snd⟩ :=
  (rfl)

/-- The induced map covers `f`. -/
@[simp]
theorem proj_map (p : grassmannBundle F E k) :
    proj (map f U p : grassmannBundle F' E' k) = f (proj p) := by
  rw [proj_apply, proj_apply, coe_map_apply]

/-- The identity of the base, covered by the identities of the fibres, induces the identity. -/
@[simp]
theorem map_id :
    (map id (fun x ↦ LinearIsometryEquiv.refl ℝ (E x)) :
      grassmannBundle F E k → grassmannBundle F E k) = id :=
  funext fun _ ↦ rfl

/-- **Functoriality.** The map induced by a composite is the composite of the induced maps. -/
theorem map_comp (g : B' → B'') (U' : ∀ y, E' y ≃ₗᵢ[ℝ] E'' (g y)) :
    (map (g ∘ f) (fun x ↦ (U x).trans (U' (f x))) :
      grassmannBundle F E k → grassmannBundle F'' E'' k) =
      (map g U' : grassmannBundle F' E' k → grassmannBundle F'' E'' k) ∘ map f U :=
  funext fun _ ↦ rfl

/-- The induced map is injective when `f` is. -/
theorem map_injective (hf : Function.Injective f) :
    Function.Injective (map f U : grassmannBundle F E k → grassmannBundle F' E' k) := by
  rintro ⟨⟨x, P⟩, hP⟩ ⟨⟨y, Q⟩, hQ⟩ h
  have h' := congrArg Subtype.val h
  rw [coe_map_apply, coe_map_apply] at h'
  dsimp only at h'
  have hxy : x = y := hf (congrArg TotalSpace.proj h')
  subst hxy
  exact Subtype.ext (TotalSpace.ext rfl
    (heq_of_eq ((U x).conjStarAlgEquiv.injective (eq_of_heq (TotalSpace.mk.inj h').2))))

/-- The induced map is surjective when `f` is. -/
theorem map_surjective (hf : Function.Surjective f) :
    Function.Surjective (map f U : grassmannBundle F E k → grassmannBundle F' E' k) := by
  rintro ⟨⟨y, Q⟩, hQ⟩
  obtain ⟨x, rfl⟩ := hf y
  refine ⟨⟨⟨x, (U x).conjStarAlgEquiv.symm Q⟩, mem_grassmannBundle.2
    ((U x).symm.conjStarAlgEquiv_mem_grassmannian (mem_grassmannBundle.1 hQ))⟩,
    Subtype.ext ?_⟩
  rw [coe_map_apply]
  exact TotalSpace.ext rfl (heq_of_eq ((U x).conjStarAlgEquiv.apply_symm_apply Q))

end Map

section Continuity

variable {B B' F F' : Type*} {E : B → Type*} {E' : B' → Type*}
  [TopologicalSpace B] [TopologicalSpace B']
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup F'] [NormedSpace ℝ F']
  [TopologicalSpace (TotalSpace F E)] [TopologicalSpace (TotalSpace F' E')]
  [∀ b, NormedAddCommGroup (E b)] [∀ b, InnerProductSpace ℝ (E b)] [∀ b, CompleteSpace (E b)]
  [∀ b, NormedAddCommGroup (E' b)] [∀ b, InnerProductSpace ℝ (E' b)] [∀ b, CompleteSpace (E' b)]
  [FiberBundle F E] [VectorBundle ℝ F E] [FiberBundle F' E'] [VectorBundle ℝ F' E'] {k : ℕ}
  {f : B → B'} {U : ∀ x, E x ≃ₗᵢ[ℝ] E' (f x)}

/-- Over a point `b`, the induced map is the homeomorphism of Grassmannians given by conjugation
by `U_b`. -/
@[simp]
theorem map_fiberIncl (b : B) (P : Euclidean.grassmannian ℝ (E b) k) :
    map f U (fiberIncl F E k b P) = fiberIncl F' E' k (f b) ((U b).grassmannianCongr k P) :=
  Subtype.ext (by
    rw [coe_map_apply, coe_fiberIncl_apply, coe_fiberIncl_apply,
      LinearIsometryEquiv.coe_grassmannianCongr_apply])

/-- **The induced map of Grassmann bundles is continuous** when `f` is continuous and the fibre
maps `U_x` are continuous in the coordinates of the bundles near each point. -/
theorem continuous_map (hf : Continuous f)
    (hU : ∀ x₀, ContinuousAt (fun x ↦ inCoordinates F E F' E' x₀ x (f x₀) (f x)
      ((U x).toContinuousLinearEquiv : E x →L[ℝ] E' (f x))) x₀) :
    Continuous (map f U : grassmannBundle F E k → grassmannBundle F' E' k) := by
  refine continuous_induced_rng.2 (continuous_iff_continuousAt.2 fun p₀ ↦ ?_)
  rw [Function.comp_def, continuousAt_hom_bundle]
  have hπ : Continuous fun p : grassmannBundle F E k ↦ p.val.proj :=
    continuous_proj.congr proj_apply
  refine ⟨by simp only [coe_map_apply]; exact (hf.comp hπ).continuousAt, ?_⟩
  -- The coordinates of the projection `P` itself vary continuously.
  have hP : ContinuousAt (fun p : grassmannBundle F E k ↦
      inCoordinates F E F E p₀.val.proj p.val.proj p₀.val.proj p.val.proj p.val.snd) p₀ :=
    ((continuousAt_hom_bundle (f := fun p : grassmannBundle F E k ↦ p.val)).1
      continuous_subtypeVal.continuousAt).2
  have h₁ := (hU p₀.val.proj).comp (f := fun p : grassmannBundle F E k ↦ p.val.proj)
    hπ.continuousAt
  -- The model fibre `F` is complete, being isomorphic to the fibre over `p₀`.
  have : CompleteSpace F :=
    let L := (trivializationAt F E p₀.val.proj).continuousLinearEquivAt ℝ p₀.val.proj
      (mem_baseSet_trivializationAt F E p₀.val.proj)
    (completeSpace_congr (e := L.toEquiv) L.isUniformEmbedding).1 inferInstance
  -- Continuity of `U⁻¹` in coordinates follows from that of `U`.
  have hU' := (hU p₀.val.proj).inCoordinates_clm_inverse (b₁ := id) isInvertible_equiv
  simp only [inverse_equiv, ← LinearIsometryEquiv.toContinuousLinearEquiv_symm] at hU'
  have h₃ := hU'.comp (f := fun p : grassmannBundle F E k ↦ p.val.proj) hπ.continuousAt
  -- In coordinates the fibre of the map is the composite `(e' U e⁻¹) (e P e⁻¹) (e U⁻¹ e'⁻¹)`.
  have h₂₃ := ContinuousAt.inCoordinates_clm_comp (V := E') (W := E) (U := E)
    (b₁ := fun p : grassmannBundle F E k ↦ f p.val.proj) (b₂ := fun p ↦ p.val.proj)
    (b₃ := fun p ↦ p.val.proj) hP h₃ hπ.continuousAt
  have h₁₂₃ := ContinuousAt.inCoordinates_clm_comp (V := E') (W := E) (U := E')
    (b₁ := fun p : grassmannBundle F E k ↦ f p.val.proj) (b₂ := fun p ↦ p.val.proj)
    (b₃ := fun p ↦ f p.val.proj) h₁ h₂₃ hπ.continuousAt
  refine h₁₂₃.congr (.of_forall fun p ↦ ?_)
  dsimp only
  rw [coe_map_apply f U p, coe_map_apply f U p₀]
  dsimp only
  rw [LinearIsometryEquiv.conjStarAlgEquiv_apply]

variable (k) in
/-- **The homeomorphism of Grassmann bundles induced by a homeomorphism of the bases** covered by
linear isometry equivalences of the fibres that are continuous in coordinates:
`(x, P) ↦ (f x, U_x P U_x⁻¹)`. -/
def mapHomeomorph [T2Space B'] [FiniteDimensional ℝ F] [ContinuousFiberNorm F E] (f : B ≃ₜ B')
    (U : ∀ x, E x ≃ₗᵢ[ℝ] E' (f x))
    (hU : ∀ x₀, ContinuousAt (fun x ↦ inCoordinates F E F' E' x₀ x (f x₀) (f x)
      ((U x).toContinuousLinearEquiv : E x →L[ℝ] E' (f x))) x₀) :
    grassmannBundle F E k ≃ₜ grassmannBundle F' E' k :=
  have hc : Continuous (map f U : grassmannBundle F E k → grassmannBundle F' E' k) :=
    continuous_map f.continuous hU
  -- The composite with the projection of `G_k(E')` is the proper map `f ∘ π`.
  have hp : IsProperMap (map f U : grassmannBundle F E k → grassmannBundle F' E' k) :=
    isProperMap_of_comp_of_t2 hc continuous_proj (by
      rw [show (proj ∘ map f U : grassmannBundle F E k → B') = f ∘ proj from
        funext (proj_map f U)]
      exact f.isProperMap.comp (isProperMap_proj F E k))
  (Equiv.ofBijective _ ⟨map_injective f U f.injective, map_surjective f U f.surjective⟩)
    |>.toHomeomorphOfContinuousClosed hc hp.isClosedMap

@[simp]
theorem coe_mapHomeomorph [T2Space B'] [FiniteDimensional ℝ F] [ContinuousFiberNorm F E]
    (f : B ≃ₜ B') (U : ∀ x, E x ≃ₗᵢ[ℝ] E' (f x))
    (hU : ∀ x₀, ContinuousAt (fun x ↦ inCoordinates F E F' E' x₀ x (f x₀) (f x)
      ((U x).toContinuousLinearEquiv : E x →L[ℝ] E' (f x))) x₀) :
    (mapHomeomorph k f U hU : grassmannBundle F E k → grassmannBundle F' E' k) = map f U :=
  (rfl)

end Continuity

end grassmannBundle

end TauCeti

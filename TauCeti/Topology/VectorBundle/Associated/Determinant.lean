/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.VectorBundle.Associated.Basic
public import TauCeti.Topology.VectorBundle.Determinant
public import TauCeti.Topology.VectorBundle.Hom

/-!
# Determinant lines of associated vector bundles

Let `P` be a principal `G`-bundle and let `G` act linearly on finite-dimensional normed spaces
`F` and `F'`, with `F` of dimension `n`. An alternating map `η : Fⁿ → F'` that is equivariant,
`η (g • v₀, …, g • vₙ₋₁) = g • η v`, descends to the fibres of the associated bundles
(`TauCeti.AssociatedBundle.alternatingMap`), and so induces on each fibre a linear map from the
top exterior power `⋀ⁿ (P ×_G F)_x`, the fibre of the determinant line `det (P ×_G F)`
(`TauCeti.DetBundle`), to the fibre `(P ×_G F')_x`
(`TauCeti.AssociatedBundle.detMap`). In every principal frame `p` it reads

`[p, v₀] ∧ ⋯ ∧ [p, vₙ₋₁] ↦ [p, η v]`

(`TauCeti.AssociatedBundle.detMap_ιMulti_mk`).

These fibre maps form a continuous bundle map of total spaces
(`TauCeti.AssociatedBundle.continuous_detMap`): in the charts of `det (P ×_G F)` and of
`P ×_G F'` induced by a local trivialization of `P`, the fibre map is multiplication by the fixed
vector `η (b₀, …, bₙ₋₁)` of `F'`, where `b` is the basis of `F` used to coordinatize determinant
lines (`TauCeti.AssociatedBundle.trivializationAt_detMap_snd`). When `F'` is a line and
`η ≠ 0` the fibre maps are isomorphisms (`TauCeti.AssociatedBundle.detMap_bijective`), and they
form an isomorphism of line bundles `det (P ×_G F) ≃ P ×_G F'`, a homeomorphism of total spaces
that is linear on each fibre (`TauCeti.AssociatedBundle.detHomeomorph`).

The main example is the determinant line of a spinor bundle: for a principal `Spinᶜ(4)`-bundle, the
half-spin representations have determinant the character `[s, z] ↦ z²`, so a nonzero alternating
two-form on a half-spinor space identifies the determinant line of the spinor bundle `W^±` with
the determinant line `L` of the `Spinᶜ` structure (`Orientation.spinorDetHomeomorph`).

## References

* I. Kolář, P. W. Michor, J. Slovák, *Natural Operations in Differential Geometry*, Springer,
  1993, §10.7.
* J. W. Milnor, J. D. Stasheff, *Characteristic Classes*, Annals of Mathematics Studies 76,
  Princeton (1974), §3.
-/

public section

noncomputable section

open Bundle Module Set Topology

namespace TauCeti.AssociatedBundle

variable {𝕜 B G F F' : Type*} [NontriviallyNormedField 𝕜]
  [TopologicalSpace B] [Group G] [TopologicalSpace G]
  {P : B → Type*} [TopologicalSpace (TotalSpace G P)] [∀ b, TopologicalSpace (P b)]
  [FiberBundle G P] [∀ b, MulAction Gᵐᵒᵖ (P b)] [PrincipalBundle G P]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [DistribMulAction G F] [SMulCommClass G 𝕜 F] [ContinuousSMul G F]
  [NormedAddCommGroup F'] [NormedSpace 𝕜 F']
  [DistribMulAction G F'] [SMulCommClass G 𝕜 F'] [ContinuousSMul G F']
  {n : ℕ}

variable (G P) in
/-- The linear map from the fibre over `x` of the determinant line `det (P ×_G F)` to the fibre
of `P ×_G F'` induced by an alternating map `η` of `n = dim F` arguments: the linear map on
`⋀ⁿ (P ×_G F)_x` induced by the descended alternating map
`TauCeti.AssociatedBundle.alternatingMap G P η x`. For equivariant `η` it reads
`[p, v₀] ∧ ⋯ ∧ [p, vₙ₋₁] ↦ [p, η v]` in every principal frame `p`
(`TauCeti.AssociatedBundle.detMap_ιMulti_mk`). -/
def detMap (hn : finrank 𝕜 F = n) (η : F [⋀^Fin n]→ₗ[𝕜] F') (x : B) :
    DetBundle 𝕜 F (AssociatedBundle G P F) x →ₗ[𝕜] AssociatedBundle G P F' x :=
  exteriorPower.alternatingMapLinearEquiv (alternatingMap G P η x) ∘ₗ
    ((LinearEquiv.ofEq _ _ (congrArg (⋀[𝕜]^· (AssociatedBundle G P F x)) hn)).toLinearMap ∘ₗ
      (DetBundle.linearEquiv 𝕜 F (AssociatedBundle G P F) x).toLinearMap)

/-- `TauCeti.AssociatedBundle.detMap` is the linear map induced on the top exterior power of the
fibre by the descended alternating map. -/
theorem detMap_apply (hn : finrank 𝕜 F = n) (η : F [⋀^Fin n]→ₗ[𝕜] F') (x : B)
    (w : DetBundle 𝕜 F (AssociatedBundle G P F) x) :
    detMap G P hn η x w =
      exteriorPower.alternatingMapLinearEquiv (alternatingMap G P η x)
        (LinearEquiv.ofEq _ _ (congrArg (⋀[𝕜]^· (AssociatedBundle G P F x)) hn)
          (DetBundle.linearEquiv 𝕜 F (AssociatedBundle G P F) x w)) :=
  (rfl)

/-- **The determinant map in a principal frame.** For an equivariant `η`, in every frame `p` of
`P` over `x`, `TauCeti.AssociatedBundle.detMap` sends `[p, v₀] ∧ ⋯ ∧ [p, vₙ₋₁]` to `[p, η v]`. -/
@[simp]
theorem detMap_ιMulti_mk (hn : finrank 𝕜 F = n) {η : F [⋀^Fin n]→ₗ[𝕜] F'}
    (hη : ∀ (g : G) (v : Fin n → F), η (fun i ↦ g • v i) = g • η v) {x : B} (p : P x)
    (v : Fin n → F) :
    detMap G P hn η x
        (exteriorPower.ιMulti 𝕜 (finrank 𝕜 F) fun i ↦ mk G p (v (Fin.cast hn i))) =
      mk G p (η v) := by
  -- The statement uses the raw `ιMulti` element, the normal form under
  -- `TauCeti.DetBundle.linearEquiv_symm_apply`; the proof passes through
  -- `(DetBundle.linearEquiv 𝕜 F _ x).symm` to unfold `detMap`.
  refine (detMap_apply hn η x ((DetBundle.linearEquiv 𝕜 F (AssociatedBundle G P F) x).symm
    (exteriorPower.ιMulti 𝕜 _ fun i ↦ mk G p (v (Fin.cast hn i))))).trans ?_
  rw [LinearEquiv.apply_symm_apply, exteriorPower.ofEq_ιMulti hn,
    exteriorPower.alternatingMapLinearEquiv_apply_ιMulti]
  simpa only [Function.comp_def, Fin.cast_cast, Fin.cast_eq_self] using
    alternatingMap_mk hη p v

/-- **The determinant map is an isomorphism onto a line.** If `F'` is a line and `η ≠ 0`, each
fibre map `TauCeti.AssociatedBundle.detMap` is bijective. -/
theorem detMap_bijective (hn : finrank 𝕜 F = n) (hF' : finrank 𝕜 F' = 1)
    {η : F [⋀^Fin n]→ₗ[𝕜] F'} (hη : η ≠ 0) (x : B) :
    Function.Bijective (detMap G P hn η x) := by
  have h := TauCeti.exteriorPower.alternatingMapLinearEquiv_bijective
    ((finrank_eq 𝕜 G F P x).trans hn) ((finrank_eq 𝕜 G F' P x).trans hF')
    ((alternatingMap_eq_zero_iff x).not.2 hη)
  exact h.comp ((LinearEquiv.ofEq _ _ (congrArg (⋀[𝕜]^· (AssociatedBundle G P F x)) hn)).bijective
    |>.comp (DetBundle.linearEquiv 𝕜 F _ x).bijective)

variable (G P) in
/-- **The determinant line isomorphism on a fibre.** If `F'` is a line and `η ≠ 0`, the fibre map
`TauCeti.AssociatedBundle.detMap` is a linear isomorphism `det (P ×_G F)_x ≃ (P ×_G F')_x`
(`TauCeti.AssociatedBundle.detMap_bijective`). -/
def detEquiv (hn : finrank 𝕜 F = n) (hF' : finrank 𝕜 F' = 1) {η : F [⋀^Fin n]→ₗ[𝕜] F'}
    (hη₀ : η ≠ 0) (x : B) :
    DetBundle 𝕜 F (AssociatedBundle G P F) x ≃ₗ[𝕜] AssociatedBundle G P F' x :=
  LinearEquiv.ofBijective (detMap G P hn η x) (detMap_bijective hn hF' hη₀ x)

/-- `TauCeti.AssociatedBundle.detEquiv` is the determinant map on each fibre. -/
@[simp]
theorem detEquiv_apply (hn : finrank 𝕜 F = n) (hF' : finrank 𝕜 F' = 1)
    {η : F [⋀^Fin n]→ₗ[𝕜] F'} (hη₀ : η ≠ 0) (x : B)
    (w : DetBundle 𝕜 F (AssociatedBundle G P F) x) :
    detEquiv G P hn hF' hη₀ x w = detMap G P hn η x w :=
  (rfl)

/-- **The inverse determinant line isomorphism in a principal frame.** For an equivariant `η`, in
every frame `p` of `P` over `x`, the inverse of `TauCeti.AssociatedBundle.detEquiv` sends `[p, η v]`
to `[p, v₀] ∧ ⋯ ∧ [p, vₙ₋₁]`. -/
@[simp]
theorem detEquiv_symm_mk (hn : finrank 𝕜 F = n) (hF' : finrank 𝕜 F' = 1)
    {η : F [⋀^Fin n]→ₗ[𝕜] F'} (hη : ∀ (g : G) (v : Fin n → F), η (fun i ↦ g • v i) = g • η v)
    (hη₀ : η ≠ 0) {x : B} (p : P x) (v : Fin n → F) :
    (detEquiv G P hn hF' hη₀ x).symm (mk G p (η v)) =
      exteriorPower.ιMulti 𝕜 (finrank 𝕜 F) fun i ↦ mk G p (v (Fin.cast hn i)) :=
  (LinearEquiv.symm_apply_eq _).2 (detMap_ιMulti_mk hn hη p v).symm

/-! ### Continuity -/

variable [CompleteSpace 𝕜] [FiniteDimensional 𝕜 F]

/-- **The determinant map in the charts at `a`.** Over the base set of the preferred chart of `P`
at `a`, the chart coordinate of the image of `w` is the chart coordinate of `w` times the fixed
vector `η (b₀, …, bₙ₋₁)`, where `b` is the basis `Module.finBasis 𝕜 F` coordinatizing the
determinant line. -/
theorem trivializationAt_detMap_snd (hn : finrank 𝕜 F = n) {η : F [⋀^Fin n]→ₗ[𝕜] F'}
    (hη : ∀ (g : G) (v : Fin n → F), η (fun i ↦ g • v i) = g • η v) {a x : B}
    (hx : x ∈ (trivializationAt F (AssociatedBundle G P F) a).baseSet)
    (w : DetBundle 𝕜 F (AssociatedBundle G P F) x) :
    (trivializationAt F' (AssociatedBundle G P F') a ⟨x, detMap G P hn η x w⟩).2 =
      DetBundle.chartCoord (trivializationAt F (AssociatedBundle G P F) a) hx w •
        η (fun i ↦ finBasis 𝕜 F (Fin.cast hn.symm i)) := by
  have hxP : x ∈ (trivializationAt G P a).baseSet := by rwa [← baseSet_trivializationAt (F := F)]
  obtain ⟨q⟩ : Nonempty (P x) := ⟨(FiberBundle.homeomorphAt G P x).symm 1⟩
  obtain ⟨g, hg⟩ : ∃ g, g = (trivializationAt G P a ⟨x, q⟩).2 := ⟨_, rfl⟩
  have hcoord (v : F) :
      (trivializationAt F (AssociatedBundle G P F) a ⟨x, mk G q (g⁻¹ • v)⟩).2 = v := by
    rw [hg, trivializationAt_mk_inv_smul_snd hxP]
  -- The classes `[q, g⁻¹ • bᵢ]` have chart coordinates `bᵢ`, so their wedge has coordinate `1`.
  obtain ⟨ω, hω⟩ : ∃ ω, ω = (DetBundle.linearEquiv 𝕜 F (AssociatedBundle G P F) x).symm
      (exteriorPower.ιMulti 𝕜 (finrank 𝕜 F) fun i ↦ mk G q (g⁻¹ • finBasis 𝕜 F i)) := ⟨_, rfl⟩
  have hω₁ : DetBundle.chartCoord (trivializationAt F (AssociatedBundle G P F) a) hx ω = 1 := by
    rw [hω, DetBundle.chartCoord_ιMulti]
    simp only [hcoord, Basis.det_self]
  have hw : w = DetBundle.chartCoord (trivializationAt F (AssociatedBundle G P F) a) hx w • ω :=
    (DetBundle.chartCoord _ hx).injective (by rw [map_smul, hω₁, smul_eq_mul, mul_one])
  have himage :
      detMap G P hn η x ω = mk G q (g⁻¹ • η fun i ↦ finBasis 𝕜 F (Fin.cast hn.symm i)) := by
    rw [hω, DetBundle.linearEquiv_symm_apply, ← hη]
    simpa only [Fin.cast_cast, Fin.cast_eq_self] using
      detMap_ιMulti_mk hn hη q fun i ↦ g⁻¹ • finBasis 𝕜 F (Fin.cast hn.symm i)
  conv_lhs => rw [hw, map_smul, himage, ← mk_smul_scalar, ← smul_comm]
  rw [hg]
  exact trivializationAt_mk_inv_smul_snd hxP q _

/-- **The determinant map is continuous.** For an equivariant `η`, the fibre maps
`TauCeti.AssociatedBundle.detMap` form a continuous map from the total space of the determinant
line `det (P ×_G F)` to the total space of `P ×_G F'`. -/
theorem continuous_detMap (hn : finrank 𝕜 F = n) {η : F [⋀^Fin n]→ₗ[𝕜] F'}
    (hη : ∀ (g : G) (v : Fin n → F), η (fun i ↦ g • v i) = g • η v) :
    Continuous fun w : TotalSpace 𝕜 (DetBundle 𝕜 F (AssociatedBundle G P F)) ↦
      TotalSpace.mk' F' w.proj (detMap G P hn η w.proj w.snd) := by
  refine FiberBundle.continuous_of_forall_trivialization _ (fun _ ↦ rfl) fun w ↦ ?_
  have he := (trivializationAt 𝕜 (DetBundle 𝕜 F (AssociatedBundle G P F)) w.proj).continuousOn
  refine ⟨trivializationAt 𝕜 (DetBundle 𝕜 F (AssociatedBundle G P F)) w.proj,
    trivializationAt F' (AssociatedBundle G P F') w.proj,
    fun _ s ↦ s • η (fun i ↦ finBasis 𝕜 F (Fin.cast hn.symm i)),
    mem_baseSet_trivializationAt 𝕜 _ w.proj, mem_baseSet_trivializationAt F' _ w.proj,
    (he.continuousAt ((trivializationAt 𝕜 _ w.proj).open_source.mem_nhds
      FiberBundle.mem_trivializationAt_proj_source)).snd.smul continuousAt_const, ?_⟩
  rintro ⟨x, v⟩ hx -
  rw [DetBundle.trivializationAt_eq, DetBundle.trivialization_baseSet] at hx
  rw [trivializationAt_detMap_snd hn hη hx, DetBundle.trivializationAt_eq,
    DetBundle.trivialization_apply_mk _ hx]

/-! ### The isomorphism of line bundles -/

variable (G P) in
/-- **The determinant line of an associated bundle.** If `F'` is a line and `η` is a nonzero
equivariant alternating map of `n = dim F` arguments, the fibre maps
`TauCeti.AssociatedBundle.detMap` form an isomorphism of line bundles
`det (P ×_G F) ≃ P ×_G F'`: a homeomorphism of total spaces over the identity of `B`, linear on
each fibre, reading `[p, v₀] ∧ ⋯ ∧ [p, vₙ₋₁] ↦ [p, η v]` in every principal frame `p`. -/
def detHomeomorph (hn : finrank 𝕜 F = n) (hF' : finrank 𝕜 F' = 1) {η : F [⋀^Fin n]→ₗ[𝕜] F'}
    (hη : ∀ (g : G) (v : Fin n → F), η (fun i ↦ g • v i) = g • η v) (hη₀ : η ≠ 0) :
    TotalSpace 𝕜 (DetBundle 𝕜 F (AssociatedBundle G P F)) ≃ₜ
      TotalSpace F' (AssociatedBundle G P F') :=
  haveI : FiniteDimensional 𝕜 F' := Module.finite_of_finrank_eq_succ hF'
  bundleHomeomorph
    (fun x ↦ (detEquiv G P hn hF' hη₀ x).toContinuousLinearEquivOfIsModuleTopology)
    ((continuous_detMap hn hη).congr fun _ ↦ by
      simp only [LinearEquiv.coe_toContinuousLinearEquivOfIsModuleTopology, detEquiv_apply])

@[simp]
theorem detHomeomorph_apply (hn : finrank 𝕜 F = n) (hF' : finrank 𝕜 F' = 1)
    {η : F [⋀^Fin n]→ₗ[𝕜] F'} (hη : ∀ (g : G) (v : Fin n → F), η (fun i ↦ g • v i) = g • η v)
    (hη₀ : η ≠ 0) (w : TotalSpace 𝕜 (DetBundle 𝕜 F (AssociatedBundle G P F))) :
    detHomeomorph G P hn hF' hη hη₀ w = ⟨w.proj, detMap G P hn η w.proj w.snd⟩ := by
  have : FiniteDimensional 𝕜 F' := Module.finite_of_finrank_eq_succ hF'
  rw [detHomeomorph, bundleHomeomorph_apply,
    LinearEquiv.coe_toContinuousLinearEquivOfIsModuleTopology, detEquiv_apply]

@[simp]
theorem detHomeomorph_symm_apply (hn : finrank 𝕜 F = n) (hF' : finrank 𝕜 F' = 1)
    {η : F [⋀^Fin n]→ₗ[𝕜] F'} (hη : ∀ (g : G) (v : Fin n → F), η (fun i ↦ g • v i) = g • η v)
    (hη₀ : η ≠ 0) (z : TotalSpace F' (AssociatedBundle G P F')) :
    (detHomeomorph G P hn hF' hη hη₀).symm z =
      ⟨z.proj, (detEquiv G P hn hF' hη₀ z.proj).symm z.snd⟩ := by
  have : FiniteDimensional 𝕜 F' := Module.finite_of_finrank_eq_succ hF'
  rw [detHomeomorph, bundleHomeomorph_symm_apply,
    LinearEquiv.symm_toContinuousLinearEquivOfIsModuleTopology,
    LinearEquiv.coe_toContinuousLinearEquivOfIsModuleTopology]

end TauCeti.AssociatedBundle

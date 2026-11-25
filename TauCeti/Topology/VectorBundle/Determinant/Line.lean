/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.VectorBundle.Determinant

/-!
# The determinant line of a line bundle and of a trivial bundle

Let `E → B` be a vector bundle over a complete nontrivially normed field `𝕜`, with
finite-dimensional model fibre `F` of dimension `r`, and let `det E = ⋀ʳ E` be its determinant
line (`TauCeti.DetBundle 𝕜 F E`). This file constructs canonical trivializations of `det E` in
the cases where `det E` is canonically a known line bundle.

* **The determinant line of a line is the line.** When `F` has dimension one, each fibre
  `⋀¹ (E x)` is identified with `E x` by `exteriorPower.oneEquiv`
  (`TauCeti.DetBundle.lineEquiv`, sending `v` to `v`), and these identifications form a
  homeomorphism of total spaces `det E ≃ E` (`TauCeti.DetBundle.lineHomeomorph`).
* **The determinant line in rank zero is trivial.** When `F` is zero, the empty exterior product
  `1 ∈ ⋀⁰ (E x)` is a continuous nowhere-vanishing section of `det E`
  (`TauCeti.DetBundle.rankZeroSection`).
* **The determinant line of a trivial bundle is trivial.** For the trivial bundle `B × F`, each
  fibre `⋀ʳ F` is identified with `𝕜` by the fixed coordinate
  `TauCeti.DetBundle.modelCoord F` of the basis `Module.finBasis 𝕜 F`
  (`TauCeti.DetBundle.trivialEquiv`), and these identifications form a homeomorphism of total
  spaces `det (B × F) ≃ B × 𝕜` (`TauCeti.DetBundle.trivialHomeomorph`).

All three are continuous because, read in the trivializations of `det E` induced from those of
`E`, they are given by a fixed linear map, or a fixed vector, independent of the base point.

For `𝕜 = ℂ` these are the identifications through which the first Chern class of a complex vector
bundle, defined as the first Chern class of its determinant line, agrees with the first Chern class
of a line bundle and vanishes on trivial bundles and in rank zero.

## Main definitions

* `TauCeti.DetBundle.lineEquiv`: the identification `⋀¹ (E x) ≃ E x` of the fibres of the
  determinant line of a line bundle.
* `TauCeti.DetBundle.lineHomeomorph`: the determinant line of a line bundle is the line bundle.
* `TauCeti.DetBundle.rankZeroSection`: the empty exterior product, a nowhere-vanishing continuous
  section of the determinant line of a bundle of rank zero.
* `TauCeti.DetBundle.trivialEquiv`: the identification `⋀ʳ F ≃ 𝕜` of the fibres of the
  determinant line of the trivial bundle `B × F`.
* `TauCeti.DetBundle.trivialHomeomorph`: the determinant line of the trivial bundle `B × F` is
  the trivial line bundle `B × 𝕜`.

## References

* J. W. Milnor, J. D. Stasheff, *Characteristic Classes*, Annals of Mathematics Studies 76,
  Princeton (1974), §14.
-/

public section

noncomputable section

open Bundle Module

namespace TauCeti

namespace DetBundle

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {B : Type*} {F : Type*} [NormedAddCommGroup F]
  [NormedSpace 𝕜 F]

/-- A fibrewise family of maps is continuous on total spaces when, read in the trivializations at
every base point, it is a fixed continuous map `Λ` between the model fibres. -/
private theorem continuous_totalSpaceMk_of_trivializationAt [TopologicalSpace B]
    {F₁ F₂ : Type*} [TopologicalSpace F₁] [TopologicalSpace F₂] {E₁ E₂ : B → Type*}
    [TopologicalSpace (TotalSpace F₁ E₁)] [∀ x, TopologicalSpace (E₁ x)] [FiberBundle F₁ E₁]
    [TopologicalSpace (TotalSpace F₂ E₂)] [∀ x, TopologicalSpace (E₂ x)] [FiberBundle F₂ E₂]
    (φ : ∀ x, E₁ x → E₂ x) {Λ : F₁ → F₂} (hΛ : Continuous Λ)
    (h : ∀ (y x : B) (v : E₁ x), x ∈ (trivializationAt F₁ E₁ y).baseSet →
      x ∈ (trivializationAt F₂ E₂ y).baseSet →
        (trivializationAt F₂ E₂ y ⟨x, φ x v⟩).2 = Λ (trivializationAt F₁ E₁ y ⟨x, v⟩).2) :
    Continuous fun p : TotalSpace F₁ E₁ ↦ TotalSpace.mk' F₂ p.proj (φ p.proj p.snd) :=
  FiberBundle.continuous_of_forall_trivialization _ (fun _ ↦ rfl) fun p ↦
    ⟨trivializationAt F₁ E₁ p.proj, trivializationAt F₂ E₂ p.proj, fun _ ↦ Λ,
      mem_baseSet_trivializationAt F₁ E₁ p.proj, mem_baseSet_trivializationAt F₂ E₂ p.proj,
      hΛ.continuousAt.comp ((trivializationAt F₁ E₁ p.proj).continuousOn.continuousAt
        ((trivializationAt F₁ E₁ p.proj).open_source.mem_nhds
          (FiberBundle.mem_trivializationAt_proj_source))).snd,
      fun q hq₁ hq₂ ↦ h p.proj q.proj q.snd hq₁ hq₂⟩

/-! ### The determinant line of a line bundle -/

section Line

variable [FiniteDimensional 𝕜 F] [CompleteSpace 𝕜] [TopologicalSpace B] {E : B → Type*}
  [∀ x, AddCommGroup (E x)] [∀ x, Module 𝕜 (E x)] [∀ x, TopologicalSpace (E x)]
  [TopologicalSpace (TotalSpace F E)] [FiberBundle F E] [VectorBundle 𝕜 F E]

/-- The linear equivalence underlying `TauCeti.DetBundle.lineEquiv`. -/
private def lineLinearEquiv (hF : finrank 𝕜 F = 1) (x : B) : DetBundle 𝕜 F E x ≃ₗ[𝕜] E x :=
  linearEquiv 𝕜 F E x ≪≫ₗ LinearEquiv.ofEq _ _ (congrArg (⋀[𝕜]^· (E x)) hF) ≪≫ₗ
    exteriorPower.oneEquiv 𝕜 (E x)

/-- **The determinant line of a line is the line**, fibrewise. When the model fibre `F` has
dimension one, the fibre `⋀¹ (E x)` of the determinant line over `x` is identified with `E x` by
`exteriorPower.oneEquiv`, which sends the one-vector `v` to `v`
(`TauCeti.DetBundle.lineEquiv_ιMulti`). -/
def lineEquiv (hF : finrank 𝕜 F = 1) (x : B) : DetBundle 𝕜 F E x ≃L[𝕜] E x where
  toLinearEquiv := lineLinearEquiv hF x
  continuous_toFun := by
    have := VectorBundle.isTopologicalAddGroup 𝕜 F E x
    have := VectorBundle.continuousSMul 𝕜 F E x
    exact IsModuleTopology.continuous_of_linearMap _
  continuous_invFun := by
    -- Through a trivialization, the inverse is a linear map out of the normed space `F`.
    let e := (trivializationAt F E x).continuousLinearEquivAt 𝕜 x
      (mem_baseSet_trivializationAt F E x)
    let g : F →ₗ[𝕜] DetBundle 𝕜 F E x :=
      (lineLinearEquiv hF x).symm.toLinearMap ∘ₗ e.symm.toLinearMap
    exact (g.continuous_of_finiteDimensional.comp e.continuous).congr fun v ↦
      congrArg (lineLinearEquiv hF x).symm (e.symm_apply_apply v)

/-- The identification of the determinant line of a line with the line is
`exteriorPower.oneEquiv`, after identifying `⋀ʳ` with `⋀¹` for `r = 1`. -/
theorem lineEquiv_apply (hF : finrank 𝕜 F = 1) (x : B) (v : DetBundle 𝕜 F E x) :
    lineEquiv hF x v = exteriorPower.oneEquiv 𝕜 (E x)
      (LinearEquiv.ofEq _ _ (congrArg (⋀[𝕜]^· (E x)) hF) (linearEquiv 𝕜 F E x v)) :=
  (rfl)

/-- The identification of the determinant line of a line with the line reads the one-vector `v`
as `v`. -/
theorem lineEquiv_ιMulti (hF : finrank 𝕜 F = 1) (x : B) (v : Fin (finrank 𝕜 F) → E x) :
    lineEquiv hF x ((linearEquiv 𝕜 F E x).symm (exteriorPower.ιMulti 𝕜 _ v)) =
      v (Fin.cast hF.symm 0) := by
  rw [lineEquiv_apply, LinearEquiv.apply_symm_apply, exteriorPower.ofEq_ιMulti hF,
    exteriorPower.oneEquiv_ιMulti, Function.comp_apply]

/-- Read in a trivialization `e` of `E` and in the induced trivialization of `det E`, the
identification of the determinant line of a line with the line is a fixed linear map `𝕜 → F`. -/
private theorem linearEquivAt_lineEquiv (hF : finrank 𝕜 F = 1) (e : Trivialization F (π F E))
    [e.IsLinear 𝕜] {x : B} (hx : x ∈ e.baseSet) (v : DetBundle 𝕜 F E x) :
    e.linearEquivAt 𝕜 x hx (lineEquiv hF x v) =
      exteriorPower.oneEquiv 𝕜 F (LinearEquiv.ofEq _ _ (congrArg (⋀[𝕜]^· F) hF)
        ((modelCoord F).symm (chartCoord e hx v))) := by
  rw [chartCoord_apply, LinearEquiv.symm_apply_apply, ← LinearEquiv.coe_toLinearMap
    ((e.linearEquivAt 𝕜 x hx).exteriorPower (finrank 𝕜 F)), LinearEquiv.exteriorPower_toLinearMap,
    exteriorPower.oneEquiv_ofEq_map hF, lineEquiv_apply, LinearEquiv.coe_coe]

/-- **The determinant line of a line bundle is the line bundle.** When the model fibre `F` has
dimension one, the fibrewise identifications `TauCeti.DetBundle.lineEquiv` of `⋀¹ (E x)` with
`E x` form a homeomorphism of total spaces `det E ≃ E`. -/
def lineHomeomorph (hF : finrank 𝕜 F = 1) : TotalSpace 𝕜 (DetBundle 𝕜 F E) ≃ₜ TotalSpace F E :=
  bundleHomeomorph (lineEquiv hF) <| by
    -- In coordinates the map is the fixed linear map `Λ : 𝕜 → F`.
    let Λ : 𝕜 →ₗ[𝕜] F := (exteriorPower.oneEquiv 𝕜 F).toLinearMap ∘ₗ
      (LinearEquiv.ofEq _ _ (congrArg (⋀[𝕜]^· F) hF)).toLinearMap ∘ₗ
        (modelCoord F).symm.toLinearMap
    refine continuous_totalSpaceMk_of_trivializationAt (fun x ↦ lineEquiv hF x)
      Λ.continuous_of_finiteDimensional
      fun y x v _ (hx : x ∈ (trivializationAt F E y).baseSet) ↦ ?_
    rw [trivializationAt_eq, trivialization_apply_mk _ hx]
    exact linearEquivAt_lineEquiv hF _ hx v

@[simp]
theorem lineHomeomorph_apply (hF : finrank 𝕜 F = 1) (p : TotalSpace 𝕜 (DetBundle 𝕜 F E)) :
    lineHomeomorph hF p = ⟨p.proj, lineEquiv hF p.proj p.snd⟩ :=
  bundleHomeomorph_apply _ _ p

@[simp]
theorem lineHomeomorph_symm_apply (hF : finrank 𝕜 F = 1) (p : TotalSpace F E) :
    (lineHomeomorph hF).symm p = ⟨p.proj, (lineEquiv hF p.proj).symm p.snd⟩ :=
  bundleHomeomorph_symm_apply _ _ p

end Line

/-! ### The determinant line in rank zero -/

section RankZero

variable {E : B → Type*} [∀ x, AddCommGroup (E x)] [∀ x, Module 𝕜 (E x)]

/-- **The empty exterior product**, a section of the determinant line of a bundle of rank zero:
over `x` it is the exterior product `1 ∈ ⋀⁰ (E x)` of the empty family of vectors. It is
continuous (`TauCeti.DetBundle.continuous_rankZeroSection`) and vanishes nowhere
(`TauCeti.DetBundle.rankZeroSection_ne_zero`), so the determinant line of a bundle of rank zero is
trivial. -/
def rankZeroSection (hF : finrank 𝕜 F = 0) (x : B) : DetBundle 𝕜 F E x :=
  (linearEquiv 𝕜 F E x).symm (exteriorPower.ιMulti 𝕜 _ fun i ↦ (Fin.cast hF i).elim0)

/-- The empty exterior product vanishes nowhere: it is `1 ∈ ⋀⁰ (E x) ≃ 𝕜`. -/
theorem rankZeroSection_ne_zero (hF : finrank 𝕜 F = 0) (x : B) :
    rankZeroSection (E := E) hF x ≠ 0 := fun h ↦ by
  have h₁ := congrArg (fun v ↦ exteriorPower.zeroEquiv 𝕜 (E x)
    (LinearEquiv.ofEq _ _ (congrArg (⋀[𝕜]^· (E x)) hF) (linearEquiv 𝕜 F E x v))) h
  simp only [rankZeroSection, LinearEquiv.apply_symm_apply, exteriorPower.ofEq_ιMulti hF,
    exteriorPower.zeroEquiv_ιMulti, map_zero] at h₁
  exact one_ne_zero h₁

variable [FiniteDimensional 𝕜 F] [TopologicalSpace B] [TopologicalSpace (TotalSpace F E)]

/-- Every chart coordinate reads the empty exterior product as `1`. -/
theorem chartCoord_rankZeroSection (hF : finrank 𝕜 F = 0) (e : Trivialization F (π F E))
    [e.IsLinear 𝕜] {x : B} (hx : x ∈ e.baseSet) : chartCoord e hx (rankZeroSection hF x) = 1 := by
  have : IsEmpty (Fin (finrank 𝕜 F)) := by rw [hF]; infer_instance
  rw [rankZeroSection, chartCoord_ιMulti, Module.Basis.det_isEmpty,
    AlternatingMap.constOfIsEmpty_apply, Function.const_apply]

variable [∀ x, TopologicalSpace (E x)] [FiberBundle F E] [VectorBundle 𝕜 F E]

variable [CompleteSpace 𝕜]

/-- The empty exterior product is a continuous section of the determinant line: in every induced
trivialization it is the constant `1`. -/
theorem continuous_rankZeroSection (hF : finrank 𝕜 F = 0) :
    Continuous fun x ↦ TotalSpace.mk' 𝕜 x (rankZeroSection (E := E) hF x) := by
  refine continuous_iff_continuousAt.2 fun x₀ ↦ (FiberBundle.continuousAt_totalSpace 𝕜 _).2
    ⟨continuousAt_id, (continuousAt_const (y := (1 : 𝕜))).congr ?_⟩
  filter_upwards [(trivializationAt F E x₀).open_baseSet.mem_nhds
    (mem_baseSet_trivializationAt F E x₀)] with x hx
  rw [trivializationAt_eq, TotalSpace.mk', trivialization_apply_mk _ hx,
    chartCoord_rankZeroSection]

end RankZero

/-! ### The determinant line of a trivial bundle -/

section Trivial

variable [FiniteDimensional 𝕜 F]

variable (𝕜 B F) in
/-- **The determinant line of a trivial bundle is trivial**, fibrewise: the fibre `⋀ʳ F` of the
determinant line of `B × F` is identified with `𝕜` by the fixed coordinate
`TauCeti.DetBundle.modelCoord F`, which reads `v₁ ∧ ⋯ ∧ vᵣ` as the determinant of `(v₁, …, vᵣ)` in
the basis `Module.finBasis 𝕜 F` (`TauCeti.DetBundle.trivialEquiv_ιMulti`). -/
def trivialEquiv (x : B) : DetBundle 𝕜 F (Trivial B F) x ≃L[𝕜] Trivial B 𝕜 x :=
  (linearEquiv 𝕜 F (Trivial B F) x ≪≫ₗ modelCoord F).toContinuousLinearEquivOfIsModuleTopology

/-- The identification of the determinant line of a trivial bundle with `𝕜` reads
`v₁ ∧ ⋯ ∧ vᵣ` as the determinant of `(v₁, …, vᵣ)` in the basis `Module.finBasis 𝕜 F`. -/
theorem trivialEquiv_ιMulti (x : B) (v : Fin (finrank 𝕜 F) → F) :
    trivialEquiv 𝕜 B F x ((linearEquiv 𝕜 F (Trivial B F) x).symm (exteriorPower.ιMulti 𝕜 _ v)) =
      (Module.finBasis 𝕜 F).det v := by
  rw [trivialEquiv, LinearEquiv.coe_toContinuousLinearEquivOfIsModuleTopology,
    LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply,
    Module.Basis.exteriorPowerTopEquiv_apply_ιMulti]

/-- The identification of the determinant line of a trivial bundle with `𝕜` is the fixed coordinate
`TauCeti.DetBundle.modelCoord F` of the determinant line of the model fibre. -/
theorem trivialEquiv_apply (x : B) (v : DetBundle 𝕜 F (Trivial B F) x) :
    trivialEquiv 𝕜 B F x v = modelCoord F (linearEquiv 𝕜 F (Trivial B F) x v) := by
  rw [trivialEquiv, LinearEquiv.coe_toContinuousLinearEquivOfIsModuleTopology,
    LinearEquiv.trans_apply]

variable [TopologicalSpace B]

/-- The chart coordinate of the trivialization of the determinant line of `B × F` induced by its
canonical trivialization is the fixed coordinate `TauCeti.DetBundle.modelCoord F`. -/
private theorem chartCoord_trivializationAt (y x : B)
    (hx : x ∈ (trivializationAt F (Trivial B F) y).baseSet) (v : DetBundle 𝕜 F (Trivial B F) x) :
    chartCoord (trivializationAt F (Trivial B F) y) hx v = trivialEquiv 𝕜 B F x v := by
  -- The canonical trivialization of `B × F` is the identity on each fibre.
  have h : (trivializationAt F (Trivial B F) y).linearEquivAt 𝕜 x hx = LinearEquiv.refl 𝕜 F :=
    LinearEquiv.ext fun _ ↦ rfl
  rw [chartCoord_apply, h, LinearEquiv.exteriorPower_refl, LinearEquiv.refl_apply,
    trivialEquiv_apply]

variable [CompleteSpace 𝕜]

variable (𝕜 B F) in
/-- **The determinant line of a trivial bundle is trivial.** The fibrewise identifications
`TauCeti.DetBundle.trivialEquiv` of `⋀ʳ F` with `𝕜` form a homeomorphism of total spaces
`det (B × F) ≃ B × 𝕜`. -/
def trivialHomeomorph :
    TotalSpace 𝕜 (DetBundle 𝕜 F (Trivial B F)) ≃ₜ TotalSpace 𝕜 (Trivial B 𝕜) :=
  bundleHomeomorph (trivialEquiv 𝕜 B F) <|
    continuous_totalSpaceMk_of_trivializationAt (fun x ↦ trivialEquiv 𝕜 B F x) continuous_id
      fun y x v _ _ ↦ by
      have hx : x ∈ (trivializationAt F (Trivial B F) y).baseSet := Set.mem_univ x
      rw [trivializationAt_eq, trivialization_apply_mk _ hx, chartCoord_trivializationAt]
      rfl

@[simp]
theorem trivialHomeomorph_apply (p : TotalSpace 𝕜 (DetBundle 𝕜 F (Trivial B F))) :
    trivialHomeomorph 𝕜 B F p = ⟨p.proj, trivialEquiv 𝕜 B F p.proj p.snd⟩ :=
  bundleHomeomorph_apply _ _ p

@[simp]
theorem trivialHomeomorph_symm_apply (p : TotalSpace 𝕜 (Trivial B 𝕜)) :
    (trivialHomeomorph 𝕜 B F).symm p = ⟨p.proj, (trivialEquiv 𝕜 B F p.proj).symm p.snd⟩ :=
  bundleHomeomorph_symm_apply _ _ p

end Trivial

end DetBundle

end TauCeti

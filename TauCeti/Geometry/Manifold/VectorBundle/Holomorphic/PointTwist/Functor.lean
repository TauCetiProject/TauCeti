/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.Hom
public import TauCeti.Geometry.Manifold.VectorBundle.Holomorphic.PointTwist.RealSmooth
public import TauCeti.Topology.Algebra.Module.Equiv.RestrictScalars

/-!
# Functoriality and cancellation of point twists

Let `X` be a Riemann surface and `E → X` a complex vector bundle with model fibre `F`. The signed
point twist `E(±x)` (`TauCeti.signedPointTwistCore`) is glued from the preferred trivializations
of `E` and the centred chart coordinate at `x`. Its fibre at `z` is the model fibre `F`, read as the
coordinates of `E z` in the preferred trivialization of `E` at `z`, and its chart `i` differs from
the chart `i.1` of `E` only by the nowhere-zero scalar `TauCeti.signedPointTwistFactor`.

This file shows that twisting is functorial and that the two opposite twists at `x` cancel.

* A family `e z : E z →L[ℂ] E' z` of complex linear fibre maps induces the family
  `TauCeti.signedPointTwistHom x s e` between the fibres of the twists: `e z` read in the
  preferred charts of `E` and `E'` at `z`. In every chart `i` of the twists it reads as `e` in the
  charts `i.1` of `E` and `E'`, because the scalars of the twist commute with the complex linear
  maps `e z` (`TauCeti.signedPointTwistCore_localTriv_signedPointTwistHom`). In particular its
  reading in the preferred charts at any point agrees with that of `e` nearby
  (`TauCeti.inCoordinates_signedPointTwistHom_eventuallyEq`), so it is `C^n` on total spaces when
  `e` is (`TauCeti.contMDiff_signedPointTwistHom`), for any model of `X` over a subfield `𝕜` of `ℂ`:
  the real structure of `TauCeti.signedPointTwistCore.contMDiffVectorBundle_real` (`𝓘(ℝ, ℂ)`) and
  the holomorphic one (`𝓘(ℂ)`).
* For fibre isomorphisms the twisted maps are isomorphisms `TauCeti.signedPointTwistEquiv`, which
  respect identities, composition and inverses (`TauCeti.signedPointTwistEquiv_refl`,
  `TauCeti.signedPointTwistEquiv_trans`, `TauCeti.signedPointTwistEquiv_symm`). A family whose
  total-space map is `C^n` induces a `C^n` diffeomorphism `E(±x) ≅ E'(±x)`
  (`TauCeti.signedPointTwistDiffeomorph`).
* The twist of `E(±x)` with the opposite sign is `E` again: the fibre isomorphism
  `TauCeti.signedPointTwistCancelEquiv` reads a coordinate of the double twist as a vector of `E`
  through the preferred chart of `E`. In the preferred charts at any point it is the identity, since
  the two scalars of the double twist are inverse to each other
  (`TauCeti.trivializationAt_signedPointTwistCancelEquiv`), so it is a `C^n` diffeomorphism for
  any model of `X` over any field for which `E` is a `C^n` bundle structure, real or holomorphic
  (`TauCeti.signedPointTwistCancelDiffeomorph`). The two signs give `E(x)(-x) ≅ E` and
  `E(-x)(x) ≅ E`.

In the proof of the Riemann–Roch formula for real Cauchy–Riemann operators (McDuff–Salamon,
Theorem C.1.10), a smooth complex line bundle `L` is identified with a twist of the trivial bundle
at the signed zeros of a generic section. Functoriality transports the identification along the
twists, and cancellation undoes a twist.

## Main definitions

* `TauCeti.signedPointTwistHom`, `TauCeti.signedPointTwistEquiv`: the fibre maps of the twists
  induced by fibre maps of the bundles.
* `TauCeti.signedPointTwistDiffeomorph`: `E ≅ E'` implies `E(±x) ≅ E'(±x)`, as `C^n`
  diffeomorphisms of total spaces with complex linear fibre maps, for any model `I` of `X` over a
  subfield `𝕜` of `ℂ` (real for `𝓘(ℝ, ℂ)`, holomorphic for `𝓘(ℂ)`).
* `TauCeti.signedPointTwistCancelEquiv` and `TauCeti.signedPointTwistCancelDiffeomorph`:
  `E(x)(-x) ≅ E` and `E(-x)(x) ≅ E`.

## Main results

* `TauCeti.signedPointTwistCore_localTriv_signedPointTwistHom`: in every chart, the twisted map
  reads as the original one.
* `TauCeti.contMDiff_signedPointTwistHom`, `TauCeti.contMDiff_signedPointTwistEquiv`: the twisted
  maps are `C^n` on total spaces.
* `TauCeti.signedPointTwistEquiv_refl`, `TauCeti.signedPointTwistEquiv_trans`,
  `TauCeti.signedPointTwistEquiv_symm`: the functor laws.
* `TauCeti.trivializationAt_signedPointTwistCancelEquiv`: in the preferred charts at any point, the
  cancellation isomorphism is the identity.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Theorem C.1.10.
* P. Griffiths and J. Harris, *Principles of Algebraic Geometry*, Chapter 1, Section 1
  (divisors and line bundles).
-/

public section

noncomputable section

open Bundle Set Topology Filter
open scoped Manifold ContDiff

namespace TauCeti

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]

section Bundle

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
  {E : X → Type*} [∀ z, AddCommGroup (E z)] [∀ z, Module ℂ (E z)]
  [∀ z, TopologicalSpace (E z)] [TopologicalSpace (TotalSpace F E)]
  [FiberBundle F E] [VectorBundle ℂ F E]
  {F' : Type*} [NormedAddCommGroup F'] [NormedSpace ℂ F']
  {E' : X → Type*} [∀ z, AddCommGroup (E' z)] [∀ z, Module ℂ (E' z)]
  [∀ z, TopologicalSpace (E' z)] [TopologicalSpace (TotalSpace F' E')]
  [FiberBundle F' E'] [VectorBundle ℂ F' E']
  {F'' : Type*} [NormedAddCommGroup F''] [NormedSpace ℂ F'']
  {E'' : X → Type*} [∀ z, AddCommGroup (E'' z)] [∀ z, Module ℂ (E'' z)]
  [∀ z, TopologicalSpace (E'' z)] [TopologicalSpace (TotalSpace F'' E'')]
  [FiberBundle F'' E''] [VectorBundle ℂ F'' E'']

/-! ### Twisting fibre maps -/

variable (F F') in
/-- The fibre map of the signed point twists induced by a complex linear fibre map `e z` from `E`
to `E'`: the fibres of the twists at `z` are, by definition, the model fibres `F` and `F'`, read as
the coordinates of `E z` and `E' z` in the preferred charts at `z`, and `e z` is read in these
charts. -/
def signedPointTwistHom (x : X) (s : Bool) (e : ∀ z, E z →L[ℂ] E' z) (z : X) :
    (signedPointTwistCore F E x s).Fiber z →L[ℂ] (signedPointTwistCore F' E' x s).Fiber z :=
  ContinuousLinearMap.inCoordinates F E F' E' z z z z (e z)

@[simp] theorem signedPointTwistHom_apply (x : X) (s : Bool) (e : ∀ z, E z →L[ℂ] E' z) (z : X)
    (w : F) :
    signedPointTwistHom F F' x s e z w =
      (trivializationAt F' E' z ⟨z, e z ((trivializationAt F E z).symm z w)⟩).2 := by
  -- The fibres of the twists are `F` and `F'` by definition, so the map is `inCoordinates`.
  change ContinuousLinearMap.inCoordinates F E F' E' z z z z (e z) w = _
  rw [ContinuousLinearMap.inCoordinates, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.comp_apply,
    Trivialization.symmL_apply _ (mem_baseSet_trivializationAt F E z),
    Trivialization.continuousLinearMapAt_apply_of_mem _ _ (mem_baseSet_trivializationAt F' E' z)]

/-- **The twisted map in every chart.** In every chart `i` of the twists, the twisted map reads as
`e` in the charts `i.1` of `E` and `E'`: both charts of the twists carry the same scalar, which
commutes with the complex linear map `e z`. -/
theorem signedPointTwistCore_localTriv_signedPointTwistHom {x : X} {s : Bool} {i : X × Bool}
    {z : X} (hz : z ∈ (trivializationAt F E i.1).baseSet)
    (hz' : z ∈ (trivializationAt F' E' i.1).baseSet) (e : ∀ z, E z →L[ℂ] E' z) (v : F) :
    ((signedPointTwistCore F' E' x s).localTriv i ⟨z, signedPointTwistHom F F' x s e z v⟩).2 =
      ContinuousLinearMap.inCoordinates F E F' E' i.1 z i.1 z (e z)
        ((signedPointTwistCore F E x s).localTriv i ⟨z, v⟩).2 := by
  have h₀ := mem_baseSet_trivializationAt F E z
  have h₀' := mem_baseSet_trivializationAt F' E' z
  -- Both sides carry the scalar of the chart `i`; pull it out of the complex linear map.
  refine (signedPointTwistCore_localTriv_apply (F := F') (E := E') x s i z _).trans ?_
  rw [signedPointTwistCore_localTriv_apply, map_smul]
  congr 1
  -- What remains is the change of charts from `z` to `i.1`, in `E` and in `E'`.
  simp only [Trivialization.coordChangeL_apply _ _ ⟨h₀', hz'⟩,
    Trivialization.coordChangeL_apply _ _ ⟨h₀, hz⟩, signedPointTwistHom_apply,
    Trivialization.symm_apply_apply_mk _ h₀', ContinuousLinearMap.inCoordinates,
    ContinuousLinearMap.comp_apply, Trivialization.symmL_apply _ hz,
    Trivialization.symm_apply_apply_mk _ hz,
    Trivialization.continuousLinearMapAt_apply_of_mem _ _ hz']

/-! ### Twisting fibre isomorphisms -/

variable (F F') in
/-- The fibre isomorphism of the signed point twists induced by a fibre isomorphism `e z` of `E`
and `E'`, read in the preferred charts at `z`; its underlying map is `signedPointTwistHom`
(`TauCeti.coe_signedPointTwistEquiv`). -/
def signedPointTwistEquiv (x : X) (s : Bool) (e : ∀ z, E z ≃L[ℂ] E' z) (z : X) :
    (signedPointTwistCore F E x s).Fiber z ≃L[ℂ] (signedPointTwistCore F' E' x s).Fiber z :=
  ((trivializationAt F E z).continuousLinearEquivAt ℂ z
      (mem_baseSet_trivializationAt F E z)).symm.trans
    ((e z).trans ((trivializationAt F' E' z).continuousLinearEquivAt ℂ z
      (mem_baseSet_trivializationAt F' E' z)))

@[simp] theorem signedPointTwistEquiv_apply (x : X) (s : Bool) (e : ∀ z, E z ≃L[ℂ] E' z) (z : X)
    (w : F) :
    signedPointTwistEquiv F F' x s e z w =
      (trivializationAt F' E' z ⟨z, e z ((trivializationAt F E z).symm z w)⟩).2 :=
  (rfl)

theorem coe_signedPointTwistEquiv (x : X) (s : Bool) (e : ∀ z, E z ≃L[ℂ] E' z) (z : X) :
    (signedPointTwistEquiv F F' x s e z : _ →L[ℂ] _) =
      signedPointTwistHom F F' x s (fun z ↦ (e z : E z →L[ℂ] E' z)) z := by
  refine ContinuousLinearMap.ext fun w ↦ ?_
  exact (signedPointTwistHom_apply (F := F) (F' := F') (E := E) (E' := E') x s
    (fun z ↦ (e z : E z →L[ℂ] E' z)) z w).symm

/-- Twisting the identity gives the identity. -/
@[simp] theorem signedPointTwistEquiv_refl (x : X) (s : Bool) (z : X) :
    signedPointTwistEquiv F F x s (fun z ↦ ContinuousLinearEquiv.refl ℂ (E z)) z =
      ContinuousLinearEquiv.refl ℂ _ := by
  refine ContinuousLinearEquiv.ext (funext fun w ↦ ?_)
  -- Evaluate the twist; the chart of `E` at `z` and its inverse then cancel.
  refine (signedPointTwistEquiv_apply (F := F) (F' := F) (E := E) (E' := E) x s _ z w).trans ?_
  exact congrArg Prod.snd
    ((trivializationAt F E z).apply_mk_symm (mem_baseSet_trivializationAt F E z) w)

/-- Twisting respects composition. -/
theorem signedPointTwistEquiv_trans (x : X) (s : Bool) (e : ∀ z, E z ≃L[ℂ] E' z)
    (e' : ∀ z, E' z ≃L[ℂ] E'' z) (z : X) :
    signedPointTwistEquiv F F'' x s (fun z ↦ (e z).trans (e' z)) z =
      (signedPointTwistEquiv F F' x s e z).trans (signedPointTwistEquiv F' F'' x s e' z) := by
  refine ContinuousLinearEquiv.ext (funext fun w ↦ ?_)
  -- Evaluate the twist of the composite. The composite of the two twists is, by
  -- `signedPointTwistEquiv_apply` applied twice, `e' z` read after `e z` with the chart of `E'` at
  -- `z` and its inverse in between, which cancel.
  refine (signedPointTwistEquiv_apply (F := F) (F' := F'') (E := E) (E' := E'') x s _ z w).trans ?_
  exact congrArg (fun y ↦ (trivializationAt F'' E'' z ⟨z, e' z y⟩).2)
    ((trivializationAt F' E' z).symm_apply_apply_mk (mem_baseSet_trivializationAt F' E' z) _).symm

/-- Twisting respects inverses. -/
@[simp] theorem signedPointTwistEquiv_symm (x : X) (s : Bool) (e : ∀ z, E z ≃L[ℂ] E' z) (z : X) :
    (signedPointTwistEquiv F F' x s e z).symm =
      signedPointTwistEquiv F' F x s (fun z ↦ (e z).symm) z :=
  -- Both sides are the inverse chart of `E'` at `z`, then `(e z).symm`, then the chart of `E` at
  -- `z`: `ContinuousLinearEquiv.symm` reverses `trans` and inverts each factor by definition.
  (rfl)

end Bundle

/-! ### Smoothness of twisted maps -/

section Smooth

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [NormedAlgebra 𝕜 ℂ]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [NormedSpace 𝕜 F]
  [IsScalarTower 𝕜 ℂ F]
  {E : X → Type*} [∀ z, AddCommGroup (E z)] [∀ z, Module ℂ (E z)] [∀ z, Module 𝕜 (E z)]
  [∀ z, IsScalarTower 𝕜 ℂ (E z)] [∀ z, TopologicalSpace (E z)] [TopologicalSpace (TotalSpace F E)]
  [FiberBundle F E] [VectorBundle ℂ F E]
  {F' : Type*} [NormedAddCommGroup F'] [NormedSpace ℂ F'] [NormedSpace 𝕜 F']
  [IsScalarTower 𝕜 ℂ F']
  {E' : X → Type*} [∀ z, AddCommGroup (E' z)] [∀ z, Module ℂ (E' z)] [∀ z, Module 𝕜 (E' z)]
  [∀ z, IsScalarTower 𝕜 ℂ (E' z)] [∀ z, TopologicalSpace (E' z)]
  [TopologicalSpace (TotalSpace F' E')] [FiberBundle F' E'] [VectorBundle ℂ F' E']
  {EB : Type*} [NormedAddCommGroup EB] [NormedSpace 𝕜 EB] {I : ModelWithCorners 𝕜 EB ℂ}
  {n : ℕ∞ω}

/-- The underlying `𝕜`-vector bundle of a complex vector bundle. -/
local instance instVectorBundlePointTwistFunctor {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℂ F] [NormedSpace 𝕜 F] [IsScalarTower 𝕜 ℂ F] {E : X → Type*}
    [∀ z, AddCommGroup (E z)] [∀ z, Module ℂ (E z)] [∀ z, Module 𝕜 (E z)]
    [∀ z, IsScalarTower 𝕜 ℂ (E z)] [∀ z, TopologicalSpace (E z)]
    [TopologicalSpace (TotalSpace F E)] [FiberBundle F E] [VectorBundle ℂ F E] :
    VectorBundle 𝕜 F E :=
  VectorBundle.restrictScalars 𝕜 ℂ F E

/-- **The twisted map in the preferred charts.** Near every point `z₀`, the twisted map read in the
preferred charts of the twists at `z₀` is `e` read in the preferred charts of `E` and `E'` at `z₀`,
as `𝕜`-linear maps. This is the chart `(z₀, decide (z₀ = x))` case of
`TauCeti.signedPointTwistCore_localTriv_signedPointTwistHom`. -/
theorem inCoordinates_signedPointTwistHom_eventuallyEq (x : X) (s : Bool) (e : ∀ z, E z →L[ℂ] E' z)
    (z₀ : X) :
    ∀ᶠ z in 𝓝 z₀,
      ContinuousLinearMap.inCoordinates F (signedPointTwistCore F E x s).Fiber F'
          (signedPointTwistCore F' E' x s).Fiber z₀ z z₀ z
          ((signedPointTwistHom F F' x s e z).restrictScalars 𝕜) =
        ContinuousLinearMap.inCoordinates F E F' E' z₀ z z₀ z ((e z).restrictScalars 𝕜) := by
  classical
  have h := (trivializationAt F (signedPointTwistCore F E x s).Fiber z₀).open_baseSet.inter
    (trivializationAt F' (signedPointTwistCore F' E' x s).Fiber z₀).open_baseSet
  filter_upwards [h.mem_nhds ⟨mem_baseSet_trivializationAt F _ z₀,
    mem_baseSet_trivializationAt F' _ z₀⟩] with z hz
  ext w
  simp only [ContinuousLinearMap.inCoordinates, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.coe_restrictScalars']
  rw [Trivialization.symmL_apply _ hz.1,
    Trivialization.continuousLinearMapAt_apply_of_mem _ _ hz.2]
  -- The preferred charts of the twists at `z₀` are their charts `(z₀, decide (z₀ = x))`.
  rw [signedPointTwistCore_trivializationAt, signedPointTwistCore_trivializationAt] at hz ⊢
  have h₁ : z ∈ (trivializationAt F E z₀).baseSet := (mem_signedPointTwistCore_baseSet.1 hz.1).1
  have h₂ : z ∈ (trivializationAt F' E' z₀).baseSet :=
    (mem_signedPointTwistCore_baseSet.1 hz.2).1
  refine (signedPointTwistCore_localTriv_signedPointTwistHom (i := (z₀, decide (z₀ = x))) h₁ h₂
    e _).trans ?_
  rw [((signedPointTwistCore F E x s).localTriv _).apply_mk_symm hz.1 w]
  simp only [ContinuousLinearMap.inCoordinates, ContinuousLinearMap.comp_apply,
    Trivialization.symmL_apply _ h₁, Trivialization.continuousLinearMapAt_apply_of_mem _ _ h₂]

variable [CompleteSpace 𝕜] [FiniteDimensional 𝕜 F]

/-- **Twisting preserves `C^n` bundle maps.** If a family of complex linear fibre maps
`e z : E z →L[ℂ] E' z` is `C^n` on total spaces, for a model `I` of `X` over a subfield `𝕜` of `ℂ`
(`𝓘(ℝ, ℂ)` for the real structure, `𝓘(ℂ)` for the holomorphic one), so is the induced family of
maps of the signed point twists. -/
theorem contMDiff_signedPointTwistHom (x : X) (s : Bool) {e : ∀ z, E z →L[ℂ] E' z}
    (he : ContMDiff (I.prod 𝓘(𝕜, F)) (I.prod 𝓘(𝕜, F')) n
      fun p : TotalSpace F E ↦ TotalSpace.mk' F' p.proj (e p.proj p.snd)) :
    ContMDiff (I.prod 𝓘(𝕜, F)) (I.prod 𝓘(𝕜, F')) n
      fun p : TotalSpace F (signedPointTwistCore F E x s).Fiber ↦
        TotalSpace.mk' F' p.proj (signedPointTwistHom F F' x s e p.proj p.snd) := by
  have : ∀ z, IsTopologicalAddGroup (E' z) := VectorBundle.isTopologicalAddGroup 𝕜 F' E'
  have : ∀ z, ContinuousSMul 𝕜 (E' z) := VectorBundle.continuousSMul 𝕜 F' E'
  have : ∀ z, IsTopologicalAddGroup ((signedPointTwistCore F' E' x s).Fiber z) :=
    VectorBundle.isTopologicalAddGroup 𝕜 F' _
  have : ∀ z, ContinuousSMul 𝕜 ((signedPointTwistCore F' E' x s).Fiber z) :=
    VectorBundle.continuousSMul 𝕜 F' _
  -- Smoothness of a bundle map is that of its Hom section, read in the preferred charts.
  have h := (contMDiff_hom_bundle_iff (IB := I) (n := n)
    fun z ↦ (e z).restrictScalars 𝕜).2 he
  refine (contMDiff_hom_bundle_iff (IB := I) (n := n)
    (E₁ := (signedPointTwistCore F E x s).Fiber) (E₂ := (signedPointTwistCore F' E' x s).Fiber)
    fun z ↦ (signedPointTwistHom F F' x s e z).restrictScalars 𝕜).1 fun z₀ ↦ ?_
  rw [contMDiffAt_hom_bundle]
  exact ⟨contMDiffAt_id, ((contMDiffAt_hom_bundle _).1 (h z₀)).2.congr_of_eventuallyEq
    (inCoordinates_signedPointTwistHom_eventuallyEq x s e z₀)⟩

/-- **Twisting preserves `C^n` bundle isomorphisms.** If a family of complex fibre isomorphisms is
`C^n` on total spaces for a model `I` over `𝕜`, so is the induced family of isomorphisms of the
signed point twists. -/
theorem contMDiff_signedPointTwistEquiv (x : X) (s : Bool) {e : ∀ z, E z ≃L[ℂ] E' z}
    (he : ContMDiff (I.prod 𝓘(𝕜, F)) (I.prod 𝓘(𝕜, F')) n
      fun p : TotalSpace F E ↦ TotalSpace.mk' F' p.proj (e p.proj p.snd)) :
    ContMDiff (I.prod 𝓘(𝕜, F)) (I.prod 𝓘(𝕜, F')) n
      fun p : TotalSpace F (signedPointTwistCore F E x s).Fiber ↦
        TotalSpace.mk' F' p.proj (signedPointTwistEquiv F F' x s e p.proj p.snd) := by
  simpa only [← coe_signedPointTwistEquiv, ContinuousLinearEquiv.coe_coe] using
    contMDiff_signedPointTwistHom x s (e := fun z ↦ (e z : E z →L[ℂ] E' z)) he

variable (F F') in
/-- **Functoriality of point twists.** A family of complex fibre isomorphisms
`e z : E z ≃L[ℂ] E' z` whose total-space map is `C^n` for a model `I` over `𝕜` induces a `C^n`
diffeomorphism `E(±x) ≅ E'(±x)` of the signed point twists, with fibre maps
`signedPointTwistEquiv`. The inverse is `C^n` because the model fibre has finite dimension over
`𝕜`. -/
def signedPointTwistDiffeomorph (x : X) (s : Bool) (e : ∀ z, E z ≃L[ℂ] E' z)
    (he : ContMDiff (I.prod 𝓘(𝕜, F)) (I.prod 𝓘(𝕜, F')) n
      fun p : TotalSpace F E ↦ TotalSpace.mk' F' p.proj (e p.proj p.snd)) :
    TotalSpace F (signedPointTwistCore F E x s).Fiber ≃ₘ^n⟮I.prod 𝓘(𝕜, F),
      I.prod 𝓘(𝕜, F')⟯ TotalSpace F' (signedPointTwistCore F' E' x s).Fiber :=
  bundleDiffeomorph (E₁ := (signedPointTwistCore F E x s).Fiber)
    (E₂ := (signedPointTwistCore F' E' x s).Fiber)
    (fun z ↦ (signedPointTwistEquiv F F' x s e z).restrictScalars' 𝕜)
    (by simpa only [ContinuousLinearEquiv.coe_restrictScalars'] using
      contMDiff_signedPointTwistEquiv x s he)

@[simp] theorem signedPointTwistDiffeomorph_apply (x : X) (s : Bool) (e : ∀ z, E z ≃L[ℂ] E' z)
    (he : ContMDiff (I.prod 𝓘(𝕜, F)) (I.prod 𝓘(𝕜, F')) n
      fun p : TotalSpace F E ↦ TotalSpace.mk' F' p.proj (e p.proj p.snd))
    (p : TotalSpace F (signedPointTwistCore F E x s).Fiber) :
    signedPointTwistDiffeomorph F F' x s e he p =
      ⟨p.proj, signedPointTwistEquiv F F' x s e p.proj p.snd⟩ := by
  rw [signedPointTwistDiffeomorph, bundleDiffeomorph_apply,
    ContinuousLinearEquiv.coe_restrictScalars']

@[simp] theorem signedPointTwistDiffeomorph_symm_apply (x : X) (s : Bool)
    (e : ∀ z, E z ≃L[ℂ] E' z)
    (he : ContMDiff (I.prod 𝓘(𝕜, F)) (I.prod 𝓘(𝕜, F')) n
      fun p : TotalSpace F E ↦ TotalSpace.mk' F' p.proj (e p.proj p.snd))
    (p : TotalSpace F' (signedPointTwistCore F' E' x s).Fiber) :
    (signedPointTwistDiffeomorph F F' x s e he).symm p =
      ⟨p.proj, (signedPointTwistEquiv F F' x s e p.proj).symm p.snd⟩ := by
  rw [signedPointTwistDiffeomorph, bundleDiffeomorph_symm_apply,
    ContinuousLinearEquiv.coe_restrictScalars'_symm]

end Smooth

/-! ### Cancellation of opposite twists -/

section Cancel

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
  {E : X → Type*} [∀ z, AddCommGroup (E z)] [∀ z, Module ℂ (E z)]
  [∀ z, TopologicalSpace (E z)] [TopologicalSpace (TotalSpace F E)]
  [FiberBundle F E] [VectorBundle ℂ F E]

variable (F E) in
/-- The twist of the signed point twist `E(±x)` with the opposite sign is `E` again: the fibre
isomorphism reads a coordinate of the double twist at `z` as a vector of `E z` through the
preferred chart of `E` at `z`. For `s = true` this is `E(x)(-x) ≅ E`, for `s = false` it is
`E(-x)(x) ≅ E`. -/
def signedPointTwistCancelEquiv (x : X) (s : Bool) (z : X) :
    (signedPointTwistCore F (signedPointTwistCore F E x s).Fiber x (!s)).Fiber z ≃L[ℂ] E z :=
  ((trivializationAt F E z).continuousLinearEquivAt ℂ z
    (mem_baseSet_trivializationAt F E z)).symm

@[simp] theorem signedPointTwistCancelEquiv_apply (x : X) (s : Bool) (z : X) (v : F) :
    signedPointTwistCancelEquiv F E x s z v = (trivializationAt F E z).symm z v :=
  (rfl)

@[simp] theorem signedPointTwistCancelEquiv_symm_apply (x : X) (s : Bool) (z : X) (v : E z) :
    (signedPointTwistCancelEquiv F E x s z).symm v = (trivializationAt F E z ⟨z, v⟩).2 :=
  (rfl)

open Classical in
/-- The chart `(a, decide (a = x))` of the double twist `E(±x)(∓x)` reads a coordinate `v` at `z`
as the vector `(trivializationAt F E z).symm z v` read in the chart of `E` at `a`: the scalars
of the two opposite twists are inverse to each other. -/
theorem signedPointTwistCore_not_localTriv_apply {x a z : X} {s : Bool}
    (hz : z ∈ (signedPointTwistCore F (signedPointTwistCore F E x s).Fiber x (!s)).baseSet
      (a, decide (a = x))) (v : F) :
    ((signedPointTwistCore F (signedPointTwistCore F E x s).Fiber x (!s)).localTriv
        (a, decide (a = x)) ⟨z, v⟩).2 =
      (trivializationAt F E a ⟨z, (trivializationAt F E z).symm z v⟩).2 := by
  set T := signedPointTwistCore F E x s
  -- The chart of `E(±x)` at `a` contains `z`.
  have hzT := (mem_signedPointTwistCore_baseSet.1 hz).1
  have hza : z ∈ T.baseSet (a, decide (a = x)) := by
    rwa [signedPointTwistCore_trivializationAt] at hzT
  -- The coordinate change of the double twist is that of `E(±x)` times the opposite scalar.
  rw [signedPointTwistCore_localTriv_apply (E := T.Fiber),
    T.trivializationAt_coordChange_eq ⟨mem_baseSet_trivializationAt F T.Fiber z, hzT⟩,
    signedPointTwistCore_indexAt, signedPointTwistCore_indexAt, signedPointTwistCore_coordChange]
  -- The two scalars cancel, leaving the coordinate change of `E`.
  simp only [smul_apply, smul_smul, signedPointTwistFactor_not,
    signedPointTwistFactor_mul_swap (mem_pointTwistBaseSet_decide x z)
      (mem_signedPointTwistCore_baseSet.1 hza).2, one_smul, ContinuousLinearEquiv.coe_coe]
  exact Trivialization.coordChangeL_apply (R := ℂ) _ _ ⟨mem_baseSet_trivializationAt F E z,
    (mem_signedPointTwistCore_baseSet.1 hza).1⟩ v

/-- **The cancellation isomorphism in coordinates.** In the preferred charts of the double twist
and of `E` at any point `a`, the cancellation isomorphism is the identity. -/
theorem trivializationAt_signedPointTwistCancelEquiv {x a z : X} {s : Bool}
    (hz : z ∈ (trivializationAt F
      (signedPointTwistCore F (signedPointTwistCore F E x s).Fiber x (!s)).Fiber a).baseSet)
    (v : F) :
    (trivializationAt F E a ⟨z, signedPointTwistCancelEquiv F E x s z v⟩).2 =
      (trivializationAt F
        (signedPointTwistCore F (signedPointTwistCore F E x s).Fiber x (!s)).Fiber a ⟨z, v⟩).2 := by
  rw [signedPointTwistCore_trivializationAt] at hz ⊢
  exact (signedPointTwistCore_not_localTriv_apply hz v).symm

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [NormedSpace 𝕜 F]
  {EB : Type*} [NormedAddCommGroup EB] [NormedSpace 𝕜 EB] (I : ModelWithCorners 𝕜 EB ℂ)
  {n : ℕ∞ω}

variable (F E) in
/-- **Cancellation of opposite point twists.** The twist of `E(±x)` with the opposite sign is
isomorphic to `E`, by a `C^n` diffeomorphism of total spaces for any model `I` of `X` over any field
`𝕜` (for instance `𝓘(ℝ, ℂ)` for the real structure and `𝓘(ℂ)` for the holomorphic one), whose
fibre maps are the complex linear isomorphisms `signedPointTwistCancelEquiv`: in the preferred
charts it is the identity. This is `E(x)(-x) ≅ E` for `s = true` and `E(-x)(x) ≅ E` for
`s = false`. -/
def signedPointTwistCancelDiffeomorph (x : X) (s : Bool) :
    TotalSpace F (signedPointTwistCore F (signedPointTwistCore F E x s).Fiber x (!s)).Fiber
      ≃ₘ^n⟮I.prod 𝓘(𝕜, F), I.prod 𝓘(𝕜, F)⟯ TotalSpace F E where
  toFun p := ⟨p.proj, signedPointTwistCancelEquiv F E x s p.proj p.snd⟩
  invFun p := ⟨p.proj, (signedPointTwistCancelEquiv F E x s p.proj).symm p.snd⟩
  left_inv p := by simp only [ContinuousLinearEquiv.symm_apply_apply]
  right_inv p := by simp only [ContinuousLinearEquiv.apply_symm_apply]
  contMDiff_toFun := contMDiff_bundleMap_of_constant_coordinates
    (fun z ↦ signedPointTwistCancelEquiv F E x s z) (ContinuousLinearMap.id 𝕜 F)
    fun _ _ hz v ↦ trivializationAt_signedPointTwistCancelEquiv hz.1 v
  contMDiff_invFun := contMDiff_bundleMap_of_constant_coordinates
    (fun z ↦ (signedPointTwistCancelEquiv F E x s z).symm) (ContinuousLinearMap.id 𝕜 F)
    fun _ z hz v ↦ by
      -- Apply the forward identity to the coordinate `(e z).symm v`; the fibre of the double
      -- twist is the model fibre `F` by definition, so this coordinate is an element of `F`.
      have h := trivializationAt_signedPointTwistCancelEquiv hz.2
        ((signedPointTwistCancelEquiv F E x s z).symm v : F)
      rw [ContinuousLinearEquiv.apply_symm_apply] at h
      exact h.symm

@[simp] theorem signedPointTwistCancelDiffeomorph_apply (x : X) (s : Bool)
    (p : TotalSpace F (signedPointTwistCore F (signedPointTwistCore F E x s).Fiber x (!s)).Fiber) :
    signedPointTwistCancelDiffeomorph (n := n) F E I x s p =
      ⟨p.proj, signedPointTwistCancelEquiv F E x s p.proj p.snd⟩ :=
  (rfl)

@[simp] theorem signedPointTwistCancelDiffeomorph_symm_apply (x : X) (s : Bool)
    (p : TotalSpace F E) :
    (signedPointTwistCancelDiffeomorph (n := n) F E I x s).symm p =
      ⟨p.proj, (signedPointTwistCancelEquiv F E x s p.proj).symm p.snd⟩ :=
  (rfl)

end Cancel

end TauCeti

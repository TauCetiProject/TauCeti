/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.Hom
public import TauCeti.Geometry.Manifold.VectorBundle.Holomorphic.PointTwist.RealSmooth

/-!
# Functoriality and cancellation of point twists

Let `X` be a Riemann surface and `E → X` a complex vector bundle with model fibre `F`. The signed
point twist `E(±x)` (`TauCeti.signedPointTwistCore`) is glued from the preferred trivializations
of `E` and the centred chart coordinate at `x`. Its fibre at `z` is the model fibre `F`, read as the
coordinates of `E z` in the preferred trivialization of `E` at `z`, and its chart `i` differs from
the chart `i.1` of `E` only by the nowhere-zero scalar `TauCeti.signedPointTwistFactor`.

This file shows that twisting is functorial and that the two opposite twists at `x` cancel, as
isomorphisms of complex vector bundles which are `C^n` over the real manifold underlying `X`, the
setting of `TauCeti.signedPointTwistCore.contMDiffVectorBundle_real`.

* A family `e z : E z ≃L[ℂ] E' z` of complex fibre isomorphisms induces the family
  `TauCeti.signedPointTwistEquiv x s e` between the fibres of the twists: `e z` read in the
  preferred charts of `E` and `E'` at `z`. In every chart of the twists it reads as `e` in the
  corresponding charts of `E` and `E'`, because the scalars of the twist commute with the complex
  linear maps `e z` (`TauCeti.inCoordinates_signedPointTwistEquiv`). Hence it is real `C^n` on total
  spaces when `e` is (`TauCeti.contMDiff_signedPointTwistEquiv`), and an isomorphism `E ≅ E'`
  induces `E(±x) ≅ E'(±x)` (`TauCeti.signedPointTwistDiffeomorph`).
* The twist of `E(±x)` with the opposite sign is `E` again: the fibre isomorphism
  `TauCeti.signedPointTwistCancelEquiv` reads a coordinate of the double twist as a vector of `E`
  through the preferred chart of `E`. In the preferred charts at any point it is the identity, since
  the two scalars of the double twist are inverse to each other
  (`TauCeti.signedPointTwistCancelEquiv_coordinates`), so it is `C^n`
  (`TauCeti.signedPointTwistCancelDiffeomorph`). The two signs give `E(x)(-x) ≅ E` and
  `E(-x)(x) ≅ E`.

In the proof of the Riemann–Roch formula for real Cauchy–Riemann operators (McDuff–Salamon,
Theorem C.1.10), a smooth complex line bundle `L` is identified with a twist of the trivial bundle
at the signed zeros of a generic section. Functoriality transports the identification along the
twists, and cancellation undoes a twist.

## Main definitions

* `TauCeti.signedPointTwistEquiv`: the fibre isomorphisms of the twists induced by fibre
  isomorphisms of the bundles.
* `TauCeti.signedPointTwistDiffeomorph`: `E ≅ E'` implies `E(±x) ≅ E'(±x)`, as real `C^n`
  diffeomorphisms of total spaces with complex linear fibre maps.
* `TauCeti.signedPointTwistCancelEquiv` and `TauCeti.signedPointTwistCancelDiffeomorph`:
  `E(x)(-x) ≅ E` and `E(-x)(x) ≅ E`.

## Main results

* `TauCeti.inCoordinates_signedPointTwistEquiv`: in the preferred charts at any point, the twisted
  isomorphism reads as the original one.
* `TauCeti.contMDiff_signedPointTwistEquiv`: the twisted isomorphism is real `C^n` on total spaces.
* `TauCeti.signedPointTwistCancelEquiv_coordinates`: in the preferred charts at any point, the
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

variable (F F') in
/-- The fibre isomorphism of the signed point twists induced by a fibre isomorphism `e z` of `E`
and `E'`: the fibres of the twists at `z` are the coordinates of `E z` and `E' z` in the preferred
charts at `z`, and `e z` is read in these charts. -/
def signedPointTwistEquiv (x : X) (s : Bool) (e : ∀ z, E z ≃L[ℂ] E' z) (z : X) :
    (signedPointTwistCore F E x s).Fiber z ≃L[ℂ] (signedPointTwistCore F' E' x s).Fiber z :=
  ((trivializationAt F E z).continuousLinearEquivAt ℂ z
      (mem_baseSet_trivializationAt F E z)).symm.trans
    ((e z).trans ((trivializationAt F' E' z).continuousLinearEquivAt ℂ z
      (mem_baseSet_trivializationAt F' E' z)))

theorem signedPointTwistEquiv_apply (x : X) (s : Bool) (e : ∀ z, E z ≃L[ℂ] E' z) (z : X)
    (w : F) :
    signedPointTwistEquiv F F' x s e z w =
      (trivializationAt F' E' z ⟨z, e z ((trivializationAt F E z).symm z w)⟩).2 :=
  (rfl)

theorem signedPointTwistEquiv_symm_apply (x : X) (s : Bool) (e : ∀ z, E z ≃L[ℂ] E' z) (z : X)
    (w : F') :
    (signedPointTwistEquiv F F' x s e z).symm w =
      (trivializationAt F E z ⟨z, (e z).symm ((trivializationAt F' E' z).symm z w)⟩).2 :=
  (rfl)

/-- In every chart `i` of the twists, the twisted isomorphism reads as `e` in the chart `i.1` of
`E` and `E'`: the scalar of the twist in the chart `i` commutes with the complex linear
map `e z`. -/
theorem signedPointTwistCore_localTriv_signedPointTwistEquiv {x : X} {s : Bool} {i : X × Bool}
    {z : X} (hz : z ∈ (trivializationAt F E i.1).baseSet)
    (hz' : z ∈ (trivializationAt F' E' i.1).baseSet) (e : ∀ z, E z ≃L[ℂ] E' z)
    (v : F) :
    ((signedPointTwistCore F' E' x s).localTriv i ⟨z, signedPointTwistEquiv F F' x s e z v⟩).2 =
      (trivializationAt F' E' i.1 ⟨z, e z ((trivializationAt F E i.1).symm z
        ((signedPointTwistCore F E x s).localTriv i ⟨z, v⟩).2)⟩).2 := by
  have h₀ := mem_baseSet_trivializationAt F E z
  have h₀' := mem_baseSet_trivializationAt F' E' z
  refine (signedPointTwistCore_localTriv_apply (F := F') (E := E') x s i z
    (show F' from signedPointTwistEquiv F F' x s e z v)).trans ?_
  rw [signedPointTwistCore_localTriv_apply, Trivialization.coordChangeL_apply _ _ ⟨h₀', hz'⟩,
    signedPointTwistEquiv_apply, (trivializationAt F' E' z).symm_apply_apply_mk h₀',
    Trivialization.coordChangeL_apply _ _ ⟨h₀, hz⟩,
    ← (trivializationAt F E i.1).symmL_apply (R := ℂ) hz, map_smul,
    (trivializationAt F E i.1).symmL_apply hz, (trivializationAt F E i.1).symm_apply_apply_mk hz,
    map_smul, ← Trivialization.continuousLinearMapAt_apply_of_mem ℂ _ hz',
    ← Trivialization.continuousLinearMapAt_apply_of_mem ℂ _ hz', map_smul]

end Bundle

section RealSmooth

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [NormedSpace ℝ F]
  [IsScalarTower ℝ ℂ F]
  {E : X → Type*} [∀ z, AddCommGroup (E z)] [∀ z, Module ℂ (E z)] [∀ z, Module ℝ (E z)]
  [∀ z, IsScalarTower ℝ ℂ (E z)] [∀ z, TopologicalSpace (E z)] [TopologicalSpace (TotalSpace F E)]
  [FiberBundle F E] [VectorBundle ℂ F E]
  {F' : Type*} [NormedAddCommGroup F'] [NormedSpace ℂ F'] [NormedSpace ℝ F']
  [IsScalarTower ℝ ℂ F']
  {E' : X → Type*} [∀ z, AddCommGroup (E' z)] [∀ z, Module ℂ (E' z)] [∀ z, Module ℝ (E' z)]
  [∀ z, IsScalarTower ℝ ℂ (E' z)] [∀ z, TopologicalSpace (E' z)]
  [TopologicalSpace (TotalSpace F' E')] [FiberBundle F' E'] [VectorBundle ℂ F' E']
  {n : ℕ∞ω}

local instance instVectorBundleRealPointTwistFunctor {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℂ F] [NormedSpace ℝ F] [IsScalarTower ℝ ℂ F] {E : X → Type*}
    [∀ z, AddCommGroup (E z)] [∀ z, Module ℂ (E z)] [∀ z, Module ℝ (E z)]
    [∀ z, IsScalarTower ℝ ℂ (E z)] [∀ z, TopologicalSpace (E z)]
    [TopologicalSpace (TotalSpace F E)] [FiberBundle F E] [VectorBundle ℂ F E] :
    VectorBundle ℝ F E :=
  VectorBundle.restrictScalars ℝ ℂ F E

/-- **The twisted isomorphism in coordinates.** Near every point `z₀`, the twisted isomorphism
read in the preferred charts of the twists at `z₀` is `e` read in the preferred charts of `E` and
`E'` at `z₀`, as real linear maps. -/
theorem inCoordinates_signedPointTwistEquiv (x : X) (s : Bool) (e : ∀ z, E z ≃L[ℂ] E' z)
    (z₀ : X) :
    ∀ᶠ z in 𝓝 z₀,
      ContinuousLinearMap.inCoordinates F (signedPointTwistCore F E x s).Fiber F'
          (signedPointTwistCore F' E' x s).Fiber z₀ z z₀ z
          ((signedPointTwistEquiv F F' x s e z).toContinuousLinearMap.restrictScalars ℝ) =
        ContinuousLinearMap.inCoordinates F E F' E' z₀ z z₀ z
          ((e z : E z →L[ℂ] E' z).restrictScalars ℝ) := by
  classical
  have h := (trivializationAt F (signedPointTwistCore F E x s).Fiber z₀).open_baseSet.inter
    (trivializationAt F' (signedPointTwistCore F' E' x s).Fiber z₀).open_baseSet
  filter_upwards [h.mem_nhds ⟨mem_baseSet_trivializationAt F _ z₀,
    mem_baseSet_trivializationAt F' _ z₀⟩] with z hz
  ext w
  simp only [ContinuousLinearMap.inCoordinates, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.coe_restrictScalars', ContinuousLinearEquiv.coe_coe]
  rw [Trivialization.symmL_apply _ hz.1,
    Trivialization.continuousLinearMapAt_apply_of_mem _ _ hz.2]
  rw [signedPointTwistCore_trivializationAt, signedPointTwistCore_trivializationAt] at hz ⊢
  have h₁ : z ∈ (trivializationAt F E z₀).baseSet :=
    (mem_signedPointTwistCore_baseSet.1 hz.1).1
  have h₂ : z ∈ (trivializationAt F' E' z₀).baseSet :=
    (mem_signedPointTwistCore_baseSet.1 hz.2).1
  rw [Trivialization.symmL_apply _ h₁, Trivialization.continuousLinearMapAt_apply_of_mem _ _ h₂]
  refine (signedPointTwistCore_localTriv_signedPointTwistEquiv (i := (z₀, decide (z₀ = x))) h₁ h₂
    e _).trans ?_
  rw [((signedPointTwistCore F E x s).localTriv _).apply_mk_symm hz.1 w]

variable [FiniteDimensional ℝ F]

/-- **Twisting preserves real-`C^n` bundle maps.** If a family of complex fibre isomorphisms
`e z : E z ≃L[ℂ] E' z` is real `C^n` on total spaces, so is the induced family of isomorphisms of
the signed point twists. -/
theorem contMDiff_signedPointTwistEquiv (x : X) (s : Bool) {e : ∀ z, E z ≃L[ℂ] E' z}
    (he : ContMDiff (𝓘(ℝ, ℂ).prod 𝓘(ℝ, F)) (𝓘(ℝ, ℂ).prod 𝓘(ℝ, F')) n
      fun p : TotalSpace F E ↦ TotalSpace.mk' F' p.proj (e p.proj p.snd)) :
    ContMDiff (𝓘(ℝ, ℂ).prod 𝓘(ℝ, F)) (𝓘(ℝ, ℂ).prod 𝓘(ℝ, F')) n
      fun p : TotalSpace F (signedPointTwistCore F E x s).Fiber ↦
        TotalSpace.mk' F' p.proj (signedPointTwistEquiv F F' x s e p.proj p.snd) := by
  have : ∀ z, IsTopologicalAddGroup (E' z) := VectorBundle.isTopologicalAddGroup ℝ F' E'
  have : ∀ z, ContinuousSMul ℝ (E' z) := VectorBundle.continuousSMul ℝ F' E'
  have : ∀ z, IsTopologicalAddGroup ((signedPointTwistCore F' E' x s).Fiber z) :=
    VectorBundle.isTopologicalAddGroup ℝ F' _
  have : ∀ z, ContinuousSMul ℝ ((signedPointTwistCore F' E' x s).Fiber z) :=
    VectorBundle.continuousSMul ℝ F' _
  have h := (contMDiff_hom_bundle_iff (IB := 𝓘(ℝ, ℂ)) (n := n)
    fun z ↦ (e z : E z →L[ℂ] E' z).restrictScalars ℝ).2 he
  refine (contMDiff_hom_bundle_iff (IB := 𝓘(ℝ, ℂ)) (n := n)
    (E₁ := (signedPointTwistCore F E x s).Fiber) (E₂ := (signedPointTwistCore F' E' x s).Fiber)
    fun z ↦ (signedPointTwistEquiv F F' x s e z).toContinuousLinearMap.restrictScalars ℝ).1
    fun z₀ ↦ ?_
  rw [contMDiffAt_hom_bundle]
  exact ⟨contMDiffAt_id, ((contMDiffAt_hom_bundle _).1 (h z₀)).2.congr_of_eventuallyEq
    (inCoordinates_signedPointTwistEquiv x s e z₀)⟩

variable [FiniteDimensional ℝ F'] (F F') in
/-- **Functoriality of point twists.** A complex bundle isomorphism `E ≅ E'` which is a real `C^n`
diffeomorphism of total spaces induces one `E(±x) ≅ E'(±x)` of the signed point twists. -/
def signedPointTwistDiffeomorph (x : X) (s : Bool) (e : ∀ z, E z ≃L[ℂ] E' z)
    (he : ContMDiff (𝓘(ℝ, ℂ).prod 𝓘(ℝ, F)) (𝓘(ℝ, ℂ).prod 𝓘(ℝ, F')) n
      fun p : TotalSpace F E ↦ TotalSpace.mk' F' p.proj (e p.proj p.snd)) :
    TotalSpace F (signedPointTwistCore F E x s).Fiber ≃ₘ^n⟮𝓘(ℝ, ℂ).prod 𝓘(ℝ, F),
      𝓘(ℝ, ℂ).prod 𝓘(ℝ, F')⟯ TotalSpace F' (signedPointTwistCore F' E' x s).Fiber :=
  bundleDiffeomorph (E₁ := (signedPointTwistCore F E x s).Fiber)
    (E₂ := (signedPointTwistCore F' E' x s).Fiber)
    -- The complex fibre isomorphisms, as real ones.
    (fun z ↦ { (signedPointTwistEquiv F F' x s e z).toLinearEquiv.restrictScalars ℝ with
      continuous_toFun := (signedPointTwistEquiv F F' x s e z).continuous
      continuous_invFun := (signedPointTwistEquiv F F' x s e z).symm.continuous })
    (by exact (contMDiff_signedPointTwistEquiv x s he).congr fun _ ↦ rfl)

@[simp] theorem signedPointTwistDiffeomorph_apply (x : X) (s : Bool) (e : ∀ z, E z ≃L[ℂ] E' z)
    (he : ContMDiff (𝓘(ℝ, ℂ).prod 𝓘(ℝ, F)) (𝓘(ℝ, ℂ).prod 𝓘(ℝ, F')) n
      fun p : TotalSpace F E ↦ TotalSpace.mk' F' p.proj (e p.proj p.snd))
    (p : TotalSpace F (signedPointTwistCore F E x s).Fiber) :
    signedPointTwistDiffeomorph F F' x s e he p =
      ⟨p.proj, signedPointTwistEquiv F F' x s e p.proj p.snd⟩ :=
  bundleDiffeomorph_apply _ _ p

end RealSmooth

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

theorem signedPointTwistCancelEquiv_apply (x : X) (s : Bool) (z : X) (v : F) :
    signedPointTwistCancelEquiv F E x s z v = (trivializationAt F E z).symm z v :=
  (rfl)

open Classical in
/-- **The cancellation isomorphism in coordinates.** In the preferred charts of the double twist
and of `E` at any point `a`, the cancellation isomorphism is the identity: the scalars of the two
opposite twists are inverse to each other. -/
theorem signedPointTwistCancelEquiv_coordinates {x a z : X} {s : Bool}
    (hz : z ∈ (trivializationAt F
      (signedPointTwistCore F (signedPointTwistCore F E x s).Fiber x (!s)).Fiber a).baseSet)
    (v : F) :
    (trivializationAt F E a ⟨z, signedPointTwistCancelEquiv F E x s z v⟩).2 =
      (trivializationAt F
        (signedPointTwistCore F (signedPointTwistCore F E x s).Fiber x (!s)).Fiber a ⟨z, v⟩).2 := by
  set T := signedPointTwistCore F E x s
  rw [signedPointTwistCore_trivializationAt] at hz ⊢
  -- The chart of `E(±x)` at `a` contains `z`, and so do the pieces of the cover at `a` and `z`.
  have hzT := (mem_signedPointTwistCore_baseSet.1 hz).1
  have hza : z ∈ T.baseSet (a, decide (a = x)) := by
    rwa [signedPointTwistCore_trivializationAt] at hzT
  have hzz := mem_pointTwistBaseSet_decide x z
  refine Eq.symm ((signedPointTwistCore_localTriv_apply (E := T.Fiber) x (!s)
    (a, decide (a = x)) z v).trans ?_)
  rw [T.trivializationAt_coordChange_eq ⟨mem_baseSet_trivializationAt F T.Fiber z, hzT⟩,
    signedPointTwistCore_indexAt, signedPointTwistCore_indexAt, signedPointTwistCore_coordChange]
  dsimp only
  rw [smul_apply, smul_smul, signedPointTwistFactor_not, signedPointTwistFactor_mul_swap hzz
    (mem_signedPointTwistCore_baseSet.1 hza).2, one_smul, ContinuousLinearEquiv.coe_coe,
    Trivialization.coordChangeL_apply _ _ ⟨mem_baseSet_trivializationAt F E z,
      (mem_signedPointTwistCore_baseSet.1 hza).1⟩, signedPointTwistCancelEquiv_apply]

variable {n : ℕ∞ω} [NormedSpace ℝ F]

variable (F E) in
/-- **Cancellation of opposite point twists.** The twist of `E(±x)` with the opposite sign is
isomorphic to `E`, by a `C^n` diffeomorphism of total spaces over the real manifold underlying `X`
whose fibre maps are the complex linear isomorphisms `signedPointTwistCancelEquiv`: in the preferred
charts it is the identity. This is `E(x)(-x) ≅ E` for `s = true` and `E(-x)(x) ≅ E` for
`s = false`. -/
def signedPointTwistCancelDiffeomorph (x : X) (s : Bool) :
    TotalSpace F (signedPointTwistCore F (signedPointTwistCore F E x s).Fiber x (!s)).Fiber
      ≃ₘ^n⟮𝓘(ℝ, ℂ).prod 𝓘(ℝ, F), 𝓘(ℝ, ℂ).prod 𝓘(ℝ, F)⟯ TotalSpace F E where
  toFun p := ⟨p.proj, signedPointTwistCancelEquiv F E x s p.proj p.snd⟩
  invFun p := ⟨p.proj, (signedPointTwistCancelEquiv F E x s p.proj).symm p.snd⟩
  left_inv p := by simp
  right_inv p := by simp
  contMDiff_toFun := contMDiff_bundleMap_of_constant_coordinates
    (fun z ↦ signedPointTwistCancelEquiv F E x s z) (ContinuousLinearMap.id ℝ F)
    fun _ _ hz v ↦ signedPointTwistCancelEquiv_coordinates hz.1 v
  contMDiff_invFun := contMDiff_bundleMap_of_constant_coordinates
    (fun z ↦ (signedPointTwistCancelEquiv F E x s z).symm) (ContinuousLinearMap.id ℝ F)
    fun _ z hz v ↦ by
      have h := signedPointTwistCancelEquiv_coordinates hz.2
        (show F from (signedPointTwistCancelEquiv F E x s z).symm v)
      rw [ContinuousLinearEquiv.apply_symm_apply] at h
      exact h.symm

@[simp] theorem signedPointTwistCancelDiffeomorph_apply (x : X) (s : Bool)
    (p : TotalSpace F (signedPointTwistCore F (signedPointTwistCore F E x s).Fiber x (!s)).Fiber) :
    signedPointTwistCancelDiffeomorph (n := n) F E x s p =
      ⟨p.proj, signedPointTwistCancelEquiv F E x s p.proj p.snd⟩ :=
  (rfl)

end Cancel

end TauCeti

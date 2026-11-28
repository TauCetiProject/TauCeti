/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Topology.ContinuousMap.Bounded.Normed

/-!
# Spaces of continuous `m`-jets

For real normed spaces `E` and `F`, a subset `K ⊆ E`, and an order `m : ℕ`,
`TauCeti.JetSpace E F K m` is the normed space of continuous `m`-jets on `K`, linearly isometric to
the finite product `Π k : Fin (m + 1), K →ᵇ (E [×k]→L[ℝ] F)` of bounded continuous multilinear-map
spaces up to order `m` with the product (sup) norm. It is complete whenever `F` is complete.

Every `C^m` function on an open neighbourhood of a compact set `K` defines an `m`-jet
`TauCeti.JetSpace.ofContDiffOn`.

## Main declarations

* `TauCeti.JetSpace`: the normed space of bounded continuous `m`-jets on `K`.
* `TauCeti.JetSpace.eval`, `TauCeti.JetSpace.evalEquiv`, `TauCeti.JetSpace.ext`,
  `TauCeti.JetSpace.norm_eval_le`, `TauCeti.JetSpace.norm_eval_apply_le`,
  `TauCeti.JetSpace.norm_le_iff`: evaluation, linear isometric equivalence with component
  functions, extensionality, and norm bounds.
* `TauCeti.JetSpace.ofContDiffOn`: the `m`-jet on a compact `K` of a `C^m` function on an open
  neighbourhood of `K`, with linearity.
-/

public section

noncomputable section

open ContDiff Filter Set TopologicalSpace Topology
open scoped BoundedContinuousFunction ContDiff

namespace TauCeti

variable (E F : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The normed space of bounded continuous `m`-jets on `K ⊆ E` with values in `F`, isomorphic to
`Π k : Fin (m + 1), K →ᵇ (E [×k]→L[ℝ] F)` with the sup norm. Its internal representation is hidden;
interact with elements through `JetSpace.eval`, `JetSpace.evalEquiv`, and
`JetSpace.ofContDiffOn`. -/
def JetSpace (K : Set E) (m : ℕ) : Type _ :=
  Π k : Fin (m + 1), K →ᵇ (E [×(k : ℕ)]→L[ℝ] F)

@[implicit_reducible]
def JetSpace.instNormedAddCommGroup (K : Set E) (m : ℕ) :
    NormedAddCommGroup (JetSpace E F K m) :=
  inferInstanceAs (NormedAddCommGroup (Π k : Fin (m + 1), K →ᵇ (E [×(k : ℕ)]→L[ℝ] F)))

attribute [instance] JetSpace.instNormedAddCommGroup

@[implicit_reducible]
def JetSpace.instNormedSpace (K : Set E) (m : ℕ) :
    NormedSpace ℝ (JetSpace E F K m) :=
  inferInstanceAs (NormedSpace ℝ (Π k : Fin (m + 1), K →ᵇ (E [×(k : ℕ)]→L[ℝ] F)))

attribute [instance] JetSpace.instNormedSpace

namespace JetSpace

variable {E F} {K : Set E} {m : ℕ}

/-- Evaluate a continuous `m`-jet at derivative order `k : Fin (m + 1)`. -/
def eval (J : JetSpace E F K m) (k : Fin (m + 1)) : K →ᵇ (E [×(k : ℕ)]→L[ℝ] F) :=
  J k

@[ext]
theorem ext {J₁ J₂ : JetSpace E F K m}
    (h : ∀ (k : Fin (m + 1)) (x : K), J₁.eval k x = J₂.eval k x) : J₁ = J₂ := by
  funext k
  exact BoundedContinuousFunction.ext (h k)

@[simp]
theorem eval_zero (k : Fin (m + 1)) : (0 : JetSpace E F K m).eval k = 0 := by rfl

@[simp]
theorem eval_add (J₁ J₂ : JetSpace E F K m) (k : Fin (m + 1)) :
    (J₁ + J₂).eval k = J₁.eval k + J₂.eval k := by rfl

@[simp]
theorem eval_neg (J : JetSpace E F K m) (k : Fin (m + 1)) : (-J).eval k = -J.eval k := by rfl

@[simp]
theorem eval_sub (J₁ J₂ : JetSpace E F K m) (k : Fin (m + 1)) :
    (J₁ - J₂).eval k = J₁.eval k - J₂.eval k := by rfl

@[simp]
theorem eval_smul (c : ℝ) (J : JetSpace E F K m) (k : Fin (m + 1)) :
    (c • J).eval k = c • J.eval k := by rfl

/-- Linear isometric equivalence between `JetSpace E F K m` and the finite product of bounded
continuous component spaces `Π k : Fin (m + 1), K →ᵇ (E [×k]→L[ℝ] F)`. -/
def evalEquiv :
    JetSpace E F K m ≃ₗᵢ[ℝ] Π k : Fin (m + 1), K →ᵇ (E [×(k : ℕ)]→L[ℝ] F) where
  toFun := eval
  invFun := id
  left_inv _ := by rfl
  right_inv _ := by rfl
  map_add' _ _ := by rfl
  map_smul' _ _ := by rfl
  norm_map' _ := by rfl

instance [CompleteSpace F] : CompleteSpace (JetSpace E F K m) :=
  (completeSpace_congr (e := evalEquiv.toEquiv)
    evalEquiv.isometry.isUniformEmbedding).2 inferInstance

@[simp]
theorem evalEquiv_apply (J : JetSpace E F K m) (k : Fin (m + 1)) :
    evalEquiv J k = J.eval k := by rfl

@[simp]
theorem eval_evalEquiv_symm (f : Π k : Fin (m + 1), K →ᵇ (E [×(k : ℕ)]→L[ℝ] F))
    (k : Fin (m + 1)) : (evalEquiv.symm f).eval k = f k := by rfl

/-- The norm of each order-`k` component of a jet is bounded by the norm of the jet. -/
theorem norm_eval_le (J : JetSpace E F K m) (k : Fin (m + 1)) : ‖J.eval k‖ ≤ ‖J‖ := by
  rw [← evalEquiv.norm_map J]
  exact norm_le_pi_norm (evalEquiv J) k

/-- A jet has norm at most `r` (for `r ≥ 0`) if and only if each of its components has norm at
most `r`. -/
theorem norm_le_iff {J : JetSpace E F K m} {r : ℝ} (hr : 0 ≤ r) :
    ‖J‖ ≤ r ↔ ∀ k : Fin (m + 1), ‖J.eval k‖ ≤ r := by
  rw [← evalEquiv.norm_map J]
  simpa using pi_norm_le_iff_of_nonneg (x := evalEquiv J) hr

/-- The norm of each pointwise derivative value of a jet is bounded by the norm of the jet. -/
theorem norm_eval_apply_le (J : JetSpace E F K m) (k : Fin (m + 1)) (x : K) :
    ‖J.eval k x‖ ≤ ‖J‖ :=
  (BoundedContinuousFunction.norm_coe_le_norm (J.eval k) x).trans (J.norm_eval_le k)

private theorem coe_fin_le {m : ℕ} (k : Fin (m + 1)) :
    ((k : ℕ) : WithTop ℕ∞) ≤ (m : WithTop ℕ∞) := mod_cast k.is_le

/-- The `m`-jet on a compact set `K` of a function `g : E → F` that is `C^m` on an open
neighbourhood `U` of `K`. -/
def ofContDiffOn {U : Set E} (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U) (m : ℕ)
    {g : E → F} (hg : ContDiffOn ℝ m g U) : JetSpace E F K m :=
  fun k ↦ by
    haveI : CompactSpace K := isCompact_iff_compactSpace.1 hK
    have hcont : ContinuousOn (iteratedFDeriv ℝ (k : ℕ) g) U :=
      (hg.continuousOn_iteratedFDerivWithin (coe_fin_le k) hU.uniqueDiffOn).congr fun y hy ↦
        (iteratedFDerivWithin_of_isOpen (k : ℕ) hU hy).symm
    exact BoundedContinuousFunction.mkOfCompact
      ⟨fun x : K ↦ iteratedFDeriv ℝ (k : ℕ) g x.val,
        (hcont.mono hKU).comp_continuous continuous_subtypeVal fun x ↦ x.property⟩

@[simp]
theorem eval_ofContDiffOn {U : Set E} (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U) (m : ℕ)
    {g : E → F} (hg : ContDiffOn ℝ m g U) (k : Fin (m + 1)) (x : K) :
    (ofContDiffOn hK hU hKU m hg).eval k x = iteratedFDeriv ℝ (k : ℕ) g x.val := by rfl

/-- Two `C^m` functions on possibly different open neighbourhoods of `K` that agree near `K`
define the same `m`-jet on `K`. -/
theorem ofContDiffOn_congr {U₁ U₂ : Set E} {hK : IsCompact K} {hU₁ : IsOpen U₁} {hKU₁ : K ⊆ U₁}
    {hU₂ : IsOpen U₂} {hKU₂ : K ⊆ U₂} {m : ℕ} {g₁ g₂ : E → F}
    (hg₁ : ContDiffOn ℝ m g₁ U₁) (hg₂ : ContDiffOn ℝ m g₂ U₂) (h : g₁ =ᶠ[𝓝ˢ K] g₂) :
    ofContDiffOn hK hU₁ hKU₁ m hg₁ = ofContDiffOn hK hU₂ hKU₂ m hg₂ :=
  ext fun k x ↦ by
    simp only [eval_ofContDiffOn]
    exact ((h.filter_mono (nhds_le_nhdsSet x.property)).iteratedFDeriv (𝕜 := ℝ) (k : ℕ)).eq_of_nhds

/-- The `m`-jet of the zero function vanishes. -/
@[simp]
theorem ofContDiffOn_zero {U : Set E} (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U) (m : ℕ) :
    ofContDiffOn hK hU hKU m (contDiffOn_const (c := (0 : F))) = 0 :=
  ext fun _ _ ↦ by simp

/-- Taking `m`-jets is additive on `C^m` functions. -/
@[simp]
theorem ofContDiffOn_add {U : Set E} (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U) (m : ℕ)
    {g₁ g₂ : E → F} (hg₁ : ContDiffOn ℝ m g₁ U) (hg₂ : ContDiffOn ℝ m g₂ U) :
    ofContDiffOn hK hU hKU m (hg₁.add hg₂) =
      ofContDiffOn hK hU hKU m hg₁ + ofContDiffOn hK hU hKU m hg₂ :=
  ext fun k x ↦ by
    simp only [eval_ofContDiffOn, eval_add, FunLike.coe_add, Pi.add_apply]
    exact iteratedFDeriv_add_apply
      ((hg₁.contDiffAt (hU.mem_nhds (hKU x.property))).of_le (coe_fin_le k))
      ((hg₂.contDiffAt (hU.mem_nhds (hKU x.property))).of_le (coe_fin_le k))

/-- Taking `m`-jets commutes with scalar multiplication on `C^m` functions. -/
@[simp]
theorem ofContDiffOn_smul {U : Set E} (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U) (m : ℕ)
    (c : ℝ) {g : E → F} (hg : ContDiffOn ℝ m g U) :
    ofContDiffOn hK hU hKU m (hg.const_smul c) = c • ofContDiffOn hK hU hKU m hg :=
  ext fun k x ↦ by
    simp only [eval_ofContDiffOn, eval_smul, FunLike.coe_smul, Pi.smul_apply]
    exact iteratedFDeriv_const_smul_apply
      ((hg.contDiffAt (hU.mem_nhds (hKU x.property))).of_le (coe_fin_le k))

end JetSpace

end TauCeti

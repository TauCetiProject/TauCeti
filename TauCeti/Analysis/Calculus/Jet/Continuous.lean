/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Topology.ContinuousMap.Bounded.Normed
import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps

/-!
# Spaces of continuous `m`-jets

For real normed spaces `E` and `F`, a subset `K ⊆ E`, and an order `m : ℕ`,
`TauCeti.JetSpace E F K m` is the normed space of continuous `m`-jets on `K`, realized as the
finite product `Π k : Fin (m + 1), K →ᵇ (E [×k]→L[ℝ] F)` of bounded continuous multilinear-map
spaces up to order `m` with the product (sup) norm. It is complete whenever `F` is complete.

Every `C^m` function on an open neighbourhood of a compact set `K` defines an `m`-jet
`TauCeti.JetSpace.ofContDiffOn`.

## Main declarations

* `TauCeti.JetSpace`: the normed space of bounded continuous `m`-jets on `K`.
* `TauCeti.JetSpace.eval`, `TauCeti.JetSpace.ext`, `TauCeti.JetSpace.norm_eval_le`,
  `TauCeti.JetSpace.norm_eval_apply_le`: evaluation, extensionality, and norm bounds.
* `TauCeti.JetSpace.ofContDiffOn`: the `m`-jet on a compact `K` of a `C^m` function on an open
  neighbourhood of `K`, with linearity and germ invariance.
-/

public section

noncomputable section

open ContDiff Filter Set TopologicalSpace Topology
open scoped BoundedContinuousFunction ContDiff

namespace TauCeti

variable (E F : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The normed space of bounded continuous `m`-jets on `K ⊆ E` with values in `F`, realized as the
finite product `Π k : Fin (m + 1), K →ᵇ (E [×k]→L[ℝ] F)` with the sup norm. Defined as a `def`
rather than an `abbrev` so that topological and algebraic instances resolve through
`NormedAddCommGroup` and `NormedSpace` without competing `Pi` topologies. -/
@[expose] def JetSpace (K : Set E) (m : ℕ) : Type _ :=
  Π k : Fin (m + 1), K →ᵇ (E [×(k : ℕ)]→L[ℝ] F)

instance (K : Set E) (m : ℕ) : NormedAddCommGroup (JetSpace E F K m) :=
  Pi.normedAddCommGroup

instance (K : Set E) (m : ℕ) : NormedSpace ℝ (JetSpace E F K m) :=
  Pi.normedSpace

instance [CompleteSpace F] (K : Set E) (m : ℕ) : CompleteSpace (JetSpace E F K m) :=
  inferInstanceAs (CompleteSpace (Π k : Fin (m + 1), K →ᵇ (E [×(k : ℕ)]→L[ℝ] F)))

namespace JetSpace

variable {E F} {K : Set E} {m : ℕ}

/-- Evaluate a continuous `m`-jet at derivative order `k : Fin (m + 1)`. -/
@[expose] def eval (J : JetSpace E F K m) (k : Fin (m + 1)) : K →ᵇ (E [×(k : ℕ)]→L[ℝ] F) :=
  J k

@[ext]
theorem ext {J₁ J₂ : JetSpace E F K m}
    (h : ∀ (k : Fin (m + 1)) (x : K), J₁.eval k x = J₂.eval k x) : J₁ = J₂ := by
  funext k
  exact BoundedContinuousFunction.ext (h k)

@[simp]
theorem eval_zero (k : Fin (m + 1)) : (0 : JetSpace E F K m).eval k = 0 := by
  rfl

@[simp]
theorem eval_add (J₁ J₂ : JetSpace E F K m) (k : Fin (m + 1)) :
    (J₁ + J₂).eval k = J₁.eval k + J₂.eval k := by
  rfl

@[simp]
theorem eval_neg (J : JetSpace E F K m) (k : Fin (m + 1)) :
    (-J).eval k = -J.eval k := by
  rfl

@[simp]
theorem eval_sub (J₁ J₂ : JetSpace E F K m) (k : Fin (m + 1)) :
    (J₁ - J₂).eval k = J₁.eval k - J₂.eval k := by
  rfl

@[simp]
theorem eval_smul (c : ℝ) (J : JetSpace E F K m) (k : Fin (m + 1)) :
    (c • J).eval k = c • J.eval k := by
  rfl

/-- The norm of each order-`k` component of a jet is bounded by the norm of the jet. -/
theorem norm_eval_le (J : JetSpace E F K m) (k : Fin (m + 1)) : ‖J.eval k‖ ≤ ‖J‖ :=
  norm_le_pi_norm (J : Π i : Fin (m + 1), K →ᵇ (E [×(i : ℕ)]→L[ℝ] F)) k

/-- The norm of each pointwise derivative value of a jet is bounded by the norm of the jet. -/
theorem norm_eval_apply_le (J : JetSpace E F K m) (k : Fin (m + 1)) (x : K) :
    ‖J.eval k x‖ ≤ ‖J‖ :=
  (BoundedContinuousFunction.norm_coe_le_norm (J.eval k) x).trans (J.norm_eval_le k)

/-- The `m`-jet on a compact set `K` of a function `g : E → F` that is `C^m` on an open
neighbourhood `U` of `K`. -/
def ofContDiffOn {U : Set E} (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U) (m : ℕ)
    {g : E → F} (hg : ContDiffOn ℝ m g U) : JetSpace E F K m :=
  fun k ↦ by
    haveI : CompactSpace K := isCompact_iff_compactSpace.1 hK
    have hk : ((k : ℕ) : WithTop ℕ∞) ≤ (m : WithTop ℕ∞) := by
      exact_mod_cast Nat.le_of_lt_succ k.isLt
    have hcont : ContinuousOn (iteratedFDeriv ℝ (k : ℕ) g) U :=
      (hg.continuousOn_iteratedFDerivWithin hk hU.uniqueDiffOn).congr fun y hy ↦
        (iteratedFDerivWithin_of_isOpen (k : ℕ) hU hy).symm
    exact BoundedContinuousFunction.mkOfCompact
      ⟨fun x : K ↦ iteratedFDeriv ℝ (k : ℕ) g x.val,
        (hcont.mono hKU).comp_continuous continuous_subtypeVal fun x ↦ x.property⟩

@[simp]
theorem eval_ofContDiffOn {U : Set E} (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U) (m : ℕ)
    {g : E → F} (hg : ContDiffOn ℝ m g U) (k : Fin (m + 1)) (x : K) :
    (ofContDiffOn hK hU hKU m hg).eval k x = iteratedFDeriv ℝ (k : ℕ) g x.val := by
  rfl

/-- The `m`-jet of the zero function vanishes. -/
theorem ofContDiffOn_zero {U : Set E} (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U) (m : ℕ) :
    ofContDiffOn hK hU hKU m (contDiffOn_const (c := (0 : F))) = 0 :=
  ext fun k x ↦ by simp

/-- Taking `m`-jets is additive on `C^m` functions. -/
theorem ofContDiffOn_add {U : Set E} (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U) (m : ℕ)
    {g₁ g₂ : E → F} (hg₁ : ContDiffOn ℝ m g₁ U) (hg₂ : ContDiffOn ℝ m g₂ U) :
    ofContDiffOn hK hU hKU m (hg₁.add hg₂) =
      ofContDiffOn hK hU hKU m hg₁ + ofContDiffOn hK hU hKU m hg₂ :=
  ext fun k x ↦ by
    have hk : ((k : ℕ) : WithTop ℕ∞) ≤ (m : WithTop ℕ∞) := by
      exact_mod_cast Nat.le_of_lt_succ k.isLt
    simp only [eval_ofContDiffOn, eval_add, FunLike.coe_add, Pi.add_apply]
    exact iteratedFDeriv_add_apply
      ((hg₁ x.val (hKU x.property)).contDiffAt (hU.mem_nhds (hKU x.property)) |>.of_le hk)
      ((hg₂ x.val (hKU x.property)).contDiffAt (hU.mem_nhds (hKU x.property)) |>.of_le hk)

/-- Taking `m`-jets commutes with scalar multiplication on `C^m` functions. -/
theorem ofContDiffOn_smul {U : Set E} (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U) (m : ℕ)
    (c : ℝ) {g : E → F} (hg : ContDiffOn ℝ m g U) :
    ofContDiffOn hK hU hKU m (hg.const_smul c) = c • ofContDiffOn hK hU hKU m hg :=
  ext fun k x ↦ by
    have hk : ((k : ℕ) : WithTop ℕ∞) ≤ (m : WithTop ℕ∞) := by
      exact_mod_cast Nat.le_of_lt_succ k.isLt
    simp only [eval_ofContDiffOn, eval_smul, FunLike.coe_smul, Pi.smul_apply]
    exact iteratedFDeriv_const_smul_apply
      ((hg x.val (hKU x.property)).contDiffAt (hU.mem_nhds (hKU x.property)) |>.of_le hk)

/-- Two `C^m` functions that agree on a neighbourhood of `K` have the same `m`-jet on `K`. -/
theorem ofContDiffOn_eq_of_eventuallyEq {U₁ U₂ : Set E} (hK : IsCompact K) (hU₁ : IsOpen U₁)
    (hKU₁ : K ⊆ U₁) (hU₂ : IsOpen U₂) (hKU₂ : K ⊆ U₂) (m : ℕ) {g₁ g₂ : E → F}
    (hg₁ : ContDiffOn ℝ m g₁ U₁) (hg₂ : ContDiffOn ℝ m g₂ U₂) (h : g₁ =ᶠ[𝓝ˢ K] g₂) :
    ofContDiffOn hK hU₁ hKU₁ m hg₁ = ofContDiffOn hK hU₂ hKU₂ m hg₂ :=
  ext fun k x ↦ by
    simp only [eval_ofContDiffOn]
    exact ((h.filter_mono (nhds_le_nhdsSet x.property)).iteratedFDeriv (𝕜 := ℝ) (k : ℕ)).eq_of_nhds

end JetSpace

end TauCeti

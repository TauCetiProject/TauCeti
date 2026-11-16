/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Holder.Iterated
public import Mathlib.Topology.Sets.Opens
import Mathlib.Algebra.Group.Action.Pi
import Mathlib.Algebra.Group.Pi.Basic
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.Comp
import TauCeti.Analysis.Calculus.UniformLimitsDeriv
import TauCeti.Topology.MetricSpace.Holder

/-!
# Bounded `C^{k,α}` spaces on open sets

This file constructs, for every `k : ℕ`, `α : ℝ≥0`, and open subset `Ω : TopologicalSpace.Opens E`
of a real normed space `E`, the normed space `C^{k,α}(Ω, F)` (`TauCeti.CkHolderOnSpace k α Ω F`) of
`C^k` maps on `Ω` whose iterated Fréchet derivatives through order `k` are bounded on `Ω` and whose
`k`-th iterated derivative has finite `α`-Hölder seminorm on `Ω`, equipped with the sum norm

`‖f‖ = ∑_{i ≤ k} sup_{x ∈ Ω} ‖D^i f(x)‖ + [D^k f]_{α; Ω}`.

When the codomain `F` is a Banach space, `CkHolderOnSpace k α Ω F` is a Banach space.

An element is represented by its jet on `Ω`, adapting the derivative-graph construction of
`TauCeti.CkHolderSpace` to an open domain: bounded continuous fields `Ω →ᵇ (E [×i]→L[ℝ] F)` for
`i < k` with the `ℓ¹` norm, together with a bounded Hölder field `HolderSpace α Ω (E [×k]→L[ℝ] F)`
of order `k`, subject to the derivative identity that the zero-extension of each field below order
`k` has the next field, curried on the left, as its Fréchet derivative at every point of `Ω`. Since
`Ω` is open, `HasFDerivAt` at `x ∈ Ω` depends only on the germ at `x`, so extending by zero outside
`Ω` records genuine interior Fréchet differentiability without imposing any boundary condition.
Uniform convergence on `Ω` preserves these identities by
`TauCeti.isClosed_setOf_hasFDerivAt_extend_comp`, yielding completeness.

## Main declarations

* `TauCeti.CkHolderOnSpace k α Ω F`: bounded `C^k` maps on an open set `Ω` with bounded iterated
  derivatives through order `k` and `α`-Hölder `k`-th derivative on `Ω`.
* `TauCeti.CkHolderOnSpace.iteratedFDeriv` and `TauCeti.CkHolderOnSpace.iteratedFDerivHolder`: the
  bounded continuous `i`-th derivative field on `Ω` for `i ≤ k`, and the `k`-th derivative field in
  `HolderSpace α Ω (E [×k]→L[ℝ] F)`.
* `TauCeti.CkHolderOnSpace.extendByZero`, `TauCeti.CkHolderOnSpace.contDiffOn_extendByZero`, and
  `TauCeti.CkHolderOnSpace.iteratedFDeriv_extendByZero`: extension by zero outside `Ω`, its `C^k`
  regularity on `Ω`, and agreement of its iterated Fréchet derivatives on `Ω` with the jet fields.
* `TauCeti.CkHolderOnSpace.ofContDiffOn`: constructor from an ambient map `g : E → F` that is `C^k`
  on `Ω` with bounded derivatives through order `k` and `α`-Hölder `k`-th derivative on `Ω`.
* `TauCeti.CkHolderOnSpace.norm_eq` and
  `TauCeti.CkHolderOnSpace.norm_le_of_norm_iteratedFDeriv_le_of_holderOnWith`: explicit formula and
  upper bound for the `C^{k,α}(Ω)` norm.
* `TauCeti.CkHolderOnSpace.instCompleteSpace`: completeness when `F` is complete.
* `TauCeti.CkHolderOnSpace.equivHolderSpace` and `TauCeti.CkHolderOnSpace.equivTop`: linear
  isometric equivalences `CkHolderOnSpace 0 α Ω F ≃ₗᵢ[ℝ] HolderSpace α Ω F` and
  `CkHolderOnSpace k α ⊤ F ≃ₗᵢ[ℝ] CkHolderSpace k α E F`.

## References

* D. Gilbarg and N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Section 4.1.
-/

public section

noncomputable section

namespace TauCeti

open Filter Set Topology
open scoped NNReal BoundedContinuousFunction

universe u v

variable (k : ℕ) (α : ℝ≥0) {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
  (Ω : TopologicalSpace.Opens E) (F : Type v) [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Local shortcut instance for bounded continuous fields of `n`-multilinear maps on `Ω`, avoiding
instance-search depth blowup in `ℓ¹` products indexed by the derivative order `n`. -/
local instance CkHolderOnSpace.instNormedAddCommGroupBoundedContinuousFunction (n : ℕ) :
    NormedAddCommGroup (Ω →ᵇ (E [×n]→L[ℝ] F)) :=
  inferInstance

/-- Local shortcut instance for the real normed-space structure on bounded continuous fields of
`n`-multilinear maps on `Ω`. -/
local instance CkHolderOnSpace.instNormedSpaceBoundedContinuousFunction (n : ℕ) :
    NormedSpace ℝ (Ω →ᵇ (E [×n]→L[ℝ] F)) :=
  inferInstance

/-- The space `C^{k,α}(Ω, F)` of `C^k` maps on an open subset `Ω` of `E` whose iterated Fréchet
derivatives through order `k` are bounded on `Ω` and whose `k`-th iterated derivative has finite
`α`-Hölder seminorm on `Ω`, equipped with the norm

`∑_{i ≤ k} sup_{x ∈ Ω} ‖D^i f(x)‖ + [D^k f]_{α; Ω}`.
-/
-- The module system requires exposure while the declarations below construct and project through
-- this graph alias. The final `irreducible` attribute restores the abstraction boundary.
@[expose] def CkHolderOnSpace : Type _ :=
  let field (i : Fin (k + 1)) :
      WithLp 1 ((PiLp 1 fun i : Fin k ↦ Ω →ᵇ (E [×i]→L[ℝ] F)) ×
        HolderSpace α Ω (E [×k]→L[ℝ] F)) →L[ℝ] (Ω →ᵇ (E [×i]→L[ℝ] F)) :=
    Fin.lastCases (motive := fun i : Fin (k + 1) ↦ WithLp 1
        ((PiLp 1 fun i : Fin k ↦ Ω →ᵇ (E [×i]→L[ℝ] F)) ×
          HolderSpace α Ω (E [×k]→L[ℝ] F)) →L[ℝ] (Ω →ᵇ (E [×i]→L[ℝ] F)))
      (HolderSpace.toBoundedContinuousFunctionCLM.comp (WithLp.sndL 1 ℝ _ _))
      (fun j ↦ (PiLp.proj 1 _ j).comp (WithLp.fstL 1 ℝ _ _)) i
  let graph : Submodule ℝ (WithLp 1 ((PiLp 1 fun i : Fin k ↦ Ω →ᵇ (E [×i]→L[ℝ] F)) ×
      HolderSpace α Ω (E [×k]→L[ℝ] F))) :=
    { carrier := {J | ∀ (j : Fin k) (x : Ω),
        HasFDerivAt (Function.extend Subtype.val (field j.castSucc J : Ω → E [×j]→L[ℝ] F) 0)
          (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (j + 1) ↦ E) F
            (field j.succ J x)) x}
      zero_mem' := fun j x ↦ by
        simp only [map_zero, FunLike.coe_zero, Function.extend_zero, Pi.zero_apply]
        exact hasFDerivAt_const (x := (x : E)) (c := (0 : E [×j]→L[ℝ] F))
      add_mem' := fun {J K} hJ hK j x ↦ by
        have hadd : Function.extend Subtype.val (field j.castSucc (J + K) : Ω → E [×j]→L[ℝ] F) 0 =
            Function.extend Subtype.val (field j.castSucc J : Ω → E [×j]→L[ℝ] F) 0 +
              Function.extend Subtype.val (field j.castSucc K : Ω → E [×j]→L[ℝ] F) 0 := by
          rw [map_add, FunLike.coe_add, ← Function.extend_add, add_zero]
        rw [hadd, map_add, _root_.add_apply, map_add]
        exact (hJ j x).add (hK j x)
      smul_mem' := fun c {J} hJ j x ↦ by
        have hsmul : Function.extend Subtype.val
            (field j.castSucc (c • J) : Ω → E [×j]→L[ℝ] F) 0 =
            c • Function.extend Subtype.val (field j.castSucc J : Ω → E [×j]→L[ℝ] F) 0 := by
          rw [map_smul, FunLike.coe_smul, ← Function.extend_smul, smul_zero]
        rw [hsmul, map_smul, _root_.smul_apply, map_smul]
        exact (hJ j x).const_smul c }
  graph

namespace CkHolderOnSpace

variable {k α Ω F}

variable (k α Ω F) in
/-- Ambient jet space on `Ω`: bounded continuous derivative fields below order `k` with the `ℓ¹`
norm, together with a bounded Hölder field of order `k` on `Ω`. -/
private abbrev Jet := WithLp 1
  ((PiLp 1 fun i : Fin k ↦ Ω →ᵇ (E [×i]→L[ℝ] F)) × HolderSpace α Ω (E [×k]→L[ℝ] F))

private def fieldL (i : Fin (k + 1)) : Jet k α Ω F →L[ℝ] (Ω →ᵇ (E [×i]→L[ℝ] F)) :=
  Fin.lastCases (motive := fun i : Fin (k + 1) ↦ Jet k α Ω F →L[ℝ] (Ω →ᵇ (E [×i]→L[ℝ] F)))
    (HolderSpace.toBoundedContinuousFunctionCLM.comp (WithLp.sndL 1 ℝ _ _))
    (fun j ↦ (PiLp.proj 1 _ j).comp (WithLp.fstL 1 ℝ _ _)) i

private theorem fieldL_castSucc (j : Fin k) (J : Jet k α Ω F) :
    fieldL j.castSucc J = J.ofLp.1 j :=
  congrArg (· J) (Fin.lastCases_castSucc (motive := fun i : Fin (k + 1) ↦
    Jet k α Ω F →L[ℝ] (Ω →ᵇ (E [×i]→L[ℝ] F))) j)

private theorem fieldL_last (J : Jet k α Ω F) :
    fieldL (Fin.last k) J = J.ofLp.2.toBoundedContinuousFunction :=
  (congrArg (· J) (Fin.lastCases_last (motive := fun i : Fin (k + 1) ↦
    Jet k α Ω F →L[ℝ] (Ω →ᵇ (E [×i]→L[ℝ] F)))
    (last := HolderSpace.toBoundedContinuousFunctionCLM.comp (WithLp.sndL 1 ℝ _ _))
    (cast := fun j ↦ (PiLp.proj 1 _ j).comp (WithLp.fstL 1 ℝ _ _)))).trans (by simp)

private def IsJetGraph (J : Jet k α Ω F) : Prop :=
  ∀ (j : Fin k) (x : Ω),
    HasFDerivAt (Function.extend Subtype.val (fieldL j.castSucc J : Ω → E [×j]→L[ℝ] F) 0)
      (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (j + 1) ↦ E) F
        (fieldL j.succ J x)) x

private def equivSubtype : CkHolderOnSpace k α Ω F ≃ {J : Jet k α Ω F // IsJetGraph J} :=
  Equiv.refl _

private def toJet (f : CkHolderOnSpace k α Ω F) : Jet k α Ω F := (equivSubtype f).1

private def mk (J : Jet k α Ω F) (hJ : IsJetGraph J) : CkHolderOnSpace k α Ω F :=
  equivSubtype.symm ⟨J, hJ⟩

private theorem toJet_injective : Function.Injective (toJet (k := k) (α := α) (Ω := Ω) (F := F)) :=
  fun _ _ h ↦ equivSubtype.injective (Subtype.ext h)

private theorem toJet_mk (J : Jet k α Ω F) (hJ) : toJet (mk J hJ) = J := by
  rw [toJet, mk, Equiv.apply_symm_apply]

private theorem hasFDerivAt_fieldL (f : CkHolderOnSpace k α Ω F) (j : Fin k) (x : Ω) :
    HasFDerivAt (Function.extend Subtype.val
        (fieldL j.castSucc (toJet f) : Ω → E [×j]→L[ℝ] F) 0)
      (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (j + 1) ↦ E) F
        (fieldL j.succ (toJet f) x)) x :=
  (equivSubtype f).2 j x

/-- The `C^{k,α}(Ω)` norm makes `CkHolderOnSpace k α Ω F` a normed additive commutative group. -/
instance instNormedAddCommGroup : NormedAddCommGroup (CkHolderOnSpace k α Ω F) := by
  unfold CkHolderOnSpace; infer_instance

/-- The space `CkHolderOnSpace k α Ω F` is a real normed space. -/
instance instNormedSpace : NormedSpace ℝ (CkHolderOnSpace k α Ω F) := by
  unfold CkHolderOnSpace; infer_instance

private theorem norm_toJet (f : CkHolderOnSpace k α Ω F) : ‖toJet f‖ = ‖f‖ := Submodule.norm_coe f

private def toJetL : CkHolderOnSpace k α Ω F →L[ℝ] Jet k α Ω F := by
  unfold CkHolderOnSpace; exact Submodule.subtypeL _

private theorem toJetL_apply (f : CkHolderOnSpace k α Ω F) : toJetL f = toJet f := (rfl)

/-- The bounded continuous `i`-th derivative field on `Ω` for `i ≤ k`. -/
def iteratedFDeriv (f : CkHolderOnSpace k α Ω F) (i : Fin (k + 1)) : Ω →ᵇ (E [×i]→L[ℝ] F) :=
  fieldL i (toJet f)

/-- The `k`-th derivative field on `Ω` as an element of `HolderSpace α Ω (E [×k]→L[ℝ] F)`. -/
def iteratedFDerivHolder (f : CkHolderOnSpace k α Ω F) : HolderSpace α Ω (E [×k]→L[ℝ] F) :=
  (toJet f).ofLp.2

/-- Underlying function on `Ω` of an element of `CkHolderOnSpace k α Ω F`. Prefer `⇑f`. -/
def toFun (f : CkHolderOnSpace k α Ω F) (x : Ω) : F :=
  (f.iteratedFDeriv ⟨0, k.succ_pos⟩ x).curry0

/-- Extension of `f` by `0` outside `Ω`; on `Ω` its derivatives match `f.iteratedFDeriv`. -/
def extendByZero (f : CkHolderOnSpace k α Ω F) : E → F := Function.extend Subtype.val f.toFun 0

private def series (f : CkHolderOnSpace k α Ω F) (x : E) : FormalMultilinearSeries ℝ E F :=
  fun m ↦ if h : m < k + 1 then
    Function.extend Subtype.val (f.iteratedFDeriv ⟨m, h⟩ : Ω → E [×m]→L[ℝ] F) 0 x
  else 0

private theorem series_of_lt (f : CkHolderOnSpace k α Ω F) (x : E) {m : ℕ} (h : m < k + 1) :
    series f x m =
      Function.extend Subtype.val (f.iteratedFDeriv ⟨m, h⟩ : Ω → E [×m]→L[ℝ] F) 0 x := by
  simp [series, h]

private theorem series_coe_of_lt (f : CkHolderOnSpace k α Ω F) (x : Ω) {m : ℕ} (h : m < k + 1) :
    series f x m = f.iteratedFDeriv ⟨m, h⟩ x := by
  rw [series_of_lt f x h]
  exact Subtype.val_injective.extend_apply _ (0 : E → E [×m]→L[ℝ] F) x

private theorem hasFTaylorSeriesUpToOn (f : CkHolderOnSpace k α Ω F) :
    HasFTaylorSeriesUpToOn k f.extendByZero (series f) (Ω : Set E) where
  zero_eq x hx := by
    rw [series_coe_of_lt f ⟨x, hx⟩ k.succ_pos, extendByZero,
      Subtype.val_injective.extend_apply f.toFun (0 : E → F) ⟨x, hx⟩, toFun]
  fderivWithin m hm x hx := by
    have hmk : m < k := by exact_mod_cast hm
    have hfun : (fun y ↦ series f y m) =
        Function.extend Subtype.val (fieldL (⟨m, hmk⟩ : Fin k).castSucc (toJet f) : _) 0 :=
      funext fun y ↦ series_of_lt f y (by omega)
    have hcurry (g : E [×m + 1]→L[ℝ] F) :
        continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (m + 1) ↦ E) F g = g.curryLeft := by
      ext; simp
    rw [hfun, series_coe_of_lt f ⟨x, hx⟩ (by omega), ← hcurry]
    exact (hasFDerivAt_fieldL f ⟨m, hmk⟩ ⟨x, hx⟩).hasFDerivWithinAt
  cont m hm := by
    have hmk : m < k + 1 := Nat.lt_succ_of_le (by exact_mod_cast hm)
    rw [continuousOn_iff_continuous_domRestrict]
    have hres : (Ω : Set E).domRestrict (fun y ↦ series f y m) =
        (f.iteratedFDeriv ⟨m, hmk⟩ : Ω → E [×m]→L[ℝ] F) :=
      funext fun y ↦ series_coe_of_lt f y hmk
    rw [hres]
    exact (f.iteratedFDeriv ⟨m, hmk⟩).continuous

/-- On `Ω`, the `i`-th iterated Fréchet derivative of `f.extendByZero` is `f.iteratedFDeriv i`. -/
theorem iteratedFDeriv_extendByZero (f : CkHolderOnSpace k α Ω F) (i : Fin (k + 1)) (x : Ω) :
    _root_.iteratedFDeriv ℝ i f.extendByZero x = f.iteratedFDeriv i x := by
  rw [← iteratedFDerivWithin_of_isOpen i Ω.isOpen x.2,
    ← (hasFTaylorSeriesUpToOn f).eq_iteratedFDerivWithin_of_uniqueDiffOn
      (by exact_mod_cast i.is_le) Ω.isOpen.uniqueDiffOn x.2,
    series_coe_of_lt f x i.2]

/-- An element of `CkHolderOnSpace k α Ω F` is determined by its underlying function on `Ω`. -/
theorem toFun_injective : Function.Injective (toFun (k := k) (α := α) (Ω := Ω) (F := F)) := by
  intro f g hfg
  have hext : f.extendByZero = g.extendByZero := by rw [extendByZero, extendByZero, hfg]
  have hfield : ∀ i, f.iteratedFDeriv i = g.iteratedFDeriv i := fun i ↦ by
    ext1 x; rw [← iteratedFDeriv_extendByZero, ← iteratedFDeriv_extendByZero, hext]
  refine toJet_injective (WithLp.ofLp_injective 1 (Prod.ext ?_ ?_))
  · refine WithLp.ofLp_injective 1 (funext fun j ↦ ?_)
    have := hfield j.castSucc
    rwa [iteratedFDeriv, iteratedFDeriv, fieldL_castSucc, fieldL_castSucc] at this
  · refine HolderSpace.ext fun x ↦ ?_
    have := DFunLike.congr_fun (hfield (Fin.last k)) x
    rwa [iteratedFDeriv, iteratedFDeriv, fieldL_last, fieldL_last,
      HolderSpace.toBoundedContinuousFunction_apply,
      HolderSpace.toBoundedContinuousFunction_apply] at this

/-- An element of `CkHolderOnSpace k α Ω F` coerces to its underlying function `Ω → F`. -/
instance instFunLike : FunLike (CkHolderOnSpace k α Ω F) Ω F where
  coe := toFun
  coe_injective := toFun_injective

/-- `CkHolderOnSpace.toFun f` agrees with the coercion `⇑f`. -/
@[simp] theorem toFun_eq_coe (f : CkHolderOnSpace k α Ω F) : f.toFun = ⇑f := (rfl)

/-- Two elements of `CkHolderOnSpace k α Ω F` are equal when they agree at every point of `Ω`. -/
@[ext] theorem ext {f g : CkHolderOnSpace k α Ω F} (h : ∀ x : Ω, f x = g x) : f = g :=
  DFunLike.ext f g h

/-- On `Ω`, `f.extendByZero` agrees with `f`. -/
@[simp] theorem extendByZero_coe (f : CkHolderOnSpace k α Ω F) (x : Ω) : f.extendByZero x = f x :=
  Subtype.val_injective.extend_apply f.toFun (0 : E → F) x

/-- Outside `Ω`, `f.extendByZero` vanishes. -/
theorem extendByZero_of_notMem (f : CkHolderOnSpace k α Ω F) {x : E} (hx : x ∉ Ω) :
    f.extendByZero x = 0 :=
  Function.extend_apply' _ _ _ fun ⟨y, hy⟩ ↦ hx (hy ▸ y.2)

/-- The zero-extension of `f` is `C^k` on `Ω`. -/
theorem contDiffOn_extendByZero (f : CkHolderOnSpace k α Ω F) :
    ContDiffOn ℝ k f.extendByZero (Ω : Set E) :=
  (hasFTaylorSeriesUpToOn f).contDiffOn

/-- Any ambient map `g : E → F` agreeing with `f` on `Ω` is `C^k` on `Ω`. -/
theorem contDiffOn_of_eq (f : CkHolderOnSpace k α Ω F) {g : E → F} (hg : ∀ x : Ω, g x = f x) :
    ContDiffOn ℝ k g (Ω : Set E) :=
  f.contDiffOn_extendByZero.congr fun x hx ↦ (hg ⟨x, hx⟩).trans (f.extendByZero_coe ⟨x, hx⟩).symm

/-- On `Ω`, the `i`-th derivative within `Ω` of `f.extendByZero` is `f.iteratedFDeriv i`. -/
theorem iteratedFDerivWithin_extendByZero (f : CkHolderOnSpace k α Ω F) (i : Fin (k + 1)) (x : Ω) :
    _root_.iteratedFDerivWithin ℝ i f.extendByZero (Ω : Set E) x = f.iteratedFDeriv i x := by
  rw [iteratedFDerivWithin_of_isOpen i Ω.isOpen x.2, f.iteratedFDeriv_extendByZero]

/-- An ambient map `g : E → F` agreeing with `f` on `Ω` has `i`-th derivative `f.iteratedFDeriv`. -/
theorem iteratedFDeriv_of_eq (f : CkHolderOnSpace k α Ω F) {g : E → F}
    (hg : ∀ x : Ω, g x = f x) (i : Fin (k + 1)) (x : Ω) :
    _root_.iteratedFDeriv ℝ i g x = f.iteratedFDeriv i x := by
  have heq : g =ᶠ[𝓝 (x : E)] f.extendByZero := by
    filter_upwards [Ω.isOpen.mem_nhds x.2] with y hy
    exact (hg ⟨y, hy⟩).trans (f.extendByZero_coe ⟨y, hy⟩).symm
  rw [(heq.iteratedFDeriv ℝ i).eq_of_nhds, f.iteratedFDeriv_extendByZero i x]

/-- The bounded continuous field underlying `f.iteratedFDerivHolder` is `f.iteratedFDeriv last`. -/
@[simp] theorem toBoundedContinuousFunction_iteratedFDerivHolder (f : CkHolderOnSpace k α Ω F) :
    f.iteratedFDerivHolder.toBoundedContinuousFunction = f.iteratedFDeriv (Fin.last k) := by
  rw [iteratedFDeriv, fieldL_last, iteratedFDerivHolder]

/-- Pointwise evaluation of `f.iteratedFDerivHolder` agrees with `f.iteratedFDeriv (Fin.last k)`. -/
@[simp] theorem iteratedFDerivHolder_apply (f : CkHolderOnSpace k α Ω F) (x : Ω) :
    f.iteratedFDerivHolder x = f.iteratedFDeriv (Fin.last k) x := by
  rw [← HolderSpace.toBoundedContinuousFunction_apply,
    toBoundedContinuousFunction_iteratedFDerivHolder]

/-- Coercion of `f.iteratedFDerivHolder` agrees with `f.iteratedFDeriv (Fin.last k)`. -/
@[simp] theorem coe_iteratedFDerivHolder (f : CkHolderOnSpace k α Ω F) :
    (f.iteratedFDerivHolder : Ω → E [×k]→L[ℝ] F) = f.iteratedFDeriv (Fin.last k) :=
  funext (iteratedFDerivHolder_apply f)

/-- The `k`-th derivative field of `f` is `α`-Hölder on `Ω`. -/
theorem memHolder_iteratedFDeriv (f : CkHolderOnSpace k α Ω F) :
    MemHolder α (f.iteratedFDeriv (Fin.last k) : Ω → E [×k]→L[ℝ] F) := by
  rw [← coe_iteratedFDerivHolder, ← HolderSpace.coe_toBoundedContinuousFunction]
  exact f.iteratedFDerivHolder.memHolder

/-- On `Ω`, the `k`-th iterated Fréchet derivative of `f.extendByZero` is `α`-Hölder with constant
the Hölder seminorm of `f.iteratedFDeriv (Fin.last k)`. -/
theorem holderOnWith_iteratedFDeriv_extendByZero (f : CkHolderOnSpace k α Ω F) :
    HolderOnWith (nnHolderNorm α (f.iteratedFDeriv (Fin.last k) : Ω → E [×k]→L[ℝ] F)) α
      (_root_.iteratedFDeriv ℝ k f.extendByZero) (Ω : Set E) := by
  have hdom : (Ω : Set E).domRestrict (_root_.iteratedFDeriv ℝ k f.extendByZero) =
      (f.iteratedFDeriv (Fin.last k) : Ω → E [×k]→L[ℝ] F) :=
    funext fun x ↦ f.iteratedFDeriv_extendByZero (Fin.last k) x
  rw [← HolderWith.restrict_iff, hdom]
  exact f.memHolder_iteratedFDeriv.holderWith

/-- The `C^{k,α}(Ω)` norm is the sum of the supremum norms of the iterated derivative fields on `Ω`
through order `k` and the `α`-Hölder seminorm of the `k`-th derivative field on `Ω`. -/
theorem norm_eq (f : CkHolderOnSpace k α Ω F) :
    ‖f‖ = ∑ i : Fin (k + 1), ‖f.iteratedFDeriv i‖ +
      nnHolderNorm α (f.iteratedFDeriv (Fin.last k) : Ω → E [×k]→L[ℝ] F) := by
  rw [← norm_toJet, WithLp.prod_norm_eq_of_L1, PiLp.norm_eq_of_L1, Fin.sum_univ_castSucc,
    HolderSpace.norm_def, ← coe_iteratedFDerivHolder, ← HolderSpace.coe_toBoundedContinuousFunction,
    add_assoc]
  simp only [iteratedFDeriv, fieldL_castSucc, fieldL_last, iteratedFDerivHolder,
    WithLp.ofLp_fst, WithLp.ofLp_snd]

/-- The supremum norm on `Ω` of each iterated derivative field is at most `‖f‖`. -/
theorem norm_iteratedFDeriv_le (f : CkHolderOnSpace k α Ω F) (i : Fin (k + 1)) :
    ‖f.iteratedFDeriv i‖ ≤ ‖f‖ := by
  rw [norm_eq]
  exact (Finset.single_le_sum (fun j _ ↦ norm_nonneg (f.iteratedFDeriv j))
    (Finset.mem_univ i)).trans (le_add_of_nonneg_right (NNReal.coe_nonneg _))

/-- Pointwise bound on the `i`-th derivative field on `Ω` by `‖f‖`. -/
theorem norm_iteratedFDeriv_apply_le (f : CkHolderOnSpace k α Ω F) (i : Fin (k + 1)) (x : Ω) :
    ‖f.iteratedFDeriv i x‖ ≤ ‖f‖ :=
  ((f.iteratedFDeriv i).norm_coe_le_norm x).trans (f.norm_iteratedFDeriv_le i)

/-- Pointwise bound on `Ω` for the `i`-th iterated derivative of `f.extendByZero`, for `i ≤ k`. -/
theorem norm_iteratedFDeriv_extendByZero_le (f : CkHolderOnSpace k α Ω F) {i : ℕ} (hi : i ≤ k)
    (x : Ω) :
    ‖_root_.iteratedFDeriv ℝ i f.extendByZero x‖ ≤ ‖f‖ := by
  rw [f.iteratedFDeriv_extendByZero ⟨i, Nat.lt_succ_of_le hi⟩ x]
  exact f.norm_iteratedFDeriv_apply_le ⟨i, Nat.lt_succ_of_le hi⟩ x

/-- Pointwise bound on `f x` for `x : Ω` by `‖f‖`. -/
theorem norm_apply_le (f : CkHolderOnSpace k α Ω F) (x : Ω) : ‖f x‖ ≤ ‖f‖ := by
  have h := f.norm_iteratedFDeriv_extendByZero_le (Nat.zero_le k) x
  rwa [norm_iteratedFDeriv_zero, extendByZero_coe] at h

/-- The `α`-Hölder seminorm on `Ω` of the `k`-th derivative field is at most `‖f‖`. -/
theorem nnHolderNorm_iteratedFDeriv_le (f : CkHolderOnSpace k α Ω F) :
    (nnHolderNorm α (f.iteratedFDeriv (Fin.last k) : Ω → E [×k]→L[ℝ] F) : ℝ) ≤ ‖f‖ := by
  rw [norm_eq]
  exact le_add_of_nonneg_left (Finset.sum_nonneg fun _ _ ↦ norm_nonneg _)

/-- Upper bound `‖f‖ ≤ (k + 1) M + K` from uniform bounds `0 ≤ M` on all iterated derivatives up to
order `k` on `Ω` and a `K`-Hölder bound on the `k`-th derivative on `Ω` of an ambient representative
`g` agreeing with `f` on `Ω`. The hypothesis `0 ≤ M` handles the case `Ω = ⊥`. -/
theorem norm_le_of_norm_iteratedFDeriv_le_of_holderOnWith {f : CkHolderOnSpace k α Ω F}
    {g : E → F} (hg : ∀ x : Ω, g x = f x) {M : ℝ} {K : ℝ≥0} (hM0 : 0 ≤ M)
    (hM : ∀ i ≤ k, ∀ x ∈ Ω, ‖_root_.iteratedFDeriv ℝ i g x‖ ≤ M)
    (hK : HolderOnWith K α (_root_.iteratedFDeriv ℝ k g) (Ω : Set E)) :
    ‖f‖ ≤ (k + 1) * M + K := by
  rw [norm_eq]
  gcongr
  · calc ∑ i : Fin (k + 1), ‖f.iteratedFDeriv i‖ ≤ ∑ _i : Fin (k + 1), M :=
          Finset.sum_le_sum fun i _ ↦ (BoundedContinuousFunction.norm_le hM0).2 fun x ↦ by
            rw [← f.iteratedFDeriv_of_eq hg i x]
            exact hM i (Nat.lt_succ_iff.1 i.2) x x.2
      _ = (k + 1) * M := by simp
  · have hdom : (f.iteratedFDeriv (Fin.last k) : Ω → E [×k]→L[ℝ] F) =
        (Ω : Set E).domRestrict (_root_.iteratedFDeriv ℝ k g) :=
      funext fun x ↦ (f.iteratedFDeriv_of_eq hg (Fin.last k) x).symm
    rw [hdom]
    exact_mod_cast hK.holderWith.nnholderNorm_le

/-- The `i`-th derivative field on `Ω` as a continuous linear map (bounded via
`CkHolderOnSpace.norm_iteratedFDeriv_le`). -/
def iteratedFDerivL (i : Fin (k + 1)) :
    CkHolderOnSpace k α Ω F →L[ℝ] (Ω →ᵇ (E [×i]→L[ℝ] F)) :=
  (fieldL i).comp toJetL

/-- `iteratedFDerivL i` sends `f` to its `i`-th derivative field. -/
@[simp] theorem iteratedFDerivL_apply (i : Fin (k + 1)) (f : CkHolderOnSpace k α Ω F) :
    iteratedFDerivL i f = f.iteratedFDeriv i := by
  rw [iteratedFDerivL, ContinuousLinearMap.comp_apply, toJetL_apply, iteratedFDeriv]

/-- The `k`-th derivative field on `Ω` as a continuous linear map into `HolderSpace α Ω _`. -/
def iteratedFDerivHolderL : CkHolderOnSpace k α Ω F →L[ℝ] HolderSpace α Ω (E [×k]→L[ℝ] F) :=
  (WithLp.sndL 1 ℝ _ _).comp toJetL

/-- `iteratedFDerivHolderL` sends `f` to its `k`-th derivative field in `HolderSpace α Ω _`. -/
@[simp] theorem iteratedFDerivHolderL_apply (f : CkHolderOnSpace k α Ω F) :
    iteratedFDerivHolderL f = f.iteratedFDerivHolder := by
  rw [iteratedFDerivHolderL, ContinuousLinearMap.comp_apply, toJetL_apply, WithLp.sndL_apply,
    iteratedFDerivHolder, WithLp.ofLp_snd]

/-- The `HolderSpace` norm of the `k`-th derivative field is at most `‖f‖`. -/
theorem norm_iteratedFDerivHolder_le (f : CkHolderOnSpace k α Ω F) :
    ‖f.iteratedFDerivHolder‖ ≤ ‖f‖ := by
  rw [← norm_toJet, WithLp.prod_norm_eq_of_L1]
  exact le_add_of_nonneg_left (norm_nonneg _)

/-- `iteratedFDerivHolderL` has operator norm at most `1`. -/
theorem norm_iteratedFDerivHolderL_le_one :
    ‖iteratedFDerivHolderL (k := k) (α := α) (Ω := Ω) (F := F)‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun f ↦ by
    rw [iteratedFDerivHolderL_apply, one_mul]; exact norm_iteratedFDerivHolder_le f

/-- Every iterated derivative field of `0` is `0`. -/
@[simp] theorem iteratedFDeriv_zero (i : Fin (k + 1)) :
    (0 : CkHolderOnSpace k α Ω F).iteratedFDeriv i = 0 := by
  simpa only [iteratedFDerivL_apply] using (iteratedFDerivL (α := α) (Ω := Ω) (F := F) i).map_zero

/-- The `i`-th derivative field distributes over addition. -/
@[simp] theorem iteratedFDeriv_add (f g : CkHolderOnSpace k α Ω F) (i : Fin (k + 1)) :
    (f + g).iteratedFDeriv i = f.iteratedFDeriv i + g.iteratedFDeriv i := by
  simpa only [iteratedFDerivL_apply] using (iteratedFDerivL i).map_add f g

/-- The `i`-th derivative field commutes with negation. -/
@[simp] theorem iteratedFDeriv_neg (f : CkHolderOnSpace k α Ω F) (i : Fin (k + 1)) :
    (-f).iteratedFDeriv i = -f.iteratedFDeriv i := by
  simpa only [iteratedFDerivL_apply] using (iteratedFDerivL i).map_neg f

/-- The `i`-th derivative field distributes over subtraction. -/
@[simp] theorem iteratedFDeriv_sub (f g : CkHolderOnSpace k α Ω F) (i : Fin (k + 1)) :
    (f - g).iteratedFDeriv i = f.iteratedFDeriv i - g.iteratedFDeriv i := by
  simpa only [iteratedFDerivL_apply] using (iteratedFDerivL i).map_sub f g

/-- The `i`-th derivative field commutes with scalar multiplication. -/
@[simp] theorem iteratedFDeriv_smul (c : ℝ) (f : CkHolderOnSpace k α Ω F) (i : Fin (k + 1)) :
    (c • f).iteratedFDeriv i = c • f.iteratedFDeriv i := by
  simpa only [iteratedFDerivL_apply] using (iteratedFDerivL i).map_smul c f

/-- The `k`-th Hölder derivative field of `0` is `0`. -/
@[simp] theorem iteratedFDerivHolder_zero :
    (0 : CkHolderOnSpace k α Ω F).iteratedFDerivHolder = 0 := by
  simpa only [iteratedFDerivHolderL_apply] using
    (iteratedFDerivHolderL (k := k) (α := α) (Ω := Ω) (F := F)).map_zero

/-- The `k`-th Hölder derivative field distributes over addition. -/
@[simp] theorem iteratedFDerivHolder_add (f g : CkHolderOnSpace k α Ω F) :
    (f + g).iteratedFDerivHolder = f.iteratedFDerivHolder + g.iteratedFDerivHolder := by
  simpa only [iteratedFDerivHolderL_apply] using iteratedFDerivHolderL.map_add f g

/-- The `k`-th Hölder derivative field commutes with negation. -/
@[simp] theorem iteratedFDerivHolder_neg (f : CkHolderOnSpace k α Ω F) :
    (-f).iteratedFDerivHolder = -f.iteratedFDerivHolder := by
  simpa only [iteratedFDerivHolderL_apply] using iteratedFDerivHolderL.map_neg f

/-- The `k`-th Hölder derivative field distributes over subtraction. -/
@[simp] theorem iteratedFDerivHolder_sub (f g : CkHolderOnSpace k α Ω F) :
    (f - g).iteratedFDerivHolder = f.iteratedFDerivHolder - g.iteratedFDerivHolder := by
  simpa only [iteratedFDerivHolderL_apply] using iteratedFDerivHolderL.map_sub f g

/-- The `k`-th Hölder derivative field commutes with scalar multiplication. -/
@[simp] theorem iteratedFDerivHolder_smul (c : ℝ) (f : CkHolderOnSpace k α Ω F) :
    (c • f).iteratedFDerivHolder = c • f.iteratedFDerivHolder := by
  simpa only [iteratedFDerivHolderL_apply] using iteratedFDerivHolderL.map_smul c f

/-- Coercion of `0` is the zero function on `Ω`. -/
@[simp] theorem coe_zero : ⇑(0 : CkHolderOnSpace k α Ω F) = 0 := by
  ext x; simp only [← toFun_eq_coe, toFun, iteratedFDeriv_zero, Pi.zero_apply, _root_.zero_apply]
  rfl

/-- Addition in `CkHolderOnSpace k α Ω F` is computed pointwise on `Ω`. -/
@[simp] theorem coe_add (f g : CkHolderOnSpace k α Ω F) : ⇑(f + g) = f + g := by
  ext x; simp only [← toFun_eq_coe, toFun, iteratedFDeriv_add, Pi.add_apply, _root_.add_apply]; rfl

/-- Negation in `CkHolderOnSpace k α Ω F` is computed pointwise on `Ω`. -/
@[simp] theorem coe_neg (f : CkHolderOnSpace k α Ω F) : ⇑(-f) = -⇑f := by
  ext x; simp only [← toFun_eq_coe, toFun, iteratedFDeriv_neg, Pi.neg_apply, _root_.neg_apply]; rfl

/-- Subtraction in `CkHolderOnSpace k α Ω F` is computed pointwise on `Ω`. -/
@[simp] theorem coe_sub (f g : CkHolderOnSpace k α Ω F) : ⇑(f - g) = f - g := by
  ext x; simp only [← toFun_eq_coe, toFun, iteratedFDeriv_sub, Pi.sub_apply, _root_.sub_apply]; rfl

/-- Scalar multiplication in `CkHolderOnSpace k α Ω F` is computed pointwise on `Ω`. -/
@[simp] theorem coe_smul (c : ℝ) (f : CkHolderOnSpace k α Ω F) : ⇑(c • f) = c • ⇑f := by
  ext x; simp only [← toFun_eq_coe, toFun, iteratedFDeriv_smul, Pi.smul_apply, _root_.smul_apply]
  rfl

/-- Every element of `CkHolderOnSpace k α Ω F` is continuous on `Ω`. -/
theorem continuous (f : CkHolderOnSpace k α Ω F) : Continuous (f : Ω → F) := by
  have heq : (f : Ω → F) = fun x ↦ (f.iteratedFDeriv ⟨0, k.succ_pos⟩ x).curry0 := (rfl)
  rw [heq]
  exact (continuousMultilinearCurryFin0 ℝ E F).continuous.comp
    (f.iteratedFDeriv ⟨0, k.succ_pos⟩).continuous

/-- Underlying bounded continuous function on `Ω` of an element of `CkHolderOnSpace k α Ω F`. -/
def toBoundedContinuousFunction (f : CkHolderOnSpace k α Ω F) : Ω →ᵇ F :=
  BoundedContinuousFunction.ofNormedAddCommGroup f f.continuous ‖f‖ f.norm_apply_le

/-- Coercing `f.toBoundedContinuousFunction` to a function on `Ω` agrees with `⇑f`. -/
@[simp] theorem coe_toBoundedContinuousFunction (f : CkHolderOnSpace k α Ω F) :
    ⇑f.toBoundedContinuousFunction = f :=
  BoundedContinuousFunction.coe_ofNormedAddCommGroup ..

/-- The supremum norm of `f.toBoundedContinuousFunction` on `Ω` is at most `‖f‖`. -/
theorem norm_toBoundedContinuousFunction_le (f : CkHolderOnSpace k α Ω F) :
    ‖f.toBoundedContinuousFunction‖ ≤ ‖f‖ :=
  BoundedContinuousFunction.norm_ofNormedAddCommGroup_le _ (norm_nonneg f) _

/-- The supremum norm of `f.toBoundedContinuousFunction` equals `‖f.iteratedFDeriv 0‖`. -/
theorem norm_toBoundedContinuousFunction (f : CkHolderOnSpace k α Ω F) :
    ‖f.toBoundedContinuousFunction‖ = ‖f.iteratedFDeriv 0‖ := by
  rw [BoundedContinuousFunction.norm_eq_iSup_norm,
    BoundedContinuousFunction.norm_eq_iSup_norm (f.iteratedFDeriv 0),
    coe_toBoundedContinuousFunction]
  congr 1 with x
  rw [← f.iteratedFDeriv_extendByZero 0 x, Fin.val_zero, norm_iteratedFDeriv_zero,
    f.extendByZero_coe x]

/-- An element of `CkHolderOnSpace k α Ω F` is determined by its underlying bounded continuous
function on `Ω`. -/
theorem toBoundedContinuousFunction_injective :
    Function.Injective (toBoundedContinuousFunction : CkHolderOnSpace k α Ω F → Ω →ᵇ F) :=
  fun _ _ h ↦ ext fun x ↦ by simpa using DFunLike.congr_fun h x

/-- The underlying bounded continuous function of `0` is `0`. -/
@[simp] theorem toBoundedContinuousFunction_zero :
    (0 : CkHolderOnSpace k α Ω F).toBoundedContinuousFunction = 0 := by ext x; simp

/-- `toBoundedContinuousFunction` distributes over addition. -/
@[simp] theorem toBoundedContinuousFunction_add (f g : CkHolderOnSpace k α Ω F) :
    (f + g).toBoundedContinuousFunction =
      f.toBoundedContinuousFunction + g.toBoundedContinuousFunction := by ext x; simp

/-- `toBoundedContinuousFunction` commutes with negation. -/
@[simp] theorem toBoundedContinuousFunction_neg (f : CkHolderOnSpace k α Ω F) :
    (-f).toBoundedContinuousFunction = -f.toBoundedContinuousFunction := by ext x; simp

/-- `toBoundedContinuousFunction` distributes over subtraction. -/
@[simp] theorem toBoundedContinuousFunction_sub (f g : CkHolderOnSpace k α Ω F) :
    (f - g).toBoundedContinuousFunction =
      f.toBoundedContinuousFunction - g.toBoundedContinuousFunction := by ext x; simp

/-- `toBoundedContinuousFunction` commutes with scalar multiplication. -/
@[simp] theorem toBoundedContinuousFunction_smul (c : ℝ) (f : CkHolderOnSpace k α Ω F) :
    (c • f).toBoundedContinuousFunction = c • f.toBoundedContinuousFunction := by ext x; simp

/-- Inclusion of `CkHolderOnSpace k α Ω F` into bounded continuous functions `Ω →ᵇ F`. -/
def toBoundedContinuousFunctionCLM : CkHolderOnSpace k α Ω F →L[ℝ] (Ω →ᵇ F) :=
  LinearMap.mkContinuous
    { toFun := toBoundedContinuousFunction
      map_add' := toBoundedContinuousFunction_add
      map_smul' := toBoundedContinuousFunction_smul } 1 fun f ↦ by
        rw [one_mul]; exact norm_toBoundedContinuousFunction_le f

/-- `toBoundedContinuousFunctionCLM` sends `f` to `f.toBoundedContinuousFunction`. -/
@[simp] theorem toBoundedContinuousFunctionCLM_apply (f : CkHolderOnSpace k α Ω F) :
    toBoundedContinuousFunctionCLM f = f.toBoundedContinuousFunction := (rfl)

/-- Forgetting derivatives into `Ω →ᵇ F` has operator norm at most `1`. -/
theorem norm_toBoundedContinuousFunctionCLM_le_one :
    ‖toBoundedContinuousFunctionCLM (k := k) (α := α) (Ω := Ω) (F := F)‖ ≤ 1 :=
  LinearMap.mkContinuous_norm_le _ zero_le_one _

/-- Point evaluation at `x : Ω` as a continuous linear map of operator norm at most `1`. -/
def evalCLM (x : Ω) : CkHolderOnSpace k α Ω F →L[ℝ] F :=
  (BoundedContinuousFunction.evalCLM ℝ x).comp toBoundedContinuousFunctionCLM

/-- Point evaluation `evalCLM x` sends `f` to `f x`. -/
@[simp] theorem evalCLM_apply (x : Ω) (f : CkHolderOnSpace k α Ω F) : evalCLM x f = f x := by
  simp [evalCLM]

/-- Point evaluation at `x : Ω` has operator norm at most `1`. -/
theorem norm_evalCLM_le_one (x : Ω) : ‖evalCLM (k := k) (α := α) (F := F) x‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun f ↦ by
    simpa only [evalCLM_apply, one_mul] using f.norm_apply_le x

private def jetOnOf (g : E → F) (hg : ContDiffOn ℝ k g (Ω : Set E))
    (hbdd : ∀ i ≤ k, ∃ C, ∀ x ∈ Ω, ‖_root_.iteratedFDeriv ℝ i g x‖ ≤ C)
    (hholder : ∃ C, HolderOnWith C α (_root_.iteratedFDeriv ℝ k g) (Ω : Set E)) :
    Jet k α Ω F :=
  WithLp.toLp 1
    (WithLp.toLp 1 fun j : Fin k ↦
        BoundedContinuousFunction.ofNormedAddCommGroup
          ((Ω : Set E).domRestrict (_root_.iteratedFDeriv ℝ j g))
          (continuousOn_iff_continuous_domRestrict.mp
            (ContinuousOn.continuousOn_iteratedFDeriv hg Ω.isOpen (by exact_mod_cast j.2.le)))
          (hbdd j j.2.le).choose (fun x ↦ (hbdd j j.2.le).choose_spec x x.2),
      HolderSpace.ofBoundedContinuousFunction
        (BoundedContinuousFunction.ofNormedAddCommGroup
          ((Ω : Set E).domRestrict (_root_.iteratedFDeriv ℝ k g))
          (continuousOn_iff_continuous_domRestrict.mp
            (ContinuousOn.continuousOn_iteratedFDeriv hg Ω.isOpen le_rfl))
          (hbdd k le_rfl).choose (fun x ↦ (hbdd k le_rfl).choose_spec x x.2))
        (let ⟨C, hC⟩ := hholder; ⟨C, hC.holderWith⟩))

private theorem fieldL_jetOnOf (g : E → F) (hg : ContDiffOn ℝ k g (Ω : Set E))
    (hbdd : ∀ i ≤ k, ∃ C, ∀ x ∈ Ω, ‖_root_.iteratedFDeriv ℝ i g x‖ ≤ C)
    (hholder : ∃ C, HolderOnWith C α (_root_.iteratedFDeriv ℝ k g) (Ω : Set E))
    (i : Fin (k + 1)) (x : Ω) :
    fieldL i (jetOnOf g hg hbdd hholder) x = _root_.iteratedFDeriv ℝ i g x := by
  induction i using Fin.lastCases with
  | last =>
    rw [fieldL_last]
    simp only [jetOnOf, WithLp.ofLp_toLp,
      HolderSpace.toBoundedContinuousFunction_ofBoundedContinuousFunction]
    exact (congrFun (BoundedContinuousFunction.coe_ofNormedAddCommGroup ..) x).trans
      (Set.domRestrict_apply ..)
  | cast j =>
    rw [fieldL_castSucc]
    simp only [jetOnOf, WithLp.ofLp_toLp]
    exact (congrFun (BoundedContinuousFunction.coe_ofNormedAddCommGroup ..) x).trans
      (Set.domRestrict_apply ..)

private theorem isJetGraph_jetOnOf (g : E → F) (hg : ContDiffOn ℝ k g (Ω : Set E))
    (hbdd : ∀ i ≤ k, ∃ C, ∀ x ∈ Ω, ‖_root_.iteratedFDeriv ℝ i g x‖ ≤ C)
    (hholder : ∃ C, HolderOnWith C α (_root_.iteratedFDeriv ℝ k g) (Ω : Set E)) :
    IsJetGraph (jetOnOf g hg hbdd hholder) := fun j x ↦ by
  have heq : Function.extend Subtype.val
      (fieldL j.castSucc (jetOnOf g hg hbdd hholder) : Ω → E [×j]→L[ℝ] F) 0 =ᶠ[𝓝 (x : E)]
      _root_.iteratedFDeriv ℝ j g := by
    filter_upwards [Ω.isOpen.mem_nhds x.2] with y hy
    exact (Subtype.val_injective.extend_apply _ (0 : E → E [×j]→L[ℝ] F) ⟨y, hy⟩).trans
      (fieldL_jetOnOf g hg hbdd hholder j.castSucc ⟨y, hy⟩)
  have h := ((hg.contDiffAt (Ω.isOpen.mem_nhds x.2)).differentiableAt_iteratedFDeriv
    (m := j) (by exact_mod_cast j.2)).hasFDerivAt
  rw [fderiv_iteratedFDeriv, Function.comp_apply] at h
  rw [fieldL_jetOnOf]
  exact h.congr_of_eventuallyEq heq

/-- Construct an element of `CkHolderOnSpace k α Ω F` from an ambient map `g : E → F` that is `C^k`
on `Ω` with bounded iterated derivatives through order `k` on `Ω` and `α`-Hölder `k`-th iterated
derivative on `Ω`. -/
def ofContDiffOn (g : E → F) (hg : ContDiffOn ℝ k g (Ω : Set E))
    (hbdd : ∀ i ≤ k, ∃ C, ∀ x ∈ Ω, ‖_root_.iteratedFDeriv ℝ i g x‖ ≤ C)
    (hholder : ∃ C, HolderOnWith C α (_root_.iteratedFDeriv ℝ k g) (Ω : Set E)) :
    CkHolderOnSpace k α Ω F :=
  mk (jetOnOf g hg hbdd hholder) (isJetGraph_jetOnOf g hg hbdd hholder)

/-- Pointwise evaluation of `ofContDiffOn g` on `Ω` agrees with `g`. -/
@[simp]
theorem ofContDiffOn_apply (g : E → F) (hg : ContDiffOn ℝ k g (Ω : Set E))
    (hbdd : ∀ i ≤ k, ∃ C, ∀ x ∈ Ω, ‖_root_.iteratedFDeriv ℝ i g x‖ ≤ C)
    (hholder : ∃ C, HolderOnWith C α (_root_.iteratedFDeriv ℝ k g) (Ω : Set E)) (x : Ω) :
    ofContDiffOn g hg hbdd hholder x = g x := by
  have hcoe : ofContDiffOn g hg hbdd hholder x = (ofContDiffOn g hg hbdd hholder).toFun x := rfl
  rw [hcoe, toFun, iteratedFDeriv, ofContDiffOn, toJet_mk, fieldL_jetOnOf,
    iteratedFDeriv_zero_eq_comp]
  simp

/-- The `i`-th derivative field of `ofContDiffOn g` on `Ω` agrees with `iteratedFDeriv ℝ i g`. -/
@[simp]
theorem iteratedFDeriv_ofContDiffOn_apply (g : E → F) (hg : ContDiffOn ℝ k g (Ω : Set E))
    (hbdd : ∀ i ≤ k, ∃ C, ∀ x ∈ Ω, ‖_root_.iteratedFDeriv ℝ i g x‖ ≤ C)
    (hholder : ∃ C, HolderOnWith C α (_root_.iteratedFDeriv ℝ k g) (Ω : Set E))
    (i : Fin (k + 1)) (x : Ω) :
    (ofContDiffOn g hg hbdd hholder).iteratedFDeriv i x = _root_.iteratedFDeriv ℝ i g x :=
  (iteratedFDeriv_of_eq _ (fun y ↦ (ofContDiffOn_apply g hg hbdd hholder y).symm) i x).symm

private theorem norm_iteratedFDeriv_const_le (y : F) (i : ℕ) (x : E) :
    ‖_root_.iteratedFDeriv ℝ i (fun _ : E ↦ y) x‖ ≤ ‖y‖ := by
  rcases eq_or_ne i 0 with rfl | hi
  · simp
  · simp [iteratedFDeriv_const_of_ne hi, norm_nonneg y]

private theorem holderOnWith_iteratedFDeriv_const (y : F) :
    HolderOnWith 0 α (_root_.iteratedFDeriv ℝ k (fun _ : E ↦ y)) (Ω : Set E) := by
  rcases eq_or_ne k 0 with rfl | hk
  · rw [iteratedFDeriv_zero_eq_comp, Function.comp_def]
    exact (HolderWith.const (C := 0)).holderOnWith _
  · rw [iteratedFDeriv_const_of_ne hk]; exact (HolderWith.const (C := 0)).holderOnWith _

/-- Constant map on `Ω` as an element of `CkHolderOnSpace k α Ω F`. -/
def const (y : F) : CkHolderOnSpace k α Ω F :=
  ofContDiffOn (fun _ : E ↦ y) contDiffOn_const
    (fun i _ ↦ ⟨‖y‖, fun x _ ↦ norm_iteratedFDeriv_const_le y i x⟩)
    ⟨0, holderOnWith_iteratedFDeriv_const y⟩

/-- Pointwise evaluation of `const y` on `Ω` returns `y`. -/
@[simp] theorem const_apply (y : F) (x : Ω) : const (k := k) (α := α) (Ω := Ω) y x = y :=
  ofContDiffOn_apply ..

/-- The constant function with value `0` is `0`. -/
@[simp] theorem const_zero : const (k := k) (α := α) (Ω := Ω) (0 : F) = 0 := ext fun _ ↦ by simp

/-- Constant functions preserve addition. -/
@[simp] theorem const_add (y₁ y₂ : F) :
    const (k := k) (α := α) (Ω := Ω) (y₁ + y₂) = const y₁ + const y₂ := ext fun _ ↦ by simp

/-- Constant functions preserve negation. -/
@[simp] theorem const_neg (y : F) : const (k := k) (α := α) (Ω := Ω) (-y) = -const y :=
  ext fun _ ↦ by simp

/-- Constant functions preserve subtraction. -/
@[simp] theorem const_sub (y₁ y₂ : F) :
    const (k := k) (α := α) (Ω := Ω) (y₁ - y₂) = const y₁ - const y₂ := ext fun _ ↦ by simp

/-- Constant functions preserve scalar multiplication. -/
@[simp] theorem const_smul (c : ℝ) (y : F) :
    const (k := k) (α := α) (Ω := Ω) (c • y) = c • const y := ext fun _ ↦ by simp

/-- The underlying bounded continuous function of `const y` is `BoundedContinuousFunction.const`. -/
@[simp] theorem toBoundedContinuousFunction_const (y : F) :
    (const (k := k) (α := α) (Ω := Ω) y).toBoundedContinuousFunction =
      BoundedContinuousFunction.const Ω y := by ext x; simp

/-- The `C^{k,α}(Ω)` norm of `const y` is at most `‖y‖`, even on an empty open set. -/
theorem norm_const_le (y : F) : ‖const (k := k) (α := α) (Ω := Ω) y‖ ≤ ‖y‖ := by
  have hc : ∀ (i : Fin (k + 1)) (x : Ω),
      (const (k := k) (α := α) (Ω := Ω) y).iteratedFDeriv i x =
        _root_.iteratedFDeriv ℝ i (fun _ : E ↦ y) x :=
    fun i x ↦ iteratedFDeriv_ofContDiffOn_apply (fun _ : E ↦ y) _ _ _ i x
  rw [norm_eq]
  have h0 : ‖(const (k := k) (α := α) (Ω := Ω) y).iteratedFDeriv 0‖ ≤ ‖y‖ :=
    (BoundedContinuousFunction.norm_le (norm_nonneg y)).2 fun x ↦ by
      rw [hc 0 x, Fin.val_zero, norm_iteratedFDeriv_zero]
  have hpos (i : Fin (k + 1)) (hi : i ≠ 0) :
      ‖(const (k := k) (α := α) (Ω := Ω) y).iteratedFDeriv i‖ = 0 := by
    refine le_antisymm ((BoundedContinuousFunction.norm_le le_rfl).2 fun x ↦ ?_) (norm_nonneg _)
    rw [hc i x, iteratedFDeriv_const_of_ne (Fin.val_ne_of_ne hi), Pi.zero_apply, norm_zero]
  have hH : nnHolderNorm α ((const (k := k) (α := α) (Ω := Ω) y).iteratedFDeriv (Fin.last k) :
      Ω → E [×k]→L[ℝ] F) = 0 := by
    have hdom : ((const (k := k) (α := α) (Ω := Ω) y).iteratedFDeriv (Fin.last k) :
          Ω → E [×k]→L[ℝ] F) =
        (Ω : Set E).domRestrict (_root_.iteratedFDeriv ℝ k (fun _ : E ↦ y)) :=
      funext fun x ↦ hc (Fin.last k) x
    rw [hdom]
    exact le_antisymm
      (holderOnWith_iteratedFDeriv_const (k := k) (α := α) (Ω := Ω) y).holderWith.nnholderNorm_le
      zero_le
  rw [Finset.sum_eq_single 0 (fun i _ hi ↦ hpos i hi) (by simp), hH, NNReal.coe_zero, add_zero]
  exact h0

/-- On a nonempty open set `Ω`, the `C^{k,α}(Ω)` norm of `const y` is `‖y‖`. -/
@[simp] theorem norm_const [Nonempty Ω] (y : F) : ‖const (k := k) (α := α) (Ω := Ω) y‖ = ‖y‖ := by
  refine le_antisymm (norm_const_le y) ?_
  obtain ⟨x⟩ := ‹Nonempty Ω›
  simpa only [const_apply] using (const (k := k) (α := α) (Ω := Ω) y).norm_apply_le x

/-- Constant-function map `F →L[ℝ] CkHolderOnSpace k α Ω F`, of operator norm at most `1`. -/
def constL : F →L[ℝ] CkHolderOnSpace k α Ω F :=
  LinearMap.mkContinuous
    { toFun := const, map_add' := const_add, map_smul' := const_smul } 1 fun y ↦ by
      rw [one_mul]; exact norm_const_le y

/-- The linear map `constL` sends `y` to `const y`. -/
@[simp] theorem constL_apply (y : F) : constL (k := k) (α := α) (Ω := Ω) y = const y := (rfl)

/-- The constant-function map `constL` has operator norm at most `1`, even on an empty open set. -/
theorem norm_constL_le_one : ‖constL (k := k) (α := α) (Ω := Ω) (F := F)‖ ≤ 1 :=
  LinearMap.mkContinuous_norm_le _ zero_le_one _

/-- On a nonempty open set with nontrivial values, `constL` has operator norm `1`. -/
@[simp] theorem norm_constL [Nonempty Ω] [Nontrivial F] :
    ‖constL (k := k) (α := α) (Ω := Ω) (F := F)‖ = 1 := by
  obtain ⟨y, hy⟩ := exists_ne (0 : F)
  refine le_antisymm norm_constL_le_one ?_
  have h := (constL (k := k) (α := α) (Ω := Ω)).le_opNorm y
  simpa only [constL_apply, norm_const, le_mul_iff_one_le_left (norm_pos_iff.mpr hy)] using h

/-- On a nonempty open set with nontrivial values, `toBoundedContinuousFunctionCLM` has norm `1`. -/
@[simp] theorem norm_toBoundedContinuousFunctionCLM [Nonempty Ω] [Nontrivial F] :
    ‖toBoundedContinuousFunctionCLM (k := k) (α := α) (Ω := Ω) (F := F)‖ = 1 := by
  obtain ⟨y, hy⟩ := exists_ne (0 : F)
  refine le_antisymm norm_toBoundedContinuousFunctionCLM_le_one ?_
  have h := (toBoundedContinuousFunctionCLM (k := k) (α := α) (Ω := Ω)).le_opNorm (const y)
  simpa only [toBoundedContinuousFunctionCLM_apply, toBoundedContinuousFunction_const,
    BoundedContinuousFunction.norm_const_eq, norm_const,
    le_mul_iff_one_le_left (norm_pos_iff.mpr hy)] using h

/-- With nontrivial values, point evaluation `evalCLM x` has operator norm `1`. -/
@[simp] theorem norm_evalCLM [Nontrivial F] (x : Ω) :
    ‖evalCLM (k := k) (α := α) (F := F) x‖ = 1 := by
  let : Nonempty Ω := ⟨x⟩
  obtain ⟨y, hy⟩ := exists_ne (0 : F)
  refine le_antisymm (norm_evalCLM_le_one x) ?_
  have h := (evalCLM (k := k) (α := α) x).le_opNorm (const y)
  simpa only [evalCLM_apply, const_apply, norm_const,
    le_mul_iff_one_le_left (norm_pos_iff.mpr hy)] using h

/-- Evaluating a constant function at `x : Ω` recovers its value. -/
@[simp] theorem evalCLM_comp_constL (x : Ω) :
    (evalCLM (k := k) (α := α) (F := F) x).comp constL = ContinuousLinearMap.id ℝ F := by
  ext y; simp

private theorem isClosed_isJetGraph : IsClosed {J : Jet k α Ω F | IsJetGraph J} := by
  have hset : {J : Jet k α Ω F | IsJetGraph J} =
      ⋂ j : Fin k, (fun J : Jet k α Ω F ↦ (fieldL j.castSucc J, fieldL j.succ J)) ⁻¹'
        {J | ∀ x : Ω, HasFDerivAt
          (Function.extend Subtype.val (J.1 : Ω → E [×j]→L[ℝ] F) 0)
          (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (j + 1) ↦ E) F (J.2 x)) x} := by
    ext J; simp [IsJetGraph]
  rw [hset]
  exact isClosed_iInter fun j ↦
    (isClosed_setOf_hasFDerivAt_extend_comp Ω.isOpen
      (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (j + 1) ↦ E) F)
      (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (j + 1) ↦ E) F).continuous).preimage
      ((fieldL (k := k) (α := α) (Ω := Ω) (F := F) _).continuous.prodMk
        (fieldL (k := k) (α := α) (Ω := Ω) (F := F) _).continuous)

/-- When `F` is a Banach space, `CkHolderOnSpace k α Ω F` is a Banach space. -/
instance instCompleteSpace [CompleteSpace F] : CompleteSpace (CkHolderOnSpace k α Ω F) := by
  unfold CkHolderOnSpace; exact isClosed_isJetGraph.completeSpace_coe

/-! ### Isometric identifications at `k = 0` and at `Ω = ⊤` -/

private def toHolderSpace (f : CkHolderOnSpace 0 α Ω F) : HolderSpace α Ω F :=
  HolderSpace.compLeftL
    (continuousMultilinearCurryFin0 ℝ E F).toLinearIsometry.toContinuousLinearMap
    f.iteratedFDerivHolder

private theorem isJetGraph_zero (J : Jet 0 α Ω F) : IsJetGraph J := fun j ↦ Fin.elim0 j

private def ofHolderSpace (g : HolderSpace α Ω F) : CkHolderOnSpace 0 α Ω F :=
  mk (WithLp.toLp 1 (0, HolderSpace.compLeftL
      (continuousMultilinearCurryFin0 ℝ E F).symm.toLinearIsometry.toContinuousLinearMap g))
    (isJetGraph_zero _)

private theorem toHolderSpace_apply (f : CkHolderOnSpace 0 α Ω F) (x : Ω) :
    toHolderSpace f x = f x := by
  simp only [toHolderSpace, HolderSpace.compLeftL_apply, iteratedFDerivHolder_apply]; rfl

private theorem ofHolderSpace_apply (g : HolderSpace α Ω F) (x : Ω) :
    ofHolderSpace g x = g x := by
  have hcoe : ofHolderSpace g x = (ofHolderSpace g).toFun x := rfl
  have hlast : fieldL ⟨0, Nat.succ_pos 0⟩ (toJet (ofHolderSpace g)) =
      (toJet (ofHolderSpace g)).ofLp.2.toBoundedContinuousFunction :=
    fieldL_last (toJet (ofHolderSpace g))
  have hjet : toJet (ofHolderSpace g) = WithLp.toLp 1 (0, HolderSpace.compLeftL
      (continuousMultilinearCurryFin0 ℝ E F).symm.toLinearIsometry.toContinuousLinearMap g) :=
    toJet_mk _ _
  rw [hcoe, toFun, iteratedFDeriv, hlast, hjet]; simp

private theorem norm_toHolderSpace (f : CkHolderOnSpace 0 α Ω F) : ‖toHolderSpace f‖ = ‖f‖ := by
  rw [toHolderSpace, HolderSpace.norm_compLeftL_linearIsometry, HolderSpace.norm_def,
    toBoundedContinuousFunction_iteratedFDerivHolder, norm_eq, Fin.sum_univ_one]; rfl

/-- At order `k = 0`, `CkHolderOnSpace 0 α Ω F` is linearly isometric to `HolderSpace α Ω F`. -/
def equivHolderSpace : CkHolderOnSpace 0 α Ω F ≃ₗᵢ[ℝ] HolderSpace α Ω F where
  toFun := toHolderSpace
  invFun := ofHolderSpace
  left_inv f := ext fun x ↦ (ofHolderSpace_apply _ x).trans (toHolderSpace_apply f x)
  right_inv g := HolderSpace.ext fun x ↦ (toHolderSpace_apply _ x).trans (ofHolderSpace_apply g x)
  map_add' f g := HolderSpace.ext fun x ↦ by
    simp only [toHolderSpace_apply, coe_add, Pi.add_apply, HolderSpace.add_apply]
  map_smul' c f := HolderSpace.ext fun x ↦ by
    simp only [toHolderSpace_apply, coe_smul, Pi.smul_apply, RingHom.id_apply,
      HolderSpace.smul_apply]
  norm_map' := norm_toHolderSpace

/-- The linear isometry `equivHolderSpace` preserves pointwise values on `Ω`. -/
@[simp] theorem equivHolderSpace_apply (f : CkHolderOnSpace 0 α Ω F) (x : Ω) :
    equivHolderSpace f x = f x := toHolderSpace_apply f x

/-- The inverse of `equivHolderSpace` preserves pointwise values on `Ω`. -/
@[simp] theorem equivHolderSpace_symm_apply (g : HolderSpace α Ω F) (x : Ω) :
    equivHolderSpace.symm g x = g x := ofHolderSpace_apply g x

private def toTop (f : CkHolderOnSpace k α (⊤ : TopologicalSpace.Opens E) F) :
    CkHolderSpace k α E F :=
  CkHolderSpace.ofContDiff f.extendByZero
    (contDiffOn_univ.mp f.contDiffOn_extendByZero)
    (fun _ hi ↦ ⟨‖f‖, fun x ↦ f.norm_iteratedFDeriv_extendByZero_le hi ⟨x, trivial⟩⟩)
    (holderOnWith_univ.mp f.holderOnWith_iteratedFDeriv_extendByZero).memHolder

private def ofTop (g : CkHolderSpace k α E F) :
    CkHolderOnSpace k α (⊤ : TopologicalSpace.Opens E) F :=
  ofContDiffOn g g.contDiff.contDiffOn
    (fun _ hi ↦ ⟨‖g‖, fun x _ ↦ g.norm_iteratedFDeriv_apply_le hi x⟩)
    ⟨_, g.memHolder_iteratedFDeriv.holderWith.holderOnWith _⟩

private theorem toTop_apply (f : CkHolderOnSpace k α (⊤ : TopologicalSpace.Opens E) F) (x : E) :
    toTop f x = f ⟨x, trivial⟩ := by
  simp only [toTop, CkHolderSpace.coe_ofContDiff]; exact f.extendByZero_coe ⟨x, trivial⟩

private theorem ofTop_apply (g : CkHolderSpace k α E F) (x : (⊤ : TopologicalSpace.Opens E)) :
    ofTop g x = g x := ofContDiffOn_apply ..

private theorem norm_toTop (f : CkHolderOnSpace k α (⊤ : TopologicalSpace.Opens E) F) :
    ‖toTop f‖ = ‖f‖ := by
  have hcoe : ⇑(toTop f) = f.extendByZero := CkHolderSpace.coe_ofContDiff ..
  have hfield (i : Fin (k + 1)) : ‖(toTop f).iteratedFDeriv i‖ = ‖f.iteratedFDeriv i‖ := by
    apply le_antisymm
    · refine (BoundedContinuousFunction.norm_le (norm_nonneg (f.iteratedFDeriv i))).2 fun x ↦ ?_
      rw [← CkHolderSpace.iteratedFDeriv_eq, hcoe, f.iteratedFDeriv_extendByZero i ⟨x, trivial⟩]
      exact (f.iteratedFDeriv i).norm_coe_le_norm ⟨x, trivial⟩
    · refine (BoundedContinuousFunction.norm_le (norm_nonneg ((toTop f).iteratedFDeriv i))).2
        fun x ↦ ?_
      rw [← f.iteratedFDeriv_extendByZero i x, ← hcoe, CkHolderSpace.iteratedFDeriv_eq]
      exact ((toTop f).iteratedFDeriv i).norm_coe_le_norm x.1
  have htop : nnHolderNorm α (_root_.iteratedFDeriv ℝ k (toTop f)) =
      nnHolderNorm α (f.iteratedFDeriv (Fin.last k) : (⊤ : TopologicalSpace.Opens E) →
        E [×k]→L[ℝ] F) := by
    apply le_antisymm
    · rw [hcoe]
      exact (holderOnWith_univ.mp f.holderOnWith_iteratedFDeriv_extendByZero).nnholderNorm_le
    · have hdom : (f.iteratedFDeriv (Fin.last k) : (⊤ : TopologicalSpace.Opens E) →
          E [×k]→L[ℝ] F) = (Set.univ : Set E).domRestrict (_root_.iteratedFDeriv ℝ k (toTop f)) :=
        funext fun x ↦ by
          rw [Set.domRestrict_apply, hcoe]
          exact (f.iteratedFDeriv_extendByZero (Fin.last k) x).symm
      rw [hdom]
      exact ((toTop f).memHolder_iteratedFDeriv.holderWith.holderOnWith
        Set.univ).holderWith.nnholderNorm_le
  rw [CkHolderSpace.norm_eq, norm_eq]; simp only [hfield, htop]

/-- On `⊤ : TopologicalSpace.Opens E`, `CkHolderOnSpace k α ⊤ F ≃ₗᵢ[ℝ] CkHolderSpace k α E F`. -/
def equivTop :
    CkHolderOnSpace k α (⊤ : TopologicalSpace.Opens E) F ≃ₗᵢ[ℝ] CkHolderSpace k α E F where
  toFun := toTop
  invFun := ofTop
  left_inv f := ext fun x ↦ (ofTop_apply _ x).trans (toTop_apply f x.1)
  right_inv g := CkHolderSpace.ext fun x ↦ (toTop_apply _ x).trans (ofTop_apply g ⟨x, trivial⟩)
  map_add' f g := CkHolderSpace.ext fun x ↦ by
    simp only [toTop_apply, coe_add, Pi.add_apply, CkHolderSpace.coe_add]
  map_smul' c f := CkHolderSpace.ext fun x ↦ by
    simp only [toTop_apply, coe_smul, Pi.smul_apply, RingHom.id_apply, CkHolderSpace.coe_smul]
  norm_map' := norm_toTop

/-- The linear isometry `equivTop` preserves pointwise values on `E`. -/
@[simp] theorem equivTop_apply (f : CkHolderOnSpace k α (⊤ : TopologicalSpace.Opens E) F) (x : E) :
    equivTop f x = f ⟨x, trivial⟩ := toTop_apply f x

/-- The inverse of `equivTop` preserves pointwise values on `⊤`. -/
@[simp] theorem equivTop_symm_apply (g : CkHolderSpace k α E F)
    (x : (⊤ : TopologicalSpace.Opens E)) : equivTop.symm g x = g x := ofTop_apply g x

attribute [irreducible] instNormedAddCommGroup instNormedSpace _root_.TauCeti.CkHolderOnSpace

end CkHolderOnSpace

end TauCeti

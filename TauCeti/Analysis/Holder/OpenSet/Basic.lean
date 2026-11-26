/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Holder.Iterated
public import Mathlib.Analysis.Convex.Basic
public import Mathlib.Topology.Sets.Opens
import Mathlib.Analysis.Calculus.ContDiff.Comp
import TauCeti.Analysis.Calculus.IteratedFDeriv.Basic
import TauCeti.Analysis.Calculus.UniformLimitsDeriv
import TauCeti.Analysis.Holder.IsBigO
import TauCeti.Analysis.Holder.Jet.Bounds
import TauCeti.Analysis.Holder.MeanValue
import TauCeti.Topology.ContinuousMap.Bounded.Normed
import TauCeti.Topology.MetricSpace.Holder

/-!
# The Hölder spaces `C^{k,α}(Ω)` on an open set

For an open set `Ω` of a real normed space `E`, this file constructs the normed space
`C^{k,α}(Ω, F)` of `C^k` maps on `Ω` whose iterated Fréchet derivatives through order `k` are
bounded on `Ω` and whose `k`-th iterated derivative has finite `α`-Hölder seminorm over `Ω`, and
proves that it is Banach when the codomain is Banach. Its norm is

`‖f‖ = ∑_{i ≤ k} sup_{x ∈ Ω} ‖D^i f(x)‖ + [D^k f]_{α, Ω}`,

where the suprema use the operator norm of continuous multilinear maps and the Hölder seminorm is
taken over all pairs of points of `Ω`. These are the spaces of the global Schauder theory on a
domain. The seminorm is global on `Ω`, not a supremum of local seminorms: on
`Ω = (-1, 0) ∪ (0, 1)` the sign function is smooth with vanishing derivatives, but for `α > 0` it
is not in `C^{0,α}(Ω)` because its Hölder quotient across the gap is unbounded.

An element is a function on the subtype `Ω`, represented, as for the whole-space spaces
`TauCeti.CkHolderSpace`, by its family of iterated derivative fields: bounded continuous fields
`Ω →ᵇ (E [×i]→L[ℝ] F)` for `i < k` and a bounded Hölder field of order `k`, such that each field,
extended by zero outside `Ω`, has the next field, curried on the left, as its Fréchet derivative
at every point of `Ω`. Since `Ω` is open, the fields are then the iterated derivatives of every
function on `E` that agrees with the element on `Ω`, so an element is determined by its values.
The derivative identities are closed under uniform convergence of the fields, which gives
completeness. The fields form an element of the jet space `TauCeti.CkHolderJet` with field
domain `Ω`, shared with `TauCeti.CkHolderSpace`.

## Main declarations

* `TauCeti.CkHolderSpaceOn k α Ω F`: the space `C^{k,α}(Ω, F)` for `Ω : Opens E`.
* `TauCeti.CkHolderSpaceOn.iteratedFDeriv`: the bounded continuous `i`-th derivative field on `Ω`
  for `i ≤ k`. `TauCeti.CkHolderSpaceOn.iteratedFDeriv_eq` identifies it with Mathlib's
  `iteratedFDeriv` of any function on `E` that agrees with the element on `Ω`, and
  `TauCeti.CkHolderSpaceOn.contDiffOn` says that such a function is `C^k` on `Ω`.
* `TauCeti.CkHolderSpaceOn.ofContDiffOn`: the element defined by a function that is `C^k` on `Ω`,
  with bounded derivatives through order `k` on `Ω` and `α`-Hölder `k`-th derivative on `Ω`.
* `TauCeti.CkHolderSpaceOn.norm_eq`: the norm is the sum of the supremum norms of the
  derivative fields through order `k` and the `α`-Hölder seminorm of the `k`-th field.
* `TauCeti.CkHolderSpaceOn.extend`: the extension by zero of an element, a canonical function on
  `E` agreeing with it on `Ω`; `TauCeti.CkHolderSpaceOn.toBoundedContinuousFunctionCLM`: forgetting
  the derivatives, a continuous linear map of norm at most one to `Ω →ᵇ F`.
* `TauCeti.CkHolderSpaceOn.holderOnWith_extend`: an element of `C^{0,α}(Ω)` is `α`-Hölder on `Ω`.
* `TauCeti.CkHolderSpaceOn.iteratedFDeriv_last_apply_eq_apply_of_one_lt` and
  `TauCeti.CkHolderSpaceOn.apply_eq_apply_of_one_lt`: for `α > 1` on a preconnected `Ω`, the
  derivative field of order `k` is constant, and `C^{0,α}(Ω)` consists of constants. The space is
  not wrong for `α > 1` but degenerate, which is why the exponents of interest lie in `(0, 1]`.
* `TauCeti.CkHolderSpaceOn.instCompleteSpace`: completeness when the codomain is complete.
* `TauCeti.CkHolderSpaceOn.exists_apply_eq_of_contDiffOn_of_isCompact`: for `α ≤ 1`, a function
  that is `C^{k+1}` on a neighbourhood of a compact set containing `Ω` defines an element of
  `C^{k,α}(Ω)`. `TauCeti.CkHolderSpaceOn.exists_apply_eq_of_differentiableOn_of_holderOnWith`:
  for `α > 0` and bounded `Ω`, a bounded function that is differentiable on `Ω` with an `α`-Hölder
  derivative on `Ω` defines an element of `C^{1,α}(Ω)`.
* `TauCeti.CkHolderSpaceOn.restrictL`: restriction to a smaller open set, of operator norm at
  most one, and `TauCeti.CkHolderSpace.restrictOnL`: restriction of a bounded `C^{k,α}` map on the
  whole space to an open set, also of operator norm at most one.
* `TauCeti.CkHolderSpaceOn.holderOnWith_iteratedFDeriv_of_le`: on a convex open set and for
  `α ≤ 1`, every derivative field through order `k` is `α`-Hölder on `Ω`, with constant `3 ‖f‖`.
  Below order `k`, `TauCeti.CkHolderSpaceOn.holderOnWith_iteratedFDeriv_of_lt` gives the sharper
  constant from the supremum norms of the field and the next one. Products and multiplication by
  coefficients are built on these in `TauCeti.Analysis.Holder.Product`.
* `TauCeti.CkHolderSpaceOn.inclusionSuccL`: on a convex open set and for `α ≤ 1`, the inclusion
  `C^{k+1,α}(Ω) → C^{k,α}(Ω)`, of operator norm at most `3`. On non-convex open sets the
  inclusion can fail: across a slit, the global Hölder seminorm of the `k`-th derivative is not
  controlled by the bound on the next derivative.
  `TauCeti.CkHolderSpaceOn.inclusionSuccLOfHolderOnWith` builds the inclusion on any open set from
  a uniform Hölder bound on the `k`-th derivative field of the elements of `C^{k+1,α}(Ω)`.

* `ContDiffOn.exists_ckHolderSpaceOn_ball`: local `C^{n,α}` data define an element on a positive
  ball with the original pointwise values, without an extra derivative or compactness assumption.

## References

D. Gilbarg and N. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
Section 4.1.
-/

public section

noncomputable section

namespace TauCeti

open TopologicalSpace
open scoped NNReal BoundedContinuousFunction

universe u v

variable (k : ℕ) (α : ℝ≥0) {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
  (Ω : Opens E) (F : Type v) [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Shortcut instance for bounded continuous fields of `n`-multilinear maps on `Ω`, for the same
reason as the corresponding local instance for `TauCeti.CkHolderSpace`: without it, instance
search for the module structure of `ℓ¹` products of these fields indexed by the order `n` exceeds
the default synthesis depth. No public statement below mentions it. -/
local instance CkHolderSpaceOn.instNormedAddCommGroupBoundedContinuousFunction (n : ℕ) :
    NormedAddCommGroup (Ω →ᵇ (E [×n]→L[ℝ] F)) :=
  inferInstance

/-- Shortcut instance for bounded continuous fields of `n`-multilinear maps on `Ω`. It is local
for the same reason. -/
local instance CkHolderSpaceOn.instNormedSpaceBoundedContinuousFunction (n : ℕ) :
    NormedSpace ℝ (Ω →ᵇ (E [×n]→L[ℝ] F)) :=
  inferInstance

/-- The space `C^{k,α}(Ω, F)` of maps on an open set `Ω` that are `C^k` on `Ω`, with iterated
Fréchet derivatives through order `k` bounded on `Ω` and `k`-th iterated derivative globally
`α`-Hölder on `Ω`. Its norm is

`∑_{i ≤ k} sup_{x ∈ Ω} ‖D^i f(x)‖ + [D^k f]_{α, Ω}`.
-/
-- The module system requires exposure while the declarations below construct and project through
-- this graph alias. The final `irreducible` attribute restores the abstraction boundary.
@[expose] def CkHolderSpaceOn : Type _ :=
  let graph : Submodule ℝ (CkHolderJet k α Ω E F) :=
    { carrier := {J | ∀ (j : Fin k) (x : Ω),
        HasFDerivAt
          (Function.extend Subtype.val (CkHolderJet.fieldL j.castSucc J : Ω → E [×j]→L[ℝ] F) 0)
          (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (j + 1) ↦ E) F
            (CkHolderJet.fieldL j.succ J x)) x}
      zero_mem' := fun j x ↦ by
        simp only [map_zero, FunLike.coe_zero, Function.extend_zero]
        exact hasFDerivAt_const (x := (x : E)) (c := (0 : E [×j]→L[ℝ] F))
      add_mem' := fun {J K} hJ hK j x ↦ by
        simp only [Set.mem_ofPred_eq, map_add, FunLike.coe_add, Pi.add_apply] at hJ hK ⊢
        have he := Function.extend_add (Subtype.val : Ω → E)
          (CkHolderJet.fieldL j.castSucc J : Ω → E [×j]→L[ℝ] F)
          (CkHolderJet.fieldL j.castSucc K) 0 0
        rw [add_zero] at he
        have h := (hJ j x).add (hK j x)
        rw [← he] at h
        exact h
      smul_mem' := fun c {J} hJ j x ↦ by
        simp only [Set.mem_ofPred_eq, map_smul, FunLike.coe_smul, Pi.smul_apply] at hJ ⊢
        have he := Function.extend_smul c (Subtype.val : Ω → E)
          (CkHolderJet.fieldL j.castSucc J : Ω → E [×j]→L[ℝ] F) 0
        rw [smul_zero] at he
        have h := (hJ j x).const_smul c
        rw [← he] at h
        exact h }
  graph

namespace CkHolderSpaceOn

open CkHolderJet

variable {k α Ω F}

/-- The extension by zero of a field on `Ω` to the whole space. -/
private def extendZero {G : Type*} [Zero G] (g : Ω → G) : E → G :=
  Function.extend Subtype.val g 0

omit [NormedSpace ℝ E] in
private theorem extendZero_coe {G : Type*} [Zero G] (g : Ω → G) (x : Ω) :
    extendZero g (x : E) = g x :=
  Subtype.val_injective.extend_apply g 0 x

/-- The derivative identities of a jet: each field below order `k`, extended by zero, has the
next field, curried on the left, as its Fréchet derivative at every point of `Ω`. -/
private def IsJetGraph (J : CkHolderJet k α Ω E F) : Prop :=
  ∀ (j : Fin k) (x : Ω), HasFDerivAt (extendZero (fieldL j.castSucc J : Ω → E [×j]→L[ℝ] F))
    (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (j + 1) ↦ E) F (fieldL j.succ J x)) x

/-- Elements are the jets satisfying the derivative identities. This is the identity map: the
carrier of `CkHolderSpaceOn` is the set of jets satisfying `IsJetGraph`. Besides this map, the
carrier is unfolded only by `toJetL`, the two norm instances, `norm_toJet` and
`instCompleteSpace`, which use that it is a submodule of the jet space. -/
private def equivSubtype : CkHolderSpaceOn k α Ω F ≃ {J : CkHolderJet k α Ω E F // IsJetGraph J} :=
  Equiv.refl _

/-- The underlying jet of an element. -/
private def toJet (f : CkHolderSpaceOn k α Ω F) : CkHolderJet k α Ω E F := (equivSubtype f).val

/-- An element from a jet satisfying the derivative identities. -/
private def mk (J : CkHolderJet k α Ω E F) (hJ : IsJetGraph J) : CkHolderSpaceOn k α Ω F :=
  equivSubtype.symm ⟨J, hJ⟩

private theorem toJet_injective :
    Function.Injective (toJet (k := k) (α := α) (Ω := Ω) (F := F)) :=
  fun _ _ h ↦ equivSubtype.injective (Subtype.ext h)

private theorem toJet_mk (J : CkHolderJet k α Ω E F) (hJ) : toJet (mk J hJ) = J := by
  rw [toJet, mk, Equiv.apply_symm_apply]

private theorem hasFDerivAt_fieldL (f : CkHolderSpaceOn k α Ω F) (j : Fin k) (x : Ω) :
    HasFDerivAt (extendZero (fieldL j.castSucc (toJet f) : Ω → E [×j]→L[ℝ] F))
      (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (j + 1) ↦ E) F
        (fieldL j.succ (toJet f) x)) x :=
  (equivSubtype f).property j x

/-- The `C^{k,α}(Ω)` norm makes the space a normed additive group. -/
instance instNormedAddCommGroup : NormedAddCommGroup (CkHolderSpaceOn k α Ω F) := by
  unfold CkHolderSpaceOn
  infer_instance

/-- The space `C^{k,α}(Ω)` is a real normed space. -/
instance instNormedSpace : NormedSpace ℝ (CkHolderSpaceOn k α Ω F) := by
  unfold CkHolderSpaceOn
  infer_instance

private theorem norm_toJet (f : CkHolderSpaceOn k α Ω F) : ‖toJet f‖ = ‖f‖ :=
  Submodule.norm_coe f

/-- The underlying jet, as a continuous linear map: the inclusion of the submodule
`CkHolderSpaceOn` into the jet space. -/
private def toJetL : CkHolderSpaceOn k α Ω F →L[ℝ] CkHolderJet k α Ω E F := by
  unfold CkHolderSpaceOn
  exact Submodule.subtypeL _

/-- The inclusion `toJetL` is `toJet`; both are the coercion of the submodule. -/
private theorem toJetL_apply (f : CkHolderSpaceOn k α Ω F) : toJetL f = toJet f :=
  rfl

/-- The bounded continuous `i`-th derivative field on `Ω` of an element of `C^{k,α}(Ω)`, for
`i ≤ k`. It agrees with Mathlib's `iteratedFDeriv` of any function on the whole space that agrees
with the element on `Ω`, by `CkHolderSpaceOn.iteratedFDeriv_eq`. -/
def iteratedFDeriv (f : CkHolderSpaceOn k α Ω F) (i : Fin (k + 1)) : Ω →ᵇ (E [×i]→L[ℝ] F) :=
  fieldL i (toJet f)

/-- The `k`-th derivative field of an element of `C^{k,α}(Ω)`, as an element of the bounded
Hölder space on `Ω`. -/
def iteratedFDerivHolder (f : CkHolderSpaceOn k α Ω F) : HolderSpace α Ω (E [×k]→L[ℝ] F) :=
  holderFieldL (toJet f)

/-- The underlying function on `Ω` of an element of `C^{k,α}(Ω)`: its order-zero derivative
field, evaluated on the empty tuple. Use the coercion `⇑f` instead. -/
def toFun (f : CkHolderSpaceOn k α Ω F) (x : Ω) : F :=
  (f.iteratedFDeriv ⟨0, k.succ_pos⟩ x).curry0

/-- The formal Taylor series recorded by an element on `Ω`, extended by zero outside `Ω` and
truncated after order `k`. -/
private def series (f : CkHolderSpaceOn k α Ω F) (x : E) : FormalMultilinearSeries ℝ E F :=
  fun m ↦ if h : m < k + 1 then extendZero (f.iteratedFDeriv ⟨m, h⟩ : Ω → E [×m]→L[ℝ] F) x
    else 0

private theorem series_of_lt (f : CkHolderSpaceOn k α Ω F) (x : E) {m : ℕ} (h : m < k + 1) :
    series f x m = extendZero (f.iteratedFDeriv ⟨m, h⟩ : Ω → E [×m]→L[ℝ] F) x := by
  simp [series, h]

/-- On `Ω`, the recorded derivative fields form a Taylor series up to order `k` for the
underlying function extended by zero. -/
private theorem hasFTaylorSeriesUpToOn (f : CkHolderSpaceOn k α Ω F) :
    HasFTaylorSeriesUpToOn k (extendZero f.toFun) (series f) Ω where
  zero_eq x hx := by
    lift x to Ω using hx
    rw [series_of_lt f x k.succ_pos, extendZero_coe, extendZero_coe, toFun]
  fderivWithin m hm x hx := by
    lift x to Ω using hx
    have hmk : m < k := by exact_mod_cast hm
    have hfun : (fun y ↦ series f y m) =
        extendZero (fieldL (⟨m, hmk⟩ : Fin k).castSucc (toJet f) : Ω → E [×m]→L[ℝ] F) :=
      funext fun y ↦ series_of_lt f y (by omega)
    rw [hfun, series_of_lt f x (by omega), extendZero_coe]
    -- `continuousMultilinearCurryLeftEquiv` applies `curryLeft`.
    exact (hasFDerivAt_fieldL f ⟨m, hmk⟩ x).hasFDerivWithinAt
  cont m hm := by
    have hmk : m < k + 1 := by
      have : m ≤ k := by exact_mod_cast hm
      omega
    rw [continuousOn_iff_continuous_domRestrict]
    have hfun : (Ω : Set E).domRestrict (fun y ↦ series f y m) =
        (f.iteratedFDeriv ⟨m, hmk⟩ : Ω → E [×m]→L[ℝ] F) :=
      funext fun y ↦ by rw [Set.domRestrict_apply, series_of_lt f _ hmk, extendZero_coe]
    rw [hfun]
    exact (f.iteratedFDeriv ⟨m, hmk⟩).continuous

/-- The recorded fields are the iterated derivatives, on `Ω`, of the extension by zero. -/
private theorem iteratedFDeriv_extendZero (f : CkHolderSpaceOn k α Ω F) (i : Fin (k + 1))
    (x : Ω) : _root_.iteratedFDeriv ℝ i (extendZero f.toFun) x = f.iteratedFDeriv i x := by
  rw [← iteratedFDerivWithin_of_isOpen i Ω.isOpen x.property,
    ← (hasFTaylorSeriesUpToOn f).eq_iteratedFDerivWithin_of_uniqueDiffOn
      (by exact_mod_cast i.is_le) Ω.isOpen.uniqueDiffOn x.property,
    series_of_lt f x i.isLt, extendZero_coe]

/-- An element of `C^{k,α}(Ω)` is determined by its underlying function on `Ω`. -/
theorem toFun_injective :
    Function.Injective (toFun (k := k) (α := α) (Ω := Ω) (F := F)) := by
  intro f g hfg
  have hfield : ∀ i, f.iteratedFDeriv i = g.iteratedFDeriv i := fun i ↦ by
    ext1 x
    rw [← iteratedFDeriv_extendZero, ← iteratedFDeriv_extendZero, hfg]
  exact toJet_injective (CkHolderJet.ext fun i ↦ by simpa only [iteratedFDeriv] using hfield i)

/-- An element of `C^{k,α}(Ω)` is coerced to its underlying function on `Ω`. -/
instance instFunLike : FunLike (CkHolderSpaceOn k α Ω F) Ω F where
  coe := toFun
  coe_injective := toFun_injective

/-- `CkHolderSpaceOn.toFun f` is equal to the coercion `⇑f` of `f` to a function. -/
@[simp]
theorem toFun_eq_coe (f : CkHolderSpaceOn k α Ω F) : f.toFun = ⇑f :=
  (rfl)

/-- Two elements of `C^{k,α}(Ω)` are equal when their underlying functions agree on `Ω`. -/
@[ext]
theorem ext {f g : CkHolderSpaceOn k α Ω F} (h : ∀ x, f x = g x) : f = g :=
  DFunLike.ext f g h

/-- A function on the whole space that agrees with an element of `C^{k,α}(Ω)` on `Ω` is `C^k`
on `Ω`. -/
theorem contDiffOn (f : CkHolderSpaceOn k α Ω F) {g : E → F} (hg : ∀ x : Ω, g x = f x) :
    ContDiffOn ℝ k g Ω :=
  ((hasFTaylorSeriesUpToOn f).congr fun x hx ↦ by
    lift x to Ω using hx
    rw [hg, extendZero_coe, toFun_eq_coe]).contDiffOn

/-- The recorded derivative fields are the iterated Fréchet derivatives, at points of `Ω`, of
every function on the whole space that agrees with the element on `Ω`. -/
theorem iteratedFDeriv_eq (f : CkHolderSpaceOn k α Ω F) {g : E → F} (hg : ∀ x : Ω, g x = f x)
    (i : Fin (k + 1)) (x : Ω) :
    _root_.iteratedFDeriv ℝ i g x = f.iteratedFDeriv i x := by
  have hEq : Set.EqOn g (extendZero f.toFun) Ω := fun y hy ↦ by
    lift y to Ω using hy
    rw [hg, extendZero_coe, toFun_eq_coe]
  rw [← iteratedFDerivWithin_of_isOpen i Ω.isOpen x.property, iteratedFDerivWithin_congr hEq
      x.property,
    iteratedFDerivWithin_of_isOpen i Ω.isOpen x.property, iteratedFDeriv_extendZero]

/-- The Hölder field, as a bounded continuous field, is the derivative field of order `k`. -/
@[simp]
theorem toBoundedContinuousFunction_iteratedFDerivHolder (f : CkHolderSpaceOn k α Ω F) :
    f.iteratedFDerivHolder.toBoundedContinuousFunction = f.iteratedFDeriv (Fin.last k) := by
  rw [iteratedFDeriv, iteratedFDerivHolder, toBoundedContinuousFunction_holderFieldL]

/-- The Hölder field is the derivative field of order `k`. -/
@[simp]
theorem coe_iteratedFDerivHolder (f : CkHolderSpaceOn k α Ω F) :
    (f.iteratedFDerivHolder : Ω → E [×k]→L[ℝ] F) = f.iteratedFDeriv (Fin.last k) := by
  rw [← HolderSpace.coe_toBoundedContinuousFunction,
    toBoundedContinuousFunction_iteratedFDerivHolder]

/-- The derivative field of order `k` is globally `α`-Hölder on `Ω`. -/
theorem memHolder_iteratedFDeriv (f : CkHolderSpaceOn k α Ω F) :
    MemHolder α (f.iteratedFDeriv (Fin.last k) : Ω → E [×k]→L[ℝ] F) := by
  rw [← coe_iteratedFDerivHolder, ← HolderSpace.coe_toBoundedContinuousFunction]
  exact f.iteratedFDerivHolder.memHolder

/-- The `k`-th iterated Fréchet derivative of a function agreeing with an element of `C^{k,α}(Ω)`
on `Ω` is `α`-Hölder on `Ω`, with constant the Hölder seminorm of the `k`-th field. -/
theorem holderOnWith_iteratedFDeriv (f : CkHolderSpaceOn k α Ω F) {g : E → F}
    (hg : ∀ x : Ω, g x = f x) :
    HolderOnWith (nnHolderNorm α (f.iteratedFDeriv (Fin.last k) : Ω → E [×k]→L[ℝ] F)) α
      (_root_.iteratedFDeriv ℝ k g) Ω := by
  rw [← HolderWith.restrict_iff]
  have he : (Ω : Set E).domRestrict (_root_.iteratedFDeriv ℝ k g) =
      (f.iteratedFDeriv (Fin.last k) : Ω → E [×k]→L[ℝ] F) :=
    funext fun x ↦ f.iteratedFDeriv_eq hg (Fin.last k) x
  rw [he]
  exact f.memHolder_iteratedFDeriv.holderWith

/-- The `C^{k,α}(Ω)` norm is the sum of the supremum norms on `Ω` of the derivative fields
through order `k` and the `α`-Hölder seminorm on `Ω` of the `k`-th field. -/
theorem norm_eq (f : CkHolderSpaceOn k α Ω F) :
    ‖f‖ = ∑ i : Fin (k + 1), ‖f.iteratedFDeriv i‖ +
      nnHolderNorm α (f.iteratedFDeriv (Fin.last k) : Ω → E [×k]→L[ℝ] F) := by
  rw [← norm_toJet, CkHolderJet.norm_eq]
  simp only [iteratedFDeriv]

/-- The sum of the supremum norms of the derivative fields is controlled by the `C^{k,α}(Ω)`
norm. -/
theorem sum_norm_iteratedFDeriv_le (f : CkHolderSpaceOn k α Ω F) :
    ∑ i : Fin (k + 1), ‖f.iteratedFDeriv i‖ ≤ ‖f‖ := by
  rw [norm_eq]
  exact le_add_of_nonneg_right (NNReal.coe_nonneg _)

/-- The supremum norm of each derivative field is controlled by the `C^{k,α}(Ω)` norm. -/
theorem norm_iteratedFDeriv_le (f : CkHolderSpaceOn k α Ω F) (i : Fin (k + 1)) :
    ‖f.iteratedFDeriv i‖ ≤ ‖f‖ :=
  (Finset.single_le_sum (fun j _ ↦ norm_nonneg (f.iteratedFDeriv j))
    (Finset.mem_univ i)).trans f.sum_norm_iteratedFDeriv_le

/-- The values of an element of `C^{k,α}(Ω)` are controlled by its norm. -/
theorem norm_apply_le (f : CkHolderSpaceOn k α Ω F) (x : Ω) : ‖f x‖ ≤ ‖f‖ := by
  calc ‖f x‖ = ‖f.iteratedFDeriv 0 x‖ := by
        rw [← f.iteratedFDeriv_eq (fun y ↦ extendZero_coe f y), Fin.val_zero,
          norm_iteratedFDeriv_zero, extendZero_coe]
    _ ≤ ‖f.iteratedFDeriv 0‖ := (f.iteratedFDeriv 0).norm_coe_le_norm x
    _ ≤ ‖f‖ := norm_iteratedFDeriv_le f 0

/-- The `α`-Hölder seminorm on `Ω` of the `k`-th field is controlled by the `C^{k,α}(Ω)`
norm. -/
theorem nnHolderNorm_iteratedFDeriv_le (f : CkHolderSpaceOn k α Ω F) :
    (nnHolderNorm α (f.iteratedFDeriv (Fin.last k) : Ω → E [×k]→L[ℝ] F) : ℝ) ≤ ‖f‖ := by
  rw [norm_eq]
  exact le_add_of_nonneg_left (Finset.sum_nonneg fun j _ ↦ norm_nonneg _)

/-- At points of `Ω`, each iterated derivative through order `k` of a function agreeing with an
element of `C^{k,α}(Ω)` on `Ω` is bounded by the supremum norm of the corresponding field. -/
theorem norm_iteratedFDeriv_apply_le_norm_iteratedFDeriv (f : CkHolderSpaceOn k α Ω F)
    {g : E → F} (hg : ∀ x : Ω, g x = f x) (i : Fin (k + 1)) (x : Ω) :
    ‖_root_.iteratedFDeriv ℝ i g x‖ ≤ ‖f.iteratedFDeriv i‖ :=
  (congrArg norm (f.iteratedFDeriv_eq hg i x)).trans_le ((f.iteratedFDeriv i).norm_coe_le_norm x)

/-- On a convex open set and for `α ≤ 1`, every iterated derivative below order `k` of a function
agreeing with an element of `C^{k,α}(Ω)` on `Ω` is `α`-Hölder on `Ω`, with constant controlled by
the supremum norms of the fields of that order and the next. -/
theorem holderOnWith_iteratedFDeriv_of_lt (f : CkHolderSpaceOn k α Ω F) {g : E → F}
    (hg : ∀ x : Ω, g x = f x) (hconv : Convex ℝ (Ω : Set E)) (hα : α ≤ 1) {j : ℕ}
    (hj : j < k) :
    HolderOnWith (‖f.iteratedFDeriv ⟨j + 1, by omega⟩‖₊ + 2 * ‖f.iteratedFDeriv ⟨j, by omega⟩‖₊)
      α (_root_.iteratedFDeriv ℝ j g) Ω :=
  (f.contDiffOn hg).holderOnWith_iteratedFDeriv_of_lt Ω.isOpen hconv hj hα
    (fun x hx ↦ f.norm_iteratedFDeriv_apply_le_norm_iteratedFDeriv hg ⟨j, by omega⟩ ⟨x, hx⟩)
    (fun x hx ↦ f.norm_iteratedFDeriv_apply_le_norm_iteratedFDeriv hg ⟨j + 1, by omega⟩ ⟨x, hx⟩)

/-- On a convex open set and for `α ≤ 1`, every iterated derivative through order `k` of a
function agreeing with an element of `C^{k,α}(Ω)` on `Ω` is `α`-Hölder on `Ω`, with constant
`3 ‖f‖`. Below the top order some geometric condition on `Ω` is needed: on the slit annulus
described at `TauCeti.CkHolderSpaceOn.inclusionSuccL` the angle function lies in `C^{1,α}(Ω)` but
is not `α`-Hölder on `Ω`. -/
theorem holderOnWith_iteratedFDeriv_of_le (f : CkHolderSpaceOn k α Ω F) {g : E → F}
    (hg : ∀ x : Ω, g x = f x) (hconv : Convex ℝ (Ω : Set E)) (hα : α ≤ 1) {j : ℕ}
    (hj : j ≤ k) :
    HolderOnWith (3 * ‖f‖₊) α (_root_.iteratedFDeriv ℝ j g) Ω := by
  rcases hj.eq_or_lt with rfl | hj
  · refine (f.holderOnWith_iteratedFDeriv hg).mono_const ?_
    rw [← NNReal.coe_le_coe]
    push_cast
    nlinarith [f.nnHolderNorm_iteratedFDeriv_le, norm_nonneg f]
  · refine (f.holderOnWith_iteratedFDeriv_of_lt hg hconv hα hj).mono_const ?_
    rw [← NNReal.coe_le_coe]
    push_cast
    linarith [norm_iteratedFDeriv_le f ⟨j + 1, by omega⟩, norm_iteratedFDeriv_le f ⟨j, by omega⟩]

/-- The `C^{k,α}(Ω)` norm is at most `∑ᵢ Mᵢ + K` when the `i`-th derivative field is bounded by
`Mᵢ ≥ 0` on `Ω` and the `k`-th field is `α`-Hölder with constant `K`. -/
theorem norm_le_sum_add_of_norm_iteratedFDeriv_le_of_holderWith {f : CkHolderSpaceOn k α Ω F}
    {M : Fin (k + 1) → ℝ} (hM0 : ∀ i, 0 ≤ M i) (hM : ∀ i x, ‖f.iteratedFDeriv i x‖ ≤ M i)
    {K : ℝ≥0} (hK : HolderWith K α (f.iteratedFDeriv (Fin.last k) : Ω → E [×k]→L[ℝ] F)) :
    ‖f‖ ≤ ∑ i, M i + K := by
  rw [norm_eq]
  gcongr with i
  · exact (BoundedContinuousFunction.norm_le (hM0 i)).2 (hM i)
  · exact_mod_cast hK.nnholderNorm_le

/-- The `i`-th derivative field, as a continuous linear map to bounded continuous fields on `Ω`.
It is bounded by the `C^{k,α}(Ω)` norm pointwise, by `CkHolderSpaceOn.norm_iteratedFDeriv_le`. -/
def iteratedFDerivL (i : Fin (k + 1)) :
    CkHolderSpaceOn k α Ω F →L[ℝ] (Ω →ᵇ (E [×i]→L[ℝ] F)) :=
  (fieldL i).comp toJetL

/-- The linear map `iteratedFDerivL i` sends an element to its `i`-th derivative field. -/
@[simp]
theorem iteratedFDerivL_apply (i : Fin (k + 1)) (f : CkHolderSpaceOn k α Ω F) :
    iteratedFDerivL i f = f.iteratedFDeriv i := by
  rw [iteratedFDerivL, ContinuousLinearMap.comp_apply, toJetL_apply, iteratedFDeriv]

/-- The `k`-th derivative field, as a continuous linear map to the bounded Hölder space on
`Ω`. -/
def iteratedFDerivHolderL : CkHolderSpaceOn k α Ω F →L[ℝ] HolderSpace α Ω (E [×k]→L[ℝ] F) :=
  holderFieldL.comp toJetL

/-- The linear map `iteratedFDerivHolderL` sends an element to its `k`-th derivative field in the
bounded Hölder space. -/
@[simp]
theorem iteratedFDerivHolderL_apply (f : CkHolderSpaceOn k α Ω F) :
    iteratedFDerivHolderL f = f.iteratedFDerivHolder := by
  rw [iteratedFDerivHolderL, ContinuousLinearMap.comp_apply, toJetL_apply, iteratedFDerivHolder]

/-- The Hölder-space norm of the `k`-th derivative field is controlled by the `C^{k,α}(Ω)`
norm. -/
theorem norm_iteratedFDerivHolder_le (f : CkHolderSpaceOn k α Ω F) :
    ‖f.iteratedFDerivHolder‖ ≤ ‖f‖ := by
  rw [← norm_toJet, WithLp.prod_norm_eq_of_L1, iteratedFDerivHolder, holderFieldL_apply]
  exact le_add_of_nonneg_left (norm_nonneg _)

/-- The `k`-th derivative map to the bounded Hölder space has operator norm at most one. -/
theorem norm_iteratedFDerivHolderL_le_one :
    ‖iteratedFDerivHolderL (k := k) (α := α) (Ω := Ω) (F := F)‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun f ↦ by
    rw [iteratedFDerivHolderL_apply, one_mul]
    exact norm_iteratedFDerivHolder_le f

/-- Each derivative field of the zero element is zero. -/
@[simp]
theorem iteratedFDeriv_zero (i : Fin (k + 1)) :
    (0 : CkHolderSpaceOn k α Ω F).iteratedFDeriv i = 0 := by
  simpa only [iteratedFDerivL_apply] using (iteratedFDerivL (α := α) (Ω := Ω) (F := F) i).map_zero

/-- Each derivative field is additive. -/
@[simp]
theorem iteratedFDeriv_add (f g : CkHolderSpaceOn k α Ω F) (i : Fin (k + 1)) :
    (f + g).iteratedFDeriv i = f.iteratedFDeriv i + g.iteratedFDeriv i := by
  simpa only [iteratedFDerivL_apply] using (iteratedFDerivL i).map_add f g

/-- Each derivative field commutes with scalar multiplication. -/
@[simp]
theorem iteratedFDeriv_smul (c : ℝ) (f : CkHolderSpaceOn k α Ω F) (i : Fin (k + 1)) :
    (c • f).iteratedFDeriv i = c • f.iteratedFDeriv i := by
  simpa only [iteratedFDerivL_apply] using (iteratedFDerivL i).map_smul c f

/-- The `k`-th derivative field of the zero element, in the bounded Hölder space, is zero. -/
@[simp]
theorem iteratedFDerivHolder_zero :
    (0 : CkHolderSpaceOn k α Ω F).iteratedFDerivHolder = 0 := by
  simpa only [iteratedFDerivHolderL_apply] using
    (iteratedFDerivHolderL (k := k) (α := α) (Ω := Ω) (F := F)).map_zero

/-- The `k`-th derivative field, in the bounded Hölder space, is additive. -/
@[simp]
theorem iteratedFDerivHolder_add (f g : CkHolderSpaceOn k α Ω F) :
    (f + g).iteratedFDerivHolder = f.iteratedFDerivHolder + g.iteratedFDerivHolder := by
  simpa only [iteratedFDerivHolderL_apply] using iteratedFDerivHolderL.map_add f g

/-- The `k`-th derivative field, in the bounded Hölder space, commutes with scalar
multiplication. -/
@[simp]
theorem iteratedFDerivHolder_smul (c : ℝ) (f : CkHolderSpaceOn k α Ω F) :
    (c • f).iteratedFDerivHolder = c • f.iteratedFDerivHolder := by
  simpa only [iteratedFDerivHolderL_apply] using iteratedFDerivHolderL.map_smul c f

/-- The underlying function of the zero element is zero. -/
@[simp]
theorem coe_zero : ⇑(0 : CkHolderSpaceOn k α Ω F) = 0 := by
  ext x
  simp only [← toFun_eq_coe, toFun, iteratedFDeriv_zero, FunLike.coe_zero,
    Pi.zero_apply]
  simp

/-- The underlying function of a sum is the sum of the underlying functions. -/
@[simp]
theorem coe_add (f g : CkHolderSpaceOn k α Ω F) : ⇑(f + g) = f + g := by
  ext x
  simp only [← toFun_eq_coe, toFun, iteratedFDeriv_add, FunLike.coe_add,
    Pi.add_apply]
  simp

/-- The underlying function of a scalar multiple is the scalar multiple of the underlying
function. -/
@[simp]
theorem coe_smul (c : ℝ) (f : CkHolderSpaceOn k α Ω F) : ⇑(c • f) = c • ⇑f := by
  ext x
  simp only [← toFun_eq_coe, toFun, iteratedFDeriv_smul, FunLike.coe_smul,
    Pi.smul_apply]
  simp

/-- The derivative field of order zero has the norm of the underlying function at each point. -/
theorem norm_iteratedFDeriv_zero (f : CkHolderSpaceOn k α Ω F) (x : Ω) :
    ‖f.iteratedFDeriv 0 x‖ = ‖f x‖ := by
  rw [← toFun_eq_coe, toFun]
  exact ((continuousMultilinearCurryFin0 ℝ E F).norm_map _).symm

/-- The values of an element of `C^{k,α}(Ω)` are controlled by the supremum norm of its order-zero
field. -/
theorem norm_apply_le_iteratedFDeriv_zero (f : CkHolderSpaceOn k α Ω F) (x : Ω) :
    ‖f x‖ ≤ ‖f.iteratedFDeriv 0‖ := by
  rw [← norm_iteratedFDeriv_zero]
  exact (f.iteratedFDeriv 0).norm_coe_le_norm x

/-- The iterated derivatives through order `k` of a function that agrees with an element of
`C^{k,α}(Ω)` on `Ω` are controlled on `Ω` by the `C^{k,α}(Ω)` norm. -/
theorem norm_iteratedFDeriv_apply_le (f : CkHolderSpaceOn k α Ω F) {g : E → F}
    (hg : ∀ x : Ω, g x = f x) {i : ℕ} (hi : i ≤ k) (x : Ω) :
    ‖_root_.iteratedFDeriv ℝ i g x‖ ≤ ‖f‖ := by
  rw [f.iteratedFDeriv_eq hg ⟨i, Nat.lt_succ_of_le hi⟩]
  exact ((f.iteratedFDeriv _).norm_coe_le_norm x).trans (norm_iteratedFDeriv_le f _)

/-- The extension by zero of an element of `C^{k,α}(Ω)` to a function on `E`. It agrees with the
element on `Ω`, so it is a representative to which `CkHolderSpaceOn.iteratedFDeriv_eq`,
`CkHolderSpaceOn.contDiffOn` and `CkHolderSpaceOn.holderOnWith_iteratedFDeriv` apply. -/
def extend (f : CkHolderSpaceOn k α Ω F) : E → F :=
  Function.extend Subtype.val f 0

/-- The extension by zero agrees with the element on `Ω`. -/
@[simp]
theorem extend_apply (f : CkHolderSpaceOn k α Ω F) (x : Ω) : f.extend x = f x :=
  Subtype.val_injective.extend_apply _ _ x

/-- The extension by zero agrees with the element at each point of `Ω`. -/
theorem extend_apply_of_mem (f : CkHolderSpaceOn k α Ω F) {x : E} (hx : x ∈ Ω) :
    f.extend x = f ⟨x, hx⟩ :=
  f.extend_apply ⟨x, hx⟩

/-- The extension by zero of an element of `C^{k,α}(Ω)` is `k` times continuously differentiable
on `Ω`. -/
theorem contDiffOn_extend (f : CkHolderSpaceOn k α Ω F) : ContDiffOn ℝ k f.extend Ω :=
  f.contDiffOn f.extend_apply

/-- The iterated derivatives of the extension by zero at points of `Ω` are the derivative fields. -/
theorem iteratedFDeriv_extend (f : CkHolderSpaceOn k α Ω F) (i : Fin (k + 1)) (x : Ω) :
    _root_.iteratedFDeriv ℝ i f.extend x = f.iteratedFDeriv i x :=
  f.iteratedFDeriv_eq f.extend_apply i x

/-- Elements of `C^{k,α}(Ω)` and `C^{k,β}(Ω)` that agree pointwise have the same derivative
fields: both are the iterated derivatives of any common representative on the whole space. -/
theorem iteratedFDeriv_eq_of_coe_eq {β : ℝ≥0} {f : CkHolderSpaceOn k α Ω F}
    {g : CkHolderSpaceOn k β Ω F} (h : ∀ x, f x = g x) (i : Fin (k + 1)) :
    f.iteratedFDeriv i = g.iteratedFDeriv i := by
  ext1 x
  rw [← g.iteratedFDeriv_extend, f.iteratedFDeriv_eq fun y ↦ by rw [g.extend_apply, h]]

/-- The `k`-th iterated derivative of the extension by zero is `α`-Hölder on `Ω`, with constant the
Hölder seminorm of the derivative field of order `k`. -/
theorem holderOnWith_iteratedFDeriv_extend (f : CkHolderSpaceOn k α Ω F) :
    HolderOnWith (nnHolderNorm α (f.iteratedFDeriv (Fin.last k) : Ω → E [×k]→L[ℝ] F)) α
      (_root_.iteratedFDeriv ℝ k f.extend) Ω :=
  f.holderOnWith_iteratedFDeriv f.extend_apply

/-- An element of `C^{0,α}(Ω)` is `α`-Hölder on `Ω`: its extension by zero is `α`-Hölder on `Ω`,
with constant the Hölder seminorm of the derivative field of order zero. -/
theorem holderOnWith_extend (f : CkHolderSpaceOn 0 α Ω F) :
    HolderOnWith (nnHolderNorm α (f.iteratedFDeriv (Fin.last 0) : Ω → E [×0]→L[ℝ] F)) α
      f.extend Ω :=
  holderOnWith_iteratedFDeriv_zero_iff.1 f.holderOnWith_iteratedFDeriv_extend

/-- **Hölder exponents above one.** For `α > 1` and a preconnected `Ω`, the derivative field of
order `k` of an element of `C^{k,α}(Ω)` is constant on `Ω`. -/
theorem iteratedFDeriv_last_apply_eq_apply_of_one_lt (hα : 1 < α)
    (hΩ : IsPreconnected (Ω : Set E)) (f : CkHolderSpaceOn k α Ω F) (x y : Ω) :
    f.iteratedFDeriv (Fin.last k) x = f.iteratedFDeriv (Fin.last k) y := by
  rw [← f.iteratedFDeriv_extend, ← f.iteratedFDeriv_extend]
  exact f.holderOnWith_iteratedFDeriv_extend.eq_of_one_lt hα Ω.isOpen hΩ x.property y.property

/-- For `α > 1` and a preconnected `Ω`, the space `C^{0,α}(Ω)` consists of constant functions. -/
theorem apply_eq_apply_of_one_lt (hα : 1 < α) (hΩ : IsPreconnected (Ω : Set E))
    (f : CkHolderSpaceOn 0 α Ω F) (x y : Ω) : f x = f y := by
  rw [← f.extend_apply, ← f.extend_apply]
  exact f.holderOnWith_extend.eq_of_one_lt hα Ω.isOpen hΩ x.property y.property

/-- The iterated derivatives through order `k` of the extension by zero are controlled on `Ω` by
the `C^{k,α}(Ω)` norm. -/
theorem norm_iteratedFDeriv_extend_le (f : CkHolderSpaceOn k α Ω F) {i : ℕ} (hi : i ≤ k)
    (x : Ω) : ‖_root_.iteratedFDeriv ℝ i f.extend x‖ ≤ ‖f‖ :=
  f.norm_iteratedFDeriv_apply_le f.extend_apply hi x

/-- The underlying function on `Ω` of an element of `C^{k,α}(Ω)` is continuous. -/
theorem continuous (f : CkHolderSpaceOn k α Ω F) : Continuous f := by
  have h := continuousOn_iff_continuous_domRestrict.1 f.contDiffOn_extend.continuousOn
  convert h using 1
  funext x
  exact (f.extend_apply x).symm

/-- The underlying function on `Ω` of an element of `C^{k,α}(Ω)`, as a bounded continuous
function. -/
def toBoundedContinuousFunction (f : CkHolderSpaceOn k α Ω F) : Ω →ᵇ F :=
  BoundedContinuousFunction.ofNormedAddCommGroup f f.continuous ‖f‖ f.norm_apply_le

@[simp]
theorem coe_toBoundedContinuousFunction (f : CkHolderSpaceOn k α Ω F) :
    ⇑f.toBoundedContinuousFunction = f :=
  BoundedContinuousFunction.coe_ofNormedAddCommGroup ..

/-- The underlying bounded continuous function has norm at most the `C^{k,α}(Ω)` norm. -/
theorem norm_toBoundedContinuousFunction_le (f : CkHolderSpaceOn k α Ω F) :
    ‖f.toBoundedContinuousFunction‖ ≤ ‖f‖ :=
  BoundedContinuousFunction.norm_ofNormedAddCommGroup_le _ (norm_nonneg f) _

/-- An element of `C^{k,α}(Ω)` is determined by its underlying bounded continuous function. -/
theorem toBoundedContinuousFunction_injective :
    Function.Injective (toBoundedContinuousFunction : CkHolderSpaceOn k α Ω F → Ω →ᵇ F) :=
  fun _ _ h ↦ ext fun x ↦ by simpa using DFunLike.congr_fun h x

/-- The supremum norm of the underlying function is that of the order-zero derivative field. -/
theorem norm_toBoundedContinuousFunction (f : CkHolderSpaceOn k α Ω F) :
    ‖f.toBoundedContinuousFunction‖ = ‖f.iteratedFDeriv 0‖ := by
  rw [BoundedContinuousFunction.norm_eq_iSup_norm,
    BoundedContinuousFunction.norm_eq_iSup_norm (f.iteratedFDeriv 0),
    coe_toBoundedContinuousFunction]
  congr 1 with x
  exact (norm_iteratedFDeriv_zero f x).symm

/-- The underlying bounded continuous function of a sum. -/
@[simp]
theorem toBoundedContinuousFunction_add (f g : CkHolderSpaceOn k α Ω F) :
    (f + g).toBoundedContinuousFunction =
      f.toBoundedContinuousFunction + g.toBoundedContinuousFunction := by
  ext x
  simp

/-- The underlying bounded continuous function of a scalar multiple. -/
@[simp]
theorem toBoundedContinuousFunction_smul (c : ℝ) (f : CkHolderSpaceOn k α Ω F) :
    (c • f).toBoundedContinuousFunction = c • f.toBoundedContinuousFunction := by
  ext x
  simp

/-- Forgetting the derivatives is a continuous linear map to bounded continuous functions on `Ω`.
-/
def toBoundedContinuousFunctionCLM : CkHolderSpaceOn k α Ω F →L[ℝ] (Ω →ᵇ F) :=
  LinearMap.mkContinuous
    { toFun := toBoundedContinuousFunction
      map_add' := toBoundedContinuousFunction_add
      map_smul' := toBoundedContinuousFunction_smul } 1 fun f ↦ by
        rw [one_mul]
        exact norm_toBoundedContinuousFunction_le f

@[simp]
theorem toBoundedContinuousFunctionCLM_apply (f : CkHolderSpaceOn k α Ω F) :
    toBoundedContinuousFunctionCLM f = f.toBoundedContinuousFunction := (rfl)

/-- Evaluating the extension by zero at a point of `Ω` is continuous on `C^{k,α}(Ω)`. -/
theorem continuous_extend_apply {x : E} (hx : x ∈ Ω) :
    Continuous fun f : CkHolderSpaceOn k α Ω F ↦ f.extend x := by
  have h := (BoundedContinuousFunction.evalCLM ℝ (⟨x, hx⟩ : Ω)).continuous.comp
    (toBoundedContinuousFunctionCLM (k := k) (α := α) (F := F)).continuous
  convert h using 2 with f
  rw [Function.comp_apply, toBoundedContinuousFunctionCLM_apply,
    BoundedContinuousFunction.evalCLM_apply, coe_toBoundedContinuousFunction, ← extend_apply]

/-- Forgetting the derivatives has operator norm at most one. -/
theorem norm_toBoundedContinuousFunctionCLM_le_one :
    ‖toBoundedContinuousFunctionCLM (k := k) (α := α) (Ω := Ω) (F := F)‖ ≤ 1 :=
  LinearMap.mkContinuous_norm_le _ zero_le_one _

/-- The jet of iterated derivatives on `Ω` of a function that is `C^k` on `Ω`, with bounded
derivatives through order `k` on `Ω` and `α`-Hölder `k`-th derivative on `Ω`. -/
private def jetOf (g : E → F) (hg : ContDiffOn ℝ k g Ω)
    (hbdd : ∀ i ≤ k, ∃ C, ∀ x : Ω, ‖_root_.iteratedFDeriv ℝ i g x‖ ≤ C)
    (hholder : MemHolder α fun x : Ω ↦ _root_.iteratedFDeriv ℝ k g x) : CkHolderJet k α Ω E F :=
  ofFields
    (fun j : Fin k ↦ BoundedContinuousFunction.ofContinuousOn (_root_.iteratedFDeriv ℝ j g)
      (ContinuousOn.continuousOn_iteratedFDeriv hg Ω.isOpen (by exact_mod_cast j.isLt.le))
      ((hbdd j j.isLt.le).elim fun C hC ↦
        isBounded_iff_forall_norm_le.2 ⟨C, Set.forall_mem_image.2 fun x hx ↦ hC ⟨x, hx⟩⟩))
    (HolderSpace.ofBoundedContinuousFunction
      (BoundedContinuousFunction.ofContinuousOn (_root_.iteratedFDeriv ℝ k g)
        (ContinuousOn.continuousOn_iteratedFDeriv hg Ω.isOpen le_rfl)
        ((hbdd k le_rfl).elim fun C hC ↦
          isBounded_iff_forall_norm_le.2 ⟨C, Set.forall_mem_image.2 fun x hx ↦ hC ⟨x, hx⟩⟩))
      (by rwa [BoundedContinuousFunction.coe_ofContinuousOn]))

private theorem fieldL_jetOf (g : E → F) (hg : ContDiffOn ℝ k g Ω)
    (hbdd : ∀ i ≤ k, ∃ C, ∀ x : Ω, ‖_root_.iteratedFDeriv ℝ i g x‖ ≤ C)
    (hholder : MemHolder α fun x : Ω ↦ _root_.iteratedFDeriv ℝ k g x) (i : Fin (k + 1))
    (x : Ω) : fieldL i (jetOf g hg hbdd hholder) x = _root_.iteratedFDeriv ℝ i g x := by
  induction i using Fin.lastCases with
  | last =>
    rw [jetOf, fieldL_last_ofFields,
      HolderSpace.toBoundedContinuousFunction_ofBoundedContinuousFunction]
    exact BoundedContinuousFunction.ofContinuousOn_apply _ _ _ x
  | cast j =>
    rw [jetOf, fieldL_castSucc_ofFields]
    exact BoundedContinuousFunction.ofContinuousOn_apply _ _ _ x

private theorem isJetGraph_jetOf (g : E → F) (hg : ContDiffOn ℝ k g Ω)
    (hbdd : ∀ i ≤ k, ∃ C, ∀ x : Ω, ‖_root_.iteratedFDeriv ℝ i g x‖ ≤ C)
    (hholder : MemHolder α fun x : Ω ↦ _root_.iteratedFDeriv ℝ k g x) :
    IsJetGraph (jetOf g hg hbdd hholder) := fun j x ↦ by
  have hEq : extendZero (fieldL j.castSucc (jetOf g hg hbdd hholder) : Ω → E [×j]→L[ℝ] F)
      =ᶠ[nhds (x : E)] _root_.iteratedFDeriv ℝ j g := by
    filter_upwards [Ω.isOpen.mem_nhds x.property] with y hy
    lift y to Ω using hy
    rw [extendZero_coe]
    exact fieldL_jetOf g hg hbdd hholder j.castSucc y
  have h := ((hg.contDiffAt (Ω.isOpen.mem_nhds x.property)).differentiableAt_iteratedFDeriv
    (m := j) (by exact_mod_cast j.isLt)).hasFDerivAt
  rw [fderiv_iteratedFDeriv, Function.comp_apply] at h
  rw [fieldL_jetOf]
  -- `continuousMultilinearCurryLeftEquiv` applies `curryLeft`.
  exact h.congr_of_eventuallyEq hEq

/-- The element of `C^{k,α}(Ω)` defined by a function on the whole space that is `C^k` on `Ω`,
whose iterated derivatives through order `k` are bounded on `Ω`, and whose `k`-th iterated
derivative is globally `α`-Hölder on `Ω`. -/
def ofContDiffOn (g : E → F) (hg : ContDiffOn ℝ k g Ω)
    (hbdd : ∀ i ≤ k, ∃ C, ∀ x : Ω, ‖_root_.iteratedFDeriv ℝ i g x‖ ≤ C)
    (hholder : MemHolder α fun x : Ω ↦ _root_.iteratedFDeriv ℝ k g x) :
    CkHolderSpaceOn k α Ω F :=
  mk (jetOf g hg hbdd hholder) (isJetGraph_jetOf g hg hbdd hholder)

/-- The derivative fields of `ofContDiffOn g` are the iterated derivatives of `g` on `Ω`. -/
@[simp]
theorem iteratedFDeriv_ofContDiffOn (g : E → F) (hg : ContDiffOn ℝ k g Ω)
    (hbdd : ∀ i ≤ k, ∃ C, ∀ x : Ω, ‖_root_.iteratedFDeriv ℝ i g x‖ ≤ C)
    (hholder : MemHolder α fun x : Ω ↦ _root_.iteratedFDeriv ℝ k g x) (i : Fin (k + 1))
    (x : Ω) :
    (ofContDiffOn g hg hbdd hholder).iteratedFDeriv i x = _root_.iteratedFDeriv ℝ i g x := by
  rw [iteratedFDeriv, ofContDiffOn, toJet_mk, fieldL_jetOf]

/-- The underlying function of `ofContDiffOn g` is the restriction of `g` to `Ω`. -/
@[simp]
theorem ofContDiffOn_apply (g : E → F) (hg : ContDiffOn ℝ k g Ω)
    (hbdd : ∀ i ≤ k, ∃ C, ∀ x : Ω, ‖_root_.iteratedFDeriv ℝ i g x‖ ≤ C)
    (hholder : MemHolder α fun x : Ω ↦ _root_.iteratedFDeriv ℝ k g x) (x : Ω) :
    ofContDiffOn g hg hbdd hholder x = g x := by
  rw [← toFun_eq_coe, toFun, iteratedFDeriv_ofContDiffOn, iteratedFDeriv_zero_eq_comp]
  simp

/-- The derivative identities are closed under uniform convergence of the fields. -/
private theorem isClosed_isJetGraph : IsClosed {J : CkHolderJet k α Ω E F | IsJetGraph J} := by
  have hset : {J : CkHolderJet k α Ω E F | IsJetGraph J} =
      ⋂ j : Fin k, (fun J : CkHolderJet k α Ω E F ↦ (fieldL j.castSucc J, fieldL j.succ J)) ⁻¹'
        {J | ∀ x : Ω, HasFDerivAt (extendZero (J.1 : Ω → E [×j]→L[ℝ] F))
          (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (j + 1) ↦ E) F (J.2 x)) x} := by
    ext J
    simp [IsJetGraph]
  rw [hset]
  exact isClosed_iInter fun j ↦
    (isClosed_setOf_hasFDerivAt_extend_comp Ω.isOpen
      (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (j + 1) ↦ E) F)
      (continuousMultilinearCurryLeftEquiv ℝ _ F).isometry.uniformContinuous).preimage
      ((fieldL (k := k) (α := α) (X := Ω) (E := E) (F := F) _).continuous.prodMk
        (fieldL (k := k) (α := α) (X := Ω) (E := E) (F := F) _).continuous)

/-- The space `C^{k,α}(Ω)` with values in a Banach space is a Banach space. -/
instance instCompleteSpace [CompleteSpace F] : CompleteSpace (CkHolderSpaceOn k α Ω F) := by
  unfold CkHolderSpaceOn
  exact isClosed_isJetGraph.completeSpace_coe

attribute [irreducible] instNormedAddCommGroup instNormedSpace _root_.TauCeti.CkHolderSpaceOn

/-- If the derivative fields of an element of `C^{k,α}(Ω)` are the pullbacks of bounded
continuous fields `D i` on a metric space `X` along a `1`-Lipschitz map `Ω → X`, and the top field
`D k` is `α`-Hölder, then the norm is at most the sum of the supremum norms of the `D i` and the
Hölder seminorm of `D k`. This bounds restrictions from a larger open set or from the whole
space. -/
private theorem norm_le_of_iteratedFDeriv_eq {X : Type*} [MetricSpace X] {ι : Ω → X}
    (hι : LipschitzWith 1 ι) (f : CkHolderSpaceOn k α Ω F)
    (D : ∀ i : Fin (k + 1), X →ᵇ (E [×i]→L[ℝ] F))
    (hD : ∀ i x, f.iteratedFDeriv i x = D i (ι x))
    (hH : MemHolder α (D (Fin.last k) : X → E [×k]→L[ℝ] F)) :
    ‖f‖ ≤ ∑ i, ‖D i‖ + nnHolderNorm α (D (Fin.last k) : X → E [×k]→L[ℝ] F) := by
  refine norm_le_sum_add_of_norm_iteratedFDeriv_le_of_holderWith (M := fun i ↦ ‖D i‖)
    (fun i ↦ norm_nonneg (D i)) (fun i x ↦ by rw [hD]; exact (D i).norm_coe_le_norm (ι x)) ?_
  convert hH.holderWith.comp_lipschitzWith_one hι using 1
  exact funext fun x ↦ hD _ x

section restrict

variable {Ω' : Opens E}

omit [NormedSpace ℝ E] in
private theorem extendZero_of_le {G : Type*} [Zero G] (h : Ω' ≤ Ω) (g : Ω → G) (x : Ω') :
    extendZero g (x : E) = g ⟨x, h x.property⟩ :=
  extendZero_coe g ⟨x, h x.property⟩

/-- At points of a smaller open set, the iterated derivatives of the extension by zero are the
derivative fields. -/
private theorem iteratedFDeriv_extendZero_of_le (h : Ω' ≤ Ω) (f : CkHolderSpaceOn k α Ω F)
    (i : Fin (k + 1)) (x : Ω') :
    _root_.iteratedFDeriv ℝ i (extendZero f) x = f.iteratedFDeriv i ⟨x, h x.property⟩ :=
  f.iteratedFDeriv_eq (fun y ↦ extendZero_coe f y) i ⟨x, h x.property⟩

/-- Restriction of an element of `C^{k,α}(Ω)` to a smaller open set `Ω' ≤ Ω`, as a continuous
linear map. -/
def restrictL (h : Ω' ≤ Ω) : CkHolderSpaceOn k α Ω F →L[ℝ] CkHolderSpaceOn k α Ω' F :=
  LinearMap.mkContinuous
    { toFun f := ofContDiffOn (extendZero f) ((f.contDiffOn fun x ↦ extendZero_coe f x).mono h)
        (fun i hi ↦ ⟨‖f.iteratedFDeriv ⟨i, Nat.lt_succ_of_le hi⟩‖, fun x ↦ by
          rw [iteratedFDeriv_extendZero_of_le h f ⟨i, Nat.lt_succ_of_le hi⟩]
          exact (f.iteratedFDeriv _).norm_coe_le_norm _⟩)
        (by
          have he : (fun x : Ω' ↦ _root_.iteratedFDeriv ℝ k (extendZero f) x) =
              (f.iteratedFDeriv (Fin.last k) : Ω → E [×k]→L[ℝ] F) ∘
                fun x : Ω' ↦ (⟨x, h x.property⟩ : Ω) :=
            funext fun x ↦ iteratedFDeriv_extendZero_of_le h f (Fin.last k) x
          rw [he]
          exact (f.memHolder_iteratedFDeriv.holderWith.comp_lipschitzWith_one
            ((LipschitzWith.subtypeVal (Ω' : Set E)).subtype_mk fun x ↦ h x.property)).memHolder)
      map_add' f g := by ext x; simp [extendZero_of_le h]
      map_smul' c f := by ext x; simp [extendZero_of_le h] }
    1 fun f ↦ by
      rw [one_mul, LinearMap.coe_mk, AddHom.coe_mk]
      exact (norm_le_of_iteratedFDeriv_eq (ι := fun x : Ω' ↦ (⟨x, h x.property⟩ : Ω))
        ((LipschitzWith.subtypeVal (Ω' : Set E)).subtype_mk fun x ↦ h x.property) _ f.iteratedFDeriv
        (fun i x ↦ by rw [iteratedFDeriv_ofContDiffOn, iteratedFDeriv_extendZero_of_le h])
        f.memHolder_iteratedFDeriv).trans (norm_eq f).ge

/-- The restriction of an element to a smaller open set has the same values there. -/
@[simp]
theorem restrictL_apply (h : Ω' ≤ Ω) (f : CkHolderSpaceOn k α Ω F) (x : Ω') :
    restrictL h f x = f ⟨x, h x.property⟩ := by
  simp [restrictL, extendZero_of_le h]

/-- The derivative fields of the restriction are the restrictions of the derivative fields. -/
@[simp]
theorem iteratedFDeriv_restrictL (h : Ω' ≤ Ω) (f : CkHolderSpaceOn k α Ω F) (i : Fin (k + 1))
    (x : Ω') : (restrictL h f).iteratedFDeriv i x = f.iteratedFDeriv i ⟨x, h x.property⟩ := by
  rw [← (restrictL h f).iteratedFDeriv_eq (g := extendZero f) (fun y ↦ by
      rw [restrictL_apply, extendZero_of_le h])]
  exact iteratedFDeriv_extendZero_of_le h f i x

/-- Restriction to a smaller open set does not increase the `C^{k,α}` norm. -/
theorem norm_restrictL_le_one (h : Ω' ≤ Ω) :
    ‖restrictL (k := k) (α := α) (F := F) h‖ ≤ 1 :=
  LinearMap.mkContinuous_norm_le _ zero_le_one _

end restrict

section inclusionSucc

/-- The inclusion `C^{k+1,α}(Ω) → C^{k,α}(Ω)`, as a continuous linear map of operator norm at most
`1 + C`, given a constant `C` such that the `k`-th iterated derivative of the extension by zero of
every `f ∈ C^{k+1,α}(Ω)` is `α`-Hölder on `Ω` with constant `C ‖f‖`. Such a bound depends on the
geometry of `Ω`: `TauCeti.CkHolderSpaceOn.inclusionSuccL` supplies it on convex open sets. -/
def inclusionSuccLOfHolderOnWith (C : ℝ≥0)
    (hC : ∀ f : CkHolderSpaceOn (k + 1) α Ω F,
      HolderOnWith (C * ‖f‖₊) α (_root_.iteratedFDeriv ℝ k f.extend) Ω) :
    CkHolderSpaceOn (k + 1) α Ω F →L[ℝ] CkHolderSpaceOn k α Ω F :=
  LinearMap.mkContinuous
    { toFun f := ofContDiffOn f.extend (f.contDiffOn_extend.of_le (by norm_cast; omega))
        (fun i hi ↦ ⟨‖f.iteratedFDeriv ⟨i, by omega⟩‖, fun x ↦
          f.norm_iteratedFDeriv_apply_le_norm_iteratedFDeriv f.extend_apply ⟨i, by omega⟩ x⟩)
        (HolderWith.memHolder fun x y ↦ hC f x x.property y y.property)
      map_add' f g := by ext x; simp
      map_smul' c f := by ext x; simp }
    (1 + C) fun f ↦ by
      rw [LinearMap.coe_mk, AddHom.coe_mk]
      refine (norm_le_sum_add_of_norm_iteratedFDeriv_le_of_holderWith
        (M := fun i ↦ ‖f.iteratedFDeriv i.castSucc‖) (fun i ↦ norm_nonneg _) (fun i x ↦ ?_)
        (K := C * ‖f‖₊) (fun x y ↦ ?_)).trans ?_
      · rw [iteratedFDeriv_ofContDiffOn]
        exact f.norm_iteratedFDeriv_apply_le_norm_iteratedFDeriv f.extend_apply i.castSucc x
      · rw [iteratedFDeriv_ofContDiffOn, iteratedFDeriv_ofContDiffOn]
        exact hC f x x.property y y.property
      · have hsum := f.sum_norm_iteratedFDeriv_le
        rw [Fin.sum_univ_castSucc] at hsum
        push_cast
        nlinarith [norm_nonneg (f.iteratedFDeriv (Fin.last (k + 1)))]

/-- The inclusion built from a Hölder bound does not change values. -/
@[simp]
theorem inclusionSuccLOfHolderOnWith_apply (C : ℝ≥0)
    (hC : ∀ f : CkHolderSpaceOn (k + 1) α Ω F,
      HolderOnWith (C * ‖f‖₊) α (_root_.iteratedFDeriv ℝ k f.extend) Ω)
    (f : CkHolderSpaceOn (k + 1) α Ω F) (x : Ω) : inclusionSuccLOfHolderOnWith C hC f x = f x := by
  simp [inclusionSuccLOfHolderOnWith]

/-- The inclusion built from a Hölder bound keeps the derivative fields through order `k`. -/
@[simp]
theorem iteratedFDeriv_inclusionSuccLOfHolderOnWith (C : ℝ≥0)
    (hC : ∀ f : CkHolderSpaceOn (k + 1) α Ω F,
      HolderOnWith (C * ‖f‖₊) α (_root_.iteratedFDeriv ℝ k f.extend) Ω)
    (f : CkHolderSpaceOn (k + 1) α Ω F) (i : Fin (k + 1)) (x : Ω) :
    (inclusionSuccLOfHolderOnWith C hC f).iteratedFDeriv i x = f.iteratedFDeriv i.castSucc x := by
  rw [inclusionSuccLOfHolderOnWith, LinearMap.mkContinuous_apply, LinearMap.coe_mk,
    AddHom.coe_mk, iteratedFDeriv_ofContDiffOn]
  exact f.iteratedFDeriv_extend i.castSucc x

/-- The inclusion built from a Hölder bound with constant `C ‖f‖` has operator norm at most
`1 + C`. -/
theorem norm_inclusionSuccLOfHolderOnWith_le (C : ℝ≥0)
    (hC : ∀ f : CkHolderSpaceOn (k + 1) α Ω F,
      HolderOnWith (C * ‖f‖₊) α (_root_.iteratedFDeriv ℝ k f.extend) Ω) :
    ‖inclusionSuccLOfHolderOnWith C hC‖ ≤ 1 + C :=
  LinearMap.mkContinuous_norm_le _ (by positivity) _

/-- On a convex open set and for `α ≤ 1`, the `k`-th derivative field of `f ∈ C^{k+1,α}(Ω)` is
`α`-Hölder on `Ω` with constant `2 ‖f‖`, the bound behind `TauCeti.CkHolderSpaceOn.inclusionSuccL`.
-/
private theorem holderOnWith_iteratedFDeriv_extend_succ (hconv : Convex ℝ (Ω : Set E))
    (hα : α ≤ 1) (f : CkHolderSpaceOn (k + 1) α Ω F) :
    HolderOnWith (2 * ‖f‖₊) α (_root_.iteratedFDeriv ℝ k f.extend) Ω := by
  refine (f.holderOnWith_iteratedFDeriv_of_lt f.extend_apply hconv hα k.lt_succ_self).mono_const ?_
  have h2 : ‖f.iteratedFDeriv ⟨k + 1, by omega⟩‖ + ‖f.iteratedFDeriv ⟨k, by omega⟩‖ ≤ ‖f‖ :=
    (Finset.add_le_sum (fun _ _ ↦ norm_nonneg _) (Finset.mem_univ _) (Finset.mem_univ _)
      (by simp)).trans f.sum_norm_iteratedFDeriv_le
  have hk := norm_iteratedFDeriv_le f ⟨k, by omega⟩
  rw [← NNReal.coe_le_coe]
  push_cast
  linarith

/-- On a convex open set `Ω` and for `α ≤ 1`, the inclusion `C^{k+1,α}(Ω) → C^{k,α}(Ω)`, as a
continuous linear map. Some geometric condition on `Ω` is needed, and this map assumes convexity:
for `0 < α ≤ 1`, on a slit annulus in the plane the angle function is in `C^{1,α}`, since its
gradient is the restriction of a smooth field on the full annulus, but it is not in `C^{0,α}`,
since it jumps across the slit, so the inclusion fails there. -/
def inclusionSuccL (hconv : Convex ℝ (Ω : Set E)) (hα : α ≤ 1) :
    CkHolderSpaceOn (k + 1) α Ω F →L[ℝ] CkHolderSpaceOn k α Ω F :=
  inclusionSuccLOfHolderOnWith 2 (holderOnWith_iteratedFDeriv_extend_succ hconv hα)

/-- The inclusion `C^{k+1,α}(Ω) → C^{k,α}(Ω)` does not change values. -/
@[simp]
theorem inclusionSuccL_apply (hconv : Convex ℝ (Ω : Set E)) (hα : α ≤ 1)
    (f : CkHolderSpaceOn (k + 1) α Ω F) (x : Ω) : inclusionSuccL hconv hα f x = f x :=
  inclusionSuccLOfHolderOnWith_apply _ _ f x

/-- The inclusion `C^{k+1,α}(Ω) → C^{k,α}(Ω)` keeps the derivative fields through order `k`. -/
@[simp]
theorem iteratedFDeriv_inclusionSuccL (hconv : Convex ℝ (Ω : Set E)) (hα : α ≤ 1)
    (f : CkHolderSpaceOn (k + 1) α Ω F) (i : Fin (k + 1)) (x : Ω) :
    (inclusionSuccL hconv hα f).iteratedFDeriv i x = f.iteratedFDeriv i.castSucc x :=
  iteratedFDeriv_inclusionSuccLOfHolderOnWith _ _ f i x

/-- The inclusion `C^{k+1,α}(Ω) → C^{k,α}(Ω)` has operator norm at most `3`. -/
theorem norm_inclusionSuccL_le (hconv : Convex ℝ (Ω : Set E)) (hα : α ≤ 1) :
    ‖inclusionSuccL (k := k) (F := F) hconv hα‖ ≤ 3 :=
  (norm_inclusionSuccLOfHolderOnWith_le _ _).trans_eq (by norm_num)

end inclusionSucc

section isCompact

/-- **`C^{k+1}` functions near a compact set are `C^{k,α}`.** For `α ≤ 1`, a function that is
`C^{k+1}` on an open set `U` containing a compact set `K` defines an element of `C^{k,α}(Ω)` for
every open `Ω ⊆ K`: its derivatives through order `k` are bounded on `K`, and its `k`-th
derivative is `α`-Hölder on `K`. -/
theorem exists_apply_eq_of_contDiffOn_of_isCompact {g : E → F} {U K : Set E} (hU : IsOpen U)
    (hg : ContDiffOn ℝ (k + 1) g U) (hK : IsCompact K) (hKU : K ⊆ U) (hΩK : (Ω : Set E) ⊆ K)
    (hα : α ≤ 1) : ∃ f : CkHolderSpaceOn k α Ω F, ∀ x : Ω, f x = g x := by
  have hbdd : ∀ i ≤ k, ∃ C, ∀ x : Ω, ‖_root_.iteratedFDeriv ℝ i g x‖ ≤ C := fun i hi ↦ by
    obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn
      ((ContinuousOn.continuousOn_iteratedFDeriv hg hU (by exact_mod_cast hi.trans k.le_succ)).mono
        hKU)
    exact ⟨C, fun x ↦ hC x (hΩK x.property)⟩
  -- Near each point of `K` the `k`-th derivative is `C¹`, hence `α`-Hölder on a ball.
  obtain ⟨δ, hδ, L, -, hL, -⟩ := hK.exists_holderOnWith_thickening_and_norm_le fun x hx ↦
    (((hg.contDiffAt (hU.mem_nhds (hKU hx))).iteratedFDeriv_right (m := 1) (i := k)
      (by rw [add_comm])).isBigO_sub_dist_rpow one_ne_zero hα).exists_holderOnWith_ball
  have hholder : MemHolder α fun x : Ω ↦ _root_.iteratedFDeriv ℝ k g x :=
    ⟨L, (hL.mono (hΩK.trans (Metric.self_subset_thickening hδ K))).holderWith⟩
  exact ⟨ofContDiffOn g ((hg.mono (hΩK.trans hKU)).of_le (by exact_mod_cast k.le_succ)) hbdd
    hholder, ofContDiffOn_apply g _ hbdd hholder⟩

end isCompact

/-- **A criterion for `C^{1,α}(Ω)`.** Let `α > 0`. On a bounded open set `Ω`, a function that is
differentiable and bounded on `Ω`, with derivative equal on `Ω` to a map `g'` which is `α`-Hölder
on `Ω`, defines an element of `C^{1,α}(Ω)`. -/
theorem exists_apply_eq_of_differentiableOn_of_holderOnWith (hα : 0 < α) {g : E → F}
    {g' : E → E →L[ℝ] F} {K : ℝ≥0} (hΩ : Bornology.IsBounded (Ω : Set E))
    (hg : DifferentiableOn ℝ g Ω) (hgb : ∃ C, ∀ x ∈ Ω, ‖g x‖ ≤ C) (hg' : HolderOnWith K α g' Ω)
    (hfd : ∀ x ∈ Ω, fderiv ℝ g x = g' x) : ∃ f : CkHolderSpaceOn 1 α Ω F, ∀ x : Ω, f x = g x := by
  have hc : ContDiffOn ℝ 1 g Ω := by
    rw [← zero_add 1, contDiffOn_succ_iff_fderiv_of_isOpen Ω.isOpen]
    refine ⟨hg, by simp, ?_⟩
    rw [contDiffOn_zero]
    exact (hg'.continuousOn hα).congr hfd
  obtain ⟨C', hC'⟩ := (hg'.isBounded_image hΩ).exists_norm_le
  have hbdd : ∀ i ≤ 1, ∃ C, ∀ x : Ω, ‖_root_.iteratedFDeriv ℝ i g x‖ ≤ C := by
    intro i hi
    obtain ⟨C, hC⟩ := hgb
    rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hi with rfl | rfl
    · exact ⟨C, fun x ↦ by simpa using hC x x.property⟩
    · exact ⟨C', fun x ↦ by
        rw [norm_iteratedFDeriv_one (𝕜 := ℝ), hfd x x.property]
        exact hC' _ ⟨x, x.property, rfl⟩⟩
  -- The first iterated derivative is the derivative, uncurried by a linear isometry.
  have hholder : MemHolder α fun x : Ω ↦ _root_.iteratedFDeriv ℝ 1 g x := by
    refine ⟨K, HolderOnWith.holderWith ?_⟩
    refine ((continuousMultilinearCurryFin1 ℝ E F).symm.isometry.comp_holderOnWith hg').congr
      fun x hx ↦ ?_
    exact (LinearIsometryEquiv.symm_apply_eq _).2
      ((continuousMultilinearCurryFin1_iteratedFDeriv_one g x).trans (hfd x hx)).symm
  exact ⟨ofContDiffOn g hc hbdd hholder, ofContDiffOn_apply g hc hbdd hholder⟩

end CkHolderSpaceOn

namespace CkHolderSpace

variable {k α F}

open CkHolderSpaceOn in
/-- Restriction of a bounded `C^{k,α}` map on the whole space to an open set `Ω`, as a continuous
linear map to `C^{k,α}(Ω)`. -/
def restrictOnL : CkHolderSpace k α E F →L[ℝ] CkHolderSpaceOn k α Ω F :=
  LinearMap.mkContinuous
    { toFun f := ofContDiffOn f f.contDiff.contDiffOn
        (fun i hi ↦ ⟨‖f‖, fun x ↦ f.norm_iteratedFDeriv_apply_le hi x⟩)
        (f.memHolder_iteratedFDeriv.holderWith.comp_lipschitzWith_one
          (LipschitzWith.subtypeVal (Ω : Set E))).memHolder
      map_add' f g := by ext x; simp
      map_smul' c f := by ext x; simp }
    1 fun f ↦ by
      rw [one_mul, LinearMap.coe_mk, AddHom.coe_mk]
      refine (norm_le_of_iteratedFDeriv_eq (LipschitzWith.subtypeVal (Ω : Set E)) _
        f.iteratedFDeriv
        (fun i x ↦ by rw [iteratedFDeriv_ofContDiffOn, CkHolderSpace.iteratedFDeriv_eq])
        (by rw [CkHolderSpace.coe_iteratedFDeriv]; exact f.memHolder_iteratedFDeriv)).trans_eq ?_
      rw [CkHolderSpace.norm_eq f, CkHolderSpace.coe_iteratedFDeriv, Fin.val_last]

/-- The restriction to `Ω` of a bounded `C^{k,α}` map has the same values on `Ω`. -/
@[simp]
theorem restrictOnL_apply (f : CkHolderSpace k α E F) (x : Ω) : restrictOnL Ω f x = f x := by
  simp [restrictOnL]

/-- The derivative fields of the restriction to `Ω` are the iterated derivatives on `Ω`. -/
@[simp]
theorem iteratedFDeriv_restrictOnL (f : CkHolderSpace k α E F) (i : Fin (k + 1)) (x : Ω) :
    (restrictOnL Ω f).iteratedFDeriv i x = _root_.iteratedFDeriv ℝ i f x := by
  simp [restrictOnL]

/-- Restriction to an open set does not increase the `C^{k,α}` norm. -/
theorem norm_restrictOnL_le_one : ‖restrictOnL (k := k) (α := α) (F := F) Ω‖ ≤ 1 :=
  LinearMap.mkContinuous_norm_le _ zero_le_one _

end CkHolderSpace

open scoped Topology in
open Metric Filter in
/-- A function of class `C^{n,α}` on a neighbourhood has a bounded-open Hölder reading on a
positive ball, agreeing pointwise with the original function. -/
theorem _root_.ContDiffOn.exists_ckHolderSpaceOn_ball
    {P : Type uP} {V : Type uV} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup V] [NormedSpace ℝ V] {φ : P → V} {s : Set P} {a : P}
    {n : ℕ} {α C : ℝ≥0} (hf : ContDiffOn ℝ n φ s) (hs : s ∈ 𝓝 a)
    (hα : α ≤ 1) (hH : HolderOnWith C α (_root_.iteratedFDeriv ℝ n φ) s) :
    ∃ r > 0, ball a r ⊆ s ∧
      ∃ g : CkHolderSpaceOn n α ⟨ball a r, isOpen_ball⟩ V, ∀ x, g x = φ x := by
  obtain ⟨ρ, hρ, hρs, M, _, hb, _⟩ :=
    hf.exists_ball_bounds_and_holderOnWith_iteratedFDeriv hs hα hH
  let Ω : Opens P := ⟨ball a ρ, isOpen_ball⟩
  have hbound : ∀ j ≤ n, ∃ A, ∀ x : Ω, ‖_root_.iteratedFDeriv ℝ j φ x‖ ≤ A :=
    fun j hj ↦ ⟨(M : ℝ), fun x ↦ hb j hj x x.property⟩
  have hholder : MemHolder α (fun x : Ω ↦ _root_.iteratedFDeriv ℝ n φ x) :=
    ⟨C, fun x y ↦ hH x (hρs x.property) y (hρs y.property)⟩
  exact ⟨ρ, hρ, hρs, CkHolderSpaceOn.ofContDiffOn φ (hf.mono hρs) hbound hholder,
    fun x ↦ CkHolderSpaceOn.ofContDiffOn_apply φ (hf.mono hρs) hbound hholder x⟩

end TauCeti

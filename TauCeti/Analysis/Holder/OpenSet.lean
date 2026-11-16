/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Holder.Iterated
public import Mathlib.Topology.Sets.Opens
import Mathlib.Analysis.Calculus.ContDiff.Comp
import TauCeti.Analysis.Calculus.UniformLimitsDeriv
import TauCeti.Analysis.Holder.JetBounds

/-!
# The Hölder spaces `C^{k,α}(Ω)` on an open set

For an open set `Ω` of a real normed space `E`, this file constructs the normed space
`C^{k,α}(Ω, F)` of maps that are `C^k` on `Ω`, whose iterated Fréchet derivatives through order
`k` are bounded on `Ω`, and whose `k`-th iterated derivative is `α`-Hölder on all of `Ω`. Its norm
is

`‖f‖ = ∑_{i ≤ k} sup_{x ∈ Ω} ‖D^i f(x)‖ + [D^k f]_{α,Ω}`,

where the suprema use the operator norm of continuous multilinear maps and `[·]_{α,Ω}` is the
`α`-Hölder seminorm over pairs of points of `Ω`. The space is Banach when the codomain is Banach.
These are the global Hölder spaces of a domain in elliptic regularity theory. Restriction maps the
bounded spaces `TauCeti.CkHolderSpace` of the whole space into them.

The Hölder seminorm is taken over all pairs of points of `Ω`, not locally. On
`Ω = (-1, 0) ∪ (0, 1)` the sign function has vanishing derivatives, but its difference quotient
between `-t` and `t` is `2 / (2t)^α`, so it does not lie in `C^{0,α}(Ω)`.

An element is represented, as for `TauCeti.CkHolderSpace`, by its family of derivative fields on
`Ω`: bounded continuous fields `Ω →ᵇ (E [×i]→L[ℝ] F)` for `i < k` and a bounded Hölder field of
order `k`, each field below order `k` having the next one, curried on the left, as its Fréchet
derivative at every point of `Ω`. The underlying function `E → F` is the order-zero field on `Ω`
and vanishes off `Ω`, so an element is determined by its values on `Ω` (`CkHolderSpaceOn.ext`).

## Main declarations

* `TauCeti.CkHolderSpaceOn k α Ω F`: the Hölder space `C^{k,α}(Ω, F)`.
* `TauCeti.CkHolderSpaceOn.iteratedFDeriv`: the bounded continuous `i`-th derivative field on
  `Ω` for `i ≤ k`; `TauCeti.CkHolderSpaceOn.iteratedFDeriv_eq` identifies it with Mathlib's
  `iteratedFDeriv` at points of `Ω`.
* `TauCeti.CkHolderSpaceOn.contDiffOn` and `TauCeti.CkHolderSpaceOn.holderOnWith_iteratedFDeriv`:
  the regularity of an element; `TauCeti.CkHolderSpaceOn.ofContDiffOn` is the converse
  constructor.
* `TauCeti.CkHolderSpaceOn.norm_eq`: the norm is the sum of the supremum norms over `Ω` of the
  derivatives through order `k` and the `α`-Hölder seminorm of the `k`-th derivative over `Ω`.
* `TauCeti.CkHolderSpaceOn.norm_le_of_norm_iteratedFDeriv_le_of_holderOnWith` and
  `TauCeti.CkHolderSpaceOn.norm_ofContDiffOn_le`: the norm is controlled by bounds on the
  derivatives over `Ω` and a Hölder constant of the `k`-th derivative over `Ω`.
* `TauCeti.CkHolderSpaceOn.instCompleteSpace`: completeness when the codomain is complete.
* `TauCeti.CkHolderSpaceOn.restrictL`: restriction to a smaller open set, of operator norm at most
  one, and `TauCeti.CkHolderSpace.restrictL`: restriction of a bounded `C^{k,α}` map of the whole
  space to an open set, of operator norm at most one.
* `TauCeti.CkHolderSpaceOn.inclusionL`: on a bounded open set, the inclusion
  `C^{k,α}(Ω) → C^{k,β}(Ω)` for `β ≤ α`, of operator norm at most `max 1 (diam Ω ^ (α - β))`.
* `TauCeti.CkHolderSpaceOn.lowerOrderL`: on a convex open set and for `α ≤ 1`, the inclusion
  `C^{k+1,α}(Ω) → C^{k,α}(Ω)`, of operator norm at most `3`. Convexity, or some other control of
  distances within `Ω` by distances in `E`, is needed: see the docstring of `lowerOrderL`.

## References

D. Gilbarg and N. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
Section 4.1.
-/

public section

noncomputable section

namespace TauCeti

open Set
open scoped NNReal BoundedContinuousFunction

universe u v

variable (k : ℕ) (α : ℝ≥0) {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
  (Ω : TopologicalSpace.Opens E) (F : Type v) [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Shortcut instance for bounded continuous fields of `n`-multilinear maps on `Ω`. Without it,
instance search for the module structure of `ℓ¹` products of these fields indexed by the order `n`
exceeds the default synthesis depth. It is local so that the instance path for these fields is
unchanged outside this file. -/
local instance CkHolderSpaceOn.instNormedAddCommGroupBoundedContinuousFunction (n : ℕ) :
    NormedAddCommGroup (Ω →ᵇ (E [×n]→L[ℝ] F)) :=
  inferInstance

/-- Shortcut instance for bounded continuous fields of `n`-multilinear maps on `Ω`, needed for
continuous linear maps into these fields indexed by the order `n`. It is local for the same
reason. -/
local instance CkHolderSpaceOn.instNormedSpaceBoundedContinuousFunction (n : ℕ) :
    NormedSpace ℝ (Ω →ᵇ (E [×n]→L[ℝ] F)) :=
  inferInstance

/-- The Hölder space `C^{k,α}(Ω, F)` of an open set `Ω`: maps that are `C^k` on `Ω`, with
iterated Fréchet derivatives through order `k` bounded on `Ω` and `k`-th iterated derivative
`α`-Hölder on `Ω`. Its norm is

`∑_{i ≤ k} sup_{x ∈ Ω} ‖D^i f(x)‖ + [D^k f]_{α,Ω}`.
-/
-- The module system requires exposure while the declarations below construct and project through
-- this graph alias. The final `irreducible` attribute restores the abstraction boundary.
@[expose] def CkHolderSpaceOn : Type _ :=
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
        HasFDerivAt (Function.extend ((↑) : Ω → E) (field j.castSucc J) 0)
          (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (j + 1) ↦ E) F
            (field j.succ J x)) x}
      zero_mem' := fun j x ↦ by
        simp only [map_zero, FunLike.coe_zero, Function.extend_zero]
        exact hasFDerivAt_const (x := (x : E)) (c := (0 : E [×j]→L[ℝ] F))
      add_mem' := fun {J K} hJ hK j x ↦ by
        simp only [Set.mem_ofPred_eq, map_add, FunLike.coe_add,
          _root_.add_apply] at hJ hK ⊢
        rw [← add_zero (0 : E → E [×j]→L[ℝ] F), Function.extend_add]
        exact (hJ j x).add (hK j x)
      smul_mem' := fun c {J} hJ j x ↦ by
        simp only [Set.mem_ofPred_eq, map_smul, FunLike.coe_smul,
          _root_.smul_apply] at hJ ⊢
        rw [← smul_zero c, Function.extend_smul]
        exact (hJ j x).const_smul c }
  graph

namespace CkHolderSpaceOn

variable {k α Ω F}

variable (k α Ω F) in
/-- The ambient jet space of `C^{k,α}(Ω)`: bounded continuous derivative fields on `Ω` of orders
below `k`, with the `ℓ¹` norm, together with a bounded Hölder field of order `k`. -/
private abbrev Jet := WithLp 1
  ((PiLp 1 fun i : Fin k ↦ Ω →ᵇ (E [×i]→L[ℝ] F)) × HolderSpace α Ω (E [×k]→L[ℝ] F))

/-- The derivative field of order `i ≤ k` of a jet; this is the map `field` in the definition of
`CkHolderSpaceOn`. -/
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

variable (E F) in
/-- Left currying of `(j + 1)`-multilinear maps, as a continuous linear map. -/
private def curryLeftL (j : ℕ) : (E [×j + 1]→L[ℝ] F) →L[ℝ] E →L[ℝ] (E [×j]→L[ℝ] F) :=
  (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (j + 1) ↦ E) F).toContinuousLinearEquiv

private theorem curryLeftL_apply (j : ℕ) (g : E [×j + 1]→L[ℝ] F) :
    curryLeftL E F j g = g.curryLeft := by
  ext x v
  simp [curryLeftL]

/-- The derivative identities of a jet: at every point of `Ω`, each field below order `k`,
extended by zero off `Ω`, has the next field, curried on the left, as its Fréchet derivative. -/
private def IsJetGraph (J : Jet k α Ω F) : Prop :=
  ∀ (j : Fin k) (x : Ω), HasFDerivAt (Function.extend ((↑) : Ω → E) (fieldL j.castSucc J) 0)
    (curryLeftL E F j (fieldL j.succ J x)) x

/-- Elements are the jets satisfying the derivative identities. This is the identity map: the
carrier of `CkHolderSpaceOn` states the identities through its local `field`, which is `fieldL`,
and through `continuousMultilinearCurryLeftEquiv`, whose underlying continuous linear map is
`curryLeftL`. -/
private def equivSubtype : CkHolderSpaceOn k α Ω F ≃ {J : Jet k α Ω F // IsJetGraph J} :=
  Equiv.refl _

/-- The underlying jet of an element. -/
private def toJet (f : CkHolderSpaceOn k α Ω F) : Jet k α Ω F := (equivSubtype f).1

/-- An element from a jet satisfying the derivative identities. -/
private def mk (J : Jet k α Ω F) (hJ : IsJetGraph J) : CkHolderSpaceOn k α Ω F :=
  equivSubtype.symm ⟨J, hJ⟩

private theorem toJet_injective :
    Function.Injective (toJet (k := k) (α := α) (Ω := Ω) (F := F)) :=
  fun _ _ h ↦ equivSubtype.injective (Subtype.ext h)

private theorem toJet_mk (J : Jet k α Ω F) (hJ) : toJet (mk J hJ) = J := by
  rw [toJet, mk, Equiv.apply_symm_apply]

private theorem hasFDerivAt_fieldL (f : CkHolderSpaceOn k α Ω F) (j : Fin k) (x : Ω) :
    HasFDerivAt (Function.extend ((↑) : Ω → E) (fieldL j.castSucc (toJet f)) 0)
      (curryLeftL E F j (fieldL j.succ (toJet f) x)) x :=
  (equivSubtype f).2 j x

/-- The `C^{k,α}(Ω)` norm makes `C^{k,α}(Ω, F)` a normed additive group. -/
instance instNormedAddCommGroup : NormedAddCommGroup (CkHolderSpaceOn k α Ω F) := by
  unfold CkHolderSpaceOn
  infer_instance

/-- `C^{k,α}(Ω, F)` is a real normed space. -/
instance instNormedSpace : NormedSpace ℝ (CkHolderSpaceOn k α Ω F) := by
  unfold CkHolderSpaceOn
  infer_instance

private theorem norm_toJet (f : CkHolderSpaceOn k α Ω F) : ‖toJet f‖ = ‖f‖ :=
  Submodule.norm_coe f

/-- The underlying jet, as a continuous linear map: the inclusion of the submodule
`CkHolderSpaceOn` into the jet space. -/
private def toJetL : CkHolderSpaceOn k α Ω F →L[ℝ] Jet k α Ω F := by
  unfold CkHolderSpaceOn
  exact Submodule.subtypeL _

/-- The inclusion `toJetL` is `toJet`; both are the coercion of the submodule. -/
private theorem toJetL_apply (f : CkHolderSpaceOn k α Ω F) : toJetL f = toJet f :=
  rfl

/-- The bounded continuous `i`-th derivative field on `Ω` of an element of `C^{k,α}(Ω)`, for
`i ≤ k`. It agrees with Mathlib's `iteratedFDeriv` at points of `Ω` by
`CkHolderSpaceOn.iteratedFDeriv_eq`. -/
def iteratedFDeriv (f : CkHolderSpaceOn k α Ω F) (i : Fin (k + 1)) : Ω →ᵇ (E [×i]→L[ℝ] F) :=
  fieldL i (toJet f)

/-- The `k`-th derivative field on `Ω` of an element of `C^{k,α}(Ω)`, as an element of the
bounded Hölder space of `Ω`. -/
def iteratedFDerivHolder (f : CkHolderSpaceOn k α Ω F) : HolderSpace α Ω (E [×k]→L[ℝ] F) :=
  (toJet f).ofLp.2

/-- The underlying function of an element of `C^{k,α}(Ω)`: its order-zero derivative field,
evaluated on the empty tuple, on `Ω`, and zero off `Ω`. Use the coercion `⇑f` instead. -/
def toFun (f : CkHolderSpaceOn k α Ω F) (x : E) : F :=
  (Function.extend ((↑) : Ω → E) (f.iteratedFDeriv ⟨0, k.succ_pos⟩) 0 x).curry0

/-- The formal Taylor series recorded by an element, truncated after order `k` and extended by
zero off `Ω`. -/
private def series (f : CkHolderSpaceOn k α Ω F) (x : E) : FormalMultilinearSeries ℝ E F :=
  fun m ↦ if h : m < k + 1 then Function.extend ((↑) : Ω → E) (f.iteratedFDeriv ⟨m, h⟩) 0 x
    else 0

private theorem series_of_lt (f : CkHolderSpaceOn k α Ω F) (x : E) {m : ℕ} (h : m < k + 1) :
    series f x m = Function.extend ((↑) : Ω → E) (f.iteratedFDeriv ⟨m, h⟩) 0 x := by
  simp [series, h]

/-- The recorded derivative fields form a Taylor series up to order `k` on `Ω` for the underlying
function. -/
private theorem hasFTaylorSeriesUpToOn (f : CkHolderSpaceOn k α Ω F) :
    HasFTaylorSeriesUpToOn k f.toFun (series f) Ω where
  zero_eq x _ := by
    rw [series_of_lt f x k.succ_pos, toFun]
  fderivWithin m hm x hx := by
    have hmk : m < k := by exact_mod_cast hm
    have hfun : (fun y ↦ series f y m) =
        Function.extend ((↑) : Ω → E) (fieldL (⟨m, hmk⟩ : Fin k).castSucc (toJet f)) 0 :=
      funext fun y ↦ series_of_lt f y (by omega)
    lift x to Ω using hx
    rw [hfun, series_of_lt f x (by omega), Subtype.val_injective.extend_apply,
      ← curryLeftL_apply]
    exact (hasFDerivAt_fieldL f ⟨m, hmk⟩ x).hasFDerivWithinAt
  cont m hm := by
    have hmk : m < k + 1 := by
      have : m ≤ k := by exact_mod_cast hm
      omega
    rw [continuousOn_iff_continuous_domRestrict]
    have hfun : (Ω : Set E).domRestrict (fun y ↦ series f y m) = f.iteratedFDeriv ⟨m, hmk⟩ :=
      funext fun y ↦ by
        rw [domRestrict_apply, series_of_lt f y hmk, Subtype.val_injective.extend_apply]
    rw [hfun]
    exact (f.iteratedFDeriv ⟨m, hmk⟩).continuous

private theorem iteratedFDerivWithin_toFun (f : CkHolderSpaceOn k α Ω F) (i : Fin (k + 1))
    (x : Ω) : iteratedFDerivWithin ℝ i f.toFun Ω x = f.iteratedFDeriv i x := by
  rw [← (hasFTaylorSeriesUpToOn f).eq_iteratedFDerivWithin_of_uniqueDiffOn
    (by exact_mod_cast i.is_le) Ω.isOpen.uniqueDiffOn x.2, series_of_lt f x i.2,
    Subtype.val_injective.extend_apply]

private theorem toFun_of_notMem (f : CkHolderSpaceOn k α Ω F) {x : E} (hx : x ∉ Ω) :
    f.toFun x = 0 := by
  rw [toFun, Function.extend_apply' _ _ _ (fun ⟨y, hy⟩ ↦ hx (hy ▸ y.2))]
  simp

/-- An element of `C^{k,α}(Ω)` is determined by its underlying function. -/
theorem toFun_injective :
    Function.Injective (toFun (k := k) (α := α) (Ω := Ω) (F := F)) := by
  intro f g hfg
  have hfield : ∀ i, f.iteratedFDeriv i = g.iteratedFDeriv i := fun i ↦ by
    ext1 x
    rw [← iteratedFDerivWithin_toFun, ← iteratedFDerivWithin_toFun, hfg]
  apply toJet_injective
  apply WithLp.ofLp_injective 1
  apply Prod.ext
  · apply WithLp.ofLp_injective 1
    funext j
    have := hfield j.castSucc
    rwa [iteratedFDeriv, iteratedFDeriv, fieldL_castSucc, fieldL_castSucc] at this
  · apply HolderSpace.ext
    intro x
    have := DFunLike.congr_fun (hfield (Fin.last k)) x
    rwa [iteratedFDeriv, iteratedFDeriv, fieldL_last, fieldL_last,
      HolderSpace.toBoundedContinuousFunction_apply,
      HolderSpace.toBoundedContinuousFunction_apply] at this

/-- An element of `C^{k,α}(Ω)` is coerced to its underlying function, which vanishes off `Ω`. -/
instance instFunLike : FunLike (CkHolderSpaceOn k α Ω F) E F where
  coe := toFun
  coe_injective := toFun_injective

/-- `CkHolderSpaceOn.toFun f` is equal to the coercion `⇑f` of `f` to a function. -/
@[simp]
theorem toFun_eq_coe (f : CkHolderSpaceOn k α Ω F) : f.toFun = ⇑f :=
  (rfl)

/-- The underlying function of an element of `C^{k,α}(Ω)` vanishes off `Ω`. -/
theorem apply_of_notMem (f : CkHolderSpaceOn k α Ω F) {x : E} (hx : x ∉ Ω) : f x = 0 :=
  toFun_of_notMem f hx

/-- Two elements of `C^{k,α}(Ω)` are equal when their underlying functions agree on `Ω`. -/
@[ext]
theorem ext {f g : CkHolderSpaceOn k α Ω F} (h : ∀ x ∈ Ω, f x = g x) : f = g :=
  DFunLike.ext f g fun x ↦ by
    by_cases hx : x ∈ Ω
    · exact h x hx
    · rw [apply_of_notMem f hx, apply_of_notMem g hx]

/-- At points of `Ω`, the iterated Fréchet derivatives within `Ω` of the underlying function are
the recorded derivative fields. -/
theorem iteratedFDerivWithin_eq (f : CkHolderSpaceOn k α Ω F) (i : Fin (k + 1)) (x : Ω) :
    iteratedFDerivWithin ℝ i f Ω x = f.iteratedFDeriv i x :=
  iteratedFDerivWithin_toFun f i x

/-- At points of `Ω`, the iterated Fréchet derivatives of the underlying function are the recorded
derivative fields. -/
theorem iteratedFDeriv_eq (f : CkHolderSpaceOn k α Ω F) (i : Fin (k + 1)) (x : Ω) :
    _root_.iteratedFDeriv ℝ i f x = f.iteratedFDeriv i x := by
  rw [← iteratedFDerivWithin_of_isOpen _ Ω.isOpen x.2, iteratedFDerivWithin_eq]

/-- The `i`-th derivative field is Mathlib's `iteratedFDeriv` of the underlying function,
restricted to `Ω`. -/
@[simp]
theorem coe_iteratedFDeriv (f : CkHolderSpaceOn k α Ω F) (i : Fin (k + 1)) :
    ⇑(f.iteratedFDeriv i) = (Ω : Set E).domRestrict (_root_.iteratedFDeriv ℝ i f) :=
  funext fun x ↦ (iteratedFDeriv_eq f i x).symm

/-- The underlying function of an element of `C^{k,α}(Ω)` is `C^k` on `Ω`. -/
theorem contDiffOn (f : CkHolderSpaceOn k α Ω F) : ContDiffOn ℝ k f Ω :=
  (hasFTaylorSeriesUpToOn f).contDiffOn

/-- The Hölder field, as a bounded continuous field, is the derivative field of order `k`. -/
@[simp]
theorem toBoundedContinuousFunction_iteratedFDerivHolder (f : CkHolderSpaceOn k α Ω F) :
    f.iteratedFDerivHolder.toBoundedContinuousFunction = f.iteratedFDeriv (Fin.last k) := by
  rw [iteratedFDeriv, fieldL_last, iteratedFDerivHolder]

/-- The Hölder field records the `k`-th iterated Fréchet derivative on `Ω`. -/
theorem iteratedFDerivHolder_apply (f : CkHolderSpaceOn k α Ω F) (x : Ω) :
    f.iteratedFDerivHolder x = _root_.iteratedFDeriv ℝ k f x := by
  rw [← HolderSpace.toBoundedContinuousFunction_apply,
    toBoundedContinuousFunction_iteratedFDerivHolder]
  exact (iteratedFDeriv_eq f (Fin.last k) x).symm

/-- The Hölder field is Mathlib's `k`-th `iteratedFDeriv` of the underlying function, restricted
to `Ω`. -/
@[simp]
theorem coe_iteratedFDerivHolder (f : CkHolderSpaceOn k α Ω F) :
    (f.iteratedFDerivHolder : Ω → E [×k]→L[ℝ] F) =
      (Ω : Set E).domRestrict (_root_.iteratedFDeriv ℝ k f) :=
  funext (iteratedFDerivHolder_apply f)

/-- The `k`-th iterated Fréchet derivative of an element of `C^{k,α}(Ω)` is `α`-Hölder on `Ω`,
with constant its Hölder seminorm over `Ω`. -/
theorem holderOnWith_iteratedFDeriv (f : CkHolderSpaceOn k α Ω F) :
    HolderOnWith (nnHolderNorm α ((Ω : Set E).domRestrict (_root_.iteratedFDeriv ℝ k f))) α
      (_root_.iteratedFDeriv ℝ k f) Ω := by
  have h := f.iteratedFDerivHolder.memHolder.holderWith
  rw [HolderSpace.coe_toBoundedContinuousFunction, coe_iteratedFDerivHolder] at h
  exact HolderWith.restrict_iff.mp h

/-- The `C^{k,α}(Ω)` norm is the sum of the supremum norms over `Ω` of the iterated derivatives
through order `k` and the `α`-Hölder seminorm over `Ω` of the `k`-th iterated derivative. -/
theorem norm_eq (f : CkHolderSpaceOn k α Ω F) :
    ‖f‖ = ∑ i : Fin (k + 1), ‖f.iteratedFDeriv i‖ +
      nnHolderNorm α ((Ω : Set E).domRestrict (_root_.iteratedFDeriv ℝ k f)) := by
  rw [← norm_toJet, WithLp.prod_norm_eq_of_L1, PiLp.norm_eq_of_L1, Fin.sum_univ_castSucc,
    HolderSpace.norm_def, ← coe_iteratedFDerivHolder,
    ← HolderSpace.coe_toBoundedContinuousFunction, add_assoc]
  simp only [iteratedFDeriv, fieldL_castSucc, fieldL_last, iteratedFDerivHolder,
    WithLp.ofLp_fst, WithLp.ofLp_snd]

/-- The supremum norm of each derivative field is controlled by the `C^{k,α}(Ω)` norm. -/
theorem norm_iteratedFDeriv_le (f : CkHolderSpaceOn k α Ω F) (i : Fin (k + 1)) :
    ‖f.iteratedFDeriv i‖ ≤ ‖f‖ := by
  rw [norm_eq]
  exact (Finset.single_le_sum (fun j _ ↦ norm_nonneg (f.iteratedFDeriv j))
    (Finset.mem_univ i)).trans (le_add_of_nonneg_right (NNReal.coe_nonneg _))

/-- At points of `Ω`, each iterated derivative through order `k` is controlled by the
`C^{k,α}(Ω)` norm. -/
theorem norm_iteratedFDeriv_apply_le (f : CkHolderSpaceOn k α Ω F) {i : ℕ} (hi : i ≤ k)
    {x : E} (hx : x ∈ Ω) : ‖_root_.iteratedFDeriv ℝ i f x‖ ≤ ‖f‖ := by
  rw [iteratedFDeriv_eq f ⟨i, Nat.lt_succ_of_le hi⟩ ⟨x, hx⟩]
  exact ((f.iteratedFDeriv _).norm_coe_le_norm _).trans (norm_iteratedFDeriv_le f _)

/-- The values of an element of `C^{k,α}(Ω)` are controlled by its norm. -/
theorem norm_apply_le (f : CkHolderSpaceOn k α Ω F) (x : E) : ‖f x‖ ≤ ‖f‖ := by
  by_cases hx : x ∈ Ω
  · simpa using norm_iteratedFDeriv_apply_le f (Nat.zero_le k) hx
  · rw [apply_of_notMem f hx, norm_zero]
    exact norm_nonneg f

/-- The `α`-Hölder seminorm over `Ω` of the `k`-th iterated derivative is controlled by the
`C^{k,α}(Ω)` norm. -/
theorem nnHolderNorm_iteratedFDeriv_le (f : CkHolderSpaceOn k α Ω F) :
    (nnHolderNorm α ((Ω : Set E).domRestrict (_root_.iteratedFDeriv ℝ k f)) : ℝ) ≤ ‖f‖ := by
  rw [norm_eq]
  exact le_add_of_nonneg_left (Finset.sum_nonneg fun j _ ↦ norm_nonneg _)

/-- The `C^{k,α}(Ω)` norm is at most `∑_{i ≤ k} M i + K` when the `i`-th derivative is bounded by
`M i` on `Ω` for every `i ≤ k` and the `k`-th derivative is `α`-Hölder on `Ω` with constant
`K`. -/
theorem norm_le_of_norm_iteratedFDeriv_le_of_holderOnWith {f : CkHolderSpaceOn k α Ω F}
    {M : Fin (k + 1) → ℝ≥0} {K : ℝ≥0}
    (hM : ∀ i : Fin (k + 1), ∀ x ∈ Ω, ‖_root_.iteratedFDeriv ℝ i f x‖ ≤ M i)
    (hK : HolderOnWith K α (_root_.iteratedFDeriv ℝ k f) Ω) : ‖f‖ ≤ ∑ i, (M i : ℝ) + K := by
  rw [norm_eq]
  gcongr with i
  · refine (BoundedContinuousFunction.norm_le (M i).coe_nonneg).2 fun x ↦ ?_
    rw [← iteratedFDeriv_eq]
    exact hM i x x.2
  · exact_mod_cast (HolderWith.restrict_iff.mpr hK).nnholderNorm_le

/-- The `i`-th derivative field, as a continuous linear map to bounded continuous fields on
`Ω`. -/
def iteratedFDerivL (i : Fin (k + 1)) :
    CkHolderSpaceOn k α Ω F →L[ℝ] (Ω →ᵇ (E [×i]→L[ℝ] F)) :=
  (fieldL i).comp toJetL

/-- The linear map `iteratedFDerivL i` sends an element to its `i`-th derivative field. -/
@[simp]
theorem iteratedFDerivL_apply (i : Fin (k + 1)) (f : CkHolderSpaceOn k α Ω F) :
    iteratedFDerivL i f = f.iteratedFDeriv i := by
  rw [iteratedFDerivL, ContinuousLinearMap.comp_apply, toJetL_apply, iteratedFDeriv]

/-- Each derivative field of the zero map is zero. -/
@[simp]
theorem iteratedFDeriv_zero (i : Fin (k + 1)) :
    (0 : CkHolderSpaceOn k α Ω F).iteratedFDeriv i = 0 := by
  simpa only [iteratedFDerivL_apply] using
    (iteratedFDerivL (α := α) (Ω := Ω) (F := F) i).map_zero

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

/-- At points of `Ω`, the underlying function is the order-zero derivative field evaluated on the
empty tuple. -/
private theorem apply_eq_curry0 (f : CkHolderSpaceOn k α Ω F) (x : Ω) :
    f x = (f.iteratedFDeriv ⟨0, k.succ_pos⟩ x).curry0 := by
  rw [← toFun_eq_coe, toFun, Subtype.val_injective.extend_apply]

/-- The underlying function of the zero map is zero. -/
@[simp]
theorem coe_zero : ⇑(0 : CkHolderSpaceOn k α Ω F) = 0 := by
  funext x
  by_cases hx : x ∈ Ω
  · lift x to Ω using hx
    simp only [apply_eq_curry0, iteratedFDeriv_zero, FunLike.coe_zero, Pi.zero_apply]
    simp
  · exact apply_of_notMem _ hx

/-- The underlying function of a sum is the sum of the underlying functions. -/
@[simp]
theorem coe_add (f g : CkHolderSpaceOn k α Ω F) : ⇑(f + g) = f + g := by
  funext x
  by_cases hx : x ∈ Ω
  · lift x to Ω using hx
    simp only [apply_eq_curry0, iteratedFDeriv_add, Pi.add_apply, _root_.add_apply]
    simp
  · simp [apply_of_notMem _ hx]

/-- The underlying function of a scalar multiple is the scalar multiple of the underlying
function. -/
@[simp]
theorem coe_smul (c : ℝ) (f : CkHolderSpaceOn k α Ω F) : ⇑(c • f) = c • ⇑f := by
  funext x
  by_cases hx : x ∈ Ω
  · lift x to Ω using hx
    simp only [apply_eq_curry0, iteratedFDeriv_smul, Pi.smul_apply, _root_.smul_apply]
    simp
  · simp [apply_of_notMem _ hx]

/-- The bounded continuous field on `Ω` given by a map that is continuous and bounded on `Ω`. -/
private def bcfOn {G : Type*} [NormedAddCommGroup G] (g : E → G) (hg : ContinuousOn g Ω)
    (hbdd : ∃ C, ∀ x ∈ Ω, ‖g x‖ ≤ C) : Ω →ᵇ G :=
  BoundedContinuousFunction.ofNormedAddCommGroup ((Ω : Set E).domRestrict g)
    (continuousOn_iff_continuous_domRestrict.mp hg) hbdd.choose fun x ↦ hbdd.choose_spec x x.2

omit [NormedSpace ℝ E] in
private theorem bcfOn_apply {G : Type*} [NormedAddCommGroup G] (g : E → G)
    (hg : ContinuousOn g Ω) (hbdd : ∃ C, ∀ x ∈ Ω, ‖g x‖ ≤ C) (x : Ω) :
    bcfOn g hg hbdd x = g x :=
  rfl

/-- The jet of iterated derivatives on `Ω` of a map that is `C^k` on `Ω`, with derivatives through
order `k` bounded on `Ω` and `k`-th iterated derivative `α`-Hölder on `Ω`. -/
private def jetOf (f : E → F) (hf : ContDiffOn ℝ k f Ω)
    (hbdd : ∀ i ≤ k, ∃ C, ∀ x ∈ Ω, ‖_root_.iteratedFDeriv ℝ i f x‖ ≤ C)
    (hholder : ∃ K, HolderOnWith K α (_root_.iteratedFDeriv ℝ k f) Ω) : Jet k α Ω F :=
  WithLp.toLp 1
    (WithLp.toLp 1 fun j : Fin k ↦ bcfOn (_root_.iteratedFDeriv ℝ j f)
        (ContinuousOn.continuousOn_iteratedFDeriv hf Ω.isOpen (by exact_mod_cast j.2.le))
        (hbdd j j.2.le),
      HolderSpace.ofBoundedContinuousFunction
        (bcfOn (_root_.iteratedFDeriv ℝ k f)
          (ContinuousOn.continuousOn_iteratedFDeriv hf Ω.isOpen le_rfl) (hbdd k le_rfl))
        (hholder.elim fun K hK ↦ ⟨K, HolderWith.restrict_iff.mpr hK⟩))

private theorem fieldL_jetOf (f : E → F) (hf : ContDiffOn ℝ k f Ω)
    (hbdd : ∀ i ≤ k, ∃ C, ∀ x ∈ Ω, ‖_root_.iteratedFDeriv ℝ i f x‖ ≤ C)
    (hholder : ∃ K, HolderOnWith K α (_root_.iteratedFDeriv ℝ k f) Ω) (i : Fin (k + 1))
    (x : Ω) : fieldL i (jetOf f hf hbdd hholder) x = _root_.iteratedFDeriv ℝ i f x := by
  induction i using Fin.lastCases with
  | last =>
    rw [fieldL_last]
    simp [jetOf, bcfOn_apply]
  | cast j =>
    rw [fieldL_castSucc]
    simp [jetOf, bcfOn_apply]

private theorem isJetGraph_jetOf (f : E → F) (hf : ContDiffOn ℝ k f Ω)
    (hbdd : ∀ i ≤ k, ∃ C, ∀ x ∈ Ω, ‖_root_.iteratedFDeriv ℝ i f x‖ ≤ C)
    (hholder : ∃ K, HolderOnWith K α (_root_.iteratedFDeriv ℝ k f) Ω) :
    IsJetGraph (jetOf f hf hbdd hholder) := fun j x ↦ by
  have heq : Function.extend ((↑) : Ω → E) (fieldL j.castSucc (jetOf f hf hbdd hholder)) 0
      =ᶠ[nhds (x : E)] _root_.iteratedFDeriv ℝ j f :=
    Filter.eventuallyEq_of_mem (Ω.isOpen.mem_nhds x.2) fun y hy ↦ by
      lift y to Ω using hy
      rw [Subtype.val_injective.extend_apply, fieldL_jetOf]
      rfl
  have h := ((hf.contDiffAt (Ω.isOpen.mem_nhds x.2)).differentiableAt_iteratedFDeriv
    (m := j) (by exact_mod_cast j.2)).hasFDerivAt
  rw [fderiv_iteratedFDeriv, Function.comp_apply] at h
  rw [fieldL_jetOf]
  exact h.congr_of_eventuallyEq heq

/-- Build an element of `C^{k,α}(Ω)` from a map that is `C^k` on `Ω`, whose iterated derivatives
through order `k` are bounded on `Ω` and whose `k`-th iterated derivative is `α`-Hölder on `Ω`.
Its underlying function is `f` on `Ω` and zero off `Ω`. -/
def ofContDiffOn (f : E → F) (hf : ContDiffOn ℝ k f Ω)
    (hbdd : ∀ i ≤ k, ∃ C, ∀ x ∈ Ω, ‖_root_.iteratedFDeriv ℝ i f x‖ ≤ C)
    (hholder : ∃ K, HolderOnWith K α (_root_.iteratedFDeriv ℝ k f) Ω) :
    CkHolderSpaceOn k α Ω F :=
  mk (jetOf f hf hbdd hholder) (isJetGraph_jetOf f hf hbdd hholder)

/-- The underlying function of `ofContDiffOn f` is `f` on `Ω` and zero off `Ω`. -/
@[simp]
theorem coe_ofContDiffOn (f : E → F) (hf : ContDiffOn ℝ k f Ω)
    (hbdd : ∀ i ≤ k, ∃ C, ∀ x ∈ Ω, ‖_root_.iteratedFDeriv ℝ i f x‖ ≤ C)
    (hholder : ∃ K, HolderOnWith K α (_root_.iteratedFDeriv ℝ k f) Ω) :
    ⇑(ofContDiffOn f hf hbdd hholder) = (Ω : Set E).indicator f := by
  funext x
  by_cases hx : x ∈ Ω
  · lift x to Ω using hx
    rw [apply_eq_curry0, iteratedFDeriv, ofContDiffOn, toJet_mk, fieldL_jetOf,
      indicator_of_mem x.2]
    simp [iteratedFDeriv_zero_apply]
  · rw [apply_of_notMem _ hx, indicator_of_notMem hx]

/-- At points of `Ω`, the iterated derivatives of `ofContDiffOn f` are those of `f`. -/
theorem iteratedFDeriv_ofContDiffOn_apply (f : E → F) (hf : ContDiffOn ℝ k f Ω)
    (hbdd : ∀ i ≤ k, ∃ C, ∀ x ∈ Ω, ‖_root_.iteratedFDeriv ℝ i f x‖ ≤ C)
    (hholder : ∃ K, HolderOnWith K α (_root_.iteratedFDeriv ℝ k f) Ω) (i : ℕ) {x : E}
    (hx : x ∈ Ω) :
    _root_.iteratedFDeriv ℝ i (ofContDiffOn f hf hbdd hholder) x =
      _root_.iteratedFDeriv ℝ i f x := by
  rw [coe_ofContDiffOn]
  exact ((EqOn.eventuallyEq_of_mem (fun y hy ↦ indicator_of_mem hy f)
    (Ω.isOpen.mem_nhds hx)).iteratedFDeriv ℝ i).eq_of_nhds

/-- The `C^{k,α}(Ω)` norm of `ofContDiffOn f` is at most `∑_{i ≤ k} M i + K` when the `i`-th
derivative of `f` is bounded by `M i` on `Ω` for every `i ≤ k` and the `k`-th derivative of `f` is
`α`-Hölder on `Ω` with constant `K`. -/
theorem norm_ofContDiffOn_le (f : E → F) (hf : ContDiffOn ℝ k f Ω)
    (hbdd : ∀ i ≤ k, ∃ C, ∀ x ∈ Ω, ‖_root_.iteratedFDeriv ℝ i f x‖ ≤ C)
    (hholder : ∃ K, HolderOnWith K α (_root_.iteratedFDeriv ℝ k f) Ω)
    {M : Fin (k + 1) → ℝ≥0} {K : ℝ≥0}
    (hM : ∀ i : Fin (k + 1), ∀ x ∈ Ω, ‖_root_.iteratedFDeriv ℝ i f x‖ ≤ M i)
    (hK : HolderOnWith K α (_root_.iteratedFDeriv ℝ k f) Ω) :
    ‖ofContDiffOn f hf hbdd hholder‖ ≤ ∑ i, (M i : ℝ) + K := by
  have hD : ∀ (i : ℕ) {x : E}, x ∈ Ω → _root_.iteratedFDeriv ℝ i
      (ofContDiffOn f hf hbdd hholder) x = _root_.iteratedFDeriv ℝ i f x :=
    fun i _ hx ↦ iteratedFDeriv_ofContDiffOn_apply f hf hbdd hholder i hx
  refine norm_le_of_norm_iteratedFDeriv_le_of_holderOnWith (fun i x hx ↦ ?_) ?_
  · rw [hD i hx]
    exact hM i x hx
  · intro x hx y hy
    rw [hD k hx, hD k hy]
    exact hK x hx y hy

section Restrict

variable {Ω' : TopologicalSpace.Opens E}

/-- The restriction of an element of `C^{k,α}(Ω)` to a smaller open set `Ω'`. -/
private def restrict (h : Ω' ≤ Ω) (f : CkHolderSpaceOn k α Ω F) : CkHolderSpaceOn k α Ω' F :=
  ofContDiffOn f (f.contDiffOn.mono h)
    (fun _ hi ↦ ⟨‖f‖, fun _ hx ↦ f.norm_iteratedFDeriv_apply_le hi (h hx)⟩)
    ⟨_, f.holderOnWith_iteratedFDeriv.mono h⟩

private theorem norm_restrict_le (h : Ω' ≤ Ω) (f : CkHolderSpaceOn k α Ω F) :
    ‖restrict h f‖ ≤ ‖f‖ := by
  calc ‖restrict h f‖
      ≤ ∑ i, ((‖f.iteratedFDeriv i‖₊ : ℝ≥0) : ℝ) +
          nnHolderNorm α ((Ω : Set E).domRestrict (_root_.iteratedFDeriv ℝ k f)) := by
        refine norm_ofContDiffOn_le _ _ _ _ (fun i x hx ↦ ?_) (f.holderOnWith_iteratedFDeriv.mono h)
        rw [iteratedFDeriv_eq f i ⟨x, h hx⟩, coe_nnNorm]
        exact (f.iteratedFDeriv i).norm_coe_le_norm _
    _ = ‖f‖ := by simp [norm_eq f]

/-- Restriction from `C^{k,α}(Ω)` to `C^{k,α}(Ω')` for open `Ω' ⊆ Ω`, as a continuous linear map
of operator norm at most one. -/
def restrictL (h : Ω' ≤ Ω) : CkHolderSpaceOn k α Ω F →L[ℝ] CkHolderSpaceOn k α Ω' F :=
  LinearMap.mkContinuous
    { toFun := restrict h
      map_add' f g := ext fun x hx ↦ by simp [restrict, indicator_of_mem hx]
      map_smul' c f := ext fun x hx ↦ by simp [restrict, indicator_of_mem hx] } 1
    fun f ↦ by
      rw [one_mul]
      exact norm_restrict_le h f

/-- The restriction of `f` to `Ω'` is `f` on `Ω'` and zero off `Ω'`. -/
@[simp]
theorem coe_restrictL (h : Ω' ≤ Ω) (f : CkHolderSpaceOn k α Ω F) :
    ⇑(restrictL h f) = (Ω' : Set E).indicator f :=
  coe_ofContDiffOn ..

/-- Restriction to a smaller open set has operator norm at most one. -/
theorem norm_restrictL_le_one (h : Ω' ≤ Ω) :
    ‖restrictL (k := k) (α := α) (F := F) h‖ ≤ 1 :=
  LinearMap.mkContinuous_norm_le _ zero_le_one _

end Restrict

section Inclusion

variable {β : ℝ≥0}

omit [NormedSpace ℝ E] in
/-- Points of a bounded set are at extended distance at most its diameter. -/
private theorem edist_le_diam (hΩ : Bornology.IsBounded (Ω : Set E)) {x y : E} (hx : x ∈ Ω)
    (hy : y ∈ Ω) : edist x y ≤ (Metric.diam (Ω : Set E)).toNNReal := by
  rw [edist_dist]
  exact ENNReal.ofReal_le_ofReal (Metric.dist_le_diam_of_mem hΩ hx hy)

/-- An element of `C^{k,α}(Ω)` on a bounded open set `Ω` lies in `C^{k,β}(Ω)` for `β ≤ α`. -/
private def inclusion (hβα : β ≤ α) (hΩ : Bornology.IsBounded (Ω : Set E))
    (f : CkHolderSpaceOn k α Ω F) : CkHolderSpaceOn k β Ω F :=
  ofContDiffOn f f.contDiffOn
    (fun _ hi ↦ ⟨‖f‖, fun _ hx ↦ f.norm_iteratedFDeriv_apply_le hi hx⟩)
    ⟨_, f.holderOnWith_iteratedFDeriv.of_le (fun _ hx _ hy ↦ edist_le_diam hΩ hx hy) hβα⟩

private theorem norm_inclusion_le (hβα : β ≤ α) (hΩ : Bornology.IsBounded (Ω : Set E))
    (f : CkHolderSpaceOn k α Ω F) :
    ‖inclusion hβα hΩ f‖ ≤ max 1 (Metric.diam (Ω : Set E) ^ ((α : ℝ) - β)) * ‖f‖ := by
  have hD : ((Metric.diam (Ω : Set E)).toNNReal ^ ((α : ℝ) - β) : ℝ≥0) ≤
      max 1 (Metric.diam (Ω : Set E) ^ ((α : ℝ) - β)) := by
    rw [NNReal.coe_rpow, Real.coe_toNNReal _ Metric.diam_nonneg]
    exact le_max_right _ _
  have hS : ∑ i, ‖f.iteratedFDeriv i‖ ≤
      max 1 (Metric.diam (Ω : Set E) ^ ((α : ℝ) - β)) * ∑ i, ‖f.iteratedFDeriv i‖ :=
    le_mul_of_one_le_left (Finset.sum_nonneg fun _ _ ↦ norm_nonneg _) (le_max_left _ _)
  have hH := mul_le_mul_of_nonneg_left hD
    (nnHolderNorm α ((Ω : Set E).domRestrict (_root_.iteratedFDeriv ℝ k f))).coe_nonneg
  calc ‖inclusion hβα hΩ f‖
      ≤ ∑ i, ((‖f.iteratedFDeriv i‖₊ : ℝ≥0) : ℝ) +
          ((nnHolderNorm α ((Ω : Set E).domRestrict (_root_.iteratedFDeriv ℝ k f)) *
            (Metric.diam (Ω : Set E)).toNNReal ^ ((α : ℝ) - β) : ℝ≥0) : ℝ) := by
        refine norm_ofContDiffOn_le _ _ _ _ (fun i x hx ↦ ?_)
          (f.holderOnWith_iteratedFDeriv.of_le (fun _ hx _ hy ↦ edist_le_diam hΩ hx hy) hβα)
        rw [iteratedFDeriv_eq f i ⟨x, hx⟩, coe_nnNorm]
        exact (f.iteratedFDeriv i).norm_coe_le_norm _
    _ ≤ max 1 (Metric.diam (Ω : Set E) ^ ((α : ℝ) - β)) * ‖f‖ := by
        rw [norm_eq f]
        simp only [coe_nnNorm, NNReal.coe_mul] at hH ⊢
        nlinarith

/-- On a bounded open set `Ω`, the inclusion `C^{k,α}(Ω) → C^{k,β}(Ω)` for `β ≤ α`, of operator
norm at most `max 1 (D^(α - β))` with `D` the diameter of `Ω`. -/
def inclusionL (hβα : β ≤ α) (hΩ : Bornology.IsBounded (Ω : Set E)) :
    CkHolderSpaceOn k α Ω F →L[ℝ] CkHolderSpaceOn k β Ω F :=
  LinearMap.mkContinuous
    { toFun := inclusion hβα hΩ
      map_add' f g := ext fun x hx ↦ by simp [inclusion, indicator_of_mem hx]
      map_smul' c f := ext fun x hx ↦ by simp [inclusion, indicator_of_mem hx] }
    (max 1 (Metric.diam (Ω : Set E) ^ ((α : ℝ) - β))) (norm_inclusion_le hβα hΩ)

/-- The inclusion `C^{k,α}(Ω) → C^{k,β}(Ω)` does not change the underlying function. -/
@[simp]
theorem coe_inclusionL (hβα : β ≤ α) (hΩ : Bornology.IsBounded (Ω : Set E))
    (f : CkHolderSpaceOn k α Ω F) : ⇑(inclusionL hβα hΩ f) = f := by
  rw [inclusionL, LinearMap.mkContinuous_apply, LinearMap.coe_mk, AddHom.coe_mk, inclusion,
    coe_ofContDiffOn]
  exact indicator_eq_self.mpr fun x hx ↦ by_contra fun h ↦ hx (apply_of_notMem f h)

/-- The inclusion `C^{k,α}(Ω) → C^{k,β}(Ω)` has operator norm at most `max 1 (D^(α - β))`, with
`D` the diameter of `Ω`. -/
theorem norm_inclusionL_le (hβα : β ≤ α) (hΩ : Bornology.IsBounded (Ω : Set E)) :
    ‖inclusionL (k := k) (F := F) hβα hΩ‖ ≤
      max 1 (Metric.diam (Ω : Set E) ^ ((α : ℝ) - β)) :=
  LinearMap.mkContinuous_norm_le _ (zero_le_one.trans (le_max_left _ _)) _

end Inclusion

section LowerOrder

/-- On a convex open set `Ω`, an element of `C^{k+1,α}(Ω)` lies in `C^{k,α}(Ω)` for `α ≤ 1`. -/
private def lowerOrder (hα : α ≤ 1) (hΩ : Convex ℝ (Ω : Set E))
    (f : CkHolderSpaceOn (k + 1) α Ω F) : CkHolderSpaceOn k α Ω F :=
  ofContDiffOn f (f.contDiffOn.of_le (by norm_cast; omega))
    (fun _ hi ↦ ⟨‖f‖, fun _ hx ↦ f.norm_iteratedFDeriv_apply_le (by omega) hx⟩)
    ⟨_, f.contDiffOn.holderOnWith_iteratedFDeriv_of_lt Ω.isOpen hΩ (Nat.lt_succ_self k) hα
      (M := ‖f‖₊) (L := ‖f‖₊) (fun _ hx ↦ f.norm_iteratedFDeriv_apply_le (by omega) hx)
      (fun _ hx ↦ f.norm_iteratedFDeriv_apply_le le_rfl hx)⟩

private theorem norm_lowerOrder_le (hα : α ≤ 1) (hΩ : Convex ℝ (Ω : Set E))
    (f : CkHolderSpaceOn (k + 1) α Ω F) : ‖lowerOrder hα hΩ f‖ ≤ 3 * ‖f‖ := by
  have hle : ∀ (i : Fin (k + 2)) {x : E}, x ∈ Ω →
      ‖_root_.iteratedFDeriv ℝ i f x‖ ≤ ‖f.iteratedFDeriv i‖ := fun i x hx ↦ by
    rw [iteratedFDeriv_eq f i ⟨x, hx⟩]
    exact (f.iteratedFDeriv i).norm_coe_le_norm _
  set S := ∑ i : Fin (k + 1), ‖f.iteratedFDeriv i.castSucc‖
  have hk : ‖f.iteratedFDeriv (Fin.last k).castSucc‖ ≤ S :=
    Finset.single_le_sum (f := fun i : Fin (k + 1) ↦ ‖f.iteratedFDeriv i.castSucc‖)
      (fun _ _ ↦ norm_nonneg _) (Finset.mem_univ _)
  have hsum : S + ‖f.iteratedFDeriv (Fin.last (k + 1))‖ ≤ ‖f‖ := by
    rw [norm_eq f, Fin.sum_univ_castSucc]
    exact le_add_of_nonneg_right (NNReal.coe_nonneg _)
  calc ‖lowerOrder hα hΩ f‖
      ≤ ∑ i : Fin (k + 1), ((‖f.iteratedFDeriv i.castSucc‖₊ : ℝ≥0) : ℝ) +
          ((‖f.iteratedFDeriv (Fin.last (k + 1))‖₊ +
            2 * ‖f.iteratedFDeriv (Fin.last k).castSucc‖₊ : ℝ≥0) : ℝ) := by
        refine norm_ofContDiffOn_le _ _ _ _ (fun i x hx ↦ ?_)
          (f.contDiffOn.holderOnWith_iteratedFDeriv_of_lt Ω.isOpen hΩ (Nat.lt_succ_self k) hα
            (fun x hx ↦ ?_) (fun x hx ↦ ?_))
        · rw [coe_nnNorm]
          exact hle i.castSucc hx
        · simpa using hle (Fin.last k).castSucc hx
        · simpa using hle (Fin.last (k + 1)) hx
    _ ≤ 3 * ‖f‖ := by
        simp only [coe_nnNorm, NNReal.coe_add, NNReal.coe_mul, NNReal.coe_ofNat]
        nlinarith [norm_nonneg (f.iteratedFDeriv (Fin.last (k + 1)))]

/-- On a convex open set `Ω` and for `α ≤ 1`, the inclusion `C^{k+1,α}(Ω) → C^{k,α}(Ω)`, of
operator norm at most `3`. Some hypothesis of this kind is needed: on the plane annulus
`1 < ‖x‖ < 2` slit along the positive first axis, the angle function lies in `C^{1,α}`, since its
derivative extends smoothly across the slit, but it jumps by `2π` across the slit, so it is not in
`C^{0,α}`. -/
def lowerOrderL (hα : α ≤ 1) (hΩ : Convex ℝ (Ω : Set E)) :
    CkHolderSpaceOn (k + 1) α Ω F →L[ℝ] CkHolderSpaceOn k α Ω F :=
  LinearMap.mkContinuous
    { toFun := lowerOrder hα hΩ
      map_add' f g := ext fun x hx ↦ by simp [lowerOrder, indicator_of_mem hx]
      map_smul' c f := ext fun x hx ↦ by simp [lowerOrder, indicator_of_mem hx] }
    3 (norm_lowerOrder_le hα hΩ)

/-- The inclusion `C^{k+1,α}(Ω) → C^{k,α}(Ω)` does not change the underlying function. -/
@[simp]
theorem coe_lowerOrderL (hα : α ≤ 1) (hΩ : Convex ℝ (Ω : Set E))
    (f : CkHolderSpaceOn (k + 1) α Ω F) : ⇑(lowerOrderL hα hΩ f) = f := by
  rw [lowerOrderL, LinearMap.mkContinuous_apply, LinearMap.coe_mk, AddHom.coe_mk, lowerOrder,
    coe_ofContDiffOn]
  exact indicator_eq_self.mpr fun x hx ↦ by_contra fun h ↦ hx (apply_of_notMem f h)

/-- The inclusion `C^{k+1,α}(Ω) → C^{k,α}(Ω)` on a convex open set has operator norm at most
`3`. -/
theorem norm_lowerOrderL_le (hα : α ≤ 1) (hΩ : Convex ℝ (Ω : Set E)) :
    ‖lowerOrderL (k := k) (F := F) hα hΩ‖ ≤ 3 :=
  LinearMap.mkContinuous_norm_le _ (by norm_num) _

end LowerOrder

end CkHolderSpaceOn

namespace CkHolderSpace

variable {k α F}

/-- The restriction of a bounded `C^{k,α}` map of the whole space to an open set `Ω`. -/
private def restrict (f : CkHolderSpace k α E F) : CkHolderSpaceOn k α Ω F :=
  CkHolderSpaceOn.ofContDiffOn f f.contDiff.contDiffOn
    (fun _ hi ↦ ⟨‖f‖, fun x _ ↦ f.norm_iteratedFDeriv_apply_le hi x⟩)
    ⟨_, f.memHolder_iteratedFDeriv.holderWith.holderOnWith Ω⟩

private theorem norm_restrict_le (f : CkHolderSpace k α E F) : ‖restrict Ω f‖ ≤ ‖f‖ := by
  calc ‖restrict Ω f‖
      ≤ ∑ i, ((‖f.iteratedFDeriv i‖₊ : ℝ≥0) : ℝ) +
          nnHolderNorm α (_root_.iteratedFDeriv ℝ k f) := by
        refine CkHolderSpaceOn.norm_ofContDiffOn_le _ _ _ _ (fun i x _ ↦ ?_)
          (f.memHolder_iteratedFDeriv.holderWith.holderOnWith Ω)
        rw [iteratedFDeriv_eq f i x, coe_nnNorm]
        exact (f.iteratedFDeriv i).norm_coe_le_norm _
    _ = ‖f‖ := by simp [norm_eq f]

/-- Restriction of bounded `C^{k,α}` maps of the whole space to an open set `Ω`, as a continuous
linear map to `C^{k,α}(Ω)` of operator norm at most one. -/
def restrictL : CkHolderSpace k α E F →L[ℝ] CkHolderSpaceOn k α Ω F :=
  LinearMap.mkContinuous
    { toFun := restrict Ω
      map_add' f g := CkHolderSpaceOn.ext fun x hx ↦ by
        simp [restrict, indicator_of_mem hx]
      map_smul' c f := CkHolderSpaceOn.ext fun x hx ↦ by
        simp [restrict, indicator_of_mem hx] } 1
    fun f ↦ by
      rw [one_mul]
      exact norm_restrict_le Ω f

/-- The restriction of `f` to `Ω` is `f` on `Ω` and zero off `Ω`. -/
@[simp]
theorem coe_restrictL (f : CkHolderSpace k α E F) :
    ⇑(restrictL Ω f) = (Ω : Set E).indicator f :=
  CkHolderSpaceOn.coe_ofContDiffOn ..

/-- Restriction to an open set has operator norm at most one. -/
theorem norm_restrictL_le_one : ‖restrictL (k := k) (α := α) (F := F) Ω‖ ≤ 1 :=
  LinearMap.mkContinuous_norm_le _ zero_le_one _

end CkHolderSpace

end TauCeti

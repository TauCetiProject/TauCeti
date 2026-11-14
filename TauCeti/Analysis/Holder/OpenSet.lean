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
import TauCeti.Topology.MetricSpace.Bounded
import TauCeti.Analysis.Holder.JetBounds

/-!
# The Hölder spaces `C^{k,α}(Ω)` on an open set

For an open set `Ω` of a real normed space `E`, this file constructs the normed space
`C^{k,α}(Ω, F)` of maps on `Ω` which are `C^k` with bounded iterated Fréchet derivatives through
order `k` and whose `k`-th iterated derivative has finite `α`-Hölder seminorm over `Ω`, and proves
that it is a Banach space when the codomain is. Its norm is

`‖f‖ = ∑_{i ≤ k} sup_{x ∈ Ω} ‖D^i f x‖ + [D^k f]_{α, Ω}`,

where the suprema use the operator norm of continuous multilinear maps. The Hölder seminorm is
global over `Ω`: it compares values of `D^k f` at any two points of `Ω`, also across different
connected components. These are the spaces of the classical Schauder theory on domains. The
bounded `C^{k,α}` maps on the whole space, `TauCeti.CkHolderSpace`, restrict into the space on
every open set.

Elements are maps on the subtype `Ω`. An element is represented by its family of iterated
derivative fields: bounded continuous fields `Ω →ᵇ (E [×i]→L[ℝ] F)` for `i < k` and a bounded
Hölder field of order `k`, subject to the condition that each field, extended by zero outside `Ω`,
has the next field, curried on the left, as its Fréchet derivative at every point of `Ω`. As `Ω`
is open, this does not depend on the extension. The conditions are closed under uniform
convergence, which gives completeness. Derivatives of an element are read off any map `g : E → F`
which agrees with it on `Ω`.

## Main declarations

* `TauCeti.CkHolderOnSpace k α Ω F`: the space `C^{k,α}(Ω, F)`, with
  `TauCeti.CkHolderOnSpace.instCompleteSpace` for a complete codomain.
* `TauCeti.CkHolderOnSpace.iteratedFDeriv` and `TauCeti.CkHolderOnSpace.iteratedFDerivHolder`: the
  derivative fields; `TauCeti.CkHolderOnSpace.iteratedFDeriv_eq` identifies them with Mathlib's
  `iteratedFDeriv` of every map agreeing with the element on `Ω`.
* `TauCeti.CkHolderOnSpace.contDiffOn` and
  `TauCeti.CkHolderOnSpace.holderOnWith_iteratedFDeriv`: the regularity of an element;
  `TauCeti.CkHolderOnSpace.ofContDiffOn` is the converse constructor.
* `TauCeti.CkHolderOnSpace.norm_eq`: the norm is the sum of the suprema of the derivatives through
  order `k` and the `α`-Hölder seminorm of the `k`-th derivative over `Ω`;
  `TauCeti.CkHolderOnSpace.norm_le_of_norm_iteratedFDeriv_le_of_holderWith` and
  `TauCeti.CkHolderOnSpace.norm_ofContDiffOn_le` bound it.
* `TauCeti.CkHolderOnSpace.restrictL`: restriction to a smaller open set, of norm at most one;
  `TauCeti.CkHolderSpace.restrictOpensL` is restriction from the whole space.
* `TauCeti.CkHolderOnSpace.inclusionSuccL`: on a convex open set and for `α ≤ 1`, the inclusion
  `C^{k+1,α}(Ω) → C^{k,α}(Ω)`, of norm at most `3`, from the Hölder bound
  `TauCeti.CkHolderOnSpace.holderOnWith_iteratedFDeriv_of_convex`.
* `TauCeti.CkHolderOnSpace.inclusionL`: on a bounded open set and for `β ≤ α`, the inclusion
  `C^{k,α}(Ω) → C^{k,β}(Ω)`, of norm at most `max 1 (D^(α - β))` for `D` the diameter of `Ω`.

## References

D. Gilbarg and N. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
Section 4.1.
-/

public section

noncomputable section

namespace TauCeti

open Filter Topology TopologicalSpace
open scoped NNReal BoundedContinuousFunction

universe u v

variable (k : ℕ) (α : ℝ≥0) {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
  (Ω : Opens E) (F : Type v) [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Shortcut instance for bounded continuous fields of `n`-multilinear maps on an open set.
Without it, instance search for the module structure of `ℓ¹` products of these fields indexed by
the order `n` exceeds the default synthesis depth. It is local so that the instance path for these
fields is unchanged outside this file, and no public statement below mentions it: only definition
bodies and proofs use it. -/
local instance CkHolderOnSpace.instNormedAddCommGroupBoundedContinuousFunction (n : ℕ) :
    NormedAddCommGroup (Ω →ᵇ (E [×n]→L[ℝ] F)) :=
  inferInstance

/-- Shortcut instance for bounded continuous fields of `n`-multilinear maps on an open set, needed
for operator norms of continuous linear maps into these fields indexed by the order `n`. It is
local for the same reason. -/
local instance CkHolderOnSpace.instNormedSpaceBoundedContinuousFunction (n : ℕ) :
    NormedSpace ℝ (Ω →ᵇ (E [×n]→L[ℝ] F)) :=
  inferInstance

omit [NormedSpace ℝ E] in
variable {Ω} in
/-- The extension by zero of a map on an open set agrees near each point of the set with every
map agreeing with it on the set. -/
private theorem extend_eventuallyEq {G : Type*} [Zero G] {g : Ω → G} {h : E → G}
    (hgh : ∀ x : Ω, g x = h x) (x : Ω) :
    Function.extend Subtype.val g 0 =ᶠ[𝓝 (x : E)] h :=
  eventually_of_mem (Ω.isOpen.mem_nhds x.2) fun y hy ↦
    (Subtype.val_injective.extend_apply g 0 ⟨y, hy⟩).trans (hgh ⟨y, hy⟩)

/-- The space `C^{k,α}(Ω, F)` of maps on the open set `Ω` which are `C^k` with bounded iterated
Fréchet derivatives through order `k` and whose `k`-th iterated derivative has finite `α`-Hölder
seminorm over `Ω`. Its norm is

`∑_{i ≤ k} sup_{x ∈ Ω} ‖D^i f x‖ + [D^k f]_{α, Ω}`.
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
        simp only [map_zero]
        exact (hasFDerivAt_const (x := (x : E)) (c := (0 : E [×j]→L[ℝ] F))).congr_of_eventuallyEq
          (extend_eventuallyEq (h := fun _ ↦ 0) (fun _ ↦ by simp) x)
      add_mem' := fun {J K} hJ hK j x ↦ by
        simp only [Set.mem_ofPred_eq, map_add] at hJ hK ⊢
        exact ((hJ j x).add (hK j x)).congr_of_eventuallyEq (extend_eventuallyEq (fun y ↦ by
          simp) x)
      smul_mem' := fun c {J} hJ j x ↦ by
        simp only [Set.mem_ofPred_eq, map_smul] at hJ ⊢
        exact ((hJ j x).const_smul c).congr_of_eventuallyEq (extend_eventuallyEq (fun y ↦ by
          simp) x) }
  graph

namespace CkHolderOnSpace

variable {k α Ω F}

variable (k α Ω F) in
/-- The ambient jet space of `C^{k,α}(Ω)`: bounded continuous derivative fields on `Ω` of orders
below `k`, with the `ℓ¹` norm, together with a bounded Hölder field of order `k`. -/
private abbrev Jet := WithLp 1
  ((PiLp 1 fun i : Fin k ↦ Ω →ᵇ (E [×i]→L[ℝ] F)) × HolderSpace α Ω (E [×k]→L[ℝ] F))

/-- The derivative field of order `i ≤ k` of a jet; this is the map `field` in the definition of
`CkHolderOnSpace`. -/
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

/-- The derivative identities of a jet: each field below order `k`, extended by zero outside `Ω`,
has the next field, curried on the left, as its Fréchet derivative at every point of `Ω`. -/
private def IsJetGraph (J : Jet k α Ω F) : Prop :=
  ∀ (j : Fin k) (x : Ω),
    HasFDerivAt (Function.extend Subtype.val (fieldL j.castSucc J : Ω → E [×j]→L[ℝ] F) 0)
      (fieldL j.succ J x).curryLeft x

/-- Elements are the jets satisfying the derivative identities. This is the identity map: the
carrier of `CkHolderOnSpace` states the identities through its local `field`, which is `fieldL`, and
through `continuousMultilinearCurryLeftEquiv`, whose underlying map is
`ContinuousMultilinearMap.curryLeft`. Besides this map, the carrier is unfolded only by `toJetL`,
the two norm instances, `norm_toJet` and `instCompleteSpace`, which use that it is a submodule of
the jet space. -/
private def equivSubtype : CkHolderOnSpace k α Ω F ≃ {J : Jet k α Ω F // IsJetGraph J} :=
  Equiv.refl _

/-- The underlying jet of an element. -/
private def toJet (f : CkHolderOnSpace k α Ω F) : Jet k α Ω F := (equivSubtype f).1

/-- An element from a jet satisfying the derivative identities. -/
private def mk (J : Jet k α Ω F) (hJ : IsJetGraph J) : CkHolderOnSpace k α Ω F :=
  equivSubtype.symm ⟨J, hJ⟩

private theorem toJet_injective :
    Function.Injective (toJet (k := k) (α := α) (Ω := Ω) (F := F)) :=
  fun _ _ h ↦ equivSubtype.injective (Subtype.ext h)

private theorem toJet_mk (J : Jet k α Ω F) (hJ) : toJet (mk J hJ) = J := by
  rw [toJet, mk, Equiv.apply_symm_apply]

private theorem hasFDerivAt_fieldL (f : CkHolderOnSpace k α Ω F) (j : Fin k) (x : Ω) :
    HasFDerivAt (Function.extend Subtype.val (fieldL j.castSucc (toJet f) : Ω → E [×j]→L[ℝ] F) 0)
      (fieldL j.succ (toJet f) x).curryLeft x :=
  (equivSubtype f).2 j x

instance instNormedAddCommGroup : NormedAddCommGroup (CkHolderOnSpace k α Ω F) := by
  unfold CkHolderOnSpace
  infer_instance

instance instNormedSpace : NormedSpace ℝ (CkHolderOnSpace k α Ω F) := by
  unfold CkHolderOnSpace
  infer_instance

private theorem norm_toJet (f : CkHolderOnSpace k α Ω F) : ‖toJet f‖ = ‖f‖ :=
  Submodule.norm_coe f

/-- The underlying jet, as a continuous linear map: the inclusion of the submodule
`CkHolderOnSpace` into the jet space. -/
private def toJetL : CkHolderOnSpace k α Ω F →L[ℝ] Jet k α Ω F := by
  unfold CkHolderOnSpace
  exact Submodule.subtypeL _

/-- The inclusion `toJetL` is `toJet`; both are the coercion of the submodule. -/
private theorem toJetL_apply (f : CkHolderOnSpace k α Ω F) : toJetL f = toJet f :=
  rfl

/-- The bounded continuous `i`-th derivative field on `Ω` of an element of `C^{k,α}(Ω)`, for
`i ≤ k`. It agrees with Mathlib's `iteratedFDeriv` by `CkHolderOnSpace.iteratedFDeriv_eq`. -/
def iteratedFDeriv (f : CkHolderOnSpace k α Ω F) (i : Fin (k + 1)) : Ω →ᵇ (E [×i]→L[ℝ] F) :=
  fieldL i (toJet f)

/-- The `k`-th derivative field on `Ω` of an element of `C^{k,α}(Ω)`, as an element of the bounded
Hölder space on `Ω`. -/
def iteratedFDerivHolder (f : CkHolderOnSpace k α Ω F) : HolderSpace α Ω (E [×k]→L[ℝ] F) :=
  (toJet f).ofLp.2

/-- The underlying map on `Ω` of an element of `C^{k,α}(Ω)`: its order-zero derivative field,
evaluated on the empty tuple. Use the coercion `⇑f` instead. -/
def toFun (f : CkHolderOnSpace k α Ω F) (x : Ω) : F :=
  (f.iteratedFDeriv ⟨0, k.succ_pos⟩ x).curry0

/-- The formal Taylor series recorded by an element, extended by zero outside `Ω` and truncated
after order `k`. -/
private def series (f : CkHolderOnSpace k α Ω F) (x : E) : FormalMultilinearSeries ℝ E F :=
  fun m ↦ if h : m < k + 1 then Function.extend Subtype.val (f.iteratedFDeriv ⟨m, h⟩) 0 x else 0

private theorem series_of_lt (f : CkHolderOnSpace k α Ω F) {m : ℕ} (h : m < k + 1) :
    (series f · m) = Function.extend Subtype.val (f.iteratedFDeriv ⟨m, h⟩) 0 :=
  funext fun x ↦ by simp [series, h]

private theorem series_apply_of_lt (f : CkHolderOnSpace k α Ω F) {m : ℕ} (h : m < k + 1)
    (x : Ω) : series f x m = f.iteratedFDeriv ⟨m, h⟩ x := by
  rw [congrFun (series_of_lt f h) x, Subtype.val_injective.extend_apply]

/-- The recorded derivative fields form a Taylor series up to order `k` on `Ω` for every map
agreeing with the element on `Ω`. -/
private theorem hasFTaylorSeriesUpToOn (f : CkHolderOnSpace k α Ω F) {g : E → F}
    (hg : ∀ x : Ω, g x = f.toFun x) : HasFTaylorSeriesUpToOn k g (series f) Ω where
  zero_eq x hx := by
    rw [series_apply_of_lt f k.succ_pos ⟨x, hx⟩, hg ⟨x, hx⟩, toFun]
  fderivWithin m hm x hx := by
    have hmk : m < k := by exact_mod_cast hm
    have hfun := series_of_lt f (m := m) (by omega)
    rw [hfun, series_apply_of_lt f (by omega) ⟨x, hx⟩]
    exact (hasFDerivAt_fieldL f ⟨m, hmk⟩ ⟨x, hx⟩).hasFDerivWithinAt
  cont m hm := by
    have hmk : m < k + 1 := by
      have : m ≤ k := by exact_mod_cast hm
      omega
    rw [series_of_lt f hmk, continuousOn_iff_continuous_domRestrict]
    convert (f.iteratedFDeriv ⟨m, hmk⟩).continuous using 1
    funext x
    exact Subtype.val_injective.extend_apply _ _ x

private theorem iteratedFDeriv_toFun_eq (f : CkHolderOnSpace k α Ω F) {g : E → F}
    (hg : ∀ x : Ω, g x = f.toFun x) (i : Fin (k + 1)) (x : Ω) :
    _root_.iteratedFDeriv ℝ i g x = f.iteratedFDeriv i x := by
  rw [← iteratedFDerivWithin_of_isOpen i Ω.isOpen x.2,
    ← (hasFTaylorSeriesUpToOn f hg).eq_iteratedFDerivWithin_of_uniqueDiffOn
      (by exact_mod_cast i.is_le) Ω.isOpen.uniqueDiffOn x.2, series_apply_of_lt f i.2 x]

/-- An element of `C^{k,α}(Ω)` is determined by its underlying map. -/
theorem toFun_injective :
    Function.Injective (toFun (k := k) (α := α) (Ω := Ω) (F := F)) := by
  intro f g hfg
  have hfield : ∀ i, f.iteratedFDeriv i = g.iteratedFDeriv i := fun i ↦ by
    ext1 x
    rw [← iteratedFDeriv_toFun_eq f (Subtype.val_injective.extend_apply f.toFun (0 : E → F)),
      ← iteratedFDeriv_toFun_eq g (Subtype.val_injective.extend_apply g.toFun (0 : E → F)), hfg]
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

instance instFunLike : FunLike (CkHolderOnSpace k α Ω F) Ω F where
  coe := toFun
  coe_injective := toFun_injective

@[simp]
theorem toFun_eq_coe (f : CkHolderOnSpace k α Ω F) : f.toFun = ⇑f :=
  (rfl)

/-- Two elements of `C^{k,α}(Ω)` are equal when their underlying maps agree pointwise. -/
@[ext]
theorem ext {f g : CkHolderOnSpace k α Ω F} (h : ∀ x, f x = g x) : f = g :=
  DFunLike.ext f g h

/-- The recorded derivative fields are the iterated Fréchet derivatives of every map agreeing with
the element on `Ω`. -/
theorem iteratedFDeriv_eq (f : CkHolderOnSpace k α Ω F) {g : E → F} (hg : ∀ x : Ω, g x = f x)
    (i : Fin (k + 1)) (x : Ω) :
    _root_.iteratedFDeriv ℝ i g x = f.iteratedFDeriv i x :=
  iteratedFDeriv_toFun_eq f hg i x

/-- An element of `C^{k,α}(Ω)` is `k` times continuously differentiable on `Ω`, in the sense that
every map agreeing with it on `Ω` is. -/
theorem contDiffOn (f : CkHolderOnSpace k α Ω F) {g : E → F} (hg : ∀ x : Ω, g x = f x) :
    ContDiffOn ℝ k g Ω :=
  (hasFTaylorSeriesUpToOn f hg).contDiffOn

/-- The Hölder field, as a bounded continuous field, is the derivative field of order `k`. -/
@[simp]
theorem toBoundedContinuousFunction_iteratedFDerivHolder (f : CkHolderOnSpace k α Ω F) :
    f.iteratedFDerivHolder.toBoundedContinuousFunction = f.iteratedFDeriv (Fin.last k) := by
  rw [iteratedFDeriv, fieldL_last, iteratedFDerivHolder]

/-- The Hölder field records the `k`-th iterated Fréchet derivative of every map agreeing with the
element on `Ω`. -/
theorem iteratedFDerivHolder_apply (f : CkHolderOnSpace k α Ω F) {g : E → F}
    (hg : ∀ x : Ω, g x = f x) (x : Ω) :
    f.iteratedFDerivHolder x = _root_.iteratedFDeriv ℝ k g x := by
  rw [← HolderSpace.toBoundedContinuousFunction_apply,
    toBoundedContinuousFunction_iteratedFDerivHolder]
  exact (iteratedFDeriv_eq f hg (Fin.last k) x).symm

/-- The `k`-th iterated Fréchet derivative of every map agreeing with an element of
`C^{k,α}(Ω)` on `Ω` is `α`-Hölder on `Ω`, with the Hölder seminorm of the Hölder field. -/
theorem holderOnWith_iteratedFDeriv (f : CkHolderOnSpace k α Ω F) {g : E → F}
    (hg : ∀ x : Ω, g x = f x) :
    HolderOnWith (nnHolderNorm α (f.iteratedFDerivHolder : Ω → E [×k]→L[ℝ] F)) α
      (_root_.iteratedFDeriv ℝ k g) Ω := by
  have he : (Ω : Set E).domRestrict (_root_.iteratedFDeriv ℝ k g) = f.iteratedFDerivHolder :=
    funext fun x ↦ (iteratedFDerivHolder_apply f hg x).symm
  rw [← HolderWith.restrict_iff, he]
  simpa only [HolderSpace.coe_toBoundedContinuousFunction] using
    f.iteratedFDerivHolder.memHolder.holderWith

/-- The `C^{k,α}(Ω)` norm is the sum of the supremum norms of the derivative fields through order
`k` and the `α`-Hölder seminorm of the `k`-th derivative field. -/
theorem norm_eq (f : CkHolderOnSpace k α Ω F) :
    ‖f‖ = ∑ i : Fin (k + 1), ‖f.iteratedFDeriv i‖ +
      nnHolderNorm α (f.iteratedFDerivHolder : Ω → E [×k]→L[ℝ] F) := by
  rw [← norm_toJet, WithLp.prod_norm_eq_of_L1, PiLp.norm_eq_of_L1, Fin.sum_univ_castSucc,
    HolderSpace.norm_def, ← HolderSpace.coe_toBoundedContinuousFunction, add_assoc]
  simp only [iteratedFDeriv, fieldL_castSucc, fieldL_last, iteratedFDerivHolder,
    WithLp.ofLp_fst, WithLp.ofLp_snd, HolderSpace.coe_toBoundedContinuousFunction]

/-- The `C^{k,α}(Ω)` norm is at most the sum of bounds for the derivative fields through order `k`
and a Hölder constant of the `k`-th derivative field. -/
theorem norm_le_of_norm_iteratedFDeriv_le_of_holderWith {M : Fin (k + 1) → ℝ} {H : ℝ≥0}
    (f : CkHolderOnSpace k α Ω F)
    (hM : ∀ i, 0 ≤ M i) (hb : ∀ i x, ‖f.iteratedFDeriv i x‖ ≤ M i)
    (hH : HolderWith H α (f.iteratedFDerivHolder : Ω → E [×k]→L[ℝ] F)) :
    ‖f‖ ≤ ∑ i, M i + H := by
  rw [norm_eq]
  gcongr with i
  · exact (BoundedContinuousFunction.norm_le (hM i)).2 (hb i)
  · exact_mod_cast hH.nnholderNorm_le

/-- The supremum norm of each derivative field is controlled by the `C^{k,α}(Ω)` norm. -/
theorem norm_iteratedFDeriv_le (f : CkHolderOnSpace k α Ω F) (i : Fin (k + 1)) :
    ‖f.iteratedFDeriv i‖ ≤ ‖f‖ := by
  rw [norm_eq]
  exact (Finset.single_le_sum (fun j _ ↦ norm_nonneg (f.iteratedFDeriv j))
    (Finset.mem_univ i)).trans (le_add_of_nonneg_right (NNReal.coe_nonneg _))

/-- The `α`-Hölder seminorm of the `k`-th derivative field is controlled by the `C^{k,α}(Ω)`
norm. -/
theorem nnHolderNorm_iteratedFDerivHolder_le (f : CkHolderOnSpace k α Ω F) :
    (nnHolderNorm α (f.iteratedFDerivHolder : Ω → E [×k]→L[ℝ] F) : ℝ) ≤ ‖f‖ := by
  rw [norm_eq]
  exact le_add_of_nonneg_left (Finset.sum_nonneg fun j _ ↦ norm_nonneg _)

/-- Each iterated derivative through order `k` of a map agreeing with an element of
`C^{k,α}(Ω)` on `Ω` is controlled on `Ω` by the supremum norm of the derivative field of the same
order. -/
theorem norm_iteratedFDeriv_apply_le_norm_iteratedFDeriv (f : CkHolderOnSpace k α Ω F)
    {g : E → F} (hg : ∀ x : Ω, g x = f x) (i : Fin (k + 1)) (x : Ω) :
    ‖_root_.iteratedFDeriv ℝ i g x‖ ≤ ‖f.iteratedFDeriv i‖ := by
  rw [iteratedFDeriv_eq f hg i x]
  exact (f.iteratedFDeriv i).norm_coe_le_norm x

/-- Each iterated derivative through order `k` of a map agreeing with an element of
`C^{k,α}(Ω)` on `Ω` is controlled on `Ω` by the `C^{k,α}(Ω)` norm. -/
theorem norm_iteratedFDeriv_apply_le (f : CkHolderOnSpace k α Ω F) {g : E → F}
    (hg : ∀ x : Ω, g x = f x) {i : ℕ} (hi : i ≤ k) (x : Ω) :
    ‖_root_.iteratedFDeriv ℝ i g x‖ ≤ ‖f‖ :=
  (f.norm_iteratedFDeriv_apply_le_norm_iteratedFDeriv hg ⟨i, Nat.lt_succ_of_le hi⟩ x).trans
    (norm_iteratedFDeriv_le f _)

/-- The values of an element of `C^{k,α}(Ω)` are controlled by its norm. -/
theorem norm_apply_le (f : CkHolderOnSpace k α Ω F) (x : Ω) : ‖f x‖ ≤ ‖f‖ := by
  have hext : ∀ y : Ω, Function.extend Subtype.val f 0 y = f y := fun y ↦
    Subtype.val_injective.extend_apply _ _ y
  simpa [hext] using norm_iteratedFDeriv_apply_le f hext (Nat.zero_le k) x

/-- The `i`-th derivative field, as a continuous linear map to bounded continuous fields on
`Ω`. It is bounded by the `C^{k,α}(Ω)` norm pointwise, by
`CkHolderOnSpace.norm_iteratedFDeriv_le`. -/
-- No operator-norm bound is stated: outside this file, without the local shortcut instances,
-- instance search for the operator norm on this space of continuous linear maps exceeds the
-- default synthesis limits, so such a statement could only be used here.
def iteratedFDerivL (i : Fin (k + 1)) :
    CkHolderOnSpace k α Ω F →L[ℝ] (Ω →ᵇ (E [×i]→L[ℝ] F)) :=
  (fieldL i).comp toJetL

@[simp]
theorem iteratedFDerivL_apply (i : Fin (k + 1)) (f : CkHolderOnSpace k α Ω F) :
    iteratedFDerivL i f = f.iteratedFDeriv i := by
  rw [iteratedFDerivL, ContinuousLinearMap.comp_apply, toJetL_apply, iteratedFDeriv]

/-- The `k`-th derivative field, as a continuous linear map to the bounded Hölder space on
`Ω`. -/
def iteratedFDerivHolderL : CkHolderOnSpace k α Ω F →L[ℝ] HolderSpace α Ω (E [×k]→L[ℝ] F) :=
  (WithLp.sndL 1 ℝ _ _).comp toJetL

@[simp]
theorem iteratedFDerivHolderL_apply (f : CkHolderOnSpace k α Ω F) :
    iteratedFDerivHolderL f = f.iteratedFDerivHolder := by
  rw [iteratedFDerivHolderL, ContinuousLinearMap.comp_apply, toJetL_apply, WithLp.sndL_apply,
    iteratedFDerivHolder, WithLp.ofLp_snd]

/-- The Hölder-space norm of the `k`-th derivative field is controlled by the `C^{k,α}(Ω)`
norm. -/
theorem norm_iteratedFDerivHolder_le (f : CkHolderOnSpace k α Ω F) :
    ‖f.iteratedFDerivHolder‖ ≤ ‖f‖ := by
  rw [← norm_toJet, WithLp.prod_norm_eq_of_L1]
  exact le_add_of_nonneg_left (norm_nonneg _)

/-- The `k`-th derivative map to the bounded Hölder space has operator norm at most one. -/
theorem norm_iteratedFDerivHolderL_le_one :
    ‖iteratedFDerivHolderL (k := k) (α := α) (Ω := Ω) (F := F)‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun f ↦ by
    rw [iteratedFDerivHolderL_apply, one_mul]
    exact norm_iteratedFDerivHolder_le f

@[simp]
theorem iteratedFDeriv_zero (i : Fin (k + 1)) :
    (0 : CkHolderOnSpace k α Ω F).iteratedFDeriv i = 0 := by
  simpa only [iteratedFDerivL_apply] using
    (iteratedFDerivL (α := α) (Ω := Ω) (F := F) i).map_zero

@[simp]
theorem iteratedFDeriv_add (f g : CkHolderOnSpace k α Ω F) (i : Fin (k + 1)) :
    (f + g).iteratedFDeriv i = f.iteratedFDeriv i + g.iteratedFDeriv i := by
  simpa only [iteratedFDerivL_apply] using (iteratedFDerivL i).map_add f g

@[simp]
theorem iteratedFDeriv_smul (c : ℝ) (f : CkHolderOnSpace k α Ω F) (i : Fin (k + 1)) :
    (c • f).iteratedFDeriv i = c • f.iteratedFDeriv i := by
  simpa only [iteratedFDerivL_apply] using (iteratedFDerivL i).map_smul c f

@[simp]
theorem iteratedFDerivHolder_zero :
    (0 : CkHolderOnSpace k α Ω F).iteratedFDerivHolder = 0 := by
  simpa only [iteratedFDerivHolderL_apply] using
    (iteratedFDerivHolderL (k := k) (α := α) (Ω := Ω) (F := F)).map_zero

@[simp]
theorem iteratedFDerivHolder_add (f g : CkHolderOnSpace k α Ω F) :
    (f + g).iteratedFDerivHolder = f.iteratedFDerivHolder + g.iteratedFDerivHolder := by
  simpa only [iteratedFDerivHolderL_apply] using iteratedFDerivHolderL.map_add f g

@[simp]
theorem iteratedFDerivHolder_smul (c : ℝ) (f : CkHolderOnSpace k α Ω F) :
    (c • f).iteratedFDerivHolder = c • f.iteratedFDerivHolder := by
  simpa only [iteratedFDerivHolderL_apply] using iteratedFDerivHolderL.map_smul c f

@[simp]
theorem coe_zero : ⇑(0 : CkHolderOnSpace k α Ω F) = 0 := by
  ext x
  simp only [← toFun_eq_coe, toFun, iteratedFDeriv_zero, Pi.zero_apply,
    FunLike.coe_zero]
  simp

@[simp]
theorem coe_add (f g : CkHolderOnSpace k α Ω F) : ⇑(f + g) = f + g := by
  ext x
  simp only [← toFun_eq_coe, toFun, iteratedFDeriv_add, Pi.add_apply,
    _root_.add_apply]
  simp

@[simp]
theorem coe_smul (c : ℝ) (f : CkHolderOnSpace k α Ω F) : ⇑(c • f) = c • ⇑f := by
  ext x
  simp only [← toFun_eq_coe, toFun, iteratedFDeriv_smul, Pi.smul_apply,
    _root_.smul_apply]
  simp

section OfContDiffOn

variable {g : E → F}

/-- The bounded continuous field on `Ω` of the `i`-th iterated derivative of a `C^k` map on `Ω`
with bounded derivatives there, for `i ≤ k`. -/
private def fieldOf (i : ℕ) (hg : ContDiffOn ℝ k g Ω) (hi : i ≤ k)
    (hbdd : ∃ C, ∀ x ∈ Ω, ‖_root_.iteratedFDeriv ℝ i g x‖ ≤ C) : Ω →ᵇ (E [×i]→L[ℝ] F) :=
  BoundedContinuousFunction.ofNormedAddCommGroup (fun x : Ω ↦ _root_.iteratedFDeriv ℝ i g x)
    ((ContinuousOn.continuousOn_iteratedFDeriv hg Ω.isOpen (by exact_mod_cast hi)).domRestrict)
    hbdd.choose fun x ↦ hbdd.choose_spec x x.2

private theorem fieldOf_apply (i : ℕ) (hg : ContDiffOn ℝ k g Ω) (hi : i ≤ k)
    (hbdd : ∃ C, ∀ x ∈ Ω, ‖_root_.iteratedFDeriv ℝ i g x‖ ≤ C) (x : Ω) :
    fieldOf i hg hi hbdd x = _root_.iteratedFDeriv ℝ i g x :=
  rfl

private theorem memHolder_fieldOf (hg : ContDiffOn ℝ k g Ω)
    (hbdd : ∃ C, ∀ x ∈ Ω, ‖_root_.iteratedFDeriv ℝ k g x‖ ≤ C)
    (hholder : ∃ C, HolderOnWith C α (_root_.iteratedFDeriv ℝ k g) Ω) :
    MemHolder α ⇑(fieldOf k hg le_rfl hbdd) :=
  hholder.choose_spec.holderWith.memHolder

/-- The jet of iterated derivatives on `Ω` of a `C^k` map on `Ω` with bounded derivatives through
order `k` and `α`-Hölder `k`-th derivative there. -/
private def jetOf (g : E → F) (hg : ContDiffOn ℝ k g Ω)
    (hbdd : ∀ i ≤ k, ∃ C, ∀ x ∈ Ω, ‖_root_.iteratedFDeriv ℝ i g x‖ ≤ C)
    (hholder : ∃ C, HolderOnWith C α (_root_.iteratedFDeriv ℝ k g) Ω) : Jet k α Ω F :=
  WithLp.toLp 1
    (WithLp.toLp 1 fun j : Fin k ↦ fieldOf j hg j.2.le (hbdd j j.2.le),
      HolderSpace.ofBoundedContinuousFunction (fieldOf k hg le_rfl (hbdd k le_rfl))
        (memHolder_fieldOf hg (hbdd k le_rfl) hholder))

private theorem fieldL_jetOf (hg : ContDiffOn ℝ k g Ω)
    (hbdd : ∀ i ≤ k, ∃ C, ∀ x ∈ Ω, ‖_root_.iteratedFDeriv ℝ i g x‖ ≤ C)
    (hholder : ∃ C, HolderOnWith C α (_root_.iteratedFDeriv ℝ k g) Ω) (i : Fin (k + 1))
    (x : Ω) : fieldL i (jetOf g hg hbdd hholder) x = _root_.iteratedFDeriv ℝ i g x := by
  induction i using Fin.lastCases with
  | last =>
    rw [fieldL_last]
    simp only [jetOf]
    rw [HolderSpace.toBoundedContinuousFunction_ofBoundedContinuousFunction]
    exact fieldOf_apply k hg le_rfl _ x
  | cast j =>
    rw [fieldL_castSucc]
    simp [jetOf, fieldOf_apply]

private theorem isJetGraph_jetOf (hg : ContDiffOn ℝ k g Ω)
    (hbdd : ∀ i ≤ k, ∃ C, ∀ x ∈ Ω, ‖_root_.iteratedFDeriv ℝ i g x‖ ≤ C)
    (hholder : ∃ C, HolderOnWith C α (_root_.iteratedFDeriv ℝ k g) Ω) :
    IsJetGraph (jetOf g hg hbdd hholder) := fun j x ↦ by
  have h := ((hg.contDiffAt (Ω.isOpen.mem_nhds x.2)).differentiableAt_iteratedFDeriv
    (m := j) (by exact_mod_cast j.2)).hasFDerivAt
  rw [fderiv_iteratedFDeriv, Function.comp_apply] at h
  rw [fieldL_jetOf]
  exact h.congr_of_eventuallyEq (extend_eventuallyEq (fieldL_jetOf hg hbdd hholder _) x)

/-- Build an element of `C^{k,α}(Ω)` from a map which is `C^k` on `Ω`, with iterated derivatives
through order `k` bounded on `Ω` and `k`-th iterated derivative `α`-Hölder on `Ω`. -/
def ofContDiffOn (g : E → F) (hg : ContDiffOn ℝ k g Ω)
    (hbdd : ∀ i ≤ k, ∃ C, ∀ x ∈ Ω, ‖_root_.iteratedFDeriv ℝ i g x‖ ≤ C)
    (hholder : ∃ C, HolderOnWith C α (_root_.iteratedFDeriv ℝ k g) Ω) :
    CkHolderOnSpace k α Ω F :=
  mk (jetOf g hg hbdd hholder) (isJetGraph_jetOf hg hbdd hholder)

variable (hg : ContDiffOn ℝ k g Ω)
  (hbdd : ∀ i ≤ k, ∃ C, ∀ x ∈ Ω, ‖_root_.iteratedFDeriv ℝ i g x‖ ≤ C)
  (hholder : ∃ C, HolderOnWith C α (_root_.iteratedFDeriv ℝ k g) Ω)

@[simp]
theorem iteratedFDeriv_ofContDiffOn (i : Fin (k + 1)) (x : Ω) :
    (ofContDiffOn g hg hbdd hholder).iteratedFDeriv i x = _root_.iteratedFDeriv ℝ i g x := by
  rw [iteratedFDeriv, ofContDiffOn, toJet_mk, fieldL_jetOf]

@[simp]
theorem coe_ofContDiffOn : ⇑(ofContDiffOn g hg hbdd hholder) = fun x : Ω ↦ g x := by
  ext x
  rw [← toFun_eq_coe, toFun, iteratedFDeriv_ofContDiffOn, iteratedFDeriv_zero_eq_comp]
  simp

@[simp]
theorem coe_iteratedFDerivHolder_ofContDiffOn :
    ⇑(ofContDiffOn g hg hbdd hholder).iteratedFDerivHolder =
      fun x : Ω ↦ _root_.iteratedFDeriv ℝ k g x := by
  funext x
  rw [← HolderSpace.toBoundedContinuousFunction_apply,
    toBoundedContinuousFunction_iteratedFDerivHolder, iteratedFDeriv_ofContDiffOn]
  -- The order `↑(Fin.last k)` is `k` by `Fin.val_last`, which holds by `rfl`; rewriting it is
  -- not possible, since the type of the derivative depends on the order.
  rfl

/-- The norm of the element built from a map is at most the sum of bounds on `Ω` for its
iterated derivatives through order `k` and a Hölder constant on `Ω` of the `k`-th one. -/
theorem norm_ofContDiffOn_le {M : Fin (k + 1) → ℝ} {H : ℝ≥0} (hM : ∀ i, 0 ≤ M i)
    (hb : ∀ i : Fin (k + 1), ∀ x ∈ Ω, ‖_root_.iteratedFDeriv ℝ i g x‖ ≤ M i)
    (hH : HolderOnWith H α (_root_.iteratedFDeriv ℝ k g) Ω) :
    ‖ofContDiffOn g hg hbdd hholder‖ ≤ ∑ i, M i + H :=
  norm_le_of_norm_iteratedFDeriv_le_of_holderWith _ hM (fun i x ↦ by
      rw [iteratedFDeriv_ofContDiffOn]
      exact hb i x x.2)
    (by
      rw [coe_iteratedFDerivHolder_ofContDiffOn]
      exact HolderWith.restrict_iff.2 hH)

end OfContDiffOn

/-- The derivative identities are closed under uniform convergence of the fields. -/
private theorem isClosed_isJetGraph : IsClosed {J : Jet k α Ω F | IsJetGraph J} := by
  have hset : {J : Jet k α Ω F | IsJetGraph J} =
      ⋂ j : Fin k, (fun J : Jet k α Ω F ↦ (fieldL j.castSucc J, fieldL j.succ J)) ⁻¹'
        {J | ∀ x : Ω, HasFDerivAt (Function.extend Subtype.val (J.1 : Ω → E [×j]→L[ℝ] F) 0)
          (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (j + 1) ↦ E) F (J.2 x)) x} := by
    ext J
    simp [IsJetGraph]
    rfl
  rw [hset]
  exact isClosed_iInter fun j ↦
    (isClosed_setOf_hasFDerivAt_extend_comp Ω.isOpen _ (continuousMultilinearCurryLeftEquiv ℝ
      (fun _ : Fin (j + 1) ↦ E) F).isometry.uniformContinuous).preimage
      ((fieldL (k := k) (α := α) (Ω := Ω) (F := F) _).continuous.prodMk
        (fieldL (k := k) (α := α) (Ω := Ω) (F := F) _).continuous)

/-- `C^{k,α}(Ω)` with a Banach codomain is a Banach space. -/
instance instCompleteSpace [CompleteSpace F] : CompleteSpace (CkHolderOnSpace k α Ω F) := by
  unfold CkHolderOnSpace
  exact isClosed_isJetGraph.completeSpace_coe

attribute [irreducible] instNormedAddCommGroup instNormedSpace _root_.TauCeti.CkHolderOnSpace

/-- The extension by zero outside `Ω` of an element of `C^{k,α}(Ω)` agrees with it on `Ω`. -/
private theorem extend_apply (f : CkHolderOnSpace k α Ω F) {x : E} (hx : x ∈ Ω) :
    Function.extend Subtype.val ⇑f (0 : E → F) x = f ⟨x, hx⟩ :=
  Function.extend_val_apply hx

section OfExtend

variable {k' : ℕ} {α' : ℝ≥0} {Ω' : Opens E}

/-- For `Ω' ≤ Ω` and `k' ≤ k`, the continuous linear map `C^{k,α}(Ω) → C^{k',α'}(Ω')` which keeps
the underlying map, built from the extension by zero of each element. It takes a Hölder constant
`H f` on `Ω'` for the `k'`-th derivative of each element `f`, and a constant `C` bounding the
derivative suprema through order `k'` plus `H f` by `C * ‖f‖`. The restriction and inclusion
maps below are of this form. -/
private def ofExtendL (hΩ : Ω' ≤ Ω) (hk : k' ≤ k) (H : CkHolderOnSpace k α Ω F → ℝ≥0)
    (hH : ∀ f : CkHolderOnSpace k α Ω F,
      HolderOnWith (H f) α' (_root_.iteratedFDeriv ℝ k' (Function.extend Subtype.val ⇑f 0)) Ω')
    (C : ℝ) (hC : ∀ f : CkHolderOnSpace k α Ω F,
      ∑ i : Fin (k' + 1), ‖f.iteratedFDeriv (Fin.castLE (by omega) i)‖ + H f ≤ C * ‖f‖) :
    CkHolderOnSpace k α Ω F →L[ℝ] CkHolderOnSpace k' α' Ω' F :=
  LinearMap.mkContinuous
    { toFun f := ofContDiffOn (Function.extend Subtype.val ⇑f 0)
        (((f.contDiffOn fun x ↦ extend_apply f x.2).mono (SetLike.coe_subset_coe.2 hΩ)).of_le
          (by exact_mod_cast hk))
        (fun _ hi ↦ ⟨‖f‖, fun x hx ↦
          f.norm_iteratedFDeriv_apply_le (fun y ↦ extend_apply f y.2) (hi.trans hk) ⟨x, hΩ hx⟩⟩)
        ⟨_, hH f⟩
      map_add' f g := ext fun x ↦ by
        simp only [coe_ofContDiffOn, coe_add, Pi.add_apply, Function.extend_val_apply (hΩ x.2)]
      map_smul' c f := ext fun x ↦ by
        simp only [coe_ofContDiffOn, coe_smul, Pi.smul_apply, RingHom.id_apply,
          Function.extend_val_apply (hΩ x.2)] }
    C fun f ↦ by
      rw [LinearMap.coe_mk, AddHom.coe_mk]
      exact (norm_ofContDiffOn_le _ _ _
        (M := fun i : Fin (k' + 1) ↦ ‖f.iteratedFDeriv (Fin.castLE (by omega) i)‖)
        (fun _ ↦ norm_nonneg _)
        (fun i x hx ↦ f.norm_iteratedFDeriv_apply_le_norm_iteratedFDeriv
          (fun y ↦ extend_apply f y.2) (Fin.castLE (by omega) i) ⟨x, hΩ hx⟩) (hH f)).trans (hC f)

variable (hΩ : Ω' ≤ Ω) (hk : k' ≤ k) (H : CkHolderOnSpace k α Ω F → ℝ≥0)
  (hH : ∀ f : CkHolderOnSpace k α Ω F,
    HolderOnWith (H f) α' (_root_.iteratedFDeriv ℝ k' (Function.extend Subtype.val ⇑f 0)) Ω')
  (C : ℝ) (hC : ∀ f : CkHolderOnSpace k α Ω F,
    ∑ i : Fin (k' + 1), ‖f.iteratedFDeriv (Fin.castLE (by omega) i)‖ + H f ≤ C * ‖f‖)

private theorem ofExtendL_apply (f : CkHolderOnSpace k α Ω F) (x : Ω') :
    ofExtendL hΩ hk H hH C hC f x = f ⟨x, hΩ x.2⟩ := by
  simp only [ofExtendL, LinearMap.mkContinuous_apply, LinearMap.coe_mk, AddHom.coe_mk,
    coe_ofContDiffOn, extend_apply f (hΩ x.2)]

private theorem iteratedFDeriv_ofExtendL (f : CkHolderOnSpace k α Ω F) (i : Fin (k' + 1))
    (x : Ω') : (ofExtendL hΩ hk H hH C hC f).iteratedFDeriv i x =
      f.iteratedFDeriv (Fin.castLE (by omega) i) ⟨x, hΩ x.2⟩ := by
  simp only [ofExtendL, LinearMap.mkContinuous_apply, LinearMap.coe_mk, AddHom.coe_mk,
    iteratedFDeriv_ofContDiffOn]
  exact iteratedFDeriv_eq f (fun y ↦ extend_apply f y.2) (Fin.castLE (by omega) i) ⟨x, hΩ x.2⟩

private theorem norm_ofExtendL_le (hC₀ : 0 ≤ C) : ‖ofExtendL hΩ hk H hH C hC‖ ≤ C :=
  LinearMap.mkContinuous_norm_le _ hC₀ _

end OfExtend

section Restrict

variable {Ω' : Opens E}

/-- Restriction of an element of `C^{k,α}(Ω)` to a smaller open set. -/
def restrictL (h : Ω' ≤ Ω) : CkHolderOnSpace k α Ω F →L[ℝ] CkHolderOnSpace k α Ω' F :=
  ofExtendL h le_rfl (fun f ↦ nnHolderNorm α (f.iteratedFDerivHolder : Ω → E [×k]→L[ℝ] F))
    (fun f ↦ (f.holderOnWith_iteratedFDeriv fun x ↦ extend_apply f x.2).mono
      (SetLike.coe_subset_coe.2 h))
    1 fun f ↦ by
      rw [one_mul]
      exact (norm_eq f).ge

@[simp]
theorem restrictL_apply (h : Ω' ≤ Ω) (f : CkHolderOnSpace k α Ω F) (x : Ω') :
    restrictL h f x = f ⟨x, h x.2⟩ :=
  ofExtendL_apply _ _ _ _ _ _ f x

@[simp]
theorem iteratedFDeriv_restrictL (h : Ω' ≤ Ω) (f : CkHolderOnSpace k α Ω F) (i : Fin (k + 1))
    (x : Ω') : (restrictL h f).iteratedFDeriv i x = f.iteratedFDeriv i ⟨x, h x.2⟩ :=
  iteratedFDeriv_ofExtendL _ _ _ _ _ _ f i x

@[simp]
theorem iteratedFDerivHolder_restrictL (h : Ω' ≤ Ω) (f : CkHolderOnSpace k α Ω F) (x : Ω') :
    (restrictL h f).iteratedFDerivHolder x = f.iteratedFDerivHolder ⟨x, h x.2⟩ := by
  rw [← HolderSpace.toBoundedContinuousFunction_apply,
    toBoundedContinuousFunction_iteratedFDerivHolder, iteratedFDeriv_restrictL,
    ← toBoundedContinuousFunction_iteratedFDerivHolder,
    HolderSpace.toBoundedContinuousFunction_apply]

/-- Restriction to a smaller open set has norm at most one. -/
theorem norm_restrictL_le (h : Ω' ≤ Ω) : ‖restrictL (k := k) (α := α) (F := F) h‖ ≤ 1 :=
  norm_ofExtendL_le _ _ _ _ _ _ zero_le_one

end Restrict

section InclusionSucc

/-- On a convex open set and for `α ≤ 1`, the `k`-th iterated derivative of an element of
`C^{k+1,α}(Ω)` is `α`-Hölder on `Ω`, with constant the supremum of the `(k+1)`-st derivative plus
twice the supremum of the `k`-th one. -/
theorem holderOnWith_iteratedFDeriv_of_convex (f : CkHolderOnSpace (k + 1) α Ω F) {g : E → F}
    (hg : ∀ x : Ω, g x = f x) (hΩ : Convex ℝ (Ω : Set E)) (hα : α ≤ 1) :
    HolderOnWith (‖f.iteratedFDeriv (Fin.last (k + 1))‖₊ +
      2 * ‖f.iteratedFDeriv (Fin.last k).castSucc‖₊) α (_root_.iteratedFDeriv ℝ k g) Ω :=
  (f.contDiffOn hg).holderOnWith_iteratedFDeriv_of_lt Ω.isOpen hΩ (Nat.lt_succ_self k) hα
    (fun x hx ↦ by
      rw [coe_nnNorm]
      exact f.norm_iteratedFDeriv_apply_le_norm_iteratedFDeriv hg (Fin.last k).castSucc ⟨x, hx⟩)
    (fun x hx ↦ by
      rw [coe_nnNorm]
      exact f.norm_iteratedFDeriv_apply_le_norm_iteratedFDeriv hg (Fin.last (k + 1)) ⟨x, hx⟩)

/-- On a convex open set and for `α ≤ 1`, the inclusion `C^{k+1,α}(Ω) → C^{k,α}(Ω)`. Some
condition on `Ω` is needed: on `(-1, 0) ∪ (0, 1)` the sign function has vanishing derivative, so it
lies in `C^{1,α}(Ω)`, but its `α`-Hölder quotient across `0` is unbounded, so it does not lie in
`C^{0,α}(Ω)`. -/
def inclusionSuccL (hΩ : Convex ℝ (Ω : Set E)) (hα : α ≤ 1) :
    CkHolderOnSpace (k + 1) α Ω F →L[ℝ] CkHolderOnSpace k α Ω F :=
  ofExtendL le_rfl k.le_succ
    (fun f ↦ ‖f.iteratedFDeriv (Fin.last (k + 1))‖₊ + 2 * ‖f.iteratedFDeriv (Fin.last k).castSucc‖₊)
    (fun f ↦ f.holderOnWith_iteratedFDeriv_of_convex (fun x ↦ extend_apply f x.2) hΩ hα)
    3 fun f ↦ by
      have hsum : ∑ i : Fin (k + 1), ‖f.iteratedFDeriv i.castSucc‖ +
          ‖f.iteratedFDeriv (Fin.last (k + 1))‖ ≤ ‖f‖ := by
        rw [norm_eq f, Fin.sum_univ_castSucc (n := k + 1)]
        exact le_add_of_nonneg_right (NNReal.coe_nonneg _)
      have hk := norm_iteratedFDeriv_le f (Fin.last k).castSucc
      change ∑ i : Fin (k + 1), ‖f.iteratedFDeriv i.castSucc‖ + _ ≤ _
      push_cast
      linarith

@[simp]
theorem inclusionSuccL_apply (hΩ : Convex ℝ (Ω : Set E)) (hα : α ≤ 1)
    (f : CkHolderOnSpace (k + 1) α Ω F) (x : Ω) : inclusionSuccL hΩ hα f x = f x :=
  ofExtendL_apply _ _ _ _ _ _ f x

@[simp]
theorem iteratedFDeriv_inclusionSuccL (hΩ : Convex ℝ (Ω : Set E)) (hα : α ≤ 1)
    (f : CkHolderOnSpace (k + 1) α Ω F) (i : Fin (k + 1)) (x : Ω) :
    (inclusionSuccL hΩ hα f).iteratedFDeriv i x = f.iteratedFDeriv i.castSucc x :=
  iteratedFDeriv_ofExtendL _ _ _ _ _ _ f i x

/-- The inclusion `C^{k+1,α}(Ω) → C^{k,α}(Ω)` on a convex open set has norm at most `3`. -/
theorem norm_inclusionSuccL_le (hΩ : Convex ℝ (Ω : Set E)) (hα : α ≤ 1) :
    ‖inclusionSuccL (k := k) (F := F) hΩ hα‖ ≤ 3 :=
  norm_ofExtendL_le _ _ _ _ _ _ zero_le_three

end InclusionSucc

section Inclusion

variable {β : ℝ≥0}

/-- On a bounded open set and for `β ≤ α`, the inclusion `C^{k,α}(Ω) → C^{k,β}(Ω)`. -/
def inclusionL (hβα : β ≤ α) (hΩ : Bornology.IsBounded (Ω : Set E)) :
    CkHolderOnSpace k α Ω F →L[ℝ] CkHolderOnSpace k β Ω F :=
  ofExtendL le_rfl le_rfl
    (fun f ↦ nnHolderNorm α (f.iteratedFDerivHolder : Ω → E [×k]→L[ℝ] F) *
      (Metric.diam (Ω : Set E)).toNNReal ^ ((α : ℝ) - β))
    (fun f ↦ (f.holderOnWith_iteratedFDeriv fun x ↦ extend_apply f x.2).of_le
      (fun _ hx _ hy ↦ Metric.edist_le_toNNReal_diam_of_mem hΩ hx hy) hβα)
    (max 1 (((Metric.diam (Ω : Set E)).toNNReal : ℝ) ^ ((α : ℝ) - β))) fun f ↦ by
      have hS : 0 ≤ ∑ i, ‖f.iteratedFDeriv i‖ := Finset.sum_nonneg fun _ _ ↦ norm_nonneg _
      have hH : (0 : ℝ) ≤ nnHolderNorm α (f.iteratedFDerivHolder : Ω → E [×k]→L[ℝ] F) :=
        NNReal.coe_nonneg _
      have h₁ : (1 : ℝ) ≤ max 1 (((Metric.diam (Ω : Set E)).toNNReal : ℝ) ^ ((α : ℝ) - β)) :=
        le_max_left _ _
      have h₂ : ((Metric.diam (Ω : Set E)).toNNReal : ℝ) ^ ((α : ℝ) - β) ≤
          max 1 (((Metric.diam (Ω : Set E)).toNNReal : ℝ) ^ ((α : ℝ) - β)) := le_max_right _ _
      change ∑ i, ‖f.iteratedFDeriv i‖ + _ ≤ _
      rw [norm_eq f]
      push_cast
      nlinarith

@[simp]
theorem inclusionL_apply (hβα : β ≤ α) (hΩ : Bornology.IsBounded (Ω : Set E))
    (f : CkHolderOnSpace k α Ω F) (x : Ω) : inclusionL hβα hΩ f x = f x :=
  ofExtendL_apply _ _ _ _ _ _ f x

@[simp]
theorem iteratedFDeriv_inclusionL (hβα : β ≤ α) (hΩ : Bornology.IsBounded (Ω : Set E))
    (f : CkHolderOnSpace k α Ω F) (i : Fin (k + 1)) (x : Ω) :
    (inclusionL hβα hΩ f).iteratedFDeriv i x = f.iteratedFDeriv i x :=
  iteratedFDeriv_ofExtendL _ _ _ _ _ _ f i x

@[simp]
theorem iteratedFDerivHolder_inclusionL (hβα : β ≤ α) (hΩ : Bornology.IsBounded (Ω : Set E))
    (f : CkHolderOnSpace k α Ω F) (x : Ω) :
    (inclusionL hβα hΩ f).iteratedFDerivHolder x = f.iteratedFDerivHolder x := by
  rw [← HolderSpace.toBoundedContinuousFunction_apply,
    toBoundedContinuousFunction_iteratedFDerivHolder, iteratedFDeriv_inclusionL,
    ← toBoundedContinuousFunction_iteratedFDerivHolder,
    HolderSpace.toBoundedContinuousFunction_apply]

/-- The inclusion `C^{k,α}(Ω) → C^{k,β}(Ω)` on a bounded open set has norm at most
`max 1 (D^(α - β))`, with `D` the diameter of `Ω`. -/
theorem norm_inclusionL_le (hβα : β ≤ α) (hΩ : Bornology.IsBounded (Ω : Set E)) :
    ‖inclusionL (k := k) (F := F) hβα hΩ‖ ≤
      max 1 (((Metric.diam (Ω : Set E)).toNNReal : ℝ) ^ ((α : ℝ) - β)) :=
  norm_ofExtendL_le _ _ _ _ _ _ (zero_le_one.trans (le_max_left _ _))

end Inclusion

end CkHolderOnSpace

/-- Shortcut instance for bounded continuous fields of `n`-multilinear maps on the whole space,
for the same reason as `CkHolderOnSpace.instNormedAddCommGroupBoundedContinuousFunction`. -/
local instance CkHolderOnSpace.instNormedAddCommGroupBoundedContinuousFunctionWhole (n : ℕ) :
    NormedAddCommGroup (E →ᵇ (E [×n]→L[ℝ] F)) :=
  inferInstance

namespace CkHolderSpace

variable {k α F}

/-- Restriction of a bounded `C^{k,α}` map on the whole space to an open set. -/
def restrictOpensL : CkHolderSpace k α E F →L[ℝ] CkHolderOnSpace k α Ω F :=
  LinearMap.mkContinuous
    { toFun f := CkHolderOnSpace.ofContDiffOn f f.contDiff.contDiffOn
        (fun _ hi ↦ ⟨‖f‖, fun x _ ↦ f.norm_iteratedFDeriv_apply_le hi x⟩)
        ⟨_, f.memHolder_iteratedFDeriv.holderWith.holderOnWith Ω⟩
      map_add' f g := CkHolderOnSpace.ext fun x ↦ by
        simp only [CkHolderOnSpace.coe_ofContDiffOn, CkHolderOnSpace.coe_add, coe_add,
          Pi.add_apply]
      map_smul' c f := CkHolderOnSpace.ext fun x ↦ by
        simp only [CkHolderOnSpace.coe_ofContDiffOn, CkHolderOnSpace.coe_smul, coe_smul,
          Pi.smul_apply, RingHom.id_apply] }
    1 fun f ↦ by
      rw [one_mul, LinearMap.coe_mk, AddHom.coe_mk]
      refine (CkHolderOnSpace.norm_ofContDiffOn_le _ _ _ (M := fun i ↦ ‖f.iteratedFDeriv i‖)
        (fun _ ↦ norm_nonneg _) (fun i x _ ↦ ?_)
        (f.memHolder_iteratedFDeriv.holderWith.holderOnWith Ω)).trans (norm_eq f).ge
      rw [iteratedFDeriv_eq]
      exact (f.iteratedFDeriv i).norm_coe_le_norm x

@[simp]
theorem restrictOpensL_apply (f : CkHolderSpace k α E F) (x : Ω) : restrictOpensL Ω f x = f x := by
  rw [restrictOpensL, LinearMap.mkContinuous_apply, LinearMap.coe_mk, AddHom.coe_mk,
    CkHolderOnSpace.coe_ofContDiffOn]

@[simp]
theorem iteratedFDeriv_restrictOpensL (f : CkHolderSpace k α E F) (i : Fin (k + 1)) (x : Ω) :
    (restrictOpensL Ω f).iteratedFDeriv i x = f.iteratedFDeriv i x := by
  rw [restrictOpensL, LinearMap.mkContinuous_apply, LinearMap.coe_mk, AddHom.coe_mk,
    CkHolderOnSpace.iteratedFDeriv_ofContDiffOn, iteratedFDeriv_eq]

@[simp]
theorem iteratedFDerivHolder_restrictOpensL (f : CkHolderSpace k α E F) (x : Ω) :
    (restrictOpensL Ω f).iteratedFDerivHolder x = f.iteratedFDerivHolder x := by
  rw [← HolderSpace.toBoundedContinuousFunction_apply,
    CkHolderOnSpace.toBoundedContinuousFunction_iteratedFDerivHolder,
    iteratedFDeriv_restrictOpensL, ← toBoundedContinuousFunction_iteratedFDerivHolder,
    HolderSpace.toBoundedContinuousFunction_apply]

/-- Restriction from the whole space to an open set has norm at most one. -/
theorem norm_restrictOpensL_le : ‖restrictOpensL (k := k) (α := α) (F := F) Ω‖ ≤ 1 :=
  LinearMap.mkContinuous_norm_le _ zero_le_one _

end CkHolderSpace

end TauCeti

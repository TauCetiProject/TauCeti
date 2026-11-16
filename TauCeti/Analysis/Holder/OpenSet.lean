/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Holder.Normed
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Normed.Lp.PiLp
public import Mathlib.Analysis.Normed.Lp.ProdLp
public import Mathlib.Topology.Sets.Opens
import Mathlib.Analysis.Calculus.ContDiff.Comp
import TauCeti.Analysis.Calculus.UniformLimitsDeriv
import TauCeti.Analysis.Holder.JetBounds
import TauCeti.Topology.ContinuousOn.Extension

/-!
# The Hölder spaces `C^{k,α}(Ω)` on an open set

For an open set `Ω` of a real normed space `E`, this file constructs the normed space
`C^{k,α}(Ω, F)` of `C^k` maps on `Ω` whose iterated Fréchet derivatives through order `k` are
bounded on `Ω` and whose `k`-th iterated derivative is `α`-Hölder on all of `Ω`, and proves that it
is Banach when the codomain is Banach. Its norm is

`‖f‖ = ∑_{i ≤ k} sup_{x ∈ Ω} ‖D^i f x‖ + [D^k f]_{α, Ω}`,

where the suprema use the operator norm of continuous multilinear maps and the Hölder seminorm
`[g]_{α, Ω} = sup_{x ≠ y ∈ Ω} ‖g x - g y‖ / ‖x - y‖^α` is taken over all pairs of points of `Ω`,
not only over nearby ones. These are the spaces in which global Schauder estimates on a domain
are stated; the bounded spaces `TauCeti.CkHolderSpace` are their analogues on the whole space.

An element is a function on the subtype `Ω`, represented by its family of iterated derivative
fields: bounded continuous fields `Ω →ᵇ (E [×i]→L[ℝ] F)` for `i < k` and a bounded Hölder field of
order `k` on `Ω`, subject to the condition that each field, extended by zero off `Ω`, has the next
field, curried on the left, as its Fréchet derivative at every point of `Ω`. Since `Ω` is open,
the extension does not affect these derivatives, and the fields are the iterated derivatives of
any function on `E` which agrees with the element on `Ω`. The conditions are closed under uniform
convergence on `Ω`, which gives completeness.

The global seminorm sees across gaps of `Ω`: on `Ω = (-1, 0) ∪ (0, 1)` the sign function is smooth
with vanishing derivatives, but for `α > 0` it is in no `C^{0,α}(Ω)`. For the same reason, for
`α > 0` the inclusion `C^{k+1,α}(Ω) ⊆ C^{k,α}(Ω)` needs some geometry of `Ω`; it is proved here
for convex `Ω`, where the mean value inequality bounds the Hölder seminorm of `D^k f` by the
supremum norms of `D^k f` and `D^{k+1} f`.

## Main declarations

* `TauCeti.CkHolderSpaceOn k α Ω F`: the space `C^{k,α}(Ω, F)` for `Ω : Opens E`.
* `TauCeti.CkHolderSpaceOn.iteratedFDeriv`: the bounded continuous `i`-th derivative field on `Ω`
  for `i ≤ k`; `TauCeti.CkHolderSpaceOn.iteratedFDeriv_eq_of_eqOn` identifies it with Mathlib's
  `iteratedFDeriv` of any function agreeing with the element on `Ω`.
* `TauCeti.CkHolderSpaceOn.contDiffOn_of_eqOn` and
  `TauCeti.CkHolderSpaceOn.holderOnWith_iteratedFDeriv_of_eqOn`: the regularity of an element;
  `TauCeti.CkHolderSpaceOn.ofContDiffOn` is the converse constructor.
* `TauCeti.CkHolderSpaceOn.norm_eq`: the norm is the sum of the supremum norms of the derivatives
  through order `k` and the `α`-Hölder seminorm on `Ω` of the `k`-th derivative.
* `TauCeti.CkHolderSpaceOn.instCompleteSpace`: completeness when the codomain is complete.
* `TauCeti.CkHolderSpaceOn.restrictL`: restriction to a smaller open set, of operator norm at most
  one.
* `TauCeti.CkHolderSpaceOn.inclusionSuccL`: the inclusion `C^{k+1,α}(Ω) → C^{k,α}(Ω)` on a convex
  open set, for `α ≤ 1`, of operator norm at most `3`.

## References

D. Gilbarg and N. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
Section 4.1.
-/

public section

noncomputable section

namespace TauCeti

open TopologicalSpace Topology
open scoped NNReal BoundedContinuousFunction

universe u v

variable (k : ℕ) (α : ℝ≥0) {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
  (Ω : Opens E) (F : Type v) [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Shortcut instance for bounded continuous fields of `n`-multilinear maps on `Ω`. Without it,
instance search for the module structure of `ℓ¹` products of these fields indexed by the order
`n` exceeds the default synthesis depth. It is local so that the instance path for these fields is
unchanged outside this file, and no public statement below mentions it: only definition bodies
and proofs use it. -/
local instance CkHolderSpaceOn.instNormedAddCommGroupBoundedContinuousFunction (n : ℕ) :
    NormedAddCommGroup (Ω →ᵇ (E [×n]→L[ℝ] F)) :=
  inferInstance

/-- Shortcut instance for bounded continuous fields of `n`-multilinear maps on `Ω`, needed for
operator norms of continuous linear maps into these fields indexed by the order `n`. It is local
for the same reason. -/
local instance CkHolderSpaceOn.instNormedSpaceBoundedContinuousFunction (n : ℕ) :
    NormedSpace ℝ (Ω →ᵇ (E [×n]→L[ℝ] F)) :=
  inferInstance

/-- The space `C^{k,α}(Ω, F)` of `C^k` maps on the open set `Ω` whose iterated Fréchet
derivatives through order `k` are bounded on `Ω` and whose `k`-th iterated derivative is
`α`-Hölder on `Ω`. Its norm is

`∑_{i ≤ k} sup_Ω ‖D^i f‖ + [D^k f]_{α, Ω}`.
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
        HasFDerivAt (Function.extend Subtype.val (field j.castSucc J : Ω → E [×j]→L[ℝ] F) 0)
          (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (j + 1) ↦ E) F
            (field j.succ J x)) x}
      zero_mem' := fun j x ↦ by
        simp only [map_zero, FunLike.coe_zero, Pi.zero_apply, Function.extend_zero]
        exact hasFDerivAt_const 0 (x : E)
      add_mem' := fun {J K} hJ hK j x ↦ by
        simp only [Set.mem_ofPred_eq, map_add, FunLike.coe_add, Pi.add_apply] at hJ hK ⊢
        have h := Function.extend_add Subtype.val (field j.castSucc J : Ω → E [×j]→L[ℝ] F)
          (field j.castSucc K) 0 0
        rw [add_zero] at h
        rw [h]
        exact (hJ j x).add (hK j x)
      smul_mem' := fun c {J} hJ j x ↦ by
        simp only [Set.mem_ofPred_eq, map_smul, FunLike.coe_smul, Pi.smul_apply] at hJ ⊢
        have h := Function.extend_smul c Subtype.val (field j.castSucc J : Ω → E [×j]→L[ℝ] F) 0
        rw [smul_zero] at h
        rw [h]
        exact (hJ j x).const_smul c }
  graph

namespace CkHolderSpaceOn

variable {k α Ω F}

variable (k α Ω F) in
/-- The ambient jet space of `C^{k,α}(Ω)`: bounded continuous derivative fields on `Ω` of orders
below `k`, with the `ℓ¹` norm, together with a bounded Hölder field of order `k` on `Ω`. -/
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

/-- The derivative identities of a jet: each field below order `k`, extended by zero, has the
next field, curried on the left, as its Fréchet derivative at every point of `Ω`. -/
private def IsJetGraph (J : Jet k α Ω F) : Prop :=
  ∀ (j : Fin k) (x : Ω),
    HasFDerivAt (Function.extend Subtype.val (fieldL j.castSucc J : Ω → E [×j]→L[ℝ] F) 0)
      (curryLeftL E F j (fieldL j.succ J x)) x

/-- Elements are the jets satisfying the derivative identities. This is the identity map: the
carrier of `CkHolderSpaceOn` states the identities through its local `field`, which is `fieldL`,
and through `continuousMultilinearCurryLeftEquiv`, whose underlying continuous linear map is
`curryLeftL`.
Besides this map, the carrier is unfolded only by `toJetL`, the two norm instances, `norm_toJet`
and `instCompleteSpace`, which use that it is a submodule of the jet space. -/
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
    HasFDerivAt (Function.extend Subtype.val (fieldL j.castSucc (toJet f) : Ω → E [×j]→L[ℝ] F) 0)
      (curryLeftL E F j (fieldL j.succ (toJet f) x)) x :=
  (equivSubtype f).2 j x

/-- The `C^{k,α}(Ω)` norm makes `CkHolderSpaceOn k α Ω F` a normed additive group. -/
instance instNormedAddCommGroup : NormedAddCommGroup (CkHolderSpaceOn k α Ω F) := by
  unfold CkHolderSpaceOn
  infer_instance

/-- The space `CkHolderSpaceOn k α Ω F` is a real normed space. -/
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
`i ≤ k`. It agrees with Mathlib's `iteratedFDeriv` by
`CkHolderSpaceOn.iteratedFDeriv_eq_of_eqOn`. -/
def iteratedFDeriv (f : CkHolderSpaceOn k α Ω F) (i : Fin (k + 1)) : Ω →ᵇ (E [×i]→L[ℝ] F) :=
  fieldL i (toJet f)

/-- The `k`-th derivative field of an element of `C^{k,α}(Ω)`, as an element of the bounded Hölder
space on `Ω`. -/
def iteratedFDerivHolder (f : CkHolderSpaceOn k α Ω F) : HolderSpace α Ω (E [×k]→L[ℝ] F) :=
  (toJet f).ofLp.2

/-- The underlying function on `Ω` of an element of `C^{k,α}(Ω)`: its order-zero derivative
field, evaluated on the empty tuple. Use the coercion `⇑f` instead. -/
def toFun (f : CkHolderSpaceOn k α Ω F) (x : Ω) : F :=
  (f.iteratedFDeriv ⟨0, k.succ_pos⟩ x).curry0

/-- The formal Taylor series recorded by an element, extended by zero off `Ω` and truncated after
order `k`. -/
private def series (f : CkHolderSpaceOn k α Ω F) (x : E) : FormalMultilinearSeries ℝ E F :=
  fun m ↦ if h : m < k + 1 then
    Function.extend Subtype.val (f.iteratedFDeriv ⟨m, h⟩ : Ω → E [×m]→L[ℝ] F) 0 x else 0

private theorem series_of_lt (f : CkHolderSpaceOn k α Ω F) (x : E) {m : ℕ} (h : m < k + 1) :
    series f x m =
      Function.extend Subtype.val (f.iteratedFDeriv ⟨m, h⟩ : Ω → E [×m]→L[ℝ] F) 0 x := by
  simp [series, h]

/-- The recorded derivative fields form a Taylor series up to order `k` on `Ω` for every function
which agrees with the element on `Ω`. -/
private theorem hasFTaylorSeriesUpToOn (f : CkHolderSpaceOn k α Ω F) {u : E → F}
    (hu : ∀ x : Ω, u x = f.toFun x) : HasFTaylorSeriesUpToOn k u (series f) Ω where
  zero_eq x hx := by
    rw [series_of_lt f x k.succ_pos, Subtype.val_injective.extend_apply _ _ (⟨x, hx⟩ : Ω),
      hu ⟨x, hx⟩, toFun]
  fderivWithin m hm x hx := by
    have hmk : m < k := by exact_mod_cast hm
    have hfun : (fun y ↦ series f y m) =
        Function.extend Subtype.val
          (fieldL (⟨m, hmk⟩ : Fin k).castSucc (toJet f) : Ω → E [×m]→L[ℝ] F) 0 :=
      funext fun y ↦ series_of_lt f y (by omega)
    rw [hfun, series_of_lt f x (by omega), Subtype.val_injective.extend_apply _ _ (⟨x, hx⟩ : Ω),
      ← curryLeftL_apply]
    exact (hasFDerivAt_fieldL f ⟨m, hmk⟩ ⟨x, hx⟩).hasFDerivWithinAt
  cont m hm := by
    have hmk : m < k + 1 := by
      have : m ≤ k := by exact_mod_cast hm
      omega
    have hfun : (fun y ↦ series f y m) =
        Function.extend Subtype.val (f.iteratedFDeriv ⟨m, hmk⟩ : Ω → E [×m]→L[ℝ] F) 0 :=
      funext fun y ↦ series_of_lt f y hmk
    rw [hfun]
    exact (f.iteratedFDeriv ⟨m, hmk⟩).continuous.continuousOn_extend_subtypeVal 0

private theorem iteratedFDeriv_eq_of_eqOn_toFun (f : CkHolderSpaceOn k α Ω F) {u : E → F}
    (hu : ∀ x : Ω, u x = f.toFun x) (i : Fin (k + 1)) (x : Ω) :
    _root_.iteratedFDeriv ℝ i u x = f.iteratedFDeriv i x := by
  rw [← iteratedFDerivWithin_of_isOpen _ Ω.isOpen x.2,
    ← (hasFTaylorSeriesUpToOn f hu).eq_iteratedFDerivWithin_of_uniqueDiffOn
      (by exact_mod_cast i.is_le) Ω.isOpen.uniqueDiffOn x.2,
    series_of_lt f x i.2, Subtype.val_injective.extend_apply]

/-- An element of `C^{k,α}(Ω)` is determined by its underlying function on `Ω`. -/
theorem toFun_injective :
    Function.Injective (toFun (k := k) (α := α) (Ω := Ω) (F := F)) := by
  intro f g hfg
  have hfield : ∀ i, f.iteratedFDeriv i = g.iteratedFDeriv i := fun i ↦ by
    ext1 x
    rw [← iteratedFDeriv_eq_of_eqOn_toFun f (Subtype.val_injective.extend_apply f.toFun 0),
      ← iteratedFDeriv_eq_of_eqOn_toFun g (u := Function.extend Subtype.val f.toFun 0)
        (fun y ↦ by rw [Subtype.val_injective.extend_apply, hfg])]
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

/-- The recorded derivative fields are the iterated Fréchet derivatives at points of `Ω` of every
function `u` on `E` which agrees with the element on `Ω`. -/
theorem iteratedFDeriv_eq_of_eqOn (f : CkHolderSpaceOn k α Ω F) {u : E → F}
    (hu : ∀ x : Ω, u x = f x) (i : Fin (k + 1)) (x : Ω) :
    _root_.iteratedFDeriv ℝ i u x = f.iteratedFDeriv i x :=
  iteratedFDeriv_eq_of_eqOn_toFun f hu i x

/-- A function on `E` which agrees with an element of `C^{k,α}(Ω)` on `Ω` is `k` times
continuously differentiable on `Ω`. -/
theorem contDiffOn_of_eqOn (f : CkHolderSpaceOn k α Ω F) {u : E → F}
    (hu : ∀ x : Ω, u x = f x) : ContDiffOn ℝ k u Ω :=
  (hasFTaylorSeriesUpToOn f hu).contDiffOn

/-- The derivative field of order zero has the norm of the underlying function at each point. -/
theorem norm_iteratedFDeriv_zero (f : CkHolderSpaceOn k α Ω F) (x : Ω) :
    ‖f.iteratedFDeriv 0 x‖ = ‖f x‖ := by
  rw [← toFun_eq_coe, toFun]
  exact ((continuousMultilinearCurryFin0 ℝ E F).norm_map _).symm

/-- The Hölder field, as a bounded continuous field, is the derivative field of order `k`. -/
@[simp]
theorem toBoundedContinuousFunction_iteratedFDerivHolder (f : CkHolderSpaceOn k α Ω F) :
    f.iteratedFDerivHolder.toBoundedContinuousFunction = f.iteratedFDeriv (Fin.last k) := by
  rw [iteratedFDeriv, fieldL_last, iteratedFDerivHolder]

/-- The Hölder field and the derivative field of order `k` have the same values. -/
@[simp]
theorem coe_iteratedFDerivHolder (f : CkHolderSpaceOn k α Ω F) :
    ⇑f.iteratedFDerivHolder = ⇑(f.iteratedFDeriv (Fin.last k)) := by
  rw [← toBoundedContinuousFunction_iteratedFDerivHolder,
    HolderSpace.coe_toBoundedContinuousFunction]

/-- The derivative field of order `k` is `α`-Hölder on `Ω`. -/
theorem memHolder_iteratedFDeriv_last (f : CkHolderSpaceOn k α Ω F) :
    MemHolder α ⇑(f.iteratedFDeriv (Fin.last k)) := by
  rw [← coe_iteratedFDerivHolder, ← HolderSpace.coe_toBoundedContinuousFunction]
  exact f.iteratedFDerivHolder.memHolder

/-- The `k`-th iterated derivative of a function which agrees with an element of `C^{k,α}(Ω)` on
`Ω` is `α`-Hölder on `Ω`, with constant the Hölder seminorm of the derivative field of order `k`.
-/
theorem holderOnWith_iteratedFDeriv_of_eqOn (f : CkHolderSpaceOn k α Ω F) {u : E → F}
    (hu : ∀ x : Ω, u x = f x) :
    HolderOnWith (nnHolderNorm α ⇑(f.iteratedFDeriv (Fin.last k))) α
      (_root_.iteratedFDeriv ℝ k u) Ω := by
  have e : ∀ z : Ω, _root_.iteratedFDeriv ℝ k u z = f.iteratedFDeriv (Fin.last k) z :=
    iteratedFDeriv_eq_of_eqOn f hu (Fin.last k)
  rw [← HolderWith.restrict_iff]
  intro x y
  rw [Set.domRestrict_apply, Set.domRestrict_apply, e, e]
  exact f.memHolder_iteratedFDeriv_last.holderWith x y

/-- The `C^{k,α}(Ω)` norm is the sum of the supremum norms on `Ω` of the derivative fields through
order `k` and the `α`-Hölder seminorm on `Ω` of the derivative field of order `k`. -/
theorem norm_eq (f : CkHolderSpaceOn k α Ω F) :
    ‖f‖ = ∑ i : Fin (k + 1), ‖f.iteratedFDeriv i‖ +
      nnHolderNorm α ⇑(f.iteratedFDeriv (Fin.last k)) := by
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

/-- The iterated derivatives through order `k` of a function which agrees with an element of
`C^{k,α}(Ω)` on `Ω` are controlled on `Ω` by the `C^{k,α}(Ω)` norm. -/
theorem norm_iteratedFDeriv_apply_le_of_eqOn (f : CkHolderSpaceOn k α Ω F) {u : E → F}
    (hu : ∀ x : Ω, u x = f x) {i : ℕ} (hi : i ≤ k) (x : Ω) :
    ‖_root_.iteratedFDeriv ℝ i u x‖ ≤ ‖f‖ := by
  rw [iteratedFDeriv_eq_of_eqOn f hu ⟨i, Nat.lt_succ_of_le hi⟩]
  exact ((f.iteratedFDeriv _).norm_coe_le_norm x).trans (norm_iteratedFDeriv_le f _)

/-- The extension by zero of an element of `C^{k,α}(Ω)` to a function on `E`. It agrees with the
element on `Ω`, so it is a representative to which the `_of_eqOn` lemmas apply. -/
def extend (f : CkHolderSpaceOn k α Ω F) : E → F :=
  Function.extend Subtype.val f 0

/-- The extension by zero agrees with the element on `Ω`. -/
@[simp]
theorem extend_apply (f : CkHolderSpaceOn k α Ω F) (x : Ω) : f.extend x = f x :=
  Subtype.val_injective.extend_apply _ _ x

/-- The extension by zero of an element of `C^{k,α}(Ω)` is `k` times continuously differentiable
on `Ω`. -/
theorem contDiffOn_extend (f : CkHolderSpaceOn k α Ω F) : ContDiffOn ℝ k f.extend Ω :=
  f.contDiffOn_of_eqOn f.extend_apply

/-- The iterated derivatives of the extension by zero at points of `Ω` are the derivative fields. -/
theorem iteratedFDeriv_extend (f : CkHolderSpaceOn k α Ω F) (i : Fin (k + 1)) (x : Ω) :
    _root_.iteratedFDeriv ℝ i f.extend x = f.iteratedFDeriv i x :=
  f.iteratedFDeriv_eq_of_eqOn f.extend_apply i x

/-- The `k`-th iterated derivative of the extension by zero is `α`-Hölder on `Ω`, with constant the
Hölder seminorm of the derivative field of order `k`. -/
theorem holderOnWith_iteratedFDeriv_extend (f : CkHolderSpaceOn k α Ω F) :
    HolderOnWith (nnHolderNorm α ⇑(f.iteratedFDeriv (Fin.last k))) α
      (_root_.iteratedFDeriv ℝ k f.extend) Ω :=
  f.holderOnWith_iteratedFDeriv_of_eqOn f.extend_apply

/-- The iterated derivatives through order `k` of the extension by zero are controlled on `Ω` by
the `C^{k,α}(Ω)` norm. -/
theorem norm_iteratedFDeriv_extend_le (f : CkHolderSpaceOn k α Ω F) {i : ℕ} (hi : i ≤ k)
    (x : Ω) : ‖_root_.iteratedFDeriv ℝ i f.extend x‖ ≤ ‖f‖ :=
  f.norm_iteratedFDeriv_apply_le_of_eqOn f.extend_apply hi x

/-- The values of an element of `C^{k,α}(Ω)` are controlled by its norm. -/
theorem norm_apply_le (f : CkHolderSpaceOn k α Ω F) (x : Ω) : ‖f x‖ ≤ ‖f‖ := by
  simpa using f.norm_iteratedFDeriv_extend_le k.zero_le x

/-- The underlying function on `Ω` of an element of `C^{k,α}(Ω)` is continuous. -/
theorem continuous (f : CkHolderSpaceOn k α Ω F) : Continuous f := by
  have h := continuousOn_iff_continuous_domRestrict.1 f.contDiffOn_extend.continuousOn
  convert h using 1
  funext x
  exact (f.extend_apply x).symm

/-- The `α`-Hölder seminorm on `Ω` of the derivative field of order `k` is controlled by the
`C^{k,α}(Ω)` norm. -/
theorem nnHolderNorm_iteratedFDeriv_le (f : CkHolderSpaceOn k α Ω F) :
    (nnHolderNorm α ⇑(f.iteratedFDeriv (Fin.last k)) : ℝ) ≤ ‖f‖ := by
  rw [norm_eq]
  exact le_add_of_nonneg_left (Finset.sum_nonneg fun j _ ↦ norm_nonneg _)

/-- The `C^{k,α}(Ω)` norm is at most `(k + 1) M + K` when every derivative field through order `k`
is bounded by `M` and the derivative field of order `k` is `α`-Hölder with constant `K`. -/
theorem norm_le_of_norm_iteratedFDeriv_le_of_holderWith {f : CkHolderSpaceOn k α Ω F} {M : ℝ}
    {K : ℝ≥0} (hM0 : 0 ≤ M) (hM : ∀ i x, ‖f.iteratedFDeriv i x‖ ≤ M)
    (hK : HolderWith K α ⇑(f.iteratedFDeriv (Fin.last k))) : ‖f‖ ≤ (k + 1) * M + K := by
  rw [norm_eq]
  gcongr
  · calc ∑ i : Fin (k + 1), ‖f.iteratedFDeriv i‖ ≤ ∑ _i : Fin (k + 1), M :=
          Finset.sum_le_sum fun i _ ↦ (BoundedContinuousFunction.norm_le hM0).2 (hM i)
      _ = (k + 1) * M := by simp
  · exact_mod_cast hK.nnholderNorm_le

/-- The values of an element of `C^{k,α}(Ω)` are controlled by the supremum norm of its order-zero
field. -/
theorem norm_apply_le_iteratedFDeriv_zero (f : CkHolderSpaceOn k α Ω F) (x : Ω) :
    ‖f x‖ ≤ ‖f.iteratedFDeriv 0‖ := by
  calc ‖f x‖ = ‖f.iteratedFDeriv 0 x‖ := (norm_iteratedFDeriv_zero f x).symm
    _ ≤ _ := (f.iteratedFDeriv 0).norm_coe_le_norm x

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

/-- The `i`-th derivative field, as a continuous linear map to bounded continuous fields on `Ω`.
It is bounded by the `C^{k,α}(Ω)` norm pointwise, by `CkHolderSpaceOn.norm_iteratedFDeriv_le`. -/
-- No operator-norm bound is stated: outside this file, without the local shortcut instances,
-- instance search for the operator norm on this space of continuous linear maps exceeds the
-- default synthesis limits, so such a statement could only be used here.
def iteratedFDerivL (i : Fin (k + 1)) :
    CkHolderSpaceOn k α Ω F →L[ℝ] (Ω →ᵇ (E [×i]→L[ℝ] F)) :=
  (fieldL i).comp toJetL

/-- The linear map `iteratedFDerivL i` sends an element to its `i`-th derivative field. -/
@[simp]
theorem iteratedFDerivL_apply (i : Fin (k + 1)) (f : CkHolderSpaceOn k α Ω F) :
    iteratedFDerivL i f = f.iteratedFDeriv i := by
  rw [iteratedFDerivL, ContinuousLinearMap.comp_apply, toJetL_apply, iteratedFDeriv]

/-- The `k`-th derivative field, as a continuous linear map to the bounded Hölder space on `Ω`. -/
def iteratedFDerivHolderL : CkHolderSpaceOn k α Ω F →L[ℝ] HolderSpace α Ω (E [×k]→L[ℝ] F) :=
  (WithLp.sndL 1 ℝ _ _).comp toJetL

/-- The linear map `iteratedFDerivHolderL` sends an element to its `k`-th derivative field in the
bounded Hölder space. -/
@[simp]
theorem iteratedFDerivHolderL_apply (f : CkHolderSpaceOn k α Ω F) :
    iteratedFDerivHolderL f = f.iteratedFDerivHolder := by
  rw [iteratedFDerivHolderL, ContinuousLinearMap.comp_apply, toJetL_apply, WithLp.sndL_apply,
    iteratedFDerivHolder, WithLp.ofLp_snd]

/-- The Hölder-space norm of the `k`-th derivative field is controlled by the `C^{k,α}(Ω)` norm. -/
theorem norm_iteratedFDerivHolder_le (f : CkHolderSpaceOn k α Ω F) :
    ‖f.iteratedFDerivHolder‖ ≤ ‖f‖ := by
  rw [← norm_toJet, WithLp.prod_norm_eq_of_L1]
  exact le_add_of_nonneg_left (norm_nonneg _)

/-- The `k`-th derivative map to the bounded Hölder space on `Ω` has operator norm at most one. -/
theorem norm_iteratedFDerivHolderL_le_one :
    ‖iteratedFDerivHolderL (k := k) (α := α) (Ω := Ω) (F := F)‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun f ↦ by
    rw [iteratedFDerivHolderL_apply, one_mul]
    exact norm_iteratedFDerivHolder_le f

/-- Each derivative field of the zero element is zero. -/
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

/-- The `k`-th derivative field of the zero element, in the bounded Hölder space, is zero. -/
@[simp]
theorem iteratedFDerivHolder_zero : (0 : CkHolderSpaceOn k α Ω F).iteratedFDerivHolder = 0 := by
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

/-- Forgetting the derivatives has operator norm at most one. -/
theorem norm_toBoundedContinuousFunctionCLM_le_one :
    ‖toBoundedContinuousFunctionCLM (k := k) (α := α) (Ω := Ω) (F := F)‖ ≤ 1 :=
  LinearMap.mkContinuous_norm_le _ zero_le_one _

/-- The jet of iterated derivatives on `Ω` of a function which is `C^k` on `Ω`, with bounded
derivatives through order `k` on `Ω` and `α`-Hölder `k`-th derivative on `Ω`. -/
private def jetOf (u : E → F) (hu : ContDiffOn ℝ k u Ω)
    (hbdd : ∀ i ≤ k, ∃ C, ∀ x ∈ Ω, ‖_root_.iteratedFDeriv ℝ i u x‖ ≤ C)
    (hholder : ∃ C, HolderOnWith C α (_root_.iteratedFDeriv ℝ k u) Ω) : Jet k α Ω F :=
  WithLp.toLp 1
    (WithLp.toLp 1 fun j : Fin k ↦ .ofNormedAddCommGroup
        (fun x : Ω ↦ _root_.iteratedFDeriv ℝ j u x)
        (ContinuousOn.continuousOn_iteratedFDeriv hu Ω.isOpen
          (by exact_mod_cast j.2.le)).domRestrict
        (hbdd j j.2.le).choose fun x ↦ (hbdd j j.2.le).choose_spec x x.2,
      HolderSpace.ofBoundedContinuousFunction
        (.ofNormedAddCommGroup (fun x : Ω ↦ _root_.iteratedFDeriv ℝ k u x)
          (ContinuousOn.continuousOn_iteratedFDeriv hu Ω.isOpen le_rfl).domRestrict
          (hbdd k le_rfl).choose fun x ↦ (hbdd k le_rfl).choose_spec x x.2)
        (hholder.elim fun _ hC ↦ hC.holderWith.memHolder))

private theorem fieldL_jetOf (u : E → F) (hu : ContDiffOn ℝ k u Ω)
    (hbdd : ∀ i ≤ k, ∃ C, ∀ x ∈ Ω, ‖_root_.iteratedFDeriv ℝ i u x‖ ≤ C)
    (hholder : ∃ C, HolderOnWith C α (_root_.iteratedFDeriv ℝ k u) Ω) (i : Fin (k + 1)) (x : Ω) :
    fieldL i (jetOf u hu hbdd hholder) x = _root_.iteratedFDeriv ℝ i u x := by
  induction i using Fin.lastCases with
  | last =>
    rw [fieldL_last]
    simp only [jetOf, WithLp.ofLp_toLp,
      HolderSpace.toBoundedContinuousFunction_ofBoundedContinuousFunction]
    exact congrFun (BoundedContinuousFunction.coe_ofNormedAddCommGroup ..) x
  | cast j =>
    rw [fieldL_castSucc]
    simp only [jetOf, WithLp.ofLp_toLp, PiLp.toLp_apply]
    exact congrFun (BoundedContinuousFunction.coe_ofNormedAddCommGroup ..) x

private theorem isJetGraph_jetOf (u : E → F) (hu : ContDiffOn ℝ k u Ω)
    (hbdd : ∀ i ≤ k, ∃ C, ∀ x ∈ Ω, ‖_root_.iteratedFDeriv ℝ i u x‖ ≤ C)
    (hholder : ∃ C, HolderOnWith C α (_root_.iteratedFDeriv ℝ k u) Ω) :
    IsJetGraph (jetOf u hu hbdd hholder) := fun j x ↦ by
  have h := ((hu.contDiffAt (Ω.isOpen.mem_nhds x.2)).differentiableAt_iteratedFDeriv
    (m := j) (by exact_mod_cast j.2)).hasFDerivAt
  rw [fderiv_iteratedFDeriv, Function.comp_apply] at h
  rw [fieldL_jetOf]
  exact h.congr_of_eventuallyEq
    (Ω.isOpen.extend_subtypeVal_eventuallyEq 0
      (fun y ↦ (fieldL_jetOf u hu hbdd hholder j.castSucc y).symm) x.2)

/-- Build an element of `C^{k,α}(Ω)` from a function which is `C^k` on `Ω`, whose iterated
derivatives through order `k` are bounded on `Ω`, and whose `k`-th iterated derivative is
`α`-Hölder on `Ω`. -/
def ofContDiffOn (u : E → F) (hu : ContDiffOn ℝ k u Ω)
    (hbdd : ∀ i ≤ k, ∃ C, ∀ x ∈ Ω, ‖_root_.iteratedFDeriv ℝ i u x‖ ≤ C)
    (hholder : ∃ C, HolderOnWith C α (_root_.iteratedFDeriv ℝ k u) Ω) :
    CkHolderSpaceOn k α Ω F :=
  mk (jetOf u hu hbdd hholder) (isJetGraph_jetOf u hu hbdd hholder)

/-- The underlying function of `ofContDiffOn u` is the restriction of `u` to `Ω`. -/
@[simp]
theorem ofContDiffOn_apply (u : E → F) (hu : ContDiffOn ℝ k u Ω)
    (hbdd : ∀ i ≤ k, ∃ C, ∀ x ∈ Ω, ‖_root_.iteratedFDeriv ℝ i u x‖ ≤ C)
    (hholder : ∃ C, HolderOnWith C α (_root_.iteratedFDeriv ℝ k u) Ω) (x : Ω) :
    ofContDiffOn u hu hbdd hholder x = u x := by
  rw [← toFun_eq_coe, toFun, iteratedFDeriv, ofContDiffOn, toJet_mk, fieldL_jetOf,
    iteratedFDeriv_zero_eq_comp]
  simp

/-- The derivative fields of `ofContDiffOn u` are the iterated derivatives of `u` on `Ω`. -/
@[simp]
theorem iteratedFDeriv_ofContDiffOn (u : E → F) (hu : ContDiffOn ℝ k u Ω)
    (hbdd : ∀ i ≤ k, ∃ C, ∀ x ∈ Ω, ‖_root_.iteratedFDeriv ℝ i u x‖ ≤ C)
    (hholder : ∃ C, HolderOnWith C α (_root_.iteratedFDeriv ℝ k u) Ω) (i : Fin (k + 1)) (x : Ω) :
    (ofContDiffOn u hu hbdd hholder).iteratedFDeriv i x = _root_.iteratedFDeriv ℝ i u x := by
  rw [iteratedFDeriv, ofContDiffOn, toJet_mk, fieldL_jetOf]

/-- The derivative identities are closed under uniform convergence of the fields on `Ω`. -/
private theorem isClosed_isJetGraph : IsClosed {J : Jet k α Ω F | IsJetGraph J} := by
  have hset : {J : Jet k α Ω F | IsJetGraph J} =
      ⋂ j : Fin k, (fun J : Jet k α Ω F ↦ (fieldL j.castSucc J, fieldL j.succ J)) ⁻¹'
        {J | ∀ x : Ω, HasFDerivAt (Function.extend Subtype.val (J.1 : Ω → E [×j]→L[ℝ] F) 0)
          (curryLeftL E F j (J.2 x)) x} := by
    ext J
    simp [IsJetGraph]
  rw [hset]
  exact isClosed_iInter fun j ↦
    (isClosed_setOf_hasFDerivAt_extend_comp Ω.isOpen (curryLeftL E F j)
      (curryLeftL E F j).uniformContinuous).preimage
      ((fieldL (k := k) (α := α) (Ω := Ω) (F := F) _).continuous.prodMk
        (fieldL (k := k) (α := α) (Ω := Ω) (F := F) _).continuous)

/-- `C^{k,α}(Ω)` with values in a Banach space is a Banach space. -/
instance instCompleteSpace [CompleteSpace F] : CompleteSpace (CkHolderSpaceOn k α Ω F) := by
  unfold CkHolderSpaceOn
  exact isClosed_isJetGraph.completeSpace_coe

/-! ### Restriction to a smaller open set -/

section Restriction

variable {V : Opens E} (h : V ≤ Ω)

/-- The restriction of an element of `C^{k,α}(Ω)` to a smaller open set. -/
private def restrict (f : CkHolderSpaceOn k α Ω F) : CkHolderSpaceOn k α V F :=
  ofContDiffOn f.extend (f.contDiffOn_extend.mono h)
    (fun _ hi ↦ ⟨‖f‖, fun x hx ↦ f.norm_iteratedFDeriv_extend_le hi ⟨x, h hx⟩⟩)
    ⟨_, f.holderOnWith_iteratedFDeriv_extend.mono h⟩

private theorem restrict_apply (f : CkHolderSpaceOn k α Ω F) (x : V) :
    restrict h f x = f ⟨x.1, h x.2⟩ := by
  rw [restrict, ofContDiffOn_apply]
  exact f.extend_apply ⟨x.1, h x.2⟩

private theorem iteratedFDeriv_restrict (f : CkHolderSpaceOn k α Ω F) (i : Fin (k + 1)) (x : V) :
    (restrict h f).iteratedFDeriv i x = f.iteratedFDeriv i ⟨x.1, h x.2⟩ := by
  rw [restrict, iteratedFDeriv_ofContDiffOn]
  exact f.iteratedFDeriv_extend i ⟨x.1, h x.2⟩

/-- Restriction does not increase the `C^{k,α}` norm: the suprema and the Hölder seminorm are
taken over a smaller set. -/
private theorem norm_restrict_le (f : CkHolderSpaceOn k α Ω F) : ‖restrict h f‖ ≤ ‖f‖ := by
  have hH : HolderWith (nnHolderNorm α ⇑(f.iteratedFDeriv (Fin.last k))) α
      ⇑((restrict h f).iteratedFDeriv (Fin.last k)) := fun x y ↦ by
    rw [iteratedFDeriv_restrict, iteratedFDeriv_restrict]
    exact f.memHolder_iteratedFDeriv_last.holderWith ⟨x.1, h x.2⟩ ⟨y.1, h y.2⟩
  rw [norm_eq, norm_eq]
  gcongr with i
  · refine (BoundedContinuousFunction.norm_le (norm_nonneg _)).2 fun x ↦ ?_
    rw [iteratedFDeriv_restrict]
    exact (f.iteratedFDeriv i).norm_coe_le_norm _
  · exact_mod_cast hH.nnholderNorm_le

/-- Restriction `C^{k,α}(Ω) → C^{k,α}(V)` to a smaller open set `V ⊆ Ω`. -/
def restrictL : CkHolderSpaceOn k α Ω F →L[ℝ] CkHolderSpaceOn k α V F :=
  LinearMap.mkContinuous
    { toFun := restrict h
      map_add' f g := by ext x; simp [restrict_apply]
      map_smul' c f := by ext x; simp [restrict_apply] } 1 fun f ↦ by
        rw [one_mul]
        exact norm_restrict_le h f

/-- The restriction of `f` to `V` takes the values of `f` on `V`. -/
@[simp]
theorem restrictL_apply (f : CkHolderSpaceOn k α Ω F) (x : V) :
    restrictL h f x = f ⟨x.1, h x.2⟩ :=
  restrict_apply h f x

/-- The derivative fields of the restriction are the restrictions of the derivative fields. -/
@[simp]
theorem iteratedFDeriv_restrictL (f : CkHolderSpaceOn k α Ω F) (i : Fin (k + 1)) (x : V) :
    (restrictL h f).iteratedFDeriv i x = f.iteratedFDeriv i ⟨x.1, h x.2⟩ :=
  iteratedFDeriv_restrict h f i x

/-- Restriction to a smaller open set has operator norm at most one. -/
theorem norm_restrictL_le_one : ‖restrictL (k := k) (α := α) (F := F) h‖ ≤ 1 :=
  LinearMap.mkContinuous_norm_le _ zero_le_one _

end Restriction

/-! ### Inclusion between consecutive orders on a convex open set -/

section Inclusion

variable (hΩ : Convex ℝ (Ω : Set E)) (hα : α ≤ 1)

/-- On a convex open set, an element of `C^{k+1,α}(Ω)` is in `C^{k,α}(Ω)`. -/
private def inclusionSucc (f : CkHolderSpaceOn (k + 1) α Ω F) : CkHolderSpaceOn k α Ω F :=
  ofContDiffOn f.extend (f.contDiffOn_extend.of_le (by exact_mod_cast k.le_succ))
    (fun _ hi ↦ ⟨‖f‖, fun x hx ↦ f.norm_iteratedFDeriv_extend_le (hi.trans k.le_succ) ⟨x, hx⟩⟩)
    ⟨_, f.contDiffOn_extend.holderOnWith_iteratedFDeriv_of_lt Ω.isOpen hΩ
      k.lt_succ_self hα (M := ‖f‖₊) (L := ‖f‖₊)
      (fun x hx ↦ f.norm_iteratedFDeriv_extend_le k.le_succ ⟨x, hx⟩)
      (fun x hx ↦ f.norm_iteratedFDeriv_extend_le le_rfl ⟨x, hx⟩)⟩

private theorem inclusionSucc_apply (f : CkHolderSpaceOn (k + 1) α Ω F) (x : Ω) :
    inclusionSucc hΩ hα f x = f x := by
  rw [inclusionSucc, ofContDiffOn_apply]
  exact f.extend_apply x

private theorem iteratedFDeriv_inclusionSucc (f : CkHolderSpaceOn (k + 1) α Ω F)
    (i : Fin (k + 1)) (x : Ω) :
    (inclusionSucc hΩ hα f).iteratedFDeriv i x = f.iteratedFDeriv i.castSucc x := by
  rw [inclusionSucc, iteratedFDeriv_ofContDiffOn]
  exact f.iteratedFDeriv_extend i.castSucc x

/-- The inclusion multiplies the norm by at most `3`: the new top seminorm `[D^k f]_{α, Ω}` is at
most `sup ‖D^{k+1} f‖ + 2 sup ‖D^k f‖` by the mean value inequality. -/
private theorem norm_inclusionSucc_le (f : CkHolderSpaceOn (k + 1) α Ω F) :
    ‖inclusionSucc hΩ hα f‖ ≤ 3 * ‖f‖ := by
  have eM : ∀ x (hx : x ∈ Ω), _root_.iteratedFDeriv ℝ k f.extend x =
      f.iteratedFDeriv (Fin.last k).castSucc ⟨x, hx⟩ := fun x hx ↦
    f.iteratedFDeriv_extend (Fin.last k).castSucc ⟨x, hx⟩
  have eL : ∀ x (hx : x ∈ Ω), _root_.iteratedFDeriv ℝ (k + 1) f.extend x =
      f.iteratedFDeriv (Fin.last (k + 1)) ⟨x, hx⟩ := fun x hx ↦
    f.iteratedFDeriv_extend (Fin.last (k + 1)) ⟨x, hx⟩
  -- The Hölder seminorm of the new top field, by the mean value inequality on the convex set.
  have hH : HolderWith (‖f.iteratedFDeriv (Fin.last (k + 1))‖₊ +
      2 * ‖f.iteratedFDeriv (Fin.last k).castSucc‖₊) α
      ⇑((inclusionSucc hΩ hα f).iteratedFDeriv (Fin.last k)) := by
    have h := f.contDiffOn_extend.holderOnWith_iteratedFDeriv_of_lt
      Ω.isOpen hΩ k.lt_succ_self hα (M := ‖f.iteratedFDeriv (Fin.last k).castSucc‖₊)
      (L := ‖f.iteratedFDeriv (Fin.last (k + 1))‖₊)
      (fun x hx ↦ by rw [eM x hx, coe_nnNorm]; exact (f.iteratedFDeriv _).norm_coe_le_norm _)
      (fun x hx ↦ by rw [eL x hx, coe_nnNorm]; exact (f.iteratedFDeriv _).norm_coe_le_norm _)
    rw [← HolderWith.restrict_iff] at h
    intro x y
    rw [iteratedFDeriv_inclusionSucc, iteratedFDeriv_inclusionSucc, ← eM x x.2, ← eM y y.2]
    exact h x y
  -- The supremum norms of the fields through order `k`, together with that of the field of
  -- order `k + 1`, are part of the norm of `f`.
  have hsum : ∑ i : Fin (k + 1), ‖(inclusionSucc hΩ hα f).iteratedFDeriv i‖ +
      ‖f.iteratedFDeriv (Fin.last (k + 1))‖ ≤ ‖f‖ := by
    calc ∑ i : Fin (k + 1), ‖(inclusionSucc hΩ hα f).iteratedFDeriv i‖ +
          ‖f.iteratedFDeriv (Fin.last (k + 1))‖
        ≤ ∑ i : Fin (k + 2), ‖f.iteratedFDeriv i‖ := by
          rw [Fin.sum_univ_castSucc (n := k + 1)]
          gcongr with i
          refine (BoundedContinuousFunction.norm_le (norm_nonneg _)).2 fun x ↦ ?_
          rw [iteratedFDeriv_inclusionSucc]
          exact (f.iteratedFDeriv _).norm_coe_le_norm _
      _ ≤ ‖f‖ := by
          rw [norm_eq f]
          exact le_add_of_nonneg_right (NNReal.coe_nonneg _)
  have hM := norm_iteratedFDeriv_le f (Fin.last k).castSucc
  have hholder : (nnHolderNorm α ⇑((inclusionSucc hΩ hα f).iteratedFDeriv (Fin.last k)) : ℝ) ≤
      ‖f.iteratedFDeriv (Fin.last (k + 1))‖ + 2 * ‖f.iteratedFDeriv (Fin.last k).castSucc‖ := by
    exact_mod_cast hH.nnholderNorm_le
  rw [norm_eq]
  linarith

/-- On a convex open set and for `α ≤ 1`, the inclusion `C^{k+1,α}(Ω) → C^{k,α}(Ω)`. Its operator
norm is at most `3`: the Hölder seminorm of `D^k f` on `Ω` is bounded by the supremum norms of
`D^k f` and `D^{k+1} f` through the mean value inequality, which needs the convexity of `Ω`. -/
def inclusionSuccL : CkHolderSpaceOn (k + 1) α Ω F →L[ℝ] CkHolderSpaceOn k α Ω F :=
  LinearMap.mkContinuous
    { toFun := inclusionSucc hΩ hα
      map_add' f g := by ext x; simp [inclusionSucc_apply]
      map_smul' c f := by ext x; simp [inclusionSucc_apply] } 3 (norm_inclusionSucc_le hΩ hα)

/-- The inclusion preserves the underlying function. -/
@[simp]
theorem inclusionSuccL_apply (f : CkHolderSpaceOn (k + 1) α Ω F) (x : Ω) :
    inclusionSuccL hΩ hα f x = f x :=
  inclusionSucc_apply hΩ hα f x

/-- The inclusion keeps the derivative fields through order `k`. -/
@[simp]
theorem iteratedFDeriv_inclusionSuccL (f : CkHolderSpaceOn (k + 1) α Ω F) (i : Fin (k + 1))
    (x : Ω) : (inclusionSuccL hΩ hα f).iteratedFDeriv i x = f.iteratedFDeriv i.castSucc x :=
  iteratedFDeriv_inclusionSucc hΩ hα f i x

/-- The inclusion `C^{k+1,α}(Ω) → C^{k,α}(Ω)` on a convex open set has operator norm at most `3`. -/
theorem norm_inclusionSuccL_le : ‖inclusionSuccL (k := k) (F := F) hΩ hα‖ ≤ 3 :=
  LinearMap.mkContinuous_norm_le _ (by norm_num) _

end Inclusion

attribute [irreducible] instNormedAddCommGroup instNormedSpace _root_.TauCeti.CkHolderSpaceOn

end CkHolderSpaceOn

end TauCeti

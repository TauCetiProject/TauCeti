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
import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
import TauCeti.Analysis.Calculus.UniformLimitsDeriv

/-!
# Hölder spaces `C^{k,α}(Ω)` on an open set

For an open set `Ω` of a real normed space `E`, this file constructs the Banach space
`C^{k,α}(Ω, F)` of maps `Ω → F` that are `k` times continuously differentiable, whose iterated
Fréchet derivatives through order `k` are bounded on `Ω`, and whose `k`-th iterated derivative
has finite `α`-Hölder seminorm over all of `Ω`. Its norm is

`‖f‖ = ∑_{i ≤ k} sup_{x ∈ Ω} ‖D^i f(x)‖ + [D^k f]_{α, Ω}`,

with the suprema taken in the operator norm of continuous multilinear maps. These are the spaces
of global Hölder estimates on a domain, as opposed to the whole-space spaces
`TauCeti.CkHolderSpace`. The Hölder seminorm compares values at any two points of `Ω`, not only
nearby ones, so on a disconnected set it sees across the gaps between components.

An element is represented, as for `TauCeti.CkHolderSpace`, by its family of iterated derivative
fields on `Ω`: bounded continuous fields `Ω →ᵇ (E [×i]→L[ℝ] F)` for `i < k` and a bounded Hölder
field of order `k`, subject to the condition that, at every point of `Ω`, the extension by zero
of each field has the next field, curried on the left, as its Fréchet derivative. Since `Ω` is
open this is a condition on `Ω` only, and it is closed under uniform convergence, which gives
completeness. The map itself is read off the order-zero field, and its extension by zero,
`TauCeti.CkHolderSpaceOn.extend`, is the ambient representative to which Mathlib's calculus
applies.

## Main declarations

* `TauCeti.CkHolderSpaceOn k α Ω F`: the space `C^{k,α}(Ω, F)`.
* `TauCeti.CkHolderSpaceOn.extend`: the extension by zero of an element to `E`;
  `TauCeti.CkHolderSpaceOn.contDiffOn` and `TauCeti.CkHolderSpaceOn.iteratedFDeriv_extend_apply`
  identify its derivatives on `Ω` with the recorded fields.
* `TauCeti.CkHolderSpaceOn.norm_eq`: the norm is the sum of the supremum norms over `Ω` of the
  derivatives through order `k` and the `α`-Hölder seminorm over `Ω` of the `k`-th derivative.
* `TauCeti.CkHolderSpaceOn.ofContDiffOn`: the converse constructor from a `C^k` map on `Ω` with
  bounded derivatives and `α`-Hölder `k`-th derivative, with the norm bound
  `TauCeti.CkHolderSpaceOn.norm_ofContDiffOn_le`.
* `TauCeti.CkHolderSpaceOn.instCompleteSpace`: completeness when the codomain is complete.
* `TauCeti.CkHolderSpaceOn.restrictL`: restriction to a smaller open set, a continuous linear map
  of operator norm at most one.

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

/-- Shortcut instance for bounded continuous fields of `n`-multilinear maps on `Ω`. Without it,
instance search for the module structure of `ℓ¹` products of these fields indexed by the order
`n` exceeds the default synthesis depth. It is local so that the instance path for these fields
is unchanged outside this file, and no public statement below mentions it. -/
local instance CkHolderSpaceOn.instNormedAddCommGroupBoundedContinuousFunction (n : ℕ) :
    NormedAddCommGroup (Ω →ᵇ (E [×n]→L[ℝ] F)) :=
  inferInstance

/-- Shortcut instance for bounded continuous fields of `n`-multilinear maps on `Ω`, needed for
the module structure of the jet space. It is local for the same reason. -/
local instance CkHolderSpaceOn.instNormedSpaceBoundedContinuousFunction (n : ℕ) :
    NormedSpace ℝ (Ω →ᵇ (E [×n]→L[ℝ] F)) :=
  inferInstance

/-- The space `C^{k,α}(Ω, F)` of maps on the open set `Ω` that are `k` times continuously
differentiable, whose iterated Fréchet derivatives through order `k` are bounded on `Ω`, and
whose `k`-th iterated derivative is `α`-Hölder on `Ω`. Its norm is

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
        HasFDerivAt (Function.extend Subtype.val (field j.castSucc J) 0 : E → E [×j]→L[ℝ] F)
          (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (j + 1) ↦ E) F
            (field j.succ J x)) x}
      zero_mem' := fun j x ↦ by
        simp only [map_zero, FunLike.coe_zero, Function.extend_zero]
        exact hasFDerivAt_const (x := (x : E)) (c := (0 : E [×j]→L[ℝ] F))
      add_mem' := fun {J K} hJ hK j x ↦ by
        simp only [Set.mem_ofPred_eq, map_add, FunLike.coe_add,
          Pi.add_apply] at hJ hK ⊢
        rw [← add_zero (0 : E → E [×j]→L[ℝ] F), Function.extend_add]
        exact (hJ j x).add (hK j x)
      smul_mem' := fun c {J} hJ j x ↦ by
        simp only [Set.mem_ofPred_eq, map_smul, FunLike.coe_smul,
          Pi.smul_apply] at hJ ⊢
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

/-- The derivative identities of a jet: at every point of `Ω`, the extension by zero of each field
below order `k` has the next field, curried on the left, as its Fréchet derivative. -/
private def IsJetGraph (J : Jet k α Ω F) : Prop :=
  ∀ (j : Fin k) (x : Ω),
    HasFDerivAt (Function.extend Subtype.val (fieldL j.castSucc J) 0 : E → E [×j]→L[ℝ] F)
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
    HasFDerivAt (Function.extend Subtype.val (fieldL j.castSucc (toJet f)) 0 :
        E → E [×j]→L[ℝ] F)
      (curryLeftL E F j (fieldL j.succ (toJet f) x)) x :=
  (equivSubtype f).2 j x

instance instNormedAddCommGroup : NormedAddCommGroup (CkHolderSpaceOn k α Ω F) := by
  unfold CkHolderSpaceOn
  infer_instance

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

private theorem toJetL_apply (f : CkHolderSpaceOn k α Ω F) : toJetL f = toJet f :=
  rfl

/-- The bounded continuous `i`-th derivative field on `Ω` of an element of `C^{k,α}(Ω)`, for
`i ≤ k`. It agrees with Mathlib's `iteratedFDeriv` of the extension by zero by
`CkHolderSpaceOn.iteratedFDeriv_extend_apply`. -/
def iteratedFDeriv (f : CkHolderSpaceOn k α Ω F) (i : Fin (k + 1)) : Ω →ᵇ (E [×i]→L[ℝ] F) :=
  fieldL i (toJet f)

/-- The `k`-th derivative field of an element of `C^{k,α}(Ω)`, as an element of the bounded
Hölder space on `Ω`. -/
def iteratedFDerivHolder (f : CkHolderSpaceOn k α Ω F) : HolderSpace α Ω (E [×k]→L[ℝ] F) :=
  (toJet f).ofLp.2

/-- The underlying map on `Ω`: the order-zero derivative field, evaluated on the empty tuple. Use
the coercion `⇑f` instead. -/
def toFun (f : CkHolderSpaceOn k α Ω F) (x : Ω) : F :=
  (f.iteratedFDeriv ⟨0, k.succ_pos⟩ x).curry0

/-- The formal Taylor series recorded by an element, extended by zero off `Ω` and truncated
after order `k`. -/
private def series (f : CkHolderSpaceOn k α Ω F) (x : E) : FormalMultilinearSeries ℝ E F :=
  fun m ↦ if h : m < k + 1 then Function.extend Subtype.val (f.iteratedFDeriv ⟨m, h⟩) 0 x else 0

private theorem series_eq_extend (f : CkHolderSpaceOn k α Ω F) {m : ℕ} (h : m < k + 1) :
    (fun x ↦ series f x m) = Function.extend Subtype.val (f.iteratedFDeriv ⟨m, h⟩) 0 :=
  funext fun x ↦ by simp [series, h]

private theorem series_of_lt (f : CkHolderSpaceOn k α Ω F) (x : Ω) {m : ℕ} (h : m < k + 1) :
    series f x m = f.iteratedFDeriv ⟨m, h⟩ x := by
  rw [← Subtype.val_injective.extend_apply (f.iteratedFDeriv ⟨m, h⟩) 0 x]
  exact congrFun (series_eq_extend f h) x

/-- On `Ω`, the recorded derivative fields form a Taylor series up to order `k` for the extension
by zero of the underlying map. -/
private theorem hasFTaylorSeriesUpToOn (f : CkHolderSpaceOn k α Ω F) :
    HasFTaylorSeriesUpToOn k (Function.extend Subtype.val f.toFun 0) (series f) Ω where
  zero_eq x hx := by
    rw [series_of_lt f ⟨x, hx⟩ k.succ_pos]
    exact (Subtype.val_injective.extend_apply f.toFun 0 ⟨x, hx⟩).symm
  fderivWithin m hm x hx := by
    have hmk : m < k := by exact_mod_cast hm
    rw [series_eq_extend f (by omega : m < k + 1), series_of_lt f ⟨x, hx⟩ (by omega),
      ← curryLeftL_apply]
    exact (hasFDerivAt_fieldL f ⟨m, hmk⟩ ⟨x, hx⟩).hasFDerivWithinAt
  cont m hm := by
    have hmk : m < k + 1 := by
      have : m ≤ k := by exact_mod_cast hm
      omega
    rw [series_eq_extend f hmk, continuousOn_iff_continuous_domRestrict]
    convert (f.iteratedFDeriv ⟨m, hmk⟩).continuous using 1
    funext x
    exact Subtype.val_injective.extend_apply _ _ x

private theorem iteratedFDeriv_extend_toFun (f : CkHolderSpaceOn k α Ω F) (i : Fin (k + 1))
    (x : Ω) :
    _root_.iteratedFDeriv ℝ i (Function.extend Subtype.val f.toFun 0) x =
      f.iteratedFDeriv i x := by
  rw [← iteratedFDerivWithin_of_isOpen _ Ω.isOpen x.2,
    ← (hasFTaylorSeriesUpToOn f).eq_iteratedFDerivWithin_of_uniqueDiffOn
      (by exact_mod_cast i.is_le) Ω.isOpen.uniqueDiffOn x.2, series_of_lt f x i.2]

/-- An element of `C^{k,α}(Ω)` is determined by its values on `Ω`. -/
theorem toFun_injective :
    Function.Injective (toFun (k := k) (α := α) (Ω := Ω) (F := F)) := by
  intro f g hfg
  have hfield : ∀ i, f.iteratedFDeriv i = g.iteratedFDeriv i := fun i ↦ by
    ext1 x
    rw [← iteratedFDeriv_extend_toFun, ← iteratedFDeriv_extend_toFun, hfg]
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

instance instFunLike : FunLike (CkHolderSpaceOn k α Ω F) Ω F where
  coe := toFun
  coe_injective := toFun_injective

@[simp]
theorem toFun_eq_coe (f : CkHolderSpaceOn k α Ω F) : f.toFun = ⇑f :=
  (rfl)

/-- Two elements of `C^{k,α}(Ω)` are equal when they agree at every point of `Ω`. -/
@[ext]
theorem ext {f g : CkHolderSpaceOn k α Ω F} (h : ∀ x, f x = g x) : f = g :=
  DFunLike.ext f g h

/-- The extension by zero of an element of `C^{k,α}(Ω)` to the ambient space. It is the ambient
representative to which Mathlib's calculus is applied; its values off `Ω` play no role. -/
def extend (f : CkHolderSpaceOn k α Ω F) : E → F :=
  Function.extend Subtype.val f 0

@[simp]
theorem extend_apply (f : CkHolderSpaceOn k α Ω F) (x : Ω) : f.extend x = f x :=
  Subtype.val_injective.extend_apply _ _ x

@[simp]
theorem extend_apply_of_notMem (f : CkHolderSpaceOn k α Ω F) {x : E} (hx : x ∉ Ω) :
    f.extend x = 0 :=
  Function.extend_apply' _ _ _ fun ⟨y, hy⟩ ↦ hx (hy ▸ y.2)

/-- The recorded derivative fields are the iterated Fréchet derivatives of the extension by
zero, at points of `Ω`. -/
theorem iteratedFDeriv_extend_apply (f : CkHolderSpaceOn k α Ω F) (i : Fin (k + 1)) (x : Ω) :
    _root_.iteratedFDeriv ℝ i f.extend x = f.iteratedFDeriv i x :=
  iteratedFDeriv_extend_toFun f i x

/-- The `i`-th derivative field is Mathlib's `iteratedFDeriv` of the extension by zero, restricted
to `Ω`. -/
@[simp]
theorem coe_iteratedFDeriv (f : CkHolderSpaceOn k α Ω F) (i : Fin (k + 1)) :
    ⇑(f.iteratedFDeriv i) = fun x : Ω ↦ _root_.iteratedFDeriv ℝ i f.extend x :=
  funext fun x ↦ (iteratedFDeriv_extend_apply f i x).symm

/-- The extension by zero of an element of `C^{k,α}(Ω)` is `k` times continuously differentiable
on `Ω`. -/
theorem contDiffOn (f : CkHolderSpaceOn k α Ω F) : ContDiffOn ℝ k f.extend Ω :=
  (hasFTaylorSeriesUpToOn f).contDiffOn

/-- The Hölder field, as a bounded continuous field, is the derivative field of order `k`. -/
@[simp]
theorem toBoundedContinuousFunction_iteratedFDerivHolder (f : CkHolderSpaceOn k α Ω F) :
    f.iteratedFDerivHolder.toBoundedContinuousFunction = f.iteratedFDeriv (Fin.last k) := by
  rw [iteratedFDeriv, fieldL_last, iteratedFDerivHolder]

/-- The Hölder field records the `k`-th iterated Fréchet derivative of the extension by zero. -/
theorem iteratedFDerivHolder_apply (f : CkHolderSpaceOn k α Ω F) (x : Ω) :
    f.iteratedFDerivHolder x = _root_.iteratedFDeriv ℝ k f.extend x := by
  rw [← HolderSpace.toBoundedContinuousFunction_apply,
    toBoundedContinuousFunction_iteratedFDerivHolder]
  exact (iteratedFDeriv_extend_apply f (Fin.last k) x).symm

@[simp]
theorem coe_iteratedFDerivHolder (f : CkHolderSpaceOn k α Ω F) :
    (f.iteratedFDerivHolder : Ω → E [×k]→L[ℝ] F) =
      fun x : Ω ↦ _root_.iteratedFDeriv ℝ k f.extend x :=
  funext (iteratedFDerivHolder_apply f)

/-- The `k`-th iterated Fréchet derivative of an element of `C^{k,α}(Ω)` is `α`-Hölder on `Ω`. -/
theorem memHolder_iteratedFDeriv (f : CkHolderSpaceOn k α Ω F) :
    MemHolder α fun x : Ω ↦ _root_.iteratedFDeriv ℝ k f.extend x := by
  rw [← coe_iteratedFDerivHolder, ← HolderSpace.coe_toBoundedContinuousFunction]
  exact f.iteratedFDerivHolder.memHolder

/-- The `k`-th iterated Fréchet derivative is `α`-Hölder on `Ω`, with its Hölder seminorm over `Ω`
as constant. -/
theorem holderOnWith_iteratedFDeriv (f : CkHolderSpaceOn k α Ω F) :
    HolderOnWith (nnHolderNorm α fun x : Ω ↦ _root_.iteratedFDeriv ℝ k f.extend x) α
      (_root_.iteratedFDeriv ℝ k f.extend) Ω :=
  HolderWith.restrict_iff.mp f.memHolder_iteratedFDeriv.holderWith

/-- The `C^{k,α}(Ω)` norm is the sum of the supremum norms over `Ω` of the iterated derivatives
through order `k` and the `α`-Hölder seminorm over `Ω` of the `k`-th iterated derivative. -/
theorem norm_eq (f : CkHolderSpaceOn k α Ω F) :
    ‖f‖ = ∑ i : Fin (k + 1), ‖f.iteratedFDeriv i‖ +
      nnHolderNorm α (fun x : Ω ↦ _root_.iteratedFDeriv ℝ k f.extend x) := by
  rw [← norm_toJet, WithLp.prod_norm_eq_of_L1, PiLp.norm_eq_of_L1, Fin.sum_univ_castSucc,
    HolderSpace.norm_def, ← coe_iteratedFDerivHolder,
    ← HolderSpace.coe_toBoundedContinuousFunction, add_assoc]
  simp only [iteratedFDeriv, fieldL_castSucc, fieldL_last, iteratedFDerivHolder,
    WithLp.ofLp_fst, WithLp.ofLp_snd]

/-- The supremum norm of each iterated derivative field is controlled by the `C^{k,α}(Ω)`
norm. -/
theorem norm_iteratedFDeriv_le (f : CkHolderSpaceOn k α Ω F) (i : Fin (k + 1)) :
    ‖f.iteratedFDeriv i‖ ≤ ‖f‖ := by
  rw [norm_eq]
  exact (Finset.single_le_sum (fun j _ ↦ norm_nonneg (f.iteratedFDeriv j))
    (Finset.mem_univ i)).trans (le_add_of_nonneg_right (NNReal.coe_nonneg _))

/-- Each iterated derivative through order `k` is controlled at every point of `Ω` by the
`C^{k,α}(Ω)` norm. -/
theorem norm_iteratedFDeriv_extend_apply_le (f : CkHolderSpaceOn k α Ω F) {i : ℕ} (hi : i ≤ k)
    (x : Ω) : ‖_root_.iteratedFDeriv ℝ i f.extend x‖ ≤ ‖f‖ := by
  rw [iteratedFDeriv_extend_apply f ⟨i, Nat.lt_succ_of_le hi⟩]
  exact ((f.iteratedFDeriv _).norm_coe_le_norm x).trans (norm_iteratedFDeriv_le f _)

/-- The values of an element of `C^{k,α}(Ω)` are controlled by its norm. -/
theorem norm_apply_le (f : CkHolderSpaceOn k α Ω F) (x : Ω) : ‖f x‖ ≤ ‖f‖ := by
  simpa using norm_iteratedFDeriv_extend_apply_le f (Nat.zero_le k) x

/-- The `α`-Hölder seminorm over `Ω` of the `k`-th iterated derivative is controlled by the
`C^{k,α}(Ω)` norm. -/
theorem nnHolderNorm_iteratedFDeriv_le (f : CkHolderSpaceOn k α Ω F) :
    (nnHolderNorm α (fun x : Ω ↦ _root_.iteratedFDeriv ℝ k f.extend x) : ℝ) ≤ ‖f‖ := by
  rw [norm_eq]
  exact le_add_of_nonneg_left (Finset.sum_nonneg fun j _ ↦ norm_nonneg _)

/-- The `C^{k,α}(Ω)` norm is at most `(k + 1) M + K` when every derivative through order `k` is
bounded by `M ≥ 0` on `Ω` and the `k`-th derivative is `α`-Hölder on `Ω` with constant `K`. -/
theorem norm_le_of_norm_iteratedFDeriv_le_of_holderOnWith {f : CkHolderSpaceOn k α Ω F} {M : ℝ}
    {K : ℝ≥0} (hM0 : 0 ≤ M)
    (hM : ∀ i ≤ k, ∀ x ∈ Ω, ‖_root_.iteratedFDeriv ℝ i f.extend x‖ ≤ M)
    (hK : HolderOnWith K α (_root_.iteratedFDeriv ℝ k f.extend) Ω) :
    ‖f‖ ≤ (k + 1) * M + K := by
  rw [norm_eq]
  gcongr
  · calc ∑ i : Fin (k + 1), ‖f.iteratedFDeriv i‖ ≤ ∑ _i : Fin (k + 1), M :=
          Finset.sum_le_sum fun i _ ↦ (BoundedContinuousFunction.norm_le hM0).2 fun x ↦ by
            rw [← iteratedFDeriv_extend_apply]
            exact hM i (Nat.lt_succ_iff.1 i.2) x x.2
      _ = (k + 1) * M := by simp
  · exact_mod_cast hK.holderWith.nnholderNorm_le

/-- The `i`-th derivative field, as a continuous linear map to bounded continuous fields on
`Ω`. -/
def iteratedFDerivL (i : Fin (k + 1)) :
    CkHolderSpaceOn k α Ω F →L[ℝ] (Ω →ᵇ (E [×i]→L[ℝ] F)) :=
  (fieldL i).comp toJetL

@[simp]
theorem iteratedFDerivL_apply (i : Fin (k + 1)) (f : CkHolderSpaceOn k α Ω F) :
    iteratedFDerivL i f = f.iteratedFDeriv i := by
  rw [iteratedFDerivL, ContinuousLinearMap.comp_apply, toJetL_apply, iteratedFDeriv]

/-- The `k`-th derivative field, as a continuous linear map to the bounded Hölder space on `Ω`. -/
def iteratedFDerivHolderL : CkHolderSpaceOn k α Ω F →L[ℝ] HolderSpace α Ω (E [×k]→L[ℝ] F) :=
  (WithLp.sndL 1 ℝ _ _).comp toJetL

@[simp]
theorem iteratedFDerivHolderL_apply (f : CkHolderSpaceOn k α Ω F) :
    iteratedFDerivHolderL f = f.iteratedFDerivHolder := by
  rw [iteratedFDerivHolderL, ContinuousLinearMap.comp_apply, toJetL_apply, WithLp.sndL_apply,
    iteratedFDerivHolder, WithLp.ofLp_snd]

/-- The Hölder-space norm of the `k`-th derivative field is controlled by the `C^{k,α}(Ω)`
norm. -/
theorem norm_iteratedFDerivHolder_le (f : CkHolderSpaceOn k α Ω F) :
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
    (0 : CkHolderSpaceOn k α Ω F).iteratedFDeriv i = 0 := by
  simpa only [iteratedFDerivL_apply] using
    (iteratedFDerivL (α := α) (Ω := Ω) (F := F) i).map_zero

@[simp]
theorem iteratedFDeriv_add (f g : CkHolderSpaceOn k α Ω F) (i : Fin (k + 1)) :
    (f + g).iteratedFDeriv i = f.iteratedFDeriv i + g.iteratedFDeriv i := by
  simpa only [iteratedFDerivL_apply] using (iteratedFDerivL i).map_add f g

@[simp]
theorem iteratedFDeriv_smul (c : ℝ) (f : CkHolderSpaceOn k α Ω F) (i : Fin (k + 1)) :
    (c • f).iteratedFDeriv i = c • f.iteratedFDeriv i := by
  simpa only [iteratedFDerivL_apply] using (iteratedFDerivL i).map_smul c f

@[simp]
theorem iteratedFDerivHolder_zero : (0 : CkHolderSpaceOn k α Ω F).iteratedFDerivHolder = 0 := by
  simpa only [iteratedFDerivHolderL_apply] using
    (iteratedFDerivHolderL (k := k) (α := α) (Ω := Ω) (F := F)).map_zero

@[simp]
theorem iteratedFDerivHolder_add (f g : CkHolderSpaceOn k α Ω F) :
    (f + g).iteratedFDerivHolder = f.iteratedFDerivHolder + g.iteratedFDerivHolder := by
  simpa only [iteratedFDerivHolderL_apply] using iteratedFDerivHolderL.map_add f g

@[simp]
theorem iteratedFDerivHolder_smul (c : ℝ) (f : CkHolderSpaceOn k α Ω F) :
    (c • f).iteratedFDerivHolder = c • f.iteratedFDerivHolder := by
  simpa only [iteratedFDerivHolderL_apply] using iteratedFDerivHolderL.map_smul c f

@[simp]
theorem coe_zero : ⇑(0 : CkHolderSpaceOn k α Ω F) = 0 := by
  ext x
  simp only [← toFun_eq_coe, toFun, iteratedFDeriv_zero, Pi.zero_apply, FunLike.coe_zero]
  simp

@[simp]
theorem coe_add (f g : CkHolderSpaceOn k α Ω F) : ⇑(f + g) = f + g := by
  ext x
  simp only [← toFun_eq_coe, toFun, iteratedFDeriv_add, Pi.add_apply, _root_.add_apply]
  simp

@[simp]
theorem coe_smul (c : ℝ) (f : CkHolderSpaceOn k α Ω F) : ⇑(c • f) = c • ⇑f := by
  ext x
  simp only [← toFun_eq_coe, toFun, iteratedFDeriv_smul, Pi.smul_apply, _root_.smul_apply]
  simp

@[simp]
theorem extend_zero : (0 : CkHolderSpaceOn k α Ω F).extend = 0 := by
  rw [extend, coe_zero, Function.extend_zero]

@[simp]
theorem extend_add (f g : CkHolderSpaceOn k α Ω F) : (f + g).extend = f.extend + g.extend := by
  rw [extend, extend, extend, coe_add, ← Function.extend_add, add_zero]

@[simp]
theorem extend_smul (c : ℝ) (f : CkHolderSpaceOn k α Ω F) : (c • f).extend = c • f.extend := by
  rw [extend, extend, coe_smul, ← Function.extend_smul, smul_zero]

/-- The restriction to `Ω` of the `i`-th iterated derivative of a map that is `C^k` on `Ω`, as a
bounded continuous field when it is bounded by `M` on `Ω`. -/
private def fieldOf (g : E → F) (hg : ContDiffOn ℝ k g Ω) {M : ℝ}
    (hbdd : ∀ i ≤ k, ∀ x ∈ Ω, ‖_root_.iteratedFDeriv ℝ i g x‖ ≤ M) (i : ℕ) (hi : i ≤ k) :
    Ω →ᵇ (E [×i]→L[ℝ] F) :=
  BoundedContinuousFunction.ofNormedAddCommGroup (fun x : Ω ↦ _root_.iteratedFDeriv ℝ i g x)
    (((hg.continuousOn_iteratedFDerivWithin (by exact_mod_cast hi)
      Ω.isOpen.uniqueDiffOn).congr fun _ hx ↦
        (iteratedFDerivWithin_of_isOpen i Ω.isOpen hx).symm).domRestrict)
    M fun x ↦ hbdd i hi x x.2

private theorem fieldOf_apply (g : E → F) (hg : ContDiffOn ℝ k g Ω) {M : ℝ}
    (hbdd : ∀ i ≤ k, ∀ x ∈ Ω, ‖_root_.iteratedFDeriv ℝ i g x‖ ≤ M) (i : ℕ) (hi : i ≤ k)
    (x : Ω) : fieldOf g hg hbdd i hi x = _root_.iteratedFDeriv ℝ i g x :=
  rfl

private theorem memHolder_fieldOf (g : E → F) (hg : ContDiffOn ℝ k g Ω) {M : ℝ}
    (hbdd : ∀ i ≤ k, ∀ x ∈ Ω, ‖_root_.iteratedFDeriv ℝ i g x‖ ≤ M) {C : ℝ≥0}
    (hholder : HolderOnWith C α (_root_.iteratedFDeriv ℝ k g) Ω) :
    MemHolder α (fieldOf g hg hbdd k le_rfl) := by
  have h : ⇑(fieldOf g hg hbdd k le_rfl) = (Ω : Set E).domRestrict (_root_.iteratedFDeriv ℝ k g) :=
    funext (fieldOf_apply g hg hbdd k le_rfl)
  rw [h]
  exact hholder.holderWith.memHolder

/-- The jet of iterated derivatives on `Ω` of a map that is `C^k` on `Ω`, with derivatives through
order `k` bounded on `Ω` and `k`-th derivative `α`-Hölder on `Ω`. -/
private def jetOf (g : E → F) (hg : ContDiffOn ℝ k g Ω) {M : ℝ}
    (hbdd : ∀ i ≤ k, ∀ x ∈ Ω, ‖_root_.iteratedFDeriv ℝ i g x‖ ≤ M) {C : ℝ≥0}
    (hholder : HolderOnWith C α (_root_.iteratedFDeriv ℝ k g) Ω) : Jet k α Ω F :=
  WithLp.toLp 1
    (WithLp.toLp 1 fun j : Fin k ↦ fieldOf g hg hbdd j j.2.le,
      HolderSpace.ofBoundedContinuousFunction (fieldOf g hg hbdd k le_rfl)
        (memHolder_fieldOf g hg hbdd hholder))

private theorem fieldL_jetOf (g : E → F) (hg : ContDiffOn ℝ k g Ω) {M : ℝ}
    (hbdd : ∀ i ≤ k, ∀ x ∈ Ω, ‖_root_.iteratedFDeriv ℝ i g x‖ ≤ M) {C : ℝ≥0}
    (hholder : HolderOnWith C α (_root_.iteratedFDeriv ℝ k g) Ω) (i : Fin (k + 1)) (x : Ω) :
    fieldL i (jetOf g hg hbdd hholder) x = _root_.iteratedFDeriv ℝ i g x := by
  induction i using Fin.lastCases with
  | last =>
    rw [fieldL_last]
    simp only [jetOf, WithLp.ofLp_toLp,
      HolderSpace.toBoundedContinuousFunction_ofBoundedContinuousFunction]
    exact fieldOf_apply g hg hbdd k le_rfl x
  | cast j =>
    rw [fieldL_castSucc]
    simp only [jetOf, WithLp.ofLp_toLp, PiLp.toLp_apply]
    exact fieldOf_apply g hg hbdd j j.2.le x

private theorem isJetGraph_jetOf (g : E → F) (hg : ContDiffOn ℝ k g Ω) {M : ℝ}
    (hbdd : ∀ i ≤ k, ∀ x ∈ Ω, ‖_root_.iteratedFDeriv ℝ i g x‖ ≤ M) {C : ℝ≥0}
    (hholder : HolderOnWith C α (_root_.iteratedFDeriv ℝ k g) Ω) :
    IsJetGraph (jetOf g hg hbdd hholder) := fun j x ↦ by
  have hfun : (Function.extend Subtype.val (fieldL j.castSucc (jetOf g hg hbdd hholder)) 0 :
      E → E [×j]→L[ℝ] F) =ᶠ[nhds (x : E)] _root_.iteratedFDeriv ℝ j g := by
    filter_upwards [Ω.isOpen.mem_nhds x.2] with y hy
    exact (Subtype.val_injective.extend_apply _ _ ⟨y, hy⟩).trans
      (fieldL_jetOf g hg hbdd hholder j.castSucc ⟨y, hy⟩)
  have h := ((hg.contDiffAt (Ω.isOpen.mem_nhds x.2)).differentiableAt_iteratedFDeriv
    (m := j) (by exact_mod_cast j.2)).hasFDerivAt
  rw [fderiv_iteratedFDeriv, Function.comp_apply] at h
  rw [fieldL_jetOf, curryLeftL_apply]
  exact h.congr_of_eventuallyEq hfun

/-- Build an element of `C^{k,α}(Ω)` from a map that is `C^k` on `Ω`, whose iterated derivatives
through order `k` are bounded by `M` on `Ω` and whose `k`-th iterated derivative is `α`-Hölder on
`Ω` with constant `C`. -/
def ofContDiffOn (g : E → F) (hg : ContDiffOn ℝ k g Ω) {M : ℝ}
    (hbdd : ∀ i ≤ k, ∀ x ∈ Ω, ‖_root_.iteratedFDeriv ℝ i g x‖ ≤ M) {C : ℝ≥0}
    (hholder : HolderOnWith C α (_root_.iteratedFDeriv ℝ k g) Ω) : CkHolderSpaceOn k α Ω F :=
  mk (jetOf g hg hbdd hholder) (isJetGraph_jetOf g hg hbdd hholder)

/-- The derivative fields of `ofContDiffOn g` are the iterated derivatives of `g` on `Ω`. -/
@[simp]
theorem iteratedFDeriv_ofContDiffOn_apply (g : E → F) (hg : ContDiffOn ℝ k g Ω) {M : ℝ}
    (hbdd : ∀ i ≤ k, ∀ x ∈ Ω, ‖_root_.iteratedFDeriv ℝ i g x‖ ≤ M) {C : ℝ≥0}
    (hholder : HolderOnWith C α (_root_.iteratedFDeriv ℝ k g) Ω) (i : Fin (k + 1)) (x : Ω) :
    (ofContDiffOn g hg hbdd hholder).iteratedFDeriv i x = _root_.iteratedFDeriv ℝ i g x := by
  rw [iteratedFDeriv, ofContDiffOn, toJet_mk, fieldL_jetOf]

@[simp]
theorem ofContDiffOn_apply (g : E → F) (hg : ContDiffOn ℝ k g Ω) {M : ℝ}
    (hbdd : ∀ i ≤ k, ∀ x ∈ Ω, ‖_root_.iteratedFDeriv ℝ i g x‖ ≤ M) {C : ℝ≥0}
    (hholder : HolderOnWith C α (_root_.iteratedFDeriv ℝ k g) Ω) (x : Ω) :
    ofContDiffOn g hg hbdd hholder x = g x := by
  rw [← toFun_eq_coe, toFun, iteratedFDeriv_ofContDiffOn_apply]
  simp

/-- On `Ω`, the iterated derivatives of the extension by zero of `ofContDiffOn g` are those
of `g`. -/
theorem iteratedFDeriv_extend_ofContDiffOn (g : E → F) (hg : ContDiffOn ℝ k g Ω) {M : ℝ}
    (hbdd : ∀ i ≤ k, ∀ x ∈ Ω, ‖_root_.iteratedFDeriv ℝ i g x‖ ≤ M) {C : ℝ≥0}
    (hholder : HolderOnWith C α (_root_.iteratedFDeriv ℝ k g) Ω) {i : ℕ} (hi : i ≤ k) {x : E}
    (hx : x ∈ Ω) :
    _root_.iteratedFDeriv ℝ i (ofContDiffOn g hg hbdd hholder).extend x =
      _root_.iteratedFDeriv ℝ i g x :=
  (iteratedFDeriv_extend_apply _ ⟨i, Nat.lt_succ_of_le hi⟩ ⟨x, hx⟩).trans
    (iteratedFDeriv_ofContDiffOn_apply g hg hbdd hholder ⟨i, Nat.lt_succ_of_le hi⟩ ⟨x, hx⟩)

/-- The norm of `ofContDiffOn g` is at most `(k + 1) M + C`. -/
theorem norm_ofContDiffOn_le (g : E → F) (hg : ContDiffOn ℝ k g Ω) {M : ℝ} (hM0 : 0 ≤ M)
    (hbdd : ∀ i ≤ k, ∀ x ∈ Ω, ‖_root_.iteratedFDeriv ℝ i g x‖ ≤ M) {C : ℝ≥0}
    (hholder : HolderOnWith C α (_root_.iteratedFDeriv ℝ k g) Ω) :
    ‖ofContDiffOn g hg hbdd hholder‖ ≤ (k + 1) * M + C :=
  norm_le_of_norm_iteratedFDeriv_le_of_holderOnWith hM0
    (fun i hi x hx ↦ by
      rw [iteratedFDeriv_extend_ofContDiffOn g hg hbdd hholder hi hx]
      exact hbdd i hi x hx)
    fun x hx y hy ↦ by
      rw [iteratedFDeriv_extend_ofContDiffOn g hg hbdd hholder le_rfl hx,
        iteratedFDeriv_extend_ofContDiffOn g hg hbdd hholder le_rfl hy]
      exact hholder x hx y hy

/-- The derivative identities are closed under uniform convergence of the fields. -/
private theorem isClosed_isJetGraph : IsClosed {J : Jet k α Ω F | IsJetGraph J} := by
  have hset : {J : Jet k α Ω F | IsJetGraph J} =
      ⋂ j : Fin k, (fun J : Jet k α Ω F ↦ (fieldL j.castSucc J, fieldL j.succ J)) ⁻¹'
        {J | ∀ x : Ω, HasFDerivAt (Function.extend Subtype.val J.1 0 : E → E [×j]→L[ℝ] F)
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

section restrict

variable {U V : Opens E}

/-- The restriction of an element of `C^{k,α}(Ω)` to a smaller open set `U`. -/
def restrict (h : U ≤ Ω) (f : CkHolderSpaceOn k α Ω F) : CkHolderSpaceOn k α U F :=
  ofContDiffOn f.extend (f.contDiffOn.mono h)
    (fun _ hi x hx ↦ f.norm_iteratedFDeriv_extend_apply_le hi ⟨x, h hx⟩)
    (f.holderOnWith_iteratedFDeriv.mono h)

@[simp]
theorem restrict_apply (h : U ≤ Ω) (f : CkHolderSpaceOn k α Ω F) (x : U) :
    f.restrict h x = f ⟨x, h x.2⟩ := by
  rw [restrict, ofContDiffOn_apply, ← extend_apply]

/-- On the smaller open set, the iterated derivatives of the extension by zero of a restriction
are those of the original extension. -/
theorem iteratedFDeriv_extend_restrict (h : U ≤ Ω) (f : CkHolderSpaceOn k α Ω F) {i : ℕ}
    (hi : i ≤ k) {x : E} (hx : x ∈ U) :
    _root_.iteratedFDeriv ℝ i (f.restrict h).extend x = _root_.iteratedFDeriv ℝ i f.extend x :=
  iteratedFDeriv_extend_ofContDiffOn _ _ _ _ hi hx

/-- The derivative fields of a restriction are the restrictions of the derivative fields. -/
@[simp]
theorem iteratedFDeriv_restrict_apply (h : U ≤ Ω) (f : CkHolderSpaceOn k α Ω F)
    (i : Fin (k + 1)) (x : U) :
    (f.restrict h).iteratedFDeriv i x = f.iteratedFDeriv i ⟨x, h x.2⟩ := by
  rw [restrict, iteratedFDeriv_ofContDiffOn_apply, ← iteratedFDeriv_extend_apply]

/-- Restriction to a smaller open set does not increase the `C^{k,α}` norm. -/
theorem norm_restrict_le (h : U ≤ Ω) (f : CkHolderSpaceOn k α Ω F) :
    ‖f.restrict h‖ ≤ ‖f‖ := by
  have hk : (fun x : U ↦ _root_.iteratedFDeriv ℝ k (f.restrict h).extend x) =
      fun x : U ↦ _root_.iteratedFDeriv ℝ k f.extend x :=
    funext fun x ↦ iteratedFDeriv_extend_restrict h f le_rfl x.2
  rw [norm_eq (f.restrict h), norm_eq f, hk]
  gcongr with i
  · refine (BoundedContinuousFunction.norm_le (norm_nonneg _)).2 fun x ↦ ?_
    rw [iteratedFDeriv_restrict_apply]
    exact (f.iteratedFDeriv i).norm_coe_le_norm _
  · exact_mod_cast (f.holderOnWith_iteratedFDeriv.mono h).holderWith.nnholderNorm_le

/-- Restriction to a smaller open set, as a continuous linear map. -/
def restrictL (h : U ≤ Ω) : CkHolderSpaceOn k α Ω F →L[ℝ] CkHolderSpaceOn k α U F :=
  LinearMap.mkContinuous
    { toFun := restrict h
      map_add' f g := by
        ext x
        simp
      map_smul' c f := by
        ext x
        simp } 1 fun f ↦ by
      rw [one_mul]
      exact norm_restrict_le h f

@[simp]
theorem restrictL_apply (h : U ≤ Ω) (f : CkHolderSpaceOn k α Ω F) :
    restrictL h f = f.restrict h :=
  (rfl)

/-- Restriction to a smaller open set has operator norm at most one. -/
theorem norm_restrictL_le_one (h : U ≤ Ω) :
    ‖restrictL (k := k) (α := α) (F := F) h‖ ≤ 1 :=
  LinearMap.mkContinuous_norm_le _ zero_le_one _

@[simp]
theorem restrict_self (f : CkHolderSpaceOn k α Ω F) : f.restrict le_rfl = f := by
  ext x
  simp

@[simp]
theorem restrict_restrict (hUV : U ≤ V) (hVΩ : V ≤ Ω) (f : CkHolderSpaceOn k α Ω F) :
    (f.restrict hVΩ).restrict hUV = f.restrict (hUV.trans hVΩ) := by
  ext x
  simp

end restrict

attribute [irreducible] instNormedAddCommGroup instNormedSpace _root_.TauCeti.CkHolderSpaceOn

end CkHolderSpaceOn

end TauCeti

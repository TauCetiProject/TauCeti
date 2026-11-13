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
import Mathlib.Analysis.Calculus.ContDiff.Comp
import TauCeti.Analysis.Calculus.IteratedFDeriv.Basic
import TauCeti.Analysis.Calculus.UniformLimitsDeriv
import TauCeti.Analysis.Holder.JetBounds

/-!
# Bounded `C^{k,α}` maps of every order

This file constructs, for every `k : ℕ`, the normed space `C_b^{k,α}(E, F)` of `C^k` maps whose
iterated Fréchet derivatives through order `k` are bounded and whose `k`-th iterated derivative is
globally `α`-Hölder, and proves that it is Banach when the codomain is Banach. Its norm is

`‖f‖ = ∑_{i ≤ k} ‖D^i f‖_∞ + [D^k f]_α`,

where `D^i f = iteratedFDeriv ℝ i f` and the suprema use the operator norm of continuous
multilinear maps. These are the spatial trace spaces of parabolic Schauder theory, and the
targets of Schauder estimates of arbitrary order.

An element is represented by its family of iterated derivative fields: bounded continuous fields
`E →ᵇ (E [×i]→L[ℝ] F)` for `i < k` and a bounded Hölder field of order `k`, subject to the
condition that each field is the Fréchet derivative of the previous one, curried on the left.
This is exactly the condition that the family is a Taylor series up to order `k` for its
order-zero field, so the fields are the iterated derivatives of the underlying function. The
conditions are closed under uniform convergence, which gives completeness.

## Main declarations

* `TauCeti.CkHolderSpace k α E F`: bounded `C^k` maps with bounded derivatives through order `k`
  and globally `α`-Hölder `k`-th derivative.
* `TauCeti.CkHolderSpace.iteratedFDeriv`: the bounded continuous `i`-th derivative field for
  `i ≤ k`; `TauCeti.CkHolderSpace.coe_iteratedFDeriv` identifies it with Mathlib's
  `iteratedFDeriv`.
* `TauCeti.CkHolderSpace.contDiff` and `TauCeti.CkHolderSpace.memHolder_iteratedFDeriv`: the
  regularity of an element; `TauCeti.CkHolderSpace.ofContDiff` is the converse constructor.
* `TauCeti.CkHolderSpace.norm_eq`: the norm is the sum of the supremum norms of the derivatives
  through order `k` and the `α`-Hölder seminorm of the `k`-th derivative.
* `TauCeti.CkHolderSpace.norm_le_of_norm_iteratedFDeriv_le_of_holderWith`: the norm is controlled
  by uniform bounds on the derivatives and a Hölder constant of the `k`-th derivative.
* `TauCeti.CkHolderSpace.toBoundedContinuousFunction` and `TauCeti.CkHolderSpace.fderivBCF`: the
  underlying function and its curried derivative as bounded continuous fields, with the supremum
  norms of the derivative fields of orders zero and one; and
  `TauCeti.CkHolderSpace.toBoundedContinuousFunctionCLM`, the first as a continuous linear map of
  operator norm at most one.
* `TauCeti.CkHolderSpace.norm_fderiv_le_iteratedFDeriv_one`,
  `TauCeti.CkHolderSpace.norm_fderiv_fderiv_le_iteratedFDeriv_two` and
  `TauCeti.CkHolderSpace.holderWith_fderiv_fderiv`: bounds on the curried derivatives `Df` and
  `D(Df)` by the derivative fields, and the Hölder bound on `D(Df)` for `k = 2`.
* `TauCeti.CkHolderSpace.iteratedFDerivL` and `TauCeti.CkHolderSpace.iteratedFDerivHolderL`: the
  derivative fields as continuous linear maps; the second has operator norm at most one.
* `TauCeti.CkHolderSpace.instCompleteSpace`: completeness when the codomain is complete.

## References

D. Gilbarg and N. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
Section 4.1; A. Lunardi, *Analytic Semigroups and Optimal Regularity in Parabolic Problems*,
Chapter 0.
-/

public section

noncomputable section

namespace TauCeti

open scoped NNReal BoundedContinuousFunction

universe u v

variable (k : ℕ) (α : ℝ≥0) (E : Type u) (F : Type v)
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Shortcut instance for bounded continuous fields of `n`-multilinear maps. Without it, instance
search for the module structure of `ℓ¹` products of these fields indexed by the order `n` exceeds
the default synthesis depth. It is local so that the instance path for these fields is unchanged
outside this file, and no public statement below mentions it: only definition bodies and proofs
use it. -/
local instance CkHolderSpace.instNormedAddCommGroupBoundedContinuousFunction (n : ℕ) :
    NormedAddCommGroup (E →ᵇ (E [×n]→L[ℝ] F)) :=
  inferInstance

/-- Shortcut instance for bounded continuous fields of `n`-multilinear maps, needed for operator
norms of continuous linear maps into these fields indexed by the order `n`. It is local for the
same reason. -/
local instance CkHolderSpace.instNormedSpaceBoundedContinuousFunction (n : ℕ) :
    NormedSpace ℝ (E →ᵇ (E [×n]→L[ℝ] F)) :=
  inferInstance

/-- The space of bounded `C^k` maps whose iterated Fréchet derivatives through order `k` are
bounded and whose `k`-th iterated derivative is globally `α`-Hölder. Its norm is

`∑_{i ≤ k} ‖D^i f‖_∞ + [D^k f]_α`.
-/
-- The module system requires exposure while the declarations below construct and project through
-- this graph alias. The final `irreducible` attribute restores the abstraction boundary.
@[expose] def CkHolderSpace : Type _ :=
  let field (i : Fin (k + 1)) :
      WithLp 1 ((PiLp 1 fun i : Fin k ↦ E →ᵇ (E [×i]→L[ℝ] F)) ×
        HolderSpace α E (E [×k]→L[ℝ] F)) →L[ℝ] (E →ᵇ (E [×i]→L[ℝ] F)) :=
    Fin.lastCases (motive := fun i : Fin (k + 1) ↦ WithLp 1
        ((PiLp 1 fun i : Fin k ↦ E →ᵇ (E [×i]→L[ℝ] F)) ×
          HolderSpace α E (E [×k]→L[ℝ] F)) →L[ℝ] (E →ᵇ (E [×i]→L[ℝ] F)))
      (HolderSpace.toBoundedContinuousFunctionCLM.comp (WithLp.sndL 1 ℝ _ _))
      (fun j ↦ (PiLp.proj 1 _ j).comp (WithLp.fstL 1 ℝ _ _)) i
  let graph : Submodule ℝ (WithLp 1 ((PiLp 1 fun i : Fin k ↦ E →ᵇ (E [×i]→L[ℝ] F)) ×
      HolderSpace α E (E [×k]→L[ℝ] F))) :=
    { carrier := {J | ∀ (j : Fin k) (x : E),
        HasFDerivAt (field j.castSucc J : E → E [×j]→L[ℝ] F)
          (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (j + 1) ↦ E) F
            (field j.succ J x)) x}
      zero_mem' := fun j x ↦ by
        simp only [map_zero, FunLike.coe_zero, Pi.zero_apply]
        exact hasFDerivAt_const (x := x) (c := (0 : E [×j]→L[ℝ] F))
      add_mem' := fun {J K} hJ hK j x ↦ by
        simp only [Set.mem_ofPred_eq, map_add, FunLike.coe_add,
          Pi.add_apply] at hJ hK ⊢
        exact (hJ j x).add (hK j x)
      smul_mem' := fun c {J} hJ j x ↦ by
        simp only [Set.mem_ofPred_eq, map_smul, FunLike.coe_smul] at hJ ⊢
        exact (hJ j x).const_smul c }
  graph

namespace CkHolderSpace

variable {k α E F}

variable (k α E F) in
/-- The ambient jet space of bounded `C^{k,α}` maps: bounded continuous derivative fields of
orders below `k`, with the `ℓ¹` norm, together with a bounded Hölder field of order `k`. -/
private abbrev Jet := WithLp 1
  ((PiLp 1 fun i : Fin k ↦ E →ᵇ (E [×i]→L[ℝ] F)) × HolderSpace α E (E [×k]→L[ℝ] F))

/-- The derivative field of order `i ≤ k` of a jet; this is the map `field` in the definition of
`CkHolderSpace`. -/
private def fieldL (i : Fin (k + 1)) : Jet k α E F →L[ℝ] (E →ᵇ (E [×i]→L[ℝ] F)) :=
  Fin.lastCases (motive := fun i : Fin (k + 1) ↦ Jet k α E F →L[ℝ] (E →ᵇ (E [×i]→L[ℝ] F)))
    (HolderSpace.toBoundedContinuousFunctionCLM.comp (WithLp.sndL 1 ℝ _ _))
    (fun j ↦ (PiLp.proj 1 _ j).comp (WithLp.fstL 1 ℝ _ _)) i

private theorem fieldL_castSucc (j : Fin k) (J : Jet k α E F) :
    fieldL j.castSucc J = J.ofLp.1 j :=
  congrArg (· J) (Fin.lastCases_castSucc (motive := fun i : Fin (k + 1) ↦
    Jet k α E F →L[ℝ] (E →ᵇ (E [×i]→L[ℝ] F))) j)

private theorem fieldL_last (J : Jet k α E F) :
    fieldL (Fin.last k) J = J.ofLp.2.toBoundedContinuousFunction :=
  (congrArg (· J) (Fin.lastCases_last (motive := fun i : Fin (k + 1) ↦
    Jet k α E F →L[ℝ] (E →ᵇ (E [×i]→L[ℝ] F)))
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

/-- The derivative identities of a jet: each field below order `k` has the next field, curried on
the left, as its Fréchet derivative. -/
private def IsJetGraph (J : Jet k α E F) : Prop :=
  ∀ (j : Fin k) (x : E), HasFDerivAt (fieldL j.castSucc J : E → E [×j]→L[ℝ] F)
    (curryLeftL E F j (fieldL j.succ J x)) x

/-- Elements are the jets satisfying the derivative identities. This is the identity map: the
carrier of `CkHolderSpace` states the identities through its local `field`, which is `fieldL`, and
through `continuousMultilinearCurryLeftEquiv`, whose underlying continuous linear map is
`curryLeftL`. Besides this map, the carrier is unfolded only by `toJetL`, the two norm instances,
`norm_toJet` and `instCompleteSpace`, which use that it is a submodule of the jet space. -/
private def equivSubtype : CkHolderSpace k α E F ≃ {J : Jet k α E F // IsJetGraph J} :=
  Equiv.refl _

/-- The underlying jet of an element. -/
private def toJet (f : CkHolderSpace k α E F) : Jet k α E F := (equivSubtype f).1

/-- An element from a jet satisfying the derivative identities. -/
private def mk (J : Jet k α E F) (hJ : IsJetGraph J) : CkHolderSpace k α E F :=
  equivSubtype.symm ⟨J, hJ⟩

private theorem toJet_injective : Function.Injective (toJet (k := k) (α := α) (E := E) (F := F)) :=
  fun _ _ h ↦ equivSubtype.injective (Subtype.ext h)

private theorem toJet_mk (J : Jet k α E F) (hJ) : toJet (mk J hJ) = J := by
  rw [toJet, mk, Equiv.apply_symm_apply]

private theorem hasFDerivAt_fieldL (f : CkHolderSpace k α E F) (j : Fin k) (x : E) :
    HasFDerivAt (fieldL j.castSucc (toJet f) : E → E [×j]→L[ℝ] F)
      (curryLeftL E F j (fieldL j.succ (toJet f) x)) x :=
  (equivSubtype f).2 j x

/-- The `C^{k,α}` norm makes the space of bounded `C^{k,α}` maps a normed additive group. -/
instance instNormedAddCommGroup : NormedAddCommGroup (CkHolderSpace k α E F) := by
  unfold CkHolderSpace
  infer_instance

/-- The space of bounded `C^{k,α}` maps is a real normed space. -/
instance instNormedSpace : NormedSpace ℝ (CkHolderSpace k α E F) := by
  unfold CkHolderSpace
  infer_instance

private theorem norm_toJet (f : CkHolderSpace k α E F) : ‖toJet f‖ = ‖f‖ :=
  Submodule.norm_coe f

/-- The underlying jet, as a continuous linear map: the inclusion of the submodule `CkHolderSpace`
into the jet space. -/
private def toJetL : CkHolderSpace k α E F →L[ℝ] Jet k α E F := by
  unfold CkHolderSpace
  exact Submodule.subtypeL _

/-- The inclusion `toJetL` is `toJet`; both are the coercion of the submodule. -/
private theorem toJetL_apply (f : CkHolderSpace k α E F) : toJetL f = toJet f :=
  rfl

/-- The bounded continuous `i`-th derivative field of a bounded `C^{k,α}` map, for `i ≤ k`. It
agrees with Mathlib's `iteratedFDeriv` by `CkHolderSpace.iteratedFDeriv_eq`. -/
def iteratedFDeriv (f : CkHolderSpace k α E F) (i : Fin (k + 1)) : E →ᵇ (E [×i]→L[ℝ] F) :=
  fieldL i (toJet f)

/-- The `k`-th derivative field of a bounded `C^{k,α}` map, as an element of the bounded
Hölder space. -/
def iteratedFDerivHolder (f : CkHolderSpace k α E F) : HolderSpace α E (E [×k]→L[ℝ] F) :=
  (toJet f).ofLp.2

/-- The underlying function of a bounded `C^{k,α}` map: its order-zero derivative field, evaluated
on the empty tuple. Use the coercion `⇑f` instead. -/
def toFun (f : CkHolderSpace k α E F) (x : E) : F :=
  (f.iteratedFDeriv ⟨0, k.succ_pos⟩ x).curry0

/-- The formal Taylor series recorded by an element, truncated after order `k`. -/
private def series (f : CkHolderSpace k α E F) (x : E) : FormalMultilinearSeries ℝ E F :=
  fun m ↦ if h : m < k + 1 then f.iteratedFDeriv ⟨m, h⟩ x else 0

private theorem series_of_lt (f : CkHolderSpace k α E F) (x : E) {m : ℕ} (h : m < k + 1) :
    series f x m = f.iteratedFDeriv ⟨m, h⟩ x := by
  simp [series, h]

/-- The recorded derivative fields form a Taylor series up to order `k` for the underlying
function. -/
private theorem hasFTaylorSeriesUpTo (f : CkHolderSpace k α E F) :
    HasFTaylorSeriesUpTo k f.toFun (series f) where
  zero_eq x := by
    rw [series_of_lt f x k.succ_pos, toFun]
  fderiv m hm x := by
    have hmk : m < k := by exact_mod_cast hm
    have hfun : (fun y ↦ series f y m) = (fieldL (⟨m, hmk⟩ : Fin k).castSucc (toJet f) : _) :=
      funext fun y ↦ series_of_lt f y (by omega)
    rw [hfun, series_of_lt f x (by omega), ← curryLeftL_apply]
    exact hasFDerivAt_fieldL f ⟨m, hmk⟩ x
  cont m hm := by
    have hmk : m < k + 1 := by
      have : m ≤ k := by exact_mod_cast hm
      omega
    have hfun : (fun y ↦ series f y m) = (f.iteratedFDeriv ⟨m, hmk⟩ : _) :=
      funext fun y ↦ series_of_lt f y hmk
    rw [hfun]
    exact (f.iteratedFDeriv ⟨m, hmk⟩).continuous

private theorem iteratedFDeriv_toFun (f : CkHolderSpace k α E F) (i : Fin (k + 1)) (x : E) :
    _root_.iteratedFDeriv ℝ i f.toFun x = f.iteratedFDeriv i x := by
  rw [← (hasFTaylorSeriesUpTo f).eq_iteratedFDeriv (by exact_mod_cast i.is_le) x,
    series_of_lt f x i.2]

/-- A bounded `C^{k,α}` map is determined by its underlying function. -/
theorem toFun_injective : Function.Injective (toFun (k := k) (α := α) (E := E) (F := F)) := by
  intro f g hfg
  have hfield : ∀ i, f.iteratedFDeriv i = g.iteratedFDeriv i := fun i ↦ by
    ext1 x
    rw [← iteratedFDeriv_toFun, ← iteratedFDeriv_toFun, hfg]
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

/-- A bounded `C^{k,α}` map is coerced to its underlying function. -/
instance instFunLike : FunLike (CkHolderSpace k α E F) E F where
  coe := toFun
  coe_injective := toFun_injective

/-- The field `toFun` is the coercion to a function. -/
@[simp]
theorem toFun_eq_coe (f : CkHolderSpace k α E F) : f.toFun = ⇑f :=
  (rfl)

/-- Two bounded `C^{k,α}` maps are equal when their underlying functions agree pointwise. -/
@[ext]
theorem ext {f g : CkHolderSpace k α E F} (h : ∀ x, f x = g x) : f = g :=
  DFunLike.ext f g h

/-- The recorded derivative fields are the iterated Fréchet derivatives of the underlying
function. -/
theorem iteratedFDeriv_eq (f : CkHolderSpace k α E F) (i : Fin (k + 1)) (x : E) :
    _root_.iteratedFDeriv ℝ i f x = f.iteratedFDeriv i x :=
  iteratedFDeriv_toFun f i x

/-- The `i`-th derivative field is Mathlib's `iteratedFDeriv` of the underlying function. -/
@[simp]
theorem coe_iteratedFDeriv (f : CkHolderSpace k α E F) (i : Fin (k + 1)) :
    ⇑(f.iteratedFDeriv i) = _root_.iteratedFDeriv ℝ i f :=
  funext fun x ↦ (iteratedFDeriv_eq f i x).symm

/-- A bounded `C^{k,α}` map is `k` times continuously differentiable. -/
theorem contDiff (f : CkHolderSpace k α E F) : ContDiff ℝ k f :=
  (hasFTaylorSeriesUpTo f).contDiff

/-- The Hölder field, as a bounded continuous field, is the derivative field of order `k`. -/
@[simp]
theorem toBoundedContinuousFunction_iteratedFDerivHolder (f : CkHolderSpace k α E F) :
    f.iteratedFDerivHolder.toBoundedContinuousFunction = f.iteratedFDeriv (Fin.last k) := by
  rw [iteratedFDeriv, fieldL_last, iteratedFDerivHolder]

/-- The Hölder field records the `k`-th iterated Fréchet derivative. -/
theorem iteratedFDerivHolder_apply (f : CkHolderSpace k α E F) (x : E) :
    f.iteratedFDerivHolder x = _root_.iteratedFDeriv ℝ k f x := by
  rw [← HolderSpace.toBoundedContinuousFunction_apply,
    toBoundedContinuousFunction_iteratedFDerivHolder]
  exact (iteratedFDeriv_eq f (Fin.last k) x).symm

/-- The Hölder field is Mathlib's `k`-th `iteratedFDeriv` of the underlying function. -/
@[simp]
theorem coe_iteratedFDerivHolder (f : CkHolderSpace k α E F) :
    (f.iteratedFDerivHolder : E → E [×k]→L[ℝ] F) = _root_.iteratedFDeriv ℝ k f :=
  funext (iteratedFDerivHolder_apply f)

/-- The `k`-th iterated Fréchet derivative of a bounded `C^{k,α}` map is globally `α`-Hölder. -/
theorem memHolder_iteratedFDeriv (f : CkHolderSpace k α E F) :
    MemHolder α (_root_.iteratedFDeriv ℝ k f) := by
  rw [← coe_iteratedFDerivHolder, ← HolderSpace.coe_toBoundedContinuousFunction]
  exact f.iteratedFDerivHolder.memHolder

/-- The `C^{k,α}` norm is the sum of the supremum norms of the iterated derivatives through
order `k` and the `α`-Hölder seminorm of the `k`-th iterated derivative. -/
theorem norm_eq (f : CkHolderSpace k α E F) :
    ‖f‖ = ∑ i : Fin (k + 1), ‖f.iteratedFDeriv i‖ +
      nnHolderNorm α (_root_.iteratedFDeriv ℝ k f) := by
  rw [← norm_toJet, WithLp.prod_norm_eq_of_L1, PiLp.norm_eq_of_L1, Fin.sum_univ_castSucc,
    HolderSpace.norm_def, ← coe_iteratedFDerivHolder, ← HolderSpace.coe_toBoundedContinuousFunction,
    add_assoc]
  simp only [iteratedFDeriv, fieldL_castSucc, fieldL_last, iteratedFDerivHolder,
    WithLp.ofLp_fst, WithLp.ofLp_snd]

/-- The supremum norm of each iterated derivative field is controlled by the `C^{k,α}` norm. -/
theorem norm_iteratedFDeriv_le (f : CkHolderSpace k α E F) (i : Fin (k + 1)) :
    ‖f.iteratedFDeriv i‖ ≤ ‖f‖ := by
  rw [norm_eq]
  exact (Finset.single_le_sum (fun j _ ↦ norm_nonneg (f.iteratedFDeriv j))
    (Finset.mem_univ i)).trans (le_add_of_nonneg_right (NNReal.coe_nonneg _))

/-- Each iterated derivative through order `k` is pointwise controlled by the `C^{k,α}` norm. -/
theorem norm_iteratedFDeriv_apply_le (f : CkHolderSpace k α E F) {i : ℕ} (hi : i ≤ k) (x : E) :
    ‖_root_.iteratedFDeriv ℝ i f x‖ ≤ ‖f‖ := by
  rw [iteratedFDeriv_eq f ⟨i, Nat.lt_succ_of_le hi⟩]
  exact ((f.iteratedFDeriv _).norm_coe_le_norm x).trans (norm_iteratedFDeriv_le f _)

/-- The values of a bounded `C^{k,α}` map are controlled by its `C^{k,α}` norm. -/
theorem norm_apply_le (f : CkHolderSpace k α E F) (x : E) : ‖f x‖ ≤ ‖f‖ := by
  simpa using norm_iteratedFDeriv_apply_le f (Nat.zero_le k) x

/-- The `α`-Hölder seminorm of the `k`-th iterated derivative is controlled by the `C^{k,α}`
norm. -/
theorem nnHolderNorm_iteratedFDeriv_le (f : CkHolderSpace k α E F) :
    (nnHolderNorm α (_root_.iteratedFDeriv ℝ k f) : ℝ) ≤ ‖f‖ := by
  rw [norm_eq]
  exact le_add_of_nonneg_left (Finset.sum_nonneg fun j _ ↦ norm_nonneg _)

/-- Every derivative field through order `k` is globally `α`-Hölder when `α ≤ 1`. Lower
fields are controlled by their supremum norm and the bound on their next derivative. -/
theorem holderWith_iteratedFDeriv_of_le (f : CkHolderSpace k α E F) (hα : α ≤ 1)
    {j : ℕ} (hj : j ≤ k) :
    HolderWith (3 * ‖f‖₊) α (_root_.iteratedFDeriv ℝ j f) := by
  rcases hj.eq_or_lt with rfl | hj
  · exact f.memHolder_iteratedFDeriv.holderWith.mono (by
      exact_mod_cast (f.nnHolderNorm_iteratedFDeriv_le.trans
        (by nlinarith [norm_nonneg f] : ‖f‖ ≤ 3 * ‖f‖)))
  · have h := holderOnWith_univ.mp
      (f.contDiff.contDiffOn.holderOnWith_iteratedFDeriv_of_lt isOpen_univ (convex_univ)
        (M := ‖f‖₊) (L := ‖f‖₊) hj hα (fun x _ ↦ f.norm_iteratedFDeriv_apply_le hj.le x)
        (fun x _ ↦ f.norm_iteratedFDeriv_apply_le hj x))
    convert h using 1; ring

/-- The `C^{k,α}` norm is at most `(k + 1) M + K` when every derivative through order `k` is
bounded by `M` and the `k`-th derivative is `α`-Hölder with constant `K`. -/
theorem norm_le_of_norm_iteratedFDeriv_le_of_holderWith {f : CkHolderSpace k α E F} {M : ℝ}
    {K : ℝ≥0} (hM : ∀ i ≤ k, ∀ x, ‖_root_.iteratedFDeriv ℝ i f x‖ ≤ M)
    (hK : HolderWith K α (_root_.iteratedFDeriv ℝ k f)) : ‖f‖ ≤ (k + 1) * M + K := by
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0 k.zero_le 0)
  rw [norm_eq]
  gcongr
  · calc ∑ i : Fin (k + 1), ‖f.iteratedFDeriv i‖ ≤ ∑ _i : Fin (k + 1), M :=
          Finset.sum_le_sum fun i _ ↦ (BoundedContinuousFunction.norm_le hM0).2 fun x ↦ by
            rw [← iteratedFDeriv_eq]
            exact hM i (Nat.lt_succ_iff.1 i.2) x
      _ = (k + 1) * M := by simp
  · exact_mod_cast hK.nnholderNorm_le

/-- The values of a bounded `C^{k,α}` map are controlled by the supremum norm of its order-zero
field. -/
theorem norm_apply_le_iteratedFDeriv_zero (f : CkHolderSpace k α E F) (x : E) :
    ‖f x‖ ≤ ‖f.iteratedFDeriv 0‖ := by
  calc ‖f x‖ = ‖f.iteratedFDeriv 0 x‖ := by
        rw [← iteratedFDeriv_eq, Fin.val_zero, norm_iteratedFDeriv_zero]
    _ ≤ _ := (f.iteratedFDeriv 0).norm_coe_le_norm x

/-- The first derivative of a bounded `C^{k+1,α}` map is controlled by the supremum norm of its
first derivative field. -/
theorem norm_fderiv_le_iteratedFDeriv_one (f : CkHolderSpace (k + 1) α E F) (x : E) :
    ‖fderiv ℝ f x‖ ≤ ‖f.iteratedFDeriv 1‖ := by
  calc ‖fderiv ℝ f x‖ = ‖f.iteratedFDeriv 1 x‖ := by
        rw [← iteratedFDeriv_eq, Fin.val_one, norm_iteratedFDeriv_one]
    _ ≤ _ := (f.iteratedFDeriv 1).norm_coe_le_norm x

/-- The curried second derivative of a bounded `C^{k+2,α}` map is controlled by the supremum norm
of its second derivative field. -/
theorem norm_fderiv_fderiv_le_iteratedFDeriv_two (f : CkHolderSpace (k + 2) α E F) (x : E) :
    ‖fderiv ℝ (fderiv ℝ f) x‖ ≤ ‖f.iteratedFDeriv 2‖ := by
  calc ‖fderiv ℝ (fderiv ℝ f) x‖ = ‖f.iteratedFDeriv 2 x‖ := by
        rw [← iteratedFDeriv_eq, Fin.val_two, ← norm_iteratedFDeriv_one, norm_iteratedFDeriv_fderiv]
    _ ≤ _ := (f.iteratedFDeriv 2).norm_coe_le_norm x

/-- The derivative of a bounded `C^{k+1,α}` map is `k` times continuously differentiable. -/
theorem contDiff_fderiv (f : CkHolderSpace (k + 1) α E F) : ContDiff ℝ k (fderiv ℝ f) :=
  f.contDiff.fderiv_right (by norm_cast)

/-- The curried second derivative of a bounded `C^{2,α}` map is `α`-Hölder with the Hölder
seminorm of `D²f`. -/
theorem holderWith_fderiv_fderiv (f : CkHolderSpace 2 α E F) :
    HolderWith (nnHolderNorm α (_root_.iteratedFDeriv ℝ 2 f)) α (fderiv ℝ (fderiv ℝ f)) := by
  have he : (fun x ↦ continuousMultilinearCurryFin2 ℝ E F (_root_.iteratedFDeriv ℝ 2 f x)) =
      fderiv ℝ (fderiv ℝ f) :=
    funext fun x ↦ continuousMultilinearCurryFin2_iteratedFDeriv_two _ x
  simpa [Function.comp_def, he] using
    (continuousMultilinearCurryFin2 ℝ E F).isometry.lipschitzWith.holderWith.comp
      f.memHolder_iteratedFDeriv.holderWith

/-- The underlying function of a bounded `C^{k,α}` map, as a bounded continuous function. -/
def toBoundedContinuousFunction (f : CkHolderSpace k α E F) : E →ᵇ F :=
  BoundedContinuousFunction.ofNormedAddCommGroup f f.contDiff.continuous ‖f‖ f.norm_apply_le

@[simp]
theorem coe_toBoundedContinuousFunction (f : CkHolderSpace k α E F) :
    ⇑f.toBoundedContinuousFunction = f :=
  BoundedContinuousFunction.coe_ofNormedAddCommGroup ..

/-- The underlying bounded continuous function has norm at most the `C^{k,α}` norm. -/
theorem norm_toBoundedContinuousFunction_le (f : CkHolderSpace k α E F) :
    ‖f.toBoundedContinuousFunction‖ ≤ ‖f‖ :=
  BoundedContinuousFunction.norm_ofNormedAddCommGroup_le _ (norm_nonneg f) _

/-- A `C^{k,α}` map is determined by its underlying bounded continuous function. -/
theorem toBoundedContinuousFunction_injective :
    Function.Injective (toBoundedContinuousFunction : CkHolderSpace k α E F → E →ᵇ F) :=
  fun _ _ h ↦ ext fun x ↦ by simpa using DFunLike.congr_fun h x

/-- The supremum norm of the underlying function is that of the order-zero derivative field. -/
theorem norm_toBoundedContinuousFunction (f : CkHolderSpace k α E F) :
    ‖f.toBoundedContinuousFunction‖ = ‖f.iteratedFDeriv 0‖ := by
  rw [BoundedContinuousFunction.norm_eq_iSup_norm,
    BoundedContinuousFunction.norm_eq_iSup_norm (f.iteratedFDeriv 0),
    coe_toBoundedContinuousFunction]
  congr 1 with x
  rw [← iteratedFDeriv_eq, Fin.val_zero, norm_iteratedFDeriv_zero]

/-- The derivative of a bounded `C^{k+1,α}` map, in curried form, as a bounded continuous
field. -/
def fderivBCF (f : CkHolderSpace (k + 1) α E F) : E →ᵇ (E →L[ℝ] F) :=
  BoundedContinuousFunction.ofNormedAddCommGroup (fderiv ℝ f)
    (f.contDiff.continuous_fderiv (by simp)) ‖f‖ fun x ↦ by
      simpa using f.norm_iteratedFDeriv_apply_le (i := 1) (by omega) x

@[simp]
theorem coe_fderivBCF (f : CkHolderSpace (k + 1) α E F) : ⇑f.fderivBCF = fderiv ℝ f :=
  BoundedContinuousFunction.coe_ofNormedAddCommGroup ..

/-- The supremum norm of the curried derivative is that of the first derivative field. -/
theorem norm_fderivBCF (f : CkHolderSpace (k + 1) α E F) :
    ‖f.fderivBCF‖ = ‖f.iteratedFDeriv 1‖ := by
  rw [BoundedContinuousFunction.norm_eq_iSup_norm,
    BoundedContinuousFunction.norm_eq_iSup_norm (f.iteratedFDeriv 1), coe_fderivBCF]
  congr 1 with x
  rw [← iteratedFDeriv_eq, Fin.val_one, norm_iteratedFDeriv_one]

/-- The derivative field `fderivBCF` is the Fréchet derivative of a bounded `C^{k+1,α}` map. -/
theorem hasFDerivAt (f : CkHolderSpace (k + 1) α E F) (x : E) :
    HasFDerivAt f (f.fderivBCF x) x := by
  rw [coe_fderivBCF]
  exact ((f.contDiff.differentiable (by simp)) x).hasFDerivAt

/-- The `i`-th derivative field, as a continuous linear map to bounded continuous fields. It is
bounded by the `C^{k,α}` norm pointwise, by `CkHolderSpace.norm_iteratedFDeriv_le`. -/
-- No operator-norm bound is stated: outside this file, without the local shortcut instances,
-- instance search for the operator norm on this space of continuous linear maps exceeds the
-- default synthesis limits, so such a statement could only be used here.
def iteratedFDerivL (i : Fin (k + 1)) :
    CkHolderSpace k α E F →L[ℝ] (E →ᵇ (E [×i]→L[ℝ] F)) :=
  (fieldL i).comp toJetL

/-- The linear map `iteratedFDerivL i` sends a map to its `i`-th derivative field. -/
@[simp]
theorem iteratedFDerivL_apply (i : Fin (k + 1)) (f : CkHolderSpace k α E F) :
    iteratedFDerivL i f = f.iteratedFDeriv i := by
  rw [iteratedFDerivL, ContinuousLinearMap.comp_apply, toJetL_apply, iteratedFDeriv]

/-- The `k`-th derivative field, as a continuous linear map to the bounded Hölder space. -/
def iteratedFDerivHolderL : CkHolderSpace k α E F →L[ℝ] HolderSpace α E (E [×k]→L[ℝ] F) :=
  (WithLp.sndL 1 ℝ _ _).comp toJetL

/-- The linear map `iteratedFDerivHolderL` sends a map to its `k`-th derivative field in the
bounded Hölder space. -/
@[simp]
theorem iteratedFDerivHolderL_apply (f : CkHolderSpace k α E F) :
    iteratedFDerivHolderL f = f.iteratedFDerivHolder := by
  rw [iteratedFDerivHolderL, ContinuousLinearMap.comp_apply, toJetL_apply, WithLp.sndL_apply,
    iteratedFDerivHolder, WithLp.ofLp_snd]

/-- The Hölder-space norm of the `k`-th derivative field is controlled by the `C^{k,α}` norm. -/
theorem norm_iteratedFDerivHolder_le (f : CkHolderSpace k α E F) :
    ‖f.iteratedFDerivHolder‖ ≤ ‖f‖ := by
  rw [← norm_toJet, WithLp.prod_norm_eq_of_L1]
  exact le_add_of_nonneg_left (norm_nonneg _)

/-- The `k`-th derivative map to the bounded Hölder space has operator norm at most one. -/
theorem norm_iteratedFDerivHolderL_le_one :
    ‖iteratedFDerivHolderL (k := k) (α := α) (E := E) (F := F)‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun f ↦ by
    rw [iteratedFDerivHolderL_apply, one_mul]
    exact norm_iteratedFDerivHolder_le f

/-- Each derivative field of the zero map is zero. -/
@[simp]
theorem iteratedFDeriv_zero (i : Fin (k + 1)) :
    (0 : CkHolderSpace k α E F).iteratedFDeriv i = 0 := by
  simpa only [iteratedFDerivL_apply] using (iteratedFDerivL (α := α) (E := E) (F := F) i).map_zero

/-- Each derivative field is additive. -/
@[simp]
theorem iteratedFDeriv_add (f g : CkHolderSpace k α E F) (i : Fin (k + 1)) :
    (f + g).iteratedFDeriv i = f.iteratedFDeriv i + g.iteratedFDeriv i := by
  simpa only [iteratedFDerivL_apply] using (iteratedFDerivL i).map_add f g

/-- Each derivative field commutes with scalar multiplication. -/
@[simp]
theorem iteratedFDeriv_smul (c : ℝ) (f : CkHolderSpace k α E F) (i : Fin (k + 1)) :
    (c • f).iteratedFDeriv i = c • f.iteratedFDeriv i := by
  simpa only [iteratedFDerivL_apply] using (iteratedFDerivL i).map_smul c f

/-- The `k`-th derivative field of the zero map, in the bounded Hölder space, is zero. -/
@[simp]
theorem iteratedFDerivHolder_zero : (0 : CkHolderSpace k α E F).iteratedFDerivHolder = 0 := by
  simpa only [iteratedFDerivHolderL_apply] using
    (iteratedFDerivHolderL (k := k) (α := α) (E := E) (F := F)).map_zero

/-- The `k`-th derivative field, in the bounded Hölder space, is additive. -/
@[simp]
theorem iteratedFDerivHolder_add (f g : CkHolderSpace k α E F) :
    (f + g).iteratedFDerivHolder = f.iteratedFDerivHolder + g.iteratedFDerivHolder := by
  simpa only [iteratedFDerivHolderL_apply] using iteratedFDerivHolderL.map_add f g

/-- The `k`-th derivative field, in the bounded Hölder space, commutes with scalar
multiplication. -/
@[simp]
theorem iteratedFDerivHolder_smul (c : ℝ) (f : CkHolderSpace k α E F) :
    (c • f).iteratedFDerivHolder = c • f.iteratedFDerivHolder := by
  simpa only [iteratedFDerivHolderL_apply] using iteratedFDerivHolderL.map_smul c f

/-- The underlying function of the zero map is zero. -/
@[simp]
theorem coe_zero : ⇑(0 : CkHolderSpace k α E F) = 0 := by
  ext x
  simp only [← toFun_eq_coe, toFun, iteratedFDeriv_zero, Pi.zero_apply,
    FunLike.coe_zero]
  simp

/-- The underlying function of a sum is the sum of the underlying functions. -/
@[simp]
theorem coe_add (f g : CkHolderSpace k α E F) : ⇑(f + g) = f + g := by
  ext x
  simp only [← toFun_eq_coe, toFun, iteratedFDeriv_add, Pi.add_apply,
    _root_.add_apply]
  simp

/-- The underlying function of a scalar multiple is the scalar multiple of the underlying
function. -/
@[simp]
theorem coe_smul (c : ℝ) (f : CkHolderSpace k α E F) : ⇑(c • f) = c • ⇑f := by
  ext x
  simp only [← toFun_eq_coe, toFun, iteratedFDeriv_smul, Pi.smul_apply,
    _root_.smul_apply]
  simp

/-- The underlying bounded continuous function of a sum. -/
@[simp]
theorem toBoundedContinuousFunction_add (f g : CkHolderSpace k α E F) :
    (f + g).toBoundedContinuousFunction =
      f.toBoundedContinuousFunction + g.toBoundedContinuousFunction := by
  ext x
  simp

/-- The underlying bounded continuous function of a scalar multiple. -/
@[simp]
theorem toBoundedContinuousFunction_smul (c : ℝ) (f : CkHolderSpace k α E F) :
    (c • f).toBoundedContinuousFunction = c • f.toBoundedContinuousFunction := by
  ext x
  simp

/-- Forgetting the derivatives is a continuous linear map to bounded continuous functions. -/
def toBoundedContinuousFunctionCLM : CkHolderSpace k α E F →L[ℝ] (E →ᵇ F) :=
  LinearMap.mkContinuous
    { toFun := toBoundedContinuousFunction
      map_add' := toBoundedContinuousFunction_add
      map_smul' := toBoundedContinuousFunction_smul } 1 fun f ↦ by
        rw [one_mul]
        exact norm_toBoundedContinuousFunction_le f

@[simp]
theorem toBoundedContinuousFunctionCLM_apply (f : CkHolderSpace k α E F) :
    toBoundedContinuousFunctionCLM f = f.toBoundedContinuousFunction := (rfl)

/-- Forgetting the derivatives has operator norm at most one. -/
theorem norm_toBoundedContinuousFunctionCLM_le_one :
    ‖toBoundedContinuousFunctionCLM (k := k) (α := α) (E := E) (F := F)‖ ≤ 1 :=
  LinearMap.mkContinuous_norm_le _ zero_le_one _

/-- A bounded continuous field built from a continuous function with a uniform bound. -/
private def bcfOf {G : Type*} [NormedAddCommGroup G] (g : E → G) (hg : Continuous g)
    (hbdd : ∃ C, ∀ x, ‖g x‖ ≤ C) : E →ᵇ G :=
  BoundedContinuousFunction.ofNormedAddCommGroup g hg hbdd.choose hbdd.choose_spec

/-- The jet of iterated derivatives of a `C^k` function with bounded derivatives through order
`k` and globally `α`-Hölder `k`-th derivative. -/
private def jetOf (f : E → F) (hf : ContDiff ℝ k f)
    (hbdd : ∀ i ≤ k, ∃ C, ∀ x, ‖_root_.iteratedFDeriv ℝ i f x‖ ≤ C)
    (hholder : MemHolder α (_root_.iteratedFDeriv ℝ k f)) : Jet k α E F :=
  WithLp.toLp 1
    (WithLp.toLp 1 fun j : Fin k ↦ bcfOf (_root_.iteratedFDeriv ℝ j f)
        (hf.continuous_iteratedFDeriv (by exact_mod_cast j.2.le)) (hbdd j j.2.le),
      HolderSpace.ofBoundedContinuousFunction
        (bcfOf (_root_.iteratedFDeriv ℝ k f) (hf.continuous_iteratedFDeriv le_rfl)
          (hbdd k le_rfl)) hholder)

private theorem fieldL_jetOf (f : E → F) (hf : ContDiff ℝ k f)
    (hbdd : ∀ i ≤ k, ∃ C, ∀ x, ‖_root_.iteratedFDeriv ℝ i f x‖ ≤ C)
    (hholder : MemHolder α (_root_.iteratedFDeriv ℝ k f)) (i : Fin (k + 1)) (x : E) :
    fieldL i (jetOf f hf hbdd hholder) x = _root_.iteratedFDeriv ℝ i f x := by
  induction i using Fin.lastCases with
  | last =>
    rw [fieldL_last]
    simp [jetOf, bcfOf]
  | cast j =>
    rw [fieldL_castSucc]
    simp [jetOf, bcfOf]

private theorem isJetGraph_jetOf (f : E → F) (hf : ContDiff ℝ k f)
    (hbdd : ∀ i ≤ k, ∃ C, ∀ x, ‖_root_.iteratedFDeriv ℝ i f x‖ ≤ C)
    (hholder : MemHolder α (_root_.iteratedFDeriv ℝ k f)) :
    IsJetGraph (jetOf f hf hbdd hholder) := fun j x ↦ by
  have hfun : (fieldL j.castSucc (jetOf f hf hbdd hholder) : E → E [×j]→L[ℝ] F) =
      _root_.iteratedFDeriv ℝ j f :=
    funext (fieldL_jetOf f hf hbdd hholder j.castSucc)
  have h := (hf.differentiable_iteratedFDeriv (m := j) (by exact_mod_cast j.2) x).hasFDerivAt
  rw [fderiv_iteratedFDeriv, Function.comp_apply] at h
  rw [hfun, fieldL_jetOf]
  exact h

/-- Build a bounded `C^{k,α}` map from a `C^k` function whose iterated derivatives through order
`k` are bounded and whose `k`-th iterated derivative is globally `α`-Hölder. -/
def ofContDiff (f : E → F) (hf : ContDiff ℝ k f)
    (hbdd : ∀ i ≤ k, ∃ C, ∀ x, ‖_root_.iteratedFDeriv ℝ i f x‖ ≤ C)
    (hholder : MemHolder α (_root_.iteratedFDeriv ℝ k f)) : CkHolderSpace k α E F :=
  mk (jetOf f hf hbdd hholder) (isJetGraph_jetOf f hf hbdd hholder)

/-- The underlying function of `ofContDiff f` is `f`. -/
@[simp]
theorem coe_ofContDiff (f : E → F) (hf : ContDiff ℝ k f)
    (hbdd : ∀ i ≤ k, ∃ C, ∀ x, ‖_root_.iteratedFDeriv ℝ i f x‖ ≤ C)
    (hholder : MemHolder α (_root_.iteratedFDeriv ℝ k f)) :
    ⇑(ofContDiff f hf hbdd hholder) = f := by
  ext x
  rw [← toFun_eq_coe, toFun, iteratedFDeriv, ofContDiff, toJet_mk, fieldL_jetOf,
    iteratedFDeriv_zero_eq_comp]
  simp

/-- The derivative identities are closed under uniform convergence of the fields. -/
private theorem isClosed_isJetGraph : IsClosed {J : Jet k α E F | IsJetGraph J} := by
  have hset : {J : Jet k α E F | IsJetGraph J} =
      ⋂ j : Fin k, (fun J : Jet k α E F ↦ (fieldL j.castSucc J, fieldL j.succ J)) ⁻¹'
        {J | ∀ x, HasFDerivAt (J.1 : E → E [×j]→L[ℝ] F) (curryLeftL E F j (J.2 x)) x} := by
    ext J
    simp [IsJetGraph]
  rw [hset]
  exact isClosed_iInter fun j ↦
    (isClosed_setOf_hasFDerivAt_comp (curryLeftL E F j)
      (curryLeftL E F j).uniformContinuous).preimage
      ((fieldL (k := k) (α := α) (E := E) (F := F) _).continuous.prodMk
        (fieldL (k := k) (α := α) (E := E) (F := F) _).continuous)

/-- Bounded `C^{k,α}` maps into a Banach space form a Banach space. -/
instance instCompleteSpace [CompleteSpace F] : CompleteSpace (CkHolderSpace k α E F) := by
  unfold CkHolderSpace
  exact isClosed_isJetGraph.completeSpace_coe

attribute [irreducible] instNormedAddCommGroup instNormedSpace _root_.TauCeti.CkHolderSpace

end CkHolderSpace

/-- Bounded finite-order Hölder maps vanishing outside a prescribed set, as a submodule of the
native derivative-graph space. -/
def supportedCkHolderSubmodule {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (k : ℕ) (α : ℝ≥0) (s : Set E) :
    Submodule ℝ (CkHolderSpace k α E F) where
  carrier := {f | ∀ x ∉ s, f x = 0}
  zero_mem' := by simp
  add_mem' := by
    intro f g hf hg x hx
    simp [hf x hx, hg x hx]
  smul_mem' := by
    intro c f hf x hx
    simp [hf x hx]

/-- Membership in the supported submodule means vanishing outside its defining set. -/
@[simp]
theorem mem_supportedCkHolderSubmodule_iff {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    {k : ℕ} {α : ℝ≥0} {s : Set E} {f : CkHolderSpace k α E F} :
    f ∈ supportedCkHolderSubmodule k α s ↔ ∀ x ∉ s, f x = 0 := Iff.rfl

/-- The support of an element of the supported Hölder submodule lies in its defining set. -/
theorem support_subset_of_mem_supportedCkHolderSubmodule {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    {k : ℕ} {α : ℝ≥0} {s : Set E} {f : CkHolderSpace k α E F}
    (hf : f ∈ supportedCkHolderSubmodule k α s) : Function.support f ⊆ s := by
  intro x hx
  by_contra h
  exact hx (hf x h)

end TauCeti

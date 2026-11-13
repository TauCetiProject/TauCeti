/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Holder.Iterated
public import Mathlib.Topology.Sets.Opens
import TauCeti.Analysis.Calculus.IteratedFDeriv.Basic
import TauCeti.Analysis.Calculus.UniformLimitsDeriv
import TauCeti.Analysis.Holder.Inclusion
import TauCeti.Topology.MetricSpace.Bounded

/-!
# `C^{k,α}` maps on an open set

For an open set `U` of a real normed space `E`, this file constructs the normed space
`C^{k,α}(U, F)` of maps `U → F` that are `k` times continuously differentiable, whose iterated
Fréchet derivatives through order `k` are bounded on `U`, and whose `k`-th iterated derivative is
`α`-Hölder on `U`. Its norm is

`‖f‖ = ∑_{i ≤ k} sup_{x ∈ U} ‖D^i f(x)‖ + [D^k f]_{α, U}`,

where `[g]_{α, U} = sup_{x ≠ y ∈ U} ‖g x - g y‖ / ‖x - y‖^α` and the suprema use the operator norm
of continuous multilinear maps. It is a Banach space when `F` is. These are the spaces in which
the global Schauder theory of elliptic equations on a domain is posed. The spaces written
`C^{k,α}(Ū)` by Gilbarg and Trudinger also require the derivatives through order `k` to extend
continuously to the closure `Ū`. For bounded convex `U`, `α > 0` and complete `F` this follows
from the bounds here, since each derivative below order `k` is then Lipschitz on `U` and the `k`-th
derivative is uniformly Hölder on `U`, so the two spaces agree. For a general bounded `U` the
extension can fail: on a slit annulus in the plane, the angle function lies in `C^{1,α}(U)` but
does not extend continuously across the slit.

The Hölder seminorm is global on `U`: it compares the `k`-th derivative at any two points of `U`,
not only at nearby ones. So for `α > 0`, on `U = (-1, 0) ∪ (0, 1)` the sign function, which is
smooth on `U` with all derivatives zero, does not lie in `C^{0,α}(U)`. For `α > 0` this is what
distinguishes `C^{k,α}(U)` from the space of maps that are `C^{k,α}` on every compact subset of
`U`.

An element is coerced to the function `E → F` which is the map on `U` and zero off `U`. This keeps
derivatives available as Mathlib's `iteratedFDeriv`, which agrees on the open set `U` with the
derivatives of the map. Internally, an element is the family of its derivative fields: bounded
continuous fields `U →ᵇ (E [×i]→L[ℝ] F)` for `i < k` and a bounded Hölder field of order `k`, such
that each field, extended by zero, has the next field, curried on the left, as its Fréchet
derivative at every point of `U`. These identities are closed under uniform convergence on `U`,
which gives completeness.

## Main declarations

* `TauCeti.CkHolderSpaceOn k α U F`: maps `U → F` with bounded derivatives through order `k`
  and `α`-Hölder `k`-th derivative on the open set `U`.
* `TauCeti.CkHolderSpaceOn.iteratedFDeriv`: the bounded continuous `i`-th derivative field on
  `U`, for `i ≤ k`; `TauCeti.CkHolderSpaceOn.iteratedFDeriv_eq` identifies it with Mathlib's
  `iteratedFDeriv`.
* `TauCeti.CkHolderSpaceOn.contDiffOn`, `TauCeti.CkHolderSpaceOn.holderOnWith_iteratedFDeriv`:
  the regularity of an element; `TauCeti.CkHolderSpaceOn.ofContDiffOn` is the converse
  constructor.
* `TauCeti.CkHolderSpaceOn.norm_eq`: the norm is the sum of the supremum norms of the derivatives
  through order `k` on `U` and the `α`-Hölder seminorm on `U` of the `k`-th derivative.
* `TauCeti.CkHolderSpaceOn.instCompleteSpace`: completeness when the codomain is complete.
* `TauCeti.CkHolderSpaceOn.restrictL`: restriction to a smaller open set, of norm at most one.
* `TauCeti.CkHolderSpaceOn.inclusionL`: the inclusion `C^{k,α}(U) → C^{k,β}(U)` for `β ≤ α` on a
  bounded open set.
* `TauCeti.CkHolderSpace.restrictL`: restriction of a bounded `C^{k,α}` map on the whole space
  to `U`, of norm at most one.

## References

D. Gilbarg and N. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
Section 4.1.
-/

public section

noncomputable section

namespace TauCeti

open Set Filter Topology TopologicalSpace
open scoped NNReal BoundedContinuousFunction

universe u v

variable (k : ℕ) (α : ℝ≥0) {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
  (U : Opens E) (F : Type v) [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Shortcut instance for bounded continuous fields of `n`-multilinear maps on an open set. It is
local for the same reason as the corresponding instance for `CkHolderSpace`: without it, instance
search for the module structure of `ℓ¹` products of these fields indexed by the order `n` exceeds
the default synthesis depth. -/
local instance CkHolderSpaceOn.instNormedAddCommGroupBoundedContinuousFunction (n : ℕ) :
    NormedAddCommGroup (U →ᵇ (E [×n]→L[ℝ] F)) :=
  inferInstance

/-- Shortcut instance for bounded continuous fields of `n`-multilinear maps on an open set, needed
for scalar multiplication on the `ℓ¹` products of these fields. -/
local instance CkHolderSpaceOn.instNormedSpaceBoundedContinuousFunction (n : ℕ) :
    NormedSpace ℝ (U →ᵇ (E [×n]→L[ℝ] F)) :=
  inferInstance

/-- The space of maps on the open set `U` that are `k` times continuously differentiable, with
iterated Fréchet derivatives through order `k` bounded on `U` and `k`-th iterated derivative
`α`-Hölder on `U`. Its norm is

`∑_{i ≤ k} sup_{x ∈ U} ‖D^i f(x)‖ + [D^k f]_{α, U}`.
-/
-- The module system requires exposure while the declarations below construct and project through
-- this graph alias. The final `irreducible` attribute restores the abstraction boundary.
@[expose] def CkHolderSpaceOn : Type _ :=
  let graph : Submodule ℝ (CkHolderJet k α U E F) :=
    { carrier := {J | ∀ (j : Fin k) (x : U),
        HasFDerivAt
          (Function.extend Subtype.val (CkHolderJet.fieldL j.castSucc J : U → E [×j]→L[ℝ] F) 0)
          (CkHolderJet.curryLeftL E F j (CkHolderJet.fieldL j.succ J x)) x}
      zero_mem' := fun j x ↦ by
        simp only [map_zero, FunLike.coe_zero, Pi.zero_apply, Function.extend_zero]
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

open CkHolderJet

variable {k α U F}

/-- The derivative identities of a jet: each field below order `k`, extended by zero, has the
next field, curried on the left, as its Fréchet derivative at every point of `U`. -/
private def IsJetGraph (J : CkHolderJet k α U E F) : Prop :=
  ∀ (j : Fin k) (x : U),
    HasFDerivAt (Function.extend Subtype.val (fieldL j.castSucc J : U → E [×j]→L[ℝ] F) 0)
      (curryLeftL E F j (fieldL j.succ J x)) x

/-- Elements are the jets satisfying the derivative identities. This is the identity map: the
carrier of `CkHolderSpaceOn` is the set of jets satisfying `IsJetGraph`. -/
private def equivSubtype : CkHolderSpaceOn k α U F ≃ {J : CkHolderJet k α U E F // IsJetGraph J} :=
  Equiv.refl _

/-- The underlying jet of an element. -/
private def toJet (f : CkHolderSpaceOn k α U F) : CkHolderJet k α U E F := (equivSubtype f).1

/-- An element from a jet satisfying the derivative identities. -/
private def mk (J : CkHolderJet k α U E F) (hJ : IsJetGraph J) : CkHolderSpaceOn k α U F :=
  equivSubtype.symm ⟨J, hJ⟩

private theorem toJet_injective :
    Function.Injective (toJet (k := k) (α := α) (U := U) (F := F)) :=
  fun _ _ h ↦ equivSubtype.injective (Subtype.ext h)

private theorem toJet_mk (J : CkHolderJet k α U E F) (hJ) : toJet (mk J hJ) = J := by
  rw [toJet, mk, Equiv.apply_symm_apply]

private theorem hasFDerivAt_fieldL (f : CkHolderSpaceOn k α U F) (j : Fin k) (x : U) :
    HasFDerivAt (Function.extend Subtype.val (fieldL j.castSucc (toJet f) : U → E [×j]→L[ℝ] F) 0)
      (curryLeftL E F j (fieldL j.succ (toJet f) x)) x :=
  (equivSubtype f).2 j x

instance instNormedAddCommGroup : NormedAddCommGroup (CkHolderSpaceOn k α U F) := by
  unfold CkHolderSpaceOn
  infer_instance

instance instNormedSpace : NormedSpace ℝ (CkHolderSpaceOn k α U F) := by
  unfold CkHolderSpaceOn
  infer_instance

private theorem norm_toJet (f : CkHolderSpaceOn k α U F) : ‖toJet f‖ = ‖f‖ :=
  Submodule.norm_coe f

/-- The underlying jet, as a continuous linear map: the inclusion of the submodule
`CkHolderSpaceOn` into the jet space. -/
private def toJetL : CkHolderSpaceOn k α U F →L[ℝ] CkHolderJet k α U E F := by
  unfold CkHolderSpaceOn
  exact Submodule.subtypeL _

/-- The inclusion `toJetL` is `toJet`; both are the coercion of the submodule. -/
private theorem toJetL_apply (f : CkHolderSpaceOn k α U F) : toJetL f = toJet f :=
  rfl

/-- The bounded continuous `i`-th derivative field on `U` of a `C^{k,α}` map on `U`, for
`i ≤ k`. It agrees with Mathlib's `iteratedFDeriv` by `CkHolderSpaceOn.iteratedFDeriv_eq`. -/
def iteratedFDeriv (f : CkHolderSpaceOn k α U F) (i : Fin (k + 1)) : U →ᵇ (E [×i]→L[ℝ] F) :=
  fieldL i (toJet f)

/-- The `k`-th derivative field on `U` of a `C^{k,α}` map on `U`, as an element of the bounded
Hölder space of `U`. -/
def iteratedFDerivHolder (f : CkHolderSpaceOn k α U F) : HolderSpace α U (E [×k]→L[ℝ] F) :=
  (toJet f).ofLp.2

/-- The underlying function of a `C^{k,α}` map on `U`: its order-zero derivative field on `U`,
evaluated on the empty tuple, and zero off `U`. Use the coercion `⇑f` instead. -/
def toFun (f : CkHolderSpaceOn k α U F) : E → F :=
  Function.extend Subtype.val (fun x : U ↦ (f.iteratedFDeriv 0 x).curry0) 0

/-- The formal Taylor series recorded by an element, truncated after order `k`. -/
private def series (f : CkHolderSpaceOn k α U F) (x : E) : FormalMultilinearSeries ℝ E F :=
  fun m ↦ if h : m < k + 1 then
    Function.extend Subtype.val (f.iteratedFDeriv ⟨m, h⟩ : U → E [×m]→L[ℝ] F) 0 x else 0

private theorem series_of_lt (f : CkHolderSpaceOn k α U F) (x : E) {m : ℕ} (h : m < k + 1) :
    series f x m = Function.extend Subtype.val (f.iteratedFDeriv ⟨m, h⟩ : U → E [×m]→L[ℝ] F) 0 x
    := by
  simp [series, h]

/-- The recorded derivative fields form a Taylor series up to order `k` on `U` for the underlying
function. -/
private theorem hasFTaylorSeriesUpToOn (f : CkHolderSpaceOn k α U F) :
    HasFTaylorSeriesUpToOn k f.toFun (series f) U where
  zero_eq x hx := by
    rw [series_of_lt f x k.succ_pos, toFun, Function.extend_val_apply (SetLike.mem_coe.1 hx),
      Function.extend_val_apply (SetLike.mem_coe.1 hx)]
    rfl
  fderivWithin m hm x hx := by
    have hmk : m < k := by exact_mod_cast hm
    have hfun : (fun y ↦ series f y m) = Function.extend Subtype.val
        (fieldL (⟨m, hmk⟩ : Fin k).castSucc (toJet f) : U → E [×m]→L[ℝ] F) 0 :=
      funext fun y ↦ series_of_lt f y (by omega)
    rw [hfun, series_of_lt f x (by omega), Function.extend_val_apply (SetLike.mem_coe.1 hx),
      ← curryLeftL_apply]
    exact (hasFDerivAt_fieldL f ⟨m, hmk⟩ ⟨x, hx⟩).hasFDerivWithinAt
  cont m hm := by
    have hmk : m < k + 1 := by
      have : m ≤ k := by exact_mod_cast hm
      omega
    have hfun : (fun y ↦ series f y m) = Function.extend Subtype.val
        (f.iteratedFDeriv ⟨m, hmk⟩ : U → E [×m]→L[ℝ] F) 0 :=
      funext fun y ↦ series_of_lt f y hmk
    have hrestrict : (U : Set E).domRestrict (Function.extend Subtype.val
        (f.iteratedFDeriv ⟨m, hmk⟩ : U → E [×m]→L[ℝ] F) 0) = f.iteratedFDeriv ⟨m, hmk⟩ :=
      funext fun y ↦ Function.extend_val_apply y.2
    rw [hfun, continuousOn_iff_continuous_domRestrict, hrestrict]
    exact (f.iteratedFDeriv ⟨m, hmk⟩).continuous

private theorem iteratedFDeriv_toFun (f : CkHolderSpaceOn k α U F) (i : Fin (k + 1)) (x : U) :
    _root_.iteratedFDeriv ℝ i f.toFun x = f.iteratedFDeriv i x := by
  rw [← iteratedFDerivWithin_of_isOpen i U.isOpen x.2,
    ← (hasFTaylorSeriesUpToOn f).eq_iteratedFDerivWithin_of_uniqueDiffOn
      (by exact_mod_cast i.is_le) U.isOpen.uniqueDiffOn x.2,
    series_of_lt f x i.2, Function.extend_val_apply x.2]

private theorem toFun_apply_of_notMem (f : CkHolderSpaceOn k α U F) {x : E} (hx : x ∉ U) :
    f.toFun x = 0 :=
  Function.extend_apply' _ _ _ fun ⟨y, hy⟩ ↦ hx (hy ▸ y.2)

/-- A `C^{k,α}` map on `U` is determined by its underlying function. -/
theorem toFun_injective :
    Function.Injective (toFun (k := k) (α := α) (U := U) (F := F)) := by
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

instance instFunLike : FunLike (CkHolderSpaceOn k α U F) E F where
  coe := toFun
  coe_injective := toFun_injective

@[simp]
theorem toFun_eq_coe (f : CkHolderSpaceOn k α U F) : f.toFun = ⇑f :=
  (rfl)

/-- Two `C^{k,α}` maps on `U` are equal when their underlying functions agree on `U`. -/
@[ext]
theorem ext {f g : CkHolderSpaceOn k α U F} (h : ∀ x ∈ U, f x = g x) : f = g := by
  refine DFunLike.ext f g fun x ↦ ?_
  by_cases hx : x ∈ U
  · exact h x hx
  · rw [← toFun_eq_coe, ← toFun_eq_coe, toFun_apply_of_notMem f hx, toFun_apply_of_notMem g hx]

/-- The underlying function of a `C^{k,α}` map on `U` vanishes off `U`. -/
theorem apply_eq_zero_of_notMem (f : CkHolderSpaceOn k α U F) {x : E} (hx : x ∉ U) : f x = 0 :=
  toFun_apply_of_notMem f hx

/-- The underlying function of a `C^{k,α}` map on `U` is its own indicator function on `U`. -/
@[simp]
theorem indicator_coe (f : CkHolderSpaceOn k α U F) : (U : Set E).indicator ⇑f = ⇑f := by
  funext x
  by_cases hx : x ∈ U
  · exact indicator_of_mem hx _
  · rw [indicator_of_notMem hx, apply_eq_zero_of_notMem f hx]

/-- The recorded derivative fields are the iterated Fréchet derivatives of the underlying
function on `U`. -/
theorem iteratedFDeriv_eq (f : CkHolderSpaceOn k α U F) (i : Fin (k + 1)) (x : U) :
    _root_.iteratedFDeriv ℝ i f x = f.iteratedFDeriv i x :=
  iteratedFDeriv_toFun f i x

/-- The `i`-th derivative field is Mathlib's `iteratedFDeriv` of the underlying function,
restricted to `U`. -/
@[simp]
theorem coe_iteratedFDeriv (f : CkHolderSpaceOn k α U F) (i : Fin (k + 1)) :
    ⇑(f.iteratedFDeriv i) = (U : Set E).domRestrict (_root_.iteratedFDeriv ℝ i f) :=
  funext fun x ↦ (iteratedFDeriv_eq f i x).symm

/-- A `C^{k,α}` map on `U` is `k` times continuously differentiable on `U`. -/
theorem contDiffOn (f : CkHolderSpaceOn k α U F) : ContDiffOn ℝ k f U :=
  (hasFTaylorSeriesUpToOn f).contDiffOn

/-- The Hölder field, as a bounded continuous field, is the derivative field of order `k`. -/
@[simp]
theorem toBoundedContinuousFunction_iteratedFDerivHolder (f : CkHolderSpaceOn k α U F) :
    f.iteratedFDerivHolder.toBoundedContinuousFunction = f.iteratedFDeriv (Fin.last k) := by
  rw [iteratedFDeriv, fieldL_last, iteratedFDerivHolder]

/-- The Hölder field records the `k`-th iterated Fréchet derivative on `U`. -/
@[simp]
theorem coe_iteratedFDerivHolder (f : CkHolderSpaceOn k α U F) :
    ⇑f.iteratedFDerivHolder = (U : Set E).domRestrict (_root_.iteratedFDeriv ℝ k f) := by
  rw [← HolderSpace.coe_toBoundedContinuousFunction,
    toBoundedContinuousFunction_iteratedFDerivHolder, coe_iteratedFDeriv]
  rfl

/-- The `k`-th iterated Fréchet derivative of a `C^{k,α}` map on `U` is `α`-Hölder on `U`, with
constant its Hölder seminorm on `U`. -/
theorem holderOnWith_iteratedFDeriv (f : CkHolderSpaceOn k α U F) :
    HolderOnWith (nnHolderNorm α ((U : Set E).domRestrict (_root_.iteratedFDeriv ℝ k f))) α
      (_root_.iteratedFDeriv ℝ k f) U := by
  rw [← HolderWith.restrict_iff, ← coe_iteratedFDerivHolder]
  exact f.iteratedFDerivHolder.holderWith

/-- The `C^{k,α}` norm on `U` is the sum of the supremum norms on `U` of the iterated derivatives
through order `k` and the `α`-Hölder seminorm on `U` of the `k`-th iterated derivative. -/
theorem norm_eq (f : CkHolderSpaceOn k α U F) :
    ‖f‖ = ∑ i : Fin (k + 1), ‖f.iteratedFDeriv i‖ +
      nnHolderNorm α ((U : Set E).domRestrict (_root_.iteratedFDeriv ℝ k f)) := by
  rw [← norm_toJet, WithLp.prod_norm_eq_of_L1, PiLp.norm_eq_of_L1, Fin.sum_univ_castSucc,
    HolderSpace.norm_def, ← coe_iteratedFDerivHolder,
    ← HolderSpace.coe_toBoundedContinuousFunction, add_assoc]
  simp only [iteratedFDeriv, fieldL_castSucc, fieldL_last, iteratedFDerivHolder,
    WithLp.ofLp_fst, WithLp.ofLp_snd]

/-- The `C^{k,α}` norm on `U` is the sum of the supremum norms on `U` of the derivative fields
below order `k` and the norm of the Hölder field. -/
private theorem norm_eq_sum_add_norm_iteratedFDerivHolder (f : CkHolderSpaceOn k α U F) :
    ‖f‖ = ∑ j : Fin k, ‖f.iteratedFDeriv j.castSucc‖ + ‖f.iteratedFDerivHolder‖ := by
  rw [← norm_toJet, WithLp.prod_norm_eq_of_L1, PiLp.norm_eq_of_L1]
  simp only [iteratedFDeriv, fieldL_castSucc, iteratedFDerivHolder, WithLp.ofLp_fst,
    WithLp.ofLp_snd]

/-- The supremum norm on `U` of each iterated derivative field is controlled by the `C^{k,α}`
norm. -/
theorem norm_iteratedFDeriv_le (f : CkHolderSpaceOn k α U F) (i : Fin (k + 1)) :
    ‖f.iteratedFDeriv i‖ ≤ ‖f‖ := by
  rw [norm_eq]
  exact (Finset.single_le_sum (fun j _ ↦ norm_nonneg (f.iteratedFDeriv j))
    (Finset.mem_univ i)).trans (le_add_of_nonneg_right (NNReal.coe_nonneg _))

/-- Each iterated derivative through order `k` is pointwise controlled on `U` by the `C^{k,α}`
norm. -/
theorem norm_iteratedFDeriv_apply_le (f : CkHolderSpaceOn k α U F) {i : ℕ} (hi : i ≤ k)
    {x : E} (hx : x ∈ U) : ‖_root_.iteratedFDeriv ℝ i f x‖ ≤ ‖f‖ := by
  calc ‖_root_.iteratedFDeriv ℝ i f x‖
      = ‖f.iteratedFDeriv ⟨i, Nat.lt_succ_of_le hi⟩ ⟨x, hx⟩‖ := by rw [← iteratedFDeriv_eq]
    _ ≤ ‖f‖ := ((f.iteratedFDeriv _).norm_coe_le_norm _).trans (norm_iteratedFDeriv_le f _)

/-- The values of a `C^{k,α}` map on `U` are controlled by its `C^{k,α}` norm. -/
theorem norm_apply_le (f : CkHolderSpaceOn k α U F) (x : E) : ‖f x‖ ≤ ‖f‖ := by
  by_cases hx : x ∈ U
  · simpa using norm_iteratedFDeriv_apply_le f (Nat.zero_le k) hx
  · rw [apply_eq_zero_of_notMem f hx, norm_zero]
    exact norm_nonneg f

/-- The `α`-Hölder seminorm on `U` of the `k`-th iterated derivative is controlled by the
`C^{k,α}` norm. -/
theorem nnHolderNorm_iteratedFDeriv_le (f : CkHolderSpaceOn k α U F) :
    (nnHolderNorm α ((U : Set E).domRestrict (_root_.iteratedFDeriv ℝ k f)) : ℝ) ≤ ‖f‖ := by
  rw [norm_eq]
  exact le_add_of_nonneg_left (Finset.sum_nonneg fun j _ ↦ norm_nonneg _)

/-- The `i`-th derivative field, as a continuous linear map to bounded continuous fields on `U`.
It is bounded by the `C^{k,α}` norm pointwise, by `CkHolderSpaceOn.norm_iteratedFDeriv_le`. -/
def iteratedFDerivL (i : Fin (k + 1)) :
    CkHolderSpaceOn k α U F →L[ℝ] (U →ᵇ (E [×i]→L[ℝ] F)) :=
  (fieldL i).comp toJetL

@[simp]
theorem iteratedFDerivL_apply (i : Fin (k + 1)) (f : CkHolderSpaceOn k α U F) :
    iteratedFDerivL i f = f.iteratedFDeriv i := by
  rw [iteratedFDerivL, ContinuousLinearMap.comp_apply, toJetL_apply, iteratedFDeriv]

/-- The `k`-th derivative field, as a continuous linear map to the bounded Hölder space of `U`. -/
def iteratedFDerivHolderL : CkHolderSpaceOn k α U F →L[ℝ] HolderSpace α U (E [×k]→L[ℝ] F) :=
  (WithLp.sndL 1 ℝ _ _).comp toJetL

@[simp]
theorem iteratedFDerivHolderL_apply (f : CkHolderSpaceOn k α U F) :
    iteratedFDerivHolderL f = f.iteratedFDerivHolder := by
  rw [iteratedFDerivHolderL, ContinuousLinearMap.comp_apply, toJetL_apply, WithLp.sndL_apply,
    iteratedFDerivHolder, WithLp.ofLp_snd]

@[simp]
theorem iteratedFDeriv_zero (i : Fin (k + 1)) :
    (0 : CkHolderSpaceOn k α U F).iteratedFDeriv i = 0 := by
  simpa only [iteratedFDerivL_apply] using
    (iteratedFDerivL (α := α) (U := U) (F := F) i).map_zero

@[simp]
theorem iteratedFDeriv_add (f g : CkHolderSpaceOn k α U F) (i : Fin (k + 1)) :
    (f + g).iteratedFDeriv i = f.iteratedFDeriv i + g.iteratedFDeriv i := by
  simpa only [iteratedFDerivL_apply] using (iteratedFDerivL i).map_add f g

@[simp]
theorem iteratedFDeriv_smul (c : ℝ) (f : CkHolderSpaceOn k α U F) (i : Fin (k + 1)) :
    (c • f).iteratedFDeriv i = c • f.iteratedFDeriv i := by
  simpa only [iteratedFDerivL_apply] using (iteratedFDerivL i).map_smul c f

@[simp]
theorem iteratedFDerivHolder_zero :
    (0 : CkHolderSpaceOn k α U F).iteratedFDerivHolder = 0 := by
  simpa only [iteratedFDerivHolderL_apply] using
    (iteratedFDerivHolderL (k := k) (α := α) (U := U) (F := F)).map_zero

@[simp]
theorem iteratedFDerivHolder_add (f g : CkHolderSpaceOn k α U F) :
    (f + g).iteratedFDerivHolder = f.iteratedFDerivHolder + g.iteratedFDerivHolder := by
  simpa only [iteratedFDerivHolderL_apply] using iteratedFDerivHolderL.map_add f g

@[simp]
theorem iteratedFDerivHolder_smul (c : ℝ) (f : CkHolderSpaceOn k α U F) :
    (c • f).iteratedFDerivHolder = c • f.iteratedFDerivHolder := by
  simpa only [iteratedFDerivHolderL_apply] using iteratedFDerivHolderL.map_smul c f

/-- On `U`, the underlying function is the order-zero derivative field. -/
private theorem apply_eq_iteratedFDeriv_zero (f : CkHolderSpaceOn k α U F) {x : E} (hx : x ∈ U) :
    f x = (f.iteratedFDeriv 0 ⟨x, hx⟩).curry0 :=
  Function.extend_val_apply (g := fun y : U ↦ (f.iteratedFDeriv 0 y).curry0) hx

@[simp]
theorem coe_zero : ⇑(0 : CkHolderSpaceOn k α U F) = 0 := by
  funext x
  by_cases hx : x ∈ U
  · rw [apply_eq_iteratedFDeriv_zero _ hx, iteratedFDeriv_zero]
    rfl
  · exact apply_eq_zero_of_notMem _ hx

@[simp]
theorem coe_add (f g : CkHolderSpaceOn k α U F) : ⇑(f + g) = f + g := by
  funext x
  by_cases hx : x ∈ U
  · rw [Pi.add_apply, apply_eq_iteratedFDeriv_zero _ hx, apply_eq_iteratedFDeriv_zero f hx,
      apply_eq_iteratedFDeriv_zero g hx, iteratedFDeriv_add]
    rfl
  · rw [Pi.add_apply, apply_eq_zero_of_notMem _ hx, apply_eq_zero_of_notMem f hx,
      apply_eq_zero_of_notMem g hx, add_zero]

@[simp]
theorem coe_smul (c : ℝ) (f : CkHolderSpaceOn k α U F) : ⇑(c • f) = c • ⇑f := by
  funext x
  by_cases hx : x ∈ U
  · rw [Pi.smul_apply, apply_eq_iteratedFDeriv_zero _ hx, apply_eq_iteratedFDeriv_zero f hx,
      iteratedFDeriv_smul]
    rfl
  · rw [Pi.smul_apply, apply_eq_zero_of_notMem _ hx, apply_eq_zero_of_notMem f hx, smul_zero]

/-- A bounded continuous field on `U` built from a function continuous on `U` with a uniform
bound on `U`. -/
private def bcfOf {G : Type*} [NormedAddCommGroup G] (g : E → G) (hg : ContinuousOn g U)
    (hbdd : ∃ C, ∀ x ∈ U, ‖g x‖ ≤ C) : U →ᵇ G :=
  BoundedContinuousFunction.ofNormedAddCommGroup ((U : Set E).domRestrict g)
    (continuousOn_iff_continuous_domRestrict.mp hg) hbdd.choose fun x ↦ hbdd.choose_spec x x.2

omit [NormedSpace ℝ E] in
private theorem coe_bcfOf {G : Type*} [NormedAddCommGroup G] (g : E → G)
    (hg : ContinuousOn g U) (hbdd : ∃ C, ∀ x ∈ U, ‖g x‖ ≤ C) :
    ⇑(bcfOf g hg hbdd) = (U : Set E).domRestrict g :=
  rfl

omit [NormedSpace ℝ E] in
private theorem bcfOf_apply {G : Type*} [NormedAddCommGroup G] (g : E → G)
    (hg : ContinuousOn g U) (hbdd : ∃ C, ∀ x ∈ U, ‖g x‖ ≤ C) (x : U) :
    bcfOf g hg hbdd x = g x :=
  rfl

/-- The jet of iterated derivatives on `U` of a function `C^k` on `U` with bounded derivatives
through order `k` on `U` and `α`-Hölder `k`-th derivative on `U`. -/
private def jetOf (f : E → F) (hf : ContDiffOn ℝ k f U)
    (hbdd : ∀ i ≤ k, ∃ C, ∀ x ∈ U, ‖_root_.iteratedFDeriv ℝ i f x‖ ≤ C)
    (hholder : ∃ C, HolderOnWith C α (_root_.iteratedFDeriv ℝ k f) U) : CkHolderJet k α U E F :=
  WithLp.toLp 1
    (WithLp.toLp 1 fun j : Fin k ↦ bcfOf (_root_.iteratedFDeriv ℝ j f)
        ((hf.continuousOn_iteratedFDerivWithin (by exact_mod_cast j.2.le)
          U.isOpen.uniqueDiffOn).congr
            fun _ hx ↦ (iteratedFDerivWithin_of_isOpen _ U.isOpen hx).symm)
        (hbdd j j.2.le),
      HolderSpace.ofBoundedContinuousFunction
        (bcfOf (_root_.iteratedFDeriv ℝ k f)
          ((hf.continuousOn_iteratedFDerivWithin le_rfl U.isOpen.uniqueDiffOn).congr
            fun _ hx ↦ (iteratedFDerivWithin_of_isOpen _ U.isOpen hx).symm) (hbdd k le_rfl))
        (by rw [coe_bcfOf]; exact hholder.choose_spec.holderWith.memHolder))

private theorem fieldL_jetOf (f : E → F) (hf : ContDiffOn ℝ k f U)
    (hbdd : ∀ i ≤ k, ∃ C, ∀ x ∈ U, ‖_root_.iteratedFDeriv ℝ i f x‖ ≤ C)
    (hholder : ∃ C, HolderOnWith C α (_root_.iteratedFDeriv ℝ k f) U) (i : Fin (k + 1))
    (x : U) : fieldL i (jetOf f hf hbdd hholder) x = _root_.iteratedFDeriv ℝ i f x := by
  induction i using Fin.lastCases with
  | last =>
    rw [fieldL_last]
    simp only [jetOf, WithLp.ofLp_toLp,
      HolderSpace.toBoundedContinuousFunction_ofBoundedContinuousFunction, bcfOf_apply]
    rfl
  | cast j =>
    rw [fieldL_castSucc]
    simp only [jetOf, WithLp.ofLp_toLp, bcfOf_apply]
    rfl

private theorem isJetGraph_jetOf (f : E → F) (hf : ContDiffOn ℝ k f U)
    (hbdd : ∀ i ≤ k, ∃ C, ∀ x ∈ U, ‖_root_.iteratedFDeriv ℝ i f x‖ ≤ C)
    (hholder : ∃ C, HolderOnWith C α (_root_.iteratedFDeriv ℝ k f) U) :
    IsJetGraph (jetOf f hf hbdd hholder) := fun j x ↦ by
  have hfx : ContDiffAt ℝ k f x := hf.contDiffAt (U.isOpen.mem_nhds x.2)
  have h := (hfx.differentiableAt_iteratedFDeriv (m := j) (by exact_mod_cast j.2)).hasFDerivAt
  rw [fderiv_iteratedFDeriv, Function.comp_apply] at h
  rw [fieldL_jetOf, curryLeftL_apply]
  exact h.congr_of_eventuallyEq (eventuallyEq_of_mem (U.isOpen.mem_nhds x.2) fun y hy ↦
    (Function.extend_val_apply (SetLike.mem_coe.1 hy)).trans
      (fieldL_jetOf f hf hbdd hholder j.castSucc ⟨y, hy⟩))

/-- Build a `C^{k,α}` map on `U` from a function that is `C^k` on `U`, whose iterated derivatives
through order `k` are bounded on `U`, and whose `k`-th iterated derivative is `α`-Hölder on `U`.
Its underlying function is the given one on `U` and zero off `U`. -/
def ofContDiffOn (f : E → F) (hf : ContDiffOn ℝ k f U)
    (hbdd : ∀ i ≤ k, ∃ C, ∀ x ∈ U, ‖_root_.iteratedFDeriv ℝ i f x‖ ≤ C)
    (hholder : ∃ C, HolderOnWith C α (_root_.iteratedFDeriv ℝ k f) U) :
    CkHolderSpaceOn k α U F :=
  mk (jetOf f hf hbdd hholder) (isJetGraph_jetOf f hf hbdd hholder)

@[simp]
theorem coe_ofContDiffOn (f : E → F) (hf : ContDiffOn ℝ k f U)
    (hbdd : ∀ i ≤ k, ∃ C, ∀ x ∈ U, ‖_root_.iteratedFDeriv ℝ i f x‖ ≤ C)
    (hholder : ∃ C, HolderOnWith C α (_root_.iteratedFDeriv ℝ k f) U) :
    ⇑(ofContDiffOn f hf hbdd hholder) = (U : Set E).indicator f := by
  funext x
  rw [← toFun_eq_coe]
  by_cases hx : x ∈ U
  · rw [indicator_of_mem hx, toFun_eq_coe, apply_eq_iteratedFDeriv_zero _ hx, iteratedFDeriv,
      ofContDiffOn, toJet_mk]
    exact (congrArg (fun m ↦ m 0) (fieldL_jetOf f hf hbdd hholder 0 ⟨x, hx⟩)).trans
      (iteratedFDeriv_zero_apply _)
  · rw [indicator_of_notMem hx, toFun_apply_of_notMem _ hx]

/-- The derivative identities are closed under uniform convergence of the fields on `U`. -/
private theorem isClosed_isJetGraph : IsClosed {J : CkHolderJet k α U E F | IsJetGraph J} := by
  rw [← isSeqClosed_iff_isClosed]
  intro J j hJ hjlim m x
  have hconv (i : Fin (k + 1)) : TendstoUniformlyOn
      (fun n ↦ Function.extend Subtype.val (fieldL i (J n) : U → E [×i]→L[ℝ] F) 0)
      (Function.extend Subtype.val (fieldL i j : U → E [×i]→L[ℝ] F) 0) atTop U := by
    have h := BoundedContinuousFunction.tendsto_iff_tendstoUniformly.mp
      (((fieldL (k := k) (α := α) (X := U) (E := E) (F := F) i).continuous.tendsto j).comp hjlim)
    rw [tendstoUniformlyOn_iff_tendstoUniformly_comp_coe]
    simp only [Function.comp_def, Function.extend_val_apply, SetLike.coe_mem]
    exact h
  have hderiv (n : ℕ) (y : E) (hy : y ∈ U) : HasFDerivAt
      (Function.extend Subtype.val (fieldL m.castSucc (J n) : U → E [×m]→L[ℝ] F) 0)
      (curryLeftL E F m
        (Function.extend Subtype.val (fieldL m.succ (J n) : U → E [×m + 1]→L[ℝ] F) 0 y)) y := by
    have h : IsJetGraph (J n) := hJ n
    rw [Function.extend_val_apply (SetLike.mem_coe.1 hy)]
    exact h m ⟨y, hy⟩
  have h := hasFDerivAt_of_tendstoUniformlyOn (l := atTop) U.isOpen
    (g := Function.extend Subtype.val (fieldL m.castSucc j : U → E [×m]→L[ℝ] F) 0)
    (g' := fun y ↦ curryLeftL E F m
      (Function.extend Subtype.val (fieldL m.succ j : U → E [×m + 1]→L[ℝ] F) 0 y))
    ((curryLeftL E F m).uniformContinuous.comp_tendstoUniformlyOn (hconv m.succ)) hderiv
    (fun y hy ↦ (hconv m.castSucc).tendsto_at hy) x.2
  rwa [Function.extend_val_apply x.2] at h

/-- `C^{k,α}` maps on an open set into a Banach space form a Banach space. -/
instance instCompleteSpace [CompleteSpace F] : CompleteSpace (CkHolderSpaceOn k α U F) := by
  unfold CkHolderSpaceOn
  exact isClosed_isJetGraph.completeSpace_coe

attribute [irreducible] instNormedAddCommGroup instNormedSpace _root_.TauCeti.CkHolderSpaceOn

/-- The derivative fields of a map built by `CkHolderSpaceOn.ofContDiffOn` are the iterated
derivatives of the given function on `U`. -/
theorem iteratedFDeriv_ofContDiffOn_apply (f : E → F) (hf : ContDiffOn ℝ k f U)
    (hbdd : ∀ i ≤ k, ∃ C, ∀ x ∈ U, ‖_root_.iteratedFDeriv ℝ i f x‖ ≤ C)
    (hholder : ∃ C, HolderOnWith C α (_root_.iteratedFDeriv ℝ k f) U) (i : Fin (k + 1))
    (x : U) :
    (ofContDiffOn f hf hbdd hholder).iteratedFDeriv i x = _root_.iteratedFDeriv ℝ i f x := by
  rw [← iteratedFDeriv_eq, coe_ofContDiffOn]
  exact iteratedFDeriv_eq_of_eqOn U.isOpen (fun y hy ↦ indicator_of_mem hy f) i x.2

/-- The norm of a `C^{k,α}` map `g` on `V` that agrees on `V` with a function `f` is at most
`∑ i, C i + H`, where the `C i ≥ 0` bound the iterated derivatives of `f` through order `k` on `V`
and `H` is an `α`-Hölder constant on `V` of its `k`-th derivative. -/
private theorem norm_le_of_eqOn {V : Opens E} {g : CkHolderSpaceOn k α V F} {f : E → F}
    (hgf : EqOn g f V) {C : Fin (k + 1) → ℝ} (hC0 : ∀ i, 0 ≤ C i)
    (hC : ∀ (i : Fin (k + 1)), ∀ x ∈ V, ‖_root_.iteratedFDeriv ℝ i f x‖ ≤ C i) {H : ℝ≥0}
    (hH : HolderOnWith H α (_root_.iteratedFDeriv ℝ k f) V) : ‖g‖ ≤ ∑ i, C i + H := by
  rw [norm_eq]
  gcongr with i
  · refine (BoundedContinuousFunction.norm_le (hC0 i)).2 fun x ↦ ?_
    rw [← iteratedFDeriv_eq, iteratedFDeriv_eq_of_eqOn V.isOpen hgf _ x.2]
    exact hC i x x.2
  · rw [show (V : Set E).domRestrict (_root_.iteratedFDeriv ℝ k g) =
        (V : Set E).domRestrict (_root_.iteratedFDeriv ℝ k f) from
          funext fun x ↦ iteratedFDeriv_eq_of_eqOn V.isOpen hgf k x.2]
    exact_mod_cast (HolderWith.restrict_iff.mpr hH).nnholderNorm_le

section Restrict

variable {V : Opens E}

/-- Restriction of a `C^{k,α}` map on `U` to a smaller open set `V`, as a continuous linear map
of norm at most one. -/
def restrictL (h : V ≤ U) : CkHolderSpaceOn k α U F →L[ℝ] CkHolderSpaceOn k α V F :=
  LinearMap.mkContinuous
    { toFun f := ofContDiffOn f (f.contDiffOn.mono (SetLike.coe_subset_coe.2 h))
        (fun _ hi ↦ ⟨‖f‖, fun _ hx ↦ f.norm_iteratedFDeriv_apply_le hi (h hx)⟩)
        ⟨_, f.holderOnWith_iteratedFDeriv.mono (SetLike.coe_subset_coe.2 h)⟩
      map_add' f g := ext fun x hx ↦ by simp [indicator_of_mem hx]
      map_smul' c f := ext fun x hx ↦ by simp [indicator_of_mem hx] }
    1 fun f ↦ by
      rw [one_mul, norm_eq f]
      exact norm_le_of_eqOn (fun x hx ↦ by simp [indicator_of_mem hx])
        (fun i ↦ norm_nonneg (f.iteratedFDeriv i))
        (fun i x hx ↦ (congrArg norm (iteratedFDeriv_eq f i ⟨x, h hx⟩)).trans_le
          ((f.iteratedFDeriv i).norm_coe_le_norm _))
        (f.holderOnWith_iteratedFDeriv.mono (SetLike.coe_subset_coe.2 h))

/-- The restriction of a `C^{k,α}` map on `U` to `V` agrees with it on `V` and vanishes off `V`. -/
@[simp]
theorem coe_restrictL (h : V ≤ U) (f : CkHolderSpaceOn k α U F) :
    ⇑(restrictL h f) = (V : Set E).indicator f :=
  coe_ofContDiffOn _ _ _ _

/-- The derivative fields of a restriction are the restrictions of the derivative fields. -/
theorem iteratedFDeriv_restrictL_apply (h : V ≤ U) (f : CkHolderSpaceOn k α U F)
    (i : Fin (k + 1)) (x : V) :
    (restrictL h f).iteratedFDeriv i x = f.iteratedFDeriv i ⟨x, h x.2⟩ :=
  (iteratedFDeriv_ofContDiffOn_apply _ _ _ _ i x).trans (iteratedFDeriv_eq f i ⟨x, h x.2⟩)

/-- Restriction to a smaller open set has norm at most one. -/
theorem norm_restrictL_le (h : V ≤ U) :
    ‖restrictL (k := k) (α := α) (F := F) h‖ ≤ 1 :=
  LinearMap.mkContinuous_norm_le _ zero_le_one _

end Restrict

section Inclusion

variable {β : ℝ≥0} [BoundedSpace U]

/-- **The inclusion of Hölder spaces of different exponents.** On a bounded open set `U`, a
`C^{k,α}` map on `U` is `C^{k,β}` on `U` for every `β ≤ α`, and the inclusion is a bounded linear
map, of norm at most `max 1 (D^(α - β))` with `D` the diameter of `U`. -/
def inclusionL (hβα : β ≤ α) : CkHolderSpaceOn k α U F →L[ℝ] CkHolderSpaceOn k β U F :=
  LinearMap.mkContinuous
    { toFun f := ofContDiffOn f f.contDiffOn
        (fun _ hi ↦ ⟨‖f‖, fun _ hx ↦ f.norm_iteratedFDeriv_apply_le hi hx⟩)
        ⟨_, HolderWith.restrict_iff.mp
          (f.holderOnWith_iteratedFDeriv.holderWith.of_le Metric.edist_le_diam_univ hβα)⟩
      map_add' f g := ext fun x hx ↦ by simp [indicator_of_mem hx]
      map_smul' c f := ext fun x hx ↦ by simp [indicator_of_mem hx] }
    (max 1 (((Metric.diam (univ : Set U)).toNNReal : ℝ) ^ ((α : ℝ) - β))) fun f ↦ by
      have key (g : CkHolderSpaceOn k β U F) (hg : ⇑g = ⇑f) :
          ‖g‖ ≤ max 1 (((Metric.diam (univ : Set U)).toNNReal : ℝ) ^ ((α : ℝ) - β)) * ‖f‖ := by
        have hfield (i : Fin (k + 1)) : g.iteratedFDeriv i = f.iteratedFDeriv i := by
          ext1 x
          rw [← iteratedFDeriv_eq, ← iteratedFDeriv_eq, hg]
        have hH : g.iteratedFDerivHolder = HolderSpace.inclusionL hβα f.iteratedFDerivHolder :=
          HolderSpace.ext fun x ↦ by
            simp only [HolderSpace.inclusionL_apply, coe_iteratedFDerivHolder, hg]
        rw [norm_eq_sum_add_norm_iteratedFDerivHolder,
          norm_eq_sum_add_norm_iteratedFDerivHolder f, hH, mul_add]
        simp only [hfield]
        gcongr ?_ + ?_
        · exact le_mul_of_one_le_left (Finset.sum_nonneg fun _ _ ↦ norm_nonneg _)
            (le_max_left _ _)
        · exact (HolderSpace.inclusionL hβα).le_of_opNorm_le (HolderSpace.norm_inclusionL_le hβα) _
      exact key _ (by rw [LinearMap.coe_mk, AddHom.coe_mk, coe_ofContDiffOn, indicator_coe])

/-- The inclusion between exponents does not change the underlying function. -/
@[simp]
theorem coe_inclusionL (hβα : β ≤ α) (f : CkHolderSpaceOn k α U F) :
    ⇑(inclusionL hβα f) = ⇑f := by
  rw [inclusionL, LinearMap.mkContinuous_apply, LinearMap.coe_mk, AddHom.coe_mk,
    coe_ofContDiffOn, indicator_coe]

/-- The inclusion between exponents does not change the derivative fields. -/
@[simp]
theorem iteratedFDeriv_inclusionL (hβα : β ≤ α) (f : CkHolderSpaceOn k α U F)
    (i : Fin (k + 1)) : (inclusionL hβα f).iteratedFDeriv i = f.iteratedFDeriv i := by
  ext1 x
  rw [← iteratedFDeriv_eq, ← iteratedFDeriv_eq, coe_inclusionL]

/-- The inclusion between exponents is bounded with norm at most `max 1 (D^(α - β))`, with `D`
the diameter of `U`. -/
theorem norm_inclusionL_le (hβα : β ≤ α) :
    ‖inclusionL (k := k) (U := U) (F := F) hβα‖ ≤
      max 1 (((Metric.diam (univ : Set U)).toNNReal : ℝ) ^ ((α : ℝ) - β)) :=
  LinearMap.mkContinuous_norm_le _ (zero_le_one.trans (le_max_left _ _)) _

end Inclusion

end CkHolderSpaceOn

namespace CkHolderSpace

variable {k α F}

/-- Restriction of a bounded `C^{k,α}` map on the whole space to an open set `U`, as a continuous
linear map of norm at most one. -/
def restrictL : CkHolderSpace k α E F →L[ℝ] CkHolderSpaceOn k α U F :=
  LinearMap.mkContinuous
    { toFun f := CkHolderSpaceOn.ofContDiffOn f f.contDiff.contDiffOn
        (fun _ hi ↦ ⟨‖f‖, fun x _ ↦ f.norm_iteratedFDeriv_apply_le hi x⟩)
        ⟨_, f.memHolder_iteratedFDeriv.holderWith.holderOnWith U⟩
      map_add' f g := CkHolderSpaceOn.ext fun x hx ↦ by simp [indicator_of_mem hx]
      map_smul' c f := CkHolderSpaceOn.ext fun x hx ↦ by simp [indicator_of_mem hx] }
    1 fun f ↦ by
      rw [one_mul, norm_eq f]
      exact CkHolderSpaceOn.norm_le_of_eqOn (fun x hx ↦ by simp [indicator_of_mem hx])
        (fun i ↦ norm_nonneg (f.iteratedFDeriv i))
        (fun i x _ ↦ (congrArg norm (iteratedFDeriv_eq f i x)).trans_le
          ((f.iteratedFDeriv i).norm_coe_le_norm x))
        (f.memHolder_iteratedFDeriv.holderWith.holderOnWith U)

/-- The restriction to `U` of a bounded `C^{k,α}` map agrees with it on `U` and vanishes off
`U`. -/
@[simp]
theorem coe_restrictL (f : CkHolderSpace k α E F) :
    ⇑(restrictL U f) = (U : Set E).indicator f :=
  CkHolderSpaceOn.coe_ofContDiffOn _ _ _ _

/-- The derivative fields of the restriction to `U` are the restrictions of the derivative
fields. -/
theorem iteratedFDeriv_restrictL_apply (f : CkHolderSpace k α E F) (i : Fin (k + 1)) (x : U) :
    (restrictL U f).iteratedFDeriv i x = f.iteratedFDeriv i x :=
  (CkHolderSpaceOn.iteratedFDeriv_ofContDiffOn_apply _ _ _ _ i x).trans (iteratedFDeriv_eq f i x)

/-- Restriction to an open set has norm at most one. -/
theorem norm_restrictL_le : ‖restrictL (k := k) (α := α) (F := F) U‖ ≤ 1 :=
  LinearMap.mkContinuous_norm_le _ zero_le_one _

end CkHolderSpace

end TauCeti

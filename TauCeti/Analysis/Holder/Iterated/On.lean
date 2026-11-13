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
import TauCeti.Analysis.Calculus.UniformLimitsDeriv
import TauCeti.Analysis.Holder.Iterated.Jet
import TauCeti.Analysis.Holder.JetBounds
import TauCeti.Topology.EMetricSpace.Lipschitz
import TauCeti.Topology.MetricSpace.Bounded
import TauCeti.Topology.MetricSpace.Holder

/-!
# The Hölder spaces `C^{k,α}(Ω)` on an open set

For an open set `Ω` of a real normed space `E`, an integer `k ≥ 0` and an exponent `α`, this file
constructs the normed space `C^{k,α}(Ω, F)` of maps `Ω → F` which are `k` times continuously
differentiable, whose iterated Fréchet derivatives through order `k` are bounded on `Ω`, and whose
`k`-th iterated derivative is `α`-Hölder on `Ω`, with the norm

`‖f‖ = ∑_{i ≤ k} sup_{x ∈ Ω} ‖D^i f x‖ + [D^k f]_{α, Ω}`.

It is a Banach space when `F` is. Both the suprema and the Hölder seminorm are taken over all of
`Ω`, so this is the space of maps on `Ω` with globally finite `C^{k,α}` norm. Nothing here
extends an element or its derivatives to the boundary of `Ω`: identifying this space with the
space `C^{k,α}(closure Ω)` of Gilbarg and Trudinger, whose norm is the same expression, requires
continuous extension of the lower derivatives to `closure Ω`, which needs further assumptions on
`Ω`. When `Ω` is the whole space, its defining conditions are those of the space
`TauCeti.CkHolderSpace` of bounded `C^{k,α}` maps.

Since the Hölder seminorm compares values at points of `Ω` that may be far apart within `Ω`, a map
can be smooth with all derivatives bounded on `Ω` and still fail to be Hölder on `Ω`: on
`(-1, 0) ∪ (0, 1)` the sign function is locally constant, but its Hölder quotients blow up across
`0`. Accordingly the inclusion `C^{k+1,α}(Ω) ⊆ C^{k,α}(Ω)` is stated
for convex `Ω` (`TauCeti.CkHolderOnSpace.succInclusionL`), where the mean value inequality bounds
the Hölder seminorm of `D^k f` by the supremum norms of `D^k f` and `D^{k+1} f`.

An element is represented, as for `TauCeti.CkHolderSpace`, by its family of derivative fields on
`Ω`: bounded continuous fields `Ω →ᵇ (E [×i]→L[ℝ] F)` for `i < k` and a bounded Hölder field of
order `k`, each the Fréchet derivative of the previous one, curried on the left. The underlying map
is a map on `Ω`, so no values outside `Ω` are recorded; the derivatives of any map `g : E → F`
which agrees with an element on `Ω` are its derivative fields
(`TauCeti.CkHolderOnSpace.iteratedFDerivWithin_eq`).

## Main declarations

* `TauCeti.CkHolderOnSpace k α Ω F`: the space `C^{k,α}(Ω, F)`.
* `TauCeti.CkHolderOnSpace.iteratedFDeriv` and `TauCeti.CkHolderOnSpace.iteratedFDerivHolder`: the
  derivative fields on `Ω`, identified with Mathlib's `iteratedFDerivWithin` by
  `TauCeti.CkHolderOnSpace.iteratedFDerivWithin_eq`.
* `TauCeti.CkHolderOnSpace.contDiffOn`: every extension of an element is `C^k` on `Ω`;
  `TauCeti.CkHolderOnSpace.ofContDiffOn` is the converse constructor.
* `TauCeti.CkHolderOnSpace.norm_eq`: the norm is the sum of the supremum norms of the derivatives
  through order `k` and the `α`-Hölder seminorm of the `k`-th derivative.
* `TauCeti.CkHolderOnSpace.instCompleteSpace`: completeness when the codomain is complete.
* `TauCeti.CkHolderOnSpace.restrictL`: restriction to a smaller open set, of norm at most one.
* `TauCeti.CkHolderOnSpace.inclusionL`: for bounded `Ω`, the inclusion
  `C^{k,α}(Ω) ⊆ C^{k,β}(Ω)` for `β ≤ α`.
* `TauCeti.CkHolderOnSpace.succInclusionL`: for convex `Ω` and `α ≤ 1`, the inclusion
  `C^{k+1,α}(Ω) ⊆ C^{k,α}(Ω)`, of norm at most `3`.

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

/-- Shortcut instance for bounded continuous fields of `n`-multilinear maps on `Ω`. Without it,
instance search for the module structure of `ℓ¹` products of these fields indexed by the order `n`
exceeds the default synthesis depth. It is local, and no public statement below mentions it. -/
local instance CkHolderOnSpace.instNormedAddCommGroupBoundedContinuousFunction (n : ℕ) :
    NormedAddCommGroup (Ω →ᵇ (E [×n]→L[ℝ] F)) :=
  inferInstance

/-- Shortcut instance for bounded continuous fields of `n`-multilinear maps on `Ω`, needed for
continuous linear maps into these fields indexed by the order `n`. It is local for the same
reason. -/
local instance CkHolderOnSpace.instNormedSpaceBoundedContinuousFunction (n : ℕ) :
    NormedSpace ℝ (Ω →ᵇ (E [×n]→L[ℝ] F)) :=
  inferInstance

/-- The space `C^{k,α}(Ω, F)` of maps on the open set `Ω` which are `k` times continuously
differentiable with bounded derivatives through order `k` and whose `k`-th iterated derivative is
`α`-Hölder on `Ω`. Its norm is

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
        HasFDerivAt (Function.extend ((↑) : Ω → E) (field j.castSucc J : Ω → E [×j]→L[ℝ] F) 0)
          (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (j + 1) ↦ E) F
            (field j.succ J x)) (x : E)}
      zero_mem' := fun j x ↦ by
        simp only [map_zero, FunLike.coe_zero, Pi.zero_apply]
        rw [show Function.extend ((↑) : Ω → E) (0 : Ω → E [×j]→L[ℝ] F) 0 = 0 from by
          simp]
        exact hasFDerivAt_const (x := (x : E)) (c := (0 : E [×j]→L[ℝ] F))
      add_mem' := fun {J K} hJ hK j x ↦ by
        simp only [Set.mem_ofPred_eq, map_add, FunLike.coe_add,
          Pi.add_apply] at hJ hK ⊢
        rw [← add_zero (0 : E → E [×j]→L[ℝ] F), Function.extend_add]
        exact (hJ j x).add (hK j x)
      smul_mem' := fun c {J} hJ j x ↦ by
        simp only [Set.mem_ofPred_eq, map_smul, FunLike.coe_smul] at hJ ⊢
        rw [← smul_zero c, Function.extend_smul]
        exact (hJ j x).const_smul c }
  graph

namespace CkHolderOnSpace

variable {k α Ω F}

open HolderJet

/-- The extension by zero of a map on `Ω` to the whole space. Only its germs at points of `Ω`
matter below. -/
private def extend {G : Type*} [Zero G] (g : Ω → G) : E → G :=
  Function.extend ((↑) : Ω → E) g 0

omit [NormedSpace ℝ E] in
private theorem extend_coe {G : Type*} [Zero G] (g : Ω → G) (x : Ω) : extend g (x : E) = g x :=
  Subtype.val_injective.extend_apply g 0 x

omit [NormedSpace ℝ E] in
private theorem extend_of_mem {G : Type*} [Zero G] (g : Ω → G) {y : E} (hy : y ∈ Ω) :
    extend g y = g ⟨y, hy⟩ :=
  extend_coe g ⟨y, hy⟩

omit [NormedSpace ℝ E] in
/-- Near a point of `Ω`, the extension by zero of a map on `Ω` agrees with every map which
restricts to it. -/
private theorem extend_eventuallyEq {G : Type*} [Zero G] {g : Ω → G} {h : E → G}
    (hg : ∀ y : Ω, h y = g y) (x : Ω) : extend g =ᶠ[𝓝 (x : E)] h :=
  Filter.mem_of_superset (Ω.isOpen.mem_nhds x.2) fun y hy ↦ by
    simp only [Set.mem_ofPred_eq]
    rw [extend_of_mem _ hy]
    exact (hg ⟨y, hy⟩).symm

/-- The derivative identities of a jet: each field below order `k` has the next field, curried on
the left, as its Fréchet derivative at every point of `Ω`. -/
private def IsJetGraph (J : HolderJet k α Ω E F) : Prop :=
  ∀ (j : Fin k) (x : Ω), HasFDerivAt (extend (fieldL j.castSucc J : Ω → E [×j]→L[ℝ] F))
    (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (j + 1) ↦ E) F (fieldL j.succ J x)) (x : E)

/-- Elements are the jets satisfying the derivative identities. This is the identity map: the
carrier of `CkHolderOnSpace` states the identities through its local `field`, which is `fieldL`,
and through `Function.extend`, which is `extend`. -/
private def equivSubtype : CkHolderOnSpace k α Ω F ≃ {J : HolderJet k α Ω E F // IsJetGraph J} :=
  Equiv.refl _

/-- The underlying jet of an element. -/
private def toJet (f : CkHolderOnSpace k α Ω F) : HolderJet k α Ω E F := (equivSubtype f).1

/-- An element from a jet satisfying the derivative identities. -/
private def mk (J : HolderJet k α Ω E F) (hJ : IsJetGraph J) : CkHolderOnSpace k α Ω F :=
  equivSubtype.symm ⟨J, hJ⟩

private theorem toJet_injective :
    Function.Injective (toJet (k := k) (α := α) (Ω := Ω) (F := F)) :=
  fun _ _ h ↦ equivSubtype.injective (Subtype.ext h)

private theorem toJet_mk (J : HolderJet k α Ω E F) (hJ) : toJet (mk J hJ) = J := by
  rw [toJet, mk, Equiv.apply_symm_apply]

private theorem hasFDerivAt_fieldL (f : CkHolderOnSpace k α Ω F) (j : Fin k) (x : Ω) :
    HasFDerivAt (extend (fieldL j.castSucc (toJet f) : Ω → E [×j]→L[ℝ] F))
      (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (j + 1) ↦ E) F
        (fieldL j.succ (toJet f) x)) (x : E) :=
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
private def toJetL : CkHolderOnSpace k α Ω F →L[ℝ] HolderJet k α Ω E F := by
  unfold CkHolderOnSpace
  exact Submodule.subtypeL _

private theorem toJetL_apply (f : CkHolderOnSpace k α Ω F) : toJetL f = toJet f :=
  rfl

/-- The bounded continuous `i`-th derivative field on `Ω` of an element of `C^{k,α}(Ω)`, for
`i ≤ k`. It agrees with Mathlib's `iteratedFDerivWithin` by
`CkHolderOnSpace.iteratedFDerivWithin_eq`. -/
def iteratedFDeriv (f : CkHolderOnSpace k α Ω F) (i : Fin (k + 1)) : Ω →ᵇ (E [×i]→L[ℝ] F) :=
  fieldL i (toJet f)

/-- The `k`-th derivative field of an element of `C^{k,α}(Ω)`, as an element of the bounded
Hölder space on `Ω`. -/
def iteratedFDerivHolder (f : CkHolderOnSpace k α Ω F) : HolderSpace α Ω (E [×k]→L[ℝ] F) :=
  (toJet f).ofLp.2

/-- The underlying map on `Ω` of an element of `C^{k,α}(Ω)`: its order-zero derivative field,
evaluated on the empty tuple. Use the coercion `⇑f` instead. -/
def toFun (f : CkHolderOnSpace k α Ω F) (x : Ω) : F :=
  (f.iteratedFDeriv ⟨0, k.succ_pos⟩ x).curry0

/-- The formal Taylor series recorded by an element, extended by zero off `Ω` and truncated after
order `k`. -/
private def series (f : CkHolderOnSpace k α Ω F) (x : E) : FormalMultilinearSeries ℝ E F :=
  fun m ↦ if h : m < k + 1 then extend (f.iteratedFDeriv ⟨m, h⟩) x else 0

private theorem series_of_lt (f : CkHolderOnSpace k α Ω F) (x : E) {m : ℕ} (h : m < k + 1) :
    series f x m = extend (f.iteratedFDeriv ⟨m, h⟩) x := by
  simp [series, h]

/-- The recorded derivative fields form a Taylor series up to order `k` on `Ω` for the extension by
zero of the underlying map. -/
private theorem hasFTaylorSeriesUpToOn (f : CkHolderOnSpace k α Ω F) :
    HasFTaylorSeriesUpToOn k (extend f.toFun) (series f) Ω where
  zero_eq x hx := by
    rw [series_of_lt f x k.succ_pos, extend_of_mem _ hx, extend_of_mem _ hx, toFun]
  fderivWithin m hm x hx := by
    have hmk : m < k := by exact_mod_cast hm
    have hfun : (fun y ↦ series f y m) =
        extend (fieldL (⟨m, hmk⟩ : Fin k).castSucc (toJet f) : Ω → E [×m]→L[ℝ] F) :=
      funext fun y ↦ series_of_lt f y (by omega)
    rw [hfun, series_of_lt f x (by omega), extend_of_mem _ hx]
    exact (hasFDerivAt_fieldL f ⟨m, hmk⟩ ⟨x, hx⟩).hasFDerivWithinAt
  cont m hm := by
    have hmk : m < k + 1 := by
      have : m ≤ k := by exact_mod_cast hm
      omega
    have hfun : (fun y ↦ series f y m) = extend (f.iteratedFDeriv ⟨m, hmk⟩ : Ω → _) :=
      funext fun y ↦ series_of_lt f y hmk
    rw [hfun, continuousOn_iff_continuous_domRestrict]
    convert (f.iteratedFDeriv ⟨m, hmk⟩).continuous using 1
    funext y
    exact extend_coe _ y

/-- The `i`-th iterated derivative within `Ω` of every map which restricts to an element of
`C^{k,α}(Ω)` is the recorded `i`-th derivative field. -/
private theorem iteratedFDerivWithin_eq_of_eq (f : CkHolderOnSpace k α Ω F) {g : E → F}
    (hg : ∀ x : Ω, g x = f.toFun x) (i : Fin (k + 1)) (x : Ω) :
    iteratedFDerivWithin ℝ i g Ω x = f.iteratedFDeriv i x := by
  have hEq : Set.EqOn g (extend f.toFun) Ω := fun y hy ↦ by
    rw [extend_of_mem _ hy]
    exact hg ⟨y, hy⟩
  rw [iteratedFDerivWithin_congr hEq x.2,
    ← (hasFTaylorSeriesUpToOn f).eq_iteratedFDerivWithin_of_uniqueDiffOn
      (by exact_mod_cast i.is_le) Ω.isOpen.uniqueDiffOn x.2,
    series_of_lt f x i.2, extend_coe]

/-- An element of `C^{k,α}(Ω)` is determined by its underlying map. -/
theorem toFun_injective :
    Function.Injective (toFun (k := k) (α := α) (Ω := Ω) (F := F)) := by
  intro f g hfg
  have hfield : ∀ i, f.iteratedFDeriv i = g.iteratedFDeriv i := fun i ↦ by
    ext1 x
    rw [← iteratedFDerivWithin_eq_of_eq f (g := extend f.toFun) (fun y ↦ extend_coe _ y),
      ← iteratedFDerivWithin_eq_of_eq g (g := extend f.toFun) (fun y ↦ by rw [extend_coe, hfg])]
  exact toJet_injective (ext_fieldL hfield)

instance instFunLike : FunLike (CkHolderOnSpace k α Ω F) Ω F where
  coe := toFun
  coe_injective := toFun_injective

@[simp]
theorem toFun_eq_coe (f : CkHolderOnSpace k α Ω F) : f.toFun = ⇑f :=
  (rfl)

/-- Two elements of `C^{k,α}(Ω)` are equal when their underlying maps agree at every point of
`Ω`. -/
@[ext]
theorem ext {f g : CkHolderOnSpace k α Ω F} (h : ∀ x, f x = g x) : f = g :=
  DFunLike.ext f g h

/-- The order-zero derivative field takes the values of the underlying map. -/
-- Not a simp lemma: `simp` rewrites the order `↑0` to `0` inside the type of the multilinear map,
-- so the left-hand side is not in simp normal form.
theorem iteratedFDeriv_zero_apply (f : CkHolderOnSpace k α Ω F) (x : Ω) (m : Fin 0 → E) :
    f.iteratedFDeriv 0 x m = f x := by
  rw [Subsingleton.elim m 0]
  rfl

/-- The recorded derivative fields are the iterated Fréchet derivatives within `Ω` of every map
`g : E → F` which agrees with the element on `Ω`. -/
theorem iteratedFDerivWithin_eq (f : CkHolderOnSpace k α Ω F) {g : E → F}
    (hg : ∀ x : Ω, g x = f x) (i : Fin (k + 1)) (x : Ω) :
    iteratedFDerivWithin ℝ i g Ω x = f.iteratedFDeriv i x :=
  iteratedFDerivWithin_eq_of_eq f hg i x

/-- Since `Ω` is open, the recorded derivative fields are also the iterated Fréchet derivatives
of every map `g : E → F` which agrees with the element on `Ω`. -/
theorem iteratedFDeriv_eq (f : CkHolderOnSpace k α Ω F) {g : E → F}
    (hg : ∀ x : Ω, g x = f x) (i : Fin (k + 1)) (x : Ω) :
    _root_.iteratedFDeriv ℝ i g x = f.iteratedFDeriv i x := by
  rw [← iteratedFDerivWithin_of_isOpen i Ω.isOpen x.2, iteratedFDerivWithin_eq f hg]

/-- Every map `g : E → F` which agrees with an element of `C^{k,α}(Ω)` on `Ω` is `k` times
continuously differentiable on `Ω`. -/
theorem contDiffOn (f : CkHolderOnSpace k α Ω F) {g : E → F} (hg : ∀ x : Ω, g x = f x) :
    ContDiffOn ℝ k g Ω :=
  (hasFTaylorSeriesUpToOn f).contDiffOn.congr fun y hy ↦ by
    rw [extend_of_mem _ hy]
    exact hg ⟨y, hy⟩

/-- The Hölder field, as a bounded continuous field, is the derivative field of order `k`. -/
@[simp]
theorem toBoundedContinuousFunction_iteratedFDerivHolder (f : CkHolderOnSpace k α Ω F) :
    f.iteratedFDerivHolder.toBoundedContinuousFunction = f.iteratedFDeriv (Fin.last k) := by
  rw [iteratedFDeriv, fieldL_last, iteratedFDerivHolder]

/-- The Hölder field records the `k`-th derivative field. -/
@[simp]
theorem iteratedFDerivHolder_apply (f : CkHolderOnSpace k α Ω F) (x : Ω) :
    f.iteratedFDerivHolder x = f.iteratedFDeriv (Fin.last k) x := by
  rw [← HolderSpace.toBoundedContinuousFunction_apply,
    toBoundedContinuousFunction_iteratedFDerivHolder]

/-- The `k`-th iterated derivative within `Ω` of every map which agrees with an element of
`C^{k,α}(Ω)` on `Ω` is `α`-Hölder on `Ω`, with the Hölder seminorm of the `k`-th derivative
field. -/
theorem holderOnWith_iteratedFDerivWithin (f : CkHolderOnSpace k α Ω F) {g : E → F}
    (hg : ∀ x : Ω, g x = f x) :
    HolderOnWith (nnHolderNorm α (f.iteratedFDerivHolder : Ω → E [×k]→L[ℝ] F)) α
      (iteratedFDerivWithin ℝ k g Ω) Ω := by
  have heq : (Ω : Set E).domRestrict (iteratedFDerivWithin ℝ k g Ω) =
      (f.iteratedFDerivHolder : Ω → E [×k]→L[ℝ] F) := by
    funext x
    rw [Set.domRestrict_apply, iteratedFDerivHolder_apply]
    exact iteratedFDerivWithin_eq f hg (Fin.last k) x
  rw [← HolderWith.restrict_iff, heq]
  exact f.iteratedFDerivHolder.holderWith

/-- The `C^{k,α}(Ω)` norm is the sum of the supremum norms on `Ω` of the derivative fields through
order `k` and the `α`-Hölder seminorm on `Ω` of the `k`-th derivative field. -/
theorem norm_eq (f : CkHolderOnSpace k α Ω F) :
    ‖f‖ = ∑ i : Fin (k + 1), ‖f.iteratedFDeriv i‖ +
      nnHolderNorm α (f.iteratedFDerivHolder : Ω → E [×k]→L[ℝ] F) := by
  rw [← norm_toJet, HolderJet.norm_eq]
  rfl

/-- The supremum norm of each derivative field is controlled by the `C^{k,α}(Ω)` norm. -/
theorem norm_iteratedFDeriv_le (f : CkHolderOnSpace k α Ω F) (i : Fin (k + 1)) :
    ‖f.iteratedFDeriv i‖ ≤ ‖f‖ := by
  rw [norm_eq]
  exact (Finset.single_le_sum (fun j _ ↦ norm_nonneg (f.iteratedFDeriv j))
    (Finset.mem_univ i)).trans (le_add_of_nonneg_right (NNReal.coe_nonneg _))

/-- The Hölder seminorm of the `k`-th derivative field is controlled by the `C^{k,α}(Ω)` norm. -/
theorem nnHolderNorm_iteratedFDerivHolder_le (f : CkHolderOnSpace k α Ω F) :
    (nnHolderNorm α (f.iteratedFDerivHolder : Ω → E [×k]→L[ℝ] F) : ℝ) ≤ ‖f‖ := by
  rw [norm_eq]
  exact le_add_of_nonneg_left (Finset.sum_nonneg fun j _ ↦ norm_nonneg _)

/-- The values of an element of `C^{k,α}(Ω)` are controlled by its norm. -/
theorem norm_apply_le (f : CkHolderOnSpace k α Ω F) (x : Ω) : ‖f x‖ ≤ ‖f‖ := by
  calc ‖f x‖ = ‖f.iteratedFDeriv 0 x‖ :=
        ContinuousMultilinearMap.curry0_norm (f.iteratedFDeriv 0 x)
    _ ≤ ‖f.iteratedFDeriv 0‖ := (f.iteratedFDeriv 0).norm_coe_le_norm x
    _ ≤ ‖f‖ := norm_iteratedFDeriv_le f 0

/-- The `i`-th derivative field, as a continuous linear map to bounded continuous fields on
`Ω`. -/
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

/-- The `k`-th derivative map to the bounded Hölder space on `Ω` has operator norm at most one. -/
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
theorem iteratedFDeriv_neg (f : CkHolderOnSpace k α Ω F) (i : Fin (k + 1)) :
    (-f).iteratedFDeriv i = -f.iteratedFDeriv i := by
  simpa only [iteratedFDerivL_apply] using (iteratedFDerivL i).map_neg f

@[simp]
theorem iteratedFDeriv_sub (f g : CkHolderOnSpace k α Ω F) (i : Fin (k + 1)) :
    (f - g).iteratedFDeriv i = f.iteratedFDeriv i - g.iteratedFDeriv i := by
  simpa only [iteratedFDerivL_apply] using (iteratedFDerivL i).map_sub f g

@[simp]
theorem iteratedFDerivHolder_zero : (0 : CkHolderOnSpace k α Ω F).iteratedFDerivHolder = 0 := by
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
theorem iteratedFDerivHolder_neg (f : CkHolderOnSpace k α Ω F) :
    (-f).iteratedFDerivHolder = -f.iteratedFDerivHolder := by
  simpa only [iteratedFDerivHolderL_apply] using iteratedFDerivHolderL.map_neg f

@[simp]
theorem iteratedFDerivHolder_sub (f g : CkHolderOnSpace k α Ω F) :
    (f - g).iteratedFDerivHolder = f.iteratedFDerivHolder - g.iteratedFDerivHolder := by
  simpa only [iteratedFDerivHolderL_apply] using iteratedFDerivHolderL.map_sub f g

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
    FunLike.coe_add]
  simp

@[simp]
theorem coe_smul (c : ℝ) (f : CkHolderOnSpace k α Ω F) : ⇑(c • f) = c • ⇑f := by
  ext x
  simp only [← toFun_eq_coe, toFun, iteratedFDeriv_smul, Pi.smul_apply,
    FunLike.coe_smul]
  simp

@[simp]
theorem coe_neg (f : CkHolderOnSpace k α Ω F) : ⇑(-f) = -⇑f := by
  ext x
  simp only [← toFun_eq_coe, toFun, iteratedFDeriv_neg, Pi.neg_apply,
    FunLike.coe_neg]
  simp

@[simp]
theorem coe_sub (f g : CkHolderOnSpace k α Ω F) : ⇑(f - g) = f - g := by
  ext x
  simp only [← toFun_eq_coe, toFun, iteratedFDeriv_sub, Pi.sub_apply,
    FunLike.coe_sub]
  simp

/-! ### Construction from a map that is `C^k` on `Ω` -/

/-- The jet on `Ω` of iterated derivatives within `Ω` of a map that is `C^k` on `Ω`, with bounded
derivatives through order `k` and `α`-Hölder `k`-th derivative on `Ω`. -/
private def jetOf (g : E → F) (hg : ContDiffOn ℝ k g Ω)
    (hbdd : ∀ i ≤ k, ∃ C, ∀ x ∈ Ω, ‖iteratedFDerivWithin ℝ i g Ω x‖ ≤ C)
    (hholder : ∃ C, HolderOnWith C α (iteratedFDerivWithin ℝ k g Ω) Ω) : HolderJet k α Ω E F :=
  have hcont (i : ℕ) (hi : i ≤ k) : Continuous ((Ω : Set E).domRestrict
      (iteratedFDerivWithin ℝ i g Ω)) :=
    continuousOn_iff_continuous_domRestrict.1
      (hg.continuousOn_iteratedFDerivWithin (by exact_mod_cast hi) Ω.isOpen.uniqueDiffOn)
  have hb (i : ℕ) (hi : i ≤ k) : ∃ C, ∀ x : Ω,
      ‖(Ω : Set E).domRestrict (iteratedFDerivWithin ℝ i g Ω) x‖ ≤ C :=
    ⟨(hbdd i hi).choose, fun x ↦ (hbdd i hi).choose_spec x x.2⟩
  ofFields (fun i ↦ BoundedContinuousFunction.ofNormedAddCommGroup _ (hcont i i.is_le)
      (hb i i.is_le).choose (hb i i.is_le).choose_spec)
    (HolderWith.restrict_iff.2 hholder.choose_spec).memHolder

private theorem fieldL_jetOf (g : E → F) (hg : ContDiffOn ℝ k g Ω)
    (hbdd : ∀ i ≤ k, ∃ C, ∀ x ∈ Ω, ‖iteratedFDerivWithin ℝ i g Ω x‖ ≤ C)
    (hholder : ∃ C, HolderOnWith C α (iteratedFDerivWithin ℝ k g Ω) Ω) (i : Fin (k + 1))
    (x : Ω) : fieldL i (jetOf g hg hbdd hholder) x = iteratedFDerivWithin ℝ i g Ω x :=
  DFunLike.congr_fun (fieldL_ofFields _ _ i) x

private theorem isJetGraph_jetOf (g : E → F) (hg : ContDiffOn ℝ k g Ω)
    (hbdd : ∀ i ≤ k, ∃ C, ∀ x ∈ Ω, ‖iteratedFDerivWithin ℝ i g Ω x‖ ≤ C)
    (hholder : ∃ C, HolderOnWith C α (iteratedFDerivWithin ℝ k g Ω) Ω) :
    IsJetGraph (jetOf g hg hbdd hholder) := fun j x ↦ by
  have hdiff := (hg.differentiableOn_iteratedFDerivWithin (m := j) (by exact_mod_cast j.2)
    Ω.isOpen.uniqueDiffOn) x x.2
  have h := (hdiff.hasFDerivWithinAt.hasFDerivAt (Ω.isOpen.mem_nhds x.2)).congr_of_eventuallyEq
    (extend_eventuallyEq (fun y ↦ (fieldL_jetOf g hg hbdd hholder j.castSucc y).symm) x)
  rw [fderivWithin_iteratedFDerivWithin, Function.comp_apply] at h
  rw [fieldL_jetOf]
  exact h

/-- Build an element of `C^{k,α}(Ω)` from a map `g : E → F` which is `C^k` on `Ω`, with
iterated derivatives within `Ω` bounded on `Ω` through order `k` and `k`-th iterated derivative
`α`-Hölder on `Ω`. -/
def ofContDiffOn (g : E → F) (hg : ContDiffOn ℝ k g Ω)
    (hbdd : ∀ i ≤ k, ∃ C, ∀ x ∈ Ω, ‖iteratedFDerivWithin ℝ i g Ω x‖ ≤ C)
    (hholder : ∃ C, HolderOnWith C α (iteratedFDerivWithin ℝ k g Ω) Ω) :
    CkHolderOnSpace k α Ω F :=
  mk (jetOf g hg hbdd hholder) (isJetGraph_jetOf g hg hbdd hholder)

@[simp]
theorem ofContDiffOn_apply (g : E → F) (hg : ContDiffOn ℝ k g Ω)
    (hbdd : ∀ i ≤ k, ∃ C, ∀ x ∈ Ω, ‖iteratedFDerivWithin ℝ i g Ω x‖ ≤ C)
    (hholder : ∃ C, HolderOnWith C α (iteratedFDerivWithin ℝ k g Ω) Ω) (x : Ω) :
    ofContDiffOn g hg hbdd hholder x = g x := by
  rw [← toFun_eq_coe, toFun, iteratedFDeriv, ofContDiffOn, toJet_mk, fieldL_jetOf,
    iteratedFDerivWithin_zero_eq_comp]
  simp

/-- The derivative fields of the element built by `ofContDiffOn` are the iterated derivatives
within `Ω` of the map it is built from. -/
@[simp]
theorem iteratedFDeriv_ofContDiffOn (g : E → F) (hg : ContDiffOn ℝ k g Ω)
    (hbdd : ∀ i ≤ k, ∃ C, ∀ x ∈ Ω, ‖iteratedFDerivWithin ℝ i g Ω x‖ ≤ C)
    (hholder : ∃ C, HolderOnWith C α (iteratedFDerivWithin ℝ k g Ω) Ω) (i : Fin (k + 1))
    (x : Ω) :
    (ofContDiffOn g hg hbdd hholder).iteratedFDeriv i x = iteratedFDerivWithin ℝ i g Ω x := by
  rw [iteratedFDeriv, ofContDiffOn, toJet_mk, fieldL_jetOf]

/-- The Hölder field of the element built by `ofContDiffOn` is the `k`-th iterated derivative within
`Ω` of the map it is built from, restricted to `Ω`. -/
@[simp]
theorem coe_iteratedFDerivHolder_ofContDiffOn (g : E → F) (hg : ContDiffOn ℝ k g Ω)
    (hbdd : ∀ i ≤ k, ∃ C, ∀ x ∈ Ω, ‖iteratedFDerivWithin ℝ i g Ω x‖ ≤ C)
    (hholder : ∃ C, HolderOnWith C α (iteratedFDerivWithin ℝ k g Ω) Ω) :
    ((ofContDiffOn g hg hbdd hholder).iteratedFDerivHolder : Ω → E [×k]→L[ℝ] F) =
      (Ω : Set E).domRestrict (iteratedFDerivWithin ℝ k g Ω) :=
  funext fun x ↦ by
    rw [iteratedFDerivHolder_apply, iteratedFDeriv_ofContDiffOn]
    rfl

/-- On an open subset `U ⊆ Ω`, the iterated derivatives within `U` of the extension by zero of an
element of `C^{k,α}(Ω)` are its derivative fields. -/
private theorem iteratedFDerivWithin_extend (f : CkHolderOnSpace k α Ω F) {U : Opens E}
    (hU : U ≤ Ω) {i : ℕ} (hi : i ≤ k) {x : E} (hx : x ∈ U) :
    iteratedFDerivWithin ℝ i (extend ⇑f) U x =
      f.iteratedFDeriv ⟨i, Nat.lt_succ_of_le hi⟩ ⟨x, hU hx⟩ := by
  rw [iteratedFDerivWithin_of_isOpen i U.isOpen hx]
  exact f.iteratedFDeriv_eq (fun y ↦ extend_coe _ y) ⟨i, Nat.lt_succ_of_le hi⟩ ⟨x, hU hx⟩

/-- The iterated derivatives within an open subset `U ⊆ Ω` of the extension by zero of an element
of `C^{k,α}(Ω)` are bounded by its norm. -/
private theorem norm_iteratedFDerivWithin_extend_le (f : CkHolderOnSpace k α Ω F) {U : Opens E}
    (hU : U ≤ Ω) {i : ℕ} (hi : i ≤ k) {x : E} (hx : x ∈ U) :
    ‖iteratedFDerivWithin ℝ i (extend ⇑f) U x‖ ≤ ‖f‖ := by
  rw [iteratedFDerivWithin_extend f hU hi hx]
  exact ((f.iteratedFDeriv _).norm_coe_le_norm _).trans (norm_iteratedFDeriv_le f _)

/-! ### Completeness -/

/-- The derivative identities are closed under uniform convergence of the fields. -/
private theorem isClosed_isJetGraph : IsClosed {J : HolderJet k α Ω E F | IsJetGraph J} := by
  have hset : {J : HolderJet k α Ω E F | IsJetGraph J} =
      ⋂ j : Fin k, (fun J : HolderJet k α Ω E F ↦ (fieldL j.castSucc J, fieldL j.succ J)) ⁻¹'
        {J | ∀ x : Ω, HasFDerivAt (extend (J.1 : Ω → E [×j]→L[ℝ] F))
          (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (j + 1) ↦ E) F (J.2 x)) (x : E)} := by
    ext J
    simp [IsJetGraph]
  rw [hset]
  exact isClosed_iInter fun j ↦
    (isClosed_setOf_hasFDerivAt_extend_comp Ω.isOpen 0 _ (continuousMultilinearCurryLeftEquiv ℝ
      (fun _ : Fin (j + 1) ↦ E) F).isometry.uniformContinuous).preimage
      ((fieldL (k := k) (α := α) (X := Ω) (E := E) (F := F) _).continuous.prodMk
        (fieldL (k := k) (α := α) (X := Ω) (E := E) (F := F) _).continuous)

/-- `C^{k,α}(Ω, F)` is a Banach space when `F` is. -/
instance instCompleteSpace [CompleteSpace F] : CompleteSpace (CkHolderOnSpace k α Ω F) := by
  unfold CkHolderOnSpace
  exact isClosed_isJetGraph.completeSpace_coe

/-! ### Restriction to a smaller open set -/

section Restrict

variable {Ω' : Opens E}

/-- Restriction to an open subset, as a linear map. -/
private def restrictₗ (h : Ω' ≤ Ω) : CkHolderOnSpace k α Ω F →ₗ[ℝ] CkHolderOnSpace k α Ω' F where
  toFun f := ofContDiffOn (extend ⇑f) ((f.contDiffOn fun y ↦ extend_coe _ y).mono h)
    (fun _ hi ↦ ⟨‖f‖, fun _ hx ↦ norm_iteratedFDerivWithin_extend_le f h hi hx⟩)
    ⟨_, fun x hx y hy ↦ by
      rw [iteratedFDerivWithin_extend f h le_rfl hx, iteratedFDerivWithin_extend f h le_rfl hy,
        ← iteratedFDerivWithin_extend f le_rfl le_rfl (h hx),
        ← iteratedFDerivWithin_extend f le_rfl le_rfl (h hy)]
      exact (f.holderOnWith_iteratedFDerivWithin fun y ↦ extend_coe _ y) x (h hx) y (h hy)⟩
  map_add' f g := ext fun x ↦ by
    simp only [ofContDiffOn_apply, coe_add, Pi.add_apply, extend_of_mem _ (h x.2)]
  map_smul' c f := ext fun x ↦ by
    simp only [ofContDiffOn_apply, coe_smul, Pi.smul_apply, extend_of_mem _ (h x.2),
      RingHom.id_apply]

private theorem iteratedFDeriv_restrictₗ (h : Ω' ≤ Ω) (f : CkHolderOnSpace k α Ω F)
    (i : Fin (k + 1)) (x : Ω') :
    (restrictₗ h f).iteratedFDeriv i x = f.iteratedFDeriv i (Set.inclusion h x) := by
  rw [restrictₗ, LinearMap.coe_mk, AddHom.coe_mk, iteratedFDeriv_ofContDiffOn,
    iteratedFDerivWithin_extend f h i.is_le x.2]

/-- **Restriction** of an element of `C^{k,α}(Ω)` to an open subset `Ω' ⊆ Ω`. Both the supremum
norms and the Hölder seminorm can only decrease, so it has norm at most one
(`TauCeti.CkHolderOnSpace.norm_restrictL_le`). -/
def restrictL (h : Ω' ≤ Ω) : CkHolderOnSpace k α Ω F →L[ℝ] CkHolderOnSpace k α Ω' F :=
  (restrictₗ h).mkContinuous 1 fun f ↦ by
    rw [one_mul, norm_eq, norm_eq f]
    have hfield (i : Fin (k + 1)) :
        ‖(restrictₗ h f).iteratedFDeriv i‖ ≤ ‖f.iteratedFDeriv i‖ :=
      (BoundedContinuousFunction.norm_le (norm_nonneg _)).2 fun x ↦ by
        rw [iteratedFDeriv_restrictₗ]
        exact (f.iteratedFDeriv i).norm_coe_le_norm _
    have hholder : ((restrictₗ h f).iteratedFDerivHolder : Ω' → E [×k]→L[ℝ] F) =
        (f.iteratedFDerivHolder : Ω → E [×k]→L[ℝ] F) ∘ Set.inclusion h :=
      funext fun x ↦ by
        rw [Function.comp_apply, iteratedFDerivHolder_apply, iteratedFDerivHolder_apply,
          iteratedFDeriv_restrictₗ]
    have hH : (nnHolderNorm α ((restrictₗ h f).iteratedFDerivHolder : Ω' → E [×k]→L[ℝ] F) : ℝ) ≤
        nnHolderNorm α (f.iteratedFDerivHolder : Ω → E [×k]→L[ℝ] F) := by
      rw [hholder]
      have := HolderSpace.nnHolderNorm_comp_le (LipschitzWith.inclusion h) f.iteratedFDerivHolder
      rw [NNReal.one_rpow, mul_one] at this
      exact_mod_cast this
    exact add_le_add (Finset.sum_le_sum fun i _ ↦ hfield i) hH

@[simp]
theorem restrictL_apply (h : Ω' ≤ Ω) (f : CkHolderOnSpace k α Ω F) (x : Ω') :
    restrictL h f x = f ⟨x, h x.2⟩ := by
  simp [restrictL, restrictₗ, extend_of_mem _ (h x.2)]

@[simp]
theorem iteratedFDeriv_restrictL (h : Ω' ≤ Ω) (f : CkHolderOnSpace k α Ω F) (i : Fin (k + 1))
    (x : Ω') : (restrictL h f).iteratedFDeriv i x = f.iteratedFDeriv i ⟨x, h x.2⟩ :=
  iteratedFDeriv_restrictₗ h f i x

@[simp]
theorem restrictL_self (h : Ω ≤ Ω) (f : CkHolderOnSpace k α Ω F) : restrictL h f = f := by
  ext x
  simp

@[simp]
theorem restrictL_restrictL {Ω'' : Opens E} (h : Ω' ≤ Ω) (h' : Ω'' ≤ Ω')
    (f : CkHolderOnSpace k α Ω F) : restrictL h' (restrictL h f) = restrictL (h'.trans h) f := by
  ext x
  simp

/-- Restriction to an open subset has norm at most one. -/
theorem norm_restrictL_le (h : Ω' ≤ Ω) : ‖restrictL (k := k) (α := α) (F := F) h‖ ≤ 1 :=
  LinearMap.mkContinuous_norm_le _ zero_le_one _

end Restrict

/-! ### Change of exponent on a bounded set -/

section Exponent

variable {β : ℝ≥0}

/-- On a bounded open set, the `k`-th derivative of an element of `C^{k,α}(Ω)` is `β`-Hölder for
`β ≤ α`, with the seminorm growing by at most the factor `D^(α - β)`, `D` the diameter of `Ω`. -/
private theorem holderOnWith_of_le (f : CkHolderOnSpace k α Ω F)
    (hΩ : Bornology.IsBounded (Ω : Set E)) (hβα : β ≤ α) :
    HolderOnWith (nnHolderNorm α (f.iteratedFDerivHolder : Ω → E [×k]→L[ℝ] F) *
        (Metric.diam (Ω : Set E)).toNNReal ^ ((α : ℝ) - β)) β
      (iteratedFDerivWithin ℝ k (extend ⇑f) Ω) Ω :=
  (f.holderOnWith_iteratedFDerivWithin fun y ↦ extend_coe _ y).of_le
    (fun _ hx _ hy ↦ Metric.edist_le_diam_of_mem hΩ hx hy) hβα

/-- On a bounded open set, the inclusion `C^{k,α}(Ω) ⊆ C^{k,β}(Ω)` for `β ≤ α`, as a linear
map. -/
private def inclusionₗ (hΩ : Bornology.IsBounded (Ω : Set E)) (hβα : β ≤ α) :
    CkHolderOnSpace k α Ω F →ₗ[ℝ] CkHolderOnSpace k β Ω F where
  toFun f := ofContDiffOn (extend ⇑f) (f.contDiffOn fun y ↦ extend_coe _ y)
    (fun _ hi ↦ ⟨‖f‖, fun _ hx ↦ norm_iteratedFDerivWithin_extend_le f le_rfl hi hx⟩)
    ⟨_, holderOnWith_of_le f hΩ hβα⟩
  map_add' f g := ext fun x ↦ by simp [extend_coe]
  map_smul' c f := ext fun x ↦ by simp [extend_coe]

private theorem iteratedFDeriv_inclusionₗ (hΩ : Bornology.IsBounded (Ω : Set E)) (hβα : β ≤ α)
    (f : CkHolderOnSpace k α Ω F) (i : Fin (k + 1)) :
    (inclusionₗ hΩ hβα f).iteratedFDeriv i = f.iteratedFDeriv i := by
  ext1 x
  rw [inclusionₗ, LinearMap.coe_mk, AddHom.coe_mk, iteratedFDeriv_ofContDiffOn,
    iteratedFDerivWithin_extend f le_rfl i.is_le x.2]

/-- **The inclusion `C^{k,α}(Ω) ⊆ C^{k,β}(Ω)`** for `β ≤ α` on a bounded open set `Ω`: an
`α`-Hölder function on `Ω` is `β`-Hölder there, and the inclusion has norm at most
`max 1 (D^(α - β))`, `D` the diameter of `Ω` (`TauCeti.CkHolderOnSpace.norm_inclusionL_le`). -/
def inclusionL (hΩ : Bornology.IsBounded (Ω : Set E)) (hβα : β ≤ α) :
    CkHolderOnSpace k α Ω F →L[ℝ] CkHolderOnSpace k β Ω F :=
  (inclusionₗ hΩ hβα).mkContinuous
      (max 1 (((Metric.diam (Ω : Set E)).toNNReal : ℝ) ^ ((α : ℝ) - β))) fun f ↦ by
    set D : ℝ := ((Metric.diam (Ω : Set E)).toNNReal : ℝ) ^ ((α : ℝ) - β)
    set H : ℝ := ((nnHolderNorm α (f.iteratedFDerivHolder : Ω → E [×k]→L[ℝ] F) : ℝ≥0) : ℝ)
    set S : ℝ := ∑ i : Fin (k + 1), ‖f.iteratedFDeriv i‖
    have hH : (nnHolderNorm β ((inclusionₗ hΩ hβα f).iteratedFDerivHolder :
        Ω → E [×k]→L[ℝ] F) : ℝ) ≤ H * D := by
      rw [inclusionₗ, LinearMap.coe_mk, AddHom.coe_mk, coe_iteratedFDerivHolder_ofContDiffOn]
      have h := NNReal.coe_le_coe.2
        (HolderWith.restrict_iff.2 (holderOnWith_of_le f hΩ hβα)).nnholderNorm_le
      rwa [NNReal.coe_mul, NNReal.coe_rpow] at h
    have hS : 0 ≤ S := Finset.sum_nonneg fun i _ ↦ norm_nonneg _
    have hH0 : 0 ≤ H := NNReal.coe_nonneg _
    have h₁ : (1 : ℝ) ≤ max 1 D := le_max_left _ _
    have h₂ : D ≤ max 1 D := le_max_right _ _
    rw [norm_eq, norm_eq f]
    simp only [iteratedFDeriv_inclusionₗ]
    nlinarith

@[simp]
theorem inclusionL_apply (hΩ : Bornology.IsBounded (Ω : Set E)) (hβα : β ≤ α)
    (f : CkHolderOnSpace k α Ω F) (x : Ω) : inclusionL hΩ hβα f x = f x := by
  simp [inclusionL, inclusionₗ, extend_coe]

@[simp]
theorem iteratedFDeriv_inclusionL (hΩ : Bornology.IsBounded (Ω : Set E)) (hβα : β ≤ α)
    (f : CkHolderOnSpace k α Ω F) (i : Fin (k + 1)) :
    (inclusionL hΩ hβα f).iteratedFDeriv i = f.iteratedFDeriv i :=
  iteratedFDeriv_inclusionₗ hΩ hβα f i

@[simp]
theorem inclusionL_self (hΩ : Bornology.IsBounded (Ω : Set E)) (h : α ≤ α)
    (f : CkHolderOnSpace k α Ω F) : inclusionL hΩ h f = f := by
  ext x
  simp

@[simp]
theorem inclusionL_inclusionL {γ : ℝ≥0} (hΩ : Bornology.IsBounded (Ω : Set E)) (hβα : β ≤ α)
    (hγβ : γ ≤ β) (f : CkHolderOnSpace k α Ω F) :
    inclusionL hΩ hγβ (inclusionL hΩ hβα f) = inclusionL hΩ (hγβ.trans hβα) f := by
  ext x
  simp

/-- The inclusion `C^{k,α}(Ω) ⊆ C^{k,β}(Ω)` has norm at most `max 1 (D^(α - β))`, `D` the
diameter of `Ω`. -/
theorem norm_inclusionL_le (hΩ : Bornology.IsBounded (Ω : Set E)) (hβα : β ≤ α) :
    ‖inclusionL (k := k) (F := F) hΩ hβα‖ ≤
      max 1 (((Metric.diam (Ω : Set E)).toNNReal : ℝ) ^ ((α : ℝ) - β)) :=
  LinearMap.mkContinuous_norm_le _ (zero_le_one.trans (le_max_left _ _)) _

end Exponent

/-! ### Change of order on a convex set -/

section Order

/-- On a convex open set and for `α ≤ 1`, the `k`-th derivative of an element of
`C^{k+1,α}(Ω)` is `α`-Hölder on `Ω`, with constant `‖D^{k+1} f‖_∞ + 2 ‖D^k f‖_∞`: it is
`‖D^{k+1} f‖_∞`-Lipschitz on `Ω` by the mean value inequality, which is used at distances less
than `1`, and it is bounded by `‖D^k f‖_∞`. -/
private theorem holderOnWith_succ (f : CkHolderOnSpace (k + 1) α Ω F)
    (hΩ : Convex ℝ (Ω : Set E)) (hα : α ≤ 1) :
    HolderOnWith (‖f.iteratedFDeriv (Fin.last (k + 1))‖₊ +
        2 * ‖f.iteratedFDeriv (Fin.last k).castSucc‖₊) α
      (iteratedFDerivWithin ℝ k (extend ⇑f) Ω) Ω := by
  have hD (i : ℕ) (hi : i < k + 2) (x : E) (hx : x ∈ Ω) :
      ‖_root_.iteratedFDeriv ℝ i (extend ⇑f) x‖ ≤ ‖f.iteratedFDeriv ⟨i, hi⟩‖ := by
    rw [f.iteratedFDeriv_eq (fun y ↦ extend_coe _ y) ⟨i, hi⟩ ⟨x, hx⟩]
    exact (f.iteratedFDeriv _).norm_coe_le_norm _
  have h := (f.contDiffOn fun y ↦ extend_coe _ y).holderOnWith_iteratedFDeriv_of_lt
    (M := ‖f.iteratedFDeriv (Fin.last k).castSucc‖₊) (L := ‖f.iteratedFDeriv (Fin.last (k + 1))‖₊)
    Ω.isOpen hΩ k.lt_succ_self hα (fun x hx ↦ hD k (by omega) x hx)
    (fun x hx ↦ hD (k + 1) (by omega) x hx)
  intro x hx y hy
  rw [iteratedFDerivWithin_of_isOpen k Ω.isOpen hx, iteratedFDerivWithin_of_isOpen k Ω.isOpen hy]
  exact h x hx y hy

/-- On a convex open set and for `α ≤ 1`, the inclusion `C^{k+1,α}(Ω) ⊆ C^{k,α}(Ω)`, as a linear
map. -/
private def succInclusionₗ (hΩ : Convex ℝ (Ω : Set E)) (hα : α ≤ 1) :
    CkHolderOnSpace (k + 1) α Ω F →ₗ[ℝ] CkHolderOnSpace k α Ω F where
  toFun f := ofContDiffOn (extend ⇑f)
    ((f.contDiffOn fun y ↦ extend_coe _ y).of_le (by exact_mod_cast k.le_succ))
    (fun _ hi ↦ ⟨‖f‖, fun _ hx ↦
      norm_iteratedFDerivWithin_extend_le f le_rfl (hi.trans k.le_succ) hx⟩)
    ⟨_, holderOnWith_succ f hΩ hα⟩
  map_add' f g := ext fun x ↦ by simp [extend_coe]
  map_smul' c f := ext fun x ↦ by simp [extend_coe]

private theorem iteratedFDeriv_succInclusionₗ (hΩ : Convex ℝ (Ω : Set E)) (hα : α ≤ 1)
    (f : CkHolderOnSpace (k + 1) α Ω F) (i : Fin (k + 1)) :
    (succInclusionₗ hΩ hα f).iteratedFDeriv i = f.iteratedFDeriv i.castSucc := by
  ext1 x
  rw [succInclusionₗ, LinearMap.coe_mk, AddHom.coe_mk, iteratedFDeriv_ofContDiffOn,
    iteratedFDerivWithin_extend f le_rfl (i.is_le.trans k.le_succ) x.2]
  rfl

/-- **The inclusion `C^{k+1,α}(Ω) ⊆ C^{k,α}(Ω)`** on a convex open set `Ω`, for `α ≤ 1`. By the
mean value inequality the `α`-Hölder seminorm of `D^k f` on `Ω` is at most
`‖D^{k+1} f‖_∞ + 2 ‖D^k f‖_∞`, so the inclusion has norm at most `3`
(`TauCeti.CkHolderOnSpace.norm_succInclusionL_le`). Without convexity the inclusion can fail, since
the Hölder seminorm compares values at points of `Ω` that no path in `Ω` joins efficiently. -/
def succInclusionL (hΩ : Convex ℝ (Ω : Set E)) (hα : α ≤ 1) :
    CkHolderOnSpace (k + 1) α Ω F →L[ℝ] CkHolderOnSpace k α Ω F :=
  (succInclusionₗ hΩ hα).mkContinuous 3 fun f ↦ by
    have hH : (nnHolderNorm α ((succInclusionₗ hΩ hα f).iteratedFDerivHolder :
        Ω → E [×k]→L[ℝ] F) : ℝ) ≤ ‖f.iteratedFDeriv (Fin.last (k + 1))‖ +
          2 * ‖f.iteratedFDeriv (Fin.last k).castSucc‖ := by
      rw [succInclusionₗ, LinearMap.coe_mk, AddHom.coe_mk, coe_iteratedFDerivHolder_ofContDiffOn]
      have h := NNReal.coe_le_coe.2
        (HolderWith.restrict_iff.2 (holderOnWith_succ f hΩ hα)).nnholderNorm_le
      rwa [NNReal.coe_add, NNReal.coe_mul, NNReal.coe_ofNat, coe_nnNorm, coe_nnNorm] at h
    have hsum : ∑ i : Fin (k + 1), ‖f.iteratedFDeriv i.castSucc‖ +
        ‖f.iteratedFDeriv (Fin.last (k + 1))‖ ≤ ‖f‖ := by
      rw [← Fin.sum_univ_castSucc (fun i ↦ ‖f.iteratedFDeriv i‖), norm_eq f]
      exact le_add_of_nonneg_right (NNReal.coe_nonneg _)
    have hk := norm_iteratedFDeriv_le f (Fin.last k).castSucc
    rw [norm_eq]
    simp only [iteratedFDeriv_succInclusionₗ]
    linarith

@[simp]
theorem succInclusionL_apply (hΩ : Convex ℝ (Ω : Set E)) (hα : α ≤ 1)
    (f : CkHolderOnSpace (k + 1) α Ω F) (x : Ω) : succInclusionL hΩ hα f x = f x := by
  simp [succInclusionL, succInclusionₗ, extend_coe]

@[simp]
theorem iteratedFDeriv_succInclusionL (hΩ : Convex ℝ (Ω : Set E)) (hα : α ≤ 1)
    (f : CkHolderOnSpace (k + 1) α Ω F) (i : Fin (k + 1)) :
    (succInclusionL hΩ hα f).iteratedFDeriv i = f.iteratedFDeriv i.castSucc :=
  iteratedFDeriv_succInclusionₗ hΩ hα f i

/-- The inclusion `C^{k+1,α}(Ω) ⊆ C^{k,α}(Ω)` on a convex open set has norm at most `3`. -/
theorem norm_succInclusionL_le (hΩ : Convex ℝ (Ω : Set E)) (hα : α ≤ 1) :
    ‖succInclusionL (k := k) (F := F) hΩ hα‖ ≤ 3 :=
  LinearMap.mkContinuous_norm_le _ zero_le_three _

end Order

attribute [irreducible] instNormedAddCommGroup instNormedSpace _root_.TauCeti.CkHolderOnSpace

end CkHolderOnSpace

end TauCeti

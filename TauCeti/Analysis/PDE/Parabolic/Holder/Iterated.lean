/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Parabolic.Holder.Two
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.Analysis.Normed.Lp.lpSpace
public import Mathlib.Analysis.Normed.Lp.PiLp
import Mathlib.Analysis.Calculus.Deriv.Comp

/-!
# Bounded parabolic Hölder maps of every order

For `k : ℕ`, an exponent `α` (typically `0 < α < 1`) and a nondegenerate closed time slab
`E × [a, b]`, this file constructs the Banach space `C_{par,b}^{k+α}` of bounded maps `u` on the
slab whose mixed derivatives `D_t^r D_x^m u` of parabolic order `2 r + m ≤ k` exist, are bounded
and continuous on the closed slab, and satisfy

* for `2 r + m = k`: `D_t^r D_x^m u` is parabolically `α`-Hölder;
* for `2 r + m = k - 1`: the time slices `t ↦ D_t^r D_x^m u (x, t)` are `(1 + α) / 2`-Hölder,
  uniformly in `x`.

Spatial derivatives are iterated Fréchet derivatives, with values in continuous multilinear maps
`E [×m]→L[ℝ] F`; time derivatives are derivatives within `[a, b]`, so at the endpoints they are
the continuous one-sided derivatives. In the parabolic scaling one time derivative counts as two
spatial ones, which is why the order is `2 r + m` and why a map of order `k` also carries the
fractional time regularity `(1 + α) / 2` one order below the top. Mathematically, `k = 0` gives
the parabolic Hölder space `C_b^{α,α/2}` and `k = 2` the space `C_b^{2+α,1+α/2}` with its full
norm; the comparison with the carriers `TauCeti.HolderSpace` and
`TauCeti.ParabolicC2HolderSpace` of these orders is not part of this file. These are the solution
and data spaces of the classical Schauder theory of parabolic equations at every order of
differentiability.

An element is represented by one entry for each pair `(r, m)` with `2 r + m ≤ k`: a bounded
continuous field `D r m`, a family of `(1 + α) / 2`-Hölder time slices and a bounded `α`-Hölder
field. The entries are subject to the conditions that `D r (m + 1)`, curried on the left, is the
spatial Fréchet derivative of `D r m`, that `D (r + 1) m` is the time derivative of `D r m`
within `[a, b]`, that the time slices are those of `D r m` when `2 r + m = k - 1` and vanish
otherwise, and that the Hölder field is `D r m` when `2 r + m = k` and vanishes otherwise.
Because a field `D r m` with `r, m ≥ 1` is reached both as a spatial derivative of
`D r (m - 1)` and as a time derivative of `D (r - 1) m`, every ordering of the spatial and
temporal derivatives exists and gives the same field. The conditions are closed under uniform
convergence, which gives completeness. This closed-derivative-graph construction follows the
spatial space `TauCeti.CkHolderSpace` (`TauCeti/Analysis/Holder/Iterated.lean`) and the order-two
parabolic space `TauCeti.ParabolicC2HolderSpace`. The norm is

`‖u‖ = ∑_{2r+m ≤ k} ‖D_t^r D_x^m u‖_∞ + ∑_{2r+m = k} ‖D_t^r D_x^m u‖_{C^α} +
  ∑_{2r+m = k-1} sup_x ‖t ↦ D_t^r D_x^m u (x, t)‖_{C^{(1+α)/2}}`,

where `‖v‖_{C^γ}` is the supremum norm of `v` plus its `γ`-Hölder seminorm
(`TauCeti.ParabolicCkHolderSpace.norm_eq`).

The fields are determined by the map: `D r m` at `(x, t)` is the `m`-th iterated Fréchet
derivative in `x` of the `r`-th iterated derivative within `[a, b]` in `t`
(`TauCeti.ParabolicCkHolderSpace.mixedDerivL_slabMk`).

## Main declarations

* `TauCeti.ParabolicCkHolderSpace k α E F hab`: the space `C_{par,b}^{k+α}` on the slab
  `E × [a, b]`, a Banach space when `F` is.
* `TauCeti.ParabolicCkHolderSpace.mk`: an element from fields satisfying the derivative
  identities and the Hölder conditions.
* `TauCeti.ParabolicCkHolderSpace.mixedDerivL`: the bounded continuous field `D_t^r D_x^m u`,
  identified with iterated derivatives by `TauCeti.ParabolicCkHolderSpace.mixedDerivL_slabMk`.
* `TauCeti.ParabolicCkHolderSpace.hasFDerivAt_mixedDerivL` and
  `TauCeti.ParabolicCkHolderSpace.hasDerivWithinAt_mixedDerivL`: the spatial and time derivative
  identities between the fields.
* `TauCeti.ParabolicCkHolderSpace.mixedDerivHolderL` and
  `TauCeti.ParabolicCkHolderSpace.timeSliceL`: the top-order fields as bounded Hölder maps, and
  the families of Hölder time slices one order below.
* `TauCeti.ParabolicCkHolderSpace.norm_eq`: the norm as a sum of the field norms.

## References

* A. Lunardi, *Linear and nonlinear diffusion problems*, Cortona lecture notes, 2004, Chapter 3
  (the parabolic Hölder spaces `C^{k+α,(k+α)/2}`).
* N. V. Krylov, *Lectures on elliptic and parabolic equations in Hölder spaces*, AMS, 1996,
  Chapter 8.
-/

public section
noncomputable section

namespace TauCeti

open Set Filter Topology ParabolicSpaceTime
open scoped NNReal ENNReal BoundedContinuousFunction

variable {k : ℕ} {α : ℝ≥0} {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {a b : ℝ}

variable (α E F a b) in
/-- Shortcut instance for bounded continuous fields of `n`-multilinear maps on the slab. Without
it and the following shortcuts, instance search for the structure of the `ℓ¹` products of these
fields indexed by their order exceeds the default synthesis depth. They are local, and no public
statement mentions them. -/
local instance ParabolicCkHolderSpace.instNormedAddCommGroupField (n : ℕ) :
    NormedAddCommGroup (slab (E := E) a b →ᵇ (E [×n]→L[ℝ] F)) :=
  inferInstance

variable (α E F a b) in
/-- Shortcut instance for scalar operations on bounded continuous fields on the slab. -/
local instance ParabolicCkHolderSpace.instNormedSpaceField (n : ℕ) :
    NormedSpace ℝ (slab (E := E) a b →ᵇ (E [×n]→L[ℝ] F)) :=
  inferInstance

variable (α E F a b) in
/-- Shortcut instance for families of Hölder time slices of `n`-multilinear fields. -/
local instance ParabolicCkHolderSpace.instNormedAddCommGroupSlices (n : ℕ) :
    NormedAddCommGroup
      (lp (fun _ : E ↦ HolderSpace ((1 + α) / 2) (Icc a b) (E [×n]→L[ℝ] F)) ∞) :=
  inferInstance

variable (α E F a b) in
/-- Shortcut instance for scalar operations on families of Hölder time slices. -/
local instance ParabolicCkHolderSpace.instNormedSpaceSlices (n : ℕ) :
    NormedSpace ℝ
      (lp (fun _ : E ↦ HolderSpace ((1 + α) / 2) (Icc a b) (E [×n]→L[ℝ] F)) ∞) :=
  inferInstance

variable (α E F a b) in
/-- Shortcut instance for bounded Hölder fields of `n`-multilinear maps on the slab. -/
local instance ParabolicCkHolderSpace.instNormedAddCommGroupHolder (n : ℕ) :
    NormedAddCommGroup (HolderSpace α (slab (E := E) a b) (E [×n]→L[ℝ] F)) :=
  inferInstance

variable (α E F a b) in
/-- Shortcut instance for scalar operations on bounded Hölder fields on the slab. -/
local instance ParabolicCkHolderSpace.instNormedSpaceHolder (n : ℕ) :
    NormedSpace ℝ (HolderSpace α (slab (E := E) a b) (E [×n]→L[ℝ] F)) :=
  inferInstance

/-- The pairs `(r, m)` with `2 r + m ≤ k`: the numbers `r` of time derivatives and `m` of space
derivatives of the mixed derivatives `D_t^r D_x^m` of parabolic order at most `k`. -/
def parabolicDerivPairs (k : ℕ) : Finset (ℕ × ℕ) :=
  {p ∈ Finset.range (k + 1) ×ˢ Finset.range (k + 1) | 2 * p.1 + p.2 ≤ k}

@[simp]
theorem mem_parabolicDerivPairs {k : ℕ} {p : ℕ × ℕ} :
    p ∈ parabolicDerivPairs k ↔ 2 * p.1 + p.2 ≤ k := by
  simp only [parabolicDerivPairs, Finset.mem_filter, Finset.mem_product, Finset.mem_range,
    and_iff_right_iff_imp]
  omega

variable (k α E F) in
/-- Bounded parabolic Hölder maps of order `k` on a nondegenerate closed time slab
`E × [a, b]`: maps whose mixed derivatives `D_t^r D_x^m u` with `2 r + m ≤ k` exist and are
bounded and continuous, are parabolically `α`-Hölder when `2 r + m = k`, and have
`(1 + α) / 2`-Hölder time slices, uniformly in space, when `2 r + m = k - 1`. The norm is the sum
of the supremum norms of the derivatives, the bounded Hölder norms of the top-order ones and the
uniform bounded temporal Hölder norms of those one order below (`ParabolicCkHolderSpace.norm_eq`).
-/
-- Exposure is needed for the module compiler to construct instances on this graph alias;
-- the final irreducibility attribute keeps consumers at the characteristic API boundary.
@[expose] def ParabolicCkHolderSpace (hab : a < b) : Type _ :=
  -- The derivative graph is written as an abstraction over the three families of field
  -- projections, applied to them, rather than with `let`s: the graph only uses that the
  -- projections are linear, and this keeps the definition cheap to elaborate.
  ↥((fun (V : Type _) [NormedAddCommGroup V] [NormedSpace ℝ V]
      (field : ℕ → ∀ m : ℕ, V →L[ℝ] (slab (E := E) a b →ᵇ (E [×m]→L[ℝ] F)))
      (slices : ℕ → ∀ m : ℕ, V →L[ℝ]
        lp (fun _ : E ↦ HolderSpace ((1 + α) / 2) (Icc a b) (E [×m]→L[ℝ] F)) ∞)
      (holder : ℕ → ∀ m : ℕ, V →L[ℝ] HolderSpace α (slab (E := E) a b) (E [×m]→L[ℝ] F)) ↦
    ({ carrier := {J |
        (∀ r m, 2 * r + m + 1 ≤ k → ∀ (t : Icc a b) (x : E),
          HasFDerivAt (fun y ↦ field r m J (slabMk y t))
            (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (m + 1) ↦ E) F
              (field r (m + 1) J (slabMk x t))) x) ∧
        (∀ r m, 2 * r + m + 2 ≤ k → ∀ (x : E) (t : Icc a b),
          HasDerivWithinAt (ParabolicC2HolderSpace.timeExtension hab.le (field r m J) x)
            (field (r + 1) m J (slabMk x t)) (Icc a b) t) ∧
        (∀ r m (x : E) (t : Icc a b), slices r m J x t =
          if 2 * r + m + 1 = k then field r m J (slabMk x t) else 0) ∧
        ∀ r m (p : slab (E := E) a b), holder r m J p =
          if 2 * r + m = k then field r m J p else 0}
       zero_mem' := by
        refine ⟨fun r m _ t x ↦ ?_, fun r m _ x t ↦ ?_, fun r m x t ↦ ?_, fun r m p ↦ ?_⟩
        · simp only [ContinuousLinearMap.map_zero, FunLike.coe_zero, Pi.zero_apply,
            LinearIsometryEquiv.map_zero]
          exact hasFDerivAt_const (x := x) (c := (0 : E [×m]→L[ℝ] F))
        · simp only [ContinuousLinearMap.map_zero, ParabolicC2HolderSpace.timeExtension_def,
            FunLike.coe_zero, Pi.zero_apply]
          exact hasDerivWithinAt_const (x := (t : ℝ)) (s := Icc a b) (c := (0 : E [×m]→L[ℝ] F))
        · simp only [ContinuousLinearMap.map_zero, lp.coeFn_zero, Pi.zero_apply,
            HolderSpace.zero_apply, FunLike.coe_zero, ite_self]
        · simp only [ContinuousLinearMap.map_zero, HolderSpace.zero_apply, FunLike.coe_zero,
            Pi.zero_apply, ite_self]
       add_mem' := by
        rintro J K ⟨hJ, hJt, hJs, hJh⟩ ⟨hK, hKt, hKs, hKh⟩
        refine ⟨fun r m h t x ↦ ?_, fun r m h x t ↦ ?_, fun r m x t ↦ ?_, fun r m p ↦ ?_⟩
        · rw [ContinuousLinearMap.map_add, ContinuousLinearMap.map_add, FunLike.coe_add,
            FunLike.coe_add, Pi.add_apply, LinearIsometryEquiv.map_add]
          exact (hJ r m h t x).add (hK r m h t x)
        · rw [ContinuousLinearMap.map_add, ContinuousLinearMap.map_add, FunLike.coe_add,
            FunLike.coe_add, Pi.add_apply, ParabolicC2HolderSpace.timeExtension_add]
          exact (hJt r m h x t).add (hKt r m h x t)
        · rw [ContinuousLinearMap.map_add, ContinuousLinearMap.map_add, lp.coeFn_add,
            Pi.add_apply, HolderSpace.add_apply, hJs r m x t, hKs r m x t, FunLike.coe_add,
            Pi.add_apply]
          split_ifs
          · rfl
          · rw [add_zero]
        · rw [ContinuousLinearMap.map_add, ContinuousLinearMap.map_add, HolderSpace.add_apply,
            hJh r m p, hKh r m p, FunLike.coe_add, Pi.add_apply]
          split_ifs
          · rfl
          · rw [add_zero]
       smul_mem' := by
        rintro c J ⟨hJ, hJt, hJs, hJh⟩
        refine ⟨fun r m h t x ↦ ?_, fun r m h x t ↦ ?_, fun r m x t ↦ ?_, fun r m p ↦ ?_⟩
        · rw [ContinuousLinearMap.map_smul, ContinuousLinearMap.map_smul, FunLike.coe_smul,
            FunLike.coe_smul, Pi.smul_apply, LinearIsometryEquiv.map_smul]
          exact (hJ r m h t x).const_smul c
        · have h' := (hJt r m h x t).const_smul c
          rw [ContinuousLinearMap.map_smul, ContinuousLinearMap.map_smul, FunLike.coe_smul,
            FunLike.coe_smul, Pi.smul_apply]
          simpa only [ParabolicC2HolderSpace.timeExtension_def, Pi.smul_apply, Pi.smul_def] using h'
        · rw [ContinuousLinearMap.map_smul, ContinuousLinearMap.map_smul, lp.coeFn_smul,
            Pi.smul_apply, HolderSpace.smul_apply, hJs r m x t, FunLike.coe_smul, Pi.smul_apply]
          split_ifs
          · rfl
          · rw [smul_zero]
        · rw [ContinuousLinearMap.map_smul, ContinuousLinearMap.map_smul, HolderSpace.smul_apply,
            hJh r m p, FunLike.coe_smul, Pi.smul_apply]
          split_ifs
          · rfl
          · rw [smul_zero] } : Submodule ℝ V))
    (PiLp 1 fun i : parabolicDerivPairs k ↦ WithLp 1
      ((slab (E := E) a b →ᵇ (E [×i.1.2]→L[ℝ] F)) ×
        WithLp 1 (lp (fun _ : E ↦ HolderSpace ((1 + α) / 2) (Icc a b) (E [×i.1.2]→L[ℝ] F)) ∞ ×
          HolderSpace α (slab (E := E) a b) (E [×i.1.2]→L[ℝ] F))))
    (fun r m ↦ if h : (r, m) ∈ parabolicDerivPairs k then
      (WithLp.fstL 1 ℝ _ _).comp (PiLp.proj 1 _ (⟨(r, m), h⟩ : parabolicDerivPairs k))
      else 0)
    (fun r m ↦ if h : (r, m) ∈ parabolicDerivPairs k then
      (WithLp.fstL 1 ℝ _ _).comp
        ((WithLp.sndL 1 ℝ _ _).comp (PiLp.proj 1 _ (⟨(r, m), h⟩ : parabolicDerivPairs k)))
      else 0)
    (fun r m ↦ if h : (r, m) ∈ parabolicDerivPairs k then
      (WithLp.sndL 1 ℝ _ _).comp
        ((WithLp.sndL 1 ℝ _ _).comp (PiLp.proj 1 _ (⟨(r, m), h⟩ : parabolicDerivPairs k)))
      else 0))

namespace ParabolicCkHolderSpace

variable {hab : a < b}

/-! ### The jet space and the field projections -/

variable (k α E F a b) in
/-- The ambient jet space: for each pair `(r, m)` of parabolic order at most `k`, a bounded
continuous field, a family of Hölder time slices and a bounded Hölder field, with the `ℓ¹` norm. -/
private abbrev Jet := PiLp 1 fun i : parabolicDerivPairs k ↦ WithLp 1
  ((slab (E := E) a b →ᵇ (E [×i.1.2]→L[ℝ] F)) ×
    WithLp 1 (lp (fun _ : E ↦ HolderSpace ((1 + α) / 2) (Icc a b) (E [×i.1.2]→L[ℝ] F)) ∞ ×
      HolderSpace α (slab (E := E) a b) (E [×i.1.2]→L[ℝ] F)))

variable (k α E F a b) in
/-- Shortcut instance for the jet space, keeping instance search on it shallow. -/
private local instance instNormedAddCommGroupJet : NormedAddCommGroup (Jet k α E F a b) :=
  inferInstance

variable (k α E F a b) in
/-- Shortcut instance for scalar operations on the jet space. -/
private local instance instNormedSpaceJet : NormedSpace ℝ (Jet k α E F a b) :=
  inferInstance

variable (α E F a b) in
/-- Shortcut instance: families of Hölder time slices of Banach-valued fields are complete. -/
private local instance instCompleteSpaceSlices [CompleteSpace F] (n : ℕ) :
    CompleteSpace (lp (fun _ : E ↦ HolderSpace ((1 + α) / 2) (Icc a b) (E [×n]→L[ℝ] F)) ∞) :=
  inferInstance

variable (k α E F a b) in
/-- Shortcut instance: the jet space of Banach-valued fields is complete. -/
private local instance instCompleteSpaceJet [CompleteSpace F] : CompleteSpace (Jet k α E F a b) :=
  inferInstance

/-- The bounded continuous field of a jet at `(r, m)`, zero unless `2 r + m ≤ k`. -/
private def fieldL (r m : ℕ) : Jet k α E F a b →L[ℝ] (slab (E := E) a b →ᵇ (E [×m]→L[ℝ] F)) :=
  if h : (r, m) ∈ parabolicDerivPairs k then
    (WithLp.fstL 1 ℝ _ _).comp (PiLp.proj 1 _ (⟨(r, m), h⟩ : parabolicDerivPairs k))
  else 0

/-- The family of time slices of a jet at `(r, m)`, zero unless `2 r + m ≤ k`. -/
private def slicesL (r m : ℕ) : Jet k α E F a b →L[ℝ]
    lp (fun _ : E ↦ HolderSpace ((1 + α) / 2) (Icc a b) (E [×m]→L[ℝ] F)) ∞ :=
  if h : (r, m) ∈ parabolicDerivPairs k then
    (WithLp.fstL 1 ℝ _ _).comp
      ((WithLp.sndL 1 ℝ _ _).comp (PiLp.proj 1 _ (⟨(r, m), h⟩ : parabolicDerivPairs k)))
  else 0

/-- The bounded Hölder field of a jet at `(r, m)`, zero unless `2 r + m ≤ k`. -/
private def holderL (r m : ℕ) :
    Jet k α E F a b →L[ℝ] HolderSpace α (slab (E := E) a b) (E [×m]→L[ℝ] F) :=
  if h : (r, m) ∈ parabolicDerivPairs k then
    (WithLp.sndL 1 ℝ _ _).comp
      ((WithLp.sndL 1 ℝ _ _).comp (PiLp.proj 1 _ (⟨(r, m), h⟩ : parabolicDerivPairs k)))
  else 0

private theorem fieldL_of_notMem {r m : ℕ} (h : (r, m) ∉ parabolicDerivPairs k) :
    fieldL (k := k) (α := α) (E := E) (F := F) (a := a) (b := b) r m = 0 :=
  dite_eq_right h

private theorem slicesL_of_notMem {r m : ℕ} (h : (r, m) ∉ parabolicDerivPairs k) :
    slicesL (k := k) (α := α) (E := E) (F := F) (a := a) (b := b) r m = 0 :=
  dite_eq_right h

private theorem holderL_of_notMem {r m : ℕ} (h : (r, m) ∉ parabolicDerivPairs k) :
    holderL (k := k) (α := α) (E := E) (F := F) (a := a) (b := b) r m = 0 :=
  dite_eq_right h

private theorem fieldL_apply (J : Jet k α E F a b) (i : parabolicDerivPairs k) :
    fieldL i.1.1 i.1.2 J = (J i).ofLp.1 := by
  rw [fieldL, dite_eq_left i.2]
  -- The pair `(i.1.1, i.1.2)` is `i.1` by eta for structures.
  rfl

private theorem slicesL_apply (J : Jet k α E F a b) (i : parabolicDerivPairs k) :
    slicesL i.1.1 i.1.2 J = (J i).ofLp.2.ofLp.1 := by
  rw [slicesL, dite_eq_left i.2]
  -- The pair `(i.1.1, i.1.2)` is `i.1` by eta for structures.
  rfl

private theorem holderL_apply (J : Jet k α E F a b) (i : parabolicDerivPairs k) :
    holderL i.1.1 i.1.2 J = (J i).ofLp.2.ofLp.2 := by
  rw [holderL, dite_eq_left i.2]
  -- The pair `(i.1.1, i.1.2)` is `i.1` by eta for structures.
  rfl

/-- A jet is determined by its fields, slices and Hölder fields. -/
private theorem jet_ext {J K : Jet k α E F a b} (hf : ∀ r m, fieldL r m J = fieldL r m K)
    (hs : ∀ r m, slicesL r m J = slicesL r m K) (hh : ∀ r m, holderL r m J = holderL r m K) :
    J = K := by
  ext1 i
  apply WithLp.ofLp_injective 1
  refine Prod.ext ?_ (WithLp.ofLp_injective 1 (Prod.ext ?_ ?_))
  · simpa only [fieldL_apply] using hf i.1.1 i.1.2
  · simpa only [slicesL_apply] using hs i.1.1 i.1.2
  · simpa only [holderL_apply] using hh i.1.1 i.1.2

/-- The derivative identities of a jet: the membership condition of `ParabolicCkHolderSpace`. -/
private def IsJetGraph (hab : a < b) (J : Jet k α E F a b) : Prop :=
  (∀ r m, 2 * r + m + 1 ≤ k → ∀ (t : Icc a b) (x : E),
    HasFDerivAt (fun y ↦ fieldL r m J (slabMk y t))
      (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (m + 1) ↦ E) F
        (fieldL r (m + 1) J (slabMk x t))) x) ∧
  (∀ r m, 2 * r + m + 2 ≤ k → ∀ (x : E) (t : Icc a b),
    HasDerivWithinAt (ParabolicC2HolderSpace.timeExtension hab.le (fieldL r m J) x)
      (fieldL (r + 1) m J (slabMk x t)) (Icc a b) t) ∧
  (∀ r m (x : E) (t : Icc a b), slicesL r m J x t =
    if 2 * r + m + 1 = k then fieldL r m J (slabMk x t) else 0) ∧
  ∀ r m (p : slab (E := E) a b), holderL r m J p =
    if 2 * r + m = k then fieldL r m J p else 0

instance instNormedAddCommGroup : NormedAddCommGroup (ParabolicCkHolderSpace k α E F hab) := by
  unfold ParabolicCkHolderSpace
  infer_instance

instance instNormedSpace : NormedSpace ℝ (ParabolicCkHolderSpace k α E F hab) := by
  unfold ParabolicCkHolderSpace
  infer_instance

/-- The underlying jet, as a continuous linear map: the inclusion of the derivative graph into the
jet space. -/
private def toJetL : ParabolicCkHolderSpace k α E F hab →L[ℝ] Jet k α E F a b := by
  unfold ParabolicCkHolderSpace
  exact Submodule.subtypeL _

private theorem isJetGraph_toJetL (f : ParabolicCkHolderSpace k α E F hab) :
    IsJetGraph hab (toJetL f) :=
  -- `toJetL` is the submodule inclusion, so its value is the underlying jet of `f`, and
  -- membership in the derivative graph is `IsJetGraph` after beta reduction.
  f.2

private theorem toJetL_injective :
    Function.Injective (toJetL (k := k) (α := α) (E := E) (F := F) (hab := hab)) :=
  -- `toJetL` is the submodule inclusion.
  Subtype.val_injective

private theorem norm_toJetL (f : ParabolicCkHolderSpace k α E F hab) : ‖toJetL f‖ = ‖f‖ :=
  Submodule.norm_coe f

/-- An element from a jet satisfying the derivative identities. -/
private def ofJet (J : Jet k α E F a b) (hJ : IsJetGraph hab J) :
    ParabolicCkHolderSpace k α E F hab := by
  unfold ParabolicCkHolderSpace
  -- Membership in the derivative graph is `IsJetGraph` after beta reduction.
  exact ⟨J, hJ⟩

/-- The jets of elements are exactly the jets satisfying the derivative identities. -/
private theorem range_toJetL :
    Set.range (toJetL (k := k) (α := α) (E := E) (F := F) (hab := hab)) =
      {J | IsJetGraph hab J} := by
  refine Set.Subset.antisymm ?_ fun J hJ ↦ ⟨ofJet J hJ, rfl⟩
  rintro _ ⟨f, rfl⟩
  exact isJetGraph_toJetL f

/-! ### The derivative fields -/

/-- The bounded continuous field `D_t^r D_x^m u` of `u ∈ C_{par,b}^{k+α}`, with values in
`m`-multilinear maps. It is zero unless `2 r + m ≤ k`; for `2 r + m ≤ k` it is the `m`-th spatial
derivative of the `r`-th time derivative of `u` (`ParabolicCkHolderSpace.mixedDerivL_slabMk`). -/
def mixedDerivL (r m : ℕ) :
    ParabolicCkHolderSpace k α E F hab →L[ℝ] (slab (E := E) a b →ᵇ (E [×m]→L[ℝ] F)) :=
  (fieldL r m).comp toJetL

/-- The top-order field `D_t^r D_x^m u`, `2 r + m = k`, as a bounded parabolically `α`-Hölder map.
It is zero unless `2 r + m = k`. -/
def mixedDerivHolderL (r m : ℕ) :
    ParabolicCkHolderSpace k α E F hab →L[ℝ] HolderSpace α (slab (E := E) a b) (E [×m]→L[ℝ] F) :=
  (holderL r m).comp toJetL

/-- The family `x ↦ (t ↦ D_t^r D_x^m u (x, t))` of `(1 + α) / 2`-Hölder time slices of the field
of order `2 r + m = k - 1`, bounded uniformly in `x`. It is zero unless `2 r + m + 1 = k`. -/
def timeSliceL (r m : ℕ) : ParabolicCkHolderSpace k α E F hab →L[ℝ]
    lp (fun _ : E ↦ HolderSpace ((1 + α) / 2) (Icc a b) (E [×m]→L[ℝ] F)) ∞ :=
  (slicesL r m).comp toJetL

private theorem mixedDerivL_apply' (r m : ℕ) (f : ParabolicCkHolderSpace k α E F hab) :
    mixedDerivL r m f = fieldL r m (toJetL f) :=
  rfl

/-- The fields beyond the order `k` vanish. -/
theorem mixedDerivL_of_lt {r m : ℕ} (h : k < 2 * r + m) :
    mixedDerivL (k := k) (α := α) (E := E) (F := F) (hab := hab) r m = 0 := by
  rw [mixedDerivL, fieldL_of_notMem (by simpa using h), ContinuousLinearMap.zero_comp]

/-- The Hölder field vanishes off the top order. -/
theorem mixedDerivHolderL_of_ne {r m : ℕ} (h : 2 * r + m ≠ k) :
    mixedDerivHolderL (k := k) (α := α) (E := E) (F := F) (hab := hab) r m = 0 := by
  refine ContinuousLinearMap.ext fun f ↦ HolderSpace.ext fun p ↦ ?_
  by_cases hm : (r, m) ∈ parabolicDerivPairs k
  · rw [mixedDerivHolderL, ContinuousLinearMap.comp_apply, (isJetGraph_toJetL f).2.2.2 r m p,
      ite_eq_right h, zero_apply, HolderSpace.zero_apply]
  · rw [mixedDerivHolderL, holderL_of_notMem hm, ContinuousLinearMap.zero_comp, zero_apply]

/-- The family of time slices vanishes off the order `k - 1`. -/
theorem timeSliceL_of_ne {r m : ℕ} (h : 2 * r + m + 1 ≠ k) :
    timeSliceL (k := k) (α := α) (E := E) (F := F) (hab := hab) r m = 0 := by
  refine ContinuousLinearMap.ext fun f ↦ lp.ext (funext fun x ↦ HolderSpace.ext fun t ↦ ?_)
  rw [timeSliceL, ContinuousLinearMap.comp_apply, (isJetGraph_toJetL f).2.2.1 r m x t,
    ite_eq_right h, zero_apply, lp.coeFn_zero, Pi.zero_apply, HolderSpace.zero_apply]

/-- **Spatial derivatives.** For `2 r + m < k`, the field `D_t^r D_x^(m+1) u`, curried on the
left, is the spatial Fréchet derivative of `D_t^r D_x^m u` on every time slice. -/
theorem hasFDerivAt_mixedDerivL (f : ParabolicCkHolderSpace k α E F hab) {r m : ℕ}
    (h : 2 * r + m + 1 ≤ k) (t : Icc a b) (x : E) :
    HasFDerivAt (fun y ↦ mixedDerivL r m f (slabMk y t))
      (mixedDerivL r (m + 1) f (slabMk x t)).curryLeft x :=
  -- The left-currying equivalence applied to a map is `curryLeft` by definition.
  (isJetGraph_toJetL f).1 r m h t x

/-- **Time derivatives.** For `2 r + m + 2 ≤ k`, the field `D_t^(r+1) D_x^m u` is the derivative of
`D_t^r D_x^m u` in time within `[a, b]`, one-sided at the endpoints. -/
theorem hasDerivWithinAt_mixedDerivL (f : ParabolicCkHolderSpace k α E F hab) {r m : ℕ}
    (h : 2 * r + m + 2 ≤ k) (x : E) (t : Icc a b) :
    HasDerivWithinAt (ParabolicC2HolderSpace.timeExtension hab.le (mixedDerivL r m f) x)
      (mixedDerivL (r + 1) m f (slabMk x t)) (Icc a b) t :=
  (isJetGraph_toJetL f).2.1 r m h x t

/-- The Hölder field of top order records the field `D_t^r D_x^m u`. -/
theorem toBoundedContinuousFunction_mixedDerivHolderL (f : ParabolicCkHolderSpace k α E F hab)
    {r m : ℕ} (h : 2 * r + m = k) :
    (mixedDerivHolderL r m f).toBoundedContinuousFunction = mixedDerivL r m f := by
  ext1 p
  rw [HolderSpace.toBoundedContinuousFunction_apply, mixedDerivHolderL,
    ContinuousLinearMap.comp_apply, (isJetGraph_toJetL f).2.2.2 r m p, ite_eq_left h,
    mixedDerivL_apply']

/-- The time slices of order `k - 1` are those of the field `D_t^r D_x^m u`. -/
theorem timeSliceL_apply (f : ParabolicCkHolderSpace k α E F hab) {r m : ℕ}
    (h : 2 * r + m + 1 = k) (x : E) (t : Icc a b) :
    timeSliceL r m f x t = mixedDerivL r m f (slabMk x t) := by
  rw [timeSliceL, ContinuousLinearMap.comp_apply, (isJetGraph_toJetL f).2.2.1 r m x t,
    ite_eq_left h, mixedDerivL_apply']

/-- The fields of top order `2 r + m = k` are parabolically `α`-Hölder. -/
theorem memHolder_mixedDerivL (f : ParabolicCkHolderSpace k α E F hab) {r m : ℕ}
    (h : 2 * r + m = k) : MemHolder α (mixedDerivL r m f : slab (E := E) a b → E [×m]→L[ℝ] F) := by
  rw [← toBoundedContinuousFunction_mixedDerivHolderL f h]
  exact (mixedDerivHolderL r m f).memHolder

/-- The time slices of the fields of order `2 r + m = k - 1` are `(1 + α) / 2`-Hölder. -/
theorem memHolder_mixedDerivL_slabMk (f : ParabolicCkHolderSpace k α E F hab) {r m : ℕ}
    (h : 2 * r + m + 1 = k) (x : E) :
    MemHolder ((1 + α) / 2) fun t : Icc a b ↦ mixedDerivL r m f (slabMk x t) := by
  have hm := (timeSliceL r m f x).memHolder
  rwa [HolderSpace.coe_toBoundedContinuousFunction,
    show (timeSliceL r m f x : Icc a b → E [×m]→L[ℝ] F) = fun t ↦ mixedDerivL r m f (slabMk x t)
      from funext (timeSliceL_apply f h x)] at hm

/-! ### The underlying map -/

/-- The underlying map of an element: its order-zero field, evaluated on the empty tuple. Use the
coercion `⇑f` instead. -/
def toFun (f : ParabolicCkHolderSpace k α E F hab) (p : slab (E := E) a b) : F :=
  (mixedDerivL 0 0 f p).curry0

/-- The order-zero field is the map, read as a `0`-multilinear map. -/
private theorem timeExtension_toFun (f : ParabolicCkHolderSpace k α E F hab) (x : E) (s : ℝ) :
    ParabolicC2HolderSpace.timeExtension hab.le f.toFun x s =
      (ParabolicC2HolderSpace.timeExtension hab.le (mixedDerivL 0 0 f) x s).curry0 := by
  simp only [ParabolicC2HolderSpace.timeExtension_def, toFun]

/-- The iterated time derivatives of the map are the fields `D_t^r u`. -/
private theorem iteratedDerivWithin_toFun (f : ParabolicCkHolderSpace k α E F hab) {r : ℕ}
    (h : 2 * r ≤ k) (x : E) : EqOn
      (iteratedDerivWithin r (ParabolicC2HolderSpace.timeExtension hab.le f.toFun x) (Icc a b))
      (fun s ↦ (ParabolicC2HolderSpace.timeExtension hab.le (mixedDerivL r 0 f) x s).curry0)
      (Icc a b) := by
  induction r with
  | zero =>
    intro s _
    rw [iteratedDerivWithin_zero, timeExtension_toFun]
  | succ r ih =>
    intro s hs
    have hd := HasFDerivAt.comp_hasDerivWithinAt s
      ((continuousMultilinearCurryFin0 ℝ E F).toContinuousLinearEquiv :
        (E [×0]→L[ℝ] F) →L[ℝ] F).hasFDerivAt
      (hasDerivWithinAt_mixedDerivL f (r := r) (m := 0) (by omega) x ⟨s, hs⟩)
    -- Evaluation at the empty tuple is `curry0`.
    have hd' : HasDerivWithinAt
        (fun s ↦ (ParabolicC2HolderSpace.timeExtension hab.le (mixedDerivL r 0 f) x s).curry0)
        (mixedDerivL (r + 1) 0 f (slabMk x ⟨s, hs⟩)).curry0 (Icc a b) s := hd
    rw [iteratedDerivWithin_succ, derivWithin_congr (ih (by omega)) (ih (by omega) hs),
      hd'.derivWithin (uniqueDiffOn_Icc hab s hs)]
    simp only [ParabolicC2HolderSpace.timeExtension_def, projIcc_of_mem hab.le hs]

/-- The recorded spatial derivatives of `D_t^r u` form a Taylor series up to order `k - 2 r`. -/
private theorem hasFTaylorSeriesUpTo_mixedDerivL (f : ParabolicCkHolderSpace k α E F hab) (r : ℕ)
    (t : Icc a b) :
    HasFTaylorSeriesUpTo ((k - 2 * r : ℕ) : WithTop ℕ∞)
      (fun y ↦ (mixedDerivL r 0 f (slabMk y t)).curry0)
      (fun y m ↦ mixedDerivL r m f (slabMk y t)) where
  zero_eq _ := rfl
  fderiv m hm x := by
    have hmk : m < k - 2 * r := by exact_mod_cast hm
    exact hasFDerivAt_mixedDerivL f (by omega) t x
  cont m _ := (mixedDerivL r m f).continuous.comp (continuous_slabMk.comp
    (continuous_id.prodMk continuous_const))

/-- The spatial derivatives of `D_t^r u` are the fields `D_t^r D_x^m u`. -/
private theorem iteratedFDeriv_mixedDerivL_zero (f : ParabolicCkHolderSpace k α E F hab)
    {r m : ℕ} (h : 2 * r + m ≤ k) (x : E) (t : Icc a b) :
    iteratedFDeriv ℝ m (fun y ↦ (mixedDerivL r 0 f (slabMk y t)).curry0) x =
      mixedDerivL r m f (slabMk x t) :=
  ((hasFTaylorSeriesUpTo_mixedDerivL f r t).eq_iteratedFDeriv (by exact_mod_cast (by omega))
    x).symm

/-- The fields are the mixed derivatives of the underlying map. -/
private theorem mixedDerivL_slabMk_toFun (f : ParabolicCkHolderSpace k α E F hab) {r m : ℕ}
    (h : 2 * r + m ≤ k) (x : E) (t : Icc a b) :
    mixedDerivL r m f (slabMk x t) = iteratedFDeriv ℝ m (fun y ↦ iteratedDerivWithin r
      (ParabolicC2HolderSpace.timeExtension hab.le f.toFun y) (Icc a b) t) x := by
  rw [← iteratedFDeriv_mixedDerivL_zero f h x t]
  congr 1
  funext y
  rw [iteratedDerivWithin_toFun f (by omega) y t.2]
  simp only [ParabolicC2HolderSpace.timeExtension_of_mem]

/-- An element is determined by its underlying map. -/
theorem toFun_injective :
    Function.Injective (toFun (k := k) (α := α) (E := E) (F := F) (hab := hab)) := by
  intro f g hfg
  have hfield : ∀ r m, mixedDerivL r m f = mixedDerivL r m g := fun r m ↦ by
    by_cases h : 2 * r + m ≤ k
    · ext1 p
      obtain ⟨x, t, rfl⟩ : ∃ x t, slabMk x t = p := ⟨_, _, slabMk_space_slabTime p⟩
      rw [mixedDerivL_slabMk_toFun f h, mixedDerivL_slabMk_toFun g h, hfg]
    · rw [mixedDerivL_of_lt (by omega), zero_apply,
        zero_apply]
  apply toJetL_injective
  refine jet_ext (fun r m ↦ hfield r m) (fun r m ↦ ?_) (fun r m ↦ ?_)
  · by_cases h : 2 * r + m + 1 = k
    · ext x t
      have hf := timeSliceL_apply f h x t
      have hg := timeSliceL_apply g h x t
      rw [timeSliceL, ContinuousLinearMap.comp_apply] at hf hg
      rw [hf, hg, hfield]
    · have hf := DFunLike.congr_fun (timeSliceL_of_ne (hab := hab) (α := α) (E := E) (F := F) h) f
      have hg := DFunLike.congr_fun (timeSliceL_of_ne (hab := hab) (α := α) (E := E) (F := F) h) g
      rw [timeSliceL, ContinuousLinearMap.comp_apply] at hf hg
      rw [hf, hg, zero_apply, zero_apply]
  · by_cases h : 2 * r + m = k
    · apply HolderSpace.ext
      intro p
      have hf := DFunLike.congr_fun (toBoundedContinuousFunction_mixedDerivHolderL f h) p
      have hg := DFunLike.congr_fun (toBoundedContinuousFunction_mixedDerivHolderL g h) p
      rw [HolderSpace.toBoundedContinuousFunction_apply, mixedDerivHolderL,
        ContinuousLinearMap.comp_apply] at hf hg
      rw [hf, hg, hfield]
    · have hf := DFunLike.congr_fun
        (mixedDerivHolderL_of_ne (hab := hab) (α := α) (E := E) (F := F) h) f
      have hg := DFunLike.congr_fun
        (mixedDerivHolderL_of_ne (hab := hab) (α := α) (E := E) (F := F) h) g
      rw [mixedDerivHolderL, ContinuousLinearMap.comp_apply] at hf hg
      rw [hf, hg, zero_apply, zero_apply]

instance instFunLike : FunLike (ParabolicCkHolderSpace k α E F hab) (slab (E := E) a b) F where
  coe := toFun
  coe_injective := toFun_injective

@[simp]
theorem toFun_eq_coe (f : ParabolicCkHolderSpace k α E F hab) : f.toFun = ⇑f :=
  (rfl)

/-- Two elements are equal when their underlying maps agree pointwise. -/
@[ext]
theorem ext {f g : ParabolicCkHolderSpace k α E F hab} (h : ∀ p, f p = g p) : f = g :=
  DFunLike.ext f g h

/-- The order-zero field is the underlying map, read as a `0`-multilinear map. -/
@[simp]
theorem mixedDerivL_zero_zero_apply (f : ParabolicCkHolderSpace k α E F hab)
    (p : slab (E := E) a b) (v : Fin 0 → E) : mixedDerivL 0 0 f p v = f p := by
  rw [Subsingleton.elim v 0, ← toFun_eq_coe, toFun, ContinuousMultilinearMap.curry0_apply]

/-- **The fields are the mixed derivatives.** For `2 r + m ≤ k`, the field `D_t^r D_x^m u` at
`(x, t)` is the `m`-th iterated Fréchet derivative in `x` of the `r`-th iterated derivative of `u`
in time within `[a, b]`. -/
theorem mixedDerivL_slabMk (f : ParabolicCkHolderSpace k α E F hab) {r m : ℕ}
    (h : 2 * r + m ≤ k) (x : E) (t : Icc a b) :
    mixedDerivL r m f (slabMk x t) = iteratedFDeriv ℝ m (fun y ↦ iteratedDerivWithin r
      (ParabolicC2HolderSpace.timeExtension hab.le f y) (Icc a b) t) x :=
  mixedDerivL_slabMk_toFun f h x t

/-- For `m ≤ k`, the field `D_x^m u` is the `m`-th iterated spatial Fréchet derivative of `u`. -/
theorem mixedDerivL_zero_slabMk (f : ParabolicCkHolderSpace k α E F hab) {m : ℕ} (h : m ≤ k)
    (x : E) (t : Icc a b) :
    mixedDerivL 0 m f (slabMk x t) = iteratedFDeriv ℝ m (fun y ↦ f (slabMk y t)) x := by
  rw [mixedDerivL_slabMk f (by omega)]
  congr 1
  funext y
  rw [iteratedDerivWithin_zero, ParabolicC2HolderSpace.timeExtension_of_mem]

/-- For `2 r ≤ k`, the field `D_t^r u`, read as a `0`-multilinear map, is the `r`-th iterated
derivative of `u` in time within `[a, b]`. -/
theorem curry0_mixedDerivL_slabMk (f : ParabolicCkHolderSpace k α E F hab) {r : ℕ}
    (h : 2 * r ≤ k) (x : E) (t : Icc a b) :
    (mixedDerivL r 0 f (slabMk x t)).curry0 = iteratedDerivWithin r
      (ParabolicC2HolderSpace.timeExtension hab.le f x) (Icc a b) t := by
  have hd := iteratedDerivWithin_toFun f h x t.2
  simp only [toFun_eq_coe] at hd
  rw [hd, ParabolicC2HolderSpace.timeExtension_of_mem]

@[simp]
theorem coe_zero : ⇑(0 : ParabolicCkHolderSpace k α E F hab) = 0 := by
  ext p
  simp [← toFun_eq_coe, toFun, ContinuousMultilinearMap.curry0_apply, -mixedDerivL_zero_zero_apply]

@[simp]
theorem coe_add (f g : ParabolicCkHolderSpace k α E F hab) : ⇑(f + g) = f + g := by
  ext p
  simp [← toFun_eq_coe, toFun, ContinuousMultilinearMap.curry0_apply, -mixedDerivL_zero_zero_apply]

@[simp]
theorem coe_smul (c : ℝ) (f : ParabolicCkHolderSpace k α E F hab) : ⇑(c • f) = c • ⇑f := by
  ext p
  simp [← toFun_eq_coe, toFun, ContinuousMultilinearMap.curry0_apply, -mixedDerivL_zero_zero_apply]

/-! ### Construction from the fields -/

section Mk

variable (D : ℕ → ∀ m : ℕ, slab (E := E) a b →ᵇ (E [×m]→L[ℝ] F))

private theorem coe_compContinuous_timeSlice {n : ℕ} (g : slab (E := E) a b →ᵇ (E [×n]→L[ℝ] F))
    (x : E) : ⇑(g.compContinuous (timeSlice x)) = fun t ↦ g (slabMk x t) :=
  funext fun t ↦ by rw [BoundedContinuousFunction.compContinuous_apply, timeSlice_apply]

/-- The families of Hölder time slices of the fields of order `k - 1` with uniformly Hölder time
slices, and zero at the other orders. -/
private def mkSlices (hs : ∀ r m, 2 * r + m + 1 = k → ∃ C, ∀ x : E,
      HolderWith C ((1 + α) / 2) fun t : Icc a b ↦ D r m (slabMk x t)) (r m : ℕ) :
    lp (fun _ : E ↦ HolderSpace ((1 + α) / 2) (Icc a b) (E [×m]→L[ℝ] F)) ∞ :=
  if h : 2 * r + m + 1 = k then
    ⟨fun x ↦ HolderSpace.ofBoundedContinuousFunction ((D r m).compContinuous (timeSlice x))
      (by simpa only [coe_compContinuous_timeSlice] using ((hs r m h).choose_spec x).memHolder),
      memℓp_infty ⟨‖D r m‖ + (hs r m h).choose, by
        rintro _ ⟨x, rfl⟩
        refine HolderSpace.norm_le_of_norm_le_of_holderWith (norm_nonneg _) (fun t ↦ ?_)
          fun t s ↦ ?_
        · rw [HolderSpace.ofBoundedContinuousFunction_apply, coe_compContinuous_timeSlice]
          exact (D r m).norm_coe_le_norm _
        · simpa only [HolderSpace.ofBoundedContinuousFunction_apply,
            coe_compContinuous_timeSlice] using (hs r m h).choose_spec x t s⟩⟩
  else 0

/-- The Hölder fields of the top-order fields, and zero at the other orders. -/
private def mkHolder
    (hh : ∀ r m, 2 * r + m = k → MemHolder α (D r m : slab (E := E) a b → E [×m]→L[ℝ] F))
    (r m : ℕ) : HolderSpace α (slab (E := E) a b) (E [×m]→L[ℝ] F) :=
  if h : 2 * r + m = k then HolderSpace.ofBoundedContinuousFunction (D r m) (hh r m h) else 0

/-- The jet of a family of fields with Hölder fields and slices at the top two orders. -/
private def mkJet (hs : ∀ r m, 2 * r + m + 1 = k → ∃ C, ∀ x : E,
      HolderWith C ((1 + α) / 2) fun t : Icc a b ↦ D r m (slabMk x t))
    (hh : ∀ r m, 2 * r + m = k → MemHolder α (D r m : slab (E := E) a b → E [×m]→L[ℝ] F)) :
    Jet k α E F a b :=
  WithLp.toLp 1 fun i ↦ WithLp.toLp 1
    (D i.1.1 i.1.2, WithLp.toLp 1 (mkSlices D hs i.1.1 i.1.2, mkHolder D hh i.1.1 i.1.2))

variable {D}
variable {hs : ∀ r m, 2 * r + m + 1 = k → ∃ C, ∀ x : E,
      HolderWith C ((1 + α) / 2) fun t : Icc a b ↦ D r m (slabMk x t)}
  {hh : ∀ r m, 2 * r + m = k → MemHolder α (D r m : slab (E := E) a b → E [×m]→L[ℝ] F)}

private theorem fieldL_mkJet {r m : ℕ} (h : 2 * r + m ≤ k) : fieldL r m (mkJet D hs hh) = D r m :=
  fieldL_apply (mkJet D hs hh) ⟨(r, m), mem_parabolicDerivPairs.2 h⟩

private theorem slicesL_mkJet {r m : ℕ} (h : 2 * r + m ≤ k) :
    slicesL r m (mkJet D hs hh) = mkSlices D hs r m :=
  slicesL_apply (mkJet D hs hh) ⟨(r, m), mem_parabolicDerivPairs.2 h⟩

private theorem holderL_mkJet {r m : ℕ} (h : 2 * r + m ≤ k) :
    holderL r m (mkJet D hs hh) = mkHolder D hh r m :=
  holderL_apply (mkJet D hs hh) ⟨(r, m), mem_parabolicDerivPairs.2 h⟩

private theorem isJetGraph_mkJet
    (hx : ∀ r m, 2 * r + m + 1 ≤ k → ∀ (t : Icc a b) (x : E),
      HasFDerivAt (fun y ↦ D r m (slabMk y t)) (D r (m + 1) (slabMk x t)).curryLeft x)
    (ht : ∀ r m, 2 * r + m + 2 ≤ k → ∀ (x : E) (t : Icc a b),
      HasDerivWithinAt (ParabolicC2HolderSpace.timeExtension hab.le (D r m) x)
        (D (r + 1) m (slabMk x t)) (Icc a b) t) :
    IsJetGraph hab (mkJet D hs hh) := by
  refine ⟨fun r m h t x ↦ ?_, fun r m h x t ↦ ?_, fun r m x t ↦ ?_, fun r m p ↦ ?_⟩
  · rw [fieldL_mkJet (by omega), fieldL_mkJet (by omega)]
    -- The left-currying equivalence applied to a map is `curryLeft` by definition.
    exact hx r m h t x
  · rw [fieldL_mkJet (by omega), fieldL_mkJet (by omega)]
    exact ht r m h x t
  · by_cases hm : 2 * r + m ≤ k
    · rw [slicesL_mkJet hm, fieldL_mkJet hm, mkSlices]
      split_ifs
      · -- Evaluation in `lp` is the application of the underlying family.
        change HolderSpace.ofBoundedContinuousFunction _ _ t = _
        rw [HolderSpace.ofBoundedContinuousFunction_apply, coe_compContinuous_timeSlice]
      · rfl
    · rw [slicesL_of_notMem (by simpa using hm), ite_eq_right (by omega)]
      rfl
  · by_cases hm : 2 * r + m ≤ k
    · rw [holderL_mkJet hm, fieldL_mkJet hm, mkHolder]
      split_ifs
      · exact HolderSpace.ofBoundedContinuousFunction_apply _ _ _
      · rfl
    · rw [holderL_of_notMem (by simpa using hm), ite_eq_right (by omega)]
      rfl

variable (D) in
/-- Construct an element from bounded continuous fields `D r m`, `2 r + m ≤ k`, such that
`D r (m + 1)`, curried on the left, is the spatial derivative of `D r m` and `D (r + 1) m` is its
time derivative within `[a, b]`, the fields of order `k - 1` have uniformly `(1 + α) / 2`-Hölder
time slices, and the fields of order `k` are parabolically `α`-Hölder. The fields with
`2 r + m > k` are ignored. -/
def mk (hx : ∀ r m, 2 * r + m + 1 ≤ k → ∀ (t : Icc a b) (x : E),
      HasFDerivAt (fun y ↦ D r m (slabMk y t)) (D r (m + 1) (slabMk x t)).curryLeft x)
    (ht : ∀ r m, 2 * r + m + 2 ≤ k → ∀ (x : E) (t : Icc a b),
      HasDerivWithinAt (ParabolicC2HolderSpace.timeExtension hab.le (D r m) x)
        (D (r + 1) m (slabMk x t)) (Icc a b) t)
    (hs : ∀ r m, 2 * r + m + 1 = k → ∃ C, ∀ x : E,
      HolderWith C ((1 + α) / 2) fun t : Icc a b ↦ D r m (slabMk x t))
    (hh : ∀ r m, 2 * r + m = k → MemHolder α (D r m : slab (E := E) a b → E [×m]→L[ℝ] F)) :
    ParabolicCkHolderSpace k α E F hab :=
  ofJet (mkJet D hs hh) (isJetGraph_mkJet hx ht)

/-- The fields of `ParabolicCkHolderSpace.mk D _ _ _ _` of order at most `k` are the fields
`D r m`. -/
@[simp]
theorem mixedDerivL_mk (hx ht hs hh) {r m : ℕ} (h : 2 * r + m ≤ k) :
    mixedDerivL r m (mk (k := k) (α := α) (hab := hab) D hx ht hs hh) = D r m := by
  rw [mixedDerivL_apply', ← fieldL_mkJet (hs := hs) (hh := hh) h]
  -- The jet of an element built from a jet is that jet.
  rfl

/-- The underlying map of `ParabolicCkHolderSpace.mk D _ _ _ _` is the order-zero field, read
as a `0`-multilinear map. -/
@[simp]
theorem mk_apply (hx ht hs hh) (p : slab (E := E) a b) :
    mk (k := k) (α := α) (hab := hab) D hx ht hs hh p = (D 0 0 p).curry0 := by
  rw [← toFun_eq_coe, toFun, mixedDerivL_mk _ _ _ _ (by omega)]

end Mk

/-! ### The norm -/

/-- The norm of a jet is the sum of the norms of its fields, slices and Hölder fields. -/
private theorem norm_jet (J : Jet k α E F a b) :
    ‖J‖ = ∑ i : parabolicDerivPairs k, (‖fieldL i.1.1 i.1.2 J‖ +
      (‖slicesL i.1.1 i.1.2 J‖ + ‖holderL i.1.1 i.1.2 J‖)) := by
  rw [PiLp.norm_eq_of_L1]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [WithLp.prod_norm_eq_of_L1, WithLp.prod_norm_eq_of_L1, fieldL_apply, slicesL_apply,
    holderL_apply]
  -- The components of a `WithLp` product are the components of the underlying product.
  rfl

/-- The norm is the sum, over the pairs `(r, m)` with `2 r + m ≤ k`, of the supremum norm of the
field `D_t^r D_x^m u`, the norm of its family of Hölder time slices (zero unless
`2 r + m = k - 1`) and its bounded Hölder norm (zero unless `2 r + m = k`). -/
theorem norm_eq (f : ParabolicCkHolderSpace k α E F hab) :
    ‖f‖ = ∑ p ∈ parabolicDerivPairs k, (‖mixedDerivL p.1 p.2 f‖ +
      (‖timeSliceL p.1 p.2 f‖ + ‖mixedDerivHolderL p.1 p.2 f‖)) := by
  rw [← norm_toJetL, norm_jet, ← Finset.sum_coe_sort (parabolicDerivPairs k)]
  -- Each field of `f` is the corresponding field of its jet.
  rfl

/-- Each field is bounded by the norm. -/
theorem norm_mixedDerivL_le (f : ParabolicCkHolderSpace k α E F hab) (r m : ℕ) :
    ‖mixedDerivL r m f‖ ≤ ‖f‖ := by
  by_cases h : (r, m) ∈ parabolicDerivPairs k
  · rw [norm_eq]
    refine le_trans ?_ (Finset.single_le_sum (fun p _ ↦ by positivity) h)
    exact le_add_of_nonneg_right (by positivity)
  · rw [mixedDerivL_of_lt (by simpa using h), zero_apply, norm_zero]
    exact norm_nonneg f

/-- Each family of time slices is bounded by the norm. -/
theorem norm_timeSliceL_le (f : ParabolicCkHolderSpace k α E F hab) (r m : ℕ) :
    ‖timeSliceL r m f‖ ≤ ‖f‖ := by
  by_cases h : (r, m) ∈ parabolicDerivPairs k
  · rw [norm_eq]
    refine le_trans ?_ (Finset.single_le_sum (fun p _ ↦ by positivity) h)
    exact (le_add_of_nonneg_right (norm_nonneg _)).trans (le_add_of_nonneg_left (norm_nonneg _))
  · rw [timeSliceL_of_ne (by simp at h; omega), zero_apply, norm_zero]
    exact norm_nonneg f

/-- Each Hölder field is bounded by the norm. -/
theorem norm_mixedDerivHolderL_le (f : ParabolicCkHolderSpace k α E F hab) (r m : ℕ) :
    ‖mixedDerivHolderL r m f‖ ≤ ‖f‖ := by
  by_cases h : (r, m) ∈ parabolicDerivPairs k
  · rw [norm_eq]
    refine le_trans ?_ (Finset.single_le_sum (fun p _ ↦ by positivity) h)
    exact (le_add_of_nonneg_left (norm_nonneg _)).trans (le_add_of_nonneg_left (norm_nonneg _))
  · rw [mixedDerivHolderL_of_ne (by simp at h; omega), zero_apply, norm_zero]
    exact norm_nonneg f

/-! ### Completeness -/

private theorem continuous_fieldL (r m : ℕ) : Continuous fun J : Jet k α E F a b ↦ fieldL r m J :=
  (fieldL r m).continuous

private theorem continuous_slicesL (r m : ℕ) :
    Continuous fun J : Jet k α E F a b ↦ slicesL r m J :=
  (slicesL r m).continuous

private theorem continuous_holderL (r m : ℕ) :
    Continuous fun J : Jet k α E F a b ↦ holderL r m J :=
  (holderL r m).continuous

private theorem isClosed_spatialGraph (r m : ℕ) (t : Icc a b) : IsClosed {J : Jet k α E F a b |
    ∀ x, HasFDerivAt (fun y ↦ fieldL r m J (slabMk y t))
      (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (m + 1) ↦ E) F
        (fieldL r (m + 1) J (slabMk x t))) x} := by
  have hL := (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (m + 1) ↦ E) F).isometry
  simpa only [preimage_ofPred_eq, Function.comp_apply,
    BoundedContinuousFunction.coe_compContinuous, BoundedContinuousFunction.compContinuous_apply,
    Function.comp_def, spatialSlice_apply] using
    (isClosed_setOf_hasFDerivAt_comp (𝕜 := ℝ) (E := E)
      (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (m + 1) ↦ E) F)
      hL.uniformContinuous).preimage
      (((BoundedContinuousFunction.continuous_compContinuous (spatialSlice t)).comp
        (continuous_fieldL r m)).prodMk
        ((BoundedContinuousFunction.continuous_compContinuous (spatialSlice t)).comp
          (continuous_fieldL r (m + 1))))

private theorem isClosed_timeGraph (hab : a < b) (r m : ℕ) (x : E) :
    IsClosed {J : Jet k α E F a b | ∀ t : Icc a b,
      HasDerivWithinAt (ParabolicC2HolderSpace.timeExtension hab.le (fieldL r m J) x)
        (fieldL (r + 1) m J (slabMk x t)) (Icc a b) t} := by
  simpa only [preimage_ofPred_eq, Function.comp_def,
    BoundedContinuousFunction.compContinuous_apply, timeSlice_apply,
    ParabolicC2HolderSpace.timeExtension_def] using
    (isClosed_setOf_hasDerivWithinAt_Icc (F := E [×m]→L[ℝ] F) hab).preimage
      (((BoundedContinuousFunction.continuous_compContinuous (timeSlice x)).comp
        (continuous_fieldL r m)).prodMk
        ((BoundedContinuousFunction.continuous_compContinuous (timeSlice x)).comp
          (continuous_fieldL (r + 1) m)))

private theorem isClosed_sliceGraph (r m : ℕ) (x : E) (t : Icc a b) :
    IsClosed {J : Jet k α E F a b | slicesL r m J x t =
      if 2 * r + m + 1 = k then fieldL r m J (slabMk x t) else 0} := by
  refine isClosed_eq ?_ (continuous_if_const _
    (fun _ ↦ (continuous_eval_const (slabMk x t)).comp (continuous_fieldL r m))
    fun _ ↦ continuous_const)
  refine ((HolderSpace.evalCLM t).continuous.comp
    ((lp.evalCLM ℝ (fun _ : E ↦ HolderSpace ((1 + α) / 2) (Icc a b) (E [×m]→L[ℝ] F)) ∞
      x).continuous.comp (continuous_slicesL r m))).congr fun J ↦ ?_
  rw [Function.comp_apply, Function.comp_apply, HolderSpace.evalCLM_apply]
  -- Evaluation in `lp` is the application of the underlying family.
  rfl

private theorem isClosed_holderGraph (r m : ℕ) (p : slab (E := E) a b) :
    IsClosed {J : Jet k α E F a b | holderL r m J p =
      if 2 * r + m = k then fieldL r m J p else 0} := by
  refine isClosed_eq ?_ (continuous_if_const _
    (fun _ ↦ (continuous_eval_const p).comp (continuous_fieldL r m)) fun _ ↦ continuous_const)
  exact ((HolderSpace.evalCLM p).continuous.comp (continuous_holderL r m)).congr fun J ↦
    HolderSpace.evalCLM_apply _ _

private theorem isClosed_isJetGraph :
    IsClosed {J : Jet k α E F a b | IsJetGraph hab J} := by
  simpa only [IsJetGraph, ofPred_and, ofPred_forall] using
    (isClosed_iInter fun r ↦ isClosed_iInter fun m ↦ isClosed_iInter fun _ ↦
      isClosed_iInter (isClosed_spatialGraph (k := k) (α := α) (F := F) r m)).inter
    ((isClosed_iInter fun r ↦ isClosed_iInter fun m ↦ isClosed_iInter fun _ ↦
      isClosed_iInter (isClosed_timeGraph (k := k) (α := α) (F := F) hab r m)).inter
    ((isClosed_iInter fun r ↦ isClosed_iInter fun m ↦ isClosed_iInter fun x ↦
      isClosed_iInter (isClosed_sliceGraph (k := k) (α := α) (F := F) r m x)).inter
    (isClosed_iInter fun r ↦ isClosed_iInter fun m ↦
      isClosed_iInter (isClosed_holderGraph (k := k) (α := α) (F := F) r m))))

/-- Bounded parabolic Hölder maps of order `k` with Banach values form a Banach space. -/
instance instCompleteSpace [CompleteSpace F] :
    CompleteSpace (ParabolicCkHolderSpace k α E F hab) := by
  have hiso : Isometry (toJetL (k := k) (α := α) (E := E) (F := F) (hab := hab)) :=
    AddMonoidHomClass.isometry_of_norm _ norm_toJetL
  rw [completeSpace_iff_isComplete_range hiso.isUniformInducing, range_toJetL]
  exact isClosed_isJetGraph.isComplete

attribute [irreducible] instNormedAddCommGroup instNormedSpace
  _root_.TauCeti.ParabolicCkHolderSpace

end ParabolicCkHolderSpace

end TauCeti

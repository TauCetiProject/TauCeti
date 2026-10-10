/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5, OpenAI GPT-5.6 Thinking
-/
module

public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.Normed.Module.Basic

/-!
# Operator ideal families

An **operator ideal** in the sense of Pietsch is a rule assigning to every pair
of spaces `E`, `F` a linear subspace of `E →L[𝕜] F` that is stable under
composition with arbitrary bounded maps on either side, together with a norm on
that subspace dominating the operator norm and submultiplicative against outer
compositions.  Because Davis--Kahan compares operators *between different
spaces*, the ideal must be handled as a coherent family across all pairs at
once, not as a norm on a single endomorphism algebra.

The families here range over **Hilbert** spaces, with source and target still in
independent universes.  See "Why Hilbert and not Banach" below: the restriction
is forced by the examples, not by the laws.

## The single-field representation

The family is presented by exactly one datum, an extended-real-valued **gauge**

```
gauge : (E →L[𝕜] F) → ℝ≥0∞
```

defined on *all* operators, with the ideal recovered as its finiteness domain
`OperatorIdealFamily.carrier`.  This is the classical presentation of a symmetric
norming function (Gohberg--Krein): an operator lies in the ideal exactly when its
ideal norm is finite.  Three things follow.

* **Extensionality is structural.**  Two families with the same gauge are equal
  (`OperatorIdealFamily.ext`), because the gauge is the only field.  A
  representation carrying membership and a gauge as *independent* data cannot
  have such a theorem: the gauge is then unconstrained off the ideal, so two
  families can agree on every ideal element and still differ.
* **Every law is unconditional.**  In `ℝ≥0∞` the triangle inequality, the
  homogeneity `gauge (c • A) = ‖c‖ₑ * gauge A`, and the ideal bound
  `gauge (L ∘L A ∘L R) ≤ ‖L‖ₑ * gauge A * ‖R‖ₑ` all hold verbatim at
  non-members, so no law needs a membership hypothesis and no lemma needs to
  carry one.
* **The axiom list is short.**  Four laws suffice.  Closure of the ideal under
  `0`, `+`, `•`, `-`, and finite sums is a *consequence* (it is
  `Submodule` membership for `carrier`), `gauge 0 = 0` follows from homogeneity
  at `c = 0`, and definiteness follows from `enorm_le_gauge`.

## Why Hilbert and not Banach

The four laws are statements about a norm, and every one of them is meaningful
verbatim for Banach `E`, `F`.  The *examples* are not.  Of the five gauges this
development has — the operator norm, the finite Ky Fan gauges, Schatten `p`,
trace class and Hilbert--Schmidt — only the first survives outside Hilbert
space, and the obstruction is `gauge_add_le`, not the definition.  Concretely,
for the finite Ky Fan gauge `∑_{n < k} aₙ(A)` the *gauge* is defined at full
Banach generality (`ContinuousLinearMap.approximationNumber` is stated for
seminormed spaces over a `NontriviallyNormedField`) while its subadditivity is
Hilbertian: the proof runs through singular values and majorization, and the
classical additivity of approximation numbers,
`a_{m+n}(S + T) ≤ aₘ(S) + aₙ(T)`, does **not** recover it — already at `k = 2`
that bound only gives `a₀(S) + 2a₀(T) + a₁(S)`, which is not
`∑_{n<2} aₙ(S) + ∑_{n<2} aₙ(T)`.

So a Banach-wide version of this structure would be a notion with one instance
and no way to acquire the motivating ones.  The parameters are therefore Hilbert
throughout.  Re-widening is a purely mechanical edit should an instance ever
appear: no proof in this file uses the inner product, only the norm.

## Layering

`OperatorIdealFamily` keeps **independent source and target universes**.  Adjoint
symmetry cannot be added at that generality: `A✝` swaps the roles of source and
target, so a family closed under adjoints must be defined on a single universe.
That is `SymmetricOperatorIdealFamily`, which extends the diagonal
instantiation.

The two universes occur only through `max v w` in the type of the structure
itself, so `linter.checkUnivs` flags them.  **They stay independent, and the
argument is the layering itself rather than an appeal to generality**:

* `SymmetricOperatorIdealFamily` extends `OperatorIdealFamily.{u, v, v}` — it
  *is* the diagonal instantiation.  Collapse `v` and `w` and `.{u, v, v}` becomes
  `.{u, v}`: the two structures acquire the same generality, and the distinction
  this section is about stops existing.  The rectangular layer earns its second
  universe by being the thing the symmetric layer specializes.
* `Family/OperatorNorm.lean` carries a hand-written specialization of
  `instIsCompleteOperatorNormIdealFamily` precisely because the general instance
  is stated at three independent universes and instance search cannot see it once
  the symmetric family equates the last two.

So the independence is exercised, not merely declared; the linter's heuristic
reads the structure's type, where it is invisible.

## Main definitions

* `TauCeti.OperatorIdealFamily`: the gauge and its four laws.
* `TauCeti.OperatorIdealFamily.carrier`: the ideal, as a `Submodule`.
* `TauCeti.OperatorIdealFamily.Elem`: the ideal as a normed space in its own
  right — a type synonym for the carrier carrying the *ideal* norm rather than
  the operator norm inherited from the ambient space.
* `TauCeti.OperatorIdealFamily.IsComplete`: completeness of the ideal, expressed
  as `CompleteSpace` for that norm rather than as a hand-rolled Cauchy criterion.
* `TauCeti.SymmetricOperatorIdealFamily`: the adjoint-invariant diagonal layer.

## Provenance

* Original repository: Davis--Kahan/DKPS formalization (Kitware, Inc.).
* Original module: `DavisKahan/OperatorIdeal/UnitarilyInvariant/RectangularFamily.lean`
  (`RectangularSymmetricIdealFamily`, Jon Crall / OpenAI GPT-5.6 Thinking); Apache 2.0.
* Extraction class: **redesigned**.  Per the signature-polish backlog the free-data presentation
  (`Mem` plus a total real gauge constrained only on members, one universe,
  hand-rolled completeness, fourteen fields) is replaced here by the
  single-gauge presentation above, and this is the only presentation of an
  operator ideal in the library.  The legacy structure was retired downstream on
  2026-08-27, together with both directions of the conversion between the two and
  the four concrete ideals that were built by converting a canonical family into a
  legacy record and back.  Its free data survives only as
  `SymmetricOperatorIdealFamily.Core` in
  `DavisKahan/OperatorIdeal/UnitarilyInvariant/FamilyCore.lean`: constructor
  arguments for `ofCore`, carrying no gauge of their own and used by the two
  source-facing Hilbert--Schmidt ideals, which are families from the moment they
  are defined.
-/

public section

namespace TauCeti

open scoped ENNReal

universe u v w

-- What the linter reports, verbatim, with the suppression removed:
--   `OperatorIdealFamily`: universes `v`, `w` only occur together.  This usually
--   means there is a `max` expression in the type where none of these universes
--   appear on their own.
-- The observation is correct and the conclusion does not follow here.  `v` and `w`
-- are invisible apart *in this structure's type*, which is all the linter reads;
-- they are apart in its fields, and one consumer depends on exactly that:
-- `SymmetricOperatorIdealFamily` extends `OperatorIdealFamily.{u, v, v}`.  It is the
-- diagonal instantiation of this structure, so collapsing `v` and `w` would make the
-- two layers equally general and delete the distinction the module docstring calls
-- the point of the design.  `Family/OperatorNorm.lean`'s specialization of
-- `instIsCompleteOperatorNormIdealFamily` is a second place the independence bites:
-- it exists because instance search cannot find the three-universe instance once the
-- symmetric family equates the last two.
-- Decided after measuring both alternatives; the earlier
-- version of this comment said the fix was to collapse them and deferred to that lane.
-- Written here rather than left silent because this is the only one
-- of the library's ten linter suppressions with no reason at its site, and
-- `ForTauCeti/README.md` §207 forbids silencing a linter without one.
/-- A **rectangular operator ideal family** over `𝕜`, presented by its gauge.

`gauge A` is the ideal norm of `A`, taken in `ℝ≥0∞` so that it is defined on
every bounded operator: `A` belongs to the ideal exactly when `gauge A ≠ ∞`
(`OperatorIdealFamily.carrier`).  Source and target are Hilbert spaces in
independent universes (see the module docstring for why Hilbert); adjoint
symmetry is added on the diagonal by `SymmetricOperatorIdealFamily`. -/
structure OperatorIdealFamily (𝕜 : Type u) [RCLike 𝕜] where
  /-- The ideal norm, extended by `∞` off the ideal. -/
  gauge : ∀ {E : Type v} {F : Type w}
      [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
      [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F],
      (E →L[𝕜] F) → ℝ≥0∞
  /-- The gauge is subadditive. -/
  gauge_add_le : ∀ {E : Type v} {F : Type w}
      [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
      [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
      (A B : E →L[𝕜] F), gauge (A + B) ≤ gauge A + gauge B
  /-- The gauge is absolutely homogeneous.  At `c = 0` this forces
  `gauge 0 = 0`, ruling out the everywhere-infinite gauge. -/
  gauge_smul : ∀ {E : Type v} {F : Type w}
      [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
      [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
      (c : 𝕜) (A : E →L[𝕜] F), gauge (c • A) = ‖c‖ₑ * gauge A
  /-- The gauge dominates the operator norm.  Together with `gauge_add_le` this
  makes the gauge a genuine norm on the ideal rather than a seminorm. -/
  enorm_le_gauge : ∀ {E : Type v} {F : Type w}
      [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
      [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
      (A : E →L[𝕜] F), ‖A‖ₑ ≤ gauge A
  /-- The two-sided ideal law.  Finiteness of `‖L‖ₑ` and `‖R‖ₑ` makes this
  imply that the ideal is stable under outer composition. -/
  gauge_comp_le : ∀ {E H : Type v} {F G : Type w}
      [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
      [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
      [NormedAddCommGroup G] [InnerProductSpace 𝕜 G] [CompleteSpace G]
      [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
      (L : F →L[𝕜] G) (A : E →L[𝕜] F) (R : H →L[𝕜] E),
      gauge (L ∘L A ∘L R) ≤ ‖L‖ₑ * gauge A * ‖R‖ₑ

namespace OperatorIdealFamily

variable {𝕜 : Type u} [RCLike 𝕜]
variable {E H : Type v} {F G : Type w}
variable [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
variable [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
variable [NormedAddCommGroup G] [InnerProductSpace 𝕜 G] [CompleteSpace G]
variable [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
variable (N : OperatorIdealFamily.{u, v, w} 𝕜)

/-- Two ideal families with the same gauge are equal.

This is the theorem the free-data presentation cannot have: there, the gauge is
unconstrained off the ideal, so equality of the gauges *on members* — the only
thing the laws talk about — does not determine the structure. -/
@[ext]
theorem ext {N M : OperatorIdealFamily.{u, v, w} 𝕜}
    (h : ∀ {E : Type v} {F : Type w}
      [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
      [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
      (A : E →L[𝕜] F), N.gauge A = M.gauge A) : N = M := by
  cases N
  cases M
  congr 1
  funext E F _ _ _ _ _ _ A
  exact h A

/-- The gauge of the zero operator is zero. -/
@[simp]
theorem gauge_zero : N.gauge (0 : E →L[𝕜] F) = 0 := by
  have h := N.gauge_smul (0 : 𝕜) (0 : E →L[𝕜] F)
  simpa using h

/-- The gauge is definite: only the zero operator has gauge zero.  This is forced rather than
assumed -- it follows from `enorm_le_gauge`, since the operator norm is already definite. -/
theorem gauge_eq_zero {A : E →L[𝕜] F} (h : N.gauge A = 0) : A = 0 := by
  have hle : ‖A‖ₑ ≤ 0 := h ▸ N.enorm_le_gauge A
  have hz : ‖A‖ₑ = 0 := le_antisymm hle (by simp)
  rwa [enorm_eq_nnnorm, ENNReal.coe_eq_zero, nnnorm_eq_zero] at hz

/-- Definiteness as an iff. -/
theorem gauge_eq_zero_iff {A : E →L[𝕜] F} : N.gauge A = 0 ↔ A = 0 :=
  ⟨N.gauge_eq_zero, fun h => h ▸ N.gauge_zero⟩

/-- The gauge is unchanged by negation. -/
@[simp]
theorem gauge_neg (A : E →L[𝕜] F) : N.gauge (-A) = N.gauge A := by
  have h := N.gauge_smul (-1 : 𝕜) A
  simpa using h

/-- Triangle inequality in subtracted form, the shape convergence arguments use. -/
theorem gauge_sub_le (A B : E →L[𝕜] F) : N.gauge (A - B) ≤ N.gauge A + N.gauge B := by
  simpa [sub_eq_add_neg] using N.gauge_add_le A (-B)

omit [CompleteSpace E] in
/-- The identity is a contraction for the extended norm. -/
private theorem enorm_id_le : ‖ContinuousLinearMap.id 𝕜 E‖ₑ ≤ 1 := by
  rw [← ofReal_norm]
  exact ENNReal.ofReal_le_one.mpr ContinuousLinearMap.norm_id_le

/-- Subadditivity over a finite sum.

Unlike its counterpart for the historical record, this needs no membership
hypotheses: at a non-member the right-hand side is `∞`. -/
theorem gauge_sum_le {ι : Type*} (s : Finset ι) (A : ι → E →L[𝕜] F) :
    N.gauge (∑ i ∈ s, A i) ≤ ∑ i ∈ s, N.gauge (A i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha]
      exact (N.gauge_add_le _ _).trans (add_le_add le_rfl ih)

/-- Left composition by a bounded map, the `R = 1` case of the ideal law. -/
theorem gauge_comp_left_le (L : F →L[𝕜] G) (A : E →L[𝕜] F) :
    N.gauge (L ∘L A) ≤ ‖L‖ₑ * N.gauge A :=
  calc N.gauge (L ∘L A)
      = N.gauge (L ∘L A ∘L ContinuousLinearMap.id 𝕜 E) := by simp
    _ ≤ ‖L‖ₑ * N.gauge A * ‖ContinuousLinearMap.id 𝕜 E‖ₑ := N.gauge_comp_le _ _ _
    _ ≤ ‖L‖ₑ * N.gauge A * 1 := by gcongr; exact enorm_id_le
    _ = ‖L‖ₑ * N.gauge A := mul_one _

/-- Right composition by a bounded map, the `L = 1` case of the ideal law. -/
theorem gauge_comp_right_le (A : E →L[𝕜] F) (R : H →L[𝕜] E) :
    N.gauge (A ∘L R) ≤ N.gauge A * ‖R‖ₑ :=
  calc N.gauge (A ∘L R)
      = N.gauge (ContinuousLinearMap.id 𝕜 F ∘L A ∘L R) := by simp
    _ ≤ ‖ContinuousLinearMap.id 𝕜 F‖ₑ * N.gauge A * ‖R‖ₑ := N.gauge_comp_le _ _ _
    _ ≤ 1 * N.gauge A * ‖R‖ₑ := by gcongr; exact enorm_id_le
    _ = N.gauge A * ‖R‖ₑ := by rw [one_mul]

/-- Left composition by a contraction does not increase the gauge. -/
theorem gauge_comp_left_le_of_norm_le_one {L : F →L[𝕜] G} (hL : ‖L‖ₑ ≤ 1) (A : E →L[𝕜] F) :
    N.gauge (L ∘L A) ≤ N.gauge A :=
  (N.gauge_comp_left_le L A).trans (by
    calc ‖L‖ₑ * N.gauge A ≤ 1 * N.gauge A := by gcongr
      _ = N.gauge A := one_mul _)

/-- Right composition by a contraction does not increase the gauge. -/
theorem gauge_comp_right_le_of_norm_le_one (A : E →L[𝕜] F) {R : H →L[𝕜] E} (hR : ‖R‖ₑ ≤ 1) :
    N.gauge (A ∘L R) ≤ N.gauge A :=
  (N.gauge_comp_right_le A R).trans (by
    calc N.gauge A * ‖R‖ₑ ≤ N.gauge A * 1 := by gcongr
      _ = N.gauge A := mul_one _)

/-- Two-sided composition by contractions does not increase the gauge. -/
theorem gauge_comp_le_of_norm_le_one {L : F →L[𝕜] G} {A : E →L[𝕜] F} {R : H →L[𝕜] E}
    (hL : ‖L‖ₑ ≤ 1) (hR : ‖R‖ₑ ≤ 1) : N.gauge (L ∘L A ∘L R) ≤ N.gauge A :=
  (N.gauge_comp_le L A R).trans (by
    calc ‖L‖ₑ * N.gauge A * ‖R‖ₑ ≤ 1 * N.gauge A * 1 := by gcongr
      _ = N.gauge A := by simp)

/-- The ideal itself: the operators of finite gauge, as a submodule.

Closure under `0`, `+` and `•` is a consequence of the gauge laws, so the
module structure of the ideal does not have to be assumed. -/
@[expose]
def carrier : Submodule 𝕜 (E →L[𝕜] F) where
  carrier := {A | N.gauge A ≠ ∞}
  zero_mem' := by simp
  add_mem' {A B} hA hB := by
    refine ne_top_of_le_ne_top ?_ (N.gauge_add_le A B)
    exact ENNReal.add_ne_top.mpr ⟨hA, hB⟩
  smul_mem' c A hA := by
    rw [Set.mem_ofPred_eq, N.gauge_smul]
    exact ENNReal.mul_ne_top (by simp) hA

/-- Membership in the ideal is exactly finiteness of the gauge; the carrier is defined that way,
so this is `Iff.rfl` and exists only to spare call sites the unfolding. -/
@[simp]
theorem mem_carrier_iff {A : E →L[𝕜] F} : A ∈ N.carrier ↔ N.gauge A ≠ ∞ := (Iff.rfl)
/-- Members of the ideal have finite gauge. -/
theorem gauge_ne_top_of_mem {A : E →L[𝕜] F} (hA : A ∈ N.carrier) : N.gauge A ≠ ∞ := hA

/-- Members of the ideal have gauge `< ∞`, the strict form. -/
theorem gauge_lt_top_of_mem {A : E →L[𝕜] F} (hA : A ∈ N.carrier) : N.gauge A < ∞ :=
  lt_top_iff_ne_top.mpr hA

/-- Membership in the ideal is stable under outer composition. -/
theorem comp_mem_carrier (L : F →L[𝕜] G) {A : E →L[𝕜] F} (R : H →L[𝕜] E)
    (hA : A ∈ N.carrier) : L ∘L A ∘L R ∈ N.carrier := by
  refine ne_top_of_le_ne_top ?_ (N.gauge_comp_le L A R)
  exact ENNReal.mul_ne_top (ENNReal.mul_ne_top (by simp) hA) (by simp)

/-- The ideal is closed under finite sums — `Submodule.sum_mem` for the
carrier, with no separate closure axiom. -/
theorem sum_mem_carrier {ι : Type*} (s : Finset ι) {A : ι → E →L[𝕜] F}
    (hA : ∀ i ∈ s, A i ∈ N.carrier) : (∑ i ∈ s, A i) ∈ N.carrier :=
  Submodule.sum_mem _ hA

/-- The ideal between `E` and `F`, as a type carrying the **ideal** norm.

This is deliberately a type synonym rather than the subtype itself: the subtype
already inherits the *operator* norm from `E →L[𝕜] F`, and the two norms differ.

**`@[expose]`, and this is the one place in the group that needs it.**  `Elem` is
a *type*: the compiler has to see that it is a subtype in order to infer the same
representation for `Elem.val` and `Elem.mk` here as in any consuming module, and
it says so — *"locally inferred compilation type differs from type that would be
inferred in other modules"*.  That is not the `api-design` rubric's
expose-instead-of-a-lemma anti-pattern, which is about proofs relying on defeq;
no lemma can substitute for a type's representation.
-/
@[expose]
def Elem (N : OperatorIdealFamily.{u, v, w} 𝕜) (E : Type v) (F : Type w)
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F] : Type max v w :=
  _root_.Subtype fun A : E →L[𝕜] F => A ∈ N.carrier

namespace Elem

variable {N}

/-- The underlying operator of an ideal element. -/
-- `@[expose]` forced by the same compiler limitation as `Elem` above: accessors on an
-- unexposed type synonym re-infer a different compilation type downstream. Revisit when
-- the limitation the compiler reports is lifted.
@[expose]
def val (A : N.Elem E F) : E →L[𝕜] F := Subtype.val (p := fun A => A ∈ N.carrier) A

/-- The underlying operator of an ideal element lies in the ideal. -/
theorem val_mem (A : N.Elem E F) : A.val ∈ N.carrier := Subtype.property (p := _) A

/-- An ideal element has finite gauge -- the fact that makes `toReal` lossless on it, and hence
the reason the ideal norm can be real-valued while the gauge is `ℝ≥0∞`-valued. -/
theorem gauge_val_ne_top (A : N.Elem E F) : N.gauge A.val ≠ ∞ := A.val_mem

/-- An operator of finite gauge, as an element of the ideal. -/
-- `@[expose]` forced by the same compiler limitation as `Elem`: constructors and accessors
-- on an unexposed type synonym re-infer a different compilation type downstream.
@[expose]
def mk {A : E →L[𝕜] F} (hA : A ∈ N.carrier) : N.Elem E F := ⟨A, hA⟩

/-- Building an ideal element and taking its value is the identity. -/
@[simp] theorem val_mk {A : E →L[𝕜] F} (hA : A ∈ N.carrier) : (mk (N := N) hA).val = A := (rfl)
/-- Ideal elements are equal when their underlying operators are.  Tagged `@[ext]`, so `ext`
reduces any such goal to the operators. -/
@[ext] theorem ext {A B : N.Elem E F} (h : A.val = B.val) : A = B := Subtype.ext h

/-- Taking an ideal element's value and rebuilding is the identity — the
companion of `val_mk`, in the direction a round-trip equivalence needs.

Written when `Family/OperatorNorm.lean`'s `left_inv` field stopped being `rfl`:
without `Elem`'s body exposed, `mk A.val_mem = A` is not definitional, and the
right answer to that is the lemma rather than the exposure. -/
@[simp] theorem mk_val (A : N.Elem E F) : mk (N := N) A.val_mem = A := ext (val_mk _)

/-- The ideal is an additive subgroup of the bounded operators, inherited from its carrier. -/
instance : AddCommGroup (N.Elem E F) :=
  inferInstanceAs (AddCommGroup (N.carrier : Submodule 𝕜 (E →L[𝕜] F)))

/-- The ideal is a `𝕜`-submodule, inherited from its carrier. -/
instance : Module 𝕜 (N.Elem E F) :=
  inferInstanceAs (Module 𝕜 (N.carrier : Submodule 𝕜 (E →L[𝕜] F)))

/-- The zero ideal element is the zero operator. -/
@[simp] theorem val_zero : (0 : N.Elem E F).val = 0 := (rfl)
/-- Addition of ideal elements is addition of operators. -/
@[simp] theorem val_add (A B : N.Elem E F) : (A + B).val = A.val + B.val := (rfl)
/-- Negation of an ideal element is negation of the operator. -/
@[simp] theorem val_neg (A : N.Elem E F) : (-A).val = -A.val := (rfl)
/-- Subtraction of ideal elements is subtraction of operators. -/
@[simp] theorem val_sub (A B : N.Elem E F) : (A - B).val = A.val - B.val := (rfl)
/-- Scaling an ideal element scales the operator. -/
@[simp] theorem val_smul (c : 𝕜) (A : N.Elem E F) : (c • A).val = c • A.val := (rfl)
/-- The ideal norm, as a real-valued norm on the ideal. -/
noncomputable instance : NormedAddCommGroup (N.Elem E F) :=
  AddGroupNorm.toNormedAddCommGroup
    { toFun := fun A => (N.gauge A.val).toReal
      map_zero' := by
        -- states the goal with the definition unfolded, in the shape the next step needs;
        -- there is no `_apply` lemma to rewrite with here.
        change (N.gauge (0 : N.Elem E F).val).toReal = 0
        rw [val_zero, N.gauge_zero, ENNReal.toReal_zero]
      add_le' := fun A B => by
        -- states the goal with the definition unfolded, in the shape the next step needs;
        -- there is no `_apply` lemma to rewrite with here.
        change (N.gauge (A + B).val).toReal ≤ (N.gauge A.val).toReal + (N.gauge B.val).toReal
        rw [val_add, ← ENNReal.toReal_add A.gauge_val_ne_top B.gauge_val_ne_top]
        exact ENNReal.toReal_mono
          (ENNReal.add_ne_top.mpr ⟨A.gauge_val_ne_top, B.gauge_val_ne_top⟩)
          (N.gauge_add_le A.val B.val)
      neg' := fun A => by
        -- states the goal with the definition unfolded, in the shape the next step needs;
        -- there is no `_apply` lemma to rewrite with here.
        change (N.gauge (-A).val).toReal = (N.gauge A.val).toReal
        rw [val_neg, N.gauge_neg]
      eq_zero_of_map_eq_zero' := fun A hA => by
        refine ext ?_
        rw [val_zero]
        exact N.gauge_eq_zero
          (((ENNReal.toReal_eq_zero_iff _).mp hA).resolve_right A.gauge_val_ne_top) }

/-- The ideal norm is the gauge, brought down to `ℝ`.  Lossless because `gauge_val_ne_top`. -/
theorem norm_def (A : N.Elem E F) : ‖A‖ = (N.gauge A.val).toReal := (rfl)

/-- Going back up: the extended norm of an ideal element is its gauge exactly, with no `toReal`
round-trip loss. -/
theorem enorm_eq_gauge (A : N.Elem E F) : ‖A‖ₑ = N.gauge A.val := by
  rw [← ofReal_norm, norm_def, ENNReal.ofReal_toReal A.gauge_val_ne_top]

/-- The ideal norm is a norm on a `𝕜`-vector space; homogeneity transfers from `gauge_smul`
through `toReal`. -/
noncomputable instance : NormedSpace 𝕜 (N.Elem E F) where
  norm_smul_le c A := by
    rw [norm_def, norm_def, val_smul, N.gauge_smul, ENNReal.toReal_mul]
    simp

/-- The ideal embeds contractively into the bounded operators: the ideal norm
dominates the operator norm. -/
theorem norm_val_le (A : N.Elem E F) : ‖A.val‖ ≤ ‖A‖ := by
  have h := ENNReal.toReal_mono A.gauge_val_ne_top (N.enorm_le_gauge A.val)
  rwa [← norm_def, toReal_enorm] at h

/-- **A gauge-Cauchy sequence is operator-norm Cauchy**, because the ideal norm
dominates the operator norm.

This is the first step of every `IsComplete` proof: get a limit in the ambient
bounded operators, then show it stays in the ideal.  It was written out
identically in all four of `HilbertSchmidt`, `KyFan`, `Schatten` and
`TraceClass`, three of them character for character. -/
theorem cauchySeq_val {a : ℕ → N.Elem E F} (ha : CauchySeq a) :
    CauchySeq fun n => (a n).val := by
  rw [Metric.cauchySeq_iff] at ha ⊢
  intro ε hε
  obtain ⟨M, hM⟩ := ha ε hε
  refine ⟨M, fun m hm n hn => lt_of_le_of_lt ?_ (hM m hm n hn)⟩
  rw [dist_eq_norm, dist_eq_norm]
  exact norm_val_le (a m - a n)

end Elem

/-- Completeness of an ideal family, stated as `CompleteSpace` for the ideal
norm rather than as a hand-rolled Cauchy criterion.

Completeness of the target is available from the ambient assumptions, exactly as
for `E →L[𝕜] F`: an ideal norm cannot repair an incomplete target. -/
class IsComplete (N : OperatorIdealFamily.{u, v, w} 𝕜) : Prop where
  completeSpace : ∀ {E : Type v} {F : Type w}
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F],
    CompleteSpace (N.Elem E F)

/-- Unpacks `IsComplete` into the `CompleteSpace` instance that instance search needs; the class
quantifies over the two spaces, so it cannot be used directly. -/
instance [N.IsComplete] : CompleteSpace (N.Elem E F) :=
  IsComplete.completeSpace

/-- **Block sums: the gauge is squeezed between the maximum and the sum of the
two block gauges.**

For an operator split as `T = Q₁ T P₁ + Q₂ T P₂` with all four factors
contractive — the shape a block-diagonal decomposition of source and target
produces.

**Both halves are formal from the family laws.**  The upper bound is
`gauge_add_le` on the splitting; the lower is `gauge_comp_le`, the two-sided
ideal law, with the contractivity hypotheses collapsing `‖Q‖ₑ * · * ‖P‖ₑ` to `·`.
No approximation-number reasoning enters.

The *general* block statement — that the approximation-number sequence of a
block-diagonal sum is the decreasing rearrangement of the union of the summands'
sequences — is genuinely harder and is **not** what this needs; anyone reaching
for a rearrangement theorem here is solving the wrong problem. -/
theorem gauge_blockSum_le {T : E →L[𝕜] F} {P₁ P₂ : E →L[𝕜] E} {Q₁ Q₂ : F →L[𝕜] F}
    (hP₁ : ‖P₁‖ ≤ 1) (hP₂ : ‖P₂‖ ≤ 1) (hQ₁ : ‖Q₁‖ ≤ 1) (hQ₂ : ‖Q₂‖ ≤ 1)
    (hsplit : Q₁ ∘L T ∘L P₁ + Q₂ ∘L T ∘L P₂ = T) :
    max (N.gauge (Q₁ ∘L T ∘L P₁)) (N.gauge (Q₂ ∘L T ∘L P₂)) ≤ N.gauge T ∧
      N.gauge T ≤ N.gauge (Q₁ ∘L T ∘L P₁) + N.gauge (Q₂ ∘L T ∘L P₂) := by
  have hcomp : ∀ (Q : F →L[𝕜] F) (P : E →L[𝕜] E), ‖Q‖ ≤ 1 → ‖P‖ ≤ 1 →
      N.gauge (Q ∘L T ∘L P) ≤ N.gauge T := by
    intro Q P hQ hP
    refine (N.gauge_comp_le Q T P).trans ?_
    have h1 : ‖Q‖ₑ ≤ 1 := by
      rw [← ofReal_norm, ← ENNReal.ofReal_one]
      exact ENNReal.ofReal_le_ofReal hQ
    have h2 : ‖P‖ₑ ≤ 1 := by
      rw [← ofReal_norm, ← ENNReal.ofReal_one]
      exact ENNReal.ofReal_le_ofReal hP
    calc ‖Q‖ₑ * N.gauge T * ‖P‖ₑ ≤ 1 * N.gauge T * 1 := by gcongr
      _ = N.gauge T := by simp
  refine ⟨max_le (hcomp Q₁ P₁ hQ₁ hP₁) (hcomp Q₂ P₂ hQ₂ hP₂), ?_⟩
  calc N.gauge T = N.gauge (Q₁ ∘L T ∘L P₁ + Q₂ ∘L T ∘L P₂) := by rw [hsplit]
    _ ≤ N.gauge (Q₁ ∘L T ∘L P₁) + N.gauge (Q₂ ∘L T ∘L P₂) := N.gauge_add_le _ _

end OperatorIdealFamily

/-- A **symmetric** (adjoint-invariant) operator ideal family on Hilbert spaces.

Adjoint invariance is stated on the diagonal instantiation of
`OperatorIdealFamily` because `ContinuousLinearMap.adjoint` exchanges the source
and target spaces: a family closed under adjoints cannot keep the two universes
independent. -/
structure SymmetricOperatorIdealFamily (𝕜 : Type u) [RCLike 𝕜]
    extends OperatorIdealFamily.{u, v, v} 𝕜 where
  /-- The gauge is unchanged by passing to the adjoint. -/
  gauge_adjoint : ∀ {E F : Type v}
      [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
      [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
      (A : E →L[𝕜] F), toOperatorIdealFamily.gauge A.adjoint = toOperatorIdealFamily.gauge A

namespace SymmetricOperatorIdealFamily

variable {𝕜 : Type u} [RCLike 𝕜]
variable {E F : Type v}
variable [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
variable [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
/-- **A symmetric family is determined by its gauge**, the same way an
`OperatorIdealFamily` is: the extra field is a `Prop`, so once the underlying
families agree there is nothing left to compare.

Without this, an equality of two symmetric families has to be proved by
destructuring both, which does not go through — the hypothesis still mentions
the undestructured terms. -/
@[ext]
theorem ext {N M : SymmetricOperatorIdealFamily.{u, v} 𝕜}
    (h : ∀ {E F : Type v}
      [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
      [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
      (A : E →L[𝕜] F), N.gauge A = M.gauge A) : N = M := by
  cases N
  cases M
  congr 1
  exact OperatorIdealFamily.ext h

variable (N : SymmetricOperatorIdealFamily.{u, v} 𝕜)

/-- The ideal of a symmetric family is stable under adjoints. -/
theorem adjoint_mem_carrier {A : E →L[𝕜] F} (hA : A ∈ N.toOperatorIdealFamily.carrier) :
    A.adjoint ∈ N.toOperatorIdealFamily.carrier := by
  simpa [OperatorIdealFamily.mem_carrier_iff, N.gauge_adjoint A] using hA

end SymmetricOperatorIdealFamily

end TauCeti

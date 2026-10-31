/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Set.Restrict
public import Mathlib.Order.Setoid.Basic

/-!
# Realized functions and parameter fibres

A supplied realization map `f : W → X → Y` describes a fixed parametric model without
prescribing an architecture representation. Its neuromanifold `realizedFunctions f` is the
set of functions realized by its parameters; `parametrization f` corestricts the realization
map to this set. Equality here means equality at every input, with no topology, regularity,
or manifold structure assumed.

The fibres and the kernel setoid describe parameter redundancy. Their quotient is equivalent
to the realized-function type, and maps constant on fibres factor uniquely through the
parametrization. Reparametrization, restriction of parameters, and composition on inputs or
outputs interact with these constructions through the ordinary set-image APIs.
Use `realizedFunctions_def` with Mathlib's `Set.range_comp_subset_range`,
`Function.Surjective.range_comp`, `Set.range_domRestrict`, `Set.range_eq_empty`,
`Set.range_unique`, and `Set.range_comp` for these range computations.
Likewise, `fiber_def` exposes the singleton preimage for `Set.preimage_singleton_nonempty`
and `Set.preimage_comp`.
For cancellation of output or input composition, first rewrite parameter equivalence with
`parameterSetoid_iff`. For an injective output map `h` with proof `hh`, use
`hh.comp_left.eq_iff`; for a surjective input map `a` with proof `ha`, use
`ha.injective_comp_right.eq_iff`. These use the public characterization, so they also apply
from modules importing this one.

Given an equivalence relation `s` on parameters, such as the symmetries of an architecture, a
parameter `w` is identifiable modulo `s` (`IdentifiableAt`) when its whole realization fibre is
its `s`-class. When the `s`-classes lie in realization fibres, this is injectivity at the class
of `w` of the parametrization induced on `Quotient s`.

The definitions follow Marchetti–Shahverdi–Mereta–Trager–Kohn,
*Algebra Unveils Deep Learning — An Invitation to Neuroalgebraic Geometry*,
[arXiv:2501.18915v2](https://arxiv.org/abs/2501.18915v2), Definition 3.1 and §4.3.
The elementary comparison and factorization results below are consequences of these
definitions, rather than additional results attributed to that paper. The constructions use
Mathlib's `Set.rangeFactorization`, `Setoid.ker`, and `Setoid.quotientKerEquivRange`.
-/

public section

namespace TauCeti.Neuromanifold

universe u v w z

variable {W : Type u} {X : Type v} {Y : Type w}

/-- The neuromanifold of a supplied realization map: its set of realized functions. -/
def realizedFunctions (f : W → X → Y) : Set (X → Y) := Set.range f

/-- The realized functions form the ordinary range of the supplied realization map. -/
theorem realizedFunctions_def (f : W → X → Y) : realizedFunctions f = Set.range f := (rfl)

/-- A function is realized exactly when it has a parameter witness. -/
@[simp] theorem mem_realizedFunctions (f : W → X → Y) (g : X → Y) :
    g ∈ realizedFunctions f ↔ ∃ w, f w = g := Iff.rfl

/-- The realization map with codomain restricted to its neuromanifold. -/
def parametrization (f : W → X → Y) : W → realizedFunctions f :=
  Set.rangeFactorization f

/-- Forgetting membership in the neuromanifold recovers the supplied realization map. -/
@[simp] theorem parametrization_coe (f : W → X → Y) (w : W) :
    (parametrization f w : X → Y) = f w := (rfl)

/-- Every realized function is represented by a parameter. -/
@[simp] theorem parametrization_surjective (f : W → X → Y) :
    Function.Surjective (parametrization f) := Set.rangeFactorization_surjective

/-- The parameters that realize a specified ambient function. -/
def fiber (f : W → X → Y) (g : X → Y) : Set W := f ⁻¹' {g}

/-- A realization fibre is the singleton preimage, exposing the ordinary set preimage API. -/
theorem fiber_def (f : W → X → Y) (g : X → Y) : fiber f g = f ⁻¹' {g} := (rfl)

/-- Membership in a realization fibre is equality of the whole realized function. -/
@[simp] theorem mem_fiber (f : W → X → Y) (g : X → Y) (w : W) :
    w ∈ fiber f g ↔ f w = g := Iff.rfl

/-- Distinct ambient functions have disjoint parameter fibres. -/
theorem disjoint_fiber (f : W → X → Y) {g h : X → Y} (hne : g ≠ h) :
    Disjoint (fiber f g) (fiber f h) :=
  (Set.disjoint_singleton.mpr hne).preimage f

/-- Two parameters are equivalent when they realize the same function. -/
def parameterSetoid (f : W → X → Y) : Setoid W := Setoid.ker f

/-- Parameter equivalence is equality of realized functions. -/
@[simp] theorem parameterSetoid_iff (f : W → X → Y) (w v : W) :
    parameterSetoid f w v ↔ f w = f v := Iff.rfl

/-- The fibre over a realized function is the equivalence class of its parameter. -/
theorem fiber_eq_class (f : W → X → Y) (w : W) :
    fiber f (f w) = {v | parameterSetoid f v w} := (rfl)

/-- Parameters modulo realization equality are equivalent to realized functions.
This is a set equivalence and makes no assertion about quotient topologies. -/
noncomputable def quotientEquiv (f : W → X → Y) :
    Quotient (parameterSetoid f) ≃ realizedFunctions f := Setoid.quotientKerEquivRange f

/-- The quotient comparison sends a parameter class to its realized function. -/
@[simp] theorem quotientEquiv_mk (f : W → X → Y) (w : W) :
    quotientEquiv f (Quotient.mk (parameterSetoid f) w) = parametrization f w := by
  apply Subtype.ext
  rfl

/-- The inverse quotient comparison recovers the class of a realizing parameter. -/
@[simp] theorem quotientEquiv_symm_parametrization (f : W → X → Y) (w : W) :
    (quotientEquiv f).symm (parametrization f w) = Quotient.mk (parameterSetoid f) w := by
  apply (quotientEquiv f).injective
  simp

/-- A map factors uniquely through realized functions exactly when it is constant on
each realization fibre. No inhabitedness of the parameter or target type is needed. -/
theorem existsUnique_factor_iff {Z : Type z} (f : W → X → Y) (h : W → Z) :
    (∃! k : realizedFunctions f → Z, k ∘ parametrization f = h) ↔
      h.FactorsThrough f := by
  constructor
  · rintro ⟨k, hk, -⟩ w v hwv
    rw [← congrFun hk w, ← congrFun hk v]
    exact congrArg k (Subtype.ext hwv)
  · intro hh
    refine ⟨h ∘ Set.rangeSplitting f, ?_, ?_⟩
    · funext w
      exact hh (Set.apply_rangeSplitting f (Set.rangeFactorization f w))
    · intro k hk
      funext g
      obtain ⟨w, rfl⟩ := parametrization_surjective f g
      exact (congrFun hk w).trans
        (hh (Set.apply_rangeSplitting f (Set.rangeFactorization f w))).symm

/-- Equivalence of new parameters is equivalence of their images under reparametrization. -/
theorem parameterSetoid_comp_iff {W' : Type*} (f : W → X → Y)
    (r : W' → W) (w v : W') :
    parameterSetoid (f ∘ r) w v ↔ parameterSetoid f (r w) (r v) := Iff.rfl

/-- An equivalence of parameter spaces restricts to an equivalence of realization fibres. -/
def fiberEquiv {W' : Type*} (f : W → X → Y) (e : W' ≃ W) (g : X → Y) :
    fiber (f ∘ e) g ≃ fiber f g := e.subtypeEquiv fun _ => Iff.rfl

/-- The fibre equivalence acts on parameters by the original parameter equivalence. -/
@[simp] theorem fiberEquiv_coe {W' : Type*} (f : W → X → Y) (e : W' ≃ W)
    (g : X → Y) (w : fiber (f ∘ e) g) : (fiberEquiv f e g w : W) = e w := (rfl)

/-- The inverse fibre equivalence acts by the inverse parameter equivalence. -/
@[simp] theorem fiberEquiv_symm_coe {W' : Type*} (f : W → X → Y) (e : W' ≃ W)
    (g : X → Y) (w : fiber f g) : ((fiberEquiv f e g).symm w : W') = e.symm w := (rfl)

/-- All parameters of a subsingleton parameter type realize the same function. -/
theorem fiber_eq_univ [Subsingleton W] (f : W → X → Y) (w : W) :
    fiber f (f w) = Set.univ := by
  ext v
  simp [Subsingleton.elim v w]

/-! ### Identifiability modulo a symmetry -/

/-- A parameter `w` is identifiable modulo an equivalence relation `s` on parameters when its
whole realization fibre is exactly its `s`-class. -/
def IdentifiableAt (f : W → X → Y) (s : Setoid W) (w : W) : Prop :=
  fiber f (f w) = {v | s v w}

/-- Identifiability at `w` says that a parameter realizes the same function as `w` exactly when
it is `s`-equivalent to `w`. -/
theorem identifiableAt_iff {f : W → X → Y} {s : Setoid W} {w : W} :
    IdentifiableAt f s w ↔ ∀ v, f v = f w ↔ s v w :=
  Set.ext_iff

/-- Every parameter is identifiable modulo realization equality itself. -/
theorem identifiableAt_parameterSetoid (f : W → X → Y) (w : W) :
    IdentifiableAt f (parameterSetoid f) w :=
  fiber_eq_class f w

/-- The parametrization induced on the quotient by an equivalence relation whose classes lie
in realization fibres. -/
def quotientParametrization (f : W → X → Y) {s : Setoid W} (h : s ≤ parameterSetoid f) :
    Quotient s → realizedFunctions f :=
  Quotient.lift (parametrization f) fun _ _ hvw => Subtype.ext (h hvw)

/-- The induced parametrization sends a class to the function realized by a representative. -/
@[simp] theorem quotientParametrization_mk (f : W → X → Y) {s : Setoid W}
    (h : s ≤ parameterSetoid f) (w : W) :
    quotientParametrization f h (Quotient.mk s w) = parametrization f w := (rfl)

/-- The induced parametrization is surjective. -/
theorem quotientParametrization_surjective (f : W → X → Y) {s : Setoid W}
    (h : s ≤ parameterSetoid f) : Function.Surjective (quotientParametrization f h) :=
  fun g => (parametrization_surjective f g).imp' (Quotient.mk s) fun _ hw => hw

/-- When the classes of `s` lie in realization fibres, identifiability at `w` only asks that
the fibre through `w` be contained in the class of `w`. -/
theorem identifiableAt_iff_fiber_subset {f : W → X → Y} {s : Setoid W}
    (h : s ≤ parameterSetoid f) {w : W} :
    IdentifiableAt f s w ↔ fiber f (f w) ⊆ {v | s v w} :=
  ⟨Eq.subset, fun hsub => hsub.antisymm fun _ hv => h hv⟩

/-- Identifiability at `w` is injectivity of the induced parametrization at the class
of `w`. -/
theorem identifiableAt_iff_quotientParametrization {f : W → X → Y} {s : Setoid W}
    (h : s ≤ parameterSetoid f) {w : W} :
    IdentifiableAt f s w ↔ ∀ q : Quotient s,
      quotientParametrization f h q = quotientParametrization f h (Quotient.mk s w) →
        q = Quotient.mk s w := by
  rw [identifiableAt_iff_fiber_subset h]
  refine ⟨fun hsub q hq => ?_, fun hinj v hv => ?_⟩
  · induction q using Quotient.inductionOn with
    | h v => exact Quotient.sound (hsub (congrArg Subtype.val hq))
  · exact Quotient.exact (hinj (Quotient.mk s v) (Subtype.ext hv))

/-- Every parameter is identifiable modulo `s` exactly when the induced parametrization is
injective. -/
theorem forall_identifiableAt_iff_injective {f : W → X → Y} {s : Setoid W}
    (h : s ≤ parameterSetoid f) :
    (∀ w, IdentifiableAt f s w) ↔ Function.Injective (quotientParametrization f h) := by
  simp_rw [identifiableAt_iff_quotientParametrization h]
  refine ⟨fun hid q q' hqq' => ?_, fun hinj w q hq => hinj hq⟩
  induction q' using Quotient.inductionOn with
  | h w => exact hid w q hqq'

end TauCeti.Neuromanifold

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.ModelTheory.Counting.Vaught
public import TauCeti.ModelTheory.RelationalConfiguration.Theory
public import TauCeti.ModelTheory.Satisfiability
import Mathlib.ModelTheory.Encoding
import TauCeti.Data.Setoid.Cardinal
import TauCeti.ModelTheory.Counting.Scattered.Thin

/-!
# Vaught's conjecture and counting dichotomies for first-order theories

Vaught's original 1961 conjecture concerned complete first-order theories rather than sentences of
`L_{ω₁ω}`: every complete first-order theory in a countable relational language has either
countably many countably infinite models up to isomorphism, or continuum many (in Steel's
witnessed form, a nonempty perfect set of pairwise non-isomorphic models on `ℕ`).

In a relational language `L` with countably many relation symbols of each arity, there are only
countably many finitary sentences in total (`Set.to_countable` via `Mathlib.ModelTheory.Encoding`),
so every first-order theory `T : L.Theory`—complete or not—has Borel model class `modelsOfTheory T`
on `ℕ` and coincides with the model class of a single `L_{ω₁ω}` sentence, namely the coded
conjunction of `BoundedFormula.toOmega '' T`. Conjoining that sentence with `L.infiniteSentence`
eliminates all finite tiers and identifies `HasVaughtDichotomy` and `HasVaughtCount` for the
conjunction with the witnessed and cardinal dichotomies on `modelsOfTheory (V := ℕ) T`
(`TauCeti.hasVaughtDichotomy_conjunction_inf_infiniteSentence_iff`,
`TauCeti.hasVaughtCount_conjunction_inf_infiniteSentence_iff`).

Three consequences follow:

1. **Unconditional Morley dichotomy for first-order theories**: without assuming completeness or
   CH, any first-order theory in a countable relational vocabulary has at most `ℵ₁` models on `ℕ`
   up to isomorphism or a nonempty perfect set of pairwise non-isomorphic models on `ℕ`
   (`TauCeti.mk_isoClasses_modelsOfTheory_nat_le_aleph_one_or_hasPerfectAntichainOn`), and hence
   at most `ℵ₁` or `𝔠` models on `ℕ`
   (`TauCeti.mk_isoClasses_modelsOfTheory_nat_le_aleph_one_or_eq_continuum`).
2. **Reduction from `L_{ω₁ω}` to first-order theories**: `VaughtConjecture` implies the witnessed
   dichotomy on `ℕ` for every first-order theory in every countable relational language in any
   universe (`TauCeti.VaughtConjecture.countable_or_hasPerfectAntichainOn_modelsOfTheory`), and in
   particular implies `TauCeti.FirstOrderVaughtConjecture` (`TauCeti.VaughtConjecture.firstOrder`),
   without using completeness of `T`. The two conjectures remain distinct definitions; the
   converse implication is false if Vaught's conjecture fails for `L_{ω₁ω}` while holding for
   first-order logic, and is not asserted.
3. **Universe invariance and equivalent formulations**: transporting theories, completeness,
   isomorphism quotients, and perfect antichains along `smallPresentationEquiv` and `uliftEquiv`
   shows that `FirstOrderVaughtConjecture` (stated over `Language.{0, 0}`) is equivalent to
   quantifying over countable relational languages in any universes `u, v`
   (`TauCeti.firstOrderVaughtConjecture_iff_forall_universe`), and also equivalent to the
   back-and-forth scattered formulation (`TauCeti.firstOrderVaughtConjecture_iff_bfScattered`) and,
   when `ℵ₁ < 𝔠`, to the cardinal formulation (`TauCeti.firstOrderVaughtConjecture_iff_cardinal`).

## Main definitions

* `TauCeti.FirstOrderVaughtConjecture`: Vaught's conjecture in perfect-set form for complete
  first-order theories in countable relational languages in universe zero.

## Main results

* `FirstOrder.Language.LEquiv.countable_quotient_isoSetoid_modelsOfTheory_onTheory_iff`,
  `FirstOrder.Language.LEquiv.lift_mk_quotient_isoSetoid_modelsOfTheory_onTheory`, and
  `FirstOrder.Language.LEquiv.hasPerfectAntichainOn_modelsOfTheory_onTheory_iff`: invariance of
  isomorphism-class counts and perfect antichains of `modelsOfTheory` along language equivalences.
* `TauCeti.mk_isoClasses_modelsOfTheory_nat_le_aleph_one_or_hasPerfectAntichainOn` and
  `TauCeti.mk_isoClasses_modelsOfTheory_nat_le_aleph_one_or_eq_continuum`: Morley's theorem on `ℕ`
  for arbitrary first-order theories.
* `TauCeti.hasVaughtDichotomy_conjunction_inf_infiniteSentence_iff`,
  `TauCeti.hasVaughtCount_conjunction_inf_infiniteSentence_iff`,
  `TauCeti.not_countable_quotient_isoSetoid_modelsOfTheory_nat_or_hasPerfectAntichainOn_iff`,
  `TauCeti.mk_isoClasses_modelsOfTheory_nat_le_aleph0_or_eq_continuum_of_aleph_one_eq_continuum`,
  and `TauCeti.mk_isoClasses_modelsOfTheory_nat_le_aleph0_or_eq_continuum_iff`: reduction to
  `L_{ω₁ω}`, counterexample profile, and CH / `< 𝔠` equivalences on `ℕ`.
* `TauCeti.VaughtConjecture.countable_or_hasPerfectAntichainOn_modelsOfTheory` and
  `TauCeti.VaughtConjecture.firstOrder`: `VaughtConjecture` implies the first-order conjecture.
* `TauCeti.firstOrderVaughtConjecture_iff_forall_universe`,
  `TauCeti.firstOrderVaughtConjecture_iff_bfScattered`, and
  `TauCeti.firstOrderVaughtConjecture_iff_cardinal`: universe invariance, scattered formulation,
  and cardinal formulation of `FirstOrderVaughtConjecture`.

## References

* R. L. Vaught, *Denumerable models of complete theories*, in Infinitistic Methods (1961),
  303–321.
* M. Morley, *The number of countable models*, J. Symbolic Logic 35 (1970), 14–18.
* J. R. Steel, *On Vaught's conjecture*, Cabal Seminar 76–77, Lecture Notes in Mathematics 689
  (1978), 193–208.
* D. Marker, *Lectures on Infinitary Model Theory*, Cambridge University Press, 2016.
-/

public section

universe u v u' v' w

open FirstOrder FirstOrder.Language Cardinal Ordinal

/-! ### Transport along language equivalences -/

namespace FirstOrder.Language.LEquiv

open TauCeti TauCeti.RelationalConfiguration

variable {L : Language.{u, v}} {L' : Language.{u', v'}} [L.IsRelational] [L'.IsRelational]
  (e : L ≃ᴸ L')

/-- A language equivalence preserves and reflects countability of the isomorphism quotient of
`modelsOfTheory` on any carrier `V`. -/
@[simp]
theorem countable_quotient_isoSetoid_modelsOfTheory_onTheory_iff (V : Type w) (T : L.Theory) :
    Countable (Quotient ((isoSetoid L' V).comap
      (Subtype.val : modelsOfTheory (e.toLHom.onTheory T) → _))) ↔
    Countable (Quotient ((isoSetoid L V).comap (Subtype.val : modelsOfTheory T → _))) :=
  (e.quotientIsoSetoidModelsOfTheoryEquiv V T).symm.countable_iff

/-- A first-order theory and its translation along a language equivalence have the same number of
models on `V` up to isomorphism, after lifting both cardinalities to a common universe. -/
theorem lift_mk_quotient_isoSetoid_modelsOfTheory_onTheory (V : Type w) (T : L.Theory) :
    Cardinal.lift.{max v' w}
      #(Quotient ((isoSetoid L V).comap (Subtype.val : modelsOfTheory T → _))) =
    Cardinal.lift.{max v w}
      #(Quotient ((isoSetoid L' V).comap
        (Subtype.val : modelsOfTheory (e.toLHom.onTheory T) → _))) :=
  Cardinal.lift_mk_eq'.2 ⟨e.quotientIsoSetoidModelsOfTheoryEquiv V T⟩

/-- **Perfect antichains of theory models along a language equivalence.** The translated theory
`e.toLHom.onTheory T` has a perfect antichain of pairwise non-isomorphic models on `V` if and only
if `T` does. -/
@[simp]
theorem hasPerfectAntichainOn_modelsOfTheory_onTheory_iff (V : Type w) (T : L.Theory) :
    (isoSetoid L' V).HasPerfectAntichainOn (modelsOfTheory (e.toLHom.onTheory T)) ↔
      (isoSetoid L V).HasPerfectAntichainOn (modelsOfTheory T) := by
  rw [← e.image_onConfiguration_modelsOfTheory (V := V) T]
  exact Setoid.hasPerfectAntichainOn_image_homeomorph_iff _
    (fun _ _ => e.isoSetoid_onConfiguration_iff) (modelsOfTheory T)

end FirstOrder.Language.LEquiv

namespace TauCeti.RelationalConfiguration

open TauCeti

variable {L : Language.{u, v}} [L.IsRelational]

/-- The `L_{ω₁ω}` conjunction of a countable first-order theory `T` has the same number of
isomorphism classes of models on `V` as `T`. -/
@[simp]
theorem mk_quotient_isoSetoidOn_conjunction_image_toOmega {V : Type w} {T : L.Theory}
    (hT : (BoundedFormula.toOmega '' T).Countable) :
    #(Quotient (isoSetoidOn V (Theoryω.conjunction (BoundedFormula.toOmega '' T) hT))) =
      #(Quotient ((isoSetoid L V).comap (Subtype.val : modelsOfTheory T → _))) := by
  rw [Setoid.mk_quotient_comap_val_eq_mk_image, Setoid.mk_quotient_comap_val_eq_mk_image,
    modelsOf_conjunction_image_toOmega hT]

/-- The `L_{ω₁ω}` conjunction of a countable first-order theory `T` has countably many
isomorphism classes of models on `V` exactly when `T` does. -/
@[simp]
theorem countable_quotient_isoSetoidOn_conjunction_image_toOmega_iff {V : Type w} {T : L.Theory}
    (hT : (BoundedFormula.toOmega '' T).Countable) :
    Countable
        (Quotient (isoSetoidOn V (Theoryω.conjunction (BoundedFormula.toOmega '' T) hT))) ↔
      Countable (Quotient ((isoSetoid L V).comap (Subtype.val : modelsOfTheory T → _))) := by
  rw [← mk_le_aleph0_iff, ← mk_le_aleph0_iff, mk_quotient_isoSetoidOn_conjunction_image_toOmega]

end TauCeti.RelationalConfiguration

namespace TauCeti

open RelationalConfiguration

/-! ### Morley's dichotomy for first-order theories on `ℕ` -/

section MorleyFirstOrder

variable {L : Language.{u, v}} [L.IsRelational] [∀ n, Countable (L.Relations n)]

/-- **Morley's dichotomy for first-order theories on `ℕ` (witnessed form).** In a relational
language with countably many relation symbols of each arity, any first-order theory `T` (complete
or not) either has at most `ℵ₁` countably infinite models on `ℕ` up to isomorphism, or has a
nonempty perfect set of pairwise non-isomorphic models on `ℕ`. -/
theorem mk_isoClasses_modelsOfTheory_nat_le_aleph_one_or_hasPerfectAntichainOn (T : L.Theory) :
    #(Quotient ((isoSetoid L ℕ).comap (Subtype.val : modelsOfTheory T → _))) ≤ ℵ₁ ∨
      (isoSetoid L ℕ).HasPerfectAntichainOn (modelsOfTheory T) :=
  mk_isoClasses_le_aleph_one_or_hasPerfectAntichainOn (measurableSet_modelsOfTheory T)

/-- **Morley's dichotomy for first-order theories on `ℕ` (cardinal form).** In a relational
language with countably many relation symbols of each arity, any first-order theory `T` has either
at most `ℵ₁` or continuum many countably infinite models on `ℕ` up to isomorphism. -/
theorem mk_isoClasses_modelsOfTheory_nat_le_aleph_one_or_eq_continuum (T : L.Theory) :
    #(Quotient ((isoSetoid L ℕ).comap (Subtype.val : modelsOfTheory T → _))) ≤ ℵ₁ ∨
      #(Quotient ((isoSetoid L ℕ).comap (Subtype.val : modelsOfTheory T → _))) = 𝔠 :=
  mk_isoClasses_le_aleph_one_or_eq_continuum (measurableSet_modelsOfTheory T)

end MorleyFirstOrder

/-! ### Reduction of countable theories to one `L_{ω₁ω}` sentence -/

section ConjunctionReduction

variable {L : Language.{u, v}} [L.IsRelational]

/-- Conjoining the `L_{ω₁ω}` conjunction of a countable first-order theory `T` with
`L.infiniteSentence` turns `HasVaughtDichotomy` into the witnessed dichotomy on `modelsOfTheory T`
at the tier `ℕ`. No countability hypothesis on the ambient language is needed. -/
theorem hasVaughtDichotomy_conjunction_inf_infiniteSentence_iff
    {T : L.Theory} (hT : (BoundedFormula.toOmega '' T).Countable) :
    HasVaughtDichotomy
      (Theoryω.conjunction (BoundedFormula.toOmega '' T) hT ⊓ L.infiniteSentence) ↔
        Countable (Quotient ((isoSetoid L ℕ).comap (Subtype.val : modelsOfTheory T → _))) ∨
          (isoSetoid L ℕ).HasPerfectAntichainOn (modelsOfTheory T) := by
  rw [hasVaughtDichotomy_inf_infiniteSentence_iff]
  unfold isoSetoidOn
  rw [modelsOf_conjunction_image_toOmega hT]

/-- Conjoining the `L_{ω₁ω}` conjunction of a countable first-order theory `T` with
`L.infiniteSentence` turns `HasVaughtCount` into the cardinal dichotomy on `modelsOfTheory T` at
the tier `ℕ`. No countability hypothesis on the ambient language is needed. -/
theorem hasVaughtCount_conjunction_inf_infiniteSentence_iff
    {T : L.Theory} (hT : (BoundedFormula.toOmega '' T).Countable) :
    HasVaughtCount
      (Theoryω.conjunction (BoundedFormula.toOmega '' T) hT ⊓ L.infiniteSentence) ↔
        #(Quotient ((isoSetoid L ℕ).comap (Subtype.val : modelsOfTheory T → _))) ≤ ℵ₀ ∨
          #(Quotient ((isoSetoid L ℕ).comap (Subtype.val : modelsOfTheory T → _))) = 𝔠 := by
  rw [hasVaughtCount_iff, countableModelCount_inf_infiniteSentence]
  unfold isoSetoidOn
  rw [modelsOf_conjunction_image_toOmega hT]

end ConjunctionReduction

section CounterexampleAndCardinal

variable {L : Language.{u, v}} [L.IsRelational] [∀ n, Countable (L.Relations n)]

/-- A first-order theory in a countable relational vocabulary fails the witnessed dichotomy on `ℕ`
if and only if it has `ℵ₁` countably infinite models up to isomorphism and no perfect antichain on
`modelsOfTheory (V := ℕ) T`. No CH hypothesis is needed. -/
theorem not_countable_quotient_isoSetoid_modelsOfTheory_nat_or_hasPerfectAntichainOn_iff
    {T : L.Theory} :
    ¬ (Countable (Quotient ((isoSetoid L ℕ).comap (Subtype.val : modelsOfTheory T → _))) ∨
        (isoSetoid L ℕ).HasPerfectAntichainOn (modelsOfTheory T)) ↔
      #(Quotient ((isoSetoid L ℕ).comap (Subtype.val : modelsOfTheory T → _))) = ℵ₁ ∧
        ¬ (isoSetoid L ℕ).HasPerfectAntichainOn (modelsOfTheory T) := by
  have h := not_hasVaughtDichotomy_iff (φ :=
    Theoryω.conjunction (BoundedFormula.toOmega '' T) (T.to_countable.image _) ⊓
      L.infiniteSentence)
  simpa only [hasVaughtDichotomy_conjunction_inf_infiniteSentence_iff,
    countableModelCount_inf_infiniteSentence,
    hasPerfectlyManyCountableModels_inf_infiniteSentence_iff,
    mk_quotient_isoSetoidOn_conjunction_image_toOmega,
    modelsOf_conjunction_image_toOmega] using h

/-- Under CH, the models on `ℕ` of every first-order theory in a countable relational vocabulary
satisfy Vaught's cardinal dichotomy. -/
theorem mk_isoClasses_modelsOfTheory_nat_le_aleph0_or_eq_continuum_of_aleph_one_eq_continuum
    (hCH : ℵ₁ = (𝔠 : Cardinal.{v})) (T : L.Theory) :
    #(Quotient ((isoSetoid L ℕ).comap (Subtype.val : modelsOfTheory T → _))) ≤ ℵ₀ ∨
      #(Quotient ((isoSetoid L ℕ).comap (Subtype.val : modelsOfTheory T → _))) = 𝔠 :=
  (hasVaughtCount_conjunction_inf_infiniteSentence_iff (T.to_countable.image _)).1
    (hasVaughtCount_of_aleph_one_eq_continuum hCH _)

/-- When `ℵ₁ < 𝔠`, the cardinal dichotomy on `ℕ` for a first-order theory `T` is equivalent to the
witnessed perfect-set dichotomy on `ℕ`. -/
theorem mk_isoClasses_modelsOfTheory_nat_le_aleph0_or_eq_continuum_iff
    (hc : ℵ₁ < (𝔠 : Cardinal.{v})) {T : L.Theory} :
    (#(Quotient ((isoSetoid L ℕ).comap (Subtype.val : modelsOfTheory T → _))) ≤ ℵ₀ ∨
        #(Quotient ((isoSetoid L ℕ).comap (Subtype.val : modelsOfTheory T → _))) = 𝔠) ↔
      (Countable (Quotient ((isoSetoid L ℕ).comap (Subtype.val : modelsOfTheory T → _))) ∨
        (isoSetoid L ℕ).HasPerfectAntichainOn (modelsOfTheory T)) := by
  simpa only [hasVaughtCount_conjunction_inf_infiniteSentence_iff,
    hasVaughtDichotomy_conjunction_inf_infiniteSentence_iff] using
    hasVaughtCount_iff_hasVaughtDichotomy (φ :=
      Theoryω.conjunction (BoundedFormula.toOmega '' T) (T.to_countable.image _) ⊓
        L.infiniteSentence) hc

end CounterexampleAndCardinal

/-! ### Vaught's conjecture for first-order theories -/

/-- Under `VaughtConjecture`, every first-order theory `T` (complete or not) in a relational
language in any universe with countably many relation symbols of each arity has countably many
models on `ℕ` up to isomorphism or a nonempty perfect set of pairwise non-isomorphic models on
`ℕ`. -/
theorem VaughtConjecture.countable_or_hasPerfectAntichainOn_modelsOfTheory
    {L : Language.{u, v}} [L.IsRelational] [∀ n, Countable (L.Relations n)]
    (h : VaughtConjecture) (T : L.Theory) :
    Countable (Quotient ((isoSetoid L ℕ).comap (Subtype.val : modelsOfTheory T → _))) ∨
      (isoSetoid L ℕ).HasPerfectAntichainOn (modelsOfTheory T) :=
  (hasVaughtDichotomy_conjunction_inf_infiniteSentence_iff ((Set.to_countable T).image _)).1
    (vaughtConjecture_iff_forall_universe.1 h L _)

/-- Under `CardinalVaughtConjecture`, every first-order theory `T` (complete or not) in a
relational language in any universe with countably many relation symbols of each arity has either
at most `ℵ₀` or continuum many models on `ℕ` up to isomorphism. -/
theorem CardinalVaughtConjecture.mk_isoClasses_modelsOfTheory_nat_le_aleph0_or_eq_continuum
    {L : Language.{u, v}} [L.IsRelational] [∀ n, Countable (L.Relations n)]
    (h : CardinalVaughtConjecture) (T : L.Theory) :
    #(Quotient ((isoSetoid L ℕ).comap (Subtype.val : modelsOfTheory T → _))) ≤ ℵ₀ ∨
      #(Quotient ((isoSetoid L ℕ).comap (Subtype.val : modelsOfTheory T → _))) = 𝔠 :=
  (hasVaughtCount_conjunction_inf_infiniteSentence_iff ((Set.to_countable T).image _)).1
    (cardinalVaughtConjecture_iff_forall_universe.1 h L _)

/-- **Vaught's conjecture for complete first-order theories (perfect-set form).** Every complete
first-order theory in a countable relational language in universe zero has either countably many
countably infinite models on `ℕ` up to isomorphism, or a nonempty perfect set of pairwise
non-isomorphic models on `ℕ`. Stated separately from `VaughtConjecture`; this is an open
conjecture, not an assertion made by the library. -/
def FirstOrderVaughtConjecture : Prop :=
  ∀ (L : Language.{0, 0}) [L.IsRelational] [Countable (Σ n, L.Relations n)]
    (T : L.Theory), T.IsComplete →
      Countable (Quotient ((isoSetoid L ℕ).comap (Subtype.val : modelsOfTheory T → _))) ∨
        (isoSetoid L ℕ).HasPerfectAntichainOn (modelsOfTheory T)

/-- Unfolding lemma for `TauCeti.FirstOrderVaughtConjecture`. -/
theorem firstOrderVaughtConjecture_iff :
    FirstOrderVaughtConjecture ↔
      ∀ (L : Language.{0, 0}) [L.IsRelational] [Countable (Σ n, L.Relations n)]
        (T : L.Theory), T.IsComplete →
          Countable (Quotient ((isoSetoid L ℕ).comap (Subtype.val : modelsOfTheory T → _))) ∨
            (isoSetoid L ℕ).HasPerfectAntichainOn (modelsOfTheory T) :=
  Iff.rfl

/-- Characterization of `TauCeti.FirstOrderVaughtConjecture` with the perfect-set witness written
out explicitly on `RelationalConfiguration L ℕ`. -/
theorem firstOrderVaughtConjecture_iff_exists_perfect :
    FirstOrderVaughtConjecture ↔
      ∀ (L : Language.{0, 0}) [L.IsRelational] [Countable (Σ n, L.Relations n)]
        (T : L.Theory), T.IsComplete →
          Countable (Quotient ((isoSetoid L ℕ).comap (Subtype.val : modelsOfTheory T → _))) ∨
            ∃ P : Set (RelationalConfiguration L ℕ), Perfect P ∧ P.Nonempty ∧
              P ⊆ modelsOfTheory T ∧ ∀ c ∈ P, ∀ d ∈ P, isoSetoid L ℕ c d → c = d := by
  simp only [firstOrderVaughtConjecture_iff, Setoid.hasPerfectAntichainOn_iff]

/-- **The `L_{ω₁ω}` Vaught conjecture implies the first-order Vaught conjecture.** Completeness of
the first-order theory is not needed for this implication; the underlying per-theory reduction is
`TauCeti.VaughtConjecture.countable_or_hasPerfectAntichainOn_modelsOfTheory`. -/
theorem VaughtConjecture.firstOrder (h : VaughtConjecture) : FirstOrderVaughtConjecture :=
  fun _ _ _ T _ => h.countable_or_hasPerfectAntichainOn_modelsOfTheory T

/-- **Universe invariance of the first-order Vaught conjecture.** Quantifying over complete
first-order theories in countable relational languages in universe zero is equivalent to
quantifying over countable relational languages in any fixed pair of universes `u, v`. -/
theorem firstOrderVaughtConjecture_iff_forall_universe :
    FirstOrderVaughtConjecture ↔
      ∀ (L : Language.{u, v}) [L.IsRelational] [Countable (Σ n, L.Relations n)]
        (T : L.Theory), T.IsComplete →
          Countable (Quotient ((isoSetoid L ℕ).comap (Subtype.val : modelsOfTheory T → _))) ∨
            (isoSetoid L ℕ).HasPerfectAntichainOn (modelsOfTheory T) := by
  constructor
  · intro h L _ _ T hT
    let e := L.smallPresentationEquiv
    simpa only [e.countable_quotient_isoSetoid_modelsOfTheory_onTheory_iff ℕ T,
      e.hasPerfectAntichainOn_modelsOfTheory_onTheory_iff ℕ T] using
        h L.smallPresentation (e.toLHom.onTheory T) (e.isComplete_onTheory_iff.2 hT)
  · intro h L₀ _ _ T₀ hT₀
    let e := L₀.uliftEquiv.{u, v}
    simpa only [e.countable_quotient_isoSetoid_modelsOfTheory_onTheory_iff ℕ T₀,
      e.hasPerfectAntichainOn_modelsOfTheory_onTheory_iff ℕ T₀] using
        h (L₀.ulift.{u, v}) (e.toLHom.onTheory T₀) (e.isComplete_onTheory_iff.2 hT₀)

/-- **The scattered formulation of the first-order Vaught conjecture.** Unconditionally,
`FirstOrderVaughtConjecture` holds if and only if every complete first-order theory whose model
class on `ℕ` is back-and-forth scattered has countably many models on `ℕ` up to isomorphism.
Neither CH nor its negation is assumed. -/
theorem firstOrderVaughtConjecture_iff_bfScattered :
    FirstOrderVaughtConjecture ↔
      ∀ (L : Language.{0, 0}) [L.IsRelational] [Countable (Σ n, L.Relations n)]
        (T : L.Theory), T.IsComplete →
        BFScattered (modelsOfTheory (V := ℕ) T) →
        Countable (Quotient ((isoSetoid L ℕ).comap (Subtype.val : modelsOfTheory T → _))) := by
  rw [firstOrderVaughtConjecture_iff]
  constructor
  · intro h L _ _ T hT hscat
    exact (h L T hT).resolve_right (Setoid.isThinOn_iff.1 hscat.isThinOn)
  · intro h L _ _ T hT
    refine or_iff_not_imp_right.2 fun hthin => h L T hT ?_
    exact BFScattered.of_isThinOn (measurableSet_modelsOfTheory T) (Setoid.isThinOn_iff.2 hthin)

/-- **The cardinal formulation of the first-order Vaught conjecture** when `ℵ₁ < 𝔠`. Under CH,
every first-order theory already satisfies the cardinal dichotomy on `ℕ`
(`mk_isoClasses_modelsOfTheory_nat_le_aleph0_or_eq_continuum_of_aleph_one_eq_continuum`), so the
equivalence requires `ℵ₁ < 𝔠`. -/
theorem firstOrderVaughtConjecture_iff_cardinal (hc : ℵ₁ < (𝔠 : Cardinal.{0})) :
    FirstOrderVaughtConjecture ↔
      ∀ (L : Language.{0, 0}) [L.IsRelational] [Countable (Σ n, L.Relations n)]
        (T : L.Theory), T.IsComplete →
        #(Quotient ((isoSetoid L ℕ).comap (Subtype.val : modelsOfTheory T → _))) ≤ ℵ₀ ∨
          #(Quotient ((isoSetoid L ℕ).comap (Subtype.val : modelsOfTheory T → _))) = 𝔠 := by
  rw [firstOrderVaughtConjecture_iff]
  refine forall_congr' fun L => forall_congr' fun _ => forall_congr' fun _ =>
    forall_congr' fun T => imp_congr_right fun _ => ?_
  exact (mk_isoClasses_modelsOfTheory_nat_le_aleph0_or_eq_continuum_iff hc).symm

end TauCeti

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.ModelTheory.Satisfiability
public import TauCeti.ModelTheory.Counting.Vaught
public import TauCeti.ModelTheory.Infinitary.Theory
import Mathlib.ModelTheory.Encoding
import TauCeti.ModelTheory.Counting.BoundedRank
import TauCeti.ModelTheory.Counting.Scattered.Thin
import TauCeti.ModelTheory.LanguageMap
import TauCeti.ModelTheory.Satisfiability

/-!
# Counting countable models of first-order theories and the first-order Vaught conjecture

Vaught originally posed his conjecture in 1961 for complete first-order theories in countable
languages, counting their countably infinite models up to isomorphism. In a relational language
`L`, the configurations on `V` decoding to models of a first-order theory `T : L.Theory` form the
model class `TauCeti.RelationalConfiguration.modelsOfTheory T`, and
`TauCeti.RelationalConfiguration.isoSetoidOnTheory V T` restricts isomorphism to that class.

In a relational language with countably many relation symbols of each arity, `L.Symbols` and hence
`L.Sentence` are countable, so every first-order theory `T : L.Theory` is a countable set of
sentences. Embedding `T` into `L_{ω₁ω}` and forming its countable conjunction
`FirstOrder.Language.Theoryω.conjunction` turns `modelsOfTheory T` into the model class of a single
`L_{ω₁ω}` sentence (`TauCeti.RelationalConfiguration.modelsOf_conjunction_image_toOmega`). The
Borel measurability of `modelsOfTheory T`, the finite-carrier dichotomy, Morley's dichotomy on `ℕ`,
and the bounded-rank dichotomy on `ℕ` all follow immediately from the infinitary results.

Conjoining the countable conjunction of `T` with `FirstOrder.Language.infiniteSentence` removes the
finite tiers while preserving `modelsOfTheory (V := ℕ) T`
(`TauCeti.hasVaughtDichotomy_conjunction_inf_infiniteSentence_iff`). Consequently the `L_{ω₁ω}`
Vaught conjecture implies the first-order Vaught conjecture (`TauCeti.VaughtConjecture.firstOrder`),
without even using completeness of `T`. The two conjectures `VaughtConjecture` and
`FirstOrderVaughtConjecture` are distinct open statements; the reverse implication is not claimed.

Just as for `VaughtConjecture`, transport along `FirstOrder.Language.smallPresentationEquiv` and
`FirstOrder.Language.uliftEquiv` shows that quantifying `FirstOrderVaughtConjecture` over
`Language.{0, 0}` is equivalent to quantifying over countable relational languages in arbitrary
universes (`TauCeti.firstOrderVaughtConjecture_iff_forall_universe`). Unconditionally,
`FirstOrderVaughtConjecture` is also equivalent to countability of the countably infinite models of
every complete theory whose model class on `ℕ` is back-and-forth scattered
(`TauCeti.firstOrderVaughtConjecture_iff_bfScattered`), and under `ℵ₁ < 𝔠` to Vaught's cardinal
dichotomy (`TauCeti.firstOrderVaughtConjecture_iff_cardinal`), whereas under CH the cardinal
dichotomy holds unconditionally by Morley's theorem.

## Main definitions

* `TauCeti.RelationalConfiguration.isoSetoidOnTheory`: isomorphism restricted to the configurations
  on `V` decoding to models of a first-order theory `T`.
* `TauCeti.FirstOrderVaughtConjecture`: Vaught's conjecture in perfect-set form for complete
  first-order theories in countable relational languages.

## Main results

* `TauCeti.RelationalConfiguration.measurableSet_modelsOfTheory` and
  `TauCeti.RelationalConfiguration.standardBorelSpace_modelsOfTheory`: in a relational language
  with countably many relation symbols of each arity, every first-order model class on a countable
  carrier is Borel and standard Borel.
* `TauCeti.RelationalConfiguration.modelsOf_conjunction_image_toOmega`: the model class of a
  countable first-order theory is the model class of its `L_{ω₁ω}` conjunction.
* `FirstOrder.Language.LEquiv.quotientIsoSetoidOnTheoryEquiv`,
  `FirstOrder.Language.LEquiv.lift_mk_quotient_isoSetoidOnTheory_onTheory`,
  `FirstOrder.Language.LEquiv.countable_quotient_isoSetoidOnTheory_onTheory_iff`, and
  `FirstOrder.Language.LEquiv.hasPerfectAntichainOn_modelsOfTheory_onTheory_iff`: transport of
  model-class quotients, counts, and perfect antichains along a language equivalence.
* `TauCeti.mk_quotient_isoSetoidOnTheory_nat_le_aleph_one_or_hasPerfectAntichainOn` and
  `TauCeti.mk_quotient_isoSetoidOnTheory_nat_le_aleph_one_or_eq_continuum`: Morley's theorem for
  countably infinite models of a first-order theory.
* `TauCeti.countable_quotient_isoSetoidOnTheory_nat_or_hasPerfectAntichainOn_of_bounded` and
  `TauCeti.countable_quotient_isoSetoidOnTheory_nat_or_hasPerfectAntichainOn_of_scottHeight_le`:
  the bounded-rank dichotomy for countably infinite models of a first-order theory.
* `TauCeti.VaughtConjecture.firstOrder`: `VaughtConjecture` implies `FirstOrderVaughtConjecture`.
* `TauCeti.firstOrderVaughtConjecture_iff_forall_universe`: universe independence of
  `FirstOrderVaughtConjecture`.
* `TauCeti.firstOrderVaughtConjecture_iff_bfScattered` and
  `TauCeti.firstOrderVaughtConjecture_iff_cardinal`: scattered and cardinal reformulations of
  `FirstOrderVaughtConjecture`.

## References

* R. L. Vaught, *Denumerable models of complete theories*, in Infinitistic Methods (1961),
  303–321.
* M. Morley, *The number of countable models*, J. Symbolic Logic 35 (1970), 14–18.
* J. R. Steel, *On Vaught's conjecture*, Cabal Seminar 76–77, Lecture Notes in Mathematics 689
  (1978), 193–208.
* D. Marker, *Lectures on Infinitary Model Theory*, Cambridge University Press, 2016, the chapters
  on the space of countable models and Vaught counterexamples.
-/

public section

universe u v u' v' w

open FirstOrder FirstOrder.Language Cardinal Ordinal Set

namespace TauCeti.RelationalConfiguration

variable {L : Language.{u, v}} [L.IsRelational] {V : Type w}

/-- In a relational language with countably many relation symbols of each arity, every first-order
theory is a countable set of sentences. -/
private theorem countable_theory [∀ n, Countable (L.Relations n)] (T : L.Theory) : T.Countable :=
  T.to_countable

/-- In a relational language with countably many relation symbols of each arity, the model class of
every first-order theory on a countable carrier is measurable. -/
theorem measurableSet_modelsOfTheory [∀ n, Countable (L.Relations n)] [Countable V]
    (T : L.Theory) : MeasurableSet (modelsOfTheory (V := V) T) :=
  measurableSet_modelsOfTheory_of_countable (countable_theory T)

/-- In a relational language with countably many relation symbols of each arity, the model class of
every first-order theory on a countable carrier is a standard Borel space. -/
instance standardBorelSpace_modelsOfTheory [∀ n, Countable (L.Relations n)] [Countable V]
    (T : L.Theory) : StandardBorelSpace (modelsOfTheory (V := V) T) :=
  (measurableSet_modelsOfTheory T).standardBorel

/-- **A countable first-order theory has the model class of one `L_{ω₁ω}` sentence.** Embedding a
countable first-order theory into `L_{ω₁ω}` and taking `Theoryω.conjunction` yields the same model
class on every carrier `V`. -/
@[simp]
theorem modelsOf_conjunction_image_toOmega {T : L.Theory} (hT : T.Countable) :
    modelsOf (V := V) (Theoryω.conjunction (BoundedFormula.toOmega '' T) (hT.image _)) =
      modelsOfTheory T := by
  ext c
  rw [mem_modelsOf, mem_modelsOfTheory,
    @Theoryω.realize_conjunction_iff L _ V c.toStructure (hT.image _),
    @Theoryω.model_image_toOmega_iff L V c.toStructure T]

variable (V) in
/-- Isomorphism of decoded structures, restricted to the configurations on `V` that decode to
models of the first-order theory `T`. It is an abbreviation for `(isoSetoid L V).comap Subtype.val`,
so results stated for the restriction of `isoSetoid L V` to an arbitrary set of configurations
apply to it directly. -/
abbrev isoSetoidOnTheory (T : L.Theory) : Setoid (modelsOfTheory (V := V) T) :=
  (isoSetoid L V).comap Subtype.val

/-- Two models of `T` on `V` are related by `isoSetoidOnTheory` exactly when their decoded
structures are isomorphic. -/
@[simp]
theorem isoSetoidOnTheory_apply {T : L.Theory} {c d : modelsOfTheory (V := V) T} :
    isoSetoidOnTheory V T c d ↔ isoSetoid L V c d :=
  Iff.rfl

/-- If every model of `T₁` on `V` is a model of `T₂`, then `T₁` has at most as many isomorphism
classes of models on `V` as `T₂`. -/
theorem mk_quotient_isoSetoidOnTheory_le_of_subset {T₁ T₂ : L.Theory}
    (h : modelsOfTheory (V := V) T₁ ⊆ modelsOfTheory T₂) :
    #(Quotient (isoSetoidOnTheory V T₁)) ≤ #(Quotient (isoSetoidOnTheory V T₂)) := by
  refine mk_le_of_injective (f := Quotient.map (inclusion h) fun _ _ hcd => hcd) ?_
  intro p q
  induction p, q using Quotient.inductionOn₂ with
  | h c d =>
    intro hcd
    exact Quotient.sound (Quotient.exact (s := isoSetoidOnTheory V T₂) hcd)

/-- Expanding a first-order theory can only shrink the number of isomorphism classes of its models
on `V`. -/
theorem mk_quotient_isoSetoidOnTheory_anti {T₁ T₂ : L.Theory} (h : T₁ ⊆ T₂) :
    #(Quotient (isoSetoidOnTheory V T₂)) ≤ #(Quotient (isoSetoidOnTheory V T₁)) :=
  mk_quotient_isoSetoidOnTheory_le_of_subset (modelsOfTheory_anti h)

/-- On a countable carrier, in a relational language with countably many relation symbols of each
arity, the models of a first-order theory have at most continuum many isomorphism classes. -/
theorem mk_quotient_isoSetoidOnTheory_le_continuum [∀ n, Countable (L.Relations n)] (V : Type w)
    [Countable V] (T : L.Theory) : #(Quotient (isoSetoidOnTheory V T)) ≤ 𝔠 :=
  mk_quotient_le.trans ((mk_subtype_le _).trans (mk_le_continuum L V))

/-- **Finite-carrier dichotomy for first-order theories (perfect-set form).** On a finite carrier,
in a relational language with countably many relation symbols of each arity, the models of a
first-order theory have countably many isomorphism classes or contain a nonempty perfect set of
pairwise non-isomorphic models. -/
theorem countable_quotient_isoSetoidOnTheory_or_hasPerfectAntichainOn
    [∀ n, Countable (L.Relations n)] (V : Type w) [Finite V] (T : L.Theory) :
    Countable (Quotient (isoSetoidOnTheory V T)) ∨
      (isoSetoid L V).HasPerfectAntichainOn (modelsOfTheory T) := by
  have hT := countable_theory T
  have h := countable_quotient_isoSetoidOn_or_hasPerfectAntichainOn V
    (Theoryω.conjunction (BoundedFormula.toOmega '' T) (hT.image _))
  unfold isoSetoidOn at h
  unfold isoSetoidOnTheory
  rwa [modelsOf_conjunction_image_toOmega hT] at h

/-- **Finite-carrier dichotomy for first-order theories (cardinal form).** On a finite carrier, in
a relational language with countably many relation symbols of each arity, the models of a
first-order theory have at most `ℵ₀` or `𝔠` isomorphism classes. -/
theorem mk_quotient_isoSetoidOnTheory_le_aleph0_or_eq_continuum
    [∀ n, Countable (L.Relations n)] (V : Type w) [Finite V] (T : L.Theory) :
    #(Quotient (isoSetoidOnTheory V T)) ≤ ℵ₀ ∨ #(Quotient (isoSetoidOnTheory V T)) = 𝔠 := by
  have hT := countable_theory T
  have h := mk_quotient_isoSetoidOn_le_aleph0_or_eq_continuum V
    (Theoryω.conjunction (BoundedFormula.toOmega '' T) (hT.image _))
  unfold isoSetoidOn at h
  unfold isoSetoidOnTheory
  rwa [modelsOf_conjunction_image_toOmega hT] at h

end TauCeti.RelationalConfiguration

namespace FirstOrder.Language.LEquiv

open TauCeti TauCeti.RelationalConfiguration

variable {L : Language.{u, v}} {L' : Language.{u', v'}} [L.IsRelational] [L'.IsRelational]
  (e : L ≃ᴸ L')

/-- Transport along a language equivalence `e` identifies the isomorphism classes of the models of
a first-order theory `T` on `V` with those of `e.toLHom.onTheory T` on `V`. -/
noncomputable def quotientIsoSetoidOnTheoryEquiv (V : Type w) (T : L.Theory) :
    Quotient (isoSetoidOnTheory V T) ≃ Quotient (isoSetoidOnTheory V (e.toLHom.onTheory T)) :=
  Quotient.congr
    (e.onConfiguration.toEquiv.subtypeEquiv fun c => by
      rw [← Set.mem_preimage, Homeomorph.coe_toEquiv, preimage_onConfiguration_modelsOfTheory])
    fun _ _ => e.isoSetoid_onConfiguration_iff.symm

/-- `quotientIsoSetoidOnTheoryEquiv` sends the class of a model `c` of `T` to the class of its
transport along `e`. -/
@[simp]
theorem quotientIsoSetoidOnTheoryEquiv_mk {V : Type w} {T : L.Theory}
    (c : modelsOfTheory (V := V) T) :
    e.quotientIsoSetoidOnTheoryEquiv V T ⟦c⟧ =
      ⟦⟨e.onConfiguration c,
        by rw [← image_onConfiguration_modelsOfTheory]; exact ⟨c, c.2, rfl⟩⟩⟧ :=
  (rfl)

/-- A first-order theory and its image along a language equivalence have the same number of models
on `V` up to isomorphism, after lifting both counts to a common universe. -/
theorem lift_mk_quotient_isoSetoidOnTheory_onTheory (V : Type w) (T : L.Theory) :
    lift.{max v' w} #(Quotient (isoSetoidOnTheory V T)) =
      lift.{max v w} #(Quotient (isoSetoidOnTheory V (e.toLHom.onTheory T))) :=
  lift_mk_eq'.2 ⟨e.quotientIsoSetoidOnTheoryEquiv V T⟩

/-- A first-order theory and its image along a language equivalence have countably many models on
`V` up to isomorphism together. -/
@[simp]
theorem countable_quotient_isoSetoidOnTheory_onTheory_iff (V : Type w) (T : L.Theory) :
    Countable (Quotient (isoSetoidOnTheory V (e.toLHom.onTheory T))) ↔
      Countable (Quotient (isoSetoidOnTheory V T)) :=
  (e.quotientIsoSetoidOnTheoryEquiv V T).countable_iff.symm

/-- A first-order theory and its image along a language equivalence admit perfect antichains of
pairwise non-isomorphic models on `V` together. -/
@[simp]
theorem hasPerfectAntichainOn_modelsOfTheory_onTheory_iff (V : Type w) (T : L.Theory) :
    (isoSetoid L' V).HasPerfectAntichainOn (modelsOfTheory (V := V) (e.toLHom.onTheory T)) ↔
      (isoSetoid L V).HasPerfectAntichainOn (modelsOfTheory (V := V) T) := by
  rw [← e.image_onConfiguration_modelsOfTheory T]
  exact Setoid.hasPerfectAntichainOn_image_homeomorph_iff _
    (fun _ _ => e.isoSetoid_onConfiguration_iff) _

end FirstOrder.Language.LEquiv

namespace TauCeti

open RelationalConfiguration

variable {L : Language.{u, v}} [L.IsRelational]

/-! ### Morley's dichotomy and bounded-rank dichotomy for first-order theories on `ℕ` -/

/-- **Morley's theorem for countably infinite models of a first-order theory (witnessed form).**
In a relational language with countably many relation symbols of each arity, the models of a
first-order theory `T` on `ℕ` have at most `ℵ₁` isomorphism classes, or contain a nonempty perfect
set of pairwise non-isomorphic models. Neither CH nor completeness of `T` is assumed. -/
theorem mk_quotient_isoSetoidOnTheory_nat_le_aleph_one_or_hasPerfectAntichainOn
    [∀ n, Countable (L.Relations n)] (T : L.Theory) :
    #(Quotient (isoSetoidOnTheory ℕ T)) ≤ ℵ₁ ∨
      (isoSetoid L ℕ).HasPerfectAntichainOn (modelsOfTheory T) :=
  mk_isoClasses_le_aleph_one_or_hasPerfectAntichainOn (measurableSet_modelsOfTheory T)

/-- **Morley's theorem for countably infinite models of a first-order theory (cardinal form).** In
a relational language with countably many relation symbols of each arity, the models of a
first-order theory `T` on `ℕ` have either at most `ℵ₁` or `𝔠` isomorphism classes. -/
theorem mk_quotient_isoSetoidOnTheory_nat_le_aleph_one_or_eq_continuum
    [∀ n, Countable (L.Relations n)] (T : L.Theory) :
    #(Quotient (isoSetoidOnTheory ℕ T)) ≤ ℵ₁ ∨ #(Quotient (isoSetoidOnTheory ℕ T)) = 𝔠 :=
  mk_isoClasses_le_aleph_one_or_eq_continuum (measurableSet_modelsOfTheory T)

/-- **The bounded-rank dichotomy for countably infinite models of a first-order theory.** If an
isolating rank is bounded below `ω₁` on `modelsOfTheory (V := ℕ) T`, then `T` has countably many
countably infinite models up to isomorphism or a nonempty perfect set of pairwise non-isomorphic
models on `ℕ`. -/
theorem countable_quotient_isoSetoidOnTheory_nat_or_hasPerfectAntichainOn_of_bounded
    [∀ n, Countable (L.Relations n)] {ρ : RelationalConfiguration L ℕ → Ordinal.{0}}
    (hρ : IsIsolatingRank ρ) {β : Ordinal.{0}} (hβ : β < ω₁) {T : L.Theory}
    (hT : ∀ c ∈ modelsOfTheory (V := ℕ) T, ρ c ≤ β) :
    Countable (Quotient (isoSetoidOnTheory ℕ T)) ∨
      (isoSetoid L ℕ).HasPerfectAntichainOn (modelsOfTheory T) :=
  hρ.countable_isoClasses_or_hasPerfectAntichainOn (measurableSet_modelsOfTheory T) hβ hT

/-- **The Scott-height dichotomy for countably infinite models of a first-order theory.** If the
external Scott height is bounded below `ω₁` on the models of `T` on `ℕ`, then `T` has countably
many countably infinite models up to isomorphism or a nonempty perfect set of pairwise
non-isomorphic models on `ℕ`. -/
theorem countable_quotient_isoSetoidOnTheory_nat_or_hasPerfectAntichainOn_of_scottHeight_le
    [∀ n, Countable (L.Relations n)] {β : Ordinal.{0}} (hβ : β < ω₁) {T : L.Theory}
    (hT : ∀ c ∈ modelsOfTheory (V := ℕ) T, @scottHeight L _ ℕ c.toStructure ≤ β) :
    Countable (Quotient (isoSetoidOnTheory ℕ T)) ∨
      (isoSetoid L ℕ).HasPerfectAntichainOn (modelsOfTheory T) :=
  countable_quotient_isoSetoidOnTheory_nat_or_hasPerfectAntichainOn_of_bounded
    (isIsolatingRank_scottHeight L) hβ hT

/-- A first-order theory in a countable relational vocabulary fails the witnessed dichotomy on `ℕ`
if and only if it has `ℵ₁` countably infinite models up to isomorphism and no perfect antichain on
`modelsOfTheory (V := ℕ) T`. No CH hypothesis is needed. -/
theorem not_countable_and_not_hasPerfectAntichainOn_modelsOfTheory_iff
    [∀ n, Countable (L.Relations n)] {T : L.Theory} :
    ¬ (Countable (Quotient (isoSetoidOnTheory ℕ T)) ∨
        (isoSetoid L ℕ).HasPerfectAntichainOn (modelsOfTheory T)) ↔
      #(Quotient (isoSetoidOnTheory ℕ T)) = ℵ₁ ∧
        ¬ (isoSetoid L ℕ).HasPerfectAntichainOn (modelsOfTheory T) := by
  rw [not_or, ← mk_le_aleph0_iff, not_le]
  constructor
  · rintro ⟨hgt, hthin⟩
    have hle := (mk_quotient_isoSetoidOnTheory_nat_le_aleph_one_or_hasPerfectAntichainOn T)
      |>.resolve_right hthin
    exact ⟨hle.antisymm (aleph_one_le_iff.2 hgt), hthin⟩
  · rintro ⟨heq, hthin⟩
    exact ⟨heq ▸ aleph0_lt_aleph_one, hthin⟩

/-- Under CH, the models on `ℕ` of every first-order theory in a countable relational vocabulary
satisfy Vaught's cardinal dichotomy. -/
theorem mk_quotient_isoSetoidOnTheory_nat_le_aleph0_or_eq_continuum_of_aleph_one_eq_continuum
    [∀ n, Countable (L.Relations n)] (hCH : ℵ₁ = (𝔠 : Cardinal.{v})) (T : L.Theory) :
    #(Quotient (isoSetoidOnTheory ℕ T)) ≤ ℵ₀ ∨ #(Quotient (isoSetoidOnTheory ℕ T)) = 𝔠 := by
  rcases mk_quotient_isoSetoidOnTheory_nat_le_aleph_one_or_eq_continuum T with hle | heq
  · by_cases h₀ : #(Quotient (isoSetoidOnTheory ℕ T)) ≤ ℵ₀
    · exact .inl h₀
    · exact .inr (hCH ▸ hle.antisymm (aleph_one_le_iff.2 (not_le.1 h₀)))
  · exact .inr heq

/-- When `ℵ₁ < 𝔠`, the cardinal dichotomy on `ℕ` for a first-order theory `T` is equivalent to the
witnessed perfect-set dichotomy on `ℕ`. -/
theorem mk_quotient_isoSetoidOnTheory_nat_le_aleph0_or_eq_continuum_iff
    [∀ n, Countable (L.Relations n)] (hc : ℵ₁ < (𝔠 : Cardinal.{v})) {T : L.Theory} :
    (#(Quotient (isoSetoidOnTheory ℕ T)) ≤ ℵ₀ ∨ #(Quotient (isoSetoidOnTheory ℕ T)) = 𝔠) ↔
      (Countable (Quotient (isoSetoidOnTheory ℕ T)) ∨
        (isoSetoid L ℕ).HasPerfectAntichainOn (modelsOfTheory T)) := by
  rw [← mk_le_aleph0_iff]
  constructor
  · rintro (hle | heq)
    · exact .inl hle
    · rcases mk_quotient_isoSetoidOnTheory_nat_le_aleph_one_or_hasPerfectAntichainOn T with
        hle | hP
      · exact (hc.not_ge (heq ▸ hle)).elim
      · exact .inr hP
  · rintro (hle | hP)
    · exact .inl hle
    · exact .inr hP.hasCantorAntichainOn.mk_quotient_comap_eq_continuum

/-! ### Reduction to `L_{ω₁ω}` and the first-order Vaught conjecture -/

/-- **Countable first-order theories reduce to `L_{ω₁ω}` sentences.** Conjoining the `L_{ω₁ω}`
conjunction of a countable first-order theory `T` with `infiniteSentence` turns `HasVaughtDichotomy`
into the witnessed dichotomy for the models of `T` on `ℕ`. Neither completeness of `T` nor
countability of `L` is needed. -/
theorem hasVaughtDichotomy_conjunction_inf_infiniteSentence_iff {T : L.Theory}
    (hT : T.Countable) :
    HasVaughtDichotomy
        ((Theoryω.conjunction (BoundedFormula.toOmega '' T) (hT.image _)) ⊓ L.infiniteSentence) ↔
      Countable (Quotient (isoSetoidOnTheory ℕ T)) ∨
        (isoSetoid L ℕ).HasPerfectAntichainOn (modelsOfTheory T) := by
  rw [hasVaughtDichotomy_inf_infiniteSentence_iff]
  unfold isoSetoidOn isoSetoidOnTheory
  rw [modelsOf_conjunction_image_toOmega hT]

/-- `VaughtConjecture` implies the witnessed dichotomy on `ℕ` for every first-order theory (complete
or not) in every countable relational language in any universe `{u, v}`. -/
theorem VaughtConjecture.countable_quotient_isoSetoidOnTheory_or_hasPerfectAntichainOn
    (h : VaughtConjecture) (L : Language.{u, v}) [L.IsRelational]
    [Countable (Σ n, L.Relations n)] (T : L.Theory) :
    Countable (Quotient (isoSetoidOnTheory ℕ T)) ∨
      (isoSetoid L ℕ).HasPerfectAntichainOn (modelsOfTheory T) :=
  (hasVaughtDichotomy_conjunction_inf_infiniteSentence_iff T.to_countable).1
    (vaughtConjecture_iff_forall_universe.1 h L _)

/-- **The first-order Vaught conjecture** (in perfect-set form): every complete first-order theory
in a countable relational language in universe zero has countably many countably infinite models up
to isomorphism, or a nonempty perfect set of pairwise non-isomorphic models on `ℕ`. This is an open
conjecture, not an assertion made by the library. -/
def FirstOrderVaughtConjecture : Prop :=
  ∀ (L : Language.{0, 0}) [L.IsRelational] [Countable (Σ n, L.Relations n)]
    (T : L.Theory), T.IsComplete →
    Countable (Quotient (isoSetoidOnTheory ℕ T)) ∨
      (isoSetoid L ℕ).HasPerfectAntichainOn (modelsOfTheory T)

/-- Unfolding lemma for `TauCeti.FirstOrderVaughtConjecture`. -/
theorem firstOrderVaughtConjecture_iff :
    FirstOrderVaughtConjecture ↔
      ∀ (L : Language.{0, 0}) [L.IsRelational] [Countable (Σ n, L.Relations n)]
        (T : L.Theory), T.IsComplete →
        Countable (Quotient (isoSetoidOnTheory ℕ T)) ∨
          (isoSetoid L ℕ).HasPerfectAntichainOn (modelsOfTheory T) :=
  Iff.rfl

/-- **The `L_{ω₁ω}` Vaught conjecture implies the first-order Vaught conjecture.** Every
first-order theory in a countable relational language is a countable set of sentences, so its
countably infinite models are the countable models of a single `L_{ω₁ω}` sentence. -/
theorem VaughtConjecture.firstOrder (h : VaughtConjecture) : FirstOrderVaughtConjecture :=
  fun L _ _ T _ => h.countable_quotient_isoSetoidOnTheory_or_hasPerfectAntichainOn L T

/-- **Universe independence of the first-order Vaught conjecture.** Quantifying over countable
relational languages in `Language.{0, 0}` is equivalent to quantifying over countable relational
languages in arbitrary universes `{u, v}`. -/
theorem firstOrderVaughtConjecture_iff_forall_universe :
    FirstOrderVaughtConjecture ↔
      ∀ (L : Language.{u, v}) [L.IsRelational] [Countable (Σ n, L.Relations n)]
        (T : L.Theory), T.IsComplete →
        Countable (Quotient (isoSetoidOnTheory ℕ T)) ∨
          (isoSetoid L ℕ).HasPerfectAntichainOn (modelsOfTheory T) := by
  constructor
  · intro h L _ _ T hT
    let e := L.smallPresentationEquiv
    have h' := h L.smallPresentation (e.toLHom.onTheory T) (e.isComplete_onTheory_iff.2 hT)
    rwa [e.countable_quotient_isoSetoidOnTheory_onTheory_iff,
      e.hasPerfectAntichainOn_modelsOfTheory_onTheory_iff] at h'
  · intro h L₀ _ _ T₀ hT₀
    let e := Language.uliftEquiv.{0, 0, u, v} L₀
    have h' := h (Language.ulift.{0, 0, u, v} L₀) (e.toLHom.onTheory T₀)
      (e.isComplete_onTheory_iff.2 hT₀)
    rwa [e.countable_quotient_isoSetoidOnTheory_onTheory_iff,
      e.hasPerfectAntichainOn_modelsOfTheory_onTheory_iff] at h'

/-- **The scattered formulation of the first-order Vaught conjecture.** Without CH,
`FirstOrderVaughtConjecture` holds if and only if every complete first-order theory whose model
class on `ℕ` is back-and-forth scattered has countably many models on `ℕ` up to isomorphism. -/
theorem firstOrderVaughtConjecture_iff_bfScattered :
    FirstOrderVaughtConjecture ↔
      ∀ (L : Language.{0, 0}) [L.IsRelational] [Countable (Σ n, L.Relations n)]
        (T : L.Theory), T.IsComplete →
        BFScattered (modelsOfTheory (V := ℕ) T) →
        Countable (Quotient (isoSetoidOnTheory ℕ T)) := by
  rw [firstOrderVaughtConjecture_iff]
  constructor
  · intro h L _ _ T hT hscat
    exact (h L T hT).resolve_right (Setoid.isThinOn_iff.1 hscat.isThinOn)
  · intro h L _ _ T hT
    refine or_iff_not_imp_right.2 fun hthin => h L T hT ?_
    exact BFScattered.of_isThinOn (measurableSet_modelsOfTheory T) (Setoid.isThinOn_iff.2 hthin)

/-- **The cardinal formulation of the first-order Vaught conjecture** when `ℵ₁ < 𝔠`. Under CH,
every first-order theory already satisfies the cardinal dichotomy on `ℕ`
(`mk_quotient_isoSetoidOnTheory_nat_le_aleph0_or_eq_continuum_of_aleph_one_eq_continuum`), so the
equivalence requires `ℵ₁ < 𝔠`. -/
theorem firstOrderVaughtConjecture_iff_cardinal (hc : ℵ₁ < (𝔠 : Cardinal.{0})) :
    FirstOrderVaughtConjecture ↔
      ∀ (L : Language.{0, 0}) [L.IsRelational] [Countable (Σ n, L.Relations n)]
        (T : L.Theory), T.IsComplete →
        #(Quotient (isoSetoidOnTheory ℕ T)) ≤ ℵ₀ ∨ #(Quotient (isoSetoidOnTheory ℕ T)) = 𝔠 := by
  rw [firstOrderVaughtConjecture_iff]
  refine forall_congr' fun L => forall_congr' fun _ => forall_congr' fun _ =>
    forall_congr' fun T => imp_congr_right fun _ => ?_
  exact (mk_quotient_isoSetoidOnTheory_nat_le_aleph0_or_eq_continuum_iff hc).symm

end TauCeti

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.ModelTheory.ModelExistence.Morleyization
public import TauCeti.ModelTheory.RelationalConfiguration.LanguageMap
public import TauCeti.ModelTheory.RelationalConfiguration.Topology
public import TauCeti.SetTheory.Descriptive.Antichain

/-!
# Morleyization of relational configurations

For a relational language `L` and a set `Φ` of `L_{ω₁ω}` formulas, the Morleyization
`morleyize L Φ` adds one relation symbol `R_φ` for each member `φ` of `Φ`, and every
`L`-structure has a canonical expansion `morleyExpansion Φ M` in which `R_φ` means `φ`. This file
codes that expansion on configurations: `RelationalConfiguration.morleyCode Φ c` copies the atoms
of `c` and sets the atom `R_φ(x)` to the truth of `φ` at `x` in the structure decoded from `c`.

The expansion code decodes to the canonical expansion, has the reduct along `lhomMorleyize Φ` as
a left inverse, and its range consists of the configurations whose new atoms agree with the
formulas they name in their own reduct. On a countable carrier it is measurable, and when `Φ` is
countable it is a measurable embedding: the inverse on the range is the reduct, and the range is
cut out by countably many measurable conditions, so no Lusin–Souslin argument is needed. Since
canonical expansions are isomorphic exactly when the structures are, the expansion code preserves
and reflects isomorphism.

Together these make Morleyization invisible to the descriptive set theory of isomorphism: a set of
configurations carries a Cantor antichain for isomorphism, or is thin, exactly when its image
under the expansion code does. This lets arguments about the isomorphism classes of models of a
sentence pass to a language in which countably many chosen formulas are atomic.

## Main definitions

* `TauCeti.RelationalConfiguration.morleyCode`: the configuration of the canonical expansion.

## Main results

* `TauCeti.RelationalConfiguration.toStructure_morleyCode`: decoding the expansion code gives the
  canonical expansion of the decoded structure.
* `TauCeti.RelationalConfiguration.reductConfiguration_morleyCode`: the reduct recovers the base
  configuration, so `morleyCode_injective`.
* `TauCeti.RelationalConfiguration.range_morleyCode`: the range of the expansion code.
* `TauCeti.RelationalConfiguration.measurableEmbedding_morleyCode`: the expansion code is a
  measurable embedding for countable `Φ` on a countable carrier.
* `TauCeti.RelationalConfiguration.isoSetoid_morleyCode_iff`: expansion codes are isomorphic
  exactly when the base configurations are.
* `TauCeti.RelationalConfiguration.hasCantorAntichainOn_image_morleyCode_iff` and
  `TauCeti.RelationalConfiguration.isThinOn_image_morleyCode_iff`: Cantor antichains and thinness
  for isomorphism transfer across the expansion code.

## References

* M. Morley, *Omitting classes of elements*, in *The Theory of Models*, North-Holland, 1965,
  265–273.
* D. Marker, *Lectures on Infinitary Model Theory*, Cambridge University Press, 2016, Chapter 1.
-/

public section

universe u v w

open FirstOrder FirstOrder.Language Set

namespace TauCeti.RelationalConfiguration

variable {L : Language.{u, v}} [L.IsRelational] {V : Type w}

section Code

variable (Φ : Set (Σ n, L.BoundedFormulaω Empty n))

/-- The **expansion code** of a configuration `c` along the Morleyization by `Φ`: the
configuration of the canonical expansion of the structure decoded from `c`. Its atoms over
relation symbols of `L` are those of `c`, and its atom `R_φ(x)` is true exactly when `φ` holds of
`x` in the decoded structure. -/
noncomputable def morleyCode (c : RelationalConfiguration L V) :
    RelationalConfiguration (morleyize L Φ) V :=
  @ofStructure (morleyize L Φ) V (@morleyExpansion L Φ V c.toStructure)

variable {Φ}

/-- **Decoding agreement.** The expansion code decodes to the canonical expansion of the structure
decoded from the base configuration. -/
@[simp]
theorem toStructure_morleyCode (c : RelationalConfiguration L V) :
    (morleyCode Φ c).toStructure = @morleyExpansion L Φ V c.toStructure :=
  toStructure_ofStructure _

/-- The expansion code copies the atoms over relation symbols of `L`. -/
@[simp]
theorem eval_morleyCode_inl (c : RelationalConfiguration L V) {n : ℕ} (R : L.Relations n)
    (x : Fin n → V) :
    (morleyCode Φ c).eval (atom (L := morleyize L Φ) (Sum.inl R) x) = c.eval (atom R x) := by
  classical
  simp [morleyCode]

/-- The atom `R_φ(x)` of the expansion code is true exactly when `φ` holds of `x` in the structure
decoded from the base configuration. -/
@[simp]
theorem eval_morleyCode_morleyRel_eq_true_iff (c : RelationalConfiguration L V) {n : ℕ}
    {φ : L.BoundedFormulaω Empty n} (hφ : ⟨n, φ⟩ ∈ Φ) (x : Fin n → V) :
    (morleyCode Φ c).eval (atom (morleyRel φ hφ) x) = true ↔
      @BoundedFormulaInf.Realize L ℕ Empty V c.toStructure n φ Empty.elim x := by
  classical
  simp [morleyCode]

/-- The reduct of the expansion code along the inclusion of `L` is the base configuration. -/
@[simp]
theorem reductConfiguration_morleyCode (c : RelationalConfiguration L V) :
    (lhomMorleyize Φ).reductConfiguration (morleyCode Φ c) = c :=
  ext fun a => by
    induction a using Atom.induction_atom with
    | h R x => simp

/-- The expansion code is injective: the reduct is a left inverse. -/
theorem morleyCode_injective : Function.Injective (morleyCode (V := V) Φ) :=
  Function.LeftInverse.injective reductConfiguration_morleyCode

/-- A configuration of the Morleyization is the expansion code of its reduct exactly when each of
its new atoms `R_φ(x)` agrees with the truth of `φ` at `x` in the reduct. -/
theorem eq_morleyCode_reductConfiguration_iff {e : RelationalConfiguration (morleyize L Φ) V} :
    e = morleyCode Φ ((lhomMorleyize Φ).reductConfiguration e) ↔
      ∀ (n : ℕ) (φ : L.BoundedFormulaω Empty n) (hφ : ⟨n, φ⟩ ∈ Φ) (x : Fin n → V),
        e.eval (atom (morleyRel φ hφ) x) = true ↔
          @BoundedFormulaInf.Realize L ℕ Empty V
            ((lhomMorleyize Φ).reductConfiguration e).toStructure n φ Empty.elim x := by
  refine ⟨fun h n φ hφ x => ?_, fun h => ext fun a => ?_⟩
  · conv_lhs => rw [h]
    exact eval_morleyCode_morleyRel_eq_true_iff _ hφ x
  · induction a using Atom.induction_atom with
    | h R x =>
      rcases R with R | ⟨φ, hφ⟩
      · simp
      · exact Bool.eq_iff_iff.2 <|
          (h _ φ hφ x).trans (eval_morleyCode_morleyRel_eq_true_iff _ hφ x).symm

/-- **The range of the expansion code**: the configurations of the Morleyization whose new atoms
`R_φ(x)` agree with the truth of `φ` at `x` in their reduct to `L`. -/
theorem range_morleyCode :
    range (morleyCode (V := V) Φ) =
      {e | ∀ (n : ℕ) (φ : L.BoundedFormulaω Empty n) (hφ : ⟨n, φ⟩ ∈ Φ) (x : Fin n → V),
        e.eval (atom (morleyRel φ hφ) x) = true ↔
          @BoundedFormulaInf.Realize L ℕ Empty V
            ((lhomMorleyize Φ).reductConfiguration e).toStructure n φ Empty.elim x} := by
  ext e
  refine ⟨?_, fun h => ⟨_, (eq_morleyCode_reductConfiguration_iff.2 h).symm⟩⟩
  rintro ⟨c, rfl⟩
  exact eq_morleyCode_reductConfiguration_iff.1 (by rw [reductConfiguration_morleyCode])

/-! ### Measurability -/

/-- On a countable carrier the expansion code is measurable, for every family `Φ`: each new atom
reads the truth of one formula, which is a measurable condition on configurations. -/
@[fun_prop]
theorem measurable_morleyCode [Countable V] : Measurable (morleyCode (V := V) Φ) :=
  measurable_iff.2 fun a => by
    induction a using Atom.induction_atom with
    | h R x =>
      rcases R with R | ⟨φ, hφ⟩
      · simpa using measurable_eval (atom R x)
      · refine measurable_to_bool ?_
        simpa [preimage] using
          measurableSet_setOf_realize φ Empty.elim x

/-- On a countable carrier, the range of the expansion code along a countable family `Φ` is
measurable. -/
theorem measurableSet_range_morleyCode [Countable V] (hΦ : Φ.Countable) :
    MeasurableSet (range (morleyCode (V := V) Φ)) := by
  have hslice (n : ℕ) : Countable {φ : L.BoundedFormulaω Empty n // ⟨n, φ⟩ ∈ Φ} :=
    (hΦ.preimage sigma_mk_injective).to_subtype
  have hreduct (n : ℕ) (φ : L.BoundedFormulaω Empty n) (x : Fin n → V) :
      MeasurableSet {e : RelationalConfiguration (morleyize L Φ) V |
        @BoundedFormulaInf.Realize L ℕ Empty V
          ((lhomMorleyize Φ).reductConfiguration e).toStructure n φ Empty.elim x} :=
    (lhomMorleyize Φ).measurable_reductConfiguration (measurableSet_setOf_realize φ Empty.elim x)
  -- Index the conditions of `range_morleyCode` by the countable slices of `Φ`.
  have hrange : range (morleyCode (V := V) Φ) =
      ⋂ (n : ℕ) (φ : {φ : L.BoundedFormulaω Empty n // ⟨n, φ⟩ ∈ Φ}) (x : Fin n → V),
        {e | e.eval (atom (morleyRel φ.1 φ.2) x) = true ↔
          @BoundedFormulaInf.Realize L ℕ Empty V
            ((lhomMorleyize Φ).reductConfiguration e).toStructure n φ.1 Empty.elim x} := by
    rw [range_morleyCode]
    ext e
    simp only [mem_ofPred_eq, mem_iInter, Subtype.forall]
  rw [hrange]
  exact .iInter fun n => .iInter fun φ => .iInter fun x =>
    (measurableSet_setOf_eval _ true).iff (hreduct n φ.1 x)

/-- **The expansion code is a measurable embedding** along a countable family `Φ` on a countable
carrier. Its measurable left inverse is the reduct, and its range is measurable. -/
theorem measurableEmbedding_morleyCode [Countable V] (hΦ : Φ.Countable) :
    MeasurableEmbedding (morleyCode (V := V) Φ) :=
  .of_measurable_inverse measurable_morleyCode (measurableSet_range_morleyCode hΦ)
    (lhomMorleyize Φ).measurable_reductConfiguration reductConfiguration_morleyCode

/-! ### Isomorphism -/

/-- **Expansion codes are isomorphic exactly when the base configurations are**, by decoding
agreement and `nonempty_morleyEquiv_iff`. -/
@[simp]
theorem isoSetoid_morleyCode_iff {c d : RelationalConfiguration L V} :
    isoSetoid (morleyize L Φ) V (morleyCode Φ c) (morleyCode Φ d) ↔ isoSetoid L V c d := by
  rw [isoSetoid_apply, isoSetoid_apply, toStructure_morleyCode, toStructure_morleyCode]
  exact @nonempty_morleyEquiv_iff L Φ V V c.toStructure d.toStructure

/-- **Transport of Cantor antichains along the expansion code.** For countable `Φ` on a countable
carrier in a vocabulary with countably many relation symbols of each arity, a set of
configurations carries a Cantor antichain for isomorphism exactly when its image under the
expansion code does. No Borel hypothesis is made on the set. -/
theorem hasCantorAntichainOn_image_morleyCode_iff [∀ n, Countable (L.Relations n)] [Countable V]
    (hΦ : Φ.Countable) (K : Set (RelationalConfiguration L V)) :
    (isoSetoid (morleyize L Φ) V).HasCantorAntichainOn (morleyCode Φ '' K) ↔
      (isoSetoid L V).HasCantorAntichainOn K := by
  have (n : ℕ) : Countable {φ : L.BoundedFormulaω Empty n // ⟨n, φ⟩ ∈ Φ} :=
    (hΦ.preimage sigma_mk_injective).to_subtype
  exact Setoid.hasCantorAntichainOn_image_iff (measurableEmbedding_morleyCode hΦ)
    (fun _ _ => isoSetoid_morleyCode_iff) K

/-- **Transport of thinness along the expansion code.** For countable `Φ` on a countable carrier
in a vocabulary with countably many relation symbols of each arity, a set of configurations is
thin for isomorphism exactly when its image under the expansion code is. -/
theorem isThinOn_image_morleyCode_iff [∀ n, Countable (L.Relations n)] [Countable V]
    (hΦ : Φ.Countable) (K : Set (RelationalConfiguration L V)) :
    (isoSetoid (morleyize L Φ) V).IsThinOn (morleyCode Φ '' K) ↔
      (isoSetoid L V).IsThinOn K := by
  have (n : ℕ) : Countable {φ : L.BoundedFormulaω Empty n // ⟨n, φ⟩ ∈ Φ} :=
    (hΦ.preimage sigma_mk_injective).to_subtype
  exact Setoid.isThinOn_image_iff (measurableEmbedding_morleyCode hΦ)
    (fun _ _ => isoSetoid_morleyCode_iff) K

end Code

end TauCeti.RelationalConfiguration

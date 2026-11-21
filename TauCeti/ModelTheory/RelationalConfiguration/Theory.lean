/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.ModelTheory.Infinitary.Theory
public import TauCeti.ModelTheory.RelationalConfiguration.LanguageMap
import Mathlib.ModelTheory.Encoding

/-!
# Model classes of first-order theories

For a relational language `L`, a carrier `V` and a first-order theory `T : L.Theory`, the **model
class** `TauCeti.RelationalConfiguration.modelsOfTheory T` is the set of configurations on `V`
whose decoded structures model `T`. It is the intersection over `φ ∈ T` of the single-sentence
model classes `modelsOf φ.toOmega`, so it turns unions of theories into intersections of model
classes, is antitone in the theory, and is invariant under isomorphism of decoded structures.

When the image of `T` in `L_{ω₁ω}` is countable—in particular for every first-order theory when `L`
has countably many relation symbols of each arity, by Mathlib's countability of finitary
formulas—`modelsOfTheory T` coincides with the model class `modelsOf` of one `L_{ω₁ω}` sentence,
the coded conjunction `Theoryω.conjunction (BoundedFormula.toOmega '' T)`. On a countable carrier,
the model class of any countable theory (hence of any theory in a countable relational vocabulary)
is a Borel subset of configuration space, and therefore a standard Borel space when the vocabulary
is countable.

Along a language map `g : L →ᴸ L'`, a configuration models `g.onTheory T` exactly when its reduct
`g.reductConfiguration` models `T`. Along a language equivalence `e : L ≃ᴸ L'`, the configuration
homeomorphism `e.onConfiguration` carries `modelsOfTheory T` onto
`modelsOfTheory (e.toLHom.onTheory T)` and identifies their isomorphism quotients.

## Main definitions

* `TauCeti.RelationalConfiguration.modelsOfTheory`: the configurations on `V` decoding to models of
  a first-order theory `T`.

## Main results

* `TauCeti.RelationalConfiguration.modelsOfTheory_eq_biInter`, `modelsOfTheory_empty`,
  `modelsOfTheory_singleton`, `modelsOfTheory_insert`, `modelsOfTheory_union`,
  `modelsOfTheory_iUnion`, and `modelsOfTheory_anti`: set-theoretic laws for model classes of
  theories.
* `TauCeti.RelationalConfiguration.modelsOf_conjunction_image_toOmega`: every first-order
  theory whose `L_{ω₁ω}` image is countable (in particular every theory in a countable relational
  vocabulary, by `Set.to_countable`) has the same model class as a single `L_{ω₁ω}` sentence.
* `TauCeti.RelationalConfiguration.measurableSet_modelsOfTheory_of_countable`,
  `TauCeti.RelationalConfiguration.measurableSet_modelsOfTheory`, and
  `TauCeti.RelationalConfiguration.standardBorelSpace_modelsOfTheory`: Borel measurability and
  standard Borel structure on countable carriers.
* `FirstOrder.Language.Equiv.mem_modelsOfTheory_iff`,
  `TauCeti.RelationalConfiguration.isomorphismInvariant_modelsOfTheory`, and
  `Equiv.encodeVia_mem_modelsOfTheory_iff`: invariance under isomorphism and carrier bijections.
* `FirstOrder.Language.LHom.mem_modelsOfTheory_reductConfiguration_iff`,
  `FirstOrder.Language.LEquiv.preimage_onConfiguration_modelsOfTheory`,
  `FirstOrder.Language.LEquiv.image_onConfiguration_modelsOfTheory`, and
  `FirstOrder.Language.LEquiv.quotientIsoSetoidModelsOfTheoryEquiv`: transport along language maps
  and language equivalences.
-/

public section

universe u v u' v' w w'

open FirstOrder FirstOrder.Language

namespace TauCeti.RelationalConfiguration

variable {L : Language.{u, v}} [L.IsRelational] {V : Type w}

/-- The **model class** of a first-order theory: the configurations on `V` whose decoded structures
satisfy every sentence of `T`. -/
def modelsOfTheory (T : L.Theory) : Set (RelationalConfiguration L V) :=
  {c | @Theory.Model L V c.toStructure T}

/-- A configuration lies in `modelsOfTheory T` exactly when its decoded structure models `T`. -/
@[simp]
theorem mem_modelsOfTheory {T : L.Theory} {c : RelationalConfiguration L V} :
    c ∈ modelsOfTheory T ↔ @Theory.Model L V c.toStructure T :=
  Iff.rfl

/-- Membership in `modelsOfTheory T` unpacked as realization of every sentence of `T`. -/
theorem mem_modelsOfTheory_iff_forall {T : L.Theory} {c : RelationalConfiguration L V} :
    c ∈ modelsOfTheory T ↔ ∀ φ ∈ T, @Sentence.Realize L V c.toStructure φ :=
  @Theory.model_iff L V c.toStructure T

/-- The model class of a first-order theory is the intersection of the model classes of its
sentences embedded into `L_{ω₁ω}`. -/
theorem modelsOfTheory_eq_biInter (T : L.Theory) :
    modelsOfTheory (V := V) T = ⋂ φ ∈ T, modelsOf φ.toOmega := by
  ext c
  simp [Theory.model_iff, Sentence.Realize, Formula.Realize]

/-- Every configuration decodes to a model of the empty theory. -/
@[simp]
theorem modelsOfTheory_empty : modelsOfTheory (V := V) (∅ : L.Theory) = Set.univ := by
  ext c
  simp [modelsOfTheory_eq_biInter]

/-- The model class of a singleton theory `{φ}` is the model class of `φ.toOmega`. -/
@[simp]
theorem modelsOfTheory_singleton (φ : L.Sentence) :
    modelsOfTheory (V := V) {φ} = modelsOf φ.toOmega := by
  ext c
  simp [modelsOfTheory_eq_biInter]

/-- Adding a sentence `φ` to a theory intersects its model class with `modelsOf φ.toOmega`. -/
@[simp]
theorem modelsOfTheory_insert (φ : L.Sentence) (T : L.Theory) :
    modelsOfTheory (V := V) (insert φ T) = modelsOf φ.toOmega ∩ modelsOfTheory T := by
  ext c
  simp [modelsOfTheory_eq_biInter]

/-- The model class of a union of two theories is the intersection of their model classes. -/
@[simp]
theorem modelsOfTheory_union (T₁ T₂ : L.Theory) :
    modelsOfTheory (V := V) (T₁ ∪ T₂) = modelsOfTheory T₁ ∩ modelsOfTheory T₂ := by
  ext c
  simp [modelsOfTheory_eq_biInter, or_imp, forall_and]

/-- The model class of an indexed union of theories is the intersection of their model classes. -/
theorem modelsOfTheory_iUnion {κ : Sort*} (Ts : κ → L.Theory) :
    modelsOfTheory (V := V) (⋃ i, Ts i) = ⋂ i, modelsOfTheory (Ts i) := by
  ext c
  simpa [modelsOfTheory_eq_biInter] using forall_comm

/-- Larger theories have smaller model classes. -/
theorem modelsOfTheory_anti : Antitone (modelsOfTheory (L := L) (V := V)) :=
  fun _ _ h c hc => @Theory.Model.mono L V c.toStructure _ _ hc h

/-! ### Reduction of countable theories to one `L_{ω₁ω}` sentence -/

/-- **A countable first-order theory has the model class of one `L_{ω₁ω}` sentence**: the coded
conjunction of the images of its sentences under `BoundedFormula.toOmega`. -/
@[simp]
theorem modelsOf_conjunction_image_toOmega {T : L.Theory}
    (hT : (BoundedFormula.toOmega '' T).Countable) :
    modelsOf (V := V) (Theoryω.conjunction (BoundedFormula.toOmega '' T) hT) =
      modelsOfTheory T := by
  ext c
  rw [mem_modelsOf, mem_modelsOfTheory,
    @Theoryω.realize_conjunction_iff L _ V c.toStructure hT,
    @Theoryω.model_image_toOmega_iff L V c.toStructure T]

/-! ### Borel measurability -/

/-- On a countable carrier, the model class of any countable first-order theory is measurable, with
no countability assumption on the language. -/
theorem measurableSet_modelsOfTheory_of_countable [Countable V] {T : L.Theory} (hT : T.Countable) :
    MeasurableSet (modelsOfTheory (V := V) T) := by
  rw [modelsOfTheory_eq_biInter]
  exact MeasurableSet.biInter hT fun φ _ => measurableSet_modelsOf φ.toOmega

/-- On a countable carrier, in a relational language with countably many relation symbols of each
arity, the model class of every first-order theory is Borel measurable. -/
theorem measurableSet_modelsOfTheory [∀ n, Countable (L.Relations n)] [Countable V]
    (T : L.Theory) : MeasurableSet (modelsOfTheory (V := V) T) :=
  measurableSet_modelsOfTheory_of_countable (Set.to_countable T)

/-- In a relational language with countably many relation symbols of each arity, the model class of
a first-order theory on a countable carrier is a standard Borel space. -/
instance standardBorelSpace_modelsOfTheory [∀ n, Countable (L.Relations n)] [Countable V]
    (T : L.Theory) : StandardBorelSpace (modelsOfTheory (V := V) T) :=
  (measurableSet_modelsOfTheory T).standardBorel

end TauCeti.RelationalConfiguration

/-! ### Invariance under isomorphism and carrier transport -/

namespace FirstOrder.Language.Equiv

open TauCeti RelationalConfiguration

variable {L : Language.{u, v}} [L.IsRelational] {V : Type w} {W : Type w'}

/-- Model classes of first-order theories are invariant under isomorphism of decoded structures,
across possibly different carriers. -/
theorem mem_modelsOfTheory_iff {c : RelationalConfiguration L V} {d : RelationalConfiguration L W}
    (e : @Language.Equiv L V W c.toStructure d.toStructure) (T : L.Theory) :
    c ∈ modelsOfTheory T ↔ d ∈ modelsOfTheory T := by
  simp only [modelsOfTheory_eq_biInter, Set.mem_iInter, e.mem_modelsOf_iff]

end FirstOrder.Language.Equiv

namespace TauCeti.RelationalConfiguration

variable {L : Language.{u, v}} [L.IsRelational] {V : Type w}

/-- Model classes of first-order theories are isomorphism invariant. -/
theorem isomorphismInvariant_modelsOfTheory (T : L.Theory) :
    IsomorphismInvariant (modelsOfTheory (V := V) T) :=
  isomorphismInvariant_iff.2 fun _ _ h hc => by
    obtain ⟨e⟩ := isoSetoid_apply.1 h
    exact (e.mem_modelsOfTheory_iff T).1 hc

end TauCeti.RelationalConfiguration

namespace Equiv

open TauCeti RelationalConfiguration

variable {L : Language.{u, v}} [L.IsRelational] {M : Type w} {V : Type w'} [L.Structure M]

/-- Encoding a structure along a bijection of carriers lands in `modelsOfTheory T` if and only if
the structure models `T`. -/
theorem encodeVia_mem_modelsOfTheory_iff (e : M ≃ V) (T : L.Theory) :
    e.encodeVia (L := L) ∈ modelsOfTheory T ↔ M ⊨ T := by
  simp only [modelsOfTheory_eq_biInter, Set.mem_iInter, mem_modelsOf, e.realize_encodeVia,
    Sentence.realize_toInf, Theory.model_iff]

end Equiv

/-! ### Transport along language maps and language equivalences -/

namespace FirstOrder.Language

open TauCeti TauCeti.RelationalConfiguration

variable {L : Language.{u, v}} {L' : Language.{u', v'}} [L.IsRelational] [L'.IsRelational]
  {V : Type w}

namespace LHom

/-- A configuration models the translated theory `g.onTheory T` if and only if its reduct
configuration along `g` models `T`. -/
theorem mem_modelsOfTheory_reductConfiguration_iff (g : L →ᴸ L') (c : RelationalConfiguration L' V)
    (T : L.Theory) :
    c ∈ modelsOfTheory (g.onTheory T) ↔ g.reductConfiguration c ∈ modelsOfTheory T := by
  rw [mem_modelsOfTheory, mem_modelsOfTheory, g.toStructure_reductConfiguration]
  let := c.toStructure
  let := g.reduct V
  exact g.onTheory_model T

/-- Pulling back `modelsOfTheory T` along `g.reductConfiguration` yields
`modelsOfTheory (g.onTheory T)`. -/
@[simp]
theorem preimage_reductConfiguration_modelsOfTheory (g : L →ᴸ L') (T : L.Theory) :
    g.reductConfiguration ⁻¹' modelsOfTheory (V := V) T = modelsOfTheory (g.onTheory T) :=
  Set.ext fun c => (g.mem_modelsOfTheory_reductConfiguration_iff c T).symm

end LHom

namespace LEquiv

variable (e : L ≃ᴸ L')

/-- Transporting a configuration along `e` lands in `modelsOfTheory (e.toLHom.onTheory T)` if and
only if the configuration lies in `modelsOfTheory T`. -/
theorem mem_modelsOfTheory_onConfiguration_iff (c : RelationalConfiguration L V) (T : L.Theory) :
    e.onConfiguration c ∈ modelsOfTheory (e.toLHom.onTheory T) ↔ c ∈ modelsOfTheory T := by
  rw [e.toLHom.mem_modelsOfTheory_reductConfiguration_iff,
    toLHom_reductConfiguration_onConfiguration]

/-- Pulling back `modelsOfTheory (e.toLHom.onTheory T)` along `e.onConfiguration` recovers
`modelsOfTheory T`. -/
@[simp]
theorem preimage_onConfiguration_modelsOfTheory (T : L.Theory) :
    e.onConfiguration ⁻¹' modelsOfTheory (V := V) (e.toLHom.onTheory T) = modelsOfTheory T :=
  Set.ext fun c => e.mem_modelsOfTheory_onConfiguration_iff c T

/-- `e.onConfiguration` carries `modelsOfTheory T` onto `modelsOfTheory (e.toLHom.onTheory T)`. -/
@[simp]
theorem image_onConfiguration_modelsOfTheory (T : L.Theory) :
    e.onConfiguration '' modelsOfTheory (V := V) T = modelsOfTheory (e.toLHom.onTheory T) := by
  rw [← e.preimage_onConfiguration_modelsOfTheory T,
    Set.image_preimage_eq _ e.onConfiguration.surjective]

/-- Transport along `e` identifies the isomorphism classes of the models of a first-order theory
`T` on `V` with those of its translation `e.toLHom.onTheory T` on `V`. -/
noncomputable def quotientIsoSetoidModelsOfTheoryEquiv (V : Type w) (T : L.Theory) :
    Quotient ((isoSetoid L V).comap (Subtype.val : modelsOfTheory T → _)) ≃
      Quotient ((isoSetoid L' V).comap
        (Subtype.val : modelsOfTheory (e.toLHom.onTheory T) → _)) :=
  Quotient.congr
    (e.onConfiguration.toEquiv.subtypeEquiv fun c => by
      rw [← Set.mem_preimage, Homeomorph.coe_toEquiv, preimage_onConfiguration_modelsOfTheory])
    fun _ _ => e.isoSetoid_onConfiguration_iff.symm

/-- `quotientIsoSetoidModelsOfTheoryEquiv` sends the class of a model `c` of `T` to the class of
its transport along `e`. -/
@[simp]
theorem quotientIsoSetoidModelsOfTheoryEquiv_mk {T : L.Theory} (c : modelsOfTheory (V := V) T) :
    e.quotientIsoSetoidModelsOfTheoryEquiv V T ⟦c⟧ =
      ⟦⟨e.onConfiguration c, (e.mem_modelsOfTheory_onConfiguration_iff c.val T).2 c.property⟩⟧ :=
  (rfl)

end LEquiv

end FirstOrder.Language

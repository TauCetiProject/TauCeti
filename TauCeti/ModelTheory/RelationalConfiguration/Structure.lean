/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.ModelTheory.RelationalConfiguration.Basic
public import TauCeti.ModelTheory.Infinitary.Equiv

/-!
# Decoding relational configurations

For a relational language, `RelationalConfiguration.toStructure` and the existing
`RelationalConfiguration.ofStructure` identify configurations with all structures on the fixed
carrier. Decoding is explicit: different configurations describe different structures on the
same type. Empty carriers and nullary relations are included.

`Equiv.encodeVia` represents a structure on a bijective carrier. It preserves infinitary
sentences, so structures in arbitrary universes can be represented on standard finite or
countably infinite carriers. Transport reuses Mathlib's `Equiv.inducedStructure` and
`Equiv.inducedStructureEquiv`.
-/

public section

universe u v w w' w''

open FirstOrder FirstOrder.Language

namespace TauCeti.RelationalConfiguration

variable {L : Language.{u, v}} {V : Type w}

/-- Decode a configuration into a relational structure, without installing an instance. -/
@[instance_reducible]
def toStructure [L.IsRelational] (c : RelationalConfiguration L V) : L.Structure V where
  RelMap R a := c.eval (atom R a) = true

/-- A decoded relation holds exactly when the corresponding atom is true. -/
@[simp]
theorem toStructure_relMap [L.IsRelational] (c : RelationalConfiguration L V) {n : ℕ}
    (R : L.Relations n) (a : Fin n → V) :
    @Structure.RelMap _ _ c.toStructure n R a ↔ c.eval (atom R a) = true := Iff.rfl

/-- Encoding after decoding recovers every configuration. -/
@[simp]
theorem ofStructure_toStructure [L.IsRelational] (c : RelationalConfiguration L V) :
    @ofStructure L V c.toStructure = c := by
  classical
  apply ext
  intro a
  induction a using Atom.induction_atom with
  | h R a => simp

/-- Decoding after encoding recovers the entire structure in a relational language. -/
@[simp]
theorem toStructure_ofStructure [L.IsRelational] (S : L.Structure V) :
    (@ofStructure L V S).toStructure = S := by
  classical
  apply Structure.ext
  · funext n f
    exact isEmptyElim f
  · funext n R a
    exact propext (by simp)

/-- Configurations and relational structures on a fixed carrier are in bijection. -/
noncomputable def equivStructure [L.IsRelational] :
    RelationalConfiguration L V ≃ L.Structure V where
  toFun := toStructure
  invFun := fun S => @ofStructure L V S
  left_inv := ofStructure_toStructure
  right_inv := toStructure_ofStructure

@[simp]
theorem equivStructure_apply [L.IsRelational] (c : RelationalConfiguration L V) :
    equivStructure c = c.toStructure := (rfl)

@[simp]
theorem equivStructure_symm_apply [L.IsRelational] (S : L.Structure V) :
    equivStructure.symm S = @ofStructure L V S := (rfl)

end TauCeti.RelationalConfiguration

namespace Equiv

open TauCeti RelationalConfiguration

variable {L : Language.{u, v}} {M : Type w} {V : Type w'} {W : Type w''}
variable [L.Structure M]

/-- Encode a structure after transporting it along a bijection of carriers. -/
noncomputable def encodeVia (e : M ≃ V) : RelationalConfiguration L V :=
  @ofStructure L V e.inducedStructure

/-- Transport reads a relation at the inverse image of its argument tuple. -/
@[simp]
theorem eval_encodeVia (e : M ≃ V) {n : ℕ} (R : L.Relations n) (a : Fin n → V) :
    (e.encodeVia (L := L)).eval (atom R a) =
      @decide (Structure.RelMap R (e.symm ∘ a)) (Classical.propDecidable _) := by
  classical
  simp [encodeVia]

/-- Decoding a transported configuration gives exactly the induced structure. -/
@[simp]
theorem toStructure_encodeVia [L.IsRelational] (e : M ≃ V) :
    (e.encodeVia (L := L)).toStructure = e.inducedStructure := by
  simp [encodeVia]

/-- A transported configuration names a structure isomorphic to the original in any universe. -/
theorem nonempty_equiv_encodeVia [L.IsRelational] (e : M ≃ V) :
    Nonempty (@Language.Equiv L M V _ (e.encodeVia (L := L)).toStructure) := by
  rw [toStructure_encodeVia]
  exact ⟨e.inducedStructureEquiv⟩

/-- Encoding through the identity is encoding the original structure. -/
@[simp]
theorem encodeVia_refl : (Equiv.refl M).encodeVia (L := L) = ofStructure L M := by
  classical
  apply RelationalConfiguration.ext
  intro a
  induction a using Atom.induction_atom with
  | h R a => simp [encodeVia]

/-- Successive carrier transports agree with transport along the composite bijection. -/
theorem encodeVia_trans (e : M ≃ V) (f : V ≃ W) :
    (e.trans f).encodeVia (L := L) = @encodeVia L V W e.inducedStructure f := by
  classical
  let := e.inducedStructure (L := L)
  apply RelationalConfiguration.ext
  intro a
  induction a using Atom.induction_atom with
  | h R a =>
    rw [eval_encodeVia, eval_encodeVia]
    rfl

/-- Carrier transport preserves every countably infinitary sentence, including on empty types. -/
theorem realize_encodeVia [L.IsRelational] (e : M ≃ V) (φ : L.Sentenceω) :
    @SentenceInf.Realize L ℕ φ V (e.encodeVia (L := L)).toStructure ↔
      SentenceInf.Realize φ M := by
  rw [toStructure_encodeVia]
  let := e.inducedStructure (L := L)
  exact (StrongHomClass.realize_sentenceInf e.inducedStructureEquiv φ).symm

end Equiv

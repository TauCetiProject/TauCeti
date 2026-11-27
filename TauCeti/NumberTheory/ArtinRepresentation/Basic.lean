/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Normed.Operator.NormedSpace
public import Mathlib.RepresentationTheory.Character
public import TauCeti.FieldTheory.Galois.AbsoluteGaloisGroup.Basic
public import TauCeti.RepresentationTheory.Continuous.Character
public import TauCeti.RepresentationTheory.Continuous.ContinuousRep.Basic

import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps
import TauCeti.RepresentationTheory.Continuous.Hom
import TauCeti.RepresentationTheory.Continuous.Intertwining

/-!
# Artin representations of a field

An *Artin representation* of a field `F` is a finite-dimensional complex representation of the
absolute Galois group `G_F = Field.absoluteGaloisGroup F` which is continuous for the Krull
topology on `G_F` and the operator-norm topology on `V →L[ℂ] V`. This file introduces the carrier
`TauCeti.ArtinRep F V`, Mathlib's `ContRepresentation ℂ G_F V` together with continuity of the
action, and develops the basic consequences of continuity.

Since `G_F` is profinite and the group of invertible operators on a normed space has no small
subgroups, continuity is equivalent to openness of the kernel
(`ContRepresentation.continuous_iff_isOpen_ker`). Hence the kernel `ρ.ker` is an open normal
subgroup of finite index, and the image `ρ.range ≅ G_F ⧸ ρ.ker` is a finite subgroup of
`(V →L[ℂ] V)ˣ`. These facts are the starting point of the reduction of every statement about an
Artin representation to a representation of the Galois group of a finite Galois extension, the
fixed field of `ρ.ker`.

On a finite-dimensional space continuity of the operators `g ↦ ρ g` is the same as joint
continuity of the action `G_F × V → V`, so Artin representations are the same as Tau Ceti's
jointly continuous representations `TauCeti.ContinuousRep G_F ℂ V`
(`TauCeti.ArtinRep.toContinuousRep`, `TauCeti.ArtinRep.ofContinuousRep`). The character of an
Artin representation is the continuous character `ContRepresentation.character` of the underlying
continuous representation, so the class-function identities `ContRepresentation.character_one`,
`ContRepresentation.character_mul_comm` and `ContRepresentation.character_conj` apply to it
directly; it is moreover constant on the cosets of the kernel.
Isomorphisms of Artin representations are Mathlib's `Representation.Equiv` of the underlying
representations; in finite dimension their linear equivalences are automatically continuous
(`ContRepresentation.equivOfEquiv`), and they preserve characters
(`TauCeti.ArtinRep.character_eq_of_equiv`).

## Main definitions

* `TauCeti.ArtinRep F V`: Artin representations of `F` on `V`.
* `TauCeti.ArtinRep.ker`, `TauCeti.ArtinRep.range`: the kernel, a subgroup of `G_F`, and the image,
  a subgroup of `(V →L[ℂ] V)ˣ`.
* `TauCeti.ArtinRep.quotientKerEquivRange`: the first isomorphism theorem `G_F ⧸ ρ.ker ≃* ρ.range`.
* `TauCeti.ArtinRep.trivial`, `TauCeti.ArtinRep.ofLinearCharacter`: the trivial representation and
  the one-dimensional representation of a continuous linear character `G_F →ₜ* ℂˣ`.
* `TauCeti.ArtinRep.toContinuousRep`, `TauCeti.ArtinRep.ofContinuousRep`: the comparison with
  jointly continuous representations.
* `TauCeti.ArtinRep.character`: the character of an Artin representation, a continuous function
  on `G_F`.

## Main results

* `TauCeti.ArtinRep.isOpen_ker`: the kernel of an Artin representation is open, hence closed
  (`TauCeti.ArtinRep.isClosed_ker`) and of finite index.
* `TauCeti.ArtinRep.finite_range`: an Artin representation has finitely many distinct operators.
* `TauCeti.ArtinRep.character_mul_of_mem_ker`: the character is constant on the cosets of the
  kernel.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter VII, §10.
* J.-P. Serre, *Linear Representations of Finite Groups*, §2.1.
* H. Darmon, F. Diamond and R. Taylor, *Fermat's Last Theorem*, §2.1, p. 53.
-/

public section

noncomputable section

namespace TauCeti

/-- An **Artin representation** of the field `F` on the finite-dimensional complex normed space
`V`: a representation of the absolute Galois group `Field.absoluteGaloisGroup F` by continuous
linear operators on `V`, continuous for the Krull topology on the Galois group and the
operator-norm topology on `V →L[ℂ] V`. Continuity forces the kernel to be open
(`TauCeti.ArtinRep.isOpen_ker`), so the representation factors through the Galois group of a finite
Galois extension of `F`. -/
structure ArtinRep (F : Type*) [Field F] (V : Type*) [NormedAddCommGroup V] [NormedSpace ℂ V]
    [FiniteDimensional ℂ V] extends ContRepresentation ℂ (Field.absoluteGaloisGroup F) V where
  /-- The action `g ↦ ρ g` is continuous for the Krull topology and the operator-norm topology. -/
  continuous_toFun : Continuous (toMonoidHom : Field.absoluteGaloisGroup F → V →L[ℂ] V)

namespace ArtinRep

variable {F : Type*} [Field F] {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
  [FiniteDimensional ℂ V]

instance : FunLike (ArtinRep F V) (Field.absoluteGaloisGroup F) (V →L[ℂ] V) where
  coe ρ := ρ.toMonoidHom
  coe_injective ρ σ h := by
    obtain ⟨⟨ρ⟩, _⟩ := ρ
    obtain ⟨⟨σ⟩, _⟩ := σ
    congr
    exact DFunLike.coe_injective h

instance : MonoidHomClass (ArtinRep F V) (Field.absoluteGaloisGroup F) (V →L[ℂ] V) where
  map_one ρ := ρ.toMonoidHom.map_one
  map_mul ρ := ρ.toMonoidHom.map_mul

@[simp]
theorem coe_toContRepresentation (ρ : ArtinRep F V) : ⇑ρ.toContRepresentation = ρ :=
  (rfl)

@[simp]
theorem coe_toMonoidHom (ρ : ArtinRep F V) : ⇑ρ.toMonoidHom = ρ :=
  (rfl)

/-- Two Artin representations with the same operators are equal. -/
@[ext]
theorem ext {ρ σ : ArtinRep F V} (h : ∀ g, ρ g = σ g) : ρ = σ :=
  DFunLike.ext _ _ h

/-- An Artin representation is determined by its underlying `ContRepresentation`. -/
theorem toContRepresentation_injective :
    Function.Injective (toContRepresentation : ArtinRep F V → _) :=
  fun ρ σ h ↦ ext fun g ↦ by rw [← coe_toContRepresentation, h, coe_toContRepresentation]

/-- The action of an Artin representation is continuous. -/
@[fun_prop]
theorem continuous (ρ : ArtinRep F V) : Continuous ρ :=
  ρ.continuous_toFun

/-- The underlying linear representation of an Artin representation. -/
abbrev toRepresentation (ρ : ArtinRep F V) : Representation ℂ (Field.absoluteGaloisGroup F) V :=
  ρ.toContRepresentation.toRepresentation

theorem toRepresentation_apply (ρ : ArtinRep F V) (g : Field.absoluteGaloisGroup F) (v : V) :
    ρ.toRepresentation g v = ρ g v :=
  (rfl)

/-- An Artin representation is determined by its underlying linear representation. -/
theorem toRepresentation_injective :
    Function.Injective (toRepresentation : ArtinRep F V → _) :=
  fun ρ σ h ↦ ext fun g ↦ ContinuousLinearMap.ext fun v ↦ by
    rw [← toRepresentation_apply, h, toRepresentation_apply]

/-! ### The kernel and the image -/

/-- The kernel of an Artin representation: the elements of the absolute Galois group acting as the
identity. It is an open normal subgroup (`TauCeti.ArtinRep.isOpen_ker`). -/
def ker (ρ : ArtinRep F V) : Subgroup (Field.absoluteGaloisGroup F) :=
  ρ.toMonoidHom.ker

@[simp]
theorem mem_ker {ρ : ArtinRep F V} {g : Field.absoluteGaloisGroup F} : g ∈ ρ.ker ↔ ρ g = 1 :=
  MonoidHom.mem_ker

/-- The kernel of an Artin representation is a normal subgroup. -/
instance normal_ker (ρ : ArtinRep F V) : ρ.ker.Normal :=
  MonoidHom.normal_ker _

/-- The kernel of the underlying linear representation is the kernel of the Artin
representation. -/
theorem ker_toRepresentation (ρ : ArtinRep F V) : ρ.toRepresentation.ker = ρ.ker := by
  ext g
  simp only [MonoidHom.mem_ker, mem_ker, LinearMap.ext_iff, ContinuousLinearMap.ext_iff,
    toRepresentation_apply, one_apply_eq_self]

/-- **The kernel of an Artin representation is open.** The absolute Galois group is profinite and
the invertible operators on `V` have no small subgroups. -/
theorem isOpen_ker (ρ : ArtinRep F V) : IsOpen (ρ.ker : Set (Field.absoluteGaloisGroup F)) :=
  (ContRepresentation.continuous_iff_isOpen_ker ρ.toContRepresentation).mp ρ.continuous

/-- The kernel of an Artin representation is closed, being an open subgroup. -/
theorem isClosed_ker (ρ : ArtinRep F V) : IsClosed (ρ.ker : Set (Field.absoluteGaloisGroup F)) :=
  Subgroup.isClosed_of_isOpen _ ρ.isOpen_ker

/-- An Artin representation factors through a finite quotient of the absolute Galois group: the
kernel is open in a compact group. -/
instance finite_quotient_ker (ρ : ArtinRep F V) : Finite (Field.absoluteGaloisGroup F ⧸ ρ.ker) :=
  Subgroup.quotient_finite_of_isOpen _ ρ.isOpen_ker

/-- The kernel of an Artin representation has finite index. -/
instance finiteIndex_ker (ρ : ArtinRep F V) : ρ.ker.FiniteIndex :=
  Subgroup.finiteIndex_of_finite_quotient

/-- The image of an Artin representation, as a subgroup of the invertible operators on `V`. It is
finite, of order the index of the kernel (`TauCeti.ArtinRep.quotientKerEquivRange`). -/
def range (ρ : ArtinRep F V) : Subgroup (V →L[ℂ] V)ˣ :=
  ρ.toMonoidHom.toHomUnits.range

@[simp]
theorem mem_range {ρ : ArtinRep F V} {u : (V →L[ℂ] V)ˣ} :
    u ∈ ρ.range ↔ ∃ g, ρ g = u := by
  simp only [range, MonoidHom.mem_range, Units.ext_iff, MonoidHom.coe_toHomUnits,
    coe_toMonoidHom]

/-- **The first isomorphism theorem for an Artin representation**: the quotient of the absolute
Galois group by the kernel is isomorphic to the image. -/
def quotientKerEquivRange (ρ : ArtinRep F V) :
    Field.absoluteGaloisGroup F ⧸ ρ.ker ≃* ρ.range :=
  (QuotientGroup.quotientMulEquivOfEq (MonoidHom.ker_toHomUnits ρ.toMonoidHom).symm).trans
    (QuotientGroup.quotientKerEquivRange ρ.toMonoidHom.toHomUnits)

@[simp]
theorem coe_quotientKerEquivRange_mk (ρ : ArtinRep F V) (g : Field.absoluteGaloisGroup F) :
    ((ρ.quotientKerEquivRange g : (V →L[ℂ] V)ˣ) : V →L[ℂ] V) = ρ g :=
  -- Definitional: `quotientMulEquivOfEq` sends the class of `g` to the class of `g`, the first
  -- isomorphism theorem sends that class to `ρ.toMonoidHom.toHomUnits g` (Mathlib has no
  -- evaluation lemma for `QuotientGroup.rangeKerLift`), and the underlying operator of
  -- `toHomUnits` is `ρ g` (`MonoidHom.coe_toHomUnits`, itself `rfl`).
  (rfl)

/-- **The image of an Artin representation is finite.** -/
instance finite_range (ρ : ArtinRep F V) : Finite ρ.range :=
  .of_equiv _ ρ.quotientKerEquivRange.toEquiv

/-- An Artin representation has only finitely many distinct operators. -/
theorem finite_set_range (ρ : ArtinRep F V) : (Set.range ρ).Finite := by
  refine (Set.finite_range fun u : ρ.range ↦ ((u : (V →L[ℂ] V)ˣ) : V →L[ℂ] V)).subset ?_
  rintro _ ⟨g, rfl⟩
  exact ⟨ρ.quotientKerEquivRange g, coe_quotientKerEquivRange_mk ρ g⟩

/-- The order of the image of an Artin representation is the index of its kernel. -/
theorem natCard_range (ρ : ArtinRep F V) : Nat.card ρ.range = ρ.ker.index := by
  rw [Subgroup.index, Nat.card_congr ρ.quotientKerEquivRange.toEquiv]

/-- On a zero space every element of the absolute Galois group acts trivially. -/
theorem ker_eq_top_of_subsingleton [Subsingleton V] (ρ : ArtinRep F V) : ρ.ker = ⊤ :=
  eq_top_iff.mpr fun _ _ ↦ mem_ker.mpr (Subsingleton.elim _ _)

/-! ### Comparison with jointly continuous representations -/

/-- An Artin representation as a jointly continuous representation: the action map
`G_F × V → V` is continuous because evaluation `(V →L[ℂ] V) × V → V` is. -/
def toContinuousRep (ρ : ArtinRep F V) : ContinuousRep (Field.absoluteGaloisGroup F) ℂ V :=
  .ofContRepresentation ρ.toContRepresentation <|
    (ρ.continuous.comp continuous_fst).clm_apply continuous_snd

@[simp]
theorem toContinuousRep_apply (ρ : ArtinRep F V) (g : Field.absoluteGaloisGroup F) (v : V) :
    ρ.toContinuousRep g v = ρ g v :=
  ContinuousRep.ofContRepresentation_apply _ _ g v

/-- A jointly continuous representation of the absolute Galois group on a finite-dimensional
complex normed space is an Artin representation: in finite dimension, continuity of the orbit maps
`g ↦ σ g v` is continuity of `g ↦ σ g` for the operator norm. -/
def ofContinuousRep (σ : ContinuousRep (Field.absoluteGaloisGroup F) ℂ V) : ArtinRep F V where
  toContRepresentation := σ.toContRepresentation
  continuous_toFun := continuous_clm_apply.mpr fun v ↦ by
    simpa only [ContRepresentation.toMonoidHom_apply, ContinuousRep.toContRepresentation_apply]
      using σ.continuous_orbit v

@[simp]
theorem ofContinuousRep_apply (σ : ContinuousRep (Field.absoluteGaloisGroup F) ℂ V)
    (g : Field.absoluteGaloisGroup F) (v : V) : ofContinuousRep σ g v = σ g v :=
  σ.toContRepresentation_apply g v

@[simp]
theorem toContRepresentation_ofContinuousRep
    (σ : ContinuousRep (Field.absoluteGaloisGroup F) ℂ V) :
    (ofContinuousRep σ).toContRepresentation = σ.toContRepresentation :=
  (rfl)

@[simp]
theorem toRepresentation_ofContinuousRep (σ : ContinuousRep (Field.absoluteGaloisGroup F) ℂ V) :
    (ofContinuousRep σ).toRepresentation = σ.toRepresentation :=
  σ.toRepresentation_toContRepresentation

@[simp]
theorem toContRepresentation_toContinuousRep (ρ : ArtinRep F V) :
    ρ.toContinuousRep.toContRepresentation = ρ.toContRepresentation :=
  ContinuousRep.toContRepresentation_ofContRepresentation _ _

@[simp]
theorem toRepresentation_toContinuousRep (ρ : ArtinRep F V) :
    ρ.toContinuousRep.toRepresentation = ρ.toRepresentation :=
  ContinuousRep.toRepresentation_ofContRepresentation _ _

@[simp]
theorem ofContinuousRep_toContinuousRep (ρ : ArtinRep F V) :
    ofContinuousRep ρ.toContinuousRep = ρ :=
  ext fun _ ↦ ContinuousLinearMap.ext fun _ ↦ by simp

@[simp]
theorem toContinuousRep_ofContinuousRep (σ : ContinuousRep (Field.absoluteGaloisGroup F) ℂ V) :
    (ofContinuousRep σ).toContinuousRep = σ :=
  ContinuousRep.ext fun _ _ ↦ by simp

/-! ### Constructions -/

/-- The trivial Artin representation of `F` on `V`, in which every element acts as the
identity. -/
def trivial (F V : Type*) [Field F] [NormedAddCommGroup V] [NormedSpace ℂ V]
    [FiniteDimensional ℂ V] : ArtinRep F V :=
  ofContinuousRep (ContinuousRep.trivial _ ℂ V)

@[simp]
theorem trivial_apply (g : Field.absoluteGaloisGroup F) : trivial F V g = 1 :=
  ContinuousLinearMap.ext fun v ↦
    (ofContinuousRep_apply _ g v).trans (ContinuousRep.trivial_apply g v)

@[simp]
theorem ker_trivial : (trivial F V).ker = ⊤ :=
  eq_top_iff.mpr fun _ _ ↦ mem_ker.mpr (trivial_apply _)

@[simp]
theorem range_trivial : (trivial F V).range = ⊥ :=
  eq_bot_iff.mpr fun _ hu ↦ by
    obtain ⟨g, hg⟩ := mem_range.mp hu
    exact Subgroup.mem_bot.mpr (Units.ext (by rw [← hg, trivial_apply, Units.val_one]))

/-- The trivial Artin representation is the trivial jointly continuous representation. -/
@[simp]
theorem toContinuousRep_trivial :
    (trivial F V).toContinuousRep = ContinuousRep.trivial _ ℂ V :=
  toContinuousRep_ofContinuousRep _

/-- The underlying linear representation of the trivial Artin representation is Mathlib's trivial
representation. -/
@[simp]
theorem toRepresentation_trivial :
    (trivial F V).toRepresentation = Representation.trivial ℂ (Field.absoluteGaloisGroup F) V :=
  (toRepresentation_ofContinuousRep _).trans ContinuousRep.toRepresentation_trivial

/-- The one-dimensional Artin representation of a continuous linear character
`χ : G_F →ₜ* ℂˣ`, in which `g` acts on `ℂ` as multiplication by `χ g`. -/
def ofLinearCharacter (χ : Field.absoluteGaloisGroup F →ₜ* ℂˣ) : ArtinRep F ℂ :=
  ofContinuousRep (ContinuousRep.ofCharacter χ)

@[simp]
theorem ofLinearCharacter_apply (χ : Field.absoluteGaloisGroup F →ₜ* ℂˣ)
    (g : Field.absoluteGaloisGroup F) (z : ℂ) : ofLinearCharacter χ g z = χ g * z :=
  (ofContinuousRep_apply _ g z).trans (ContinuousRep.ofCharacter_apply χ g z)

@[simp]
theorem toRepresentation_ofLinearCharacter (χ : Field.absoluteGaloisGroup F →ₜ* ℂˣ) :
    (ofLinearCharacter χ).toRepresentation =
      Representation.ofLinearCharacter (χ : Field.absoluteGaloisGroup F →* ℂˣ) :=
  (toRepresentation_ofContinuousRep _).trans (ContinuousRep.toRepresentation_ofCharacter χ)

@[simp]
theorem ker_ofLinearCharacter (χ : Field.absoluteGaloisGroup F →ₜ* ℂˣ) :
    (ofLinearCharacter χ).ker = χ.ker := by
  rw [← ker_toRepresentation, toRepresentation_ofLinearCharacter,
    Representation.ker_ofLinearCharacter]
  ext g
  simp

/-! ### The character -/

/-- The character of an Artin representation: the continuous function `g ↦ trace (ρ g)` on the
absolute Galois group, which is `ContRepresentation.character` of the underlying continuous
representation. The lemmas `ContRepresentation.character_one`,
`ContRepresentation.character_mul_comm` and `ContRepresentation.character_conj` apply to it
directly. -/
abbrev character (ρ : ArtinRep F V) : C(Field.absoluteGaloisGroup F, ℂ) :=
  ρ.toContRepresentation.character ρ.continuous

theorem character_apply (ρ : ArtinRep F V) (g : Field.absoluteGaloisGroup F) :
    ρ.character g = LinearMap.trace ℂ V (ρ g : V →ₗ[ℂ] V) :=
  ContRepresentation.character_apply _ _ g

/-- The character of an Artin representation is constant on the cosets of its kernel. -/
theorem character_mul_of_mem_ker (ρ : ArtinRep F V) (g : Field.absoluteGaloisGroup F)
    {k : Field.absoluteGaloisGroup F} (hk : k ∈ ρ.ker) : ρ.character (g * k) = ρ.character g := by
  rw [character_apply, character_apply, map_mul, mem_ker.mp hk, mul_one]

/-- The character of an Artin representation on a zero space vanishes. -/
theorem character_eq_zero_of_subsingleton [Subsingleton V] (ρ : ArtinRep F V) :
    ρ.character = 0 := by
  ext g
  simp [Subsingleton.elim (ρ g : V →ₗ[ℂ] V) 0]

/-- The character of the trivial Artin representation is the constant function at the dimension
of `V`. -/
@[simp]
theorem character_trivial :
    (trivial F V).character = ContinuousMap.const _ (Module.finrank ℂ V : ℂ) := by
  ext g
  simp

/-- The character of the one-dimensional Artin representation of a linear character `χ` is `χ`.
This is not a `simp` lemma: `simp` already unfolds the character to a trace with
`ContRepresentation.character_apply`. -/
theorem character_ofLinearCharacter (χ : Field.absoluteGaloisGroup F →ₜ* ℂˣ)
    (g : Field.absoluteGaloisGroup F) : (ofLinearCharacter χ).character g = χ g := by
  simp only [ContRepresentation.coe_character, toRepresentation_ofLinearCharacter,
    Representation.char_ofLinearCharacter, MonoidHom.coe_ofClass]

/-- Isomorphic Artin representations have the same character. The underlying continuous
equivalence is `ContRepresentation.equivOfEquiv`. -/
theorem character_eq_of_equiv {W : Type*} [NormedAddCommGroup W] [NormedSpace ℂ W]
    [FiniteDimensional ℂ W] {ρ : ArtinRep F V} {σ : ArtinRep F W}
    (e : ρ.toRepresentation.Equiv σ.toRepresentation) : ρ.character = σ.character :=
  ContinuousMap.coe_injective <| by
    simpa only [ContRepresentation.coe_character] using Representation.char_iso e

end ArtinRep

end TauCeti

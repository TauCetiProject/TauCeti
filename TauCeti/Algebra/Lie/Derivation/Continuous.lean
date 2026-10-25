/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Derivation.Basic
public import TauCeti.Topology.Algebra.Lie.Quotient
public import Mathlib.Topology.Algebra.Ring.Basic

/-!
# Continuous derivations and their outer quotient

Continuous derivations of a possibly non-associative algebra form a Lie subalgebra of
`TauCeti.derivationLieAlgebra`. We equip it with the topology of pointwise convergence,
not a topology of uniform convergence on bounded sets. Inner derivations form a Lie ideal:
`[D, ad b] = ad (D b)`. The quotient by this actual image is the continuous outer-derivation
Lie algebra. No closure is taken, so the quotient topology need not be Hausdorff.

This quotient records precisely the ambiguity in a derivation that changes a module
self-extension by the comparison `(u, v) ↦ (u + b • v, v)`. In particular, equality in the
quotient provides an actual element `b`, rather than a limit of inner derivations.

The continuous subalgebra construction also applies to non-associative algebras; only the
inner derivations and their quotient require associativity. We prove continuity of evaluation,
of the inner-derivation map, and of the quotient projection, and give the continuous descent
property for Lie homomorphisms killing inner derivations. No continuity of the Lie bracket
in the pointwise topology is asserted.

## References

* N. Jacobson, *Lie Algebras* (1962), Chapter I, §2, for derivations and inner derivations.
-/

public section

namespace TauCeti

attribute [local instance 100] LieRing.ofAssociativeRing

universe u v w

section Continuous

variable (R : Type u) (A : Type v) [CommRing R] [NonUnitalNonAssocRing A] [Module R A]
  [SMulCommClass R A A] [IsScalarTower R A A] [TopologicalSpace A]
  [IsTopologicalAddGroup A] [ContinuousConstSMul R A]

/-- The Lie subalgebra of continuous derivations, with the Leibniz rule
`D (x * y) = D x * y + x * D y`. -/
def continuousDerivationLieAlgebra : LieSubalgebra R (derivationLieAlgebra R A) where
  carrier := {D | Continuous (D : Module.End R A)}
  zero_mem' := continuous_const
  add_mem' := fun hD hE => hD.add hE
  smul_mem' := fun r _ hD => hD.const_smul r
  lie_mem' := fun hD hE => (hD.comp hE).sub (hE.comp hD)

variable {R A}

@[simp]
theorem mem_continuousDerivationLieAlgebra (D : derivationLieAlgebra R A) :
    D ∈ continuousDerivationLieAlgebra R A ↔ Continuous (D : Module.End R A) :=
  Iff.rfl

namespace continuousDerivationLieAlgebra

/-- Continuous derivations are determined by their values. -/
@[ext]
theorem ext {D E : continuousDerivationLieAlgebra R A}
    (h : ∀ a, (D.1 : Module.End R A) a = (E.1 : Module.End R A) a) : D = E :=
  Subtype.ext (derivationLieAlgebra.ext h)

/-- Each member of the continuous derivation Lie algebra is continuous on the algebra. -/
theorem continuous (D : continuousDerivationLieAlgebra R A) :
    Continuous (D.1 : Module.End R A) :=
  D.2

/-- The topology of pointwise convergence on continuous derivations. -/
instance : TopologicalSpace (continuousDerivationLieAlgebra R A) :=
  TopologicalSpace.induced (fun D => (D.1 : Module.End R A) :
    continuousDerivationLieAlgebra R A → A → A) inferInstance

/-- A family of continuous derivations is continuous exactly when every evaluation is. -/
theorem continuous_iff {X : Type*} [TopologicalSpace X]
    (f : X → continuousDerivationLieAlgebra R A) :
    Continuous f ↔ ∀ a, Continuous fun x => ((f x).1 : Module.End R A) a :=
  continuous_induced_rng.trans continuous_pi_iff

/-- Evaluation at a fixed element is continuous in the pointwise topology. -/
@[fun_prop]
theorem continuous_apply (a : A) :
    Continuous fun D : continuousDerivationLieAlgebra R A => (D.1 : Module.End R A) a :=
  (continuous_iff id).1 continuous_id a

instance : IsTopologicalAddGroup (continuousDerivationLieAlgebra R A) where
  continuous_add := (continuous_iff _).2 fun a =>
    ((continuous_apply a).comp continuous_fst).add ((continuous_apply a).comp continuous_snd)
  continuous_neg := (continuous_iff _).2 fun a => (continuous_apply a).neg

instance : ContinuousConstSMul R (continuousDerivationLieAlgebra R A) where
  continuous_const_smul r := (continuous_iff _).2 fun a => (continuous_apply a).const_smul r

end continuousDerivationLieAlgebra

end Continuous

section Inner

variable (R : Type u) (A : Type v) [CommRing R] [Ring A] [Algebra R A]
  [TopologicalSpace A] [IsTopologicalAddGroup A] [SeparatelyContinuousMul A]
  [ContinuousConstSMul R A]

/-- Inner derivations of a topological algebra, valued in its continuous derivations. -/
def continuousInnerDerivation : A →ₗ⁅R⁆ continuousDerivationLieAlgebra R A :=
  { (innerDerivation R).toLinearMap.codRestrict (continuousDerivationLieAlgebra R A).toSubmodule
      (fun b => (mem_continuousDerivationLieAlgebra (innerDerivation R b)).2 (by
        exact (continuous_congr (innerDerivation_apply R b)).2 (by fun_prop))) with
    map_lie' := fun {a b} => Subtype.ext ((innerDerivation R).map_lie a b) }

variable {A}

@[simp]
theorem coe_continuousInnerDerivation (b : A) :
    (continuousInnerDerivation R A b).1 = innerDerivation R b :=
  (rfl)

/-- The inner-derivation map is continuous for pointwise convergence. -/
@[fun_prop]
theorem continuous_continuousInnerDerivation : Continuous (continuousInnerDerivation R A) :=
  (continuousDerivationLieAlgebra.continuous_iff _).2 fun a => by
    simp only [coe_continuousInnerDerivation, innerDerivation_apply]
    fun_prop

/-- Commuting a derivation with an inner derivation gives an actual inner derivation. -/
theorem lie_continuousInnerDerivation (D : continuousDerivationLieAlgebra R A) (b : A) :
    ⁅D, continuousInnerDerivation R A b⁆ =
      continuousInnerDerivation R A ((D.1 : Module.End R A) b) := by
  apply continuousDerivationLieAlgebra.ext
  intro a
  simp only [LieSubalgebra.coe_bracket, coe_continuousInnerDerivation,
    Ring.lie_def, LinearMap.sub_apply, Module.End.mul_apply,
    innerDerivation_apply, map_sub, derivationLieAlgebra.leibniz]
  abel

/-- The image of the inner-derivation map is a Lie ideal, without taking its closure. -/
theorem continuousInnerDerivation_isIdealMorphism :
    (continuousInnerDerivation R A).IsIdealMorphism :=
  (continuousInnerDerivation R A).isIdealMorphism_iff.2 fun D b =>
    ⟨(D.1 : Module.End R A) b, lie_continuousInnerDerivation R D b⟩

variable (A)

/-- The Lie ideal of actual continuous inner derivations. -/
def continuousInnerDerivations : LieIdeal R (continuousDerivationLieAlgebra R A) :=
  (continuousInnerDerivation R A).idealRange

variable {R A}

/-- Membership gives an actual implementing element of the algebra, not a limiting one. -/
@[simp]
theorem mem_continuousInnerDerivations (D : continuousDerivationLieAlgebra R A) :
    D ∈ continuousInnerDerivations R A ↔ ∃ b, continuousInnerDerivation R A b = D :=
  (continuousInnerDerivation R A).mem_idealRange_iff
    (continuousInnerDerivation_isIdealMorphism R)

variable (R A)

/-- Continuous outer derivations, modulo the actual inner image, with the quotient topology.
This quotient need not be separated. -/
abbrev ContinuousOuterDerivation :=
  continuousDerivationLieAlgebra R A ⧸ continuousInnerDerivations R A

/-- The canonical Lie homomorphism to continuous outer derivations. -/
def continuousOuterDerivationMk :
    continuousDerivationLieAlgebra R A →ₗ⁅R⁆ ContinuousOuterDerivation R A :=
  (continuousInnerDerivations R A).mkQ

variable {R A}

/-- The outer projection is the quotient map for the actual inner ideal. -/
theorem continuousOuterDerivationMk_def :
    continuousOuterDerivationMk R A = (continuousInnerDerivations R A).mkQ :=
  (rfl)

/-- Every outer derivation class has a continuous derivation representative. -/
theorem continuousOuterDerivationMk_surjective :
    Function.Surjective (continuousOuterDerivationMk R A) :=
  (continuousInnerDerivations R A).surjective_mkQ

/-- The kernel of the outer projection is exactly the actual inner ideal. -/
@[simp]
theorem ker_continuousOuterDerivationMk :
    (continuousOuterDerivationMk R A).ker = continuousInnerDerivations R A :=
  (continuousInnerDerivations R A).mkQ_ker

/-- The topology on outer derivations is the quotient of pointwise convergence. -/
theorem isQuotientMap_continuousOuterDerivationMk :
    Topology.IsQuotientMap (continuousOuterDerivationMk R A) :=
  Submodule.isQuotientMap_mkQ _

/-- Projection to outer derivations is continuous. -/
@[fun_prop]
theorem continuous_continuousOuterDerivationMk :
    Continuous (continuousOuterDerivationMk R A) :=
  isQuotientMap_continuousOuterDerivationMk.continuous

/-- An outer class vanishes exactly when it is implemented by an actual inner derivation. -/
@[simp]
theorem continuousOuterDerivationMk_eq_zero (D : continuousDerivationLieAlgebra R A) :
    continuousOuterDerivationMk R A D = 0 ↔ ∃ b, continuousInnerDerivation R A b = D := by
  rw [continuousOuterDerivationMk, LieIdeal.mkQ_eq_zero, mem_continuousInnerDerivations]

/-- Equality of outer classes is equivalent to changing representatives by `ad b`. -/
theorem continuousOuterDerivationMk_eq_iff (D E : continuousDerivationLieAlgebra R A) :
    continuousOuterDerivationMk R A D = continuousOuterDerivationMk R A E ↔
      ∃ b, D = E + continuousInnerDerivation R A b := by
  rw [← sub_eq_zero, ← map_sub, continuousOuterDerivationMk_eq_zero]
  exact exists_congr fun b => by rw [eq_sub_iff_add_eq, add_comm, eq_comm]

section Descent

variable {L : Type w} [LieRing L] [LieAlgebra R L]

/-- Lie homomorphisms from outer derivations are determined by their pullbacks. -/
@[ext]
theorem continuousOuterDerivation_hom_ext
    {g h : ContinuousOuterDerivation R A →ₗ⁅R⁆ L}
    (H : g.comp (continuousOuterDerivationMk R A) =
      h.comp (continuousOuterDerivationMk R A)) : g = h :=
  (continuousInnerDerivations R A).lieHom_qext (LieHom.congr_fun H)

/-- Killing the actual inner derivations is precisely the hypothesis for `LieIdeal.liftQ`.
Its uniqueness and pullback equation are `LieIdeal.eq_liftQ` and `LieIdeal.liftQ_mkQ`;
`TauCeti.continuous_lieIdeal_liftQ` supplies continuous descent. -/
theorem continuousInnerDerivations_le_ker_iff
    (f : continuousDerivationLieAlgebra R A →ₗ⁅R⁆ L) :
    continuousInnerDerivations R A ≤ f.ker ↔
      ∀ b, f (continuousInnerDerivation R A b) = 0 := by
  constructor
  · intro h b
    exact h ((mem_continuousInnerDerivations _).2 ⟨b, rfl⟩)
  · intro h D hD
    obtain ⟨b, rfl⟩ := (mem_continuousInnerDerivations D).1 hD
    exact h b

end Descent

end Inner

end TauCeti

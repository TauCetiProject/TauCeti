/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Derivation.Center
public import TauCeti.Topology.Algebra.Lie.Quotient

/-!
# Continuous derivations and continuous outer derivations

For an algebra `A` with a topology, the continuous derivations form a Lie subalgebra
`Der_cont(A)` of the derivation Lie algebra `Der(A)`. We give it the topology of pointwise
convergence, induced from the product topology on `A → A`. For an associative topological algebra
every inner derivation `ad z = ⁅z, -⁆` is continuous, and the bracket identity
`⁅D, ad z⁆ = ad (D z)` shows that the image of `z ↦ ad z` is a Lie ideal of `Der_cont(A)`. The
quotient by that image is the Lie algebra of **continuous outer derivations**

`OutDer_cont(A) = Der_cont(A) ⧸ ad(A)`,

with the quotient topology, for which the class map is an open quotient map
(`LieIdeal.isOpenQuotientMap_mkQ`).

Two continuous derivations have the same class in `OutDer_cont(A)` exactly when they differ by an
inner derivation `ad b` with `b ∈ A`. This is the form in which the class of a derivation is used:
changing `δ` to `δ + ad b` changes the self-extension `E_δ(M)` of `TauCeti.DerivationExtension` only
up to the isomorphism `TauCeti.DerivationExtension.innerEquiv` built from the actual element `b`.
For that reason the ideal is the image of `ad` itself, not its closure, and `OutDer_cont(A)` need
not be Hausdorff.

## Main definitions

* `TauCeti.continuousDerivationLieAlgebra R A`: the continuous derivations, as a Lie subalgebra of
  `TauCeti.derivationLieAlgebra R A`, with the topology of pointwise convergence.
* `TauCeti.continuousInnerDerivation`: `z ↦ ad z`, as a continuous homomorphism of Lie algebras
  from `A` to the continuous derivations.
* `TauCeti.ContinuousOuterDerivation R A`: the quotient of the continuous derivations by the
  inner derivations, with its quotient topology.

## Main results

* `TauCeti.continuousDerivationLieAlgebra.continuous_iff`: a map into the continuous derivations is
  continuous exactly when each evaluation `D ↦ D a` of it is.
* `TauCeti.continuousInnerDerivation_isIdealMorphism`: the inner derivations form a Lie ideal of
  the continuous derivations, with no closure taken.
* `TauCeti.ContinuousOuterDerivation.mkQ_eq_mkQ_iff`: two continuous derivations have the same
  outer class exactly when they differ by an inner derivation `ad b`.

## References

* E. Frenkel, *Langlands Correspondence for Loop Groups*, Cambridge University Press (2007),
  for outer derivations of the completed enveloping algebra at the critical level.
-/

public section

namespace TauCeti

attribute [local instance 100] LieRing.ofAssociativeRing

universe u v

open Topology

/-- Multiplying a continuous derivation by a central element preserves continuity. -/
theorem derivationLieAlgebra.continuous_center_smul {R A : Type*} [CommRing R] [Ring A]
    [Algebra R A] [TopologicalSpace A] [SeparatelyContinuousMul A]
    (z : Subalgebra.center R A) {D : derivationLieAlgebra R A}
    (hD : Continuous (D : Module.End R A)) :
    Continuous ((z • D : derivationLieAlgebra R A) : Module.End R A) :=
  (continuous_const_mul (z : A)).comp hD

section ContinuousDerivations

variable (R : Type u) (A : Type v) [CommRing R] [NonUnitalNonAssocRing A] [Module R A]
  [SMulCommClass R A A] [IsScalarTower R A A] [TopologicalSpace A] [IsTopologicalAddGroup A]
  [ContinuousConstSMul R A]

/-- **The continuous derivations** of a topological algebra `A`: the derivations whose underlying
map `A → A` is continuous, as a Lie subalgebra of `TauCeti.derivationLieAlgebra R A`. -/
def continuousDerivationLieAlgebra : LieSubalgebra R (derivationLieAlgebra R A) where
  carrier := {D | Continuous (D : Module.End R A)}
  zero_mem' := continuous_zero
  add_mem' hD hE := hD.add hE
  smul_mem' r _ hD := hD.const_smul r
  lie_mem' := by
    intro D E hD hE
    -- The nested Lie-subalgebra coercions hide that this bracket is the commutator of
    -- endomorphisms.
    change Continuous fun a => (D : Module.End R A) ((E : Module.End R A) a) -
      (E : Module.End R A) ((D : Module.End R A) a)
    exact (hD.comp hE).sub (hE.comp hD)

variable {R A}

@[simp]
theorem mem_continuousDerivationLieAlgebra {D : derivationLieAlgebra R A} :
    D ∈ continuousDerivationLieAlgebra R A ↔ Continuous (D : Module.End R A) :=
  Iff.rfl

namespace continuousDerivationLieAlgebra

/-- The underlying map of a continuous derivation is continuous. -/
theorem continuous (D : continuousDerivationLieAlgebra R A) :
    Continuous ((D : derivationLieAlgebra R A) : Module.End R A) :=
  D.2

/-- A continuous derivation is determined by its values. -/
@[ext]
theorem ext {D E : continuousDerivationLieAlgebra R A}
    (h : ∀ a : A, ((D : derivationLieAlgebra R A) : Module.End R A) a =
      ((E : derivationLieAlgebra R A) : Module.End R A) a) : D = E :=
  Subtype.ext (derivationLieAlgebra.ext h)

/-- **The topology of pointwise convergence** on the continuous derivations: the topology induced
by the underlying maps from the product topology on `A → A`. -/
instance : TopologicalSpace (continuousDerivationLieAlgebra R A) :=
  .induced (fun D => ⇑((D : derivationLieAlgebra R A) : Module.End R A)) inferInstance

/-- The topology on the continuous derivations is induced by their underlying maps `A → A`. -/
theorem isInducing_coeFn :
    IsInducing fun D : continuousDerivationLieAlgebra R A =>
      ⇑((D : derivationLieAlgebra R A) : Module.End R A) :=
  ⟨rfl⟩

/-- **The universal property of pointwise convergence**: a map into the continuous derivations is
continuous exactly when each of its evaluations is. -/
theorem continuous_iff {X : Type*} [TopologicalSpace X]
    {f : X → continuousDerivationLieAlgebra R A} :
    Continuous f ↔
      ∀ a : A, Continuous fun x => ((f x : derivationLieAlgebra R A) : Module.End R A) a := by
  rw [isInducing_coeFn.continuous_iff, continuous_pi_iff]
  rfl

/-- Evaluation at a point is continuous on the continuous derivations. -/
@[fun_prop]
theorem continuous_apply (a : A) :
    Continuous fun D : continuousDerivationLieAlgebra R A =>
      ((D : derivationLieAlgebra R A) : Module.End R A) a :=
  continuous_iff.mp continuous_id a

/-- The underlying maps, as an additive homomorphism `Der_cont(A) →+ (A → A)`. -/
private def coeFnAddMonoidHom : continuousDerivationLieAlgebra R A →+ (A → A) where
  toFun D := ⇑((D : derivationLieAlgebra R A) : Module.End R A)
  map_zero' := rfl
  map_add' _ _ := rfl

instance : IsTopologicalAddGroup (continuousDerivationLieAlgebra R A) :=
  isInducing_coeFn.isTopologicalAddGroup coeFnAddMonoidHom

instance : ContinuousConstSMul R (continuousDerivationLieAlgebra R A) :=
  isInducing_coeFn.continuousConstSMul id rfl

end continuousDerivationLieAlgebra

end ContinuousDerivations

section Inner

variable (R : Type u) {A : Type v} [CommRing R] [Ring A] [Algebra R A] [TopologicalSpace A]
  [IsTopologicalAddGroup A] [SeparatelyContinuousMul A] [ContinuousConstSMul R A]

/-- **Inner derivations are continuous**: `ad z = (z * ·) - (· * z)` is continuous as soon as
multiplication is separately continuous. -/
theorem innerDerivation_mem_continuousDerivationLieAlgebra (z : A) :
    innerDerivation R z ∈ continuousDerivationLieAlgebra R A := by
  rw [mem_continuousDerivationLieAlgebra]
  refine ((continuous_const_mul z).sub (continuous_mul_const z)).congr fun a => ?_
  simp [Ring.lie_def]

/-- **The continuous inner derivations**: `z ↦ ad z = ⁅z, -⁆`, as a homomorphism of Lie algebras
from `A` under its commutator bracket to the continuous derivations. -/
def continuousInnerDerivation : A →ₗ⁅R⁆ continuousDerivationLieAlgebra R A :=
  { (innerDerivation R).toLinearMap.codRestrict (continuousDerivationLieAlgebra R A).toSubmodule
      (innerDerivation_mem_continuousDerivationLieAlgebra R) with
    map_lie' := fun {z w} => Subtype.ext ((innerDerivation R).map_lie z w) }

/-- The continuous inner derivation by `z` is the inner derivation by `z`. -/
@[simp]
theorem coe_continuousInnerDerivation (z : A) :
    (continuousInnerDerivation R z : derivationLieAlgebra R A) = innerDerivation R z :=
  (rfl)

variable {R}

/-- **The bracket of a continuous derivation with an inner derivation is inner**:
`⁅D, ad z⁆ = ad (D z)`. -/
theorem lie_continuousInnerDerivation (D : continuousDerivationLieAlgebra R A) (z : A) :
    ⁅D, continuousInnerDerivation R z⁆ =
      continuousInnerDerivation R (((D : derivationLieAlgebra R A) : Module.End R A) z) :=
  Subtype.ext (lie_innerDerivation R (D : derivationLieAlgebra R A) z)

variable (R A)

/-- **The inner derivations form a Lie ideal of the continuous derivations**: the image of
`continuousInnerDerivation` is already an ideal, so its ideal range adds nothing to it. This
follows Mathlib's `LieDerivation.ad_isIdealMorphism`. -/
theorem continuousInnerDerivation_isIdealMorphism :
    (continuousInnerDerivation R : A →ₗ⁅R⁆ continuousDerivationLieAlgebra R A).IsIdealMorphism :=
  (LieHom.isIdealMorphism_iff _).mpr fun D z => ⟨_, lie_continuousInnerDerivation D z⟩

variable {R A}

/-- A continuous derivation lies in the ideal of inner derivations exactly when it is `ad z` for
some `z ∈ A`. This follows Mathlib's `LieDerivation.mem_ad_idealRange_iff`. -/
theorem mem_continuousInnerDerivation_idealRange_iff {D : continuousDerivationLieAlgebra R A} :
    D ∈ (continuousInnerDerivation R : A →ₗ⁅R⁆ continuousDerivationLieAlgebra R A).idealRange ↔
      ∃ z : A, continuousInnerDerivation R z = D :=
  LieHom.mem_idealRange_iff _ (continuousInnerDerivation_isIdealMorphism R A)

/-- The inner derivations are continuous in the topology of pointwise convergence:
`z ↦ z * a - a * z` is continuous for each `a`. -/
theorem continuous_continuousInnerDerivation :
    Continuous (continuousInnerDerivation R : A → continuousDerivationLieAlgebra R A) := by
  refine continuousDerivationLieAlgebra.continuous_iff.mpr fun a => ?_
  simp only [coe_continuousInnerDerivation, coe_innerDerivation, LieAlgebra.ad_apply,
    Ring.lie_def]
  exact (continuous_mul_const a).sub (continuous_const_mul a)

variable (R A)

/-- **The continuous outer derivations** `OutDer_cont(A)`: the quotient Lie algebra of the
continuous derivations by the Lie ideal of inner derivations, with the quotient topology. The
ideal is the image of `ad` itself rather than its closure, so this quotient need not be
Hausdorff. -/
abbrev ContinuousOuterDerivation : Type v :=
  continuousDerivationLieAlgebra R A ⧸
    (continuousInnerDerivation R : A →ₗ⁅R⁆ continuousDerivationLieAlgebra R A).idealRange

namespace ContinuousOuterDerivation

variable {R A}

/-- A continuous derivation has zero outer class exactly when it is inner. -/
theorem mkQ_eq_zero_iff {D : continuousDerivationLieAlgebra R A} :
    LieIdeal.mkQ _ D = (0 : ContinuousOuterDerivation R A) ↔
      ∃ z : A, continuousInnerDerivation R z = D := by
  rw [LieIdeal.mkQ_eq_zero, mem_continuousInnerDerivation_idealRange_iff]

/-- **Two continuous derivations have the same outer class exactly when they differ by an inner
derivation** `ad b` with `b ∈ A`. -/
theorem mkQ_eq_mkQ_iff {D D' : continuousDerivationLieAlgebra R A} :
    (LieIdeal.mkQ _ D : ContinuousOuterDerivation R A) = LieIdeal.mkQ _ D' ↔
      ∃ b : A, D' = D + continuousInnerDerivation R b := by
  rw [eq_comm, ← sub_eq_zero, ← map_sub, mkQ_eq_zero_iff]
  refine exists_congr fun b => ?_
  rw [eq_sub_iff_add_eq, add_comm, eq_comm]

end ContinuousOuterDerivation

end Inner

end TauCeti

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Twist.Descent

/-!
# Pointed twists and nonabelian Galois cohomology

Let `W` be a Weierstrass curve over a field `K` and let `L/K` be a Galois extension. A pointed
twist of `W` split by `L` is a Weierstrass curve `V` over `K` together with a change of variables
identifying `V_L` with `W_L`, modulo change of variables over `K`. This file constructs the type
`WeierstrassCurve.PointedTwist W L` of these isomorphism classes and proves the classification

`PointedTwist W L ≃ H¹(Gal(L/K), Aut(W_L))`.

The equivalence sends a trivialisation `C : V_L ≅ W_L` to the class of the cocycle
`σ ↦ C (σ C)⁻¹`. Its injectivity is Galois descent for changes of variables; its surjectivity is
effective descent for Weierstrass equations. The distinguished class of `W` corresponds to the
base point of nonabelian cohomology.

The construction does not require ellipticity. It classifies pointed Weierstrass forms, and hence
specializes to pointed elliptic twists when `W` is elliptic.

## Main definitions

* `WeierstrassCurve.PointedTwist`: pointed twists split by a fixed extension.
* `WeierstrassCurve.PointedTwist.mk`: the class represented by a curve and a trivialisation.
* `WeierstrassCurve.PointedTwist.lift`: descend a representative-invariant function to pointed
  twists.
* `WeierstrassCurve.PointedTwist.toCohomologyClass`: the associated nonabelian cohomology class.
* `WeierstrassCurve.pointedTwistEquivNonabelianH1`: the classification equivalence.

## References

* [J. H. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], X.2 and X.5.
* J.-P. Serre, *Galois Cohomology*, Springer, 1997, III.1.
-/

public section

noncomputable section

namespace WeierstrassCurve

open TauCeti

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

/-- A representative of a pointed twist of `W` split by `L`: a curve over `K` and a pointed
change of variables from its base change to `W_L`. Representatives are auxiliary; the public
type `PointedTwist W L` quotients out both the chosen equation and the trivialisation. -/
private structure PointedTwistPresentation (W : WeierstrassCurve K) (L : Type*) [Field L]
    [Algebra K L] where
  curve : WeierstrassCurve K
  trivialisation : VariableChange L
  isTrivialisation : trivialisation • curve.baseChange L = W.baseChange L

/-- Two presentations represent the same pointed twist when their curves differ by a change of
variables over the base field. -/
private def pointedTwistSetoid (W : WeierstrassCurve K) (L : Type*) [Field L] [Algebra K L] :
    Setoid (PointedTwistPresentation W L) where
  r P Q := ∃ C : VariableChange K, C • P.curve = Q.curve
  iseqv := by
    refine ⟨fun P ↦ ⟨1, one_smul _ _⟩, ?_, ?_⟩
    · rintro P Q ⟨C, hC⟩
      exact ⟨C⁻¹, by rw [← hC, inv_smul_smul]⟩
    · rintro P Q T ⟨C, hC⟩ ⟨D, hD⟩
      exact ⟨D * C, by rw [mul_smul, hC, hD]⟩

/-- The pointed twists of `W` over `K` which split over `L`, up to pointed isomorphism over `K`.

A representative is a curve `V/K` together with a change of variables `C` carrying `V_L` to
`W_L`. Two representatives are identified exactly when their curves are related by a change of
variables over `K`; the chosen trivialisations over `L` do not form part of the resulting class. -/
def PointedTwist (W : WeierstrassCurve K) (L : Type*) [Field L] [Algebra K L] : Type _ :=
  Quotient (pointedTwistSetoid W L)

namespace PointedTwist

variable (W : WeierstrassCurve K) (L : Type*) [Field L] [Algebra K L]

/-- The pointed-twist class represented by `V` and a trivialisation `C : V_L ≅ W_L`. -/
def mk (V : WeierstrassCurve K) (C : VariableChange L)
    (hC : C • V.baseChange L = W.baseChange L) : PointedTwist W L :=
  Quotient.mk _ ⟨V, C, hC⟩

variable {W L}

/-- Two presentations define the same pointed twist exactly when their curves are related by a
change of variables over the base field. -/
theorem mk_eq_mk_iff {V U : WeierstrassCurve K} {C D : VariableChange L}
    {hC : C • V.baseChange L = W.baseChange L}
    {hD : D • U.baseChange L = W.baseChange L} :
    mk W L V C hC = mk W L U D hD ↔ ∃ B : VariableChange K, B • V = U :=
  Quotient.eq

/-- Every pointed twist may be proved about using a representing curve and trivialisation. -/
@[elab_as_elim]
theorem induction_on {motive : PointedTwist W L → Prop} (T : PointedTwist W L)
    (mk : ∀ (V : WeierstrassCurve K) (C : VariableChange L)
      (hC : C • V.baseChange L = W.baseChange L), motive (mk W L V C hC)) : motive T := by
  refine Quotient.inductionOn T ?_
  rintro ⟨V, C, hC⟩
  exact mk V C hC

section lift

variable {β : Sort*}

/-- Descend a function of a representing curve and trivialisation to pointed twists, provided it
takes equal values on representatives whose curves differ by a change of variables over `K`. -/
def lift (f : ∀ (V : WeierstrassCurve K) (C : VariableChange L),
      C • V.baseChange L = W.baseChange L → β)
    (hf : ∀ (V : WeierstrassCurve K) (C : VariableChange L)
      (hC : C • V.baseChange L = W.baseChange L) (U : WeierstrassCurve K) (D : VariableChange L)
      (hD : D • U.baseChange L = W.baseChange L), (∃ B : VariableChange K, B • V = U) →
        f V C hC = f U D hD) :
    PointedTwist W L → β :=
  Quotient.lift (fun P ↦ f P.curve P.trivialisation P.isTrivialisation)
    fun _ _ h ↦ hf _ _ _ _ _ _ h

/-- A lifted function computes on a represented twist by evaluating on the representative. -/
@[simp]
theorem lift_mk (f : ∀ (V : WeierstrassCurve K) (C : VariableChange L),
      C • V.baseChange L = W.baseChange L → β)
    (hf : ∀ (V : WeierstrassCurve K) (C : VariableChange L)
      (hC : C • V.baseChange L = W.baseChange L) (U : WeierstrassCurve K) (D : VariableChange L)
      (hD : D • U.baseChange L = W.baseChange L), (∃ B : VariableChange K, B • V = U) →
        f V C hC = f U D hD)
    (V : WeierstrassCurve K) (C : VariableChange L) (hC : C • V.baseChange L = W.baseChange L) :
    lift f hf (mk W L V C hC) = f V C hC :=
  (rfl)

/-- A function on pointed twists that agrees with `f` on every representative is `lift f hf`. -/
theorem lift_unique (f : ∀ (V : WeierstrassCurve K) (C : VariableChange L),
      C • V.baseChange L = W.baseChange L → β)
    (hf : ∀ (V : WeierstrassCurve K) (C : VariableChange L)
      (hC : C • V.baseChange L = W.baseChange L) (U : WeierstrassCurve K) (D : VariableChange L)
      (hD : D • U.baseChange L = W.baseChange L), (∃ B : VariableChange K, B • V = U) →
        f V C hC = f U D hD)
    (g : PointedTwist W L → β)
    (hg : ∀ (V : WeierstrassCurve K) (C : VariableChange L)
      (hC : C • V.baseChange L = W.baseChange L), g (mk W L V C hC) = f V C hC) :
    g = lift f hf := by
  funext T
  induction T using induction_on with
  | mk V C hC => exact hg V C hC

end lift

/-- The distinguished pointed twist, represented by `W` with the identity trivialisation. -/
instance : One (PointedTwist W L) :=
  ⟨mk W L W 1 (one_smul _ _)⟩

/-- The distinguished pointed twist is represented by `W` with the identity trivialisation. -/
theorem one_def : (1 : PointedTwist W L) = mk W L W 1 (one_smul _ _) :=
  (rfl)

variable [IsGalois K L]

/-- The nonabelian Galois cohomology class of a pointed twist. It is represented by
`σ ↦ C (σ C)⁻¹` for any trivialisation `C : V_L ≅ W_L`. -/
def toCohomologyClass : PointedTwist W L → NonabelianH1 Gal(L/K) (W.AutCoeff L) :=
  lift (fun _ C hC ↦ C.twistCohomologyClass hC)
    fun _ C hC _ D hD h ↦ (C.twistCohomologyClass_eq_iff hC D hD).2 h

/-- The cohomology class of a represented twist is the class of its trivialisation cocycle. -/
@[simp]
theorem toCohomologyClass_mk (V : WeierstrassCurve K) (C : VariableChange L)
    (hC : C • V.baseChange L = W.baseChange L) :
    toCohomologyClass (mk W L V C hC) = C.twistCohomologyClass hC :=
  (rfl)

/-- The cohomology class determines a pointed twist. -/
theorem toCohomologyClass_injective : Function.Injective (toCohomologyClass (W := W) (L := L)) := by
  intro T U h
  induction T using induction_on with
  | mk V C hC =>
      induction U using induction_on with
      | mk U D hD =>
          rw [toCohomologyClass_mk, toCohomologyClass_mk] at h
          exact mk_eq_mk_iff.mpr
            ((C.twistCohomologyClass_eq_iff hC D hD).mp h)

/-- Every nonabelian cohomology class is the class of a pointed twist. -/
theorem toCohomologyClass_surjective :
    Function.Surjective (toCohomologyClass (W := W) (L := L)) := by
  intro x
  obtain ⟨V, C, hC, hx⟩ := VariableChange.exists_twistCohomologyClass_eq W x
  exact ⟨mk W L V C hC, by simpa using hx⟩

/-- The distinguished pointed twist maps to the base point of nonabelian cohomology. -/
@[simp]
theorem toCohomologyClass_one :
    toCohomologyClass (1 : PointedTwist W L) = 1 := by
  rw [one_def, toCohomologyClass_mk, VariableChange.twistCohomologyClass_def,
    VariableChange.twistCocycle_one, NonabelianH1.mk_one]

end PointedTwist

/-- **Pointed twists are classified by nonabelian Galois cohomology.** For a Galois extension
`L/K`, the pointed twists of `W` split by `L` are in bijection with
`H¹(Gal(L/K), Aut(W_L))`. The equivalence sends a trivialisation `C` to the class of the cocycle
`σ ↦ C (σ C)⁻¹`. -/
def pointedTwistEquivNonabelianH1 (W : WeierstrassCurve K) (L : Type*) [Field L] [Algebra K L]
    [IsGalois K L] : PointedTwist W L ≃ NonabelianH1 Gal(L/K) (W.AutCoeff L) :=
  Equiv.ofBijective PointedTwist.toCohomologyClass
    ⟨PointedTwist.toCohomologyClass_injective, PointedTwist.toCohomologyClass_surjective⟩

/-- The twist-classification equivalence is the cohomology-class map on representatives. -/
@[simp]
theorem pointedTwistEquivNonabelianH1_apply (W : WeierstrassCurve K) (L : Type*) [Field L]
    [Algebra K L] [IsGalois K L] (T : PointedTwist W L) :
    pointedTwistEquivNonabelianH1 W L T = T.toCohomologyClass :=
  (rfl)

end WeierstrassCurve

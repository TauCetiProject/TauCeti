/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.CliffordAlgebra.Quadratic.Realization
public import TauCeti.Algebra.Lie.SkewAdjoint
public import TauCeti.LinearAlgebra.ExteriorAlgebra.Derivation.OfEnd
import TauCeti.LinearAlgebra.CliffordAlgebra.Derivation

/-!
# Lie representations induced from Clifford modules

A Lie homomorphism into the skew-adjoint endomorphisms of a nondegenerate quadratic module
lifts through the quadratic realization in its Clifford algebra. Composing this lift with any
Clifford action makes the target Clifford module a module for the original Lie algebra.

## Main results

* `CliffordAlgebra.quadraticLift`: the quadratic realization of a skew-adjoint Lie action.
* `CliffordAlgebra.quadraticLift_lie_ι`: its defining action on Clifford generators.
* `CliffordAlgebra.quadraticLift_injective_iff`: the lift is injective exactly when the
  skew-adjoint action it lifts is.
* `CliffordAlgebra.cliffordInducedRep`: the induced Lie representation on a Clifford
  module.
* `CliffordAlgebra.cliffordInducedRep_apply`: its defining equation.
* `CliffordAlgebra.cliffordDerivationRep`: the induced representation on the Clifford
  algebra by inner derivations.
* `CliffordAlgebra.cliffordDerivationRep_apply`: its defining commutator equation.
* `CliffordAlgebra.equivExterior_cliffordDerivationRep` and
  `CliffordAlgebra.cliffordDerivationRep_equivExterior_symm`: the identification
  `CliffordAlgebra.equivExterior Q` with the exterior algebra, and its inverse the quantization
  map, intertwine this representation with the derivations `ExteriorAlgebra.derivationOfEnd` of the
  exterior algebra extending the skew-adjoint action.
* `CliffordAlgebra.adjointCliffordHom`: the quadratic lift of the adjoint representation
  for a Killing-semisimple Lie algebra.
* `CliffordAlgebra.adjointCliffordHom_lie_ι`: the lift acts on Clifford generators by the
  original adjoint action.
* `CliffordAlgebra.adjointCliffordHom_injective`: the lift is injective, since the adjoint action
  it encodes is faithful.
-/

public section


universe u v w x

namespace CliffordAlgebra

attribute [local instance 100] LieRing.ofAssociativeRing

/-- Lift a skew-adjoint Lie action through the quadratic realization in the Clifford algebra. -/
noncomputable def quadraticLift {K : Type u} [Field K]
    {V : Type v} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    [Invertible (2 : K)] (Q : QuadraticForm K V) (hQ : Q.Nondegenerate)
    {L : Type w} [LieRing L] [LieAlgebra K L]
    (θ : L →ₗ⁅K⁆ skewAdjointLieSubalgebra (QuadraticMap.polarBilin Q)) :
    L →ₗ⁅K⁆ CliffordAlgebra Q :=
  (quadraticLieSubalgebra Q).incl.comp <|
    (soEquivQuadratic Q hQ).toLieHom.comp θ

/-- The quadratic lift is the quadratic realization of the supplied skew-adjoint action. -/
@[simp, grind =]
theorem quadraticLift_apply {K : Type u} [Field K]
    {V : Type v} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    [Invertible (2 : K)] (Q : QuadraticForm K V) (hQ : Q.Nondegenerate)
    {L : Type w} [LieRing L] [LieAlgebra K L]
    (θ : L →ₗ⁅K⁆ skewAdjointLieSubalgebra (QuadraticMap.polarBilin Q)) (x : L) :
    quadraticLift Q hQ θ x = (soEquivQuadratic Q hQ (θ x) : CliffordAlgebra Q) := by
  rfl

/-- Values of the quadratic lift lie in the quadratic Lie subalgebra. -/
theorem quadraticLift_mem_quadraticLieSubalgebra {K : Type u} [Field K]
    {V : Type v} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    [Invertible (2 : K)] (Q : QuadraticForm K V) (hQ : Q.Nondegenerate)
    {L : Type w} [LieRing L] [LieAlgebra K L]
    (θ : L →ₗ⁅K⁆ skewAdjointLieSubalgebra (QuadraticMap.polarBilin Q)) (x : L) :
    quadraticLift Q hQ θ x ∈ quadraticLieSubalgebra Q :=
  (soEquivQuadratic Q hQ (θ x)).property

/-- The quadratic lift acts on Clifford generators through the supplied skew-adjoint action. -/
@[grind =]
theorem quadraticLift_lie_ι {K : Type u} [Field K]
    {V : Type v} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    [Invertible (2 : K)] (Q : QuadraticForm K V) (hQ : Q.Nondegenerate)
    {L : Type w} [LieRing L] [LieAlgebra K L]
    (θ : L →ₗ⁅K⁆ skewAdjointLieSubalgebra (QuadraticMap.polarBilin Q)) (x : L) (v : V) :
    ⁅quadraticLift Q hQ θ x, ι Q v⁆ = ι Q ((θ x : Module.End K V) v) := by
  rw [quadraticLift_apply, soEquivQuadratic_lie_ι]

/-- **The quadratic lift is injective exactly when the action it lifts is.** The lift is the
skew-adjoint action followed by the quadratic realization equivalence and the inclusion of the
quadratic Lie subalgebra, both of which are injective. -/
theorem quadraticLift_injective_iff {K : Type u} [Field K]
    {V : Type v} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    [Invertible (2 : K)] (Q : QuadraticForm K V) (hQ : Q.Nondegenerate)
    {L : Type w} [LieRing L] [LieAlgebra K L]
    (θ : L →ₗ⁅K⁆ skewAdjointLieSubalgebra (QuadraticMap.polarBilin Q)) :
    Function.Injective (quadraticLift Q hQ θ) ↔ Function.Injective θ :=
  (Subtype.val_injective.of_comp_iff _).trans ((soEquivQuadratic Q hQ).injective.of_comp_iff θ)

/-- The Lie representation on a Clifford module induced through the quadratic realization. -/
noncomputable def cliffordInducedRep {K : Type u} [Field K] {V : Type v} [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] [Invertible (2 : K)] (Q : QuadraticForm K V)
    (hQ : Q.Nondegenerate) {L : Type w} [LieRing L] [LieAlgebra K L]
    (θ : L →ₗ⁅K⁆ skewAdjointLieSubalgebra (QuadraticMap.polarBilin Q))
    {S : Type x} [AddCommGroup S] [Module K S]
    (ρ : CliffordAlgebra Q →ₐ[K] Module.End K S) : L →ₗ⁅K⁆ Module.End K S :=
  ρ.toLieHom.comp (quadraticLift Q hQ θ)

/-- The induced representation acts through the quadratic realization and the Clifford action. -/
@[simp, grind =]
theorem cliffordInducedRep_apply {K : Type u} [Field K] {V : Type v} [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] [Invertible (2 : K)] (Q : QuadraticForm K V)
    (hQ : Q.Nondegenerate) {L : Type w} [LieRing L] [LieAlgebra K L]
    (θ : L →ₗ⁅K⁆ skewAdjointLieSubalgebra (QuadraticMap.polarBilin Q))
    {S : Type x} [AddCommGroup S] [Module K S]
    (ρ : CliffordAlgebra Q →ₐ[K] Module.End K S) (y : L) :
    cliffordInducedRep Q hQ θ ρ y = ρ ↑(soEquivQuadratic Q hQ (θ y)) := by
  rfl

/-- The representation on the Clifford algebra induced by the inner derivations of the
quadratic realization. -/
noncomputable def cliffordDerivationRep {K : Type u} [Field K]
    {V : Type v} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    [Invertible (2 : K)] (Q : QuadraticForm K V) (hQ : Q.Nondegenerate)
    {L : Type w} [LieRing L] [LieAlgebra K L]
    (θ : L →ₗ⁅K⁆ skewAdjointLieSubalgebra (QuadraticMap.polarBilin Q)) :
    L →ₗ⁅K⁆ Module.End K (CliffordAlgebra Q) :=
  (LieAlgebra.ad K (CliffordAlgebra Q)).comp (quadraticLift Q hQ θ)

/-- The induced derivation representation acts by commutator with the quadratic
realization. -/
@[simp, grind =]
theorem cliffordDerivationRep_apply {K : Type u} [Field K]
    {V : Type v} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    [Invertible (2 : K)] (Q : QuadraticForm K V) (hQ : Q.Nondegenerate)
    {L : Type w} [LieRing L] [LieAlgebra K L]
    (θ : L →ₗ⁅K⁆ skewAdjointLieSubalgebra (QuadraticMap.polarBilin Q))
    (y : L) (c : CliffordAlgebra Q) :
    cliffordDerivationRep Q hQ θ y c =
      ⁅(soEquivQuadratic Q hQ (θ y) : CliffordAlgebra Q), c⁆ := by
  rfl

/-- **The identification with the exterior algebra is equivariant**: `CliffordAlgebra.equivExterior`
carries the commutator action `CliffordAlgebra.cliffordDerivationRep Q hQ θ y` to the derivation
`ExteriorAlgebra.derivationOfEnd K V (θ y)` of the exterior algebra extending `θ y`.

Not a `simp` lemma: `simp` unfolds `CliffordAlgebra.equivExterior` to the underlying
`CliffordAlgebra.changeFormEquiv`, so the left-hand side is not in simp-normal form. -/
theorem equivExterior_cliffordDerivationRep {K : Type u} [Field K]
    {V : Type v} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    [Invertible (2 : K)] (Q : QuadraticForm K V) (hQ : Q.Nondegenerate)
    {L : Type w} [LieRing L] [LieAlgebra K L]
    (θ : L →ₗ⁅K⁆ skewAdjointLieSubalgebra (QuadraticMap.polarBilin Q))
    (y : L) (c : CliffordAlgebra Q) :
    equivExterior Q (cliffordDerivationRep Q hQ θ y c) =
      (ExteriorAlgebra.derivationOfEnd K V (θ y : Module.End K V) :
          Module.End K (ExteriorAlgebra K V)) (equivExterior Q c) := by
  rw [cliffordDerivationRep_apply]
  exact equivExterior_lie (soEquivQuadratic_lie_ι Q hQ (θ y)) c

/-- **The quantization map is equivariant**: the inverse of `CliffordAlgebra.equivExterior Q`
carries the derivation `ExteriorAlgebra.derivationOfEnd K V (θ y)` of the exterior algebra to the
commutator action `CliffordAlgebra.cliffordDerivationRep Q hQ θ y`. -/
theorem cliffordDerivationRep_equivExterior_symm {K : Type u} [Field K]
    {V : Type v} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    [Invertible (2 : K)] (Q : QuadraticForm K V) (hQ : Q.Nondegenerate)
    {L : Type w} [LieRing L] [LieAlgebra K L]
    (θ : L →ₗ⁅K⁆ skewAdjointLieSubalgebra (QuadraticMap.polarBilin Q))
    (y : L) (w : ExteriorAlgebra K V) :
    cliffordDerivationRep Q hQ θ y ((equivExterior Q).symm w) =
      (equivExterior Q).symm
        ((ExteriorAlgebra.derivationOfEnd K V (θ y : Module.End K V) :
          Module.End K (ExteriorAlgebra K V)) w) := by
  rw [cliffordDerivationRep_apply]
  exact lie_equivExterior_symm (soEquivQuadratic_lie_ι Q hQ (θ y)) w

/-- The quadratic lift of the adjoint representation of a Killing-semisimple Lie algebra into the
Clifford algebra of its Killing quadratic form. -/
noncomputable def adjointCliffordHom (K : Type u) (L : Type v) [Field K]
    [LieRing L] [LieAlgebra K L] [FiniteDimensional K L] [Invertible (2 : K)]
    [_root_.LieAlgebra.IsKilling K L] :
    L →ₗ⁅K⁆ CliffordAlgebra (_root_.TauCeti.LieAlgebra.killingQuadraticForm K L) :=
  quadraticLift (_root_.TauCeti.LieAlgebra.killingQuadraticForm K L)
    (_root_.TauCeti.LieAlgebra.killingQuadraticForm_nondegenerate K L)
    (_root_.TauCeti.LieAlgebra.killingAdjointSO K L)

/-- The adjoint Clifford homomorphism is the quadratic realization of the Killing adjoint
action. -/
@[simp, grind =]
theorem adjointCliffordHom_apply (K : Type u) (L : Type v) [Field K]
    [LieRing L] [LieAlgebra K L] [FiniteDimensional K L] [Invertible (2 : K)]
    [_root_.LieAlgebra.IsKilling K L] (x : L) :
    adjointCliffordHom K L x =
      (soEquivQuadratic (_root_.TauCeti.LieAlgebra.killingQuadraticForm K L)
        (_root_.TauCeti.LieAlgebra.killingQuadraticForm_nondegenerate K L)
        (_root_.TauCeti.LieAlgebra.killingAdjointSO K L x) :
          CliffordAlgebra (_root_.TauCeti.LieAlgebra.killingQuadraticForm K L)) := by
  rfl

/-- The adjoint quadratic lift acts on Clifford generators by the original adjoint action. -/
@[grind =]
theorem adjointCliffordHom_lie_ι (K : Type u) (L : Type v) [Field K]
    [LieRing L] [LieAlgebra K L] [FiniteDimensional K L] [Invertible (2 : K)]
    [_root_.LieAlgebra.IsKilling K L] (x y : L) :
    ⁅adjointCliffordHom K L x,
        CliffordAlgebra.ι (_root_.TauCeti.LieAlgebra.killingQuadraticForm K L) y⁆ =
      CliffordAlgebra.ι (_root_.TauCeti.LieAlgebra.killingQuadraticForm K L) ⁅x, y⁆ := by
  rw [adjointCliffordHom, quadraticLift_lie_ι,
    _root_.TauCeti.LieAlgebra.coe_killingAdjointSO, _root_.LieAlgebra.ad_apply]

/-- **The adjoint quadratic lift of a Killing-semisimple Lie algebra is injective.** The lift is
injective exactly when the adjoint action it lifts is
(`CliffordAlgebra.quadraticLift_injective_iff`), and that action is faithful because the centre of
a Killing-semisimple Lie algebra vanishes. -/
theorem adjointCliffordHom_injective (K : Type u) (L : Type v) [Field K]
    [LieRing L] [LieAlgebra K L] [FiniteDimensional K L] [Invertible (2 : K)]
    [_root_.LieAlgebra.IsKilling K L] :
    Function.Injective (adjointCliffordHom K L) :=
  (quadraticLift_injective_iff _ _ _).2 <|
    (_root_.TauCeti.LieAlgebra.killingAdjointSO_injective_iff K L).mpr
      (_root_.LieAlgebra.center_eq_bot K L)

end CliffordAlgebra

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.UniversalEnveloping.Basic
public import TauCeti.LinearAlgebra.SymmetricAlgebra.Derivation
public import TauCeti.LinearAlgebra.SymmetricAlgebra.Functoriality
public import TauCeti.LinearAlgebra.SymmetricAlgebra.Homogeneous
public import Mathlib.RingTheory.Derivation.Lie

/-!
# The adjoint action on a symmetric algebra

Let `L` be a Lie algebra over a commutative ring `R`. The adjoint endomorphism
`y ↦ ⁅x, y⁆` extends uniquely from `L` to a derivation of its symmetric algebra `S(L)`.
These extensions preserve brackets, giving a representation of `L` on `S(L)` by derivations and,
by the universal property, an action of `UniversalEnvelopingAlgebra R L` on `S(L)`.

On a product of symmetric generators the action differentiates one factor at a time. This is the
equivariant input for comparing `S(L)` with the associated graded of the PBW filtration: the
canonical PBW map sends symmetric generators to their leading classes, and this file supplies the
symmetric-algebra side of its equivariance.

## Main definitions and results

* `TauCeti.SymmetricAlgebra.adjointDerivation`: the Lie homomorphism from `L` to derivations of
  `S(L)`.
* `TauCeti.SymmetricAlgebra.adjointRepresentation`: the resulting representation on the underlying
  `R`-module of `S(L)`.
* `TauCeti.SymmetricAlgebra.envelopingAdjointRepresentation`: its extension to an algebra
  homomorphism from `U(L)` to endomorphisms of `S(L)`.
* `TauCeti.SymmetricAlgebra.adjointDerivation_mem_homogeneousSubmodule`: the action preserves
  each homogeneous degree.

## References

* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, Chapter V, §17.
* N. Bourbaki, *Lie Groups and Lie Algebras*, Chapter I, §2.7.
-/

public section

namespace TauCeti.SymmetricAlgebra

open _root_.SymmetricAlgebra

universe u v

section Homogeneous

variable (R : Type u) (M : Type v) [CommSemiring R] [AddCommMonoid M] [Module R M]

/-- A derivation induced by a linear endomorphism preserves the degree of a product of symmetric
generators. -/
theorem mkDerivation_ι_comp_prod_map_ι_mem_homogeneousSubmodule
    (f : M →ₗ[R] M) (l : List M) :
    mkDerivation ((ι R M).comp f) (l.map (ι R M)).prod ∈
      TauCeti.SymmetricAlgebra.homogeneousSubmodule R M l.length := by
  induction l with
  | nil => simp
  | cons y l ih =>
      rw [List.map_cons, List.prod_cons, Derivation.leibniz, mkDerivation_ι]
      simp only [LinearMap.comp_apply, smul_eq_mul]
      apply Submodule.add_mem
      · have hhead := TauCeti.SymmetricAlgebra.prod_map_ι_mem_homogeneousSubmodule R M [y]
        simpa [Nat.add_comm] using
          SetLike.GradedMonoid.toGradedMul.mul_mem hhead ih
      · have htail := TauCeti.SymmetricAlgebra.prod_map_ι_mem_homogeneousSubmodule R M l
        have hhead :=
          TauCeti.SymmetricAlgebra.prod_map_ι_mem_homogeneousSubmodule R M [f y]
        simpa [Nat.add_comm] using
          SetLike.GradedMonoid.toGradedMul.mul_mem htail hhead

/-- A derivation of a symmetric algebra induced by a linear endomorphism preserves every
homogeneous submodule. -/
theorem mkDerivation_ι_comp_mem_homogeneousSubmodule (f : M →ₗ[R] M) {n : ℕ}
    {p : SymmetricAlgebra R M}
    (hp : p ∈ TauCeti.SymmetricAlgebra.homogeneousSubmodule R M n) :
    mkDerivation ((ι R M).comp f) p ∈
      TauCeti.SymmetricAlgebra.homogeneousSubmodule R M n := by
  rw [TauCeti.SymmetricAlgebra.homogeneousSubmodule_eq_span] at hp
  induction hp using Submodule.span_induction with
  | mem p hp =>
      obtain ⟨l, hl, rfl⟩ := hp
      simpa [hl] using
        mkDerivation_ι_comp_prod_map_ι_mem_homogeneousSubmodule R M f l
  | zero => simp
  | add p q _ _ hp hq => simpa using Submodule.add_mem _ hp hq
  | smul r p _ hp => simpa using Submodule.smul_mem _ r hp

end Homogeneous

variable (R : Type u) (L : Type v) [CommRing R] [LieRing L] [LieAlgebra R L]

local notation "S" => SymmetricAlgebra R L
attribute [local instance 100] LieRing.ofAssociativeRing

/-- The linear map on generators that sends `y` to the symmetric generator corresponding to
`⁅x, y⁆`. -/
private def adjointGeneratorMap (x : L) : L →ₗ[R] S :=
  (ι R L).comp (LieAlgebra.ad R L x)

/-- The `R`-linear assignment taking `x : L` to the derivation of `S(L)` induced by
`y ↦ ι(⁅x, y⁆)`. -/
private noncomputable def adjointDerivationLinearMap :
    L →ₗ[R] Derivation R S S where
  toFun x := mkDerivation (adjointGeneratorMap R L x)
  map_add' x y := derivation_ext fun z => by simp [adjointGeneratorMap]
  map_smul' r x := derivation_ext fun z => by simp [adjointGeneratorMap]

@[simp]
private theorem adjointDerivationLinearMap_ι (x y : L) :
    adjointDerivationLinearMap R L x (ι R L y) = ι R L ⁅x, y⁆ := by
  simp [adjointDerivationLinearMap, adjointGeneratorMap]

/-- The adjoint action of `L` on its symmetric algebra, by derivations. -/
noncomputable def adjointDerivation : L →ₗ⁅R⁆ Derivation R S S where
  toLinearMap := adjointDerivationLinearMap R L
  map_lie' {x y} := by
    apply derivation_ext
    intro z
    simp only [Derivation.commutator_apply]
    simp only [adjointDerivationLinearMap, mkDerivation_ι, adjointGeneratorMap,
      LinearMap.comp_apply, LieAlgebra.ad_apply]
    rw [lie_lie]
    simp

/-- The adjoint derivation sends a symmetric generator `ι(y)` to `ι(⁅x, y⁆)`. -/
@[simp]
theorem adjointDerivation_ι (x y : L) :
    adjointDerivation R L x (ι R L y) = ι R L ⁅x, y⁆ := by
  rw [adjointDerivation]
  exact adjointDerivationLinearMap_ι R L x y

/-- The representation of `L` on the underlying module of its symmetric algebra obtained from
the adjoint derivations. -/
noncomputable def adjointRepresentation : L →ₗ⁅R⁆ Module.End R S :=
  (LieModule.toEnd R (Derivation R S S) S).comp (adjointDerivation R L)

/-- The adjoint representation acts by the corresponding adjoint derivation. -/
@[simp]
theorem adjointRepresentation_apply (x : L) (p : S) :
    adjointRepresentation R L x p = adjointDerivation R L x p := by
  simp [adjointRepresentation, LieModule.toEnd_apply_apply]

/-- The adjoint representation of `L` on `S(L)`, extended to its universal enveloping algebra. -/
noncomputable def envelopingAdjointRepresentation :
    UniversalEnvelopingAlgebra R L →ₐ[R] Module.End R S :=
  UniversalEnvelopingAlgebra.lift R (adjointRepresentation R L)

/-- The enveloping adjoint representation restricts to the adjoint representation on `L`. -/
theorem envelopingAdjointRepresentation_ι (x : L) :
    envelopingAdjointRepresentation R L (UniversalEnvelopingAlgebra.ι R x) =
      adjointRepresentation R L x := by
  exact UniversalEnvelopingAlgebra.lift_ι_apply R (adjointRepresentation R L) x

/-- A generator from `L` acts through the enveloping adjoint representation by the corresponding
adjoint derivation. -/
@[simp]
theorem envelopingAdjointRepresentation_ι_apply (x : L) (p : S) :
    envelopingAdjointRepresentation R L
        ((UniversalEnvelopingAlgebra.mkAlgHom R L) (TensorAlgebra.ι R x)) p =
      adjointDerivation R L x p := by
  rw [envelopingAdjointRepresentation, UniversalEnvelopingAlgebra.lift_ι_apply']
  exact adjointRepresentation_apply R L x p

section Naturality

variable {M : Type*} [LieRing M] [LieAlgebra R M]

/-- The symmetric-algebra map induced by a Lie homomorphism intertwines the adjoint derivations. -/
theorem map_adjointDerivation (f : L →ₗ⁅R⁆ M) (x : L) (p : S) :
    map R f.toLinearMap (adjointDerivation R L x p) =
      adjointDerivation R M (f x) (map R f.toLinearMap p) := by
  induction p using SymmetricAlgebra.induction with
  | algebraMap r => simp
  | ι y => simp [adjointDerivation_ι]
  | mul p q hp hq =>
      simp only [Derivation.leibniz, smul_eq_mul, map_add, map_mul, hp, hq]
  | add p q hp hq => simp only [map_add, hp, hq]

/-- Naturality of the adjoint action, as an equality of linear maps. -/
theorem map_comp_adjointDerivation (f : L →ₗ⁅R⁆ M) (x : L) :
    (map R f.toLinearMap).toLinearMap.comp (adjointDerivation R L x).toLinearMap =
      (adjointDerivation R M (f x)).toLinearMap.comp (map R f.toLinearMap).toLinearMap := by
  ext p
  exact map_adjointDerivation R L f x p

end Naturality

section Homogeneous

/-- Every adjoint derivation preserves each homogeneous submodule of the symmetric algebra. -/
theorem adjointDerivation_mem_homogeneousSubmodule (x : L) {n : ℕ} {p : S}
    (hp : p ∈ TauCeti.SymmetricAlgebra.homogeneousSubmodule R L n) :
    adjointDerivation R L x p ∈
      TauCeti.SymmetricAlgebra.homogeneousSubmodule R L n := by
  simpa [adjointDerivation, adjointDerivationLinearMap, adjointGeneratorMap] using
    mkDerivation_ι_comp_mem_homogeneousSubmodule R L (LieAlgebra.ad R L x) hp

end Homogeneous

end TauCeti.SymmetricAlgebra

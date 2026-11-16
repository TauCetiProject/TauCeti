/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Sheaves.Cech.Cup.Basic
public import TauCeti.Topology.Sheaves.LocallyConstant.Module

/-!
# The graded Čech cohomology algebra with locally constant coefficients

This file packages the Čech cup product of `TauCeti.Topology.Sheaves.Cech.Cup.Basic` for the
sheaf `TopCat.locallyConstantModuleSheaf X R A` of locally constant functions with values in an
`R`-algebra `A`, yielding the graded `R`-algebra `TauCeti.Topology.cechCohomologyAlgebra X R A`.

It supplies:
* the canonical `DirectSum.GRing` and `DirectSum.GAlgebra R` instances on
  `n ↦ Hⁿ(X, A_X)` and graded commutativity when `A` is commutative
  (`TauCeti.Topology.cechCohomologyAlgebra_of_mul_comm`);
* the injective `R`-algebra homomorphism `TauCeti.Topology.cechCohomologyZeroAlgHom` from
  `LocallyConstant X A` into the degree-`0` summand of `cechCohomologyAlgebra X R A`;
* contravariant pullback `TopCat.Hom.cechCohomologyAlgebraPullback` as an `R`-algebra homomorphism
  along any continuous map `f : X ⟶ Y`, compatible with composition, identity, and
  `cechCohomologyZeroAlgHom`;
* a counterexample (`TauCeti.Topology.exists_cechCupCochain_cocycles_not_gradedComm`) confirming
  that `cechCupCochain` is not graded-commutative on `1`-cocycles even when `A` is commutative
  (graded commutativity holds only after passing to cohomology).

## Main definitions

* `TauCeti.Topology.locallyConstantCechCohomologyZeroEquiv`: `R`-linear equivalence
  `LocallyConstant X M ≃ₗ[R] H⁰(X, M_X)`.
* `TauCeti.Topology.cechCohomologyAlgebra X R A`: the graded Čech cohomology `R`-algebra
  `⨁ n : ℕ, Hⁿ(X, A_X)` with multiplication given by the Čech cup product.
* `TauCeti.Topology.cechCohomologyZeroAlgHom`: the injective `R`-algebra homomorphism
  `LocallyConstant X A →ₐ[R] cechCohomologyAlgebra X R A`.
* `TopCat.Hom.cechCohomologyAlgebraPullback`: the contravariant `R`-algebra homomorphism
  `cechCohomologyAlgebra Y R A →ₐ[R] cechCohomologyAlgebra X R A` induced by `f : X ⟶ Y`.

## Main results

* `TauCeti.Topology.cechCohomologyAlgebra_of_mul_of`,
  `TauCeti.Topology.cechCohomologyAlgebra_one`: multiplication and unit of
  `cechCohomologyAlgebra X R A`.
* `TauCeti.Topology.cechCohomologyAlgebra_of_mul_comm`: graded commutativity for commutative `A`.
* `TauCeti.Topology.injective_cechCohomologyZeroAlgHom`: injectivity of degree-`0` inclusion.
* `TopCat.Hom.cechCohomologyAlgebraPullback_id`,
  `TopCat.Hom.cechCohomologyAlgebraPullback_comp`,
  `TopCat.Hom.cechCohomologyAlgebraPullback_cechCohomologyZeroAlgHom`: functoriality and
  degree-`0` compatibility of pullback on the graded cohomology algebra.
* `TauCeti.Topology.exists_cechCupCochain_cocycles_not_gradedComm`: `cechCupCochain` is not
  graded-commutative at the cocycle level.

## References

* The Stacks Project, Cohomology of Sheaves, §20.25 (tags 01FP, 07MB), for the Čech cup product,
  its graded commutativity, and its compatibility with continuous maps.
-/

public section

noncomputable section

open CategoryTheory Limits TopologicalSpace Opposite DirectSum
open TauCeti.CategoryTheory

universe uR u

/-! ### The graded Čech cohomology `R`-algebra with locally constant coefficients -/

namespace TauCeti.Topology

/-- The degree-`0` Čech cohomology of the locally constant presheaf `M_X` is `R`-linearly
equivalent to `LocallyConstant X M`. -/
def locallyConstantCechCohomologyZeroEquiv (X : TopCat.{u}) (R : Type uR) [Ring R]
    (M : Type u) [AddCommGroup M] [Module R M] :
    LocallyConstant X M ≃ₗ[R]
      (cechCohomology X (ModuleCat.{u} R) 0).obj (TopCat.locallyConstantModulePresheaf X R M) :=
  LinearEquiv.trans
    { toLinearMap := LocallyConstant.comapₗ R ⟨Subtype.val, continuous_subtype_val⟩
      invFun := fun s ↦ s.comap ⟨fun x ↦ ⟨x, trivial⟩, continuous_id.subtype_mk _⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl }
    ((cechCohomologyZeroIso (TopCat.locallyConstantModuleSheaf X R M)).toLinearEquiv :
      LocallyConstant (⊤ : Opens X) M ≃ₗ[R]
        (cechCohomology X (ModuleCat.{u} R) 0).obj (TopCat.locallyConstantModulePresheaf X R M))

/-- Formula for `locallyConstantCechCohomologyZeroEquiv` via `cechCohomologyZeroIso`. -/
theorem locallyConstantCechCohomologyZeroEquiv_apply (X : TopCat.{u}) (R : Type uR) [Ring R]
    (M : Type u) [AddCommGroup M] [Module R M] (s : LocallyConstant X M) :
    locallyConstantCechCohomologyZeroEquiv X R M s =
      (cechCohomologyZeroIso (TopCat.locallyConstantModuleSheaf X R M)).hom
        (s.comap ⟨Subtype.val, continuous_subtype_val⟩) := by
  rfl

section Algebra

variable (X : TopCat.{u}) (R : Type uR) [CommRing R] (A : Type u) [Ring A] [Algebra R A]

/-- The canonical graded ring structure on `n ↦ Hⁿ(X, A_X)` induced by the Čech cup product and
pointwise multiplication in the `R`-algebra `A`. -/
instance locallyConstantCechCohomologyGRing :
    DirectSum.GRing fun n : ℕ ↦
      ((cechCohomology X (ModuleCat.{u} R) n).obj
        (TopCat.locallyConstantModulePresheaf X R A) : Type u) :=
  cechCohomologyGRing X (TopCat.locallyConstantModulePresheaf X R A)
    (TopCat.locallyConstantMul X R A) (fun _ _ _ ↦ rfl)
    (fun U r s t ↦ TopCat.locallyConstantMul_assoc U r s t)
    (TopCat.locallyConstantOne X R A) (fun _ ↦ rfl)
    (fun U s ↦ TopCat.locallyConstantMul_one_left U s)
    (fun U s ↦ TopCat.locallyConstantMul_one_right U s)

/-- The canonical graded `R`-algebra structure on `n ↦ Hⁿ(X, A_X)`. -/
instance locallyConstantCechCohomologyGAlgebra :
    DirectSum.GAlgebra R fun n : ℕ ↦
      ((cechCohomology X (ModuleCat.{u} R) n).obj
        (TopCat.locallyConstantModulePresheaf X R A) : Type u) :=
  cechCohomologyGAlgebra X (TopCat.locallyConstantModulePresheaf X R A)
    (TopCat.locallyConstantMul X R A) (fun _ _ _ ↦ rfl)
    (fun U r s t ↦ TopCat.locallyConstantMul_assoc U r s t)
    (TopCat.locallyConstantOne X R A) (fun _ ↦ rfl)
    (fun U s ↦ TopCat.locallyConstantMul_one_left U s)
    (fun U s ↦ TopCat.locallyConstantMul_one_right U s)

/-- **The graded Čech cohomology `R`-algebra `H^*(X; A)`** with locally constant coefficients in an
`R`-algebra `A`, realized as `⨁ n : ℕ, Hⁿ(X, A_X)` with multiplication given by the Čech cup
product. -/
abbrev cechCohomologyAlgebra : Type u :=
  ⨁ n : ℕ, ((cechCohomology X (ModuleCat.{u} R) n).obj
    (TopCat.locallyConstantModulePresheaf X R A) : Type u)

/-- Multiplication of homogeneous classes in `cechCohomologyAlgebra X R A` is the Čech cup
product. -/
@[simp]
theorem cechCohomologyAlgebra_of_mul_of {p q : ℕ}
    (x : (cechCohomology X (ModuleCat.{u} R) p).obj (TopCat.locallyConstantModulePresheaf X R A))
    (y : (cechCohomology X (ModuleCat.{u} R) q).obj (TopCat.locallyConstantModulePresheaf X R A)) :
    DirectSum.of (fun n : ℕ ↦ ((cechCohomology X (ModuleCat.{u} R) n).obj
        (TopCat.locallyConstantModulePresheaf X R A) : Type u)) p x *
      DirectSum.of (fun n : ℕ ↦ ((cechCohomology X (ModuleCat.{u} R) n).obj
        (TopCat.locallyConstantModulePresheaf X R A) : Type u)) q y =
    DirectSum.of (fun n : ℕ ↦ ((cechCohomology X (ModuleCat.{u} R) n).obj
        (TopCat.locallyConstantModulePresheaf X R A) : Type u)) (p + q)
      (cechCohomologyCup X (TopCat.locallyConstantMul X R A) (fun _ _ _ ↦ rfl) p q (p + q) rfl
        x y) := by
  exact DirectSum.of_mul_of
    (A := fun n : ℕ ↦ ((cechCohomology X (ModuleCat.{u} R) n).obj
      (TopCat.locallyConstantModulePresheaf X R A) : Type u)) x y

/-- The multiplicative unit of `cechCohomologyAlgebra X R A` is the degree-`0` class of the
constant section `1`. -/
@[simp]
theorem cechCohomologyAlgebra_one :
    (1 : cechCohomologyAlgebra X R A) =
      DirectSum.of (fun n : ℕ ↦ ((cechCohomology X (ModuleCat.{u} R) n).obj
        (TopCat.locallyConstantModulePresheaf X R A) : Type u)) 0
        (cechCohomologyUnitClass X (TopCat.locallyConstantModulePresheaf X R A)
          (TopCat.locallyConstantOne X R A) (fun _ ↦ rfl)) := by
  rfl

/-- **Graded commutativity of `cechCohomologyAlgebra`.** When `A` is a commutative `R`-algebra,
homogeneous classes `x ∈ Hᵖ(X; A)` and `y ∈ H^q(X; A)` satisfy `y * x = (-1)^(p * q) • (x * y)`. -/
theorem cechCohomologyAlgebra_of_mul_comm {B : Type u} [CommRing B] [Algebra R B] {p q : ℕ}
    (x : (cechCohomology X (ModuleCat.{u} R) p).obj (TopCat.locallyConstantModulePresheaf X R B))
    (y : (cechCohomology X (ModuleCat.{u} R) q).obj (TopCat.locallyConstantModulePresheaf X R B)) :
    DirectSum.of (fun n : ℕ ↦ ((cechCohomology X (ModuleCat.{u} R) n).obj
        (TopCat.locallyConstantModulePresheaf X R B) : Type u)) q y *
      DirectSum.of (fun n : ℕ ↦ ((cechCohomology X (ModuleCat.{u} R) n).obj
        (TopCat.locallyConstantModulePresheaf X R B) : Type u)) p x =
    (-1 : ℤ) ^ (p * q) •
      (DirectSum.of (fun n : ℕ ↦ ((cechCohomology X (ModuleCat.{u} R) n).obj
          (TopCat.locallyConstantModulePresheaf X R B) : Type u)) p x *
        DirectSum.of (fun n : ℕ ↦ ((cechCohomology X (ModuleCat.{u} R) n).obj
          (TopCat.locallyConstantModulePresheaf X R B) : Type u)) q y) := by
  rw [cechCohomologyAlgebra_of_mul_of, cechCohomologyAlgebra_of_mul_of, ← map_zsmul]
  refine DFinsupp.single_eq_of_sigma_eq (Sigma.ext (Nat.add_comm q p) ?_)
  refine (cechCohomologyCup_heq X (TopCat.locallyConstantMul X R B) (fun _ _ _ ↦ rfl)
    rfl (Nat.add_comm q p) y x).trans (heq_of_eq ?_)
  exact cechCohomologyCup_comm X (TopCat.locallyConstantMul X R B)
    (TopCat.locallyConstantMul X R B) (fun _ _ _ ↦ rfl) (fun _ _ _ ↦ rfl)
    (fun U s t ↦ TopCat.locallyConstantMul_comm U t s) p q (p + q) rfl x y

private lemma locallyConstantCechCohomologyZeroEquiv_one :
    locallyConstantCechCohomologyZeroEquiv X R A 1 =
      cechCohomologyUnitClass X (TopCat.locallyConstantModulePresheaf X R A)
        (TopCat.locallyConstantOne X R A) (fun _ ↦ rfl) :=
  cechCohomologyZeroIso_hom_eq_cechCohomologyUnitClass X
    (TopCat.locallyConstantModuleSheaf X R A) (TopCat.locallyConstantOne X R A (op ⊤))

private lemma locallyConstantCechCohomologyZeroEquiv_mul (s t : LocallyConstant X A) :
    locallyConstantCechCohomologyZeroEquiv X R A (s * t) =
      cechCohomologyCup X (TopCat.locallyConstantMul X R A) (fun _ _ _ ↦ rfl) 0 0 0 rfl
        (locallyConstantCechCohomologyZeroEquiv X R A s)
        (locallyConstantCechCohomologyZeroEquiv X R A t) :=
  (cechCohomologyCup_cechCohomologyZeroIso_hom X
    (TopCat.locallyConstantModuleSheaf X R A) (TopCat.locallyConstantModuleSheaf X R A)
    (TopCat.locallyConstantModuleSheaf X R A)
    (TopCat.locallyConstantMul X R A) (fun _ _ _ ↦ rfl)
    (s.comap ⟨Subtype.val, continuous_subtype_val⟩)
    (t.comap ⟨Subtype.val, continuous_subtype_val⟩)).symm

/-- The canonical `R`-algebra homomorphism from locally constant functions `LocallyConstant X A`
into the degree-`0` summand of `cechCohomologyAlgebra X R A`. -/
def cechCohomologyZeroAlgHom : LocallyConstant X A →ₐ[R] cechCohomologyAlgebra X R A where
  toFun s :=
    DirectSum.of (fun n : ℕ ↦ ((cechCohomology X (ModuleCat.{u} R) n).obj
        (TopCat.locallyConstantModulePresheaf X R A) : Type u)) 0
      (locallyConstantCechCohomologyZeroEquiv X R A s)
  map_one' := by
    rw [locallyConstantCechCohomologyZeroEquiv_one, cechCohomologyAlgebra_one]
  map_mul' s t := by
    rw [cechCohomologyAlgebra_of_mul_of, locallyConstantCechCohomologyZeroEquiv_mul]
  map_zero' := by
    rw [map_zero, map_zero]
  map_add' s t := by
    rw [map_add, map_add]
  commutes' r := by
    rw [Algebra.algebraMap_eq_smul_one, map_smul, locallyConstantCechCohomologyZeroEquiv_one,
      DirectSum.algebraMap_apply]
    rfl

/-- Evaluation of `cechCohomologyZeroAlgHom` on a locally constant function. -/
@[simp]
theorem cechCohomologyZeroAlgHom_apply (s : LocallyConstant X A) :
    cechCohomologyZeroAlgHom X R A s =
      DirectSum.of (fun n : ℕ ↦ ((cechCohomology X (ModuleCat.{u} R) n).obj
          (TopCat.locallyConstantModulePresheaf X R A) : Type u)) 0
        (locallyConstantCechCohomologyZeroEquiv X R A s) := by
  rfl

/-- `cechCohomologyZeroAlgHom` is injective: global locally constant functions embed into the
degree-`0` part of `cechCohomologyAlgebra X R A`. -/
theorem injective_cechCohomologyZeroAlgHom :
    Function.Injective (cechCohomologyZeroAlgHom X R A) := fun _ _ h ↦
  (locallyConstantCechCohomologyZeroEquiv X R A).injective (DirectSum.of_injective 0 h)

end Algebra

end TauCeti.Topology

/-! ### Pullback on the graded Čech cohomology algebra -/

namespace TopCat.Hom

section AlgebraPullback

variable {X Y Z : TopCat.{u}}

/-- **Pullback on the graded Čech cohomology `R`-algebra.** A continuous map `f : X ⟶ Y` induces an
`R`-algebra homomorphism `H^*(Y; A) →ₐ[R] H^*(X; A)` acting in each degree `n` by
`f.cechCohomologyPullback n (f.locallyConstantModulePullback R A)`. -/
def cechCohomologyAlgebraPullback (f : X ⟶ Y) (R : Type uR) [CommRing R] (A : Type u) [Ring A]
    [Algebra R A] :
    TauCeti.Topology.cechCohomologyAlgebra Y R A →ₐ[R]
      TauCeti.Topology.cechCohomologyAlgebra X R A :=
  DirectSum.toAlgebra R
    (fun n : ℕ ↦ ((TauCeti.Topology.cechCohomology Y (ModuleCat.{u} R) n).obj
      (TopCat.locallyConstantModulePresheaf Y R A) : Type u))
    (fun n ↦ (DirectSum.lof R ℕ
        (fun k : ℕ ↦ ((TauCeti.Topology.cechCohomology X (ModuleCat.{u} R) k).obj
          (TopCat.locallyConstantModulePresheaf X R A) : Type u)) n).comp
      (f.cechCohomologyPullback n (f.locallyConstantModulePullback R A)).hom)
    (by
      -- Unfold `GradedMonoid.GOne.one` to `cechCohomologyUnitClass`.
      change DirectSum.of (fun k : ℕ ↦ ((TauCeti.Topology.cechCohomology X (ModuleCat.{u} R) k).obj
            (TopCat.locallyConstantModulePresheaf X R A) : Type u)) 0
          (f.cechCohomologyPullback 0 (f.locallyConstantModulePullback R A)
            (TauCeti.Topology.cechCohomologyUnitClass Y
              (TopCat.locallyConstantModulePresheaf Y R A)
              (TopCat.locallyConstantOne Y R A) (fun _ ↦ rfl))) =
        (1 : TauCeti.Topology.cechCohomologyAlgebra X R A)
      rw [f.cechCohomologyPullback_cechCohomologyUnitClass (f.locallyConstantModulePullback R A)
        (TopCat.locallyConstantOne Y R A) (fun _ ↦ rfl)
        (TopCat.locallyConstantOne X R A) (fun _ ↦ rfl)
        (fun U ↦ f.locallyConstantModulePullback_app_one U),
        TauCeti.Topology.cechCohomologyAlgebra_one])
    (fun {p q} x y ↦ by
      -- Unfold `GradedMonoid.GMul.mul` to `cechCohomologyCup`.
      change DirectSum.of (fun k : ℕ ↦ ((TauCeti.Topology.cechCohomology X (ModuleCat.{u} R) k).obj
            (TopCat.locallyConstantModulePresheaf X R A) : Type u)) (p + q)
          (f.cechCohomologyPullback (p + q) (f.locallyConstantModulePullback R A)
            (TauCeti.Topology.cechCohomologyCup Y (TopCat.locallyConstantMul Y R A)
              (fun _ _ _ ↦ rfl) p q (p + q) rfl x y)) =
        DirectSum.of (fun k : ℕ ↦ ((TauCeti.Topology.cechCohomology X (ModuleCat.{u} R) k).obj
            (TopCat.locallyConstantModulePresheaf X R A) : Type u)) p
          (f.cechCohomologyPullback p (f.locallyConstantModulePullback R A) x) *
        DirectSum.of (fun k : ℕ ↦ ((TauCeti.Topology.cechCohomology X (ModuleCat.{u} R) k).obj
            (TopCat.locallyConstantModulePresheaf X R A) : Type u)) q
          (f.cechCohomologyPullback q (f.locallyConstantModulePullback R A) y)
      rw [TauCeti.Topology.cechCohomologyAlgebra_of_mul_of,
        f.cechCohomologyPullback_cechCohomologyCup (TopCat.locallyConstantMul Y R A)
          (TopCat.locallyConstantMul X R A) (fun _ _ _ ↦ rfl) (fun _ _ _ ↦ rfl)
          (f.locallyConstantModulePullback R A) (f.locallyConstantModulePullback R A)
          (f.locallyConstantModulePullback R A)
          (fun U s t ↦ f.locallyConstantModulePullback_app_mul U s t) p q (p + q) rfl x y])

/-- On a homogeneous class in degree `n`, `cechCohomologyAlgebraPullback` acts by
`cechCohomologyPullback` in degree `n`. -/
@[simp]
theorem cechCohomologyAlgebraPullback_of (f : X ⟶ Y) (R : Type uR) [CommRing R] (A : Type u)
    [Ring A] [Algebra R A] (n : ℕ)
    (x : (TauCeti.Topology.cechCohomology Y (ModuleCat.{u} R) n).obj
      (TopCat.locallyConstantModulePresheaf Y R A)) :
    f.cechCohomologyAlgebraPullback R A
        (DirectSum.of (fun k : ℕ ↦ ((TauCeti.Topology.cechCohomology Y (ModuleCat.{u} R) k).obj
          (TopCat.locallyConstantModulePresheaf Y R A) : Type u)) n x) =
      DirectSum.of (fun k : ℕ ↦ ((TauCeti.Topology.cechCohomology X (ModuleCat.{u} R) k).obj
        (TopCat.locallyConstantModulePresheaf X R A) : Type u)) n
        (f.cechCohomologyPullback n (f.locallyConstantModulePullback R A) x) := by
  unfold cechCohomologyAlgebraPullback
  exact DirectSum.toAddMonoid_of
    (β := fun k : ℕ ↦ ((TauCeti.Topology.cechCohomology Y (ModuleCat.{u} R) k).obj
      (TopCat.locallyConstantModulePresheaf Y R A) : Type u))
    (γ := TauCeti.Topology.cechCohomologyAlgebra X R A)
    (fun k ↦ ((DirectSum.lof R ℕ
        (fun m : ℕ ↦ ((TauCeti.Topology.cechCohomology X (ModuleCat.{u} R) m).obj
          (TopCat.locallyConstantModulePresheaf X R A) : Type u)) k).comp
      (f.cechCohomologyPullback k (f.locallyConstantModulePullback R A)).hom).toAddMonoidHom)
    n x

/-- Pullback along the identity map is the identity algebra homomorphism on
`cechCohomologyAlgebra`. -/
@[simp]
theorem cechCohomologyAlgebraPullback_id (X : TopCat.{u}) (R : Type uR) [CommRing R] (A : Type u)
    [Ring A] [Algebra R A] :
    TopCat.Hom.cechCohomologyAlgebraPullback (𝟙 X) R A =
      AlgHom.id R (TauCeti.Topology.cechCohomologyAlgebra X R A) := by
  refine DirectSum.algHom_ext R _ fun n x ↦ ?_
  rw [cechCohomologyAlgebraPullback_of, TopCat.Hom.locallyConstantModulePullback_id,
    cechCohomologyPullback_id, AlgHom.id_apply]
  rfl

/-- Pullback on `cechCohomologyAlgebra` is contravariantly functorial in continuous maps. -/
@[simp]
theorem cechCohomologyAlgebraPullback_comp (f : X ⟶ Y) (g : Y ⟶ Z) (R : Type uR) [CommRing R]
    (A : Type u) [Ring A] [Algebra R A] :
    TopCat.Hom.cechCohomologyAlgebraPullback (f ≫ g) R A =
      (f.cechCohomologyAlgebraPullback R A).comp (g.cechCohomologyAlgebraPullback R A) := by
  refine DirectSum.algHom_ext R _ fun n x ↦ ?_
  rw [AlgHom.comp_apply, cechCohomologyAlgebraPullback_of, cechCohomologyAlgebraPullback_of,
    cechCohomologyAlgebraPullback_of,
    cechCohomologyPullback_comp f g n (g.locallyConstantModulePullback R A)
      (f.locallyConstantModulePullback R A)
      (TopCat.Hom.locallyConstantModulePullback (f ≫ g) R A)
      (fun V ↦ NatTrans.congr_app (TopCat.Hom.locallyConstantModulePullback_comp f g R A) V),
    ModuleCat.comp_apply]

/-- Pullback on `cechCohomologyAlgebra` agrees on degree-`0` classes with precomposition of
globally defined locally constant functions. -/
theorem cechCohomologyAlgebraPullback_cechCohomologyZeroAlgHom (f : X ⟶ Y) (R : Type uR)
    [CommRing R] (A : Type u) [Ring A] [Algebra R A] (s : LocallyConstant Y A) :
    f.cechCohomologyAlgebraPullback R A (TauCeti.Topology.cechCohomologyZeroAlgHom Y R A s) =
      TauCeti.Topology.cechCohomologyZeroAlgHom X R A (s.comap f.hom) := by
  rw [TauCeti.Topology.cechCohomologyZeroAlgHom_apply,
    TauCeti.Topology.cechCohomologyZeroAlgHom_apply, cechCohomologyAlgebraPullback_of]
  congr 1
  let sY : (TopCat.locallyConstantModulePresheaf Y R A).obj (op ⊤) :=
    s.comap ⟨Subtype.val, continuous_subtype_val⟩
  let sX : (TopCat.locallyConstantModulePresheaf X R A).obj (op ⊤) :=
    (s.comap f.hom).comap ⟨Subtype.val, continuous_subtype_val⟩
  have hY : TauCeti.Topology.locallyConstantCechCohomologyZeroEquiv Y R A s =
      TauCeti.Topology.cechCohomologyUnitClass Y (TopCat.locallyConstantModulePresheaf Y R A)
        (fun U ↦ (TopCat.locallyConstantModulePresheaf Y R A).map (homOfLE le_top).op sY)
        (fun _ ↦ by rw [← ModuleCat.comp_apply, ← Functor.map_comp]; rfl) :=
    TauCeti.Topology.cechCohomologyZeroIso_hom_eq_cechCohomologyUnitClass Y
      (TopCat.locallyConstantModuleSheaf Y R A) sY
  have hX : TauCeti.Topology.locallyConstantCechCohomologyZeroEquiv X R A (s.comap f.hom) =
      TauCeti.Topology.cechCohomologyUnitClass X (TopCat.locallyConstantModulePresheaf X R A)
        (fun U ↦ (TopCat.locallyConstantModulePresheaf X R A).map (homOfLE le_top).op sX)
        (fun _ ↦ by rw [← ModuleCat.comp_apply, ← Functor.map_comp]; rfl) :=
    TauCeti.Topology.cechCohomologyZeroIso_hom_eq_cechCohomologyUnitClass X
      (TopCat.locallyConstantModuleSheaf X R A) sX
  exact (congrArg (f.cechCohomologyPullback 0 (f.locallyConstantModulePullback R A)) hY).trans <|
    (f.cechCohomologyPullback_cechCohomologyUnitClass (f.locallyConstantModulePullback R A)
      _ _ _ _ fun V ↦ by
        rw [TopCat.locallyConstantModulePresheaf_map_apply,
          TopCat.locallyConstantModulePresheaf_map_apply,
          TopCat.Hom.locallyConstantModulePullback_app_apply]
        rfl).trans hX.symm

end AlgebraPullback

end TopCat.Hom

/-! ### Non-commutativity on Čech cocycles -/

namespace TauCeti.Topology

private lemma cechComplexπ_d_zero {X : TopCat.{u}} {R : Type uR} [CommRing R]
    {ι : Type u} (U : ι → Opens X) (P : X.Presheaf (ModuleCat.{u} R))
    (w : ((cechComplexFunctor U).obj P).X 0) (d : Fin 2 → ι) :
    cechComplexπ U P 1 d (((cechComplexFunctor U).obj P).d 0 1 w) =
      P.map (Limits.Pi.lift fun j : Fin 1 ↦
          Limits.Pi.π (fun k : Fin 2 ↦ U (d k)) (Fin.succAbove 0 j)).op
        (cechComplexπ U P 0 (d ∘ Fin.succAbove 0) w) -
      P.map (Limits.Pi.lift fun j : Fin 1 ↦
          Limits.Pi.π (fun k : Fin 2 ↦ U (d k)) (Fin.succAbove 1 j)).op
        (cechComplexπ U P 0 (d ∘ Fin.succAbove 1) w) := by
  have hm : ((cechComplexFunctor U).obj P).d 0 1 ≫ cechComplexπ U P 1 d =
      ∑ k : Fin 2, (-1 : ℤ) ^ (k : ℕ) •
        (cechComplexπ U P 0 (d ∘ k.succAbove) ≫
          P.map (Limits.Pi.lift fun j : Fin 1 ↦
            Limits.Pi.π (fun i : Fin 2 ↦ U (d i)) (k.succAbove j)).op) := by
    simp only [cechComplexπ_eq]
    exact cechComplexFunctor_obj_d_comp_π U P 0 d
  exact (ModuleCat.comp_apply _ _ w).symm.trans <| (ConcreteCategory.congr_hom hm w).trans <| by
    rw [Fin.sum_univ_two, Fin.val_zero, pow_zero, one_zsmul, Fin.val_one, pow_one,
      neg_one_zsmul, sub_eq_add_neg]
    simp only [ModuleCat.hom_add, ModuleCat.hom_neg, ModuleCat.hom_comp,
      LinearMap.add_apply, LinearMap.neg_apply, LinearMap.comp_apply]

/-- **The Čech cup product is not graded-commutative on cocycles.** On any nonempty space `X` and
nontrivial commutative `R`-algebra `A`, taking the three-element cover of `X` by copies of `⊤`,
there exist `1`-cocycles `a` and `b` whose cochain cup products `a ⌣ b` and `(-1)^(1 * 1) •
(b ⌣ a)` differ in `Č²(U, A_X)`. (They are cohomologous by `cechComplexCup_comm`.) -/
theorem exists_cechCupCochain_cocycles_not_gradedComm (X : TopCat.{u}) [Nonempty X]
    (R : Type uR) [CommRing R] (A : Type u) [CommRing A] [Algebra R A] [Nontrivial A] :
    let U : ULift.{u} (Fin 3) → Opens X := fun _ ↦ ⊤
    let P := TopCat.locallyConstantModulePresheaf X R A
    ∃ a b : ((cechComplexFunctor U).obj P).X 1,
      ((cechComplexFunctor U).obj P).d 1 2 a = 0 ∧
      ((cechComplexFunctor U).obj P).d 1 2 b = 0 ∧
      cechCupCochain U (TopCat.locallyConstantMul X R A) 1 1 2 rfl a b ≠
        (-1 : ℤ) ^ (1 * 1) • cechCupCochain U (TopCat.locallyConstantMul X R A) 1 1 2 rfl b a := by
  intro U P
  -- Take `a = d u` and `b = d v` where `u` is `1` on index `0` and `v` is `1` on index `2`.
  let u : ((cechComplexFunctor U).obj P).X 0 :=
    cechCochainMk U P 0 fun c ↦
      if c 0 = ULift.up 0 then TopCat.locallyConstantOne X R A _ else 0
  let v : ((cechComplexFunctor U).obj P).X 0 :=
    cechCochainMk U P 0 fun c ↦
      if c 0 = ULift.up 2 then TopCat.locallyConstantOne X R A _ else 0
  let a : ((cechComplexFunctor U).obj P).X 1 := ((cechComplexFunctor U).obj P).d 0 1 u
  let b : ((cechComplexFunctor U).obj P).X 1 := ((cechComplexFunctor U).obj P).d 0 1 v
  refine ⟨a, b, ?_, ?_, ?_⟩
  · exact (ModuleCat.comp_apply _ _ u).symm.trans <| by rw [HomologicalComplex.d_comp_d]; rfl
  · exact (ModuleCat.comp_apply _ _ v).symm.trans <| by rw [HomologicalComplex.d_comp_d]; rfl
  · intro heq
    -- Evaluate both sides on the simplex `c = (0, 1, 2)`: `a(0, 1) = -1`, `b(1, 2) = 1`, while
    -- `a(1, 2) = 0` and `b(0, 1) = 0`, so `(a ⌣ b)(0, 1, 2) = -1` and `-(b ⌣ a)(0, 1, 2) = 0`.
    let c : Fin 3 → ULift.{u} (Fin 3) := fun j ↦ ULift.up j
    have ha01 : cechComplexπ U P 1 (fun j : Fin 2 ↦ c ⟨j.val, by omega⟩) a =
        -TopCat.locallyConstantOne X R A _ := by
      rw [cechComplexπ_d_zero U P u]
      have h0 : ((fun j : Fin 2 ↦ c ⟨j.val, by omega⟩) ∘ Fin.succAbove 0) 0 = ULift.up.{u} 1 := rfl
      have h1 : ((fun j : Fin 2 ↦ c ⟨j.val, by omega⟩) ∘ Fin.succAbove 1) 0 = ULift.up.{u} 0 := rfl
      have hne : ULift.up.{u} (1 : Fin 3) ≠ ULift.up.{u} 0 := fun h ↦ by cases h
      simp only [u, P, cechComplexπ_cechCochainMk, h0, h1, hne, ↓reduceIte, map_zero, zero_sub]
      rfl
    have ha12 : cechComplexπ U P 1 (fun j : Fin 2 ↦ c ⟨1 + j.val, by omega⟩) a = 0 := by
      rw [cechComplexπ_d_zero U P u]
      have h0 : ((fun j : Fin 2 ↦ c ⟨1 + j.val, by omega⟩) ∘ Fin.succAbove 0) 0 =
          ULift.up.{u} 2 := rfl
      have h1 : ((fun j : Fin 2 ↦ c ⟨1 + j.val, by omega⟩) ∘ Fin.succAbove 1) 0 =
          ULift.up.{u} 1 := rfl
      have hne0 : ULift.up.{u} (2 : Fin 3) ≠ ULift.up.{u} 0 := fun h ↦ by cases h
      have hne1 : ULift.up.{u} (1 : Fin 3) ≠ ULift.up.{u} 0 := fun h ↦ by cases h
      simp only [u, cechComplexπ_cechCochainMk, h0, h1, hne0, hne1, ↓reduceIte, map_zero, sub_self]
    have hb01 : cechComplexπ U P 1 (fun j : Fin 2 ↦ c ⟨j.val, by omega⟩) b = 0 := by
      rw [cechComplexπ_d_zero U P v]
      have h0 : ((fun j : Fin 2 ↦ c ⟨j.val, by omega⟩) ∘ Fin.succAbove 0) 0 = ULift.up.{u} 1 := rfl
      have h1 : ((fun j : Fin 2 ↦ c ⟨j.val, by omega⟩) ∘ Fin.succAbove 1) 0 = ULift.up.{u} 0 := rfl
      have hne0 : ULift.up.{u} (1 : Fin 3) ≠ ULift.up.{u} 2 := fun h ↦ by cases h
      have hne1 : ULift.up.{u} (0 : Fin 3) ≠ ULift.up.{u} 2 := fun h ↦ by cases h
      simp only [v, cechComplexπ_cechCochainMk, h0, h1, hne0, hne1, ↓reduceIte, map_zero, sub_self]
    have hb12 : cechComplexπ U P 1 (fun j : Fin 2 ↦ c ⟨1 + j.val, by omega⟩) b =
        TopCat.locallyConstantOne X R A _ := by
      rw [cechComplexπ_d_zero U P v]
      have h0 : ((fun j : Fin 2 ↦ c ⟨1 + j.val, by omega⟩) ∘ Fin.succAbove 0) 0 =
          ULift.up.{u} 2 := rfl
      have h1 : ((fun j : Fin 2 ↦ c ⟨1 + j.val, by omega⟩) ∘ Fin.succAbove 1) 0 =
          ULift.up.{u} 1 := rfl
      have hne : ULift.up.{u} (1 : Fin 3) ≠ ULift.up.{u} 2 := fun h ↦ by cases h
      simp only [v, P, cechComplexπ_cechCochainMk, h0, h1, hne, ↓reduceIte, map_zero, sub_zero]
      rfl
    have hπeq := congrArg (cechComplexπ U P 2 c) heq
    rw [cechCupCochain_π, map_zsmul, cechCupCochain_π, ha01, ha12, hb01, hb12] at hπeq
    simp only [map_neg, LinearMap.neg_apply, map_zero,
      TopCat.locallyConstantModulePresheaf_map_one, smul_zero] at hπeq
    have htop : (∏ᶜ fun j : Fin 3 ↦ U (c j)) = ⊤ :=
      top_unique (leOfHom (Limits.Pi.lift fun _ ↦ homOfLE le_top))
    obtain ⟨x₀⟩ := ‹Nonempty X›
    have hx₀ : x₀ ∈ (∏ᶜ fun j : Fin 3 ↦ U (c j)) := htop.symm ▸ trivial
    have hval := DFunLike.congr_fun
      (F := LocallyConstant ↥(∏ᶜ fun j : Fin 3 ↦ U (c j)) A) hπeq ⟨x₀, hx₀⟩
    have hneg : -((1 : A) * 1) = 0 := hval
    rw [mul_one] at hneg
    exact neg_ne_zero.mpr one_ne_zero hneg

end TauCeti.Topology

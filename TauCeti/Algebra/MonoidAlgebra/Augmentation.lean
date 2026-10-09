/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.MonoidAlgebra.Module
public import Mathlib.RingTheory.Ideal.Maps

/-!
# The augmentation of a monoid algebra

The coefficient-sum augmentation `R[K] → R` sends each singleton `single k r` to `r`. It is
natural in the monoid `K` and is defined over any semiring `R`. As an `R`-linear map it is
surjective, and its kernel is the augmentation ideal with scalars restricted to `R`.

The augmentation gives the trivial action of `K` on `R` and is the counit of the monoid-algebra
bialgebra. Descriptions of its kernel by generators and the resulting exactness statements live
in `TauCeti.Algebra.MonoidAlgebra.Exactness`.

## Main declarations

* `TauCeti.MonoidAlgebra.augmentation`: the coefficient-sum ring homomorphism.
* `TauCeti.MonoidAlgebra.augmentation_comp_mapDomainRingHom`: naturality in the monoid.
* `TauCeti.MonoidAlgebra.augmentation_mapDomainRingEquiv`: invariance under monoid isomorphisms.
* `MonoidAlgebra.augmentationLinearMap`: the coefficient-sum linear map.
* `MonoidAlgebra.augmentationLinearMap_surjective`: surjectivity over any semiring.
* `MonoidAlgebra.ker_augmentationLinearMap`: the linear kernel is the augmentation ideal.

## References

* J. S. Milne, *Algebraic Groups* (2017), Theorem 12.9(b), for the augmentation of a group algebra.
-/

public section

universe u v w

namespace TauCeti.MonoidAlgebra

open _root_.MonoidAlgebra

variable (R : Type u) [Semiring R]

/-- The coefficient-sum augmentation of a monoid algebra. It sends every standard basis element
to `1` and acts identically on coefficients. -/
noncomputable def augmentation (K : Type v) [Monoid K] : MonoidAlgebra R K →+* R :=
  liftNCRingHom (.id R) 1 fun _ _ ↦ Commute.one_right _

/-- The coefficient-sum augmentation sends a singleton to its coefficient. -/
@[simp]
theorem augmentation_single {K : Type v} [Monoid K] (k : K) (r : R) :
    augmentation R K (single k r) = r := by
  simp [augmentation]

/-- The coefficient-sum augmentation is natural with respect to homomorphisms of monoids. -/
@[simp]
theorem augmentation_comp_mapDomainRingHom {M : Type v} {N : Type w} [Monoid M] [Monoid N]
    (f : M →* N) :
    (augmentation R N).comp (mapDomainRingHom R f) = augmentation R M := by
  apply ringHom_ext <;> intro <;> simp

/-- The coefficient-sum augmentation is invariant under an isomorphism of monoids. -/
@[simp]
theorem augmentation_mapDomainRingEquiv {M : Type v} {N : Type w} [Monoid M] [Monoid N]
    (e : M ≃* N) (x : MonoidAlgebra R M) :
    augmentation R N (mapDomainRingEquiv R e x) = augmentation R M x :=
  RingHom.congr_fun (augmentation_comp_mapDomainRingHom R (e : M →* N)) x

end TauCeti.MonoidAlgebra

namespace MonoidAlgebra

open TauCeti.MonoidAlgebra

variable (R : Type u) [Semiring R] (K : Type v) [Monoid K]

/-- The coefficient-sum augmentation as an `R`-linear map `R[K] → R`. -/
noncomputable def augmentationLinearMap :
    MonoidAlgebra R K →ₗ[R] R where
  toFun := augmentation R K
  map_add' := map_add _
  map_smul' r x := by
    induction x using induction_linear with
    | zero => simp
    | add x y hx hy => simp only [smul_add, map_add, hx, hy, RingHom.id_apply]
    | single k c => simp

@[simp]
theorem augmentationLinearMap_apply (x : MonoidAlgebra R K) :
    augmentationLinearMap R K x = augmentation R K x :=
  (rfl)

/-- Over any semiring, the coefficient-sum linear map is surjective. -/
theorem augmentationLinearMap_surjective :
    Function.Surjective (augmentationLinearMap R K) :=
  fun r ↦ ⟨single 1 r, by simp⟩

/-- The kernel of the linear augmentation is the augmentation ideal, with scalars restricted. -/
theorem ker_augmentationLinearMap :
    LinearMap.ker (augmentationLinearMap R K) =
      (RingHom.ker (augmentation R K)).restrictScalars R := by
  ext; simp [RingHom.mem_ker]

end MonoidAlgebra

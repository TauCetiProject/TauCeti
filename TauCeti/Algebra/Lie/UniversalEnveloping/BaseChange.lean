/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.BaseChange
public import TauCeti.Algebra.Lie.UniversalEnveloping.Basic

/-!
# Universal enveloping algebras under extension of scalars

Let `A` be a commutative `R`-algebra and `L` a Lie algebra over `R`. The canonical map
`x ↦ ι (1 ⊗ x)` from `L` to the universal enveloping algebra of the base change `A ⊗[R] L` over `A`
is a Lie homomorphism over `R`, so it induces a ring homomorphism
`U_R(L) →+* U_A(A ⊗[R] L)`.

Mathlib equips `UniversalEnvelopingAlgebra A (A ⊗[R] L)` with an `A`-algebra structure only, not an
`R`-algebra structure, so the map is bundled as a ring homomorphism (as `MvPolynomial.map` is) and
its `R`-linearity is the separate statement `baseChangeRingHom_smul`.

The canonical generators `ι (a ⊗ x) = a • ι (1 ⊗ x)` of `U_A(A ⊗[R] L)` are `A`-multiples of images
of generators of `U_R(L)`. Hence the map carries the centre of `U_R(L)` into the centre of
`U_A(A ⊗[R] L)`. This is the naturality of central elements under extension of scalars; it fails
for an arbitrary Lie homomorphism, whose image need not generate the target. It is used to
transport Hochschild's central `p`-polynomials along a field extension.

## Main definitions

* `UniversalEnvelopingAlgebra.baseChangeRingHom`: the ring homomorphism
  `U_R(L) →+* U_A(A ⊗[R] L)` sending `ι x` to `ι (1 ⊗ x)`.

## Main results

* `UniversalEnvelopingAlgebra.baseChangeRingHom_ι`: the characteristic equation on the
  canonical Lie generators.
* `UniversalEnvelopingAlgebra.baseChangeRingHom_unique`: it is the only ring homomorphism with
  these values on the Lie generators and the scalars.
* `UniversalEnvelopingAlgebra.baseChangeRingHom_smul`: the map is `R`-linear, `R` acting
  on the target through `algebraMap R A`.
* `UniversalEnvelopingAlgebra.baseChangeRingHom_mem_center`: central elements map to
  central elements.
-/

public section

namespace UniversalEnvelopingAlgebra

open TensorProduct

universe u v w

-- Mathlib does not register the Lie ring of an associative ring as a global instance; the
-- commutator of two elements of an enveloping algebra is written with it below.
attribute [local instance 100] LieRing.ofAssociativeRing

variable (R : Type u) (A : Type v) (L : Type w)
variable [CommRing R] [CommRing A] [Algebra R A] [LieRing L] [LieAlgebra R L]

section Lift

-- `R` acts on `U_A(A ⊗[R] L)` through `A`. Mathlib registers no such `R`-algebra structure, so the
-- lift defining `baseChangeRingHom` and the lemmas proved through it share this local one.
private noncomputable local instance algebraOfBaseChange :
    Algebra R (UniversalEnvelopingAlgebra A (A ⊗[R] L)) :=
  Algebra.compHom _ (algebraMap R A)

private local instance isScalarTowerOfBaseChange :
    IsScalarTower R A (UniversalEnvelopingAlgebra A (A ⊗[R] L)) :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl

/-- The Lie homomorphism `x ↦ ι (1 ⊗ x)` over `R` whose lift is `baseChangeRingHom`. -/
private noncomputable def baseChangeLieHom :
    L →ₗ⁅R⁆ UniversalEnvelopingAlgebra A (A ⊗[R] L) where
  toFun x := ι A ((1 : A) ⊗ₜ[R] x)
  map_add' x y := by rw [tmul_add, map_add]
  map_smul' r x := by
    rw [tmul_smul, ← algebraMap_smul A, map_smul, algebraMap_smul, RingHom.id_apply]
  map_lie' {x y} := by
    rw [← LieHom.map_lie, LieAlgebra.ExtendScalars.bracket_tmul, mul_one]

/-- The ring homomorphism `U_R(L) →+* U_A(A ⊗[R] L)` induced by the Lie homomorphism
`x ↦ ι (1 ⊗ x)`, for a commutative `R`-algebra `A`. It sends `ι x` to `ι (1 ⊗ x)` and
`algebraMap R _ r` to `algebraMap A _ (algebraMap R A r)`; see `baseChangeRingHom_ι` and
`baseChangeRingHom_algebraMap`, and `baseChangeRingHom_unique` for the uniqueness. -/
noncomputable def baseChangeRingHom :
    UniversalEnvelopingAlgebra R L →+*
      UniversalEnvelopingAlgebra A (A ⊗[R] L) :=
  (lift R (baseChangeLieHom R A L)).toRingHom

variable {R A L}

private theorem baseChangeRingHom_apply (u : UniversalEnvelopingAlgebra R L) :
    baseChangeRingHom R A L u = lift R (baseChangeLieHom R A L) u :=
  rfl

/-- `baseChangeRingHom` sends the canonical generator `ι x` to `ι (1 ⊗ x)`. -/
-- `simp`-normal form is `baseChangeRingHom_ι'`, since `simp` unfolds `ι` through `ι_apply`.
theorem baseChangeRingHom_ι (x : L) :
    baseChangeRingHom R A L (ι R x) =
      ι A ((1 : A) ⊗ₜ[R] x) := by
  rw [baseChangeRingHom_apply, lift_ι_apply]
  rfl

/-- `baseChangeRingHom` sends the scalar `r` of `U_R(L)` to the scalar `algebraMap R A r`. -/
@[simp]
theorem baseChangeRingHom_algebraMap (r : R) :
    baseChangeRingHom R A L (algebraMap R _ r) =
      algebraMap A _ (algebraMap R A r) := by
  rw [baseChangeRingHom_apply, AlgHom.commutes]
  rfl

/-- `baseChangeRingHom` is the only ring homomorphism `U_R(L) →+* U_A(A ⊗[R] L)` sending `ι x`
to `ι (1 ⊗ x)` and the scalar `r` to the scalar `algebraMap R A r`. -/
theorem baseChangeRingHom_unique
    (g : UniversalEnvelopingAlgebra R L →+* UniversalEnvelopingAlgebra A (A ⊗[R] L))
    (hι : ∀ x, g (ι R x) = ι A ((1 : A) ⊗ₜ[R] x))
    (halg : ∀ r, g (algebraMap R _ r) = algebraMap A _ (algebraMap R A r)) :
    g = baseChangeRingHom R A L := by
  have h : ({ g with commutes' := halg } : _ →ₐ[R] _) = lift R (baseChangeLieHom R A L) :=
    hom_ext R (LieHom.ext fun x => (hι x).trans (lift_ι_apply R (baseChangeLieHom R A L) x).symm)
  exact RingHom.ext fun u => congrArg (· u) h

end Lift

variable {R A L}

/-- The `simp`-normal form of `baseChangeRingHom_ι`, stated for the canonical generators as `simp`
writes them: `ι R x` unfolds to `mkAlgHom R L (TensorAlgebra.ι R x)`. -/
@[simp]
theorem baseChangeRingHom_ι' (x : L) :
    baseChangeRingHom R A L
        (mkAlgHom R L (TensorAlgebra.ι R x)) =
      mkAlgHom A (A ⊗[R] L)
        (TensorAlgebra.ι A ((1 : A) ⊗ₜ[R] x)) :=
  baseChangeRingHom_ι x

/-- `baseChangeRingHom` is `R`-linear, `R` acting on `U_A(A ⊗[R] L)` through `algebraMap R A`. -/
@[simp]
theorem baseChangeRingHom_smul (r : R) (u : UniversalEnvelopingAlgebra R L) :
    baseChangeRingHom R A L (r • u) = algebraMap R A r • baseChangeRingHom R A L u := by
  rw [Algebra.smul_def, map_mul, baseChangeRingHom_algebraMap, ← Algebra.smul_def]

/-- **Central elements stay central under extension of scalars.** If `u` is central in `U_R(L)`,
its image under `baseChangeRingHom` is central in `U_A(A ⊗[R] L)`. -/
theorem baseChangeRingHom_mem_center {u : UniversalEnvelopingAlgebra R L}
    (hu : u ∈ Subalgebra.center R (UniversalEnvelopingAlgebra R L)) :
    baseChangeRingHom R A L u ∈
      Subalgebra.center A (UniversalEnvelopingAlgebra A (A ⊗[R] L)) := by
  -- Test centrality on the generators `ι (a ⊗ x) = a • ι (1 ⊗ x)`, where `ι (1 ⊗ x)` is the
  -- image of `ι x`.
  rw [TauCeti.UniversalEnvelopingAlgebra.mem_center_iff_forall_lie_ι]
  intro t
  induction t using TensorProduct.inductionOn with
  | tmul a x =>
    have hx : Commute u (ι R x) := (Subalgebra.mem_center_iff.mp hu (ι R x)).symm
    have hax : a ⊗ₜ[R] x = a • ((1 : A) ⊗ₜ[R] x) := by rw [smul_tmul', smul_eq_mul, mul_one]
    rw [hax, map_smul, lie_smul, ← baseChangeRingHom_ι, LieRing.of_associative_ring_bracket,
      (hx.map (baseChangeRingHom R A L)).eq, sub_self, smul_zero]
  | add s t hs ht => rw [map_add, lie_add, hs, ht, add_zero]

end UniversalEnvelopingAlgebra

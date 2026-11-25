/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.Opposite
public import TauCeti.RepresentationTheory.OfMulAction.CosetLift
public import TauCeti.RepresentationTheory.OfMulAction.Hecke

/-!
# The Hecke algebra of a level and its right action on invariants

For a subgroup `U` of a group `G` (in practice a compact open subgroup of a locally profinite
group) and a commutative ring `A`, the **Hecke algebra of level `U`** is
`H(G, U; A) := Fun_G(G/U × G/U, A)`, the permutation Hecke algebra
(`TauCeti.permutationHeckeModule`) of the coset space `G ⧸ U`. Since `G` permutes `G ⧸ U`
transitively, it is a unital `A`-algebra as soon as the stabilizer orbits are finite
(`TauCeti.FiniteStabilizerOrbits`), for instance for `U` compact open
(`TauCeti.FiniteStabilizerOrbits.of_isCompact_of_isOpen`), and it is isomorphic to
`End_G(A[G/U])` (`TauCeti.PermutationHecke.toIntertwiningMapAlgEquiv`). No measure is used, so it
is defined over every coefficient ring.

For a representation `ρ` of `G` on `V`, the `U`-invariants are the intertwining maps
`A[G/U] → V` (`Representation.ofMulActionQuotientMapEquiv`), and precomposition with the action of
`H(G, U; A)` on `A[G/U]` makes `V^U` a right `H(G, U; A)`-module: an algebra homomorphism
`H(G, U; A)ᵐᵒᵖ →ₐ[A] End_A(V^U)` (`TauCeti.HeckeAlgebraLevel.rightAction`). Explicitly, `v * h` is
`∑_t h(t, U) ρ(g_t) v` over the cosets `t = g_t U`
(`TauCeti.HeckeAlgebraLevel.coe_rightAction_apply`).

## Main definitions

* `TauCeti.HeckeAlgebraLevel G U A`: the Hecke algebra `H(G, U; A)`.
* `TauCeti.HeckeAlgebraLevel.rightAction ρ`: the right action of `H(G, U; A)` on `V^U`.

## References

* D. Treumann and A. Venkatesh, *Functoriality, Smith theory, and the Brauer homomorphism*,
  Ann. of Math. 183 (2016), §2.10, (2.10.1)–(2.10.3), pp. 187–188 (arXiv:1407.2346v1 §2.10).
-/

public section
noncomputable section

open MulAction Representation

namespace TauCeti

variable (G : Type*) [Group G] (U : Subgroup G) (A : Type*) [CommRing A]

/-- The **Hecke algebra of level `U`**, `H(G, U; A) = Fun_G(G/U × G/U, A)`: the permutation Hecke
algebra of the coset space `G ⧸ U`. -/
abbrev HeckeAlgebraLevel : Type _ :=
  permutationHeckeModule G (G ⧸ U) A

/-- `G` permutes the cosets `G ⧸ U` transitively, so there is a single orbit. -/
instance finite_orbitRel_quotient_quotient : Finite (orbitRel.Quotient G (G ⧸ U)) :=
  haveI := (pretransitive_iff_subsingleton_quotient G (G ⧸ U)).1 inferInstance
  inferInstance

namespace HeckeAlgebraLevel

variable {G U A} [FiniteStabilizerOrbits G (G ⧸ U)]
  {V : Type*} [AddCommGroup V] [Module A V] (ρ : Representation A G V)

/-- Precomposition with the action of `h` on `A[G ⧸ U]`, on intertwining maps `A[G ⧸ U] → V`. -/
private def precomp :
    HeckeAlgebraLevel G U A →ₗ[A] Module.End A (IntertwiningMap (ofMulAction A G (G ⧸ U)) ρ) where
  toFun h :=
    { toFun φ := φ.comp (PermutationHecke.toIntertwiningMap G (G ⧸ U) A h)
      map_add' _ _ := IntertwiningMap.ext (LinearMap.ext fun _ ↦ rfl)
      map_smul' _ _ := IntertwiningMap.ext (LinearMap.ext fun _ ↦ rfl) }
  map_add' _ _ := LinearMap.ext fun φ ↦ IntertwiningMap.ext (LinearMap.ext fun _ ↦ by simp)
  map_smul' _ _ := LinearMap.ext fun φ ↦ IntertwiningMap.ext (LinearMap.ext fun _ ↦ by simp)

private theorem precomp_apply (h : HeckeAlgebraLevel G U A)
    (φ : IntertwiningMap (ofMulAction A G (G ⧸ U)) ρ) :
    precomp ρ h φ = φ.comp (PermutationHecke.toIntertwiningMap G (G ⧸ U) A h) :=
  rfl

private theorem precomp_one : precomp ρ (1 : HeckeAlgebraLevel G U A) = 1 :=
  LinearMap.ext fun φ ↦ IntertwiningMap.ext (LinearMap.ext fun x ↦ by
    simp [precomp_apply])

private theorem precomp_mul (h₁ h₂ : HeckeAlgebraLevel G U A) :
    precomp ρ (h₁ * h₂) = precomp ρ h₂ * precomp ρ h₁ :=
  LinearMap.ext fun φ ↦ IntertwiningMap.ext (LinearMap.ext fun x ↦ by
    simp [precomp_apply])

/-- **`V^U` is a right `H(G, U; A)`-module.** Identifying `V^U` with the intertwining maps
`A[G ⧸ U] → V`, `h` acts by precomposition with its action on `A[G ⧸ U]`. -/
def rightAction : (HeckeAlgebraLevel G U A)ᵐᵒᵖ →ₐ[A] Module.End A (invariants (ρ.comp U.subtype)) :=
  AlgHom.ofLinearMap
    ((ρ.ofMulActionQuotientMapEquiv U).conj.toLinearMap ∘ₗ precomp ρ ∘ₗ
      (MulOpposite.opLinearEquiv A).symm.toLinearMap)
    (LinearMap.ext fun v ↦ by simp [LinearEquiv.conj_apply_apply, precomp_one])
    fun h₁ h₂ ↦ LinearMap.ext fun v ↦ by
      simp [LinearEquiv.conj_apply_apply, precomp_mul]

/-- `v * h` is `φ_v (h * [U])`, where `φ_v : A[G ⧸ U] → V` is the intertwining map sending the
coset `g U` to `ρ g v`. -/
theorem coe_rightAction_apply_eq (h : HeckeAlgebraLevel G U A)
    (v : invariants (ρ.comp U.subtype)) :
    (rightAction ρ (MulOpposite.op h) v : V) = (ρ.ofMulActionQuotientMapEquiv U).symm v
      (PermutationHecke.toIntertwiningMap G (G ⧸ U) A h
        (MonoidAlgebra.single ((1 : G) : G ⧸ U) 1)) := by
  simp [rightAction, LinearEquiv.conj_apply_apply, precomp_apply, IntertwiningMap.comp_apply]

/-- **The right action explicitly**: `v * h = ∑_t h(t, U) ρ(g_t) v`, the sum over the cosets
`t = g_t U` in the support of the column of `h` at the coset `U`. -/
theorem coe_rightAction_apply (h : HeckeAlgebraLevel G U A) (v : invariants (ρ.comp U.subtype)) :
    (rightAction ρ (MulOpposite.op h) v : V) =
      (PermutationHecke.column h ((1 : G) : G ⧸ U)).sum fun t c ↦ c • ρ t.out v := by
  have hcol : PermutationHecke.toIntertwiningMap G (G ⧸ U) A h
      (MonoidAlgebra.single ((1 : G) : G ⧸ U) 1) =
        (PermutationHecke.column h ((1 : G) : G ⧸ U)).sum fun t c ↦ MonoidAlgebra.single t c := by
    apply MonoidAlgebra.coeff_injective
    ext t
    simp only [PermutationHecke.coeff_toIntertwiningMap_apply, MonoidAlgebra.coeff_single,
      PermutationHecke.toEnd_single, one_mul, Finsupp.sum, MonoidAlgebra.coeff_sum]
    rw [Finsupp.finsetSum_apply, Finset.sum_eq_single t
      (fun x _ hx ↦ by simp [hx])
      (fun ht ↦ by simpa using Finsupp.notMem_support_iff.1 ht)]
    simp
  rw [coe_rightAction_apply_eq, hcol, map_finsuppSum]
  refine Finsupp.sum_congr fun t _ ↦ ?_
  have := ofMulActionQuotientMapEquiv_symm_apply_single ρ U v t.out
    (PermutationHecke.column h ((1 : G) : G ⧸ U) t)
  rwa [QuotientGroup.out_eq'] at this

end HeckeAlgebraLevel

end TauCeti

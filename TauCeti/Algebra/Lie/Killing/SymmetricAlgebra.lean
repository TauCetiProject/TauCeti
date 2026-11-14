/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Killing.DualBasis
public import TauCeti.Algebra.Lie.Killing.Duality
public import TauCeti.LinearAlgebra.SymmetricAlgebra.LieModule

/-!
# The Killing identification of `S(L)` with the polynomial functions on `L`

Let `L` be a finite-dimensional Lie algebra over a field `K` whose Killing form `κ` is
nondegenerate. The Killing form is invariant, `κ ⁅x, y⁆ z = -κ y ⁅x, z⁆`, so `x ↦ κ x` is an
equivalence of Lie modules from the adjoint module `L` to the coadjoint module `L*`. It induces an
algebra equivalence from the symmetric algebra `S(L)` to the algebra `S(L*)` of polynomial
functions on `L`, sending a generator `x` to the linear function `κ x`, and this equivalence
intertwines the adjoint action of `L` on `S(L)` with the coadjoint action on `S(L*)`. Hence it
carries the adjoint invariants `S(L)^L` onto the invariant polynomial functions `S(L*)^L`.

This is the identification under which polynomial functions on `L`, such as the trace
polynomials `x ↦ tr (ρ(x) ^ m)` of a representation `ρ`, are compared with the leading symbols of
central elements of the enveloping algebra, which live in `S(L)^L`, in the proof of the
Harish-Chandra isomorphism by Chevalley's restriction theorem.

Choosing a basis `xᵢ` of `L` and its Killing-dual basis `yᵢ`, the **quadratic symmetric Casimir**
`∑ᵢ xᵢ yᵢ ∈ S²(L)` (`TauCeti.symmetricCasimir`) is independent of the basis, homogeneous of degree
two, and evaluates under `κ(v, ·)` to `κ(v, v)`. Away from characteristic two it is nonzero
whenever `L` is nontrivial; in characteristic two the Killing form is alternating, so the sum
vanishes in `S²(L)`.

## Main definitions

* `TauCeti.killingSymmetricEquiv`: the algebra equivalence `S(L) ≃ S(L*)` induced by the Killing
  duality `TauCeti.killingDuality : L ≃ L*` of `TauCeti/Algebra/Lie/Killing/Duality.lean`.
* `TauCeti.symmetricCasimir`: the quadratic Casimir tensor `∑ᵢ xᵢ yᵢ ∈ S(L)`.

## Main results

* `TauCeti.killingSymmetricEquiv_ι`: a generator `x` goes to the linear function `κ x`.
* `TauCeti.killingSymmetricEquiv_symm_ι`: conversely, a linear function `f` goes back to the
  generator `x` with `κ x = f`.
* `TauCeti.killingSymmetricEquiv_lieModuleDerivation`: the equivalence intertwines the adjoint
  action on `S(L)` with the coadjoint action on `S(L*)`.
* `TauCeti.map_killingSymmetricEquiv_lieInvariants`: it carries the invariants `S(L)^L` onto the
  invariant polynomial functions `S(L*)^L`.
* `TauCeti.symmetricCasimir_eq_sum`, `TauCeti.symmetricCasimir_mem_homogeneousSubmodule`,
  `TauCeti.lift_killingForm_symmetricCasimir`, `TauCeti.symmetricCasimir_ne_zero`: basis
  independence, degree-two homogeneity, Killing evaluation, and nonvanishing of `symmetricCasimir`.

## References

* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, GTM 9, §23.1 and
  §23.3.
* J. Dixmier, *Enveloping Algebras*, §7.3.
-/

public section

namespace TauCeti

open LieAlgebra Module _root_.SymmetricAlgebra TauCeti.SymmetricAlgebra

variable (K L : Type*) [Field K] [LieRing L] [LieAlgebra K L] [FiniteDimensional K L]
  [IsKilling K L]

/-- The algebra equivalence of the symmetric algebra `S(L)` with the algebra `S(L*)` of polynomial
functions on `L` induced by the Killing duality. -/
noncomputable def killingSymmetricEquiv :
    SymmetricAlgebra K L ≃ₐ[K] SymmetricAlgebra K (Dual K L) :=
  mapEquiv K (killingDuality K L : L ≃ₗ[K] Dual K L)

/-- The Killing equivalence `S(L) ≃ S(L*)` is the symmetric-algebra map of the Killing form,
read as a linear map `L → L*`. -/
theorem killingSymmetricEquiv_apply (p : SymmetricAlgebra K L) :
    killingSymmetricEquiv K L p = map K (killingForm K L) p := by
  rw [killingSymmetricEquiv, mapEquiv_apply, toLinearMap_killingDuality]

/-- The Killing equivalence `S(L) ≃ S(L*)` sends a generator `x` to the linear function `κ x`. -/
@[simp]
theorem killingSymmetricEquiv_ι (x : L) :
    killingSymmetricEquiv K L (ι K L x) = ι K (Dual K L) (killingForm K L x) := by
  rw [killingSymmetricEquiv_apply, map_apply_ι]

/-- The inverse of the Killing equivalence `S(L) ≃ S(L*)` is the symmetric-algebra equivalence
induced by the inverse of the Killing duality. -/
theorem killingSymmetricEquiv_symm :
    (killingSymmetricEquiv K L).symm =
      mapEquiv K ((killingDuality K L).symm : Dual K L ≃ₗ[K] L) := by
  rw [killingSymmetricEquiv, mapEquiv_symm]
  exact congrArg (mapEquiv K) <|
    LinearEquiv.ext fun f ↦ (killingDuality K L : L ≃ₗ[K] Dual K L).injective (by simp)

/-- The inverse of the Killing equivalence `S(L) ≃ S(L*)` sends a linear function `f` to the
generator `x` with `κ x = f`. -/
@[simp]
theorem killingSymmetricEquiv_symm_ι (f : Dual K L) :
    (killingSymmetricEquiv K L).symm (ι K (Dual K L) f) = ι K L ((killingDuality K L).symm f) := by
  rw [killingSymmetricEquiv_symm, mapEquiv_ι, LieModuleEquiv.coe_toLinearEquiv]

/-- **The Killing equivalence intertwines the adjoint and coadjoint actions**: it carries the
adjoint derivation of `x` on `S(L)` to the coadjoint derivation of `x` on `S(L*)`. -/
theorem killingSymmetricEquiv_lieModuleDerivation (x : L) (p : SymmetricAlgebra K L) :
    killingSymmetricEquiv K L (lieModuleDerivation K L L x p) =
      lieModuleDerivation K L (Dual K L) x (killingSymmetricEquiv K L p) := by
  rw [killingSymmetricEquiv, mapEquiv_apply, mapEquiv_apply]
  exact (killingDuality K L).map_apply_lieModuleDerivation x p

/-- An element of `S(L)` is invariant exactly when its image in `S(L*)` under the Killing
equivalence is an invariant polynomial function. -/
@[simp]
theorem killingSymmetricEquiv_mem_lieInvariants_iff {p : SymmetricAlgebra K L} :
    killingSymmetricEquiv K L p ∈ lieInvariants K L (Dual K L) ↔ p ∈ lieInvariants K L L := by
  rw [killingSymmetricEquiv, mapEquiv_apply]
  exact (killingDuality K L).map_mem_lieInvariants_iff

/-- **The Killing equivalence identifies the invariants**: it carries `S(L)^L` onto the invariant
polynomial functions `S(L*)^L`. -/
theorem map_killingSymmetricEquiv_lieInvariants :
    (lieInvariants K L L).map
        (killingSymmetricEquiv K L : SymmetricAlgebra K L →ₐ[K] SymmetricAlgebra K (Dual K L)) =
      lieInvariants K L (Dual K L) := by
  rw [killingSymmetricEquiv, ← (killingDuality K L).map_lieInvariants, ← mapEquiv_toAlgHom]

/-! ### The quadratic symmetric Casimir -/

/-- Multiplying two canonical generators of `S(L)`, as a `K`-bilinear map. -/
private noncomputable def symGenMul :
    L →ₗ[K] L →ₗ[K] SymmetricAlgebra K L :=
  (LinearMap.mul K (SymmetricAlgebra K L)).compl₁₂ (ι K L) (ι K L)

omit [FiniteDimensional K L] [IsKilling K L] in
private theorem symGenMul_apply (x y : L) : symGenMul K L x y = ι K L x * ι K L y := by
  simp only [symGenMul, LinearMap.compl₁₂_apply, LinearMap.mul_apply']

/-- **The quadratic symmetric Casimir** `∑ᵢ xᵢ yᵢ ∈ S(L)` built from a basis `x` of `L` and its
Killing-dual basis `y`. It is the degree-two PBW symbol of the Casimir element of `U(L)`. -/
noncomputable def symmetricCasimir : SymmetricAlgebra K L :=
  ∑ i, ι K L (Module.finBasis K L i) * ι K L (killingDualBasis (Module.finBasis K L) i)

variable {K L} in
/-- **The quadratic symmetric Casimir may be computed in any basis.** -/
theorem symmetricCasimir_eq_sum {ι' : Type*} [DecidableEq ι'] [Fintype ι']
    (b : Module.Basis ι' K L) :
    symmetricCasimir K L = ∑ i, ι K L (b i) * ι K L (killingDualBasis b i) := by
  simp only [symmetricCasimir, ← symGenMul_apply]
  exact (symGenMul K L).sum_apply_dualBasis_eq _ (Module.finBasis K L) b

/-- **The quadratic symmetric Casimir is homogeneous of degree two.** -/
theorem symmetricCasimir_mem_homogeneousSubmodule :
    symmetricCasimir K L ∈ homogeneousSubmodule K L 2 := by
  refine Submodule.sum_mem _ fun i _ ↦ ?_
  simpa using SetLike.mul_mem_graded
    (ι_mem_homogeneousSubmodule K L (Module.finBasis K L i))
    (ι_mem_homogeneousSubmodule K L (killingDualBasis (Module.finBasis K L) i))

/-- **Evaluating the quadratic symmetric Casimir at `κ(v, ·)` gives `κ(v, v)`.** -/
@[simp]
theorem lift_killingForm_symmetricCasimir (v : L) :
    lift (killingForm K L v) (symmetricCasimir K L) = killingForm K L v v := by
  set b := Module.finBasis K L
  have hnd := IsKilling.killingForm_nondegenerate K L
  rw [symmetricCasimir_eq_sum b]
  simp only [map_sum, map_mul, lift_ι_apply]
  simp only [← smul_eq_mul, ← map_smul, ← map_sum]
  rw [LinearMap.BilinForm.sum_apply_smul_dualBasis hnd b v]

/-- **Away from characteristic two, the quadratic symmetric Casimir of a nontrivial Lie algebra is
nonzero.** In characteristic two the Killing form is alternating, so `∑ᵢ xᵢ yᵢ` vanishes in
`S²(L)`. -/
theorem symmetricCasimir_ne_zero [NeZero (2 : K)] [Nontrivial L] :
    symmetricCasimir K L ≠ 0 := by
  intro h0
  have hdiag (v : L) : killingForm K L v v = 0 := by
    rw [← lift_killingForm_symmetricCasimir K L v, h0, map_zero]
  have hbil (u w : L) : killingForm K L u w = 0 := by
    have hpol : killingForm K L (u + w) (u + w) =
        killingForm K L u u + 2 * killingForm K L u w + killingForm K L w w := by
      simp only [map_add, LinearMap.add_apply, LieModule.traceForm_comm K L L w u]
      ring
    rw [hdiag, hdiag, hdiag] at hpol
    exact (mul_eq_zero.1 (by linear_combination -hpol)).resolve_left (NeZero.ne (2 : K))
  obtain ⟨u, hu⟩ := exists_ne (0 : L)
  exact hu ((IsKilling.killingForm_nondegenerate K L).1 u (hbil u))

end TauCeti

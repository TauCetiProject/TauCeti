/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.ModuleCat.CartanMap.Basic
public import TauCeti.LinearAlgebra.Matrix.ToLin
public import TauCeti.RingTheory.CyclicCohomology.EvenPairing.Invariance

/-!
# The even pairing on algebraic `K₀`

Let `A` be a unital algebra over a field `R` of characteristic zero and `M` an `R`-module.
Algebraic `K₀(A)` is the Grothendieck group `K₀(proj A)` of finitely generated projective left
`A`-modules, `TauCeti.ExactK0 (TauCeti.finiteProjectiveModulesExactStructure A)`: the group
completion of the isomorphism classes under direct sum. This file shows that Connes' even pairing
of idempotent matrices with cyclic cohomology descends to a homomorphism

```text
K₀(proj A) → Hom_R(HC²ᵐ(A; M), M),   [A^ι e] ↦ (c ↦ ⟨[e], c⟩).
```

Here an idempotent matrix `e : Matrix ι ι A` acts on row vectors by `v ↦ v ᵥ* e`, and its image
`A^ι e` is a finitely generated projective left module. Conversely, every finitely generated
projective module `P` is a direct summand `s ∘ i = id` of some `A^ι`, and is isomorphic to the image
of the idempotent matrix of `i ∘ s`.

The pairing is well defined because two idempotent matrices with isomorphic images factor as
`e = a * b` and `f = b * a` through the matrices of the isomorphism and its inverse, so they have
the same pairing by `TauCeti.cyclicCohomology.evenPairing_matrixExtension_eq_of_mul_eq`. It is
additive because a split short exact sequence of projectives presents its middle term by the
block-diagonal sum of idempotents presenting the outer terms, and the even pairing is additive on
block sums.

## Main definitions

* `TauCeti.cyclicCohomology.evenPairingK0`: the even pairing
  `K₀(proj A) →+ (HC²ᵐ(A; M) →ₗ[R] M)`.

## Main results

* `TauCeti.cyclicCohomology.evenPairingK0_of_linearEquiv_range`: the class of a finitely generated
  projective module isomorphic to the image `A^ι e` of an idempotent matrix `e` pairs with a cyclic
  cohomology class `c` as Connes' pairing `⟨[e], c⟩` of `e` with `c`.

## References

* A. Connes, *Noncommutative Geometry*, Chapter III, §3.
* J.-L. Loday, *Cyclic Homology*, §8.3.
* J. Rosenberg, *Algebraic K-Theory and Its Applications*, Chapter 1, for projective modules as
  images of idempotent matrices.
-/

public section

noncomputable section

namespace TauCeti

open CategoryTheory

universe u

variable {R : Type*} {A : Type u} {M : Type*} [Field R] [CharZero R] [Ring A] [Algebra R A]
  [AddCommGroup M] [Module R M]

namespace cyclicCohomology

section Presentation

variable {P Q : Type*} [AddCommGroup P] [Module A P] [AddCommGroup Q] [Module A Q]

/-- The pairing of the idempotent attached to a direct summand `s ∘ i = id` of `A^ι`. -/
private def summandPairing {ι : Type*} [Fintype ι] [DecidableEq ι] {s : (ι → A) →ₗ[A] P}
    {i : P →ₗ[A] ι → A} (h : s ∘ₗ i = LinearMap.id) (m : ℕ) :
    cyclicCohomology R A M (2 * m) →ₗ[R] M :=
  (evenPairing _ (LinearMap.isIdempotentElem_toMatrixRight'_comp h) m).comp
    (matrixExtension M ι (2 * m))

/-- Isomorphic direct summands of free modules have Murray–von Neumann equivalent idempotents,
hence the same pairing. -/
private theorem summandPairing_eq_of_linearEquiv {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] {s : (ι → A) →ₗ[A] P} {i : P →ₗ[A] ι → A}
    (h : s ∘ₗ i = LinearMap.id) {s' : (κ → A) →ₗ[A] Q} {i' : Q →ₗ[A] κ → A}
    (h' : s' ∘ₗ i' = LinearMap.id) (θ : P ≃ₗ[A] Q) (m : ℕ) :
    summandPairing (R := R) (M := M) h m = summandPairing h' m := by
  have hsi (x : P) : s (i x) = x := LinearMap.congr_fun h x
  have hsi' (y : Q) : s' (i' y) = y := LinearMap.congr_fun h' y
  refine LinearMap.ext fun c ↦ evenPairing_matrixExtension_eq_of_mul_eq _ _
    (a := (i' ∘ₗ θ.toLinearMap ∘ₗ s).toMatrixRight')
    (b := (i ∘ₗ θ.symm.toLinearMap ∘ₗ s').toMatrixRight') ?_ ?_ m c <;>
  · rw [← LinearMap.toMatrixRight'_comp]
    exact congrArg _ (LinearMap.ext fun x ↦ by simp [hsi, hsi'])

end Presentation

/-- The pairing of a finitely generated projective module, computed from a chosen presentation as
a direct summand of some `A^n`. -/
private def objPairing (m : ℕ) (X : (finiteProjectiveModules A).FullSubcategory) :
    cyclicCohomology R A M (2 * m) →ₗ[R] M :=
  summandPairing (Module.Finite.exists_comp_eq_id_of_projective A
    X.obj).choose_spec.choose_spec.choose_spec.2.2 m

private theorem objPairing_eq {X : (finiteProjectiveModules A).FullSubcategory} {P : Type*}
    [AddCommGroup P] [Module A P] (θ : X.obj ≃ₗ[A] P) {ι : Type*} [Fintype ι] [DecidableEq ι]
    {s : (ι → A) →ₗ[A] P} {i : P →ₗ[A] ι → A} (h : s ∘ₗ i = LinearMap.id) (m : ℕ) :
    objPairing (R := R) (M := M) m X = summandPairing h m :=
  summandPairing_eq_of_linearEquiv _ h θ m

/-- The pairing of finitely generated projective modules is additive on split short exact
sequences, which are all the conflations of `finiteProjectiveModulesExactStructure A`. -/
private theorem objPairing_conflation (m : ℕ)
    {S : ShortComplex (finiteProjectiveModules A).FullSubcategory}
    (hS : (finiteProjectiveModulesExactStructure A).Conflation S) :
    objPairing (R := R) (M := M) m S.X₂ = objPairing m S.X₁ + objPairing m S.X₃ := by
  rw [finiteProjectiveModulesExactStructure_eq_split] at hS
  obtain ⟨σ⟩ := (ExactStructure.split_conflation S).1 hS
  -- Pass to the underlying split short exact sequence of modules.
  let T := S.map (finiteProjectiveModules A).ι
  let σ' : T.Splitting := σ.map (finiteProjectiveModules A).ι
  obtain ⟨n₁, s₁, i₁, -, -, h₁⟩ := Module.Finite.exists_comp_eq_id_of_projective A S.X₁.obj
  obtain ⟨n₃, s₃, i₃, -, -, h₃⟩ := Module.Finite.exists_comp_eq_id_of_projective A S.X₃.obj
  obtain ⟨s₂, i₂, h₂, hblock⟩ := LinearMap.exists_toMatrixRight'_comp_eq_fromBlocks
    (congrArg ModuleCat.Hom.hom σ'.f_r) (congrArg ModuleCat.Hom.hom σ'.s_g)
    (congrArg ModuleCat.Hom.hom σ'.id) (congrArg ModuleCat.Hom.hom T.zero)
    (congrArg ModuleCat.Hom.hom σ'.s_r) h₁ h₃
  rw [objPairing_eq (LinearEquiv.refl A _) h₂, objPairing_eq (LinearEquiv.refl A _) h₁,
    objPairing_eq (LinearEquiv.refl A _) h₃]
  refine LinearMap.ext fun c ↦ ?_
  simp only [summandPairing, LinearMap.comp_apply, LinearMap.add_apply]
  rw [← evenPairing_fromBlocks_matrixExtension]
  simp only [hblock]

variable (R M) in
/-- **Connes' even pairing on algebraic `K₀`.** The class of a finitely generated projective
module isomorphic to the image `A^ι e` of an idempotent matrix `e` is sent to the pairing
`c ↦ ⟨[e], c⟩` of `e` with cyclic cohomology classes of degree `2m`; see
`TauCeti.cyclicCohomology.evenPairingK0_of_linearEquiv_range`. -/
def evenPairingK0 (m : ℕ) :
    ExactK0.{u} (finiteProjectiveModulesExactStructure A) →+
      (cyclicCohomology R A M (2 * m) →ₗ[R] M) :=
  ExactK0.lift { obj := objPairing m, map_conflation := fun _ hS ↦ objPairing_conflation m hS }

private theorem evenPairingK0_of (m : ℕ) (X : (finiteProjectiveModules A).FullSubcategory) :
    evenPairingK0 R M m (ExactK0.of X) = objPairing m X :=
  ExactK0.lift_of.{u} _ X

/-- **Connes' even pairing on algebraic `K₀` is computed by idempotent matrices.** If a finitely
generated projective module `P` is isomorphic to the image `A^ι e` of an idempotent matrix `e`,
acting on row vectors, then `[P]` pairs with a cyclic cohomology class `c` of degree `2m` as
`⟨[e], c⟩ = (m!)⁻¹ (φ#Tr)(e, …, e)` for any cocycle `φ` representing `c`. -/
theorem evenPairingK0_of_linearEquiv_range {ι : Type*} [Fintype ι] [DecidableEq ι]
    {e : Matrix ι ι A} (he : IsIdempotentElem e) (P : (finiteProjectiveModules A).FullSubcategory)
    (θ : P.obj ≃ₗ[A] LinearMap.range e.toLinearMapRight') (m : ℕ) :
    evenPairingK0 R M m (ExactK0.of P) =
      (evenPairing e he m).comp (matrixExtension M ι (2 * m)) := by
  -- The image of `e` is a direct summand of `A^ι`, with idempotent `e` itself.
  have hsub : e.toLinearMapRight'.rangeRestrict ∘ₗ (LinearMap.range e.toLinearMapRight').subtype =
      LinearMap.id := by
    refine LinearMap.ext fun ⟨_, v, rfl⟩ ↦ Subtype.ext ?_
    simp [Matrix.vecMul_vecMul, he.eq]
  rw [evenPairingK0_of, objPairing_eq θ hsub]
  simp only [summandPairing, LinearMap.subtype_comp_rangeRestrict, LinearEquiv.apply_symm_apply]

end cyclicCohomology

end TauCeti

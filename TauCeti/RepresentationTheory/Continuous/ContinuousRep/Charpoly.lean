/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Charpoly.BaseChange
public import TauCeti.RepresentationTheory.Continuous.ContinuousRep.Continuity
import TauCeti.LinearAlgebra.Charpoly.Comp
import TauCeti.Topology.Instances.Matrix

/-!
# Characteristic polynomials of continuous representations

For a continuous representation `ρ : ContinuousRep Γ A M` on a finite free module `M` over a
commutative ring `A`, the characteristic polynomial at `g : Γ` is
`ρ.charpoly g := (ρ g).charpoly = det(X - ρ(g)) ∈ A[X]`.

On the algebraic side, `ρ.charpoly g` is monic of degree `Module.finrank A M` (for nontrivial `A`),
annihilates `ρ g` by Cayley–Hamilton, is `1` on a subsingleton carrier, equals `X - C (χ g)` on the
rank-one representation `ofCharacter χ` (recording the covariant convention `g ↦ χ(g)`, not the
contragredient `χ(g)⁻¹`), is invariant under isomorphism of representations and cyclic permutation
`charpoly(g h) = charpoly(h g)` (hence conjugation in a group), and commutes with continuous scalar
extension (`charpoly_baseChange`).

On the topological side, when `A` is a topological commutative ring and `M` carries its `A`-module
topology, every coefficient `g ↦ (ρ.charpoly g).coeff k` is continuous
(`continuous_coeff_charpoly`): in any finite basis of `M` the matrix entries of `ρ g` vary
continuously, and each characteristic coefficient is a universal polynomial in those entries
(`Matrix.continuous_charpoly_coeff`). As a consequence, two continuous representations whose
characteristic polynomials agree (after mapping into a common Hausdorff ring) on a dense subset of
`Γ` have the same characteristic polynomials everywhere (`charpoly_map_eq_of_dense`,
`charpoly_eq_of_dense`).

## Main definitions

* `TauCeti.ContinuousRep.charpoly`: the characteristic polynomial `det(X - ρ(g)) ∈ A[X]` of `ρ` at
  `g : Γ` on a finite free carrier.

## Main results

* `TauCeti.ContinuousRep.Iso.charpoly_eq`: isomorphic continuous representations have equal
  characteristic polynomials.
* `TauCeti.ContinuousRep.charpoly_ofCharacter`: `(ofCharacter χ).charpoly g = X - C (χ g)`.
* `TauCeti.ContinuousRep.charpoly_baseChange`:
  `(ρ.baseChange B).charpoly g = (ρ.charpoly g).map (algebraMap A B)`.
* `TauCeti.ContinuousRep.continuous_coeff_charpoly`: each coefficient `g ↦ (ρ.charpoly g).coeff k`
  is continuous when `M` carries its module topology over a topological commutative ring `A`.
* `TauCeti.ContinuousRep.charpoly_map_eq_of_dense`: equality of characteristic polynomials into a
  Hausdorff ring propagates from a dense subset of `Γ` to all of `Γ`.

## References

* H. Darmon, F. Diamond and R. Taylor, *Fermat's Last Theorem*, §2.1, p. 52.
* J. Newton and J. A. Thorne, *Symmetric power functoriality for holomorphic modular forms*, §1.2,
  p. 7.
* G. Böckle, M. Harris, C. Khare and J. A. Thorne, *Potential automorphy of `G`-local systems*,
  §2, p. 5.
-/

public section

open Polynomial
open scoped TensorProduct

namespace TauCeti.ContinuousRep

section Algebraic

variable {Γ A M : Type*} [Monoid Γ] [TopologicalSpace Γ] [CommRing A]
  [AddCommGroup M] [Module A M] [Module.Free A M] [Module.Finite A M] [TopologicalSpace M]

/-- **Characteristic polynomial of a continuous representation** on a finite free module:
`ρ.charpoly g = det(X - ρ(g)) ∈ A[X]`. -/
noncomputable def charpoly (ρ : ContinuousRep Γ A M) (g : Γ) : A[X] :=
  (ρ g).charpoly

/-- Unfolding `ContinuousRep.charpoly` to `LinearMap.charpoly`. -/
theorem charpoly_def (ρ : ContinuousRep Γ A M) (g : Γ) :
    ρ.charpoly g = (ρ g).charpoly :=
  (rfl)

/-- In any finite basis `b` of `M`, `ρ.charpoly g` is the characteristic polynomial of the matrix of
`ρ g` in `b`. -/
theorem charpoly_eq_matrix_charpoly {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ρ : ContinuousRep Γ A M) (b : Module.Basis ι A M) (g : Γ) :
    ρ.charpoly g = (LinearMap.toMatrix b b (ρ g)).charpoly :=
  (LinearMap.charpoly_toMatrix (ρ g) b).symm

/-- Every characteristic polynomial of a continuous representation is monic. -/
theorem charpoly_monic (ρ : ContinuousRep Γ A M) (g : Γ) : (ρ.charpoly g).Monic :=
  LinearMap.charpoly_monic (ρ g)

/-- Over a nontrivial coefficient ring, the degree of `ρ.charpoly g` is `Module.finrank A M`. -/
@[simp]
theorem charpoly_natDegree [Nontrivial A] (ρ : ContinuousRep Γ A M) (g : Γ) :
    (ρ.charpoly g).natDegree = Module.finrank A M :=
  LinearMap.charpoly_natDegree (ρ g)

/-- Evaluating `ρ.charpoly g` at `t : A` gives `det(t · id - ρ g)`. -/
theorem eval_charpoly (ρ : ContinuousRep Γ A M) (g : Γ) (t : A) :
    (ρ.charpoly g).eval t = LinearMap.det (algebraMap A (Module.End A M) t - ρ g) :=
  LinearMap.eval_charpoly (ρ g) t

/-- **Cayley–Hamilton**: each operator `ρ g` is annihilated by `ρ.charpoly g`. -/
@[simp]
theorem aeval_apply_charpoly (ρ : ContinuousRep Γ A M) (g : Γ) :
    aeval (ρ g) (ρ.charpoly g) = 0 :=
  LinearMap.aeval_self_charpoly (ρ g)

/-- On a subsingleton carrier (such as the zero module), every operator has characteristic
polynomial `1`. -/
theorem charpoly_subsingleton [Subsingleton M] (ρ : ContinuousRep Γ A M) (g : Γ) :
    ρ.charpoly g = 1 := by
  nontriviality A
  have : IsEmpty (Module.Free.ChooseBasisIndex A M) :=
    ⟨fun i => (Module.Free.chooseBasis A M).ne_zero i (Subsingleton.elim _ _)⟩
  rw [charpoly_def, LinearMap.charpoly_def, Matrix.charpoly_isEmpty]

/-- At `1 : Γ`, the characteristic polynomial is `(X - 1) ^ finrank A M`. -/
@[simp]
theorem charpoly_one (ρ : ContinuousRep Γ A M) :
    ρ.charpoly 1 = (X - 1) ^ Module.finrank A M := by
  nontriviality A
  rw [charpoly_def, map_one]
  exact LinearMap.charpoly_one

/-- Every element of the trivial representation has characteristic polynomial
`(X - 1) ^ finrank A M`. -/
@[simp]
theorem charpoly_trivial (g : Γ) :
    (trivial Γ A M).charpoly g = (X - 1) ^ Module.finrank A M := by
  nontriviality A
  rw [charpoly_def, trivial_apply_eq_id]
  exact LinearMap.charpoly_one

/-- Cyclic invariance of the characteristic polynomial: `ρ.charpoly (g * h) = ρ.charpoly (h * g)`
for any elements `g, h` of the acting monoid `Γ`. -/
theorem charpoly_mul_comm (ρ : ContinuousRep Γ A M) (g h : Γ) :
    ρ.charpoly (g * h) = ρ.charpoly (h * g) := by
  rw [charpoly_def, charpoly_def, map_mul, map_mul]
  exact LinearMap.charpoly_comp_comm (ρ h) (ρ g) rfl

/-- Conjugation invariance of the characteristic polynomial for a group representation. -/
@[simp]
theorem charpoly_conj {G : Type*} [Group G] [TopologicalSpace G]
    (ρ : ContinuousRep G A M) (g h : G) :
    ρ.charpoly (g * h * g⁻¹) = ρ.charpoly h := by
  rw [charpoly_mul_comm, inv_mul_cancel_left]

/-- **Isomorphism invariance of characteristic polynomials.** Isomorphic continuous representations
have the same characteristic polynomial at every `g : Γ`. -/
theorem Iso.charpoly_eq {N : Type*} [AddCommGroup N] [Module A N] [Module.Free A N]
    [Module.Finite A N] [TopologicalSpace N]
    {ρ : ContinuousRep Γ A M} {σ : ContinuousRep Γ A N} (e : Iso ρ σ) (g : Γ) :
    ρ.charpoly g = σ.charpoly g := by
  change (ρ.toRepresentation g).charpoly = (σ.toRepresentation g).charpoly
  rw [← e.toRepresentationEquiv.conj_apply_self g, LinearEquiv.charpoly_conj]

end Algebraic

/-! ### Character lines and scalar extension -/

section CharacterAndBaseChange

variable {Γ A : Type*} [Monoid Γ] [TopologicalSpace Γ] [CommRing A] [TopologicalSpace A]

/-- **Characteristic polynomial of a character line.** The rank-one representation `ofCharacter χ`
has characteristic polynomial `X - C (χ g)` at `g`. -/
@[simp]
theorem charpoly_ofCharacter [ContinuousMul A] (χ : Γ →ₜ* Aˣ) (g : Γ) :
    (ofCharacter χ).charpoly g = X - C (χ g : A) := by
  nontriviality A
  let b := Module.Basis.singleton Unit A
  have hmat :
      LinearMap.toMatrix b b (ofCharacter χ g) = Matrix.diagonal fun _ : Unit => (χ g : A) := by
    ext ⟨⟩ ⟨⟩
    simp [b, LinearMap.toMatrix_apply]
  rw [charpoly_eq_matrix_charpoly _ b, hmat, Matrix.charpoly_diagonal]
  simp

/-- **Scalar extension of characteristic polynomials.** Along any continuous coefficient map `A → B`
of commutative rings, the characteristic polynomial of `ρ.baseChange B` at `g` is obtained by
mapping the coefficients of `ρ.charpoly g` along `algebraMap A B`. -/
@[simp]
theorem charpoly_baseChange {M : Type*} [AddCommGroup M] [Module A M] [Module.Free A M]
    [Module.Finite A M] [TopologicalSpace M] [IsModuleTopology A M]
    (B : Type*) [CommRing B] [TopologicalSpace B] [IsTopologicalSemiring B] [Algebra A B]
    [ContinuousSMul A B] [TopologicalSpace (B ⊗[A] M)] [IsModuleTopology B (B ⊗[A] M)]
    (ρ : ContinuousRep Γ A M) (g : Γ) :
    (ρ.baseChange B).charpoly g = (ρ.charpoly g).map (algebraMap A B) := by
  rw [charpoly_def, baseChange_apply, LinearMap.charpoly_baseChange, charpoly_def]

end CharacterAndBaseChange

/-! ### Continuity of characteristic coefficients and density recognition -/

section Continuity

variable {Γ : Type*} [Monoid Γ] [TopologicalSpace Γ]

/-- **Continuity of characteristic coefficients.** When `M` is finite free over a topological
commutative ring `A` and carries its `A`-module topology, every coefficient
`g ↦ (ρ.charpoly g).coeff k` is continuous on `Γ`. -/
@[fun_prop]
theorem continuous_coeff_charpoly {A M : Type*} [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] [AddCommGroup M] [Module A M] [Module.Free A M] [Module.Finite A M]
    [TopologicalSpace M] [IsModuleTopology A M] (ρ : ContinuousRep Γ A M) (k : ℕ) :
    Continuous fun g => (ρ.charpoly g).coeff k := by
  classical
  let b := Module.Free.chooseBasis A M
  have hmat : Continuous fun g : Γ => LinearMap.toMatrix b b (ρ g) :=
    continuous_matrix fun i j =>
      (ρ.toRepresentation.continuous_iff_toMatrix_apply b).mp ρ.continuous_action i j
  simpa only [Function.comp_def, charpoly_eq_matrix_charpoly ρ b] using
    (Matrix.continuous_charpoly_coeff k).comp hmat

/-- **Density propagation for characteristic polynomials across coefficient rings.** Let `ρ₁` and
`ρ₂` be continuous representations on finite free modules with their module topologies over
topological commutative rings `A₁` and `A₂`, and let `f₁ : A₁ →+* B`, `f₂ : A₂ →+* B` be continuous
homomorphisms into a Hausdorff ring `B`. If `(ρ₁.charpoly g).map f₁ = (ρ₂.charpoly g).map f₂` for
all `g` in a dense subset `s ⊆ Γ`, then equality holds for all `g : Γ`. -/
theorem charpoly_map_eq_of_dense {A₁ A₂ B M₁ M₂ : Type*}
    [CommRing A₁] [TopologicalSpace A₁] [IsTopologicalRing A₁]
    [CommRing A₂] [TopologicalSpace A₂] [IsTopologicalRing A₂]
    [CommRing B] [TopologicalSpace B] [T2Space B]
    [AddCommGroup M₁] [Module A₁ M₁] [Module.Free A₁ M₁] [Module.Finite A₁ M₁]
    [TopologicalSpace M₁] [IsModuleTopology A₁ M₁]
    [AddCommGroup M₂] [Module A₂ M₂] [Module.Free A₂ M₂] [Module.Finite A₂ M₂]
    [TopologicalSpace M₂] [IsModuleTopology A₂ M₂]
    (ρ₁ : ContinuousRep Γ A₁ M₁) (ρ₂ : ContinuousRep Γ A₂ M₂)
    {f₁ : A₁ →+* B} {f₂ : A₂ →+* B} (hf₁ : Continuous f₁) (hf₂ : Continuous f₂)
    {s : Set Γ} (hs : Dense s)
    (h : ∀ g ∈ s, (ρ₁.charpoly g).map f₁ = (ρ₂.charpoly g).map f₂) (g : Γ) :
    (ρ₁.charpoly g).map f₁ = (ρ₂.charpoly g).map f₂ := by
  ext k
  have hc₁ : Continuous fun x : Γ => ((ρ₁.charpoly x).map f₁).coeff k := by
    simpa only [coeff_map, Function.comp_def] using hf₁.comp (ρ₁.continuous_coeff_charpoly k)
  have hc₂ : Continuous fun x : Γ => ((ρ₂.charpoly x).map f₂).coeff k := by
    simpa only [coeff_map, Function.comp_def] using hf₂.comp (ρ₂.continuous_coeff_charpoly k)
  exact congrFun (hc₁.ext_on hs hc₂ fun x hx => congrArg (fun p => p.coeff k) (h x hx)) g

/-- **Density propagation for characteristic polynomials** over a Hausdorff topological commutative
ring: agreement on a dense subset `s ⊆ Γ` implies agreement on all of `Γ`. -/
theorem charpoly_eq_of_dense {A M₁ M₂ : Type*} [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] [T2Space A]
    [AddCommGroup M₁] [Module A M₁] [Module.Free A M₁] [Module.Finite A M₁]
    [TopologicalSpace M₁] [IsModuleTopology A M₁]
    [AddCommGroup M₂] [Module A M₂] [Module.Free A M₂] [Module.Finite A M₂]
    [TopologicalSpace M₂] [IsModuleTopology A M₂]
    (ρ₁ : ContinuousRep Γ A M₁) (ρ₂ : ContinuousRep Γ A M₂)
    {s : Set Γ} (hs : Dense s) (h : ∀ g ∈ s, ρ₁.charpoly g = ρ₂.charpoly g) (g : Γ) :
    ρ₁.charpoly g = ρ₂.charpoly g := by
  simpa using ρ₁.charpoly_map_eq_of_dense ρ₂ (f₁ := RingHom.id A) (f₂ := RingHom.id A)
    continuous_id continuous_id hs (fun x hx => by simp [h x hx]) g

end Continuity

end TauCeti.ContinuousRep

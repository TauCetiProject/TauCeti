/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Flat.TorsionFree
public import TauCeti.RingTheory.DedekindDomain.PseudoBasis
public import TauCeti.LinearAlgebra.TensorProduct.ScalarExtension

/-!
# Decomposing finite torsion-free modules over a Dedekind domain

A pseudo-basis identifies a lattice with a finite product of nonzero integral ideals.
Applying this to the image of a finite torsion-free module in its scalar extension to the fraction
field gives the corresponding module decomposition, with one ideal for each generic dimension.
This makes the pseudo-basis theorem available for abstract projective modules, in particular
for computing their classes in projective `K₀`.

## References

* H. Cohen, *Advanced Topics in Computational Number Theory*, Graduate Texts in Mathematics 193,
  Springer, 2000, Section 1.2 (pseudo-bases and finitely generated torsion-free modules).
-/

public section

open Module TensorProduct Submodule

variable {R K V : Type*} [CommRing R] [Field K] [Algebra R K]
  [IsFractionRing R K] [AddCommGroup V] [Module R V] [Module K V] [IsScalarTower R K V]

/-- The coordinate equivalence from a specified pseudo-basis of a lattice to the product of
its coefficient ideals. -/
noncomputable def Submodule.linearEquivPiIdealOfPseudoBasis {ι : Type*} [Finite ι]
    (L : Submodule R V) (b : Basis ι K V) (J : ι → Ideal R)
    (hb : ∀ x, x ∈ L ↔ ∀ i, b.repr x i ∈ IsLocalization.coeSubmodule K (J i)) :
    L ≃ₗ[R] (i : ι) → J i := by
  let f : ((i : ι) → J i) →ₗ[R] V :=
    (b.equivFun.symm.restrictScalars R).comp (LinearMap.pi fun i ↦
      ((Algebra.linearMap R K).comp (J i).subtype).comp (LinearMap.proj i))
  have hf (x : (i : ι) → J i) (i : ι) : b.repr (f x) i = algebraMap R K (x i) := by
    rw [← b.equivFun_apply]
    simp [f, -Basis.equivFun_apply]
  have hinj : Function.Injective f := by
    intro x y h
    funext i
    apply Subtype.ext
    exact IsFractionRing.injective R K ((hf x i).symm.trans ((congrArg (fun v ↦ b.repr v i) h).trans
      (hf y i)))
  have hrange : LinearMap.range f = L := by
    ext v
    constructor
    · rintro ⟨x, rfl⟩
      exact (hb _).2 fun i ↦ (IsLocalization.mem_coeSubmodule _ _).2 ⟨x i, (x i).2, (hf x i).symm⟩
    · intro hv
      choose x hx heq using fun i ↦ (IsLocalization.mem_coeSubmodule K (J i)).1 ((hb v).1 hv i)
      refine ⟨fun i ↦ ⟨x i, hx i⟩, b.repr.injective ?_⟩
      ext i
      exact (hf _ i).trans (heq i)
  exact ((LinearEquiv.ofInjective f hinj).trans (LinearEquiv.ofEq _ _ hrange)).symm

/-- Reconstructing a vector from ideal coordinates recovers those coordinates in the basis. -/
@[simp]
theorem Submodule.repr_linearEquivPiIdealOfPseudoBasis_symm {ι : Type*} [Finite ι]
    (L : Submodule R V) (b : Basis ι K V) (J : ι → Ideal R)
    (hb : ∀ x, x ∈ L ↔ ∀ i, b.repr x i ∈ IsLocalization.coeSubmodule K (J i))
    (c : (i : ι) → J i) (i : ι) :
    b.repr ((L.linearEquivPiIdealOfPseudoBasis b J hb).symm c : V) i =
      algebraMap R K (c i) := by
  change b.repr (b.equivFun.symm (fun i ↦ algebraMap R K (c i))) i = _
  rw [← b.equivFun_apply, b.equivFun.apply_symm_apply]

/-- The ideal coordinates of a lattice vector map to its basis coordinates in the fraction field. -/
@[simp]
theorem Submodule.algebraMap_linearEquivPiIdealOfPseudoBasis_apply {ι : Type*} [Finite ι]
    (L : Submodule R V) (b : Basis ι K V) (J : ι → Ideal R)
    (hb : ∀ x, x ∈ L ↔ ∀ i, b.repr x i ∈ IsLocalization.coeSubmodule K (J i))
    (x : L) (i : ι) :
    algebraMap R K (L.linearEquivPiIdealOfPseudoBasis b J hb x i) = b.repr (x : V) i := by
  rw [← L.repr_linearEquivPiIdealOfPseudoBasis_symm b J hb, LinearEquiv.symm_apply_apply]

variable [IsDedekindDomain R]

/-- A lattice is isomorphic to a product of nonzero integral ideals, indexed by any finite type
of the generic dimension. -/
theorem Submodule.exists_linearEquiv_pi_ideal {ι : Type*} [Finite ι]
    (L : Submodule R V) (hL : L.FG) (hspan : span K (L : Set V) = ⊤)
    (hι : Nat.card ι = finrank K V) :
    ∃ J : ι → Ideal R, (∀ i, J i ≠ ⊥) ∧ Nonempty (L ≃ₗ[R] (i : ι) → J i) := by
  obtain ⟨b, J, hJ, hb⟩ := L.exists_pseudoBasis hL hspan hι
  exact ⟨J, hJ, ⟨L.linearEquivPiIdealOfPseudoBasis b J hb⟩⟩

/-- A finite torsion-free module over a Dedekind domain is a product of nonzero integral ideals.
The number of factors is its dimension after extension to the fraction field. -/
theorem Module.exists_linearEquiv_pi_ideal (R K M : Type*) [CommRing R] [IsDedekindDomain R]
    [Field K] [Algebra R K] [IsFractionRing R K] [AddCommGroup M] [Module R M]
    [Module.Finite R M] [Module.IsTorsionFree R M] :
    ∃ J : Fin (finrank K (K ⊗[R] M)) → Ideal R, (∀ i, J i ≠ ⊥) ∧
      Nonempty (M ≃ₗ[R] (i : Fin (finrank K (K ⊗[R] M))) → J i) := by
  let L := LinearMap.range (TensorProduct.mk R K M 1)
  have hL : L.FG := Submodule.fg_range _
  have hspan : span K (L : Set (K ⊗[R] M)) = ⊤ := by
    simpa only [Submodule.baseChange_eq_span, Submodule.map_top] using
      (Submodule.baseChange_top (R := R) (A := K) (M := M))
  obtain ⟨J, hJ, ⟨e⟩⟩ :=
    L.exists_linearEquiv_pi_ideal (ι := Fin (finrank K (K ⊗[R] M))) hL hspan (by simp)
  exact ⟨J, hJ, ⟨(TensorProduct.unitTmulEquiv R K M).trans e⟩⟩

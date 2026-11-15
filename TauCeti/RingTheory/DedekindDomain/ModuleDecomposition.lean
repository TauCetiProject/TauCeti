/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.DedekindDomain.PseudoBasis
public import TauCeti.LinearAlgebra.TensorProduct.ScalarExtension

/-!
# Decomposing finite flat modules over a Dedekind domain

A pseudo-basis identifies a lattice with a finite product of nonzero integral ideals.
Applying this to the image of a finite flat module in its scalar extension to the fraction
field gives the corresponding module decomposition, with one ideal for each generic dimension.
This makes the pseudo-basis theorem available for abstract projective modules, in particular
for computing their classes in projective `K₀`.

## References

* C. A. Weibel, *The K-book*, Chapter I, §3, Proposition 3.4.
-/

public section

open Module TensorProduct Submodule

variable {R K V : Type*} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
  [IsFractionRing R K] [AddCommGroup V] [Module R V] [Module K V] [IsScalarTower R K V]

/-- A lattice is isomorphic to a product of nonzero integral ideals, indexed by any finite type
of the generic dimension. -/
theorem Submodule.exists_linearEquiv_pi_ideal {ι : Type*} [Finite ι]
    (L : Submodule R V) (hL : L.FG) (hspan : span K (L : Set V) = ⊤)
    (hι : Nat.card ι = finrank K V) :
    ∃ J : ι → Ideal R, (∀ i, J i ≠ ⊥) ∧ Nonempty (L ≃ₗ[R] (i : ι) → J i) := by
  classical
  let := Fintype.ofFinite ι
  obtain ⟨b, J, hJ, hb⟩ := L.exists_pseudoBasis hL hspan hι
  let f : ((i : ι) → J i) →ₗ[R] V :=
    (b.equivFun.symm.restrictScalars R).comp (LinearMap.pi fun i ↦
      ((Algebra.linearMap R K).comp (J i).subtype).comp (LinearMap.proj i))
  have hf (x : (i : ι) → J i) (i : ι) : b.repr (f x) i = algebraMap R K (x i) := by
    exact congrFun (b.equivFun.apply_symm_apply (fun i ↦ algebraMap R K (x i))) i
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
  exact ⟨J, hJ, ⟨((LinearEquiv.ofInjective f hinj).trans (LinearEquiv.ofEq _ _ hrange)).symm⟩⟩

/-- A finite flat module over a Dedekind domain is a product of nonzero integral ideals.
The number of factors is its dimension after extension to the fraction field. -/
theorem Module.exists_linearEquiv_pi_ideal (R K M : Type*) [CommRing R] [IsDedekindDomain R]
    [Field K] [Algebra R K] [IsFractionRing R K] [AddCommGroup M] [Module R M]
    [Module.Finite R M] [Module.Flat R M] :
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

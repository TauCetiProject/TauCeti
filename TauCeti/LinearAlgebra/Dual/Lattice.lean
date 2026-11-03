/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Dual.Basis
public import TauCeti.Algebra.Module.Lattice

/-!
# Lattices in the linear dual

The integral dual of an `R`-submodule of a `K`-module consists of the `K`-linear
functionals taking values in `R` on that submodule. This construction requires no
bilinear form on the ambient module. For the span of a finite basis it is the span
of the dual basis; in particular the dual of a free full lattice is a full lattice.

Precomposition carries integral duals contravariantly along lattice-preserving
linear maps. This is the linear-algebra input to contragredient actions on
admissible integral lattices.
-/

public section

namespace Submodule

variable {R K V W : Type*} [CommRing R] [CommRing K] [Algebra R K]
  [AddCommGroup V] [Module K V] [Module R V]
  [AddCommGroup W] [Module K W] [Module R W]

variable (K) in
/-- The linear functionals taking values in the image of `R` on `N`.
No bilinear form or full-lattice hypothesis is required. -/
def dualLattice (N : Submodule R V) : Submodule R (Module.Dual K V) :=
  ⨅ x : N, (1 : Submodule R K).comap
    ((LinearMap.applyₗ (R := K) (M₂ := K) (x : V)).restrictScalars R)

/-- Membership in the integral dual is integrality of every evaluation on the original
submodule. -/
@[simp]
theorem mem_dualLattice (N : Submodule R V) (φ : Module.Dual K V) :
    φ ∈ N.dualLattice K ↔ ∀ x ∈ N, φ x ∈ (1 : Submodule R K) := by
  simp [dualLattice]

variable (K) in
/-- Taking the integral dual reverses inclusions. -/
theorem dualLattice_antitone : Antitone (dualLattice (R := R) (V := V) K) := by
  intro M N h φ hφ
  exact (mem_dualLattice M φ).mpr fun x hx => (mem_dualLattice N φ).mp hφ x (h hx)

/-- Precomposition with a lattice-preserving map preserves the corresponding integral duals. -/
theorem dualMap_mem_dualLattice (M : Submodule R V) (N : Submodule R W)
    (f : V →ₗ[K] W) (hf : ∀ x ∈ M, f x ∈ N)
    {φ : Module.Dual K W} (hφ : φ ∈ N.dualLattice K) :
    f.dualMap φ ∈ M.dualLattice K := by
  exact (mem_dualLattice M _).mpr fun x hx => (mem_dualLattice N φ).mp hφ _ (hf x hx)

end Submodule

namespace Module.Basis

variable {R K V ι : Type*} [CommRing R] [CommRing K] [Algebra R K]
  [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V]
  [Finite ι] [DecidableEq ι]

/-- The integral dual of a basis lattice is the lattice spanned by the dual basis. -/
@[simp]
theorem dualLattice_span (b : Basis ι K V) :
    (Submodule.span R (Set.range b)).dualLattice K =
      Submodule.span R (Set.range b.dualBasis) := by
  classical
  let := Fintype.ofFinite ι
  apply le_antisymm
  · intro φ hφ
    rw [← b.dualBasis.sum_repr φ]
    refine Submodule.sum_mem _ fun i _ => ?_
    rw [dualBasis_repr]
    obtain ⟨r, hr⟩ := Submodule.mem_one.mp
      ((Submodule.mem_dualLattice _ _).mp hφ _ (Submodule.subset_span ⟨i, rfl⟩))
    rw [← hr, algebraMap_smul]
    exact Submodule.smul_mem _ r (Submodule.subset_span ⟨i, rfl⟩)
  · refine Submodule.span_le.mpr ?_
    rintro _ ⟨i, rfl⟩
    refine (Submodule.mem_dualLattice _ _).mpr ?_
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨j, rfl⟩ := hx
      simp only [dualBasis_apply_self]
      split
      · exact Submodule.mem_one.mpr ⟨1, map_one _⟩
      · exact Submodule.zero_mem _
    | zero => simp
    | add x y _ _ hx hy => simpa using (1 : Submodule R K).add_mem hx hy
    | smul r x _ hx => simpa using (1 : Submodule R K).smul_mem r hx

end Module.Basis

namespace Submodule

variable {R K V : Type*} [CommRing R] [IsDomain R] [Field K] [Algebra R K]
  [IsFractionRing R K] [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V]

/-- The integral dual of a free full lattice is again a full lattice. -/
instance isLattice_dualLattice (N : Submodule R V) [N.IsLattice K] [Module.Free R N] :
    (N.dualLattice K).IsLattice K := by
  classical
  let b := Module.Free.chooseBasis R N
  rw [← b.span_range_extendOfIsLattice (K := K), (b.extendOfIsLattice K).dualLattice_span]
  exact isLattice_span (Set.finite_range _) (b.extendOfIsLattice K).dualBasis.span_eq

end Submodule

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.NormTwoShell.FullCartan.Basic
public import Mathlib.Algebra.Lie.Abelian

/-!
# The center of the signed Lie algebra over a full Cartan lattice

For a full Cartan datum `D`, the center of `Matrix.FullShellLieAlgebra D` consists of the
Cartan vectors annihilated by every root weight. In particular no root coordinate is central:
bracketing with the coroot of that root multiplies its coordinate by two. This calculation is
integral and allows torsion in the Cartan group itself; it does not split that group into
central and coroot summands.

`Matrix.FullShellLieAlgebra.forall_cartan_lie_eq_zero_iff` identifies the centralizer of the
Cartan group. `Matrix.FullShellLieAlgebra.mem_center_iff` then describes the center in product
coordinates, and `Matrix.FullShellLieAlgebra.center_eq_map_iInf_ker` identifies its underlying
module with the image of the common kernel of the root weights. These give the central part
needed when comparing a reductive Lie algebra with its semisimple part.

## References

* J. C. Jantzen, *Representations of Algebraic Groups*, Part II, Chapter 1.
* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, §§8 and 19.
-/

public section

namespace Matrix.FullShellLieAlgebra

variable {I Y : Type*} [Fintype I] [LinearOrder I] [AddCommGroup Y]
  {B : Matrix I I ℤ} (D : Matrix.ShellCartanDatum B Y)

/-- Bracketing with a Cartan vector multiplies each root coordinate by its root weight. -/
@[simp]
theorem equivProd_cartan_lie_snd (y : Y) (x : FullShellLieAlgebra D)
    (a : B.normTwoShell) :
    (equivProd D ⁅cartan D y, x⁆).2 a = D.weight a y * (equivProd D x).2 a := by
  let coordinate : FullShellLieAlgebra D →ₗ[ℤ] ℤ :=
    (Finsupp.lapply a).comp ((LinearMap.snd ℤ Y (B.normTwoShell →₀ ℤ)).comp
      (equivProd D).toLinearMap)
  have h : coordinate.comp (bracketBilin D (cartan D y)) =
      (D.weight a y) • coordinate := by
    apply linearMap_ext
    · intro z
      simp [coordinate]
    · intro b
      by_cases hab : a = b
      · subst b
        simp [coordinate]
      · simp [coordinate, hab]
  exact LinearMap.congr_fun h x

/-- The centralizer of the full Cartan group is exactly its image in the signed Lie algebra.
No positive-definiteness or torsion-freeness assumption on the Cartan group is needed. -/
theorem forall_cartan_lie_eq_zero_iff (x : FullShellLieAlgebra D) :
    (∀ y, ⁅cartan D y, x⁆ = 0) ↔ x ∈ LinearMap.range (cartan D) := by
  constructor
  · intro hx
    have hroot : (equivProd D x).2 = 0 := by
      apply Finsupp.ext
      intro a
      simp only [Finsupp.zero_apply]
      have h := equivProd_cartan_lie_snd D (D.coroot a) x a
      rw [hx, map_zero, Prod.snd_zero, Finsupp.zero_apply, D.weight_coroot,
        Matrix.mem_normTwoShell.mp a.property] at h
      omega
    refine ⟨(equivProd D x).1, (equivProd D).injective ?_⟩
    rw [equivProd_cartan]
    exact Prod.ext rfl hroot.symm
  · rintro ⟨y, rfl⟩ z
    exact cartan_lie_cartan z y

/-- A Cartan vector commutes with every vector exactly when all root weights vanish on it. -/
@[simp]
theorem forall_lie_cartan_eq_zero_iff (y : Y) :
    (∀ x : FullShellLieAlgebra D, ⁅x, cartan D y⁆ = 0) ↔
      ∀ a : B.normTwoShell, D.weight a y = 0 := by
  constructor
  · intro hy a
    have h := congrArg (fun z => (equivProd D z).2 a) (hy (root D a))
    simpa using h
  · intro hweight
    have h : (bracketBilin D).flip (cartan D y) = 0 := by
      apply linearMap_ext
      · intro z
        simp
      · intro a
        simp [hweight]
    exact LinearMap.congr_fun h

section Center

variable (hB : B.PosDef) (hdiag : ∀ i, Even (B i i))

/-- A central vector has zero root coordinates and its Cartan coordinate is annihilated by
every root weight. -/
theorem mem_center_iff (x : FullShellLieAlgebra D) :
    letI := lieRing D hB hdiag
    x ∈ LieAlgebra.center ℤ (FullShellLieAlgebra D) ↔
      (equivProd D x).2 = 0 ∧ ∀ a : B.normTwoShell, D.weight a (equivProd D x).1 = 0 := by
  let := lieRing D hB hdiag
  constructor
  · intro hx
    obtain ⟨y, rfl⟩ := (forall_cartan_lie_eq_zero_iff D x).mp fun y => hx (cartan D y)
    simp only [equivProd_cartan, true_and]
    exact (forall_lie_cartan_eq_zero_iff D y).mp hx
  · rintro ⟨hroot, hweight⟩
    have hx : x = cartan D (equivProd D x).1 := by
      apply (equivProd D).injective
      rw [equivProd_cartan]
      exact Prod.ext rfl hroot
    rw [hx]
    exact (forall_lie_cartan_eq_zero_iff D (equivProd D x).1).mpr hweight

/-- The center, as an integral module, is the Cartan image of the common kernel of all root
weights. This retains the entire central toral part, including for an empty root shell. -/
theorem center_eq_map_iInf_ker :
    letI := lieRing D hB hdiag
    (LieAlgebra.center ℤ (FullShellLieAlgebra D)).toSubmodule =
      Submodule.map (cartan D) (⨅ a : B.normTwoShell, LinearMap.ker (D.weight a)) := by
  let := lieRing D hB hdiag
  ext x
  constructor
  · intro hx
    obtain ⟨y, rfl⟩ := (forall_cartan_lie_eq_zero_iff D x).mp fun y => hx (cartan D y)
    exact ⟨y, by simpa using (forall_lie_cartan_eq_zero_iff D y).mp hx, rfl⟩
  · rintro ⟨y, hy, rfl⟩
    exact (forall_lie_cartan_eq_zero_iff D y).mpr (by simpa using hy)

end Center

end Matrix.FullShellLieAlgebra

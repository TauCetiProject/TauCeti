/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.NumberField.Discriminant.Basic
public import TauCeti.NumberTheory.NumberField.CanonicalEmbedding.IdealLattice
public import TauCeti.NumberTheory.NumberField.Global.RayClass.Modulus

/-!
# The congruence lattice of a modulus

Let `𝔪` be a modulus of a number field `K` with finite part `𝔪₀`, and let `I` be an invertible
fractional ideal.  Under the mixed embedding `K → ℝ^r₁ × ℂ^r₂`, the ideal `I` becomes the full
lattice `mixedEmbedding.idealLattice K I`.  The **congruence lattice** `congruenceLattice 𝔪 I` is
the sublattice coming from `I * 𝔪₀`: the elements of `I` congruent to `0` modulo `𝔪₀`.

Counting the elements of `I` in a region that satisfy a congruence `x ≡ a mod I * 𝔪₀` is
counting the points of one coset of this sublattice, which is itself a translate of a full
lattice.  The index computation below says that there are exactly `N 𝔪₀` such cosets, so each
congruence class carries the fraction `1 / N 𝔪₀` of the lattice points of `I`, and the covolume
grows by the factor `N 𝔪₀`.  These are the lattice inputs to counting integral ideals in a ray
class.

## Main definitions

* `TauCeti.GlobalNumberFields.congruenceLattice`: the lattice of `I * 𝔪₀` in the mixed space.

## Main results

* `TauCeti.GlobalNumberFields.mem_congruenceLattice_iff`: its points are the images of the
  elements of `I * 𝔪₀`.
* `TauCeti.GlobalNumberFields.congruenceLattice_le_idealLattice`: it is a sublattice of the ideal
  lattice of `I`.
* `TauCeti.GlobalNumberFields.relIndex_congruenceLattice`: its index in the ideal lattice of `I`
  is the absolute norm of `𝔪₀`.
* `TauCeti.GlobalNumberFields.covolume_congruenceLattice`: its covolume is `N 𝔪₀` times the
  covolume of the ideal lattice of `I`.
* `TauCeti.GlobalNumberFields.congruenceLattice_one`: for the trivial modulus it is the ideal
  lattice itself.

## References

* S. Lang, *Algebraic Number Theory*, Chapter VI, §3.
* J. Neukirch, *Algebraic Number Theory*, Chapter VI, §1.
-/

public section

open NumberField NumberField.mixedEmbedding
open scoped nonZeroDivisors

namespace TauCeti.GlobalNumberFields

variable {K : Type*} [Field K] [NumberField K]

/-- The **congruence lattice** of a modulus `𝔪` inside the ideal lattice of `I`: the image in the
mixed space of the fractional ideal `I * 𝔪₀`, whose elements are those of `I` congruent to `0`
modulo the finite part `𝔪₀`. -/
noncomputable def congruenceLattice (𝔪 : Modulus K) (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    Submodule ℤ (mixedSpace K) :=
  idealLattice K
    (I * FractionalIdeal.mk0 K ⟨𝔪.finitePart, mem_nonZeroDivisors_of_ne_zero 𝔪.finitePart_ne_zero⟩)

/-- The congruence lattice is the ideal lattice of `I * 𝔪₀`. -/
theorem congruenceLattice_def (𝔪 : Modulus K) (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    congruenceLattice 𝔪 I = idealLattice K (I * FractionalIdeal.mk0 K
      ⟨𝔪.finitePart, mem_nonZeroDivisors_of_ne_zero 𝔪.finitePart_ne_zero⟩) :=
  (rfl)

/-- The congruence lattice is a discrete subgroup of the mixed space. -/
instance (𝔪 : Modulus K) (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    DiscreteTopology (congruenceLattice 𝔪 I) := by
  unfold congruenceLattice
  infer_instance

open scoped Classical in
/-- The congruence lattice is a full `ℤ`-lattice in the mixed space. -/
instance (𝔪 : Modulus K) (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    IsZLattice ℝ (congruenceLattice 𝔪 I) := by
  unfold congruenceLattice
  infer_instance

/-- The points of the congruence lattice are the images of the elements of `I * 𝔪₀`. -/
theorem mem_congruenceLattice_iff {𝔪 : Modulus K} {I : (FractionalIdeal (𝓞 K)⁰ K)ˣ}
    {x : mixedSpace K} :
    x ∈ congruenceLattice 𝔪 I ↔
      ∃ y ∈ (I : FractionalIdeal (𝓞 K)⁰ K) * 𝔪.finitePart, mixedEmbedding K y = x := by
  rw [congruenceLattice_def, mem_idealLattice]
  simp [← FractionalIdeal.mem_coe, FractionalIdeal.coe_mul]

/-- The congruence lattice is a sublattice of the ideal lattice of `I`. -/
theorem congruenceLattice_le_idealLattice (𝔪 : Modulus K) (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    congruenceLattice 𝔪 I ≤ idealLattice K I := fun x hx ↦ by
  obtain ⟨y, hy, rfl⟩ := mem_congruenceLattice_iff.mp hx
  exact (mem_idealLattice K I).mpr
    ⟨y, mul_le_of_le_one_right' FractionalIdeal.coeIdeal_le_one hy, rfl⟩

/-- **The index of the congruence lattice.**  The congruence lattice of `𝔪` has index `N 𝔪₀` in
the ideal lattice of `I`, so it has exactly `N 𝔪₀` cosets there, one for each residue class
modulo `I * 𝔪₀`. -/
theorem relIndex_congruenceLattice (𝔪 : Modulus K) (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    (congruenceLattice 𝔪 I).toAddSubgroup.relIndex (idealLattice K I).toAddSubgroup =
      Ideal.absNorm 𝔪.finitePart := by
  have hI : FractionalIdeal.absNorm (I : FractionalIdeal (𝓞 K)⁰ K) ≠ 0 :=
    FractionalIdeal.absNorm_eq_zero_iff.not.mpr I.ne_zero
  have := relIndex_idealLattice (I := I) (J := I * FractionalIdeal.mk0 K
    ⟨𝔪.finitePart, mem_nonZeroDivisors_of_ne_zero 𝔪.finitePart_ne_zero⟩)
    (mul_le_of_le_one_right' FractionalIdeal.coeIdeal_le_one)
  rw [Units.val_mul, map_mul, FractionalIdeal.coe_mk0, FractionalIdeal.coeIdeal_absNorm,
    mul_div_cancel_left₀ _ hI] at this
  exact_mod_cast this

open scoped Classical in
/-- **The covolume of the congruence lattice** is `N 𝔪₀` times the covolume of the ideal lattice
of `I`. -/
theorem covolume_congruenceLattice (𝔪 : Modulus K) (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    ZLattice.covolume (congruenceLattice 𝔪 I) =
      Ideal.absNorm 𝔪.finitePart * ZLattice.covolume (idealLattice K I) := by
  rw [congruenceLattice_def, covolume_idealLattice, covolume_idealLattice,
    Units.val_mul, map_mul, FractionalIdeal.coe_mk0, FractionalIdeal.coeIdeal_absNorm]
  push_cast
  ring

/-- For the trivial modulus the congruence lattice is the whole ideal lattice. -/
@[simp]
theorem congruenceLattice_one (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    congruenceLattice (Modulus.one K) I = idealLattice K I := by
  ext x
  simp [mem_congruenceLattice_iff]

end TauCeti.GlobalNumberFields

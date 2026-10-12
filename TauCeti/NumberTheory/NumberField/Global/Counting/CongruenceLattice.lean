/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.CanonicalEmbedding.IdealLattice
public import TauCeti.NumberTheory.NumberField.Global.RayClass.Modulus

/-!
# The congruence lattice of a modulus

Let `𝔪` be a modulus of a number field `K` with finite part `𝔪₀`, and let `I` be an invertible
fractional ideal.  Under the mixed embedding `K → ℝ^r₁ × ℂ^r₂`, the ideal `I` becomes the full
lattice `mixedEmbedding.idealLattice K I`.  The **congruence lattice** `congruenceLattice 𝔪 I` is
the sublattice coming from `I * 𝔪₀`: the elements of `I` congruent to `0` modulo `I * 𝔪₀`.

Counting the elements of `I` in a region that satisfy a congruence `x ≡ a mod I * 𝔪₀` is
counting the points of one coset of this sublattice, which is itself a translate of a full
lattice.  The index computation below says that there are exactly `N 𝔪₀` such cosets, and the
covolume grows by the factor `N 𝔪₀`.  These are the lattice inputs to counting integral ideals in
a ray class.

Only the finite part `𝔪₀` enters the lattice: the infinite part of `𝔪` plays no role here, and
the sign conditions at the real places of `𝔪.infinitePart` are imposed by the region, not by the
sublattice.

## Main definitions

* `TauCeti.GlobalNumberFields.congruenceLattice`: the lattice of `I * 𝔪₀` in the mixed space.

## Main results

* `TauCeti.GlobalNumberFields.mem_congruenceLattice_iff`: its points are the images of the
  elements of `I * 𝔪₀`.
* `TauCeti.GlobalNumberFields.coe_congruenceLattice_mk0_eq_image`: for an integral ideal `𝔞`,
  the same description over `𝔞 * 𝔪₀`.
* `TauCeti.GlobalNumberFields.congruenceLattice_le_idealLattice`: it is a sublattice of the ideal
  lattice of `I`.
* `TauCeti.GlobalNumberFields.relIndex_congruenceLattice`: its index in the ideal lattice of `I`
  is the absolute norm of `𝔪₀`.
* `TauCeti.GlobalNumberFields.covolume_congruenceLattice`: its covolume is `N 𝔪₀` times the
  covolume of the ideal lattice of `I`.
* `TauCeti.GlobalNumberFields.covolume_congruenceLattice_div_absNorm`: its covolume divided by
  `N I` is `N 𝔪₀ · √|d_K| / 2 ^ r₂`.
* `TauCeti.GlobalNumberFields.congruenceLattice_eq_of_finitePart_eq`: it depends only on the
  finite part of the modulus.
* `TauCeti.GlobalNumberFields.congruenceLattice_eq_idealLattice_of_finitePart_eq_top`: for a
  modulus with trivial finite part it is the ideal lattice itself; `congruenceLattice_one` and
  `congruenceLattice_narrowModulus` are the cases of the trivial and the narrow modulus.

## References

* S. Lang, *Algebraic Number Theory*, Chapter VI, §3.
* J. Neukirch, *Algebraic Number Theory*, Chapter VI, §1.
-/

public section

open MeasureTheory NumberField NumberField.InfinitePlace NumberField.mixedEmbedding
open scoped nonZeroDivisors

namespace TauCeti.GlobalNumberFields

variable {K : Type*} [Field K] [NumberField K]

/-- The **congruence lattice** of a modulus `𝔪` inside the ideal lattice of `I`: the image in the
mixed space of the fractional ideal `I * 𝔪₀`, whose elements are those of `I` congruent to `0`
modulo `I * 𝔪₀`, where `𝔪₀` is the finite part of `𝔪`. -/
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
@[simp]
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
@[simp]
theorem relIndex_congruenceLattice (𝔪 : Modulus K) (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    (congruenceLattice 𝔪 I).toAddSubgroup.relIndex (idealLattice K I).toAddSubgroup =
      Ideal.absNorm 𝔪.finitePart := by
  rw [congruenceLattice_def, relIndex_idealLattice_mul_mk0]

open scoped Classical in
/-- **The covolume of the congruence lattice** is `N 𝔪₀` times the covolume of the ideal lattice
of `I`. -/
@[simp]
theorem covolume_congruenceLattice (𝔪 : Modulus K) (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    ZLattice.covolume (congruenceLattice 𝔪 I) =
      Ideal.absNorm 𝔪.finitePart * ZLattice.covolume (idealLattice K I) := by
  rw [congruenceLattice_def, covolume_idealLattice_mul_mk0]

open scoped Classical in
/-- **The covolume of the congruence lattice, per unit norm.**  For an invertible fractional
ideal `I`, the covolume of the congruence lattice of `𝔪` at `I`, divided by `N I`, is
`N 𝔪₀ · √|d_K| / 2 ^ r₂`, where `d_K` is the discriminant and `r₂` the number of complex places
of `K`; in particular it does not depend on `I`. -/
theorem covolume_congruenceLattice_div_absNorm (𝔪 : Modulus K)
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    ZLattice.covolume (congruenceLattice 𝔪 I) volume /
        (FractionalIdeal.absNorm (I : FractionalIdeal (𝓞 K)⁰ K) : ℝ) =
      Ideal.absNorm 𝔪.finitePart * √|(discr K : ℝ)| / 2 ^ nrComplexPlaces K := by
  simp only [covolume_congruenceLattice, covolume_idealLattice, inv_pow]
  field_simp

/-- The congruence lattice depends only on the finite part of the modulus. -/
theorem congruenceLattice_eq_of_finitePart_eq {𝔪 𝔫 : Modulus K}
    (h : 𝔪.finitePart = 𝔫.finitePart) (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    congruenceLattice 𝔪 I = congruenceLattice 𝔫 I := by
  ext x
  simp [mem_congruenceLattice_iff, h]

/-- For a modulus with trivial finite part the congruence lattice is the whole ideal lattice. -/
theorem congruenceLattice_eq_idealLattice_of_finitePart_eq_top {𝔪 : Modulus K}
    (h : 𝔪.finitePart = ⊤) (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    congruenceLattice 𝔪 I = idealLattice K I := by
  ext x
  simp [mem_congruenceLattice_iff, h]

/-- For the trivial modulus the congruence lattice is the whole ideal lattice. -/
@[simp]
theorem congruenceLattice_one (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    congruenceLattice (Modulus.one K) I = idealLattice K I :=
  congruenceLattice_eq_idealLattice_of_finitePart_eq_top (Modulus.one_finitePart) I

/-- For the narrow modulus the congruence lattice is the whole ideal lattice. -/
@[simp]
theorem congruenceLattice_narrowModulus (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    congruenceLattice (narrowModulus K) I = idealLattice K I :=
  congruenceLattice_eq_idealLattice_of_finitePart_eq_top (narrowModulus_finitePart) I

/-- **The congruence lattice of an integral ideal, upstairs.**  For a nonzero integral ideal `𝔞`,
the congruence lattice of `𝔪` at `mk0 𝔞` is the image under `mixedEmbedding` of the ideal
`𝔞 * 𝔪₀` of `𝓞 K`. -/
@[simp]
theorem coe_congruenceLattice_mk0_eq_image (𝔪 : Modulus K) (𝔞 : (Ideal (𝓞 K))⁰) :
    (congruenceLattice 𝔪 (FractionalIdeal.mk0 K 𝔞) : Set (mixedSpace K)) =
      (fun y : 𝓞 K ↦ mixedEmbedding K (y : K)) ''
        ((𝔞 : Ideal (𝓞 K)) * 𝔪.finitePart : Ideal (𝓞 K)) := by
  ext x
  simp [mem_congruenceLattice_iff, FractionalIdeal.coe_mk0, ← FractionalIdeal.coeIdeal_mul,
    FractionalIdeal.mem_coeIdeal]

end TauCeti.GlobalNumberFields

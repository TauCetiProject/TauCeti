/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Biproducts
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import TauCeti.Algebra.Homology.ModuleCat.Finrank
public import TauCeti.Algebra.Homology.ShortComplex.ModuleCat
public import TauCeti.Algebra.Homology.Periodic.Compression.Acyclic

/-!
# Homology of the periodic compression

Let `K` be a strictly bounded cochain complex in a preadditive category with homology, and let
`Δₙ K` be its `n`-periodic compression, `(Δₙ K)^r = ⨁_{i ≡ r mod n} K^i`. The homology of `Δₙ K`
in residue `r` is the direct sum of the homology objects of `K` in the degrees congruent to `r`:

`H^r(Δₙ K) ≅ ⨁_{i ≡ r mod n} H^i(K)`.

The summand inclusions `TauCeti.PeriodicComplex.ιCompressionHomology` and projections
`TauCeti.PeriodicComplex.πCompressionHomology` are the maps induced on homology by the inclusions
and projections of the summands of `Δₙ K`. Over the degrees of the residue class `r` in an
interval `[a, b]` containing the support of `K`, they form a biproduct bicone
(`TauCeti.PeriodicComplex.isBilimitCompressionHomologyBicone`), which gives the isomorphism
`TauCeti.PeriodicComplex.compressionHomologyIso`.

For complexes of vector spaces with finite-dimensional homology this computes dimensions. The
dimension of `H^r(Δₙ K)` is the sum of the dimensions of the `H^i(K)` with `i ≡ r`
(`TauCeti.PeriodicComplex.finrank_homology_compression`), so for positive `n` the total dimension
of the homology of `Δₙ K` is the total dimension of the homology of `K`
(`TauCeti.PeriodicComplex.sum_finrank_homology_compression`). Hence a `ZMod n`-graded complex of
finite-dimensional vector spaces whose homology is isomorphic to that of `Δₙ K`, for instance one
chain homotopy equivalent to `Δₙ K` (through `HomotopyEquiv.toHomologyIso`), has total dimension
at least the total dimension of the homology of `K`
(`TauCeti.PeriodicComplex.sum_finrank_homology_le_sum_finrank_X`).

This is the rank inequality behind lower bounds for the number of generators of cyclically graded
complexes, such as Hamiltonian Floer complexes graded modulo twice the minimal Chern number: when
such a complex is chain homotopy equivalent to the compression of an integer-graded complex, its
number of generators is at least the total Betti number of that complex.

## References

* T. Stai, *The triangulated hull of periodic complexes*, Mathematical Research Letters **25**
  (2018), 199–236, Section 3.3.
* H. Hofer and D. A. Salamon, *Floer homology and Novikov rings*, in *The Floer memorial volume*,
  Progress in Mathematics **133** (1995), 483–524.
-/

public section

open CategoryTheory Limits Module

universe v u

namespace TauCeti.PeriodicComplex

variable {C : Type u} [Category.{v} C]

section HasZeroMorphisms

variable [HasZeroMorphisms C] [CategoryWithHomology C] (n : ℕ) (K : CochainComplex C ℤ)
  [HasCompression n K]

/-- The inclusion of the homology of `K` in degree `i` into the homology of its `n`-periodic
compression in residue `r`, induced by the inclusion of the summand of degree `i`. It is zero
when `i` does not lie in the residue class `r`. -/
noncomputable def ιCompressionHomology (r : ZMod n) (i : ℤ) :
    K.homology i ⟶ (compression n K).homology r :=
  (K.homologyIsoSc' (i - 1) i (i + 1) (by simp) (by simp)).hom ≫
    ShortComplex.homologyMap (compressionScι n K r i) ≫
      ((compression n K).homologyIsoSc' (r - 1) r (r + 1) (by simp) (by simp)).inv

/-- The projection of the homology of the `n`-periodic compression of `K` in residue `r` onto the
homology of `K` in degree `i`, induced by the projection onto the summand of degree `i`. It is
zero when `i` does not lie in the residue class `r`. -/
noncomputable def πCompressionHomology (r : ZMod n) (i : ℤ) :
    (compression n K).homology r ⟶ K.homology i :=
  ((compression n K).homologyIsoSc' (r - 1) r (r + 1) (by simp) (by simp)).hom ≫
    ShortComplex.homologyMap (compressionScπ n K r i) ≫
      (K.homologyIsoSc' (i - 1) i (i + 1) (by simp) (by simp)).inv

/-- The inclusion of the homology in a degree outside the residue class `r` is zero. -/
@[simp]
lemma ιCompressionHomology_eq_zero (r : ZMod n) (i : ℤ) (hi : (i : ZMod n) ≠ r) :
    ιCompressionHomology n K r i = 0 := by
  simp [ιCompressionHomology, compressionScι_eq_zero n K r i hi]

/-- The projection onto the homology in a degree outside the residue class `r` is zero. -/
@[simp]
lemma πCompressionHomology_eq_zero (r : ZMod n) (i : ℤ) (hi : (i : ZMod n) ≠ r) :
    πCompressionHomology n K r i = 0 := by
  simp [πCompressionHomology, compressionScπ_eq_zero n K r i hi]

/-- The homology of `K` in a degree of the residue class `r` is a retract of the homology of the
compression in residue `r`. -/
@[reassoc (attr := simp)]
lemma ιCompressionHomology_πCompressionHomology (r : ZMod n) (i : ℤ) (hi : (i : ZMod n) = r) :
    ιCompressionHomology n K r i ≫ πCompressionHomology n K r i = 𝟙 _ := by
  have h : ShortComplex.homologyMap (compressionScι n K r i) ≫
      ShortComplex.homologyMap (compressionScπ n K r i) = 𝟙 _ := by
    rw [← ShortComplex.homologyMap_comp, compressionScι_compressionScπ n K r i hi,
      ShortComplex.homologyMap_id]
  simp [ιCompressionHomology, πCompressionHomology, reassoc_of% h]

/-- The retractions of the homology of `K` in two different degrees onto the homology of the
compression are orthogonal. -/
@[reassoc]
lemma ιCompressionHomology_πCompressionHomology_of_ne (r : ZMod n) {i j : ℤ} (hij : i ≠ j) :
    ιCompressionHomology n K r i ≫ πCompressionHomology n K r j = 0 := by
  have h : ShortComplex.homologyMap (compressionScι n K r i) ≫
      ShortComplex.homologyMap (compressionScπ n K r j) = 0 := by
    rw [← ShortComplex.homologyMap_comp, compressionScι_compressionScπ_of_ne n K r hij,
      ShortComplex.homologyMap_zero]
  simp [ιCompressionHomology, πCompressionHomology, reassoc_of% h]

/-- The **homology bicone of the compression** in residue `r`: the homology of the compression in
residue `r`, with the inclusions and projections of the homology of `K` in the degrees of `[a, b]`
congruent to `r`. It is a biproduct bicone when `K` is supported in `[a, b]`
(`TauCeti.PeriodicComplex.isBilimitCompressionHomologyBicone`). -/
@[expose, simps]
noncomputable def compressionHomologyBicone (a b : ℤ) (r : ZMod n) :
    Bicone fun i : ({i ∈ Finset.Icc a b | (i : ZMod n) = r} : Finset ℤ) ↦ K.homology i where
  pt := (compression n K).homology r
  π i := πCompressionHomology n K r i
  ι i := ιCompressionHomology n K r i
  ι_π i j := by
    split_ifs with h
    · subst h
      simpa using ιCompressionHomology_πCompressionHomology n K r i (Finset.mem_filter.1 i.2).2
    · exact ιCompressionHomology_πCompressionHomology_of_ne n K r fun h' ↦ h (Subtype.ext h')

end HasZeroMorphisms

section Preadditive

variable [Preadditive C] [CategoryWithHomology C] (n : ℕ) (K : CochainComplex C ℤ)
  [HasCompression n K] (a b : ℤ) [K.IsStrictlyGE a] [K.IsStrictlyLE b]

/-- For a complex supported in `[a, b]`, the identity of the homology of the compression in
residue `r` is the sum, over the degrees of `[a, b]` congruent to `r`, of the projections onto the
homology of `K` followed by the inclusions. -/
lemma sum_πCompressionHomology_ιCompressionHomology (r : ZMod n) :
    ∑ i ∈ ({i ∈ Finset.Icc a b | (i : ZMod n) = r} : Finset ℤ),
      πCompressionHomology n K r i ≫ ιCompressionHomology n K r i = 𝟙 _ := by
  -- Outside `[a, b]` the homology of `K` vanishes, so the sum may run over `[a - 1, b + 1]`, where
  -- it is induced by the decomposition of the identity of the short complex of the compression.
  rw [Finset.sum_filter_of_ne fun i _ h ↦ by_contra fun hi ↦ h (by simp [hi]),
    Finset.sum_subset (Finset.Icc_subset_Icc (by omega : a - 1 ≤ a) (by omega : b ≤ b + 1))
      fun i _ hi ↦ ?_]
  · have hsum : ∑ i ∈ Finset.Icc (a - 1) (b + 1),
        ShortComplex.homologyMap (compressionScπ n K r i ≫ compressionScι n K r i) = 𝟙 _ := by
      have := (ShortComplex.homologyFunctor C).map_sum
        (fun i ↦ compressionScπ n K r i ≫ compressionScι n K r i) (Finset.Icc (a - 1) (b + 1))
      rw [sum_compressionScπ_compressionScι n K a b r, CategoryTheory.Functor.map_id] at this
      simp only [ShortComplex.homologyFunctor_map] at this
      exact this.symm
    have hsum' : ∑ i ∈ Finset.Icc (a - 1) (b + 1),
        ShortComplex.homologyMap (compressionScπ n K r i) ≫
          ShortComplex.homologyMap (compressionScι n K r i) ≫
            ((compression n K).homologyIsoSc' (r - 1) r (r + 1) (by simp) (by simp)).inv =
        ((compression n K).homologyIsoSc' (r - 1) r (r + 1) (by simp) (by simp)).inv := by
      simp_rw [← Category.assoc, ← ShortComplex.homologyMap_comp]
      rw [← Preadditive.sum_comp, hsum, Category.id_comp]
    simp only [πCompressionHomology, ιCompressionHomology, Category.assoc, Iso.inv_hom_id_assoc]
    rw [← Preadditive.comp_sum, hsum', Iso.hom_inv_id]
  · have hZ : IsZero (K.homology i) := by
      rw [Finset.mem_Icc, not_and_or, not_le, not_le] at hi
      rcases hi with h | h
      · exact K.isZero_of_isGE a i h
      · exact K.isZero_of_isLE b i h
    rw [hZ.eq_of_tgt (πCompressionHomology n K r i) 0, zero_comp]

/-- For a complex supported in `[a, b]`, the homology of the compression in residue `r` is the
biproduct of the homology objects of `K` in the degrees of `[a, b]` congruent to `r`. -/
noncomputable def isBilimitCompressionHomologyBicone (r : ZMod n) :
    (compressionHomologyBicone n K a b r).IsBilimit :=
  isBilimitOfTotal _ <| by
    simp only [compressionHomologyBicone_π, compressionHomologyBicone_ι]
    exact (Finset.sum_coe_sort _ fun i ↦ πCompressionHomology n K r i ≫
      ιCompressionHomology n K r i).trans (sum_πCompressionHomology_ιCompressionHomology n K a b r)

/-- For a complex supported in `[a, b]`, the homology of its `n`-periodic compression in residue
`r` is isomorphic to the biproduct of the homology objects of `K` in the degrees of `[a, b]`
congruent to `r`: `H^r(Δₙ K) ≅ ⨁_{i ≡ r} H^i(K)`. -/
noncomputable def compressionHomologyIso [HasFiniteBiproducts C] (r : ZMod n) :
    (compression n K).homology r ≅
      ⨁ fun i : ({i ∈ Finset.Icc a b | (i : ZMod n) = r} : Finset ℤ) ↦ K.homology i :=
  biproduct.uniqueUpToIso _ (isBilimitCompressionHomologyBicone n K a b r)

/-- The isomorphism `compressionHomologyIso`, followed by the projection onto the summand of
degree `i`, is the projection `πCompressionHomology`. -/
@[reassoc (attr := simp)]
lemma compressionHomologyIso_hom_π [HasFiniteBiproducts C] (r : ZMod n)
    (i : ({i ∈ Finset.Icc a b | (i : ZMod n) = r} : Finset ℤ)) :
    (compressionHomologyIso n K a b r).hom ≫ biproduct.π _ i = πCompressionHomology n K r i :=
  biproduct.lift_π _ _

/-- The inclusion of the summand of degree `i`, followed by the inverse of
`compressionHomologyIso`, is the inclusion `ιCompressionHomology`. -/
@[reassoc (attr := simp)]
lemma ι_compressionHomologyIso_inv [HasFiniteBiproducts C] (r : ZMod n)
    (i : ({i ∈ Finset.Icc a b | (i : ZMod n) = r} : Finset ℤ)) :
    biproduct.ι _ i ≫ (compressionHomologyIso n K a b r).inv = ιCompressionHomology n K r i :=
  biproduct.ι_desc _ _

end Preadditive

section ModuleCat

variable {k : Type u} [DivisionRing k] (n : ℕ) (K : CochainComplex (ModuleCat.{v} k) ℤ)
  [HasCompression n K] (a b : ℤ) [K.IsStrictlyGE a] [K.IsStrictlyLE b]

/-- For a complex of vector spaces supported in `[a, b]` with finite-dimensional homology, the
dimension of the homology of its `n`-periodic compression in residue `r` is the sum of the
dimensions of its homology in the degrees congruent to `r`. -/
theorem finrank_homology_compression [∀ i, Module.Finite k (K.homology i)] (r : ZMod n) :
    finrank k ((compression n K).homology r) =
      ∑ i ∈ ({i ∈ Finset.Icc a b | (i : ZMod n) = r} : Finset ℤ), finrank k (K.homology i) := by
  rw [(compressionHomologyIso n K a b r ≪≫ ModuleCat.biproductIsoPi _).toLinearEquiv.finrank_eq,
    Module.finrank_pi_fintype]
  exact Finset.sum_coe_sort _ fun i ↦ finrank k (K.homology i)

/-- For positive `n` and a complex of vector spaces supported in `[a, b]` with finite-dimensional
homology, the total dimension of the homology of its `n`-periodic compression is the total
dimension of its homology. -/
theorem sum_finrank_homology_compression [NeZero n] [∀ i, Module.Finite k (K.homology i)] :
    ∑ r : ZMod n, finrank k ((compression n K).homology r) =
      ∑ i ∈ Finset.Icc a b, finrank k (K.homology i) := by
  simp_rw [finrank_homology_compression n K a b]
  exact Finset.sum_fiberwise _ _ _

/-- **The rank inequality for cyclically graded complexes.** Let `K` be a complex of vector spaces
supported in `[a, b]`, and let `D` be a `ZMod n`-graded complex of finite-dimensional vector
spaces, for positive `n`, whose homology is isomorphic in each residue to that of the `n`-periodic
compression of `K`. Then the total dimension of `D` is at least the total dimension of the
homology of `K`, which is finite-dimensional in each degree. A chain homotopy equivalence `e`
between `D` and the compression supplies the isomorphisms as `e.toHomologyIso`. -/
theorem sum_finrank_homology_le_sum_finrank_X [NeZero n]
    (D : HomologicalComplex (ModuleCat.{v} k) (ComplexShape.up (ZMod n)))
    [∀ r, Module.Finite k (D.X r)] (e : ∀ r, D.homology r ≅ (compression n K).homology r) :
    ∑ i ∈ Finset.Icc a b, finrank k (K.homology i) ≤ ∑ r : ZMod n, finrank k (D.X r) := by
  -- The homology of `K` in degree `i` is a retract of that of `D` in residue `i`, which is a
  -- subquotient of the finite-dimensional `D.X i`.
  have : ∀ i, Module.Finite k (K.homology i) := fun i ↦ by
    have : Module.Finite k (D.sc i).X₂ := inferInstanceAs (Module.Finite k (D.X i))
    have : Module.Finite k (D.homology i) := (D.sc i).finite_homology
    have h : (ιCompressionHomology n K i i ≫ (e i).inv) ≫
        ((e i).hom ≫ πCompressionHomology n K i i) = 𝟙 _ := by
      simp
    exact Module.Finite.of_injective _
      (Function.LeftInverse.injective (g := ((e i).hom ≫ πCompressionHomology n K i i).hom)
        fun x ↦ congr(ModuleCat.Hom.hom $h x))
  rw [← sum_finrank_homology_compression n K a b]
  refine Finset.sum_le_sum fun r _ ↦ ?_
  rw [← (e r).toLinearEquiv.finrank_eq]
  exact D.finrank_homology_le_finrank_X r

end ModuleCat

end TauCeti.PeriodicComplex

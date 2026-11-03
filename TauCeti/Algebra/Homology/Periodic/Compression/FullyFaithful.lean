/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.Periodic.Compression.Component

/-!
# The orbit functor `K^b(C)/[n] ⥤ K_n(C)` is fully faithful

Let `C` be a preadditive category with finite coproducts and let `n` be positive. Compression
`K^b(C) ⥤ K_n(C)` descends to the orbit functor
`TauCeti.PeriodicComplex.orbitCompressionFunctor n : K^b(C)/[n] ⥤ K_n(C)`, which sends a
homogeneous piece `f : X ⟶ Y⟦n * j⟧` of an orbit morphism to the compression of `f` followed by
the `j`-th power of the periodicity isomorphism. This file proves that the orbit functor is fully
faithful:

`⨁_{j : ℤ} Hom_{K^b(C)}(X, Y⟦n * j⟧) ≅ Hom_{K_n(C)}(Δₙ X, Δₙ Y)`.

The `j`-th power of the periodicity isomorphism is, up to a sign, the periodicity isomorphism for
the shift by `n * j` (`TauCeti.PeriodicComplex.exists_periodicityZPow_hom_app_eq`), because the
periodicity isomorphisms compose up to the signs
`TauCeti.PeriodicComplex.homotopyCompressionFunctorPeriodicityIso_shiftComp_hom_app`. Hence the
image of an orbit morphism is represented by the sum of the compressions of its homogeneous pieces,
transported along the periodicity isomorphisms. Faithfulness follows by extracting the components
of degree `n * j` (`TauCeti.PeriodicComplex.compressionComponent`), which is compatible with
homotopies, and fullness from the decomposition of every morphism between compressions of bounded
complexes into its finitely many components. The hypothesis that `n` is nonzero is needed: for
`n = 0` an orbit hom group is a direct sum of infinitely many copies of a hom group of `K^b(C)`,
all sent to the same hom group of `K_0(C)`.

For finitely generated modules over a finite-dimensional algebra of finite global dimension,
bounded complexes of projectives model the bounded derived category and periodic complexes of
projectives model the periodic derived category. This computation then underlies the full
faithfulness of the derived orbit functor `D^b(C)/[n] ⥤ D_n(C)` (Stai, Lemma 3.12).

## Main results

* `TauCeti.PeriodicComplex.exists_periodicityZPow_hom_app_eq`: the powers of the periodicity
  isomorphism are the periodicity isomorphisms for the multiples of `n`, up to signs.
* `TauCeti.PeriodicComplex.faithful_orbitCompressionFunctor`: the orbit functor is faithful.
* `TauCeti.PeriodicComplex.full_orbitCompressionFunctor`: the orbit functor is full.

## References

* T. Stai, *The triangulated hull of periodic complexes*, Mathematical Research Letters **25**
  (2018), 199–236, Section 3.3 and Lemma 3.12.
* B. Keller, *On triangulated orbit categories*, Documenta Mathematica **10** (2005),
  551–581, Section 1.
-/

public section

open CategoryTheory Limits

universe v u

namespace TauCeti.PeriodicComplex

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasFiniteCoproducts C] (n : ℕ)

open HomotopyCategory.Bounded (quotient quotient_obj_surjective)

/-- The `j`-th power of the periodicity isomorphism of `K^b(C) ⥤ K_n(C)` for the shift by `n` is,
up to a sign independent of the object, the periodicity isomorphism for the shift by `n * j`. -/
lemma exists_periodicityZPow_hom_app_eq (j : ℤ) :
    ∃ ε : ℤˣ, ∀ X : HomotopyCategory.Bounded C,
      ((homotopyCompressionFunctorPeriodicityIso n n (by simp)).periodicityZPow j).hom.app X =
        ε • (homotopyCompressionFunctorPeriodicityIso n (n * j) (by simp)).hom.app X := by
  set φ := homotopyCompressionFunctorPeriodicityIso (C := C) n n (by simp)
  -- `φ` composed with the periodicity isomorphism for `n * j` is, up to a sign, the one for
  -- `n * j'` with `j' = j + 1`.
  have step (j j' : ℤ) (hj : j + 1 = j') (X : HomotopyCategory.Bounded C) :
      (φ.shiftComp (homotopyCompressionFunctorPeriodicityIso n (n * j) (by simp))
        (by rw [← hj]; ring : (n : ℤ) + n * j = n * j')).hom.app X =
        ((n : ℤ) * (n * j)).negOnePow •
          (homotopyCompressionFunctorPeriodicityIso n (n * j') (by simp)).hom.app X :=
    homotopyCompressionFunctorPeriodicityIso_shiftComp_hom_app n _ _ _ _ _ _ _ X
  induction j using Int.induction_on with
  | zero =>
    refine ⟨1, fun X ↦ ?_⟩
    rw [Iso.periodicityZPow_zero, one_smul,
      homotopyCompressionFunctorPeriodicityIso_eq_of_eq_zero n _ _ (mul_zero _)]
  | succ j ih =>
    obtain ⟨ε, hε⟩ := ih
    refine ⟨ε * ((n : ℤ) * (n * j)).negOnePow, fun X ↦ ?_⟩
    have h := step j (j + 1) rfl X
    rw [Iso.shiftComp_hom_app] at h
    simp only [Iso.periodicityZPow_succ φ j (j + 1) rfl, Iso.shiftComp_hom_app, hε,
      Linear.units_smul_comp, Linear.comp_units_smul, h, smul_smul]
  | pred j ih =>
    obtain ⟨ε, hε⟩ := ih
    set s := ((n : ℤ) * (n * (-j - 1))).negOnePow
    set χ := homotopyCompressionFunctorPeriodicityIso (C := C) n (n * (-j - 1)) (by simp)
    refine ⟨ε * s, fun X ↦ ?_⟩
    -- The claim holds on objects of the form `Y⟦n⟧`, after cancelling the composition with `φ`.
    have key (Y : HomotopyCategory.Bounded C) :
        (φ.periodicityZPow (-j - 1)).hom.app (Y⟦(n : ℤ)⟧) = (ε * s) • χ.hom.app (Y⟦(n : ℤ)⟧) := by
      have h := hε Y
      have h' := step (-j - 1) (-j) (by ring) Y
      rw [Iso.periodicityZPow_succ φ (-j - 1) (-j) (by ring), Iso.shiftComp_hom_app] at h
      rw [Iso.shiftComp_hom_app] at h'
      rw [← cancel_epi ((homotopyCompressionFunctor n).map
          ((CategoryTheory.shiftFunctorAdd' _ (n : ℤ) (n * (-j - 1)) (n * -j)
            (by ring)).hom.app Y)), ← cancel_mono (φ.hom.app Y)]
      simp only [χ, s, Category.assoc, h, Linear.units_smul_comp, Linear.comp_units_smul, h',
        smul_smul, mul_assoc, Int.units_mul_self, mul_one]
    -- It transports to every object along `X ≅ X⟦-n⟧⟦n⟧`.
    let e : X⟦-(n : ℤ)⟧⟦(n : ℤ)⟧ ≅ X :=
      (shiftFunctorCompIsoId (HomotopyCategory.Bounded C) (-(n : ℤ)) n (neg_add_cancel _)).app X
    have nat₁ := (φ.periodicityZPow (-j - 1)).hom.naturality e.hom
    have nat₂ := χ.hom.naturality e.hom
    rw [← cancel_epi ((CategoryTheory.shiftFunctor _ ((n : ℤ) * (-j - 1)) ⋙
      homotopyCompressionFunctor n).map e.hom), nat₁, Linear.comp_units_smul, nat₂, key,
      Linear.units_smul_comp]

variable {n} in
/-- If the `j`-th power of the periodicity isomorphism is `ε` times the periodicity isomorphism for
the shift by `n * j`, the orbit functor sends the homogeneous piece of degree `j` given by a map
`f : K ⟶ L⟦n * j⟧` of bounded complexes to `ε` times the class of the compression of `f` followed
by the periodicity isomorphism, up to the identifications of the descended compression on classes
of bounded complexes. -/
private lemma orbitCompressionFunctor_map_homOf {K L : CochainComplex.Bounded C} {j : ℤ}
    {ε : ℤˣ} (hε : ∀ X : HomotopyCategory.Bounded C,
      ((homotopyCompressionFunctorPeriodicityIso n n (by simp)).periodicityZPow j).hom.app X =
        ε • (homotopyCompressionFunctorPeriodicityIso n (n * j) (by simp)).hom.app X)
    (f : K ⟶ L⟦(n : ℤ) * j⟧) :
    Eq (α := (quotient C ⋙ homotopyCompressionFunctor n).obj K ⟶
        (quotient C ⋙ homotopyCompressionFunctor n).obj L)
      ((orbitCompressionFunctor n).map (OrbitCategory.homOf j
        ((quotient C).map f ≫ ((quotient C).commShiftIso ((n : ℤ) * j)).hom.app L)))
      (ε • ((quotientCompHomotopyCompressionFunctorIso n).hom.app K ≫
        (HomotopyCategory.quotient C _).map ((compressionFunctor n).map f ≫
          (compressionFunctorPeriodicityIso n ((n : ℤ) * j) (by simp)).hom.app L) ≫
        (quotientCompHomotopyCompressionFunctorIso n).inv.app L)) := by
  have hE := (quotientCompHomotopyCompressionFunctorIso n).hom.naturality f
  simp only [Functor.comp_map] at hE
  rw [OrbitCategory.lift_map_homOf, hε, Linear.comp_units_smul, Functor.map_comp, Category.assoc,
    map_commShiftIso_hom_app_comp_homotopyCompressionFunctorPeriodicityIso_hom_app,
    reassoc_of% hE, Functor.map_comp_assoc]

variable {n} in
/-- The orbit functor sends a finite sum of homogeneous pieces given by maps
`f j : K ⟶ L⟦n * j⟧` of bounded complexes to the class of the signed sum of their compressions,
each followed by the periodicity isomorphism, up to the identifications of the descended
compression on classes of bounded complexes. -/
private lemma orbitCompressionFunctor_map_sum_homOf {K L : CochainComplex.Bounded C}
    (S : Finset ℤ) {ε : ℤ → ℤˣ} (hε : ∀ (j : ℤ) (X : HomotopyCategory.Bounded C),
      ((homotopyCompressionFunctorPeriodicityIso n n (by simp)).periodicityZPow j).hom.app X =
        ε j • (homotopyCompressionFunctorPeriodicityIso n (n * j) (by simp)).hom.app X)
    (f : ∀ j : ℤ, K ⟶ L⟦(n : ℤ) * j⟧) :
    Eq (α := (quotient C ⋙ homotopyCompressionFunctor n).obj K ⟶
        (quotient C ⋙ homotopyCompressionFunctor n).obj L)
      ((orbitCompressionFunctor n).map (∑ j ∈ S, OrbitCategory.homOf j
        ((quotient C).map (f j) ≫ ((quotient C).commShiftIso ((n : ℤ) * j)).hom.app L)))
      ((quotientCompHomotopyCompressionFunctorIso n).hom.app K ≫
        (HomotopyCategory.quotient C _).map (∑ j ∈ S, ε j • ((compressionFunctor n).map (f j) ≫
          (compressionFunctorPeriodicityIso n ((n : ℤ) * j) (by simp)).hom.app L)) ≫
        (quotientCompHomotopyCompressionFunctorIso n).inv.app L) := by
  rw [Functor.map_sum, Functor.map_sum, Preadditive.sum_comp, Preadditive.comp_sum]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [orbitCompressionFunctor_map_homOf (hε j) (f j)]
  simp [Functor.map_units_smul]

variable {n} in
/-- If the class of a finite signed sum of the compressions of maps `f j : K ⟶ L⟦n * j⟧` of bounded
complexes, each followed by the periodicity isomorphism, vanishes, then every `f j` vanishes in the
bounded homotopy category: its class is the component of degree `n * j` of that sum. -/
private lemma quotient_map_eq_zero_of_quotient_map_sum_eq_zero [NeZero n]
    {K L : CochainComplex.Bounded C} (S : Finset ℤ) (ε : ℤ → ℤˣ)
    (f : ∀ j : ℤ, K ⟶ L⟦(n : ℤ) * j⟧)
    (h : (HomotopyCategory.quotient C _).map (∑ j ∈ S, ε j •
      (compressionMap (L := L.obj⟦(n : ℤ) * j⟧) n
        ((f j).hom ≫ ((CochainComplex.Bounded.ι C).commShiftIso ((n : ℤ) * j)).hom.app L) ≫
          (compressionPeriodicityIso n L.obj ((n : ℤ) * j) (by simp)).hom)) = 0)
    {j : ℤ} (hj : j ∈ S) : (quotient C).map (f j) = 0 := by
  have hq := HomotopyCategory.eq_of_homotopy _ _ (compressionComponentHomotopy n ((n : ℤ) * j)
    (HomotopyCategory.homotopyOfEq _ 0 (by rw [h, Functor.map_zero])))
  rw [map_sum, Finset.sum_eq_single_of_mem j hj fun l _ hlj ↦ ?_] at hq
  · simp only [Units.smul_def, map_zsmul, map_zero, Functor.map_zero, Functor.map_zsmul,
      compressionComponent_compressionMap_comp_compressionPeriodicityIso_hom] at hq
    rw [← Units.smul_def, smul_eq_zero_iff_eq, Functor.map_comp] at hq
    refine ObjectProperty.hom_ext _ ?_
    rw [HomotopyCategory.Bounded.quotient_map_hom, ObjectProperty.zero_hom,
      (cancel_mono _).mp (hq.trans Limits.zero_comp.symm)]
    simp
  · rw [Units.smul_def, map_zsmul,
      compressionComponent_compressionMap_comp_compressionPeriodicityIso_hom_of_ne _ _
        (by simpa [NeZero.ne n] using hlj.symm), smul_zero]

/-- For positive `n`, the orbit functor `K^b(C)/[n] ⥤ K_n(C)` is faithful. -/
instance faithful_orbitCompressionFunctor [NeZero n] :
    (orbitCompressionFunctor (C := C) n).Faithful where
  map_injective {X Y} x y hxy := by
    obtain ⟨X⟩ := X
    obtain ⟨Y⟩ := Y
    obtain ⟨K, rfl⟩ := quotient_obj_surjective X
    obtain ⟨L, rfl⟩ := quotient_obj_surjective Y
    rw [← sub_eq_zero, ← Functor.map_sub] at hxy
    rw [← sub_eq_zero]
    generalize x - y = z at hxy ⊢
    -- Read `z` as an element of the direct sum of its homogeneous pieces.
    obtain ⟨z, rfl⟩ : ∃ z' : DirectSum ℤ fun j : ℤ ↦
        ShiftedHom ((quotient C).obj K) ((quotient C).obj L) ((n : ℤ) * j), z' = z := ⟨z, rfl⟩
    classical
    choose ε hε using exists_periodicityZPow_hom_app_eq (C := C) n
    -- Represent each homogeneous piece of `z` by a map of bounded complexes.
    let f (j : ℤ) : K ⟶ L⟦(n : ℤ) * j⟧ :=
      (quotient C).preimage (z j ≫ ((quotient C).commShiftIso ((n : ℤ) * j)).inv.app L)
    have hf (j : ℤ) :
        (quotient C).map (f j) ≫ ((quotient C).commShiftIso ((n : ℤ) * j)).hom.app L = z j := by
      simp [f]
    have hz : ∑ j ∈ z.support, OrbitCategory.homOf j
        ((quotient C).map (f j) ≫ ((quotient C).commShiftIso ((n : ℤ) * j)).hom.app L) = z := by
      simp only [hf, OrbitCategory.homOf_def]
      exact DirectSum.sum_support_of z
    -- The signed sum of the compressions of the pieces represents the image of `z`, which is zero.
    have h₀ : (quotientCompHomotopyCompressionFunctorIso n).hom.app K ≫
        (HomotopyCategory.quotient C _).map (∑ j ∈ z.support, ε j •
          ((compressionFunctor n).map (f j) ≫
            (compressionFunctorPeriodicityIso n ((n : ℤ) * j) (by simp)).hom.app L)) ≫
          (quotientCompHomotopyCompressionFunctorIso n).inv.app L = 0 :=
      (orbitCompressionFunctor_map_sum_homOf z.support hε f).symm.trans (by rw [hz]; exact hxy)
    rw [← cancel_epi ((quotientCompHomotopyCompressionFunctorIso n).inv.app K),
      ← cancel_mono ((quotientCompHomotopyCompressionFunctorIso n).hom.app L)] at h₀
    simp only [Iso.inv_hom_id_app_assoc, Category.assoc, Iso.inv_hom_id_app, Functor.comp_obj,
      Category.comp_id, Limits.zero_comp, Limits.comp_zero] at h₀
    have hsum : ∑ j ∈ z.support, ε j • (compressionMap (L := L.obj⟦(n : ℤ) * j⟧) n
        ((f j).hom ≫ ((CochainComplex.Bounded.ι C).commShiftIso ((n : ℤ) * j)).hom.app L) ≫
          (compressionPeriodicityIso n L.obj ((n : ℤ) * j) (by simp)).hom) =
        eqToHom (compressionFunctor_obj n K).symm ≫ (∑ j ∈ z.support, ε j •
          ((compressionFunctor n).map (f j) ≫
            (compressionFunctorPeriodicityIso n ((n : ℤ) * j) (by simp)).hom.app L)) ≫
          eqToHom (compressionFunctor_obj n L) := by
      simp only [Preadditive.comp_sum, Preadditive.sum_comp, Linear.comp_units_smul,
        Linear.units_smul_comp, Category.assoc,
        compressionFunctor_map_comp_compressionFunctorPeriodicityIso_hom_app]
    refine DFinsupp.ext fun j ↦ ?_
    by_cases hj : j ∈ z.support
    · rw [← hf j, quotient_map_eq_zero_of_quotient_map_sum_eq_zero z.support ε f
        (by rw [hsum, Functor.map_comp, Functor.map_comp, h₀, Limits.zero_comp, Limits.comp_zero])
        hj, Limits.zero_comp, DFinsupp.zero_apply]
    · exact DFinsupp.notMem_support_iff.mp hj

/-- For positive `n`, the orbit functor `K^b(C)/[n] ⥤ K_n(C)` is full. -/
instance full_orbitCompressionFunctor [NeZero n] :
    (orbitCompressionFunctor (C := C) n).Full where
  map_surjective {X Y} φ := by
    obtain ⟨X⟩ := X
    obtain ⟨Y⟩ := Y
    obtain ⟨K, rfl⟩ := quotient_obj_surjective X
    obtain ⟨L, rfl⟩ := quotient_obj_surjective Y
    -- Read `φ` as a morphism between the images of the underlying objects.
    obtain ⟨φ, rfl⟩ : ∃ φ' : (quotient C ⋙ homotopyCompressionFunctor n).obj K ⟶
        (quotient C ⋙ homotopyCompressionFunctor n).obj L, φ' = φ := ⟨φ, rfl⟩
    choose ε hε using exists_periodicityZPow_hom_app_eq (C := C) n
    -- Represent `φ` by a chain map `g` between the compressions of `K` and `L`, and decompose `g`
    -- into its finitely many components.
    obtain ⟨g, hg⟩ := (HomotopyCategory.quotient C _).map_surjective
      (eqToHom (congrArg (HomotopyCategory.quotient C _).obj (compressionFunctor_obj n K)).symm ≫
        (quotientCompHomotopyCompressionFunctorIso n).inv.app K ≫ φ ≫
          (quotientCompHomotopyCompressionFunctorIso n).hom.app L ≫
            eqToHom (congrArg (HomotopyCategory.quotient C _).obj (compressionFunctor_obj n L)))
    obtain ⟨J, hJ⟩ := exists_sum_compressionMap_compressionComponent_comp n K.property L.property g
    -- The homogeneous pieces given by the components of `g`, with the signs of the powers of the
    -- periodicity isomorphism.
    let f (j : ℤ) : K ⟶ L⟦(n : ℤ) * j⟧ := ε j • ObjectProperty.homMk
      (compressionComponent n ((n : ℤ) * j) g ≫
        ((CochainComplex.Bounded.ι C).commShiftIso ((n : ℤ) * j)).inv.app L)
    refine ⟨∑ j ∈ J, OrbitCategory.homOf j
      ((quotient C).map (f j) ≫ ((quotient C).commShiftIso ((n : ℤ) * j)).hom.app L),
      (orbitCompressionFunctor_map_sum_homOf J hε f).trans ?_⟩
    have hsum : ∑ j ∈ J, ε j • ((compressionFunctor n).map (f j) ≫
        (compressionFunctorPeriodicityIso n ((n : ℤ) * j) (by simp)).hom.app L) =
        eqToHom (compressionFunctor_obj n K) ≫ g ≫ eqToHom (compressionFunctor_obj n L).symm := by
      rw [← hJ, Preadditive.sum_comp, Preadditive.comp_sum]
      refine Finset.sum_congr rfl fun j _ ↦ ?_
      have hX := compressionFunctor_map_comp_compressionFunctorPeriodicityIso_hom_app n
        ((n : ℤ) * j) (by simp) (ObjectProperty.homMk (compressionComponent n ((n : ℤ) * j) g ≫
          ((CochainComplex.Bounded.ι C).commShiftIso ((n : ℤ) * j)).inv.app L))
      simp only [ObjectProperty.homMk_hom, Category.assoc, Iso.inv_hom_id_app, Functor.comp_obj,
        ObjectProperty.ι_obj, Category.comp_id] at hX
      -- The sign of the piece cancels the sign of the power of the periodicity isomorphism.
      simp only [f, Units.smul_def, Functor.map_zsmul, Preadditive.zsmul_comp, smul_smul,
        Int.units_coe_mul_self, one_smul]
      rw [← hX]
      simp
    rw [hsum, Functor.map_comp, Functor.map_comp, hg]
    simp [eqToHom_map]

end TauCeti.PeriodicComplex

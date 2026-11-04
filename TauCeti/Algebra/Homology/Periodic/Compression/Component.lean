/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.Periodic.Compression.Periodicity
public import TauCeti.Algebra.Homology.Periodic.Unfold

/-!
# Homogeneous components of morphisms between compressions

A morphism `g : Δₙ K ⟶ Δₙ L` between the `n`-periodic compressions of two integer-indexed
complexes sends the summand `Kⁱ` of `(Δₙ K)^r` into the summands `L^(i + k)` with `k` divisible
by `n`. For a fixed `k`, these pieces form a chain map `K ⟶ L⟦k⟧` after the sign `(-1)^(k * i)`
on the summand of degree `i`: this is the component `TauCeti.PeriodicComplex.compressionComponent`
of degree `k` of `g`. It factors as the inclusion of `K` into the unfolding of its compression,
the unfolding of `g`, and a projection from the unfolding of `Δₙ L` onto `L⟦k⟧`, so it is additive
and carries homotopies to homotopies.

The component of degree `k'` of `Δₙ f` followed by the periodicity isomorphism
`Δₙ (L⟦k⟧) ≅ Δₙ L` is `f` when `k' = k` and zero otherwise
(`TauCeti.PeriodicComplex.compressionComponent_compressionMap_comp_compressionPeriodicityIso_hom`).
Conversely, when only finitely many components can be nonzero, for instance for bounded `K` and
`L` and positive `n`, every morphism `Δₙ K ⟶ Δₙ L` is the sum of its components, transported back
along compression and periodicity
(`TauCeti.PeriodicComplex.sum_compressionMap_compressionComponent_comp`). Thus the morphisms
`Δₙ K ⟶ Δₙ L` are the finite sums of compressions of morphisms `K ⟶ L⟦n * j⟧`, and the same holds
up to homotopy. This is the computation behind the full faithfulness of the orbit functor
`K^b(C)/[n] ⥤ K_n(C)`.

## Main definitions

* `TauCeti.PeriodicComplex.toUnfoldCompression`: the inclusion `K ⟶ unfold (Δₙ K)`.
* `TauCeti.PeriodicComplex.fromUnfoldCompression`: the signed projection `unfold (Δₙ L) ⟶ L⟦k⟧`.
* `TauCeti.PeriodicComplex.compressionComponent`: the component of degree `k` of a morphism
  between compressions.

## References

* T. Stai, *The triangulated hull of periodic complexes*, Mathematical Research Letters **25**
  (2018), 199–236, Section 3.3.
-/

public section

open CategoryTheory Limits

universe v u

namespace TauCeti.PeriodicComplex

variable {C : Type u} [Category.{v} C] [Preadditive C] (n : ℕ)

section Unfold

variable (K L : CochainComplex C ℤ) [HasCompression n K] [HasCompression n L]

/-- The inclusion of a complex into the unfolding of its compression: in degree `i`, the
inclusion of the summand of degree `i` into the term of residue `i` of the compression. -/
noncomputable def toUnfoldCompression : K ⟶ (unfoldFunctor C n).obj (compression n K) where
  f i := ιCompression n K i i rfl
  comm' i j hij := by
    obtain rfl : i + 1 = j := hij
    rw [unfoldFunctor_obj_d]
    exact ιCompression_d n K i (i + 1) rfl _ _ rfl rfl

@[simp]
lemma toUnfoldCompression_f (i : ℤ) :
    (toUnfoldCompression n K).f i = ιCompression n K i i rfl :=
  (rfl)

/-- The projection of the unfolding of the compression of `L` onto `L⟦k⟧`: in degree `i`, the
projection of the term of residue `i` onto the summand of degree `i + k`, with the sign
`(-1)^(k * i)`. It is zero in every degree when `k` is not divisible by `n`. -/
noncomputable def fromUnfoldCompression (k : ℤ) :
    (unfoldFunctor C n).obj (compression n L) ⟶ L⟦k⟧ where
  f i := (k * i).negOnePow •
    (πCompression n L i (i + k) ≫ (L.shiftFunctorObjXIso k i (i + k) rfl).inv)
  comm' i j hij := by
    obtain rfl : i + 1 = j := hij
    rw [unfoldFunctor_obj_d, Linear.comp_units_smul,
      d_πCompression_assoc n L _ _ (by push_cast; rfl) (i + k) (i + 1 + k) (by omega)]
    simp only [CochainComplex.shiftFunctor_obj_d', CochainComplex.shiftFunctorObjXIso,
      HomologicalComplex.XIsoOfEq_rfl, Iso.refl_inv, Category.comp_id,
      Linear.units_smul_comp, Linear.comp_units_smul, smul_smul]
    -- The signs agree: `(-1)^(k * (i + 1)) = (-1)^(k * i) * (-1)^k`.
    rw [mul_add, mul_one, Int.negOnePow_add, mul_comm]

@[simp]
lemma fromUnfoldCompression_f (k i : ℤ) :
    (fromUnfoldCompression n L k).f i = (k * i).negOnePow •
      (πCompression n L i (i + k) ≫ (L.shiftFunctorObjXIso k i (i + k) rfl).inv) :=
  (rfl)

end Unfold

section Component

variable {K L : CochainComplex C ℤ} [HasCompression n K] [HasCompression n L]

/-- The component of degree `k` of a morphism `g : Δₙ K ⟶ Δₙ L` between compressions: the chain
map `K ⟶ L⟦k⟧` whose component in degree `i` is the piece `Kⁱ ⟶ L^(i + k)` of `g`, with the sign
`(-1)^(k * i)`. It is the inclusion of `K` into the unfolding of its compression, followed by the
unfolding of `g` and the projection onto `L⟦k⟧`. -/
noncomputable def compressionComponent (k : ℤ) :
    (compression n K ⟶ compression n L) →+ (K ⟶ L⟦k⟧) :=
  AddMonoidHom.mk' (fun g ↦ toUnfoldCompression n K ≫ (unfoldFunctor C n).map g ≫
    fromUnfoldCompression n L k) (fun g g' ↦ by
      simp only [Functor.map_add, Preadditive.add_comp, Preadditive.comp_add])

/-- The component of degree `k` of `g` restricts, on the summand of degree `i`, to the piece of
`g` with values in the summand of degree `i + k`, with the sign `(-1)^(k * i)`. -/
lemma compressionComponent_f (k : ℤ) (g : compression n K ⟶ compression n L) (i : ℤ) :
    (compressionComponent n k g).f i = (k * i).negOnePow •
      (ιCompression n K i i rfl ≫ g.f i ≫ πCompression n L i (i + k) ≫
        (L.shiftFunctorObjXIso k i (i + k) rfl).inv) := by
  simp [compressionComponent]

/-- A homotopy between morphisms of compressions induces a homotopy between their components of
any degree. -/
noncomputable def compressionComponentHomotopy (k : ℤ)
    {g g' : compression n K ⟶ compression n L} (h : Homotopy g g') :
    Homotopy (compressionComponent n k g) (compressionComponent n k g') :=
  (h.unfoldPeriodic.compRight _).compLeft _

variable {n} in
/-- The component of degree `k'` of the compression of `f : K ⟶ L⟦k⟧`, followed by the
periodicity isomorphism, vanishes unless `k' = k`. -/
@[simp]
lemma compressionComponent_compressionMap_comp_compressionPeriodicityIso_hom_of_ne
    {k k' : ℤ} (hk : (k : ZMod n) = 0) (f : K ⟶ L⟦k⟧) (hkk' : k' ≠ k) :
    compressionComponent n k'
      (compressionMap n f ≫ (compressionPeriodicityIso n L k hk).hom) = 0 := by
  ext i
  have hne : i + k ≠ i + k' := by omega
  simp [compressionComponent_f, hne]

variable {n} in
/-- The component of degree `k` of the compression of `f : K ⟶ L⟦k⟧`, followed by the
periodicity isomorphism `Δₙ (L⟦k⟧) ≅ Δₙ L`, is `f`. -/
@[simp]
lemma compressionComponent_compressionMap_comp_compressionPeriodicityIso_hom
    {k : ℤ} (hk : (k : ZMod n) = 0) (f : K ⟶ L⟦k⟧) :
    compressionComponent n k
      (compressionMap n f ≫ (compressionPeriodicityIso n L k hk).hom) = f := by
  ext i
  simp [compressionComponent_f, smul_smul, CochainComplex.shiftFunctorObjXIso]

/-- If the pieces `Kⁱ ⟶ L^(i + n * j)` can only be nonzero for `j` in a finite set `J`, a
morphism `Δₙ K ⟶ Δₙ L` between compressions is the sum over `J` of the compressions of its
components of degree `n * j`, followed by the periodicity isomorphisms. -/
lemma sum_compressionMap_compressionComponent_comp [NeZero n]
    (g : compression n K ⟶ compression n L) (J : Finset ℤ)
    (hJ : ∀ i j : ℤ, ¬IsZero (K.X i) → ¬IsZero (L.X (i + n * j)) → j ∈ J) :
    ∑ j ∈ J, compressionMap n (compressionComponent n (n * j) g) ≫
      (compressionPeriodicityIso n L (n * j) (by simp)).hom = g := by
  ext r i hi
  by_cases hK : IsZero (K.X i)
  · exact hK.eq_of_src _ _
  -- Expand the identity of `(Δₙ L)^r` as the sum of the summand projections over `i + n * J`.
  have hinj : Set.InjOn (fun j : ℤ ↦ i + n * j) J := fun j₁ _ j₂ _ h ↦ by
    simpa [NeZero.ne n] using h
  have hT : ∀ m : ℤ, (m : ZMod n) = r → m ∉ J.image (fun j ↦ i + n * j) → IsZero (L.X m) := by
    intro m hm hmT
    obtain ⟨j, hj⟩ := (ZMod.intCast_eq_intCast_iff_dvd_sub i m n).mp (hi.trans hm.symm)
    by_contra hL
    refine hmT (Finset.mem_image.mpr ⟨j, hJ i j hK (by rwa [← hj, add_sub_cancel]), ?_⟩)
    omega
  rw [← Category.comp_id (g.f r), ← sum_πCompression_ιCompressionOrZero n L r _ hT,
    Finset.sum_image hinj, Preadditive.comp_sum, Preadditive.comp_sum,
    ← HomologicalComplex.Hom.fAddMonoidHom_apply, map_sum, Preadditive.comp_sum]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  have hj : ((i + n * j : ℤ) : ZMod n) = r := by simp [← hi]
  simp [compressionComponent_f, smul_smul, CochainComplex.shiftFunctorObjXIso,
    ιCompressionOrZero_eq n L _ _ hj]
  -- The two sides differ only in how the residue `r` of `i` is written.
  cases hi
  rfl

/-- A morphism `Δₙ K ⟶ Δₙ L` between the compressions of bounded complexes is a finite sum of the
compressions of its components of degrees `n * j`, followed by the periodicity isomorphisms. -/
lemma exists_sum_compressionMap_compressionComponent_comp [NeZero n]
    (hK : CochainComplex.bounded C K) (hL : CochainComplex.bounded C L)
    (g : compression n K ⟶ compression n L) :
    ∃ J : Finset ℤ, ∑ j ∈ J, compressionMap n (compressionComponent n (n * j) g) ≫
      (compressionPeriodicityIso n L (n * j) (by simp)).hom = g := by
  obtain ⟨sK, hsK⟩ := (CochainComplex.bounded_iff_exists_finset_isZero_X C K).1 hK
  obtain ⟨sL, hsL⟩ := (CochainComplex.bounded_iff_exists_finset_isZero_X C L).1 hL
  refine ⟨(sK ×ˢ sL).image fun p ↦ (p.2 - p.1) / (n : ℤ),
    sum_compressionMap_compressionComponent_comp n g _ fun i j hi hj ↦ ?_⟩
  refine Finset.mem_image.mpr ⟨(i, i + n * j), Finset.mem_product.mpr
    ⟨by_contra fun h ↦ hi (hsK i h), by_contra fun h ↦ hj (hsL _ h)⟩, ?_⟩
  simp [NeZero.ne n]

end Component

end TauCeti.PeriodicComplex

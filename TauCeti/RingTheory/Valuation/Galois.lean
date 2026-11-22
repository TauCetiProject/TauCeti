/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.FieldTheory.PurelyInseparable.PerfectClosure
public import Mathlib.RingTheory.Valuation.ValuationSubring
import TauCeti.FieldTheory.Galois.AbsoluteGaloisGroup.Basic
import TauCeti.FieldTheory.Galois.FixedField
import TauCeti.RingTheory.Valuation.AlgebraicExtension
import TauCeti.RingTheory.Valuation.ValuationSubring

/-!
# Conjugacy of the extensions of a valuation subring

Let `L / K` be a field extension and `G` a finite group acting on `L` by automorphisms fixing `K`,
whose fixed field is purely inseparable over `K`. This file shows that `G` acts transitively on
the valuation subrings of `L` lying over a given valuation subring `O` of `K`: two valuation
subrings `A` and `B` of `L` with `A ∩ K = B ∩ K` satisfy `g • A = B` for some `g ∈ G`. No
assumption is made on the rank of the valuations or on the order of `G`.

The two standard instances of the hypothesis are a finite Galois group (the fixed field is `K`)
and the automorphism group `Gal(L/K)` of a normal extension, when finite: its fixed field is the
relative perfect closure `perfectClosure K L` (`TauCeti.mem_perfectClosure_iff_fixed`). Along a
purely inseparable extension a valuation subring extends uniquely
(`ValuationSubring.comap_injective_of_isPurelyInseparable`), so `O` has a unique extension to the
fixed field, and the extensions of `O` to `L` all lie over it and are permuted transitively by `G`.

## Method

Suppose `B` is not conjugate to `A`. The finitely many conjugates of `A` and of `B` all lie over
`O`, and `L / K` is algebraic, so `ValuationSubring.exists_valuation_eq_one_and_lt_one` gives an
element `x` that is a unit of every conjugate of `A` and a nonunit of every conjugate of `B`. Its
orbit product `N = ∏_{g ∈ G} g • x` is `G`-invariant, so a `p`-power `N ^ q` lies in `K`. Then
`N ^ q` is a unit of `A`, while it is a nonunit of `B`; these two conditions on an element of `K`
depend only on `O = A ∩ K = B ∩ K`, a contradiction.

## Main results

* `ValuationSubring.exists_smul_eq_of_comap_eq` and
  `ValuationSubring.comap_eq_comap_iff_exists_smul_eq`: **the extensions of a valuation subring
  are conjugate** under a finite group whose fixed field is purely inseparable over `K`.
* `ValuationSubring.exists_algEquiv_smul_eq_of_comap_eq`: the case of a normal extension with
  finite automorphism group.

## References

* D. Hansen, *Quotients of adic spaces by finite groups*, Math. Res. Lett. 28 (2021), proof of
  Theorem 3.1, Step 1.
* A. J. Engler and A. Prestel, *Valued Fields*, Springer Monographs in Mathematics, 2005, §3.2,
  for the conjugacy of the extensions of a valuation to a normal extension.
-/

public section

open scoped Pointwise

namespace ValuationSubring

variable {K L G : Type*} [Field K] [Field L] [Algebra K L] [Group G] [MulSemiringAction G L]
  [SMulCommClass G K L] [Finite G]

/-- **Separating two orbits of extensions.** If no conjugate of `A` is a conjugate of `B`, and
`A` and `B` restrict to the same valuation subring of `K`, then some element of `L` is a unit of
every conjugate of `A` and a nonunit of every conjugate of `B`. -/
private theorem exists_forall_valuation_smul_eq_one_and_mem_nonunits [Algebra.IsAlgebraic K L]
    {A B : ValuationSubring L} (h : A.comap (algebraMap K L) = B.comap (algebraMap K L))
    (hdisj : ∀ g g' : G, g • A ≠ g' • B) :
    ∃ x : L, (∀ g : G, (g • A).valuation x = 1) ∧ ∀ g : G, x ∈ (g • B).nonunits := by
  classical
  cases nonempty_fintype G
  set SA : Finset (ValuationSubring L) := Finset.univ.image fun g : G ↦ g • A
  set SB : Finset (ValuationSubring L) := Finset.univ.image fun g : G ↦ g • B
  have hS (C) (hC : C ∈ SA ∪ SB) : C.comap (algebraMap K L) = A.comap (algebraMap K L) := by
    rcases Finset.mem_union.mp hC with hC | hC <;> obtain ⟨g, -, rfl⟩ := Finset.mem_image.mp hC <;>
      simp only [comap_algebraMap_pointwise_smul, h]
  -- `e C` is a unit of `C` and a nonunit of the other conjugates; sum it over the orbit of `A`
  obtain ⟨e, he⟩ := exists_valuation_eq_one_and_lt_one _ (SA ∪ SB) hS
  have hA (g : G) : g • A ∈ SA := Finset.mem_image_of_mem _ (Finset.mem_univ g)
  have hB (g : G) : g • B ∈ SB := Finset.mem_image_of_mem _ (Finset.mem_univ g)
  refine ⟨∑ C ∈ SA, e C, fun g ↦ ?_, fun g ↦ ?_⟩
  · have he₁ := (he _ (Finset.mem_union_left _ (hA g))).1
    have hrest : ∑ C ∈ SA.erase (g • A), e C ∈ (g • A).nonunits :=
      sum_mem fun C hC ↦ (mem_nonunits_iff _).mpr <| (he C (Finset.mem_union_left _
        (Finset.mem_of_mem_erase hC))).2 _ (Finset.mem_union_left _ (hA g))
        (Finset.ne_of_mem_erase hC).symm
    rw [← Finset.add_sum_erase _ _ (hA g), Valuation.map_add_eq_of_lt_left _
      (he₁.symm ▸ (mem_nonunits_iff _).mp hrest), he₁]
  · refine sum_mem fun C hC ↦ (mem_nonunits_iff _).mpr <|
      (he C (Finset.mem_union_left _ hC)).2 _ (Finset.mem_union_right _ (hB g)) ?_
    obtain ⟨g', -, rfl⟩ := Finset.mem_image.mp hC
    exact (hdisj g' g).symm

/-- **The extensions of a valuation subring are conjugate.** Let `G` be a finite group acting on
`L` by automorphisms fixing `K`, whose fixed field is purely inseparable over `K` (for instance a
finite Galois group, whose fixed field is `K`). If two valuation subrings `A` and `B` of `L` have
the same restriction to `K`, then `g • A = B` for some `g ∈ G`. -/
theorem exists_smul_eq_of_comap_eq
    (hG : FixedPoints.intermediateField (F := K) G ≤ perfectClosure K L)
    {A B : ValuationSubring L} (h : A.comap (algebraMap K L) = B.comap (algebraMap K L)) :
    ∃ g : G, g • A = B := by
  classical
  cases nonempty_fintype G
  have := Algebra.IsAlgebraic.of_fixedPoints_le_perfectClosure hG
  by_contra! hne
  obtain ⟨x, hxA, hxB⟩ := exists_forall_valuation_smul_eq_one_and_mem_nonunits h
    fun g g' hgg' ↦ hne (g'⁻¹ * g) (by rw [mul_smul, hgg', inv_smul_smul])
  -- the orbit product of `x` is a unit of `A`, a nonunit of `B`, and has a `p`-power in `K`
  obtain ⟨n, a, ha⟩ := mem_perfectClosure_iff.mp
    (hG ((FixedPoints.mem_intermediateField_iff (F := K)).mpr (Finset.smul_prod_perm x)))
  have hNA : A.valuation (∏ g : G, g • x) = 1 := by
    rw [map_prod]
    refine Finset.prod_eq_one fun g _ ↦ ?_
    have := (valuation_pointwise_smul_smul_eq_one_iff (g := g) (A := g⁻¹ • A)).mpr (hxA g⁻¹)
    rwa [smul_inv_smul] at this
  have hNB : B.valuation (∏ g : G, g • x) < 1 := by
    have hx1 := hxB 1
    rw [one_smul] at hx1
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ 1), map_mul, one_smul, map_prod]
    refine mul_lt_one_of_lt_of_le ((mem_nonunits_iff _).mp hx1)
      (Finset.prod_le_one fun g _ ↦ (B.valuation_le_one_iff _).mpr ?_)
    exact mem_inv_pointwise_smul_iff.mp (nonunits_subset (hxB g⁻¹))
  -- so `a` is a unit of `A ∩ K` and a nonunit of `B ∩ K`, which are the same valuation subring
  have hq : ringExpChar K ^ n ≠ 0 := pow_ne_zero _ (expChar_ne_zero K _)
  have haB : a ∈ (B.comap (algebraMap K L)).nonunits := by
    rw [mem_nonunits_comap, ha, mem_nonunits_iff, map_pow]
    exact pow_lt_one₀ zero_le hNB hq
  rw [← h, mem_nonunits_comap, ha, mem_nonunits_iff, map_pow, hNA, one_pow] at haB
  exact lt_irrefl _ haB

/-- **The extensions of a valuation subring form one orbit.** Under a finite group whose fixed
field is purely inseparable over `K`, two valuation subrings of `L` have the same restriction to
`K` exactly when they are conjugate. -/
theorem comap_eq_comap_iff_exists_smul_eq
    (hG : FixedPoints.intermediateField (F := K) G ≤ perfectClosure K L)
    {A B : ValuationSubring L} :
    A.comap (algebraMap K L) = B.comap (algebraMap K L) ↔ ∃ g : G, g • A = B :=
  ⟨exists_smul_eq_of_comap_eq hG, fun ⟨g, hg⟩ ↦ hg ▸ (comap_algebraMap_pointwise_smul g A).symm⟩

omit [Group G] [MulSemiringAction G L] [SMulCommClass G K L] [Finite G] in
/-- **The extensions of a valuation subring to a normal extension are conjugate.** If `L / K` is
normal with finitely many automorphisms, two valuation subrings of `L` with the same restriction
to `K` are conjugate under `Gal(L/K)`. -/
theorem exists_algEquiv_smul_eq_of_comap_eq [Normal K L] [Finite Gal(L/K)]
    {A B : ValuationSubring L} (h : A.comap (algebraMap K L) = B.comap (algebraMap K L)) :
    ∃ σ : Gal(L/K), σ • A = B :=
  exists_smul_eq_of_comap_eq (fun _ hx ↦ TauCeti.mem_perfectClosure_iff_fixed.mpr hx) h

end ValuationSubring

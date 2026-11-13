/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.DirectSum.Finite
public import TauCeti.Algebra.Homology.SpectralObject.ModuleCat
public import TauCeti.Algebra.Homology.SpectralSequence.EulerCharacteristic
public import TauCeti.AlgebraicTopology.Cellular.EulerCharacteristic.FiniteCWType
public import TauCeti.AlgebraicTopology.Singular.Fibration.ArbitraryBase
public import TauCeti.AlgebraicTopology.Singular.Fibration.FiberInclusion
import TauCeti.Topology.CWComplex.Comparison

/-!
# Homology finiteness and Euler characteristic of Serre fibrations

Let `p : E ⟶ B` be a Serre fibration over a space `B` of finite CW type. Pulling `p` back along a
homotopy equivalence `g : Z ⟶ B` from a finite CW complex `Z` yields a Serre spectral sequence
`TauCeti.TopCat.serreSpectralSequence` whose abutment is `H_*(E; R)`
(`TauCeti.TopCat.serreSpectralObjectPullbackAbutmentIso`) and whose first page (numbered `2`) has
objects `⨁_{j ∈ cell Z k} H_q(p⁻¹(g(χⱼ(0))); R)`
(`TauCeti.TopCat.serreSpectralSequencePullbackFirstPageXIsoSigma`).

Combining this spectral sequence with Euler characteristic invariance across pages
(`CategoryTheory.SpectralSequence.eulerChar_page_eq_of_le`) and additivity of rank across the
abutment filtration (`CategoryTheory.Abelian.SpectralObject.finrank_abutment_eq_sum_Ico`) yields
the homological finiteness and Euler characteristic theorems of Serre (1951) and
Klein--Malkiewich--Ramzi:

* **Invariance of the fibre Euler characteristic along paths.** By path transport on fibre
  singular homology (`TauCeti.TopCat.fiberSingularHomologyIsoOfPath`), fibres over points in the
  same path component have the same Euler characteristic whenever both have finite CW type
  (`TauCeti.TopCat.eulerChar_fiber_eq_of_joined`).
* **Vanishing in large degrees and finite generation.** Over a base `B` of finite CW type, if the
  singular homology of each fibre vanishes in large degrees, then so does `H_*(E; R)` over any ring
  `R` (`TauCeti.TopCat.eventually_isZero_singularHomology_of_mem_serreFibrations_of_forall`); over
  a Noetherian ring `R`, if `H_q(p⁻¹(b); R)` is finitely generated for every `b` and `q` (with no
  boundedness assumption on fibre homology), then `H_n(E; R)` is finitely generated in every degree
  `n` (`TauCeti.TopCat.finite_singularHomology_of_mem_serreFibrations_of_forall`).
* **Multiplicativity of the Euler characteristic.** Over any division ring `k`, if each fibre has
  finite-dimensional homology vanishing in large degrees with alternating dimension sum `d`, then
  `∑ᶠ n, (-1)ⁿ dim H_n(E; k) = χ(B) · d`
  (`TauCeti.TopCat.finsum_finrank_singularHomology_of_mem_serreFibrations_of_forall` and
  `TauCeti.TopCat.finsum_finrank_singularHomology_of_mem_serreFibrations`). Over a path-connected
  base `B`, hypotheses on a single fibre `p.fiber b` suffice
  (`TauCeti.TopCat.finsum_finrank_singularHomology_of_mem_serreFibrations_of_finite` and
  `TauCeti.TopCat.finsum_finrank_singularHomology_of_mem_serreFibrations_of_pathConnectedSpace`).

## References

* Jean-Pierre Serre, *Homologie singulière des espaces fibrés. Applications*, Ann. of Math. 54
  (1951), 425--505, Chapter II, Section 4, Proposition 3.
* John R. Klein, Cary Malkiewich, and Maxime Ramzi, *Euler characteristic of fibrations*,
  arXiv:2408.13877, Theorem A.
* Allen Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 5.1.
-/

public section

noncomputable section

universe u

open CategoryTheory Limits Module Set Topology Topology.RelCWComplex AlgebraicTopology
open scoped DirectSum Topology.Homotopy

namespace TauCeti.TopCat

section PathTransport

/-- Fibres of a Serre fibration over points in the same path component have the same Euler
characteristic whenever both fibres have finite CW type. -/
theorem eulerChar_fiber_eq_of_joined {E B : _root_.TopCat.{u}} {p : E ⟶ B}
    (hp : serreFibrations p) {b₀ b₁ : B} (h : Joined b₀ b₁)
    [FiniteCWType (p.fiber b₀)] [FiniteCWType (p.fiber b₁)] :
    eulerChar (p.fiber b₀) = eulerChar (p.fiber b₁) := by
  rw [eulerChar_eq_finsum_finrank_singularHomology (p.fiber b₀) (ULift.{u} ℚ),
    eulerChar_eq_finsum_finrank_singularHomology (p.fiber b₁) (ULift.{u} ℚ)]
  exact finsum_congr fun i ↦ by
    rw [(fiberSingularHomologyIsoOfPath hp (ULift.{u} ℚ) h.somePath i).toLinearEquiv.finrank_eq]

end PathTransport

section PageTwo

/-- The position `(1 - q - 2k, k - 1)` on the first page (numbered `2`) of `serreSpectralSequence`
corresponding to classical base degree `k` and fibre degree `q`. -/
private def serreFirstPagePos (k q : ℕ) : ℤ × ℤ :=
  (1 - (q : ℤ) - 2 * (k : ℤ), (k : ℤ) - 1)

private lemma serreFirstPagePos_snd (k q : ℕ) : (serreFirstPagePos k q).2 = (k : ℤ) - 1 := rfl

private lemma serreFirstPagePos_add (k q : ℕ) :
    (serreFirstPagePos k q).1 + (serreFirstPagePos k q).2 = -((q + k : ℕ) : ℤ) := by
  dsimp [serreFirstPagePos]
  lia

private lemma serreFirstPagePos_injective :
    Function.Injective (fun kq : ℕ × ℕ ↦ serreFirstPagePos kq.1 kq.2) := by
  rintro ⟨k, q⟩ ⟨k', q'⟩ h
  have h1 := congrArg Prod.fst h
  have h2 := congrArg Prod.snd h
  dsimp [serreFirstPagePos] at h1 h2
  ext <;> lia

/-- Reindex the cokernel of `abutmentFiltrationMap` along an equality of total degrees. -/
private def cokernelAbutmentFiltrationMapIso {R : Type u} [Ring R]
    (O : Abelian.SpectralObject (ModuleCat.{u} R) EInt) (b : ℤ) {m m' : ℤ} (h : m = m') :
    cokernel (O.abutmentFiltrationMap b m) ≅ cokernel (O.abutmentFiltrationMap b m') := by
  cases h
  exact Iso.refl _

/-- Over any relative CW complex `C ⊆ B`, the first page (numbered `2`) of `serreSpectralSequence`
vanishes below row `-1` (`pq.2 + 1 < 0`), because `preimageSkeleton C p` is constant below `0`. -/
theorem isZero_serreSpectralSequence_page_two_X_of_lt_neg_one {E B : _root_.TopCat.{u}} [T2Space B]
    (C : Set B) {D : Set B} [RelCWComplex C D] (p : E ⟶ B) (R : Type u) [Ring R]
    (pq : ℤ × ℤ) (h : pq.2 + 1 < 0) :
    IsZero (((serreSpectralSequence C p R).page 2).X pq) := by
  rcases lt_or_ge 0 (pq.1 + pq.2) with hpos | hneg
  · exact isZero_filteredSpaceSpectralSequence_page_two_X _ _ pq hpos
  · obtain ⟨n, hn⟩ := Int.eq_ofNat_of_zero_le (by lia : 0 ≤ -(pq.1 + pq.2))
    let P₀ := TopPair.ofInclusion (Set.Subset.rfl : p ⁻¹' D ⊆ p ⁻¹' D)
    have hP₀ : IsZero (P₀.singularHomology (ModuleCat.of R R) n) := by
      refine (IsZero.iff_id_eq_zero _).2 ?_
      rw [← P₀.singularHomologyMap_id (ModuleCat.of R R) n]
      exact P₀.singularHomologyMap_eq_zero_of_fac (f := 𝟙 P₀) (ModuleCat.of R R) (𝟙 P₀.fst)
        (Category.id_comp _) n
    have hpair : IsZero ((TopPair.ofInclusion
        (monotone_preimageSkeleton (C := C) p (Int.le_add_one le_rfl) :
          preimageSkeleton C p pq.2 ⊆ preimageSkeleton C p (pq.2 + 1))).singularHomology
            (ModuleCat.of R R) n) :=
      (TopPair.isZero_singularHomology_ofInclusion_congr (ModuleCat.of R R) _
        (Set.Subset.rfl : p ⁻¹' D ⊆ p ⁻¹' D)
        (preimageSkeleton_of_neg p h) (preimageSkeleton_of_neg p (by lia)) n).2 hP₀
    exact hpair.of_iso (filteredSpaceSpectralSequenceFirstPageXIso (ModuleCat.of R R)
      (monotone_preimageSkeleton p) pq pq.2 (pq.2 + 1) rfl rfl _ rfl n (by lia))

variable {E B B' : _root_.TopCat.{u}} {p : E ⟶ B} (hp : serreFibrations p)
  [T2Space B'] (C : Set B') [CWComplex C] (g : B' ⟶ B) (R : Type u) [Ring R]
include hp

/-- Every position `pq` on page `2` of the pullback Serre spectral sequence either vanishes (when
`pq.2 + 1 < 0` or `0 ≤ pq.1 + 2 * pq.2`) or has the form `serreFirstPagePos k q`. -/
private lemma isZero_or_eq_serreFirstPagePos (pq : ℤ × ℤ) :
    IsZero (((serreSpectralSequence C (_root_.TopCat.pullbackFst g p) R).page 2).X pq) ∨
      ∃ k q : ℕ, pq = serreFirstPagePos k q := by
  by_cases h1 : pq.2 + 1 < 0
  · exact Or.inl (isZero_serreSpectralSequence_page_two_X_of_lt_neg_one C _ R pq h1)
  · by_cases h2 : 0 ≤ pq.1 + 2 * pq.2
    · exact Or.inl (isZero_serreSpectralSequence_page_two_X
        (mem_serreFibrations_pullbackFst hp g) R C pq h2)
    · refine Or.inr ⟨(pq.2 + 1).toNat, (-1 - pq.1 - 2 * pq.2).toNat, ?_⟩
      ext <;> dsimp [serreFirstPagePos] <;> lia

/-- Over a CW complex `C` with finitely many cells in each dimension, every object on page `2` of
the pullback Serre spectral sequence is finitely generated whenever the fibres of `p` have finitely
generated singular homology in each degree. -/
private lemma finite_serreSpectralSequence_page_two_X [FiniteType C]
    (hfin : ∀ (b : B) (q : ℕ), Module.Finite R
      (((singularHomologyFunctor (ModuleCat.{u} R) q).obj (ModuleCat.of R R)).obj (p.fiber b)))
    (pq : ℤ × ℤ) :
    Module.Finite R
      (((serreSpectralSequence C (_root_.TopCat.pullbackFst g p) R).page 2).X pq) := by
  classical
  rcases isZero_or_eq_serreFirstPagePos hp C g R pq with hz | ⟨k, q, rfl⟩
  · have := ModuleCat.subsingleton_of_isZero hz
    infer_instance
  · have : _root_.Finite (cell C k) := FiniteType.finite_cell k
    have (j : cell C k) : Module.Finite R
        (((singularHomologyFunctor (ModuleCat.{u} R) q).obj (ModuleCat.of R R)).obj
          (p.fiber (g (map k j 0)))) := hfin _ q
    exact Module.Finite.equiv
      ((serreSpectralSequencePullbackFirstPageXIsoSigma hp R C g k q (serreFirstPagePos k q)
        (serreFirstPagePos_snd k q) (serreFirstPagePos_add k q) ≪≫
        ModuleCat.coprodIsoDirectSum _).toLinearEquiv).symm

/-- If `C` has no cells in dimensions `≥ K` and the fibres over the cell centres of `C` have
vanishing homology in degrees `≥ Q`, then page `2` of the pullback Serre spectral sequence vanishes
outside the finite image of `Finset.range K ×ˢ Finset.range Q` under `serreFirstPagePos`. -/
private lemma isZero_serreSpectralSequence_page_two_X_of_notMem {K Q : ℕ}
    (hK : ∀ k, K ≤ k → IsEmpty (cell C k))
    (hQ : ∀ k < K, ∀ (j : cell C k), ∀ q, Q ≤ q →
      IsZero (((singularHomologyFunctor (ModuleCat.{u} R) q).obj (ModuleCat.of R R)).obj
        (p.fiber (g (map k j 0)))))
    {pq : ℤ × ℤ}
    (hpq : pq ∉ (Finset.range K ×ˢ Finset.range Q).image
      (fun kq : ℕ × ℕ ↦ serreFirstPagePos kq.1 kq.2)) :
    IsZero (((serreSpectralSequence C (_root_.TopCat.pullbackFst g p) R).page 2).X pq) := by
  rcases isZero_or_eq_serreFirstPagePos hp C g R pq with hz | ⟨k, q, rfl⟩
  · exact hz
  · refine ((colimit.isColimit _).isZero_pt (Functor.isZero _ fun ⟨j⟩ ↦ ?_)).of_iso
      (serreSpectralSequencePullbackFirstPageXIsoSigma hp R C g k q (serreFirstPagePos k q)
        (serreFirstPagePos_snd k q) (serreFirstPagePos_add k q))
    by_cases hk : k < K
    · refine hQ k hk j q ?_
      by_contra hq
      exact hpq (Finset.mem_image.2
        ⟨(k, q), Finset.mem_product.2 ⟨Finset.mem_range.2 hk, Finset.mem_range.2 (by lia)⟩, rfl⟩)
    · exact ((hK k (by lia)).false j).elim

omit hp [T2Space B'] in
/-- Over a finite CW complex `C`, if the homology of every fibre over `B` vanishes in all large
degrees, there exist bounds `K` and `Q` such that `C` has no cells in dimensions `≥ K` and every
cell centre in dimension `< K` has vanishing fibre homology in degrees `≥ Q`. -/
private lemma exists_cell_and_fiber_bounds [RelCWComplex.Finite C]
    (hvanish : ∀ b : B, ∀ᶠ q in Filter.atTop,
      IsZero (((singularHomologyFunctor (ModuleCat.{u} R) q).obj (ModuleCat.of R R)).obj
        (p.fiber b))) :
    ∃ K Q : ℕ, (∀ k, K ≤ k → IsEmpty (cell C k)) ∧
      ∀ k < K, ∀ (j : cell C k), ∀ q, Q ≤ q →
        IsZero (((singularHomologyFunctor (ModuleCat.{u} R) q).obj (ModuleCat.of R R)).obj
          (p.fiber (g (map k j 0)))) := by
  obtain ⟨K, hK⟩ := Filter.eventually_atTop.1
    (FiniteDimensional.eventually_isEmpty_cell (C := C) (D := ∅))
  have (i : Fin K) : _root_.Finite (cell C i.1) := FiniteType.finite_cell i.1
  have hsigma : ∀ᶠ q in Filter.atTop, ∀ x : Σ i : Fin K, cell C i.1,
      IsZero (((singularHomologyFunctor (ModuleCat.{u} R) q).obj (ModuleCat.of R R)).obj
        (p.fiber (g (map x.1.1 x.2 0)))) :=
    Filter.eventually_all.2 fun x ↦ hvanish (g (map x.1.1 x.2 0))
  obtain ⟨Q, hQ⟩ := Filter.eventually_atTop.1 hsigma
  exact ⟨K, Q, hK, fun k hk j q hq ↦ hQ q hq ⟨⟨k, hk⟩, j⟩⟩

/-- Computing `(S.page 2).eulerChar` over a finite CW complex `C` when every fibre has alternating
homology dimension sum `d`: it equals `cwEulerChar C * d`. -/
private lemma eulerChar_serreSpectralSequence_page_two [RelCWComplex.Finite C]
    {k : Type u} [DivisionRing k] {K Q : ℕ} {d : ℤ}
    (hfin : ∀ (b : B) (q : ℕ), Module.Finite k
      (((singularHomologyFunctor (ModuleCat.{u} k) q).obj (ModuleCat.of k k)).obj (p.fiber b)))
    (hK : ∀ m, K ≤ m → IsEmpty (cell C m))
    (hQ : ∀ m < K, ∀ (j : cell C m), ∀ q, Q ≤ q →
      IsZero (((singularHomologyFunctor (ModuleCat.{u} k) q).obj (ModuleCat.of k k)).obj
        (p.fiber (g (map m j 0)))))
    (hd : ∀ b : B,
      (∑ᶠ q : ℕ, (-1 : ℤ) ^ q * finrank k
        (((singularHomologyFunctor (ModuleCat.{u} k) q).obj (ModuleCat.of k k)).obj
          (p.fiber b))) = d) :
    ((serreSpectralSequence C (_root_.TopCat.pullbackFst g p) k).page 2).eulerChar =
      cwEulerChar C * d := by
  classical
  let S := serreSpectralSequence C (_root_.TopCat.pullbackFst g p) k
  let s₂ := (Finset.range K ×ˢ Finset.range Q).image
    (fun kq : ℕ × ℕ ↦ serreFirstPagePos kq.1 kq.2)
  rw [S.page 2 |>.eulerChar_eq_sum_finSet_of_finrankSupport_subset s₂
    ((GradedObject.finrankSupport_subset_iff _ _).2 fun pq hpq ↦
      ModuleCat.finrank_eq_zero_of_isZero
        (isZero_serreSpectralSequence_page_two_X_of_notMem hp C g k hK hQ hpq)),
    Finset.sum_image serreFirstPagePos_injective.injOn, Finset.sum_product,
    cwEulerChar_eq_sum_range C hK, Finset.sum_mul]
  refine Finset.sum_congr rfl fun m hm ↦ ?_
  have hmK : m < K := Finset.mem_range.1 hm
  have : _root_.Finite (cell C m) := FiniteType.finite_cell m
  let _ : Fintype (cell C m) := Fintype.ofFinite (cell C m)
  have hterm (q : ℕ) :
      ((ComplexShape.up' ((2 : ℤ), 1 - (2 : ℤ))).χ (serreFirstPagePos m q) : ℤ) *
          finrank k ((S.page 2).X (serreFirstPagePos m q)) =
        ∑ j : cell C m, (-1 : ℤ) ^ m * ((-1 : ℤ) ^ q * finrank k
          (((singularHomologyFunctor (ModuleCat.{u} k) q).obj (ModuleCat.of k k)).obj
            (p.fiber (g (map m j 0))))) := by
    have (j : cell C m) : Module.Finite k
        (((singularHomologyFunctor (ModuleCat.{u} k) q).obj (ModuleCat.of k k)).obj
          (p.fiber (g (map m j 0)))) := hfin _ q
    rw [ComplexShape.χ_up'_sub, serreFirstPagePos_add, Int.negOnePow_neg, Int.coe_negOnePow_natCast,
      (serreSpectralSequencePullbackFirstPageXIsoSigma hp k C g m q (serreFirstPagePos m q)
        (serreFirstPagePos_snd m q) (serreFirstPagePos_add m q) ≪≫
        ModuleCat.coprodIsoDirectSum _).toLinearEquiv.finrank_eq,
      Module.finrank_directSum, Nat.cast_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [pow_add]
    ring
  simp_rw [hterm]
  rw [Finset.sum_comm]
  have hcell (j : cell C m) :
      ∑ q ∈ Finset.range Q, (-1 : ℤ) ^ m * ((-1 : ℤ) ^ q * finrank k
          (((singularHomologyFunctor (ModuleCat.{u} k) q).obj (ModuleCat.of k k)).obj
            (p.fiber (g (map m j 0))))) = (-1 : ℤ) ^ m * d := by
    rw [← Finset.mul_sum, ← ModuleCat.finsum_neg_one_pow_finrank_eq_sum_range (hQ m hmK j), hd]
  simp_rw [hcell]
  rw [Finset.sum_const, Finset.card_univ, ← Nat.card_eq_fintype_card]
  ring

/-- On a sufficiently late page `r`, position `(-n - b, b)` of the pullback Serre spectral sequence
is isomorphic to the `b`-th graded piece of the abutment filtration in degree `-n`. -/
private def serreSpectralSequencePageXIsoCokernel
    (hC : range (_root_.TopCat.pullbackFst g p) ⊆ C) (r : ℤ) (hr : 2 ≤ r) (n : ℕ) (b : ℤ)
    (hb₁ : b + 3 ≤ r) (hb₂ : 2 + (n : ℤ) - b ≤ r) :
    ((serreSpectralSequence C (_root_.TopCat.pullbackFst g p) R).page r hr).X (-(n : ℤ) - b, b) ≅
      cokernel ((serreSpectralObject C (_root_.TopCat.pullbackFst g p) R).abutmentFiltrationMap
        b (-n)) :=
  (serreSpectralSequencePageXIsoGraded (mem_serreFibrations_pullbackFst hp g) R hC r hr
    (-(n : ℤ) - b, b) hb₁ (by lia)).trans (cokernelAbutmentFiltrationMapIso _ b (by dsimp; lia))

/-- Over an exhaustive CW complex `C` with cells in dimensions `< K` and fibre homology vanishing in
degrees `≥ Q`, if `g : B' ⟶ B` is a weak homotopy equivalence, then `H_n(E; R)` vanishes for all
`n ≥ K + Q`. -/
private lemma isZero_singularHomology_of_cell_and_fiber_bounds {K Q : ℕ}
    (hg : g.hom.IsWeakHomotopyEquivalence)
    (hC : range (_root_.TopCat.pullbackFst g p) ⊆ C)
    (hK : ∀ m, K ≤ m → IsEmpty (cell C m))
    (hQ : ∀ m < K, ∀ (j : cell C m), ∀ q, Q ≤ q →
      IsZero (((singularHomologyFunctor (ModuleCat.{u} R) q).obj (ModuleCat.of R R)).obj
        (p.fiber (g (map m j 0)))))
    {n : ℕ} (hn : K + Q ≤ n) :
    IsZero (((singularHomologyFunctor (ModuleCat.{u} R) n).obj (ModuleCat.of R R)).obj E) := by
  let p' := _root_.TopCat.pullbackFst g p
  have hp' : serreFibrations p' := mem_serreFibrations_pullbackFst hp g
  let S := serreSpectralSequence C p' R
  let O := serreSpectralObject C p' R
  let r : ℤ := (n : ℤ) + 3
  have hr : (2 : ℤ) ≤ r := by lia
  have : IsIso (O.abutmentFiltrationι (n : ℤ) (-n)) :=
    isIso_serreSpectralObject_abutmentFiltrationι hp' R C hC n le_rfl
  refine (O.isZero_abutment_of_isZero_cokernel (by lia : (-1 : ℤ) ≤ n)
    (isZero_serreSpectralObject_abutmentFiltration p' R C (by lia : (-1 : ℤ) < 0) (-n))
    fun b hb ↦ ?_).of_iso (serreSpectralObjectPullbackAbutmentIso hp R C hg n).symm
  have hb' := Finset.mem_Ico.1 hb
  have hzero2 : IsZero ((S.page 2).X (-(n : ℤ) - b, b)) :=
    isZero_serreSpectralSequence_page_two_X_of_notMem hp C g R hK hQ fun hmem ↦ by
      rcases Finset.mem_image.1 hmem with ⟨⟨m, q⟩, hmq, heq⟩
      rcases Finset.mem_product.1 hmq with ⟨hm, hq⟩
      have hm' : m < K := Finset.mem_range.1 hm
      have hq' : q < Q := Finset.mem_range.1 hq
      have h1 := congrArg Prod.fst heq
      have h2 := congrArg Prod.snd heq
      dsimp [serreFirstPagePos] at h1 h2
      lia
  exact (S.isZero_page_X_of_le (le_rfl : (2 : ℤ) ≤ 2) hzero2 r hr).of_iso
    (serreSpectralSequencePageXIsoCokernel hp C g R hC r hr n b (by lia) (by lia)).symm

/-- Computing `(S.page (N + 3)).eulerChar` over an exhaustive CW complex `C` when `S.page 2`
vanishes outside `s₂` with `N = K + Q` and `g : B' ⟶ B` is a weak homotopy equivalence: it equals
the alternating `finsum` of the homology dimensions of `E`. -/
private lemma eulerChar_serreSpectralSequence_page_top [FiniteType C]
    {k : Type u} [DivisionRing k] {K Q : ℕ} (hg : g.hom.IsWeakHomotopyEquivalence)
    (hC : range (_root_.TopCat.pullbackFst g p) ⊆ C)
    (hfin : ∀ (b : B) (q : ℕ), Module.Finite k
      (((singularHomologyFunctor (ModuleCat.{u} k) q).obj (ModuleCat.of k k)).obj (p.fiber b)))
    (hK : ∀ m, K ≤ m → IsEmpty (cell C m))
    (hQ : ∀ m < K, ∀ (j : cell C m), ∀ q, Q ≤ q →
      IsZero (((singularHomologyFunctor (ModuleCat.{u} k) q).obj (ModuleCat.of k k)).obj
        (p.fiber (g (map m j 0))))) :
    ((serreSpectralSequence C (_root_.TopCat.pullbackFst g p) k).page
        (((K + Q : ℕ) : ℤ) + 3) (by lia)).eulerChar =
      ∑ᶠ n : ℕ, (-1 : ℤ) ^ n * finrank k
        (((singularHomologyFunctor (ModuleCat.{u} k) n).obj (ModuleCat.of k k)).obj E) := by
  classical
  let N := K + Q
  let r : ℤ := (N : ℤ) + 3
  have hr : (2 : ℤ) ≤ r := by lia
  let p' := _root_.TopCat.pullbackFst g p
  let S := serreSpectralSequence C p' k
  let O := serreSpectralObject C p' k
  let φ : ℕ × ℤ → ℤ × ℤ := fun nb ↦ (-(nb.1 : ℤ) - nb.2, nb.2)
  have hφ_inj : Function.Injective φ := fun ⟨_, _⟩ ⟨_, _⟩ h ↦ by
    have h1 := congrArg Prod.fst h; have h2 := congrArg Prod.snd h; dsimp [φ] at h1 h2; ext <;> lia
  let s_rect := (Finset.range N ×ˢ Finset.Ico (-1 : ℤ) (N : ℤ)).image φ
  have hzero_out (pq : ℤ × ℤ) (hpq : pq ∉ s_rect) : IsZero ((S.page r hr).X pq) := by
    refine S.isZero_page_X_of_le (le_rfl : (2 : ℤ) ≤ 2)
      (isZero_serreSpectralSequence_page_two_X_of_notMem hp C g k hK hQ fun hmem ↦ hpq ?_) r hr
    rcases Finset.mem_image.1 hmem with ⟨⟨m, q⟩, hmq, rfl⟩
    rcases Finset.mem_product.1 hmq with ⟨hm, hq⟩
    have hm' := Finset.mem_range.1 hm; have hq' := Finset.mem_range.1 hq
    exact Finset.mem_image.2 ⟨(q + m, (m : ℤ) - 1),
      Finset.mem_product.2 ⟨Finset.mem_range.2 (by lia), Finset.mem_Ico.2 ⟨by lia, by lia⟩⟩,
      by dsimp [φ, serreFirstPagePos]; ext <;> lia⟩
  have := finite_serreSpectralSequence_page_two_X hp C g k hfin
  have (pq : ℤ × ℤ) : Module.Finite k ((S.page r hr).X pq) :=
    S.finite_page_X_of_le (le_rfl : (2 : ℤ) ≤ 2) r hr
  rw [(S.page r hr).eulerChar_eq_sum_finSet_of_finrankSupport_subset s_rect
      ((GradedObject.finrankSupport_subset_iff _ _).2 fun pq hpq ↦
        ModuleCat.finrank_eq_zero_of_isZero (hzero_out pq hpq)),
    Finset.sum_image hφ_inj.injOn, Finset.sum_product,
    ModuleCat.finsum_neg_one_pow_finrank_eq_sum_range fun n hn ↦
      isZero_singularHomology_of_cell_and_fiber_bounds hp C g k hg hC hK hQ hn]
  refine Finset.sum_congr rfl fun n hn ↦ ?_
  have hnN : n < N := Finset.mem_range.1 hn
  have : IsIso (O.abutmentFiltrationι (N : ℤ) (-n)) :=
    isIso_serreSpectralObject_abutmentFiltrationι
      (mem_serreFibrations_pullbackFst hp g) k C hC n (by lia)
  have hcok_iso (b : ℤ) (hb : b ∈ Finset.Ico (-1 : ℤ) (N : ℤ)) :=
    have hb' := Finset.mem_Ico.1 hb
    serreSpectralSequencePageXIsoCokernel hp C g k hC r hr n b (by lia) (by lia)
  rw [← (serreSpectralObjectPullbackAbutmentIso hp k C hg n).toLinearEquiv.finrank_eq,
    O.finrank_abutment_eq_sum_Ico (by lia : (-1 : ℤ) ≤ N)
      (isZero_serreSpectralObject_abutmentFiltration p' k C (by lia : (-1 : ℤ) < 0) (-n))
      (fun b hb ↦ Module.Finite.equiv (hcok_iso b hb).toLinearEquiv),
    Nat.cast_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun b hb ↦ ?_
  rw [ComplexShape.χ_up'_sub, show (φ (n, b)).1 + (φ (n, b)).2 = -(n : ℤ) by dsimp [φ]; ring,
    Int.negOnePow_neg, Int.coe_negOnePow_natCast, (hcok_iso b hb).toLinearEquiv.finrank_eq]

end PageTwo

section Main

variable {E B : _root_.TopCat.{u}} {p : E ⟶ B} (hp : serreFibrations p) [FiniteCWType B]
include hp

/-- **Vanishing of singular homology in large degrees for a Serre fibration.** Let `p : E ⟶ B` be
a Serre fibration over a space `B` of finite CW type. Over any ring `R`, if the singular homology of
every fibre `p.fiber b` vanishes in all large degrees, then `H_n(E; R)` vanishes in all large
degrees. -/
theorem eventually_isZero_singularHomology_of_mem_serreFibrations_of_forall
    (R : Type u) [Ring R]
    (hvanish : ∀ b : B, ∀ᶠ q in Filter.atTop,
      IsZero (((singularHomologyFunctor (ModuleCat.{u} R) q).obj (ModuleCat.of R R)).obj
        (p.fiber b))) :
    ∀ᶠ n in Filter.atTop,
      IsZero (((singularHomologyFunctor (ModuleCat.{u} R) n).obj (ModuleCat.of R R)).obj E) := by
  obtain ⟨Z, _, _, _, _, ⟨e⟩⟩ := FiniteCWType.exists_homotopyEquiv_univ B
  let g : _root_.TopCat.of Z ⟶ B := _root_.TopCat.ofHom e.symm.toFun
  obtain ⟨K, Q, hK, hQ⟩ := exists_cell_and_fiber_bounds (univ : Set Z) g R hvanish
  exact Filter.eventually_atTop.2 ⟨K + Q, fun n hn ↦
    isZero_singularHomology_of_cell_and_fiber_bounds hp univ g R e.symm.isWeakHomotopyEquivalence
      (subset_univ _) hK hQ hn⟩

/-- **Finite generation of singular homology for a Serre fibration.** Let `p : E ⟶ B` be a Serre
fibration over a space `B` of finite CW type, and let `R` be a Noetherian ring. If `H_q(p⁻¹(b); R)`
is finitely generated for every `b : B` and `q : ℕ` (with no boundedness assumption on fibre
homology), then `H_n(E; R)` is finitely generated in every degree `n`. -/
theorem finite_singularHomology_of_mem_serreFibrations_of_forall
    (R : Type u) [Ring R] [IsNoetherianRing R]
    (hfin : ∀ (b : B) (q : ℕ), Module.Finite R
      (((singularHomologyFunctor (ModuleCat.{u} R) q).obj (ModuleCat.of R R)).obj (p.fiber b)))
    (n : ℕ) :
    Module.Finite R
      (((singularHomologyFunctor (ModuleCat.{u} R) n).obj (ModuleCat.of R R)).obj E) := by
  obtain ⟨Z, _, _, _, _, ⟨e⟩⟩ := FiniteCWType.exists_homotopyEquiv_univ B
  let g : _root_.TopCat.of Z ⟶ B := _root_.TopCat.ofHom e.symm.toFun
  have hg : g.hom.IsWeakHomotopyEquivalence := e.symm.isWeakHomotopyEquivalence
  let p' := _root_.TopCat.pullbackFst g p
  let S := serreSpectralSequence (univ : Set Z) p' R
  let O := serreSpectralObject (univ : Set Z) p' R
  let r : ℤ := (n : ℤ) + 3
  have hr : (2 : ℤ) ≤ r := by lia
  have : IsIso (O.abutmentFiltrationι (n : ℤ) (-n)) :=
    isIso_serreSpectralObject_abutmentFiltrationι
      (mem_serreFibrations_pullbackFst hp g) R univ (subset_univ _) n le_rfl
  have hcok (b : ℤ) (hb : b ∈ Finset.Ico (-1 : ℤ) (n : ℤ)) :
      Module.Finite R ↑(cokernel (O.abutmentFiltrationMap b (-n))) := by
    have hb' := Finset.mem_Ico.1 hb
    have := finite_serreSpectralSequence_page_two_X hp univ g R hfin
    have : Module.Finite R ((S.page r hr).X (-(n : ℤ) - b, b)) :=
      S.finite_page_X_of_le (le_rfl : (2 : ℤ) ≤ 2) r hr
    exact Module.Finite.equiv
      (serreSpectralSequencePageXIsoCokernel hp univ g R (subset_univ _) r hr n b
        (by lia) (by lia)).toLinearEquiv
  have := O.finite_abutment_of_finite_cokernel (by lia : (-1 : ℤ) ≤ n)
    (isZero_serreSpectralObject_abutmentFiltration p' R univ (by lia : (-1 : ℤ) < 0) (-n)) hcok
  exact Module.Finite.equiv
    (serreSpectralObjectPullbackAbutmentIso hp R univ hg n).toLinearEquiv

/-- **Euler characteristic of a Serre fibration with homologically finite fibres.** Let `p : E ⟶ B`
be a Serre fibration over a space `B` of finite CW type, and let `k` be a division ring. If every
fibre `p.fiber b` has finite-dimensional singular homology in each degree, vanishing singular
homology in large degrees, and alternating homology dimension sum `d`, then
`∑ᶠ n, (-1)ⁿ dim H_n(E; k) = χ(B) · d`. -/
theorem finsum_finrank_singularHomology_of_mem_serreFibrations_of_forall
    (k : Type u) [DivisionRing k] {d : ℤ}
    (hfin : ∀ (b : B) (q : ℕ), Module.Finite k
      (((singularHomologyFunctor (ModuleCat.{u} k) q).obj (ModuleCat.of k k)).obj (p.fiber b)))
    (hvanish : ∀ b : B, ∀ᶠ q in Filter.atTop,
      IsZero (((singularHomologyFunctor (ModuleCat.{u} k) q).obj (ModuleCat.of k k)).obj
        (p.fiber b)))
    (hd : ∀ b : B,
      (∑ᶠ q : ℕ, (-1 : ℤ) ^ q * finrank k
        (((singularHomologyFunctor (ModuleCat.{u} k) q).obj (ModuleCat.of k k)).obj
          (p.fiber b))) = d) :
    ∑ᶠ n : ℕ, (-1 : ℤ) ^ n * finrank k
      (((singularHomologyFunctor (ModuleCat.{u} k) n).obj (ModuleCat.of k k)).obj E) =
      eulerChar B * d := by
  obtain ⟨Z, _, _, _, _, ⟨e⟩⟩ := FiniteCWType.exists_homotopyEquiv_univ B
  let g : _root_.TopCat.of Z ⟶ B := _root_.TopCat.ofHom e.symm.toFun
  obtain ⟨K, Q, hK, hQ⟩ := exists_cell_and_fiber_bounds (univ : Set Z) g k hvanish
  let S := serreSpectralSequence (univ : Set Z) (_root_.TopCat.pullbackFst g p) k
  have := finite_serreSpectralSequence_page_two_X hp univ g k hfin
  have hsupp : {pq : ℤ × ℤ | ¬ IsZero ((S.page 2).X pq)}.Finite := by
    classical
    exact ((Finset.range K ×ˢ Finset.range Q).image
      (fun kq : ℕ × ℕ ↦ serreFirstPagePos kq.1 kq.2)).finite_toSet.subset fun pq hpq ↦ by
        by_contra hnot
        exact hpq (isZero_serreSpectralSequence_page_two_X_of_notMem hp univ g k hK hQ
          (Finset.mem_coe.not.1 hnot))
  have hB : eulerChar B = cwEulerChar (univ : Set Z) :=
    eulerChar_eq_cwEulerChar (e.trans (Homeomorph.Set.univ Z).symm.toHomotopyEquiv)
  rw [← eulerChar_serreSpectralSequence_page_top hp univ g e.symm.isWeakHomotopyEquivalence
      (subset_univ _) hfin hK hQ,
    S.eulerChar_page_eq_of_le (le_rfl : (2 : ℤ) ≤ 2) hsupp (((K + Q : ℕ) : ℤ) + 3) (by lia),
    eulerChar_serreSpectralSequence_page_two hp univ g hfin hK hQ hd, hB]

/-! ### Specializations to path-connected bases and fibres of finite CW type -/

/-- **Klein--Malkiewich--Ramzi Theorem A** (over a division ring): for a Serre fibration
`p : E ⟶ B` over a path-connected space `B` of finite CW type, if a single fibre `p.fiber b` has
finite-dimensional singular homology in every degree and vanishing homology in all large degrees,
then the homological Euler characteristic of `E` is `χ(B)` times that of `p.fiber b`. -/
theorem finsum_finrank_singularHomology_of_mem_serreFibrations_of_finite
    [PathConnectedSpace B] (b : B) (k : Type u) [DivisionRing k]
    (hfin : ∀ q : ℕ, Module.Finite k
      (((singularHomologyFunctor (ModuleCat.{u} k) q).obj (ModuleCat.of k k)).obj (p.fiber b)))
    (hvanish : ∀ᶠ q in Filter.atTop,
      IsZero (((singularHomologyFunctor (ModuleCat.{u} k) q).obj (ModuleCat.of k k)).obj
        (p.fiber b))) :
    ∑ᶠ n : ℕ, (-1 : ℤ) ^ n * finrank k
      (((singularHomologyFunctor (ModuleCat.{u} k) n).obj (ModuleCat.of k k)).obj E) =
      eulerChar B * ∑ᶠ q : ℕ, (-1 : ℤ) ^ q * finrank k
        (((singularHomologyFunctor (ModuleCat.{u} k) q).obj (ModuleCat.of k k)).obj (p.fiber b)) :=
  finsum_finrank_singularHomology_of_mem_serreFibrations_of_forall hp k
    (fun b' q ↦
      have := hfin q
      Module.Finite.equiv
        (fiberSingularHomologyIsoOfPath hp k (PathConnectedSpace.somePath b b') q).toLinearEquiv)
    (fun b' ↦ hvanish.mono fun q hq ↦
      hq.of_iso (fiberSingularHomologyIsoOfPath hp k (PathConnectedSpace.somePath b b') q).symm)
    (fun b' ↦ finsum_congr fun q ↦ by
      rw [(fiberSingularHomologyIsoOfPath hp k
        (PathConnectedSpace.somePath b b') q).toLinearEquiv.finrank_eq])

/-- Over a path-connected base `B` of finite CW type, if a single fibre `p.fiber b` of a Serre
fibration `p : E ⟶ B` has finite CW type, then `H_n(E; R)` vanishes in all large degrees over any
ring `R`. -/
theorem eventually_isZero_singularHomology_of_mem_serreFibrations_of_pathConnectedSpace
    [PathConnectedSpace B] (b : B) [FiniteCWType (p.fiber b)] (R : Type u) [Ring R] :
    ∀ᶠ n in Filter.atTop,
      IsZero (((singularHomologyFunctor (ModuleCat.{u} R) n).obj (ModuleCat.of R R)).obj E) :=
  eventually_isZero_singularHomology_of_mem_serreFibrations_of_forall hp R fun b' ↦
    (eventually_isZero_singularHomology_of_finiteCWType (p.fiber b) (ModuleCat.of R R)).mono
      fun q hq ↦ hq.of_iso
        (fiberSingularHomologyIsoOfPath hp R (PathConnectedSpace.somePath b b') q).symm

/-- Over a path-connected base `B` of finite CW type, if a single fibre `p.fiber b` of a Serre
fibration `p : E ⟶ B` has finite CW type, then `H_n(E; R)` is finitely generated in every degree
over any Noetherian ring `R`. -/
theorem finite_singularHomology_of_mem_serreFibrations_of_pathConnectedSpace
    [PathConnectedSpace B] (b : B) [FiniteCWType (p.fiber b)]
    (R : Type u) [Ring R] [IsNoetherianRing R] (n : ℕ) :
    Module.Finite R
      (((singularHomologyFunctor (ModuleCat.{u} R) n).obj (ModuleCat.of R R)).obj E) :=
  finite_singularHomology_of_mem_serreFibrations_of_forall hp R
    (fun b' q ↦
      have := finite_singularHomology_of_finiteCWType (p.fiber b) (ModuleCat.of R R) q
      Module.Finite.equiv
        (fiberSingularHomologyIsoOfPath hp R (PathConnectedSpace.somePath b b') q).toLinearEquiv)
    n

/-- **Multiplicativity of the Euler characteristic in a Serre fibration** over a path-connected base
`B` of finite CW type: if a single fibre `p.fiber b` has finite CW type, then for any division ring
`k`, `∑ᶠ n, (-1)ⁿ dim H_n(E; k) = χ(B) · χ(p⁻¹(b))`. -/
theorem finsum_finrank_singularHomology_of_mem_serreFibrations_of_pathConnectedSpace
    [PathConnectedSpace B] (b : B) [FiniteCWType (p.fiber b)] (k : Type u) [DivisionRing k] :
    ∑ᶠ n : ℕ, (-1 : ℤ) ^ n * finrank k
      (((singularHomologyFunctor (ModuleCat.{u} k) n).obj (ModuleCat.of k k)).obj E) =
      eulerChar B * eulerChar (p.fiber b) := by
  rw [finsum_finrank_singularHomology_of_mem_serreFibrations_of_finite hp b k
    (fun q ↦ finite_singularHomology_of_finiteCWType (p.fiber b) (ModuleCat.of k k) q)
    (eventually_isZero_singularHomology_of_finiteCWType (p.fiber b) (ModuleCat.of k k)),
    ← eulerChar_eq_finsum_finrank_singularHomology (p.fiber b) k]

/-- For a Serre fibration `p : E ⟶ B` over a (possibly disconnected) space `B` of finite CW type
whose fibres all have finite CW type, `H_n(E; R)` vanishes in all large degrees over any ring
`R`. -/
theorem eventually_isZero_singularHomology_of_mem_serreFibrations
    [∀ b, FiniteCWType (p.fiber b)] (R : Type u) [Ring R] :
    ∀ᶠ n in Filter.atTop,
      IsZero (((singularHomologyFunctor (ModuleCat.{u} R) n).obj (ModuleCat.of R R)).obj E) :=
  eventually_isZero_singularHomology_of_mem_serreFibrations_of_forall hp R fun b ↦
    eventually_isZero_singularHomology_of_finiteCWType (p.fiber b) (ModuleCat.of R R)

/-- For a Serre fibration `p : E ⟶ B` over a (possibly disconnected) space `B` of finite CW type
whose fibres all have finite CW type, `H_n(E; R)` is finitely generated in every degree over any
Noetherian ring `R`. -/
theorem finite_singularHomology_of_mem_serreFibrations
    [∀ b, FiniteCWType (p.fiber b)] (R : Type u) [Ring R] [IsNoetherianRing R] (n : ℕ) :
    Module.Finite R
      (((singularHomologyFunctor (ModuleCat.{u} R) n).obj (ModuleCat.of R R)).obj E) :=
  finite_singularHomology_of_mem_serreFibrations_of_forall hp R
    (fun b q ↦ finite_singularHomology_of_finiteCWType (p.fiber b) (ModuleCat.of R R) q) n

/-- **Multiplicativity of the Euler characteristic in a Serre fibration** over a (possibly
disconnected) base `B` of finite CW type: if every fibre `p.fiber b` has finite CW type and Euler
characteristic `d`, then `∑ᶠ n, (-1)ⁿ dim H_n(E; k) = χ(B) · d` over any division ring `k`. -/
theorem finsum_finrank_singularHomology_of_mem_serreFibrations
    [∀ b, FiniteCWType (p.fiber b)] {d : ℤ} (hd : ∀ b, eulerChar (p.fiber b) = d)
    (k : Type u) [DivisionRing k] :
    ∑ᶠ n : ℕ, (-1 : ℤ) ^ n * finrank k
      (((singularHomologyFunctor (ModuleCat.{u} k) n).obj (ModuleCat.of k k)).obj E) =
      eulerChar B * d :=
  finsum_finrank_singularHomology_of_mem_serreFibrations_of_forall hp k
    (fun b q ↦ finite_singularHomology_of_finiteCWType (p.fiber b) (ModuleCat.of k k) q)
    (fun b ↦ eventually_isZero_singularHomology_of_finiteCWType (p.fiber b) (ModuleCat.of k k))
    (fun b ↦ (eulerChar_eq_finsum_finrank_singularHomology (p.fiber b) k).symm.trans (hd b))

end Main

end TauCeti.TopCat
